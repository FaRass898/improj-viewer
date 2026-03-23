"""
improj_viewer.py — IMPROJ Viewer v2
Структура: Профиль (Фарис) → Месяц (Март 2026) → Задачи
"""

import json, os, datetime, math, tkinter as tk
try:
    from PIL import Image as _PILImage, ImageTk as _ImageTk
    _PIL_OK = True
except ImportError:
    _PIL_OK = False
from tkinter import ttk, filedialog, messagebox, simpledialog
import threading, urllib.request, urllib.error

VERSION = "1.0.0"
# Замени на свой GitHub репозиторий после загрузки:
GITHUB_USER = "FaRass898"
GITHUB_REPO = "improj-viewer"
UPDATE_URL  = f"https://raw.githubusercontent.com/{GITHUB_USER}/{GITHUB_REPO}/main/improj_viewer.py"
VERSION_URL = f"https://raw.githubusercontent.com/{GITHUB_USER}/{GITHUB_REPO}/main/version.txt"

UNITS = {0: "ft", 1: "m", 2: "in", 3: "cm"}
FACTOR_A = 0.045
FACTOR_B = 0.030
SETTINGS_FILE = os.path.join(os.path.expanduser("~"), "improj_settings.json")
MONTHS_RU = ["Январь","Февраль","Март","Апрель","Май","Июнь",
             "Июль","Август","Сентябрь","Октябрь","Ноябрь","Декабрь"]
COLORS = ["#5b8ef0","#4dc87a","#f0a050","#c084fc","#60c8f0",
          "#e05555","#f0d050","#50c8c8","#c05080","#80c050"]

def get_profiles_file():
    try:
        if os.path.exists(SETTINGS_FILE):
            with open(SETTINGS_FILE,"r",encoding="utf-8") as f:
                s = json.load(f)
            p = s.get("profiles_path","").strip()
            if p and os.path.isdir(os.path.dirname(p) or "."):
                return p
    except Exception:
        pass
    return os.path.join(os.path.expanduser("~"), "improj_profiles.json")

def save_settings(path):
    json.dump({"profiles_path":path},
              open(SETTINGS_FILE,"w",encoding="utf-8"), ensure_ascii=False, indent=2)

def load_profiles():
    try:
        pf = get_profiles_file()
        if pf and os.path.exists(pf):
            with open(pf,"r",encoding="utf-8") as f:
                return json.load(f)
    except Exception:
        pass
    return {}

def save_profiles(p):
    try:
        pf = get_profiles_file()
        if pf:
            os.makedirs(os.path.dirname(pf) or ".", exist_ok=True)
            with open(pf,"w",encoding="utf-8") as f:
                json.dump(p, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print("Save error:", e)

def get_scale(grid):
    mn=grid.get("MinY",0); mx=grid.get("MaxY",0); meta=mx-mn
    if meta<=0: return None,None,None
    for bg in grid.get("Bounds",[]):
        items=bg.get("Items",[])
        top=next((i for i in items if i.get("BoundType")==1),None)
        bot=next((i for i in items if i.get("BoundType")==3),None)
        if top and bot:
            px=abs(bot["ImagePoint"]["Y"]-top["ImagePoint"]["Y"])
            if px>0: return meta/px,top["ImagePoint"]["Y"],mn
    return None,None,None

def detect_scale(grids):
    for g in grids:
        s=g.get("scale")
        if s is not None: return "A" if s<0.3 else "B"
    return "A"

def parse_improj(path):
    with open(path,"r",encoding="utf-8") as f: data=json.load(f)
    uc=data.get("Unit",0); unit=UNITS.get(uc,"ft"); total=0.0; grids=[]
    for gi,grid in enumerate(data.get("Grids",[])):
        g_unit=UNITS.get(grid.get("Unit",uc),unit)
        scale,top_px,min_yr=get_scale(grid); gsum=0.0; curves=[]
        for curve in grid.get("Curves",[]):
            for item in curve.get("Items",[]):
                pts=item.get("Points",[]); lr=fr=tr=None
                if pts and scale:
                    ys=[p["Y"] for p in pts]
                    lr=(max(ys)-min(ys))*scale
                    fr=min_yr+(min(ys)-top_px)*scale
                    tr=min_yr+(max(ys)-top_px)*scale
                    gsum+=lr; total+=lr
                col=item.get("Color") or {}
                curves.append({"name":item.get("Name","?"),"n_pts":len(pts),
                    "color":"#{:02x}{:02x}{:02x}".format(col.get("R",128),col.get("G",128),col.get("B",128)),
                    "length":lr,"from":fr,"to":tr,"unit":g_unit})
        grids.append({"name":grid.get("Name",f"Grid {gi}"),"unit":g_unit,
                      "scale":scale,"sum":gsum,"curves":curves,
                      "total_pts":sum(c["n_pts"] for c in curves)})
    return {"filename":os.path.basename(path),"path":path,
            "well":data.get("WELL","—"),"api":str(data.get("API","—")),
            "unit":unit,"step":data.get("Step",0),"total_sum":total,"grids":grids,
            "added":datetime.datetime.now().strftime("%d.%m.%Y %H:%M")}

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("IMPROJ Viewer")
        self.geometry("1100x700")
        self.configure(bg="#0f1117")
        self.resizable(True,True)
        self._profiles=load_profiles()
        self._cur_profile=None; self._cur_month=None
        self._sel_row=None; self._svars={}
        self._view="tasks"; self._anim_prog=0.0; self._anim_job=None
        self._profile_colors=self._load_profile_colors()
        self._search_var=tk.StringVar()
        self._sort_var=tk.StringVar(value="дата")
        self._sort_rev=tk.BooleanVar(value=False)
        self._setup_style(); self._build_ui()
        self._refresh_profiles(); self._auto_refresh()
        self.bind("<Configure>", lambda e: self._on_resize(e))
        try:
            ico=os.path.join(os.path.dirname(os.path.abspath(__file__)),"icon.ico")
            if os.path.exists(ico): self.iconbitmap(ico)
        except: pass
        self._bg_image = None
        self._bg_photo = None
        self._load_bg_image()
        # Проверяем обновления в фоне при запуске
        threading.Thread(target=self._check_update_bg, daemon=True).start()

    def _check_update_bg(self):
        """Проверяет обновления в фоновом потоке — не блокирует UI."""
        try:
            req=urllib.request.Request(VERSION_URL,
                headers={"User-Agent":"improj-viewer"})
            with urllib.request.urlopen(req, timeout=5) as r:
                latest=r.read().decode().strip()
            if latest and latest != VERSION:
                # Уведомляем в главном потоке
                self.after(0, lambda v=latest: self._show_update_badge(v))
        except Exception:
            pass  # Нет интернета — тихо игнорируем

    def _show_update_badge(self, latest_version):
        """Показывает кнопку обновления в хедере."""
        if hasattr(self, "_update_btn"):
            return
        self._update_btn = tk.Button(
            self.pbar,
            text=f"🔔 Обновление {latest_version}",
            command=lambda v=latest_version: self._do_update(v),
            bg="#1a2a1a", fg="#4dc87a",
            activebackground="#243524",
            bd=0, relief="flat", padx=12, pady=5,
            font=("Segoe UI",9,"bold"), cursor="hand2")
        self._update_btn.pack(side="right", padx=12, pady=6)

    def _do_update(self, latest_version):
        """Скачивает и устанавливает новую версию."""
        if not messagebox.askyesno("Обновление",
            f"Доступна версия {latest_version}\n"
            f"Текущая версия: {VERSION}\n\n"
            "Скачать и установить обновление?\n"
            "(программа перезапустится автоматически)"):
            return

        win=tk.Toplevel(self); win.title("Обновление")
        win.geometry("360x120"); win.configure(bg="#0f1117")
        win.resizable(False,False); win.grab_set()
        tk.Label(win,text="Скачиваем обновление...",
                 bg="#0f1117",fg="#e2e6f0",
                 font=("Segoe UI",11,"bold")).pack(pady=(24,8))
        prog=ttk.Progressbar(win,mode="indeterminate",length=300)
        prog.pack(padx=30); prog.start(10)

        def _download():
            try:
                req=urllib.request.Request(UPDATE_URL,
                    headers={"User-Agent":"improj-viewer"})
                with urllib.request.urlopen(req, timeout=30) as r:
                    new_code=r.read()

                # Сохраняем рядом с текущим файлом
                current=os.path.abspath(__file__)
                # Бэкап старой версии
                backup=current+".backup"
                if os.path.exists(current):
                    import shutil; shutil.copy2(current, backup)
                # Записываем новую версию
                with open(current,"wb") as f:
                    f.write(new_code)

                self.after(0, lambda: _done(True))
            except Exception as e:
                self.after(0, lambda err=str(e): _done(False, err))

        def _done(ok, err=""):
            prog.stop(); win.destroy()
            if ok:
                messagebox.showinfo("Готово",
                    "Обновление установлено!\n"
                    "Закрой и снова открой программу.")
                # Удаляем кнопку обновления
                if hasattr(self,"_update_btn"):
                    self._update_btn.destroy()
                    del self._update_btn
            else:
                messagebox.showerror("Ошибка",
                    f"Не удалось скачать обновление:\n{err}\n\n"
                    "Скачай файл вручную с GitHub.")

        threading.Thread(target=_download, daemon=True).start()

    def _load_bg_image(self):
        """Загружает фоновое изображение Fon.png рядом с программой."""
        if not _PIL_OK: return
        try:
            folder = os.path.dirname(os.path.abspath(__file__))
            fon_path = os.path.join(folder, "Fon.png")
            if not os.path.exists(fon_path): return
            img = _PILImage.open(fon_path).convert("RGBA")
            # Делаем полупрозрачным — 25% видимости
            r,g,b,a = img.split()
            a = a.point(lambda x: int(x * 0.18))
            img.putalpha(a)
            self._bg_image = img
            self._draw_bg()
        except Exception as e:
            print("Фон не загружен:", e)

    def _draw_bg(self):
        """Рисует фон на главном окне через canvas."""
        if not self._bg_image: return
        try:
            W = self.winfo_width() or 1100
            H = self.winfo_height() or 700
            # Масштабируем фон под размер окна
            bg = self._bg_image.resize((W, H), _PILImage.LANCZOS)
            self._bg_photo = _ImageTk.PhotoImage(bg)
            # Помещаем как метку позади всего
            if not hasattr(self, '_bg_label'):
                self._bg_label = tk.Label(self, image=self._bg_photo, bd=0)
                self._bg_label.place(x=0, y=0, relwidth=1, relheight=1)
                self._bg_label.lower()  # отправляем на задний план
            else:
                self._bg_label.configure(image=self._bg_photo)
        except Exception as e:
            print("Ошибка фона:", e)

    def _load_profile_colors(self):
        """Загружает сохранённые цвета профилей."""
        try:
            f = os.path.join(os.path.expanduser("~"), "improj_colors.json")
            if os.path.exists(f):
                return json.load(open(f, encoding="utf-8"))
        except: pass
        return {}

    def _save_profile_colors(self):
        f = os.path.join(os.path.expanduser("~"), "improj_colors.json")
        json.dump(self._profile_colors, open(f,"w",encoding="utf-8"),
                  ensure_ascii=False, indent=2)

    def _get_profile_color(self, name):
        """Возвращает цвет профиля — сохранённый или авто."""
        if name in self._profile_colors:
            return self._profile_colors[name]
        idx = sorted(self._profiles.keys()).index(name) if name in self._profiles else 0
        return COLORS[idx % len(COLORS)]

    def _pick_profile_color(self, name):
        """Открывает диалог выбора цвета для профиля."""
        from tkinter import colorchooser
        current = self._get_profile_color(name)
        color = colorchooser.askcolor(color=current,
            title=f"Цвет профиля «{name}»")
        if color and color[1]:
            self._profile_colors[name] = color[1]
            self._save_profile_colors()
            self._refresh_profiles()
            if self._view == "analytics":
                self._start_anim()

    def _setup_style(self):
        s=ttk.Style()
        try: s.theme_use("clam")
        except: pass
        s.configure("Treeview",background="#13161f",fieldbackground="#13161f",
                    foreground="#c5cce0",borderwidth=0,rowheight=24)
        s.configure("Treeview.Heading",background="#1e2233",foreground="#8b93a8",relief="flat")
        s.map("Treeview",background=[("selected","#252d45")],foreground=[("selected","#5b8ef0")])

    def _btn(self,p,text,cmd,fg="#8b93a8",bg="#1e2233",**kw):
        kw.setdefault("font",("Segoe UI",9))
        b=tk.Button(p,text=text,command=cmd,bg=bg,fg=fg,
                    activebackground="#252d45",activeforeground=fg,
                    bd=0,relief="flat",cursor="hand2",**kw)
        return b

    def _build_ui(self):
        # Header
        hdr=tk.Frame(self,bg="#0d0f18",height=48); hdr.pack(fill="x"); hdr.pack_propagate(False)
        tk.Label(hdr,text="IMPROJ Viewer",bg="#0d0f18",fg="#e2e6f0",
                 font=("Segoe UI",13,"bold")).pack(side="left",padx=16,pady=12)
        vtabs=tk.Frame(hdr,bg="#0d0f18"); vtabs.pack(side="left",padx=12)
        self.btn_tasks=tk.Button(vtabs,text="Задачи",command=lambda:self._switch("tasks"),
                    bg="#1e2233",fg="#5b8ef0",bd=0,relief="flat",padx=14,pady=6,
                    font=("Segoe UI",9,"bold"),cursor="hand2"); self.btn_tasks.pack(side="left")
        self.btn_an=tk.Button(vtabs,text="Аналитика",command=lambda:self._switch("analytics"),
                    bg="#0d0f18",fg="#4a5580",bd=0,relief="flat",padx=14,pady=6,
                    font=("Segoe UI",9),cursor="hand2"); self.btn_an.pack(side="left",padx=(2,0))
        self._btn(hdr,"🔄",self._refresh_all,fg="#4dc87a",bg="#0d0f18",padx=10,pady=6
                  ).pack(side="right",padx=8,pady=8)
        self._btn(hdr,"📂 Общая папка",self._shared_folder,fg="#4a5580",bg="#0d0f18",padx=10,pady=6
                  ).pack(side="right",pady=8)
        self.path_lbl=tk.Label(hdr,text="",bg="#0d0f18",fg="#252d45",font=("Segoe UI",8))
        self.path_lbl.pack(side="right",padx=8); self._upd_path()

        # Profiles bar
        self.pbar=tk.Frame(self,bg="#13151e",height=40); self.pbar.pack(fill="x"); self.pbar.pack_propagate(False)
        self.ptabs=tk.Frame(self.pbar,bg="#13151e"); self.ptabs.pack(side="left",fill="y",padx=8)
        self._btn(self.pbar,"+ Профиль",self._new_profile,fg="#4dc87a",bg="#1a2a1a",padx=10,pady=5
                  ).pack(side="left",pady=6)
        self._btn(self.pbar,"✕",self._del_profile,fg="#e05555",bg="#2a1515",padx=8,pady=5
                  ).pack(side="left",padx=4,pady=6)

        # Content
        self.cf=tk.Frame(self,bg="#0f1117"); self.cf.pack(fill="both",expand=True)
        self._build_tasks(); self._build_analytics(); self._switch("tasks")

    def _build_tasks(self):
        self.tf=tk.Frame(self.cf,bg="#0f1117")
        # Left months panel
        left=tk.Frame(self.tf,bg="#13161f",width=165); left.pack(side="left",fill="y"); left.pack_propagate(False)
        tk.Label(left,text="Месяцы",bg="#13161f",fg="#6b7599",
                 font=("Segoe UI",8,"bold")).pack(anchor="w",padx=10,pady=(10,4))
        mf=tk.Frame(left,bg="#13161f"); mf.pack(fill="x",padx=8,pady=(0,6))
        self._btn(mf,"+ Месяц",self._new_month,fg="#7b8fff",bg="#1c2035",padx=8,pady=5
                  ).pack(side="left",fill="x",expand=True,padx=(0,2))
        self._btn(mf,"✕",self._del_month,fg="#e05555",bg="#2a1515",padx=6,pady=5).pack(side="left")
        self.months_panel=tk.Frame(left,bg="#13161f"); self.months_panel.pack(fill="both",expand=True,padx=6)
        # Right tasks area
        right=tk.Frame(self.tf,bg="#0f1117"); right.pack(side="left",fill="both",expand=True)
        # Table header
        th=tk.Frame(right,bg="#13151e",height=28); th.pack(fill="x"); th.pack_propagate(False)
        for t in ["№","Файл / Скважина","","Длина","Сумма","Масштаб","Дата"]:
            tk.Label(th,text=t,bg="#13151e",fg="#4a5580",
                     font=("Segoe UI",8,"bold")).pack(side="left",padx=6)
        # Scrollable list
        wrap=tk.Frame(right,bg="#0f1117"); wrap.pack(fill="both",expand=True)
        c=tk.Canvas(wrap,bg="#0f1117",highlightthickness=0)
        sb=ttk.Scrollbar(wrap,orient="vertical",command=c.yview)
        c.configure(yscrollcommand=sb.set); sb.pack(side="right",fill="y"); c.pack(side="left",fill="both",expand=True)
        self.ti=tk.Frame(c,bg="#0f1117"); cw=c.create_window(0,0,anchor="nw",window=self.ti)
        self.ti.bind("<Configure>",lambda e:c.configure(scrollregion=c.bbox("all")))
        c.bind("<Configure>",lambda e:c.itemconfig(cw,width=e.width))
        c.bind("<MouseWheel>",lambda e:c.yview_scroll(-1*(e.delta//120),"units"))
        self._tc=c
        # Bottom bar
        bot=tk.Frame(right,bg="#13151e",height=52); bot.pack(fill="x",side="bottom"); bot.pack_propagate(False)
        self._btn(bot,"＋ Файл",self._add_task,fg="#7b8fff",bg="#1c2035",padx=12,pady=8,
                  font=("Segoe UI",9,"bold")).pack(side="left",padx=(12,4),pady=8)
        self._btn(bot,"📁 Папку",self._add_folder,fg="#4dc87a",bg="#1a2a1a",padx=12,pady=8,
                  font=("Segoe UI",9,"bold")).pack(side="left",padx=(0,8),pady=8)
        self._btn(bot,"🗑 Удалить",self._del_task,fg="#e05555",bg="#2a1515",padx=10,pady=8
                  ).pack(side="left",pady=8)
        # ── Поиск ─────────────────────────────────────────────────────────────
        tk.Frame(bot,bg="#252d45",width=1).pack(side="left",fill="y",padx=10,pady=6)
        search_wrap=tk.Frame(bot,bg="#0d0f18",bd=1,relief="flat")
        search_wrap.pack(side="left",pady=8)
        tk.Label(search_wrap,text=" 🔍",bg="#0d0f18",fg="#5b8ef0",
                 font=("Segoe UI",9)).pack(side="left")
        search_entry=tk.Entry(search_wrap,textvariable=self._search_var,
                              bg="#0d0f18",fg="#e2e6f0",insertbackground="#5b8ef0",
                              relief="flat",font=("Segoe UI",9),width=15,bd=0)
        search_entry.pack(side="left",ipady=5,padx=(0,4))
        self._search_var.trace_add("write",lambda *a:self._refresh_tasks())
        tk.Button(search_wrap,text="×",command=lambda:self._search_var.set(""),
                  bg="#0d0f18",fg="#4a5578",bd=0,relief="flat",
                  font=("Segoe UI",11),cursor="hand2",
                  activebackground="#0d0f18",activeforeground="#e05555"
                  ).pack(side="left",padx=(0,4))
        # ── Сортировка ────────────────────────────────────────────────────────
        tk.Frame(bot,bg="#252d45",width=1).pack(side="left",fill="y",padx=10,pady=6)
        sort_wrap=tk.Frame(bot,bg="#13151e"); sort_wrap.pack(side="left",pady=8)
        tk.Label(sort_wrap,text="Сортировка:",bg="#13151e",fg="#4a5578",
                 font=("Segoe UI",8)).pack(side="left",padx=(0,6))
        # Кнопки сортировки вместо комбобокса
        for lbl,val,icon in [("Дата","дата","📅"),("Имя","имя","🔤"),
                               ("Длина","длина","📏"),("Сумма","сумма","💰")]:
            def make_sort_btn(v=val):
                def cmd():
                    if self._sort_var.get()==v:
                        self._sort_rev.set(not self._sort_rev.get())
                    else:
                        self._sort_var.set(v)
                        self._sort_rev.set(False)
                    self._refresh_tasks()
                return cmd
            sb=tk.Button(sort_wrap,text=f"{icon} {lbl}",
                         command=make_sort_btn(),
                         bg="#1e2233",fg="#6b7599",
                         activebackground="#252d45",activeforeground="#5b8ef0",
                         bd=0,relief="flat",padx=8,pady=4,
                         font=("Segoe UI",8),cursor="hand2")
            sb.pack(side="left",padx=2)
            # Подсветить активный
            def _upd_btn(b=sb,v=val):
                active=self._sort_var.get()==v
                arr="↑" if (active and not self._sort_rev.get()) else "↓" if (active and self._sort_rev.get()) else ""
                b.configure(bg="#1c2a4a" if active else "#1e2233",
                            fg="#5b8ef0" if active else "#6b7599")
            self._sort_btns=getattr(self,"_sort_btns",[])+[(sb,val,_upd_btn)]
        stats=tk.Frame(bot,bg="#13151e"); stats.pack(side="right",padx=16,pady=4)
        r1=tk.Frame(stats,bg="#13151e"); r1.pack(anchor="e")
        tk.Label(r1,text="Итого:",bg="#13151e",fg="#6b7599",font=("Segoe UI",9)).pack(side="left",padx=(0,6))
        self.tot_lbl=tk.Label(r1,text="—",bg="#13151e",fg="#4dc87a",font=("Segoe UI",12,"bold"))
        self.tot_lbl.pack(side="left")
        self.st_lbl=tk.Label(stats,text="",bg="#13151e",fg="#3d4a6a",font=("Segoe UI",8))
        self.st_lbl.pack(anchor="e")

    def _build_analytics(self):
        self.af=tk.Frame(self.cf,bg="#0f1117")
        # Заголовок + переключатель метрик
        hdr=tk.Frame(self.af,bg="#0f1117"); hdr.pack(fill="x",padx=16,pady=(14,0))
        tk.Label(hdr,text="Аналитика",bg="#0f1117",fg="#e2e6f0",
                 font=("Segoe UI",13,"bold")).pack(side="left")
        # Переключатель метрики
        mf=tk.Frame(hdr,bg="#0f1117"); mf.pack(side="right")
        tk.Label(mf,text="Метрика:",bg="#0f1117",fg="#4a5580",
                 font=("Segoe UI",9)).pack(side="left",padx=(0,8))
        self.metric_var=tk.StringVar(value="сом")
        for label,val in [("Задачи","задачи"),("Футы","футы"),("Сомы","сом")]:
            tk.Radiobutton(mf,text=label,variable=self.metric_var,value=val,
                          bg="#0f1117",fg="#8b93a8",selectcolor="#1e2233",
                          activebackground="#0f1117",
                          font=("Segoe UI",9),cursor="hand2",
                          command=self._redraw_all
                          ).pack(side="left",padx=4)

        charts_top=tk.Frame(self.af,bg="#0f1117")
        charts_top.pack(fill="both",expand=True,padx=16,pady=(8,4))
        # Bars — по пользователям
        lc_frame=tk.Frame(charts_top,bg="#13161f")
        lc_frame.pack(side="left",fill="both",expand=True,padx=(0,6))
        self.bars_title=tk.Label(lc_frame,text="По пользователям",bg="#13161f",fg="#8b93a8",
                 font=("Segoe UI",9,"bold")); self.bars_title.pack(anchor="w",padx=12,pady=(10,6))
        self.bc=tk.Canvas(lc_frame,bg="#13161f",highlightthickness=0)
        self.bc.pack(fill="both",expand=True,padx=8,pady=(0,10))
        self.bc.bind("<Configure>",lambda e:self._draw_bars())
        # Line — по месяцам
        rc_frame=tk.Frame(charts_top,bg="#13161f")
        rc_frame.pack(side="left",fill="both",expand=True)
        self.line_title=tk.Label(rc_frame,text="По месяцам",bg="#13161f",fg="#8b93a8",
                 font=("Segoe UI",9,"bold")); self.line_title.pack(anchor="w",padx=12,pady=(10,6))
        self.lc=tk.Canvas(rc_frame,bg="#13161f",highlightthickness=0)
        self.lc.pack(fill="both",expand=True,padx=8,pady=(0,10))
        self.lc.bind("<Configure>",lambda e:self._draw_line())

        # По дням — нижний широкий график
        day_frame=tk.Frame(self.af,bg="#13161f")
        day_frame.pack(fill="x",padx=16,pady=(0,16))
        dh=tk.Frame(day_frame,bg="#13161f"); dh.pack(fill="x",padx=12,pady=(10,6))
        self.day_title=tk.Label(dh,text="По дням",bg="#13161f",fg="#8b93a8",
                 font=("Segoe UI",9,"bold")); self.day_title.pack(side="left")
        # Фильтр по профилю
        tk.Label(dh,text="Профиль:",bg="#13161f",fg="#4a5580",
                 font=("Segoe UI",8)).pack(side="right",padx=(0,4))
        self.day_profile_var=tk.StringVar(value="Все")
        self.day_profile_cb=ttk.Combobox(dh,textvariable=self.day_profile_var,
                                          state="readonly",width=12,
                                          font=("Segoe UI",9))
        self.day_profile_cb.pack(side="right",padx=(0,8))
        self.day_profile_cb.bind("<<ComboboxSelected>>",lambda e:self._draw_days())
        self.dc=tk.Canvas(day_frame,bg="#13161f",highlightthickness=0,height=120)
        self.dc.pack(fill="x",padx=8,pady=(0,10))
        self.dc.bind("<Configure>",lambda e:self._draw_days())

    def _redraw_all(self):
        self._update_metric_titles()
        self._draw_bars(); self._draw_line(); self._draw_days()

    def _update_metric_titles(self):
        m=self.metric_var.get()
        labels={"сом":"сом","футы":"ft","задачи":"шт"}
        u=labels.get(m,m)
        self.bars_title.configure(text=f"По пользователям ({u})")
        self.line_title.configure(text=f"По месяцам ({u})")
        self.day_title.configure(text=f"По дням ({u})")

    def _metric_val(self,task):
        m=self.metric_var.get()
        if m=="задачи": return 1
        if m=="футы": return task.get("total_sum",0)
        s=task.get("scale","A")
        return task.get("total_sum",0)*(FACTOR_A if s=="A" else FACTOR_B)

    def _profile_total_metric(self,name):
        total=0.0; p=self._profiles.get(name,{})
        tasks=[]
        if isinstance(p,list): tasks=p
        else:
            for mt in p.values():
                if isinstance(mt,list): tasks.extend(mt)
        for t in tasks: total+=self._metric_val(t)
        return total

    def _monthly_data_metric(self,name):
        p=self._profiles.get(name,{}); res={}
        if isinstance(p,dict):
            for m,tasks in p.items():
                if isinstance(tasks,list):
                    res[m]=sum(self._metric_val(t) for t in tasks)
        return res

    def _daily_data(self):
        """Собирает данные по дням из всех профилей или выбранного."""
        sel=self.day_profile_var.get() if hasattr(self,"day_profile_var") else "Все"
        names=list(self._profiles.keys()) if sel=="Все" else ([sel] if sel in self._profiles else [])
        day_totals={}  # "дд.мм.гггг" -> {profile->val}
        for name in names:
            p=self._profiles.get(name,{})
            tasks=[]
            if isinstance(p,list): tasks=p
            else:
                for mt in p.values():
                    if isinstance(mt,list): tasks.extend(mt)
            for t in tasks:
                added=t.get("added","")
                if added:
                    day=added.split()[0] if " " in added else added
                    if day not in day_totals: day_totals[day]={}
                    day_totals[day][name]=day_totals[day].get(name,0)+self._metric_val(t)
        return day_totals

    def _draw_days(self):
        """График по дням — плавные кривые с анимацией для каждого профиля."""
        c=self.dc; c.delete("all"); W=c.winfo_width(); H=c.winfo_height()
        if W<10 or H<10: return
        # Обновляем комбобокс профилей
        if hasattr(self,"day_profile_cb"):
            opts=["Все"]+list(self._profiles.keys())
            self.day_profile_cb["values"]=opts
            if self.day_profile_var.get() not in opts:
                self.day_profile_var.set("Все")
        day_data=self._daily_data()
        if not day_data:
            c.create_text(W//2,H//2,text="Нет данных с датами",
                         fill="#3d4a6a",font=("Segoe UI",9)); return

        def dkey(d):
            try: p=d.split("."); return (int(p[2]),int(p[1]),int(p[0]))
            except: return (0,0,0)
        days=sorted(day_data.keys(),key=dkey)
        profiles=list(self._profiles.keys())
        sel=self.day_profile_var.get() if hasattr(self,"day_profile_var") else "Все"
        draw_profiles=profiles if sel=="Все" else ([sel] if sel in profiles else profiles)

        # Максимум по всем профилям
        mx=0
        for d in days:
            for pn in draw_profiles:
                mx=max(mx,day_data[d].get(pn,0))
        mx=mx or 1

        pl,pr,pt,pb=55,16,16,32; cw=W-pl-pr; ch=H-pt-pb
        n=len(days)
        if n==0: return
        prog=self._ease(self._anim_prog)

        # Сетка горизонтальная
        for i in range(4):
            y=pt+ch*i//3
            c.create_line(pl,y,W-pr,y,fill="#1a1e30",width=1)
            c.create_text(pl-4,y,text=f"{mx*(3-i)/3:,.0f}",
                         fill="#4a5580",font=("Segoe UI",7),anchor="e")

        # Вертикальные метки дат
        step=max(1,n//12)
        for j,day in enumerate(days):
            if j%step==0:
                x=pl+j*cw//(n-1) if n>1 else pl+cw//2
                c.create_line(x,pt,x,pt+ch,fill="#14172a",width=1,dash=(2,6))
                c.create_text(x,pt+ch+14,text=day[:5],
                             fill="#4a5580",font=("Segoe UI",7),anchor="center")

        # Кривые для каждого профиля
        for pi,pname in enumerate(draw_profiles):
            color=self._get_profile_color(pname)
            pts=[]
            for j,day in enumerate(days):
                val=day_data[day].get(pname,0)
                x=pl+j*cw//(n-1) if n>1 else pl+cw//2
                y=pt+ch-int(ch*(val/mx))
                pts.append((x,y,val))

            # Рисуем только до прогресса анимации
            n_draw=max(2,int(len(pts)*prog))
            draw=pts[:n_draw]
            if len(draw)<2: continue

            # Закрашенная область под кривой (полупрозрачная — через stipple)
            fill_coords=[pl,pt+ch]
            for x,y,v in draw: fill_coords.extend([x,y])
            fill_coords.extend([draw[-1][0],pt+ch])
            if len(fill_coords)>=6:
                c.create_polygon(*fill_coords,fill=color,outline="",
                                stipple="gray25")

            # Плавная кривая через сглаживание
            if len(draw)>=2:
                # Catmull-Rom сплайн через промежуточные точки
                smooth_pts=[]
                for i in range(len(draw)):
                    x,y,v=draw[i]
                    if i==0: smooth_pts.extend([x,y])
                    else:
                        px,py,_=draw[i-1]
                        # Контрольные точки для сглаживания
                        cx1=px+(x-px)*0.5
                        smooth_pts.extend([cx1,py,cx1,y,x,y])

                # Рисуем основную линию
                coords=[]
                for x,y,v in draw: coords.extend([x,y])
                c.create_line(*coords,fill=color,width=2,smooth=True,
                             splinesteps=20)

            # Точки на данных
            for x,y,val in draw:
                if val>0:
                    c.create_oval(x-3,y-3,x+3,y+3,
                                 fill=color,outline="#0f1117",width=1)

            # Значения над точками (если немного данных)
            if n<=15:
                m=self.metric_var.get()
                for x,y,val in draw:
                    if val>0:
                        lbl=f"{val:,.0f}" if m!="задачи" else str(int(val))
                        c.create_text(x,y-10,text=lbl,fill=color,
                                     font=("Segoe UI",7),anchor="s")

            # Имя профиля на последней точке
            if draw:
                lx,ly,lv=draw[-1]
                c.create_text(lx+6,ly,text=pname,fill=color,
                             font=("Segoe UI",8,"bold"),anchor="w")

        # Ось Y
        c.create_line(pl,pt,pl,pt+ch,fill="#2a3560",width=1)

    def _switch(self,view):
        self._view=view; self.tf.pack_forget(); self.af.pack_forget()
        if view=="tasks":
            self.tf.pack(fill="both",expand=True)
            self.btn_tasks.configure(bg="#1e2233",fg="#5b8ef0",font=("Segoe UI",9,"bold"))
            self.btn_an.configure(bg="#0d0f18",fg="#4a5580",font=("Segoe UI",9))
        else:
            self.af.pack(fill="both",expand=True)
            self.btn_an.configure(bg="#1e2233",fg="#5b8ef0",font=("Segoe UI",9,"bold"))
            self.btn_tasks.configure(bg="#0d0f18",fg="#4a5580",font=("Segoe UI",9))
            self._start_anim()

    def _profile_total(self,name):
        total=0.0; p=self._profiles.get(name,{})
        tasks=[]
        if isinstance(p,list): tasks=p
        else:
            for mt in p.values():
                if isinstance(mt,list): tasks.extend(mt)
        for t in tasks:
            total+=t.get("total_sum",0)*(FACTOR_A if t.get("scale","A")=="A" else FACTOR_B)
        return total

    def _monthly_data(self,name):
        p=self._profiles.get(name,{}); res={}
        if isinstance(p,dict):
            for m,tasks in p.items():
                if isinstance(tasks,list):
                    res[m]=sum(t.get("total_sum",0)*(FACTOR_A if t.get("scale","A")=="A" else FACTOR_B) for t in tasks)
        return res

    def _start_anim(self):
        if self._anim_job: self.after_cancel(self._anim_job)
        self._anim_prog=0.0
        if hasattr(self,"metric_var"): self._update_metric_titles()
        self._animate()

    def _animate(self):
        self._anim_prog=min(1.0,self._anim_prog+0.05)
        self._draw_bars(); self._draw_line(); self._draw_days()
        if self._anim_prog<1.0: self._anim_job=self.after(16,self._animate)

    def _ease(self,t): return 1-(1-t)**3

    def _draw_bars(self):
        c=self.bc; c.delete("all"); W=c.winfo_width(); H=c.winfo_height()
        if W<10 or H<10: return
        names=list(self._profiles.keys())
        if not names:
            c.create_text(W//2,H//2,text="Нет данных",fill="#3d4a6a",font=("Segoe UI",11)); return
        totals={n:self._profile_total_metric(n) for n in names}
        mx=max(totals.values()) if totals else 1; mx=mx or 1
        pl,pr,pt,pb=55,20,20,40; cw=W-pl-pr; ch=H-pt-pb
        for i in range(5):
            y=pt+ch*i//4; c.create_line(pl,y,W-pr,y,fill="#1e2233",width=1)
            c.create_text(pl-4,y,text=f"{mx*(4-i)/4:,.0f}",fill="#4a5580",font=("Segoe UI",7),anchor="e")
        bw=min(60,cw//max(len(names),1)-16); prog=self._ease(self._anim_prog)
        for i,name in enumerate(names):
            xc=pl+(i+0.5)*cw//len(names); val=totals.get(name,0)
            bh=int(ch*(val/mx)*prog); x1=xc-bw//2; x2=xc+bw//2; y1=pt+ch-bh; y2=pt+ch
            color=self._get_profile_color(name)
            c.create_rectangle(x1+3,y1+3,x2+3,y2,fill="#0a0c14",outline="")
            c.create_rectangle(x1,y1,x2,y2,fill=color,outline="")
            if bh>20: c.create_text(xc,y1-4,text=f"{val:,.0f}",fill=color,font=("Segoe UI",7,"bold"),anchor="s")
            c.create_text(xc,y2+14,text=name[:10],fill="#8b93a8",font=("Segoe UI",8),anchor="center")
        c.create_line(pl,pt,pl,pt+ch,fill="#2a3560",width=1)

    def _mkey(self,m):
        p=m.split()
        if len(p)==2:
            try: return (int(p[1]),MONTHS_RU.index(p[0]) if p[0] in MONTHS_RU else 0)
            except: pass
        return (0,0)

    def _draw_line(self):
        c=self.lc; c.delete("all"); W=c.winfo_width(); H=c.winfo_height()
        if W<10 or H<10: return
        names=list(self._profiles.keys())
        if not names:
            c.create_text(W//2,H//2,text="Нет данных",fill="#3d4a6a",font=("Segoe UI",11)); return
        all_months=set()
        for n in names: all_months.update(self._monthly_data_metric(n).keys())
        if not all_months:
            c.create_text(W//2,H//2,text="Нет данных по месяцам",fill="#3d4a6a",font=("Segoe UI",11)); return
        months=sorted(all_months,key=self._mkey)
        mx=0
        for n in names:
            md=self._monthly_data(n)
            for v in md.values(): mx=max(mx,v)
        mx=mx or 1
        pl,pr,pt,pb=55,16,20,55; cw=W-pl-pr; ch=H-pt-pb; nm=max(len(months),1)
        for i in range(5):
            y=pt+ch*i//4; c.create_line(pl,y,W-pr,y,fill="#1e2233",width=1)
            c.create_text(pl-4,y,text=f"{mx*(4-i)/4:,.0f}",fill="#4a5580",font=("Segoe UI",7),anchor="e")
        prog=self._ease(self._anim_prog)
        for pi,name in enumerate(names):
            md=self._monthly_data_metric(name); color=self._get_profile_color(name); pts=[]
            for j,m in enumerate(months):
                val=md.get(m,0)
                x=pl+j*cw//(nm-1) if nm>1 else pl+cw//2
                y=pt+ch-int(ch*(val/mx)); pts.append((x,y,val))
            ndraw=max(1,int(len(pts)*prog*2)); draw=pts[:min(ndraw,len(pts))]
            if len(draw)>=2:
                coords=[]
                for x,y,v in draw: coords.extend([x,y])
                c.create_line(*coords,fill=color,width=2,smooth=True)
            for x,y,val in draw:
                c.create_oval(x-4,y-4,x+4,y+4,fill=color,outline="#0f1117",width=2)
                if val>0: c.create_text(x,y-10,text=f"{val:,.0f}",fill=color,font=("Segoe UI",7),anchor="s")
        # Legend
        lx=pl
        for pi,name in enumerate(names):
            color=self._get_profile_color(name)
            c.create_rectangle(lx,H-14,lx+12,H-4,fill=color,outline="")
            c.create_text(lx+16,H-9,text=name,fill="#8b93a8",font=("Segoe UI",8),anchor="w")
            lx+=len(name)*7+28

    def _refresh_profiles(self):
        for w in self.ptabs.winfo_children(): w.destroy()
        for i,name in enumerate(sorted(self._profiles.keys())):
            active=(name==self._cur_profile)
            color=self._get_profile_color(name)
            grp=tk.Frame(self.ptabs,bg="#0d0f18"); grp.pack(side="left",padx=(0,3),pady=6)
            tk.Button(grp,text=name,command=lambda n=name:self._sel_profile(n),
                      bg="#1e2233" if active else "#13151e",fg=color if active else "#6b7599",
                      activebackground="#1e2233",activeforeground=color,
                      bd=0,relief="flat",padx=12,pady=5,cursor="hand2",
                      font=("Segoe UI",9,"bold" if active else "normal")
                      ).pack(side="left")
            # Цветная точка — кликни чтобы изменить цвет
            dot=tk.Button(grp,text="●",command=lambda n=name:self._pick_profile_color(n),
                      bg="#0d0f18",fg=color,
                      activebackground="#1e2233",activeforeground=color,
                      bd=0,relief="flat",padx=2,pady=5,cursor="hand2",
                      font=("Segoe UI",10))
            dot.pack(side="left")

    def _new_profile(self):
        n=simpledialog.askstring("Новый профиль","Имя (Фарис, Алишер...):")
        if not n or not n.strip(): return
        n=n.strip()
        if n in self._profiles: messagebox.showwarning("","Уже существует"); return
        self._profiles[n]={}; save_profiles(self._profiles); self._sel_profile(n)

    def _del_profile(self):
        if not self._cur_profile: messagebox.showwarning("","Выбери профиль"); return
        if not messagebox.askyesno("Удалить?",f"Удалить «{self._cur_profile}» со всеми данными?"): return
        del self._profiles[self._cur_profile]; save_profiles(self._profiles)
        self._cur_profile=None; self._cur_month=None
        self._refresh_profiles(); self._refresh_months(); self._refresh_tasks()

    def _sel_profile(self,name):
        self._cur_profile=name; self._cur_month=None; self._sel_row=None; self._svars={}
        p=self._profiles.get(name,{})
        if isinstance(p,list):
            now=datetime.datetime.now()
            mn=f"{MONTHS_RU[now.month-1]} {now.year}"
            self._profiles[name]={mn:p}; save_profiles(self._profiles)
        self._refresh_profiles(); self._refresh_months(); self._refresh_tasks()

    def _refresh_months(self):
        for w in self.months_panel.winfo_children(): w.destroy()
        if not self._cur_profile: return
        p=self._profiles.get(self._cur_profile,{})
        if not isinstance(p,dict): return
        for m in sorted(p.keys(),key=self._mkey):
            tasks=p.get(m,[]); n=len(tasks) if isinstance(tasks,list) else 0
            active=(m==self._cur_month)
            tk.Button(self.months_panel,text=f"{m}  ({n})",
                      command=lambda mn=m:self._sel_month(mn),
                      bg="#1e2644" if active else "#0f1117",
                      fg="#5b8ef0" if active else "#6b7599",
                      activebackground="#1e2644",bd=0,relief="flat",
                      padx=8,pady=6,cursor="hand2",anchor="w",
                      font=("Segoe UI",9,"bold" if active else "normal")
                      ).pack(fill="x",pady=1)

    def _new_month(self):
        if not self._cur_profile: messagebox.showwarning("","Выбери профиль"); return
        now=datetime.datetime.now()
        default=f"{MONTHS_RU[now.month-1]} {now.year}"
        n=simpledialog.askstring("Новый месяц","Название:",initialvalue=default)
        if not n or not n.strip(): return
        n=n.strip(); p=self._profiles.get(self._cur_profile,{})
        if not isinstance(p,dict): p={}; self._profiles[self._cur_profile]=p
        if n in p: messagebox.showwarning("","Уже существует"); return
        p[n]=[]; save_profiles(self._profiles); self._sel_month(n)

    def _del_month(self):
        if not self._cur_month: messagebox.showwarning("","Выбери месяц"); return
        if not messagebox.askyesno("Удалить?",f"Удалить «{self._cur_month}» со всеми задачами?"): return
        p=self._profiles.get(self._cur_profile,{})
        if self._cur_month in p: del p[self._cur_month]
        save_profiles(self._profiles); self._cur_month=None
        self._refresh_months(); self._refresh_tasks()

    def _sel_month(self,m):
        self._cur_month=m; self._sel_row=None; self._svars={}
        self._refresh_months(); self._refresh_tasks()

    def _cur_tasks(self):
        if not self._cur_profile or not self._cur_month: return []
        p=self._profiles.get(self._cur_profile,{})
        return p.get(self._cur_month,[]) if isinstance(p,dict) else []

    def _check_dup(self,path):
        norm=os.path.normcase(os.path.abspath(path))
        for t in self._cur_tasks():
            try:
                if os.path.normcase(os.path.abspath(t.get("path",""))) == norm: return True
            except Exception: pass
        return False

    def _add_one(self,path):
        if self._check_dup(path): return "dup"
        try:
            info=parse_improj(path)
            info["scale"]=detect_scale(info.get("grids",[]))
            self._cur_tasks().append(info); return "ok"
        except Exception as e: return f"err:{e}"

    def _add_task(self):
        if not self._cur_profile: messagebox.showwarning("","Выбери профиль"); return
        if not self._cur_month: messagebox.showwarning("","Выбери или создай месяц"); return
        path=filedialog.askopenfilename(title="Открыть .improj",
            filetypes=[("IMPROJ","*.improj"),("All","*.*")])
        if not path: return
        r=self._add_one(path)
        if r=="dup": messagebox.showwarning("Дубль","Файл уже добавлен"); return
        if r.startswith("err:"): messagebox.showerror("Ошибка",r[4:]); return
        save_profiles(self._profiles); self._refresh_months(); self._refresh_tasks()

    def _add_folder(self):
        if not self._cur_profile: messagebox.showwarning("","Выбери профиль"); return
        if not self._cur_month: messagebox.showwarning("","Выбери или создай месяц"); return
        folder=filedialog.askdirectory(title="Выбери папку")
        if not folder: return
        found=[]
        for root,_,files in os.walk(folder):
            for f in files:
                if f.lower().endswith(".improj"): found.append(os.path.join(root,f))
        if not found: messagebox.showinfo("","Файлов .improj не найдено"); return
        added=dups=errors=0
        for path in found:
            r=self._add_one(path)
            if r=="ok": added+=1
            elif r=="dup": dups+=1
            else: errors+=1
        save_profiles(self._profiles); self._refresh_months(); self._refresh_tasks()
        msg=f"Найдено: {len(found)}  |  Добавлено: {added}"
        if dups: msg+=f"  |  Дублей: {dups}"
        if errors: msg+=f"  |  Ошибок: {errors}"
        messagebox.showinfo("Готово",msg)

    def _del_task(self):
        if self._sel_row is None: messagebox.showwarning("","Кликни на задачу"); return
        tasks=self._cur_tasks(); idx=self._sel_row
        if idx>=len(tasks): return
        if not messagebox.askyesno("Удалить?",f"Удалить «{tasks[idx]['filename']}»?"): return
        tasks.pop(idx); save_profiles(self._profiles)
        self._sel_row=None; self._refresh_months(); self._refresh_tasks()

    def _refresh_tasks(self):
        # Обновляем подсветку кнопок сортировки
        for btn,val,upd in getattr(self,"_sort_btns",[]):
            upd()
        for w in self.ti.winfo_children(): w.destroy()
        self._svars={}; tasks=self._cur_tasks()
        if not self._cur_profile:
            self._empty("← Создай или выбери профиль"); self._upd_tot([]); return
        if not self._cur_month:
            self._empty("← Выбери месяц"); self._upd_tot([]); return
        if not tasks:
            self._empty("Нет задач — нажми «＋ Файл»"); self._upd_tot([]); return
        # Фильтрация по поиску
        q = self._search_var.get().lower().strip() if hasattr(self,"_search_var") else ""
        if q:
            tasks = [t for t in tasks if
                     q in t.get("filename","").lower() or
                     q in t.get("well","").lower() or
                     q in t.get("api","").lower()]

        # Сортировка
        sort = self._sort_var.get() if hasattr(self,"_sort_var") else "дата"
        rev  = self._sort_rev.get() if hasattr(self,"_sort_rev") else False
        key_fn = {
            "дата":  lambda t: t.get("added",""),
            "имя":   lambda t: t.get("filename","").lower(),
            "длина": lambda t: t.get("total_sum",0),
            "сумма": lambda t: t.get("total_sum",0) * (
                FACTOR_A if t.get("scale","A")=="A" else FACTOR_B),
        }.get(sort, lambda t: t.get("added",""))
        tasks = sorted(tasks, key=key_fn, reverse=rev)

        for i,task in enumerate(tasks): self._make_row(i,task)
        self._upd_tot(tasks)

    def _empty(self,text):
        tk.Label(self.ti,text=text,bg="#0f1117",fg="#3d4a6a",
                 font=("Segoe UI",13)).pack(pady=60)

    def _make_row(self,idx,task):
        unit=task.get("unit","ft"); total=task.get("total_sum",0.0)
        sa=total*FACTOR_A; sb=total*FACTOR_B
        rbg="#13161f"; row=tk.Frame(self.ti,bg=rbg,cursor="hand2"); row.pack(fill="x",pady=1)
        auto=detect_scale(task.get("grids",[]))
        if "scale" not in task: task["scale"]=auto
        # Ключ = путь файла (не индекс!) — не съезжает при сортировке
        task_key = task.get("path") or task.get("filename","")
        sv=tk.StringVar(value=task["scale"]); self._svars[task_key]=sv

        def sel(e=None,r=row,i=idx):
            for w in self.ti.winfo_children():
                w.configure(bg="#13161f")
                for cc in w.winfo_children():
                    try: cc.configure(bg="#13161f")
                    except: pass
            r.configure(bg="#1e2644")
            for cc in r.winfo_children():
                try: cc.configure(bg="#1e2644")
                except: pass
            self._sel_row=i

        row.bind("<Button-1>",sel)
        def lbl(p,text,fg="#c5cce0",w=0,bold=False,anch="center"):
            l=tk.Label(p,text=text,bg=rbg,fg=fg,
                       font=("Segoe UI",10,"bold" if bold else "normal"),anchor=anch,width=w)
            l.bind("<Button-1>",lambda e:sel()); return l

        lbl(row,str(idx+1),fg="#4a5580",w=3).pack(side="left",padx=(8,4),pady=8)
        inf=tk.Frame(row,bg=rbg); inf.bind("<Button-1>",sel); inf.pack(side="left",fill="x",expand=True,padx=4)
        tk.Label(inf,text=task.get("filename","?"),bg=rbg,fg="#e2e6f0",
                 font=("Segoe UI",10,"bold"),anchor="w").pack(anchor="w")
        tk.Label(inf,text=task.get("well","—"),bg=rbg,fg="#6b7599",
                 font=("Segoe UI",8),anchor="w").pack(anchor="w")
        lbl(row,f"{total:,.1f} {unit}",fg="#4dc87a",bold=True,w=13).pack(side="left",padx=4)
        init_s=sa if task["scale"]=="A" else sb
        init_fg="#7b8fff" if task["scale"]=="A" else "#c084fc"
        sl=tk.Label(row,text=f"{init_s:,.0f} сом",bg=rbg,fg=init_fg,
                    font=("Segoe UI",10,"bold"),width=13,anchor="center")
        sl.pack(side="left",padx=4)
        at=f"авто: {'5:100' if auto=='A' else '1:100'}"
        ac="#7b8fff" if auto=="A" else "#c084fc"
        tk.Label(row,text=at,bg=rbg,fg=ac,font=("Segoe UI",8)).pack(side="left",padx=(4,2))
        rf=tk.Frame(row,bg=rbg); rf.pack(side="left",padx=4)
        ra=tk.Radiobutton(rf,text="5:100",variable=sv,value="A",bg=rbg,
                          selectcolor="#1c2035",activebackground=rbg,
                          font=("Segoe UI",9,"bold"),cursor="hand2"); ra.pack(side="left")
        rb=tk.Radiobutton(rf,text="1:100",variable=sv,value="B",bg=rbg,
                          selectcolor="#1c2035",activebackground=rbg,
                          font=("Segoe UI",9,"bold"),cursor="hand2"); rb.pack(side="left",padx=(6,0))

        def on_change(*a):
            v=sv.get(); s=sa if v=="A" else sb; fg="#7b8fff" if v=="A" else "#c084fc"
            sl.configure(text=f"{s:,.0f} сом",fg=fg)
            ra.configure(fg="#7b8fff" if v=="A" else "#3d4a6a")
            rb.configure(fg="#c084fc" if v=="B" else "#3d4a6a")
            tasks=self._cur_tasks()
            if idx<len(tasks): tasks[idx]["scale"]=v; save_profiles(self._profiles)
            self._recalc()

        def upd_colors(*a):
            v=sv.get()
            ra.configure(fg="#7b8fff" if v=="A" else "#3d4a6a",activeforeground="#7b8fff")
            rb.configure(fg="#c084fc" if v=="B" else "#3d4a6a",activeforeground="#c084fc")

        sv.trace_add("write",on_change); sv.trace_add("write",upd_colors); upd_colors()
        ra.configure(command=on_change); rb.configure(command=on_change)
        lbl(row,task.get("added","—"),fg="#4a5580",w=15).pack(side="left",padx=(4,12))

    def _recalc(self):
        tasks=self._cur_tasks(); ts=tf=0.0; unit="ft"
        for t in tasks:
            val=t.get("total_sum",0.0); tf+=val; unit=t.get("unit","ft")
            task_key=t.get("path") or t.get("filename","")
            sv=self._svars.get(task_key)
            ts+=val*(FACTOR_A if (not sv or sv.get()=="A") else FACTOR_B)
        if ts>0:
            self.tot_lbl.configure(text=f"{ts:,.0f} сом")
            avg=tf/len(tasks) if tasks else 0
            self.st_lbl.configure(
                text=f"Задач: {len(tasks)}  |  Длина: {tf:,.0f} {unit}  |  Среднее: {avg:,.0f} {unit}")
        else:
            self.tot_lbl.configure(text="—"); self.st_lbl.configure(text="")

    def _upd_tot(self,tasks): self._recalc()

    def _upd_path(self):
        pf=get_profiles_file(); home=os.path.expanduser("~")
        short=pf.replace(home,"~")
        if len(short)>40: short="..."+short[-37:]
        self.path_lbl.configure(text=short)

    def _shared_folder(self):
        win=tk.Toplevel(self); win.title("Общая папка"); win.geometry("520x220")
        win.configure(bg="#0f1117"); win.resizable(False,False)
        tk.Label(win,text="Где хранить данные?",bg="#0f1117",fg="#e2e6f0",
                 font=("Segoe UI",12,"bold")).pack(pady=(20,4))
        tk.Label(win,text="Укажи папку — туда сохранится improj_profiles.json",
                 bg="#0f1117",fg="#6b7599",font=("Segoe UI",9)).pack(pady=(0,12))
        path_var=tk.StringVar(value=get_profiles_file())
        pf=tk.Frame(win,bg="#0f1117"); pf.pack(fill="x",padx=20)
        tk.Label(pf,text="Путь:",bg="#0f1117",fg="#6b7599",font=("Segoe UI",9)).pack(side="left",padx=(0,6))
        tk.Entry(pf,textvariable=path_var,font=("Segoe UI",9),width=38).pack(side="left",fill="x",expand=True,ipady=6)
        def browse():
            folder=filedialog.askdirectory(title="Выбери папку")
            if folder: path_var.set(os.path.join(folder,"improj_profiles.json"))
        tk.Button(pf,text="📁",command=browse,bg="#1e2233",fg="#8b93a8",
                  bd=0,relief="flat",padx=10,pady=6,cursor="hand2").pack(side="left",padx=(4,0))
        def apply():
            np=path_var.get().strip().strip('"').strip("'")
            if not np.endswith(".json"): np=os.path.join(np,"improj_profiles.json")
            folder=os.path.dirname(np)
            try:
                if not os.path.isdir(folder): os.listdir(folder)
            except Exception:
                messagebox.showerror("Ошибка",f"Папка недоступна:\n{folder}"); return
            op=get_profiles_file(); save_settings(np)
            if op!=np and os.path.exists(op) and not os.path.exists(np):
                if messagebox.askyesno("Скопировать?","Скопировать существующие данные?"):
                    import shutil; shutil.copy2(op,np)
            self._profiles=load_profiles(); self._upd_path()
            self._refresh_profiles(); self._refresh_months(); self._refresh_tasks()
            win.destroy()
        br=tk.Frame(win,bg="#0f1117"); br.pack(fill="x",padx=20,pady=(16,0))
        self._btn(br,"✓ Применить",apply,fg="#4dc87a",bg="#1a2a1a",padx=14,pady=8,
                  font=("Segoe UI",10,"bold")).pack(side="left")
        self._btn(br,"Отмена",win.destroy,fg="#6b7599",bg="#1e2233",padx=12,pady=8).pack(side="left",padx=8)

    def _refresh_all(self):
        self._profiles=load_profiles(); self._refresh_profiles()
        self._refresh_months(); self._refresh_tasks()
        if self._view=="analytics": self._start_anim()

    def _on_resize(self, event):
        if event.widget == self and self._bg_image:
            self.after(100, self._draw_bg)

    def _auto_refresh(self):
        try:
            new=load_profiles()
            if json.dumps(new,sort_keys=True)!=json.dumps(self._profiles,sort_keys=True):
                self._profiles=new; self._refresh_profiles()
                self._refresh_months(); self._refresh_tasks()
        except Exception: pass
        self.after(30000,self._auto_refresh)

if __name__=="__main__":
    app=App(); app.mainloop()
