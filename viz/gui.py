"""
viz/gui.py - JapeAI proof assistant GUI.

Layout inspired by the Jape theorem prover (github.com/RBornat/jape):
  - Menu bar:  File | Proof | Examples
  - Toolbar:   inline assumptions / goal entry + Prove / Clear
  - Proof pane (top, white): numbered steps "n: formula   rule"
  - Given pane (bottom):     "Given" label + one button per hypothesis
"""

from __future__ import annotations

import sys
import os
import time
import threading

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import tkinter as tk
from tkinter import ttk, font as tkfont

from parser.parser import parse_formula
from csp.fol_csp import solve_fol_csp, render_fol_csp_steps
from planning.internal_planner import plan_forward
from cbn.logic_causal import solve_logic_causal, render_logic_causal_steps


# ---------------------------------------------------------------------------
# Colour scheme — modern light theme
# ---------------------------------------------------------------------------
BG_ROOT     = "#F0F2F5"
BG_TOOLBAR  = "#FFFFFF"
BG_PROOF    = "#FFFFFF"
BG_GIVEN    = "#F7F8FA"

C_TEXT      = "#1A1A2E"
C_RULE      = "#4F46E5"   # indigo – rule labels
C_HYP       = "#1B6B3A"   # green  – assumption labels
C_SCOPE     = "#7C3AED"   # violet – scope depth bars
C_STEPNUM   = "#9CA3AF"   # grey   – step numbers
C_ERROR     = "#DC2626"
C_SEP       = "#E5E7EB"
C_ACCENT    = "#4F46E5"   # indigo accent

C_BTN_PROVE_BG  = "#4F46E5"
C_BTN_PROVE_FG  = "#FFFFFF"
C_BTN_PROVE_ACT = "#3730A3"
C_BTN_2_BG      = "#F3F4F6"
C_BTN_2_FG      = "#374151"
C_BTN_2_ACT     = "#E5E7EB"
C_BTN_DIS_FG    = "#9CA3AF"

C_CAUSAL_BADGE  = "#0369A1"   # sky-blue accent for the "Causal" solver label

FONT_FORMULA  = ("Palatino Linotype", 14)
FONT_FORMULA_B= ("Palatino Linotype", 14, "bold")
FONT_RULE     = ("Segoe UI", 10)
FONT_STEPNUM  = ("Segoe UI", 10)
FONT_TOOLBAR  = ("Segoe UI", 10)
FONT_GIVEN_BTN= ("Palatino Linotype", 12)
FONT_TITLE    = ("Segoe UI", 11, "bold")
FONT_MONO     = ("Consolas", 10)

BTN_HYP_BG  = "#EEF2FF"
BTN_HYP_ACT = "#E0E7FF"

# ---------------------------------------------------------------------------
# Example problems
# ---------------------------------------------------------------------------
# Each entry is either:
#   (label, assumptions, goal)  — a loadable example
#   (section_title,)            — a disabled section header
#   None                        — a separator
EXAMPLES = [
    # ── Propositional ─────────────────────────────────────────────────────────
    ("Propositional",),
    ("P, P→Q  ⊢  Q",               ["P", "P→Q"],                          "Q"),
    ("P∧Q  ⊢  Q∧P",                ["P & Q"],                             "Q & P"),
    ("P, Q  ⊢  P∧Q",               ["P", "Q"],                            "P & Q"),
    ("⊢  P→P",                     [],                                    "P→P"),
    ("⊢  (P∧Q)→(Q∧P)",            [],                                    "(P & Q)→(Q & P)"),
    ("P  ⊢  Q→(P∧Q)",             ["P"],                                  "Q→(P & Q)"),
    # ── FOL Warm-up ───────────────────────────────────────────────────────────
    None,
    ("FOL — Warm-up",),
    ("∀y.(T(y)→Q(y)), ∀y.T(y)  ⊢  ∀y.Q(y)",
        ["∀y.(T(y)→Q(y))", "∀y.T(y)"],                                    "∀y.Q(y)"),
    # ── FOL Level 1 ───────────────────────────────────────────────────────────
    None,
    ("FOL: Level 1",),
    ("∀y.(T(y)→Q(y)∧R(y))  ⊢  ∀y.(T(y)→∃z.Q(z))",
        ["∀y.(T(y)→(Q(y)∧R(y)))"],                                        "∀y.(T(y)→∃z.Q(z))"),
    ("∃y.Q(y)∨∃z.S(z)  ⊢  ∃x.(S(x)∨Q(x))",
        ["∃y.Q(y)∨∃z.S(z)"],                                              "∃x.(S(x)∨Q(x))"),
    ("∃y.T(y), ∀y.(T(y)→R(y))  ⊢  ∃y.R(y)",
        ["∃y.T(y)", "∀y.(T(y)→R(y))"],                                    "∃y.R(y)"),
    # ── FOL Level 2 ───────────────────────────────────────────────────────────
    None,
    ("FOL: Level 2",),
    ("∀x.∀z.(¬Q(z)∧S(x))  ⊢  ¬∃x.∀z.(S(x)→Q(z))",
        ["∀x.∀z.(¬Q(z)∧S(x))"],                                           "¬∃x.∀z.(S(x)→Q(z))"),
    ("∃x.¬Q(x), ∀x.R(x)∨∀x.Q(x), ∀x.(R(x)→T(x))  ⊢  ∀x.T(x)",
        ["∃x.¬Q(x)", "∀x.R(x)∨∀x.Q(x)", "∀x.(R(x)→T(x))"],              "∀x.T(x)"),
    ("∀y.T(y)∨∀y.S(y), ∃y.¬T(y), ∀y.(S(y)→P(y))  ⊢  ∀y.P(y)",
        ["∀y.T(y)∨∀y.S(y)", "∃y.¬T(y)", "∀y.(S(y)→P(y))"],              "∀y.P(y)"),
    # ── FOL Level 3 ───────────────────────────────────────────────────────────
    None,
    ("FOL: Level 3",),
    ("¬∃x.(¬∃z.T(z)→Q(x))  ⊢  ∀x.¬(Q(x)∨∃z.T(z))",
        ["¬∃x.(¬∃z.T(z)→Q(x))"],                                          "∀x.¬(Q(x)∨∃z.T(z))"),
    ("∀z.¬(P(z)∨∃x.T(x))  ⊢  ¬∃z.(¬∃x.T(x)→P(z))",
        ["∀z.¬(P(z)∨∃x.T(x))"],                                           "¬∃z.(¬∃x.T(x)→P(z))"),
    ("∀y.∀z.(∃x.¬R(x)→(P(z)→¬Q(y)))  ⊢  ∀y.∀z.∀x.((P(z)∧Q(x))→R(z))",
        ["∀y.∀z.(∃x.¬R(x)→(P(z)→¬Q(y)))"],                               "∀y.∀z.∀x.((P(z)∧Q(x))→R(z))"),
    ("∀x.(P(x)→T(x))  ⊢  ∃x.P(x)→∃x.T(x)",
        ["∀x.(P(x)→T(x))"],                                                "∃x.P(x)→∃x.T(x)"),
    ("∃y.(Q(y)→T(y))∧∀y.((T(y)∧Q(y))∨Q(y))  ⊢  ∃y.(T(y)∧Q(y))",
        ["∃y.(Q(y)→T(y))∧∀y.((T(y)∧Q(y))∨Q(y))"],                        "∃y.(T(y)∧Q(y))"),
    ("∀y.¬(T(y)∨∃z.P(z))  ⊢  ¬∃y.(¬∃z.P(z)→T(y))",
        ["∀y.¬(T(y)∨∃z.P(z))"],                                           "¬∃y.(¬∃z.P(z)→T(y))"),
    # ── Causal / CBN (same Assumptions+Goal format as other solvers) ──────────
    None,
    ("Causal CBN",),
    ("P, P→Q, Q→R  ⊢  R  [CBN chain]",
        ["P", "P→Q", "Q→R"],                      "R"),
    ("P, P→Q, Q→R, R→S  ⊢  S  [long chain]",
        ["P", "P→Q", "Q→R", "R→S"],               "S"),
    ("P∧Q, (P∧Q)→R  ⊢  R  [and-elim + MP]",
        ["P & Q", "(P & Q)→R"],                    "R"),
    ("P, Q  ⊢  P∧Q  [and-intro]",
        ["P", "Q"],                                "P & Q"),
    ("P∧Q  ⊢  P  [and-elim]",
        ["P & Q"],                                 "P"),
]


def render_plan(plan: list[str], lines: list) -> None:
    for action in plan:
        lines.append((0, action, "action", None))




# ---------------------------------------------------------------------------
# Scrollable proof frame
# ---------------------------------------------------------------------------

class _ScrollableFrame(tk.Frame):
    """A vertically-scrollable container of child widgets."""

    def __init__(self, parent, bg: str, **kw):
        super().__init__(parent, bg=bg, **kw)

        self._canvas = tk.Canvas(self, bg=bg, highlightthickness=0, bd=0)
        self._scrollbar = ttk.Scrollbar(self, orient=tk.VERTICAL,
                                        command=self._canvas.yview)
        self._canvas.configure(yscrollcommand=self._scrollbar.set)

        self._scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self._canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.inner = tk.Frame(self._canvas, bg=bg)
        self._win_id = self._canvas.create_window(
            (0, 0), window=self.inner, anchor="nw"
        )

        self.inner.bind("<Configure>", self._on_inner_configure)
        self._canvas.bind("<Configure>", self._on_canvas_configure)

        # Mouse-wheel scrolling
        self._canvas.bind("<Enter>", self._bind_wheel)
        self._canvas.bind("<Leave>", self._unbind_wheel)

    def _on_inner_configure(self, _event=None):
        self._canvas.configure(scrollregion=self._canvas.bbox("all"))

    def _on_canvas_configure(self, event):
        self._canvas.itemconfig(self._win_id, width=event.width)

    def _bind_wheel(self, _event=None):
        self._canvas.bind_all("<MouseWheel>", self._on_wheel)

    def _unbind_wheel(self, _event=None):
        self._canvas.unbind_all("<MouseWheel>")

    def _on_wheel(self, event):
        self._canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

    def clear(self):
        for widget in self.inner.winfo_children():
            widget.destroy()

    def scroll_to_bottom(self):
        self._canvas.update_idletasks()
        self._canvas.yview_moveto(1.0)


# ---------------------------------------------------------------------------
# Main application
# ---------------------------------------------------------------------------

class JapeAIApp:

    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("JapeAI")
        self.root.geometry("1000x680")
        self.root.configure(bg=BG_ROOT)
        self.root.minsize(600, 420)

        # Taskbar icon
        _icon_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        try:
            self._icon = tk.PhotoImage(
                file=os.path.join(_icon_dir, "taskbar_icon.png"))
            self.root.wm_iconphoto(True, self._icon)
        except Exception:
            pass

        self._solver_var = tk.StringVar(value="csp")
        self._status_var = tk.StringVar(value="Enter a problem and press Prove.")
        self._last_proof_lines: list = []   # (depth, formula, rule, note) tuples
        self._last_sequent: str = ""
        self._causal_mode: bool = False     # True when "causal" solver is active

        self._build_menu()
        self._build_toolbar()
        self._build_main()

    # -----------------------------------------------------------------------
    # Menu bar  (File | Proof | Examples)
    # -----------------------------------------------------------------------

    def _build_menu(self) -> None:
        menubar = tk.Menu(self.root)

        # -- File ------------------------------------------------------------
        file_menu = tk.Menu(menubar, tearoff=False)
        file_menu.add_command(label="Copy Proof", command=self._on_copy,
                              accelerator="Ctrl+C")
        file_menu.add_command(label="Clear",  command=self._on_clear,
                              accelerator="Ctrl+L")
        file_menu.add_separator()
        file_menu.add_command(label="Quit",   command=self.root.destroy,
                              accelerator="Ctrl+Q")
        menubar.add_cascade(label="File", menu=file_menu)
        self.root.bind_all("<Control-c>", lambda _: self._on_copy())
        self.root.bind_all("<Control-l>", lambda _: self._on_clear())
        self.root.bind_all("<Control-q>", lambda _: self.root.destroy())

        # -- Proof -----------------------------------------------------------
        proof_menu = tk.Menu(menubar, tearoff=False)
        proof_menu.add_command(label="Prove",
                               command=self._on_prove,
                               accelerator="Ctrl+Return")
        proof_menu.add_separator()

        solver_menu = tk.Menu(proof_menu, tearoff=False)
        for label, value in [
            ("CSP  (forward + FOL)",        "csp"),
            ("PDDL planner  (forward BFS)", "pddl"),
            ("Bayes  (CBN / SCM)",          "causal"),
        ]:
            solver_menu.add_radiobutton(
                label=label, variable=self._solver_var, value=value,
                command=self._on_solver_change,
            )
        proof_menu.add_cascade(label="Solver", menu=solver_menu)
        menubar.add_cascade(label="Proof", menu=proof_menu)
        self.root.bind_all("<Control-Return>", lambda _: self._on_prove())

        # -- Examples --------------------------------------------------------
        ex_menu = tk.Menu(menubar, tearoff=False)
        for entry in EXAMPLES:
            if entry is None:
                ex_menu.add_separator()
            elif len(entry) == 1:
                # Section header — disabled label
                ex_menu.add_command(label=entry[0], state=tk.DISABLED)
            else:
                label, assumptions, goal = entry
                ex_menu.add_command(
                    label=label,
                    command=lambda a=assumptions, g=goal: self._load_example(a, g),
                )
        menubar.add_cascade(label="Examples", menu=ex_menu)

        self.root.configure(menu=menubar)

    # -----------------------------------------------------------------------
    # Toolbar  (assumptions | goal | Prove | Clear | status)
    # -----------------------------------------------------------------------

    # Keyboard substitution map: type these ASCII sequences → get Unicode symbols
    _SUBSTITUTIONS = [
        ("forall", "∀"), ("exists", "∃"),
        ("<->",    "↔"), ("->",    "→"),
        ("\\/",    "∨"), ("/\\",   "∧"),
        ("~",      "¬"), ("|-",    "⊢"),
    ]

    def _wire_substitutions(self, entry: tk.Entry) -> None:
        """Attach keyboard-substitution bindings to an Entry widget."""
        def _on_key(event, widget=entry):
            # After any key, scan for substitution sequences
            widget.after_idle(lambda: self._apply_substitutions(widget))
        entry.bind("<KeyRelease>", _on_key)

    def _apply_substitutions(self, entry: tk.Entry) -> None:
        text = entry.get()
        cursor = entry.index(tk.INSERT)
        changed = False
        for seq, sym in self._SUBSTITUTIONS:
            idx = text.find(seq)
            while idx != -1:
                text = text[:idx] + sym + text[idx + len(seq):]
                # Adjust cursor position
                if cursor > idx:
                    cursor = max(idx + len(sym),
                                 cursor - len(seq) + len(sym))
                changed = True
                idx = text.find(seq, idx + len(sym))
        if changed:
            entry.delete(0, tk.END)
            entry.insert(0, text)
            entry.icursor(min(cursor, len(text)))

    def _insert_symbol(self, symbol: str) -> None:
        """Insert *symbol* at the cursor position of the focused entry."""
        widget = self.root.focus_get()
        if isinstance(widget, tk.Entry):
            try:
                widget.insert(tk.INSERT, symbol)
            except tk.TclError:
                pass

    def _build_toolbar(self) -> None:
        tb = tk.Frame(self.root, bg=BG_TOOLBAR, bd=0)
        tb.pack(side=tk.TOP, fill=tk.X)
        tk.Frame(tb, bg=C_SEP, height=1).pack(side=tk.BOTTOM, fill=tk.X)

        # ── Row 1: Assumptions ⊢ Goal ────────────────────────────────────────
        # Both entries live on their own full-width row so they always
        # have space and are never squeezed out by buttons.
        row1 = tk.Frame(tb, bg=BG_TOOLBAR)
        row1.pack(fill=tk.X, padx=10, pady=(8, 4))
        row1.columnconfigure(1, weight=3, minsize=120)  # assumptions expands
        row1.columnconfigure(4, weight=1, minsize=80)   # goal expands less

        self._lbl_assumptions = tk.Label(row1, text="Assumptions:", font=FONT_TOOLBAR,
                 bg=BG_TOOLBAR, fg=C_STEPNUM)
        self._lbl_assumptions.grid(row=0, column=0, sticky="w", padx=(0, 4))
        self._assumptions_entry = tk.Entry(
            row1, font=FONT_MONO,
            relief=tk.SOLID, bd=1,
            highlightthickness=1, highlightcolor=C_ACCENT,
            highlightbackground=C_SEP,
        )
        self._assumptions_entry.grid(row=0, column=1, sticky="ew", padx=(0, 6))
        self._assumptions_entry.bind("<Return>", lambda _: self._on_prove())
        self._wire_substitutions(self._assumptions_entry)

        tk.Label(row1, text="⊢", font=("Palatino Linotype", 15),
                 bg=BG_TOOLBAR, fg=C_SCOPE).grid(row=0, column=2, padx=4)

        self._lbl_goal = tk.Label(row1, text="Goal:", font=FONT_TOOLBAR,
                 bg=BG_TOOLBAR, fg=C_STEPNUM)
        self._lbl_goal.grid(row=0, column=3, sticky="w", padx=(0, 4))
        self._goal_entry = tk.Entry(
            row1, font=FONT_MONO,
            relief=tk.SOLID, bd=1,
            highlightthickness=1, highlightcolor=C_ACCENT,
            highlightbackground=C_SEP,
        )
        self._goal_entry.grid(row=0, column=4, sticky="ew")
        self._goal_entry.bind("<Return>", lambda _: self._on_prove())
        self._wire_substitutions(self._goal_entry)

        # ── Row 2: buttons + solver + status ────────────────────────────────
        # Buttons are on their own row — they never compete with entries.
        row2 = tk.Frame(tb, bg=BG_TOOLBAR)
        row2.pack(fill=tk.X, padx=10, pady=(0, 5))

        self._prove_btn = tk.Button(
            row2, text="Prove", font=("Segoe UI", 10, "bold"),
            bg=C_BTN_PROVE_BG, fg=C_BTN_PROVE_FG,
            activebackground=C_BTN_PROVE_ACT, activeforeground=C_BTN_PROVE_FG,
            relief=tk.FLAT, padx=14, pady=3,
            cursor="hand2", command=self._on_prove,
        )
        self._prove_btn.pack(side=tk.LEFT, padx=(0, 4))

        tk.Button(
            row2, text="Clear", font=FONT_TOOLBAR,
            bg=C_BTN_2_BG, fg=C_BTN_2_FG,
            activebackground=C_BTN_2_ACT,
            relief=tk.FLAT, padx=10, pady=3,
            cursor="hand2", command=self._on_clear,
        ).pack(side=tk.LEFT, padx=(0, 3))

        self._copy_btn = tk.Button(
            row2, text="Copy", font=FONT_TOOLBAR,
            bg=C_BTN_2_BG, fg=C_BTN_DIS_FG,
            activebackground=C_BTN_2_ACT, activeforeground=C_BTN_2_FG,
            relief=tk.FLAT, padx=10, pady=3,
            cursor="hand2", command=self._on_copy, state=tk.DISABLED,
        )
        self._copy_btn.pack(side=tk.LEFT, padx=(0, 10))

        ttk.Separator(row2, orient=tk.VERTICAL).pack(
            side=tk.LEFT, fill=tk.Y, pady=3, padx=(0, 8))

        solver_frame = tk.Frame(row2, bg=BG_TOOLBAR)
        solver_frame.pack(side=tk.LEFT)
        for label, value in [("CSP", "csp"), ("PDDL", "pddl"), ("Bayes", "causal")]:
            tk.Radiobutton(
                solver_frame, text=label, variable=self._solver_var,
                value=value, font=FONT_TOOLBAR, bg=BG_TOOLBAR,
                fg=C_TEXT, selectcolor=BG_TOOLBAR,
                activebackground=BG_TOOLBAR,
                command=self._on_solver_change,
            ).pack(side=tk.LEFT, padx=4)

        self._status_label = tk.Label(
            row2, textvariable=self._status_var,
            font=FONT_TOOLBAR, bg=BG_TOOLBAR, fg=C_STEPNUM, anchor="w",
        )
        self._status_label.pack(side=tk.LEFT, padx=(12, 0))

        # ── Row 3: symbol palette ────────────────────────────────────────────
        row3 = tk.Frame(tb, bg=BG_TOOLBAR)
        row3.pack(fill=tk.X, padx=10, pady=(0, 7))

        tk.Label(row3, text="Insert:", font=FONT_TOOLBAR,
                 bg=BG_TOOLBAR, fg=C_STEPNUM).pack(side=tk.LEFT, padx=(0, 4))

        SYMBOLS = [
            ("∀", "∀"), ("∃", "∃"), ("¬", "¬"),
            ("∧", "∧"), ("∨", "∨"), ("→", "→"), ("↔", "↔"),
        ]
        for display, sym in SYMBOLS:
            tk.Button(
                row3, text=display,
                font=("Palatino Linotype", 12),
                bg=BTN_HYP_BG, fg=C_SCOPE,
                activebackground=BTN_HYP_ACT,
                relief=tk.FLAT, bd=0,
                padx=7, pady=1,
                cursor="hand2",
                command=lambda s=sym: self._insert_symbol(s),
            ).pack(side=tk.LEFT, padx=1)

    # -----------------------------------------------------------------------
    # Main area  (proof pane + given pane, PanedWindow)
    # -----------------------------------------------------------------------

    def _build_main(self) -> None:
        paned = tk.PanedWindow(
            self.root, orient=tk.VERTICAL, bg=C_SEP,
            sashwidth=4, sashrelief=tk.FLAT, sashpad=0,
        )
        paned.pack(fill=tk.BOTH, expand=True)

        # -- Proof pane (top) ------------------------------------------------
        proof_outer = tk.Frame(paned, bg=BG_PROOF)
        paned.add(proof_outer, stretch="always", minsize=260)

        self._proof_header = tk.Label(
            proof_outer, text="Proof",
            font=("Segoe UI", 9, "bold"),
            bg=BG_ROOT, fg=C_STEPNUM, anchor="w",
            padx=12, pady=4,
        )
        self._proof_header.pack(fill=tk.X)
        tk.Frame(proof_outer, bg=C_SEP, height=1).pack(fill=tk.X)

        self._proof_scroll = _ScrollableFrame(proof_outer, bg=BG_PROOF)
        self._proof_scroll.pack(fill=tk.BOTH, expand=True)

        # -- Given pane (bottom) ---------------------------------------------
        given_outer = tk.Frame(paned, bg=BG_GIVEN)
        paned.add(given_outer, stretch="never", minsize=72)

        tk.Frame(given_outer, bg=C_SEP, height=1).pack(fill=tk.X)

        tk.Label(
            given_outer, text="Given",
            font=("Segoe UI", 9, "bold"),
            bg=BG_ROOT, fg=C_STEPNUM, anchor="w",
            padx=12, pady=4,
        ).pack(fill=tk.X)
        tk.Frame(given_outer, bg=C_SEP, height=1).pack(fill=tk.X)

        self._given_buttons_frame = tk.Frame(given_outer, bg=BG_GIVEN)
        self._given_buttons_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=8)

    # -----------------------------------------------------------------------
    # Event handlers
    # -----------------------------------------------------------------------

    def _on_solver_change(self) -> None:
        """Update button label when switching solvers (field labels stay the same)."""
        solver = self._solver_var.get()
        self._causal_mode = (solver == "causal")
        # All three solvers share the same Assumptions / Goal field labels.
        self._lbl_assumptions.configure(text="Assumptions:")
        self._lbl_goal.configure(text="Goal:")
        self._prove_btn.configure(text="Prove")

    def _on_prove(self) -> None:
        self._prove_btn.configure(state=tk.DISABLED, text="Proving…")
        self._set_status("Working…", color=C_STEPNUM)
        self.root.update_idletasks()
        threading.Thread(target=self._prove_worker, daemon=True).start()

    def _prove_worker(self) -> None:
        raw_assumptions = self._assumptions_entry.get().strip()
        raw_goal        = self._goal_entry.get().strip()
        solver          = self._solver_var.get()

        # --- Causal solver path (same parse as CSP / PDDL) ---
        if solver == "causal":
            try:
                assumption_strs_c = [s.strip() for s in raw_assumptions.split(",") if s.strip()]
                assumptions_c     = [parse_formula(s) for s in assumption_strs_c]
                goal_c            = parse_formula(raw_goal)
            except Exception as exc:
                self.root.after(0, lambda: self._show_error(f"Parse error: {exc}"))
                self.root.after(0, lambda: self._prove_btn.configure(
                    state=tk.NORMAL, text="Prove"))
                return
            t0 = time.perf_counter()
            result_c = solve_logic_causal(assumptions_c, goal_c)
            elapsed_c = time.perf_counter() - t0
            if result_c is None:
                self.root.after(0, lambda: self._show_no_proof(elapsed_c))
            else:
                lines_c: list = []
                render_logic_causal_steps(result_c, lines_c)
                self.root.after(0, lambda: self._display_proof(
                    lines_c, assumptions_c, goal_c, elapsed_c, "causal"))
            self.root.after(0, lambda: self._prove_btn.configure(
                state=tk.NORMAL, text="Prove"))
            return

        try:
            assumption_strs = [s.strip() for s in raw_assumptions.split(",") if s.strip()]
            assumptions     = [parse_formula(s) for s in assumption_strs]
            goal            = parse_formula(raw_goal)
        except Exception as exc:
            self.root.after(0, lambda: self._show_error(f"Parse error: {exc}"))
            return

        t0 = time.perf_counter()

        if solver == "csp":
            result = solve_fol_csp(assumptions, goal)
            elapsed = time.perf_counter() - t0
            if result is None:
                self.root.after(0, lambda: self._show_no_proof(elapsed))
            else:
                lines: list = []
                render_fol_csp_steps(result, lines)
                self.root.after(0, lambda: self._display_proof(
                    lines, assumptions, goal, elapsed, "csp"))

        elif solver == "pddl":
            result = plan_forward(assumptions, goal)
            elapsed = time.perf_counter() - t0
            if result is None:
                self.root.after(0, lambda: self._show_no_proof(elapsed))
            else:
                lines = []
                render_plan(result, lines)
                self.root.after(0, lambda: self._display_proof(
                    lines, assumptions, goal, elapsed, "pddl"))

        self.root.after(0, lambda: self._prove_btn.configure(
            state=tk.NORMAL, text="Prove"))

    def _on_clear(self) -> None:
        self._assumptions_entry.delete(0, tk.END)
        self._goal_entry.delete(0, tk.END)
        self._clear_proof()
        self._clear_given()
        self._last_proof_lines = []
        self._last_sequent = ""
        self._copy_btn.configure(state=tk.DISABLED)
        self._set_status("Enter a problem and press Prove.")
        self.root.title("JapeAI")
        solver = self._solver_var.get()
        self._proof_header.configure(
            text="Causal Reasoning Trace" if solver == "causal" else "Proof"
        )

    def _on_copy(self) -> None:
        if not self._last_proof_lines:
            return
        INDENT = "    "
        parts = [self._last_sequent, ""]
        for depth, formula, rule, note in self._last_proof_lines:
            pad = INDENT * depth
            if rule in ("premise", "premises", "assumption", "assumptions"):
                parts.append(f"{pad}{formula}   {rule}")
            elif rule == "hyp":
                parts.append(f"{pad}{formula}")
            else:
                n = f"  [{note}]" if note else ""
                parts.append(f"{pad}{formula}   ({rule}){n}")
        text = "\n".join(parts)
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self._set_status("Proof copied to clipboard.", color=C_HYP)

    def _load_example(self, assumptions: list[str], goal: str) -> None:
        self._assumptions_entry.delete(0, tk.END)
        self._assumptions_entry.insert(0, ", ".join(assumptions))
        self._goal_entry.delete(0, tk.END)
        self._goal_entry.insert(0, goal)

    # -----------------------------------------------------------------------
    # Proof display
    # -----------------------------------------------------------------------

    def _display_proof(
        self, lines: list, assumptions, goal, elapsed: float, solver: str,
    ) -> None:
        # Prepend a "premise(s)" line listing the assumptions (like Jape line 1)
        if assumptions:
            premises_str = ", ".join(str(a) for a in assumptions)
            label = "premise" if len(assumptions) == 1 else "premises"
            lines = [(0, premises_str, label, None)] + lines

        self._last_proof_lines = lines
        self._last_sequent = (
            (", ".join(str(a) for a in assumptions) + "  ⊢  " if assumptions else "⊢  ")
            + str(goal)
        )
        self._copy_btn.configure(state=tk.NORMAL)
        self._clear_proof()
        self._update_given(assumptions)

        # Update window title and proof pane header to show sequent (Jape style)
        hyps_str = ", ".join(str(a) for a in assumptions) if assumptions else ""
        sequent  = f"{hyps_str}  |-  {goal}" if hyps_str else f"|-  {goal}"
        self.root.title(f"JapeAI  –  {sequent}")
        self._proof_header.configure(text=sequent)

        container = self._proof_scroll.inner
        INDENT    = "  |  "   # per depth level, shown as a scope bar label

        solver_label = {
            "csp":    "CSP",
            "pddl":   "PDDL planner",
            "causal": "Causal (CBN/SCM)",
        }.get(solver, solver)

        for i, entry in enumerate(lines, start=1):
            depth, formula, rule, note = (entry + (None,))[:4] if len(entry) == 3 else entry

            row_bg = BG_PROOF
            row = tk.Frame(container, bg=row_bg)
            row.pack(fill=tk.X, padx=0, pady=0)

            # Coloured left accent bar by rule type
            accent = (C_SCOPE    if rule in ("premise", "premises", "assumption", "assumptions")
                      else C_HYP  if rule == "hyp"
                      else row_bg)
            tk.Frame(row, bg=accent, width=3).pack(side=tk.LEFT, fill=tk.Y)

            # Step number
            tk.Label(
                row, text=f"{i}",
                font=FONT_STEPNUM, fg=C_STEPNUM, bg=row_bg,
                width=3, anchor="e",
            ).pack(side=tk.LEFT, padx=(4, 0))

            # Scope indent
            if depth and depth > 0:
                tk.Label(
                    row, text="  │  " * depth,
                    font=FONT_RULE, fg=C_SEP, bg=row_bg,
                ).pack(side=tk.LEFT)

            # Formula
            if rule == "hyp":
                tk.Label(
                    row, text=formula,
                    font=FONT_FORMULA, fg=C_HYP, bg=row_bg, anchor="w",
                ).pack(side=tk.LEFT, padx=(8, 16))
            else:
                f_font = FONT_FORMULA_B if rule in ("→ intro", "∀ intro") else FONT_FORMULA
                f_col  = (C_SCOPE if rule in ("premise", "premises", "assumption", "assumptions")
                          else C_TEXT)
                tk.Label(
                    row, text=formula,
                    font=f_font, fg=f_col, bg=row_bg, anchor="w",
                ).pack(side=tk.LEFT, padx=(8, 12))

                # Rule label
                rule_text = rule
                if note:
                    rule_text += f"  {note}"
                tk.Label(
                    row, text=rule_text,
                    font=FONT_RULE, fg=C_RULE, bg=row_bg, anchor="w",
                ).pack(side=tk.LEFT)

            # Thin hairline between rows
            tk.Frame(container, bg=C_SEP, height=1).pack(fill=tk.X, padx=3)

        # Footer
        if lines:
            footer_text = (
                f"Proved by {solver_label}  ·  "
                f"{len(lines)} step{'s' if len(lines) != 1 else ''}  ·  "
                f"{elapsed*1000:.1f} ms"
            )
            tk.Label(
                container, text=footer_text,
                font=FONT_RULE, fg=C_STEPNUM, bg=BG_PROOF, anchor="w",
            ).pack(fill=tk.X, padx=16, pady=(6, 10))

        self._proof_scroll.scroll_to_bottom()

        steps = len(lines)
        self._set_status(
            f"Proved  ·  {steps} step{'s' if steps != 1 else ''}  ·  {elapsed*1000:.1f} ms",
            color=C_HYP,
        )

    def _show_no_proof(self, elapsed: float) -> None:
        self._clear_proof()
        container = self._proof_scroll.inner
        tk.Label(
            container, text="No proof found within the search bound.",
            font=FONT_FORMULA, fg=C_ERROR, bg=BG_PROOF, anchor="w",
        ).pack(fill=tk.X, padx=16, pady=(24, 4))
        tk.Label(
            container, text=f"{elapsed*1000:.1f} ms",
            font=FONT_RULE, fg=C_STEPNUM, bg=BG_PROOF, anchor="w",
        ).pack(fill=tk.X, padx=16)
        self._set_status(f"No proof found.  ({elapsed*1000:.1f} ms)", color=C_ERROR)
        self._prove_btn.configure(state=tk.NORMAL, text="Prove")

    def _show_error(self, message: str) -> None:
        self._clear_proof()
        container = self._proof_scroll.inner
        tk.Label(
            container, text=message,
            font=FONT_RULE, fg=C_ERROR, bg=BG_PROOF, anchor="w",
            wraplength=700,
        ).pack(fill=tk.X, padx=16, pady=12)
        self._set_status(message, color=C_ERROR)
        self._prove_btn.configure(state=tk.NORMAL, text="Prove")

    # -----------------------------------------------------------------------
    # Given pane — hypothesis buttons (Jape style: grey boxes)
    # -----------------------------------------------------------------------

    def _update_given(self, assumptions) -> None:
        self._clear_given()
        frame = self._given_buttons_frame

        if not assumptions:
            tk.Label(
                frame, text="(no assumptions)",
                font=FONT_RULE, fg=C_STEPNUM, bg=BG_GIVEN,
            ).pack(side=tk.LEFT, padx=4)
            return

        for formula in assumptions:
            btn = tk.Button(
                frame,
                text=str(formula),
                font=FONT_GIVEN_BTN,
                bg=BTN_HYP_BG,
                fg=C_SCOPE,
                activebackground=BTN_HYP_ACT,
                activeforeground=C_SCOPE,
                relief=tk.FLAT, bd=0,
                padx=12, pady=5,
                cursor="hand2",
            )
            btn.pack(side=tk.LEFT, padx=4, pady=4)

    def _clear_given(self) -> None:
        for widget in self._given_buttons_frame.winfo_children():
            widget.destroy()

    def _clear_proof(self) -> None:
        self._proof_scroll.clear()

    # -----------------------------------------------------------------------
    # Status helper
    # -----------------------------------------------------------------------

    def _set_status(self, message: str, color: str = C_STEPNUM) -> None:
        self._status_var.set(message)
        self._status_label.configure(fg=color)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    # Give the app its own Windows identity so the taskbar shows our icon
    # instead of grouping under python.exe.
    try:
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("JapeAI.App")
    except Exception:
        pass

    root = tk.Tk()
    app  = JapeAIApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
