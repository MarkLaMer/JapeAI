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


# ---------------------------------------------------------------------------
# Colour scheme (close to Jape defaults)
# ---------------------------------------------------------------------------
BG_PROOF    = "#FFFFFF"
BG_GIVEN    = "#F5F5F5"
BG_TOOLBAR  = "#ECECEC"
BG_ROOT     = "#ECECEC"

C_TEXT      = "#000000"
C_RULE      = "#0055CC"   # blue  – rule labels
C_HYP       = "#005500"   # dark green – hypothesis buttons
C_SCOPE     = "#7B00A0"   # purple – imp_intro scope bars
C_STEPNUM   = "#888888"   # grey  – "n:"
C_ERROR     = "#CC0000"
C_SEP       = "#CCCCCC"

FONT_FORMULA  = ("Palatino Linotype", 15)        # large, serif – Jape uses MathJax-like fonts
FONT_FORMULA_B= ("Palatino Linotype", 15, "bold")
FONT_RULE     = ("Segoe UI", 11)
FONT_STEPNUM  = ("Segoe UI", 11)
FONT_TOOLBAR  = ("Segoe UI", 11)
FONT_GIVEN_BTN= ("Palatino Linotype", 13)
FONT_TITLE    = ("Segoe UI", 13, "bold")
FONT_MONO     = ("Consolas", 11)

BTN_HYP_BG  = "#D8D8D8"   # grey box like Jape's hypothesis buttons
BTN_HYP_ACT = "#B8B8B8"

# ---------------------------------------------------------------------------
# Example problems
# ---------------------------------------------------------------------------
EXAMPLES = [
    # Propositional
    ("P, P→Q  ⊢  Q",                  ["P", "P -> Q"],                              "Q"),
    ("P∧Q  ⊢  Q∧P",                   ["P & Q"],                                    "Q & P"),
    ("P, Q  ⊢  P ∧ Q",                ["P", "Q"],                                   "P & Q"),
    ("⊢  P → P",                      [],                                            "P -> P"),
    ("⊢  (P∧Q) → (Q∧P)",             [],                                            "(P & Q) -> (Q & P)"),
    ("P  ⊢  Q → (P ∧ Q)",            ["P"],                                         "Q -> (P & Q)"),
    # FOL
    ("∀y.T(y)→Q(y), ∀y.T(y)  ⊢  ∀y.Q(y)",
        ["∀y.(T(y)→Q(y))", "∀y.T(y)"],                                              "∀y.Q(y)"),
    ("∀y.(T(y)→Q(y)∧R(y))  ⊢  ∀y.(T(y)→∃z.Q(z))",
        ["∀y.(T(y)→(Q(y)∧R(y)))"],                                                  "∀y.(T(y)→∃z.Q(z))"),
    ("∃y.T(y), ∀y.(T(y)→R(y))  ⊢  ∃y.R(y)",
        ["∃y.T(y)", "∀y.(T(y)→R(y))"],                                              "∃y.R(y)"),
    ("∀x.(P(x)→T(x))  ⊢  ∃x.P(x)→∃x.T(x)",
        ["∀x.(P(x)→T(x))"],                                                          "∃x.P(x)→∃x.T(x)"),
    ("∀y.∀z.(∃x.¬R(x)→(P(z)→¬Q(y)))  ⊢  ∀y.∀z.∀x.((P(z)∧Q(x))→R(z))",
        ["∀y.∀z.(∃x.¬R(x)→(P(z)→¬Q(y)))"],                                         "∀y.∀z.∀x.((P(z)∧Q(x))→R(z))"),
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
        self.root.geometry("900x620")
        self.root.configure(bg=BG_ROOT)
        self.root.minsize(640, 460)

        self._solver_var = tk.StringVar(value="csp")
        self._status_var = tk.StringVar(value="Enter a problem and press Prove.")
        self._last_proof_lines: list = []   # (depth, formula, rule, note) tuples
        self._last_sequent: str = ""

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
            ("CSP  (forward + FOL)",       "csp"),
            ("PDDL planner  (forward BFS)","pddl"),
        ]:
            solver_menu.add_radiobutton(
                label=label, variable=self._solver_var, value=value,
            )
        proof_menu.add_cascade(label="Solver", menu=solver_menu)
        menubar.add_cascade(label="Proof", menu=proof_menu)
        self.root.bind_all("<Control-Return>", lambda _: self._on_prove())

        # -- Examples --------------------------------------------------------
        ex_menu = tk.Menu(menubar, tearoff=False)
        for i, (label, assumptions, goal) in enumerate(EXAMPLES):
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
        tb.pack(side=tk.TOP, fill=tk.X, padx=0, pady=0)

        # Thin separator line at bottom of toolbar
        tk.Frame(tb, bg=C_SEP, height=1).pack(side=tk.BOTTOM, fill=tk.X)

        # ── Row 1: entry fields, solver radios, Prove/Clear, status ────────
        inner = tk.Frame(tb, bg=BG_TOOLBAR)
        inner.pack(fill=tk.X, padx=8, pady=(6, 2))

        # Assumptions
        tk.Label(inner, text="Assumptions:", font=FONT_TOOLBAR,
                 bg=BG_TOOLBAR).pack(side=tk.LEFT)
        self._assumptions_entry = tk.Entry(
            inner, font=FONT_MONO, width=28,
            relief=tk.SOLID, bd=1,
        )
        self._assumptions_entry.pack(side=tk.LEFT, padx=(4, 12))
        self._assumptions_entry.bind("<Return>", lambda _: self._on_prove())
        self._wire_substitutions(self._assumptions_entry)

        # Goal
        tk.Label(inner, text="Goal:", font=FONT_TOOLBAR,
                 bg=BG_TOOLBAR).pack(side=tk.LEFT)
        self._goal_entry = tk.Entry(
            inner, font=FONT_MONO, width=20,
            relief=tk.SOLID, bd=1,
        )
        self._goal_entry.pack(side=tk.LEFT, padx=(4, 12))
        self._goal_entry.bind("<Return>", lambda _: self._on_prove())
        self._wire_substitutions(self._goal_entry)

        # Solver radio buttons
        solver_frame = tk.Frame(inner, bg=BG_TOOLBAR)
        solver_frame.pack(side=tk.LEFT, padx=(0, 12))
        for label, value in [("CSP", "csp"), ("PDDL", "pddl")]:
            tk.Radiobutton(
                solver_frame, text=label, variable=self._solver_var,
                value=value, font=FONT_TOOLBAR, bg=BG_TOOLBAR,
                activebackground=BG_TOOLBAR,
            ).pack(side=tk.LEFT, padx=2)

        # Prove button
        self._prove_btn = tk.Button(
            inner, text="Prove", font=("Segoe UI", 11, "bold"),
            bg="#1565C0", fg="white",
            activebackground="#0D47A1", activeforeground="white",
            relief=tk.FLAT, padx=14, pady=3,
            cursor="hand2", command=self._on_prove,
        )
        self._prove_btn.pack(side=tk.LEFT, padx=(0, 4))

        tk.Button(
            inner, text="Clear", font=FONT_TOOLBAR,
            bg=BG_TOOLBAR, relief=tk.GROOVE, padx=8, pady=3,
            cursor="hand2", command=self._on_clear,
        ).pack(side=tk.LEFT)

        self._copy_btn = tk.Button(
            inner, text="Copy Proof", font=FONT_TOOLBAR,
            bg=BG_TOOLBAR, relief=tk.GROOVE, padx=8, pady=3,
            cursor="hand2", command=self._on_copy,
            state=tk.DISABLED,
        )
        self._copy_btn.pack(side=tk.LEFT, padx=(4, 0))

        # Status (right-aligned)
        self._status_label = tk.Label(
            inner, textvariable=self._status_var,
            font=FONT_TOOLBAR, bg=BG_TOOLBAR, fg=C_STEPNUM,
            anchor="e",
        )
        self._status_label.pack(side=tk.RIGHT, padx=(8, 0))

        # ── Row 2: symbol palette ───────────────────────────────────────────
        palette_row = tk.Frame(tb, bg=BG_TOOLBAR)
        palette_row.pack(fill=tk.X, padx=8, pady=(0, 5))

        tk.Label(palette_row, text="Insert:", font=FONT_TOOLBAR,
                 bg=BG_TOOLBAR, fg=C_STEPNUM).pack(side=tk.LEFT, padx=(0, 4))

        SYMBOLS = [
            ("∀  forall", "∀"),
            ("∃  exists", "∃"),
            ("¬  ~",      "¬"),
            ("∧  /\\",    "∧"),
            ("∨  \\/",    "∨"),
            ("→  ->",     "→"),
            ("↔  <->",    "↔"),
            ("⊢  |-",     "⊢"),
        ]
        for display, sym in SYMBOLS:
            tk.Button(
                palette_row, text=display,
                font=("Segoe UI", 10),
                bg=BTN_HYP_BG, fg=C_TEXT,
                activebackground=BTN_HYP_ACT,
                relief=tk.RAISED, bd=1,
                padx=6, pady=1,
                cursor="hand2",
                command=lambda s=sym: self._insert_symbol(s),
            ).pack(side=tk.LEFT, padx=2)

    # -----------------------------------------------------------------------
    # Main area  (proof pane + given pane, PanedWindow)
    # -----------------------------------------------------------------------

    def _build_main(self) -> None:
        paned = tk.PanedWindow(
            self.root, orient=tk.VERTICAL, bg=C_SEP,
            sashwidth=5, sashrelief=tk.FLAT,
        )
        paned.pack(fill=tk.BOTH, expand=True)

        # -- Proof pane (top) ------------------------------------------------
        proof_outer = tk.Frame(paned, bg=BG_PROOF)
        paned.add(proof_outer, stretch="always", minsize=280)

        # "Proof" label header (like Jape's window title bar area)
        self._proof_header = tk.Label(
            proof_outer, text="Proof",
            font=("Segoe UI", 10, "bold"),
            bg=BG_TOOLBAR, fg=C_STEPNUM, anchor="w",
            padx=8, pady=3,
        )
        self._proof_header.pack(fill=tk.X)
        tk.Frame(proof_outer, bg=C_SEP, height=1).pack(fill=tk.X)

        self._proof_scroll = _ScrollableFrame(proof_outer, bg=BG_PROOF)
        self._proof_scroll.pack(fill=tk.BOTH, expand=True)

        # -- Given pane (bottom) ---------------------------------------------
        given_outer = tk.Frame(paned, bg=BG_GIVEN)
        paned.add(given_outer, stretch="never", minsize=80)

        tk.Frame(given_outer, bg=C_SEP, height=1).pack(fill=tk.X)

        given_header = tk.Label(
            given_outer, text="Given",
            font=("Segoe UI", 10, "bold"),
            bg=BG_TOOLBAR, fg=C_STEPNUM, anchor="w",
            padx=8, pady=3,
        )
        given_header.pack(fill=tk.X)
        tk.Frame(given_outer, bg=C_SEP, height=1).pack(fill=tk.X)

        self._given_buttons_frame = tk.Frame(given_outer, bg=BG_GIVEN)
        self._given_buttons_frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)

    # -----------------------------------------------------------------------
    # Event handlers
    # -----------------------------------------------------------------------

    def _on_prove(self) -> None:
        self._prove_btn.configure(state=tk.DISABLED, text="Proving…")
        self._set_status("Working…", color=C_STEPNUM)
        self.root.update_idletasks()
        threading.Thread(target=self._prove_worker, daemon=True).start()

    def _prove_worker(self) -> None:
        raw_assumptions = self._assumptions_entry.get().strip()
        raw_goal        = self._goal_entry.get().strip()
        solver          = self._solver_var.get()

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
        self._proof_header.configure(text="Proof")

    def _on_copy(self) -> None:
        if not self._last_proof_lines:
            return
        INDENT = "    "
        parts = [self._last_sequent, ""]
        for depth, formula, rule, note in self._last_proof_lines:
            pad = INDENT * depth
            if rule == "hyp":
                parts.append(f"{pad}{formula}")
            elif rule in ("premise",):
                parts.append(f"{pad}{formula}")
            elif rule in ("premises", "assumptions"):
                parts.append(f"{pad}{formula}   {rule}")
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
        # Prepend a "premises" line listing the assumptions (like Jape line 1)
        if assumptions:
            premises_str = ", ".join(str(a) for a in assumptions)
            lines = [(0, premises_str, "premises", None)] + lines

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
            "csp":  "CSP",
            "pddl": "PDDL planner",
        }.get(solver, solver)

        for i, entry in enumerate(lines, start=1):
            depth, formula, rule, note = (entry + (None,))[:4] if len(entry) == 3 else entry

            row = tk.Frame(container, bg=BG_PROOF)
            row.pack(fill=tk.X, padx=12, pady=1)

            # Step number  "n:"
            tk.Label(
                row, text=f"{i}:",
                font=FONT_STEPNUM, fg=C_STEPNUM, bg=BG_PROOF,
                width=4, anchor="e",
            ).pack(side=tk.LEFT)

            # Scope bars (purple pipes for imp_intro depth)
            if depth and depth > 0:
                tk.Label(
                    row, text=INDENT * depth,
                    font=FONT_RULE, fg=C_SCOPE, bg=BG_PROOF,
                ).pack(side=tk.LEFT)

            # Formula  (bold if it is the conclusion of an imp_intro scope)
            if rule == "hyp":
                # Jape-style assumption bracket:  [ assume  A ]
                tk.Label(
                    row, text=f"[ assume  {formula} ]",
                    font=FONT_FORMULA, fg=C_SCOPE, bg=BG_PROOF,
                    anchor="w",
                ).pack(side=tk.LEFT, padx=(2, 16))
            else:
                f_font = FONT_FORMULA_B if rule in ("-> intro", "& intro") else FONT_FORMULA
                tk.Label(
                    row, text=formula,
                    font=f_font, fg=C_TEXT, bg=BG_PROOF,
                    anchor="w",
                ).pack(side=tk.LEFT, padx=(2, 16))

                # Rule label (blue)
                rule_text = rule
                if note:
                    rule_text += f"  ({note})"
                tk.Label(
                    row, text=rule_text,
                    font=FONT_RULE, fg=C_RULE, bg=BG_PROOF,
                    anchor="w",
                ).pack(side=tk.LEFT)

        # Footer row
        if lines:
            sep = tk.Frame(container, bg=C_SEP, height=1)
            sep.pack(fill=tk.X, padx=12, pady=(6, 2))

            footer_text = (
                f"Proved by {solver_label}  ·  "
                f"{len(lines)} step{'s' if len(lines) != 1 else ''}  ·  "
                f"{elapsed*1000:.1f} ms"
            )
            tk.Label(
                container, text=footer_text,
                font=FONT_RULE, fg=C_STEPNUM, bg=BG_PROOF,
                anchor="w",
            ).pack(fill=tk.X, padx=12, pady=(0, 8))

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
                fg=C_HYP,
                activebackground=BTN_HYP_ACT,
                activeforeground=C_HYP,
                relief=tk.RAISED, bd=1,
                padx=10, pady=4,
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
    root = tk.Tk()
    app  = JapeAIApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
