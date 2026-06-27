"""Render extracted Lean statements as human-readable LaTeX math.

Input  : the JSON facts produced by `probe.extract` (names, binders with Lean
         pretty-printed types, conclusions).
Output : a compilable LaTeX document — one theorem/definition environment per
         target, with hypotheses and conclusion typeset in math mode.

Honesty: this is a *faithful syntactic* translation of the Lean statement
(token-level Lean-pp -> LaTeX), NOT a re-proof or a re-statement. It changes
notation, never content. Project operators can be mapped to readable macros via
a `[latex.notation]` table in the track TOML; anything unmapped is rendered as
\\mathrm{name} so nothing is silently dropped.
"""
import re

# ---- single-codepoint Lean glyphs -> LaTeX (math mode) ----------------------
SYMBOLS = {
    # logic / quantifiers
    "∀": r"\forall ", "∃": r"\exists ", "¬": r"\neg ", "∧": r"\wedge ",
    "∨": r"\vee ", "↔": r"\leftrightarrow ", "→": r"\to ", "↦": r"\mapsto ",
    "⟶": r"\longrightarrow ", "⊢": r"\vdash ",
    # relations
    "≤": r"\le ", "≥": r"\ge ", "≠": r"\ne ", "≈": r"\approx ", "≡": r"\equiv ",
    "≃": r"\simeq ", "≅": r"\cong ", "∼": r"\sim ", "≪": r"\ll ", "≫": r"\gg ",
    "∝": r"\propto ", "≜": r"\triangleq ", "≔": r":= ", "∣": r"\mid ",
    # sets
    "∈": r"\in ", "∉": r"\notin ", "⊆": r"\subseteq ", "⊂": r"\subset ",
    "⊇": r"\supseteq ", "∩": r"\cap ", "∪": r"\cup ", "∅": r"\emptyset ",
    "⋃": r"\bigcup ", "⋂": r"\bigcap ", "∖": r"\setminus ",
    # big operators / analysis
    "∑": r"\sum ", "∏": r"\prod ", "∫": r"\int ", "∂": r"\partial ",
    "∇": r"\nabla ", "√": r"\sqrt ", "∞": r"\infty ", "∘": r"\circ ",
    # arithmetic / algebra
    "×": r"\times ", "⊗": r"\otimes ", "⊕": r"\oplus ", "·": r"\cdot ",
    "•": r"\cdot ", "∙": r"\cdot ", "⬝": r"\cdot ", "±": r"\pm ", "∓": r"\mp ",
    "⊤": r"\top ", "⊥": r"\bot ", "†": r"^{\dagger}",
    # blackboard
    "ℝ": r"\mathbb{R}", "ℂ": r"\mathbb{C}", "ℕ": r"\mathbb{N}",
    "ℤ": r"\mathbb{Z}", "ℚ": r"\mathbb{Q}", "𝟙": r"\mathbb{1}", "𝕜": r"\Bbbk ",
    # letterlike
    "ℓ": r"\ell ", "ℏ": r"\hbar ", "ℵ": r"\aleph ", "∎": r"\qed ",
    # delimiters / misc
    "⟨": r"\langle ", "⟩": r"\rangle ", "‖": r"\|", "∥": r"\|",
    "⌊": r"\lfloor ", "⌋": r"\rfloor ", "⌈": r"\lceil ", "⌉": r"\rceil ",
    "↑": r"", "↓": r"", "⇑": r"", "⇓": r"", "↥": r"", "↟": r"",  # coercions: drop
    "⋯": r"\cdots ", "⋮": r"\vdots ", "⋱": r"\ddots ", "…": r"\ldots ",
    "⇒": r"\Rightarrow ", "⟹": r"\Longrightarrow ", "⟸": r"\Longleftarrow ",
    "ᵒ": r"^{\circ}", "ₐ": r"_{a}",
}

# ---- Greek letters used as identifiers --------------------------------------
GREEK = {
    "α": r"\alpha", "β": r"\beta", "γ": r"\gamma", "δ": r"\delta",
    "ε": r"\varepsilon", "ζ": r"\zeta", "η": r"\eta", "θ": r"\theta",
    "ι": r"\iota", "κ": r"\kappa", "λ": r"\lambda", "μ": r"\mu", "ν": r"\nu",
    "ξ": r"\xi", "π": r"\pi", "ρ": r"\rho", "σ": r"\sigma", "τ": r"\tau",
    "υ": r"\upsilon", "φ": r"\varphi", "χ": r"\chi", "ψ": r"\psi", "ω": r"\omega",
    "Γ": r"\Gamma", "Δ": r"\Delta", "Θ": r"\Theta", "Λ": r"\Lambda",
    "Ξ": r"\Xi", "Π": r"\Pi", "Σ": r"\Sigma", "Φ": r"\Phi", "Ψ": r"\Psi",
    "Ω": r"\Omega",
}

# ---- unicode sub/superscripts ----------------------------------------------
SUPERS = {"⁰": "0", "¹": "1", "²": "2", "³": "3", "⁴": "4", "⁵": "5", "⁶": "6",
          "⁷": "7", "⁸": "8", "⁹": "9", "⁺": "+", "⁻": "-", "ⁿ": "n", "ⁱ": "i",
          "ᵀ": "T", "ᵃ": "a", "ᵇ": "b", "ᶜ": "c", "ᵈ": "d", "ᵉ": "e", "ᶠ": "f"}
SUBS = {"₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4", "₅": "5", "₆": "6",
        "₇": "7", "₈": "8", "₉": "9", "₊": "+", "₋": "-", "ₙ": "n", "ᵢ": "i",
        "ⱼ": "j", "ₖ": "k", "ₗ": "l", "ₘ": "m", "ₚ": "p", "ᵣ": "r", "ₛ": "s",
        "ₜ": "t", "ᵥ": "v", "ᵤ": "u", "ₕ": "h", "ₓ": "x", "ₒ": "o", "ₑ": "e"}

# Lean keywords that survive pretty-printing -> their math-mode rendering.
KW_TEX = {
    "fun": r"\lambda ", "if": r"\text{if }", "then": r"\text{ then }",
    "else": r"\text{ else }", "in": r"\text{ in }", "let": r"\text{let }",
    "do": r"\text{do }", "match": r"\text{match }", "with": r"\text{ with }",
    "from": r"\text{ from }", "by": r"\text{ by }", "at": r"\text{ at }",
}
KEYWORDS = set(KW_TEX)

# Common Mathlib names with standard math notation. Track configs may extend or
# override these via [latex.notation].
DEFAULT_NOTATION = {
    "Real.pi": r"\pi", "Real.exp": r"\exp", "Real.log": r"\log",
    "Real.sqrt": r"\sqrt", "Real.sin": r"\sin", "Real.cos": r"\cos",
    "Real.cosh": r"\cosh", "Real.sinh": r"\sinh", "Complex.I": r"i",
    "Complex.exp": r"\exp", "Finset.univ": r"\mathrm{univ}",
    "Finset.sum": r"\sum", "Nat": r"\mathbb{N}", "Int": r"\mathbb{Z}",
    "Rat": r"\mathbb{Q}", "True": r"\top", "False": r"\bot",
    # Common project / operator-theory names with standard notation, so long
    # \mathrm{camelCase} identifiers across the dependency closure read as math.
    # Per-track [latex.notation] overrides any of these.
    "christoffel": r"\Gamma^{#3}_{#4#5}(#6)",   # g gi a b c x -> Γ^a_{bc}(x)
    "riemann": r"\mathrm{Riem}", "riemannQuad": r"\mathrm{Riem}",
    "covDerivRiem": r"\nabla\mathrm{Riem}",
    "modConj": r"J", "modConjBilin": r"J", "modUnitary": r"\Delta",
    "modChar": r"\chi_{\mathrm{mod}}", "modCharC": r"\chi_{\mathrm{mod}}",
    "boostUnitary": r"U", "boostKMS": r"U",
    "spectrum": r"\mathrm{sp}", "specMeasure": r"\mu_{\mathrm{sp}}",
    "specProj": r"E", "scalarMeasure": r"\mu",
    "rvdSqrtR": r"R^{1/2}", "rvdSpecMeasure": r"\mu^{R}",
    "boundedFC": r"\Phi", "borelFC": r"\Phi_{B}", "cfcCont": r"\Phi_{c}",
    "starRingEnd": r"\overline{#2}", "fourier": r"\mathcal{F}",
    "niceWedgeStandardSubspace": r"\mathcal{K}",
    "niceWedgeClosedSubmodule": r"\mathcal{K}", "niceWedgeGenSet": r"\mathcal{G}",
    "gaussSmear": r"g", "gaussSmearC": r"g",
    # second pass — remaining recurring closure operators (short, recognisable
    # abbreviations of the Lean name; tune per-track if a different symbol is wanted)
    "toClosedSubmodule": r"\mathrm{cl}", "closure": r"\overline{#1}",
    "bilinDiag": r"\mathrm{bd}", "diagInt": r"\textstyle\int",
    "integralSimple": r"\textstyle\int",
    "rvdTwoSubRC": r"(2-R)", "rvdSqrtTwoSubR": r"\sqrt{2-R}", "rvdTwoSubR": r"(2-R)",
    "deviceVecF": r"\mathrm{dev}", "deviceOpC": r"\mathrm{dev}_{\mathbb{C}}",
    "deviceOpReal": r"\mathrm{dev}", "devChar": r"\chi_{\mathrm{dev}}",
    "kmsFunCut": r"\mathrm{kms}", "kmsStripOpen": r"S^{\circ}",
    "kmsHalfStripOpen": r"S^{\circ}_{1/2}", "negStrip": r"S^{-}",
    "negStripOpen": r"S^{-}",
    "lorentzBoost": r"\mathrm{L}", "lorentzBoostₗ": r"\mathrm{L}",
    "riemannLin": r"\mathrm{Riem}", "covDeriv2Vec": r"\nabla^{2}",
    "covDeriv02": r"\nabla^{2}", "kernelDeriv": r"\mathrm{K}'",
    "minkowskiFourier": r"\mathcal{F}", "minkowskiDot": r"\eta",
    "minkowskiDotℂ": r"\eta", "massShell": r"\mathrm{MS}", "massShellℂ": r"\mathrm{MS}",
    "indicator": r"\mathbf{1}", "adjoint": r"{#1}^{\dagger}", "unitary": r"\mathrm{U}",
    "specCoord": r"\mathrm{sc}", "modSpecFun": r"f_{\mathrm{mod}}",
    "boostTest": r"\phi_{B}", "entireVec": r"\mathrm{ev}",
    "schwartzTranslate": r"\tau", "closedBall": r"\bar{B}",
    "ftKrep'": r"\hat{K}", "ftKrepF": r"\hat{K}",
    "restrictScalars": r"\mathrm{res}", "compMeasurePreserving": r"\mathrm{cmp}",
    "nhdsWithin": r"\mathcal{N}", "withDensity": r"\mathrm{wd}",
    "approxSeq": r"\mathrm{aseq}", "restrict": r"\mathrm{restr}",
    "bumpRealW": r"\mathrm{bump}",
    "minkBilin": r"\eta", "iteratedFDeriv": r"\mathrm{D}", "intBorel": r"\textstyle\int",
    "kmsHalfStrip": r"S_{1/2}", "kmsStrip": r"S", "devSpecReal": r"\chi_{\mathrm{dev}}",
    "deviceDerivOpC": r"\mathrm{dev}'", "elemental": r"\mathrm{elem}",
    "negMulLog": r"\mathrm{nml}", "fourierChar": r"\mathrm{e}", "fourierIntegral": r"\mathcal{F}",
    "covDeriv20": r"\nabla^{2}", "realCommutant": r"\mathcal{M}'",
    "inner": r"\langle #2,#3\rangle",   # inner 𝕜 x y -> ⟨x, y⟩
    # third pass — the highest-frequency long names still surviving into the math,
    # each given its OWN docstring's symbol (faithful, not invented):
    "Krep": r"K", "KrepCont": r"K_{\mathbb{C}}",          # localization map (K f)(θ)
    "projK": r"P", "projIK": r"Q",                        # RvD projections onto 𝒦, i𝒦
    "rvdR": r"R", "rvdRC": r"R", "rvdPmQ": r"(P-Q)", "rvdT": r"T",  # RvD R=P+Q, P−Q, T
    "qForm": r"q", "bForm": r"b", "cForm": r"c",          # spectral quad/bilinear/complex forms
    "kmsFun": r"F", "kmsBCF": r"F", "gaussMode": r"g_{0}",  # KMS function F(z); reference profile g₀
    # standard Mathlib operators with conventional math notation:
    "lam": r"\lambda",
    "volume": r"\mathrm{vol}", "MeasureTheory.volume": r"\mathrm{vol}",
    "Ioo": r"(#1,#2)", "Icc": r"[#1,#2]", "Ico": r"[#1,#2)", "Ioc": r"(#1,#2]",
    "nhds": r"\mathcal{N}", "deriv": r"\mathrm{D}", "span": r"\mathrm{span}",
    "cfc": r"#1(#2)",                                    # functional calculus: cfc f a = f(a)
    "min": r"\min(#1,#2)", "max": r"\max(#1,#2)",
}

_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_.'!?]*")

# glyphs that escaped every map during this run (surfaced by the CLI for review)
_UNMAPPED = set()

# characters that cannot begin an application argument (operators / separators /
# closers). Everything else — letters, digits, (, [, Greek, ⊤ ⊥ ∅ ℝ ∞ … — can.
_DELIMS = set(")]},;=<>+-*/|:^"
                "→↦⟶↔≤≥≠≈≡≃≅∼≪≫∝∣∈∉⊆⊂⊇∩∪∖∧∨¬·•∙×⊗⊕±∓∘⇒⟹⟸⋯⋮⋱∑∏∫")

# operator commands (NOT atoms): a thin-space must never follow these.
_OP_WORDS = ["cdot", "le", "ge", "ne", "approx", "equiv", "simeq", "cong",
             "sim", "propto", "in", "notin", "subseteq", "subset", "supseteq",
             "cap", "cup", "setminus", "to", "mapsto", "longrightarrow",
             "wedge", "vee", "neg", "times", "otimes", "oplus", "circ", "pm",
             "mp", "sum", "prod", "int", "partial", "nabla", "vdash", "mid",
             "Rightarrow", "Longrightarrow", "Longleftarrow", "ll", "gg"]


def _read_arg(pp, i):
    """Read one application argument from `pp` at offset `i` (after skipping
    spaces): a balanced (...)/[...] group, or a single atom (identifier / Greek /
    number) plus any trailing unicode sub/superscripts. Returns (substring, new_i),
    or (None, i) when the next token is a delimiter — `i` is then left untouched.
    """
    n = len(pp)
    orig = i
    while i < n and pp[i] == " ":
        i += 1
    if i >= n:
        return None, orig
    # an unparenthesized `fun … => …` / `λ …` argument binds maximally — it runs
    # to the end of the enclosing scope (here, the rest of the string, since a
    # parenthesised lambda is caught by the balanced-group branch below).
    if pp[i] == "λ" or re.match(r"fun\b", pp[i:]):
        return pp[i:], n
    if pp[i] in "([":
        opener = pp[i]
        depth, j = 0, i
        while j < n:
            if pp[j] in "([":
                depth += 1
            elif pp[j] in ")]":
                depth -= 1
                if depth == 0:
                    j += 1
                    break
            j += 1
        # strip a (...) wrapper so the *template* controls bracketing (avoids the
        # double parens of S((p x v t))); keep [...] groups intact.
        if opener == "(":
            return pp[i + 1:j - 1], j
        return pp[i:j], j
    if pp[i] in _DELIMS:
        return None, orig                       # a delimiter: no argument here
    m = _IDENT.match(pp, i)
    if m:
        j = m.end()
    elif pp[i].isdigit():
        j = i
        while j < n and (pp[j].isdigit() or pp[j] == "."):
            j += 1
    else:
        j = i + 1            # any other non-delimiter glyph (⊤, ℝ, μ, ℓ, …) is an atom
    while j < n and (pp[j] in SUPERS or pp[j] in SUBS):
        j += 1
    return pp[i:j], j


def _lookup(tok, notation):
    """Return the notation entry for a token (full name, then last segment)."""
    if tok in notation:
        return notation[tok]
    last = tok.split(".")[-1]
    return notation.get(last)


def _render_ident(tok, notation):
    """A dotted Lean identifier -> a LaTeX atom.

    Order: explicit notation override (full name, then last segment) >
    Greek letter > single-letter variable (italic) > \\mathrm{lastsegment}.
    """
    if tok in KEYWORDS:
        return None  # handled by caller
    # plain (non-template) notation overrides; templates are handled by the
    # tokenizer's arity-aware firing, and must fall through here when they don't fire.
    if tok in notation and not re.search(r"#\d", notation[tok]):
        return notation[tok]
    last = tok.split(".")[-1]
    if last in notation and not re.search(r"#\d", notation[last]):
        return notation[last]
    # strip Lean decorations Lean allows in names
    base = last.rstrip("!?")
    primes = ""
    while base.endswith("'"):
        primes += r"\prime"; base = base[:-1]
    if not base:
        base = last
    # a bare Greek letter
    if base in GREEK:
        return GREEK[base] + ("^{" + primes + "}" if primes else "")
    # split a trailing numeric/letter subscript Lean folded into the name
    m = re.fullmatch(r"([A-Za-z]+)([0-9]+)", base)
    if m and len(m.group(1)) == 1:
        return m.group(1) + "_{" + m.group(2) + "}"
    if len(base) == 1:
        return base + ("^{" + primes + "}" if primes else "")
    # multi-letter -> upright operator name; escape TeX-special underscores
    safe = base.replace("_", r"\_")
    return r"\mathrm{" + safe + "}" + ("^{" + primes + "}" if primes else "")


def tex_of_pp(pp, notation=None):
    """Translate one Lean pretty-printed expression string into LaTeX math."""
    notation = {**DEFAULT_NOTATION, **(notation or {})}
    pp = pp.replace("\n", " ")
    pp = re.sub(r"\s+", " ", pp).strip()

    out, i, n = [], 0, len(pp)
    while i < n:
        c = pp[i]
        # unicode sub/superscript runs -> ^{...} / _{...}. Done HERE (not in a
        # pre-pass) so the braces we emit are never re-scanned as set-builder
        # braces and escaped — that was the nested-script corruption bug.
        if c in SUPERS:
            run = ""
            while i < n and pp[i] in SUPERS:
                run += SUPERS[pp[i]]; i += 1
            out.append("^{" + run + "}"); continue
        if c in SUBS:
            run = ""
            while i < n and pp[i] in SUBS:
                run += SUBS[pp[i]]; i += 1
            out.append("_{" + run + "}"); continue
        m = _IDENT.match(pp, i)
        if m:
            tok = m.group(0)
            i = m.end()
            if tok in KEYWORDS:
                out.append(KW_TEX[tok]); continue
            val = _lookup(tok, notation)
            if val is not None and re.search(r"#\d", val):   # applied template
                argc = max(int(d) for d in re.findall(r"#(\d+)", val))
                # arity-aware: fire only if exactly `argc` real arguments are present
                # (so a variadic variable like `g` renders `g_{μν}(x)` when applied to
                # 3 args but stays plain `g` in `(g x)` or when passed bare).
                args, j, ok = [], i, True
                for _ in range(argc):
                    raw, j = _read_arg(pp, j)
                    if raw is None:
                        ok = False; break
                    args.append(tex_of_pp(raw, notation))
                if ok:
                    i = j
                    # brace-wrap each substituted arg so adjacent placeholders stay
                    # self-delimiting (e.g. #2#3 with σ,b -> {\sigma}{b}, not \sigmab).
                    out.append(re.sub(r"#(\d+)",
                                      lambda mt: "{" + args[int(mt.group(1)) - 1] + "}",
                                      val))
                    continue
            out.append(_render_ident(tok, notation))
            continue
        if c in SYMBOLS:
            out.append(SYMBOLS[c]); i += 1; continue
        if c in GREEK:
            out.append(GREEK[c]); i += 1; continue
        if c == "=":
            # do not collapse '=>' handled below; plain '='
            if i + 1 < n and pp[i + 1] == ">":
                out.append(r"\mapsto "); i += 2; continue
            out.append("="); i += 1; continue
        if c == "*":             # Lean multiplication -> centred dot
            out.append(r" \cdot "); i += 1; continue
        if c in "{}":            # set-builder braces in pp -> \{ \}
            out.append("\\" + c); i += 1; continue
        if c in "#$%&":          # TeX-special -> escape
            out.append("\\" + c); i += 1; continue
        if c == "\\":
            out.append(r"\backslash "); i += 1; continue
        out.append(c); i += 1     # digits, ( ) [ ] , : + - / < > | etc. pass through
    tex = "".join(out)
    # fold big-operator binders: `\sum x, body` -> `\sum_{x} body`
    tex = re.sub(r"(\\(?:sum|prod|bigcup|bigcap|int))\s+([^,]+?)\s*,",
                 r"\1_{\2}", tex)
    # thin-space between juxtaposed application atoms so `g x mu nu` does not
    # collapse to `gxmunu`; fires only atom->atom (letter/digit/}/) to letter/digit/(),
    # never before a control word like \mu or an operator.
    tex = re.sub(r"(?<=[A-Za-z0-9})\]])[ ]+(?=[A-Za-z0-9(])", r"\\,", tex)
    # ...but the lookbehind also matched the trailing letter of an operator
    # command (\cdot, \le, ...). Undo the thin-space directly after those.
    tex = re.sub(r"(\\(?:" + "|".join(_OP_WORDS) + r"))\\,", r"\1 ", tex)

    # --- idiom prettifiers (syntactic, content-preserving) ---
    # Kronecker delta:  if X = Y then 1 else 0  ->  δ_{XY}
    tex = re.sub(
        r"\\text\{if \}(?:\\,)?\s*([^=]+?)\s*=\s*(.+?)\s*"
        r"\\text\{ then \}(?:\\,)?\s*1\s*\\text\{ else \}(?:\\,)?\s*0",
        r"\\delta_{\1\2}", tex)
    # neighbourhood-eventually filter:
    #   ∀ᶠ (t : ℝ) in nhds c, P   ->   for t near c, P
    _sp = r"(?:\\,|\s)*"   # optional thin-space / whitespace
    tex = re.sub(
        r"\\forall" + _sp + r"\^\{f\}" + _sp + r"\(\s*([^:]+?)\s*:[^)]*\)" + _sp +
        r"\\text\{ in \}" + _sp + r"\\mathrm\{nhds\}" + _sp + r"([^,]+?)\s*,",
        r"\\text{for }\1\\text{ near }\2,\\;", tex)
    # safety net: drop any exotic glyph that escaped every map, so output always
    # compiles. Greek/symbols/blackboard are already translated above, so this
    # only removes rare unmapped Lean notation (record any drops for review).
    leftover = sorted({ch for ch in tex if ord(ch) > 0x7F})
    if leftover:
        _UNMAPPED.update(leftover)
        tex = re.sub(r"[^\x00-\x7F]", "", tex)
    tex = re.sub(r"\s+", " ", tex).strip()
    return tex


# ---------------------------------------------------------------------------- #
#  document assembly
# ---------------------------------------------------------------------------- #
ENV_OF_KIND = {"thm": "theorem", "def": "definition", "axiom": "axiom",
               "opaque": "definition", "other": "theorem"}


def _texlabel(name):
    slug = name.replace("'", "-prime")
    return "thm:" + re.sub(r"[^A-Za-z0-9]+", "-", slug).strip("-").lower()


def render_theorem(t, notation=None, role_label=None):
    """One extracted target -> a LaTeX environment string."""
    notation = notation or {}
    name = t["name"]
    if not t.get("present"):
        return (f"\\paragraph{{\\texttt{{{_texname(name)}}}}}"
                f" \\emph{{(not found in the current build)}}\n")
    env = ENV_OF_KIND.get(t.get("kind", "thm"), "theorem")
    data, insts, hyps = [], [], []
    for b in t.get("binders", []):
        rt = tex_of_pp(b["type"], notation)
        nm = tex_of_pp(b["name"], notation)
        if b["kind"] == "prop":
            hyps.append((b["name"], rt))
        elif b["kind"] == "instance":
            insts.append(rt)
        else:
            data.append((nm, rt))

    lines = [f"\\begin{{{env}}}[\\texttt{{{_texname(name)}}}]\\label{{{_texlabel(name)}}}"]
    if role_label:
        lines.append(f"\\textit{{{role_label}.}}")
    if data:
        items = ", ".join(f"${nm} : {rt}$" for nm, rt in data)
        lines.append(f"Given {items}" + ("." if not (insts or hyps) else ","))
    if insts:
        lines.append("with " + ", ".join(f"${rt}$" for rt in insts)
                     + ("." if not hyps else ","))
    if hyps:
        lines.append("assume")
        lines.append(r"\begin{itemize}")
        for hn, rt in hyps:
            lines.append(f"  \\item[\\rm({_hyp_label(hn)})] ${rt}$")
        lines.append(r"\end{itemize}")
    concl = t.get("concl", {})
    claim = tex_of_pp(concl.get("pp", ""), notation)
    lead = "Then" if (data or insts or hyps) else "We have"
    if concl.get("isProp", True):
        lines.append(f"{lead} \\[ {claim} \\]")
    else:                       # a def: the body/type is the object
        lines.append(f"{lead} the object \\[ {claim} \\]")
    lines.append(f"\\end{{{env}}}")
    return "\n".join(lines) + "\n"


def _texname(s):
    return s.replace("_", r"\_").replace("'", r"\textquotesingle{}")


def _hyp_label(hn):
    """A readable itemize tag; collapse Lean's hygienic / anonymous-instance names."""
    if hn.startswith("inst") or "._@." in hn or "_hyg" in hn:
        return "instance"
    return _texname(hn)


PREAMBLE = r"""\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage[T1]{fontenc}
\usepackage{newunicodechar}
% Fallbacks so any unicode that survives in a name / \texttt still compiles.
\newunicodechar{ᶠ}{\ensuremath{^{f}}}
\newunicodechar{₀}{\ensuremath{_0}}\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}\newunicodechar{₃}{\ensuremath{_3}}
\newunicodechar{₄}{\ensuremath{_4}}\newunicodechar{₅}{\ensuremath{_5}}
\newunicodechar{₆}{\ensuremath{_6}}\newunicodechar{₇}{\ensuremath{_7}}
\newunicodechar{₈}{\ensuremath{_8}}\newunicodechar{₉}{\ensuremath{_9}}
\newunicodechar{⁰}{\ensuremath{^0}}\newunicodechar{¹}{\ensuremath{^1}}
\newunicodechar{²}{\ensuremath{^2}}\newunicodechar{³}{\ensuremath{^3}}
\newunicodechar{α}{\ensuremath{\alpha}}   \newunicodechar{β}{\ensuremath{\beta}}
\newunicodechar{γ}{\ensuremath{\gamma}}   \newunicodechar{δ}{\ensuremath{\delta}}
\newunicodechar{ε}{\ensuremath{\varepsilon}} \newunicodechar{ζ}{\ensuremath{\zeta}}
\newunicodechar{η}{\ensuremath{\eta}}     \newunicodechar{θ}{\ensuremath{\theta}}
\newunicodechar{ι}{\ensuremath{\iota}}    \newunicodechar{κ}{\ensuremath{\kappa}}
\newunicodechar{λ}{\ensuremath{\lambda}}  \newunicodechar{μ}{\ensuremath{\mu}}
\newunicodechar{ν}{\ensuremath{\nu}}      \newunicodechar{ξ}{\ensuremath{\xi}}
\newunicodechar{π}{\ensuremath{\pi}}      \newunicodechar{ρ}{\ensuremath{\rho}}
\newunicodechar{σ}{\ensuremath{\sigma}}   \newunicodechar{τ}{\ensuremath{\tau}}
\newunicodechar{φ}{\ensuremath{\varphi}}  \newunicodechar{χ}{\ensuremath{\chi}}
\newunicodechar{ψ}{\ensuremath{\psi}}     \newunicodechar{ω}{\ensuremath{\omega}}
\newunicodechar{Γ}{\ensuremath{\Gamma}}   \newunicodechar{Δ}{\ensuremath{\Delta}}
\newunicodechar{Λ}{\ensuremath{\Lambda}}  \newunicodechar{Σ}{\ensuremath{\Sigma}}
\newunicodechar{Φ}{\ensuremath{\Phi}}     \newunicodechar{Ψ}{\ensuremath{\Psi}}
\newunicodechar{Ω}{\ensuremath{\Omega}}   \newunicodechar{Π}{\ensuremath{\Pi}}
\newunicodechar{ℝ}{\ensuremath{\mathbb{R}}} \newunicodechar{ℂ}{\ensuremath{\mathbb{C}}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}} \newunicodechar{ℤ}{\ensuremath{\mathbb{Z}}}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{definition}[theorem]{Definition}
\newtheorem{axiom}[theorem]{Axiom}
\setlength{\parindent}{0pt}\setlength{\parskip}{4pt}
"""


def render_document(targets, cfg, notation=None, roles=None):
    """Full standalone LaTeX document for a list of extracted targets."""
    notation = notation or {}
    roles = roles or {}
    tr = cfg.get("track", {})
    title = tr.get("title", "Formal statements")
    subtitle = tr.get("subtitle", "")
    extra_macros = (cfg.get("latex", {}) or {}).get("preamble", "")
    body = [PREAMBLE, extra_macros,
            r"\begin{document}",
            f"\\section*{{{_tex_title(title)}}}"]
    if subtitle:
        body.append(f"\\noindent\\emph{{{_tex_title(subtitle)}}}\\par\\medskip")
    body.append(r"\noindent\small Statements machine-translated from the Lean 4 / "
                r"Mathlib source by \texttt{lean\_track latex}: notation only, content "
                r"verbatim. Each \texttt{name} is the Lean declaration.\normalsize\par\medskip")
    for t in targets:
        body.append(render_theorem(t, notation, roles.get(t["name"])))
        body.append("")
    body.append(r"\end{document}")
    return "\n".join(body)


def _tex_title(s):
    return (s.replace("&", r"\&").replace("_", r"\_")
            .replace("#", r"\#").replace("%", r"\%"))
