"""Render the delaborated Lean `Syntax` tree (from probe.syntax_trees) to LaTeX.

Prototype of the AST route: instead of reconstructing structure from a flat
pretty-printed string (latexify.py), we walk the parenthesized Syntax tree, so
application arity, if-then-else, the eventually-filter, big operators, etc. are
known exactly — no regex heuristics. Reuses latexify's symbol maps, identifier
renderer, and the `[latex.notation]` glossary (templates apply by exact arity).
"""
import re

from . import latexify

# atoms that are whole words rather than single glyphs
ATOM_WORDS = {
    "fun": r"\lambda ", "=>": r" \mapsto ", "↦": r" \mapsto ",
    "↑": "", "⇑": "", "↥": "", "⁻¹": "^{-1}", "⁻¹'": "^{-1}", ":": " : ",
}
_SPACED = {"→": r" \to ", ",": ", ", "∧": r" \wedge ", "∨": r" \vee "}

# name -> href URL, for in-formula hyperlinks (set by the caller around a render).
# When an identifier in a formula names a declaration with an entry, it is wrapped
# in \href so clicking the symbol jumps to that declaration.
_LINKS = {}


def _wrap_link(name, tex):
    url = _LINKS.get(name)
    return (r"\href{" + url + "}{" + tex + "}") if url else tex


def tex_atom(s):
    if s in ATOM_WORDS:
        return ATOM_WORDS[s]
    out, i, n = [], 0, len(s)
    while i < n:
        ch = s[i]
        if ch in _SPACED:
            out.append(_SPACED[ch]); i += 1
        elif ch == "*":
            out.append(r"\cdot"); i += 1
        elif ch in "{}":                 # literal set-builder braces -> \{ \}
            out.append("\\" + ch); i += 1
        elif ch in latexify.SUPERS:      # collapse a RUN of superscripts (⁻¹ -> ^{-1})
            run = ""
            while i < n and s[i] in latexify.SUPERS:
                run += latexify.SUPERS[s[i]]; i += 1
            out.append("^{" + run + "}")
        elif ch in latexify.SUBS:
            run = ""
            while i < n and s[i] in latexify.SUBS:
                run += latexify.SUBS[s[i]]; i += 1
            out.append("_{" + run + "}")
        elif ch in latexify.SYMBOLS:
            out.append(latexify.SYMBOLS[ch]); i += 1
        elif ch in latexify.GREEK:
            out.append(latexify.GREEK[ch]); i += 1
        else:
            out.append(ch); i += 1
    return "".join(out)


def _strip_parens(s):
    """Remove one balanced outer (...) so a template's own parens don't double up."""
    s = s.strip()
    if not (s.startswith("(") and s.endswith(")")):
        return s
    depth = 0
    for idx, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return s[1:-1] if idx == len(s) - 1 else s
    return s


def _join_app(parts):
    """Join an application head + args with thin spaces (parens already in tree)."""
    return r"\,".join(p for p in parts if p != "")


def _app_pieces(node):
    """An app node -> (fn_node, [arg_nodes])."""
    a = node["args"]
    fn = a[0]
    args = a[1]["args"] if len(a) > 1 and a[1].get("kind") == "null" else []
    return fn, args


def _fire_template(val, rargs):
    """Apply a #k template to already-rendered args (arity-aware)."""
    argc = max(int(d) for d in re.findall(r"#(\d+)", val))
    if len(rargs) < argc:
        return None
    sub = [_strip_parens(a) for a in rargs]      # template controls bracketing
    filled = re.sub(r"#(\d+)", lambda m: "{" + sub[int(m.group(1)) - 1] + "}", val)
    rest = rargs[argc:]
    return _join_app([filled] + rest)


def render(node, notation):
    if not node or not isinstance(node, dict):
        return ""
    k = node.get("k")
    if k == "atom":
        return tex_atom(node["v"])
    if k == "ident":
        # full string translation handles Greek + sub/superscripts (e.g. e₁ -> e_{1})
        # and notation; app heads are resolved earlier so this is only operands/indices.
        return _wrap_link(node["v"], latexify.tex_of_pp(node["v"], notation))
    if k != "node":
        return ""
    kind, A = node["kind"], node["args"]

    if kind == "Lean.Parser.Term.app":
        fn, args = _app_pieces(node)
        rargs = [render(a, notation) for a in args]
        head = fn["v"] if fn.get("k") == "ident" else None
        if head is not None:
            val = latexify._lookup(head, notation)
            if val and re.search(r"#\d", val):
                fired = _fire_template(val, rargs)
                if fired is not None:
                    # wrap the whole tensor unless an argument already carries a link
                    return fired if r"\href" in fired else _wrap_link(head, fired)
            return _join_app([_wrap_link(head, latexify._render_ident(head, notation))]
                             + rargs)
        return _join_app([render(fn, notation)] + rargs)

    if kind == "termIfThenElse":
        # [if, cond, then, tval, else, eval]
        cond, tval, eval_ = A[1], A[3], A[5]
        rt, re_ = render(tval, notation), render(eval_, notation)
        if rt == "1" and re_ == "0" and cond.get("kind") == "«term_=_»":
            lo = render(cond["args"][0], notation)
            hi = render(cond["args"][2], notation)
            return r"\delta_{" + lo + hi + "}"
        return (r"\text{if }" + render(cond, notation) + r"\text{ then }" + rt
                + r"\text{ else }" + re_)

    if kind in ("BigOperators.bigsum", "BigOperators.bigprod"):
        # [∑/∏, bigOpBinders, null, ',', body]
        op = r"\prod" if kind.endswith("bigprod") else r"\sum"
        binder = _sum_binder(A[1], notation)
        return op + "_{" + binder + "} " + render(A[-1], notation)

    if kind == "Filter.«term∀ᶠ_In_,_»":
        return _eventually(A, notation)

    if kind == "«term_^_»":
        return "{" + render(A[0], notation) + "}^{" + render(A[2], notation) + "}"

    if kind == "«term_⁻¹»":
        return "{" + render(A[0], notation) + "}^{-1}"

    if kind == "coeNotation":               # ↑x -> x
        return "".join(render(a, notation) for a in A
                       if not (a.get("k") == "atom" and a.get("v") in ("↑", "⇑", "↥")))

    if kind == "termℝ":
        return r"\mathbb{R}"

    if kind == "hygieneInfo":               # invisible hygiene metadata
        return ""

    if kind == "null":                       # binder lists etc. — space-separated
        return " ".join(render(a, notation) for a in A)

    # generic: concatenate children (operator atoms carry their own spacing)
    return "".join(render(a, notation) for a in A)


def _sum_binder(binders_node, notation):
    """Pull the bound variable(s) out of a BigOperators.bigOpBinders node."""
    idents = []

    def walk(n):
        if isinstance(n, dict):
            if n.get("k") == "ident":
                idents.append(latexify._render_ident(n["v"], notation))
            for a in n.get("args", []):
                walk(a)
    walk(binders_node)
    return " ".join(idents)


def _eventually(A, notation):
    """Filter.«∀ᶠ x In F, P» -> 'for x near c, P' when F is nhds c."""
    idents, filt, body = [], None, A[-1]

    def walk_binder(n):
        if isinstance(n, dict):
            if n.get("k") == "ident":
                idents.append(latexify._render_ident(n["v"], notation))
            for a in n.get("args", []):
                walk_binder(a)
    # A = [∀ᶠ, binders, 'in'?, filter, ',', body]; binders is A[1], filter A[3]
    walk_binder(A[1])
    filt = A[3] if len(A) > 4 else None
    near = ""
    if filt and filt.get("kind") == "Lean.Parser.Term.app":
        fn, args = _app_pieces(filt)
        if fn.get("k") == "ident" and fn["v"].split(".")[-1] == "nhds" and args:
            near = render(args[0], notation)
    var = " ".join(idents)
    if near:
        return r"\text{for }" + var + r"\text{ near }" + near + r",\; " + render(body, notation)
    return r"\forall^{f} " + var + ", " + render(body, notation)


def tex_of_tree(node, notation=None):
    notation = {**latexify.DEFAULT_NOTATION, **(notation or {})}
    tex = render(node, notation)
    # a prime ' immediately after a braced super/subscript is a second superscript
    # to KaTeX ("Double superscript"): insert an empty group to separate them.
    tex = tex.replace("}'", "}{}'")
    # safety net: drop any glyph that escaped every map so output always compiles,
    # recording it (shared with latexify) for review.
    leftover = sorted({ch for ch in tex if ord(ch) > 0x7F})
    if leftover:
        latexify._UNMAPPED.update(leftover)
        tex = re.sub(r"[^\x00-\x7F]", "", tex)
    tex = re.sub(r"\s+", " ", tex).strip()
    return tex


# ---------------------------------------------------------------------------- #
#  document assembly (mirrors latexify.render_theorem/render_document, tree-fed)
# ---------------------------------------------------------------------------- #
def render_theorem(t, notation=None, role_label=None):
    notation = {**latexify.DEFAULT_NOTATION, **(notation or {})}
    name = t["name"]
    if not t.get("present"):
        return (f"\\paragraph{{\\texttt{{{latexify._texname(name)}}}}}"
                f" \\emph{{(not found in the current build)}}\n")
    env = "definition" if t.get("kind") == "def" else "theorem"
    data, hyps = [], []
    for b in t.get("binders", []):
        if b["kind"] == "prop":
            hyps.append((b["name"], tex_of_tree(b["type"], notation)))
        elif b["kind"] == "data":
            data.append(latexify._texname(b["name"]))
    lines = [f"\\begin{{{env}}}[\\texttt{{{latexify._texname(name)}}}]"
             f"\\label{{{latexify._texlabel(name)}}}"]
    if role_label:
        lines.append(f"\\textit{{{role_label}.}}")
    if data:
        lines.append("Given " + ", ".join(f"${d}$" for d in data)
                     + ("." if not hyps else ","))
    if hyps:
        lines.append("assume")
        lines.append(r"\begin{itemize}")
        for hn, rt in hyps:
            lines.append(f"  \\item[\\rm({latexify._hyp_label(hn)})] ${rt}$")
        lines.append(r"\end{itemize}")
    lead = "Then" if (data or hyps) else "We have"
    lines.append(f"{lead} \\[ {tex_of_tree(t.get('concl'), notation)} \\]")
    lines.append(f"\\end{{{env}}}")
    return "\n".join(lines) + "\n"


# hypothesis categories that are routine scaffolding — summarised, not listed.
_SUMMARISE_CATS = {"regularity", "setup", "background", "structure",
                   "kinematics", "bridge"}


def _peel_forall(node):
    """Drop leading universal quantifiers (free-index convention)."""
    while isinstance(node, dict) and node.get("kind") == "Lean.Parser.Term.forall":
        node = node["args"][-1]
    return node


def _category_of(name, rules):
    """First category_rule whose name_regex matches `name` (type_regex rules skipped
    here — we only have the name at web-render time)."""
    for r in rules:
        nre = r.get("name_regex")
        if nre and r.get("type_regex"):
            continue                      # needs the type string we don't carry here
        if nre and re.search(nre, name):
            return r.get("category", "?")
    return None


def _conjuncts(node):
    """Flatten a top-level ∧ chain into its conjuncts."""
    if isinstance(node, dict) and node.get("kind") == "«term_∧_»":
        a = node["args"]
        return _conjuncts(a[0]) + _conjuncts(a[-1])
    return [node]


def _claim(concl, notation):
    """(prose lead, body node) for a conclusion, peeling ∀ and naming any leading ∃."""
    n = concl if isinstance(concl, dict) else {}
    if "∃" in n.get("kind", ""):
        vs = []

        def gv(x):
            if isinstance(x, dict):
                if x.get("k") == "ident":
                    vs.append(latexify.tex_of_pp(x["v"], notation))
                for a in x.get("args", []):
                    gv(a)
        gv(n["args"][1])                  # the bound variable(s)
        uniq = "!" in n.get("kind", "")
        lead = ("there is a unique " if uniq else "there is ") + \
               "$" + ",\\ ".join(vs) + "$ such that" if vs else "we have"
        return lead, _peel_forall(n["args"][-1])
    return "we have", _peel_forall(concl)


def render_web(trees, cfg, notation=None, roles=None, heading="###"):
    """Paper-style Markdown (KaTeX) rendering of a track's statements for the website.

    Reads like a theorem list, not a hypothesis dump: leading ∀/types are factored
    out (free-index convention), the conclusion leads in display math, load-bearing
    hypotheses are shown while routine ones (regularity/setup/…) are summarised by
    count. Per-theorem display titles come from `[[theorems]] display = "..."`.
    """
    notation = {**latexify.DEFAULT_NOTATION, **(notation or {})}
    roles = roles or {}
    rules = cfg.get("category_rules", [])
    displays = {t["name"]: t.get("display") for t in cfg.get("theorems", [])}
    out = []
    for t in trees:
        nm = t["name"]
        short = nm.split(".")[-1]
        role = roles.get(nm)
        title = displays.get(nm) or f"`{short}`"
        out.append(f"{heading} {title}")
        out.append("")
        tag = f"`{short}`" + (f" · *{role}*" if role else "")
        if not t.get("present"):
            out.append(f"{tag} — *(not in the current build)*\n")
            continue
        lead, body_node = _claim(t.get("concl"), notation)
        parts = _conjuncts(body_node)
        if len(parts) > 1:                # multi-part conclusion -> numbered list
            out.append(f"{tag} —  {lead} all of:")
            out.append("")
            for idx, c in enumerate(parts, 1):
                out.append(f"{idx}. ${tex_of_tree(c, notation)}$")
            out.append("")
        else:
            out.append(f"{tag} —  {lead}")
            out.append("")
            out.append(f"$$ {tex_of_tree(body_node, notation)} $$")
            out.append("")
        featured, summ = [], {}
        for b in t.get("binders", []):
            if b["kind"] != "prop":
                continue
            hn = b["name"]
            if hn.startswith("inst") or "._@." in hn or "_hyg" in hn:
                summ["typeclass"] = summ.get("typeclass", 0) + 1
                continue
            cat = _category_of(hn, rules)
            if cat in _SUMMARISE_CATS:
                summ[cat] = summ.get(cat, 0) + 1
            else:
                featured.append((hn, _peel_forall(b["type"])))
        if featured:
            # factor a common leading antecedent (e.g. the null condition g_x(v,v)=0)
            def _arrow(n):
                if isinstance(n, dict) and n.get("kind") == "Lean.Parser.Term.arrow":
                    return n["args"][0], n["args"][-1]
                return None, None
            ante = {hn: (tex_of_tree(_arrow(nd)[0], notation) if _arrow(nd)[0] else None)
                    for hn, nd in featured}
            from collections import Counter
            cnt = Counter(a for a in ante.values() if a)
            common = cnt.most_common(1)[0][0] if cnt and cnt.most_common(1)[0][1] >= 2 else None
            out.append("*assuming*")
            out.append("")
            if common:
                out.append(f"when $ {common} $&nbsp;:")
                out.append("")
                for hn, nd in featured:
                    if ante[hn] == common:
                        out.append(f"- `{hn}` &nbsp; ${tex_of_tree(_arrow(nd)[1], notation)}$")
                rest = [(hn, nd) for hn, nd in featured if ante[hn] != common]
                if rest:
                    out.append("")
                    out.append("and")
                    out.append("")
                    for hn, nd in rest:
                        out.append(f"- `{hn}` &nbsp; ${tex_of_tree(nd, notation)}$")
            else:
                for hn, nd in featured:
                    out.append(f"- `{hn}` &nbsp; ${tex_of_tree(nd, notation)}$")
            out.append("")
        if summ:
            parts = ", ".join(f"{n} {c}" for c, n in sorted(summ.items()))
            out.append(f"<small>plus {sum(summ.values())} routine conditions "
                       f"({parts}) — full list in the per-track PDF.</small>")
            out.append("")
    return "\n".join(out)


def render_document(trees, cfg, notation=None, roles=None):
    notation = notation or {}
    roles = roles or {}
    tr = cfg.get("track", {})
    body = [latexify.PREAMBLE, (cfg.get("latex", {}) or {}).get("preamble", ""),
            r"\begin{document}",
            f"\\section*{{{latexify._tex_title(tr.get('title', 'Formal statements'))}}}"]
    if tr.get("subtitle"):
        body.append(f"\\noindent\\emph{{{latexify._tex_title(tr['subtitle'])}}}"
                    r"\par\medskip")
    body.append(r"\noindent\small Statements machine-translated from the Lean 4 / "
                r"Mathlib source by \texttt{lean\_track latex}: rendered from the "
                r"delaborated \emph{Syntax tree} (notation only, content verbatim).\normalsize"
                r"\par\medskip")
    for t in trees:
        body.append(render_theorem(t, notation, roles.get(t["name"])))
        body.append("")
    body.append(r"\end{document}")
    return "\n".join(body)
