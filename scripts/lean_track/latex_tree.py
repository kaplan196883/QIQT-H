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
    "↑": "", "⇑": "", "↥": "", "⁻¹": "^{-1}", ":": " : ",
}


def tex_atom(s):
    if s in ATOM_WORDS:
        return ATOM_WORDS[s]
    out = []
    _SPACED = {"→": r" \to ", ",": ", ", "∧": r" \wedge ", "∨": r" \vee "}
    for ch in s:
        if ch in _SPACED:
            out.append(_SPACED[ch])
        elif ch == "*":
            out.append(r"\cdot")
        elif ch in latexify.SYMBOLS:
            out.append(latexify.SYMBOLS[ch])
        elif ch in latexify.GREEK:
            out.append(latexify.GREEK[ch])
        else:
            out.append(ch)
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
        return latexify._render_ident(node["v"], notation)
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
                    return fired
            return _join_app([latexify._render_ident(head, notation)] + rargs)
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

    if kind == "BigOperators.bigsum":
        # [∑, bigOpBinders, null, ',', body]
        binder = _sum_binder(A[1], notation)
        body = render(A[-1], notation)
        return r"\sum_{" + binder + "} " + body

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
    tex = re.sub(r"\s+", " ", tex).strip()
    return tex
