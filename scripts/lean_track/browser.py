"""Render a project dependency closure (probe.browser_closure) as a hyperlinked,
nicely-printed math browser: each declaration's conclusion/signature in KaTeX, with
`uses` / `used by` links to follow the dependency network deeper, and a source link
to the exact Lean file + line on GitHub.
"""
import re

from . import latex_tree, latexify

REPO_URL = "https://github.com/kaplan196883/QIQT-H"
SRC_PREFIX = "lean/mathlib"           # QIQTH modules live under here in the repo


def _slug(name):
    return "d-" + re.sub(r"[^A-Za-z0-9]+", "-", name).strip("-").lower()


def _source_url(module, line, ref="main"):
    if not module:
        return None
    path = f"{SRC_PREFIX}/{module.replace('.', '/')}.lean"
    anchor = f"#L{line}" if line else ""
    return f"{REPO_URL}/blob/{ref}/{path}{anchor}"


def _modslug(module):
    return "sec-" + re.sub(r"[^A-Za-z0-9]+", "-", module).strip("-").lower()


def _kindword(d, roles):
    """Book environment for a declaration."""
    if roles.get(d["name"]):
        return "Theorem"              # the tracked headline results
    if d["kind"] == "def":
        return "Definition"
    if d["kind"] == "axiom":
        return "Axiom"
    return "Lemma"


_ABBR = {"Theorem": "Thm", "Definition": "Def", "Lemma": "Lem", "Axiom": "Ax"}


def _claim_tex(d, notation):
    """A theorem's conclusion as one or more LaTeX strings (∧ split into parts)."""
    _, body = latex_tree._claim(d.get("type"), notation)
    return [latex_tree.tex_of_tree(c, notation) for c in latex_tree._conjuncts(body)]


def render_browser(decls, notation=None, roles=None, ref="main"):
    notation = {**latexify.DEFAULT_NOTATION, **(notation or {})}
    roles = roles or {}
    present = {d["name"]: d for d in decls}
    latex_tree._LINKS = {n: f"#{_slug(n)}" for n in present}    # in-formula links

    # reading order: by module, then by source line — and number the whole book.
    order = sorted(decls, key=lambda d: (d.get("module", ""), d.get("line") or 0))
    label = {}                          # name -> (number, kindword)
    for i, d in enumerate(order, 1):
        label[d["name"]] = (i, _kindword(d, roles))

    usedby = {n: [] for n in present}
    for d in decls:
        for u in d.get("usesStmt", []) + d.get("usesProof", []):
            if u in usedby:
                usedby[u].append(d["name"])

    def cite(name):
        if name in label:
            num, kw = label[name]
            return f"[{_ABBR[kw]} {num}](#{_slug(name)})"
        return f"`{name.split('.')[-1]}`"   # outside the closure -> plain

    def cite_list(names):
        names = [n for n in dict.fromkeys(names) if n in present]
        return ", ".join(cite(n) for n in sorted(names, key=lambda n: label[n][0]))

    out = []
    # table of contents (sections = modules, in reading order)
    mods = list(dict.fromkeys(d.get("module", "?") for d in order))
    out.append("## Contents\n")
    for m in mods:
        out.append(f"- [{m}](#{_modslug(m)})")
    out.append("")

    cur = None
    for d in order:
        name, short = d["name"], d["name"].split(".")[-1]
        mod = d.get("module", "?")
        if mod != cur:
            cur = mod
            out.append(f'<a id="{_modslug(mod)}"></a>')
            out.append(f"## {mod}")
            out.append("")
        num, kw = label[name]
        src = _source_url(mod, d.get("line"), ref)
        srctag = f" &nbsp;<small>[source ↗]({src})</small>" if src else ""
        out.append(f'<a id="{_slug(name)}"></a>')
        out.append(f"**{kw} {num}** (`{short}`).{srctag}")
        out.append("")
        if kw == "Definition":
            dlist = cite_list(d.get("usesStmt", []))
            out.append("A definition" + (f", built from {dlist}" if dlist else "")
                       + " — see source for the body.")
        else:
            parts = _claim_tex(d, notation)
            if len(parts) > 1:                 # multi-part conclusion -> stacked displays
                out.append("The following hold.")
                out.append("")
                for k, p in enumerate(parts, 1):
                    out.append("$$")
                    out.append(rf"\text{{({k})}}\quad {p}")
                    out.append("$$")
            else:
                out.append("$$")
                out.append(parts[0])
                out.append("$$")
            out.append("")
            cites = cite_list(d.get("usesProof", []))
            if cites:
                out.append(f"*Proof.* By {cites}. $\\square$")
            else:
                out.append(r"*Proof.* Immediate from the definitions. $\square$")
        ub = cite_list(usedby.get(name, []))
        if ub:
            out.append("")
            out.append(f"<small>Referenced in {ub}.</small>")
        out.append("")
    return "\n".join(out)
