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


def _statement(d, notation):
    """Conclusion (for theorems) or full signature (for defs) as a LaTeX string."""
    ty = d.get("type")
    if d["kind"] in ("thm", "axiom", "opaque"):
        _, body = latex_tree._claim(ty, notation)
        return latex_tree.tex_of_tree(body, notation)
    return latex_tree.tex_of_tree(ty, notation)


def render_browser(decls, notation=None, roles=None, ref="main"):
    notation = {**latexify.DEFAULT_NOTATION, **(notation or {})}
    roles = roles or {}
    present = {d["name"]: d for d in decls}
    # in-formula hyperlinks: every named declaration links to its entry's anchor
    latex_tree._LINKS = {n: f"#{_slug(n)}" for n in present}
    # "used by" backlinks (a theorem is used in the proof/statement of ...)
    usedby = {n: [] for n in present}
    for d in decls:
        for u in d.get("usesStmt", []) + d.get("usesProof", []):
            if u in usedby:
                usedby[u].append(d["name"])

    def link(name):
        short = name.split(".")[-1]
        if name in present:
            return f"[`{short}`](#{_slug(name)})"
        return f"`{short}`"

    def link_row(label, names):
        names = [n for n in names if n in present]
        if not names:
            return None
        return f"**{label}** " + " ".join(link(n) for n in sorted(set(names)))

    out = []
    by_mod = {}
    for d in decls:
        by_mod.setdefault(d.get("module", "?"), []).append(d)
    out.append("## Index\n")
    for mod in sorted(by_mod):
        names = ", ".join(link(d["name"]) for d in
                          sorted(by_mod[mod], key=lambda d: d["name"]))
        out.append(f"- **{mod.split('.')[-1] or mod}** &nbsp; {names}")
    out.append("\n## Declarations\n")
    order = sorted(decls, key=lambda d: (d["kind"] != "thm", d["name"]))
    for d in order:
        name = d["name"]
        short = name.split(".")[-1]
        out.append(f'<a id="{_slug(name)}"></a>')
        role = roles.get(name)
        src = _source_url(d.get("module"), d.get("line"), ref)
        meta = f"*{d['kind']}*" + (f" · *{role}*" if role else "")
        if src:
            meta += f" · [{d.get('module','').split('.')[-1]}:{d.get('line','')} ↗]({src})"
        out.append(f"### `{short}`")
        out.append("")
        out.append(meta + "  ")
        out.append("")
        if d["kind"] in ("thm", "axiom", "opaque"):
            out.append("$$")           # delimiters on their own lines -> display block
            out.append(_statement(d, notation))
            out.append("$$")
            out.append("")
        # the proof network: the lemmas this proof invokes are the edges to dig into.
        prooflabel = "defined using" if d["kind"] == "def" else "proof uses"
        for row in (link_row(prooflabel, d.get("usesProof", [])),
                    link_row("statement uses", d.get("usesStmt", [])),
                    link_row("used by", usedby.get(name, []))):
            if row:
                out.append(row)
        out.append("")
    return "\n".join(out)
