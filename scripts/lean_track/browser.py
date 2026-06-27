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


def _peel_lambda(node):
    """A `fun a b … => body` value -> ([binder ident nodes], body node)."""
    binders = []
    while isinstance(node, dict) and node.get("kind") in (
            "Lean.Parser.Term.fun", "Lean.Parser.Term.basicFun"):
        args = node["args"]
        if node["kind"] == "Lean.Parser.Term.fun":          # [atom"fun", basicFun]
            node = args[-1]
            continue
        # basicFun: [binders, atom"=>", body]
        def collect(n):
            if isinstance(n, dict):
                if n.get("k") == "ident":
                    binders.append(n)
                else:
                    for a in n.get("args", []):
                        collect(a)
        collect(args[0])
        node = args[-1]
    return binders, node


def _definition_tex(d, notation, max_len=900):
    """`LHS := body` for a definition with a body. Uses the notation template for the
    LHS only when its arity matches the binder count (else a plain `name args` LHS, to
    avoid mis-indexed output like R_{giσ}(ν))."""
    val = d.get("value")
    if not val:
        return None
    binders, body = _peel_lambda(val)
    name = d["name"]
    tmpl = latexify._lookup(name, notation) or latexify._lookup(name.split(".")[-1], notation)
    argc = max((int(x) for x in re.findall(r"#(\d+)", tmpl)), default=0) if tmpl else 0
    if binders and argc and len(binders) == argc:
        head = {"k": "ident", "v": name}
        lhs = latex_tree.tex_of_tree(
            {"k": "node", "kind": "Lean.Parser.Term.app",
             "args": [head, {"k": "node", "kind": "null", "args": binders}]}, notation)
    else:                                 # plain signature: name b1 … bn
        parts = [latexify._render_ident(name, notation)]
        parts += [latex_tree.tex_of_tree(b, notation) for b in binders]
        lhs = r"\,".join(parts)
    rhs = latex_tree.tex_of_tree(body, notation)
    if len(rhs) > max_len:               # huge body -> don't dump it
        return None
    return lhs + r" \;:=\; " + rhs


def _doc_lead(doc, max_len=760):
    """The author's docstring as book prose: drop priority stars, collapse intra-paragraph
    line wraps, keep paragraph breaks, and cap politely at a sentence boundary."""
    if not doc:
        return None
    s = doc.replace("★", "").replace("☆", "").strip()
    s = re.sub(r"(^|\s)\*\*[ \t]+", r"\1**", s)   # heal '** text' opener left by stripped stars
    paras = [re.sub(r"\s*\n\s*", " ", p).strip() for p in re.split(r"\n\s*\n", s)]
    paras = [p for p in paras if p]
    if not paras:
        return None
    lead, i = paras[0], 1
    while i < len(paras) and len(lead) + len(paras[i]) + 2 < max_len:
        lead += "\n\n" + paras[i]
        i += 1
    if len(lead) > max_len or i < len(paras):
        cut = lead[:max_len]
        m = max(cut.rfind(". "), cut.rfind(".\n"))
        if m > max_len * 0.5:
            cut = cut[:m + 1]
        lead = cut.rstrip().rstrip(".") + ". …"
    return lead


def _pageslug(module):
    return re.sub(r"[^a-z0-9]+", "-", (module or "misc").lower()).strip("-")


def browser_href_map(decls):
    """name -> /browser/<page>#<anchor> for every declaration (for cross-page links from
    other pages, e.g. the statements page)."""
    return {d["name"]: f"/browser/{_pageslug(d.get('module', '?'))}#{_slug(d['name'])}"
            for d in decls}


def _entry_md(d, notation, label, cite_list, usedby, ref):
    """One book entry (definition/lemma/theorem) as a list of markdown lines."""
    name, short = d["name"], d["name"].split(".")[-1]
    mod = d.get("module", "?")
    num, kw = label[name]
    out = []
    src = _source_url(mod, d.get("line"), ref)
    srctag = f" &nbsp;<small>[source ↗]({src})</small>" if src else ""
    out.append(f'<a id="{_slug(name)}"></a>')
    out.append(f"**{kw} {num}** (`{short}`).{srctag}")
    out.append("")
    lead = _doc_lead(d.get("doc"))          # the author's own prose explanation
    if lead:
        out.append(lead)
        out.append("")
    if kw == "Definition":
        body = _definition_tex(d, notation)
        if body:
            out += ["$$", body, "$$"]
        else:
            dlist = cite_list(d.get("usesStmt", []))
            out.append("A definition" + (f", built from {dlist}" if dlist else "")
                       + " — see source for the body.")
    else:
        parts = _claim_tex(d, notation)
        if len(parts) > 1:                  # multi-part conclusion -> stacked displays
            out += ["The following hold.", ""]
            for k, p in enumerate(parts, 1):
                out += ["$$", rf"\text{{({k})}}\quad {p}", "$$"]
        else:
            out += ["$$", parts[0], "$$"]
        out.append("")
        cites = cite_list(d.get("usesProof", []))
        if cites:
            out.append(f"*Proof.* By {cites}. $\\square$")
        else:
            out.append(r"*Proof.* Immediate from the definitions. $\square$")
    ub = cite_list(usedby.get(name, []), cap=8)
    if ub:
        out += ["", f"<small>Used by {ub}.</small>"]
    out.append("")
    return out


def render_browser(decls, notation=None, roles=None, ref="main"):
    """Render the closure as a *nested* book: an index plus one page per Lean module.
    Returns {"index": <body>, "pages": [ {slug,title,group,count,body}, … ]} with all
    cross-references (citations + in-formula symbol links) pointing across pages."""
    notation = {**latexify.DEFAULT_NOTATION, **(notation or {})}
    roles = roles or {}
    present = {d["name"]: d for d in decls}

    # reading order: by module, then by source line — and number the whole book.
    order = sorted(decls, key=lambda d: (d.get("module", ""), d.get("line") or 0))
    label, page_of = {}, {}
    for i, d in enumerate(order, 1):
        label[d["name"]] = (i, _kindword(d, roles))
        page_of[d["name"]] = _pageslug(d.get("module", "?"))

    # cross-page hrefs: /browser/<page>#<anchor> (works same-page and across pages).
    def href(name):
        return f"/browser/{page_of[name]}#{_slug(name)}"
    latex_tree._LINKS = {n: href(n) for n in present}          # in-formula symbol links

    usedby = {n: [] for n in present}
    for d in decls:
        for u in d.get("usesStmt", []) + d.get("usesProof", []):
            if u in usedby:
                usedby[u].append(d["name"])

    def cite(name):
        short = name.split(".")[-1]
        if name in present:
            return f"[`{short}`]({href(name)})"
        return f"`{short}`"                 # outside the closure -> plain
    cite.__wrapped_present__ = present

    def cite_list(names, cap=None):
        names = [n for n in dict.fromkeys(names) if n in present]
        names.sort(key=lambda n: label[n][0])
        if cap and len(names) > cap:
            shown = ", ".join(cite(n) for n in names[:cap])
            return f"{shown}, and {len(names) - cap} more"
        return ", ".join(cite(n) for n in names)

    # one page per module, in reading order.
    mods = list(dict.fromkeys(d.get("module", "?") for d in order))
    by_mod = {m: [d for d in order if d.get("module", "?") == m] for m in mods}

    def group_of(module):                   # 2nd namespace component, e.g. QIQTH.Fock.* -> Fock
        parts = (module or "").split(".")
        return parts[1] if len(parts) > 2 else (parts[-1] if parts else "misc")

    pages = []
    for idx, m in enumerate(mods):
        ds = by_mod[m]
        nums = [label[d["name"]][0] for d in ds]
        prev_m, next_m = (mods[idx - 1] if idx else None), (mods[idx + 1] if idx + 1 < len(mods) else None)
        nav = ['<small>[← all sections](/browser)']
        if prev_m:
            nav.append(f"· [← {prev_m.split('.')[-1]}](/browser/{_pageslug(prev_m)})")
        if next_m:
            nav.append(f"· [{next_m.split('.')[-1]} →](/browser/{_pageslug(next_m)})")
        nav.append("</small>")
        body = [" ".join(nav), "",
                f"<small>{group_of(m)} · entries {nums[0]}–{nums[-1]} of {len(order)}</small>", ""]
        for d in ds:
            body += _entry_md(d, notation, label, cite_list, usedby, ref)
        body += ["---", " ".join(nav)]
        pages.append({"slug": _pageslug(m), "title": m, "group": group_of(m),
                      "count": len(ds), "body": "\n".join(body),
                      "nums": (nums[0], nums[-1])})

    # index: sections grouped by top-level namespace, each linking to its page.
    groups = list(dict.fromkeys(p["group"] for p in pages))
    ix = [f"A hyperlinked math book in **{len(pages)} sections** ({len(order)} numbered "
          "definitions, lemmas and theorems). Pick a section:", ""]
    for g in groups:
        gp = [p for p in pages if p["group"] == g]
        tot = sum(p["count"] for p in gp)
        ix.append(f"### {g} &nbsp;<small>({tot})</small>")
        ix.append("")
        for p in gp:
            ix.append(f"- [{p['title']}](/browser/{p['slug']}) "
                      f"&nbsp;<small>{p['count']} entries (#{p['nums'][0]}–{p['nums'][1]})</small>")
        ix.append("")
    return {"index": "\n".join(ix), "pages": pages}
