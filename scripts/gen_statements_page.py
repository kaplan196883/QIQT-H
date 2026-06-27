#!/usr/bin/env python3
"""Generate website/src/pages/statements.md from the cached Syntax trees of each track.

Renders paper-style statements (latex_tree.render_web) for gr, born, lorentz into one
KaTeX markdown page. Regenerate the trees with `lean_track latex` (or probe.syntax_trees)
and re-run this to refresh the page.
"""
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from lean_track import browser, latex_tree, latexify, probe  # noqa: E402

REPO = HERE.parent
TRACKS = [
    ("gr", "Target 3 — QIQT-H gives the Einstein field equations"),
    ("born", "Target 1 — the Born rule: reductions and a no-go"),
    ("lorentz", "Target 2 — Lorentz covariance of the selection"),
]

INDEX_FM = """---
layout: ../layouts/Deep.astro
title: Machine-rendered statements
eyebrow: Auto-generated from Lean
description: The QIQT-H headline theorems, machine-translated from the Lean 4 / Mathlib source to readable math — one page per target track, each statement with the author's explanation, conclusion first, load-bearing hypotheses shown.
---

The three **headline targets** of the development, each on its own page. Every result is
**machine-translated from the Lean&nbsp;4 / Mathlib source** by the project tool
(`lean_track latex`), which walks the *delaborated syntax tree* of each declaration. The content is
**verbatim**; only the presentation is editorial — leading universal quantifiers and type
ascriptions are factored out (free variables are implicitly universally quantified: $x$ ranges over
spacetime points, indices $\\mu,\\nu$ over $\\{0,1,2,3\\}$, $v$ over tangent vectors), each statement
leads with the **author's explanation**, the **conclusion** follows in display math, the
**load-bearing hypotheses are shown**, and routine conditions are summarized by count. To explore
the full dependency network behind these results, see the [**theorem browser**](/browser).

"""

PAGE_FM = """---
layout: ../../layouts/Deep.astro
title: "{title}"
eyebrow: "{subtitle}"
description: "{title} — QIQT-H headline statements machine-translated from Lean, each with the author's explanation, conclusion and load-bearing hypotheses."
---

<small>[← all targets](/statements){nav}</small>

*{subtitle}*

"""


def main():
    # in-formula links point into the browser pages (which have the full declaration set),
    # so clicking a symbol on the clean statements pages jumps to its entry there.
    closure_path = REPO / "reports" / "browser" / "closure.json"
    docs = {}
    if closure_path.exists():
        decls = json.loads(closure_path.read_text(encoding="utf-8"))
        latex_tree._LINKS = browser.browser_href_map(decls)
        docs = {d["name"]: browser._doc_lead(d.get("doc")) for d in decls}

    pages_dir = REPO / "website" / "src" / "pages" / "statements"
    if pages_dir.exists():
        for f in pages_dir.glob("*.md"):
            f.unlink()
    pages_dir.mkdir(parents=True, exist_ok=True)

    slugs = {tid: tid for tid, _ in TRACKS}
    index, total = [INDEX_FM], 0
    for i, (tid, subtitle) in enumerate(TRACKS):
        cfg = probe.load_config(REPO / "tracks" / f"{tid}.toml")
        notation = (cfg.get("latex", {}) or {}).get("notation", {})
        roles = {t["name"]: t.get("role") for t in cfg["theorems"]}
        trees = json.loads((REPO / "reports" / tid / "syntax_trees.json")
                           .read_text(encoding="utf-8"))
        total += len(trees)
        title = cfg["track"]["title"]
        # prev/next nav between track pages
        nav = ""
        if i:
            pt, ps = TRACKS[i - 1]
            nav += f" · [← {ps.split('—')[0].strip()}](/statements/{pt})"
        if i + 1 < len(TRACKS):
            nt, ns = TRACKS[i + 1]
            nav += f" · [{ns.split('—')[0].strip()} →](/statements/{nt})"
        fm = PAGE_FM.format(title=title, subtitle=subtitle, nav=nav)
        body = latex_tree.render_web(trees, cfg, notation=notation, roles=roles,
                                     heading="##", docs=docs)
        (pages_dir / f"{tid}.md").write_text(fm + body, encoding="utf-8")
        index.append(f"### [{title}](/statements/{tid})")
        index.append("")
        index.append(f"*{subtitle}* &nbsp;<small>({len(trees)} statements)</small>")
        index.append("")

    out = REPO / "website" / "src" / "pages" / "statements.md"
    out.write_text("\n".join(index), encoding="utf-8")
    unmapped = " ".join(sorted(latexify._UNMAPPED)) or "(none)"
    print(f"wrote {out.relative_to(REPO)} + {len(TRACKS)} track pages: "
          f"{total} theorems · unmapped: {unmapped}")


if __name__ == "__main__":
    main()
