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

FRONTMATTER = """---
layout: ../layouts/Deep.astro
title: Machine-rendered statements
eyebrow: Auto-generated from Lean
description: The QIQT-H theorem statements, machine-translated from the Lean 4 / Mathlib source to readable math — conclusion first, load-bearing hypotheses shown, routine conditions summarized.
---

Each result below is **machine-translated from the Lean&nbsp;4 / Mathlib source** by the project
tool (`lean_track latex`), which walks the *delaborated syntax tree* of every declaration. The
content is **verbatim**; only the presentation is editorial — leading universal quantifiers and
type ascriptions are factored out (free variables are implicitly universally quantified: $x$ ranges
over spacetime points, indices $\\mu,\\nu$ over $\\{0,1,2,3\\}$, $v$ over tangent vectors), the
**conclusion leads** in display math, the **load-bearing hypotheses are shown**, and routine
regularity / setup / typeclass conditions are summarized by count (the full assumption surface lives
in each track's PDF). Labels like `hFlux` are the Lean hypothesis names. To explore the full
dependency network — every lemma and definition these results rest on, hyperlinked, with source
links — see the [**theorem browser**](/browser). Regenerate with
`python scripts/lean-track.py latex -c tracks/<id>.toml`.
"""


def main():
    # in-formula links point into the browser page (which has the full declaration set),
    # so clicking a symbol on the clean statements page jumps to its entry there.
    closure_path = REPO / "reports" / "browser" / "closure.json"
    if closure_path.exists():
        names = [d["name"] for d in json.loads(closure_path.read_text(encoding="utf-8"))]
        latex_tree._LINKS = {n: f"/browser#{browser._slug(n)}" for n in names}
    body, total = [FRONTMATTER], 0
    for tid, subtitle in TRACKS:
        cfg = probe.load_config(REPO / "tracks" / f"{tid}.toml")
        notation = (cfg.get("latex", {}) or {}).get("notation", {})
        roles = {t["name"]: t.get("role") for t in cfg["theorems"]}
        trees = json.loads((REPO / "reports" / tid / "syntax_trees.json")
                           .read_text(encoding="utf-8"))
        total += len(trees)
        body.append(f"\n## {cfg['track']['title']}\n")
        body.append(f"*{subtitle}*\n")
        body.append(latex_tree.render_web(trees, cfg, notation=notation, roles=roles,
                                          heading="###"))
    out = REPO / "website" / "src" / "pages" / "statements.md"
    out.write_text("\n".join(body), encoding="utf-8")
    unmapped = " ".join(sorted(latexify._UNMAPPED)) or "(none)"
    print(f"wrote {out.relative_to(REPO)}: {total} theorems · unmapped: {unmapped}")


if __name__ == "__main__":
    main()
