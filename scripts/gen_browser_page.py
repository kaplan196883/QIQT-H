#!/usr/bin/env python3
"""Generate website/src/pages/browser.md from a cached project dependency closure.

Refresh the closure first with:
    PYTHONPATH=scripts python -c "import json; from lean_track import probe; \
      cfg=probe.load_config('tracks/gr.toml'); \
      json.dump(probe.browser_closure([<roots>], cfg, maxdecls=600), \
                open('reports/browser/closure.json','w'))"
then run this to (re)render the page.
"""
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from lean_track import browser, probe  # noqa: E402

REPO = HERE.parent
CLOSURE = REPO / "reports" / "browser" / "closure.json"

FRONTMATTER = """---
layout: ../layouts/Deep.astro
title: The development as a book
eyebrow: Definitions · theorems · lemmas · proofs
description: The QIQT-H Lean development presented as a hyperlinked math book — definitions, theorems and lemmas in printed math, each proof citing the lemmas it uses, all linked down to the Lean source.
---

The Lean development, presented as a **hyperlinked math book**. It is organized into sections (one
per Lean module, in dependency order); each entry is a numbered **Definition**, **Theorem** or
**Lemma**, typeset in printed math (free variables are implicitly universally quantified). Every
**Proof** cites the lemmas it rests on — click a citation to jump to that result, read it, and
follow *its* proof deeper; symbols inside the formulas link to their definitions; and a *source ↗*
link on each entry opens the exact Lean line. Regenerate with `scripts/gen_browser_page.py`.
"""


def main():
    decls = json.loads(CLOSURE.read_text(encoding="utf-8"))
    notation, roles = {}, {}
    for tid in ("gr", "born", "lorentz"):
        cfg = probe.load_config(REPO / "tracks" / f"{tid}.toml")
        notation.update((cfg.get("latex", {}) or {}).get("notation", {}))
        roles.update({t["name"]: t.get("role") for t in cfg["theorems"]})
    page = FRONTMATTER + "\n" + browser.render_browser(decls, notation=notation, roles=roles)
    out = REPO / "website" / "src" / "pages" / "browser.md"
    out.write_text(page, encoding="utf-8")
    print(f"wrote {out.relative_to(REPO)}: {len(decls)} declarations")


if __name__ == "__main__":
    main()
