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
title: Theorem browser
eyebrow: Hyperlinked dependency network
description: Browse the QIQT-H Lean development as a network of nicely-printed theorems — follow the uses / used-by links deeper, jump to the Lean source.
---

A hyperlinked browser over the Lean development. Each **theorem** is rendered in printed math
(its conclusion; free variables are implicitly universally quantified); **definitions** are
navigation nodes. Follow the dependency network through the *uses* and *used by* links, or jump
to the exact **Lean source** line on GitHub. Regenerate with `scripts/gen_browser_page.py`.
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
