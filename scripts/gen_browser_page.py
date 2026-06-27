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

INDEX_FM = """---
layout: ../layouts/Deep.astro
title: The development as a book
eyebrow: Definitions · theorems · lemmas · proofs
description: The QIQT-H Lean development presented as a hyperlinked math book — definitions, theorems and lemmas in printed math, each with the author's explanation, each proof citing the lemmas it uses, all linked down to the Lean source.
---

The Lean development, presented as a **hyperlinked math book** split into one section per Lean
module. Each entry is a numbered **Definition**, **Theorem** or **Lemma** with the author's own
explanation, typeset in printed math (free variables are implicitly universally quantified). Every
**Proof** cites the lemmas it rests on — click a citation to jump straight to that result (on its
own section page), read it, and follow *its* proof deeper; symbols inside the formulas link to
their definitions; and a *source ↗* link opens the exact Lean line.

"""

PAGE_FM = """---
layout: ../../layouts/Deep.astro
title: {title}
eyebrow: {group} · section of the QIQT-H book
description: {title} — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

"""


def main():
    decls = json.loads(CLOSURE.read_text(encoding="utf-8"))
    notation, roles = {}, {}
    for tid in ("gr", "born", "lorentz"):
        cfg = probe.load_config(REPO / "tracks" / f"{tid}.toml")
        notation.update((cfg.get("latex", {}) or {}).get("notation", {}))
        roles.update({t["name"]: t.get("role") for t in cfg["theorems"]})

    book = browser.render_browser(decls, notation=notation, roles=roles)
    pages_dir = REPO / "website" / "src" / "pages" / "browser"
    # clear stale section pages, then (re)write
    if pages_dir.exists():
        for f in pages_dir.glob("*.md"):
            f.unlink()
    pages_dir.mkdir(parents=True, exist_ok=True)

    index = REPO / "website" / "src" / "pages" / "browser.md"
    index.write_text(INDEX_FM + book["index"], encoding="utf-8")
    for p in book["pages"]:
        fm = PAGE_FM.format(title=p["title"], group=p["group"])
        (pages_dir / f"{p['slug']}.md").write_text(fm + p["body"], encoding="utf-8")
    print(f"wrote {index.relative_to(REPO)} + {len(book['pages'])} section pages "
          f"({len(decls)} declarations)")


if __name__ == "__main__":
    main()
