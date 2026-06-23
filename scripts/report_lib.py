#!/usr/bin/env python3
"""Shared library for the per-target QIQT-H state reports (Born / Lorentz / GR).

Lean-facts only: every fact in a report (axioms, hypotheses, conclusions) is extracted
live from the Lean library via `scripts/target_probe.lean.tmpl` run through `lake env lean`.
No narrative, no verdict, no categorization — Lean is the source of truth.
"""
import json
import os
import pathlib
import subprocess
import sys
from datetime import datetime, timezone

REPO = pathlib.Path(__file__).resolve().parents[1]          # .../qiqt
MATHLIB = REPO / "lean" / "mathlib"
TMPL = pathlib.Path(__file__).resolve().parent / "target_probe.lean.tmpl"
PROBE = MATHLIB / "QIQTH" / "_ReportProbeTmp.lean"          # temp, gitignored, cleaned each run
LAKE = os.path.expanduser("~/.elan/bin/lake")
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def _git_rev() -> str:
    try:
        return subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=REPO,
                              capture_output=True, encoding="utf-8", errors="replace"
                              ).stdout.strip() or "?"
    except Exception:
        return "?"


def probe(names):
    """Run the Lean probe over `names`; return the parsed list of per-theorem dicts."""
    targets = ", ".join("`" + n for n in names)
    PROBE.write_text(TMPL.read_text(encoding="utf-8").replace("@@TARGETS@@", targets),
                     encoding="utf-8")
    try:
        r = subprocess.run([LAKE, "env", "lean", str(PROBE.relative_to(MATHLIB))],
                           cwd=MATHLIB, capture_output=True, encoding="utf-8",
                           errors="replace", timeout=1800)
        for line in reversed(r.stdout.splitlines()):
            line = line.strip()
            if line.startswith("["):
                return json.loads(line)
        raise RuntimeError(
            "Lean probe produced no JSON.\n--- stdout ---\n" + r.stdout +
            "\n--- stderr ---\n" + r.stderr)
    finally:
        PROBE.unlink(missing_ok=True)


def axiom_status(obj):
    """(is_axiom_free, [project axioms]) for one theorem dict."""
    if not obj.get("present", False):
        return (False, ["<MISSING FROM LIBRARY>"])
    proj = [a for a in obj.get("axioms", []) if a not in STANDARD_AXIOMS]
    return (len(proj) == 0, proj)


def _fence(s: str) -> str:
    return "```\n" + s.rstrip() + "\n```"


def render(target: str, subtitle: str, data) -> str:
    rev, now = _git_rev(), datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    n = len(data)
    present = [d for d in data if d.get("present")]
    missing = [d for d in data if not d.get("present")]
    proj_axioms = sorted({a for d in present for a in axiom_status(d)[1]})
    all_free = len(proj_axioms) == 0 and not missing
    total_hyp = sum(len(d.get("propHyps", [])) for d in present)

    L = []
    L.append(f"# QIQT-H state report — {target}")
    L.append(f"*{subtitle}*")
    L.append(f"\n_Generated {now} · git `{rev}` · {n} theorems_\n")

    # --- Axiom status ---
    L.append("## Axiom status")
    L.append(f"- **Project-specific axioms: {len(proj_axioms)}** (target 0)"
             + ("" if not proj_axioms else f" — {', '.join(proj_axioms)}"))
    L.append(f"- All theorems axiom-free (only `propext`, `Classical.choice`, `Quot.sound`): "
             f"**{'YES' if all_free else 'NO'}**")
    if missing:
        L.append(f"- ⚠️ Missing from library: {', '.join('`'+d['name']+'`' for d in missing)}")
    L.append("")
    L.append("| theorem | axioms |")
    L.append("|---|---|")
    for d in data:
        free, proj = axiom_status(d)
        tag = "✓ standard-3 only" if free else ("**MISSING**" if not d.get("present")
                                                else "⚠ " + ", ".join(proj))
        L.append(f"| `{d['name']}` | {tag} |")
    L.append("")

    # --- Per-theorem dump (facts from Lean) ---
    L.append("## Theorems — facts from Lean")
    for d in data:
        L.append(f"\n### `{d['name']}`")
        if not d.get("present"):
            L.append("**MISSING FROM LIBRARY** (name not found — renamed or removed).")
            continue
        free, proj = axiom_status(d)
        L.append(f"- **axioms:** {'✓ standard-3 only' if free else '⚠ '+', '.join(proj)}")
        hyps = d.get("propHyps", [])
        datab = d.get("dataBinders", [])
        L.append(f"- **conclusion:**")
        L.append(_fence(d.get("concl", "")))
        L.append(f"- **hypotheses ({len(hyps)}):**")
        if hyps:
            L.append(_fence("\n".join(f"{i+1}. {h['name']} : {h['type']}"
                                      for i, h in enumerate(hyps))))
        else:
            L.append("  *(none)*")
        L.append(f"- **data binders ({len(datab)}):** "
                 + (", ".join(f"`{x}`" for x in datab) if datab else "*(none)*"))

    # --- Current state (factual) ---
    L.append("\n## Current state (factual)")
    L.append(f"- Theorems present: **{len(present)}/{n}**")
    L.append(f"- All axiom-free: **{'YES' if all_free else 'NO'}**")
    L.append(f"- Total Prop-hypotheses across the spine: **{total_hyp}**")
    L.append("- Per-theorem hypothesis counts: "
             + ", ".join(f"`{d['name'].split('.')[-1]}`={len(d.get('propHyps', []))}"
                         for d in present))
    return "\n".join(L) + "\n"


def main(target: str, subtitle: str, names):
    data = probe(names)
    md = render(target, subtitle, data)
    out = REPO / "reports" / f"{target}_state.md"
    out.parent.mkdir(exist_ok=True)
    out.write_text(md, encoding="utf-8")

    present = [d for d in data if d.get("present")]
    proj = sorted({a for d in present for a in axiom_status(d)[1]})
    all_free = len(proj) == 0 and len(present) == len(data)
    total_hyp = sum(len(d.get("propHyps", [])) for d in present)
    print(f"{target}: {len(present)}/{len(data)} theorems present · "
          f"all axiom-free={'Y' if all_free else 'N'} · project-axioms {len(proj)} · "
          f"{total_hyp} total hypotheses  →  {out.relative_to(REPO)}")
    return 0 if all_free else 1


if __name__ == "__main__":
    print("This is a library. Run scripts/report_born.py / report_lorentz.py / report_gr.py.",
          file=sys.stderr)
    sys.exit(2)
