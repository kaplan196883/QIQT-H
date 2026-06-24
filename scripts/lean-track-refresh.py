#!/usr/bin/env python3
"""Regenerate every tracks/*.toml report and diff against the previous run.

Loop- and hook-ready. With --skip-unchanged it is a cheap no-op unless the Lean library
(lean/mathlib/QIQTH) actually changed since the last refresh — so a /loop firing this on an
interval, or a git post-commit hook, only pays the `lake` cost when there's something to report.

    python scripts/lean-track-refresh.py [--skip-unchanged] [--quiet]

Exit code: 0 if nothing changed (or skipped); 1 if any track's axioms or assumption surface changed.
"""
import json
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from lean_track import probe, report  # noqa: E402

TRACKS_DIR = probe.REPO / "tracks"
STAMP = probe.REPO / "reports" / ".last_qiqth_tree"   # the QIQTH tree-hash of the last refresh


def _qiqth_tree_hash():
    """Object id of lean/mathlib/QIQTH at HEAD — changes iff a committed QIQTH file changed."""
    r = subprocess.run(["git", "rev-parse", "HEAD:lean/mathlib/QIQTH"], cwd=probe.REPO,
                       capture_output=True, encoding="utf-8", errors="replace")
    return r.stdout.strip()


def _qiqth_dirty():
    r = subprocess.run(["git", "status", "--porcelain", "lean/mathlib/QIQTH"], cwd=probe.REPO,
                       capture_output=True, encoding="utf-8", errors="replace")
    return bool(r.stdout.strip())


def refresh_track(cfg_path):
    cfg = probe.load_config(cfg_path)
    outdir = probe.REPO / "reports" / cfg["track"]["id"]
    prev = outdir / "agent_summary.json"
    old = json.loads(prev.read_text(encoding="utf-8")) if prev.exists() else None

    names = [t["name"] for t in cfg["theorems"]]
    roles = {t["name"]: t.get("role") for t in cfg["theorems"]}
    ex = probe.extract(names, cfg)
    for t in ex:
        t["role"] = roles.get(t["name"])
    pr = probe.discharge(names, cfg)
    merged = report.apply_curation(report.analyze(ex, pr, cfg), cfg)

    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "facts.curated.json").write_text(json.dumps(merged, indent=2, ensure_ascii=False), encoding="utf-8")
    new = report.agent_summary(merged, cfg)
    (outdir / "agent_summary.json").write_text(json.dumps(new, indent=2, ensure_ascii=False), encoding="utf-8")
    (outdir / "report.machine.md").write_text(report.render_markdown(merged, cfg), encoding="utf-8")

    d = report.diff(old, new) if old else "(first run — nothing to diff against)"
    changed = old is not None and any(m in d for m in
                                      ("new assumption", "NEW project axioms",
                                       "discharged/removed", "retired project axioms"))
    return cfg["track"]["id"], d, changed


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    skip = "--skip-unchanged" in argv
    quiet = "--quiet" in argv

    if skip and not _qiqth_dirty() and STAMP.exists() and STAMP.read_text().strip() == _qiqth_tree_hash():
        if not quiet:
            print("lean-track-refresh: QIQTH unchanged since last refresh — skipping.")
        return 0

    tracks = sorted(TRACKS_DIR.glob("*.toml"))
    any_changed = False
    for cfg_path in tracks:
        tid, d, changed = refresh_track(cfg_path)
        any_changed = any_changed or changed
        if changed or not quiet:
            print(f"\n===== {tid} {'(CHANGED)' if changed else '(no change)'} =====")
            if changed:
                print(d)

    STAMP.parent.mkdir(exist_ok=True)
    STAMP.write_text(_qiqth_tree_hash() or "", encoding="utf-8")
    print(f"\nlean-track-refresh: {len(tracks)} tracks refreshed · "
          f"{'CHANGES detected' if any_changed else 'no surface/axiom changes'}.")
    return 1 if any_changed else 0


if __name__ == "__main__":
    sys.exit(main())
