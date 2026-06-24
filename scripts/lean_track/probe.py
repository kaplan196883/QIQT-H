"""Config loading + the two Lean probes (extractor, prober). Emits raw Lean facts only."""
import json
import os
import pathlib
import subprocess
import sys

try:
    import tomllib  # py3.11+
except ModuleNotFoundError:  # pragma: no cover
    import tomli as tomllib  # type: ignore

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[1]                         # .../qiqt
MATHLIB = REPO / "lean" / "mathlib"
LAKE = os.path.expanduser("~/.elan/bin/lake")
EXTRACT_TMPL = HERE / "probe_extract.lean.tmpl"
DISCHARGE_TMPL = HERE / "probe_discharge.lean.tmpl"
STANDARD_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def load_config(path):
    cfg = tomllib.loads(pathlib.Path(path).read_text(encoding="utf-8"))
    cfg.setdefault("project", {})
    cfg["project"].setdefault("lean_import", "QIQTH")
    cfg["project"].setdefault("allowed_axioms", STANDARD_AXIOMS)
    cfg["project"].setdefault("timeout_sec", 1800)
    cfg.setdefault("theorems", [])
    cfg.setdefault("category_rules", [])
    if not cfg["theorems"]:
        raise ValueError(f"{path}: config has no [[theorems]]")
    return cfg


def git_rev():
    try:
        return subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=REPO,
                              capture_output=True, encoding="utf-8", errors="replace"
                              ).stdout.strip() or "?"
    except Exception:
        return "?"


def _run_probe(tmpl_path, names, lean_import, timeout, tag):
    """Fill a probe template, run `lake env lean` (cwd=MATHLIB), return the JSON it writes."""
    targets = ", ".join("`" + n for n in names)
    probe = MATHLIB / "QIQTH" / f"_lt_probe_{tag}.lean"   # temp .lean (gitignored)
    out_name = f"_lt_out_{tag}.json"                      # written by the probe into cwd (MATHLIB)
    out = MATHLIB / out_name
    src = (tmpl_path.read_text(encoding="utf-8")
           .replace("@@IMPORT@@", lean_import)
           .replace("@@TARGETS@@", targets)
           .replace("@@OUTPUT@@", out_name))
    probe.write_text(src, encoding="utf-8")
    try:
        r = subprocess.run([LAKE, "env", "lean", str(probe.relative_to(MATHLIB))],
                           cwd=MATHLIB, capture_output=True, encoding="utf-8",
                           errors="replace", timeout=timeout)
        if not out.exists():
            raise RuntimeError(f"{tag} probe wrote no output.\n--- stderr ---\n{r.stderr[-4000:]}"
                               f"\n--- stdout ---\n{r.stdout[-2000:]}")
        return json.loads(out.read_text(encoding="utf-8"))
    finally:
        probe.unlink(missing_ok=True)
        out.unlink(missing_ok=True)


def extract(names, cfg):
    return _run_probe(EXTRACT_TMPL, names, cfg["project"]["lean_import"],
                      cfg["project"]["timeout_sec"], "ex")


def discharge(names, cfg):
    return _run_probe(DISCHARGE_TMPL, names, cfg["project"]["lean_import"],
                      cfg["project"]["timeout_sec"], "pr")
