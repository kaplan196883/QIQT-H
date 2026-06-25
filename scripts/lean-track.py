#!/usr/bin/env python3
"""Thin launcher so the tool runs from the repo root without PYTHONPATH:

    python scripts/lean-track.py report  -c tracks/gr.toml
    python scripts/lean-track.py extract -c tracks/born.toml
    python scripts/lean-track.py latex   -c tracks/gr.toml   # readable LaTeX from Lean
    python scripts/lean-track.py diff --old A/agent_summary.json --new B/agent_summary.json
"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lean_track.__main__ import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main())
