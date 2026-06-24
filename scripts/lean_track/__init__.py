"""lean_track — a generic, config-driven Lean state-report tool (driven by an AI skill).

Layers (with a visible honesty boundary):
  probe.py   — EXTRACTOR + PROBER: Lean facts only ([L]) and Lean-checked probes ([P]).
  report.py  — DETERMINISTIC analysis + version-controlled CURATION ([D]/[C]) + render + diff.
  __main__.py — CLI (extract / report / diff).

Every fact carries provenance:  [L] Lean fact · [P] Lean-checked prober · [C:rule] curation · [AI] AI judgment.
"""
__version__ = "0.1.0"
