#!/usr/bin/env python3
"""State report for Target 2 — QIQT-H compatible with Lorentz.
Lean-facts only; run:  python scripts/report_lorentz.py"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import report_lib

NAMES = [
    # --- positive spine: covariant selection + covariant typicality measure ---
    "QIQTH.LorentzSelection.evaluation_covariance",
    "QIQTH.LorentzSelectionStrong.group_evaluation_covariance",
    "QIQTH.LorentzSelectionStrong.upvm_covariant_probability",            # capstone
    "QIQTH.FreeFieldTypicality.freeFieldMeasure_boost_invariant",
    "QIQTH.BHTypicalityMeasure.bh_typicalityMeasure_exists",
    "QIQTH.Fock.fock_typicalityMeasure_exists",
    "QIQTH.ContinuumSelection.continuum_volume_selects",
    "QIQTH.Theorem7.Setup.no_signaling",
    "QIQTH.NoSignalingGeneral.bipartite_no_signaling",
    # --- the honest no-go: invariant measure exists, invariant SELECTOR cannot ---
    "QIQTH.CovariantGluing.no_covariant_selector",
    "QIQTH.CovariantGluing.bool_swap_no_selector",
]

if __name__ == "__main__":
    sys.exit(report_lib.main("LORENTZ", "Target 2 — QIQT-H compatible with Lorentz "
                             "(covariance spine + selector no-go)", NAMES))
