#!/usr/bin/env python3
"""State report for Target 1 — QIQT-H compatible with Born.
Lean-facts only; run:  python scripts/report_born.py"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import report_lib

# Spine (positive results) + no-go audits. Order = report order.
NAMES = [
    # --- positive spine ---
    "QIQTH.BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality",   # capstone
    "QIQTH.EffectGleason.EffectMeasure.finite_effect_gleason",
    "QIQTH.GleasonSelector.positive_ray_certain_forces_born",
    "QIQTH.RefinementBorn.continuous_additive_fMeasure_eq_born",
    "QIQTH.RecordGleason.decoherent_partition_additive",
    "QIQTH.BornJoin.ActualEnsemble.finite_noCollapseBornRepresentation",
    "QIQTH.BornMeasureUniqueness.product_born_measure_unique",
    "QIQTH.BornTypicalityFinite.chebyshev_freq",
    "QIQTH.BornTypicality.qiqth_born_typicality_conditional",
    # --- no-go audits (what is NOT forced) ---
    "QIQTH.NoBornFromNothing.born_distribution_realizable_conditional",
    "QIQTH.NoConcentration.decoherence_does_not_concentrate",
    "QIQTH.EquivarianceGap.support_preservation_does_not_imply_measure_preservation",
    "QIQTH.OperationalNoGo.operational_data_insufficient",
]

if __name__ == "__main__":
    sys.exit(report_lib.main("BORN", "Target 1 — QIQT-H compatible with Born "
                             "(spine + no-go audits)", NAMES))
