#!/usr/bin/env python3
"""State report for Target 3 — QIQT-H gives the GR field equations.
Lean-facts only; run:  python scripts/report_gr.py"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import report_lib

NAMES = [
    # --- the QIQT->GR capstones ---
    "QIQTH.WedgeKMSToGR.qiqt_gr_freefield",                # capstone (free KG field)
    "QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg",
    "QIQTH.WedgeKMSToGR.qiqt_gr_from_flux_complete",
    "QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr",             # the abstract Jacobson core
    # --- the free-field modular / Bisognano-Wichmann chain feeding the flux ---
    "QIQTH.Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional",
    "QIQTH.Fock.freeField_oneParticle_hFlux",
    "QIQTH.Fock.freeField_component_hFlux",
]

if __name__ == "__main__":
    sys.exit(report_lib.main("GR", "Target 3 — QIQT-H gives the GR field equations "
                             "(Jacobson route, free KG field)", NAMES))
