/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# F1: field-level Bisognano–Wichmann, unconditional

The wedge modular automorphism acts on Weyl operators as the geometric boost, with NO carried
BW hypothesis, discharged from the one-particle result.

`secondQuantModFlowH_acts_as_boost` (in `OneParticleBW.lean`) proves the field-level BW geometric
action `σ_t(W(u) x) = W(boost·u)(σ_t x)` but CARRIES the one-particle BW identification
`modUnitary S = boostUnitary(·)` as a labelled hypothesis `hbw`, and is written in the `−2π`
convention.  The REAL modular flow of the free-field nice-wedge standard subspace satisfies the
satisfiable `+2π` convention and its BW identification is already axiom-free
(`oneParticleBW_niceWedge_unconditional`).  This file assembles the `+2π` field-level BW with the
hypothesis discharged internally — a sign-clean copy of the geometric-action step feeding its `hbw`
from the unconditional one-particle theorem (mirroring the `+2π` sign-copy in `FreeFieldHFlux.lean`).

Honest scope: this is the free-field (linear, Gaussian) wedge BW for a single mass; it is NOT the
interacting theory, and makes NO low-energy Lorentz-violation prediction (unconditional BW = standard
induced gravity).

Axiom-free.
-/
import QIQTH.Fock.CyclicWitness

namespace QIQTH.Fock

open QIQTH.Fock.OneParticle QIQTH.Fock.OneParticleBW QIQTH.Fock.BoostKMS QIQTH.Fock.CyclicWitness
  QIQTH.StandardSubspaceModular
open MeasureTheory

/-- **★★ The field-level Bisognano–Wichmann — FULLY UNCONDITIONAL, axiom-free.**  For every mass
    `m > 0`, the second-quantized modular automorphism `σ_t = Γ(Δ^{it})` of the free-field right-wedge
    algebra acts on the Weyl operators by the **geometric Lorentz boost** (`+2π` convention):
    `σ_t(W(u) x) = W(boostUnitary(2πt) u)(σ_t x)`, with NO carried Bisognano–Wichmann hypothesis.
    The one-particle BW identification `modUnitary S = boostUnitary(+2π·)` is discharged internally and
    axiom-free by `oneParticleBW_niceWedge_unconditional`; the field-level transport is the project's
    Tomita covariance `secondQuantModFlowH_weylH` (σ_t(W(u)) = W(Δ^{it}u)).  This is the genuine content
    of Bisognano–Wichmann at the field/Fock level — modular flow = boost — for the free field, machine
    checked end-to-end.  (`#print axioms` = the standard three only.) -/
theorem freeField_secondQuant_BW_unconditional {m : ℝ} (hm : 0 < m)
    (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ))
    (x : Fock (Lp ℂ 2 (volume : Measure ℝ))) :
    secondQuantModFlowH (niceWedgeStandardSubspace m
        (niceWedge_isSeparating_of_no_complex_line m (niceWedgeSeparating_pos_mass hm))
        (niceWedge_isCyclic_of_total_integral m (niceWedgeCyclic_pos_mass hm))) t (weylH u x)
      = weylH (boostUnitary (2 * Real.pi * t) u)
          (secondQuantModFlowH (niceWedgeStandardSubspace m
            (niceWedge_isSeparating_of_no_complex_line m (niceWedgeSeparating_pos_mass hm))
            (niceWedge_isCyclic_of_total_integral m (niceWedgeCyclic_pos_mass hm))) t x) := by
  rw [QIQTH.Fock.secondQuantModFlowH_weylH]
  have hBW := QIQTH.Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional hm
    (fun t => (boostUnitary (2 * Real.pi * t) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] _))
    (fun _ _ => rfl) t
  rw [hBW]; rfl

end QIQTH.Fock
