/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Free-field `hFlux` in the satisfiable `+2π` convention

`QIQT_GR_FREEFIELD_COMPLETION_PLAN.md`, Phase 1–2.  The `hFlux` machinery in `OneParticleBW.lean`
(`hasDerivAt_modularEnergy_of_boost`, `oneParticle_hFlux`) is written in the `boostUnitary(−2πt)` convention and
takes the BW identification `modUnitary S = boostUnitary(−2π·)` as a labelled input.  But the REAL modular flow of
the free-field nice-wedge standard subspace satisfies the `+2π` convention (`oneParticleBW_niceWedge_unconditional`,
axiom-free).  This file rebuilds the modular-energy = stress-flux step in the satisfiable `+2π` convention and
supplies the BW identification INTERNALLY from `oneParticleBW_niceWedge_unconditional` — so the only remaining input
is the boost-charge derivative (discharged separately from `boostEnergy_eq_neg_stressFlux`).

Axiom-free.
-/
import QIQTH.Fock.CyclicWitness

namespace QIQTH.Fock

open QIQTH.Fock.OneParticle QIQTH.Fock.OneParticleBW QIQTH.Fock.BoostKMS QIQTH.Fock.CyclicWitness
  QIQTH.StandardSubspaceModular
open MeasureTheory

/-- **Modular energy = boost energy, in the `+2π` convention** (sign-flipped copy of
    `hasDerivAt_modularEnergy_of_boost`).  Given the BW identification `modUnitary S = boostUnitary(+2π·)`, the
    modular-energy derivative of `ξ` equals its boost-energy derivative. -/
theorem hasDerivAt_modularEnergy_of_boost_pos
    (S : StandardSubspace (Lp ℂ 2 (volume : Measure ℝ)))
    (hbw : ∀ (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)),
        modUnitary S t u = boostUnitary (2 * Real.pi * t) u)
    (ξ : Lp ℂ 2 (volume : Measure ℝ)) (c : ℂ)
    (h : HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (2 * Real.pi * t) ξ)) c 0) :
    HasDerivAt (fun t : ℝ => inner ℂ ξ (modUnitary S t ξ)) c 0 := by
  have heq : (fun t : ℝ => inner ℂ ξ (modUnitary S t ξ))
      = (fun t : ℝ => inner ℂ ξ (boostUnitary (2 * Real.pi * t) ξ)) := by
    funext t; rw [hbw t ξ]
  rw [heq]; exact h

/-- **★ The free-field modular-energy = stress-flux derivative, BW supplied internally (Phase 2).**  For the
    nice-wedge standard subspace `S` and ANY mode `ξ`, given the boost-charge derivative `HasDerivAt (t ↦
    ⟨ξ, boostUnitary(2πt) ξ⟩) c 0`, the modular-energy derivative `HasDerivAt (t ↦ ⟨ξ, modUnitary S t ξ⟩) c 0`
    holds — with the Bisognano–Wichmann identification `modUnitary S = boostUnitary(+2π·)` supplied internally and
    axiom-free by `oneParticleBW_niceWedge_unconditional` (no labelled `hUniq`/`hStrip`, no sign mismatch). -/
theorem freeField_modularEnergy_eq_boostCharge {m : ℝ} (hm : 0 < m)
    (ξ : Lp ℂ 2 (volume : Measure ℝ)) (c : ℂ)
    (hBoostCharge : HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (2 * Real.pi * t) ξ)) c 0) :
    HasDerivAt (fun t : ℝ => inner ℂ ξ
        (modUnitary (niceWedgeStandardSubspace m
          (niceWedge_isSeparating_of_no_complex_line m (niceWedgeSeparating_pos_mass hm))
          (niceWedge_isCyclic_of_total_integral m (niceWedgeCyclic_pos_mass hm))) t ξ)) c 0 := by
  have hbw : ∀ (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)),
      modUnitary (niceWedgeStandardSubspace m
        (niceWedge_isSeparating_of_no_complex_line m (niceWedgeSeparating_pos_mass hm))
        (niceWedge_isCyclic_of_total_integral m (niceWedgeCyclic_pos_mass hm))) t u
        = boostUnitary (2 * Real.pi * t) u := by
    intro t u
    have hBW := QIQTH.Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional hm
      (fun t => (boostUnitary (2 * Real.pi * t) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] _))
      (fun _ _ => rfl) t
    rw [hBW]; rfl
  exact hasDerivAt_modularEnergy_of_boost_pos _ hbw ξ c hBoostCharge

end QIQTH.Fock
