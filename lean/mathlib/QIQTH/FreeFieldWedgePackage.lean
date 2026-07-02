/-
  E1 (MICROTHEORY_EARNS_GRAVITY_PLAN.md) — BW discharged into the bridge: the free-field wedge package.
  The carried BW identification of C1 (`WedgeBoostPackage.hBW`) is DISCHARGED for the free field by the
  unconditional one-particle Bisognano–Wichmann theorem (`oneParticleBW_niceWedge_unconditional`): the geometric
  boost IS the modular flow, as an operator identity. Corollary: the wedge Clausius datum `δ⟨K_boost⟩ = −δS` is
  FORCED with NO external BW premise — only the domain/spectral regularity conditions remain (per the verifier).
  ⚠ Free field (positive mass), nice wedge; the Clausius/area law and `G` stay the separate carried inputs.
-/
import Mathlib
import QIQTH.WedgeBoostClausius
import QIQTH.Fock.CyclicWitness

namespace QIQTH.EarnGravity

open QIQTH.StandardSubspaceModular QIQTH.SpectralTheorem QIQTH.Spectral QIQTH.WedgeBoost
open QIQTH.Fock.OneParticle QIQTH.Fock.BoostKMS QIQTH.Fock.CyclicWitness MeasureTheory

variable {m : ℝ}

/-- The free-field nice-wedge standard subspace (positive mass), with both Reeh–Schlieder inputs discharged. -/
noncomputable def wedgeS (hm : 0 < m) : StandardSubspace (Lp ℂ 2 (volume : Measure ℝ)) :=
  niceWedgeStandardSubspace m
    (niceWedge_isSeparating_of_no_complex_line m (niceWedgeSeparating_pos_mass hm))
    (niceWedge_isCyclic_of_total_integral m (niceWedgeCyclic_pos_mass hm))

/-- **E1 — the free-field wedge package: BW DISCHARGED.** The geometric boost flow `V_t = boostUnitary(2πt)`
    satisfies `WedgeBoostPackage.hBW` as a THEOREM (`oneParticleBW_niceWedge_unconditional`), not a carried
    hypothesis — for every state `ξ`. -/
noncomputable def freeFieldWedgePackage (hm : 0 < m) (ξ : Lp ℂ 2 (volume : Measure ℝ)) :
    WedgeBoostPackage (wedgeS hm) ξ where
  boost := fun t x => boostUnitary (2 * Real.pi * t) x
  hBW := fun t => by
    have h := oneParticleBW_niceWedge_unconditional hm
      (fun s => (boostUnitary (2 * Real.pi * s)).toLinearIsometry.toContinuousLinearMap)
      (fun s x => rfl) t
    exact (congrArg (fun U => U ξ) h).symm

/-- **E1 corollary — the wedge Clausius datum with NO BW premise.** For the free field, any candidate heat-flux
    value `c` with `d/dt⟪ξ,V_tξ⟫|₀ = i·c` MUST equal `−S` (the modular entanglement entropy) — the
    Bisognano–Wichmann input is a theorem here, not a hypothesis; only the domain/spectral conditions remain. -/
theorem freeField_clausius_unconditional (hm : 0 < m) (ξ : Lp ℂ 2 (volume : Measure ℝ)) (c : ℝ)
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC (wedgeS hm)) (rvdRC_isSelfAdjoint (wedgeS hm))).fcDomain
      (fun ω : spectrum ℝ (rvdRC (wedgeS hm)) => kFn ω.val))
    (hspec : ∀ ω : spectrum ℝ (rvdRC (wedgeS hm)), (ω : spectrum ℝ (rvdRC (wedgeS hm))).val ∈ Set.Ioo (0 : ℝ) 2)
    (hc : HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (2 * Real.pi * t) ξ)) (Complex.I * (c : ℂ)) 0) :
    c = -cgpEntropy (wedgeS hm) ξ :=
  boost_flux_unique (freeFieldWedgePackage hm ξ) c hdom hspec hc

end QIQTH.EarnGravity
