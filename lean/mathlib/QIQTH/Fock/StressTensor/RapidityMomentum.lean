import QIQTH.Fock.OneParticleBW

/-!
# Free-field stress tensor (Route B) — Phase 0: the rapidity-momentum functional

This is the first brick of `STRESS_TENSOR_FORMALIZATION_PLAN.md` (Route B, the horizon null-cut), whose
end goal is to discharge the labelled scalar `hTkk : (2π/ℏ)·T_kk = (2π·Im∫ conj(K)·K')` by *defining* the
horizon null stress flux and *proving* it equals the boost/rapidity energy.

Phase 0 simply NAMES the right-hand side of `hTkk` as a functional and restates the (already machine-checked)
boost-charge derivative in terms of it:
* `rapidityMomentum f f' = Im ∫ conj(f θ)·f'(θ) dθ` — the boost energy `⟪f, (−i d/dθ) f⟫` of the smooth
  one-particle wedge mode `f` (rapidity wavefunction).
* `hasDerivAt_inner_boost_rapidityMomentum` — the boost correlation derivative is `i·2π·rapidityMomentum`,
  i.e. the boost energy IS `2π` times the rapidity momentum.  (Restates
  `QIQTH.Fock.OneParticleBW.hasDerivAt_inner_boostUnitary_imaginary`.)

Everything is axiom-free.  The genuine analytic content (the horizon field, the null stress component, the
Mellin/Plancherel identity that turns `rapidityMomentum` into a *defined* stress flux) is Phases 1–3.
-/

namespace QIQTH.Fock.StressTensor

open MeasureTheory
open QIQTH.Fock.OneParticleBW QIQTH.Fock.OneParticle

/-- The **rapidity-momentum expectation** of a smooth one-particle wedge mode `f` (a rapidity
    wavefunction with pointwise derivative `f'`):
    `rapidityMomentum f f' = Im ∫ conj(f θ)·f'(θ) dθ = ⟪f, (−i d/dθ) f⟫`.
    This is the *boost energy* of the mode — exactly the real scalar the labelled `hTkk` identifies with
    `(2π/ℏ)·T_kk`.  Route B (Phases 1–3) re-expresses this as the genuine null stress-energy flux of the
    field across the horizon. -/
noncomputable def rapidityMomentum (f f' : ℝ → ℂ) : ℝ :=
  (∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ)).im

/-- **The boost-charge derivative, with its right-hand side named.**  For any smooth wedge mode `ξ = f.toLp`,
    `d/dt ⟪ξ, boostUnitary(−2π t) ξ⟫|₀ = i·2π·rapidityMomentum f f'` — the boost energy is `2π` times the
    rapidity momentum.  This is exactly the labelled `hBoostCharge` slot with `(2π/ℏ)·T_kk` replaced by the
    *named* boost energy `2π·rapidityMomentum`; the remaining physics (`hTkk`) is precisely the identification
    of `rapidityMomentum` with the horizon stress flux, which Route B Phases 1–3 supply.
    Restates `hasDerivAt_inner_boostUnitary_imaginary`. -/
theorem hasDerivAt_inner_boost_rapidityMomentum
    (f f' : ℝ → ℂ) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hf_int : Integrable f (volume : Measure ℝ))
    (hF0_int : Integrable (fun θ => (starRingEnd ℂ) (f θ) * f θ) (volume : Measure ℝ))
    (hf_meas : AEStronglyMeasurable f (volume : Measure ℝ))
    (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hf'_meas : AEStronglyMeasurable f' (volume : Measure ℝ))
    (B : ℝ) (hB : ∀ x, ‖f' x‖ ≤ B) :
    HasDerivAt
      (fun t : ℝ => inner ℂ (hf2.toLp f) (boostUnitary (-(2 * Real.pi * t)) (hf2.toLp f)))
      (Complex.I * ((2 * Real.pi * rapidityMomentum f f' : ℝ) : ℂ)) 0 := by
  have h := hasDerivAt_inner_boostUnitary_imaginary f f' hf2 hf_int hF0_int hf_meas hfd hf'_meas B hB
  have heq : (2 * Real.pi * rapidityMomentum f f' : ℝ)
      = (2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ)).im := by
    simp only [rapidityMomentum, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [heq]; exact h

end QIQTH.Fock.StressTensor
