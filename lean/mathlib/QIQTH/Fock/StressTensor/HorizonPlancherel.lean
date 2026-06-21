import QIQTH.Fock.StressTensor.NullStressFlux

/-!
# Free-field stress tensor (Route B) — Phase 3: dilation-invariance of the horizon flux

`STRESS_TENSOR_FORMALIZATION_PLAN.md`, Phase 3.  The goal of Phase 3 is the Mellin/Plancherel identity
`stressFluxKK m f = π · rapidityMomentum (Krep m f) (Krep m f)'` (the horizon dilation charge equals the
rapidity-translation/boost charge), which discharges `hTkk`.

This file establishes the **unconditional half** of that goal — the **dilation-invariance** of the (full-line)
horizon stress flux:
`stressFluxKK m (boostTest a f) = stressFluxKK m f`.
Physically: the boost charge `K = ∫_H λ T_kk dλ` is **boost-invariant** — exactly the Noether/KMS
consistency the wedge-modular structure demands (the modular Hamiltonian commutes with the boost).  It is the
integrated form of the Phase-1/2 covariances (`Tkk_boostTest`: weight 2) combined with the Jacobian of the
horizon dilation `λ ↦ e^a λ` (the affine weight `λ` and the measure `dλ` together carry weight `−2`, exactly
cancelling).  Proof: `Tkk_boostTest` + the full-line scaling change of variables `integral_comp_mul_left`.
Axiom-free.

## Toward the final identity (corrected route, post GPT-5.5 consult)

`stressFluxKK = −2π · rapidityMomentum` (with the **full-line** `∫_ℝ` flux, now the definition) IS tractable
with current Mathlib — NO tempered distributions, NO Plancherel isometry.  The single-integral form
`λ |∂_λ φ_H|² = conj(χ_H)·ψ_H` (with `χ_H = ∂_λ φ_H`, `ψ_H = λ ∂_λ φ_H`, no `δ'`) plus the IBP `λ χ_H = ψ_H`
expresses both as Fourier transforms on the `k`-line; Mathlib's weak sesquilinear Fourier identity
(`integral_sesq_fourierIntegral_eq_neg_flip`, integrability-only) then pairs them, and the `θ ↔ k` change of
variables lands `−2π·Im∫ conj(K)·K'`.  (The earlier `δ'`-distribution alarm was an ARTIFACT of the WRONG
half-line definition `∫_{λ>0}`; the `1_{λ>0}` multiplier is what created the singular kernel.  See
`STRESS_TENSOR_FORMALIZATION_PLAN.md` Status Update 2.)  That is Phase 3b-i/3b-ii; this file is Phase 3a′.
-/

namespace QIQTH.Fock.StressTensor

open MeasureTheory Set
open QIQTH.Fock.Localization QIQTH.Fock.OneParticle

/-- **★ Dilation-invariance of the horizon stress flux (Phase 3a′, unconditional half).**
    `stressFluxKK m (boostTest a f) = stressFluxKK m f`: the full-line affine-weighted null flux
    `∫_ℝ λ T_kk dλ` — the (two-sided) modular/boost charge — is invariant under the Lorentz boost.  This is the
    Noether/KMS consistency that the boost commutes with the modular Hamiltonian, here proved as the exact
    cancellation of the weight-2 scaling of `T_kk` (`Tkk_boostTest`) against the weight-(−2) Jacobian of the
    horizon dilation `λ ↦ e^a λ`. -/
theorem stressFluxKK_boostTest (m a : ℝ) (f : V → ℂ) :
    stressFluxKK m (boostTest a f) = stressFluxKK m f := by
  unfold stressFluxKK
  have key : (∫ lam, lam * Tkk m (boostTest a f) lam)
      = ∫ lam, Real.exp a * ((Real.exp a * lam) * Tkk m f (Real.exp a * lam)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun lam => ?_))
    show lam * Tkk m (boostTest a f) lam
      = Real.exp a * ((Real.exp a * lam) * Tkk m f (Real.exp a * lam))
    rw [Tkk_boostTest]; ring
  rw [key, integral_const_mul,
    Measure.integral_comp_mul_left (fun x => x * Tkk m f x) (Real.exp a),
    abs_of_pos (inv_pos.mpr (Real.exp_pos a)),
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Real.exp_pos a).ne', one_mul]

end QIQTH.Fock.StressTensor
