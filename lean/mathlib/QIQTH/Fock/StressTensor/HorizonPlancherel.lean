import QIQTH.Fock.StressTensor.NullStressFlux

/-!
# Free-field stress tensor (Route B) — Phase 3: dilation-invariance of the horizon flux

`STRESS_TENSOR_FORMALIZATION_PLAN.md`, Phase 3.  The goal of Phase 3 is the Mellin/Plancherel identity
`stressFluxKK m f = π · rapidityMomentum (Krep m f) (Krep m f)'` (the horizon dilation charge equals the
rapidity-translation/boost charge), which discharges `hTkk`.

This file establishes the **unconditional half** of that goal — the **dilation-invariance** of the horizon
stress flux:
`stressFluxKK m (boostTest a f) = stressFluxKK m f`.
Physically: the boost charge `K = ∫_H λ T_kk dλ` is **boost-invariant** — exactly the Noether/KMS
consistency the wedge-modular structure demands (the modular Hamiltonian commutes with the boost).  It is the
integrated form of the Phase-1/2 covariances (`Tkk_boostTest`: weight 2) combined with the Jacobian of the
horizon dilation `λ ↦ e^a λ` (the affine weight `λ` and the measure `dλ` together carry weight `−2`, exactly
cancelling).  Proof: `Tkk_boostTest` + the half-line scaling change of variables
`integral_comp_mul_left_Ioi`.  Axiom-free.

## Remaining crux (honest status)

The final identity `stressFluxKK = π · rapidityMomentum` is NOT yet proved.  It is a genuine analytic obstacle:
`∫_{λ>0} λ |∂_λ φ_H(λ)|² dλ` expands (Parseval) to a double `θ`-integral against the oscillatory kernel
`∫_0^∞ λ e^{−iλ(k(θ)−k(θ'))} dλ`, which converges only as a **distribution** and contributes a `δ'(k(θ)−k(θ'))`
term — i.e. the derivative coupling `∫ conj(K)·K'` (the momentum) — that Mathlib's integration theory cannot
yet evaluate directly (no tempered-distribution / oscillatory-regularization toolkit).  Routes for the next
phase: (a) a regularized definition `stressFluxKK_ε` with a convergence factor `e^{−ελ}` and an `ε → 0` limit;
(b) restrict to the dense `gaussianLocalTest` class and integrate explicitly; or (c) build the minimal
`∫_0^∞ λ e^{−iλΔ−ελ} dλ = (ε+iΔ)^{−2}` lemma and push the distributional limit by hand.  The dilation-invariance
below holds for ALL admissible `f` and is the correct, fully-rigorous structural milestone in the meantime.
-/

namespace QIQTH.Fock.StressTensor

open MeasureTheory Set
open QIQTH.Fock.Localization QIQTH.Fock.OneParticle

/-- **★ Dilation-invariance of the horizon stress flux (Phase 3, unconditional half).**
    `stressFluxKK m (boostTest a f) = stressFluxKK m f`: the affine-weighted null flux `∫_H λ T_kk dλ` — the
    modular/boost charge — is invariant under the Lorentz boost.  This is the Noether/KMS consistency that the
    boost commutes with the modular Hamiltonian, here proved as the exact cancellation of the weight-2 scaling
    of `T_kk` (`Tkk_boostTest`) against the weight-(−2) Jacobian of the horizon dilation `λ ↦ e^a λ`. -/
theorem stressFluxKK_boostTest (m a : ℝ) (f : V → ℂ) :
    stressFluxKK m (boostTest a f) = stressFluxKK m f := by
  unfold stressFluxKK
  have key : (∫ lam in Ioi (0 : ℝ), lam * Tkk m (boostTest a f) lam)
      = ∫ lam in Ioi (0 : ℝ),
          Real.exp a * ((Real.exp a * lam) * Tkk m f (Real.exp a * lam)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun lam _ => ?_)
    rw [Tkk_boostTest]; ring
  rw [key, integral_const_mul,
    integral_comp_mul_left_Ioi (fun x => x * Tkk m f x) 0 (Real.exp_pos a), mul_zero,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Real.exp_pos a).ne', one_mul]

end QIQTH.Fock.StressTensor
