/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.TraceClass.CompactSpectral

/-!
# From a compact self-adjoint injective resolvent to the discrete spectrum and heat trace

Model the Laplacian resolvent `R = (Δ + 1)⁻¹`. If `R` is a **compact, self-adjoint, injective**
operator on a complex Hilbert space, then `R` has an orthonormal `HilbertBasis` of eigenvectors with
**nonzero** real eigenvalues `ρᵢ` (compact self-adjoint spectral theorem of `CompactSpectral` plus
injectivity), and hence `Δ` has the discrete spectrum `λᵢ = ρᵢ⁻¹ − 1` on the same basis
(`R (bᵢ) = (λᵢ + 1)⁻¹ • bᵢ`). Given **Weyl summability** of the heat spectrum `e^{−t λᵢ}`, the heat
operator `e^{−tΔ}` exists, is **trace-class**, and satisfies the **McKean–Singer heat trace**
`Tr e^{−tΔ} = Σᵢ e^{−t λᵢ}`.

This packages the reduction: the discrete spectrum and heat trace are **derived** from the single
hypothesis "R compact" (with reality/self-adjointness and injectivity), not assumed independently.

## Main results

* `compactResolvent_hasEigenbasis` : a compact self-adjoint injective `R` has an orthonormal eigen-
  `HilbertBasis` `b` with real, **nonzero** eigenvalues `ρ`, `R (b i) = ρ i • b i`, `ρ i ≠ 0`.
* `compactResolvent_heatTrace` : the induced `Δ`-spectrum `λ i = ρ i⁻¹ − 1` (so
  `R (b i) = (λ i + 1)⁻¹ • b i`), together with the McKean–Singer identity for *any* operator
  diagonalized by `b` with heat eigenvalues `e^{−t λ i}`.
* `heatOperator_of_summable` : given a Hilbert basis, a `Δ`-spectrum `lam`, and Weyl summability of
  `e^{−t·lam}`, the diagonal heat operator exists, is trace-class, and has trace `Σ e^{−t·lam}`.

## Honest firewall

This is **pure functional analysis**. It does **not** prove that `R` is compact (that is
Rellich–Kondrachov / elliptic regularity — the manifold wall) nor Weyl summability of the heat
spectrum; both are taken as **hypotheses**. It does not build the manifold heat kernel and does not
discharge the general `a₁ = R/6`. NOT the conjecture, NOT QG. No axioms, no `sorry`.
-/

open scoped ENNReal NNReal ComplexInnerProductSpace lp

namespace QIQTH.TraceClass

universe u

variable {ι : Type*} {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The discrete spectrum of the operator from a compact injective resolvent -/

/-- **Compact self-adjoint injective ⟹ eigenbasis with nonzero eigenvalues.** A compact self-adjoint
operator `R` that is *injective* has an orthonormal `HilbertBasis` of eigenvectors with real,
**nonzero** eigenvalues `ρ`. The eigenbasis is `compactSelfAdjoint_hasEigenbasis`; nonvanishing of
the eigenvalues is forced by injectivity: a zero eigenvalue would send a unit basis vector to `0`,
contradicting injectivity together with `‖b i‖ = 1`. -/
theorem compactResolvent_hasEigenbasis {R : H →L[ℂ] H}
    (hcomp : IsCompactOperator R) (hsa : IsSelfAdjoint R) (hinj : Function.Injective R) :
    ∃ (κ : Type u) (b : HilbertBasis κ ℂ H) (ρ : κ → ℝ),
      (∀ i, R (b i) = ((ρ i : ℝ) : ℂ) • b i) ∧ (∀ i, ρ i ≠ 0) := by
  obtain ⟨κ, b, ρ, hR⟩ := compactSelfAdjoint_hasEigenbasis hcomp hsa
  refine ⟨κ, b, ρ, hR, fun i hρ => ?_⟩
  -- A zero eigenvalue would kill the unit basis vector `b i`.
  have hbi : R (b i) = R 0 := by rw [hR i, hρ]; simp
  have hb0 : b i = 0 := hinj hbi
  have hone : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  rw [hb0, norm_zero] at hone
  exact one_ne_zero hone.symm

/-- **Discrete spectrum + McKean–Singer identity from a compact injective resolvent.** With
`R = (Δ + 1)⁻¹`, the eigenvalues `ρ i ≠ 0` of `R` give the `Δ`-spectrum `λ i = ρ i⁻¹ − 1`, so
`R (b i) = (λ i + 1)⁻¹ • b i`. For any heat time `t`, *any* operator `Hop` diagonalized by the same
basis with heat eigenvalues `e^{−t λ i}` has trace `Σᵢ e^{−t λ i}` (the McKean–Singer heat trace, a
direct instance of `traceE_eq_tsum_eigenvalues`). This exposes the spectrum without constructing the
heat operator. -/
theorem compactResolvent_heatTrace {R : H →L[ℂ] H}
    (hcomp : IsCompactOperator R) (hsa : IsSelfAdjoint R) (hinj : Function.Injective R) (t : ℝ) :
    ∃ (κ : Type u) (b : HilbertBasis κ ℂ H) (lam : κ → ℝ),
      (∀ i, R (b i) = (((lam i + 1)⁻¹ : ℝ) : ℂ) • b i) ∧
      (∀ (Hop : H →L[ℂ] H),
        (∀ i, Hop (b i) = ((Real.exp (-(t * lam i)) : ℝ) : ℂ) • b i) →
          traceE b Hop = ∑' i, ((Real.exp (-(t * lam i)) : ℝ) : ℂ)) := by
  obtain ⟨κ, b, ρ, hR, hρ⟩ := compactResolvent_hasEigenbasis hcomp hsa hinj
  refine ⟨κ, b, fun i => (ρ i)⁻¹ - 1, fun i => ?_,
    fun Hop hHop => traceE_eq_tsum_eigenvalues b hHop⟩
  -- `R (b i) = ρ i • b i` and `((ρ i)⁻¹ - 1) + 1)⁻¹ = ρ i`.
  have h1 : ((ρ i)⁻¹ - 1 + 1)⁻¹ = ρ i := by
    have he : (ρ i)⁻¹ - 1 + 1 = (ρ i)⁻¹ := by ring
    rw [he, inv_inv]
  rw [h1]
  exact hR i

/-! ### The diagonal heat operator on `ℓ²`, transported to `H`

We replicate the diagonal `ℓ²`-multiplier construction of `Spectral.lean` (there `private`) to build
the heat operator `e^{−tΔ}` directly, then invoke `isTraceClass_of_summable_eigenvalues` and
`traceE_eq_tsum_eigenvalues`. -/

/-- Diagonal multiplication `f ↦ (i ↦ σ i · f i)` by a norm-bounded scalar family `σ`, as a linear
map on `ℓ²(ι, ℂ)` (it lands in `ℓ²` since `‖σ i · f i‖ ≤ C ‖f i‖`). -/
private noncomputable def resDiagMulₗ (σ : ι → ℂ) {C : ℝ} (hC : ∀ i, ‖σ i‖ ≤ C) :
    ℓ²(ι, ℂ) →ₗ[ℂ] ℓ²(ι, ℂ) where
  toFun f := ⟨fun i => σ i * f i, by
    refine Memℓp.mono (g := fun i => C * ‖(f : ∀ _ : ι, ℂ) i‖)
      (((lp.memℓp f).norm).const_mul C) (fun i => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)⟩
  map_add' f g := by
    refine lp.ext (funext fun i => ?_)
    simp only [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine lp.ext (funext fun i => ?_)
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
private theorem resDiagMulₗ_apply (σ : ι → ℂ) {C : ℝ} (hC : ∀ i, ‖σ i‖ ≤ C) (f : ℓ²(ι, ℂ)) (i : ι) :
    (resDiagMulₗ σ hC f) i = σ i * f i := rfl

/-- The diagonal multiplier as a *bounded* operator on `ℓ²`, with operator norm `≤ C`. -/
private noncomputable def resDiagMul (σ : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖σ i‖ ≤ C) :
    ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  (resDiagMulₗ σ hC).mkContinuous C (fun f => by
    refine (lp.norm_mono (y := (C : ℂ) • f) (by norm_num) (fun i => ?_)).trans (le_of_eq ?_)
    · rw [resDiagMulₗ_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)
    · rw [lp.norm_const_smul (by norm_num), Complex.norm_real, Real.norm_of_nonneg hC0])

private theorem resDiagMul_apply (σ : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖σ i‖ ≤ C)
    (f : ℓ²(ι, ℂ)) (i : ι) : (resDiagMul σ hC0 hC f) i = σ i * f i := rfl

/-- **The trace-class heat operator under Weyl summability.** Given a Hilbert basis `b`, a
`Δ`-spectrum `lam`, a heat time `t`, and **Weyl summability** of the heat spectrum
`i ↦ e^{−t · lam i}`, the diagonal heat operator `e^{−tΔ}` exists (acting as
`Hop (b i) = e^{−t · lam i} • b i`), is **trace-class**, and satisfies the McKean–Singer heat trace
`Tr Hop = Σᵢ e^{−t · lam i}`. The heat eigenvalues are automatically nonnegative
(`Real.exp_nonneg`); trace-class is `isTraceClass_of_summable_eigenvalues` and the trace is
`traceE_eq_tsum_eigenvalues`. -/
theorem heatOperator_of_summable (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) (t : ℝ)
    (hsum : Summable (fun i => Real.exp (-(t * lam i)))) :
    ∃ (Hop : H →L[ℂ] H),
      (∀ i, Hop (b i) = ((Real.exp (-(t * lam i)) : ℝ) : ℂ) • b i) ∧
        IsTraceClass Hop ∧
        traceE b Hop = ∑' i, ((Real.exp (-(t * lam i)) : ℝ) : ℂ) := by
  classical
  set μ : ι → ℝ := fun i => Real.exp (-(t * lam i)) with hμdef
  have hμnn : ∀ i, 0 ≤ μ i := fun i => Real.exp_nonneg _
  set C : ℝ := ∑' i, μ i with hCdef
  have hC0 : 0 ≤ C := tsum_nonneg hμnn
  have hnc : ∀ r : ℝ, 0 ≤ r → ‖(r : ℂ)‖ = r := fun r hr => by
    rw [Complex.norm_real, Real.norm_of_nonneg hr]
  have hCbound : ∀ i, ‖((μ i : ℝ) : ℂ)‖ ≤ C := by
    intro i
    rw [hnc _ (hμnn i)]
    exact hsum.le_tsum i (fun j _ => hμnn j)
  -- The diagonal heat multiplier on `ℓ²`, transported to `H` through `b.repr`.
  set D : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
    resDiagMul (fun i => ((μ i : ℝ) : ℂ)) hC0 hCbound with hDdef
  have hDsingle : ∀ i, D (lp.single 2 i (1 : ℂ)) = ((μ i : ℝ) : ℂ) • lp.single 2 i 1 := by
    intro i
    refine lp.ext (funext fun j => ?_)
    simp only [hDdef, resDiagMul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  set Hop : H →L[ℂ] H :=
    (b.repr.symm.toContinuousLinearEquiv : ℓ²(ι, ℂ) →L[ℂ] H).comp
      (D.comp (b.repr.toContinuousLinearEquiv : H →L[ℂ] ℓ²(ι, ℂ))) with hHopdef
  have hHop : ∀ i, Hop (b i) = ((μ i : ℝ) : ℂ) • b i := by
    intro i
    rw [hHopdef]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [b.repr_self, hDsingle i, map_smul, b.repr_symm_single]
  exact ⟨Hop, hHop,
    isTraceClass_of_summable_eigenvalues b hHop hμnn hsum,
    traceE_eq_tsum_eigenvalues b hHop⟩

end QIQTH.TraceClass
