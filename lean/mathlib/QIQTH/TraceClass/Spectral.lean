/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.TraceClass.Cyclic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The McKean–Singer identity `Tr A = ∑ λᵢ` and trace-class ⟸ summable spectrum

The **McKean–Singer identity** `Tr A = ∑ᵢ λᵢ` (the trace is the sum of the eigenvalues, computed in
an eigenbasis) together with **trace-class ⟸ summable spectrum**. **T4** (final) of the trace-class
API (**L5** of the heat-kernel full-infrastructure plan) — pure functional analysis, no manifold/PDE.

Specializes to `Tr e^{−tΔ} = Σ e^{−λt}` (the McKean–Singer heat trace, `mckean_singer_heatTrace`),
but the eigenbasis / discrete spectrum of `Δ` is the **L3 wall** (Rellich / elliptic regularity) and
is **carried as the hypothesis** `hA`. So this completes the trace-class API *given* a discrete
spectrum; it does **not** build the heat kernel or discharge the general `a₁ = R/6`. NOT the
conjecture, NOT QG. No axioms, no `sorry`.

## Main results

* `traceE_eq_tsum_eigenvalues` : **the McKean–Singer identity** `Tr A = ∑' i, μ i` for `A` with an
  eigenbasis `A (b i) = μ i • b i`. Unconditional (a `tsum` identity, no summability needed).
* `re_traceE_eq_tsum_eigenvalues` : the real part `(Tr A).re = ∑' i, μ i` (the eigenvalues `μ` real).
* `mckean_singer_heatTrace` : the headline specialization `Tr e^{−tΔ} = Σ e^{−λt}` (eigenvalues
  `e^{−t λᵢ}`), a direct instance of the McKean–Singer identity.
* `isTraceClass_of_summable_eigenvalues` : if a positive discrete spectrum `μ ≥ 0` is summable then
  `A` is trace-class, via the diagonal `√μ` multiplier `B` (bounded, Hilbert–Schmidt, `B ∘ B = A`).

## Implementation notes

The termwise identity `⟪b i, A (b i)⟫ = μ i` is `inner_smul_right` plus orthonormality
(`⟪b i, b i⟫ = 1`). For the trace-class direction, the diagonal `√μ` operator is built as an
ℓ²-multiplier `diagMul` (a `LinearMap.mkContinuous` on `lp`, bounded by `√(∑' μ)` via `lp.norm_mono`),
transported to `H` through `b.repr`; it is Hilbert–Schmidt because `∑ ‖B (b i)‖² = ∑ μ i < ∞`, and
`B ∘ B = A` by `ContinuousLinearMap.ext_on` on the (dense) span of the basis, giving
`A = (Bᴴ)ᴴ ∘ B` with `Bᴴ`, `B` Hilbert–Schmidt.
-/

open scoped ENNReal NNReal ComplexInnerProductSpace lp

namespace QIQTH.TraceClass

variable {ι κ : Type*} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The McKean–Singer identity: trace = sum of eigenvalues -/

omit [CompleteSpace H] in
/-- **The McKean–Singer identity.** If `b` is a Hilbert basis diagonalizing `A`, with real
eigenvalues `μ` (`A (b i) = μ i • b i`), then the trace is the sum of the eigenvalues
`Tr A = ∑' i, μ i`. This is *unconditional*: a `tsum` identity, no summability hypothesis. Termwise,
`⟪b i, A (b i)⟫ = ⟪b i, μ i • b i⟫ = μ i · ⟪b i, b i⟫ = μ i` by `inner_smul_right` and
orthonormality (`⟪b i, b i⟫ = 1`). -/
theorem traceE_eq_tsum_eigenvalues (b : HilbertBasis ι ℂ H) {A : H →L[ℂ] H} {μ : ι → ℝ}
    (hA : ∀ i, A (b i) = ((μ i : ℝ) : ℂ) • b i) :
    traceE b A = ∑' i, ((μ i : ℝ) : ℂ) := by
  unfold traceE
  refine tsum_congr fun i => ?_
  have hself : (inner ℂ (b i) (b i) : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one i]; norm_num
  rw [hA i, inner_smul_right, hself, mul_one]

omit [CompleteSpace H] in
/-- **Real part of the McKean–Singer identity.** Since the eigenvalues `μ` are real, the real part of
the trace is the (real) sum of the eigenvalues, `(Tr A).re = ∑' i, μ i`. -/
theorem re_traceE_eq_tsum_eigenvalues (b : HilbertBasis ι ℂ H) {A : H →L[ℂ] H} {μ : ι → ℝ}
    (hA : ∀ i, A (b i) = ((μ i : ℝ) : ℂ) • b i) :
    (traceE b A).re = ∑' i, μ i := by
  rw [traceE_eq_tsum_eigenvalues b hA, ← Complex.ofReal_tsum, Complex.ofReal_re]

omit [CompleteSpace H] in
/-- **The McKean–Singer heat trace** `Tr e^{−tΔ} = Σ e^{−λt}`. A direct instance of the McKean–Singer
identity for a heat semigroup `A = e^{−tΔ}` whose eigenvalues are `e^{−t λᵢ}`. The eigenbasis of `Δ`
(discrete spectrum, the L3 wall) is *carried* as the hypothesis `hA`. -/
theorem mckean_singer_heatTrace (b : HilbertBasis ι ℂ H) {A : H →L[ℂ] H} (t : ℝ) (lam : ι → ℝ)
    (hA : ∀ i, A (b i) = ((Real.exp (-(t * lam i)) : ℝ) : ℂ) • b i) :
    traceE b A = ∑' i, ((Real.exp (-(t * lam i)) : ℝ) : ℂ) :=
  traceE_eq_tsum_eigenvalues b hA

/-! ### The diagonal `√μ` multiplier on `ℓ²` -/

/-- The **diagonal multiplication** `f ↦ (i ↦ σ i · f i)` by a norm-bounded scalar family `σ`, as a
linear map on `ℓ²(ι, ℂ)`. It lands in `ℓ²` because `‖σ i · f i‖ = ‖σ i‖ ‖f i‖ ≤ C ‖f i‖`. -/
private noncomputable def diagMulₗ (σ : ι → ℂ) {C : ℝ} (hC : ∀ i, ‖σ i‖ ≤ C) :
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
private theorem diagMulₗ_apply (σ : ι → ℂ) {C : ℝ} (hC : ∀ i, ‖σ i‖ ≤ C) (f : ℓ²(ι, ℂ)) (i : ι) :
    (diagMulₗ σ hC f) i = σ i * f i := rfl

/-- The diagonal multiplier as a *bounded* operator on `ℓ²`, with operator norm `≤ C`. The bound is
`lp.norm_mono` against `C • f` (pointwise `‖σ i · f i‖ ≤ C ‖f i‖`, then `‖C • f‖ = C ‖f‖`). -/
private noncomputable def diagMul (σ : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖σ i‖ ≤ C) :
    ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  (diagMulₗ σ hC).mkContinuous C (fun f => by
    refine (lp.norm_mono (y := (C : ℂ) • f) (by norm_num) (fun i => ?_)).trans (le_of_eq ?_)
    · rw [diagMulₗ_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)
    · rw [lp.norm_const_smul (by norm_num), Complex.norm_real, Real.norm_of_nonneg hC0])

private theorem diagMul_apply (σ : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖σ i‖ ≤ C)
    (f : ℓ²(ι, ℂ)) (i : ι) : (diagMul σ hC0 hC f) i = σ i * f i := rfl

/-! ### Trace-class from a summable positive spectrum -/

/-- **Trace-class from a summable positive spectrum.** If `A` is diagonalized by a Hilbert basis with
a *nonnegative, summable* spectrum `μ`, then `A` is trace-class. Construct the diagonal `√μ`
multiplier `B` (bounded since `√μ ≤ √(∑' μ)`); it is Hilbert–Schmidt (`∑ ‖B (b i)‖² = ∑ μ i < ∞`) and
satisfies `B ∘ B = A`, so `A = (Bᴴ)ᴴ ∘ B` exhibits the trace-class factorization. -/
theorem isTraceClass_of_summable_eigenvalues (b : HilbertBasis ι ℂ H) {A : H →L[ℂ] H} {μ : ι → ℝ}
    (hA : ∀ i, A (b i) = ((μ i : ℝ) : ℂ) • b i) (hμ : ∀ i, 0 ≤ μ i) (hsum : Summable μ) :
    IsTraceClass A := by
  classical
  -- `√·` of the complex-valued family, with the uniform bound `C = √(∑' μ)`.
  have hnc : ∀ r : ℝ, 0 ≤ r → ‖(r : ℂ)‖ = r := fun r hr => by
    rw [Complex.norm_real, Real.norm_of_nonneg hr]
  set C : ℝ := Real.sqrt (∑' i, μ i) with hCdef
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hCbound : ∀ i, ‖((Real.sqrt (μ i) : ℝ) : ℂ)‖ ≤ C := by
    intro i
    rw [hnc _ (Real.sqrt_nonneg _), hCdef]
    exact Real.sqrt_le_sqrt (hsum.le_tsum i (fun j _ => hμ j))
  -- The diagonal `√μ` operator on `ℓ²`, transported to `H`.
  set D : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
    diagMul (fun i => ((Real.sqrt (μ i) : ℝ) : ℂ)) hC0 hCbound with hDdef
  have hDsingle : ∀ i, D (lp.single 2 i (1 : ℂ)) = ((Real.sqrt (μ i) : ℝ) : ℂ) • lp.single 2 i 1 := by
    intro i
    refine lp.ext (funext fun j => ?_)
    simp only [hDdef, diagMul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  set B : H →L[ℂ] H :=
    (b.repr.symm.toContinuousLinearEquiv : ℓ²(ι, ℂ) →L[ℂ] H).comp
      (D.comp (b.repr.toContinuousLinearEquiv : H →L[ℂ] ℓ²(ι, ℂ))) with hBdef
  -- `B` acts diagonally: `B (b i) = √μ i • b i`.
  have hBbasis : ∀ i, B (b i) = ((Real.sqrt (μ i) : ℝ) : ℂ) • b i := by
    intro i
    rw [hBdef]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [b.repr_self, hDsingle i, map_smul, b.repr_symm_single]
  -- `B` is Hilbert–Schmidt: `∑ ‖B (b i)‖² = ∑ μ i < ∞`.
  have hBHS : IsHilbertSchmidt B := by
    rw [isHilbertSchmidt_iff_summable b]
    refine hsum.congr (fun i => ?_)
    rw [hBbasis i, norm_smul, hnc _ (Real.sqrt_nonneg _), b.orthonormal.norm_eq_one i, mul_one,
      Real.sq_sqrt (hμ i)]
  -- `B ∘ B = A`, checked on the (dense) span of the basis.
  have hBB : B.comp B = A := by
    refine ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) ?_
    rintro x ⟨i, rfl⟩
    rw [ContinuousLinearMap.comp_apply, hBbasis i, map_smul, hBbasis i, smul_smul, hA i,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (hμ i)]
  -- Assemble the trace-class factorization `A = (Bᴴ)ᴴ ∘ B`.
  exact ⟨ContinuousLinearMap.adjoint B, B, (isHilbertSchmidt_adjoint B).mp hBHS, hBHS, by
    rw [ContinuousLinearMap.adjoint_adjoint, hBB]⟩

end QIQTH.TraceClass
