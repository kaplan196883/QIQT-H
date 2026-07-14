/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.TraceClass.IntegralKernelHS
import QIQTH.TraceClass.CompactSpectral
import Mathlib.Topology.UniformSpace.Dini

/-!
# Toward Mercer's theorem: continuity of the integral operator and the trace identity

For a **continuous** kernel `K` on a **compact** space `X` carrying a **finite** measure `μ`, the
integral operator `T_K` on `L²(μ)` smooths `L¹`/`L²` inputs to *continuous* functions.  In
particular its eigenfunctions (for a nonzero eigenvalue) have continuous representatives.  Mercer's
theorem then asserts the trace identity
`Tr T_K = ∫ x, K x x ∂μ`
(for a Hermitian, positive kernel), tying the two McKean–Singer sides together.

This file is *manifold-free*: only a compact space with a finite Borel measure and a jointly
continuous kernel.

## Main results (which landed vs. checkpointed)

* `memLp_of_continuous_kernel` (**helper**): a jointly continuous kernel on the compact product,
  being bounded, lies in `L²(μ × μ)`, so `integralOpCLM` applies.
* `continuous_integralOp_apply` (**A — landed**): `x ↦ ∫ y, K x y · f y ∂μ` is continuous for any
  `f ∈ L¹(μ)`.  Proved by dominated convergence (`continuousAt_of_dominated`): `K` is bounded on the
  compact product `X × X`, `x ↦ K x y` is continuous, and `M · ‖f‖` dominates.
* `eigenfunction_continuous` (**B — landed**): if `T_K φ = c • φ` in `L²(μ)` with `c ≠ 0`, then the
  class `φ` has a continuous representative, namely `x ↦ c⁻¹ · ∫ y, K x y · φ y ∂μ`.
* `integralOpCLM_isSelfAdjoint` (**C, self-adjointness — landed**): a Hermitian kernel
  `K y x = conj (K x y)` gives a self-adjoint `T_K`, via a Fubini swap of the double-integral form of
  the `L²` inner products.
* `mercer_traceE_eq_tsum_eigenvalues` (**C, trace half — landed given self-adjointness**): for a
  self-adjoint `T_K` the trace is the sum of the (real) eigenvalues `Tr T_K = ∑' i, λ i`, via the
  compact self-adjoint spectral theorem.
* `mercer_traceE_eq_tsum_eigenvalues_of_hermitian` (**C, trace half, Hermitian — landed**): the same
  conclusion for a Hermitian kernel with *no* carried self-adjointness hypothesis (combining the
  previous two).
* `mercer_eigenvalues_nonneg` (**C, positivity half — landed**): if `T_K` is a positive operator
  then every eigenvalue is `≥ 0`.

## Honest firewall

This is the McKean–Singer **geometric-side bridge** `Tr = ∫ diagonal`.  The *analytic core of
Mercer* — the pointwise diagonal series `∑ᵢ λᵢ |φᵢ(x)|² = K(x,x)` (uniform convergence by **Dini**,
positivity of the remainder kernel) and its **termwise integration** to `∑ᵢ λᵢ = ∫ K(x,x)` — is
**not** discharged here; it is recorded as the checkpointed wall (see the note at the end of the
file).  Nothing here builds the manifold heat kernel or discharges the general `a₁ = R/6`
(irreducibly behind the manifold heat-kernel parametrix / curvature, layers L0/L1/L4).  NOT the
conjecture, NOT QG.  No axioms, no `sorry`.
-/

open scoped ENNReal NNReal ComplexInnerProductSpace
open MeasureTheory

namespace QIQTH.TraceClass

section Mercer

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {K : X → X → ℂ}

/-- **A jointly continuous kernel on a compact space lies in `L²(μ × μ)`.**  On the compact product
`X × X`, `‖K‖` is bounded by some `M`, and `μ × μ` is finite, so `MemLp.of_bound` applies. -/
theorem memLp_of_continuous_kernel (hKc : Continuous fun p : X × X => K p.1 p.2) :
    MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ) := by
  obtain ⟨M, hM⟩ := (isCompact_range (X := X × X) hKc.norm).bddAbove
  exact MemLp.of_bound hKc.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun p => hM ⟨p, rfl⟩)

/-! ### A — the continuity lemma (the clean anchor) -/

omit [IsFiniteMeasure μ] in
/-- **A — the integral operator smooths `L¹` to continuous functions.**  For a jointly continuous
kernel `K` on the compact space `X` and any `f ∈ L¹(μ)`, the function `x ↦ ∫ y, K x y · f y ∂μ` is
continuous.  Proof by dominated convergence: `K` is bounded by some `M` on the compact product, so
`‖K x y · f y‖ ≤ M · ‖f y‖` (integrable, independent of `x`); each `x ↦ K x y · f y` is continuous;
`continuousAt_of_dominated` concludes.

This is the foundation of Mercer's theorem: the eigenfunctions of `T_K` are continuous. -/
theorem continuous_integralOp_apply (hKc : Continuous fun p : X × X => K p.1 p.2)
    {f : X → ℂ} (hf : Integrable f μ) :
    Continuous (fun x => ∫ y, K x y * f y ∂μ) := by
  obtain ⟨M, hM⟩ := (isCompact_range (X := X × X) hKc.norm).bddAbove
  have hKbound : ∀ x y : X, ‖K x y‖ ≤ M := fun x y => hM ⟨(x, y), rfl⟩
  rw [continuous_iff_continuousAt]
  intro x₀
  refine continuousAt_of_dominated (bound := fun y => M * ‖f y‖) ?_ ?_ ?_ ?_
  · -- a.e. strong measurability of `y ↦ K x y · f y`, uniformly near `x₀`
    refine Filter.Eventually.of_forall fun x => ?_
    exact ((hKc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · -- domination `‖K x y · f y‖ ≤ M · ‖f y‖`
    refine Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hKbound x y) (norm_nonneg _)
  · -- the dominating function `M · ‖f‖` is integrable
    exact hf.norm.const_mul M
  · -- pointwise continuity `x ↦ K x y · f y` at `x₀`
    refine Filter.Eventually.of_forall fun y => ?_
    exact ((hKc.comp (continuous_id.prodMk continuous_const)).mul continuous_const).continuousAt

/-! ### B — eigenfunctions are continuous -/

/-- **B — eigenfunctions of `T_K` (for a nonzero eigenvalue) are continuous.**  If
`integralOpCLM hK φ = c • φ` in `L²(μ)` with `c ≠ 0`, then `φ` equals a.e. the *continuous* function
`x ↦ c⁻¹ · ∫ y, K x y · φ y ∂μ` (continuity from A, `φ ∈ L² ⊆ L¹` on a finite measure). -/
theorem eigenfunction_continuous (hKc : Continuous fun p : X × X => K p.1 p.2)
    {φ : X →₂[μ] ℂ} {c : ℂ} (hc : c ≠ 0)
    (heig : integralOpCLM (memLp_of_continuous_kernel hKc) φ = c • φ) :
    ∃ g : X → ℂ, Continuous g ∧ (⇑φ) =ᵐ[μ] g := by
  have hφint : Integrable (⇑φ) μ := (Lp.memLp φ).integrable (by norm_num)
  refine ⟨fun x => c⁻¹ * ∫ y, K x y * (φ : X → ℂ) y ∂μ, ?_, ?_⟩
  · exact continuous_const.mul (continuous_integralOp_apply hKc hφint)
  · have key : ⇑(integralOpCLM (memLp_of_continuous_kernel hKc) φ) =ᵐ[μ] c • ⇑φ := by
      rw [heig]; exact Lp.coeFn_smul c φ
    filter_upwards [integralOpCLM_apply (memLp_of_continuous_kernel hKc) φ, key] with x hx hkx
    have hval : (∫ y, K x y * (φ : X → ℂ) y ∂μ) = c * (φ : X → ℂ) x := by
      have h := hx.symm.trans hkx
      simpa only [Pi.smul_apply, smul_eq_mul] using h
    rw [hval, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-! ### C — toward the Mercer trace identity `Tr T_K = ∫ K x x`

The full identity has two halves.  The **trace half**, `Tr T_K = ∑ᵢ λᵢ` (McKean–Singer), is landed
below from the compact self-adjoint spectral theorem; the **positivity half**, `λᵢ ≥ 0`, is landed
from operator positivity.  The remaining piece — the *diagonal series* `∑ᵢ λᵢ = ∫ K x x` — is the
checkpointed wall (see the note after the theorems). -/

/-- **C (trace half) — the trace of a self-adjoint integral operator is the sum of its eigenvalues.**
For a jointly continuous kernel whose integral operator `T_K` is self-adjoint (e.g. a Hermitian
kernel `K y x = conj (K x y)`), `T_K` is compact (its kernel is `L²`), so by the compact self-adjoint
spectral theorem it has an orthonormal eigenbasis `b` with real eigenvalues `λ`, and
`Tr T_K = ∑' i, λ i`.  This is the McKean–Singer side of Mercer's identity. -/
theorem mercer_traceE_eq_tsum_eigenvalues (hKc : Continuous fun p : X × X => K p.1 p.2)
    (hsa : IsSelfAdjoint (integralOpCLM (μ := μ) (memLp_of_continuous_kernel hKc))) :
    ∃ (κ : Type u) (b : HilbertBasis κ ℂ (X →₂[μ] ℂ)) (lam : κ → ℝ),
      (∀ i, integralOpCLM (memLp_of_continuous_kernel hKc) (b i) = ((lam i : ℝ) : ℂ) • b i) ∧
        traceE b (integralOpCLM (memLp_of_continuous_kernel hKc))
          = ∑' i, ((lam i : ℝ) : ℂ) :=
  compactSelfAdjoint_traceE_eq_tsum_eigenvalues
    (integralOpCLM_isCompactOperator (μ := μ) (memLp_of_continuous_kernel hKc)) hsa

/-- **C (positivity half) — the eigenvalues of a positive integral operator are nonnegative.**
If `T_K` is a positive operator (`0 ≤ (⟪f, T_K f⟫).re` for all `f`; this holds for a positive-definite
kernel), then along an orthonormal eigenbasis every eigenvalue satisfies `λ i ≥ 0`, since
`⟪b i, T_K (b i)⟫ = λ i · ⟪b i, b i⟫ = λ i`. -/
theorem mercer_eigenvalues_nonneg (hKc : Continuous fun p : X × X => K p.1 p.2)
    {κ : Type*} (b : HilbertBasis κ ℂ (X →₂[μ] ℂ)) {lam : κ → ℝ}
    (hlam : ∀ i, integralOpCLM (memLp_of_continuous_kernel hKc) (b i) = ((lam i : ℝ) : ℂ) • b i)
    (hpos : ∀ f : X →₂[μ] ℂ,
      0 ≤ (inner ℂ f (integralOpCLM (memLp_of_continuous_kernel hKc) f)).re) (i : κ) :
    0 ≤ lam i := by
  have h := hpos (b i)
  have hself : (inner ℂ (b i) (b i) : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one i]; norm_num
  rw [hlam i, inner_smul_right, hself, mul_one] at h
  simpa using h

/-- **C (self-adjointness) — a Hermitian continuous kernel gives a self-adjoint integral operator.**
If `K y x = conj (K x y)`, then `⟪T_K f, g⟫ = ⟪f, T_K g⟫`: unfolding the `L²` inner products to double
integrals, `⟪T_K f, g⟫ = ∫∫ conj(K x y) conj(f y) g x` and `⟪f, T_K g⟫ = ∫∫ conj(f x) K x y g y`, and
the second turns into the first by Fubini (`integral_integral_swap`, the integrand being integrable on
the finite product measure) followed by the Hermitian symmetry `K y x = conj (K x y)`. -/
theorem integralOpCLM_isSelfAdjoint (hKc : Continuous fun p : X × X => K p.1 p.2)
    (hHerm : ∀ x y, K y x = starRingEnd ℂ (K x y)) :
    IsSelfAdjoint (integralOpCLM (μ := μ) (memLp_of_continuous_kernel hKc)) := by
  set hK := memLp_of_continuous_kernel (μ := μ) hKc with hKdef
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  obtain ⟨M, hM⟩ := (isCompact_range (X := X × X) hKc.norm).bddAbove
  have hKbound : ∀ x y : X, ‖K x y‖ ≤ M := fun x y => hM ⟨(x, y), rfl⟩
  have hfi : Integrable (⇑f) μ := (Lp.memLp f).integrable (by norm_num)
  have hgi : Integrable (⇑g) μ := (Lp.memLp g).integrable (by norm_num)
  set A : X → X → ℂ :=
    fun x y => starRingEnd ℂ (K x y) * starRingEnd ℂ ((f : X → ℂ) y) * (g : X → ℂ) x with hAdef
  set B : X → X → ℂ :=
    fun x y => starRingEnd ℂ ((f : X → ℂ) x) * (K x y * (g : X → ℂ) y) with hBdef
  -- `⟪T_K f, g⟫ = ∫ x, ∫ y, A x y`.
  have hTf : (inner ℂ (integralOpCLM hK f) g : ℂ) = ∫ x, ∫ y, A x y ∂μ ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [integralOpCLM_apply hK f] with x hx
    rw [RCLike.inner_apply', hx, ← integral_conj, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hAdef, map_mul]
  -- `⟪f, T_K g⟫ = ∫ x, ∫ y, B x y`.
  have hfTg : (inner ℂ f (integralOpCLM hK g) : ℂ) = ∫ x, ∫ y, B x y ∂μ ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [integralOpCLM_apply hK g] with x hx
    rw [RCLike.inner_apply', hx, ← integral_const_mul]
  -- `uncurry B` is integrable on the finite product measure (dominated by `M · ‖f‖ · ‖g‖`).
  have hBint : Integrable (Function.uncurry B) (μ.prod μ) := by
    have hD : Integrable
        (fun p : X × X => M * ‖(f : X → ℂ) p.1‖ * ‖(g : X → ℂ) p.2‖) (μ.prod μ) :=
      Integrable.mul_prod (hfi.norm.const_mul M) hgi.norm
    refine hD.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (Complex.continuous_conj.comp_aestronglyMeasurable
        ((Lp.aestronglyMeasurable f).comp_fst)).mul
        (hK.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable g).comp_snd))
    · simp only [Function.uncurry, hBdef, norm_mul, RCLike.norm_conj]
      nlinarith [hKbound p.1 p.2, norm_nonneg ((f : X → ℂ) p.1), norm_nonneg ((g : X → ℂ) p.2),
        mul_nonneg (mul_nonneg (norm_nonneg ((f : X → ℂ) p.1)) (norm_nonneg ((g : X → ℂ) p.2)))
          (sub_nonneg.mpr (hKbound p.1 p.2))]
  -- Assemble: Fubini swap of `B`, then the Hermitian symmetry turns `B` into `A`.
  show (inner ℂ (integralOpCLM hK f) g : ℂ) = inner ℂ f (integralOpCLM hK g)
  rw [hTf, hfTg, integral_integral_swap hBint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a =>
    integral_congr_ae (Filter.Eventually.of_forall fun b => ?_))
  simp only [hAdef, hBdef]
  rw [hHerm a b]; ring

/-- **C (trace half, Hermitian form) — the trace of the integral operator of a Hermitian continuous
kernel is the sum of its eigenvalues.**  Combines `integralOpCLM_isSelfAdjoint` with
`mercer_traceE_eq_tsum_eigenvalues`, so no self-adjointness hypothesis need be carried: for a
Hermitian kernel `K y x = conj (K x y)`, `T_K` has an orthonormal eigenbasis with real eigenvalues
`λ` and `Tr T_K = ∑' i, λ i`. -/
theorem mercer_traceE_eq_tsum_eigenvalues_of_hermitian
    (hKc : Continuous fun p : X × X => K p.1 p.2)
    (hHerm : ∀ x y, K y x = starRingEnd ℂ (K x y)) :
    ∃ (κ : Type u) (b : HilbertBasis κ ℂ (X →₂[μ] ℂ)) (lam : κ → ℝ),
      (∀ i, integralOpCLM (memLp_of_continuous_kernel hKc) (b i) = ((lam i : ℝ) : ℂ) • b i) ∧
        traceE b (integralOpCLM (memLp_of_continuous_kernel hKc))
          = ∑' i, ((lam i : ℝ) : ℂ) :=
  mercer_traceE_eq_tsum_eigenvalues hKc (integralOpCLM_isSelfAdjoint hKc hHerm)

/-! ### Checkpoint — the analytic core of Mercer that is *not* closed here

Combining `mercer_traceE_eq_tsum_eigenvalues` (`Tr T_K = ∑ᵢ λᵢ`) with the full trace identity
`Tr T_K = ∫ x, K x x ∂μ` reduces to the **diagonal series identity**
`∑ᵢ λᵢ = ∫ x, K x x ∂μ`, whose standard proof (Mercer's theorem proper) requires:

1. **Pointwise positivity of the continuous kernel.** For a *continuous* kernel whose operator `T_K`
   is positive, the kernel is pointwise positive-semidefinite, and the *remainder kernel*
   `K_n(x, y) = K x y − ∑_{i<n} λᵢ φᵢ(x) conj (φᵢ y)` is again such a kernel, so its diagonal
   `K x x − ∑_{i<n} λᵢ |φᵢ(x)|² ≥ 0`.  This "operator-positivity ⟹ pointwise-PSD for continuous
   kernels" step has *no* Mathlib support.
2. **Dini's theorem.** The partial sums `x ↦ ∑_{i<n} λᵢ |φᵢ(x)|²` are continuous (each `φᵢ` is
   continuous by `eigenfunction_continuous`), increase monotonically (step 1), and converge pointwise
   to the continuous function `x ↦ K x x`; Dini (`Mathlib.Topology.UniformSpace.Dini`) upgrades this
   to *uniform* convergence — but only after step 1 supplies monotonicity and the pointwise limit,
   which is exactly the unbuilt piece.
3. **Termwise integration.** Uniform convergence on the *finite* measure `μ` lets one integrate the
   series term by term, giving `∑ᵢ λᵢ ∫ |φᵢ|² = ∑ᵢ λᵢ = ∫ K x x`.

Steps 2 and 3 are within reach given Mathlib, but step 1 (the diagonal identity / pointwise PSD of a
continuous positive-definite kernel, i.e. the Mercer series converging to `K` on the diagonal) is the
genuine wall.  It is recorded here, not discharged.  This file therefore lands the **operator side**
of the McKean–Singer bridge (`Tr = ∑ λ`, continuity/smoothing, positivity of the spectrum) and leaves
the analytic diagonal identity as the cited frontier. -/

end Mercer

end QIQTH.TraceClass
