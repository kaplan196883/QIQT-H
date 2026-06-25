/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The bounded multiplication operator `M_φ` on `L²(μ)`

For a bounded measurable symbol `φ : α → ℂ` (`‖φ‖ ≤ C`), the pointwise multiplication
`f ↦ (s ↦ φ s · f s)` is a bounded `ℂ`-linear operator `M_φ : L²(μ) →L L²(μ)` with `‖M_φ‖ ≤ C`.

This is the first brick of the **multiplication PVM** (the position operator's spectral measure
`E(A) = M_{𝟙_A}`), which — Fourier-conjugated — yields the momentum/translation generator (the
`boostUnitary` generator, `WedgeKMSToGR.WedgeKMSFlux` input #5).  It mirrors `CrossedProductRep`'s
`matterRep` (operator-valued fiber multiplication) for the scalar case.  Axiom-free.
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace QIQTH.Spectral.Multiplication

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The multiplication fiber `s ↦ φ s · f s` is `AEStronglyMeasurable`. -/
theorem aesm_mulFiber {φ : α → ℂ} (hφ : Measurable φ) {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun s => φ s * f s) μ :=
  hφ.aestronglyMeasurable.mul hf

/-- The multiplication fiber `φ · f` lies in `L²` when `f` does and `φ` is bounded (`‖φ‖ ≤ C`),
    dominated pointwise by `C · ‖f s‖`. -/
theorem memLp_mulFiber {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ s, ‖φ s‖ ≤ C)
    (f : Lp ℂ 2 μ) : MemLp (fun s => φ s * (f s)) 2 μ :=
  MemLp.of_le_mul (Lp.memLp f) (aesm_mulFiber hφ (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun s => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC s) (norm_nonneg _))

/-- `M_φ f` as an `L²(μ)` element. -/
noncomputable def mulFun {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ s, ‖φ s‖ ≤ C)
    (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_mulFiber hφ hC f).toLp

/-- Its fiber: `(M_φ f)(s) = φ s · f s` a.e. -/
theorem mulFun_coeFn {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ s, ‖φ s‖ ≤ C)
    (f : Lp ℂ 2 μ) : mulFun hφ hC f =ᵐ[μ] fun s => φ s * (f s) := MemLp.coeFn_toLp _

theorem mulFun_add {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ s, ‖φ s‖ ≤ C)
    (f g : Lp ℂ 2 μ) : mulFun hφ hC (f + g) = mulFun hφ hC f + mulFun hφ hC g := by
  rw [Lp.ext_iff]
  filter_upwards [mulFun_coeFn hφ hC (f + g), Lp.coeFn_add (mulFun hφ hC f) (mulFun hφ hC g),
    mulFun_coeFn hφ hC f, mulFun_coeFn hφ hC g, Lp.coeFn_add f g] with s e1 e2 e3 e4 e5
  simp only [e1, e2, Pi.add_apply, e3, e4, e5, mul_add]

theorem mulFun_smul {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ s, ‖φ s‖ ≤ C) (c : ℂ)
    (f : Lp ℂ 2 μ) : mulFun hφ hC (c • f) = c • mulFun hφ hC f := by
  rw [Lp.ext_iff]
  filter_upwards [mulFun_coeFn hφ hC (c • f), Lp.coeFn_smul c (mulFun hφ hC f),
    mulFun_coeFn hφ hC f, Lp.coeFn_smul c f] with s e1 e2 e3 e4
  simp only [e1, e2, Pi.smul_apply, e3, e4, smul_eq_mul]; ring

theorem mulFun_norm_le {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s, ‖φ s‖ ≤ C)
    (f : Lp ℂ 2 μ) : ‖mulFun hφ hC f‖ ≤ C * ‖f‖ := by
  have hg : ‖mulFun hφ hC f‖ ≤ ‖(C : ℝ) • f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [mulFun_coeFn hφ hC f, Lp.coeFn_smul (C : ℝ) f] with s e1 e2
    rw [e1, e2, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC0, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC s) (norm_nonneg _)
  rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC0] at hg

/-- **The bounded multiplication operator `M_φ` on `L²(μ)`** for a bounded measurable symbol
    `φ` (`‖φ‖ ≤ C`): `(M_φ f)(s) = φ s · f s`, `ℂ`-linear with `‖M_φ‖ ≤ C`.  The first brick of the
    multiplication (position) PVM. -/
noncomputable def mulOp {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s, ‖φ s‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := mulFun hφ hC
      map_add' := mulFun_add hφ hC
      map_smul' := mulFun_smul hφ hC }
    C (mulFun_norm_le hφ hC0 hC)

@[simp] theorem mulOp_apply {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s, ‖φ s‖ ≤ C) (f : Lp ℂ 2 μ) : mulOp hφ hC0 hC f = mulFun hφ hC f := rfl

/-- `(M_φ f)(s) = φ s · f s` a.e. -/
theorem mulOp_coeFn {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s, ‖φ s‖ ≤ C)
    (f : Lp ℂ 2 μ) : mulOp hφ hC0 hC f =ᵐ[μ] fun s => φ s * (f s) := mulFun_coeFn hφ hC f

/-- **Multiplicativity `M_φ ∘ M_ψ = M_{φ·ψ}`** — the operator product is multiplication by the product
    symbol.  (The `*`-algebra-hom multiplicativity; gives idempotency of indicator multiplications.) -/
theorem mulOp_mul {φ ψ : α → ℂ} (hφ : Measurable φ) {Cφ : ℝ} (hCφ0 : 0 ≤ Cφ) (hCφ : ∀ s, ‖φ s‖ ≤ Cφ)
    (hψ : Measurable ψ) {Cψ : ℝ} (hCψ0 : 0 ≤ Cψ) (hCψ : ∀ s, ‖ψ s‖ ≤ Cψ) :
    mulOp (μ := μ) hφ hCφ0 hCφ ∘L mulOp (μ := μ) hψ hCψ0 hCψ
      = mulOp (μ := μ) (hφ.mul hψ) (mul_nonneg hCφ0 hCψ0)
          (fun s => by rw [norm_mul]; exact mul_le_mul (hCφ s) (hCψ s) (norm_nonneg _) hCφ0) := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.comp_apply, Lp.ext_iff]
  filter_upwards [mulOp_coeFn hφ hCφ0 hCφ (mulOp hψ hCψ0 hCψ f), mulOp_coeFn hψ hCψ0 hCψ f,
    mulOp_coeFn (hφ.mul hψ) (mul_nonneg hCφ0 hCψ0)
      (fun s => by rw [norm_mul]; exact mul_le_mul (hCφ s) (hCψ s) (norm_nonneg _) hCφ0) f]
    with s e1 e2 e3
  rw [e1, e2, e3]; ring

/-- **The constant symbol gives a scalar `M_c = c·1`.**  In particular `M_1 = 1` (unital). -/
theorem mulOp_const (c : ℂ) :
    mulOp (μ := μ) (φ := fun _ => c) measurable_const (norm_nonneg c) (fun _ => le_rfl)
      = c • (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, Lp.ext_iff]
  filter_upwards [mulOp_coeFn (μ := μ) (φ := fun _ => c) measurable_const (norm_nonneg c)
    (fun _ => le_rfl) f, Lp.coeFn_smul c f] with s e1 e2
  rw [e1, e2, Pi.smul_apply, smul_eq_mul]

/-- **Additivity in the symbol `M_φ + M_ψ = M_{φ+ψ}`.** -/
theorem mulOp_add {φ ψ : α → ℂ} (hφ : Measurable φ) {Cφ : ℝ} (hCφ0 : 0 ≤ Cφ) (hCφ : ∀ s, ‖φ s‖ ≤ Cφ)
    (hψ : Measurable ψ) {Cψ : ℝ} (hCψ0 : 0 ≤ Cψ) (hCψ : ∀ s, ‖ψ s‖ ≤ Cψ) :
    mulOp (μ := μ) hφ hCφ0 hCφ + mulOp (μ := μ) hψ hCψ0 hCψ
      = mulOp (μ := μ) (hφ.add hψ) (add_nonneg hCφ0 hCψ0)
          (fun s => (norm_add_le _ _).trans (add_le_add (hCφ s) (hCψ s))) := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.add_apply, Lp.ext_iff]
  filter_upwards [Lp.coeFn_add (mulOp hφ hCφ0 hCφ f) (mulOp hψ hCψ0 hCψ f),
    mulOp_coeFn hφ hCφ0 hCφ f, mulOp_coeFn hψ hCψ0 hCψ f,
    mulOp_coeFn (hφ.add hψ) (add_nonneg hCφ0 hCψ0)
      (fun s => (norm_add_le _ _).trans (add_le_add (hCφ s) (hCψ s))) f] with s e1 e2 e3 e4
  rw [e1, Pi.add_apply, e2, e3, e4]; ring

/-- **Subtractivity in the symbol `M_φ − M_ψ = M_{φ−ψ}`.** -/
theorem mulOp_sub {φ ψ : α → ℂ} (hφ : Measurable φ) {Cφ : ℝ} (hCφ0 : 0 ≤ Cφ) (hCφ : ∀ s, ‖φ s‖ ≤ Cφ)
    (hψ : Measurable ψ) {Cψ : ℝ} (hCψ0 : 0 ≤ Cψ) (hCψ : ∀ s, ‖ψ s‖ ≤ Cψ) :
    mulOp (μ := μ) hφ hCφ0 hCφ - mulOp (μ := μ) hψ hCψ0 hCψ
      = mulOp (μ := μ) (hφ.sub hψ) (add_nonneg hCφ0 hCψ0)
          (fun s => (norm_sub_le _ _).trans (add_le_add (hCφ s) (hCψ s))) := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.sub_apply, Lp.ext_iff]
  filter_upwards [Lp.coeFn_sub (mulOp hφ hCφ0 hCφ f) (mulOp hψ hCψ0 hCψ f),
    mulOp_coeFn hφ hCφ0 hCφ f, mulOp_coeFn hψ hCψ0 hCψ f,
    mulOp_coeFn (hφ.sub hψ) (add_nonneg hCφ0 hCψ0)
      (fun s => (norm_sub_le _ _).trans (add_le_add (hCφ s) (hCψ s))) f] with s e1 e2 e3 e4
  rw [e1, Pi.sub_apply, e2, e3, e4]; ring

/-- **Homogeneity in the symbol `M_{c·φ} = c · M_φ`.** -/
theorem mulOp_smul (c : ℂ) {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s, ‖φ s‖ ≤ C) :
    mulOp (μ := μ) (hφ.const_mul c) (mul_nonneg (norm_nonneg c) hC0)
        (fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC s) (norm_nonneg c))
      = c • mulOp (μ := μ) hφ hC0 hC := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.smul_apply, Lp.ext_iff]
  filter_upwards [mulOp_coeFn (hφ.const_mul c) (mul_nonneg (norm_nonneg c) hC0)
      (fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC s) (norm_nonneg c)) f,
    Lp.coeFn_smul c (mulOp hφ hC0 hC f), mulOp_coeFn hφ hC0 hC f] with s e1 e2 e3
  rw [e1, e2, Pi.smul_apply, e3, smul_eq_mul, mul_assoc]

/-- `M_φ` depends only on the symbol `φ` (not on the bound witness). -/
theorem mulOp_congr {φ φ' : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s, ‖φ s‖ ≤ C)
    (hφ' : Measurable φ') {C' : ℝ} (hC0' : 0 ≤ C') (hC' : ∀ s, ‖φ' s‖ ≤ C') (h : φ = φ') :
    mulOp (μ := μ) hφ hC0 hC = mulOp (μ := μ) hφ' hC0' hC' := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [Lp.ext_iff]
  filter_upwards [mulOp_coeFn hφ hC0 hC f, mulOp_coeFn hφ' hC0' hC' f] with s e1 e2
  rw [e1, e2, h]

/-- The complex indicator symbol `𝟙_A : α → ℂ`. -/
noncomputable def indSymbol (A : Set α) : α → ℂ := A.indicator (fun _ => 1)

theorem indSymbol_measurable {A : Set α} (hA : MeasurableSet A) : Measurable (indSymbol A) :=
  measurable_const.indicator hA

theorem indSymbol_norm_le (A : Set α) (s : α) : ‖indSymbol A s‖ ≤ 1 := by
  rw [indSymbol]
  by_cases h : s ∈ A
  · rw [Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h]; simp

theorem indSymbol_mul_self (A : Set α) (s : α) :
    indSymbol A s * indSymbol A s = indSymbol A s := by
  rw [indSymbol]
  by_cases h : s ∈ A
  · rw [Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h]; simp

/-- **The spectral projection `E(A) = M_{𝟙_A}`** — multiplication by the indicator of a measurable set `A`,
    the building block of the multiplication (position) PVM. -/
noncomputable def indMul {A : Set α} (hA : MeasurableSet A) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  mulOp (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)

/-- **`E(A)` is idempotent** `E(A)² = E(A)` (since `𝟙_A · 𝟙_A = 𝟙_A`).  With self-adjointness (`indMul_isSelfAdjoint`)
    this exhibits `E(A)` as an orthogonal projection — a spectral projection of the multiplication PVM. -/
theorem indMul_idempotent {A : Set α} (hA : MeasurableSet A) :
    indMul (μ := μ) hA ∘L indMul hA = indMul hA := by
  rw [indMul, mulOp_mul (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)
    (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)]
  exact mulOp_congr _ _ _ (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)
    (funext fun s => indSymbol_mul_self A s)

/-- **Adjoint of a multiplication operator `M_φ* = M_φ̄`** — the adjoint multiplies by the conjugate symbol,
    from the `L²` inner product `⟪M_φ̄ f, g⟫ = ⟪f, M_φ g⟫ = ∫ conj(φ·f)... `.  The `*`-structure of the
    multiplication `*`-algebra. -/
theorem mulOp_adjoint {φ : α → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s, ‖φ s‖ ≤ C) :
    ContinuousLinearMap.adjoint (mulOp (μ := μ) hφ hC0 hC)
      = mulOp (μ := μ) (Complex.continuous_conj.measurable.comp hφ) hC0
          (fun s => by simp only [Function.comp_apply, RCLike.norm_conj]; exact hC s) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [mulOp_coeFn (Complex.continuous_conj.measurable.comp hφ) hC0
    (fun s => by simp only [Function.comp_apply, RCLike.norm_conj]; exact hC s) x, mulOp_coeFn hφ hC0 hC y] with a e1 e2
  simp only [e1, e2, Function.comp_apply, RCLike.inner_apply', map_mul, RCLike.conj_conj]
  ring

/-- **`E(A)` is self-adjoint** `E(A)* = E(A)` (the indicator symbol is real, `conj 𝟙_A = 𝟙_A`).  Together with
    `indMul_idempotent` this is exactly: `E(A)` is an **orthogonal projection** — the spectral projection of
    the position observable. -/
theorem indMul_isSelfAdjoint {A : Set α} (hA : MeasurableSet A) :
    IsSelfAdjoint (indMul (μ := μ) hA) := by
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, indMul, mulOp_adjoint]
  exact mulOp_congr _ _ _ (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)
    (funext fun s => by
      by_cases h : s ∈ A <;> simp [indSymbol, Set.indicator_of_mem, Set.indicator_of_notMem, h])

theorem indSymbol_inter (A B : Set α) (s : α) :
    indSymbol A s * indSymbol B s = indSymbol (A ∩ B) s := by
  simp only [indSymbol]
  by_cases hA : s ∈ A <;> by_cases hB : s ∈ B <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hA, hB, Set.mem_inter_iff]

/-- **`E(univ) = 1`** (the multiplication PVM is normalized). -/
theorem indMul_univ : indMul (μ := μ) MeasurableSet.univ = 1 := by
  rw [indMul, mulOp_congr (indSymbol_measurable MeasurableSet.univ) zero_le_one (indSymbol_norm_le _)
    measurable_const (norm_nonneg (1 : ℂ)) (fun _ => le_rfl)
    (funext fun s => by simp [indSymbol]), mulOp_const, one_smul]

/-- **`E(∅) = 0`**. -/
theorem indMul_empty : indMul (μ := μ) MeasurableSet.empty = 0 := by
  rw [indMul, mulOp_congr (indSymbol_measurable MeasurableSet.empty) zero_le_one (indSymbol_norm_le _)
    measurable_const (norm_nonneg (0 : ℂ)) (fun _ => le_rfl)
    (funext fun s => by simp [indSymbol]), mulOp_const, zero_smul]

/-- **Multiplicativity of spectral projections `E(A)·E(B) = E(A∩B)`** — commuting orthogonal projections; in
    particular for disjoint `A, B` (`A∩B = ∅`) the projections are orthogonal `E(A)E(B) = 0`. -/
theorem indMul_inter {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    indMul (μ := μ) hA ∘L indMul hB = indMul (hA.inter hB) := by
  rw [indMul, indMul, mulOp_mul (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)
    (indSymbol_measurable hB) zero_le_one (indSymbol_norm_le B)]
  exact mulOp_congr _ _ _ (indSymbol_measurable (hA.inter hB)) zero_le_one (indSymbol_norm_le _)
    (funext fun s => indSymbol_inter A B s)

theorem indSymbol_union_disjoint {A B : Set α} (h : Disjoint A B) :
    indSymbol (A ∪ B) = fun s => indSymbol A s + indSymbol B s := by
  funext s
  simp only [indSymbol]
  by_cases hA : s ∈ A
  · rw [Set.indicator_of_mem (Set.mem_union_left B hA), Set.indicator_of_mem hA,
      Set.indicator_of_notMem (Set.disjoint_left.mp h hA)]; simp
  · by_cases hB : s ∈ B
    · rw [Set.indicator_of_mem (Set.mem_union_right A hB), Set.indicator_of_notMem hA,
        Set.indicator_of_mem hB]; simp
    · rw [Set.indicator_of_notMem (by simp [Set.mem_union, hA, hB]),
        Set.indicator_of_notMem hA, Set.indicator_of_notMem hB]; simp

/-- **Finite additivity of the spectral measure `E(A ⊔ B) = E(A) + E(B)`** for disjoint `A, B` — the
    multiplication PVM is finitely additive (the orthogonal projections onto `L²(A)` and `L²(B)` add). -/
theorem indMul_union_disjoint {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : Disjoint A B) :
    indMul (μ := μ) (hA.union hB) = indMul hA + indMul hB := by
  simp only [indMul]
  rw [mulOp_add (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)
    (indSymbol_measurable hB) zero_le_one (indSymbol_norm_le B)]
  exact mulOp_congr _ _ _ _ _ _ (indSymbol_union_disjoint h)

/-- **Orthogonality of the projections at the operator level:** for disjoint measurable `A, B` the
    spectral projections compose to zero, `E(A) ∘ E(B) = 0` (`A∩B = ∅`, so `𝟙_{A∩B} = 0`). -/
theorem indMul_comp_disjoint {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : Disjoint A B) : indMul (μ := μ) hA ∘L indMul hB = 0 := by
  have hAB : A ∩ B = ∅ := Set.disjoint_iff_inter_eq_empty.mp h
  rw [indMul_inter hA hB]
  simp only [indMul]
  rw [mulOp_congr (indSymbol_measurable (hA.inter hB)) zero_le_one (indSymbol_norm_le _)
    measurable_const (norm_nonneg (0 : ℂ)) (fun _ => le_rfl)
    (funext fun s => by simp [indSymbol, hAB]), mulOp_const, zero_smul]

/-- **Pairwise orthogonality of the spectral-projection vectors:** for disjoint measurable `A, B`,
    `⟪E(A) x, E(B) x⟫ = 0` — the projected components live in orthogonal subspaces `L²(A) ⟂ L²(B)`.
    The orthogonality input to the operator σ-additivity in `HasSum` form (unconditional, pairwise-disjoint). -/
theorem indMul_inner_orthogonal {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : Disjoint A B) (x : Lp ℂ 2 μ) :
    inner ℂ (indMul (μ := μ) hA x) (indMul hB x) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, (indMul_isSelfAdjoint hA).star_eq,
    ← ContinuousLinearMap.comp_apply, indMul_comp_disjoint hA hB h,
    ContinuousLinearMap.zero_apply, inner_zero_right]

/-- The spectral projection depends only on the *set* (the measurability proof is irrelevant): equal sets give
    the same operator. -/
theorem indMul_set_congr {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A = B) :
    indMul (μ := μ) hA = indMul hB := by subst h; rfl

/-- **Finite (range) additivity of the spectral measure over a `Finset`:** for a pairwise-disjoint measurable
    family `A`, `∑ᵢ∈s E(Aᵢ) = E(⋃ᵢ∈s Aᵢ)`. The discrete additivity feeding the unconditional (`HasSum`)
    σ-additivity — the orthogonal projections onto the `L²(Aᵢ)` add up to the projection onto their union. -/
theorem indMul_biUnion_disjoint {ι : Type*} (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∑ i ∈ s, indMul (μ := μ) (hA i) = indMul (s.measurableSet_biUnion (fun i _ => hA i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [indMul_set_congr (by simp : MeasurableSet (⋃ i ∈ (∅ : Finset ι), A i)) MeasurableSet.empty
      (by simp), indMul_empty]
  | @insert a s ha ih =>
    have hdisj : Disjoint (A a) (⋃ i ∈ s, A i) := by
      simp only [Set.disjoint_iUnion₂_right]
      exact fun i hi => hd (fun (hai : a = i) => ha (hai ▸ hi))
    rw [Finset.sum_insert ha, ih,
      ← indMul_union_disjoint (hA a) (s.measurableSet_biUnion (fun i _ => hA i)) hdisj,
      indMul_set_congr ((hA a).union (s.measurableSet_biUnion (fun i _ => hA i)))
        (Finset.measurableSet_biUnion _ (fun i _ => hA i)) (by rw [Finset.set_biUnion_insert])]

theorem indSymbol_sdiff {A B : Set α} (hAB : A ⊆ B) :
    indSymbol B = fun s => indSymbol A s + indSymbol (B \ A) s := by
  funext s
  simp only [indSymbol]
  by_cases hA : s ∈ A
  · rw [Set.indicator_of_mem (hAB hA), Set.indicator_of_mem hA,
      Set.indicator_of_notMem (by simp [Set.mem_diff, hA])]; simp
  · by_cases hB : s ∈ B
    · rw [Set.indicator_of_mem hB, Set.indicator_of_notMem hA,
        Set.indicator_of_mem (show s ∈ B \ A from ⟨hB, hA⟩)]; simp
    · rw [Set.indicator_of_notMem hB, Set.indicator_of_notMem hA,
        Set.indicator_of_notMem (by simp [Set.mem_diff, hB])]; simp

/-- **Subtractivity of the spectral measure `E(B) = E(A) + E(B \ A)`** for `A ⊆ B` (equivalently
    `E(B) − E(A) = E(B\A)`) — the finite-additive decomposition `B = A ⊔ (B\A)`, the building block for the
    operator σ-additivity. -/
theorem indMul_sdiff {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    indMul (μ := μ) hB = indMul hA + indMul (hB.diff hA) := by
  simp only [indMul]
  rw [mulOp_add (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)
    (indSymbol_measurable (hB.diff hA)) zero_le_one (indSymbol_norm_le _)]
  exact mulOp_congr _ _ _ _ _ _ (indSymbol_sdiff hAB)

/-- **The scalar spectral measure (diagonal):** `⟪f, E(A) f⟫ = ∫_A conj(f)·f dμ = ∫_A ‖f‖² dμ` — the `L²` mass
    of `f` on `A` (`conj(f a)·f a = ‖f a‖²`).  Since `E(A) = M_{𝟙_A}` is an orthogonal projection this is
    `‖E(A)f‖² ≥ 0`; as `A` varies it is the `‖f‖²`-weighted measure, the scalar spectral measure `μ_f` of the
    position PVM. -/
theorem indMul_inner_self {A : Set α} (hA : MeasurableSet A) (f : Lp ℂ 2 μ) :
    inner ℂ f (indMul hA f) = ∫ a in A, (starRingEnd ℂ) (f a) * f a ∂μ := by
  rw [indMul, MeasureTheory.L2.inner_def, ← MeasureTheory.integral_indicator hA]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [mulOp_coeFn (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A) f] with a e1
  rw [e1, RCLike.inner_apply']
  by_cases h : a ∈ A
  · simp only [Set.indicator_of_mem h, indSymbol, one_mul]
  · simp [indSymbol, Set.indicator_of_notMem h]

/-- **The norm of the spectral projection `‖E(A) f‖² = ∫_A ‖f‖² dμ`** — the `L²` mass of `f` on `A`.  As `A`
    varies this is the (genuine, real, nonnegative) scalar spectral measure `μ_f(A) = ∫_A ‖f‖²` of the position
    PVM; it is the key quantitative input to σ-additivity (the tail `∫_{A_N} ‖f‖² → 0`). -/
theorem norm_indMul_sq {A : Set α} (hA : MeasurableSet A) (f : Lp ℂ 2 μ) :
    ‖indMul (μ := μ) hA f‖ ^ 2 = ∫ a in A, ‖f a‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), indMul, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner _ _), ← MeasureTheory.integral_indicator hA]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [mulOp_coeFn (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A) f] with a e1
  rw [e1, inner_self_eq_norm_sq (𝕜 := ℂ)]
  by_cases h : a ∈ A
  · simp only [indSymbol, Set.indicator_of_mem h, one_mul]
  · simp [indSymbol, Set.indicator_of_notMem h]

/-- The squared `L²` norm as the integral of the pointwise squared norm, `‖x‖² = ∫ ‖x a‖² dμ` — read off the
    spectral measure at `A = univ` (`E(univ) = 1`). -/
theorem norm_sq_eq_integral (x : Lp ℂ 2 μ) : ‖x‖ ^ 2 = ∫ a, ‖x a‖ ^ 2 ∂μ := by
  have h := norm_indMul_sq (μ := μ) MeasurableSet.univ x
  rw [indMul_univ, ContinuousLinearMap.one_apply, MeasureTheory.setIntegral_univ] at h
  exact h

/-- **The spectral projection is contractive, `‖E(A) x‖ ≤ ‖x‖`** (`E(A)` is an orthogonal projection): the
    `L²` mass on `A` never exceeds the total mass. The uniform bound feeding the orthogonal-summability estimate
    `∑ ‖E(Aₙ)x‖² ≤ ‖x‖²`. -/
theorem norm_indMul_le {A : Set α} (hA : MeasurableSet A) (x : Lp ℂ 2 μ) :
    ‖indMul (μ := μ) hA x‖ ≤ ‖x‖ := by
  have hsq : ‖indMul hA x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_indMul_sq, norm_sq_eq_integral]
    refine MeasureTheory.setIntegral_le_integral ?_ (Filter.Eventually.of_forall fun a => sq_nonneg _)
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable x)).mp (Lp.memLp x)
  calc ‖indMul hA x‖ = Real.sqrt (‖indMul hA x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Two-vector orthogonality of the spectral projections:** for disjoint measurable `A, B`,
    `⟪E(A) x, E(B) y⟫ = 0` for *all* `x, y` (the ranges `L²(A) ⟂ L²(B)` are orthogonal subspaces). The form the
    `OrthogonalFamily` of the projection ranges requires (generalizes the same-vector `indMul_inner_orthogonal`). -/
theorem indMul_inner_orthogonal' {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : Disjoint A B) (x y : Lp ℂ 2 μ) :
    inner ℂ (indMul (μ := μ) hA x) (indMul hB y) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, (indMul_isSelfAdjoint hA).star_eq,
    ← ContinuousLinearMap.comp_apply, indMul_comp_disjoint hA hB h,
    ContinuousLinearMap.zero_apply, inner_zero_right]

/-- **Summability of the spectral components** `∑ₙ E(Aₙ) x` for a pairwise-disjoint measurable family — the
    analytic heart of the unconditional σ-additivity. The vectors `E(Aₙ) x` live in the pairwise-orthogonal
    ranges `L²(Aₙ)`, and `∑ₙ ‖E(Aₙ)x‖² ≤ ‖x‖²` (finite partial sums `= ‖E(⋃ᵢ₌₀ⁿ Aᵢ)x‖² ≤ ‖x‖²` by Pythagoras +
    contractivity), so by `OrthogonalFamily.summable_iff_norm_sq_summable` the family is summable in `L²`. -/
theorem summable_indMul {A : ℕ → Set α} (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (fun m n => Disjoint (A m) (A n))) (x : Lp ℂ 2 μ) :
    Summable (fun n => indMul (μ := μ) (hA n) x) := by
  classical
  set K : ℕ → Submodule ℂ (Lp ℂ 2 μ) := fun n => LinearMap.range (indMul (hA n)).toLinearMap with hKdef
  have hOF : OrthogonalFamily ℂ (fun n => (K n : Submodule ℂ (Lp ℂ 2 μ)))
      (fun n => (K n).subtypeₗᵢ) := by
    intro i j hij v w
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp v.2
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp w.2
    show inner ℂ (↑v : Lp ℂ 2 μ) (↑w : Lp ℂ 2 μ) = 0
    rw [← ha, ← hb]
    exact indMul_inner_orthogonal' (hA i) (hA j) (hd hij) a b
  set vv : (∀ n, (K n : Submodule ℂ (Lp ℂ 2 μ))) := fun n => ⟨indMul (hA n) x, ⟨x, rfl⟩⟩ with hvvdef
  have hVcoe : ∀ n, (K n).subtypeₗᵢ (vv n) = indMul (hA n) x := fun n => rfl
  have hsq : Summable (fun n => ‖vv n‖ ^ 2) := by
    apply summable_of_sum_range_le (c := ‖x‖ ^ 2) (fun n => sq_nonneg _)
    intro n
    rw [← hOF.norm_sum vv (Finset.range n)]
    have hsum_eq : ∑ i ∈ Finset.range n, (K i).subtypeₗᵢ (vv i)
        = indMul ((Finset.range n).measurableSet_biUnion (fun i _ => hA i)) x := by
      simp only [hVcoe]
      rw [← ContinuousLinearMap.sum_apply, indMul_biUnion_disjoint (Finset.range n) A hA hd]
    rw [hsum_eq]
    have hle := norm_indMul_le ((Finset.range n).measurableSet_biUnion (fun i _ => hA i)) x
    nlinarith [norm_nonneg (indMul ((Finset.range n).measurableSet_biUnion (fun i _ => hA i)) x),
      norm_nonneg x, hle]
  have hsummable := (hOF.summable_iff_norm_sq_summable vv).mpr hsq
  simpa only [hVcoe] using hsummable

/-- **σ-additivity of the scalar spectral measure (continuity from above):** for an antitone family of
    measurable sets `Bₙ`, the spectral-projection masses `‖E(Bₙ) f‖² = ∫_{Bₙ} ‖f‖²` converge to `∫_{⋂Bₙ} ‖f‖²`.
    In particular `Bₙ ↓ ∅ ⟹ ‖E(Bₙ) f‖ → 0` — the measure-tail that drives the operator σ-additivity of the
    position PVM (`E(⋃Aₙ) = ∑ E(Aₙ)` strong, for disjoint `Aₙ`).  From `norm_indMul_sq` +
    `tendsto_setIntegral_of_antitone` (`‖f‖² ∈ L¹` since `f ∈ L²`). -/
theorem norm_indMul_tendsto_iInter {B : ℕ → Set α} (hB : ∀ n, MeasurableSet (B n)) (hanti : Antitone B)
    (f : Lp ℂ 2 μ) :
    Filter.Tendsto (fun n => ‖indMul (μ := μ) (hB n) f‖ ^ 2) Filter.atTop
      (nhds (∫ a in ⋂ n, B n, ‖f a‖ ^ 2 ∂μ)) := by
  simp_rw [norm_indMul_sq]
  exact MeasureTheory.tendsto_setIntegral_of_antitone hB hanti
    ⟨0, ((MeasureTheory.memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)).integrableOn⟩

/-- **Operator σ-additivity / continuity from below of the spectral measure:** for a monotone increasing
    measurable family `Bₙ ↑ ⋃ₖ Bₖ`, the projections converge strongly, `E(Bₙ) f → E(⋃ₖ Bₖ) f` in `L²`.
    Proof: `‖E(Bₙ)f − E(⋃)f‖² = ‖E((⋃)\Bₙ)f‖² = ∫_{(⋃)\Bₙ}‖f‖²` (subtractivity `indMul_sdiff` + `norm_indMul_sq`),
    and `(⋃)\Bₙ ↓ ∅`, so the tail integral `→ ∫_∅ = 0` (`tendsto_setIntegral_of_antitone`); `‖·‖² → 0 ⟹ ‖·‖ → 0`.
    This is the genuine countable-additivity (strong-convergence) property of the position PVM. -/
theorem indMul_tendsto_iUnion {B : ℕ → Set α} (hB : ∀ n, MeasurableSet (B n)) (hmono : Monotone B)
    (f : Lp ℂ 2 μ) :
    Filter.Tendsto (fun n => indMul (μ := μ) (hB n) f) Filter.atTop
      (nhds (indMul (MeasurableSet.iUnion hB) f)) := by
  have hUmeas : MeasurableSet (⋃ k, B k) := MeasurableSet.iUnion hB
  have hCmeas : ∀ n, MeasurableSet ((⋃ k, B k) \ B n) := fun n => hUmeas.diff (hB n)
  have hsub : ∀ n, B n ⊆ ⋃ k, B k := fun n => Set.subset_iUnion B n
  have hCanti : Antitone (fun n => (⋃ k, B k) \ B n) :=
    fun _ _ hmn => Set.diff_subset_diff_right (hmono hmn)
  have hCinter : (⋂ n, (⋃ k, B k) \ B n) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Set.mem_iInter] at hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hx 0).1
    exact (hx k).2 hk
  -- ‖E(Bₙ)f − E(⋃)f‖² = ∫_{(⋃)\Bₙ}‖f‖²
  have hkey : ∀ n, ‖indMul (hB n) f - indMul hUmeas f‖ ^ 2
      = ∫ a in (⋃ k, B k) \ B n, ‖f a‖ ^ 2 ∂μ := by
    intro n
    have hdecomp : indMul hUmeas f = indMul (hB n) f + indMul (hCmeas n) f := by
      rw [indMul_sdiff (hB n) hUmeas (hsub n), ContinuousLinearMap.add_apply]
    rw [hdecomp,
      show indMul (hB n) f - (indMul (hB n) f + indMul (hCmeas n) f) = -(indMul (hCmeas n) f) from by abel,
      norm_neg, norm_indMul_sq]
  -- the tail integral → 0
  have hlim : Filter.Tendsto (fun n => ‖indMul (hB n) f - indMul hUmeas f‖ ^ 2) Filter.atTop (nhds 0) := by
    simp_rw [hkey]
    have htail := MeasureTheory.tendsto_setIntegral_of_antitone hCmeas hCanti
      (⟨0, ((MeasureTheory.memLp_two_iff_integrable_sq_norm
        (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)).integrableOn⟩ :
        ∃ n, MeasureTheory.IntegrableOn (fun a => ‖f a‖ ^ 2) ((⋃ k, B k) \ B n) μ)
    rw [hCinter, MeasureTheory.setIntegral_empty] at htail
    exact htail
  -- ‖·‖² → 0 ⟹ ‖·‖ → 0 ⟹ strong convergence
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : (fun n => ‖indMul (hB n) f - indMul hUmeas f‖)
      = fun n => Real.sqrt (‖indMul (hB n) f - indMul hUmeas f‖ ^ 2) := by
    funext n; rw [Real.sqrt_sq (norm_nonneg _)]
  rw [h2]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt

end QIQTH.Spectral.Multiplication
