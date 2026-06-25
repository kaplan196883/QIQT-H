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

/-- **`E(A)` is idempotent** `E(A)² = E(A)` (since `𝟙_A · 𝟙_A = 𝟙_A`).  With self-adjointness (to come, via the
    `L²` inner product) this exhibits `E(A)` as an orthogonal projection — a spectral projection of the
    multiplication PVM. -/
theorem indMul_idempotent {A : Set α} (hA : MeasurableSet A) :
    indMul (μ := μ) hA ∘L indMul hA = indMul hA := by
  rw [indMul, mulOp_mul (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)
    (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)]
  exact mulOp_congr _ _ _ (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)
    (funext fun s => indSymbol_mul_self A s)

end QIQTH.Spectral.Multiplication
