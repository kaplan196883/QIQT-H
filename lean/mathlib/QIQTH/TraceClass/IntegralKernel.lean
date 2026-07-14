/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.TraceClass.Compact
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral operators on `L²(X, μ)` with an `L²` kernel

This file *starts* the theory of integral operators on `L²(X, μ)` induced by a kernel
`K : X → X → ℂ` that lies in `L²(X × X)`.  Mathlib currently has **no** integral-operator theory
at all, so everything here is built from the measure-theoretic foundations (Tonelli, `MemLp`,
Cauchy–Schwarz).  The manifold-free abstract core: any σ-finite measure space.

## Main results

* `kernel_lintegral_section_eq` (**T1**, the section/Tonelli identity): the iterated Lebesgue
  integral of `‖K x y‖²` equals the integral over the product,
  `∫⁻ x, ∫⁻ y, ‖K x y‖₊² ∂μ ∂μ = ∫⁻ p, ‖K p.1 p.2‖₊² ∂(μ.prod μ)`.  Pure Tonelli.
* `kernel_lintegral_prod_ne_top` : the product integral is finite (from `K ∈ L²(X × X)`).
* `kernel_section_memLp` : for a.e. `x`, the section `y ↦ K x y` is itself in `L²(μ)`.

## Honest firewall

This is the abstract functional-analytic core of *"an integral operator with an `L²` kernel is
Hilbert–Schmidt"* — the McKean–Singer **geometric-side bridge** infrastructure.  It does **not**
build the manifold heat kernel, and it does **not** discharge the general `a₁ = R/6` coefficient
(which lives in the manifold heat-kernel parametrix / curvature — the deepest wall, layers
L0/L1/L4).  NOT the conjecture, NOT QG.  No axioms, no `sorry`.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace QIQTH.TraceClass

section IntegralKernel

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
variable {K : X → X → ℂ}

omit [SigmaFinite μ] in
/-- AE-measurability of the squared `nnnorm` of the kernel on the product space. -/
private theorem kernel_sq_aemeasurable
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) :
    AEMeasurable (fun p : X × X => (‖K p.1 p.2‖₊ : ℝ≥0∞) ^ 2) (μ.prod μ) :=
  (hK.aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2

/-- **T1 — the section/Tonelli identity.**  The iterated Lebesgue integral of the squared kernel
equals its integral over the product measure.  Pure Tonelli for the nonnegative measurable
function `‖K · ·‖₊²`. -/
theorem kernel_lintegral_section_eq
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) :
    ∫⁻ x, (∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ) ∂μ
      = ∫⁻ p : X × X, (‖K p.1 p.2‖₊ : ℝ≥0∞) ^ 2 ∂(μ.prod μ) :=
  (lintegral_prod _ (kernel_sq_aemeasurable hK)).symm

omit [SigmaFinite μ] in
/-- The `L²(X × X)`-norm-squared of the kernel is finite: `∫⁻ p, ‖K p.1 p.2‖₊² < ⊤`. -/
theorem kernel_lintegral_prod_ne_top
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) :
    ∫⁻ p : X × X, (‖K p.1 p.2‖₊ : ℝ≥0∞) ^ 2 ∂(μ.prod μ) ≠ ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := μ.prod μ)
    (f := fun p : X × X => K p.1 p.2) (p := 2) (by norm_num) (by norm_num) hK.eLpNorm_lt_top
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num] at h
  simp only [ENNReal.rpow_natCast, enorm_eq_nnnorm] at h
  exact h.ne

/-- **A.e. section is `L²`.**  From `K ∈ L²(X × X)`, for almost every `x` the section
`y ↦ K x y` belongs to `L²(μ)`.  This packages a.e. strong measurability of the sections
(`AEStronglyMeasurable.prodMk_left`) with a.e. finiteness of the inner integral (Tonelli + T1
+ `ae_lt_top'`). -/
theorem kernel_section_memLp
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y => K x y) 2 μ := by
  have hsm : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => K x y) μ :=
    hK.aestronglyMeasurable.prodMk_left
  have hfin : ∫⁻ x, (∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ) ∂μ ≠ ⊤ := by
    rw [kernel_lintegral_section_eq hK]; exact kernel_lintegral_prod_ne_top hK
  have haem : AEMeasurable (fun x => ∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ) μ :=
    (kernel_sq_aemeasurable hK).lintegral_prod_right'
  have hlt : ∀ᵐ x ∂μ, (∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤ := ae_lt_top' haem hfin
  filter_upwards [hsm, hlt] with x hx1 hx2
  refine ⟨hx1, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num),
    show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num]
  simp only [ENNReal.rpow_natCast, enorm_eq_nnnorm]
  exact hx2

/-! ### T2 — the bounded integral operator (Schur / Cauchy–Schwarz bound) -/

/-- `‖z‖ₑ ^ (2:ℝ) = (‖z‖₊ : ℝ≥0∞) ^ 2`: bridge between the real-power form used by `eLpNorm`
and the natural-power form used by the Tonelli identity T1. -/
private lemma enorm_rpow_two (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = (‖z‖₊ : ℝ≥0∞) ^ 2 := by
  rw [enorm_eq_nnnorm, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]

/-- For any complex function `g ∈ L²(ν)`, `∫⁻ (‖g·‖₊)² < ⊤`. -/
private lemma memLp_two_lintegral_sq_ne_top {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {g : Y → ℂ} (hg : MemLp g 2 ν) : ∫⁻ y, (‖g y‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := ν) (f := g) (p := 2)
    (by norm_num) (by norm_num) hg.eLpNorm_lt_top
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num] at h
  simp only [ENNReal.rpow_natCast, enorm_eq_nnnorm] at h
  exact h.ne

/-- The `L²` seminorm (exponent `2`) as the square-root of the `ℝ≥0∞`-integral of the squared
`nnnorm`. -/
private lemma eLpNorm_two_eq {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (g : Y → ℂ) :
    eLpNorm g 2 ν = (∫⁻ y, (‖g y‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_congr fun y => enorm_rpow_two (g y)]

/-- **Pointwise Schur/Cauchy–Schwarz bound.**  For a.e. `x`, the squared value of the integral
operator at `x` is bounded by the `L²`-mass of the section `K x ·` times the `L²`-mass of `f`.
Proved in `ℝ≥0∞` via `enorm_integral_le_lintegral_enorm` and Hölder's inequality
(`lintegral_mul_le_Lp_mul_Lq`, exponents `2, 2`). -/
private theorem integralOp_apply_enorm_sq_le_ae
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))
    {f : X → ℂ} (hf : MemLp f 2 μ) :
    ∀ᵐ x ∂μ, (‖∫ y, K x y * f y ∂μ‖₊ : ℝ≥0∞) ^ 2
      ≤ (∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ) * (∫⁻ y, (‖f y‖₊ : ℝ≥0∞) ^ 2 ∂μ) := by
  filter_upwards [kernel_section_memLp hK] with x hKx
  set Sx := ∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ with hSx
  set F := ∫⁻ y, (‖f y‖₊ : ℝ≥0∞) ^ 2 ∂μ with hF
  -- `‖∫ K·f‖ₑ ≤ ∫⁻ ‖K‖ₑ‖f‖ₑ`
  have h1 : (‖∫ y, K x y * f y ∂μ‖₊ : ℝ≥0∞) ≤ ∫⁻ y, ‖K x y‖ₑ * ‖f y‖ₑ ∂μ := by
    calc (‖∫ y, K x y * f y ∂μ‖₊ : ℝ≥0∞)
        = ‖∫ y, K x y * f y ∂μ‖ₑ := rfl
      _ ≤ ∫⁻ y, ‖K x y * f y‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ‖K x y‖ₑ * ‖f y‖ₑ ∂μ := by simp_rw [enorm_mul]
  -- Hölder
  have hKxm : AEMeasurable (fun y => ‖K x y‖ₑ) μ := hKx.aestronglyMeasurable.aemeasurable.enorm
  have hfm : AEMeasurable (fun y => ‖f y‖ₑ) μ := hf.aestronglyMeasurable.aemeasurable.enorm
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h2 : ∫⁻ y, ‖K x y‖ₑ * ‖f y‖ₑ ∂μ ≤ Sx ^ (1 / (2 : ℝ)) * F ^ (1 / (2 : ℝ)) := by
    have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hKxm hfm
    simp only [Pi.mul_apply] at hh
    rw [hSx, hF,
      show (∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ) = ∫⁻ y, ‖K x y‖ₑ ^ (2 : ℝ) ∂μ from
        lintegral_congr fun y => (enorm_rpow_two (K x y)).symm,
      show (∫⁻ y, (‖f y‖₊ : ℝ≥0∞) ^ 2 ∂μ) = ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ from
        lintegral_congr fun y => (enorm_rpow_two (f y)).symm]
    exact hh
  have h3 : (‖∫ y, K x y * f y ∂μ‖₊ : ℝ≥0∞) ≤ Sx ^ (1 / (2 : ℝ)) * F ^ (1 / (2 : ℝ)) := h1.trans h2
  calc (‖∫ y, K x y * f y ∂μ‖₊ : ℝ≥0∞) ^ 2
      = (‖∫ y, K x y * f y ∂μ‖₊ : ℝ≥0∞) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    _ ≤ (Sx ^ (1 / (2 : ℝ)) * F ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
    _ = Sx * F := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 from by norm_num, ENNReal.rpow_one,
          ENNReal.rpow_one]

/-- **The global `L²`-norm bound in `ℝ≥0∞` form.**  `∫⁻ ‖T_K f‖² ≤ ‖K‖²_{L²(X²)} · ‖f‖²_{L²}`. -/
theorem lintegral_integralOp_enorm_sq_le
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))
    {f : X → ℂ} (hf : MemLp f 2 μ) :
    ∫⁻ x, (‖∫ y, K x y * f y ∂μ‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ (∫⁻ p : X × X, (‖K p.1 p.2‖₊ : ℝ≥0∞) ^ 2 ∂(μ.prod μ))
        * (∫⁻ y, (‖f y‖₊ : ℝ≥0∞) ^ 2 ∂μ) := by
  set F := ∫⁻ y, (‖f y‖₊ : ℝ≥0∞) ^ 2 ∂μ with hF
  have haem : AEMeasurable (fun x => ∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ) μ :=
    (kernel_sq_aemeasurable hK).lintegral_prod_right'
  calc ∫⁻ x, (‖∫ y, K x y * f y ∂μ‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ ∫⁻ x, (∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ) * F ∂μ :=
        lintegral_mono_ae (integralOp_apply_enorm_sq_le_ae hK hf)
    _ = (∫⁻ x, (∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ) ∂μ) * F := lintegral_mul_const'' F haem
    _ = (∫⁻ p : X × X, (‖K p.1 p.2‖₊ : ℝ≥0∞) ^ 2 ∂(μ.prod μ)) * F := by
        rw [kernel_lintegral_section_eq hK]

/-- **T2 (membership).**  If `K ∈ L²(X × X)` and `f ∈ L²(μ)`, then `T_K f := ∫ K · y · f y`
belongs to `L²(μ)`. -/
theorem memLp_integralOp
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))
    {f : X → ℂ} (hf : MemLp f 2 μ) :
    MemLp (fun x => ∫ y, K x y * f y ∂μ) 2 μ := by
  refine ⟨?_, ?_⟩
  · have := (hK.aestronglyMeasurable.mul (hf.aestronglyMeasurable.comp_snd)).integral_prod_right'
    simpa using this
  · rw [eLpNorm_two_eq μ (fun x => ∫ y, K x y * f y ∂μ)]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (kernel_lintegral_prod_ne_top hK)
      (memLp_two_lintegral_sq_ne_top hf)) (lintegral_integralOp_enorm_sq_le hK hf)

/-- **T2 (Schur bound).**  The `L²`→`L²` operator norm of the integral operator is bounded by the
`L²(X × X)` norm of the kernel:
`‖T_K f‖₂ ≤ ‖K‖_{L²(X²)} · ‖f‖₂`. -/
theorem eLpNorm_integralOp_le
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))
    {f : X → ℂ} (hf : MemLp f 2 μ) :
    eLpNorm (fun x => ∫ y, K x y * f y ∂μ) 2 μ
      ≤ eLpNorm (fun p : X × X => K p.1 p.2) 2 (μ.prod μ) * eLpNorm f 2 μ := by
  rw [eLpNorm_two_eq μ (fun x => ∫ y, K x y * f y ∂μ), eLpNorm_two_eq (μ.prod μ) _,
    eLpNorm_two_eq μ f, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact ENNReal.rpow_le_rpow (lintegral_integralOp_enorm_sq_le hK hf) (by norm_num)

/-! ### T2 (packaged) — the bounded operator `T_K` on `L²(μ)` -/

/-- A.e. integrability of `y ↦ K x y · g y` when `g ∈ L²(μ)` (Hölder with exponents `2, 2`). -/
private theorem integralOp_integrable_ae
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))
    {g : X → ℂ} (hg : MemLp g 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => K x y * g y) μ := by
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  filter_upwards [kernel_section_memLp hK] with x hKx
  simpa only [Pi.mul_apply] using hKx.integrable_mul hg

/-- **T2 (operator).**  The integral operator `T_K : L²(μ) →L[ℂ] L²(μ)` induced by a kernel
`K ∈ L²(X × X)`, acting by `(T_K f) x = ∫ y, K x y · f y ∂μ`, continuous with
`‖T_K‖ ≤ ‖K‖_{L²(X²)}`.  Well-definedness on the `Lp` quotient is automatic: the Bochner integral
only sees the a.e.-class of its integrand, so a.e.-equal representatives give equal images. -/
noncomputable def integralOpCLM
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) :
    (X →₂[μ] ℂ) →L[ℂ] (X →₂[μ] ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_integralOp hK (Lp.memLp f)).toLp (fun x => ∫ y, K x y * f y ∂μ)
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [integralOp_integrable_ae hK (Lp.memLp f),
          integralOp_integrable_ae hK (Lp.memLp g)] with x hif hig
        simp only [Pi.add_apply]
        rw [← integral_add hif hig]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with y hy
        simp only [Pi.add_apply] at hy ⊢
        rw [hy]; ring
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        refine Filter.Eventually.of_forall fun x => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with y hy
        simp only [Pi.smul_apply, smul_eq_mul] at hy ⊢
        rw [hy]; ring }
    ((eLpNorm (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)).toReal)
    (fun f => by
      show ‖(memLp_integralOp hK (Lp.memLp f)).toLp (fun x => ∫ y, K x y * f y ∂μ)‖
        ≤ (eLpNorm (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)).toReal * ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono ?_ (eLpNorm_integralOp_le hK (Lp.memLp f))
      exact ENNReal.mul_ne_top hK.eLpNorm_ne_top (Lp.memLp f).eLpNorm_ne_top)

/-- The action of `T_K` unfolds a.e. to the integral operator on representatives. -/
theorem integralOpCLM_apply
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) (f : X →₂[μ] ℂ) :
    integralOpCLM hK f =ᵐ[μ] fun x => ∫ y, K x y * f y ∂μ :=
  MemLp.coeFn_toLp (memLp_integralOp hK (Lp.memLp f))

/-- **T2 (operator-norm bound).**  `‖T_K‖ ≤ ‖K‖_{L²(X²)}`. -/
theorem integralOpCLM_opNorm_le
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) :
    ‖integralOpCLM hK‖ ≤ (eLpNorm (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

end IntegralKernel

end QIQTH.TraceClass
