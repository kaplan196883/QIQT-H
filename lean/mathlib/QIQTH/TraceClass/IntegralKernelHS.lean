/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.TraceClass.IntegralKernel

/-!
# Integral operators with an `L²` kernel are Hilbert–Schmidt (hence compact)

This file *completes* the integral-operator bridge started in `IntegralKernel.lean`: the bounded
operator `T_K` on `L²(X, μ)` induced by a kernel `K ∈ L²(X × X)` is **Hilbert–Schmidt** with
`∑ᵢ ‖T_K bᵢ‖²_{L²(μ)} = ‖K‖²_{L²(X × X)}`, and therefore **compact**.  The proof is the standard
one: for a Hilbert basis `b` of `L²(μ)` and a fixed `x`, the coefficients `⟪T_K bᵢ⟫(x)` are exactly
the Fourier coefficients of the conjugate section `y ↦ conj (K x y)`, so **per-`x` Bessel/Parseval**
gives `∑ᵢ ‖(T_K bᵢ) x‖² ≤ ‖K x ·‖²_{L²(μ)}`; integrating over `x` (Tonelli, via the
`kernel_lintegral_section_eq` identity) bounds every finite partial sum by `‖K‖²_{L²(X × X)} < ∞`,
which yields summability.

## Main results

* `isHilbertSchmidt_integralOpCLM` : `T_K` is Hilbert–Schmidt.
* `integralOpCLM_isCompactOperator` : `T_K` is a compact operator.

## Honest firewall

This is the McKean–Singer **geometric-side bridge** infrastructure: it upgrades the `L²`-kernel
integral operator from *bounded* to *Hilbert–Schmidt / compact*.  It does **not** build the
manifold heat kernel, and it does **not** discharge the general `a₁ = R/6` coefficient (which is
irreducibly behind the manifold heat-kernel parametrix / curvature — layers L0/L1/L4).  NOT the
conjecture, NOT QG.  No axioms, no `sorry`.
-/

open scoped ENNReal NNReal ComplexInnerProductSpace
open MeasureTheory

namespace QIQTH.TraceClass

section IntegralKernelHS

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
variable {K : X → X → ℂ}

/-- `‖z‖ₑ ^ (2:ℝ) = (‖z‖₊ : ℝ≥0∞) ^ 2`: bridge between the real-power form used by `eLpNorm`
and the natural-power form used throughout. -/
private lemma enorm_rpow_two (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = (‖z‖₊ : ℝ≥0∞) ^ 2 := by
  rw [enorm_eq_nnnorm, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]

/-- `(a ^ (1/2))² = a` in `ℝ≥0∞` (isolated so the rewrite of `^2 → ^(2:ℝ)` cannot touch the
integrand). -/
private lemma ennreal_rpow_half_sq (a : ℝ≥0∞) : (a ^ (1 / (2 : ℝ))) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast (a ^ (1 / (2 : ℝ))) 2, ← ENNReal.rpow_mul,
    show (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 from by norm_num, ENNReal.rpow_one]

/-- The squared `L²` seminorm of a complex function as the `ℝ≥0∞`-integral of the squared
`nnnorm`: `(eLpNorm h 2 ν)² = ∫⁻ y, ‖h y‖₊²`. -/
private lemma eLpNorm_two_sq {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} (h : Y → ℂ) :
    eLpNorm h 2 ν ^ 2 = ∫⁻ y, (‖h y‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_congr fun y => enorm_rpow_two (h y)]
  exact ennreal_rpow_half_sq _

/-- **Per-`x` Bessel/Parseval bound.**  For almost every `x`, the finite partial sum of the squared
Fourier coefficients of the integral operator at `x` (relative to a Hilbert basis `b` of `L²(μ)`) is
bounded by the `L²`-mass of the section `K x ·`.  The coefficients `∫ y, K x y · bᵢ y` are the inner
products `⟪conj(K x ·), bᵢ⟫`, so this is exactly Bessel's inequality for `conj(K x ·) ∈ L²(μ)`. -/
private theorem finset_sum_integralOp_enorm_sq_le_ae
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ))
    {w : Type*} (b : HilbertBasis w ℂ (X →₂[μ] ℂ)) (s : Finset w) :
    ∀ᵐ x ∂μ, ∑ i ∈ s, (‖∫ y, K x y * (b i) y ∂μ‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  filter_upwards [kernel_section_memLp hK] with x hKx
  -- The conjugate section `g = conj (K x ·)`, its `L²` class `G`.
  set g : X → ℂ := star (fun y => K x y) with hgdef
  have hg : MemLp g 2 μ := hKx.star
  set G : X →₂[μ] ℂ := hg.toLp g with hGdef
  have hcoe : ⇑G =ᵐ[μ] g := hg.coeFn_toLp
  -- The Fourier coefficient identity: `∫ y, K x y · bᵢ y = ⟪G, bᵢ⟫`.
  have hid : ∀ i, (inner ℂ G (b i) : ℂ) = ∫ y, K x y * (b i) y ∂μ := by
    intro i
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with y hy
    rw [RCLike.inner_apply, hy]
    simp only [hgdef, Pi.star_apply, starRingEnd_apply, star_star]
    ring
  -- `‖G‖² = ‖K x ·‖²_{L²(μ)}`.
  have hGnorm : (‖G‖₊ : ℝ≥0∞) ^ 2 = ∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
    have hcoeE : (‖G‖₊ : ℝ≥0∞) = eLpNorm G 2 μ := by
      rw [Lp.nnnorm_def, ENNReal.coe_toNNReal (Lp.eLpNorm_ne_top G)]
    rw [hcoeE, eLpNorm_congr_ae hcoe, eLpNorm_two_sq]
    refine lintegral_congr fun y => ?_
    congr 1
    simp only [hgdef, Pi.star_apply, nnnorm_star]
  calc ∑ i ∈ s, (‖∫ y, K x y * (b i) y ∂μ‖₊ : ℝ≥0∞) ^ 2
      = ∑ i ∈ s, (‖(inner ℂ (b i) G : ℂ)‖₊ : ℝ≥0∞) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hs : (‖(inner ℂ G (b i) : ℂ)‖₊ : ℝ≥0∞) = (‖(inner ℂ (b i) G : ℂ)‖₊ : ℝ≥0∞) := by
          rw [ENNReal.coe_inj, ← NNReal.coe_inj]
          simpa using norm_inner_symm (𝕜 := ℂ) G (b i)
        rw [← hid i, hs]
    _ ≤ ∑' i, (‖(inner ℂ (b i) G : ℂ)‖₊ : ℝ≥0∞) ^ 2 := ENNReal.sum_le_tsum s
    _ = (‖G‖₊ : ℝ≥0∞) ^ 2 := (parsevalE b G).symm
    _ = ∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ := hGnorm

/-- **The integral operator of an `L²` kernel is Hilbert–Schmidt.**  For any Hilbert basis `b`,
`∑ᵢ ‖T_K bᵢ‖²_{L²(μ)}` is summable, because each finite partial sum is bounded by
`‖K‖²_{L²(X × X)} < ∞` (per-`x` Bessel + Tonelli via `kernel_lintegral_section_eq`). -/
theorem isHilbertSchmidt_integralOpCLM
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) :
    IsHilbertSchmidt (integralOpCLM hK) := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ (X →₂[μ] ℂ)
  rw [isHilbertSchmidt_iff_summable b]
  refine summable_of_sum_le
    (c := (∫⁻ p : X × X, (‖K p.1 p.2‖₊ : ℝ≥0∞) ^ 2 ∂(μ.prod μ)).toReal)
    (fun i => sq_nonneg _) (fun s => ?_)
  -- Measurability of each `x ↦ ‖(T_K bᵢ) x‖₊²`.
  have hmeas : ∀ i : w, AEMeasurable
      (fun x => (‖(integralOpCLM hK (b i)) x‖₊ : ℝ≥0∞) ^ 2) μ := fun i =>
    ((Lp.aestronglyMeasurable (integralOpCLM hK (b i))).aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  -- Reduce the real partial sum to a `toReal` of an `ℝ≥0∞` integral sum.
  have hne : ∀ i ∈ s, (∫⁻ x, (‖(integralOpCLM hK (b i)) x‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≠ ⊤ := by
    intro i _
    rw [← eLpNorm_two_sq]
    exact ENNReal.pow_ne_top (Lp.eLpNorm_ne_top _)
  have key : ∑ i ∈ s, ‖integralOpCLM hK (b i)‖ ^ 2
      = (∑ i ∈ s, ∫⁻ x, (‖(integralOpCLM hK (b i)) x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal := by
    rw [ENNReal.toReal_sum hne]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Lp.norm_def, ← ENNReal.toReal_pow, eLpNorm_two_sq]
  rw [key]
  refine ENNReal.toReal_mono (kernel_lintegral_prod_ne_top hK) ?_
  -- The a.e. identity `(T_K bᵢ) x = ∫ y, K x y · bᵢ y`, uniformly over the finite index set.
  have haeeq : ∀ᵐ x ∂μ, ∀ i ∈ s,
      (integralOpCLM hK (b i)) x = ∫ y, K x y * (b i) y ∂μ := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => integralOpCLM_apply hK (b i)
  have hcombined : ∀ᵐ x ∂μ, ∑ i ∈ s, (‖(integralOpCLM hK (b i)) x‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
    filter_upwards [haeeq, finset_sum_integralOp_enorm_sq_le_ae hK b s] with x hx hbx
    calc ∑ i ∈ s, (‖(integralOpCLM hK (b i)) x‖₊ : ℝ≥0∞) ^ 2
        = ∑ i ∈ s, (‖∫ y, K x y * (b i) y ∂μ‖₊ : ℝ≥0∞) ^ 2 :=
          Finset.sum_congr rfl fun i hi => by rw [hx i hi]
      _ ≤ ∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ := hbx
  calc ∑ i ∈ s, ∫⁻ x, (‖(integralOpCLM hK (b i)) x‖₊ : ℝ≥0∞) ^ 2 ∂μ
      = ∫⁻ x, ∑ i ∈ s, (‖(integralOpCLM hK (b i)) x‖₊ : ℝ≥0∞) ^ 2 ∂μ :=
        (lintegral_finsetSum' s fun i _ => hmeas i).symm
    _ ≤ ∫⁻ x, (∫⁻ y, (‖K x y‖₊ : ℝ≥0∞) ^ 2 ∂μ) ∂μ := lintegral_mono_ae hcombined
    _ = ∫⁻ p : X × X, (‖K p.1 p.2‖₊ : ℝ≥0∞) ^ 2 ∂(μ.prod μ) := kernel_lintegral_section_eq hK

/-- **The integral operator of an `L²` kernel is compact.**  Immediate from
`isHilbertSchmidt_integralOpCLM` and `IsHilbertSchmidt.isCompactOperator`. -/
theorem integralOpCLM_isCompactOperator
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) :
    IsCompactOperator (integralOpCLM hK) :=
  (isHilbertSchmidt_integralOpCLM hK).isCompactOperator

end IntegralKernelHS

end QIQTH.TraceClass
