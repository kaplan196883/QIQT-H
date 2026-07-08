/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The positive-frequency map is well-defined on the KG-Sobolev domain `H^{1/2} ⊕ H^{-1/2}`

This is the **payoff** of the weighted-`L²` detour (`WeightedL2.lean`).  The KG one-particle
positive-frequency coefficient

    a(Ψ,π) k  =  (ω k · Ψ k + i · π k) / √(2ℏ · ω k) ,    ω k = √(k²+m²) > 0 ,

involves the `√ω` multiplier that is **unbounded on plain `L²`**.  Rewriting

    a  =  (2ℏ)^{-1/2} · (√ω · Ψ)  +  i (2ℏ)^{-1/2} · (ω^{-1/2} · π) ,

each term is `weight · (field)`, so by the weight isometry `memLp_two_weight_smul_iff` the map lands
in flat `L²(volume)` **exactly when** the Cauchy data lie in the correctly-weighted Sobolev spaces:

    Ψ ∈ L²(ω-weighted) = H^{1/2}    and    π ∈ L²(ω^{-1}-weighted) = H^{-1/2} .

So the positive-frequency map `(Ψ,π) ↦ a` is a well-defined map `H^{1/2} ⊕ H^{-1/2} → L²(volume)`.
This is the correct operator domain that the naive-`L²` "unbounded `√ω`" objection was missing.

## What is proved (axiom-free)

* `kg_posFreq_memLp_split` — the split-form coefficient (the two weighted pieces, scaled and added)
  lies in flat `L²`, given the two weighted-Sobolev memberships.  Uses the weight isometry twice
  (`w₁ = √ω`, `w₂ = ω^{-1/2}`), `MemLp.const_smul`, `MemLp.add`.
* `kg_coeff_eq_split` — the pointwise identity `(ω ψ + iπ)/√(2ℏω) = (2ℏ)^{-1/2}(√ω ψ) + i(2ℏ)^{-1/2}(ω^{-1/2}π)`
  (for `ℏ, ω > 0`).
* `kg_posFreq_memLp` — the quotient-form conclusion: `a(Ψ,π) ∈ L²(volume)` on the `H^{1/2}⊕H^{-1/2}`
  domain, i.e. the positive-frequency map is well-defined into `L²`.

## Scope firewall (HONEST)

This identifies the correct domain and shows the positive-frequency map lands in `L²` — the operator
is WELL-DEFINED on `H^{1/2}⊕H^{-1/2}`.  It is NOT the full `j_ℏ` (the Fourier `L²→L²` step exists in
Mathlib as `MeasureTheory.Lp.fourierTransformₗᵢ`; the boost covariance and the completed one-particle
map remain).  `ω > 0` (i.e. `m > 0`), measurability of `Ψ, π`, and the weighted memberships are
carried as HYPOTHESES.  NOT numerical-`G`; NOT QG.
-/
import QIQTH.WeightedL2
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace QIQTH.PosFreqDomain

open MeasureTheory
open QIQTH.WeightedL2
open scoped ENNReal

/-- **The positive-frequency coefficient lands in flat `L²` (split form).**  With `ω ≥ 0` and the two
weighted-Sobolev memberships `Ψ ∈ L²(ω-weighted)`, `π ∈ L²(ω^{-1}-weighted)`, the scaled sum of the
weighted pieces `(2ℏ)^{-1/2}(√ω·Ψ) + i(2ℏ)^{-1/2}(ω^{-1/2}·π)` lies in `L²(volume)`. -/
theorem kg_posFreq_memLp_split
    (ℏ : ℝ) (ω : ℝ → ℝ) (Ψ π : ℝ → ℂ)
    (hω0 : ∀ k, 0 ≤ ω k) (hωm : Measurable ω) (hΨm : Measurable Ψ) (hπm : Measurable π)
    (hΨ : MemLp Ψ 2 (volume.withDensity (fun k => ENNReal.ofReal (ω k))))
    (hπ : MemLp π 2 (volume.withDensity (fun k => ENNReal.ofReal ((ω k)⁻¹)))) :
    MemLp (fun k =>
        (1 / (Real.sqrt (2 * ℏ) : ℂ)) • ((Real.sqrt (ω k) : ℝ) • Ψ k)
        + (Complex.I / (Real.sqrt (2 * ℏ) : ℂ)) • (((Real.sqrt (ω k))⁻¹ : ℝ) • π k))
      2 volume := by
  set w1 : ℝ → ℝ := fun k => Real.sqrt (ω k) with hw1def
  set w2 : ℝ → ℝ := fun k => (Real.sqrt (ω k))⁻¹ with hw2def
  have hw1_nonneg : ∀ k, 0 ≤ w1 k := fun k => Real.sqrt_nonneg _
  have hw2_nonneg : ∀ k, 0 ≤ w2 k := fun k => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hw1m : Measurable w1 := Real.continuous_sqrt.measurable.comp hωm
  have hw2m : Measurable w2 := (Real.continuous_sqrt.measurable.comp hωm).inv
  -- transfer Ψ: √ω · Ψ ∈ flat L² (w₁² = ω)
  have hΨ_flat : MemLp (fun k => w1 k • Ψ k) 2 volume := by
    refine (memLp_two_weight_smul_iff w1 hw1_nonneg hw1m Ψ hΨm).1 ?_
    have hsq : (fun k => ENNReal.ofReal (w1 k ^ 2)) = (fun k => ENNReal.ofReal (ω k)) := by
      funext k; rw [hw1def]; rw [Real.sq_sqrt (hω0 k)]
    rw [hsq]; exact hΨ
  -- transfer π: ω^{-1/2} · π ∈ flat L² (w₂² = ω⁻¹)
  have hπ_flat : MemLp (fun k => w2 k • π k) 2 volume := by
    refine (memLp_two_weight_smul_iff w2 hw2_nonneg hw2m π hπm).1 ?_
    have hsq : (fun k => ENNReal.ofReal (w2 k ^ 2)) = (fun k => ENNReal.ofReal ((ω k)⁻¹)) := by
      funext k; rw [hw2def]; rw [inv_pow, Real.sq_sqrt (hω0 k)]
    rw [hsq]; exact hπ
  -- scale each by its complex constant, then add
  have hΨ_term : MemLp (fun k => (1 / (Real.sqrt (2 * ℏ) : ℂ)) • (w1 k • Ψ k)) 2 volume := by
    simpa [Pi.smul_apply] using MemLp.const_smul hΨ_flat (1 / (Real.sqrt (2 * ℏ) : ℂ))
  have hπ_term : MemLp
      (fun k => (Complex.I / (Real.sqrt (2 * ℏ) : ℂ)) • (w2 k • π k)) 2 volume := by
    simpa [Pi.smul_apply] using MemLp.const_smul hπ_flat (Complex.I / (Real.sqrt (2 * ℏ) : ℂ))
  simpa [hw1def, hw2def, Pi.add_apply] using MemLp.add hΨ_term hπ_term

/-- **The coefficient split identity.**  For `ℏ, Ω > 0`, the KG positive-frequency coefficient factors
as `(Ω ψ + iπ)/√(2ℏΩ) = (2ℏ)^{-1/2}(√Ω · ψ) + i(2ℏ)^{-1/2}(Ω^{-1/2} · π)`.  (`√(2ℏΩ)=√(2ℏ)√Ω`,
`Ω=√Ω·√Ω`.) -/
theorem kg_coeff_eq_split {ℏ Ω : ℝ} (hℏ : 0 < ℏ) (hΩ : 0 < Ω) (ψ π : ℂ) :
    ((Ω : ℂ) * ψ + Complex.I * π) / (Real.sqrt (2 * ℏ * Ω) : ℂ)
      = (1 / (Real.sqrt (2 * ℏ) : ℂ)) • ((Real.sqrt Ω : ℝ) • ψ)
        + (Complex.I / (Real.sqrt (2 * ℏ) : ℂ)) • (((Real.sqrt Ω)⁻¹ : ℝ) • π) := by
  have hA : 0 < 2 * ℏ := mul_pos (by norm_num) hℏ
  have hsqrtA_ne : (Real.sqrt (2 * ℏ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hA))
  have hsqrtΩ_ne : (Real.sqrt Ω : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hΩ))
  have hsqrt_mul : Real.sqrt (2 * ℏ * Ω) = Real.sqrt (2 * ℏ) * Real.sqrt Ω := by
    rw [Real.sqrt_mul hA.le]
  have hΩ_sqrt : (Ω : ℂ) = (Real.sqrt Ω : ℂ) * (Real.sqrt Ω : ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt hΩ.le]
  rw [hsqrt_mul, hΩ_sqrt]
  simp only [Complex.ofReal_mul, Complex.real_smul, Complex.ofReal_inv, smul_eq_mul]
  field_simp

/-- **The positive-frequency map is well-defined `H^{1/2}⊕H^{-1/2} → L²(volume)`.**  For `ω > 0`
(i.e. `m > 0`) and Cauchy data in the weighted-Sobolev domain, the quotient-form coefficient
`a(Ψ,π) k = (ω k·Ψ k + i·π k)/√(2ℏ·ω k)` lies in flat `L²`.  This is the correct operator domain the
naive-`L²` "unbounded `√ω`" objection was missing. -/
theorem kg_posFreq_memLp
    (ℏ : ℝ) (hℏ : 0 < ℏ) (ω : ℝ → ℝ) (Ψ π : ℝ → ℂ)
    (hωpos : ∀ k, 0 < ω k) (hωm : Measurable ω) (hΨm : Measurable Ψ) (hπm : Measurable π)
    (hΨ : MemLp Ψ 2 (volume.withDensity (fun k => ENNReal.ofReal (ω k))))
    (hπ : MemLp π 2 (volume.withDensity (fun k => ENNReal.ofReal ((ω k)⁻¹)))) :
    MemLp (fun k => ((ω k : ℂ) * Ψ k + Complex.I * π k) / (Real.sqrt (2 * ℏ * ω k) : ℂ))
      2 volume := by
  have hsplit := kg_posFreq_memLp_split ℏ ω Ψ π (fun k => (hωpos k).le) hωm hΨm hπm hΨ hπ
  have hae : (fun k =>
      (1 / (Real.sqrt (2 * ℏ) : ℂ)) • ((Real.sqrt (ω k) : ℝ) • Ψ k)
      + (Complex.I / (Real.sqrt (2 * ℏ) : ℂ)) • (((Real.sqrt (ω k))⁻¹ : ℝ) • π k))
      =ᵐ[volume]
      fun k => ((ω k : ℂ) * Ψ k + Complex.I * π k) / (Real.sqrt (2 * ℏ * ω k) : ℂ) :=
    Filter.Eventually.of_forall (fun k => (kg_coeff_eq_split hℏ (hωpos k) (Ψ k) (π k)).symm)
  exact MemLp.ae_eq hae hsplit

end QIQTH.PosFreqDomain
