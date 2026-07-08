/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Weighted-`L²` isometry — the √ω "unbounded multiplier" is bounded on the right domain

The KG positive-frequency map `(φ,π) ↦ √ω·φ̂ + i·ω^{-1/2}·π̂` has an **unbounded** multiplier `√ω`
on plain `L²(dk)`.  This file supplies the structural resolution: multiplication by a weight `w ≥ 0`
is a **norm-preserving (isometric) map**

    `L²(volume.withDensity w²)  →  L²(volume)` ,   `f ↦ w · f` ,

so `√ω` is *not* unbounded once the domain is the correctly-weighted space (a weighted KG-Sobolev
space).  This is the first genuine brick past the naive-`L²` wall: it turns the multiplier into a
bounded isometry between the correct Hilbert spaces.

## What is proved (axiom-free)

* `lintegral_enorm_rpow_smul_weight` — the `L²` weight identity at the `lintegral` level:
  `∫⁻ ‖w·f‖ₑ² dvol = ∫⁻ ‖f‖ₑ² d(vol.withDensity w²)`  (both `= ∫⁻ w²·‖f‖ₑ² dvol`).
* `eLpNorm_smul_weight_eq_withDensity` — the `eLpNorm` (L²-seminorm) form: multiplication by `w`
  carries the `w²`-weighted `L²` seminorm to the flat one, `eLpNorm (w·f) 2 vol = eLpNorm f 2 (w²-weighted)`.

Measurability of `w` and `f` is carried as HYPOTHESES (the physical `w = √ω` is continuous, `f` a
one-particle wavefunction), never axioms.

## Scope firewall (HONEST)

This is the weight-isometry brick — the correct Hilbert-space setting for the `√ω` multiplier.  It is
NOT the full positive-frequency map `j_ℏ` (which still needs the Fourier `L²→L²` step, the
real-Cauchy-data → complex domain, and boost covariance); NOT numerical-`G`; NOT QG.  It removes the
"`√ω` is unbounded" objection by moving to the weighted domain, one honest brick toward `j_ℏ`.
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace QIQTH.WeightedL2

open MeasureTheory
open scoped ENNReal

/-- **Pointwise weight identity.**  For `w k ≥ 0`, `‖w k • f k‖ₑ² = ofReal(w k²) · ‖f k‖ₑ²`
(real exponent `2`).  The `enorm_smul` factorization plus `‖w k‖ₑ = ofReal (w k)` for `w k ≥ 0`. -/
theorem enorm_rpow_smul_weight (w : ℝ → ℝ) (hw : ∀ k, 0 ≤ w k) (f : ℝ → ℂ) (k : ℝ) :
    ‖w k • f k‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (w k ^ 2) * ‖f k‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, ENNReal.rpow_two, enorm_smul, Real.enorm_of_nonneg (hw k), mul_pow]
  congr 1
  rw [← ENNReal.ofReal_pow (hw k)]

/-- **The `L²` weight identity at the `lintegral` level.**  For `w ≥ 0` measurable and `f`
measurable, `∫⁻ ‖w·f‖ₑ² dvol = ∫⁻ ‖f‖ₑ² d(vol.withDensity w²)`.  This is the substance of the
weight isometry: the `w²` in the measure exactly matches multiplication by `w` on the function. -/
theorem lintegral_enorm_rpow_smul_weight
    (w : ℝ → ℝ) (hw : ∀ k, 0 ≤ w k) (hwm : Measurable w) (f : ℝ → ℂ) (hfm : Measurable f) :
    (∫⁻ k, ‖w k • f k‖ₑ ^ (2 : ℝ) ∂volume)
      = ∫⁻ k, ‖f k‖ₑ ^ (2 : ℝ)
          ∂(volume.withDensity (fun k => ENNReal.ofReal (w k ^ 2))) := by
  have hdens : Measurable (fun k => ENNReal.ofReal (w k ^ 2)) := by fun_prop
  have hg : Measurable (fun k => ‖f k‖ₑ ^ (2 : ℝ)) := by fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens hg]
  refine lintegral_congr (fun k => ?_)
  rw [enorm_rpow_smul_weight w hw f k]
  rfl

/-- **The weighted-`L²` isometry (seminorm form).**  Multiplication by `w ≥ 0` carries the
`w²`-weighted `L²` seminorm to the flat `L²` seminorm:
`eLpNorm (fun k => w k • f k) 2 volume = eLpNorm f 2 (volume.withDensity w²)`.
So `f ↦ w·f` is norm-preserving from `L²(w²·vol)` to `L²(vol)` — the `√ω` multiplier is an isometry,
not unbounded, on the correctly-weighted domain. -/
theorem eLpNorm_smul_weight_eq_withDensity
    (w : ℝ → ℝ) (hw : ∀ k, 0 ≤ w k) (hwm : Measurable w) (f : ℝ → ℂ) (hfm : Measurable f) :
    eLpNorm (fun k => w k • f k) 2 volume
      = eLpNorm f 2 (volume.withDensity (fun k => ENNReal.ofReal (w k ^ 2))) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
    eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
    eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  congr 1
  rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by simp]
  exact lintegral_enorm_rpow_smul_weight w hw hwm f hfm

/-- **The `MemLp` transfer — the usable form of the weight isometry.**  A function `f` lies in the
`w²`-weighted `L²` iff its `w`-scaling `w·f` lies in the flat `L²`:
`MemLp f 2 (vol.withDensity w²) ↔ MemLp (w·f) 2 vol`.  This is what lets one actually move a
one-particle wavefunction between the weighted KG-Sobolev space and the flat rapidity `L²` — the
membership-level content of the `√ω` isometry (`eLpNorm_smul_weight_eq_withDensity`).  Both `eLpNorm`s
are literally equal, so the finiteness transfers both ways; measurability supplies the
`AEStronglyMeasurable` halves. -/
theorem memLp_two_weight_smul_iff
    (w : ℝ → ℝ) (hw : ∀ k, 0 ≤ w k) (hwm : Measurable w) (f : ℝ → ℂ) (hfm : Measurable f) :
    MemLp f 2 (volume.withDensity (fun k => ENNReal.ofReal (w k ^ 2)))
      ↔ MemLp (fun k => w k • f k) 2 volume := by
  have hnorm := eLpNorm_smul_weight_eq_withDensity w hw hwm f hfm
  constructor
  · intro hf
    refine ⟨(hwm.smul hfm).aestronglyMeasurable, ?_⟩
    rw [hnorm]; exact hf.eLpNorm_lt_top
  · intro hf
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [← hnorm]; exact hf.eLpNorm_lt_top

end QIQTH.WeightedL2
