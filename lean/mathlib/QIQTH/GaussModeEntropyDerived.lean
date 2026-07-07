/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Gaussian per-mode entropy IS the Shannon entropy of a thermal occupation distribution

`QIQTH.GaussianStateEntropy.gaussModeEntropy ν = (ν+½)log(ν+½) − (ν−½)log(ν−½)` is the per-mode
entanglement-entropy building block summed by the (boundary-local) area law.  So far that formula was
*posited* as the single-mode Srednicki/Williamson entropy.  This file **grounds it in first principles**:
it proves `gaussModeEntropy (thermalNu q)` equals the honest Shannon / von Neumann entropy
`−∑ₖ pₖ log pₖ` of the thermal (geometric) occupation distribution `pₖ = (1−q) qᵏ` — the diagonal of a
single-mode thermal density matrix in the number basis.

Convention (reconciled with the `ν ≥ ½` floor of `gaussModeEntropy`): a geometric law with ratio `q`
(`0<q<1`) has mean occupation `n̄ = q/(1−q)`, and the symplectic eigenvalue is `ν = n̄ + ½ = (1+q)/(2(1−q))`.
With this `ν`,  `ν+½ = 1/(1−q) = n̄+1`  and  `ν−½ = q/(1−q) = n̄`, and the entropy formula reproduces
`−∑ₖ pₖ log pₖ` exactly.

This does **not** change the area-law scope: it grounds the *entropy formula* in the thermal distribution,
but the area-law *scaling* (`Σ over boundary modes ∝ A`) remains the explicit boundary-local model of
`BoundaryGaussianAreaLaw`, not the actual continuum vacuum.  Axiom-free.

`THE_STRONG_G_PLAN.md`, step SG1.
-/
import Mathlib
import QIQTH.GaussianStateEntropy

namespace QIQTH.GaussModeEntropyDerived

open QIQTH.GaussianStateEntropy

/-- The thermal (geometric) occupation probability of finding `k` quanta in a single-mode thermal state
    with Boltzmann ratio `q = e^{−ℏω/kT}`:  `pₖ = (1−q) qᵏ`. -/
noncomputable def thermalProb (q : ℝ) (k : ℕ) : ℝ := (1 - q) * q ^ k

/-- The mean occupation `n̄ = ∑ₖ k pₖ = q/(1−q)` of the thermal distribution. -/
noncomputable def meanOcc (q : ℝ) : ℝ := q / (1 - q)

/-- The symplectic eigenvalue of the thermal mode: `ν = n̄ + ½ = (1+q)/(2(1−q))`. -/
noncomputable def thermalNu (q : ℝ) : ℝ := (1 + q) / (2 * (1 - q))

/-- `thermalNu q = meanOcc q + 1/2` — the eigenvalue is the mean occupation shifted by the pure floor. -/
theorem thermalNu_eq_meanOcc_add_half (q : ℝ) (hq1 : q < 1) :
    thermalNu q = meanOcc q + 1 / 2 := by
  have hne : (1 - q) ≠ 0 := (by linarith : (0:ℝ) < 1 - q).ne'
  unfold thermalNu meanOcc
  field_simp
  ring

/-- **The capstone.**  The Gaussian per-mode entropy at the thermal symplectic eigenvalue `ν = thermalNu q`
    IS the Shannon / von Neumann entropy `−∑ₖ pₖ log pₖ` of the thermal geometric occupation law
    `pₖ = (1−q) qᵏ`.  This grounds `gaussModeEntropy` in first principles: it is not a posited formula but
    literally the entropy of the thermal number-basis distribution. -/
theorem gaussModeEntropy_eq_thermal_shannon (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (- ∑' k : ℕ, thermalProb q k * Real.log (thermalProb q k)) = gaussModeEntropy (thermalNu q) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hne : (1 - q) ≠ 0 := h1q.ne'
  have hqnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  -- Summability of the base distribution and of `k · pₖ`.
  have hThermalSummable : Summable (thermalProb q) := by
    unfold thermalProb
    exact (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  have hkThermalSummable : Summable (fun k : ℕ => (k : ℝ) * thermalProb q k) := by
    have h := (hasSum_coe_mul_geometric_of_norm_lt_one hqnorm).summable
    have hrw : (fun k : ℕ => (k : ℝ) * thermalProb q k) = fun k : ℕ => (1 - q) * ((k : ℝ) * q ^ k) := by
      funext k; unfold thermalProb; ring
    rw [hrw]; exact h.mul_left _
  -- (1) Normalization:  ∑ₖ pₖ = 1.
  have hNorm : ∑' k : ℕ, thermalProb q k = 1 := by
    unfold thermalProb
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1, mul_inv_cancel₀ hne]
  -- (2) Mean:  ∑ₖ k pₖ = q/(1−q).
  have hMean : ∑' k : ℕ, (k : ℝ) * thermalProb q k = q / (1 - q) := by
    have hcongr : ∀ k : ℕ, (k : ℝ) * thermalProb q k = (1 - q) * ((k : ℝ) * q ^ k) := by
      intro k; unfold thermalProb; ring
    rw [tsum_congr hcongr, tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hqnorm]
    field_simp
  -- (3) Split log pₖ = log(1−q) + k log q, giving the summand a two-term shape.
  have hlog : ∀ k : ℕ, Real.log (thermalProb q k) = Real.log (1 - q) + (k : ℝ) * Real.log q := by
    intro k
    unfold thermalProb
    rw [Real.log_mul hne (pow_ne_zero k hq0.ne'), Real.log_pow]
  have hsummand : ∀ k : ℕ, thermalProb q k * Real.log (thermalProb q k)
      = thermalProb q k * Real.log (1 - q) + ((k : ℝ) * thermalProb q k) * Real.log q := by
    intro k; rw [hlog k]; ring
  have hSa : Summable (fun k : ℕ => thermalProb q k * Real.log (1 - q)) :=
    hThermalSummable.mul_right _
  have hSb : Summable (fun k : ℕ => ((k : ℝ) * thermalProb q k) * Real.log q) :=
    hkThermalSummable.mul_right _
  have hsplit : ∑' k : ℕ, thermalProb q k * Real.log (thermalProb q k)
      = Real.log (1 - q) + (q / (1 - q)) * Real.log q := by
    rw [tsum_congr hsummand, hSa.tsum_add hSb, tsum_mul_right, tsum_mul_right, hNorm, hMean]
    ring
  -- (4) Reconcile with the closed-form gaussModeEntropy at ν = thermalNu q.
  have hp : thermalNu q + 1 / 2 = 1 / (1 - q) := by unfold thermalNu; field_simp; ring
  have hm : thermalNu q - 1 / 2 = q / (1 - q) := by unfold thermalNu; field_simp; ring
  have hlog1 : Real.log (1 / (1 - q)) = - Real.log (1 - q) := by rw [one_div, Real.log_inv]
  have hlog2 : Real.log (q / (1 - q)) = Real.log q - Real.log (1 - q) :=
    Real.log_div hq0.ne' hne
  have hRecon : gaussModeEntropy (thermalNu q)
      = - Real.log (1 - q) - (q / (1 - q)) * Real.log q := by
    unfold gaussModeEntropy
    rw [hp, hm, hlog1, hlog2]
    field_simp
    ring
  rw [hsplit, hRecon]; ring

/-- **Corollary: the thermal per-mode entropy is nonnegative** — it is the Shannon entropy of a genuine
    probability distribution (`0 < pₖ ≤ 1 ⟹ log pₖ ≤ 0 ⟹ pₖ log pₖ ≤ 0`), so its negation is `≥ 0`.
    Independent re-derivation of `gaussModeEntropy_nonneg` from the distribution itself. -/
theorem gaussModeEntropy_thermal_nonneg (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ gaussModeEntropy (thermalNu q) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  rw [← gaussModeEntropy_eq_thermal_shannon q hq0 hq1, neg_nonneg]
  apply tsum_nonpos
  intro k
  have hpos : 0 < thermalProb q k := by
    unfold thermalProb; positivity
  have hle1 : thermalProb q k ≤ 1 := by
    unfold thermalProb
    calc (1 - q) * q ^ k ≤ (1 - q) * 1 := by
          apply mul_le_mul_of_nonneg_left _ h1q.le
          exact pow_le_one₀ hq0.le hq1.le
      _ = 1 - q := by ring
      _ ≤ 1 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos hpos.le (Real.log_nonpos hpos.le hle1)

end QIQTH.GaussModeEntropyDerived
