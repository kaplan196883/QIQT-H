/-
  THE DECOUPLING SHADOW DS3 (THE_DECOUPLING_SHADOW_PLAN.md) — entropy regimes + THE GUARD.

  The truncated thermal entropy `S_D(x) = log Z_D + x·⟨N⟩_D` in its two honest regimes:
  • FIXED `x = βω > 0`, `D → ∞`: `S_D(x) → −log(1−e^{−x}) + x·e^{−x}/(1−e^{−x})` — the free
    (Planck) oscillator entropy;
  • FIXED `D`, `x → 0⁺`: `S_D(x) → log D` — capacity saturation;
  • **THE REGIME-SEPARATION GUARD** (the load-bearing honesty theorem, per the binding verdict):
    along ANY schedule with `x_D·D → 0`, capacity saturates (`S_D(x_D) − log D → 0`) **BUT** the
    truncation-defect expectation tends to **1**, not 0 — exact saturated capacity is NOT
    simultaneously the positive-temperature free-oscillator limit. The two halves of the
    decoupling shadow live in DIFFERENT regimes, and this file proves it.
-/
import Mathlib
import QIQTH.Decoupling.GibbsSingleMode

namespace QIQTH.Decoupling

open Filter

/-- **The truncated thermal entropy** `S_D(x) = log Z_D(e^{−x}) + x·⟨N⟩_D(e^{−x})` (the
    thermodynamic form; `x = βω`). -/
noncomputable def thermalEntropy (D : ℕ) (x : ℝ) : ℝ :=
  Real.log (Zgeom D (Real.exp (-x))) + x * meanN D (Real.exp (-x))

/-! ### Elementary bounds on the truncated partition data -/

theorem one_le_Zgeom {D : ℕ} (hD : 1 ≤ D) {q : ℝ} (h0 : 0 ≤ q) : 1 ≤ Zgeom D q := by
  have h : (q ^ 0 : ℝ) ≤ ∑ n ∈ Finset.range D, q ^ n :=
    Finset.single_le_sum (fun n _ => pow_nonneg h0 n) (Finset.mem_range.mpr (by omega))
  simpa using h

theorem Zgeom_pos {D : ℕ} (hD : 1 ≤ D) {q : ℝ} (h0 : 0 ≤ q) : 0 < Zgeom D q :=
  lt_of_lt_of_le one_pos (one_le_Zgeom hD h0)

theorem Zgeom_le_card (D : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : Zgeom D q ≤ D := by
  have h : ∑ n ∈ Finset.range D, q ^ n ≤ ∑ _n ∈ Finset.range D, (1 : ℝ) :=
    Finset.sum_le_sum fun n _ => pow_le_one₀ h0 h1
  simpa [Zgeom] using h

theorem card_mul_pow_le_Zgeom (D : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (D : ℝ) * q ^ (D - 1) ≤ Zgeom D q := by
  have h : ∑ _n ∈ Finset.range D, q ^ (D - 1) ≤ ∑ n ∈ Finset.range D, q ^ n :=
    Finset.sum_le_sum fun n hn =>
      pow_le_pow_of_le_one h0 h1 (by
        have := Finset.mem_range.mp hn
        omega)
  simpa [Zgeom, Finset.sum_const, nsmul_eq_mul] using h

theorem meanN_nonneg {D : ℕ} (hD : 1 ≤ D) {q : ℝ} (h0 : 0 ≤ q) : 0 ≤ meanN D q :=
  div_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (pow_nonneg h0 n))
    (Zgeom_pos hD h0).le

theorem meanN_le_card {D : ℕ} (hD : 1 ≤ D) {q : ℝ} (h0 : 0 ≤ q) : meanN D q ≤ D := by
  rw [meanN, div_le_iff₀ (Zgeom_pos hD h0)]
  calc ∑ n ∈ Finset.range D, (n : ℝ) * q ^ n
      ≤ ∑ n ∈ Finset.range D, (D : ℝ) * q ^ n :=
        Finset.sum_le_sum fun n hn => by
          have hn' := Finset.mem_range.mp hn
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn'.le) (pow_nonneg h0 n)
    _ = (D : ℝ) * Zgeom D q := by rw [Zgeom, Finset.mul_sum]

/-! ### Regime 1 — fixed `x > 0`: the free (Planck) oscillator entropy -/

/-- **The truncated entropy converges to the free-oscillator entropy** at fixed `x = βω > 0`:
    `S_D(x) → −log(1−e^{−x}) + x·e^{−x}/(1−e^{−x})`. -/
theorem tendsto_thermalEntropy_planck {x : ℝ} (hx : 0 < x) :
    Tendsto (fun D : ℕ => thermalEntropy D x) atTop
      (nhds (-Real.log (1 - Real.exp (-x))
        + x * (Real.exp (-x) / (1 - Real.exp (-x))))) := by
  have h0 : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  have h1 : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hlog : Tendsto (fun D : ℕ => Real.log (Zgeom D (Real.exp (-x)))) atTop
      (nhds (Real.log (1 - Real.exp (-x))⁻¹)) :=
    (tendsto_Zgeom h0 h1).log (inv_ne_zero (by linarith))
  have hN : Tendsto (fun D : ℕ => x * meanN D (Real.exp (-x))) atTop
      (nhds (x * (Real.exp (-x) / (1 - Real.exp (-x))))) :=
    (tendsto_meanN h0 h1).const_mul x
  have := hlog.add hN
  rwa [Real.log_inv] at this

/-- The cosmetic Planck form: `x·e^{−x}/(1−e^{−x}) = x/(e^x−1)`. -/
theorem planck_form {x : ℝ} (hx : 0 < x) :
    x * (Real.exp (-x) / (1 - Real.exp (-x))) = x / (Real.exp x - 1) := by
  have h1 : (1 : ℝ) < Real.exp x := by
    rw [Real.one_lt_exp_iff]
    exact hx
  have h2 : Real.exp x - 1 ≠ 0 := by linarith
  have h5 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  rw [Real.exp_neg]
  field_simp

/-! ### Regime 2 — fixed `D`, `x → 0⁺`: capacity saturation -/

theorem Zgeom_one (D : ℕ) : Zgeom D 1 = D := by
  simp [Zgeom]

/-- **Capacity saturation**: at fixed `D ≥ 1`, `S_D(x) → log D` as `x → 0⁺`. -/
theorem tendsto_thermalEntropy_saturation (D : ℕ) (hD : 1 ≤ D) :
    Tendsto (fun x : ℝ => thermalEntropy D x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.log D)) := by
  have hZc : Continuous fun x : ℝ => Zgeom D (Real.exp (-x)) := by
    refine continuous_finset_sum _ fun n _ => ?_
    exact (Real.continuous_exp.comp continuous_neg).pow n
  have hNumc : Continuous fun x : ℝ => ∑ n ∈ Finset.range D, (n : ℝ) * Real.exp (-x) ^ n := by
    refine continuous_finset_sum _ fun n _ => ?_
    exact continuous_const.mul ((Real.continuous_exp.comp continuous_neg).pow n)
  have hZ0 : Zgeom D (Real.exp (-(0 : ℝ))) = D := by
    rw [neg_zero, Real.exp_zero, Zgeom_one]
  have hZne : Zgeom D (Real.exp (-(0 : ℝ))) ≠ 0 := by
    rw [hZ0]
    exact_mod_cast (by omega : D ≠ 0)
  have hcont : ContinuousAt (fun x : ℝ => thermalEntropy D x) 0 := by
    refine ContinuousAt.add ?_ ?_
    · exact hZc.continuousAt.log hZne
    · exact continuousAt_id.mul
        ((hNumc.continuousAt).div hZc.continuousAt hZne)
  have hval : thermalEntropy D 0 = Real.log D := by
    rw [thermalEntropy, hZ0, zero_mul, add_zero]
  have := hcont.tendsto
  rw [hval] at this
  exact this.mono_left nhdsWithin_le_nhds

/-! ### THE REGIME-SEPARATION GUARD -/

/-- **The guard, entropy half**: along ANY schedule `x_D ≥ 0` with `x_D·D → 0`, capacity
    saturates — `S_D(x_D) − log D → 0`. -/
theorem guard_entropy_saturates (x : ℕ → ℝ) (hx0 : ∀ D, 0 ≤ x D)
    (hxD : Tendsto (fun D : ℕ => x D * D) atTop (nhds 0)) :
    Tendsto (fun D : ℕ => thermalEntropy D (x D) - Real.log D) atTop (nhds 0) := by
  have hneg : Tendsto (fun D : ℕ => -(x D * D)) atTop (nhds 0) := by
    have := hxD.neg
    rwa [neg_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hxD ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with D hD
    have h0 : (0 : ℝ) ≤ Real.exp (-(x D)) := (Real.exp_pos _).le
    have h1 : Real.exp (-(x D)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx0 D])
    have hq : (0 : ℝ) < Real.exp (-(x D)) := Real.exp_pos _
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have hlow : (D : ℝ) * Real.exp (-(x D)) ^ (D - 1) ≤ Zgeom D (Real.exp (-(x D))) :=
      card_mul_pow_le_Zgeom D h0 h1
    have hlowpos : (0 : ℝ) < (D : ℝ) * Real.exp (-(x D)) ^ (D - 1) := by positivity
    have hlog : Real.log ((D : ℝ) * Real.exp (-(x D)) ^ (D - 1))
        ≤ Real.log (Zgeom D (Real.exp (-(x D)))) :=
      Real.log_le_log hlowpos hlow
    rw [Real.log_mul hDpos.ne' (by positivity), Real.log_pow, Real.log_exp] at hlog
    have hxN : 0 ≤ x D * meanN D (Real.exp (-(x D))) :=
      mul_nonneg (hx0 D) (meanN_nonneg hD h0)
    have hstep : Real.log D + (D - 1 : ℕ) * (-(x D)) ≤ thermalEntropy D (x D) := by
      rw [thermalEntropy]
      linarith
    have hcast : ((D - 1 : ℕ) : ℝ) * x D ≤ x D * D := by
      have h1' : ((D - 1 : ℕ) : ℝ) ≤ (D : ℝ) := by
        exact_mod_cast Nat.sub_le D 1
      calc ((D - 1 : ℕ) : ℝ) * x D ≤ (D : ℝ) * x D :=
            mul_le_mul_of_nonneg_right h1' (hx0 D)
        _ = x D * D := by ring
    linarith
  · filter_upwards [eventually_ge_atTop 1] with D hD
    have h0 : (0 : ℝ) ≤ Real.exp (-(x D)) := (Real.exp_pos _).le
    have h1 : Real.exp (-(x D)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx0 D])
    have hZle : Zgeom D (Real.exp (-(x D))) ≤ D := Zgeom_le_card D h0 h1
    have hZpos : (0 : ℝ) < Zgeom D (Real.exp (-(x D))) := Zgeom_pos hD h0
    have hlogle : Real.log (Zgeom D (Real.exp (-(x D)))) ≤ Real.log D :=
      Real.log_le_log hZpos hZle
    have hNle : meanN D (Real.exp (-(x D))) ≤ D := meanN_le_card hD h0
    have hxN : x D * meanN D (Real.exp (-(x D))) ≤ x D * D :=
      mul_le_mul_of_nonneg_left hNle (hx0 D)
    rw [thermalEntropy]
    linarith

/-- **DS3 CAPSTONE — the guard, defect half**: along the SAME saturating schedules
    (`x_D·D → 0`), the truncation-defect expectation tends to **1**, not 0 — exact saturated
    capacity is provably NOT the positive-temperature free-oscillator limit (contrast
    `tendsto_defectExpect`, where fixed `x > 0` kills the defect). The two halves of the
    decoupling shadow live in different regimes. -/
theorem guard_defect_survives (x : ℕ → ℝ) (hx0 : ∀ D, 0 ≤ x D)
    (hxD : Tendsto (fun D : ℕ => x D * D) atTop (nhds 0)) :
    Tendsto (fun D : ℕ => defectExpect D (Real.exp (-(x D)))) atTop (nhds 1) := by
  have hexp : Tendsto (fun D : ℕ => Real.exp (-(x D * D))) atTop (nhds 1) := by
    have hneg : Tendsto (fun D : ℕ => -(x D * D)) atTop (nhds 0) := by
      have := hxD.neg
      rwa [neg_zero] at this
    have := (Real.continuous_exp.tendsto 0).comp hneg
    rwa [Real.exp_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hexp tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with D hD
    have h0 : (0 : ℝ) ≤ Real.exp (-(x D)) := (Real.exp_pos _).le
    have h1 : Real.exp (-(x D)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx0 D])
    have hq : (0 : ℝ) < Real.exp (-(x D)) := Real.exp_pos _
    have hZle : Zgeom D (Real.exp (-(x D))) ≤ D := Zgeom_le_card D h0 h1
    have hZpos : (0 : ℝ) < Zgeom D (Real.exp (-(x D))) := Zgeom_pos hD h0
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have hnum : (0 : ℝ) ≤ (D : ℝ) * Real.exp (-(x D)) ^ (D - 1) := by positivity
    -- defect ≥ D·q^{D−1}/D = q^{D−1} ≥ q^D = e^{−x_D·D}
    have hstep1 : (D : ℝ) * Real.exp (-(x D)) ^ (D - 1) / (D : ℝ)
        ≤ defectExpect D (Real.exp (-(x D))) :=
      div_le_div_of_nonneg_left hnum hZpos hZle
    have heq : (D : ℝ) * Real.exp (-(x D)) ^ (D - 1) / (D : ℝ)
        = Real.exp (-(x D)) ^ (D - 1) := by
      field_simp
    rw [heq] at hstep1
    have hstep2 : Real.exp (-(x D)) ^ D ≤ Real.exp (-(x D)) ^ (D - 1) :=
      pow_le_pow_of_le_one h0 h1 (Nat.sub_le D 1)
    have hstep3 : Real.exp (-(x D * D)) = Real.exp (-(x D)) ^ D := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    linarith [hstep3 ▸ hstep2]
  · filter_upwards [eventually_ge_atTop 1] with D hD
    have h0 : (0 : ℝ) ≤ Real.exp (-(x D)) := (Real.exp_pos _).le
    have h1 : Real.exp (-(x D)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx0 D])
    have hZpos : (0 : ℝ) < Zgeom D (Real.exp (-(x D))) := Zgeom_pos hD h0
    have hlow : (D : ℝ) * Real.exp (-(x D)) ^ (D - 1) ≤ Zgeom D (Real.exp (-(x D))) :=
      card_mul_pow_le_Zgeom D h0 h1
    rw [defectExpect, div_le_one hZpos]
    exact hlow

end QIQTH.Decoupling
