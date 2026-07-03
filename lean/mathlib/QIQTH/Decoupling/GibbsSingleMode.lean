/-
  THE DECOUPLING SHADOW DS2 (THE_DECOUPLING_SHADOW_PLAN.md) — the single-mode Gibbs limit.

  QIQT-H's first GENUINE LIMIT THEOREMS (`Filter.Tendsto`): at fixed Boltzmann factor
  `0 ≤ q < 1` (fixed `βω > 0`), as the cutoff `D → ∞`:
  • the truncated partition function converges to the free-oscillator one, `Z_D(q) → 1/(1−q)`;
  • the truncated occupation expectation converges to the PLANCK value, `⟨N⟩_D → q/(1−q)`;
  • the TRUNCATION-DEFECT EXPECTATION dies, `D·q^{D−1}/Z_D → 0` — the state-level half of the
    decoupling shadow (DS1 was the operator-level half).
  Plus the bridge to the held code thermal states: `ZMode = Zgeom` at `q = e^{−βω}`.

  ⚠ HONEST SCOPE (binding verdict): fixed `βω > 0` ONLY — the capacity-saturation regime is
  DIFFERENT (the DS3 guard); this forces the free-oscillator thermal sector, never the screen
  geometry or G. NOT a full decoupling derivation.
-/
import Mathlib
import QIQTH.Dynamics

namespace QIQTH.Decoupling

open Filter

/-- The truncated geometric partition function `Z_D(q) = Σ_{n<D} q^n`. -/
noncomputable def Zgeom (D : ℕ) (q : ℝ) : ℝ := ∑ n ∈ Finset.range D, q ^ n

/-- The truncated occupation expectation `⟨N⟩_D = (Σ n·q^n)/Z_D`. -/
noncomputable def meanN (D : ℕ) (q : ℝ) : ℝ :=
  (∑ n ∈ Finset.range D, (n : ℝ) * q ^ n) / Zgeom D q

/-- The truncation-defect expectation `⟨D·P_top⟩_β = D·q^{D−1}/Z_D`. -/
noncomputable def defectExpect (D : ℕ) (q : ℝ) : ℝ :=
  (D : ℝ) * q ^ (D - 1) / Zgeom D q

/-- **The partition function converges to the free-oscillator value**: `Z_D(q) → 1/(1−q)`. -/
theorem tendsto_Zgeom {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Tendsto (fun D : ℕ => Zgeom D q) atTop (nhds (1 - q)⁻¹) :=
  (hasSum_geometric_of_lt_one h0 h1).tendsto_sum_nat

/-- **The occupation expectation converges to the PLANCK value**: `⟨N⟩_D → q/(1−q)`. -/
theorem tendsto_meanN {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Tendsto (fun D : ℕ => meanN D q) atTop (nhds (q / (1 - q))) := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hnum : Tendsto (fun D : ℕ => ∑ n ∈ Finset.range D, (n : ℝ) * q ^ n) atTop
      (nhds (q / (1 - q) ^ 2)) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).tendsto_sum_nat
  have hden := tendsto_Zgeom h0 h1
  have hne : ((1 - q)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (by linarith)
  rw [show q / (1 - q) = (q / (1 - q) ^ 2) / (1 - q)⁻¹ from by field_simp]
  exact hnum.div hden hne

/-- **DS2 CAPSTONE — the truncation-defect expectation DIES in the cutoff limit**:
    `⟨D·P_top⟩_β = D·q^{D−1}/Z_D → 0` at fixed `βω > 0` — the state-level statement that the
    thermal code decouples onto the free oscillator (the honest regime: fixed positive
    temperature; the saturation regime behaves OPPOSITELY — the DS3 guard). -/
theorem tendsto_defectExpect {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Tendsto (fun D : ℕ => defectExpect D q) atTop (nhds 0) := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hsum : Summable (fun n : ℕ => (n : ℝ) * q ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  have hterm : Tendsto (fun n : ℕ => (n : ℝ) * q ^ n) atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hq : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) atTop (nhds 0) := by
    have := hterm.add hq
    rw [add_zero] at this
    refine this.congr fun n => ?_
    ring
  have h3 : Tendsto (fun D : ℕ => (D : ℝ) * q ^ (D - 1)) atTop (nhds 0) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    refine h2.congr fun n => ?_
    push_cast
    ring
  have hden := tendsto_Zgeom h0 h1
  have hne : ((1 - q)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (by linarith)
  have := h3.div hden hne
  rw [zero_div] at this
  exact this

/-- **The bridge to the held code thermal states**: the DY2 per-mode partition function IS the
    truncated geometric sum at `q = e^{−βω}` — the DS2 limits are statements about the code's own
    Gibbs states. -/
theorem ZMode_eq_Zgeom {M : Type*} (L : QIQTH.Keystone.LinkDims M) (ω : M → ℝ)
    (β : ℝ) (k : M) :
    QIQTH.Dynamics.ZMode L ω β k = Zgeom (L.D k) (Real.exp (-(β * ω k))) := by
  rw [QIQTH.Dynamics.ZMode, Zgeom,
    ← Fin.sum_univ_eq_sum_range (fun n => Real.exp (-(β * ω k)) ^ n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end QIQTH.Decoupling
