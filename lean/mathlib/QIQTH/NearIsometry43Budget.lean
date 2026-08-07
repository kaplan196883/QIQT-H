/-
  NearIsometry43Budget — J4-371: the WIDTH-4/3 near-isometry budget.

  ## ⚠ HONESTY FIREWALL
  This file is NOT `a₁ = R/6`; `a₁ = R/6` remains CONDITIONAL.  It only supplies a tighter
  (width-4/3) ball-local near-isometry budget mirroring the banked width-2 pairing
  `QIQTH.HeatResidualBound.uniformFlowExp_hdisp_ball` (J4-96), so that the ambient
  `v → (p − q)` transfer of the AffineGateBound closure can run at target width `4/3` (rather than `2`).

  ## Context — the banked pairing being mirrored.

  `QIQTH.HeatResidualBound.uniformFlowExp_hdisp_ball` (`NearIsometryBudget.lean`, J4-96) delivers the
  ball-local budget
    `∃ r₁ > 0, ∀ q ∈ K, ∀ ‖v‖ < r₁,  (3/2)·rncRadialSq (φ_q v − q) ≤ 2·rncRadialSq v`,
  which the Gaussian transfer `gaussDdim_le_gaussDdim_chart (c := 3/2) (d := 2)` consumes as
    `gaussDdim ((3/2)·τ) v ≤ √(2/(3/2))ⁿ · gaussDdim (2·τ) (φ_q v − q)`
  (`c·rncRadialSq w ≤ d·rncRadialSq v ⟹ G_c(τ,v) ≤ √(d/c)ⁿ·G_d(τ, w)`, `w = φ_q v − q`).

  ## What this file delivers (all DERIVED from `hC` + `IsCompact K`; NO `sorry`, NOT `a₁ = R/6`).

  * (N1) `uniformFlowExp_hdisp43_ball` — the ball-local width-4/3 budget with the CONCRETE `w₀ = 5/4`:
    `∃ r₁ > 0, ∀ q ∈ K, ∀ ‖v‖ < r₁,  (5/4)·rncRadialSq (φ_q v − q) ≤ (4/3)·rncRadialSq v`.
    Proof MIRRORS J4-96's `uniformFlowExp_hdisp_ball` verbatim (same quadratic-displacement `D2` input,
    same ℓ²-expansion `rncRadialSq_add_le`), but shrinks `r₁` so the correction factor is `≤ 1/15`
    (rather than `≤ 1/3`), giving `(5/4)·(1 + 1/15) = (5/4)·(16/15) = 4/3` (rather than `(3/2)·(4/3) = 2`).
    The choice `w₀ = 5/4 < 4/3` leaves the reserve `(4/3)/(5/4) = 16/15 > 1` for the near-identity slack.

  * (N2) `uniformFlowExp_gaussDdim_transfer_43` — the Gaussian comparison the ambient transfer consumes:
    `∃ r₁ > 0, ∀ q ∈ K, ∀ ‖v‖ < r₁, ∀ τ > 0,
        gaussDdim ((5/4)·τ) v ≤ √((4/3)/(5/4))ⁿ · gaussDdim ((4/3)·τ) (φ_q v − q)`,
    obtained by feeding N1 into `gaussDdim_le_gaussDdim_chart (c := 5/4) (d := 4/3)` (mirroring the
    banked `(3/2, 2)` invocation exactly, with the tighter constants).  This is what closes the width-4/3
    ambient leg.
-/
import Mathlib
import QIQTH.NearIsometryBudget

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric QIQTH.RadialDistance
open QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.RNCDecay QIQTH.TrueHeatKernel
open Set Filter
open scoped Topology NNReal BigOperators Matrix

namespace QIQTH.NearIsometry43Budget

open QIQTH.ExpMap QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### (N1) The ball-local width-4/3 near-isometry budget (`w₀ = 5/4`). -/

/-- **★ J4-371 (N1) — ball-local width-4/3 budget.**  There is `r₁ > 0` such that for every `q ∈ K`,
    `‖v‖ < r₁`,
      `(5/4)·rncRadialSq (φ_q v − q) ≤ (4/3)·rncRadialSq v`.
    Mirrors the banked width-2 pairing `uniformFlowExp_hdisp_ball` (J4-96) verbatim from the same
    quadratic displacement bound `uniformFlowExp_displacement_bound` (D2)
    `‖φ_q v − q − v‖ ≤ C_D·‖v‖²` and the ℓ² expansion `rncRadialSq_add_le`
    `rncRadialSq (v + e) ≤ rncRadialSq v + 2n·(‖v‖·‖e‖) + n·‖e‖²`, but shrinks `r₁` so the correction
    factor is `≤ 1/15`, giving `(5/4)·(1 + 1/15) = (5/4)·(16/15) = 4/3`.  (This is NOT `a₁ = R/6`.) -/
theorem uniformFlowExp_hdisp43_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₁ →
      (5 / 4 : ℝ) * rncRadialSq (uniformFlowExp g gi hC hK q v - q) ≤ (4 / 3 : ℝ) * rncRadialSq v := by
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hdisp2⟩ := uniformFlowExp_displacement_bound g gi hC hK
  set D : ℝ := 2 * (n : ℝ) * C_D + (n : ℝ) * C_D ^ 2 + 1 with hD
  have hDpos : 0 < D := by
    have h1 : 0 ≤ 2 * (n : ℝ) * C_D := mul_nonneg (by positivity) hCD0
    have h2 : 0 ≤ (n : ℝ) * C_D ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg C_D)
    rw [hD]; linarith
  set r₁ : ℝ := min ρ₀ (min 1 (1 / (15 * D))) with hr₁
  have hr₁pos : 0 < r₁ := lt_min hρ₀pos (lt_min one_pos (by positivity))
  refine ⟨r₁, hr₁pos, ?_⟩
  intro q hq v hv
  have hvρ₀ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (by rw [hr₁]; exact min_le_left _ _)
  have he : ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_D * ‖v‖ * ‖v‖ := hdisp2 q hq v hvρ₀
  set e : Point n := uniformFlowExp g gi hC hK q v - q - v with hedef
  have hxe : uniformFlowExp g gi hC hK q v - q = v + e := by rw [hedef]; abel
  rw [hxe]
  have hadd := rncRadialSq_add_le v e
  have hrv : (0 : ℝ) ≤ rncRadialSq v := rncRadialSq_nonneg v
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hne : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
  have hnvsq : ‖v‖ ^ 2 ≤ rncRadialSq v := by
    have h := norm_le_rncRadial v
    calc ‖v‖ ^ 2 ≤ (rncRadial v) ^ 2 := pow_le_pow_left₀ hnv h 2
      _ = rncRadialSq v := rncRadial_sq v
  have he2 : ‖e‖ ≤ C_D * ‖v‖ ^ 2 := by rw [sq, ← mul_assoc]; exact he
  have hvr1 : ‖v‖ ≤ r₁ := hv.le
  have hr1_le1 : r₁ ≤ 1 := by rw [hr₁]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr1_leD : r₁ ≤ 1 / (15 * D) := by
    rw [hr₁]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- term bounds
  have hnvsq_r1 : ‖v‖ ^ 2 ≤ r₁ ^ 2 := by nlinarith [hvr1, hnv, hr₁pos.le]
  have hT1 : ‖v‖ * ‖e‖ ≤ C_D * r₁ * rncRadialSq v := by
    have h1 : ‖v‖ * ‖e‖ ≤ ‖v‖ * (C_D * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left he2 hnv
    have h2 : ‖v‖ ^ 2 * ‖v‖ ≤ rncRadialSq v * r₁ := mul_le_mul hnvsq hvr1 hnv hrv
    nlinarith [h1, mul_le_mul_of_nonneg_left h2 hCD0]
  have hT2 : ‖e‖ ^ 2 ≤ C_D ^ 2 * r₁ ^ 2 * rncRadialSq v := by
    have he2sq : ‖e‖ ^ 2 ≤ (C_D * ‖v‖ ^ 2) ^ 2 := pow_le_pow_left₀ hne he2 2
    have hv4 : ‖v‖ ^ 2 * ‖v‖ ^ 2 ≤ rncRadialSq v * r₁ ^ 2 :=
      mul_le_mul hnvsq hnvsq_r1 (sq_nonneg _) hrv
    nlinarith [he2sq, mul_le_mul_of_nonneg_left hv4 (sq_nonneg C_D)]
  -- coefficient bound: shrink r₁ so the correction is ≤ 1/15
  have hr1sq : r₁ ^ 2 ≤ r₁ := by nlinarith [hr₁pos.le, hr1_le1]
  have hnC2 : (0 : ℝ) ≤ (n : ℝ) * C_D ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg C_D)
  have hbig : 2 * (n : ℝ) * C_D * r₁ + (n : ℝ) * C_D ^ 2 * r₁ ^ 2 ≤ D * r₁ := by
    rw [hD]; nlinarith [mul_nonneg hnC2 (sub_nonneg.mpr hr1sq), hr₁pos.le]
  have hr1D : D * r₁ ≤ 1 / 15 := by
    calc D * r₁ ≤ D * (1 / (15 * D)) := mul_le_mul_of_nonneg_left hr1_leD hDpos.le
      _ = 1 / 15 := by
          rw [mul_one_div, div_eq_iff (mul_ne_zero (by norm_num : (15 : ℝ) ≠ 0) hDpos.ne')]; ring
  have hcoef : 2 * (n : ℝ) * C_D * r₁ + (n : ℝ) * C_D ^ 2 * r₁ ^ 2 ≤ 1 / 15 := le_trans hbig hr1D
  -- middle bound
  have hM : 2 * (n : ℝ) * (‖v‖ * ‖e‖) + (n : ℝ) * ‖e‖ ^ 2 ≤ 1 / 15 * rncRadialSq v := by
    nlinarith [mul_le_mul_of_nonneg_left hT1 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hT2 (Nat.cast_nonneg n),
      mul_le_mul_of_nonneg_right hcoef hrv, hrv]
  linarith [hadd, hM]

/-! ### (N2) The width-4/3 Gaussian transfer the ambient leg consumes. -/

/-- **★ J4-371 (N2) — width-4/3 Gaussian transfer.**  There is `r₁ > 0` such that for every `q ∈ K`,
    `‖v‖ < r₁`, `τ > 0`,
      `gaussDdim ((5/4)·τ) v ≤ √((4/3)/(5/4))ⁿ · gaussDdim ((4/3)·τ) (φ_q v − q)`.
    Feeds the ball-local width-4/3 budget (N1) into the banked chart transfer
    `gaussDdim_le_gaussDdim_chart (c := 5/4) (d := 4/3)` (the width-budget → Gaussian-comparison
    step), mirroring the banked `(3/2, 2)` invocation exactly with the tighter constants.
    (This is NOT `a₁ = R/6`.) -/
theorem uniformFlowExp_gaussDdim_transfer_43 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₁ → ∀ τ : ℝ, 0 < τ →
      gaussDdim (5 / 4 * τ) v
        ≤ Real.sqrt ((4 / 3) / (5 / 4)) ^ n
            * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q) := by
  obtain ⟨r₁, hr₁pos, hbud⟩ := uniformFlowExp_hdisp43_ball g gi hC hK
  refine ⟨r₁, hr₁pos, ?_⟩
  intro q hq v hv τ hτ
  exact gaussDdim_le_gaussDdim_chart (c := 5 / 4) (d := 4 / 3) (by norm_num) (by norm_num) hτ
    (hbud q hq v hv)

end QIQTH.NearIsometry43Budget

/-! ### Axiom audit. -/

#print axioms QIQTH.NearIsometry43Budget.uniformFlowExp_hdisp43_ball
#print axioms QIQTH.NearIsometry43Budget.uniformFlowExp_gaussDdim_transfer_43
