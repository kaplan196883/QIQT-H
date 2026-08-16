/-
  InverseChartFirstJet — the FIRST-JET GAP of the van-Vleck inverse chart, DERIVED by plumbing the
  forward-flow Jacobian gap (which itself is derived from the geodesic Taylor machinery) through the
  inverse-function-theorem chain rule.  This PIERCES the first-jet half of the J4-556 substrate wall.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6` and proves nothing new about `R/6`.  It is one
  geometry-layer analytic brick of the a₁=R/6 mixed-sliver campaign's chart-surface residue.  It
  supplies the exact SHAPE of the mixed-sliver hypotheses `hJ3i`/`hJ3j` of
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed`

      `hJ3i : ‖Pi z - unitVec i‖ ≤ C_P · ‖z‖`   (the RNC first-jet / Jacobian-near-identity gap)

  for the CONCRETE van-Vleck chart `V z = uniformInverseChart g gi hC hK z 0`, with
  `Pi z := fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (unitVec i)` its first jet at the origin.

  ── THE WALL, AND WHAT IT IS.  The J4-556 substrate wall says the frozen `uniformChart_exists` spec
  (`ApproximatesLinearOn` first-order + pointwise `ContDiffAt 2`) does NOT expose a uniform-in-base
  second-order Taylor / Jacobian-Lipschitz bound of the INVERSE chart, which `hJ3i`/`hJ3j` need — one
  Fréchet order above the displacement bound `hVdisp`.  The observation that BREAKS the first-jet half:
  the tower ALREADY carries the FORWARD-flow Jacobian gap
      `uniformFlowExp_fderiv_near_id_quant : ‖fderiv (φ_q) v − id‖ ≤ C_D·‖v‖`   (‖v‖ small),
  itself derived from `GeodesicTaylorCompact.geodesicField_taylor_remainder_uniform`; and the inverse
  chart's germ `W ∘ φ = id` + its `ContDiffAt 2` (both in the frozen spec) give, by the chain rule,
  `D W(0) = (D φ_z(w))⁻¹` at the root `w = W₀ z` (`φ_z w = 0`).  The operator-inverse perturbation
  `‖T⁻¹ − 1‖ ≤ 2‖T − 1‖` (on `‖T − 1‖ ≤ 1/2`) then transfers the forward gap to the inverse jet.

  ── WHAT LANDS (all DERIVED; NO `sorry`, no new axioms, NOT `a₁ = R/6`).
    * (A) `clm_inverse_sub_one_le` — the reusable OPERATOR-INVERSE PERTURBATION primitive: for any
      `T : E →L[ℝ] E` with `‖T − 1‖ ≤ ρ ≤ 1/2`, `T` is a unit and `‖Ring.inverse T − 1‖ ≤ 2ρ`
      (Neumann series, `NormedRing.inverse_one_sub` + `tsum_geometric_le_of_norm_lt_one`).
    * (B) `firstJet_gap_of_leftInverse` — the chart-agnostic first-jet transfer: given a forward
      Jacobian `T` with `‖T − 1‖ ≤ ρ ≤ 1/2` and any left inverse `P` (`P * T = 1`, from the germ
      chain rule), for any `‖e‖ ≤ 1`, `‖P e − e‖ ≤ 2ρ`.  (`P` is forced `= Ring.inverse T`.)
    * (C) `chartW0_firstJet_gap` — the CONCRETE discharge, per-point on a ball: an explicit `r > 0`
      and `C_P ≥ 0` with `‖fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (unitVec i) − unitVec i‖
      ≤ C_P·‖z‖` for `z ∈ K`, `‖z‖ < r` (`C_P = 4·C_D`).

  ── HONEST SCOPE (what is NOT closed).  Like `RNCNearIsometryPointwise.chartW0_hco_ball` /
  `InverseChartDisplacement.chartW0_displacement`, this is per-point on the injectivity BALL, not the
  GLOBAL `∀ z` the sliver literally carries (the global form needs the unbuilt gating layer setting
  `V = −id, Pi = eᵢ, Q = 0` off the injectivity ball).  The SECOND-jet bound `hJ3Q` (`‖Q z‖ ≤ C_Q`) is
  one further Fréchet order up and remains the carried substrate frontier: the frozen spec exposes only
  `ContDiffAt 2` (so `Q` exists and is continuous per base point) but no UNIFORM-in-base bound; the
  forward second Taylor exists (`geodesicField_taylor_remainder_uniform`) but its transfer to a uniform
  inverse Hessian is not plumbed here.  This brick discharges the FIRST-jet gaps `hJ3i`/`hJ3j` only.

  No `sorry`, no new axioms, no `:= True`; every hypothesis satisfiable and non-vacuous; none equals the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InverseChartDisplacement
import QIQTH.ResidueThreading
import QIQTH.SliverAssembly
import QIQTH.NearIsometryBudget
import QIQTH.PullbackNaturalityLocal

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.ExpMap QIQTH.RadialDistance
open scoped Topology BigOperators

/-! ############################################################################
    ### (A)/(B) The ABSTRACT reusable primitives — operator-inverse perturbation
    ### and the chart-agnostic first-jet transfer.  Pure calculus; no geometry.
    ############################################################################ -/

namespace QIQTH.InverseChartFirstJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]

/-- **★ (A) THE OPERATOR-INVERSE PERTURBATION PRIMITIVE — `clm_inverse_sub_one_le`.**  For any
    continuous linear endomorphism `T : E →L[ℝ] E` with `‖T − 1‖ ≤ ρ ≤ 1/2`, `T` is a unit and its
    ring inverse is `2ρ`-close to the identity:
        `‖Ring.inverse T − 1‖ ≤ 2·ρ`.
    Proof: `S := 1 − T`, `‖S‖ ≤ ρ < 1`, so `T = 1 − S` is a unit (`Units.oneSub`) with
    `Ring.inverse T = ∑' Sⁿ` and (`inverse_one_sub_nth_order' 1`) `Ring.inverse T = 1 + S·Ring.inverse T`,
    whence `Ring.inverse T − 1 = S·Ring.inverse T`; `‖Ring.inverse T‖ ≤ (1−‖S‖)⁻¹ ≤ 2`
    (`tsum_geometric_le_of_norm_lt_one`), giving `‖S·Ring.inverse T‖ ≤ ‖S‖·2 ≤ 2ρ`.
    ⚠ NOT `a₁ = R/6`. -/
theorem clm_inverse_sub_one_le (T : E →L[ℝ] E) {ρ : ℝ}
    (hT : ‖T - 1‖ ≤ ρ) (hρ : ρ ≤ 1 / 2) :
    IsUnit T ∧ ‖Ring.inverse T - 1‖ ≤ 2 * ρ := by
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) hT
  set S : E →L[ℝ] E := 1 - T with hSdef
  have hSnorm : ‖S‖ ≤ ρ := by
    have hSeq : S = -(T - 1) := by rw [hSdef]; abel
    rw [hSeq, norm_neg]; exact hT
  have hSlt1 : ‖S‖ < 1 := lt_of_le_of_lt (hSnorm.trans hρ) (by norm_num)
  have hTeq : T = 1 - S := by rw [hSdef]; abel
  have hunit : IsUnit T := by rw [hTeq]; exact (Units.oneSub S hSlt1).isUnit
  refine ⟨hunit, ?_⟩
  rw [hTeq]
  -- Neumann first-order identity: inverse(1−S) = 1 + S·inverse(1−S).
  have hnth := NormedRing.inverse_one_sub_nth_order' 1 hSlt1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, pow_one] at hnth
  have hdiff : Ring.inverse (1 - S) - 1 = S * Ring.inverse (1 - S) := by
    rw [sub_eq_iff_eq_add']; exact hnth
  -- ‖inverse(1−S)‖ ≤ (1−‖S‖)⁻¹ ≤ 2.
  have hgeom : Ring.inverse (1 - S) = ∑' m : ℕ, S ^ m := (geom_series_eq_inverse S hSlt1).symm
  have hpos : 0 < 1 - ‖S‖ := by linarith [hSnorm, hρ]
  have h2 : (1 - ‖S‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith [hSnorm, hρ]
  have hone : ‖(1 : E →L[ℝ] E)‖ = 1 := by rw [ContinuousLinearMap.one_def]; exact ContinuousLinearMap.norm_id
  have hinvnorm : ‖Ring.inverse (1 - S)‖ ≤ 2 := by
    rw [hgeom]
    calc ‖∑' m : ℕ, S ^ m‖
        ≤ ‖(1 : E →L[ℝ] E)‖ - 1 + (1 - ‖S‖)⁻¹ := tsum_geometric_le_of_norm_lt_one S hSlt1
      _ = (1 - ‖S‖)⁻¹ := by rw [hone]; ring
      _ ≤ 2 := h2
  rw [hdiff]
  calc ‖S * Ring.inverse (1 - S)‖
      ≤ ‖S‖ * ‖Ring.inverse (1 - S)‖ := norm_mul_le _ _
    _ ≤ ρ * 2 := mul_le_mul hSnorm hinvnorm (norm_nonneg _) hρ0
    _ = 2 * ρ := by ring

/-- **★ (B) THE CHART-AGNOSTIC FIRST-JET TRANSFER — `firstJet_gap_of_leftInverse`.**  Let `T` be a
    forward Jacobian with `‖T − 1‖ ≤ ρ ≤ 1/2`, and `P` ANY left inverse (`P * T = 1`, as produced by
    the chain rule on an inverse germ `W ∘ φ = id`).  Then `P` is forced equal to `Ring.inverse T`, and
    for any vector `e` with `‖e‖ ≤ 1`,
        `‖P e − e‖ ≤ 2·ρ`.
    This is the exact `hJ3i`/`hJ3j` SHAPE (with `e = unitVec i`).  ⚠ NOT `a₁ = R/6`. -/
theorem firstJet_gap_of_leftInverse (T P : E →L[ℝ] E) {ρ : ℝ}
    (hT : ‖T - 1‖ ≤ ρ) (hρ : ρ ≤ 1 / 2) (hPT : P * T = 1)
    (e : E) (he : ‖e‖ ≤ 1) :
    ‖P e - e‖ ≤ 2 * ρ := by
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) hT
  obtain ⟨hunit, hbound⟩ := clm_inverse_sub_one_le T hT hρ
  -- a left inverse of a unit is the (two-sided) inverse.
  have hP : P = Ring.inverse T := by
    have hc : T * Ring.inverse T = 1 := Ring.mul_inverse_cancel T hunit
    calc P = P * 1 := by rw [mul_one]
      _ = P * (T * Ring.inverse T) := by rw [hc]
      _ = (P * T) * Ring.inverse T := by rw [mul_assoc]
      _ = 1 * Ring.inverse T := by rw [hPT]
      _ = Ring.inverse T := by rw [one_mul]
  -- ‖P e − e‖ = ‖(P − 1) e‖ ≤ ‖P − 1‖·‖e‖ ≤ 2ρ·1.
  have hPe : (P - 1) e = P e - e := by
    simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  rw [← hPe, hP]
  calc ‖(Ring.inverse T - 1) e‖
      ≤ ‖Ring.inverse T - 1‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (2 * ρ) * 1 := mul_le_mul hbound he (norm_nonneg _) (by linarith [hρ0])
    _ = 2 * ρ := by ring

end QIQTH.InverseChartFirstJet

/-! ############################################################################
    ### (C) The CONCRETE discharge for the van-Vleck inverse chart on a ball.
    ############################################################################ -/

namespace QIQTH.HeatResidualBound

open QIQTH.InverseChartFirstJet

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-- **★ (C) `chartW0_firstJet_gap` — the mixed-sliver `hJ3i` shape for the CONCRETE van-Vleck chart,
    per-point on a ball.**  There is `r > 0` and `C_P ≥ 0` such that for every base point `z ∈ K` with
    `‖z‖ < r`, the inverse chart's first jet at the origin obeys the Jacobian-near-identity gap
        `‖fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (unitVec i) − unitVec i‖ ≤ C_P · ‖z‖`.
    Proof: at the root `w = W₀ z` (`φ_z w = 0`, `chartW0_rightInverse`), the inverse germ + `ContDiffAt 2`
    give `HasFDerivAt (W_z ∘ φ_z) (P ∘L T) w` and `= id` (germ), so `P * T = 1` with `T = fderiv φ_z w`,
    `P = fderiv W_z 0`; the forward Jacobian gap `‖T − 1‖ ≤ C_D‖w‖` (`uniformFlowExp_fderiv_near_id_quant`,
    itself from the geodesic Taylor bound) plus `firstJet_gap_of_leftInverse` give `‖P eᵢ − eᵢ‖ ≤ 2C_D‖w‖
    ≤ 4C_D‖z‖` (via `‖w‖ ≤ 2‖z‖` from `chartW0_displacement`).  ⚠ NOT `a₁ = R/6` — the GLOBAL `∀ z` form
    needs the gating layer, and `hJ3Q` (second jet) stays carried. -/
theorem chartW0_firstJet_gap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (i : Fin n) :
    ∃ r > (0 : ℝ), ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ z ∈ K, ‖z‖ < r →
      ‖fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (unitVec i) - unitVec i‖ ≤ C_P * ‖z‖ := by
  classical
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨ρ₀, hρ₀, C_D, hCD0, hnear⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  obtain ⟨rRI, hrRI, hRI⟩ := chartW0_rightInverse g gi hC hK
  obtain ⟨rD, hrD, C_W, hCW0, hdisp⟩ := chartW0_displacement g gi hC hK
  have hRf0 : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  set r : ℝ := min rRI (min rD (min (1 / (C_W + 1)) (min (δ₀ / 3)
      (min (ρ₀ / 3) (min (uniformFlowRadius g gi hC hK / 3) (1 / (4 * (C_D + 1)))))))) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact lt_min hrRI (lt_min hrD (lt_min (div_pos one_pos (by linarith [hCW0]))
      (lt_min (by linarith [hδ₀]) (lt_min (by linarith [hρ₀])
        (lt_min (by linarith [hRf0]) (div_pos one_pos (by nlinarith [hCD0])))))))
  refine ⟨r, hrpos, 4 * C_D, by nlinarith [hCD0], ?_⟩
  -- radius extraction helpers.
  have hr_rRI : r ≤ rRI := by rw [hrdef]; exact min_le_left _ _
  have hr_rD : r ≤ rD := by rw [hrdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hr_CW : r ≤ 1 / (C_W + 1) := by
    rw [hrdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr_δ : r ≤ δ₀ / 3 := by
    rw [hrdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr_ρ : r ≤ ρ₀ / 3 := by
    rw [hrdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hr_Rf : r ≤ uniformFlowRadius g gi hC hK / 3 := by
    rw [hrdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hr_CD : r ≤ 1 / (4 * (C_D + 1)) := by
    rw [hrdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  intro z hz hzr
  have hzrRI : ‖z‖ < rRI := lt_of_lt_of_le hzr hr_rRI
  have hzrD : ‖z‖ < rD := lt_of_lt_of_le hzr hr_rD
  have hzCW : ‖z‖ < 1 / (C_W + 1) := lt_of_lt_of_le hzr hr_CW
  have hzδ : ‖z‖ < δ₀ / 3 := lt_of_lt_of_le hzr hr_δ
  have hzρ : ‖z‖ < ρ₀ / 3 := lt_of_lt_of_le hzr hr_ρ
  have hzRf : ‖z‖ < uniformFlowRadius g gi hC hK / 3 := lt_of_lt_of_le hzr hr_Rf
  have hzCD : ‖z‖ < 1 / (4 * (C_D + 1)) := lt_of_lt_of_le hzr hr_CD
  rcases subsingleton_or_nontrivial (Point n) with hsub | hns
  · -- trivial space: the gap vector is 0.
    have hzero : fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (unitVec i) - unitVec i = 0 :=
      Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact mul_nonneg (by nlinarith [hCD0]) (norm_nonneg z)
  · haveI := hns
    set W : Point n → Point n := uniformInverseChart g gi hC hK z with hWdef
    set φ : Point n → Point n := uniformFlowExp g gi hC hK z with hφdef
    set w : Point n := W 0 with hwdef
    -- displacement + the bound ‖w‖ ≤ 2‖z‖.
    have hdispz : ‖w + z‖ ≤ C_W * ‖z‖ * ‖z‖ := hdisp z hz hzrD
    have hCWz : C_W * ‖z‖ ≤ 1 := by
      have hden : (0 : ℝ) < C_W + 1 := by linarith [hCW0]
      have h1 : C_W * ‖z‖ ≤ C_W * (1 / (C_W + 1)) :=
        mul_le_mul_of_nonneg_left hzCW.le hCW0
      have h2 : C_W * (1 / (C_W + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one hden]; linarith [hCW0]
      linarith
    have hw2z : ‖w‖ ≤ 2 * ‖z‖ := by
      have hwsub : ‖w‖ ≤ ‖w + z‖ + ‖z‖ := by
        calc ‖w‖ = ‖(w + z) - z‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖w + z‖ + ‖z‖ := norm_sub_le _ _
      have hwz1 : ‖w + z‖ ≤ ‖z‖ := by nlinarith [hdispz, hCWz, norm_nonneg z]
      linarith
    -- smallness of ‖w‖.
    have hwδ₀ : ‖w‖ < δ₀ := by nlinarith [hw2z, hzδ, hδ₀]
    have hwρ₀ : ‖w‖ < ρ₀ := by nlinarith [hw2z, hzρ, hρ₀]
    have hwRf : ‖w‖ < uniformFlowRadius g gi hC hK := by nlinarith [hw2z, hzRf, hRf0]
    -- the root property φ w = 0.
    have hφw0 : φ w = 0 := hRI z hz hzrRI
    -- germ + C²  of the inverse chart at w.
    have hpair := (hchart z hz).1 w hwδ₀
    have hgerm : (fun z' => W (φ z')) =ᶠ[nhds w] (fun z' => z') := hpair.1
    have hC2W0 : ContDiffAt ℝ 2 W 0 := by rw [← hφw0]; exact hpair.2
    have hWdiff : DifferentiableAt ℝ W 0 := hC2W0.differentiableAt (by norm_num)
    set P : Point n →L[ℝ] Point n := fderiv ℝ W 0 with hPdef
    have hWfd0 : HasFDerivAt W P 0 := hWdiff.hasFDerivAt
    have hWfdφ : HasFDerivAt W P (φ w) := by rw [hφw0]; exact hWfd0
    -- forward flow differentiable at w; T = its Jacobian.
    have hφC2 : ContDiffAt ℝ 2 φ w := contDiffAt2_uniformFlowExp g gi hC hK z hz w hwRf
    have hφdiff : DifferentiableAt ℝ φ w := hφC2.differentiableAt (by norm_num)
    set T : Point n →L[ℝ] Point n := fderiv ℝ φ w with hTdef
    have hφfd : HasFDerivAt φ T w := hφdiff.hasFDerivAt
    -- chain rule: (W ∘ φ) has derivative P ∘L T at w; germ makes it the identity ⟹ P * T = 1.
    have hcomp : HasFDerivAt (fun x => W (φ x)) (P.comp T) w := hWfdφ.comp w hφfd
    have hidbase : HasFDerivAt (fun x : Point n => x) (ContinuousLinearMap.id ℝ (Point n)) w :=
      hasFDerivAt_id w
    have hidfd : HasFDerivAt (fun x : Point n => x) (P.comp T) w :=
      hcomp.congr_of_eventuallyEq hgerm.symm
    have hPTid : P.comp T = ContinuousLinearMap.id ℝ (Point n) := hidfd.unique hidbase
    have hPTmul : P * T = 1 := by rw [ContinuousLinearMap.one_def]; exact hPTid
    -- forward Jacobian gap ‖T − 1‖ ≤ C_D‖w‖.
    have hnearz : ‖T - ContinuousLinearMap.id ℝ (Point n)‖ ≤ C_D * ‖w‖ := hnear z hz w hwρ₀
    have hTnorm : ‖T - (1 : Point n →L[ℝ] Point n)‖ ≤ C_D * ‖w‖ := by
      rw [ContinuousLinearMap.one_def]; exact hnearz
    -- coercivity radius C_D‖w‖ ≤ 1/2.
    have hCDw : C_D * ‖w‖ ≤ 1 / 2 := by
      have hden : (0 : ℝ) < 4 * (C_D + 1) := by nlinarith [hCD0]
      have hz2 : 2 * C_D * ‖z‖ ≤ 2 * C_D * (1 / (4 * (C_D + 1))) :=
        mul_le_mul_of_nonneg_left hzCD.le (by nlinarith [hCD0])
      have hb : 2 * C_D * (1 / (4 * (C_D + 1))) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hden]; nlinarith [hCD0]
      nlinarith [mul_le_mul_of_nonneg_left hw2z hCD0, hz2, hb]
    -- apply the abstract first-jet transfer.
    have hgap : ‖P (unitVec i) - unitVec i‖ ≤ 2 * (C_D * ‖w‖) :=
      firstJet_gap_of_leftInverse T P hTnorm hCDw hPTmul (unitVec i) (norm_single_le_one i)
    have hfin : 2 * (C_D * ‖w‖) ≤ 4 * C_D * ‖z‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hw2z hCD0, norm_nonneg w, norm_nonneg z]
    calc ‖fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (unitVec i) - unitVec i‖
        = ‖P (unitVec i) - unitVec i‖ := by rw [hPdef, hWdef]
      _ ≤ 2 * (C_D * ‖w‖) := hgap
      _ ≤ 4 * C_D * ‖z‖ := hfin

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.InverseChartFirstJet.clm_inverse_sub_one_le
#print axioms QIQTH.InverseChartFirstJet.firstJet_gap_of_leftInverse
#print axioms QIQTH.HeatResidualBound.chartW0_firstJet_gap
