/-
  InverseChartDisplacement — J4-129: the INVERSE-CHART displacement bound + near-isometry, derived
  from the tower's EXP-side displacement bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS BRICK IS.

  `ChartWrapperConcrete` (J4-128) isolated — as explicit, honest, labelled hypotheses — the concrete
  chart near-isometry facts consumed by the L¹ Gaussian kernel-replacement adapter
  (`chartGauss_concrete_sub_plain_tendsto`):
      `hcoarse₀ : ∃ c>0, ∀ z∈S, c·‖z‖² ≤ ‖W₀ z‖²`   and
      `hasymp₀  : ∀ δ∈(0,1) ∃ r>0, ∀ z∈S, ‖z‖²<r² → (1−δ)‖z‖² ≤ ‖W₀ z‖² ≤ (1+δ)‖z‖²`,
  where `W₀ z := uniformInverseChart g gi hC hK z 0` is the normal coordinate of the origin seen from
  the base point `z` (the Gaussian argument produced by the van-Vleck gated witness).  Its header called
  the quantitative inverse-function control of `W₀` "the recognized geometric BLOCKER (1)" — the tower
  carried only the EXP-side displacement `‖φ_q v − q − v‖ ≤ C_D‖v‖²` (`NearIsometryBudget`), not the
  inverse side.

  ## WHAT LANDS HERE (all DERIVED from the tower; NO `sorry`, no new axioms, no `expRho`; NOT `a₁=R/6`).

    * (D1) `chartW0_displacement` — the INVERSE-CHART displacement bound
        `‖W₀ z + z‖ ≤ 4·C_D·‖z‖²`  (sup norm),  for `z ∈ K`, `‖z‖` small.
      Route: `φ_z(W₀ z) = 0` (the inverse property, recovered by combining the local-inverse germ of
      `uniformInverseChart` with a Mathlib `ApproximatesLinearOn.surjOn` root `w` of `φ_z`), so
      `z + W₀ z + err = 0` with `‖err‖ ≤ C_D‖W₀ z‖²` (`uniformFlowExp_displacement_bound`); a bootstrap
      on `C_D‖W₀ z‖ ≤ 1/2` gives `‖W₀ z‖ ≤ 2‖z‖`, hence `‖W₀ z + z‖ ≤ 4C_D‖z‖²`.  NOTE the SIGN:
      `W₀ z ≈ −z`.

    * (raw) `chartW0_rncRadialSq_error` — the ℓ²-squared near-isometry error
        `|rncRadialSq(W₀ z) − rncRadialSq z| ≤ L·‖z‖·rncRadialSq z`  (`L := 2n·C_W + 3n·C_W²`),
      from D1 via `rncRadialSq_add_le` and the evenness `rncRadialSq(−z) = rncRadialSq z`.

    * (D2) `chartW0_nearIsometry` — the near-isometry family in EXACTLY the shapes
      `chartGauss_concrete_sub_plain_tendsto` carries: a single `r>0` such that for every
      `S ⊆ K ∩ ball 0 r` BOTH `hcoarse₀` (with `c = 1/2`) AND `hasymp₀` hold verbatim.  This DISCHARGES
      the recognized BLOCKER (1) of `ChartWrapperConcrete`.

    * (D5-lite) `chartW0_l1_sub_plain_of_meas` — the concrete L¹ kernel replacement with the near-isometry
      inputs DISCHARGED: only the base MEASURABILITY `hWmeas₀` (blocker (2)) remains as an honest labelled
      hypothesis (see FIREWALL below).

  ⚠ HONEST FIREWALL — what is NOT discharged (carried, labelled, per the `ChartWrapperConcrete` header).
    * (2) BASE-POINT measurability/continuity of `z ↦ W₀ z` (`hWmeas₀`).  This is a GENUINE geometric fact
      of the honest chart but the tower has NO base-point (`q`) regularity of the flow
      `uniformFlowExp g gi hC hK q v` — the chart is `.choose`-built and the only `q`-regularity in the
      tower is the second-jet operator-norm continuity on `K ×ˢ B̄` (`BasepointJetModulus`), which is not
      the flow itself.  So `hWmeas₀` is CARRIED as an explicit hypothesis (satisfiable, non-vacuous,
      never the conclusion) in `chartW0_l1_sub_plain_of_meas`.
    * (3) the uniform gate-ball containment `∃ ρ>0, ball 0 ρ ⊆ {z : 0 ∈ S z}` for the per-`z` gate — a
      distinct concern from the near-isometry set `S ⊆ K ∩ ball 0 r`; not addressed here.
    D1 + D2 are the prize (the near-isometry discharge); (2)+(3) stay labelled.
-/
import Mathlib
import QIQTH.ChartWrapperConcrete

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.RNCDecay
open scoped Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### Elementary ℓ² helpers. -/

/-- `rncRadialSq` is even. -/
theorem rncRadialSq_neg (z : Point n) : rncRadialSq (-z) = rncRadialSq z := by
  simp only [rncRadialSq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.neg_apply]; ring

/-- The sup-norm square is `≤` the ℓ²-square `rncRadialSq`. -/
theorem norm_sq_le_rncRadialSq (z : Point n) : ‖z‖ ^ 2 ≤ rncRadialSq z := by
  have h := norm_le_rncRadial z
  have h2 := rncRadial_sq z
  nlinarith [h, rncRadial_nonneg z, norm_nonneg z, h2]

/-! ### (D1) The inverse-chart displacement bound `‖W₀ z + z‖ ≤ 4·C_D·‖z‖²`. -/

/-- **★ D1 — `chartW0_displacement`.**  There is `r₁ > 0` and a constant `C_W ≥ 0` such that for every
    base point `z ∈ K` with `‖z‖ < r₁`, the inverse-chart origin coordinate `W₀ z =
    uniformInverseChart g gi hC hK z 0` satisfies the quadratic displacement bound (sup norm)
        `‖W₀ z + z‖ ≤ C_W · ‖z‖ · ‖z‖`.
    Note the SIGN: `W₀ z ≈ −z`.  Proof: a Mathlib `ApproximatesLinearOn` surjectivity root gives
    `w` with `φ_z w = 0`, `‖w‖` small; the inverse germ pins `W₀ z = w`; the EXP-side displacement
    `uniformFlowExp_displacement_bound` gives `‖w + z‖ ≤ C_D‖w‖²`; a bootstrap on `C_D‖w‖ ≤ 1/2`
    yields `‖w‖ ≤ 2‖z‖`, hence `‖w + z‖ ≤ 4C_D‖z‖²` with `C_W := 4C_D`. -/
theorem chartW0_displacement (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₁ > (0 : ℝ), ∃ C_W : ℝ, 0 ≤ C_W ∧ ∀ z ∈ K, ‖z‖ < r₁ →
      ‖uniformInverseChart g gi hC hK z 0 + z‖ ≤ C_W * ‖z‖ * ‖z‖ := by
  classical
  obtain ⟨δc, hδc, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨δ₁, hδ₁, c, hc1, hAL⟩ := uniformFlowExp_approximatesLinearOn g gi hC hK
  obtain ⟨ρd, hρd, C_D, hCD0, hdisp⟩ := uniformFlowExp_displacement_bound g gi hC hK
  -- master small radius `M` and the root radius `ε = M/2`.
  set M : ℝ := min δ₁ (min δc (min ρd (1 / (2 * (C_D + 1))))) with hMdef
  have hM1 : M ≤ δ₁ := min_le_left _ _
  have hM2 : M ≤ δc := le_trans (min_le_right _ _) (min_le_left _ _)
  have hM3 : M ≤ ρd := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hM4 : M ≤ 1 / (2 * (C_D + 1)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMpos : 0 < M := lt_min hδ₁ (lt_min hδc (lt_min hρd (by positivity)))
  set ε : ℝ := M / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεδ₁ : ε < δ₁ := by rw [hεdef]; linarith
  have hεδc : ε < δc := by rw [hεdef]; linarith
  have hερd : ε < ρd := by rw [hεdef]; linarith
  have hεCD : ε ≤ 1 / (2 * (C_D + 1)) := by rw [hεdef]; linarith
  have hc0 : 0 < 1 - (c : ℝ) := by linarith [hc1]
  refine ⟨(1 - (c : ℝ)) * ε, mul_pos hc0 hεpos, 4 * C_D, by linarith [hCD0], ?_⟩
  intro z hz hzr
  rcases subsingleton_or_nontrivial (Point n) with hsub | hns
  · -- trivial space: every vector is `0`.
    have he : uniformInverseChart g gi hC hK z 0 + z = 0 := Subsingleton.elim _ _
    rw [he, norm_zero]
    nlinarith [mul_nonneg (mul_nonneg hCD0 (norm_nonneg z)) (norm_nonneg z)]
  · haveI := hns
    -- the `ApproximatesLinearOn` root `w` of `φ_z`.
    set fri := (ContinuousLinearEquiv.refl ℝ (Point n)).toNonlinearRightInverse with hfri
    have hnn : ((fri.nnnorm : ℝ)) = 1 := by
      have h1 : fri.nnnorm
          = ‖((ContinuousLinearEquiv.refl ℝ (Point n)).symm : Point n →L[ℝ] Point n)‖₊ := rfl
      have h2 : ((ContinuousLinearEquiv.refl ℝ (Point n)).symm : Point n →L[ℝ] Point n)
          = ContinuousLinearMap.id ℝ (Point n) := by ext x; simp
      have h3 : ‖ContinuousLinearMap.id ℝ (Point n)‖₊ = 1 := by simp
      rw [h1, h2, h3]; norm_num
    have hALz : ApproximatesLinearOn (uniformFlowExp g gi hC hK z)
        (ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n)
        (Metric.ball 0 δ₁) c := hAL z hz
    have hφ0 : uniformFlowExp g gi hC hK z 0 = z := uniformFlowExp_zero g gi hC hK z hz
    have hεsub : Metric.closedBall (0 : Point n) ε ⊆ Metric.ball 0 δ₁ := by
      intro x hx
      rw [mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt hx hεδ₁
    have hsurj := hALz.surjOn_closedBall_of_nonlinearRightInverse fri hεpos.le hεsub
    have h0mem : (0 : Point n) ∈ Metric.closedBall (uniformFlowExp g gi hC hK z 0)
        (((fri.nnnorm : ℝ)⁻¹ - ↑c) * ε) := by
      rw [Metric.mem_closedBall, hnn, inv_one, hφ0, dist_eq_norm, zero_sub, norm_neg]
      linarith [hzr]
    obtain ⟨w, hwmem, hwφ⟩ := hsurj h0mem
    have hwε : ‖w‖ ≤ ε := by rwa [mem_closedBall_zero_iff] at hwmem
    have hwδc : ‖w‖ < δc := lt_of_le_of_lt hwε hεδc
    have hwρd : ‖w‖ < ρd := lt_of_le_of_lt hwε hερd
    -- pin `W₀ z = w` via the inverse germ.
    obtain ⟨hgermC2, _⟩ := hchart z hz
    obtain ⟨hgerm, _⟩ := hgermC2 w hwδc
    have hval : uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z w) = w :=
      hgerm.eq_of_nhds
    rw [hwφ] at hval
    -- the displacement bound at `w`.
    have hd := hdisp z hz w hwρd
    rw [hwφ] at hd
    have hdd : ‖w + z‖ ≤ C_D * ‖w‖ * ‖w‖ := by
      have e : (0 : Point n) - z - w = -(w + z) := by abel
      rw [e, norm_neg] at hd; exact hd
    -- bootstrap `C_D‖w‖ ≤ 1/2 ⟹ ‖w‖ ≤ 2‖z‖`.
    have hCDw : C_D * ‖w‖ ≤ 1 / 2 := by
      have hA : C_D * ‖w‖ ≤ C_D * ε := mul_le_mul_of_nonneg_left hwε hCD0
      have hB : C_D * ε ≤ C_D * (1 / (2 * (C_D + 1))) := mul_le_mul_of_nonneg_left hεCD hCD0
      have hCc : C_D * (1 / (2 * (C_D + 1))) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith [hCD0]
      linarith
    have hwz : ‖w‖ ≤ ‖w + z‖ + ‖z‖ := by
      calc ‖w‖ = ‖(w + z) - z‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖w + z‖ + ‖z‖ := norm_sub_le _ _
    have hw2z : ‖w‖ ≤ 2 * ‖z‖ := by
      nlinarith [hdd, hwz, hCDw, norm_nonneg w, norm_nonneg z]
    have hww : ‖w‖ * ‖w‖ ≤ (2 * ‖z‖) * (2 * ‖z‖) :=
      mul_le_mul hw2z hw2z (norm_nonneg w) (by positivity)
    -- conclude.
    rw [hval]
    nlinarith [hdd, hww, hCD0]

/-! ### (raw) The ℓ²-squared near-isometry error `|rncRadialSq(W₀ z) − rncRadialSq z| ≤ L·‖z‖·rncRadialSq z`. -/

/-- **raw — `chartW0_rncRadialSq_error`.**  From the D1 displacement bound `‖W₀ z + z‖ ≤ C_W‖z‖²`
    (sign: `W₀ z = −z + b`, `‖b‖ ≤ C_W‖z‖²`) and the evenness `rncRadialSq(−z) = rncRadialSq z`, the
    coordinatewise expansion `rncRadialSq_add_le` gives, on `‖z‖ < r₀ ≤ 1`, the two-sided error
        `rncRadialSq z − L·‖z‖·rncRadialSq z ≤ rncRadialSq(W₀ z) ≤ rncRadialSq z + L·‖z‖·rncRadialSq z`,
    with `L := 2n·C_W + 3n·C_W²`.  (The dimension `n` is absorbed into `L`; `‖z‖² ≤ ‖z‖` on the ball.) -/
theorem chartW0_rncRadialSq_error (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ K, ‖z‖ < r₀ →
      rncRadialSq z - L * ‖z‖ * rncRadialSq z
          ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)
      ∧ rncRadialSq (uniformInverseChart g gi hC hK z 0)
          ≤ rncRadialSq z + L * ‖z‖ * rncRadialSq z := by
  obtain ⟨rd, hrd, C_W, hCW0, hD1⟩ := chartW0_displacement g gi hC hK
  refine ⟨min rd 1, lt_min hrd one_pos, 2 * (n : ℝ) * C_W + 3 * (n : ℝ) * C_W ^ 2,
    by positivity, ?_⟩
  intro z hz hzr
  have hzrd : ‖z‖ < rd := lt_of_lt_of_le hzr (min_le_left _ _)
  have hz1 : ‖z‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hzr (min_le_right _ _))
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set W : Point n := uniformInverseChart g gi hC hK z 0 with hWdef
  have hb0 := hD1 z hz hzrd
  rw [← hWdef] at hb0
  set b : Point n := W + z with hbdef
  have hb : ‖b‖ ≤ C_W * ‖z‖ * ‖z‖ := hb0
  have hWeq : W = -z + b := by rw [hbdef]; abel
  have hzsq : ‖z‖ ^ 2 ≤ rncRadialSq z := norm_sq_le_rncRadialSq z
  have hz3 : ‖z‖ ^ 3 ≤ ‖z‖ * rncRadialSq z := by nlinarith [hzsq, norm_nonneg z]
  have hz4 : ‖z‖ ^ 4 ≤ ‖z‖ * rncRadialSq z := by
    have s1 : ‖z‖ ^ 4 ≤ ‖z‖ ^ 2 * rncRadialSq z := by nlinarith [hzsq, sq_nonneg (‖z‖)]
    have s2 : ‖z‖ ^ 2 * rncRadialSq z ≤ ‖z‖ * rncRadialSq z := by
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg z)
        (by linarith [hz1] : (0 : ℝ) ≤ 1 - ‖z‖)) (rncRadialSq_nonneg z)]
    linarith [s1, s2]
  have hzb : ‖z‖ * ‖b‖ ≤ C_W * (‖z‖ * rncRadialSq z) := by
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg z), hz3, hCW0, norm_nonneg z]
  have hbsq : ‖b‖ ^ 2 ≤ C_W ^ 2 * (‖z‖ * rncRadialSq z) := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg b) hb 2, hz4, sq_nonneg C_W]
  have hWn : ‖W‖ ≤ (1 + C_W) * ‖z‖ := by
    have h1 : ‖W‖ ≤ ‖z‖ + ‖b‖ := by
      rw [hWeq]
      calc ‖-z + b‖ ≤ ‖-z‖ + ‖b‖ := norm_add_le _ _
        _ = ‖z‖ + ‖b‖ := by rw [norm_neg]
    have hb1 : ‖b‖ ≤ C_W * ‖z‖ := by
      have hstep : C_W * ‖z‖ * ‖z‖ ≤ C_W * ‖z‖ * 1 :=
        mul_le_mul_of_nonneg_left hz1 (mul_nonneg hCW0 (norm_nonneg z))
      nlinarith [hb, hstep]
    nlinarith [h1, hb1]
  have hWb : ‖W‖ * ‖b‖ ≤ C_W * (1 + C_W) * (‖z‖ * rncRadialSq z) := by
    have hmul : ‖W‖ * ‖b‖ ≤ ((1 + C_W) * ‖z‖) * (C_W * ‖z‖ * ‖z‖) :=
      mul_le_mul hWn hb (norm_nonneg b) (mul_nonneg (by linarith [hCW0]) (norm_nonneg z))
    nlinarith [hmul, hz3, mul_nonneg hCW0 (by linarith [hCW0] : (0 : ℝ) ≤ 1 + C_W)]
  have hneg : rncRadialSq (-z) = rncRadialSq z := rncRadialSq_neg z
  -- the two `rncRadialSq_add_le` inequalities.
  have hU : rncRadialSq W ≤ rncRadialSq z + 2 * (n : ℝ) * (‖z‖ * ‖b‖) + (n : ℝ) * ‖b‖ ^ 2 := by
    have h := rncRadialSq_add_le (-z) b
    rw [hneg, norm_neg, ← hWeq] at h
    exact h
  have hLo : rncRadialSq z ≤ rncRadialSq W + 2 * (n : ℝ) * (‖W‖ * ‖b‖) + (n : ℝ) * ‖b‖ ^ 2 := by
    have h := rncRadialSq_add_le W (-b)
    rw [norm_neg, show W + -b = -z from by rw [hWeq]; abel, hneg] at h
    exact h
  refine ⟨?_, ?_⟩
  · -- lower
    nlinarith [hLo, mul_le_mul_of_nonneg_left hWb (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hbsq hn0, hn0, hCW0, norm_nonneg z, rncRadialSq_nonneg z]
  · -- upper
    nlinarith [hU, mul_le_mul_of_nonneg_left hzb (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hbsq hn0, hn0, hCW0, norm_nonneg z, rncRadialSq_nonneg z,
      mul_nonneg (mul_nonneg (mul_nonneg hn0 (sq_nonneg C_W)) (norm_nonneg z)) (rncRadialSq_nonneg z)]

/-! ### (D2) The near-isometry family — `hcoarse₀` + `hasymp₀`, verbatim shapes. -/

/-- **★★ D2 — `chartW0_nearIsometry`: the recognized BLOCKER (1) of `ChartWrapperConcrete`, DISCHARGED.**
    There is a single `r > 0` such that for EVERY active set `S ⊆ K ∩ ball 0 r`, BOTH concrete chart
    near-isometry facts consumed by `chartGauss_concrete_sub_plain_tendsto` hold verbatim:
      * `hcoarse₀` with `c = 1/2`:  `∀ z ∈ S, (1/2)·rncRadialSq z ≤ rncRadialSq(W₀ z)`;
      * `hasymp₀`:  `∀ δ∈(0,1) ∃ r'>0, ∀ z∈S, rncRadialSq z < r'² →
            (1−δ)·rncRadialSq z ≤ rncRadialSq(W₀ z) ≤ (1+δ)·rncRadialSq z`.
    Both from the raw error `|rncRadialSq(W₀ z) − rncRadialSq z| ≤ L·‖z‖·rncRadialSq z`, shrinking the
    radius so `L·‖z‖ ≤ 1/2` (coarse) resp. `L·‖z‖ ≤ δ` (asymptotic). -/
theorem chartW0_nearIsometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ (S : Set (Point n)), S ⊆ K ∩ Metric.ball 0 r →
      (∃ c > (0 : ℝ), ∀ z ∈ S,
          c * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
      ∧ (∀ δ : ℝ, 0 < δ → δ < 1 → ∃ r' > (0 : ℝ), ∀ z ∈ S, rncRadialSq z < r' ^ 2 →
          (1 - δ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)
          ∧ rncRadialSq (uniformInverseChart g gi hC hK z 0) ≤ (1 + δ) * rncRadialSq z) := by
  obtain ⟨r₀, hr₀, L, hL0, hraw⟩ := chartW0_rncRadialSq_error g gi hC hK
  set r : ℝ := min r₀ (1 / (2 * (L + 1))) with hrdef
  have hrpos : 0 < r := lt_min hr₀ (by positivity)
  refine ⟨r, hrpos, ?_⟩
  intro S hSsub
  refine ⟨?_, ?_⟩
  · -- hcoarse₀, c = 1/2.
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro z hzS
    have hzK : z ∈ K := (hSsub hzS).1
    have hznorm : ‖z‖ < r := by
      have := (hSsub hzS).2; rwa [mem_ball_zero_iff] at this
    have hzr₀ : ‖z‖ < r₀ := lt_of_lt_of_le hznorm (min_le_left _ _)
    have hzrL : ‖z‖ < 1 / (2 * (L + 1)) := lt_of_lt_of_le hznorm (min_le_right _ _)
    obtain ⟨hlow, _⟩ := hraw z hzK hzr₀
    have hLz : L * ‖z‖ ≤ 1 / 2 := by
      have hstep : L * ‖z‖ ≤ L * (1 / (2 * (L + 1))) :=
        mul_le_mul_of_nonneg_left hzrL.le hL0
      have hbound : L * (1 / (2 * (L + 1))) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by linarith [hL0] : (0 : ℝ) < 2 * (L + 1))]; nlinarith [hL0]
      linarith
    nlinarith [hlow, hLz, rncRadialSq_nonneg z]
  · -- hasymp₀.
    intro δ hδ0 hδ1
    have hdLpos : 0 < δ / (L + 1) := div_pos hδ0 (by linarith [hL0])
    refine ⟨min r (δ / (L + 1)), lt_min hrpos hdLpos, ?_⟩
    intro z hzS hzrsz
    have hzK : z ∈ K := (hSsub hzS).1
    have hznorm : ‖z‖ < r := by
      have := (hSsub hzS).2; rwa [mem_ball_zero_iff] at this
    have hzr₀ : ‖z‖ < r₀ := lt_of_lt_of_le hznorm (min_le_left _ _)
    have hminpos : 0 < min r (δ / (L + 1)) := lt_min hrpos hdLpos
    have hzsq : ‖z‖ ^ 2 ≤ rncRadialSq z := norm_sq_le_rncRadialSq z
    have hzlt : ‖z‖ < min r (δ / (L + 1)) := by
      have h : ‖z‖ ^ 2 < (min r (δ / (L + 1))) ^ 2 := lt_of_le_of_lt hzsq hzrsz
      nlinarith [h, norm_nonneg z, hminpos]
    have hzδ : ‖z‖ < δ / (L + 1) := lt_of_lt_of_le hzlt (min_le_right _ _)
    have hLzδ : L * ‖z‖ ≤ δ := by
      have hstep : L * ‖z‖ ≤ L * (δ / (L + 1)) := mul_le_mul_of_nonneg_left hzδ.le hL0
      have hbound : L * (δ / (L + 1)) ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith [hL0] : (0 : ℝ) < L + 1)]; nlinarith [hδ0, hL0]
      linarith
    obtain ⟨hlow, hup⟩ := hraw z hzK hzr₀
    refine ⟨?_, ?_⟩
    · nlinarith [hlow, hLzδ, rncRadialSq_nonneg z]
    · nlinarith [hup, hLzδ, rncRadialSq_nonneg z]

/-! ### (D5-lite) The concrete L¹ kernel replacement, near-isometry DISCHARGED. -/

/-- **★ D5-lite — `chartW0_l1_sub_plain_of_meas`.**  The concrete L¹ Gaussian kernel replacement
    (`chartGauss_concrete_sub_plain_tendsto`) with the near-isometry BLOCKER (1) DISCHARGED by
    `chartW0_nearIsometry`: for every `S ⊆ K ∩ ball 0 r` the chart-image Gaussian and the plain Gaussian
    are L¹-close as `τ → 0⁺`, given ONLY the honest labelled base-measurability hypothesis `hWmeas₀`
    (blocker (2), see FIREWALL) — the two chart near-isometry inputs are now proved, not assumed. -/
theorem chartW0_l1_sub_plain_of_meas (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ (S : Set (Point n)), S ⊆ K ∩ Metric.ball 0 r → MeasurableSet S →
      (∀ τ : ℝ, AEStronglyMeasurable
          (fun z : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z 0)) (volume.restrict S)) →
      Tendsto (fun τ => ∫ z in S,
          |gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨r, hr, hni⟩ := chartW0_nearIsometry g gi hC hK
  refine ⟨r, hr, ?_⟩
  intro S hSsub hS hWmeas
  obtain ⟨hcoarse, hasymp⟩ := hni S hSsub
  exact chartGauss_concrete_sub_plain_tendsto g gi hC hK S hS hWmeas hcoarse hasymp

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.chartW0_displacement
#print axioms QIQTH.HeatResidualBound.chartW0_rncRadialSq_error
#print axioms QIQTH.HeatResidualBound.chartW0_nearIsometry
#print axioms QIQTH.HeatResidualBound.chartW0_l1_sub_plain_of_meas
