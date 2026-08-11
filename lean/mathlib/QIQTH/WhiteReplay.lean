/-
  WhiteReplay — J4-622: the WHITENED REPLAY — (i) the chart-level identification of the whitened
  pullback metric with the honest `fderiv`-pullback of `whiteExp`, (ii) ★ the replay of the SOLE
  `hframeK` consumer (the pullback-metric-inverse deviation bound) for the whitened family using
  the banked `(δ, 0)` jets — NO `hframeK`, NO `hdevK`, NO `ε₀` — and (iii) the START of the
  whitened `hpkgBound` producer: the diagonal-cleanliness lemma for the whitened chart pair.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; nothing here touches the coefficient VALUE.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still
  owes: the whitened `hpkgBound` COMPLETION (off-diagonal Gaussian domination of the whitened
  witness defect — only the DIAGONAL cleanliness is landed here) + `hEbound`/`hInt` at the
  transport kernel + the `K1TransportBudget` + the fat-`K` carrier piles + the capstone
  co-instantiation at the whitened witness + the prior analytic piles.

  ── ITEM (i): THE CHART-LEVEL IDENTIFICATION.
    • `whitePullbackMetric_eq_fderiv_pullback` — the J4-621 transport-formula DEFINITION
      `ĝ_q(w) = E_qᵀ·g̃_q(E_q w)·E_q` AGREES with the honest `fderiv`-pullback of the whitened
      chart `whiteExp = uniformFlowExp_q ∘ E_q`:
          `ĝ_q(w)ᵢⱼ = ∑_{a,b} g^κ_{ab}(whiteExp_q w) · (D whiteExp_q w · eᵢ)_a · (D whiteExp_q w · eⱼ)_b`
      wherever the flow chart is differentiable at `E_q w` (`‖E_q w‖ <` the uniform flow radius).
      Mechanism: chain rule `D(F ∘ E) = (DF ∘ E)·E` (`fderiv_comp` + `ContinuousLinearMap.fderiv`)
      + the pure `Finset` sum-swap `congr_double_sum_swap` + the symmetry of `E_q`.  So the
      whitened transport formula is NOT an ad-hoc matrix: it IS the pullback metric of the
      whitened chart.  (`…_ball` discharges the radius gate from `‖w‖ < R/(√n+1)`, nonempty.)

  ── ITEM (ii): ★★ THE WHITENED REPLAY OF THE SOLE `hframeK` CONSUMER.
    • `uniformFlowPullbackMetric_dev_uniform_toBase` — the FRAME-FREE forward Taylor bound
      `|g̃_q(v)ᵢⱼ − g(q)ᵢⱼ| ≤ M·‖v‖²` (uniform over `q ∈ K`): the banked replay recentred at the
      true value jet `g̃_q(0) = g(q)` — no frame hypothesis anywhere (value jet
      `uniformFlowPullbackMetric_zero_center`, pd-jet `uniformFlowPullbackMetric_pd_zero_center`,
      uniform C² packet `uniformFlowPullbackMetric_c2_uniform_full`, `decay_order_two`).
    • `whitePullbackMetric_dev_uniform` — the whitened FORWARD deviation from `δ` ITSELF:
      `|ĝ_q(w)ᵢⱼ − δᵢⱼ| ≤ M̂·‖w‖²` for all `q ∈ K` — the `δ`-recentred bound the original
      consumer concluded only under `hframeK`, now with NO frame hypothesis: sandwich
      `ĝ(w) − δ = E_qᵀ·(g̃(E_q w) − g(q))·E_q` (all-`q` whitening identity) + entry contraction
      `|E_q| ≤ 1` + `√n` velocity confinement.
    • ★★ `whitePullbackMetricInv_dev_uniform` — THE REPLAYED CONSUMER:
          `∃ r₀ > 0, ∃ M ≥ 0, ∀ q ∈ K, ∀ ‖w‖ < r₀, ∀ i j, |ĝ⁻¹_q(w)ᵢⱼ − δᵢⱼ| ≤ M·rncRadialSq w`
      — EXACTLY the shape of the banked `uniformFlowPullbackMetricInv_dev_uniform`
      (UniformFlowJetZero.lean:462) with `hframeK` GONE and no `ε₀` floor (contrast the J4-604
      center replay, which pays `+ε₀`): the value jet is exactly `δ` at every whitened row.
      Neumann mechanism self-contained: `‖1 − Â‖ ≤ n·M̂·‖w‖² ≤ 1/2` on a shrunk radius ⟹
      `Â` a unit with `‖Â⁻¹‖ ≤ 2` (geometric series, `isUnit_one_sub_of_norm_lt_one` +
      `tsum_geometric_le_of_norm_lt_one`), then the banked push `Â⁻¹ − 1 = Â⁻¹(1 − Â)`.
      This DISCHARGES the sole `hframeK` consumer for the whitened family — the last frame
      obstacle in the per-`q`-uniform machinery.  (`whitePullbackMetric_neumann` exposes the
      unit + `‖Â⁻¹‖ ≤ 2` package for the downstream `hpkgBound` producer.)

  ── ITEM (iii): THE WHITENED `hpkgBound` PRODUCER — START (diagonal cleanliness).
    • `whitePullbackMetricInv` (definition, mirroring `uniformFlowPullbackMetricInv`) with
      `whitePullbackMetricInv_zero` : `ĝ⁻¹_q(0) = δ` — hence `tr ĝ⁻¹_q(0) = n` by construction.
    • ★ `whiteChart_heatOp_diag_clean` — THE DIAGONAL IS CLEAN: for the whitened chart metric
      pair `(ĝ_q, ĝ⁻¹_q)`, the heat defect of the flat-phase kernel at the chart diagonal is
      EXACTLY ZERO for every `τ > 0` and every row `q ∈ K`:
          `heatOp ĝ_q ĝ⁻¹_q (gaussDdim τ (x−y)) τ 0 0 = ((tr ĝ⁻¹_q(0) − n)/(2τ))·G₀ = 0`
      (the exact diagonal identity `flatPhaseModel_heatOp_diag`, J4-621, instantiated at the
      whitened pair; the `1/τ` coefficient VANISHES).  Contrast gate
      `whiteChart_vs_ambient_diag_gate`: at the SAME genuinely curved witness (`n = 2`,
      `κ = −1`, `q = (1,1)`), the whitened-chart diagonal defect is `0` while the ambient
      flat-phase defect is nonzero (the J4-621 no-go mechanism) — the whitening kills exactly
      the `1/τ` floor that broke the as-built `hpkgBound`.
      ⚠ SCOPE (honest partial): the OFF-diagonal Gaussian domination of the whitened witness
      defect (the `O(1)·G_{2τ}` bound away from the chart origin, and the transfer from the
      chart-side pair to the ambient `heatOp g^κ gi^κ` on the whitened kernel) is NOT here — it
      is the body of the whitened `hpkgBound` producer (J4-623+).

  ── NON-VACUITY (cp466 discipline): `whiteW_genuinely_curved` — at the curved witness the
  whitened Gaussian carries amplitude `√det g^κ(q) = √(5/3) ≠ 1` (`curvedRNC_det_probe`), so the
  whitened objects are GENUINELY curved, not the flat tower in disguise; `whiteReplay_witness_gate`
  — the ★ deviation bound is INSTANTIATED at the genuinely curved fat witness (`n = 2`, `κ = −1`,
  `K = closedBall 0 2`) where the frame change is genuinely non-identity (`whiteVel_nondegenerate`).

  No `sorry`, no `admit`, no new axioms, no `:= True`; no existing file edited except the
  `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.WhiteWitness

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.RNCDecay
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.CurvedA1CenterAmp QIQTH.CurvedA1CenterN1 QIQTH.EquivProbe
open QIQTH.FrozenGauss QIQTH.LeviSeries QIQTH.WhiteWitness
open Set Filter
open scoped Topology BigOperators

namespace QIQTH.WhiteReplay

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ### 0. Small suppliers: entry contraction of the whitening frame (symmetry is the banked
    `QIQTH.EquivProbe.curvedWhitening_symm`). -/

/-- The whitening frame entry is the `i`-th component of the whitened basis velocity:
    `E_q i j = (E_q eⱼ)ᵢ`. -/
theorem curvedWhitening_eq_whiteVel_single (K : ℝ) (q : Point n) (i j : Fin n) :
    whiteVel K q (Pi.single j (1 : ℝ)) i = curvedWhitening K q i j := by
  simp only [whiteVel]
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, mul_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **ENTRY CONTRACTION** (`κ ≤ 0`): every entry of the whitening frame is bounded by `1`,
    `|E_q i j| ≤ 1` — from the banked radial contraction `‖E_q w‖² ≤ ‖w‖²` at `w = eⱼ`. -/
theorem curvedWhitening_entry_abs_le_one (K : ℝ) (hK : K ≤ 0) (q : Point n) (i j : Fin n) :
    |curvedWhitening K q i j| ≤ 1 := by
  have hsingle : rncRadialSq (Pi.single j (1 : ℝ) : Point n) = 1 := by
    show (∑ k, (Pi.single j (1 : ℝ) : Point n) k ^ 2) = 1
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]; norm_num
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]; norm_num
    · intro h; exact absurd (Finset.mem_univ j) h
  have hcontr : rncRadialSq (whiteVel K q (Pi.single j (1 : ℝ))) ≤ 1 := by
    have h := whiteVel_radialSq_le K hK q (Pi.single j (1 : ℝ))
    rwa [hsingle] at h
  have hsq : (curvedWhitening K q i j) ^ 2 ≤ 1 := by
    have h1 : (whiteVel K q (Pi.single j (1 : ℝ)) i) ^ 2
        ≤ ∑ k, (whiteVel K q (Pi.single j (1 : ℝ)) k) ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : (∑ k, (whiteVel K q (Pi.single j (1 : ℝ)) k) ^ 2)
        = rncRadialSq (whiteVel K q (Pi.single j (1 : ℝ))) := rfl
    rw [← curvedWhitening_eq_whiteVel_single K q i j]
    calc (whiteVel K q (Pi.single j (1 : ℝ)) i) ^ 2
        ≤ rncRadialSq (whiteVel K q (Pi.single j (1 : ℝ))) := by rw [← h2]; exact h1
      _ ≤ 1 := hcontr
  nlinarith [sq_abs (curvedWhitening K q i j), abs_nonneg (curvedWhitening K q i j)]

/-! ### 1. Item (ii), step 1 — the FRAME-FREE forward Taylor bound recentred at the base value. -/

/-- **The frame-free forward deviation at the base value** — ONE radius `r₀ > 0`, ONE constant
    `M ≥ 0` with `|g̃_q(v)ᵢⱼ − g(q)ᵢⱼ| ≤ M·‖v‖²` for every `q ∈ K`, `‖v‖ ≤ r₀`.  The banked
    Taylor replay (`decay_order_two` + the uniform C² packet) recentred at the TRUE value jet
    `g̃_q(0) = g(q)` (`uniformFlowPullbackMetric_zero_center`) with the frame-free pd-jet
    (`uniformFlowPullbackMetric_pd_zero_center`) — NO frame hypothesis anywhere.
    NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetric_dev_uniform_toBase (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ r₀ → ∀ i j : Fin n,
      |uniformFlowPullbackMetric g gi hC hK q v i j - g q i j| ≤ M * ‖v‖ ^ 2 := by
  obtain ⟨r₀, hr₀0, M, hpk⟩ := uniformFlowPullbackMetric_c2_uniform_full g gi hg hC hK
  refine ⟨r₀ / 2, by positivity, max 0 M, le_max_left _ _, ?_⟩
  intro q hq v hv i j
  have hjetpd : ∀ e, pd (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) e
      (0 : Point n) = 0 :=
    fun e => uniformFlowPullbackMetric_pd_zero_center g gi hC hK hg hgsymm hinvF q hq i j e
  set f : Point n → ℝ :=
    fun w => uniformFlowPullbackMetric g gi hC hK q w i j
      - uniformFlowPullbackMetric g gi hC hK q 0 i j with hf
  have hballs : ∀ w : Point n, w ∈ Metric.closedBall (0 : Point n) (r₀ / 2) → ‖w‖ < r₀ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    linarith
  have hfd_eq : fderiv ℝ f
      = fderiv ℝ (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) := by
    funext w
    exact fderiv_sub_const _
  have hf0 : f 0 = 0 := by rw [hf]; simp
  have h0mem : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀0
  have hdf0 : fderiv ℝ f 0 = 0 := by
    rw [hfd_eq]
    exact fderiv_zero_of_pd_zero ((hpk q hq 0 h0mem i j).1.differentiableAt) hjetpd
  have hdiff : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2), DifferentiableAt ℝ f w := by
    intro w hw
    exact ((hpk q hq w (hballs w hw) i j).1.differentiableAt).sub (differentiableAt_const _)
  have hdiff2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2),
      DifferentiableAt ℝ (fderiv ℝ f) w := by
    intro w hw
    rw [hfd_eq]
    exact (hpk q hq w (hballs w hw) i j).2.1.differentiableAt
  have hbound2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2),
      ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ max 0 M := by
    intro w hw
    rw [hfd_eq]
    exact le_trans (hpk q hq w (hballs w hw) i j).2.2.2.2 (le_max_right _ _)
  have hdecay := decay_order_two f (max 0 M) (r₀ / 2) (by positivity)
    hf0 hdf0 hdiff hdiff2 hbound2 hv
  have h0 : uniformFlowPullbackMetric g gi hC hK q 0 i j = g q i j :=
    uniformFlowPullbackMetric_zero_center g gi hC hK q hq i j
  rw [← h0]
  exact hdecay

/-! ### 2. Item (ii), step 2 — the whitened FORWARD deviation from `δ`, NO frame hypothesis. -/

/-- **★ The whitened forward deviation** — `|ĝ_q(w)ᵢⱼ − δᵢⱼ| ≤ M̂·‖w‖²` uniformly over `q ∈ K`,
    with NO `hframeK`, NO `hdevK`, NO `ε₀`: sandwich
    `ĝ(w) − δ = E_qᵀ·(g̃_q(E_q w) − g^κ(q))·E_q` (the all-`q` whitening identity
    `curvedRNC_whitening_all` collapses the constant term to `δ` EXACTLY), the frame-free base
    bound `uniformFlowPullbackMetric_dev_uniform_toBase` at `v = E_q w`, entry contraction
    `|E_q| ≤ 1` and the `√n` velocity confinement.  NOT `a₁ = R/6`. -/
theorem whitePullbackMetric_dev_uniform (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ Kset, ∀ w : Point n, ‖w‖ ≤ r₀ → ∀ i j : Fin n,
      |whitePullbackMetric κ hκ hKc q w i j - (if i = j then (1 : ℝ) else 0)|
        ≤ M * ‖w‖ ^ 2 := by
  obtain ⟨r₀, hr₀0, M, hM0, hdev⟩ :=
    uniformFlowPullbackMetric_dev_uniform_toBase (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (fun y a b => curvedRNCMetric_symm κ y a b)
      (fun y a b => curvedRNCMetric_hinvF κ hκ y a b)
  have hsn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  refine ⟨r₀ / (Real.sqrt n + 1), by positivity,
    ((n : ℝ) * n) * (M * n), by positivity, ?_⟩
  intro q hq w hw i j
  -- velocity confinement into the base radius
  have hEw : ‖whiteVel κ q w‖ ≤ r₀ := by
    have h1 := whiteVel_norm_le κ hκ q w
    have h2 : Real.sqrt n * ‖w‖ ≤ Real.sqrt n * (r₀ / (Real.sqrt n + 1)) :=
      mul_le_mul_of_nonneg_left hw hsn
    have h3 : Real.sqrt n * (r₀ / (Real.sqrt n + 1)) ≤ r₀ := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hr₀0.le]
    linarith
  -- the squared velocity budget
  have hEwsq : ‖whiteVel κ q w‖ ^ 2 ≤ (n : ℝ) * ‖w‖ ^ 2 := by
    have h5 : ‖whiteVel κ q w‖ * ‖whiteVel κ q w‖
        ≤ (Real.sqrt n * ‖w‖) * (Real.sqrt n * ‖w‖) :=
      mul_self_le_mul_self (norm_nonneg _) (whiteVel_norm_le κ hκ q w)
    have h6 : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    nlinarith [h5, h6]
  -- the exact sandwich
  have hdiffE : whitePullbackMetric κ hκ hKc q w i j - (if i = j then (1 : ℝ) else 0)
      = ∑ k, ∑ l, curvedWhitening κ q i k
          * (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l - curvedRNCMetric κ q k l)
          * curvedWhitening κ q l j := by
    rw [show (if i = j then (1 : ℝ) else 0)
        = ∑ k, ∑ l, curvedWhitening κ q i k * curvedRNCMetric κ q k l * curvedWhitening κ q l j
      from (curvedRNC_whitening_all κ hκ q i j).symm]
    simp only [whitePullbackMetric]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hdiffE]
  -- the entrywise bound
  have hterm : ∀ k l : Fin n,
      |curvedWhitening κ q i k
        * (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l - curvedRNCMetric κ q k l)
        * curvedWhitening κ q l j|
      ≤ M * ((n : ℝ) * ‖w‖ ^ 2) := by
    intro k l
    have hd : |uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l - curvedRNCMetric κ q k l|
        ≤ M * ‖whiteVel κ q w‖ ^ 2 := hdev q hq (whiteVel κ q w) hEw k l
    have hd2 : M * ‖whiteVel κ q w‖ ^ 2 ≤ M * ((n : ℝ) * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hEwsq hM0
    have hE1 := curvedWhitening_entry_abs_le_one κ hκ q i k
    have hE2 := curvedWhitening_entry_abs_le_one κ hκ q l j
    rw [abs_mul, abs_mul]
    calc |curvedWhitening κ q i k|
          * |uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l - curvedRNCMetric κ q k l|
          * |curvedWhitening κ q l j|
        ≤ 1 * (M * ((n : ℝ) * ‖w‖ ^ 2)) * 1 := by
          have hmid := le_trans hd hd2
          have h1 : |curvedWhitening κ q i k|
              * |uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
                  (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l
                  - curvedRNCMetric κ q k l|
              ≤ 1 * (M * ((n : ℝ) * ‖w‖ ^ 2)) :=
            mul_le_mul hE1 hmid (abs_nonneg _) zero_le_one
          exact mul_le_mul h1 hE2 (abs_nonneg _) (by positivity)
      _ = M * ((n : ℝ) * ‖w‖ ^ 2) := by ring
  calc |∑ k, ∑ l, curvedWhitening κ q i k
        * (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l - curvedRNCMetric κ q k l)
        * curvedWhitening κ q l j|
      ≤ ∑ k, |∑ l, curvedWhitening κ q i k
          * (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l - curvedRNCMetric κ q k l)
          * curvedWhitening κ q l j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ l, |curvedWhitening κ q i k
          * (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l - curvedRNCMetric κ q k l)
          * curvedWhitening κ q l j| :=
        Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, ∑ _l : Fin n, M * ((n : ℝ) * ‖w‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
    _ = ((n : ℝ) * n) * (M * n) * ‖w‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### 3. Item (ii), step 3 — the Neumann package and ★ the replayed consumer. -/

/-- The whitened pullback INVERSE metric — mirror of `uniformFlowPullbackMetricInv`:
    the `(i,j)` entry of the operator inverse of `matToCLM ĝ_q(w)`. -/
noncomputable def whitePullbackMetricInv (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q w : Point n) (i j : Fin n) : ℝ :=
  (Ring.inverse (matToCLM (fun a b => whitePullbackMetric κ hκ hKc q w a b)))
    (Pi.single j (1 : ℝ)) i

/-- **The whitened Neumann package** — ONE radius `r₀ > 0` and ONE constant `M ≥ 0` with, for
    every `q ∈ K` and `‖w‖ < r₀`: the forward deviation `|ĝ(w) − δ| ≤ M·‖w‖²`, `matToCLM ĝ(w)`
    a UNIT, and `‖(matToCLM ĝ(w))⁻¹‖ ≤ 2`.  Self-contained Neumann: `‖1 − Â‖ ≤ n·M·‖w‖² ≤ 1/2`
    on the shrunk radius, then the geometric series.  NO frame hypothesis.  NOT `a₁ = R/6`. -/
theorem whitePullbackMetric_neumann (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ Kset, ∀ w : Point n, ‖w‖ < r₀ →
      (∀ i j : Fin n, |whitePullbackMetric κ hκ hKc q w i j - (if i = j then (1 : ℝ) else 0)|
          ≤ M * ‖w‖ ^ 2)
      ∧ IsUnit (matToCLM (fun a b => whitePullbackMetric κ hκ hKc q w a b))
      ∧ ‖Ring.inverse (matToCLM (fun a b => whitePullbackMetric κ hκ hKc q w a b))‖ ≤ 2 := by
  obtain ⟨r₁, hr₁0, M, hM0, hdev⟩ := whitePullbackMetric_dev_uniform κ hκ hKc
  set c : ℝ := (n : ℝ) * M + 1 with hc
  have hc0 : (0 : ℝ) < c := by positivity
  refine ⟨min r₁ (Real.sqrt (1 / (2 * c))), lt_min hr₁0 (Real.sqrt_pos.mpr (by positivity)),
    M, hM0, ?_⟩
  intro q hq w hw
  have hw1 : ‖w‖ ≤ r₁ := le_of_lt (lt_of_lt_of_le hw (min_le_left _ _))
  have hw2 : ‖w‖ < Real.sqrt (1 / (2 * c)) := lt_of_lt_of_le hw (min_le_right _ _)
  have hdev' := hdev q hq w hw1
  refine ⟨hdev', ?_⟩
  set A : Point n →L[ℝ] Point n :=
    matToCLM (fun a b => whitePullbackMetric κ hκ hKc q w a b) with hA
  set D : Point n →L[ℝ] Point n := 1 - A with hD
  -- the operator-norm bound on the defect `1 − Â`
  have hDnorm : ‖D‖ ≤ (n : ℝ) * M * ‖w‖ ^ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    have hDx : (D x) i = ∑ jj, ((if i = jj then (1 : ℝ) else 0)
        - whitePullbackMetric κ hκ hKc q w i jj) * x jj := by
      rw [hD, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, Pi.sub_apply,
        hA, matToCLM_apply]
      rw [show x i = ∑ jj, (if i = jj then (1 : ℝ) else 0) * x jj by
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun jj _ => by ring
    rw [Real.norm_eq_abs, hDx]
    calc |∑ jj, ((if i = jj then (1 : ℝ) else 0)
          - whitePullbackMetric κ hκ hKc q w i jj) * x jj|
        ≤ ∑ jj, |((if i = jj then (1 : ℝ) else 0)
            - whitePullbackMetric κ hκ hKc q w i jj) * x jj| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _jj : Fin n, M * ‖w‖ ^ 2 * ‖x‖ := by
          refine Finset.sum_le_sum fun jj _ => ?_
          rw [abs_mul, abs_sub_comm]
          have h1 := hdev' i jj
          have h2 : |x jj| ≤ ‖x‖ := by
            have := norm_le_pi_norm x jj
            simpa [Real.norm_eq_abs] using this
          exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = (n : ℝ) * M * ‖w‖ ^ 2 * ‖x‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- the half bound on the shrunk radius
  have hwsq : ‖w‖ ^ 2 < 1 / (2 * c) := by
    have h1 : ‖w‖ * ‖w‖ < Real.sqrt (1 / (2 * c)) * Real.sqrt (1 / (2 * c)) :=
      mul_self_lt_mul_self (norm_nonneg w) hw2
    have h2 : Real.sqrt (1 / (2 * c)) * Real.sqrt (1 / (2 * c)) = 1 / (2 * c) :=
      Real.mul_self_sqrt (by positivity)
    nlinarith [h1, h2]
  have hhalf : (n : ℝ) * M * ‖w‖ ^ 2 ≤ 1 / 2 := by
    have h1 : (n : ℝ) * M * ‖w‖ ^ 2 ≤ c * ‖w‖ ^ 2 := by
      have : (n : ℝ) * M ≤ c := by rw [hc]; linarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have h2 : c * ‖w‖ ^ 2 ≤ c * (1 / (2 * c)) :=
      mul_le_mul_of_nonneg_left hwsq.le hc0.le
    have h3 : c * (1 / (2 * c)) = 1 / 2 := by
      rw [mul_one_div, mul_comm 2 c, ← div_div, div_self hc0.ne']
    linarith
  have hD12 : ‖D‖ ≤ 1 / 2 := le_trans hDnorm hhalf
  have hDlt : ‖D‖ < 1 := lt_of_le_of_lt hD12 (by norm_num)
  have hAeq : A = 1 - D := by rw [hD]; exact (sub_sub_cancel 1 A).symm
  have hU : IsUnit A := by
    rw [hAeq]
    exact isUnit_one_sub_of_norm_lt_one hDlt
  refine ⟨hU, ?_⟩
  have hgeom : Ring.inverse A = ∑' m : ℕ, D ^ m := by
    rw [hAeq]
    exact (geom_series_eq_inverse D hDlt).symm
  rw [hgeom]
  refine le_trans (tsum_geometric_le_of_norm_lt_one D hDlt) ?_
  have h1 : ‖(1 : Point n →L[ℝ] Point n)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le
  have h2 : (1 - ‖D‖)⁻¹ ≤ 2 := by
    have hpos : (0 : ℝ) < 1 / 2 := by norm_num
    have hle : (1 : ℝ) / 2 ≤ 1 - ‖D‖ := by linarith
    have := one_div_le_one_div_of_le hpos hle
    rw [inv_eq_one_div]
    calc 1 / (1 - ‖D‖) ≤ 1 / (1 / 2) := this
      _ = 2 := by norm_num
  linarith

/-- **★★ J4-622 capstone — the WHITENED replay of the sole `hframeK` consumer.**  EXACTLY the
    shape of the banked `uniformFlowPullbackMetricInv_dev_uniform` (UniformFlowJetZero.lean:462)
    for the whitened family, with `hframeK` GONE and NO `ε₀` floor (contrast the J4-604 center
    replay `uniformFlowPullbackMetricInv_dev_uniform_center`, which pays `+ε₀`):
        `∃ r₀ > 0, ∃ M ≥ 0, ∀ q ∈ K, ∀ ‖w‖ < r₀, ∀ i j,
            |ĝ⁻¹_q(w)ᵢⱼ − δᵢⱼ| ≤ M · rncRadialSq w`.
    The value jet of the whitened chart is EXACTLY `δ` at every row (`whitePullbackMetric_zero`),
    so the replay is CLEANER than the center version — no frame deviation to carry.  Neumann push
    `Â⁻¹ − 1 = Â⁻¹(1 − Â)` (banked mechanism) with the self-contained unit/norm package
    `whitePullbackMetric_neumann`.  This discharges the LAST frame obstacle of the
    per-`q`-uniform machinery for the whitened witness.  NOT `a₁ = R/6`. -/
theorem whitePullbackMetricInv_dev_uniform (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ Kset, ∀ w : Point n, ‖w‖ < r₀ → ∀ i j : Fin n,
      |whitePullbackMetricInv κ hκ hKc q w i j - (if i = j then (1 : ℝ) else 0)|
        ≤ M * rncRadialSq w := by
  obtain ⟨r₀, hr₀0, M, hM0, hpkg⟩ := whitePullbackMetric_neumann κ hκ hKc
  refine ⟨r₀, hr₀0, 2 * M, by positivity, ?_⟩
  intro q hq w hw i j
  obtain ⟨hdev', hU, hn2⟩ := hpkg q hq w hw
  set A : Point n →L[ℝ] Point n :=
    matToCLM (fun a b => whitePullbackMetric κ hκ hKc q w a b) with hA
  -- entries of `(1 − Â)e_j` are the forward deviations.
  have hzk : ∀ k : Fin n, ((1 - A) (Pi.single j (1 : ℝ))) k
      = (if k = j then (1 : ℝ) else 0) - whitePullbackMetric κ hκ hKc q w k j := by
    intro k
    have hAw : (A (Pi.single j (1 : ℝ))) k = whitePullbackMetric κ hκ hKc q w k j := by
      rw [hA, matToCLM_apply]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, Pi.sub_apply, hAw,
      Pi.single_apply]
  have hznorm : ‖(1 - A) (Pi.single j (1 : ℝ))‖ ≤ M * ‖w‖ ^ 2 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    rw [Real.norm_eq_abs, hzk k, abs_sub_comm]
    exact hdev' k j
  -- the entry deviation IS the `i`-th coordinate of `Â⁻¹((1−Â)e_j)`.
  have hmain : whitePullbackMetricInv κ hκ hKc q w i j - (if i = j then (1 : ℝ) else 0)
      = ((Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))) i := by
    have hRA : Ring.inverse A ((1 - A) (Pi.single j (1 : ℝ)))
        = Ring.inverse A (Pi.single j (1 : ℝ)) - Pi.single j (1 : ℝ) := by
      have h1 : (1 - A) (Pi.single j (1 : ℝ))
          = Pi.single j (1 : ℝ) - A (Pi.single j (1 : ℝ)) := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
      have h2 : Ring.inverse A (A (Pi.single j (1 : ℝ))) = Pi.single j (1 : ℝ) := by
        rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hU,
          ContinuousLinearMap.one_apply]
      rw [h1, map_sub, h2]
    rw [hRA, Pi.sub_apply, Pi.single_apply]
    simp only [whitePullbackMetricInv, hA]
  rw [hmain]
  have hsq : ‖w‖ ^ 2 ≤ rncRadialSq w := by
    rw [← rncRadial_sq]
    nlinarith [norm_le_rncRadial w, norm_nonneg w, rncRadial_nonneg w]
  calc |((Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))) i|
      = ‖((Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))) i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖(Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))‖ := norm_le_pi_norm _ i
    _ ≤ ‖Ring.inverse A‖ * ‖(1 - A) (Pi.single j (1 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 2 * (M * ‖w‖ ^ 2) := mul_le_mul hn2 hznorm (norm_nonneg _) (by norm_num)
    _ ≤ 2 * M * rncRadialSq w := by
        have h1 : 2 * (M * ‖w‖ ^ 2) = 2 * M * ‖w‖ ^ 2 := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-! ### 4. Item (iii) — the whitened `hpkgBound` producer START: diagonal cleanliness. -/

/-- **The whitened inverse value jet**: `ĝ⁻¹_q(0) = δ` at every `q ∈ K` — since `ĝ_q(0) = δ`
    EXACTLY (`whitePullbackMetric_zero`), the operator is the identity and `Ring.inverse 1 = 1`.
    Hence `tr ĝ⁻¹_q(0) = n` BY CONSTRUCTION — the diagonal-cleanliness input. -/
theorem whitePullbackMetricInv_zero (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (i j : Fin n) :
    whitePullbackMetricInv κ hκ hKc q 0 i j = if i = j then (1 : ℝ) else 0 := by
  have hmat : (fun a b => whitePullbackMetric κ hκ hKc q 0 a b)
      = ((1 : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → ℝ) := by
    funext a b
    rw [whitePullbackMetric_zero κ hκ hKc q hq a b, Matrix.one_apply]
  simp only [whitePullbackMetricInv]
  rw [hmat, matToCLM_one, Ring.inverse_one, ContinuousLinearMap.one_apply, Pi.single_apply]

/-- **★ J4-622 item (iii) — THE DIAGONAL IS CLEAN.**  For the whitened chart metric pair
    `(ĝ_q, ĝ⁻¹_q)`, the heat defect of the flat-phase kernel at the chart diagonal is EXACTLY
    ZERO at every `τ > 0` and every row `q ∈ K`:
        `heatOp ĝ_q ĝ⁻¹_q (gaussDdim τ (x − y)) τ 0 0
           = ((tr ĝ⁻¹_q(0) − n)/(2τ)) · gaussDdim τ 0 = 0` —
    the EXACT diagonal identity (`flatPhaseModel_heatOp_diag`, J4-621, valid for ANY metric
    pair) instantiated at the whitened pair, where `tr ĝ⁻¹_q(0) = n` BY CONSTRUCTION
    (`whitePullbackMetricInv_zero`).  The `1/τ` diagonal floor that broke the as-built
    `hpkgBound` (`flatPhase_hpkgBound_fails`) VANISHES for the whitened chart.  This is the
    diagonal layer of the whitened `hpkgBound` producer; the OFF-diagonal Gaussian domination
    is the labelled J4-623+ residue.  NOT `a₁ = R/6`. -/
theorem whiteChart_heatOp_diag_clean (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (τ : ℝ) (hτ : 0 < τ) :
    heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
      (fun w => whitePullbackMetricInv κ hκ hKc q w)
      (fun t x y => flatPhaseModel t x y) τ (0 : Point n) (0 : Point n) = 0 := by
  rw [flatPhaseModel_heatOp_diag (fun w => whitePullbackMetric κ hκ hKc q w)
    (fun w => whitePullbackMetricInv κ hκ hKc q w) τ hτ (0 : Point n)]
  have htr : (∑ i, whitePullbackMetricInv κ hκ hKc q 0 i i) = (n : ℝ) := by
    rw [Finset.sum_congr rfl fun i _ => whitePullbackMetricInv_zero κ hκ hKc q hq i i]
    simp
  rw [htr]
  simp

/-! ### 5. Non-vacuity / adversarial gates (cp466 discipline). -/

/-- The determinant of the curved witness metric at the genuinely curved off-center row
    (`n = 2`, `κ = −1`, `q = (1,1)`): `det g^κ(q) = 5/3 ≠ 1` — the whitened amplitude is
    genuinely non-flat. -/
theorem curvedRNC_det_probe :
    Matrix.det (curvedRNCMetric (-1 : ℝ) probeQ) = 5 / 3 := by
  have hr2 : rncRadialSq probeQ = 2 := by
    simp [rncRadialSq, probeQ]
  rw [Matrix.det_fin_two]
  have h00 : curvedRNCMetric (-1 : ℝ) probeQ 0 0 = 4 / 3 := by
    simp only [curvedRNCMetric, hr2, probeQ]
    norm_num
  have h01 : curvedRNCMetric (-1 : ℝ) probeQ 0 1 = -(1 / 3) := by
    simp only [curvedRNCMetric, hr2, probeQ]
    norm_num
  have h10 : curvedRNCMetric (-1 : ℝ) probeQ 1 0 = -(1 / 3) := by
    simp only [curvedRNCMetric, hr2, probeQ]
    norm_num
  have h11 : curvedRNCMetric (-1 : ℝ) probeQ 1 1 = 4 / 3 := by
    simp only [curvedRNCMetric, hr2, probeQ]
    norm_num
  show curvedRNCMetric (-1 : ℝ) probeQ 0 0 * curvedRNCMetric (-1 : ℝ) probeQ 1 1
      - curvedRNCMetric (-1 : ℝ) probeQ 0 1 * curvedRNCMetric (-1 : ℝ) probeQ 1 0 = 5 / 3
  rw [h00, h01, h10, h11]
  norm_num

/-- **Non-vacuity: the whitened Gaussian is GENUINELY curved** at the off-center witness —
    its amplitude is `√(5/3) ≠ 1`, so `whiteW ≠ gaussDdim`: the whitened objects are not the
    flat tower in disguise. -/
theorem whiteW_genuinely_curved (τ : ℝ) (hτ : 0 < τ) (w : Point 2) :
    whiteW (-1 : ℝ) probeQ τ w ≠ gaussDdim τ w := by
  rw [whiteW_eq_det_mul_gaussDdim (-1 : ℝ) (by norm_num) probeQ τ w]
  intro h
  have hG : 0 < gaussDdim τ w := gaussDdim_pos τ hτ w
  have hamp : Real.sqrt (Matrix.det (curvedRNCMetric (-1 : ℝ) probeQ)) = 1 := by
    have h1 : Real.sqrt (Matrix.det (curvedRNCMetric (-1 : ℝ) probeQ)) * gaussDdim τ w
        = 1 * gaussDdim τ w := by rw [h, one_mul]
    exact mul_right_cancel₀ hG.ne' h1
  rw [curvedRNC_det_probe] at hamp
  have h53 : (5 : ℝ) / 3 = 1 := Real.sqrt_eq_one.mp hamp
  norm_num at h53

/-- **★ The witness gate for the replayed consumer**: at the genuinely curved fat witness
    (`n = 2`, `κ = −1`, `K = closedBall 0 2` — containing the off-center row `q = (1,1)` where
    the frame change is genuinely non-identity, `whiteVel_nondegenerate`), the whitened inverse
    deviation bound HOLDS with no frame hypothesis, AND the whitened-chart diagonal defect is
    ZERO while the ambient flat-phase defect at the same row is NONZERO (the J4-621 no-go
    mechanism) — the whitening kills exactly the `1/τ` floor.  NOT `a₁ = R/6`. -/
theorem whiteReplay_witness_gate (τ : ℝ) (hτ : 0 < τ) :
    (∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧
      ∀ q ∈ Metric.closedBall (0 : Point 2) 2, ∀ w : Point 2, ‖w‖ < r₀ → ∀ i j : Fin 2,
        |whitePullbackMetricInv (-1 : ℝ) (by norm_num)
            (isCompact_closedBall (0 : Point 2) 2) q w i j - (if i = j then (1 : ℝ) else 0)|
          ≤ M * rncRadialSq w)
    ∧ heatOp (fun w => whitePullbackMetric (-1 : ℝ) (by norm_num)
          (isCompact_closedBall (0 : Point 2) 2) probeQ w)
        (fun w => whitePullbackMetricInv (-1 : ℝ) (by norm_num)
          (isCompact_closedBall (0 : Point 2) 2) probeQ w)
        (fun t x y => flatPhaseModel t x y) τ (0 : Point 2) (0 : Point 2) = 0
    ∧ heatOp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
        (fun t x y => flatPhaseModel t x y) τ probeQ probeQ ≠ 0
    ∧ whiteVel (-1 : ℝ) probeQ probeW 0 ≠ probeW 0 :=
  ⟨whitePullbackMetricInv_dev_uniform (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2),
    whiteChart_heatOp_diag_clean (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) probeQ probeQ_mem_ball τ hτ,
    flatPhaseModel_heatOp_diag_ne_zero (-1 : ℝ) (by norm_num) le_rfl probeQ probeQ_ne_zero τ hτ,
    whiteVel_nondegenerate⟩

/-! ### 6. Item (i) — the chart-level identification. -/

/-- **The pure `Finset` sum swap of a congruence**: the double-sum congruence with expanded
    columns equals the transported double sum — the combinatorial core of the chart-level
    identification, isolated from the analysis. -/
theorem congr_double_sum_swap (G J : Fin n → Fin n → ℝ) (Ei Ej : Fin n → ℝ) :
    (∑ a, ∑ b, G a b * (∑ k, Ei k * J a k) * (∑ l, Ej l * J b l))
      = ∑ k, ∑ l, Ei k * (∑ a, ∑ b, G a b * J a k * J b l) * Ej l := by
  have hL : ∀ a b : Fin n, G a b * (∑ k, Ei k * J a k) * (∑ l, Ej l * J b l)
      = ∑ k, ∑ l, G a b * J a k * J b l * Ei k * Ej l := by
    intro a b
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hR : ∀ k l : Fin n, Ei k * (∑ a, ∑ b, G a b * J a k * J b l) * Ej l
      = ∑ a, ∑ b, G a b * J a k * J b l * Ei k * Ej l := by
    intro k l
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hL a b]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
    Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hR k l]
  -- exchange `Σ_a Σ_b Σ_k Σ_l = Σ_k Σ_l Σ_a Σ_b`
  calc (∑ a, ∑ b, ∑ k, ∑ l, G a b * J a k * J b l * Ei k * Ej l)
      = ∑ a, ∑ k, ∑ b, ∑ l, G a b * J a k * J b l * Ei k * Ej l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, ∑ l, G a b * J a k * J b l * Ei k * Ej l := Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ l, ∑ b, G a b * J a k * J b l * Ei k * Ej l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, G a b * J a k * J b l * Ei k * Ej l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- **★ J4-622 item (i) — the CHART-LEVEL IDENTIFICATION.**  The J4-621 transport-formula
    definition `ĝ_q(w) = E_qᵀ·g̃_q(E_q w)·E_q` AGREES with the honest `fderiv`-pullback of the
    whitened chart `whiteExp = uniformFlowExp_q ∘ E_q` wherever the flow chart is `C²` at the
    whitened velocity (`‖E_q w‖ <` the uniform flow radius):
        `ĝ_q(w)ᵢⱼ = ∑_{a,b} g^κ_{ab}(whiteExp_q w)·(D whiteExp_q w · eᵢ)_a·(D whiteExp_q w · eⱼ)_b`.
    Chain rule `D(F∘E) = (DF∘E)·E` + `congr_double_sum_swap` + symmetry of `E_q`.
    NOT `a₁ = R/6`. -/
theorem whitePullbackMetric_eq_fderiv_pullback (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (w : Point n)
    (hw : ‖whiteVel κ q w‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc) (i j : Fin n) :
    whitePullbackMetric κ hκ hKc q w i j
      = ∑ a, ∑ b, curvedRNCMetric κ (whiteExp κ hκ hKc q w) a b
          * (fderiv ℝ (whiteExp κ hκ hKc q) w) (Pi.single i 1) a
          * (fderiv ℝ (whiteExp κ hκ hKc q) w) (Pi.single j 1) b := by
  classical
  set F : Point n → Point n :=
    uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q with hF
  set E : Point n →L[ℝ] Point n := matToCLM (curvedWhitening κ q) with hE
  have hEfun : ∀ v : Point n, E v = whiteVel κ q v := by
    intro v; funext k
    rw [hE, matToCLM_apply]
    rfl
  have hcomp : whiteExp κ hκ hKc q = F ∘ ⇑E := by
    funext v
    rw [Function.comp_apply, hEfun v]
    rfl
  have hdiffF : DifferentiableAt ℝ F (E w) := by
    rw [hEfun w]
    exact (contDiffAt2_uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q hq (whiteVel κ q w) hw).differentiableAt (by norm_num)
  have hfd : fderiv ℝ (whiteExp κ hκ hKc q) w = (fderiv ℝ F (E w)).comp E := by
    rw [hcomp]
    rw [fderiv_comp w hdiffF (E.differentiableAt)]
    rw [E.fderiv]
  -- the whitened basis image `E eₛ = (E_q)_{·s}` and its basis decomposition
  have hEs : ∀ s : Fin n, E (Pi.single s (1 : ℝ)) = fun k => curvedWhitening κ q k s := by
    intro s; funext k
    rw [hE, matToCLM_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hdecomp : ∀ s : Fin n, (fun k => curvedWhitening κ q k s)
      = ∑ m : Fin n, curvedWhitening κ q m s • Pi.single m (1 : ℝ) := by
    intro s; funext k
    rw [Finset.sum_apply]
    have hterm : ∀ m : Fin n, (curvedWhitening κ q m s • Pi.single m (1 : ℝ)) k
        = if k = m then curvedWhitening κ q m s else 0 := by
      intro m
      by_cases h : k = m
      · subst h; simp
      · simp [h]
    rw [Finset.sum_congr rfl fun m _ => hterm m,
      Finset.sum_ite_eq Finset.univ k fun m => curvedWhitening κ q m s]
    simp
  have happ : ∀ (s : Fin n) (a : Fin n),
      (fderiv ℝ (whiteExp κ hκ hKc q) w) (Pi.single s 1) a
        = ∑ m, curvedWhitening κ q m s * (fderiv ℝ F (E w)) (Pi.single m 1) a := by
    intro s a
    rw [hfd, ContinuousLinearMap.comp_apply, hEs s, hdecomp s, map_sum]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
  -- assemble
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => by rw [happ i a, happ j b]]
  rw [congr_double_sum_swap
    (fun a b => curvedRNCMetric κ (whiteExp κ hκ hKc q w) a b)
    (fun a m => (fderiv ℝ F (E w)) (Pi.single m 1) a)
    (fun m => curvedWhitening κ q m i) (fun m => curvedWhitening κ q m j)]
  have hEw : E w = whiteVel κ q w := hEfun w
  simp only [whitePullbackMetric, whiteExp_eq, hEw, hF, uniformFlowPullbackMetric]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [curvedWhitening_symm κ q i k]

/-- **The radius-gated corollary**: the identification holds on the concrete shrunk ball
    `‖w‖ < R/(√n + 1)` (nonempty, `uniformFlowRadius_pos`), via the `√n` confinement. -/
theorem whitePullbackMetric_eq_fderiv_pullback_ball (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (w : Point n)
    (hw : ‖w‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc / (Real.sqrt n + 1)) (i j : Fin n) :
    whitePullbackMetric κ hκ hKc q w i j
      = ∑ a, ∑ b, curvedRNCMetric κ (whiteExp κ hκ hKc q w) a b
          * (fderiv ℝ (whiteExp κ hκ hKc q) w) (Pi.single i 1) a
          * (fderiv ℝ (whiteExp κ hκ hKc q) w) (Pi.single j 1) b := by
  refine whitePullbackMetric_eq_fderiv_pullback κ hκ hKc q hq w ?_ i j
  have hsn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  set R : ℝ := uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc with hR
  have h1 : ‖whiteVel κ q w‖ ≤ Real.sqrt n * ‖w‖ := whiteVel_norm_le κ hκ q w
  have h2 : Real.sqrt n * ‖w‖ ≤ (Real.sqrt n + 1) * ‖w‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg w)
  have h3 : (Real.sqrt n + 1) * ‖w‖ < (Real.sqrt n + 1) * (R / (Real.sqrt n + 1)) :=
    mul_lt_mul_of_pos_left hw (by positivity)
  have h4 : (Real.sqrt n + 1) * (R / (Real.sqrt n + 1)) = R := by
    field_simp
  linarith

end QIQTH.WhiteReplay

section AxiomChecks
open QIQTH.WhiteReplay
#print axioms QIQTH.WhiteReplay.curvedWhitening_entry_abs_le_one
#print axioms QIQTH.WhiteReplay.uniformFlowPullbackMetric_dev_uniform_toBase
#print axioms QIQTH.WhiteReplay.whitePullbackMetric_dev_uniform
#print axioms QIQTH.WhiteReplay.whitePullbackMetric_neumann
#print axioms QIQTH.WhiteReplay.whitePullbackMetricInv_dev_uniform
#print axioms QIQTH.WhiteReplay.whitePullbackMetricInv_zero
#print axioms QIQTH.WhiteReplay.whiteChart_heatOp_diag_clean
#print axioms QIQTH.WhiteReplay.curvedRNC_det_probe
#print axioms QIQTH.WhiteReplay.whiteW_genuinely_curved
#print axioms QIQTH.WhiteReplay.whiteReplay_witness_gate
#print axioms QIQTH.WhiteReplay.congr_double_sum_swap
#print axioms QIQTH.WhiteReplay.whitePullbackMetric_eq_fderiv_pullback
#print axioms QIQTH.WhiteReplay.whitePullbackMetric_eq_fderiv_pullback_ball
end AxiomChecks
