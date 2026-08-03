/-
  ResidueThreading — J4-151: the RESIDUE-THREADING SWEEP.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS BRICK IS.

  A single sweep that DISCHARGES / THREADS several small residue items of the `a₁ = R/6` conditional
  chain, each of which had been CARRIED as an explicit labelled hypothesis by a downstream consumer.
  Every item is closed by wiring an ALREADY-PROVEN supplier into the exact carried shape — no new
  analysis. NOTHING here is `a₁ = R/6`; this is plumbing that shrinks the carried surface.

  ## WHAT LANDS HERE (all threaded from proven suppliers; NO `sorry`, no new axioms, no `expRho`).

    * (T1) `chartW0_rightInverse` — the standalone RIGHT-INVERSE identity
        `∃ r>0, ∀ z∈K, ‖z‖<r → uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0`.
      This is EXACTLY the `hRI` slot carried by `GeodesicGronwall`'s W4 family
      (`chartOrigin_lipschitz_modulus` / `chartOrigin_continuousOn` / `hWmeas₀_unconditional`). It was
      recovered *internally* inside `InverseChartDisplacement.chartW0_displacement` (the
      `ApproximatesLinearOn.surjOn` root `w` with `φ_z w = 0` + the inverse germ pinning
      `W₀ z = w`); here that recovery is EXTRACTED as a reusable lemma, trimmed of the displacement
      bootstrap it does not need.

    * (T2) `hLHSlim_discharge` — the `hLHSlim` slot of `InterchangeThreading.hLapFull_of_lims`,
      `Tendsto (m ↦ Δ_g(frozen H F u (u−ε_m)) 0) atTop (𝓝 (Δ_g(H*F u) 0))`, threaded from
      `DaLimLocUnif.lapTrunc_tendstoUniformlyOn` (U2, the `K`-uniform `LapTrunc` limit) via
      `TendstoUniformlyOn.tendsto_at` at a point `u ∈ K`. Uses `LapTrunc = Δ_g(frozen)` DEFINITIONALLY.

    * (T3) `hVol_discharge` — the Volterra `hVol` slot of `LeviLipschitz.resolvent_lipschitz_pointwise`,
      `F s z 0 = −E s z 0 − heatConv E F s z 0` for `F := leviSeries E`, threaded from
      `TrueHeatKernel.leviSeries_volterra` with its `hInter` carry SUPPLIED by the proven
      `heatConv_leviSeries_interchange` (LeviInterchange). Reduces the carry to the
      `hEbound`/`hEzero`/`hEmeas`/`hSum` family the M6 tower already runs on.

    * (T4) `gate_ball_floor` — the per-`z` gate-ball containment `∃ ρ>0, ∀ z∈K, ‖z‖<ρ → 0 ∈ S z` for
      the flow-image gate `S z := uniformFlowExp g gi hC hK z '' ball 0 (cf z)`, threading T1
      (`uniformFlowExp z (W₀ z) = 0`) + the displacement bound `chartW0_displacement`
      (`‖W₀ z‖ ≤ ‖z‖ + C_W‖z‖²`). This is the recognized carried item (3) of
      `InverseChartDisplacement`'s firewall — DERIVED here MODULO a positive floor on the gate radius.

    * (T5) `hWmeas₀_unconditional_of_ball` — the W4b capstone `hWmeas₀_unconditional`
      REFRESHED with its `hRI` slot GONE (supplied by T1 on `S ⊆ K ∩ ball 0 r`); and
      `a1_R6_of_residue_hCH_hInter_discharged` — the C3 capstone `a1_R6_of_residue_hCH_discharged`
      with its `hInter` slot GONE (supplied by `heatConv_leviSeries_interchange` at the center).

  ⚠ HONEST FIREWALL — what is NOT closed (carried, labelled).
    * T4 CARRIES the positive gate-radius FLOOR `hfloor : ∀ z∈K, ρ₀ ≤ cf z` (`ρ₀>0`). This is the
      genuinely-open piece: whether the concrete `.choose`-built gate radius `cf` admits a positive
      floor over `K` is a regularity fact about the `.choose` chart the tower does not provide. The
      GEOMETRY (0 lands in the gate once `‖z‖` is small) is fully derived here; only the floor is
      assumed. Satisfiable, non-vacuous, never the conclusion.
    * T5's `a1_R6_of_residue_hCH_hInter_discharged` TRADES the opaque tsum identity `hInter` for the
      Gaussian-domination family `hEbound`/`hEzero`/`hEmeas` on `E := heatOp g gi H` — strictly more
      basic carries, still CONDITIONAL. NOT `a₁ = R/6`.
    * The `hball`/`hnorm` slots of the W4b capstone are DISTINCT geometric facts about `W₀`'s
      ball/norm control (not `hRI`); they stay carried in T5.

  NOTHING here derives `a₁ = R/6`. This is a residue-threading sweep only.
-/
import Mathlib
import QIQTH.InverseChartDisplacement
import QIQTH.GeodesicGronwall
import QIQTH.DaLimLocUnif
import QIQTH.InterchangeThreading
import QIQTH.LeviLipschitz
import QIQTH.LeviInterchange
import QIQTH.TrueHeatKernel
import QIQTH.SpatialC2

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.RNCDecay
open QIQTH.LeviSeries QIQTH.GaussianWidthTolerant
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.HeatParametrixOrder
open scoped Interval Topology BigOperators NNReal

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-! ###############################################################################
    ### T1 — `chartW0_rightInverse`: the standalone `hRI` right-inverse identity.
    ############################################################################### -/

/-- **★★ T1 — `chartW0_rightInverse`.**  There is `r > 0` such that for every base point `z ∈ K` with
    `‖z‖ < r`, the inverse-chart origin coordinate `W₀ z := uniformInverseChart g gi hC hK z 0` is a
    genuine right inverse at the origin:
        `uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0`.
    This is EXACTLY the `hRI` slot the `GeodesicGronwall` W4 family carries. Proof: the
    `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse` root `w` of `φ_z` (with
    `φ_z w = 0`, `‖w‖` small) plus the inverse germ pinning `W₀ z = w`; the displacement bootstrap of
    `chartW0_displacement` is NOT needed. NOT `a₁ = R/6`. -/
theorem chartW0_rightInverse (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ z ∈ K, ‖z‖ < r →
      uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0 := by
  classical
  obtain ⟨δc, hδc, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨δ₁, hδ₁, c, hc1, hAL⟩ := uniformFlowExp_approximatesLinearOn g gi hC hK
  set M : ℝ := min δ₁ δc with hMdef
  have hMpos : 0 < M := lt_min hδ₁ hδc
  set ε : ℝ := M / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεδ₁ : ε < δ₁ := by
    rw [hεdef]; have : M ≤ δ₁ := min_le_left _ _; linarith
  have hεδc : ε < δc := by
    rw [hεdef]; have : M ≤ δc := min_le_right _ _; linarith
  have hc0 : 0 < 1 - (c : ℝ) := by linarith [hc1]
  refine ⟨(1 - (c : ℝ)) * ε, mul_pos hc0 hεpos, ?_⟩
  intro z hz hzr
  rcases subsingleton_or_nontrivial (Point n) with hsub | hns
  · -- trivial space: every vector is `0`.
    exact @Subsingleton.elim _ hsub _ _
  · haveI := hns
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
    -- pin `W₀ z = w` via the inverse germ.
    obtain ⟨hgermC2, _⟩ := hchart z hz
    obtain ⟨hgerm, _⟩ := hgermC2 w hwδc
    have hval : uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z w) = w :=
      hgerm.eq_of_nhds
    rw [hwφ] at hval
    -- conclude: `φ_z (W₀ z) = φ_z w = 0`.
    rw [hval]; exact hwφ

/-! ###############################################################################
    ### T2 — `hLHSlim_discharge`: the `hLHSlim` slot of `hLapFull_of_lims`.
    ############################################################################### -/

/-- **★★ T2 — `hLHSlim_discharge`.**  The `hLHSlim` slot of `InterchangeThreading.hLapFull_of_lims`,
        `Tendsto (m ↦ Δ_g(frozen H F u (u−ε_m)) 0) atTop (𝓝 (Δ_g(H*F u) 0))`,
    threaded pointwise at `u ∈ K` from the `K`-uniform `LapTrunc` limit
    `DaLimLocUnif.lapTrunc_tendstoUniformlyOn` (U2) via `TendstoUniformlyOn.tendsto_at`.  Since
    `LapTrunc g gi H F m u := laplaceBeltrami g gi (frozen H F u (u−ε_m) · 0) 0` DEFINITIONALLY, the
    `tendsto_at` conclusion IS the carried `hLHSlim` shape.  Genuine carries = U2's hypothesis family;
    NOT `a₁ = R/6`. -/
theorem hLHSlim_discharge (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (K : Set ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ K,
        pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hLapFull : ∀ u ∈ K, laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hII_lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ K,
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m))
    (hII_hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ K,
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume (u - epsSeq m) u)
    (B : ℝ → ℝ)
    (hSliver : ∀ (m : ℕ), ∀ u ∈ K,
        ‖∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0‖
          ≤ B (epsSeq m))
    (hBlim : Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0))
    {u : ℝ} (hu : u ∈ K) :
    Tendsto
        (fun m => laplaceBeltrami g gi (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) 0)
        atTop (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0)) := by
  have hU := lapTrunc_tendstoUniformlyOn g gi H F K hgi hΓ pdpdH hInterchange hLapFull
    hII_lo hII_hi B hSliver hBlim
  simpa only [LapTrunc] using hU.tendsto_at hu

/-! ###############################################################################
    ### T3 — `hVol_discharge`: the Volterra `hVol` slot of `resolvent_lipschitz_pointwise`.
    ############################################################################### -/

/-- **★★★ T3 — `hVol_discharge`.**  The Volterra identity `hVol` slot of
    `LeviLipschitz.resolvent_lipschitz_pointwise`, for the signed Levi series `F := leviSeries E`:
        `leviSeries E s z 0 = − E s z 0 − heatConv E (leviSeries E) s z 0`,
    threaded from `TrueHeatKernel.leviSeries_volterra` with its `hInter` carry SUPPLIED by the proven
    `heatConv_leviSeries_interchange`.  Reduces the Volterra carry to the width-2 Gaussian-domination
    family (`hEbound`/`hEzero`/`hEmeas`) + summability (`hSum`) the M6 tower already runs on.  Supply
    at `z` and at `z'` gives BOTH the `hVol`/`hVol'` slots of `resolvent_lipschitz_pointwise`.  NOT
    `a₁ = R/6`. -/
theorem hVol_discharge (E : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (s : ℝ) (hs : 0 < s) (z : Point n)
    (hSum : Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z 0)) :
    leviSeries E s z 0 = - E s z 0 - heatConv E (leviSeries E) s z 0 :=
  leviSeries_volterra E s z 0 hSum
    (heatConv_leviSeries_interchange E C hC hEbound hEzero hEmeas s hs z 0)

/-! ###############################################################################
    ### T4 — `gate_ball_floor`: the per-`z` gate-ball containment (floor CARRIED).
    ############################################################################### -/

/-- **★ T4 — `gate_ball_floor`.**  For the flow-image gate `S z := uniformFlowExp g gi hC hK z '' ball
    0 (cf z)`, GIVEN a positive floor `ρ₀ ≤ cf z` on `K`, the origin `0` lands inside the gate once
    `‖z‖` is small:
        `∃ ρ>0, ∀ z∈K, ‖z‖<ρ → 0 ∈ uniformFlowExp g gi hC hK z '' ball 0 (cf z)`.
    Geometry: `W₀ z := uniformInverseChart g gi hC hK z 0` satisfies `uniformFlowExp z (W₀ z) = 0`
    (T1) with `‖W₀ z‖ ≤ ‖z‖ + C_W‖z‖²` (`chartW0_displacement` + triangle), so on
    `‖z‖ < min{r₁, r_ri, 1, ρ₀/(1+C_W)}` we get `‖W₀ z‖ < ρ₀ ≤ cf z`, i.e. `W₀ z ∈ ball 0 (cf z)` and
    `0 = uniformFlowExp z (W₀ z) ∈ S z`.  This DERIVES the recognized carried item (3) of
    `InverseChartDisplacement`'s firewall — modulo the CARRIED floor `hfloor` (the genuinely-open
    `.choose`-gate regularity).  NOT `a₁ = R/6`. -/
theorem gate_ball_floor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (cf : Point n → ℝ) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hfloor : ∀ z ∈ K, ρ₀ ≤ cf z) :
    ∃ ρ > (0 : ℝ), ∀ z ∈ K, ‖z‖ < ρ →
      (0 : Point n) ∈ uniformFlowExp g gi hC hK z '' Metric.ball 0 (cf z) := by
  obtain ⟨r₁, hr₁, C_W, hCW0, hD1⟩ := chartW0_displacement g gi hC hK
  obtain ⟨rri, hrri, hri⟩ := chartW0_rightInverse g gi hC hK
  have h1C : 0 < 1 + C_W := by linarith [hCW0]
  refine ⟨min r₁ (min rri (min 1 (ρ₀ / (1 + C_W)))),
    lt_min hr₁ (lt_min hrri (lt_min one_pos (by positivity))), ?_⟩
  intro z hz hzρ
  set w : Point n := uniformInverseChart g gi hC hK z 0 with hwdef
  have hzr₁ : ‖z‖ < r₁ := lt_of_lt_of_le hzρ (min_le_left _ _)
  have hzrri : ‖z‖ < rri :=
    lt_of_lt_of_le hzρ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hz1 : ‖z‖ ≤ 1 :=
    le_of_lt (lt_of_lt_of_le hzρ
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hzfl : ‖z‖ < ρ₀ / (1 + C_W) :=
    lt_of_lt_of_le hzρ
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- displacement + triangle: ‖w‖ ≤ ‖w + z‖ + ‖z‖ ≤ C_W‖z‖² + ‖z‖.
  have hD : ‖w + z‖ ≤ C_W * ‖z‖ * ‖z‖ := hD1 z hz hzr₁
  have htri : ‖w‖ ≤ ‖w + z‖ + ‖z‖ := by
    calc ‖w‖ = ‖(w + z) - z‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖w + z‖ + ‖z‖ := norm_sub_le _ _
  have hsq : ‖z‖ * ‖z‖ ≤ ‖z‖ := by nlinarith [norm_nonneg z, hz1]
  have hchain : ‖w‖ ≤ ‖z‖ * (1 + C_W) := by nlinarith [htri, hD, hsq, hCW0, norm_nonneg z]
  have hlt : ‖z‖ * (1 + C_W) < ρ₀ := (lt_div_iff₀ h1C).mp hzfl
  have hwlt : ‖w‖ < cf z :=
    lt_of_le_of_lt hchain (lt_of_lt_of_le hlt (hfloor z hz))
  -- `0 = uniformFlowExp z w` with `w ∈ ball 0 (cf z)`.
  exact ⟨w, mem_ball_zero_iff.mpr hwlt, hri z hz hzrri⟩

/-! ###############################################################################
    ### T5 — the refresh: residue slots newly DISCHARGED in the capstones.
    ############################################################################### -/

/-- **★★ T5a — `hWmeas₀_unconditional_of_ball`.**  The W4b capstone
    `GeodesicGronwall.hWmeas₀_unconditional` REFRESHED with its `hRI` slot GONE: T1 supplies the
    right-inverse identity on any `S ⊆ K` with `‖z‖ < r`, so the base-point measurability holds under
    the two REMAINING geometric carries (`hball`/`hnorm` — distinct from `hRI`).  NOT `a₁ = R/6`. -/
theorem hWmeas₀_unconditional_of_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ {S : Set (Point n)}, MeasurableSet S → S ⊆ K →
      (∀ z ∈ S, uniformInverseChart g gi hC hK z 0
        ∈ Metric.ball (0 : Point n)
            (QIQTH.GeodesicGronwall.chartOrigin_lipschitz_modulus g gi hC hK).choose) →
      (∀ z ∈ S, ‖uniformInverseChart g gi hC hK z 0‖ ≤ uniformFlowRadius g gi hC hK) →
      (∀ z ∈ S, ‖z‖ < r) →
      ∀ τ : ℝ, AEStronglyMeasurable
        (fun z : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z 0))
        (volume.restrict S) := by
  obtain ⟨r, hr0, hr⟩ := chartW0_rightInverse g gi hC hK
  refine ⟨r, hr0, ?_⟩
  intro S hS hSK hball hnorm hSr
  exact QIQTH.GeodesicGronwall.hWmeas₀_unconditional g gi hC hK hS hSK hball hnorm
    (fun z hz => hr z (hSK hz) (hSr z hz))

/-- **★★ T5b — `a1_R6_of_residue_hCH_hInter_discharged`.**  The C3 capstone
    `SpatialC2.a1_R6_of_residue_hCH_discharged` REFRESHED with its `hInter` slot GONE: the proven
    `heatConv_leviSeries_interchange` supplies the tsum interchange at the center `(t,0,0)` from the
    Gaussian-domination family for `E := heatOp g gi H`.  Trades the opaque tsum identity for the more
    basic `hEbound`/`hEzero`/`hEmeas` carries.  ⚠ STILL NOT `a₁ = R/6`; the full residue stays
    carried. -/
theorem a1_R6_of_residue_hCH_hInter_discharged
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hSopen : IsOpen (S 0))
    (H : ℝ → Point n → Point n → ℝ)
    (hHeq : H = vanVleckGatedWitness g gi hChr hK S a b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    -- the UNRESTRICTED Gaussian-domination family for `E := heatOp g gi H` (replaces `hInter`).
    (hEbound : ∀ τ p q, 0 < τ →
        |heatOp g gi H τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0)
    (hEmeas : StronglyMeasurable
        (fun q : ℝ × Point n × Point n => heatOp g gi H q.1 q.2.1 q.2.2))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi H τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi H) 2 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
        = leviSeries (heatOp g gi H) t 0 0
          + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t)
    (D : Point n → (Point n →L[ℝ] ℝ))
    (hConvDeriv : ∃ u ∈ 𝓝 (0 : Point n),
      ∀ x ∈ u, HasFDerivAt (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (D x) x)
    (hConvD1 : ContDiffAt ℝ 1 D (0 : Point n)) :
    heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
    ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  have hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
      = ∑' k : ℕ, heatConv (heatOp g gi H)
          (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0 :=
    heatConv_leviSeries_interchange (heatOp g gi H) C hCnn hEbound hEzero hEmeas t ht 0 0
  exact QIQTH.HeatResidualBound.a1_R6_of_residue_hCH_discharged g gi Ric t ht C hCnn hChr hK S a b
    ha hab hK0 hS0 hSopen H hHeq hg hg0 hgi hΓ hdg0 htr hsrc hu hEboundW_le hInt hDuhamel hInter
    hDConv D hConvDeriv hConvD1

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms chartW0_rightInverse
#print axioms hLHSlim_discharge
#print axioms hVol_discharge
#print axioms gate_ball_floor
#print axioms hWmeas₀_unconditional_of_ball
#print axioms a1_R6_of_residue_hCH_hInter_discharged
end AxiomChecks
