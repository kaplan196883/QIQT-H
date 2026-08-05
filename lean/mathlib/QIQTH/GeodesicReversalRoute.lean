/-
  GeodesicReversalRoute — J4-273: the GEODESIC-REVERSAL route to base-slot chart regularity.

  THE ARCHITECTURE (external consult #6).  The last structural blocker of the W1 chart-image
  approximate identity is the base-slot regularity input consumed by
  `QIQTH.BaseVaryingIFTPackage.baseVaryingIFTPackage`:

      hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) 0        (the "J3 blocker")

  — the `.choose`-defined chart carries NO base-slot regularity.  The reversal route sidesteps the
  `.choose`/joint-base coherence entirely through the geometric identity (`U p x :=`
  `uniformInverseChart g gi hC hK p x`,  `E p := uniformFlowExp g gi hC hK p`,
  `T₀ v := (uniformFlowTube g gi hC hK 0 v 1).2` the TERMINAL VELOCITY of the geodesic from `(0, v)`):

      U z 0  =  − T₀ (U 0 z)        eventually at  z = 0.

  Derivation:  set `v := U 0 z`; the base-`0` right inverse gives `E 0 v = z`, so the geodesic
  `Y := uniformFlowTube 0 v` runs from `(0, v)` to `(z, u)` with `u := T₀ v`.  Reversing time
  `t ↦ 1 − t` and negating the velocity turns `Y` into a geodesic from `(z, −u)` to `(0, −v)`
  (the acceleration `−Γ(P)(W,W)` is EVEN in `W`), so by ODE uniqueness `E z (−u) = 0`; the base-`z`
  left inverse germ then reads `U z 0 = U z (E z (−u)) = −u = −T₀ (U 0 z)`.  The RHS is `C²` in `z`
  from (i) the banked field-slot `C²` of `U 0 ·` at `0` and (ii) fixed-base `C²` of `T₀` at `0` —
  NO joint base dependence, NO `.choose` coherence.

  ── PIECE STATUS (honest firewall — NOT `a₁ = R/6`). ──
    • (R) `geodesicField_flipVel`, `geodesic_reversal_hasDerivAt` — THE TIME-REVERSAL ODE LEMMA.
          FULLY PROVEN, UNCONDITIONAL.  `t ↦ flipVel (Y (1 − t))` solves the SAME autonomous geodesic
          system whenever `Y` does (evenness of the Γ-quadratic).  A clean reusable ODE fact.
    • (REACH) `uniformFlow_reversal_reach` — THE REVERSED-GEODESIC REACHABILITY.  FULLY PROVEN.
          Combines (R) with `ODE_solution_unique_of_mem_Icc_right`: for `q ∈ K`, `‖w‖ ≤ ρ_K`, with
          `z := E q w`, `u := T₀-at-`q` `w`, if `z ∈ K` and `‖u‖ ≤ ρ_K` then `E z (−u) = q`.
    • (RI0) `chart0_rightInverse` — the base-`0` RIGHT inverse `E 0 (U 0 z) = z` near `0`.  FULLY
          PROVEN (mirrors `chartW0_rightInverse` with the target `z` variable instead of `0`).
    • (I) `baseSlot_eq_neg_terminalVel` — THE IDENTITY `U z 0 = − T₀ (U 0 z)` EVENTUALLY at `0`.
          FULLY PROVEN from (REACH) + (RI0) + the base-`z` left-inverse germ + gate management.
    • (T) `hbaseC2_of_terminalVel_contDiffAt`, `baseVaryingIFTPackage_of_terminalVel_contDiffAt` —
          THE CONDITIONAL TRANSFER.  Given the SINGLE remaining regularity input
          `hT0 : ContDiffAt ℝ 2 T₀ 0` (fixed-base velocity-endpoint `C²` at `0`), (I) + the banked
          field-slot `C²` (`chartField_contDiffAt_center`) discharge `hbaseC2`, feeding the
          UNCONDITIONAL base-varying change-of-variables bundle.  PROVEN CONDITIONALLY on `hT0`.

  ── THE HONEST RESIDUAL.  The reversal route REDUCES the `.choose`/joint-base J3 blocker to ONE
    fixed-base fact: `hT0 : ContDiffAt ℝ 2 T₀ 0`, the neighbourhood `C²` of the base-`0` terminal
    VELOCITY endpoint.  Only the first Fréchet derivative of the velocity endpoint at the centre is
    banked (`flowVelocity_endpoint_hasFDerivAt_exists` — a `HasFDerivAt` at `0`, not a `𝓝`-`C²`); the
    2nd-order neighbourhood velocity-slot regularity is a genuine tower increment (the position slot
    reaches `C⁴` via `expMap_contDiffOn_four`, the velocity slot is "one order less" per the audit).
    So `hT0` is the precise, bankable residual — a standard fixed-base ODE-flow regularity, strictly
    weaker than and orthogonal to the base-varying `.choose` coherence it replaces.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  No `sorry` (prose only), no new
  axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypotheses.  `hT0` is a
  genuinely DIFFERENT function's regularity (the fixed-base velocity endpoint `T₀`, not the
  base-varying chart), reached through the nontrivial reversal identity (I); it does not trivially
  yield the conclusion.  No existing file is edited.
-/
import Mathlib
import QIQTH.UniformFlowBridge
import QIQTH.ResidueThreading
import QIQTH.ChartJetBounds
import QIQTH.BaseVaryingIFTPackage

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.GeodesicReversalRoute

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### (R) The velocity-flip continuous-linear map and the reversal algebra. -/

/-- **`flipVel` — the velocity-negation continuous-linear map** `(x, v) ↦ (x, −v)` on the geodesic
    phase space `Point n × Point n`.  A self-inverse linear isometry. -/
noncomputable def flipVel : (Point n × Point n) →L[ℝ] (Point n × Point n) :=
  (ContinuousLinearMap.id ℝ (Point n)).prodMap (-(ContinuousLinearMap.id ℝ (Point n)))

@[simp] theorem flipVel_apply (p : Point n × Point n) :
    flipVel p = (p.1, -p.2) := by
  apply Prod.ext
  · simp [flipVel, Prod.map_fst]
  · simp [flipVel, Prod.map_snd]

/-- `flipVel` is a linear isometry on the (sup-normed) product phase space. -/
theorem norm_flipVel (p : Point n × Point n) : ‖flipVel p‖ = ‖p‖ := by
  rw [flipVel_apply, Prod.norm_def, Prod.norm_def, norm_neg]

/-- **(R, algebra) — the geodesic field is REVERSAL-COMPATIBLE.**  Because the geodesic acceleration
    `−Γ(x)(v, v)` is EVEN in the velocity `v`, the field satisfies
        `geodesicField (flipVel p) = flipVel (−(geodesicField p))`.
    This is the pointwise fact that makes the time-reversed, velocity-negated curve solve the SAME
    autonomous system. -/
theorem geodesicField_flipVel (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n × Point n) :
    geodesicField g gi (flipVel p) = flipVel (-(geodesicField g gi p)) := by
  apply Prod.ext
  · simp [geodesicField, flipVel_apply]
  · funext i
    simp only [geodesicField, flipVel_apply, Prod.snd_neg, Prod.fst_neg, Pi.neg_apply,
      neg_neg, mul_neg, neg_mul]

/-- **(R, ODE) — THE TIME-REVERSAL LEMMA.**  If `Y` solves the geodesic system on `Ioo (−2) 2`, then
    the time-reversed, velocity-negated curve `Z t := flipVel (Y (1 − t))` solves the SAME system at
    every `t` with `1 − t ∈ Ioo (−2) 2`.  Proof: chain rule `d/dt Y(1−t) = −(geodesicField (Y(1−t)))`,
    then the linear `flipVel`, then the reversal-compatibility `geodesicField_flipVel`. -/
theorem geodesic_reversal_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    {Y : ℝ → Point n × Point n}
    (hYderiv : ∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t)
    {t : ℝ} (ht : (1 - t) ∈ Set.Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun s => flipVel (Y (1 - s)))
      (geodesicField g gi (flipVel (Y (1 - t)))) t := by
  have h1t : HasDerivAt (fun s : ℝ => 1 - s) (-1 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have hY : HasDerivAt Y (geodesicField g gi (Y (1 - t))) (1 - t) := hYderiv (1 - t) ht
  have hcomp : HasDerivAt (fun s => Y (1 - s))
      ((-1 : ℝ) • geodesicField g gi (Y (1 - t))) t := hY.scomp t h1t
  have hflip : HasDerivAt (fun s => flipVel (Y (1 - s)))
      (flipVel ((-1 : ℝ) • geodesicField g gi (Y (1 - t)))) t :=
    (flipVel.hasFDerivAt.comp_hasDerivAt t hcomp)
  have hval : flipVel ((-1 : ℝ) • geodesicField g gi (Y (1 - t)))
      = geodesicField g gi (flipVel (Y (1 - t))) := by
    rw [geodesicField_flipVel]; congr 1; module
  rwa [hval] at hflip

/-! ### The base-`0` terminal-velocity map `T₀`. -/

/-- **`terminalVel0` — the base-`0` terminal velocity** `T₀ v := (uniformFlowTube 0 v 1).2`, the
    velocity component at time `1` of the confined geodesic starting at `(0, v)`. -/
noncomputable def terminalVel0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) : Point n → Point n :=
  fun v => (uniformFlowTube g gi hC hK 0 v 1).2

/-! ### (REACH) The reversed-geodesic reachability, via time reversal + ODE uniqueness. -/

/-- **(REACH) — REVERSED-GEODESIC REACHABILITY.**  For a base `q ∈ K` and a velocity `w` with
    `‖w‖ ≤ ρ_K`, write `z := uniformFlowExp q w` for the position endpoint and `u := (tube q w 1).2`
    for the TERMINAL VELOCITY.  If `z ∈ K` and `‖u‖ ≤ ρ_K`, then the geodesic from `(z, −u)` returns
    to `q`:
        `uniformFlowExp z (−u) = q`.
    Proof: the reversed curve `Z t := flipVel (Y (1 − t))` (`Y := tube q w`) solves the SAME geodesic
    system (`geodesic_reversal_hasDerivAt`) with `Z 0 = (z, −u) = tube z (−u) 0`; both curves are
    confined to a common compact ball on `[0,1]` (`flipVel` is an isometry), on which `geodesicField`
    is Lipschitz, so `ODE_solution_unique_of_mem_Icc_right` forces `Z 1 = tube z (−u) 1`, whose
    position slot reads `q = (Z 1).1`.  FULLY DERIVED — no uniqueness carried.  NOT `a₁ = R/6`. -/
theorem uniformFlow_reversal_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q w : Point n) (hq : q ∈ K)
    (hw : ‖w‖ ≤ uniformFlowRadius g gi hC hK)
    (hz : uniformFlowExp g gi hC hK q w ∈ K)
    (hu : ‖(uniformFlowTube g gi hC hK q w 1).2‖ ≤ uniformFlowRadius g gi hC hK) :
    uniformFlowExp g gi hC hK (uniformFlowExp g gi hC hK q w)
        (-(uniformFlowTube g gi hC hK q w 1).2) = q := by
  set Y : ℝ → Point n × Point n := uniformFlowTube g gi hC hK q w with hYdef
  set z : Point n := uniformFlowExp g gi hC hK q w with hzdef
  set u : Point n := (Y 1).2 with hudef
  -- `Y 1 = (z, u)`.
  have hY1 : Y 1 = (z, u) := by
    rw [hzdef, hudef, uniformFlowExp_eq]
  -- Specs of `Y`.
  have hY0 : Y 0 = (q, w) := uniformFlowTube_spec_ic g gi hC hK q hq w hw
  have hYode : ∀ t ∈ Set.Ioo (-2 : ℝ) 2,
      HasDerivAt Y (geodesicField g gi (Y t)) t :=
    uniformFlowTube_spec_ode g gi hC hK q hq w hw
  have hYconf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Y t - ((q, 0) : Point n × Point n)‖ ≤ uniformFlowConst g gi hC hK * ‖w‖ :=
    uniformFlowTube_spec_conf g gi hC hK q hq w hw
  -- The reversed curve.
  set Z : ℝ → Point n × Point n := fun s => flipVel (Y (1 - s)) with hZdef
  -- The forward curve from `(z, -u)`.
  set V : ℝ → Point n × Point n := uniformFlowTube g gi hC hK z (-u) with hVdef
  have hun : ‖(-u)‖ ≤ uniformFlowRadius g gi hC hK := by rwa [norm_neg]
  have hV0 : V 0 = (z, -u) := uniformFlowTube_spec_ic g gi hC hK z hz (-u) hun
  have hVode : ∀ t ∈ Set.Ioo (-2 : ℝ) 2,
      HasDerivAt V (geodesicField g gi (V t)) t :=
    uniformFlowTube_spec_ode g gi hC hK z hz (-u) hun
  have hVconf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖V t - ((z, 0) : Point n × Point n)‖ ≤ uniformFlowConst g gi hC hK * ‖(-u)‖ :=
    uniformFlowTube_spec_conf g gi hC hK z hz (-u) hun
  -- Interval inclusions.
  have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIco_sub : Set.Ico (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hrev_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) ∈ Set.Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  -- `Z` solves the geodesic system on `[0,1]`.
  have hZderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Z (geodesicField g gi (Z t)) t := by
    intro t ht
    exact geodesic_reversal_hasDerivAt g gi hYode (hIcc_sub (hrev_mem t ht))
  -- Common compact confinement ball around `0`.
  set R : ℝ := max (‖((q, 0) : Point n × Point n)‖ + uniformFlowConst g gi hC hK * ‖w‖)
    (‖((z, 0) : Point n × Point n)‖ + uniformFlowConst g gi hC hK * ‖(-u)‖) with hRdef
  set S : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) R with hSdef
  -- Lipschitz on the compact convex ball `S`.
  obtain ⟨Kq, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) (by rw [hSdef]; exact convex_closedBall _ R)
      (by rw [hSdef]; exact isCompact_closedBall _ R)
  -- Continuity on `[0,1]`.
  have hcont_Z : ContinuousOn Z (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hZderiv t ht).continuousAt.continuousWithinAt
  have hcont_V : ContinuousOn V (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hVode t (hIcc_sub ht)).continuousAt.continuousWithinAt
  -- Membership in `S` on `[0,1]`.
  have hmem_Z : ∀ t ∈ Set.Icc (0 : ℝ) 1, Z t ∈ S := by
    intro t ht
    rw [hSdef, Metric.mem_closedBall, dist_zero_right, hZdef, norm_flipVel]
    have hnorm : ‖Y (1 - t)‖ ≤ ‖((q, 0) : Point n × Point n)‖ + uniformFlowConst g gi hC hK * ‖w‖ := by
      have hconf := hYconf (1 - t) (hrev_mem t ht)
      have htri := norm_le_norm_add_norm_sub' (Y (1 - t)) ((q, 0) : Point n × Point n)
      linarith [hconf, htri]
    exact le_trans hnorm (le_max_left _ _)
  have hmem_V : ∀ t ∈ Set.Icc (0 : ℝ) 1, V t ∈ S := by
    intro t ht
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖V t‖ ≤ ‖((z, 0) : Point n × Point n)‖ + uniformFlowConst g gi hC hK * ‖(-u)‖ := by
      have hconf := hVconf t ht
      have htri := norm_le_norm_add_norm_sub' (V t) ((z, 0) : Point n × Point n)
      linarith [hconf, htri]
    exact le_trans hnorm (le_max_right _ _)
  -- Same value at `t = 0`.
  have ha : Z 0 = V 0 := by
    rw [hZdef]
    simp only [sub_zero, hY1, flipVel_apply]
    rw [hV0]
  -- Grönwall uniqueness on `[0,1]`.
  have hEqOn : Set.EqOn Z V (Set.Icc (0 : ℝ) 1) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ => geodesicField g gi)
      (s := fun _ => S) (K := Kq)
      (fun t _ => hLip) hcont_Z
      (fun t ht => (hZderiv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => hmem_Z t (Set.Ico_subset_Icc_self ht))
      hcont_V
      (fun t ht => (hVode t (hIco_sub ht)).hasDerivWithinAt)
      (fun t ht => hmem_V t (Set.Ico_subset_Icc_self ht))
      ha
  -- Evaluate the position component at `t = 1`.
  have h1 : Z 1 = V 1 := hEqOn (Set.right_mem_Icc.mpr (by norm_num))
  have hZ1 : (Z 1).1 = q := by
    rw [hZdef]
    simp only [show (1 : ℝ) - 1 = 0 by ring, hY0, flipVel_apply]
  have hV1 : uniformFlowExp g gi hC hK z (-u) = (V 1).1 := by
    rw [hVdef, uniformFlowExp_eq]
  rw [hV1, ← h1, hZ1]

/-! ### (RI0) The base-`0` RIGHT inverse of the chart. -/

/-- **(RI0) — the base-`0` chart RIGHT inverse.**  There is `r > 0` such that for every target
    `z` with `‖z‖ < r`, the base-`0` inverse chart `U 0 := uniformInverseChart g gi hC hK 0` is a
    genuine right inverse of the base-`0` forward map `E 0 := uniformFlowExp g gi hC hK 0`:
        `uniformFlowExp g gi hC hK 0 (uniformInverseChart g gi hC hK 0 z) = z`.
    The verbatim base-`0`, variable-target analogue of `chartW0_rightInverse` (which fixes the target
    at `0`): the `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse` root `w` of `E 0`
    (`E 0 w = z`, `‖w‖ ≤ ε`) plus the inverse germ pinning `U 0 z = w`.  NOT `a₁ = R/6`. -/
theorem chart0_rightInverse (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    ∃ r > (0 : ℝ), ∀ z : Point n, ‖z‖ < r →
      uniformFlowExp g gi hC hK 0 (uniformInverseChart g gi hC hK 0 z) = z := by
  classical
  obtain ⟨δc, hδc, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨δ₁, hδ₁, c, hc1, hAL⟩ := uniformFlowExp_approximatesLinearOn g gi hC hK
  set M : ℝ := min δ₁ δc with hMdef
  have hMpos : 0 < M := lt_min hδ₁ hδc
  set ε : ℝ := M / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεδ₁ : ε < δ₁ := by rw [hεdef]; have : M ≤ δ₁ := min_le_left _ _; linarith
  have hεδc : ε < δc := by rw [hεdef]; have : M ≤ δc := min_le_right _ _; linarith
  have hc0 : 0 < 1 - (c : ℝ) := by linarith [hc1]
  refine ⟨(1 - (c : ℝ)) * ε, mul_pos hc0 hεpos, ?_⟩
  intro z hzr
  rcases subsingleton_or_nontrivial (Point n) with hsub | hns
  · exact @Subsingleton.elim _ hsub _ _
  · haveI := hns
    set fri := (ContinuousLinearEquiv.refl ℝ (Point n)).toNonlinearRightInverse with hfri
    have hnn : ((fri.nnnorm : ℝ)) = 1 := by
      have h1 : fri.nnnorm
          = ‖((ContinuousLinearEquiv.refl ℝ (Point n)).symm : Point n →L[ℝ] Point n)‖₊ := rfl
      have h2 : ((ContinuousLinearEquiv.refl ℝ (Point n)).symm : Point n →L[ℝ] Point n)
          = ContinuousLinearMap.id ℝ (Point n) := by ext x; simp
      have h3 : ‖ContinuousLinearMap.id ℝ (Point n)‖₊ = 1 := by simp
      rw [h1, h2, h3]; norm_num
    have hAL0 : ApproximatesLinearOn (uniformFlowExp g gi hC hK 0)
        (ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n)
        (Metric.ball 0 δ₁) c := hAL 0 h0K
    have hφ0 : uniformFlowExp g gi hC hK 0 0 = 0 := uniformFlowExp_zero g gi hC hK 0 h0K
    have hεsub : Metric.closedBall (0 : Point n) ε ⊆ Metric.ball 0 δ₁ := by
      intro x hx
      rw [mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt hx hεδ₁
    have hsurj := hAL0.surjOn_closedBall_of_nonlinearRightInverse fri hεpos.le hεsub
    have hzmem : z ∈ Metric.closedBall (uniformFlowExp g gi hC hK 0 0)
        (((fri.nnnorm : ℝ)⁻¹ - ↑c) * ε) := by
      rw [Metric.mem_closedBall, hnn, inv_one, hφ0, dist_eq_norm, sub_zero]
      linarith [hzr]
    obtain ⟨w, hwmem, hwφ⟩ := hsurj hzmem
    have hwε : ‖w‖ ≤ ε := by rwa [mem_closedBall_zero_iff] at hwmem
    have hwδc : ‖w‖ < δc := lt_of_le_of_lt hwε hεδc
    obtain ⟨hgermC2, _⟩ := hchart 0 h0K
    obtain ⟨hgerm, _⟩ := hgermC2 w hwδc
    have hval : uniformInverseChart g gi hC hK 0 (uniformFlowExp g gi hC hK 0 w) = w :=
      hgerm.eq_of_nhds
    rw [hwφ] at hval
    rw [hval]
    exact hwφ

/-! ### Confinement bound on the terminal velocity. -/

/-- **Terminal-velocity confinement.**  At base `0 ∈ K`, for `‖v‖ ≤ ρ_K` the terminal velocity is
    controlled linearly, `‖T₀ v‖ ≤ C₀ ‖v‖`, directly from the tube's `C₀‖v‖`-confinement at `t = 1`
    (the velocity slot is dominated by the full phase norm).  NOT `a₁ = R/6`. -/
theorem terminalVel0_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (v : Point n)
    (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK) :
    ‖terminalVel0 g gi hC hK v‖ ≤ uniformFlowConst g gi hC hK * ‖v‖ := by
  have hconf := uniformFlowTube_spec_conf g gi hC hK 0 h0K v hv 1
    (Set.right_mem_Icc.mpr zero_le_one)
  set P : Point n × Point n := uniformFlowTube g gi hC hK 0 v 1 with hP
  have hP2 : P.2 = (P - ((0, 0) : Point n × Point n)).2 := by simp
  have hle : ‖(P - ((0, 0) : Point n × Point n)).2‖ ≤ ‖P - ((0, 0) : Point n × Point n)‖ := by
    rw [Prod.norm_def]; exact le_max_right _ _
  calc ‖terminalVel0 g gi hC hK v‖ = ‖P.2‖ := rfl
    _ = ‖(P - ((0, 0) : Point n × Point n)).2‖ := by rw [hP2]
    _ ≤ ‖P - ((0, 0) : Point n × Point n)‖ := hle
    _ ≤ uniformFlowConst g gi hC hK * ‖v‖ := hconf

/-! ### (I) The base-slot reversal identity `U z 0 = − T₀ (U 0 z)`. -/

/-- **(I) — THE REVERSAL IDENTITY.**  Eventually at `z = 0`, the base-slot chart equals the negated
    terminal velocity of the base-`0` chart image:
        `(fun z => uniformInverseChart g gi hC hK z 0)`
          `=ᶠ[𝓝 0] (fun z => − terminalVel0 g gi hC hK (uniformInverseChart g gi hC hK 0 z))`.
    Proof (all gates eventual): with `v := U 0 z`, `chart0_rightInverse` gives `E 0 v = z`; the
    terminal-velocity confinement bounds `‖T₀ v‖ ≤ C₀‖v‖` (so `‖v‖`-gates control every radius);
    `uniformFlow_reversal_reach` gives `E z (−T₀ v) = 0`; and the base-`z` left-inverse germ reads
    `U z 0 = U z (E z (−T₀ v)) = −T₀ v`.  FULLY DERIVED.  NOT `a₁ = R/6`. -/
theorem baseSlot_eventuallyEq_neg_terminalVel (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    (fun z => uniformInverseChart g gi hC hK z 0)
      =ᶠ[𝓝 (0 : Point n)]
      (fun z => -terminalVel0 g gi hC hK (uniformInverseChart g gi hC hK 0 z)) := by
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  obtain ⟨r, hr, hRI0⟩ := chart0_rightInverse g gi hC hK h0K
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  set ρK : ℝ := uniformFlowRadius g gi hC hK with hρK
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC0
  have hρpos : 0 < ρK := uniformFlowRadius_pos g gi hC hK
  have hC0nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  have hC1 : (0 : ℝ) < C₀ + 1 := by linarith
  set θ : ℝ := min (ρK / (C₀ + 1)) (δ₀ / (C₀ + 1)) with hθ
  have hθpos : 0 < θ := lt_min (by positivity) (by positivity)
  -- Continuity of the field-slot chart at `0`, value `0`.
  have hcontv : ContinuousAt (fun z => uniformInverseChart g gi hC hK 0 z) 0 :=
    (chartField_contDiffAt_center g gi hC hK h0K).continuousAt
  have hval0 : uniformInverseChart g gi hC hK 0 0 = 0 :=
    chartField_centerValue_base0 g gi hC hK h0K
  have htend : Tendsto (fun z => ‖uniformInverseChart g gi hC hK 0 z‖) (𝓝 0) (𝓝 0) := by
    simpa [hval0] using hcontv.norm.tendsto
  have hev_θ : ∀ᶠ z in 𝓝 (0 : Point n),
      ‖uniformInverseChart g gi hC hK 0 z‖ < θ :=
    htend.eventually (eventually_lt_nhds hθpos)
  filter_upwards [Metric.ball_mem_nhds (0 : Point n) hr, h0Kmem, hev_θ]
    with z hzball hzK hzθ
  -- The base-`0` chart image `v` and its right-inverse property.
  set v : Point n := uniformInverseChart g gi hC hK 0 z with hvdef
  have hzr : ‖z‖ < r := mem_ball_zero_iff.mp hzball
  have hRI : uniformFlowExp g gi hC hK 0 v = z := by
    rw [hvdef]; exact hRI0 z hzr
  -- Norm gates.
  have hvθ : ‖v‖ < θ := hzθ
  have hvr1 : ‖v‖ < ρK / (C₀ + 1) := lt_of_lt_of_le hvθ (min_le_left _ _)
  have hvd1 : ‖v‖ < δ₀ / (C₀ + 1) := lt_of_lt_of_le hvθ (min_le_right _ _)
  have hvr1' : ‖v‖ * (C₀ + 1) < ρK := (lt_div_iff₀ hC1).mp hvr1
  have hvd1' : ‖v‖ * (C₀ + 1) < δ₀ := (lt_div_iff₀ hC1).mp hvd1
  have hv_ρ : ‖v‖ ≤ ρK := by nlinarith [norm_nonneg v]
  -- Terminal-velocity bound and derived radius gates.
  have hu_le : ‖terminalVel0 g gi hC hK v‖ ≤ C₀ * ‖v‖ :=
    terminalVel0_norm_le g gi hC hK h0K v hv_ρ
  have hu_ρ : ‖terminalVel0 g gi hC hK v‖ ≤ ρK := by
    nlinarith [hu_le, hvr1', norm_nonneg v, hC0nn]
  have hu_δ : ‖terminalVel0 g gi hC hK v‖ < δ₀ := by
    nlinarith [hu_le, hvd1', norm_nonneg v, hC0nn]
  -- Reversed-geodesic reachability, transported to base `z` via `E 0 v = z`.
  have hzKmem : uniformFlowExp g gi hC hK 0 v ∈ K := by rw [hRI]; exact hzK
  have hreach := uniformFlow_reversal_reach g gi hC hK 0 v h0K hv_ρ hzKmem hu_ρ
  rw [hRI] at hreach
  -- Base-`z` left-inverse germ at the reversed velocity.
  obtain ⟨hgermCz, _⟩ := hchart z hzK
  obtain ⟨hgermz, _⟩ := hgermCz (-(uniformFlowTube g gi hC hK 0 v 1).2)
    (by rw [norm_neg]; exact hu_δ)
  have hgz := hgermz.eq_of_nhds
  rw [hreach] at hgz
  -- Conclude:  `U z 0 = − T₀ v`.
  simpa using hgz

/-! ### (T) The conditional transfer: `hbaseC2` and the unconditional CoV bundle. -/

/-- **(T, hbaseC2) — the base-slot `C²` input, CONDITIONAL on `hT0`.**  Given the SINGLE remaining
    regularity input `hT0 : ContDiffAt ℝ 2 T₀ 0` (the fixed-base terminal-velocity `C²` at the
    centre), the reversal identity (I) + the banked field-slot `C²` (`chartField_contDiffAt_center`)
    yield exactly the `hbaseC2` input consumed by `baseVaryingIFTPackage`:
        `ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) 0`.
    `hT0` is a genuinely DIFFERENT function's regularity (the base-`0` velocity endpoint), reached
    through the nontrivial identity (I) — not the conclusion in disguise.  NOT `a₁ = R/6`. -/
theorem hbaseC2_of_terminalVel_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hT0 : ContDiffAt ℝ 2 (terminalVel0 g gi hC hK) 0) :
    ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n) := by
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  have hEq := baseSlot_eventuallyEq_neg_terminalVel g gi hC hK h0Kmem
  have hfield := chartField_contDiffAt_center g gi hC hK h0K
  have hval := chartField_centerValue_base0 g gi hC hK h0K
  have hcomp : ContDiffAt ℝ 2
      (fun z => terminalVel0 g gi hC hK (uniformInverseChart g gi hC hK 0 z)) 0 := by
    have hg : ContDiffAt ℝ 2 (terminalVel0 g gi hC hK)
        (uniformInverseChart g gi hC hK 0 0) := by rw [hval]; exact hT0
    exact hg.comp 0 hfield
  exact hcomp.neg.congr_of_eventuallyEq hEq

/-- **(T, capstone) — the UNCONDITIONAL base-varying change-of-variables bundle, CONDITIONAL on
    `hT0`.**  Feeds `hbaseC2_of_terminalVel_contDiffAt` into
    `QIQTH.BaseVaryingIFTPackage.baseVaryingIFTPackage`.  The `.choose`/joint-base J3 blocker is
    thereby REDUCED to the single fixed-base fact `hT0`.  NOT `a₁ = R/6`. -/
theorem baseVaryingIFTPackage_of_terminalVel_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hT0 : ContDiffAt ℝ 2 (terminalVel0 g gi hC hK) 0) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      MeasurableSet (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0) (f' z)
            (Metric.ball (0 : Point n) ρ) z)
      ∧ Set.InjOn (fun z => uniformInverseChart g gi hC hK z 0) (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          V (uniformInverseChart g gi hC hK z 0) = z)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ, 0 < |(f' z).det|)
      ∧ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)
          ∈ 𝓝 (0 : Point n) :=
  QIQTH.BaseVaryingIFTPackage.baseVaryingIFTPackage g gi hC hK h0Kmem
    (hbaseC2_of_terminalVel_contDiffAt g gi hC hK h0Kmem hT0)

end QIQTH.GeodesicReversalRoute

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.GeodesicReversalRoute
#print axioms geodesicField_flipVel
#print axioms geodesic_reversal_hasDerivAt
#print axioms uniformFlow_reversal_reach
#print axioms chart0_rightInverse
#print axioms baseSlot_eventuallyEq_neg_terminalVel
#print axioms hbaseC2_of_terminalVel_contDiffAt
#print axioms baseVaryingIFTPackage_of_terminalVel_contDiffAt
end AxiomChecks
