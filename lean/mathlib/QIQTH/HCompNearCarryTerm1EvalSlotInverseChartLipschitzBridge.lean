/-
  HCompNearCarryTerm1EvalSlotInverseChartLipschitzBridge — J4-1055: cloning J4-1024's
  `HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge` §A/§B/§C/§D structure (the
  `V`/Jacobian-composition Lipschitz-at-0 mechanism for an ABSTRACT globally-regular weight `P`)
  from the BASE-slot chart `W p := uniformInverseChart g gi hC hK p q₀` onto the EVAL-slot chart
  `We z := uniformInverseChart g gi hC hK q₀ z` (base `q₀` FIXED, field `z` VARYING — the
  orientation `ChartIFTPackageGeneralQ0.chartIFTPackage_generalQ0` uses).  Sol (`gpt-5.6-sol`,
  high, 2026-08-23) plan-reviewed GO before Lean: no eval-slot-specific obstruction, purely
  mechanical modulo dropping the `negCLE` wrapper (eval-slot's derivative at the diagonal is the
  PLAIN identity, not `-Id`, so `ContinuousLinearEquiv.refl` is used directly — actually simpler
  than the base-slot case).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT'S NEW HERE (vs J4-1024's base-slot file).

  J4-1024 built this exact mechanism for `W p := uniformInverseChart g gi hC hK p q₀` (BASE varies).
  `ChartIFTPackageGeneralQ0.chartIFTPackage_generalQ0` (J4-1011) instead needs the EVAL-slot
  orientation `We z := uniformInverseChart g gi hC hK q₀ z` (FIELD varies, base fixed at `q₀`) — the
  slot `VanVleckGatedSpatialSymmetry.hcomp`'s STEP-4c residual (r6) actually requires (per J4-1011's
  own docstring).  J4-1054's survey found the Jacobian/C² internals needed to redo J4-1024's
  mechanism for `We` are NOT exposed in `chartIFTPackage_generalQ0`'s packaged conclusion — but ARE
  already exposed, unconditionally, general-`q₀`, in `JointRNCRegularityInterfaceLocalGeneralK.lean`
  (the very inputs `chartIFTPackage_generalQ0`'s own proof uses):
    • `uniformInverseChart_slice_contDiffAt_diag_generalK : ContDiffAt ℝ 2 We q₀`
    • `uniformInverseChart_slice_value_diag_generalK : We q₀ = 0`
    • `uniformInverseChart_slice_fderiv_id_diag_generalK : fderiv ℝ We q₀ = ContinuousLinearMap.id`
  This file re-derives J4-1024's §A/§B/§C/§D mechanism from THESE already-banked facts directly
  (no extraction from `chartIFTPackage_generalQ0`'s proof body was needed after all — the facts it
  uses internally already have standalone, exposed, unconditional lemmas one file away).

  ## WHAT LANDS.
    • §A `uniformInverseChart_evalSlot_inverse_lipschitz_package_generalK` — ★★★ UNCONDITIONALLY: the
        IFT local inverse `V` of `We` satisfies `V 0 = q₀` (since `We q₀ = 0`) and is pairwise
        Lipschitz on an IMAGE ball `ball 0 σ`.  Eval-slot analogue of J4-1024 §A, SIMPLER (no
        `negCLE` wrapper — the diagonal derivative is the plain identity).
    • §B `uniformInverseChart_evalSlot_det_fderiv_regularity_bundle_generalK` — ★★ UNCONDITIONALLY: on
        a BASE ball `ball q₀ r`, `z ↦ (fderiv We z).det` is bounded below by `1/2` and pairwise
        Lipschitz.  Eval-slot analogue of J4-1024 §B, SIMPLER (`det Id = 1` directly, no
        `(-1)^n`/`abs_pow` sign bookkeeping).
    • §C `transported_ratio_regularity_evalSlot_generalK` — ★★★★ for ANY globally bounded (`M_P`) +
        globally Lipschitz (`L_P`) real weight `P : Point n → ℝ`, the CoV transformed integrand
        `w ↦ P (V w) / |det (fderiv We (V w))|` is bounded + pairwise-Lipschitz on an image ball
        `ball 0 σ` — UNCONDITIONALLY, general `q₀`.  Eval-slot analogue of J4-1024 §C.
    • §D `amp_of_transported_ratio_evalSlot_global_lipschitz_at_zero` — ★★★★★ THE BRIDGE.  TRUNCATES
        §C's ball-only bound into a GLOBALLY-defined function `AmpExt : Point n → ℝ` (equal to the
        transported ratio inside `ball 0 σ`, constant `= P q₀` outside) satisfying
        `AEStronglyMeasurable AmpExt volume` and a GLOBAL Lipschitz-at-0 bound
        `∀ v, |AmpExt v − AmpExt 0| ≤ L * ‖v‖` — for ANY `Point n`, not just the ball.  Eval-slot
        analogue of J4-1024 §D.

  ## HONEST SCOPE — WHAT THIS DOES **NOT** DO.
  This does NOT instantiate `HCompNearCarryTerm1DomainRestrictedBound`'s capstone (J4-1024's §E):
  that capstone's literal CoV-integral shape was built against the BASE-slot chart
  `uniformInverseChart g gi hC hK p q₀`, not the eval-slot chart `We` here — wiring §D's `AmpExt`
  into the ACTUAL downstream consumer (`terminalVelAt_chartReplace_sliver_bound`, per
  `ChartIFTPackageGeneralQ0`'s own docstring: "identifying `V`'s image set with `ball 0 R`,
  reconciling `ball x ρ` with the CoV's domain `ball q₀ ρ`, and threading the resulting difference
  integral through the rest of STEP-4c... a SEPARATE, NOT-attempted next step") remains completely
  untouched here.  This file closes ONLY the "`V`/Jacobian-composition Lipschitz-at-0" mechanism —
  for an ABSTRACT globally-regular `P` — in the EVAL-slot orientation; it does NOT plug in the
  literal geometric `Bfac` (whose OWN global boundedness + Lipschitz regularity remains a SEPARATE,
  NOT-yet-established gap, exactly as flagged in J4-1024), does NOT compose with the evenness link
  or `kPrime`'s factorization, and does NOT close `nb`'s term1 with the literal integrand.  `Bfac`'s
  4 summands (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`, `∂ⱼ∂ᵢA`, and the base term) remain untouched, `fb` (far carry)
  remains SEPARATELY open, and `hxmem`'s general (all-of-`K`) discharge remains open.  `a₁ = R/6`
  remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge
import QIQTH.JointRNCRegularityInterfaceLocalGeneralK

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.JointRNCRegularityLocalGeneralK
open QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge
open scoped Topology

namespace QIQTH.HCompNearCarryTerm1EvalSlotInverseChartLipschitzBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the local inverse `V` of the EVAL-slot chart `We` is center/pairwise
    ### Lipschitz, GENERAL `q₀`, UNCONDITIONALLY.
    ############################################################################### -/

/-- **★★★ `uniformInverseChart_evalSlot_inverse_lipschitz_package_generalK`.**  For
    `We z := uniformInverseChart g gi hC hK q₀ z` (EVAL-slot: base `q₀` FIXED, field `z` VARIES) at
    ANY `q₀ ∈ interior K` — NO extra hypothesis — the IFT local inverse `V` satisfies `V 0 = q₀`
    (`We q₀ = 0`) and is pairwise Lipschitz on an image ball `ball 0 σ`.  Route:
    `ContDiffAt.toOpenPartialHomeomorph` fed by `uniformInverseChart_slice_contDiffAt_diag_generalK`
    + `uniformInverseChart_slice_fderiv_id_diag_generalK` (the diagonal derivative is the PLAIN
    identity, so `ContinuousLinearEquiv.refl` is used directly — no `negCLE` wrapper needed, unlike
    the base-slot §A), then `to_localInverse` + the convex-MVT technique. NOT `a₁ = R/6`. -/
theorem uniformInverseChart_evalSlot_inverse_lipschitz_package_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (L_V : ℝ), 0 ≤ L_V ∧
      V 0 = q₀ ∧
      ∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        ‖V x - V y‖ ≤ L_V * dist x y := by
  classical
  set We : Point n → Point n := uniformInverseChart g gi hC hK q₀ with hWedef
  have hWeq0 : We q₀ = 0 := uniformInverseChart_slice_value_diag_generalK g gi hC hK q₀ hq₀
  have hbaseC2 : ContDiffAt ℝ 2 We q₀ :=
    uniformInverseChart_slice_contDiffAt_diag_generalK g gi hC hK q₀ hq₀
  have hfd_id : fderiv ℝ We q₀ = ContinuousLinearMap.id ℝ (Point n) :=
    uniformInverseChart_slice_fderiv_id_diag_generalK g gi hC hK q₀ hq₀
  have hWediff0 : DifferentiableAt ℝ We q₀ := hbaseC2.differentiableAt (by norm_num)
  have hWe'0 : HasFDerivAt We
      ((ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n)) q₀ := by
    have hcoe : fderiv ℝ We q₀
        = ((ContinuousLinearEquiv.refl ℝ (Point n)) : Point n →L[ℝ] Point n) := by
      rw [hfd_id, ContinuousLinearEquiv.coe_refl]
    rw [← hcoe]; exact hWediff0.hasFDerivAt
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  set Φ := hbaseC2.toOpenPartialHomeomorph We hWe'0 hn2 with hΦdef
  have hVc2 : ContDiffAt ℝ 2 (⇑Φ.symm) (0 : Point n) := by
    have hti := hbaseC2.to_localInverse hWe'0 hn2
    rw [hWeq0] at hti
    exact hti
  have hV1 : ContDiffAt ℝ 1 (⇑Φ.symm) (0 : Point n) := hVc2.of_le (by norm_num)
  have hΦcoe : (⇑Φ : Point n → Point n) = We := by
    rw [hΦdef]; exact hbaseC2.toOpenPartialHomeomorph_coe hWe'0 hn2
  have hq0src : q₀ ∈ Φ.source := by
    rw [hΦdef]; exact hbaseC2.mem_toOpenPartialHomeomorph_source hWe'0 hn2
  have hV0 : (⇑Φ.symm) (0 : Point n) = q₀ := by
    have h := Φ.left_inv hq0src
    have hc0 : (⇑Φ : Point n → Point n) q₀ = 0 := by rw [hΦcoe]; exact hWeq0
    rw [hc0] at h; exact h
  obtain ⟨r, hr, L, hL, hlip⟩ :=
    QIQTH.AmpQuantBundle.contDiffAt_one_lipschitzOn_ball (⇑Φ.symm) hV1
  refine ⟨r, hr, ⇑Φ.symm, L, hL, hV0, ?_⟩
  intro x hx y hy
  have hxb : ‖x‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hyb : ‖y‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hy
  have h := hlip x y hxb hyb
  rw [dist_eq_norm]
  exact h

/-! ###############################################################################
    ### §B — the determinant regularity bundle for `We`, GENERAL `q₀`, UNCONDITIONALLY.
    ############################################################################### -/

/-- **★★ `uniformInverseChart_evalSlot_det_fderiv_regularity_bundle_generalK`.**  On a BASE ball
    `ball q₀ r`, `z ↦ (fderiv ℝ We z).det` (`We z := uniformInverseChart g gi hC hK q₀ z`) is bounded
    below by `1/2` and pairwise Lipschitz — UNCONDITIONALLY, at ANY `q₀ ∈ interior K`.  Eval-slot
    analogue of J4-1024 §B, simpler at the center value (`det Id = 1` directly, no sign
    bookkeeping). NOT `a₁ = R/6`. -/
theorem uniformInverseChart_evalSlot_det_fderiv_regularity_bundle_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ r > (0 : ℝ), ∃ L_D : ℝ, 0 ≤ L_D ∧
      (∀ z ∈ Metric.ball q₀ r,
        (1 / 2 : ℝ) ≤ |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) z).det|) ∧
      (∀ x ∈ Metric.ball q₀ r, ∀ y ∈ Metric.ball q₀ r,
        |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) x).det
            - (fderiv ℝ (uniformInverseChart g gi hC hK q₀) y).det| ≤ L_D * dist x y) := by
  set We : Point n → Point n := uniformInverseChart g gi hC hK q₀ with hWedef
  have hbaseC2 : ContDiffAt ℝ 2 We q₀ :=
    uniformInverseChart_slice_contDiffAt_diag_generalK g gi hC hK q₀ hq₀
  have hfd_id : fderiv ℝ We q₀ = ContinuousLinearMap.id ℝ (Point n) :=
    uniformInverseChart_slice_fderiv_id_diag_generalK g gi hC hK q₀ hq₀
  -- `z ↦ (fderiv We z).det` is `ContDiffAt ℝ 1` at `q₀`.
  have hderivCDA1 : ContDiffAt ℝ 1 (fderiv ℝ We) q₀ := hbaseC2.fderiv_right (by norm_num)
  have hdetCDA : ContDiffAt ℝ 1 (fun z => (fderiv ℝ We z).det) q₀ :=
    ((QIQTH.BaseSlotDetRegularity.det_clm_contDiff (n := n)).contDiffAt).comp q₀ hderivCDA1
  -- Lipschitz on a base ball `ball q₀ rL` (via the shifted convex-MVT helper).
  obtain ⟨rL, hrL, L_D, hLD, hlipD⟩ :=
    contDiffAt_one_lipschitzOn_ball_atPoint (fun z => (fderiv ℝ We z).det) q₀ hdetCDA
  -- lower bound `≥ 1/2` on a base ball `ball q₀ rc`, via continuity + value `1` at `q₀`.
  have hval0 : |(fderiv ℝ We q₀).det| = 1 := by
    rw [hfd_id]; simp [ContinuousLinearMap.det]
  have hcontD : ContinuousAt (fun z => (fderiv ℝ We z).det) q₀ := hdetCDA.continuousAt
  have hcontAbs : ContinuousAt (fun z => |(fderiv ℝ We z).det|) q₀ := hcontD.abs
  have hgt : ∀ᶠ z in 𝓝 q₀, (1 / 2 : ℝ) < |(fderiv ℝ We z).det| := by
    have hlt : (fun _ : Point n => (1 / 2 : ℝ)) q₀
        < (fun z => |(fderiv ℝ We z).det|) q₀ := by simp only [hval0]; norm_num
    exact continuousAt_const.eventually_lt hcontAbs hlt
  obtain ⟨rc, hrc, hball⟩ := Metric.eventually_nhds_iff.mp hgt
  refine ⟨min rL rc, lt_min hrL hrc, L_D, hLD, ?_, ?_⟩
  · intro z hz
    have hzc : dist z q₀ < rc := lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    exact le_of_lt (hball hzc)
  · intro x hx y hy
    exact hlipD x (Metric.ball_subset_ball (min_le_left _ _) hx)
      y (Metric.ball_subset_ball (min_le_left _ _) hy)

/-! ###############################################################################
    ### §C — the MAIN transport for `We`, GENERAL `q₀`, UNCONDITIONALLY.
    ############################################################################### -/

/-- **★★★★ `transported_ratio_regularity_evalSlot_generalK`.**  For ANY globally bounded (`M_P`) +
    globally Lipschitz (`L_P`) weight `P`, the CoV transformed integrand
    `w ↦ P (V w) / |det (fderiv We (V w))|` (`We z := uniformInverseChart g gi hC hK q₀ z`, `V` the
    IFT local inverse) is bounded by `2 M_P` AND pairwise-Lipschitz on an image ball `ball 0 σ` —
    UNCONDITIONALLY, at ANY `q₀ ∈ interior K`.  Eval-slot analogue of J4-1024 §C. NOT `a₁ = R/6`. -/
theorem transported_ratio_regularity_evalSlot_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (P : Point n → ℝ) (M_P L_P : ℝ) (hMP : 0 ≤ M_P) (hLP : 0 ≤ L_P)
    (hPb : ∀ z, |P z| ≤ M_P)
    (hPl : ∀ x y : Point n, |P x - P y| ≤ L_P * dist x y) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (Lc : ℝ), 0 ≤ Lc ∧ V 0 = q₀ ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (P (V w) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V w)).det|)
          ≤ M_P / (1 / 2 : ℝ)) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (P (V x) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V x)).det|
            - P (V y) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V y)).det|)
          ≤ Lc * dist x y) := by
  obtain ⟨r, hr, L_D, hLD, hlb, hlip⟩ :=
    uniformInverseChart_evalSlot_det_fderiv_regularity_bundle_generalK g gi hC hK hq₀
  obtain ⟨hqb, hql⟩ :=
    QIQTH.HeatResidualBound.ratio_abs_lipschitzOn (Metric.ball q₀ r) P
      (fun z => (fderiv ℝ (uniformInverseChart g gi hC hK q₀) z).det)
      M_P L_P (1 / 2) L_D hMP hLP (by norm_num) hLD (fun z _ => hPb z) (fun x _ y _ => hPl x y) hlb hlip
  obtain ⟨σ0, hσ0, V, L_V, hLV, hV0, hVlip⟩ :=
    uniformInverseChart_evalSlot_inverse_lipschitz_package_generalK g gi hC hK hq₀
  have hLq0 : 0 ≤ L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2 := by
    have h1 : 0 ≤ L_P / (1 / 2 : ℝ) := div_nonneg hLP (by norm_num)
    have h2 : 0 ≤ M_P * L_D / (1 / 2 : ℝ) ^ 2 := div_nonneg (mul_nonneg hMP hLD) (by positivity)
    exact add_nonneg h1 h2
  -- `V` maps a small image ball into the base ball `ball q₀ r`.
  have hmaps : ∀ w ∈ Metric.ball (0 : Point n) (min σ0 (r / (L_V + 1))),
      V w ∈ Metric.ball q₀ r := by
    intro w hw
    have hwσ0 : w ∈ Metric.ball (0 : Point n) σ0 :=
      Metric.ball_subset_ball (min_le_left _ _) hw
    have h0σ0 : (0 : Point n) ∈ Metric.ball (0 : Point n) σ0 := Metric.mem_ball_self hσ0
    have hlip0 := hVlip w hwσ0 0 h0σ0
    rw [hV0] at hlip0
    have hVwnorm : ‖V w - q₀‖ ≤ L_V * ‖w‖ := by
      simpa [dist_zero_right] using hlip0
    have hwr : ‖w‖ < r / (L_V + 1) := by
      have hd : dist w (0 : Point n) < min σ0 (r / (L_V + 1)) := Metric.mem_ball.mp hw
      rw [dist_zero_right] at hd
      exact lt_of_lt_of_le hd (min_le_right _ _)
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖V w - q₀‖ ≤ L_V * ‖w‖ := hVwnorm
      _ ≤ (L_V + 1) * ‖w‖ := by nlinarith [norm_nonneg w]
      _ < (L_V + 1) * (r / (L_V + 1)) := by
            apply mul_lt_mul_of_pos_left hwr (by positivity)
      _ = r := by field_simp
  refine ⟨min σ0 (r / (L_V + 1)), lt_min hσ0 (by positivity), V,
    (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * L_V, mul_nonneg hLq0 hLV, hV0, ?_, ?_⟩
  · intro w hw
    exact hqb (V w) (hmaps w hw)
  · intro x hx y hy
    have hVx := hmaps x hx
    have hVy := hmaps y hy
    have h1 := hql (V x) hVx (V y) hVy
    have h2 := hVlip x (Metric.ball_subset_ball (min_le_left _ _) hx)
                      y (Metric.ball_subset_ball (min_le_left _ _) hy)
    calc abs (P (V x) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V x)).det|
            - P (V y) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V y)).det|)
          ≤ (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * dist (V x) (V y) := h1
      _ = (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * ‖V x - V y‖ := by rw [dist_eq_norm]
      _ ≤ (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * (L_V * dist x y) :=
            mul_le_mul_of_nonneg_left h2 hLq0
      _ = (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2) * L_V * dist x y := by ring

/-! ###############################################################################
    ### §D — the bridge: truncating the ball-only bound to a GLOBAL Lipschitz-at-0
    ### function for `We`, matching J4-1023's exact `Amp` interface.
    ############################################################################### -/

/-- **★★★★★ `amp_of_transported_ratio_evalSlot_global_lipschitz_at_zero` — THE BRIDGE.**  For ANY
    globally bounded + globally Lipschitz `P`, the piecewise-truncated function
        `AmpExt w := P (V w) / |det (fderiv We (V w))|` if `‖w‖ < σ`, else `P q₀`
    (`σ` the ball radius from `transported_ratio_regularity_evalSlot_generalK`) is
    `AEStronglyMeasurable` and satisfies a GLOBAL Lipschitz-at-`0` bound
    `∀ v, |AmpExt v − AmpExt 0| ≤ L·‖v‖` — EXACTLY `HCompNearCarryTerm1DomainRestrictedBound`'s
    `hAmp`/`hlip` interface SHAPE (this file does NOT itself instantiate that capstone — see the
    file docstring's honest-scope note on the base-slot-vs-eval-slot mismatch). NOT `a₁ = R/6`. -/
theorem amp_of_transported_ratio_evalSlot_global_lipschitz_at_zero
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (P : Point n → ℝ) (M_P L_P : ℝ) (hMP : 0 ≤ M_P) (hLP : 0 ≤ L_P)
    (hPb : ∀ z, |P z| ≤ M_P) (hPl : ∀ x y : Point n, |P x - P y| ≤ L_P * dist x y) :
    ∃ (AmpExt : Point n → ℝ) (L : ℝ), 0 ≤ L ∧
      AEStronglyMeasurable AmpExt volume ∧
      (∀ v : Point n, |AmpExt v - AmpExt 0| ≤ L * ‖v‖) := by
  classical
  obtain ⟨σ, hσ, V, Lc, hLc, hV0, hbnd, hlip⟩ :=
    transported_ratio_regularity_evalSlot_generalK g gi hC hK hq₀ P M_P L_P hMP hLP hPb hPl
  set AmpExt : Point n → ℝ := fun w =>
    if w ∈ Metric.ball (0 : Point n) σ then
      P (V w) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V w)).det|
    else P q₀ with hAmpExtdef
  have h0mem : (0 : Point n) ∈ Metric.ball (0 : Point n) σ := Metric.mem_ball_self hσ
  have hdet0 : |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) q₀).det| = 1 := by
    have hfd_id : fderiv ℝ (uniformInverseChart g gi hC hK q₀) q₀
        = ContinuousLinearMap.id ℝ (Point n) :=
      uniformInverseChart_slice_fderiv_id_diag_generalK g gi hC hK q₀ hq₀
    rw [hfd_id]; simp [ContinuousLinearMap.det]
  have hAmp0 : AmpExt 0 = P q₀ := by
    rw [hAmpExtdef]
    simp only [h0mem, if_true, hV0, hdet0]
    ring
  refine ⟨AmpExt, Lc, hLc, ?_, ?_⟩
  · -- `AEStronglyMeasurable`: gluing two `AEStronglyMeasurable` pieces on `μ.restrict s`/`μ.restrict sᶜ`.
    have hballmeas : MeasurableSet (Metric.ball (0 : Point n) σ) := measurableSet_ball
    have hrawmeas : AEStronglyMeasurable
        (fun w : Point n =>
          P (V w) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V w)).det|)
        (volume.restrict (Metric.ball (0 : Point n) σ)) := by
      have hlipfun : LipschitzOnWith (Real.toNNReal Lc)
          (fun w : Point n =>
            P (V w) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V w)).det|)
          (Metric.ball (0 : Point n) σ) := by
        rw [lipschitzOnWith_iff_dist_le_mul]
        intro x hx y hy
        have h := hlip x hx y hy
        rw [Real.dist_eq]
        simpa [Real.coe_toNNReal', hLc] using h
      exact (hlipfun.continuousOn.aestronglyMeasurable hballmeas)
    have hconstmeas : AEStronglyMeasurable (fun _ : Point n => P q₀)
        (volume.restrict (Metric.ball (0 : Point n) σ)ᶜ) := aestronglyMeasurable_const
    have hpiece : AEStronglyMeasurable AmpExt volume := by
      rw [← MeasureTheory.Measure.restrict_add_restrict_compl (μ := (volume : Measure (Point n)))
        hballmeas]
      apply AEStronglyMeasurable.add_measure
      · apply AEStronglyMeasurable.congr (f := fun w : Point n =>
          P (V w) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V w)).det|)
        · exact hrawmeas
        · filter_upwards [ae_restrict_mem hballmeas] with w hw
          rw [hAmpExtdef]; simp only [hw, if_true]
      · apply AEStronglyMeasurable.congr (f := fun _ : Point n => P q₀)
        · exact hconstmeas
        · filter_upwards [ae_restrict_mem hballmeas.compl] with w hw
          rw [hAmpExtdef]
          simp only [Set.mem_compl_iff] at hw
          simp only [hw, if_false]
    exact hpiece
  · intro v
    by_cases hv : v ∈ Metric.ball (0 : Point n) σ
    · have hvraw : AmpExt v
          = P (V v) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V v)).det| := by
        rw [hAmpExtdef]; simp only [hv, if_true]
      rw [hvraw, hAmp0]
      have hb := hlip v hv 0 h0mem
      have hV0det : P (V 0) / |(fderiv ℝ (uniformInverseChart g gi hC hK q₀) (V 0)).det|
          = P q₀ := by simp only [hV0, hdet0]; ring
      rw [hV0det] at hb
      have hdv : dist v (0 : Point n) = ‖v‖ := dist_zero_right v
      rwa [hdv] at hb
    · have hvconst : AmpExt v = P q₀ := by rw [hAmpExtdef]; simp only [hv, if_false]
      rw [hvconst, hAmp0]
      simp only [sub_self, abs_zero]
      exact mul_nonneg hLc (norm_nonneg v)

end QIQTH.HCompNearCarryTerm1EvalSlotInverseChartLipschitzBridge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryTerm1EvalSlotInverseChartLipschitzBridge
#print axioms uniformInverseChart_evalSlot_inverse_lipschitz_package_generalK
#print axioms uniformInverseChart_evalSlot_det_fderiv_regularity_bundle_generalK
#print axioms transported_ratio_regularity_evalSlot_generalK
#print axioms amp_of_transported_ratio_evalSlot_global_lipschitz_at_zero
end AxiomChecks
