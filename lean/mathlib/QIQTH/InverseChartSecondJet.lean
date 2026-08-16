/-
  InverseChartSecondJet — the SECOND-JET (Hessian) UNIFORM BOUND of the van-Vleck inverse chart,
  DERIVED by plumbing the uniform FORWARD-flow Hessian bound (R3) through the second-order
  inverse-function-theorem chain rule.  This PIERCES the SECOND-jet half of the J4-556 substrate wall,
  the residue that `InverseChartFirstJet` (first-jet half) left carried.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6` and proves nothing new about `R/6`.  It is one
  geometry-layer analytic brick of the a₁=R/6 mixed-sliver campaign's chart-surface residue.  It
  supplies the exact SHAPE of the mixed-sliver hypothesis `hJ3Q` of
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed`

      `hJ3Q : ‖Q z‖ ≤ C_Q`   (the RNC second-jet / inverse-Hessian bound)

  for the CONCRETE van-Vleck chart, with
  `Q z := fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0` its second jet at the
  origin.

  ── THE WALL, AND WHY IT NOW FALLS.  The J4-556 substrate wall said the frozen `uniformChart_exists`
  spec exposes only a pointwise `ContDiffAt 2` of the inverse chart (so `Q z` EXISTS and is continuous
  per base point) but NO uniform-in-base bound.  The mixed-sliver residue doc (J4-796) flagged `hJ3Q`
  as blocked because "the forward second Taylor's transfer to a uniform inverse Hessian is not plumbed."
  BUT the two ingredients ALREADY EXIST in the repo and only needed wiring:

    (i)  the second-order IFT identity for the inverse chart at the field centre
         (`Hid2Germ.hid2_discharged` / `ChartSecondJet.chartSecondJet_eq_of_forward2`):
             `Q z = (−mulLeftRight ℝ _ I I) ∘L ((D²φ_z(W_z 0)) ∘L I)`,  `I = Ring.inverse (Dφ_z(W_z 0))`;
    (ii) the UNIFORM forward-Hessian operator-norm bound R3 (`uniformFlowExp_hessian_opNorm_le`,
         J4-70): `∃ r₀ M', ∀ q∈K ∀‖v‖<r₀, ‖fderiv ℝ (fderiv ℝ (uniformFlowExp … q)) v‖ ≤ M'`.

  With `‖I‖ ≤ 2` (from the forward Jacobian gap `uniformFlowExp_fderiv_near_id_quant` +
  `InverseChartFirstJet.clm_inverse_sub_one_le`), the operator-norm of the IFT expression is
      `‖Q z‖ ≤ ‖I‖³ · ‖D²φ_z(W_z 0)‖ ≤ 2³ · M' = 8·M'`,
  a UNIFORM bound.  This is exactly the transfer the doc said "is not plumbed here" — now plumbed.

  ── WHAT LANDS (all DERIVED; NO `sorry`, no new axioms, NOT `a₁ = R/6`).
    * (A) `secondJet_opNorm_le` — the reusable OPERATOR-NORM primitive: for `I : E →L E`, `D2 : E →L
      (E →L E)` with `‖I‖ ≤ 2` and `‖D2‖ ≤ M` (`0 ≤ M`),
          `‖(−mulLeftRight ℝ (E →L E) I I) ∘L (D2 ∘L I)‖ ≤ 8·M`,
      via `‖mulLeftRight I I‖ ≤ ‖I‖·‖I‖` (`opNorm_le_bound` + `norm_mul_le`) and `opNorm_comp_le`.
    * (B) `chartW0_secondJet_bound` — the CONCRETE discharge, per-point on a ball: an explicit `r > 0`
      and `C_Q ≥ 0` with `‖fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0‖ ≤ C_Q`
      for `z ∈ K`, `‖z‖ < r` (`C_Q = 8·M'`).  Assembles the per-`z` second-order IFT identity (the
      `Hid2Germ` germ apparatus) with the two norm inputs.

  ── HONEST SCOPE (what is NOT closed).  Like `InverseChartFirstJet.chartW0_firstJet_gap` /
  `RNCNearIsometryPointwise.chartW0_hco_ball`, this is per-point on the injectivity BALL, not the
  GLOBAL `∀ z` the sliver literally carries (the global form needs the unbuilt gating layer setting
  `V = −id, Pi = eᵢ, Q = 0` off the injectivity ball).  Together with `chartW0_firstJet_gap`
  (`hJ3i`/`hJ3j`) and `chartW0_hco_ball`/`chartW0_displacement` (`hco`/`hVdisp`), this closes the
  per-point BALL forms of ALL FIVE RNC chart-surface estimates; only the global gating layer remains.

  No `sorry`, no new axioms, no `:= True`; every hypothesis satisfiable and non-vacuous; none equals the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Hid2Germ
import QIQTH.InverseChartFirstJet
import QIQTH.UniformFlowHessianDiag

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap
open QIQTH.Hid2Germ QIQTH.ChartFieldC2General QIQTH.GeodesicGronwall
open QIQTH.JacobiCLMExposure QIQTH.ChartFieldJacobian QIQTH.ChartSecondJet
open scoped Topology BigOperators

/-! ############################################################################
    ### (A) The ABSTRACT reusable primitive — the second-order IFT operator-norm
    ### bound.  Pure calculus; no geometry.
    ############################################################################ -/

namespace QIQTH.InverseChartSecondJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **★ (A) THE SECOND-ORDER IFT OPERATOR-NORM PRIMITIVE — `secondJet_opNorm_le`.**  For continuous
    linear `I : E →L[ℝ] E` and bilinear `D2 : E →L[ℝ] (E →L[ℝ] E)` with `‖I‖ ≤ 2` and `‖D2‖ ≤ M`
    (`0 ≤ M`), the second-order ring-inverse expression obeys
        `‖(−mulLeftRight ℝ (E →L E) I I) ∘L (D2 ∘L I)‖ ≤ 8·M`.
    Proof: `‖mulLeftRight ℝ _ I I‖ ≤ ‖I‖·‖I‖` (`opNorm_le_bound` + `norm_mul_le` twice), then
    `opNorm_comp_le` gives `‖·‖ ≤ (‖I‖·‖I‖)·(‖D2‖·‖I‖) ≤ (2·2)·(M·2) = 8·M`.  ⚠ NOT `a₁ = R/6`. -/
theorem secondJet_opNorm_le (I : E →L[ℝ] E) (D2 : E →L[ℝ] (E →L[ℝ] E)) {M : ℝ}
    (hI : ‖I‖ ≤ 2) (hD2 : ‖D2‖ ≤ M) (hM : 0 ≤ M) :
    ‖(-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) I I).comp (D2.comp I)‖ ≤ 8 * M := by
  have hmlr : ‖ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) I I‖ ≤ ‖I‖ * ‖I‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    rw [ContinuousLinearMap.mulLeftRight_apply]
    calc ‖I * x * I‖ ≤ ‖I * x‖ * ‖I‖ := norm_mul_le _ _
      _ ≤ (‖I‖ * ‖x‖) * ‖I‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖I‖ * ‖I‖ * ‖x‖ := by ring
  have hQ : ‖D2.comp I‖ ≤ ‖D2‖ * ‖I‖ := ContinuousLinearMap.opNorm_comp_le _ _
  rw [ContinuousLinearMap.neg_comp, norm_neg]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  have h1 : ‖ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) I I‖ * ‖D2.comp I‖
      ≤ (‖I‖ * ‖I‖) * (‖D2‖ * ‖I‖) := by
    apply mul_le_mul hmlr hQ (norm_nonneg (D2.comp I))
    positivity
  refine le_trans h1 ?_
  calc (‖I‖ * ‖I‖) * (‖D2‖ * ‖I‖)
      ≤ (2 * 2) * (M * 2) := by gcongr
    _ = 8 * M := by ring

end QIQTH.InverseChartSecondJet

/-! ############################################################################
    ### (B) The CONCRETE discharge for the van-Vleck inverse chart on a ball.
    ############################################################################ -/

namespace QIQTH.HeatResidualBound

open QIQTH.InverseChartSecondJet QIQTH.InverseChartFirstJet

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-- **★ (B) `chartW0_secondJet_bound` — the mixed-sliver `hJ3Q` shape for the CONCRETE van-Vleck chart,
    per-point on a ball.**  There is `r > 0` and `C_Q ≥ 0` such that for every base point `z ∈ K` with
    `‖z‖ < r`, the inverse chart's SECOND jet at the origin is uniformly bounded:
        `‖fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0‖ ≤ C_Q`.
    Proof: the per-`z` 2nd-order IFT identity (`Hid2Germ.hid2_discharged`, via the right-inverse germ
    apparatus) writes the second jet as `(−mulLeftRight I I) ∘L (D²φ_z(W_z 0) ∘L I)`, `I =
    Ring.inverse (Dφ_z(W_z 0))`; `‖I‖ ≤ 2` from the forward Jacobian gap + `clm_inverse_sub_one_le`;
    `‖D²φ_z(W_z 0)‖ ≤ M'` from R3 (`uniformFlowExp_hessian_opNorm_le`); `secondJet_opNorm_le` combines
    them to `C_Q = 8·M'`.  ⚠ NOT `a₁ = R/6` — the GLOBAL `∀ z` form needs the gating layer. -/
theorem chartW0_secondJet_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∃ C_Q : ℝ, 0 ≤ C_Q ∧ ∀ z ∈ K, ‖z‖ < r →
      ‖fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0‖ ≤ C_Q := by
  classical
  obtain ⟨r₁, hr₁0, C_W, hCW0, hD1⟩ := chartW0_displacement g gi hC hK
  obtain ⟨rRI, hrRI0, hRIspec⟩ := chartW0_rightInverse g gi hC hK
  obtain ⟨δg, hδg0, hgermspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨δr, hδr0, hreach⟩ := chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨ρnd, hρnd0, hnondeg⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  obtain ⟨ρ₀, hρ₀0, C_D, hCD0, hnear⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  obtain ⟨r₀R3, hr₀R30, hr₀R3ρ, M', hR3⟩ := uniformFlowExp_hessian_opNorm_le g gi hC hK
  have hRf0 : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  -- ceiling for `‖W_z 0‖`: below every radius the germ apparatus + R3 + forward gap need.
  set Wbound : ℝ := min (min δg δr)
      (min (min (uniformFlowRadius g gi hC hK) ρnd) (min ρ₀ r₀R3)) with hWbdef
  have hWb_δg : Wbound ≤ δg := le_trans (min_le_left _ _) (min_le_left _ _)
  have hWb_δr : Wbound ≤ δr := le_trans (min_le_left _ _) (min_le_right _ _)
  have hWb_uf : Wbound ≤ uniformFlowRadius g gi hC hK :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hWb_ρnd : Wbound ≤ ρnd :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hWb_ρ₀ : Wbound ≤ ρ₀ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hWb_r₀R3 : Wbound ≤ r₀R3 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hWbpos : 0 < Wbound :=
    lt_min (lt_min hδg0 hδr0)
      (lt_min (lt_min hRf0 hρnd0) (lt_min hρ₀0 hr₀R30))
  have h1CW : (0 : ℝ) < 1 + C_W := by linarith
  -- the master small radius.
  set r : ℝ := min (min (min r₁ rRI) 1)
      (min (Wbound / (1 + C_W)) (1 / (2 * (C_D + 1) * (1 + C_W)))) with hrdef
  have hden2 : (0 : ℝ) < 2 * (C_D + 1) * (1 + C_W) := by
    have : (0 : ℝ) < C_D + 1 := by linarith
    positivity
  have hrpos : 0 < r := by
    rw [hrdef]
    exact lt_min (lt_min (lt_min hr₁0 hrRI0) one_pos)
      (lt_min (by positivity) (by positivity))
  refine ⟨r, hrpos, 8 * max M' 0, by positivity, ?_⟩
  intro z hz hzr
  -- unpack the master radius.
  rw [hrdef] at hzr
  simp only [lt_min_iff] at hzr
  obtain ⟨⟨⟨hzr₁, hzrRI⟩, hz1⟩, hzWb, hzCD⟩ := hzr
  have hz1' : ‖z‖ ≤ 1 := le_of_lt hz1
  -- displacement ⟹ `‖W_z 0‖ ≤ (1+C_W)‖z‖`.
  have hDisp : ‖uniformInverseChart g gi hC hK z 0 + z‖ ≤ C_W * ‖z‖ * ‖z‖ := hD1 z hz hzr₁
  have hWle : ‖uniformInverseChart g gi hC hK z 0‖ ≤ (1 + C_W) * ‖z‖ := by
    have htri : ‖uniformInverseChart g gi hC hK z 0‖
        ≤ ‖uniformInverseChart g gi hC hK z 0 + z‖ + ‖z‖ := by
      calc ‖uniformInverseChart g gi hC hK z 0‖
          = ‖(uniformInverseChart g gi hC hK z 0 + z) - z‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖uniformInverseChart g gi hC hK z 0 + z‖ + ‖z‖ := norm_sub_le _ _
    nlinarith [htri, hDisp, mul_nonneg (mul_nonneg hCW0 (norm_nonneg z)) (sub_nonneg.mpr hz1')]
  -- `‖W_z 0‖ < Wbound`.
  have hWlt : ‖uniformInverseChart g gi hC hK z 0‖ < Wbound := by
    have hstep : (1 + C_W) * ‖z‖ < (1 + C_W) * (Wbound / (1 + C_W)) :=
      mul_lt_mul_of_pos_left hzWb h1CW
    have heq : (1 + C_W) * (Wbound / (1 + C_W)) = Wbound := by
      field_simp
    exact lt_of_le_of_lt hWle (by rw [heq] at hstep; exact hstep)
  -- key smallness facts.
  have hRIz : uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0 :=
    hRIspec z hz hzrRI
  have hunitz : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)) :=
    hnondeg z hz (uniformInverseChart g gi hC hK z 0) (lt_of_lt_of_le hWlt hWb_ρnd)
  have hregz : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n) := by
    have hcd := hreach z hz (uniformInverseChart g gi hC hK z 0) (lt_of_lt_of_le hWlt hWb_δr)
    rwa [hRIz] at hcd
  have hφC2v₀ : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0) :=
    contDiffAt2_uniformFlowExp g gi hC hK z hz (uniformInverseChart g gi hC hK z 0)
      (lt_of_lt_of_le hWlt hWb_uf)
  -- ── the per-`z` 2nd-order IFT identity, via the `Hid2Germ` germ apparatus. ──
  have hWd0 : DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) 0 :=
    hregz.differentiableAt (by norm_num)
  have hφ2 : DifferentiableAt ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
      (uniformInverseChart g gi hC hK z 0) :=
    (hφC2v₀.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hleftv₀ : ∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z 0),
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v := by
    filter_upwards [((hgermspec z hz).1 (uniformInverseChart g gi hC hK z 0)
      (lt_of_lt_of_le hWlt hWb_δg)).1] with v hv using hv
  have hRightGerm := chartRightInverse_germ g gi hC hK z hφC2v₀ hunitz hleftv₀ hRIz
  -- the neighbourhood smallness bound near `0`.
  set m : ℝ := min (min δg (uniformFlowRadius g gi hC hK)) ρnd with hmdef
  have hmδg : m ≤ δg := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmR : m ≤ uniformFlowRadius g gi hC hK := le_trans (min_le_left _ _) (min_le_right _ _)
  have hmρnd : m ≤ ρnd := min_le_right _ _
  have hv₀m : ‖uniformInverseChart g gi hC hK z 0‖ < m :=
    lt_min (lt_min (lt_of_lt_of_le hWlt hWb_δg) (lt_of_lt_of_le hWlt hWb_uf))
      (lt_of_lt_of_le hWlt hWb_ρnd)
  have hmnhds : Metric.ball (0 : Point n) m ∈ 𝓝 (uniformInverseChart g gi hC hK z 0) :=
    Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hv₀m)
  have hEnorm : ∀ᶠ y in 𝓝 (0 : Point n),
      uniformInverseChart g gi hC hK z y ∈ Metric.ball (0 : Point n) m :=
    hregz.continuousAt.eventually_mem hmnhds
  have hφdGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      DifferentiableAt ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z y) := by
    filter_upwards [hEnorm] with y hy
    exact (contDiffAt2_uniformFlowExp g gi hC hK z hz (uniformInverseChart g gi hC hK z y)
      (lt_of_lt_of_le (mem_ball_zero_iff.mp hy) hmR)).differentiableAt (by norm_num)
  have hWdGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) y := by
    filter_upwards [hregz.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hleftGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      ∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z y),
        uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v := by
    filter_upwards [hEnorm] with y hy
    filter_upwards [((hgermspec z hz).1 (uniformInverseChart g gi hC hK z y)
      (lt_of_lt_of_le (mem_ball_zero_iff.mp hy) hmδg)).1] with v hv using hv
  have hunitGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z y)) := by
    filter_upwards [hEnorm] with y hy
    exact hnondeg z hz (uniformInverseChart g gi hC hK z y)
      (lt_of_lt_of_le (mem_ball_zero_iff.mp hy) hmρnd)
  have hid2 := hid2_discharged g gi hC hK z hWd0 hφ2 hRIz hunitz
    hRightGerm hφdGerm hWdGerm hleftGerm hunitGerm
  -- ── the two operator-norm inputs. ──
  set Df : Point n →L[ℝ] Point n :=
    fderiv ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z 0) with hDfdef
  set I : Point n →L[ℝ] Point n := Ring.inverse Df with hIdef
  -- `‖I‖ ≤ 2` from the forward Jacobian gap.
  have hIbound : ‖I‖ ≤ 2 := by
    rcases subsingleton_or_nontrivial (Point n) with hsub | hns
    · -- trivial space: everything is `0`, so `‖I‖ = 0 ≤ 2`.
      have : I = 0 := Subsingleton.elim _ _
      rw [this, norm_zero]; norm_num
    · haveI := hns
      have hnearz : ‖Df - ContinuousLinearMap.id ℝ (Point n)‖
          ≤ C_D * ‖uniformInverseChart g gi hC hK z 0‖ :=
        hnear z hz (uniformInverseChart g gi hC hK z 0) (lt_of_lt_of_le hWlt hWb_ρ₀)
      have hDf1 : ‖Df - (1 : Point n →L[ℝ] Point n)‖
          ≤ C_D * ‖uniformInverseChart g gi hC hK z 0‖ := by
        rw [ContinuousLinearMap.one_def]; exact hnearz
      -- `C_D · ‖W_z 0‖ ≤ 1/2`.
      have hCDw : C_D * ‖uniformInverseChart g gi hC hK z 0‖ ≤ 1 / 2 := by
        have hle : C_D * ‖uniformInverseChart g gi hC hK z 0‖ ≤ C_D * ((1 + C_W) * ‖z‖) :=
          mul_le_mul_of_nonneg_left hWle hCD0
        have hzsmall : (1 + C_W) * ‖z‖ ≤ 1 / (2 * (C_D + 1)) := by
          have hstep : (1 + C_W) * ‖z‖ < (1 + C_W) * (1 / (2 * (C_D + 1) * (1 + C_W))) :=
            mul_lt_mul_of_pos_left hzCD h1CW
          have heq : (1 + C_W) * (1 / (2 * (C_D + 1) * (1 + C_W))) = 1 / (2 * (C_D + 1)) := by
            field_simp
          rw [heq] at hstep; exact le_of_lt hstep
        have hCDle : C_D * ((1 + C_W) * ‖z‖) ≤ C_D * (1 / (2 * (C_D + 1))) :=
          mul_le_mul_of_nonneg_left hzsmall hCD0
        have hfin : C_D * (1 / (2 * (C_D + 1))) ≤ 1 / 2 := by
          have hden : (0 : ℝ) < 2 * (C_D + 1) := by nlinarith [hCD0]
          rw [mul_one_div, div_le_iff₀ hden]; nlinarith [hCD0]
        linarith [hle, hCDle, hfin]
      obtain ⟨hunitDf, hinv1⟩ := clm_inverse_sub_one_le Df hDf1 hCDw
      -- `‖I‖ ≤ ‖I − 1‖ + ‖1‖ ≤ 2·(1/2) + 1 = 2`.
      have hone : ‖(1 : Point n →L[ℝ] Point n)‖ = 1 := by
        rw [ContinuousLinearMap.one_def]; exact ContinuousLinearMap.norm_id
      have htri : ‖I‖ ≤ ‖I - 1‖ + ‖(1 : Point n →L[ℝ] Point n)‖ := by
        calc ‖I‖ = ‖(I - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖I - 1‖ + ‖(1 : Point n →L[ℝ] Point n)‖ := norm_add_le _ _
      rw [hIdef] at htri ⊢
      rw [hone] at htri
      linarith [hinv1, htri, hCDw]
  -- `‖D²φ_z(W_z 0)‖ ≤ M'` from R3.
  have hD2bound : ‖fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
      (uniformInverseChart g gi hC hK z 0)‖ ≤ M' :=
    hR3 z hz (uniformInverseChart g gi hC hK z 0) (lt_of_lt_of_le hWlt hWb_r₀R3)
  have hM'0 : 0 ≤ M' := le_trans (norm_nonneg
    (fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
      (uniformInverseChart g gi hC hK z 0))) hD2bound
  -- ── combine. ──
  rw [hid2]
  have hcombine := secondJet_opNorm_le I
    (fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
      (uniformInverseChart g gi hC hK z 0)) hIbound hD2bound hM'0
  refine le_trans hcombine ?_
  gcongr
  exact le_max_left _ _

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.InverseChartSecondJet.secondJet_opNorm_le
#print axioms QIQTH.HeatResidualBound.chartW0_secondJet_bound
