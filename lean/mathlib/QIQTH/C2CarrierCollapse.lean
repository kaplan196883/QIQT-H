/-
  C2CarrierCollapse — J4-488: collapsing `supConstant_phase4`'s STANDING GEOMETRIC CARRIERS to the
  single (I1) reachability input (+ the isolated second-order IFT residue).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.  std-3
  only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT.  `AmplitudeSecondJet.supConstant_phase4` grounded the whole sup family `M₀`/`M₁`/`M₂`
  (= `C₀`/`C₁`/`C₂`) MODULO (I1) `hReach` PLUS the STANDING GEOMETRIC CARRIES on `closedBall 0 ρ`:
      `hUK`  (`closedBall 0 ρ ⊆ K`),  `hW0` (origin-section continuity),  `horigin` (origin smallness),
      `hunit` (forward-Jacobian nondegeneracy),  `hid2` (2nd-order IFT identity),  `hJac` (field-Jacobian
      continuity),  `hreg` (reachable `C²` at the centre).
  These seven were carried as HYPOTHESES with the small-ball domain reconciliation left as the "stated
  residual" (SupFamilyFirstOrder's DOMAIN RESIDUAL v3).  THIS BRICK DISCHARGES that reconciliation:
  it exhibits a CONCRETE small ball on which SIX of the seven carriers hold, from the BANKED
  chart-regularity lemmas alone — collapsing `supConstant_phase4` to a statement resting on
  (I1) `hReach` + the SINGLE isolated second-order IFT residue `hid2`.

  ## THE GATES (per carrier — the banked discharger + the smallness bookkeeping).
    * `hUK`     ⟸ `K ∈ 𝓝 0` (`Metric.mem_nhds_iff`) — pick `ρ` below the `𝓝`-ball radius.
    * `horigin` ⟸ `chartW0_displacement` (`‖W₀ z‖ ≤ (1+C_W)‖z‖`) — pick `ρ` below all field radii.
    * `hunit`   ⟸ `uniformFlowExp_common_nondeg_radius` (`IsUnit` for `‖v‖ < ρnd`).
    * `hreg`    ⟸ `chartField_contDiffAt_reachable_uniform` (reachable `C²` at `φ_z v`) + the right
                inverse `chartW0_rightInverse` (`φ_z (W₀ z) = 0`).
    * `hW0`     ⟸ `GeodesicGronwall.chartOrigin_continuousOn` (Lipschitz-in-base) — its `hball`/`hnorm`/
                `hRI` supplied by the displacement bound + the right inverse.
    * `hJac`    ⟸ `JacobiCLMExposure.chartFieldJacobian_continuousOn` (UNCONDITIONAL per J4-435), whose
                `hIFT` is `ChartFieldJacobian.chartFieldJacobian_eq_ringInverse` from the banked
                per-`z` regularity facts (`contDiffAt2_uniformFlowExp` + the left-inverse germ + `hunit`).
    * `hid2`    ⚠ THE ISOLATED RESIDUE, NOT discharged here: the per-`z` 2nd-order IFT identity
                (`ChartSecondJet.chartSecondJet_eq_of_forward2`) needs the FDERIV-germ
                `∀ᶠ y, fderiv (W z) y = Ring.inverse (fderiv φ_z (W z y))`, i.e. the RIGHT-inverse germ
                `φ_z ∘ W_z = id` near `0` — a distinct sub-brick (the natural J4-489).  Carried as a
                labelled, satisfiable, ball-scoped hypothesis.

  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `c2_carriers_discharged` — ★★ SIX of the seven carriers on a CONCRETE small ball, from the bank
      alone (no (I1), no residue): `∃ ρ > 0, hUK ∧ hW0 ∧ horigin ∧ hunit ∧ hJac ∧ hreg`.
    * `supConstant_phase5`     — ★★★ the sup family, phase 5: on that concrete ball, `C₀`/`C₁`/`C₂` are
      grounded from (I1) `hReach` + the SINGLE remaining second-order residue `hid2` — the six geometric
      carriers are supplied INTERNALLY.  C₀ unconditional, C₁ geometric-closed, C₂ on (I1) + `hid2`.

  ⚠ CARRIED (labelled, satisfiable, non-vacuous, NEVER a conclusion): (I1) `hReach` and the isolated
    2nd-order IFT residue `hid2`.  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.AmplitudeSecondJet
import QIQTH.InverseChartDisplacement
import QIQTH.ResidueThreading
import QIQTH.UniformChartRadius
import QIQTH.ChartFieldC2General
import QIQTH.UniformFlowNondegClose
import QIQTH.GeodesicGronwall
import QIQTH.JacobiCLMExposure
import QIQTH.ChartFieldJacobian
import QIQTH.ChartSecondJet

open Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.ChartFieldC2General QIQTH.GeodesicGronwall QIQTH.JacobiCLMExposure
open QIQTH.ChartFieldJacobian QIQTH.ChartSecondJet QIQTH.AmplitudeSecondJet
open QIQTH.SupFamilyFirstOrder QIQTH.SupConstantFamily QIQTH.AmplitudeDataOnCollar
open QIQTH.HrepGermFactorization
open scoped Topology ContDiff

namespace QIQTH.C2CarrierCollapse

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★ THE CARRIER DISCHARGE — six of the seven carriers on a concrete small ball.
    ############################################################################### -/

/-- **★★ `c2_carriers_discharged` — the geometric-carrier bundle on a concrete small ball.**  There is
    a CONCRETE small radius `ρ > 0` such that on `closedBall 0 ρ` SIX of the seven `supConstant_phase4`
    carriers hold, each from the BANKED chart-regularity lemmas (NO (I1), NO 2nd-order residue):
      • `hUK`     — `closedBall 0 ρ ⊆ K`   (`ρ` below the `K ∈ 𝓝 0` ball radius);
      • `hW0`     — origin-section base continuity   (`chartOrigin_continuousOn`);
      • `horigin` — origin smallness `‖W₀ z‖ < uniformFlowRadius`   (`chartW0_displacement`);
      • `hunit`   — forward-Jacobian nondegeneracy   (`uniformFlowExp_common_nondeg_radius`);
      • `hJac`    — field-Jacobian base continuity   (`chartFieldJacobian_continuousOn` + the IFT identity);
      • `hreg`    — reachable `C²` at the centre   (`chartField_contDiffAt_reachable_uniform` + right inverse).
    Mechanism: pick `ρ` below every banked radius AND below `Wbound/(1+C_W)` where the displacement
    bound `chartW0_displacement` gives `‖W₀ z‖ ≤ (1+C_W)‖z‖`; then every carrier's smallness
    side-condition (`‖W₀ z‖ < δ_·`) is met, the right inverse `chartW0_rightInverse` holds, and each
    banked discharger fires.  NOT `a₁ = R/6`. -/
theorem c2_carriers_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    ∃ ρ > (0 : ℝ),
      Metric.closedBall (0 : Point n) ρ ⊆ K
      ∧ ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0)
          (Metric.closedBall (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK)
      ∧ (∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
            (uniformInverseChart g gi hC hK z 0)))
      ∧ ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0)
          (Metric.closedBall (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n)) := by
  classical
  -- the banked uniform radii.
  obtain ⟨εK, hεK0, hεKsub⟩ := Metric.mem_nhds_iff.mp h0Kmem
  obtain ⟨r₁, hr₁0, C_W, hCW0, hD1⟩ := chartW0_displacement g gi hC hK
  obtain ⟨rRI, hrRI0, hRIspec⟩ := chartW0_rightInverse g gi hC hK
  obtain ⟨δg, hδg0, hgermspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨δr, hδr0, hreach⟩ := chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨ρnd, hρnd0, hnondeg⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  set δlip : ℝ := (chartOrigin_lipschitz_modulus g gi hC hK).choose with hδlipdef
  have hδlip0 : 0 < δlip := (chartOrigin_lipschitz_modulus g gi hC hK).choose_spec.1
  -- the ceiling for `‖W₀ z‖`.
  set Wbound : ℝ := min (min δg δr) (min (min (uniformFlowRadius g gi hC hK) ρnd) δlip) with hWbdef
  have hWb_δg : Wbound ≤ δg := le_trans (min_le_left _ _) (min_le_left _ _)
  have hWb_δr : Wbound ≤ δr := le_trans (min_le_left _ _) (min_le_right _ _)
  have hWb_uf : Wbound ≤ uniformFlowRadius g gi hC hK :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hWb_ρnd : Wbound ≤ ρnd :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hWb_δlip : Wbound ≤ δlip := le_trans (min_le_right _ _) (min_le_right _ _)
  have hWbpos : 0 < Wbound :=
    lt_min (lt_min hδg0 hδr0) (lt_min (lt_min (uniformFlowRadius_pos g gi hC hK) hρnd0) hδlip0)
  have h1CW : (0 : ℝ) < 1 + C_W := by linarith
  -- the master small radius (half of the min, for STRICT inequalities on `closedBall`).
  set base : ℝ := min (min εK r₁) (min rRI (min 1 (Wbound / (1 + C_W)))) with hbasedef
  have hbase0 : 0 < base :=
    lt_min (lt_min hεK0 hr₁0) (lt_min hrRI0 (lt_min one_pos (by positivity)))
  set ρ : ℝ := base / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  -- `ρ` is STRICTLY below every component of `base`.
  have hρbase : ρ < base := by rw [hρdef]; linarith
  have hρ_lt : ∀ x : ℝ, base ≤ x → ρ < x := fun x hx => lt_of_lt_of_le hρbase hx
  have hρεK : ρ < εK := hρ_lt εK (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρr₁ : ρ < r₁ := hρ_lt r₁ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρrRI : ρ < rRI := hρ_lt rRI (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ1 : ρ < 1 := hρ_lt 1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρWb : ρ < Wbound / (1 + C_W) :=
    hρ_lt _ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- `hUK`.
  have hUK : Metric.closedBall (0 : Point n) ρ ⊆ K := by
    intro x hx
    have hxn : ‖x‖ ≤ ρ := mem_closedBall_zero_iff.mp hx
    exact hεKsub (mem_ball_zero_iff.mpr (lt_of_le_of_lt hxn hρεK))
  -- the per-`z` package on the ball.
  have hzfacts : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      z ∈ K
      ∧ ‖uniformInverseChart g gi hC hK z 0‖ < Wbound
      ∧ uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0 := by
    intro z hz
    have hzn : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp hz
    have zK : z ∈ K := hUK hz
    have hzr₁ : ‖z‖ < r₁ := lt_of_le_of_lt hzn hρr₁
    have hzrRI : ‖z‖ < rRI := lt_of_le_of_lt hzn hρrRI
    have hz1 : ‖z‖ ≤ 1 := le_of_lt (lt_of_le_of_lt hzn hρ1)
    -- displacement ⟹ `‖W₀ z‖ ≤ (1+C_W)‖z‖`.
    have hDisp : ‖uniformInverseChart g gi hC hK z 0 + z‖ ≤ C_W * ‖z‖ * ‖z‖ := hD1 z zK hzr₁
    have hWle : ‖uniformInverseChart g gi hC hK z 0‖ ≤ (1 + C_W) * ‖z‖ := by
      have htri : ‖uniformInverseChart g gi hC hK z 0‖
          ≤ ‖uniformInverseChart g gi hC hK z 0 + z‖ + ‖z‖ := by
        calc ‖uniformInverseChart g gi hC hK z 0‖
            = ‖(uniformInverseChart g gi hC hK z 0 + z) - z‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖uniformInverseChart g gi hC hK z 0 + z‖ + ‖z‖ := norm_sub_le _ _
      nlinarith [htri, hDisp, mul_nonneg (mul_nonneg hCW0 (norm_nonneg z)) (sub_nonneg.mpr hz1)]
    have hWlt : ‖uniformInverseChart g gi hC hK z 0‖ < Wbound := by
      have hstep : (1 + C_W) * ‖z‖ ≤ (1 + C_W) * ρ :=
        mul_le_mul_of_nonneg_left hzn (le_of_lt h1CW)
      have hlt : (1 + C_W) * ρ < Wbound := by
        rw [mul_comm]; exact (lt_div_iff₀ h1CW).mp hρWb
      exact lt_of_le_of_lt (le_trans hWle hstep) hlt
    have hRIz : uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0 :=
      hRIspec z zK hzrRI
    exact ⟨zK, hWlt, hRIz⟩
  -- `horigin`.
  have horigin : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK := by
    intro z hz
    exact lt_of_lt_of_le (hzfacts z hz).2.1 hWb_uf
  -- `hunit`.
  have hunit : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z 0)) := by
    intro z hz
    obtain ⟨zK, hWlt, _⟩ := hzfacts z hz
    exact hnondeg z zK (uniformInverseChart g gi hC hK z 0) (lt_of_lt_of_le hWlt hWb_ρnd)
  -- `hreg`.
  have hreg : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n) := by
    intro z hz
    obtain ⟨zK, hWlt, hRIz⟩ := hzfacts z hz
    have hcd := hreach z zK (uniformInverseChart g gi hC hK z 0) (lt_of_lt_of_le hWlt hWb_δr)
    rwa [hRIz] at hcd
  -- `hW0`.
  have hball : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      uniformInverseChart g gi hC hK z 0 ∈ Metric.ball (0 : Point n) δlip := by
    intro z hz
    exact mem_ball_zero_iff.mpr (lt_of_lt_of_le (hzfacts z hz).2.1 hWb_δlip)
  have hnorm : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ‖uniformInverseChart g gi hC hK z 0‖ ≤ uniformFlowRadius g gi hC hK :=
    fun z hz => le_of_lt (horigin z hz)
  have hRI : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0 :=
    fun z hz => (hzfacts z hz).2.2
  have hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0)
      (Metric.closedBall (0 : Point n) ρ) :=
    chartOrigin_continuousOn g gi hC hK hUK hball hnorm hRI
  -- `hIFT` (per `z`) ⟹ `hJac`.
  have hIFT : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      fderiv ℝ (uniformInverseChart g gi hC hK z) 0
        = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
            (uniformInverseChart g gi hC hK z 0)) := by
    intro z hz
    obtain ⟨zK, hWlt, hRIz⟩ := hzfacts z hz
    have hφd : DifferentiableAt ℝ (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0) :=
      (contDiffAt2_uniformFlowExp g gi hC hK z zK (uniformInverseChart g gi hC hK z 0)
        (lt_of_lt_of_le hWlt hWb_uf)).differentiableAt (by norm_num)
    have hWd : DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) 0 :=
      (hreg z hz).differentiableAt (by norm_num)
    have hgerm : ∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z 0),
        uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v := by
      have hge := ((hgermspec z zK).1 (uniformInverseChart g gi hC hK z 0)
        (lt_of_lt_of_le hWlt hWb_δg)).1
      filter_upwards [hge] with v hv using hv
    exact chartFieldJacobian_eq_ringInverse g gi hC hK z hφd hWd hgerm hRIz (hunit z hz)
  have hJac : ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0)
      (Metric.closedBall (0 : Point n) ρ) :=
    chartFieldJacobian_continuousOn g gi hC hK hUK hW0 horigin hunit hIFT
  exact ⟨ρ, hρ0, hUK, hW0, horigin, hunit, hJac, hreg⟩

/-! ###############################################################################
    ### ★★★ THE PACKAGE — the sup family, phase 5 (C₂ on (I1) + the isolated `hid2`).
    ############################################################################### -/

/-- **★★★ `supConstant_phase5` — the sup/constant family, phase 5.**  On a CONCRETE small ball (supplied
    internally by `c2_carriers_discharged`), the whole sup family `M₀`/`M₁`/`M₂` (= `C₀`/`C₁`/`C₂`, and
    hence `Sconst`) is grounded from just TWO carried inputs: (I1) `hReach` and the ISOLATED second-order
    IFT residue `hid2` (the per-`z` chart 2nd-jet identity on the exposed ball).  The SIX other geometric
    carriers of `supConstant_phase4` — `hUK`/`hW0`/`horigin`/`hunit`/`hJac`/`hreg` — are DISCHARGED
    internally from the banked chart-regularity lemmas.  `C₀` is UNCONDITIONAL, `C₁` geometric-closed,
    `C₂` rests on (I1) + `hid2`.  Carries (I1) `hReach` + the 2nd-order IFT residue `hid2`.
    NOT `a₁ = R/6`. -/
theorem supConstant_phase5 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b c τ₀ : ℝ) (i : Fin n)
    (hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q) :
    ∃ ρ, 0 < ρ ∧
      ((∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0
            = (-ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
                  (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                    (uniformInverseChart g gi hC hK z 0)))
                  (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                    (uniformInverseChart g gi hC hK z 0)))).comp
              ((fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
                    (uniformInverseChart g gi hC hK z 0)).comp
                (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                  (uniformInverseChart g gi hC hK z 0))))) →
        (∃ ρ₀ > (0 : ℝ), ∃ M₀ : ℝ, 0 ≤ M₀ ∧
            ∀ τ z, collarRegime (K := K) ρ₀ c τ₀ τ z → |chartAmp g gi hC hK a b τ z 0| ≤ M₀)
        ∧ (∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
            |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)| ≤ M₁)
        ∧ (∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
            |pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0| ≤ M₂)) := by
  obtain ⟨ρ, hρ0, hUK, hW0, horigin, hunit, hJac, hreg⟩ :=
    c2_carriers_discharged g gi hC hK h0Kmem
  refine ⟨ρ, hρ0, fun hid2 => ?_⟩
  exact supConstant_phase4 g gi hC hK h0Kmem hg hgi hgpos a b c τ₀ i ρ hρ0 hUK hReach
    hW0 horigin hunit hid2 hJac hreg

end QIQTH.C2CarrierCollapse

/-! ## THE CARRIER LEDGER (post J4-488).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE STANDING CARRIES.  `AmplitudeSecondJet.supConstant_phase4` grounded `C₀`/`C₁`/`C₂` MODULO      │
  │  (I1) `hReach` PLUS the seven geometric carries on `closedBall 0 ρ`:                                │
  │    `hUK` · `hW0` · `horigin` · `hunit` · `hid2` · `hJac` · `hreg`.                                  │
  │  SupFamilyFirstOrder left the small-ball reconciliation as the "stated residual".                   │
  ├──────────┬────────────────────────────────────────────────────────────────────────────────────┤
  │ CARRIER  │ GATE (this brick)                                                                     │
  ├──────────┼────────────────────────────────────────────────────────────────────────────────────┤
  │ hUK      │ DISCHARGED.  `K ∈ 𝓝 0` (`Metric.mem_nhds_iff`); `ρ` below the `𝓝`-ball radius.        │
  │ horigin  │ DISCHARGED.  `chartW0_displacement` (`‖W₀ z‖ ≤ (1+C_W)‖z‖`) + `ρ` below the radii.     │
  │ hunit    │ DISCHARGED.  `uniformFlowExp_common_nondeg_radius` at `‖W₀ z‖ < ρnd`.                  │
  │ hreg     │ DISCHARGED.  `chartField_contDiffAt_reachable_uniform` + `chartW0_rightInverse`.        │
  │ hW0      │ DISCHARGED.  `GeodesicGronwall.chartOrigin_continuousOn` (hball/hnorm/hRI from smallness).│
  │ hJac     │ DISCHARGED.  `JacobiCLMExposure.chartFieldJacobian_continuousOn` + the IFT identity     │
  │          │              `ChartFieldJacobian.chartFieldJacobian_eq_ringInverse`.                    │
  │ hid2     │ ⚠ RESIDUE (folds toward (I1)).  The per-`z` 2nd-order IFT identity needs the FDERIV-germ  │
  │          │   / RIGHT-inverse germ `φ_z ∘ W_z = id` near `0` — a distinct sub-brick (J4-489).        │
  ├──────────┴────────────────────────────────────────────────────────────────────────────────────┤
  │  THE OUTCOME.  `supConstant_phase5`: the whole sup family is grounded on a CONCRETE small ball from │
  │  just (I1) `hReach` + the ISOLATED second-order residue `hid2`.  Six carriers gone; C₀ UNCONDITIONAL,│
  │  C₁ geometric-closed, C₂ on (I1) + `hid2`.  NEVER `a₁ = R/6`.                                       │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── DONT-UNDERCREDIT findings.
    * NONE of the six discharged carriers needed (I1) `hReach`: the reachable-`C²`, nondegeneracy,
      displacement, origin-continuity and field-Jacobian lemmas are all K-uniform WITHOUT `expRho`.
      Only the 2nd-jet WALL (inside `hcont2_of_reach`) and the isolated `hid2` touch `hReach`.
    * The small-ball reconciliation was NOT a new analytic wall: it is pure radius bookkeeping over the
      ALREADY-BANKED uniform radii (`chartW0_displacement`/`chartW0_rightInverse`/
      `uniformInverseChart_huniformChart`/`chartField_contDiffAt_reachable_uniform`/
      `uniformFlowExp_common_nondeg_radius`/`chartOrigin_lipschitz_modulus`), exactly the "stated
      residual" SupFamilyFirstOrder flagged — now discharged.
    * `hid2` is the SOLE geometric carrier that does not collapse here; it is a genuine second-order germ
      sub-brick, not an assembly gap.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL (on (I1) `hReach`, the isolated `hid2`, the banked
    convergence trio, and the geometric wiring).
-/

section AxiomChecks
open QIQTH.C2CarrierCollapse
#print axioms c2_carriers_discharged
#print axioms supConstant_phase5
end AxiomChecks
