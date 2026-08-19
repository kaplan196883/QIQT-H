/-
  GeodesicReversalRouteAtPoint — Plan v9 Task B (STEP 1–3): the GENERIC-BASE-POINT `x₀`
  generalization of the geodesic-reversal route.

  ROLE.  `QIQTH.GeodesicReversalRoute` (J4-273) + `QIQTH.TerminalVelC2` (J4-274) built the base↔eval
  reversal identity ONLY at the hard-coded centre `0`:
      `U z 0 =ᶠ[𝓝 0] − T₀ (U 0 z)`,     `U p x := uniformInverseChart g gi hC hK p x`,
      `T₀ v := (uniformFlowTube g gi hC hK 0 v 1).2`.
  Every consumer that needs the base↔eval swap at a GENERIC field point `x₀` (e.g.
  `VanVleckGatedSpatialSymmetry.hcomp`) was blocked because the identity is CENTRE-ANCHORED.  This
  file re-derives the whole reversal identity at an ARBITRARY fixed base point `x₀ ∈ K`:
      `U z x₀ =ᶠ[𝓝 x₀] − T_{x₀} (U x₀ z)`,     `T_{x₀} v := (uniformFlowTube g gi hC hK x₀ v 1).2`,
  by mirroring the two source files' EXACT proof techniques with `x₀` in place of `0`.  This is
  possible because every underlying mechanism is already BASE-GENERIC:
    • `uniformFlow_reversal_reach`         — the reversed-geodesic reachability, stated `∀ q w`.
    • `uniformFlowExp_contDiffAt_four`     — the position-endpoint `C⁴`, stated `∀ z ∈ K`.
    • `uniformFlowExp_zero`                — `E x₀ 0 = x₀`, stated `∀ q ∈ K`.
    • `uniformFlowExp_approximatesLinearOn`, `uniformInverseChart_huniformChart` — chart data `∀ q ∈ K`.
    • `chartField_contDiffAt_center_at`    — the field-slot chart `C²` at the base, stated `∀ w ∈ K`.
    • `scaleVel`, `geodesicField_scaleVel` — the velocity-scaling algebra, base-independent.

  ── PIECE STATUS (honest firewall — NOT `a₁ = R/6`). ──
    • (STEP 2) `terminalVelAt`, `terminalVelAt_norm_le`, `uniformFlow_scale_position_at`,
          `terminalVelAt_apply_eq_fderiv_diag`, `terminalVelAt_contDiffAt_two` — the `x₀`-analogue of
          `terminalVel0` and its `C²` regularity, via the SAME homogeneity route
          (`terminalVel_{x₀} =ᶠ v ↦ fderiv (uniformFlowExp x₀) v [v]`, banked `C⁴` ⟹ `C³ ⟹ C²`).
          UNCONDITIONAL given `x₀ ∈ K`.
    • (STEP 1) `chartAt_rightInverse` — the base-`x₀` chart RIGHT inverse `E x₀ (U x₀ z) = z` near `x₀`.
    • (STEP 3) `baseSlot_eventuallyEq_neg_terminalVel_at` — THE GENERIC-BASE REVERSAL IDENTITY
          `U z x₀ =ᶠ[𝓝 x₀] − T_{x₀} (U x₀ z)`, fully derived from STEP 1 + reachability + the base-`z`
          left-inverse germ.
    • (CAPSTONE) `baseSlot_contDiffAt_two_at` — the base-slot `C²`, `ContDiffAt ℝ 2 (z ↦ U z x₀) x₀`,
          UNCONDITIONAL given `x₀` interior to `K` (generic-base analogue of the whole reversal +
          `TerminalVelC2` capstone, now at any `x₀`, not just `0`).

  ⚠ HONESTY FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  No `sorry` (prose only), no new
  axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypotheses.  The only
  hypotheses are the standing geometry `(hC, hK)` plus `x₀ ∈ K` / `K ∈ 𝓝 x₀`, all satisfiable at any
  concrete curved metric (e.g. `K = closedBall x₀ 1`, `x₀` arbitrary — a genuinely curved, non-vacuous
  witness).  `terminalVelAt` is a genuinely DIFFERENT function's regularity, reached through the
  nontrivial reversal identity; it does not trivially yield the conclusion.  No existing file is edited.
-/
import Mathlib
import QIQTH.TerminalVelC2
import QIQTH.FrozenBaseWChain
import QIQTH.UniformChartRadius

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.ChartThirdJet QIQTH.GeodesicReversalRoute QIQTH.TerminalVelC2 QIQTH.FrozenBaseWChain
open scoped Topology

namespace QIQTH.GeodesicReversalRouteAtPoint

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### STEP 2a — the base-`x₀` terminal-velocity map `T_{x₀}` and its confinement. -/

/-- **`terminalVelAt x₀` — the base-`x₀` terminal velocity** `T_{x₀} v := (uniformFlowTube x₀ v 1).2`,
    the velocity component at time `1` of the confined geodesic starting at `(x₀, v)`.  The generic-base
    analogue of `terminalVel0`. -/
noncomputable def terminalVelAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (x₀ : Point n) : Point n → Point n :=
  fun v => (uniformFlowTube g gi hC hK x₀ v 1).2

/-- **Terminal-velocity confinement at base `x₀`.**  For `‖v‖ ≤ ρ_K` the terminal velocity is
    controlled linearly, `‖T_{x₀} v‖ ≤ C₀ ‖v‖`, from the tube's `C₀‖v‖`-confinement near `(x₀,0)` at
    `t = 1`.  Generic-base analogue of `terminalVel0_norm_le`.  NOT `a₁ = R/6`. -/
theorem terminalVelAt_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) (v : Point n)
    (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK) :
    ‖terminalVelAt g gi hC hK x₀ v‖ ≤ uniformFlowConst g gi hC hK * ‖v‖ := by
  have hconf := uniformFlowTube_spec_conf g gi hC hK x₀ hx₀K v hv 1
    (Set.right_mem_Icc.mpr zero_le_one)
  set P : Point n × Point n := uniformFlowTube g gi hC hK x₀ v 1 with hP
  have hP2 : P.2 = (P - ((x₀, 0) : Point n × Point n)).2 := by simp
  have hle : ‖(P - ((x₀, 0) : Point n × Point n)).2‖ ≤ ‖P - ((x₀, 0) : Point n × Point n)‖ := by
    rw [Prod.norm_def]; exact le_max_right _ _
  calc ‖terminalVelAt g gi hC hK x₀ v‖ = ‖P.2‖ := rfl
    _ = ‖(P - ((x₀, 0) : Point n × Point n)).2‖ := by rw [hP2]
    _ ≤ ‖P - ((x₀, 0) : Point n × Point n)‖ := hle
    _ ≤ uniformFlowConst g gi hC hK * ‖v‖ := hconf

/-! ### STEP 2b — the reparametrisation (homogeneity) identity at base `x₀`. -/

/-- **REPARAMETRISATION / HOMOGENEITY at base `x₀`.**  For `‖v‖ ≤ ρ_K` and `s ∈ [0,1]`,
        `uniformFlowExp x₀ (s • v) = (uniformFlowTube x₀ v s).1`.
    Generic-base analogue of `uniformFlow_scale_position`; the rescaled curve `Z t := scaleVel s (Y (s·t))`
    (`Y := uniformFlowTube x₀ v`) solves the SAME geodesic system, confined to the common ball
    `closedBall (x₀,0) (C₀‖v‖)` (using `scaleVel s (x₀,0) = (x₀,0)` and nonexpansiveness of `scaleVel s`).
    NOT `a₁ = R/6`. -/
theorem uniformFlow_scale_position_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) (v : Point n)
    (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    uniformFlowExp g gi hC hK x₀ (s • v) = (uniformFlowTube g gi hC hK x₀ v s).1 := by
  obtain ⟨hs0, hs1⟩ := hs
  set Y : ℝ → Point n × Point n := uniformFlowTube g gi hC hK x₀ v with hYdef
  set sv : Point n := s • v with hsvdef
  have hsv_le : ‖sv‖ ≤ uniformFlowRadius g gi hC hK := by
    rw [hsvdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    calc s * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg v)
      _ = ‖v‖ := one_mul _
      _ ≤ _ := hv
  set Z : ℝ → Point n × Point n := fun t => scaleVel s (Y (s * t)) with hZdef
  set V : ℝ → Point n × Point n := uniformFlowTube g gi hC hK x₀ sv with hVdef
  -- Specs.
  have hY0 : Y 0 = (x₀, v) := uniformFlowTube_spec_ic g gi hC hK x₀ hx₀K v hv
  have hYode : ∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t :=
    uniformFlowTube_spec_ode g gi hC hK x₀ hx₀K v hv
  have hYconf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Y t - ((x₀, 0) : Point n × Point n)‖ ≤ uniformFlowConst g gi hC hK * ‖v‖ :=
    uniformFlowTube_spec_conf g gi hC hK x₀ hx₀K v hv
  have hV0 : V 0 = (x₀, sv) := uniformFlowTube_spec_ic g gi hC hK x₀ hx₀K sv hsv_le
  have hVode : ∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt V (geodesicField g gi (V t)) t :=
    uniformFlowTube_spec_ode g gi hC hK x₀ hx₀K sv hsv_le
  have hVconf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖V t - ((x₀, 0) : Point n × Point n)‖ ≤ uniformFlowConst g gi hC hK * ‖sv‖ :=
    uniformFlowTube_spec_conf g gi hC hK x₀ hx₀K sv hsv_le
  -- `scaleVel s` fixes `(x₀,0)`.
  have hfix : scaleVel s ((x₀, 0) : Point n × Point n) = ((x₀, 0) : Point n × Point n) := by
    rw [scaleVel_apply]; simp
  -- Interval helpers.
  have hst_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, s * t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    refine ⟨mul_nonneg hs0 ht.1, ?_⟩
    calc s * t ≤ 1 * 1 := mul_le_mul hs1 ht.2 ht.1 (by norm_num)
      _ = 1 := by norm_num
  have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIco_sub : Set.Ico (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- `Z` solves the geodesic ODE on `[0,1]`.
  have hZderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Z (geodesicField g gi (Z t)) t := by
    intro t ht
    have hst_ioo : s * t ∈ Set.Ioo (-2 : ℝ) 2 := hIcc_sub (hst_mem t ht)
    have hlin : HasDerivAt (fun r : ℝ => s * r) s t := by
      simpa using (hasDerivAt_id t).const_mul s
    have hcomp : HasDerivAt (fun r => Y (s * r)) (s • geodesicField g gi (Y (s * t))) t :=
      (hYode (s * t) hst_ioo).scomp t hlin
    have hZd : HasDerivAt Z (scaleVel s (s • geodesicField g gi (Y (s * t)))) t := by
      have hh := (scaleVel s).hasFDerivAt.comp_hasDerivAt t hcomp
      simpa [hZdef, Function.comp_def] using hh
    have hval : scaleVel s (s • geodesicField g gi (Y (s * t))) = geodesicField g gi (Z t) := by
      rw [hZdef, map_smul, geodesicField_scaleVel g gi s (Y (s * t))]
    rwa [hval] at hZd
  -- Common confinement ball around `(x₀,0)` and Lipschitz field.
  set R : ℝ := uniformFlowConst g gi hC hK * ‖v‖ with hRdef
  set S : Set (Point n × Point n) := Metric.closedBall ((x₀, 0) : Point n × Point n) R with hSdef
  obtain ⟨Kq, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) (by rw [hSdef]; exact convex_closedBall _ R)
      (by rw [hSdef]; exact isCompact_closedBall _ R)
  have hcont_Z : ContinuousOn Z (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hZderiv t ht).continuousAt.continuousWithinAt
  have hcont_V : ContinuousOn V (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hVode t (hIcc_sub ht)).continuousAt.continuousWithinAt
  have hmem_Z : ∀ t ∈ Set.Icc (0 : ℝ) 1, Z t ∈ S := by
    intro t ht
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm, hZdef]
    have hrw : scaleVel s (Y (s * t)) - ((x₀, 0) : Point n × Point n)
        = scaleVel s (Y (s * t) - ((x₀, 0) : Point n × Point n)) := by
      rw [map_sub, hfix]
    rw [hrw]
    have hsc : ‖scaleVel s (Y (s * t) - ((x₀, 0) : Point n × Point n))‖
        ≤ ‖Y (s * t) - ((x₀, 0) : Point n × Point n)‖ :=
      scaleVel_norm_le s hs0 hs1 (Y (s * t) - ((x₀, 0) : Point n × Point n))
    exact le_trans hsc (hYconf (s * t) (hst_mem t ht))
  have hmem_V : ∀ t ∈ Set.Icc (0 : ℝ) 1, V t ∈ S := by
    intro t ht
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    have hc := hVconf t ht
    have hsvv : uniformFlowConst g gi hC hK * ‖sv‖ ≤ R := by
      rw [hRdef, hsvdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      have hsvle : s * ‖v‖ ≤ ‖v‖ := by nlinarith [norm_nonneg v, hs1, hs0]
      nlinarith [uniformFlowConst_nonneg g gi hC hK, hsvle, norm_nonneg v]
    exact le_trans hc hsvv
  -- Same initial value at `t = 0`.
  have ha : Z 0 = V 0 := by
    rw [hZdef, hV0]
    simp only [mul_zero, hY0, scaleVel_apply]
    rw [hsvdef]
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
  have h1 : Z 1 = V 1 := hEqOn (Set.right_mem_Icc.mpr (by norm_num))
  have hZ1 : (Z 1).1 = (Y s).1 := by rw [hZdef]; simp [mul_one]
  have hV1 : (V 1).1 = uniformFlowExp g gi hC hK x₀ sv := by
    rw [hVdef]; exact (uniformFlowExp_eq g gi hC hK x₀ sv).symm
  rw [← hV1, ← h1]; exact hZ1

/-! ### STEP 2c — the diagonal identity `T_{x₀} v = fderiv (uniformFlowExp x₀) v [v]`. -/

/-- **THE DIAGONAL IDENTITY at base `x₀`.**  At a reachable field point `v`,
        `(uniformFlowTube x₀ v 1).2 = fderiv ℝ (uniformFlowExp x₀) v [v]`.
    Generic-base analogue of `terminalVel0_apply_eq_fderiv_diag`: differentiate the reparametrisation
    identity in `s` at `s = 1` from the left.  NOT `a₁ = R/6`. -/
theorem terminalVelAt_apply_eq_fderiv_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) (v : Point n)
    (hvexp : ‖v‖ < expRho g gi hC x₀) (hvuf : ‖v‖ < uniformFlowRadius g gi hC hK) :
    (uniformFlowTube g gi hC hK x₀ v 1).2
      = fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v := by
  have hvuf_le : ‖v‖ ≤ uniformFlowRadius g gi hC hK := hvuf.le
  have hcd4 : ContDiffAt ℝ 4 (uniformFlowExp g gi hC hK x₀) v :=
    uniformFlowExp_contDiffAt_four g gi hC hK x₀ hx₀K v hvexp hvuf
  have hFD : HasFDerivAt (uniformFlowExp g gi hC hK x₀)
      (fderiv ℝ (uniformFlowExp g gi hC hK x₀) v) v :=
    (hcd4.differentiableAt (by norm_num)).hasFDerivAt
  have h1mem : (1 : ℝ) ∈ Set.Ioo (-2 : ℝ) 2 := by norm_num
  have hode1 : HasDerivAt (uniformFlowTube g gi hC hK x₀ v)
      (geodesicField g gi (uniformFlowTube g gi hC hK x₀ v 1)) 1 :=
    uniformFlowTube_spec_ode g gi hC hK x₀ hx₀K v hvuf_le 1 h1mem
  have hψ : HasDerivAt (fun s => (uniformFlowTube g gi hC hK x₀ v s).1)
      ((uniformFlowTube g gi hC hK x₀ v 1).2) 1 := by
    have hh := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt 1 hode1
    simpa only [Function.comp_def, ContinuousLinearMap.coe_fst'] using hh
  have hsv : HasDerivAt (fun s : ℝ => s • v) v 1 := by
    have hh := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v).hasDerivAt (x := (1 : ℝ))
    simpa [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply] using hh
  have hφ : HasDerivAt (fun s : ℝ => uniformFlowExp g gi hC hK x₀ (s • v))
      (fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v) 1 := by
    have hFD1 : HasFDerivAt (uniformFlowExp g gi hC hK x₀)
        (fderiv ℝ (uniformFlowExp g gi hC hK x₀) v) ((1 : ℝ) • v) := by rw [one_smul]; exact hFD
    have hh := hFD1.comp_hasDerivAt (1 : ℝ) hsv
    simpa [Function.comp_def] using hh
  have hmem : Set.Icc (1 / 2 : ℝ) 1 ∈ 𝓝[Set.Iic 1] (1 : ℝ) := by
    have h1 : Set.Iic 1 ∩ Set.Ioi (1 / 2 : ℝ) ∈ 𝓝[Set.Iic 1] (1 : ℝ) :=
      inter_mem_nhdsWithin (Set.Iic 1) (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
    exact mem_of_superset h1 (fun x hx => ⟨le_of_lt hx.2, hx.1⟩)
  have hhom : (fun s : ℝ => uniformFlowExp g gi hC hK x₀ (s • v))
      =ᶠ[𝓝[Set.Iic 1] (1 : ℝ)] (fun s : ℝ => (uniformFlowTube g gi hC hK x₀ v s).1) := by
    filter_upwards [hmem] with s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
    exact uniformFlow_scale_position_at g gi hC hK hx₀K v hvuf_le s hs01
  have hφ' : HasDerivWithinAt (fun s : ℝ => (uniformFlowTube g gi hC hK x₀ v s).1)
      (fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v) (Set.Iic 1) 1 :=
    (hφ.hasDerivWithinAt).congr_of_eventuallyEq hhom.symm
      (by rw [one_smul, uniformFlowExp_eq])
  have heq := UniqueDiffWithinAt.eq_deriv (Set.Iic 1) (uniqueDiffWithinAt_Iic 1)
    hφ' hψ.hasDerivWithinAt
  exact heq.symm

/-! ### STEP 2d — `T_{x₀}` is `C²` at `0`. -/

/-- **★★ `terminalVelAt_contDiffAt_two` — the base-`x₀` terminal-velocity `C²` at `0`, UNCONDITIONAL
    (given `x₀ ∈ K`).**  Generic-base analogue of `terminalVel0_contDiffAt_two`: via the diagonal
    identity `terminalVelAt x₀ =ᶠ[𝓝 0] (v ↦ fderiv (uniformFlowExp x₀) v [v])`; the position endpoint
    is `C⁴` at `0`, so `fderiv` is `C³`, the diagonal `C³`, hence `C² ≤ C³`.  NOT `a₁ = R/6`. -/
theorem terminalVelAt_contDiffAt_two (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    ContDiffAt ℝ 2 (terminalVelAt g gi hC hK x₀) 0 := by
  have hcd4 : ContDiffAt ℝ 4 (uniformFlowExp g gi hC hK x₀) 0 :=
    uniformFlowExp_contDiffAt_four g gi hC hK x₀ hx₀K 0
      (by simpa using expRho_pos g gi hC x₀)
      (by simpa using uniformFlowRadius_pos g gi hC hK)
  have hfd3 : ContDiffAt ℝ 3 (fderiv ℝ (uniformFlowExp g gi hC hK x₀)) 0 :=
    hcd4.fderiv_right (m := 3) (by norm_num)
  have hF3 : ContDiffAt ℝ 3
      (fun v => fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v) 0 :=
    hfd3.clm_apply contDiffAt_id
  have hF2 : ContDiffAt ℝ 2
      (fun v => fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v) 0 :=
    hF3.of_le (by norm_num)
  have hEq : terminalVelAt g gi hC hK x₀
      =ᶠ[𝓝 (0 : Point n)] (fun v => fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v) := by
    have hball : Metric.ball (0 : Point n)
        (min (expRho g gi hC x₀) (uniformFlowRadius g gi hC hK)) ∈ 𝓝 (0 : Point n) :=
      Metric.ball_mem_nhds _ (lt_min (expRho_pos g gi hC x₀) (uniformFlowRadius_pos g gi hC hK))
    filter_upwards [hball] with v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    have hvexp : ‖v‖ < expRho g gi hC x₀ := lt_of_lt_of_le hv (min_le_left _ _)
    have hvuf : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv (min_le_right _ _)
    exact terminalVelAt_apply_eq_fderiv_diag g gi hC hK hx₀K v hvexp hvuf
  exact hF2.congr_of_eventuallyEq hEq

/-! ### STEP 1 — the base-`x₀` RIGHT inverse of the chart. -/

/-- **STEP 1 — the base-`x₀` chart RIGHT inverse.**  There is `r > 0` such that for every target `z`
    with `‖z − x₀‖ < r`, the base-`x₀` inverse chart `U x₀ := uniformInverseChart g gi hC hK x₀` is a
    genuine right inverse of the base-`x₀` forward map `E x₀ := uniformFlowExp g gi hC hK x₀`:
        `uniformFlowExp g gi hC hK x₀ (uniformInverseChart g gi hC hK x₀ z) = z`.
    Generic-base analogue of `chart0_rightInverse` (which fixes the base at `0`): the target ball is
    centred at `E x₀ 0 = x₀`.  NOT `a₁ = R/6`. -/
theorem chartAt_rightInverse (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    ∃ r > (0 : ℝ), ∀ z : Point n, ‖z - x₀‖ < r →
      uniformFlowExp g gi hC hK x₀ (uniformInverseChart g gi hC hK x₀ z) = z := by
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
    have hAL0 : ApproximatesLinearOn (uniformFlowExp g gi hC hK x₀)
        (ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n)
        (Metric.ball 0 δ₁) c := hAL x₀ hx₀K
    have hφ0 : uniformFlowExp g gi hC hK x₀ 0 = x₀ := uniformFlowExp_zero g gi hC hK x₀ hx₀K
    have hεsub : Metric.closedBall (0 : Point n) ε ⊆ Metric.ball 0 δ₁ := by
      intro x hx
      rw [mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt hx hεδ₁
    have hsurj := hAL0.surjOn_closedBall_of_nonlinearRightInverse fri hεpos.le hεsub
    have hzmem : z ∈ Metric.closedBall (uniformFlowExp g gi hC hK x₀ 0)
        (((fri.nnnorm : ℝ)⁻¹ - ↑c) * ε) := by
      rw [Metric.mem_closedBall, hnn, inv_one, hφ0, dist_eq_norm]
      linarith [hzr]
    obtain ⟨w, hwmem, hwφ⟩ := hsurj hzmem
    have hwε : ‖w‖ ≤ ε := by rwa [mem_closedBall_zero_iff] at hwmem
    have hwδc : ‖w‖ < δc := lt_of_le_of_lt hwε hεδc
    obtain ⟨hgermC2, _⟩ := hchart x₀ hx₀K
    obtain ⟨hgerm, _⟩ := hgermC2 w hwδc
    have hval : uniformInverseChart g gi hC hK x₀ (uniformFlowExp g gi hC hK x₀ w) = w :=
      hgerm.eq_of_nhds
    rw [hwφ] at hval
    rw [hval]
    exact hwφ

/-! ### STEP 3a — the base-`x₀` chart centre value `U x₀ x₀ = 0`. -/

/-- **Base-`x₀` centre value.**  `uniformInverseChart g gi hC hK x₀ x₀ = 0`.  Generic-base analogue of
    `chartField_centerValue_base0`: the left-inverse germ at `0` reads `U x₀ (E x₀ 0) = 0`, and
    `E x₀ 0 = x₀`.  NOT `a₁ = R/6`. -/
theorem chartField_centerValue_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    uniformInverseChart g gi hC hK x₀ x₀ = 0 := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨hgermC2, _⟩ := hspec x₀ hx₀K
  obtain ⟨hgerm, _⟩ := hgermC2 0 (by rw [norm_zero]; exact hδ₀)
  have h := hgerm.eq_of_nhds
  rwa [uniformFlowExp_zero g gi hC hK x₀ hx₀K] at h

/-! ### STEP 3 — the generic-base reversal identity `U z x₀ = − T_{x₀} (U x₀ z)`. -/

/-- **★★ STEP 3 — THE GENERIC-BASE REVERSAL IDENTITY.**  Eventually at `z = x₀`, the base-slot chart
    at the generic eval point `x₀` equals the negated terminal velocity of the base-`x₀` chart image:
        `(fun z => uniformInverseChart g gi hC hK z x₀)`
          `=ᶠ[𝓝 x₀] (fun z => − terminalVelAt g gi hC hK x₀ (uniformInverseChart g gi hC hK x₀ z))`.
    Generic-base analogue of `baseSlot_eventuallyEq_neg_terminalVel` (the `x₀ = 0` case).  With
    `v := U x₀ z`, `chartAt_rightInverse` gives `E x₀ v = z`; `terminalVelAt_norm_le` controls every
    radius; `uniformFlow_reversal_reach` gives `E z (−T_{x₀} v) = x₀`; the base-`z` left-inverse germ
    reads `U z x₀ = U z (E z (−T_{x₀} v)) = −T_{x₀} v`.  FULLY DERIVED.  NOT `a₁ = R/6`. -/
theorem baseSlot_eventuallyEq_neg_terminalVel_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀Kmem : K ∈ 𝓝 x₀) :
    (fun z => uniformInverseChart g gi hC hK z x₀)
      =ᶠ[𝓝 x₀]
      (fun z => -terminalVelAt g gi hC hK x₀ (uniformInverseChart g gi hC hK x₀ z)) := by
  have hx₀K : x₀ ∈ K := mem_of_mem_nhds hx₀Kmem
  obtain ⟨r, hr, hRI0⟩ := chartAt_rightInverse g gi hC hK hx₀K
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  set ρK : ℝ := uniformFlowRadius g gi hC hK with hρK
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC0
  have hρpos : 0 < ρK := uniformFlowRadius_pos g gi hC hK
  have hC0nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  have hC1 : (0 : ℝ) < C₀ + 1 := by linarith
  set θ : ℝ := min (ρK / (C₀ + 1)) (δ₀ / (C₀ + 1)) with hθ
  have hθpos : 0 < θ := lt_min (by positivity) (by positivity)
  have hcontv : ContinuousAt (fun z => uniformInverseChart g gi hC hK x₀ z) x₀ :=
    (chartField_contDiffAt_center_at g gi hC hK hx₀K).continuousAt
  have hval0 : uniformInverseChart g gi hC hK x₀ x₀ = 0 :=
    chartField_centerValue_at g gi hC hK hx₀K
  have htend : Tendsto (fun z => ‖uniformInverseChart g gi hC hK x₀ z‖) (𝓝 x₀) (𝓝 0) := by
    simpa [hval0] using hcontv.norm.tendsto
  have hev_θ : ∀ᶠ z in 𝓝 x₀,
      ‖uniformInverseChart g gi hC hK x₀ z‖ < θ :=
    htend.eventually (eventually_lt_nhds hθpos)
  filter_upwards [Metric.ball_mem_nhds x₀ hr, hx₀Kmem, hev_θ]
    with z hzball hzK hzθ
  set v : Point n := uniformInverseChart g gi hC hK x₀ z with hvdef
  have hzr : ‖z - x₀‖ < r := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hzball
  have hRI : uniformFlowExp g gi hC hK x₀ v = z := by
    rw [hvdef]; exact hRI0 z hzr
  have hvθ : ‖v‖ < θ := hzθ
  have hvr1 : ‖v‖ < ρK / (C₀ + 1) := lt_of_lt_of_le hvθ (min_le_left _ _)
  have hvd1 : ‖v‖ < δ₀ / (C₀ + 1) := lt_of_lt_of_le hvθ (min_le_right _ _)
  have hvr1' : ‖v‖ * (C₀ + 1) < ρK := (lt_div_iff₀ hC1).mp hvr1
  have hvd1' : ‖v‖ * (C₀ + 1) < δ₀ := (lt_div_iff₀ hC1).mp hvd1
  have hv_ρ : ‖v‖ ≤ ρK := by nlinarith [norm_nonneg v]
  have hu_le : ‖terminalVelAt g gi hC hK x₀ v‖ ≤ C₀ * ‖v‖ :=
    terminalVelAt_norm_le g gi hC hK hx₀K v hv_ρ
  have hu_ρ : ‖terminalVelAt g gi hC hK x₀ v‖ ≤ ρK := by
    nlinarith [hu_le, hvr1', norm_nonneg v, hC0nn]
  have hu_δ : ‖terminalVelAt g gi hC hK x₀ v‖ < δ₀ := by
    nlinarith [hu_le, hvd1', norm_nonneg v, hC0nn]
  have hzKmem : uniformFlowExp g gi hC hK x₀ v ∈ K := by rw [hRI]; exact hzK
  have hreach := uniformFlow_reversal_reach g gi hC hK x₀ v hx₀K hv_ρ hzKmem hu_ρ
  rw [hRI] at hreach
  obtain ⟨hgermCz, _⟩ := hchart z hzK
  obtain ⟨hgermz, _⟩ := hgermCz (-(uniformFlowTube g gi hC hK x₀ v 1).2)
    (by rw [norm_neg]; exact hu_δ)
  have hgz := hgermz.eq_of_nhds
  rw [hreach] at hgz
  simpa [terminalVelAt] using hgz

/-! ### CAPSTONE — the base-slot `C²` at the generic base, UNCONDITIONAL. -/

/-- **★★ `baseSlot_contDiffAt_two_at` — the base-slot `C²` at the generic base `x₀`, UNCONDITIONAL.**
    Generic-base analogue of the whole reversal + `TerminalVelC2` capstone, now at ANY interior `x₀`,
    not just `0`:
        `ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z x₀) x₀`.
    From the reversal identity (STEP 3), the discharged `terminalVelAt_contDiffAt_two` (STEP 2), and the
    banked field-slot `C²` at the base (`chartField_contDiffAt_center_at`).  NOT `a₁ = R/6`. -/
theorem baseSlot_contDiffAt_two_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀Kmem : K ∈ 𝓝 x₀) :
    ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z x₀) x₀ := by
  have hx₀K : x₀ ∈ K := mem_of_mem_nhds hx₀Kmem
  have hEq := baseSlot_eventuallyEq_neg_terminalVel_at g gi hC hK hx₀Kmem
  have hfield : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK x₀) x₀ :=
    chartField_contDiffAt_center_at g gi hC hK hx₀K
  have hval : uniformInverseChart g gi hC hK x₀ x₀ = 0 :=
    chartField_centerValue_at g gi hC hK hx₀K
  have hcomp : ContDiffAt ℝ 2
      (fun z => terminalVelAt g gi hC hK x₀ (uniformInverseChart g gi hC hK x₀ z)) x₀ := by
    have hg : ContDiffAt ℝ 2 (terminalVelAt g gi hC hK x₀)
        (uniformInverseChart g gi hC hK x₀ x₀) := by
      rw [hval]; exact terminalVelAt_contDiffAt_two g gi hC hK hx₀K
    exact hg.comp x₀ hfield
  exact hcomp.neg.congr_of_eventuallyEq hEq

end QIQTH.GeodesicReversalRouteAtPoint

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.GeodesicReversalRouteAtPoint
#print axioms terminalVelAt_norm_le
#print axioms uniformFlow_scale_position_at
#print axioms terminalVelAt_apply_eq_fderiv_diag
#print axioms terminalVelAt_contDiffAt_two
#print axioms chartAt_rightInverse
#print axioms chartField_centerValue_at
#print axioms baseSlot_eventuallyEq_neg_terminalVel_at
#print axioms baseSlot_contDiffAt_two_at
end AxiomChecks
