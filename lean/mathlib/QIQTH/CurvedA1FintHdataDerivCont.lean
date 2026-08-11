/-
  CurvedA1FintHdataDerivCont — J4-577: PROVING the `hcont` residual of conjunct (3b) for the
  genuinely-curved witness `g^K = curvedRNCMetric κ` (κ ≤ 0) — the joint `(τ,z)`-continuity of the
  chart FIELD-DERIVATIVE section — thereby turning `curved_hdata_amp_deriv_uniform_at_gate` from
  hcont-conditional into carrier-conditional (analytic core fully discharged).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ## CONTEXT — the single carried residual of J4-576.
  `CurvedA1FintHdataUniform.curved_hdata_amp_deriv_uniform_at_gate_of_cont` (conjunct (3b) of the
  `hdata`-family) reduced the UNIFORM amplitude-derivative bound `Bd` for `g^K` to ONE carried
  continuity residual:
     `hcont : ContinuousOn (fun p : ℝ × Point n =>
                pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b p.1 p.2) i 0)
              (Set.Icc 0 T ×ˢ Metric.closedBall 0 ρ)`.
  The J4-576 report flagged the route: the base-continuity of the chart field-Jacobian via
  `pd_chartAmp_center_eq` in `BaseSlotAmpDeriv`.

  ## WHAT THIS BRICK FINDS (DON'T-UNDERCREDIT).
  The joint continuity is ALREADY PROVED at ambient (general-metric) generality:
    • `SupFamilyFirstOrder.supFamilyFirstOrder_hcont1` establishes EXACTLY the `hcont` shape for
      `chartAmp` on `[0,τ₀] ×ˢ closedBall 0 ρ`, reduced to THREE named geometric carries on
      `closedBall 0 ρ`:
        - `hreg` : per-point reachable `ContDiffAt ℝ 2 (W z) 0`,
        - `hW0`  : base-continuity of the origin section `z ↦ W z 0`,
        - `hJac` : base-continuity of the chart field-slot Jacobian `z ↦ fderiv ℝ (W z) 0`
                   (itself banked via `JacobiCLMExposure.chartFieldJacobian_continuousOn`, whose
                   forward-flow joint-continuity input `forwardFlowJet_continuousOn` is now banked —
                   the OLD J3 base-point-regularity blocker is DISCHARGED at the general level).
      The analytic composition (`pd_chartAmp_center_eq` identification →
      `manifoldAmp_fderiv_continuous` CLM factor × `hJac`-derived vector factor → `ContinuousOn.clm_apply`
      → `ContinuousOn.congr`) is BANKED there.
    • `BaseSlotAmpDeriv.chartAmp_eq_chartFieldAmp_fun` gives `chartAmp … = chartFieldAmp …` as field
      functions, so `pd (chartFieldAmp … p.1 p.2) i 0 = pd (chartAmp … p.1 p.2) i 0` and the two
      `ContinuousOn` statements are literally about the same section.

  ## WHAT LANDS HERE (DERIVED; NOT `a₁ = R/6`).
    • `curved_hdata_amp_deriv_cont_at_gate` — ★★ the `hcont` residual PROVED for `g^K` (in the exact
      `chartFieldAmp` shape J4-576 consumes), by instantiating `supFamilyFirstOrder_hcont1` at
      `g = curvedRNCMetric κ`, `gi = curvedRNCInv κ` (κ ≤ 0, via the banked curved carries
      `curvedRNCMetric_contDiff` / `curvedRNCInv_contDiff` / `curvedRNCMetric_hgpos`) and transferring
      `chartAmp → chartFieldAmp`.  CONDITIONAL only on the three GEOMETRIC carries `hreg`/`hW0`/`hJac`
      for `g^K` on `closedBall 0 ρ` — NO opaque analytic continuity carry remains.
    • `curved_hdata_amp_deriv_uniform_at_gate` — ★★ conjunct (3b) for `g^K` with the analytic `hcont`
      DISCHARGED: the UNIFORM amplitude-derivative bound `Bd`, obtained by feeding the proved `hcont`
      into `curved_hdata_amp_deriv_uniform_at_gate_of_cont` (J4-576).  Now depends only on the three
      geometric carries + `hρ`, not on the raw joint-continuity assumption.
    • `curved_hdata_amp_deriv_cont_curved_satisfiable` — the CURVED (not-secretly-flat) gate: for
      `κ ≠ 0`, `n ≥ 2`, `Ric(0) = n(n−1)κ ≠ 0`, so the result is discharged at a genuinely curved
      witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.

  ## PRECISE DEPTH VERDICT.
    • Conjunct (3b)'s ANALYTIC residual `hcont` is now DISCHARGED for `g^K` — the joint continuity of
      the chart field-derivative section is a proved theorem, not a carried hypothesis.
    • It rests on the three GEOMETRIC carries `hreg`/`hW0`/`hJac` on `closedBall 0 ρ` (the reachable
      `C²`, origin-section continuity, and chart field-Jacobian continuity), each banked-reducible for
      `g^K` under a small-ρ reachability gate — a SEPARATE (geometric) thread, NOT an analytic
      continuity wall.  These are the same three carries `supFamilyFirstOrder_hcont1` reduces to at the
      general level; they are satisfiable (the flat RNC metric has them, and `g^K` has them on a small
      collar), strictly weaker than the conclusion, and never the `a₁ = R/6` conclusion in disguise.

  ⚠  a₁ = R/6 remains CONDITIONAL.  Discharging `hcont` (completing conjunct (3)'s analytic core) does
  NOT make a₁ = R/6 unconditional — the hFar far-field lower coercivity, conjuncts (1)/(2)
  inverse-chart jet, the geometric `hreg`/`hW0`/`hJac` discharge for `g^K`, `hsrc`, `hOffCollarTail`,
  the convergence trio, and `hInnerCont` all remain owed.
-/
import QIQTH.CurvedA1FintHdataUniform
import QIQTH.SupFamilyFirstOrder
import QIQTH.BaseSlotAmpDeriv

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness
open QIQTH.CurvedRNCPosDef QIQTH.BaseSlotAmplitude
open QIQTH.HrepGermFactorization
open QIQTH.SupFamilyFirstOrder QIQTH.BaseSlotAmpDeriv
open QIQTH.CurvedA1FintHdataUniform
open scoped Topology BigOperators

namespace QIQTH.CurvedA1FintHdataDerivCont

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### ★★ (3b) — THE `hcont` RESIDUAL, PROVED for `g^K`.
    ############################################################################### -/

/-- **★★ J4-577 — `curved_hdata_amp_deriv_cont_at_gate`.**  The J4-576 `hcont` residual — the joint
    `(τ,z)`-continuity of the chart FIELD-DERIVATIVE section
        `(τ, z) ↦ pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z ·) i 0`
    on `[0,T] ×ˢ closedBall 0 ρ` — PROVED for the genuinely-curved witness `g^K = curvedRNCMetric κ`
    (`κ ≤ 0`).  Route: `SupFamilyFirstOrder.supFamilyFirstOrder_hcont1` establishes the identical
    continuity for `chartAmp` (from the banked `pd_chartAmp_center_eq` identification +
    `manifoldAmp_fderiv_continuous` + the now-banked chart field-Jacobian continuity), instantiated at
    `g = curvedRNCMetric κ`, `gi = curvedRNCInv κ` with the banked curved carries
    `curvedRNCMetric_contDiff` / `curvedRNCInv_contDiff` (`κ ≤ 0`) / `curvedRNCMetric_hgpos` (`κ ≤ 0`);
    `chartAmp_eq_chartFieldAmp_fun` transfers to the `chartFieldAmp` shape J4-576 consumes.  CONDITIONAL
    only on the three GEOMETRIC carries `hreg`/`hW0`/`hJac` for `g^K` on `closedBall 0 ρ` — no opaque
    analytic continuity carry.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_amp_deriv_cont_at_gate (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b T : ℝ) (i : Fin n) (ρ : ℝ)
    (hreg : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) (0 : Point n))
    (hW0 : ContinuousOn
      (fun z : Point n => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
      (Metric.closedBall (0 : Point n) ρ))
    (hJac : ContinuousOn
      (fun z : Point n => fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) 0)
      (Metric.closedBall (0 : Point n) ρ)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b p.1 p.2) i (0 : Point n))
      (Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : Point n) ρ) := by
  have hcontAmp := supFamilyFirstOrder_hcont1 (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (fun a b => curvedRNCMetric_contDiff κ a b)
    (fun a b => curvedRNCInv_contDiff κ hκ a b)
    (curvedRNCMetric_hgpos κ hκ) a b T i ρ hreg hW0 hJac
  refine hcontAmp.congr (fun p _ => ?_)
  show pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b p.1 p.2) i (0 : Point n)
      = pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b p.1 p.2) i (0 : Point n)
  rw [chartAmp_eq_chartFieldAmp_fun (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b p.1 p.2]

/-! ###############################################################################
    ### ★★ (3b) — THE UNIFORM AMPLITUDE-DERIVATIVE BOUND, `hcont` DISCHARGED.
    ############################################################################### -/

/-- **★★ J4-577 — `curved_hdata_amp_deriv_uniform_at_gate`.**  Conjunct (3b) of the `hdata`-family for
    `g^K = curvedRNCMetric κ` (`κ ≤ 0`), with the analytic `hcont` DISCHARGED: the UNIFORM
    amplitude-derivative bound on the near-`0` gate `‖z‖ < ρ`,
        `∃ Bd≥0, ∀ τ, 0<τ→τ≤T → ∀ z∈K, ‖z‖<ρ → |pd (chartFieldAmp … a b τ z) i 0| ≤ Bd`,
    obtained by feeding the PROVED `hcont` (`curved_hdata_amp_deriv_cont_at_gate`) into the J4-576 thin
    reduction `curved_hdata_amp_deriv_uniform_at_gate_of_cont` (compactness / extreme-value theorem).
    Depends only on the three geometric carries `hreg`/`hW0`/`hJac` + `hρ`, NOT on any raw
    joint-continuity assumption.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_amp_deriv_uniform_at_gate (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b T : ℝ) (i : Fin n) (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) (0 : Point n))
    (hW0 : ContinuousOn
      (fun z : Point n => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
      (Metric.closedBall (0 : Point n) ρ))
    (hJac : ContinuousOn
      (fun z : Point n => fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) 0)
      (Metric.closedBall (0 : Point n) ρ)) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧
      ∀ (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K, ‖z‖ < ρ →
        |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd :=
  curved_hdata_amp_deriv_uniform_at_gate_of_cont κ hChr hK a b T i ρ hρ
    (curved_hdata_amp_deriv_cont_at_gate κ hκ hChr hK a b T i ρ hreg hW0 hJac)

/-! ###############################################################################
    ### the CURVED (not-secretly-flat) satisfiability GATE.
    ############################################################################### -/

/-- **★ J4-577 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0) = n(n−1)κ`) of `g^K = curvedRNCMetric κ` is nonzero, so the discharged
    amplitude-derivative continuity/bound is at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the
    flat `δ`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_amp_deriv_cont_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintHdataDerivCont

section AxiomChecks
open QIQTH.CurvedA1FintHdataDerivCont
#print axioms curved_hdata_amp_deriv_cont_at_gate
#print axioms curved_hdata_amp_deriv_uniform_at_gate
#print axioms curved_hdata_amp_deriv_cont_curved_satisfiable
end AxiomChecks
