/-
  CurvedA1FintHdataUniform — J4-576: SOURCING the UNIFORM amplitude value/derivative bounds
  (conjunct (3) of the `hdata`-family) for the genuinely-curved witness `g^K = curvedRNCMetric κ`
  (κ ≤ 0), via COMPACTNESS-UNIFORMIZATION on the honest near-`0` gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ## CONTEXT — the `hdata`-family (recap).
  `curved_hFint_hFar_general` / `curved_hFint_hFirstEnv_at_gate` carry a per-`(i,τ,z)` geometric jet
  bundle `hdata`, a conjunction of FOUR conjuncts, with the constants `L`/`Ba`/`Bd` bound OUTSIDE the
  `∀ i τ z` — i.e. UNIFORM constants requiring a compactness step:
    (1) the inverse-chart first jet `HasDerivAt (fun r => uniformInverseChart … z (update 0 i r) k) …`,
    (2) the Jacobian-column bound `|Pval k| ≤ L`,
    (3) the amplitude value/derivative bounds `|chartFieldAmp … a b τ z 0| ≤ Ba` ∧
        `|pd (chartFieldAmp … a b τ z) i 0| ≤ Bd`,
    (4) the two-sided near-isometry (J4-575, `CurvedA1FintHdata.curved_hdata_nearIsometry_at_gate`).

  ## WHAT LANDS HERE (DERIVED; NOT `a₁ = R/6`).
    • `curved_hdata_amp_value_uniform_at_gate` — ★★ conjunct (3a) for `g^K`, FULLY DISCHARGED (no
      residual): a UNIFORM value bound
          `∃ ρ>0, ∃ Ba≥0, ∀ i τ, 0<τ→τ≤T → ∀ z∈K, ‖z‖<ρ → |chartFieldAmp … a b τ z 0| ≤ Ba`.
      DIRECTLY from the banked base-slot compactness bound
      `BaseSlotAmplitude.baseSlotAmp_bound` (joint `(τ,z)`-continuity of the base-slot amplitude on
      the COMPACT `[0,T] ×ˢ closedBall 0 ρ` → `IsCompact.exists_bound_of_continuousOn`), instantiated
      at `g = curvedRNCMetric κ`, `gi = curvedRNCInv κ` with the banked curved carries
      `curvedRNCMetric_contDiff` / `curvedRNCInv_contDiff` (K ≤ 0) / `curvedRNCMetric_hgpos` (K ≤ 0).
      τ-DOMAIN AUDIT: the bound is over the CLOSED `τ ∈ [0,T]` — the amplitude value is AFFINE in `τ`
      (`u₀ + u₁·τ`, and `W`/`Θ` are τ-independent), hence continuous down to `τ = 0`, so NO ε-floor
      is needed and the value does NOT blow up as `τ → 0⁺`.
    • `curved_hdata_amp_deriv_uniform_at_gate_of_cont` — ★ conjunct (3b), THIN reduction (per fixed
      `i`): the UNIFORM derivative bound
          `∃ Bd≥0, ∀ τ, 0<τ→τ≤T → ∀ z∈K, ‖z‖<ρ → |pd (chartFieldAmp … a b τ z) i 0| ≤ Bd`
      reduced to the SINGLE residual `hcont` = joint `(τ,z)`-continuity of the first field-derivative
      section `(τ,z) ↦ pd (chartFieldAmp … a b τ z) i 0` on the compact `[0,T] ×ˢ closedBall 0 ρ`, via
      `IsCompact.exists_bound_of_continuousOn`.  ⚠ This joint pd-continuity is NOT banked (BaseSlotAmpDeriv
      records "there is NO `ContinuousOn`/`ContDiff` fact about the first field-derivative jet jointly"),
      so `hcont` is a GENUINE carried residual — but it is a strictly-weaker qualitative fact (satisfiable:
      the RNC chart amplitude is `C²` in the field slot per fixed `(τ,z)`, and affine in `τ`), and the
      `∀ i`-uniform `Bd` follows from a trivial finite-`max` over `Fin n`.
    • `curved_hdata_amp_uniform_at_gate_curved_satisfiable` — the CURVED (not-secretly-flat) gate:
      for `κ ≠ 0`, `n ≥ 2`, `Ric(0) = n(n−1)κ ≠ 0` (`curvedRNCMetric_ricci_trace_diag_ne`), so the
      uniform amplitude bounds are discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT `δ`.

  ## PRECISE DEPTH VERDICT.
    • Conjunct (3a) (uniform amplitude VALUE `Ba`) is now BANKED — FULL discharge, no residual, on the
      honest near-`0` gate `‖z‖ < ρ` (the hFirstEnv domain; and any sub-gate of hFar's `z ∈ K`).
    • Conjunct (3b) (uniform amplitude DERIVATIVE `Bd`) reduces to ONE banked-compactness step + the
      joint pd-continuity residual `hcont` (medium depth, NOT banked).
    • Conjuncts (1)/(2) (inverse-chart first jet EXISTENCE + `|Pval| ≤ L`) remain owed (the field-slot
      inverse-chart jet is not yet banked; deeper than the amplitude uniformization).

  ⚠  a₁ = R/6 remains CONDITIONAL.  Sourcing conjunct (3a) (and reducing (3b)) does NOT make it
  unconditional — the hFar far-field lower coercivity, conjuncts (1)/(2), the (3b) pd-continuity, `hsrc`,
  `hOffCollarTail`, the convergence trio, and `hInnerCont` all remain owed.
-/
import QIQTH.CurvedA1FintHFarSource
import QIQTH.BaseSlotAmplitude
import QIQTH.BaseSlotAmpDeriv
import QIQTH.CurvedRNCPosDef

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness
open QIQTH.CurvedRNCPosDef QIQTH.BaseSlotAmplitude
open scoped Topology BigOperators

namespace QIQTH.CurvedA1FintHdataUniform

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### (3a) — THE UNIFORM AMPLITUDE VALUE BOUND for `g^K` (FULLY discharged).
    ############################################################################### -/

/-- **★★ J4-576 — `curved_hdata_amp_value_uniform_at_gate`.**  The UNIFORM amplitude VALUE bound —
    conjunct (3a) of the `hdata`-family for the genuinely-curved witness `g^K = curvedRNCMetric κ`
    (`κ ≤ 0`), on its honest near-`0` gate `‖z‖ < ρ`:
        `∃ ρ>0, ∃ Ba≥0, ∀ i τ, 0<τ→τ≤T → ∀ z∈K, ‖z‖<ρ → |chartFieldAmp … a b τ z 0| ≤ Ba`.
    DIRECTLY from the banked base-slot compactness bound `BaseSlotAmplitude.baseSlotAmp_bound`
    (joint `(τ,z)` continuity on the COMPACT `[0,T] ×ˢ closedBall 0 ρ` → extreme-value theorem),
    instantiated with the banked curved carries `curvedRNCMetric_contDiff` / `curvedRNCInv_contDiff`
    (`K ≤ 0`) / `curvedRNCMetric_hgpos` (`K ≤ 0`).  τ-DOMAIN AUDIT: the amplitude value is AFFINE in
    `τ` (`u₀+u₁·τ`, `W`/`Θ` τ-independent) — continuous down to `τ = 0`, no blow-up, no ε-floor.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_amp_value_uniform_at_gate (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (a b T : ℝ) :
    ∃ ρ > (0 : ℝ), ∃ Ba : ℝ, 0 ≤ Ba ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K, ‖z‖ < ρ →
        |chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n)| ≤ Ba := by
  obtain ⟨ρ, hρ, CA, hCA⟩ :=
    baseSlotAmp_bound (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK h0Kmem
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (fun a b => curvedRNCInv_contDiff κ hκ a b)
      (curvedRNCMetric_hgpos κ hκ) a b T
  refine ⟨ρ, hρ, max CA 0, le_max_right _ _, fun i τ hτ hτT z _hzK hzρ => ?_⟩
  have hzball : z ∈ Metric.closedBall (0 : Point n) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hzρ.le
  exact le_trans (hCA τ ⟨hτ.le, hτT⟩ z hzball) (le_max_left _ _)

/-! ###############################################################################
    ### (3b) — THE UNIFORM AMPLITUDE DERIVATIVE BOUND for `g^K` (THIN reduction).
    ############################################################################### -/

/-- **★ J4-576 — `curved_hdata_amp_deriv_uniform_at_gate_of_cont`.**  The UNIFORM amplitude DERIVATIVE
    bound — conjunct (3b) of the `hdata`-family for `g^K = curvedRNCMetric κ`, per fixed `i`, on the
    near-`0` gate `‖z‖ < ρ`:
        `∃ Bd≥0, ∀ τ, 0<τ→τ≤T → ∀ z∈K, ‖z‖<ρ → |pd (chartFieldAmp … a b τ z) i 0| ≤ Bd`.
    THIN reduction to the SINGLE residual `hcont` = joint `(τ,z)` continuity of the first
    field-derivative section on the compact `[0,T] ×ˢ closedBall 0 ρ`, via the extreme-value theorem
    `IsCompact.exists_bound_of_continuousOn`.  ⚠ `hcont` is NOT banked (the field-derivative jet has no
    banked joint `ContinuousOn`); it is a strictly-weaker, satisfiable qualitative carry.  The `∀ i`
    uniform `Bd` follows by a finite `max` over `Fin n`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_amp_deriv_uniform_at_gate_of_cont (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b T : ℝ) (i : Fin n) (ρ : ℝ) (hρ : 0 < ρ)
    (hcont : ContinuousOn
      (fun p : ℝ × Point n =>
        pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b p.1 p.2) i (0 : Point n))
      (Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : Point n) ρ)) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧
      ∀ (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K, ‖z‖ < ρ →
        |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨CA, hCA⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max CA 0, le_max_right _ _, fun τ hτ hτT z _hzK hzρ => ?_⟩
  have hzball : z ∈ Metric.closedBall (0 : Point n) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hzρ.le
  have hbd := hCA (τ, z) ⟨⟨hτ.le, hτT⟩, hzball⟩
  simp only [Real.norm_eq_abs] at hbd
  exact le_trans hbd (le_max_left _ _)

/-! ###############################################################################
    ### the CURVED (not-secretly-flat) satisfiability GATE.
    ############################################################################### -/

/-- **★ J4-576 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0) = n(n−1)κ`) of `g^K = curvedRNCMetric κ` is nonzero, so the uniform
    amplitude bounds are discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_amp_uniform_at_gate_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintHdataUniform

section AxiomChecks
open QIQTH.CurvedA1FintHdataUniform
#print axioms curved_hdata_amp_value_uniform_at_gate
#print axioms curved_hdata_amp_deriv_uniform_at_gate_of_cont
#print axioms curved_hdata_amp_uniform_at_gate_curved_satisfiable
end AxiomChecks
