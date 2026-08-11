/-
  CurvedA1CenterGauge — J4-584: the CURVED-CAPSTONE SALVAGE non-vacuity certificate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It certifies
  that the CENTER-ONLY gauge weakening (J4-583) removes the J4-582 vacuity — i.e. the weakened
  antecedent bundle of the curved a₁ two-jet capstone is JOINTLY SATISFIABLE at a GENUINELY-CURVED
  witness (`κ < 0`, `n ≥ 2`) on a GENUINE (non-singleton, positive-measure) base set `K`.

  ## THE CONTEXT (J4-582 vacuity, J4-583 salvageability).
  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` was proven VACUOUS at `κ ≠ 0`, `n ≥ 2`: its
  frame antecedent `hframeK : ∀ q ∈ K, curvedRNCMetric κ q = δ` together with `hK0 : 0 ∈ K` FORCES
  `K = {0}` (`curvedRNCMetric_frame_forces_origin` / `frameK_forces_singleton`), collapsing the gated
  source support to the Lebesgue-null singleton, hence forcing every base integral to `0`
  (`witness_baseIntegral_zero`), hence making `hmassone : ∫ z, H(εₘ) 0 z → 1` UNSATISFIABLE
  (`hmassone_unsatisfiable`).  J4-583 (`CurvedA1FrameAudit`) established this is a REMOVABLE artefact of
  `hframeK`'s neighbourhood strength: every curved consumer uses `hframeK` ONLY as `hframeK 0 hK0` to
  extract the 0-jet VALUE `g(0) = δ`, and the banked `DaLimCurvedGauge.gauge_from_pointwise` produces
  BOTH gauge census members (`MemGaugeGi`, `MemGaugeGamma`) from the CENTER-ONLY jet — no `hframeK`.

  ## THE J4-584 DELIVERABLE (this file).  The NON-VACUITY CERTIFICATE (the anti-J4-582).
  `curved_center_antecedents_nonvacuous` exhibits, at every `κ < 0`, `n ≥ 2`, a GENUINE compact base set
  `K = closedBall 0 1` (NOT the collapsed `{0}`; it contains a nonzero point) on which
    • the two center-only gauge members hold (via `curved_gauge_from_center`, WITHOUT `hframeK`/`hK0`);
    • the metric is GENUINELY CURVED (`Ric(0)`-proxy metric-Hessian trace `≠ 0`);
    • the over-strong flat frame `hframeK` PROVABLY FAILS (`¬ ∀ q ∈ K, g q = δ`) — so we are genuinely
      OUTSIDE the J4-582 collapse regime;
    • the gated source support is NON-TRIVIAL (`∃ z ≠ 0, z ∈ K`), so the J4-582
      `witness_baseIntegral_zero` collapse mechanism (which needed `∀ z ≠ 0, z ∉ K`) NO LONGER APPLIES —
      the structural obstruction to `hmassone` is REMOVED.

  ## WHAT IS *NOT* DELIVERED HERE (honest scope).  The FULL binder rethread of the curved capstone —
  weakening `hframeK` to the center-only `hg0` IN PLACE across `curved_a1_R6_fully_wired`,
  `curved_hDa_at_gate`, `curved_core_at_gate`, `curved_leg2_hLapFull` and rethreading `gauge_from_geometry
  → gauge_from_pointwise` — is DEFERRED.  Leg-1's `hframeK` flows into the census monolith
  `DaLimLUCappedStep3.hDaLimLU_from_labelled_capped` (its `gauge_from_geometry` site), which the capstone
  needs for BOTH legs; rethreading it means editing that monolith.  So the curved `a₁ = R/6` THEOREM
  itself is still OWED the binder weakening (J4-585).  This file certifies that weakening is SOUND and
  NON-VACUOUS — it does not perform it.

  ⚠ HONEST a₁ FRAMING.  `a₁ = R/6` is established non-vacuously ONLY for the FLAT tower.  For the CURVED
  case it is being RE-ESTABLISHED non-vacuously: J4-582 showed the shipped curved capstone is vacuous at
  the curved witness; this brick certifies the fix (center-only gauge on a genuine `K`) is inhabited by a
  genuinely-curved metric — but the curved capstone's own binders are not yet weakened.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CurvedA1FrameAudit
import QIQTH.CurvedA1FintHFarCoercivity

open MeasureTheory Filter Set
open QIQTH.Curvature
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.DaLimLUWallRecon
open QIQTH.CurvedA1FrameAudit QIQTH.CurvedA1FintHFarCoercivity
open scoped BigOperators Topology

namespace QIQTH.CurvedA1CenterGauge

variable {n : ℕ}

/-- A genuinely-nonzero point of the closed unit ball of `Point n` (`n ≥ 1`): the `i₀ = 0` axis point
    `½·e₀`.  It witnesses that `closedBall 0 1 ≠ {0}` — the base set is NOT the J4-582 collapsed
    singleton.  Its `∞`-norm is `½ ≤ 1`, and it is `≠ 0` (its `0`-th coordinate is `½`). -/
theorem half_axis_mem_ball (hn : 1 ≤ n) :
    (Pi.single (⟨0, hn⟩ : Fin n) (1 / 2 : ℝ)) ∈ Metric.closedBall (0 : Point n) 1
      ∧ (Pi.single (⟨0, hn⟩ : Fin n) (1 / 2 : ℝ)) ≠ (0 : Point n) := by
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro i
    rcases eq_or_ne i (⟨0, hn⟩ : Fin n) with h | h
    · subst h; rw [Pi.single_eq_same, Real.norm_eq_abs]; norm_num
    · rw [Pi.single_eq_of_ne h, norm_zero]; norm_num
  · intro hzero
    have hc := congrFun hzero (⟨0, hn⟩ : Fin n)
    rw [Pi.single_eq_same, Pi.zero_apply] at hc
    norm_num at hc

/-- **★★★ J4-584 — `curved_center_antecedents_nonvacuous` — THE NON-VACUITY CERTIFICATE (anti-J4-582).**
    For every genuinely-curved witness (`κ < 0`, `n ≥ 2`) there is a GENUINE compact base set `K`
    (the closed unit ball, containing a nonzero point — NOT the J4-582 collapsed `{0}`) such that the
    CENTER-ONLY gauge weakening's antecedents are JOINTLY SATISFIABLE:
      (1) `0 ∈ K`;
      (2) `K` genuinely contains a nonzero point (positive-measure source support);
      (3) the two center-only gauge census members hold — WITHOUT `hframeK`/`hK0` — from the PROVED
          `curved_gauge_from_center` (`DaLimCurvedGauge.gauge_from_pointwise` on `curvedRNCMetric`);
      (4) the metric is GENUINELY CURVED: the `Ric(0)` proxy (diagonal metric-Hessian trace) `≠ 0`
          (`curvedRNCMetric_ricci_trace_diag_ne`);
      (5) the over-strong flat frame `hframeK` PROVABLY FAILS on this `K` — so this is NOT the J4-582
          collapse regime.
    Contrast `CurvedA1FarConsumeCheck.hmassone_unsatisfiable`: there the shipped `{hframeK, hK0}` bundle
    forced `K = {0}` and killed `hmassone`; here the WEAKENED (center-only) gauge places NO constraint on
    `K`, so a genuine `K` is admissible and the collapse is gone.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_center_antecedents_nonvacuous (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) (c : Fin n) :
    ∃ K : Set (Point n),
      IsCompact K
      ∧ (0 : Point n) ∈ K
      ∧ (∃ q, q ∈ K ∧ q ≠ (0 : Point n))
      ∧ (MemGaugeGi (n := n) (curvedRNCInv κ)
          ∧ MemGaugeGamma (n := n) (curvedRNCMetric κ) (curvedRNCInv κ))
      ∧ pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0
      ∧ ¬ (∀ q ∈ K, ∀ i j, curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0)) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  obtain ⟨hqmem, hqne⟩ := half_axis_mem_ball (n := n) hn1
  refine ⟨Metric.closedBall (0 : Point n) 1, isCompact_closedBall _ _, ?_,
    ⟨_, hqmem, hqne⟩, curved_gauge_from_center κ hκ,
    curvedRNCMetric_ricci_trace_diag_ne κ (ne_of_lt hκ) hn c, ?_⟩
  · -- 0 ∈ closedBall 0 1
    simp [Metric.mem_closedBall]
  · -- hframeK fails: it would force the genuine nonzero point of `K` to be `0`.
    intro hframe
    exact hqne (curvedRNCMetric_frame_forces_origin κ (ne_of_lt hκ) hn (hframe _ hqmem))

/-- **★★★ J4-584 — `curved_center_gate` — the antecedent-inhabitance GATE (contrast the coefficient-only
    gate).**  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired_curved_satisfiable` checked ONLY the
    CONCLUSION coefficient (`Ric(0) ≠ 0`) — the axiom-budget blind spot J4-582 exploited.  This gate
    checks ANTECEDENT INHABITANCE: at `κ < 0`, `n ≥ 2` the center-only gauge members are inhabited by the
    GENUINELY-CURVED `curvedRNCMetric κ` (Ric-proxy `≠ 0`), on a base set that is genuinely larger than
    `{0}` (`∃ z ≠ 0, z ∈ closedBall 0 1`) — so the source support that J4-582 collapsed is non-trivial and
    the `hmassone` obstruction is structurally removed.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_center_gate (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) (c : Fin n) :
    (MemGaugeGi (n := n) (curvedRNCInv κ)
        ∧ MemGaugeGamma (n := n) (curvedRNCMetric κ) (curvedRNCInv κ))
      ∧ pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0
      ∧ (∃ z : Point n, z ≠ 0 ∧ z ∈ Metric.closedBall (0 : Point n) 1) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  obtain ⟨hqmem, hqne⟩ := half_axis_mem_ball (n := n) hn1
  exact ⟨curved_gauge_from_center κ hκ,
    curvedRNCMetric_ricci_trace_diag_ne κ (ne_of_lt hκ) hn c,
    ⟨_, hqne, hqmem⟩⟩

end QIQTH.CurvedA1CenterGauge

section AxiomChecks
open QIQTH.CurvedA1CenterGauge
#print axioms half_axis_mem_ball
#print axioms curved_center_antecedents_nonvacuous
#print axioms curved_center_gate
end AxiomChecks
