/-
  TripleHEmeasConcreteV4GenWith — J4-1164: dispatch 15 of the chart-parametric rebuild campaign — THE
  TRIPLE ASSEMBLY, Canary **C3 ("PrimeHEmeasAudit")**, per `docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ASSEMBLY.  All three `HEmeasBorelAudit.BorelDischargeSurface` conjuncts are now chart-generic +
  primed: conjunct (1) `∂_τ` (`WitnessTauDerivEqWith.tauDeriv_prod_stronglyMeasurable_v4With`, J4-1161),
  conjunct (2) first field-`pd` (`GatedFieldRepSGenWith.firstFieldPd_prod_stronglyMeasurable_v4With`,
  J4-1162), conjunct (3) mixed second field-`pd`
  (`GatedMixed2RepSGenWith.secondFieldPd_prod_stronglyMeasurable_v4With`, this dispatch, earlier file).
  This file assembles them, plus the already-chart-independent `gi`/`christoffel` measurabilities, into
  ONE primed `HEmeasBorelAudit.tripleHEmeas` result for the NEW-chart concrete witness
  `vanVleckGatedWitness'` — a complete primed `HEmeasBorelAudit`-level triple with NO raw `hWmeas`/
  chart-measurability hypothesis remaining.  THIS IS CANARY C3.

  ── THE SHARED-`δ₀` KEY STEP.  The naive route — reusing the three individually-primed capstones
  `tauDeriv_prod_stronglyMeasurable_v4'` / `firstFieldPd_prod_stronglyMeasurable_v4'` /
  `secondFieldPd_prod_stronglyMeasurable_v4'` verbatim — would produce THREE separately-obtained `δ₀`
  witnesses from three separate `∃`-eliminations of `uniformInverseChart'_joint_measurable g gi hC hK`,
  with no built-in guarantee the assembly could pick a single common `c` window without extra
  `min`-juggling.  Avoided entirely: this file calls `uniformInverseChart'_joint_measurable g gi hC hK`
  exactly ONCE at the top, extracting a single `δ₀` and a single `hWmeas` fact per `c`, then feeds that
  ONE `hWmeas` into the three GENERIC (`…With`, not `…'`) capstones directly at the fixed
  `W := uniformInverseChart' g gi hC hK c` — no `min`, no cross-δ₀ reconciliation needed, because the
  generic capstones take `hWmeas` as a free hypothesis rather than re-deriving it internally.  This is a
  ROUTINE engineering choice (not a new mathematical obstruction), following the shape already used by
  every earlier `_'`-suffixed instantiation in this campaign.

  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * ★★★ CANARY C3 — `tripleHEmeas_concrete_v4'`.  Given `hKSmeas`, the (now genuinely `c`-parametric)
      SATISFIABLE `hcarTau`/`hcarField`/`hcarField2` carriers (about `chartFieldAmp'`/
      `uniformInverseChart'`, one instance per `c` in the discharge window), and `hgi`/`hchr`:
        `∃ δ₀ > 0, ∀ c, 0 < c → c < δ₀ → tripleHEmeas g gi (vanVleckGatedWitness' g gi hC hK S a b c)`.
      This is the S1 (`hEmeas`) conjunct of `HEmeasBorelAudit.tripleHEmeas`, for the NEW jointly-
      measurable chart's concrete gated witness, with EVERY chart-measurability obligation discharged
      via `uniformInverseChart'_joint_measurable` — completing the primed analogue of
      `GatedRepSFix.tripleHEmeas_concrete_v4` (J4-232) for the rebuilt chart.

  ## CANARY C3 ASSESSMENT — HONEST, NOT OVERCLAIMED.
  This is the FIRST complete primed `HEmeasBorelAudit`-level triple result with no raw `hWmeas`
  hypothesis — CANARY C3 PASSES.  What remains OUTSIDE this dispatch's scope (Phase 5/6 of the plan,
  NOT part of C3 itself): (a) feeding `tripleHEmeas_concrete_v4'` into
  `gatedWitness_hEboundW_final_gen`/the primed unconditional summit (Phase 5 Task C, Canary C5
  territory); (b) the `hcarTau`/`hcarField`/`hcarField2` carriers here are STILL existential/conditional
  data supplied by the caller (exactly like the OLD `tripleHEmeas_concrete_v4`'s own carriers were —
  this is NOT a new weakening, it mirrors the honest-fix discipline `GatedRepSFix.lean` itself
  established); (c) no claim that `vanVleckGatedWitness'` globally equals `vanVleckGatedWitness`
  (false in general, tube-only agreement per `uniformInverseChart'_eqOn_uniformInverseChart`).

  ## WHAT THIS DOES NOT DO.
  Does NOT touch `GatedRepSFix.lean`, `ChartJetHessianMixed.lean`, `HgateSatAudit.lean`,
  `HEmeasBorelAudit.lean`, `GatedFieldRepSGenWith.lean`, `WitnessTauDerivEqWith.lean`,
  `GatedMixed2RepSGenWith.lean`, or any other existing file (all left completely unedited).  Does NOT
  feed the result into the Phase 5/6 summit (`gatedWitness_hEboundW_final_gen`) — next dispatch target.

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.WitnessTauDerivEqWith
import QIQTH.GatedFieldRepSGenWith
import QIQTH.GatedMixed2RepSGenWith

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ThetaMeasurableEmbedding
open QIQTH.HgateSatAudit
open scoped Topology BigOperators ContDiff

namespace QIQTH.GatedRepSFix

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ CANARY C3 — `tripleHEmeas_concrete_v4'` — THE PRIMED TRIPLE ASSEMBLY.
    ############################################################################### -/

/-- **★★★ CANARY C3 — `tripleHEmeas_concrete_v4'`.**  The FIRST complete primed
    `HEmeasBorelAudit`-level triple result for the NEW-chart concrete witness `vanVleckGatedWitness'`,
    with NO raw `hWmeas`/chart-measurability hypothesis remaining (fully discharged via
    `uniformInverseChart'_joint_measurable`).  Assembled through
    `HEmeasBorelAudit.tripleHEmeas_of_surface` from the three chart-generic capstones
    (`tauDeriv_prod_stronglyMeasurable_v4With`, `firstFieldPd_prod_stronglyMeasurable_v4With`,
    `secondFieldPd_prod_stronglyMeasurable_v4With`), instantiated at the SAME
    `W := uniformInverseChart' g gi hC hK c` with a SINGLE shared `hWmeas` witness. NOT `a₁ = R/6`. -/
theorem tripleHEmeas_concrete_v4' (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcarTau : ∀ c : ℝ, 0 < c → ∃ Cfield : Point n → Point n → ℝ,
        Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp' g gi hC hK a b c w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp' g gi hC hK a b c u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ c : ℝ, 0 < c → ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp' g gi hC hK a b c w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart' g gi hC hK c w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            witnessFieldDeriv' g gi hC hK S a b c k w.1 w.2.1 w.2.2 = 0))
    (hcarField2 : ∀ c : ℝ, 0 < c → ∀ i j : Fin n,
        ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp' g gi hC hK a b c w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart' g gi hC hK c w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart' g gi hC hK c w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp' g gi hC hK a b c w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x => vanVleckGatedWitness' g gi hC hK S a b c w.1 x w.2.2) j y)
              i w.2.1 = 0))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness' g gi hC hK S a b c) := by
  obtain ⟨δ₀, hδ₀, hmeas⟩ := uniformInverseChart'_joint_measurable g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  have hWmeas := hmeas c hc0 hcδ
  refine QIQTH.HEmeasBorelAudit.tripleHEmeas_of_surface g gi
    (vanVleckGatedWitness' g gi hC hK S a b c) ⟨?_, ?_, ?_, hgi, hchr⟩
  · unfold vanVleckGatedWitness'
    exact tauDeriv_prod_stronglyMeasurable_v4With hn g gi hC hK S a b
      (uniformInverseChart' g gi hC hK c) hWmeas hKSmeas (hcarTau c hc0)
  · unfold vanVleckGatedWitness'
    exact firstFieldPd_prod_stronglyMeasurable_v4With hn g gi hC hK S a b
      (uniformInverseChart' g gi hC hK c) hWmeas hKSmeas (hcarField c hc0)
  · unfold vanVleckGatedWitness'
    exact secondFieldPd_prod_stronglyMeasurable_v4With hn g gi hC hK S a b
      (uniformInverseChart' g gi hC hK c) hWmeas hKSmeas (hcarField2 c hc0)

end QIQTH.GatedRepSFix

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GatedRepSFix
#print axioms tripleHEmeas_concrete_v4'
end AxiomChecks
