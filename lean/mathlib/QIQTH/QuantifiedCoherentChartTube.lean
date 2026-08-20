/-
  QuantifiedCoherentChartTube — J4-889: the ON-CORE-GRAPH continuity residual of `hbint` (J4-888's
  surviving residual (a)) REDUCED to a single crisp GEOMETRIC input — an open chart-`C²` + in-gate
  cover of the compact core-graph — by composing J4-887's on-gate joint-`C¹` engine with J4-878's
  partial-Fréchet-derivative continuity engine, then restricting to the core-graph.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE — the b-tube frontier, made crisp and localised.

  J4-888 (`HbintCollarMatchedCutoffClosed`) reduced `hbint`'s joint field-Hessian continuity to
  {`BL`-continuity; ON-CORE-GRAPH continuity of the field-Hessian norm on `(K ×ˢ concreteKx) ∩
  jointCore`; matched-cutoff seam-vanishing}.  Its HONEST VERDICT flagged the ON-CORE-GRAPH continuity
  (residual (a)) as the surviving wall: it needs the joint chart `C²` on a neighbourhood of the
  FIXED-radius closed `b`-tube (the compact core-graph), which J4-884's tube supplies only near the
  interior diagonal, unquantified.

  This brick makes that wall CRISP.  It PROVES that the on-core-graph continuity FOLLOWS from a single
  purely geometric input:

    * `onCoreGraphContinuity_of_chartC2_gate_cover` — GIVEN an OPEN set `W` that (i) COVERS the compact
      core-graph `(K ×ˢ concreteKx) ∩ jointCore`, (ii) is entirely IN-GATE (`p.1 ∈ K` ∧ `S p.1 ∈ 𝓝
      p.2` for every `p ∈ W`), and (iii) carries the joint chart `ContDiffOn ℝ 2`, the field-Hessian
      norm is `ContinuousOn` the core-graph.  Mechanism: on `W` the field-derivative kernel is jointly
      `ContDiffOn ℝ 1` (J4-887 `witnessFieldDeriv_jointContDiffOn_onGate`), so its partial-Fréchet
      derivative in the field slot is `ContinuousOn W` (J4-878 `partialFDeriv_norm_jointContinuousOn`);
      `.mono` down to the core-graph `⊆ W` finishes.

    * `hbint_reduced_to_chartC2_gate_cover` — the EXACT `hbint` field of
      `MixedDirectionsFieldHessianEnvelope`, at the concrete flow-ball gate, REDUCED a.e. to:
      `BL`-continuity; the crisp chart-`C²`+in-gate open COVER of the core-graph (per a.e. `s`,
      replacing J4-888's abstract on-core-graph continuity carry); and the matched-cutoff seam
      (unchanged from J4-888).  Chains `onCoreGraphContinuity_of_chartC2_gate_cover` into J4-888's
      `hbint_reduced_to_coreGraphContinuity`.

  ## WHAT THIS FILE DOES **NOT** DO — the honest limit (the frontier is now named, not closed).
  The chart-`C²`+in-gate open cover `W` of the core-graph IS the `JointSecondOrderRNCRegularity`
  frontier restated geometrically: it requires the joint geodesic-exp inverse chart to be `C²` on an
  ambient neighbourhood of the whole `b`-tube over ALL of `K` (boundary included), while the gate is a
  joint neighbourhood of the core-graph.  This is exactly the object J4-884's near-diagonal,
  interior-only, unquantified tube does NOT supply; building it uniformly over `K` needs (i) a
  uniform-over-`K` lower bound on the flow / near-identity radius, (ii) joint `C²` of exp at nonzero
  velocities up to `b` (an extension of J4-884's near-`(z₀,0)` Task D), (iii) boundary coverage via a
  reference-ball transport, and (iv) a compactness assembly — a multi-lemma sub-campaign, NOT a single
  increment.  This brick supplies the crisp reduction + the two-engine composition; it does NOT close
  `hbint`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HbintCollarMatchedCutoffClosed
import QIQTH.FieldHessianJointContinuityClosed
import QIQTH.WitnessFieldDerivJointC1FromTube

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.FieldHessianJointContinuity
open QIQTH.HbintCollarMatchedCutoffClosed
open QIQTH.WitnessFieldDerivJointC1FromTube
open QIQTH.FieldHessianJointContinuityClosed
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators ContDiff

namespace QIQTH.QuantifiedCoherentChartTube

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### C0 — the two-engine composition: on-core-graph continuity from a chart-`C²`+in-gate cover.
    ############################################################################### -/

/-- **★★★ J4-889 — `onCoreGraphContinuity_of_chartC2_gate_cover`.**  J4-888's surviving on-core-graph
    continuity residual (a), PRODUCED from a single crisp geometric input.  For an OPEN set `W` that

      (i)   COVERS the compact core-graph `(K ×ˢ concreteKx) ∩ jointCore`   (`hWcover`);
      (ii)  is entirely IN-GATE — `p.1 ∈ K` and the field gate `S p.1` is a neighbourhood of the
            field point `p.2`, for every `p ∈ W`                            (`hWgate`);
      (iii) carries the joint chart `ContDiffOn ℝ 2`                        (`hWchart`),

    the field-Hessian norm `(z,x) ↦ ‖fderiv ℝ (fun y => witnessFieldDeriv … y z) x‖` is `ContinuousOn`
    the core-graph.

    Mechanism (two banked engines, one order apart).  On `W` the field-derivative kernel
    `(z,y) ↦ witnessFieldDeriv … y z` is jointly `ContDiffOn ℝ 1` (J4-887
    `witnessFieldDeriv_jointContDiffOn_onGate`, from the chart `C²` + gate transparency).  Its
    partial-Fréchet derivative in the field slot then has continuous norm on `W` (J4-878
    `partialFDeriv_norm_jointContinuousOn`).  `ContinuousOn.mono` restricts to the core-graph `⊆ W`.
    `hw` = folded-coefficient smoothness (`prof` `C^∞`).  NOT `a₁ = R/6`. -/
theorem onCoreGraphContinuity_of_chartC2_gate_cover (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    {W : Set (Point n × Point n)} (hWopen : IsOpen W)
    (hWcover : (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b ⊆ W)
    (hWgate : ∀ p ∈ W, p.1 ∈ K ∧ S p.1 ∈ nhds p.2)
    (hWchart : ContDiffOn ℝ 2
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) W) :
    ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖)
      ((K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b) := by
  -- (1) the field-derivative kernel is jointly `ContDiffOn ℝ 1` on the in-gate chart-`C²` open `W`.
  have hc1 : ContDiffOn ℝ 1
      (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1) W :=
    witnessFieldDeriv_jointContDiffOn_onGate g gi hC hK S a b i τ hw hWopen hWchart hWgate
  -- (2) its partial-Fréchet derivative in the field slot has continuous norm on `W`.
  have hcont : ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖) W :=
    partialFDeriv_norm_jointContinuousOn hWopen
      (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1) hc1
  -- (3) restrict to the core-graph `⊆ W`.
  exact hcont.mono hWcover

/-! ###############################################################################
    ### C1 — the `hbint` field, REDUCED a.e. to the chart-`C²`+in-gate cover + seam + `BL`-continuity.
    ############################################################################### -/

/-- **★★★ J4-889 — `hbint_reduced_to_chartC2_gate_cover`.**  The EXACT `hbint` field of
    `MixedDirectionsFieldHessianEnvelope`, at the CONCRETE flow-ball gate, REDUCED a.e. to:
      • the standard `BL`-continuity on `K`;
      • per a.e. `s`, a crisp chart-`C²`+in-gate open COVER `W` of the core-graph
        `(K ×ˢ concreteKx) ∩ jointCore` — this replaces J4-888's abstract on-core-graph continuity
        carry (residual (a)) by the single geometric input that IS the `JointSecondOrderRNCRegularity`
        frontier;
      • the matched-cutoff SEAM-vanishing (per a.e. `s`) — residual (c), UNCHANGED from J4-888,
        dischargeable from `radialCutoff`'s vanishing at radius `b`.
    Chains `onCoreGraphContinuity_of_chartC2_gate_cover` (this file) into J4-888's
    `hbint_reduced_to_coreGraphContinuity`.  `K` nonempty; radii `0 < a < b < c < δ₀`,
    `b < uniformFlowRadius`.  `hbint` is NOT closed — the chart-`C²`+in-gate cover of the WHOLE `b`-tube
    over `K` remains the honest wall.  NOT `a₁ = R/6`. -/
theorem hbint_reduced_to_chartC2_gate_cover (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) (i : Fin n) (t : ℝ) (m : ℕ) (BL : ℝ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ContinuousOn (BL s) K) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∃ W : Set (Point n × Point n), IsOpen W ∧
              (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b ⊆ W ∧
              (∀ p ∈ W, p.1 ∈ K ∧ S p.1 ∈ nhds p.2) ∧
              ContDiffOn ℝ 2
                (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) W) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ p ∈ (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b,
              p ∈ closure ((K ×ˢ concreteKx g gi hC hK b) \ jointCore g gi hC hK b) →
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y p.1) p.2‖ = 0) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          Integrable (fun z => BL s z *
            (⨆ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume := by
  obtain ⟨δ₀, hδ₀, hcollar⟩ :=
    hbint_reduced_to_coreGraphContinuity g gi hC hK hKne a b ha hab hbρ i t m BL
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq hBL hcover hseam
  refine hcollar c hbc hcδ S hSeq hBL ?_ hseam
  -- turn the per-`s` chart-`C²`+in-gate cover into the per-`s` on-core-graph continuity.
  filter_upwards [hcover] with s hs hsU
  obtain ⟨W, hWopen, hWcover, hWgate, hWchart⟩ := hs hsU
  exact onCoreGraphContinuity_of_chartC2_gate_cover g gi hC hK S a b i (t - s) hw
    hWopen hWcover hWgate hWchart

/-! ###############################################################################
    ### C2 — NON-VACUITY: the chart-`C²`+in-gate cover hypotheses are jointly SATISFIABLE.
    ############################################################################### -/

/-- **NON-VACUITY (no unsatisfiable-antecedent trap).**  At the DEGENERATE empty base `K := ∅` the
    core-graph is empty (`jointCore = (…) '' (∅ ×ˢ closedBall 0 b) = ∅`), so the cover `W := ∅`
    discharges ALL three antecedents of `onCoreGraphContinuity_of_chartC2_gate_cover` — cover (`∅ ⊆ ∅`),
    in-gate (vacuous over `∅`), chart `C²` (`ContDiffOn` on `∅`) — and the conclusion `ContinuousOn …
    ∅` holds.  So the hypothesis bundle is jointly SATISFIABLE (not a J4-548-style jointly-unsatisfiable
    antecedent).  The genuinely non-degenerate satisfier — a chart-`C²`+in-gate open cover of a NONEMPTY
    `b`-tube — is the honest frontier that remains.  NOT `a₁ = R/6`. -/
theorem chartC2_gate_cover_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b : ℝ) (i : Fin n) (τ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC (isCompact_empty) S a b i τ y p.1) p.2‖)
      ((∅ ×ˢ concreteKx g gi hC (isCompact_empty) b)
        ∩ jointCore g gi hC (isCompact_empty) b) := by
  refine onCoreGraphContinuity_of_chartC2_gate_cover g gi hC (isCompact_empty) S a b i τ hw
    (W := (∅ : Set (Point n × Point n))) isOpen_empty ?_ ?_ ?_
  · -- cover: the core-graph is empty (`∅ ×ˢ _ = ∅`), hence `⊆ ∅`.
    intro p hp
    exact ((Set.mem_empty_iff_false p.1).mp hp.1.1).elim
  · -- in-gate: vacuous over `∅`.
    intro p hp
    exact ((Set.mem_empty_iff_false p).mp hp).elim
  · -- chart `C²` on `∅`.
    exact contDiffOn_empty

end QIQTH.QuantifiedCoherentChartTube

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.QuantifiedCoherentChartTube
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms onCoreGraphContinuity_of_chartC2_gate_cover
#print axioms hbint_reduced_to_chartC2_gate_cover
#print axioms chartC2_gate_cover_nonvacuous
end AxiomChecks
