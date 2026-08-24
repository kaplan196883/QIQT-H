/-
  TripleHEmeasV5 — J4-1152: the `tripleHEmeas_concrete_v5` mechanical rethread of `GatedRepSFix`'s S1
  payoff, swapping the `hcarField2` conjunct for `Field2NbhdReshape`'s (J4-237) already-improved WEAKENED
  (`∀ y ∈ S w.2.2`, not global-`∀ y`) shape.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is PURE BOOKKEEPING: a mechanical
  substitution of one conjunct-supplier for an equivalent-but-narrower one inside the S1 assembly, per
  J4-1151's flagged "Dispatch 2/3" optional rethread.  No `sorry` (prose excepted), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypotheses.  No existing file is edited.

  ## CONTEXT.  `GatedRepSFix.tripleHEmeas_concrete_v4` (J4-232) assembles S1 for the concrete gated
  van-Vleck witness from three conjuncts: `∂_τ` (`HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4`),
  first field-`pd` (`GatedRepSFix.firstFieldPd_prod_stronglyMeasurable_v4`), and mixed second field-`pd`
  (`GatedRepSFix.secondFieldPd_prod_stronglyMeasurable_v4`).  The last conjunct's `hcarField2` existential
  carries an `hgate` block whose `j`-line first-jet family and `j`-amplitude `PdiffAt` family are
  quantified GLOBALLY (`∀ y k, …` / `∀ y, …`, over ALL of `Point n`).  `Field2NbhdReshape.lean` (J4-237)
  already builds a STRICTLY WEAKER (hence easier-to-satisfy) replacement conjunct
  `secondFieldPd_prod_stronglyMeasurable_v5`, whose `hcar` existential weakens those two families to
  `∀ y ∈ S w.2.2, …` (the honest local-`C²` region) — everything else (the `i`-line jet, mixed second jet
  `Qfield`, `i`/mixed amplitude data) identical.  `tripleHEmeas_concrete_v5` below is the SAME S1 assembly
  as `tripleHEmeas_concrete_v4`, with ONLY the third conjunct sourced from the v5 (narrower-hypothesis)
  supplier instead of the v4 one — a strictly weaker (more general) top-level hypothesis list.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GatedRepSFix
import QIQTH.Field2NbhdReshape

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open scoped Topology BigOperators ContDiff

namespace QIQTH.TripleHEmeasV5

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `tripleHEmeas_concrete_v5` — S1 FOR THE CONCRETE WITNESS, `hcarField2` NARROWED.**  Identical
    assembly to `GatedRepSFix.tripleHEmeas_concrete_v4`, EXCEPT the third (mixed second field-`pd`)
    conjunct is sourced from `Field2NbhdReshape.secondFieldPd_prod_stronglyMeasurable_v5` instead of
    `GatedRepSFix.secondFieldPd_prod_stronglyMeasurable_v4` — so the `hcarField2` hypothesis here carries
    the STRICTLY WEAKER (`∀ y ∈ S w.2.2`) jet/amplitude families rather than the global-`∀ y` ones.  Every
    carried existential remains SATISFIABLE at the concrete flow-ball gate (S-membership a HYPOTHESIS,
    `hKSmeas` the product-preimage measurable set, `hOffS`/`hOffS2` the radialCutoff-support vanishings).
    Continuity-free.  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_concrete_v5 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0))
    -- ★ THE NARROWED CONJUNCT: `hcarField2` with the `j`-line jet family AND `j`-amplitude `PdiffAt`
    -- family weakened from global-`∀ y` to `∀ y ∈ S w.2.2` (`Field2NbhdReshape`, J4-237).
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y ∈ S w.2.2, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
              = 0))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hC hK S a b) := by
  refine QIQTH.HEmeasBorelAudit.tripleHEmeas_of_surface g gi
    (vanVleckGatedWitness g gi hC hK S a b) ⟨?_, ?_, ?_, hgi, hchr⟩
  · exact QIQTH.HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4 hn g gi hC hK S a b hKSmeas hcarTau
  · exact QIQTH.GatedRepSFix.firstFieldPd_prod_stronglyMeasurable_v4 hn g gi hC hK S a b hKSmeas hcarField
  · exact QIQTH.Field2NbhdReshape.secondFieldPd_prod_stronglyMeasurable_v5 hn g gi hC hK S a b hKSmeas
      hcarField2

end QIQTH.TripleHEmeasV5

/-! ## Axiom check — the public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.TripleHEmeasV5
#print axioms tripleHEmeas_concrete_v5
end AxiomChecks
