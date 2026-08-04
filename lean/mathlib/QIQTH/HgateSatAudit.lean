/-
  HgateSatAudit — J4-231: THE SATISFIABILITY AUDIT of the `hgate` measurable-supplier carriers.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure SOUNDNESS AUDIT of
  the `hcarTau` / `hcarField` / `hcarField2` measurable-supplier existentials that thread the concrete
  Route-B measurability family (`ChartJetHessianMixed.tripleHEmeas_concrete`,
  `GatedTauDerivRep.tripleHEmeas_concrete_of_mixed`, and the `AssemblyLadderR{1,2,3,5}.a1_R6_assembled_v*`
  wrappers).  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous/unsatisfiable
  hypotheses IN THIS FILE'S OWN THEOREMS.  No existing file is edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FLAG (J4-230) AND THE VERDICT: **VACUOUS CONFIRMED — the carriers are UNSATISFIABLE at any
     nonempty gate.**

  Each carrier's on-gate clause is packaged (verbatim, from `ChartJetHessianMixed.tripleHEmeas_concrete`
  lines 580-583 / 591-596 / 611-624) as an UNCONDITIONAL conjunction whose FIRST piece asserts gate
  MEMBERSHIP as a CONCLUSION:

    hcarTau  : … ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
                      w.2.1 ∈ S w.2.2 ∧
                      HasDerivAt (fun u => chartFieldAmp … u w.2.2 w.2.1) (Cfield w.2.2 w.2.1) w.1)

    hcarField k : … ∧ (∀ w, w.2.2 ∈ K → 0 < w.1 →
                        IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
                        (∀ jj, HasDerivAt … ) ∧ PdiffAt … )

    hcarField2 i j : … ∧ (∀ w, w.2.2 ∈ K → 0 < w.1 →
                          IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧ … )

  The field point `w.2.1` ranges over ALL of `Point n` (it is a component of the ∀-quantified `w`), and
  the ONLY guards are `w.2.2 ∈ K` and `0 < w.1` — NEITHER of which constrains `w.2.1`.  So the clause
  demands, for EVERY base `q ∈ K`, EVERY time `τ > 0`, and EVERY field point `p : Point n`, that
  `p ∈ S q`.  That is `S q = Set.univ` for every `q ∈ K`.  For the concrete gate
  `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c` (a PROPER subset — `≠ univ`) with `K` NONEMPTY,
  this is FALSE.  Hence the whole supplier existential is UNSATISFIABLE for the concrete instantiation:
  `a1_R6_assembled_v2` (& v3/v5) is VACUOUSLY dischargeable ONLY by `K = ∅`.

  §1 encodes this verdict as Lean impossibility theorems (`gate_Sconj_impossible`,
  `gate_Sconj₂_impossible`, and the exact-shape corollaries `hcarTau_unsat`, `hcarField_unsat`,
  `hcarField2_unsat`), plus the `Nonempty`+`≠ univ` packaging that matches the concrete flow-ball gate.

  ## THE HONEST FIX (§2): the S-membership belongs on the HYPOTHESIS side.  The identity proof
  `GatedTauDerivRep.witnessTauDeriv_eq_gatedTauRepProd` only ever CONSULTS the gate datum on the branch
  `w.2.2 ∈ K ∧ 0 < w.1` and there it uses `w.2.1 ∈ S w.2.2` to rewrite the on-gate factorisation
  (`vanVleckGatedWitness_gate_apply`).  BUT the representative `gatedTauRepProd` is indicator-gated ONLY
  on the BASE set `{w | w.2.2 ∈ K}`, so the old identity is TRUE only because the over-strong hypothesis
  ERASES the region `q ∈ K, p ∉ S q, τ > 0` (where the witness is `0` yet the base-only representative is
  NOT).  The correct, SATISFIABLE shape carries S-membership as a HYPOTHESIS and re-gates the
  representative on the FULL gate `{w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}`:

    hcarTau_v4 : … ∧ (∀ w, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
                       HasDerivAt (fun u => chartFieldAmp … u w.2.2 w.2.1) (Cfield w.2.2 w.2.1) w.1)

  with the extra (genuinely provable, satisfiable) input `hKSmeas : MeasurableSet {w | w.2.2 ∈ K ∧
  w.2.1 ∈ S w.2.2}`.  §2 delivers this fix FULLY PROVED for the τ carrier: `gatedTauRepProdS` (the
  S-re-gated representative), `gatedTauRepProdS_measurable`, `witnessTauDeriv_eq_gatedTauRepProdS` (the
  everywhere identity under the CONDITIONAL hgate), and `tauDeriv_prod_stronglyMeasurable_v4`
  (BorelDischargeSurface conjunct (1), CONCRETE, with SATISFIABLE hypotheses).  The field / field² v4
  shapes and the re-thread plan are documented in §3 (prose) — they require the identical S-re-gating of
  the `firstFieldPd_prod` / `secondFieldPd_prod` representatives.

  ## BLAST-RADIUS CENSUS (the over-strong `∀ w, w.2.2 ∈ K → 0 < w.1 → … w.2.1 ∈ S w.2.2 …`
     conclusion-shape carrier appears as an OPEN HYPOTHESIS — never DISCHARGED for a nonempty concrete
     K — in ALL of):
       • QIQTH/GatedTauDerivRep.lean       (hgate of `witnessTauDeriv_eq_gatedTauRepProd`;
                                            hcar of `tauDeriv_prod_stronglyMeasurable`;
                                            hcarTau/hcarField of `tripleHEmeas_concrete_of_mixed`)
       • QIQTH/GatedDerivRepProduct.lean   (hcar/hgate of the field-`pd` reps, J4-216)
       • QIQTH/ChartJetHessianMixed.lean   (hcarTau/hcarField/hcarField2 of `tripleHEmeas_concrete`,
                                            J4-218; hgate of the mixed second-jet reps)
       • QIQTH/GatedChartMeasAudit.lean    (hcarTau/hcarField/hcarField2 of `tripleHEmeas_concrete_v3`,
                                            J4-228)
       • QIQTH/ChartJointBorel.lean        (chart-Borel carriers)
       • QIQTH/RightInverseGeneral.lean    (right-inverse carriers)
       • QIQTH/AssemblyLadderR1R2.lean     (hcarTau/hcarField/hcarField2 binders of
                                            `a1_R6_assembled_v2`, lines 158/167/180)
       • QIQTH/AssemblyLadderR3.lean       (same binders, v3 wrapper)
       • QIQTH/AssemblyLadderR5.lean       (same binders, v5 wrapper)
     STATUS: in EVERY one of these the carrier is an INPUT hypothesis carried toward the assembly; NO
     file supplies/discharges it for a concrete NONEMPTY `K`.  So this is a LATENT VACUITY TRAP, NOT an
     already-unsound banked theorem: each `a1_R6_assembled_v*` is a valid implication whose antecedent is
     UNSATISFIABLE at the concrete gate.  The trap fires the moment anyone tries to CLOSE the endgame by
     supplying these existentials at `S z = φ_z '' ball 0 c` with `K ≠ ∅` — at which point §1 proves
     they are FORCED to `K = ∅`.  The corrected §2 shape is what the closure must instead route through.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetHessianMixed

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open scoped Topology BigOperators ContDiff

namespace QIQTH.HgateSatAudit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — THE VERDICT: the over-strong S-conclusion carriers are UNSATISFIABLE.
    ############################################################################### -/

/-- **★★★ `gate_Sconj_impossible` — the atomic impossibility (S-membership as FIRST conclusion).**
    For a NONEMPTY gate base `q₀ ∈ K` and a PROPER gate `p₀ ∉ S q₀`, NO predicate `P` can rescue the
    over-strong clause `∀ w, w.2.2 ∈ K → 0 < w.1 → (w.2.1 ∈ S w.2.2 ∧ P w)`: instantiate at
    `w = (1, p₀, q₀)` (`w.2.2 = q₀ ∈ K`, `w.1 = 1 > 0`) and read off `p₀ ∈ S q₀`, contradicting `hp₀`.
    The analytic tail `P` (a `HasDerivAt`) is IRRELEVANT — the gate MEMBERSHIP alone is the poison.
    NOT `a₁ = R/6`. -/
theorem gate_Sconj_impossible (K : Set (Point n)) (S : Point n → Set (Point n))
    {q₀ : Point n} (hq₀ : q₀ ∈ K) {p₀ : Point n} (hp₀ : p₀ ∉ S q₀)
    (P : ℝ × Point n × Point n → Prop) :
    ¬ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 ∧ P w) := by
  intro h
  exact hp₀ (h (1, p₀, q₀) hq₀ one_pos).1

/-- **★★★ `gate_Sconj₂_impossible` — the atomic impossibility (S-membership as SECOND conclusion).**
    The `hcarField` / `hcarField2` shape puts `IsOpen (S w.2.2)` first and `w.2.1 ∈ S w.2.2` second;
    same poison, read off `.2.1`.  `Q`, `R` (the `IsOpen`, `HasDerivAt`, `PdiffAt` tail) are irrelevant.
    NOT `a₁ = R/6`. -/
theorem gate_Sconj₂_impossible (K : Set (Point n)) (S : Point n → Set (Point n))
    {q₀ : Point n} (hq₀ : q₀ ∈ K) {p₀ : Point n} (hp₀ : p₀ ∉ S q₀)
    (Q R : ℝ × Point n × Point n → Prop) :
    ¬ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → Q w ∧ w.2.1 ∈ S w.2.2 ∧ R w) := by
  intro h
  exact hp₀ (h (1, p₀, q₀) hq₀ one_pos).2.1

/-- **★★★ `hcarTau_unsat` — the EXACT `hcarTau` existential is UNSATISFIABLE at a nonempty proper gate.**
    Verbatim the `hcarTau` body of `ChartJetHessianMixed.tripleHEmeas_concrete` (lines 575-583).  Given
    `q₀ ∈ K` and `p₀ ∉ S q₀`, no `Cfield` satisfies it: its last conjunct falls to
    `gate_Sconj_impossible`.  The three measurability conjuncts are discarded (never needed — the poison
    is purely the gate-membership conclusion).  NOT `a₁ = R/6`. -/
theorem hcarTau_unsat (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    {q₀ : Point n} (hq₀ : q₀ ∈ K) {p₀ : Point n} (hp₀ : p₀ ∉ S q₀) :
    ¬ (∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ S w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1)) := by
  rintro ⟨Cfield, _, _, _, hgate⟩
  exact gate_Sconj_impossible K S hq₀ hp₀ _ hgate

/-- **★★★ `hcarField_unsat` — the EXACT `hcarField k` existential is UNSATISFIABLE.**  Verbatim the
    `hcarField` body (lines 584-596); its last conjunct falls to `gate_Sconj₂_impossible` (S-membership
    is the second conjunct, after `IsOpen (S w.2.2)`).  NOT `a₁ = R/6`. -/
theorem hcarField_unsat (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    {q₀ : Point n} (hq₀ : q₀ ∈ K) {p₀ : Point n} (hp₀ : p₀ ∉ S q₀) :
    ¬ (∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)) := by
  rintro ⟨Pfield, _, _, _, _, hgate⟩
  exact gate_Sconj₂_impossible K S hq₀ hp₀ _ _ hgate

/-- **★★★ `hcarField2_unsat` — the EXACT `hcarField2 i j` existential is UNSATISFIABLE.**  Verbatim the
    `hcarField2` body (lines 597-624); its last conjunct falls to `gate_Sconj₂_impossible`.
    NOT `a₁ = R/6`. -/
theorem hcarField2_unsat (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (i j : Fin n)
    {q₀ : Point n} (hq₀ : q₀ ∈ K) {p₀ : Point n} (hp₀ : p₀ ∉ S q₀) :
    ¬ (∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
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
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)) := by
  rintro ⟨Pifield, Pjfield, Qfield, _, _, _, _, _, _, _, _, hgate⟩
  exact gate_Sconj₂_impossible K S hq₀ hp₀ _ _ hgate

/-- **★★ `hcarTau_unsat_of_nonempty_proper` — the concrete-gate packaging.**  For the concrete flow-ball
    gate `S z = uniformFlowExp … z '' Metric.ball 0 c` one has `S q₀ ≠ Set.univ` (a PROPER subset) for
    every `q₀`, and `K` is NONEMPTY; either datum yields the missing field point `p₀ ∉ S q₀` via
    `Set.ne_univ_iff_exists_not_mem`.  Both hypotheses here are GENUINELY SATISFIABLE (the concrete gate
    IS proper and nonempty), so this corollary is NOT itself vacuous — it is the honest witness that the
    over-strong `hcarTau` carrier collapses exactly at the concrete instantiation.  NOT `a₁ = R/6`. -/
theorem hcarTau_unsat_of_nonempty_proper (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    {q₀ : Point n} (hq₀ : q₀ ∈ K) (hSproper : S q₀ ≠ Set.univ) :
    ¬ (∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ S w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1)) := by
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : Point n, p₀ ∉ S q₀ := by
    by_contra h
    push_neg at h
    exact hSproper (Set.eq_univ_of_forall h)
  exact hcarTau_unsat g gi hC hK S a b hq₀ hp₀

/-! ###############################################################################
    ### §2 — THE HONEST FIX (τ carrier): S-membership as a HYPOTHESIS, representative
    ###       re-gated on the FULL gate `{w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}`.
    ############################################################################### -/

/-- **`gatedTauRepProdS` — the FULL-gate (base ∧ S) re-gated τ representative.**  Identical closed form
    to `GatedTauDerivRep.gatedTauRepProd` (the Gaussian `t`-derivative closed form × amplitude, plus
    Gaussian × `Cfield`) but indicator-gated on `{w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}` — so it VANISHES on
    the region `q ∈ K, p ∉ S q` where the witness is `0` (the region the over-strong hypothesis illicitly
    erased).  NOT `a₁ = R/6`. -/
noncomputable def gatedTauRepProdS (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) : ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
    (fun w : ℝ × Point n × Point n =>
      ((∑ i, ((uniformInverseChart g gi hC hK w.2.2 w.2.1 i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1)))
            * gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1))
          * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
        + gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1) * Cfield w.2.2 w.2.1)

/-- **★ `gatedTauRepProdS_measurable`.**  Joint `(τ,p,q)`-Borel measurability of the re-gated τ
    representative, from `hKSmeas` (the FULL-gate set is measurable — SATISFIABLE for the concrete gate),
    plus the same factor measurabilities as `GatedTauDerivRep.gatedTauRepProd_measurable`.  NO
    continuity.  NOT `a₁ = R/6`. -/
theorem gatedTauRepProdS_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hCmeas : Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)) :
    Measurable (gatedTauRepProdS g gi hC hK S a b Cfield) := by
  unfold gatedTauRepProdS
  have hG : Measurable
      (fun w : ℝ × Point n × Point n =>
        gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hChartMeas)
  have hCoef : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ i, ((uniformInverseChart g gi hC hK w.2.2 w.2.1 i) ^ 2 / (4 * w.1 ^ 2)
              - 1 / (2 * w.1))) := by
    refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
    have h1 : Measurable
        (fun w : ℝ × Point n × Point n =>
          (uniformInverseChart g gi hC hK w.2.2 w.2.1 i) ^ 2 / (4 * w.1 ^ 2)) :=
      (((measurable_pi_apply i).comp hChartMeas).pow_const 2).div
        (measurable_const.mul (measurable_fst.pow_const 2))
    have h2 : Measurable (fun w : ℝ × Point n × Point n => (1 : ℝ) / (2 * w.1)) :=
      measurable_const.div (measurable_const.mul measurable_fst)
    exact h1.sub h2
  exact (((hCoef.mul hG).mul hAmpMeas).add (hG.mul hCmeas)).indicator hKSmeas

/-- **★ `witnessTauDeriv_eq_gatedTauRepProdS` — THE τ EVERYWHERE IDENTITY, under the CONDITIONAL hgate.**
    The raw `∂_τ` kernel of the concrete witness EQUALS the FULL-gate re-gated representative at EVERY
    `w = (τ,p,q)`, now with `hgate` SATISFIABLE (S-membership is a HYPOTHESIS).  Four-way dichotomy:
      • `¬(q ∈ K ∧ p ∈ S q)` — witness `≡ 0` (off the FULL gate, `gatedKernel_apply_of_notMem` from
        `not_and_or`), so `deriv = 0 =` indicator;
      • `q ∈ K, p ∈ S q, τ ≤ 0` — witness `≡ 0` on `Iic τ`, `deriv = 0`, representative shares the
        vanishing `gaussDdim τ` factor;
      • `q ∈ K, p ∈ S q, 0 < τ` — the on-gate `funext` factorisation + product rule, `∂_τ A` supplied by
        the CONDITIONAL `hgate w hzK hτ hpS`.
    The over-strong version's illicit region `q ∈ K, p ∉ S q, τ > 0` is now a HONEST off-gate branch
    (both sides `0`), NOT erased by an unsatisfiable hypothesis.  NOT `a₁ = R/6`. -/
theorem witnessTauDeriv_eq_gatedTauRepProdS (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1) :
    ∀ w : ℝ × Point n × Point n,
      deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1
        = gatedTauRepProdS g gi hC hK S a b Cfield w := by
  intro w
  simp only [gatedTauRepProdS]
  by_cases hzKS : w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2
  · obtain ⟨hzK, hpS⟩ := hzKS
    rw [Set.indicator_of_mem
      (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from ⟨hzK, hpS⟩)]
    set v := uniformInverseChart g gi hC hK w.2.2 w.2.1 with hvdef
    by_cases hτ : 0 < w.1
    · -- ON FULL GATE, τ > 0: the funext factorisation + product rule.
      have hamp := hgate w hzK hτ hpS
      have hfe : (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2)
          = (fun u => gaussDdim u v * chartFieldAmp g gi hC hK a b u w.2.2 w.2.1) := by
        funext u
        rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b u hzK hpS]
        simp only [chartFieldAmp, hvdef]
        ring
      have hgauss_deriv_eq : deriv (fun u => gaussDdim u v) w.1
          = (∑ i, ((v i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) * gaussDdim w.1 v := by
        rw [gaussDdim_heat_eqn w.1 hτ v, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => gaussDdim_pd_pd_i w.1 hτ v i)
      have hgd : DifferentiableAt ℝ (fun u => gaussDdim u v) w.1 := by
        have h := HasDerivAt.fun_finsetProd
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => heatKernel1D_hasDerivAt_t w.1 (v i) hτ)
        simpa only [gaussDdim] using h.differentiableAt
      have hg : HasDerivAt (fun u => gaussDdim u v)
          ((∑ i, ((v i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) * gaussDdim w.1 v) w.1 := by
        have h0 := hgd.hasDerivAt
        rwa [hgauss_deriv_eq] at h0
      rw [hfe]
      exact (hg.mul hamp).deriv
    · -- ON FULL GATE, τ ≤ 0: both sides `0` (witness `≡ 0` on `Iic τ`, `gaussDdim τ = 0`).
      rw [not_lt] at hτ
      have hzero_le : ∀ u : ℝ, u ≤ 0 →
          vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2 = 0 := by
        intro u hu
        rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b u hzK hpS,
            gaussDdim_eq_zero_of_nonpos hn u (uniformInverseChart g gi hC hK w.2.2 w.2.1) hu]
        ring
      have hDW : HasDerivWithinAt
          (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) 0 (Set.Iic w.1) w.1 := by
        refine (hasDerivAt_const w.1 (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
        · exact eventuallyEq_of_mem self_mem_nhdsWithin
            (fun u hu => hzero_le u (le_trans (Set.mem_Iic.mp hu) hτ))
        · exact hzero_le w.1 hτ
      have hderiv0 : deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1 = 0 :=
        hDW.deriv_eq_zero (uniqueDiffWithinAt_Iic w.1)
      rw [hderiv0, hvdef, gaussDdim_eq_zero_of_nonpos hn w.1
        (uniformInverseChart g gi hC hK w.2.2 w.2.1) hτ]
      ring
  · -- OFF the FULL gate (`q ∉ K` ∨ `p ∉ S q`): the `u`-function is identically `0`.
    rw [Set.indicator_of_notMem
      (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from hzKS)]
    have hzero : (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2)
        = (fun _ => (0 : ℝ)) := by
      funext u
      unfold vanVleckGatedWitness
      exact gatedKernel_apply_of_notMem K S _ u w.2.1 w.2.2 (not_and_or.mp hzKS)
    rw [hzero]
    simp

/-- **★★ `tauDeriv_prod_stronglyMeasurable_v4` — BorelDischargeSurface CONJUNCT (1), CONCRETE, with
    SATISFIABLE hypotheses.**  Same conclusion shape as `GatedTauDerivRep.tauDeriv_prod_stronglyMeasurable`
    but with the HONEST carrier: S-membership is a HYPOTHESIS inside `hgate`, and the FULL-gate
    measurability `hKSmeas` is carried (genuinely provable for `S z = φ_z '' ball 0 c`).  Neither
    hypothesis forces `K = ∅`.  CONTINUITY-FREE.  NOT `a₁ = R/6`. -/
theorem tauDeriv_prod_stronglyMeasurable_v4 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1) := by
  obtain ⟨Cfield, hChartMeas, hAmpMeas, hCmeas, hgate⟩ := hcar
  have hrw : (fun w : ℝ × Point n × Point n =>
        deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1)
      = gatedTauRepProdS g gi hC hK S a b Cfield := by
    funext w
    exact witnessTauDeriv_eq_gatedTauRepProdS hn g gi hC hK S a b Cfield hgate w
  rw [hrw]
  exact (gatedTauRepProdS_measurable g gi hC hK S a b Cfield hKSmeas hChartMeas hAmpMeas
    hCmeas).stronglyMeasurable

/-! ###############################################################################
    ### §3 — RE-THREAD PLAN (field / field² v4 shapes + assembly re-thread) — PROSE.
    ###
    ### The τ carrier above is the fully-proved proof-of-concept.  The remaining two carriers require
    ### the IDENTICAL surgery (re-gate the representative on `{w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}`, carry
    ### `hKSmeas`, move S-membership from conclusion to hypothesis):
    ###
    ### hcarField_v4 k : … ∧ (∀ w, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
    ###                        IsOpen (S w.2.2) ∧
    ###                        (∀ jj, HasDerivAt (fun s => uniformInverseChart … (update w.2.1 k s) jj)
    ###                                 (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
    ###                        PdiffAt (chartFieldAmp … w.1 w.2.2) k w.2.1)
    ###   — re-gate `GatedDerivRepProduct.gatedFieldPdRepProd` (currently base-only indicator) on the
    ###   FULL gate; re-prove `firstFieldPd_prod_measurable` with `hKSmeas`; re-prove the field-`pd`
    ###   everywhere identity `witnessFieldPd_eq_gatedFieldPdRepProd` with the CONDITIONAL hgate (its
    ###   on-gate branch already case-splits on `p ∈ S q` and uses the FIELD-NEIGHBOURHOOD `S q ∈ nhds p`
    ###   — supplied here by the on-gate `hpS` plus `IsOpen (S w.2.2)`).
    ###
    ### hcarField2_v4 i j : … ∧ (∀ w, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 → IsOpen (S w.2.2) ∧ … )
    ###   — re-gate `ChartJetHessianMixed.gatedMixed2RepProd` on the FULL gate; re-prove
    ###   `secondFieldPd_prod_measurable` with `hKSmeas`; re-prove `witnessMixed2_eq_gatedMixed2RepProd`
    ###   with the CONDITIONAL hgate.
    ###
    ### THEN: `tripleHEmeas_concrete_v4` = `tripleHEmeas_concrete_of_mixed`-analogue taking
    ### (hKSmeas, hcarTau_v4, hcarField_v4, hcarField2_v4) and feeding `tauDeriv_prod_stronglyMeasurable_v4`
    ### (this file) + the two re-gated field capstones; and `a1_R6_assembled_v6` = `_v2`-analogue with the
    ### v4 carriers + `hKSmeas`.  The `hKSmeas` slot is discharged for the concrete gate by
    ### `ConcreteGateAssembly` (the flow-ball gate is OPEN, hence measurable; `K` is `MeasurableSet` —
    ### their product-preimage intersection is measurable).  All the HARD content (the everywhere
    ### identities, the closed forms, the measurability envelopes) is REUSABLE verbatim; only the outer
    ### indicator set and the hgate quantifier-order change.  See §2 for the completed τ template.
    ###
    ### NOT `a₁ = R/6`.
    ############################################################################### -/

end QIQTH.HgateSatAudit

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HgateSatAudit
#print axioms gate_Sconj_impossible
#print axioms gate_Sconj₂_impossible
#print axioms hcarTau_unsat
#print axioms hcarField_unsat
#print axioms hcarField2_unsat
#print axioms hcarTau_unsat_of_nonempty_proper
#print axioms gatedTauRepProdS_measurable
#print axioms witnessTauDeriv_eq_gatedTauRepProdS
#print axioms tauDeriv_prod_stronglyMeasurable_v4
end AxiomChecks
