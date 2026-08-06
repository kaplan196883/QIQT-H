/-
  S1TripleHEmeasGate — J4-314: the S1 (`tripleHEmeas`) ∀-gate measurability carry, AUDITED and
  discharged AT THE CONCRETE GEOMETRIC GATE.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It concerns
  ONLY the base joint-measurability slot (S1) that the wide a₁ capstone
  `ProviderSideExports.wide_a1_R6_interface_discharged_v2` carries as an OUTER antecedent.  No
  `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no
  conclusion-in-disguise.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## (W0) RECON — what `tripleHEmeas` is, the EXACT capstone quantification, the provider audit.

  ── WHAT `tripleHEmeas` UNFOLDS TO.  `HEmeasBorelAudit.tripleHEmeas g gi Wit` is a SINGLE joint
     strong-measurability statement (NOT a triple of components — the "triple" names the three
     coordinates `(τ,p,q)`):
        `tripleHEmeas g gi Wit  :=  StronglyMeasurable
             (fun q : ℝ × Point n × Point n => heatOp g gi Wit q.1 q.2.1 q.2.2)`.
     `heatOp g gi Wit τ p q = deriv (fun u => Wit u p q) τ − laplaceBeltrami g gi (fun p ↦ Wit τ p q) p`.
     So it consumes, jointly in `(τ,p,q)`:  the `∂_τ`-field, the first-`pd` fields `∂_k`, the
     second-`pd` fields `∂_i∂_j`, and the coefficient fields `gⁱʲ` / `Γᵏᵢⱼ` — this is exactly the
     Route-B (E3d, `GatedWitnessEmeas.heatOp_stronglyMeasurable_of_deriv_fields`) surface, PURE
     measurable algebra, NO joint continuity (`hKp1` retired, HEmeasBorelAudit J4-215).

  ── THE EXACT CAPSTONE QUANTIFICATION.  In `wide_a1_R6_interface_discharged_v2` the S1 antecedent is
        `(hEmeas : ∀ (S : Point n → Set (Point n)) (a b : ℝ),
                    tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b))`.
     It is quantified over **ALL** gate-functions `S`, with NO measurability constraint on `S`.

  ── WHY THE LITERAL `∀ S` IS NOT DISCHARGEABLE (and MUST NOT be assumed as a hypothesis).  The
     witness is `vanVleckGatedWitness g gi hC hK S a b = gatedKernel K S (base)`, and
        `gatedKernel K S H τ p q = if q ∈ K then (if p ∈ S q then H τ p q else 0) else 0`.
     For a NON-measurable set-function `S` (e.g. `S q = A` a fixed Lebesgue-non-measurable set) the
     resulting field is non-measurable, so `tripleHEmeas g gi (vanVleckGatedWitness … S a b)` is
     FALSE.  Hence `∀ S, tripleHEmeas …` is an UNSATISFIABLE proposition; it cannot be proved, and it
     cannot be introduced as a hypothesis either (that would violate the satisfiability firewall).
     The honest content of S1 is CONDITIONAL on the gate being measurable (`hKSmeas`, below).

  ── THE PROVIDER AUDIT (the X0 lesson).  The capstone's own provider
     `ProviderSideExports.hEboundW_wide_from_geometry_open_inter` takes the `∀`-gate `hEmeas` and
     applies it at EXACTLY ONE gate — the `S` produced INTERNALLY by
     `GateOpennessExport.gatedWitnessN1_package_open`, namely (chain: `…_le_of_good_pkg_open`)
        `S = fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)`,
     a flow-ball gate whose radius `cf q` is **q-varying** (a covering `.choose`, behind a `dif_pos`).
     So the capstone genuinely NEEDS S1 only at this one measurable gate; the `∀ S` shape is an
     over-general interface artefact.  The geometry-only discharge that IS available
     (`JetsGcUnification.tripleHEmeas_Gc_concrete`) covers the flow-ball at a **constant** radius `c`;
     the residue to internalize S1 into the provider is precisely extending that discharge from a
     constant `c` to the provider's varying `cf q` (a `.choose`-measurability + radialCutoff-support
     brick, NOT the ODE / continuity wall — measurability-only).

  ── POISONING AUDIT.  NONE.  The two discharge routes reused here
     (`JetsGcUnification.tripleHEmeas_Gc_concrete`, `GatedRepSFix.tripleHEmeas_concrete_v4`) are
     std-3 measurable-algebra assemblies; no `hAnear` / W1 (variational-Grönwall) input appears in
     the measurability family (`hDConv_from_banked` W1-poisoning is on the hDConv arrow, not S1).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## (W1) THE HONEST S1 SURFACE (banked upstream; re-exposed here).

     • PER-GATE (arbitrary `S`, CONDITIONAL on honest satisfiable data) — `GatedRepSFix.
       tripleHEmeas_concrete_v4`: for ANY fixed `S`, given the gate-set is measurable
       (`hKSmeas : MeasurableSet {w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}`) and the field-derivative
       CARRIERS (chart-jet + amplitude representatives, on-gate `HasDerivAt`, off-gate vanishing),
       `tripleHEmeas g gi (vanVleckGatedWitness … S a b)` holds.  Every hypothesis is SATISFIABLE at
       the flow-ball gate.  This is the canonical S1 AT-A-MEASURABLE-GATE slot; re-exposed here as
       `tripleHEmeas_at_measurable_gate`.

     • GEOMETRY-ONLY (concrete flow-ball, CONSTANT radius) — `JetsGcUnification.
       tripleHEmeas_Gc_concrete`: from geometry alone (christoffel `C^∞`, metric/inverse `C^∞`,
       `det g > 0`, transport-coeff `C^∞`, measurable `gi`/`christoffel`), for `0 < a < b` there is a
       radius `δ₀ > 0` s.t. every constant-radius flow-ball gate `c ∈ (b, δ₀)` satisfies S1.  This is
       the SATISFIABILITY WITNESS that the per-gate census is inhabited by a genuine geometric gate;
       re-exposed here in the streamlined `tripleHEmeas_flowball_geometry` (the `S = flowball c`
       indirection discharged).

  ## (W2) SLOT VERDICT.  The literal capstone antecedent `∀ S a b, tripleHEmeas …` is BLOCKED —
  it is unsatisfiable over arbitrary `S`.  It is NOT a missing measurability proof; it is an
  over-general interface.  The satisfiable, TRUE content — S1 at every MEASURABLE gate, and its
  inhabitation by the concrete flow-ball — is banked (W1).  The concrete path to remove the outer
  `hEmeas` from the capstone is to REFACTOR the provider to internalize S1 at its OWN gate, which
  requires the constant→varying-radius (`cf q`) extension of `tripleHEmeas_Gc_concrete` (a
  measurability-only brick).  That refactor edits the provider/capstone signature and is deferred to
  a following brick.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.JetsGcUnification
import QIQTH.GatedRepSFix

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open scoped Topology BigOperators ContDiff

namespace QIQTH.S1TripleHEmeasGate

variable {n : ℕ}

/-- **★★ (W1, geometry route) `tripleHEmeas_flowball_geometry` — S1 AT THE CONCRETE FLOW-BALL GATE,
    from geometry alone.**  For `0 < a < b`, there is a radius `δ₀ > 0` such that for every constant
    radius `c ∈ (b, δ₀)` the base joint strong measurability `HEmeasBorelAudit.tripleHEmeas` holds for
    the concrete gated van-Vleck witness at the flow-ball gate `z ↦ uniformFlowExp g gi hC hK z ''
    Metric.ball 0 c`.  A streamlined re-exposition of `JetsGcUnification.tripleHEmeas_Gc_concrete`
    with the `S = flowball c` indirection discharged (`rfl`).  This is the honest SATISFIABILITY
    WITNESS for the S1 gate: the per-gate measurability census is inhabited by a genuine geometric
    (hence measurable) gate.  It does NOT prove the capstone's over-general `∀ S` antecedent — which
    is unsatisfiable — see the header (W2).  Continuity-free (Route B).  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_flowball_geometry (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
        (vanVleckGatedWitness g gi hC hK
          (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b) := by
  obtain ⟨δ₀, hδ0, hspec⟩ :=
    QIQTH.JetsGcUnification.tripleHEmeas_Gc_concrete hn g gi hC hK a b ha hab hg hgiC hgpos hu
      hgiMeas hchr
  exact ⟨δ₀, hδ0, fun c hbc hcδ => hspec c hbc hcδ _ rfl⟩

/-- **★ (W1, per-gate route) `tripleHEmeas_at_measurable_gate` — S1 AT ANY MEASURABLE GATE.**  The
    honest per-gate S1 slot: for an ARBITRARY gate `S`, the base joint strong measurability
    `HEmeasBorelAudit.tripleHEmeas` for the concrete gated van-Vleck witness follows from the HONEST,
    SATISFIABLE data — the gate-set is a `MeasurableSet` (`hKSmeas`) and the field-derivative carriers
    (`hcarTau`/`hcarField`/`hcarField2`: chart-jet / amplitude representatives, on-gate `HasDerivAt`,
    off-gate vanishing).  This is exactly `GatedRepSFix.tripleHEmeas_concrete_v4`, re-exposed through
    this file's namespace as the canonical S1 AT-A-MEASURABLE-GATE slot the capstone provider consumes
    per-instance; each hypothesis is realized at the concrete flow-ball gate (whence
    `tripleHEmeas_flowball_geometry`).  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_at_measurable_gate (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
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
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
              = 0))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hC hK S a b) :=
  QIQTH.GatedRepSFix.tripleHEmeas_concrete_v4 hn g gi hC hK S a b hKSmeas hcarTau hcarField
    hcarField2 hgi hchr

end QIQTH.S1TripleHEmeasGate

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.S1TripleHEmeasGate
#print axioms tripleHEmeas_flowball_geometry
#print axioms tripleHEmeas_at_measurable_gate
end AxiomChecks
