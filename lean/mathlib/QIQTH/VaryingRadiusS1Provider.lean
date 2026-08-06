/-
  VaryingRadiusS1Provider — J4-315: the S1 (`tripleHEmeas`) gate-measurability carry, discharged at the
  PROVIDER'S OWN VARYING-RADIUS flow-ball gate, modulo the single honest measurable-selection residue.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It concerns
  ONLY the base joint-measurability slot (S1, `HEmeasBorelAudit.tripleHEmeas`) at the concrete gate the
  capstone provider CHOOSES.  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypotheses, no conclusion-in-disguise.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (V0) RECON — the provider gate, the banked openness, the chosen route, where hEmeas is applied.

  ── THE `cf` CONSTRUCTION.  The capstone provider chain that consumes the outer S1 carry is
        `ProviderSideExports.hEboundW_wide_from_geometry_open_inter`
          →  `GateOpennessExport.gatedWitnessN1_package_open`
          →  `GateOpennessExport.gatedWitnessN1_hEboundW_le_lin_pkg_open`
          →  `GateOpennessExport.gatedWitnessN1_hEboundW_le_of_good_pkg_open`.
     In `_of_good_pkg_open` (GateOpennessExport.lean:104) the gate radius is
        `cf : Point n → ℝ := fun q => if hq : q ∈ K then (hgood q hq).choose else 0`,
     a per-point covering `.choose` behind a `dif_pos`, and the exported gate is
        `S = fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)`.
     (In `_lin_pkg_open` the `hgood` witness is instantiated with the CONSTANT `c = (b+ρc)/2`, but because
     `Classical.choose ⟨const, _⟩` is NOT defeq/propeq to `const`, the exported `cf` is opaque: no
     measurability nor constancy of `cf` survives the `.choose`.  This is the crux.)

  ── WHERE hEmeas IS APPLIED.  In `hEboundW_wide_from_geometry_open_inter` (ProviderSideExports.lean:147)
     the outer `∀`-gate `hEmeas` is used at EXACTLY ONE instance, `hEmeas S a b`, with `S` the destructured
     `∃ S` from `gatedWitnessN1_package_open` — i.e. the varying-radius flow-ball gate above.  So the
     capstone genuinely needs S1 only at this one gate; the `∀ S` shape is an over-general artefact
     (J4-314's verdict: `∀ S` is unsatisfiable).

  ── BANKED OPENNESS INVENTORY.  `GateOpennessExport` exports, for this gate, only the PER-`q` fibrewise
     openness `∀ q ∈ K, IsOpen (S q)` (line 100, read off the `hgood` 5th `.choose_spec` conjunct), and
     downstream just its restriction to `q = 0` (`0 ∈ K → IsOpen (S 0)`).  Per-fibre openness does NOT
     give JOINT `(p,q)`-measurability of the gate set: the `q ∈ K` factor (K compact, not open) blocks
     joint openness (Route A as literally stated), and `cf` carries no regularity, so the flow-ball image
     cannot be shown to vary lower-semicontinuously in `q`.  What IS banked as the true joint-gate engine
     is `ConcreteGateInstantiation.hKSmeas_concrete`: for a CONSTANT radius `c < δ₀` the joint set
        `{w | w.2.2 ∈ K ∧ w.2.1 ∈ φ_(w.2.2) '' ball 0 c}`
     is Borel, via Lusin–Souslin on the injective jointly-continuous graph `Θ(q,v) = (q, φ_q v)` over the
     Borel domain `D = K ×ˢ ball 0 c`.

  ── THE CHOSEN ROUTE (Lusin–Souslin, varying domain).  The `hKSmeas_concrete` construction extends
     VERBATIM to a `q`-VARYING radius `cf`, replacing the product domain `D = K ×ˢ ball 0 c` by the
     graph-of-radius domain `D = {(q,v) | q ∈ K ∧ ‖v‖ < cf q}`.  Everything downstream is unchanged:
       • `Θ` continuous on `D` — `D ⊆ K ×ˢ ball 0 (uniformFlowRadius)` from the reach bound `cf q < δ₀`;
       • `Θ` injective on `D` — the germ left-inverse at radius `cf q < δ₀`;
       • `Θ '' D` Borel — Lusin–Souslin (`ContinuousOn.measurableEmbedding`), then swap-preimage.
     The ONLY new input is measurability of the varying DOMAIN `D`, which factors as
        `{(q,v) | q ∈ K}` (Borel)  ∩  `{(q,v) | ‖v‖ < cf q}` (Borel  ⟺  `Measurable cf`).
     So the varying gate-set measurability reduces EXACTLY to `Measurable cf` (+ the reach bound
     `∀ q ∈ K, cf q < δ₀`, satisfiable geometry).  This is `hKSmeas_varying` below — a genuine PROOF,
     not a residue, of the reduction.

  ── THE HONEST RESIDUE.  `Measurable cf` for the provider's specific `.choose`-built `cf` is NOT
     exported by `GateOpennessExport` and does not follow from the per-point `.choose` (it would require a
     MEASURABLE-SELECTION upgrade of the `hgood`-cover — a Kuratowski–Ryll-Nardzewski / Michael selector,
     or restructuring the provider to expose a measurable/constant radius).  This is the single honest
     residue this brick isolates; every OTHER ingredient of S1-at-the-varying-gate is discharged
     (V1) or transfers from the constant machinery (V2, the base-kernel field carriers, gate-independent
     in their measurable-algebra core).

  ## (V1) `hKSmeas_varying` — BANKED.  The joint gate-set is Borel for ANY measurable radius `cf` bounded
  by the uniform reach on `K`.  Reduces the provider-gate S1 measurability slot to `Measurable cf`.

  ## (V3) `tripleHEmeas_at_varying_flowball_gate` — BANKED (conditional).  Feeding `hKSmeas_varying` into
  `S1TripleHEmeasGate.tripleHEmeas_at_measurable_gate`, S1 holds at the provider's varying flow-ball gate
  given `{Measurable cf, reach bound, the base field-derivative carriers}`.  The carriers are the SAME
  satisfiable jet-supplier existentials the constant gate uses (they concern the base kernel fields, not
  the gate value); here they are carried as hypotheses (V2 discharge at the varying gate is a separate
  on-gate-jet brick).

  ## VERDICT.  The provider gate's S1 slot is NOT an unprovable `∀ S` artefact and NOT a joint-openness
  wall; it is the joint Lusin–Souslin measurability of a varying-radius flow-ball, PROVED here modulo the
  single measurable-selection fact `Measurable cf`.  Internalizing S1 into the provider (V4) additionally
  requires restating the ~130-binder capstone with the `∀`-gate `hEmeas` removed — a mechanical but heavy
  substitution deferred; the load-bearing per-gate content is `hKSmeas_varying` + the V3 wiring.

  NOT `a₁ = R/6`.
-/
import QIQTH.ConcreteGateInstantiation
import QIQTH.S1TripleHEmeasGate

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.FlowJointContinuity
open scoped Topology BigOperators ContDiff

namespace QIQTH.VaryingRadiusS1Provider

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (V1) — the joint gate-set measurability at a VARYING radius `cf`.
    ############################################################################### -/

/-- **★★ (V1) `hKSmeas_varying` — the FULL-gate `MeasurableSet` at the provider's VARYING flow-ball gate.**
    The `q`-varying-radius extension of `ConcreteGateInstantiation.hKSmeas_concrete`.  There is a uniform
    reach `δ₀ > 0` such that, for ANY radius function `cf` that is `Measurable` and bounded on `K` by `δ₀`
    (`∀ q ∈ K, cf q < δ₀`), the joint gate set
      `{w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ φ_(w.2.2) '' Metric.ball 0 (cf w.2.2)}`
    (`φ_q = uniformFlowExp g gi hC hK q`) is `MeasurableSet`.  Route (verbatim `hKSmeas_concrete` with the
    product domain `K ×ˢ ball 0 c` replaced by the graph-of-radius domain
    `D = {(q,v) | q ∈ K ∧ v ∈ ball 0 (cf q)}`): `D` is Borel (`Measurable cf` gives
    `{(q,v) | ‖v‖ < cf q}` measurable via `measurableSet_lt`), `Θ(q,v) = (q, φ_q v)` is jointly continuous
    and injective on `D` (germ left-inverse at radius `cf q < δ₀`), so by Lusin–Souslin
    (`ContinuousOn.measurableEmbedding`) `Θ '' D` is Borel, and the target is its swap-preimage.  The
    varying-gate S1 measurability slot thus reduces EXACTLY to `Measurable cf`.  NOT `a₁ = R/6`. -/
theorem hKSmeas_varying (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (cf : Point n → ℝ) (hcfMeas : Measurable cf) :
    ∃ δ₀ > (0 : ℝ), (∀ q ∈ K, cf q < δ₀) →
      MeasurableSet {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 ''
          Metric.ball (0 : Point n) (cf w.2.2)} := by
  classical
  obtain ⟨δg, hδg, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  have hRpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨min δg (uniformFlowRadius g gi hC hK), lt_min hδg hRpos, ?_⟩
  intro hcfsmall
  -- germ left inverse on `ball 0 (cf q)` for `q ∈ K` (radius below the germ reach).
  have hLeftInv : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < cf q →
      uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v := by
    intro q hq v hv
    have hvg : ‖v‖ < δg :=
      lt_of_lt_of_le (lt_trans hv (hcfsmall q hq)) (min_le_left _ _)
    have hgerm := ((hchart q hq).1 v hvg).1
    simpa using hgerm.eq_of_nhds
  -- the forward-flow graph map and its Borel graph-of-radius domain.
  set Θ : Point n × Point n → Point n × Point n :=
    fun p => (p.1, uniformFlowExp g gi hC hK p.1 p.2) with hΘ
  set D : Set (Point n × Point n) :=
    {p : Point n × Point n | p.1 ∈ K ∧ p.2 ∈ Metric.ball (0 : Point n) (cf p.1)} with hD
  -- `D` is Borel: `{p | p.1 ∈ K}` ∩ `{p | ‖p.2‖ < cf p.1}`.
  have hDmeas : MeasurableSet D := by
    have h1 : MeasurableSet {p : Point n × Point n | p.1 ∈ K} :=
      hK.measurableSet.preimage measurable_fst
    have h2 : MeasurableSet {p : Point n × Point n |
        p.2 ∈ Metric.ball (0 : Point n) (cf p.1)} := by
      have hrw : {p : Point n × Point n | p.2 ∈ Metric.ball (0 : Point n) (cf p.1)}
          = {p : Point n × Point n | ‖p.2‖ < cf p.1} := by
        ext p; simp only [Set.mem_setOf_eq, mem_ball_zero_iff]
      rw [hrw]
      exact measurableSet_lt measurable_snd.norm (hcfMeas.comp measurable_fst)
    have hDeq : D = {p : Point n × Point n | p.1 ∈ K}
        ∩ {p : Point n × Point n | p.2 ∈ Metric.ball (0 : Point n) (cf p.1)} := by
      rw [hD]; ext p; exact Iff.rfl
    rw [hDeq]; exact h1.inter h2
  -- `Θ` is continuous on `D` (the ball sits inside the flow joint-continuity reach).
  have hDsub : D ⊆ K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) := by
    rintro p ⟨hp1, hp2⟩
    refine ⟨hp1, ?_⟩
    rw [mem_ball_zero_iff] at hp2 ⊢
    exact lt_of_lt_of_le (lt_trans hp2 (hcfsmall p.1 hp1)) (min_le_right _ _)
  have hsnd : ContinuousOn (fun p : Point n × Point n =>
      uniformFlowExp g gi hC hK p.1 p.2) D :=
    (uniformFlowExp_joint_continuousOn g gi hC hK).mono hDsub
  have hΘcont : ContinuousOn Θ D := (continuous_fst.continuousOn).prodMk hsnd
  -- `Θ` is injective on `D` via the germ left inverse at the shared base.
  have hΘinj : Set.InjOn Θ D := by
    intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    rw [mem_ball_zero_iff] at hx2 hy2
    rw [hΘ] at hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have hx2' : uniformInverseChart g gi hC hK x.1 (uniformFlowExp g gi hC hK x.1 x.2) = x.2 :=
      hLeftInv x.1 hx1 x.2 hx2
    have hy2c : ‖y.2‖ < cf x.1 := by rw [h1]; exact hy2
    have hy2' : uniformInverseChart g gi hC hK x.1 (uniformFlowExp g gi hC hK x.1 y.2) = y.2 :=
      hLeftInv x.1 hx1 y.2 hy2c
    have hval : uniformFlowExp g gi hC hK x.1 x.2 = uniformFlowExp g gi hC hK x.1 y.2 := by
      rw [h2, ← h1]
    have hxy2 : x.2 = y.2 := by rw [← hx2', hval, hy2']
    exact Prod.ext_iff.mpr ⟨h1, hxy2⟩
  -- Lusin–Souslin: `D.restrict Θ` is a measurable embedding, so the graph `Θ '' D` is Borel.
  have hemb : MeasurableEmbedding (D.restrict Θ) :=
    ContinuousOn.measurableEmbedding hDmeas hΘcont hΘinj
  have hgraph : MeasurableSet (Θ '' D) := by
    have hrange : Θ '' D = Set.range (D.restrict Θ) := (Set.range_restrict Θ D).symm
    rw [hrange, ← Set.image_univ]
    exact hemb.measurableSet_image.mpr MeasurableSet.univ
  -- `Θ '' D` is the `(q,p)`-graph of the varying flow-ball gate.
  have hΘimg : Θ '' D =
      {qp : Point n × Point n | qp.1 ∈ K ∧ qp.2 ∈ uniformFlowExp g gi hC hK qp.1 ''
        Metric.ball (0 : Point n) (cf qp.1)} := by
    ext qp
    constructor
    · rintro ⟨⟨q, v⟩, hqv, rfl⟩
      rw [hD] at hqv
      obtain ⟨hqK, hv⟩ := hqv
      exact ⟨hqK, v, hv, rfl⟩
    · rintro ⟨hqK, v, hv, hvp⟩
      refine ⟨(qp.1, v), ?_, ?_⟩
      · rw [hD]; exact ⟨hqK, hv⟩
      · rw [hΘ]; exact Prod.ext rfl hvp
  -- the target set is the preimage of the graph under the measurable coordinate swap.
  have hpre : {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 ''
          Metric.ball (0 : Point n) (cf w.2.2)}
      = (fun w : ℝ × Point n × Point n => (w.2.2, w.2.1)) ⁻¹'
          {qp : Point n × Point n | qp.1 ∈ K ∧ qp.2 ∈ uniformFlowExp g gi hC hK qp.1 ''
            Metric.ball (0 : Point n) (cf qp.1)} := by
    ext w; exact Iff.rfl
  rw [hpre, ← hΘimg]
  exact hgraph.preimage ((measurable_snd.snd).prodMk measurable_snd.fst)

/-! ###############################################################################
    ### (V3) — S1 (`tripleHEmeas`) at the provider's varying flow-ball gate.
    ############################################################################### -/

/-- **★★ (V3) `tripleHEmeas_at_varying_flowball_gate` — S1 AT THE PROVIDER'S VARYING GATE.**  Feeding
    `hKSmeas_varying` (V1) into `S1TripleHEmeasGate.tripleHEmeas_at_measurable_gate`: for the provider's
    concrete varying-radius flow-ball gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 (cf z)`
    (`hSeq`), the base joint strong measurability `HEmeasBorelAudit.tripleHEmeas` holds, once `cf` is
    `Measurable` and bounded by the exported reach `δ₀` on `K`, and the base field-derivative carriers
    (`hcarTau`/`hcarField`/`hcarField2`, VERBATIM the `tripleHEmeas_at_measurable_gate` slots — they
    concern the base kernel fields, not the gate value, so they transfer from the constant machinery) and
    measurable `gi`/`christoffel` are supplied.  The ONLY genuinely new residue relative to the constant
    gate is `Measurable cf` (the provider's `.choose`-radius measurable-selection fact — see the header
    (V0)); everything else here is a proof or a satisfiable transfer.  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_at_varying_flowball_gate (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (cf : Point n → ℝ) (hcfMeas : Measurable cf)
    (S : Point n → Set (Point n))
    (hSeq : S = fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) (cf z))
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
    ∃ δ₀ > (0 : ℝ), (∀ q ∈ K, cf q < δ₀) →
      QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hC hK S a b) := by
  obtain ⟨δ₀, hδ₀, hmeas⟩ := hKSmeas_varying g gi hC hK cf hcfMeas
  refine ⟨δ₀, hδ₀, fun hbound => ?_⟩
  have hKSmeas : MeasurableSet
      {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} := by
    rw [hSeq]; exact hmeas hbound
  exact QIQTH.S1TripleHEmeasGate.tripleHEmeas_at_measurable_gate hn g gi hC hK S a b
    hKSmeas hcarTau hcarField hcarField2 hgi hchr

end QIQTH.VaryingRadiusS1Provider

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.VaryingRadiusS1Provider
#print axioms hKSmeas_varying
#print axioms tripleHEmeas_at_varying_flowball_gate
end AxiomChecks
