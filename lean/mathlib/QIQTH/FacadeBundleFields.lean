/-
  FacadeBundleFields — J4-319: the hCConv facade-bundle FIELD census (B2–B5 + hD1), with per-field
  discharges at the CONSTANT-RADIUS flow-ball gate.  ONE brick of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  CENSUS / per-field-discharge brick for the hCConv slot's data piles.  No `sorry` (header prose
  excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to
  (or trivially yielding) the conclusion, no existing file edited, nothing committed.  Every carried
  hypothesis is SATISFIABLE.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (P0) THE PER-FIELD CENSUS — `CConvFacadeGate.hCConvSlot_AT_GATE`'s four bundle binders + hD1.

  `hCConvSlot_AT_GATE` (J4-313) discharges B1 (`CConvMetricData`, bare constructor from `{hg,hgi,hgpos}`)
  at the gate and carries the honest census below.  The gate throughout is the CONSTANT-RADIUS flow-ball
  gate exposed by `ConstRadiusGateExport` (J4-316): `S z = uniformFlowExp g gi hC hK z '' ball 0 c`, a
  LITERAL constant radius `c` (no `.choose`).  Verdict key:
    ND  = DERIVABLE-NOW (unconditional at the gate; discharged here or a bare Mathlib fact)
    DH  = DERIVABLE with named, satisfiable hypotheses (a builder exists; its residues are carried)
    W   = GENUINE WALL (no builder anywhere; the honest analytic/geometric carry)
  The "CONSTRADIUS" column records whether exposing the literal constant radius simplifies the field:
  it dissolves the S1 gate-measurability `.choose` residue (see ConstRadiusGateExport) but does NOT
  touch the chart-inverse-at-off-image-points fields — those remain W regardless of the radius.

  ── B2 `CConvChartGateData g gi hC hK S a b t u`  (chart/gate measurability, 7 fields).
     hKmeasSet   : MeasurableSet K
        ND.   `hK.measurableSet`.  DISCHARGED HERE (`hKmeasSet_field`).  CONSTRADIUS: irrelevant.
     hCover      : ∀ x₀∈u,∀ i,∀ᶠ x,∀ᵐ z, z∈K → (x∈S z ∧ IsOpen (S z) ∧ ContDiffAt ℝ 2 (W_z) x)
        DH.   `ConcreteGateAssembly.reachableGate_concrete` (openness + field-C²) + the s-independent
              coverage carry `hMemCov`.  STANDALONE EXTRACTION HERE (`hCover_field`); previously banked
              only inside the `chartGateData_flowBall` monolith.  CONSTRADIUS: the gate is already the
              literal flow-ball, so no `.choose` to dissolve; reachability is at the constant `c`.
     hKmeas      : ∀ x₀∈u,∀ i,∀ᵐ s,s∈uIoc 0 t → ∀ᶠ x, AEStronglyMeasurable (witnessFieldDeriv …) volume
        DH.   `GateSetMeasurability.hKmeas_concrete_v7` (via `FlowBallInstantiation.chartGateData_flowBall`),
              fed the per-`p` disjunction `hDisj` + `hMemCov`.  Carried (heavy monolith); NOT re-extracted.
     hSmeasSet   : ∀ x₀∈u,∀ i,∀ᶠ x,∀ w, MeasurableSet {z | update x i w ∈ S z}
        W.    No builder.  The z-slice of the gate-graph at a FIXED off-image point; `hKSmeas_concrete`
              (Lusin–Souslin) gives the JOINT (q,p)-graph Borel, but z-slices of a Borel set need not be
              Borel.  CONSTRADIUS does NOT help (the graph is already constant-radius).
     hVmapMeas   : ∀ x₀∈u,∀ i,∀ᶠ x,∀ w, AEMeasurable (fun z ↦ W_z (update x i w)) volume
        W.    No builder.  `ChartRepConstruction.flowInverse_jointMeasurable_regional` gives a measurable
              representative `G` that agrees with `W_z p` ONLY on the flow-IMAGE over `K`; off-image the
              chart inverse `W_z p` is uncontrolled.  Genuine chart-inverse measurability carry.
     hChartB     : ∀ x₀∈u,∀ i,∀ᶠ x,∀ w, Measurable (fun p:ℝ×Point ↦ W_{p.2} (update x i w))
        W.    Same root as hVmapMeas (the `Measurable`, not merely `AEMeasurable`, strengthening of the
              same z-measurability of the off-image chart inverse).
     hSliceData  : ∀ x₀∈u,∀ i,∀ᶠ x,∀ p, p.2∉K ∨ (p.2∈K ∧ off-gate cutoff-vanishing ∧ inner-field cont.)
        W.    No builder; the off-gate radialCutoff-support vanishing + inner-field w-continuity carry.

  ── B3 `CConvSourceData (fun s z ↦ leviSeries (heatOp g gi H_G) s z 0) t Cf`  (source data, 3 fields).
     (Audit line 103's "DS none" is SUPERSEDED — `FixedGateSourceProviders` (brick 8) landed a builder.)
     hFjoint     : AEStronglyMeasurable (fun p ↦ F p.1 p.2) ((vol.restrict (uIoc 0 t)).prod vol)
        DH.   `FixedGateSourceProviders.leviSource_joint_aesm` from a `LeviSeriesLocalData E C t` package.
              SPECIALIZED-TO-GATE HERE (`hFjoint_field`, E := heatOp g gi (vanVleckGatedWitness …)).
     hFmeas      : ∀ s, AEStronglyMeasurable (fun z ↦ F s z) volume
        DH.   `FixedGateSourceProviders.leviSource_zslice_aesm` from the same package + the carried
              summability `hFsum`.  SPECIALIZED-TO-GATE HERE (`hFmeas_field`).
     hFbd        : ∀ s z, |F s z| ≤ Cf
        W.    No builder — the machinery gives only the non-uniform Gaussian domination, not a uniform
              constant bound.  Honest uniform-bound carry.

  ── B4 `CConvDerivativeData g gi hC hK S a b t u F H_G leviSeries D`  (derivative data, 3 fields + D).
     hDmeas      : ∀ x₀∈u,∀ i,∀ᶠ x, Measurable (fun p ↦ witnessFieldDeriv … i (t−p.1) x p.2)
        DH.   `GatedDInstantiation.hDmeas_discharged` from `hK.measurableSet` + the bundled `∀ᶠ x` jet
              carry `hData` (Pfield first-jet + chart/amplitude measurabilities + on-gate jet/openness).
     hlin        : ∀ x∈u,∀ i, HasDerivAt (fun w ↦ heatConv H_G F t (update x i w) 0) (D x (Pi.single i 1)) (x i)
        W.    The C²-regularity linewise-derivative family; rides the regularity chain, no self-contained
              witness builder (differentiability at EVERY x∈u).
     hDrep       : ∀ x∈u, D x = ∑ i, (∫∫ witnessFieldDeriv · F) • proj i
        W.    The coordinate representation of D; a definitional carry pairing D to its integral form.
     D           : the explicit derivative map — a free parameter (satisfiable; the hDrep witness).

  ── B5 `CConvEnvelopeData g gi hC hK S a b t u Bs Ba Bd`  (envelope data, 4 fields).
     hcoef       : 0 ≤ Bs*Ba+Bd
        ND.   From `0≤Bs,0≤Ba,0≤Bd`.  DISCHARGED HERE (`hcoef_field`).  CONSTRADIUS: irrelevant.
     hC2fam      : ∀ x₀∈u,∀ᵐ s,s∈uIoc → ∀ᵐ z, ContDiffAt ℝ 2 (fun x' ↦ vanVleckGatedWitness … (t−s) x' z) x₀
        DH.   `ConcreteGateAssembly.hC2fam_concrete_final` at the flow-ball gate, from the point-coverage
              carry `hMemPt` + `hg`/`hgpos`/`hu`.  (Already at the constant gate; re-export banked there.)
     hGateData   : ∀ x₀∈u,∀ i,∀ᶠ x,∀ᵐ s,… ∀ᵐ z, (off-gate ∨ on-gate Gaussian jet dichotomy, Bs/Ba/Bd bounds)
        W.    No builder.  The on-gate/off-gate Gaussian-dichotomy carry (W4 in the DataPileWitnessAudit).
     hGateData'  : the ∀ᵐ s → ∀ᶠ x reordering of hGateData
        W.    Same wall as hGateData (measure-order-swapped; feeds the `henv_assembled` leg).

  ── hD1 : ContDiffAt ℝ 1 D 0
        DH.   `XUniformSliverFull.hD1_from_data` (scalar interface) lifted per-coordinate by
              `HD1CLMLift.hD1_concrete_from_scalar` to the CLM-valued `D`.  The honest STILL-OPEN L2 carry:
              its residue = the per-component x-uniform sliver data (bulk derivatives, bulk pointwise
              convergence, the sqrt-eps sliver).  NOT the conclusion; the genuine L2 singular-second-
              derivative content lives HERE.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (P1) WHAT THIS FILE LANDS — five per-field top-level discharges (no full-bundle constructors).
    • `hKmeasSet_field`  (B2)  — `MeasurableSet K` from compactness.
    • `hCover_field`     (B2)  — the hCover field, standalone from `reachableGate_concrete` + `hMemCov`.
    • `hFjoint_field`    (B3)  — the hFjoint field at the concrete gated-witness Levi source.
    • `hFmeas_field`     (B3)  — the hFmeas field at the same source (+ carried summability).
    • `hcoef_field`      (B5)  — `0 ≤ Bs*Ba+Bd` from three nonnegativities.

  ## (P2) NOT ATTEMPTED — no bundle assembled.  The `CConvChartGateData`/`CConvSourceData`/
  `CConvDerivativeData`/`CConvEnvelopeData` full constructors whnf-time-out per the AxiomAudit; the
  standing rule (one lemma per field) is respected.  The remaining DH fields have banked builders cited
  above (`hKmeas_concrete_v7`, `hDmeas_discharged`, `hC2fam_concrete_final`, `hD1_concrete_from_scalar`)
  and are NOT re-exported here (pure identity re-exports carry no new content).

  ## UPDATED R2 MAP (hCConv tranche after J4-319).  hCConv's field surface now reads:
    ND (2): hKmeasSet, hcoef.
    DH (7): hCover, hKmeas, hFjoint, hFmeas, hDmeas, hC2fam, hD1 — all with banked builders; residues
            are named satisfiable carries (`hMemCov`, `hDisj`, `hData`, `hFsum`, `hMemPt`, sliver data).
    W  (9): hSmeasSet, hVmapMeas, hChartB, hSliceData (chart-inverse off-image measurability, B2);
            hFbd (uniform source bound, B3); hlin, hDrep (derivative-representative, B4);
            hGateData, hGateData' (on-gate Gaussian dichotomy, B5).
  The four B2 chart-inverse walls + the B5 Gaussian-dichotomy walls are the residual hCConv analytic
  surface.  (hDConv diff-under-∫ and hDaLimLU census unchanged by this brick.)

  ⚠  STILL NOT `a₁ = R/6`; every carried hypothesis is an honest satisfiable input.
-/
import QIQTH.ConcreteGateAssembly
import QIQTH.GatedDInstantiation
import QIQTH.FixedGateSourceProviders
import QIQTH.CConvFacade

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.TrueHeatKernel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.HeatDuhamel
open QIQTH.CConvFacade QIQTH.ConcreteGateAssembly QIQTH.FixedGateSourceProviders
open QIQTH.LeviSeriesLocalData
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.FacadeBundleFields

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (B2) — chart/gate measurability field discharges.
    ############################################################################### -/

/-- **★ (B2) `hKmeasSet_field` — the `CConvChartGateData.hKmeasSet` field.**  `MeasurableSet K` from
    compactness (`IsCompact.measurableSet`, `Point n` is `T2`).  DERIVABLE-NOW; unconditional at the
    gate.  NOT `a₁ = R/6`. -/
theorem hKmeasSet_field {K : Set (Point n)} (hK : IsCompact K) : MeasurableSet K :=
  hK.measurableSet

/-- **★★ (B2) `hCover_field` — the `CConvChartGateData.hCover` field at the flow-ball gate.**  For the
    constant-radius flow-ball gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c`, there is a
    uniform radius `δ₀ > 0` such that for every `0 < c < δ₀`, GIVEN the s-independent coverage carry
    `hMemCov` (whenever `z ∈ K` the field point `x` lies in the gate), the exact `hCover` field holds:
    on a.e. `z ∈ K`, `x ∈ S z`, `S z` is OPEN, and the inverse chart is `C²` at `x`.  The openness and
    field-`C²` are supplied by `ConcreteGateAssembly.reachableGate_concrete`; `hMemCov` is the honest
    satisfiable coverage carry (the design intent of the flow-ball gate — never the conclusion).
    Standalone extraction of the `chartGateData_flowBall` internal `hCover` leg.  NOT `a₁ = R/6`. -/
theorem hCover_field (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (u : Set (Point n)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
          ∀ᵐ z ∂(volume : Measure (Point n)),
            z ∈ K → x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
      ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → (x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c
            ∧ IsOpen (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
            ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x) := by
  obtain ⟨δ₀, hδ₀, hreach⟩ := reachableGate_concrete g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ hMemCov x₀ hx₀ i
  filter_upwards [hMemCov x₀ hx₀ i] with x hx
  filter_upwards [hx] with z hz
  intro hzK
  have hxSz : x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c := hz hzK
  obtain ⟨hopen, _hLI, hxfacts⟩ := hreach c hc0 hcδ z hzK
  exact ⟨hxSz, hopen, (hxfacts x hxSz).2⟩

/-! ###############################################################################
    ### (B3) — Levi-source field discharges at the concrete gated witness.
    ############################################################################### -/

/-- **★★ (B3) `hFjoint_field` — the `CConvSourceData.hFjoint` field at the gated Levi source.**  The
    joint `(s,z)` strong measurability of the concrete source
    `F s z = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0` on the restricted
    product `(volume.restrict (uIoc 0 t)).prod volume`, from a `LeviSeriesLocalData` package at the gated
    residual kernel.  Verbatim `FixedGateSourceProviders.leviSource_joint_aesm` specialized to the gate's
    `E := heatOp g gi (vanVleckGatedWitness …)`.  The package is the honest satisfiable carry.
    NOT `a₁ = R/6`. -/
theorem hFjoint_field (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (C t : ℝ)
    (data : LeviSeriesLocalData
      (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C t) :
    AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 t)).prod (volume : Measure (Point n))) :=
  leviSource_joint_aesm _ C t data

/-- **★★ (B3) `hFmeas_field` — the `CConvSourceData.hFmeas` field at the gated Levi source.**  For every
    `s`, the spatial `z`-slice strong measurability of the concrete source `leviSeries (heatOp g gi H_G) s · 0`,
    from the `LeviSeriesLocalData` package + the carried a.e. `z` summability `hFsum`.  Verbatim
    `FixedGateSourceProviders.leviSource_zslice_aesm` specialized to the gate's residual kernel.
    NOT `a₁ = R/6`. -/
theorem hFmeas_field (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (C t : ℝ)
    (data : LeviSeriesLocalData
      (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C t)
    (hFsum : ∀ s : ℝ, ∀ᵐ z ∂(volume : Measure (Point n)),
        Summable (fun k : ℕ =>
          (-1 : ℝ) ^ (k + 1)
            * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (k + 1) s z 0)) :
    ∀ s : ℝ, AEStronglyMeasurable
      (fun z : Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      (volume : Measure (Point n)) :=
  fun s => leviSource_zslice_aesm _ C t data hFsum s

/-! ###############################################################################
    ### (B5) — envelope field discharge.
    ############################################################################### -/

/-- **★ (B5) `hcoef_field` — the `CConvEnvelopeData.hcoef` field.**  `0 ≤ Bs*Ba+Bd` from the three
    envelope-constant nonnegativities.  DERIVABLE-NOW.  NOT `a₁ = R/6`. -/
theorem hcoef_field {Bs Ba Bd : ℝ} (hBs : 0 ≤ Bs) (hBa : 0 ≤ Ba) (hBd : 0 ≤ Bd) :
    0 ≤ Bs * Ba + Bd :=
  add_nonneg (mul_nonneg hBs hBa) hBd

end QIQTH.FacadeBundleFields

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.FacadeBundleFields
#print axioms hKmeasSet_field
#print axioms hCover_field
#print axioms hFjoint_field
#print axioms hFmeas_field
#print axioms hcoef_field
end AxiomChecks
