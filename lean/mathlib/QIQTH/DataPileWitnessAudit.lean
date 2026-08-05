/-
  DataPileWitnessAudit — J4-244: the N=1-witness DATA audit.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is an
  AUDIT / INVENTORY brick.  It (i) records, family by family, which DATA hypotheses of the R1 capstone
  `RightInverseGeneral.a1_R6_assembled_v2'` (equivalently the vacuity-fixed, live capstone
  `AssemblyV7Rethread.a1_R6_assembled_v7`) have a genuine CONCRETE PROVIDER at the concrete `N = 1`
  gated van-Vleck witness `H_G := vanVleckGatedWitness g gi hChr hK S a b`, and (ii) re-exports the
  cheap, exactly-typed discharges as build-checked `_concrete` theorems.  No `sorry` (prose excepted),
  no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no existing file edited.  Every
  public theorem here is `std-3` (see the `#print axioms` block at the end).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ANCHOR.
  The current closest-to-endpoint, all-hypotheses-satisfiable capstone is
  `AssemblyV7Rethread.a1_R6_assembled_v7` (a pure re-plumb of `a1_R6_assembled_v2'` whose measurability
  supplier is sourced from the VACUITY-FIXED `GatedRepSFix.tripleHEmeas_concrete_v4`).  ⚠ Note the
  earlier `a1_R6_assembled_v6` is a VALID implication but its `hcar{Tau,Field,Field2}` supplier block is
  UNSATISFIABLE for a nonempty proper gate (`HgateSatAudit.hcar*_unsat`: the conclusion-form
  `w.2.1 ∈ S w.2.2` over ALL field points forces `S q = univ`); v7 corrects this by making S-membership a
  hypothesis.  The endpoint `a1_R6_of_geometry` would be v7 with EVERY remaining DATA family discharged
  from pure geometry `(g, gi, Ric)` + the RNC gauge + ONE compatible choice of gate `(a, b, S)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE AUDIT TABLE (family → member → verdict → provider).  Verdicts:
    DC  = DISCHARGED-CONCRETE  (a public theorem whose conclusion IS the member at H_G, not self-consuming)
    D   = DISCHARGEABLE        (banked pieces compose, or a bundle input remains)
    DS  = DATA-still           (no provider anywhere; genuine named input)

  ── Family 1 (F2 measurability / integrability / continuity + sliver).
     hAmeas    D   WitnessMeasDeriv.vanVleckGatedWitness_slice_aestronglyMeasurable   [→ hAmeas_concrete]
                     (reduces to hKm, hSm, hIn = inner order-1 parametrix z-slice ae-meas)
     hBmeas    D   LeviSeriesLocalData.leviSeries_stronglyMeasurable_of_termwise
                     ∘ HEmeasBorelAudit.iterE_zslice_of_tripleHEmeas   (consumes S1 tripleHEmeas + summability)
     hFint     D   ConvCarriesDischarge.heatConvInner_intervalIntegrable_gaussianDom
                     (consumes hAdom/hAzero/hBdom [banked] + base s-meas [= the hFmeas family])
     hpardiff  D   HeatConvRegularity.heatConvInner_hasDerivAt   (abstract engine; z-level diff family)
     hMeasFII  DS  none.  Inner s-integral ae-meas of `W(u−s)0z·L s z0` on restrict(uIoc 0 u); slot S4
                     of HEmeasBorelAudit; no discharge banked.
     hInnerCont DS none.  Abstract HeatConvRegularity.heatConv_inner_continuous exists but consumes an
                     unbanked a.e.-z time-continuity `hcont`; not witness-specialized.
     hFmeas    DS  none (same shape as hMeasFII on the sub-interval; only C3ε consumers).
     hF'meas   DS  none (deriv-integrand inner s-meas; only C3ε consumers).
     hu₀meas   DS  none (near-diagonal amplitude, slot S5; genuine input).
     hu₁meas   DS  none (ditto).
     hUfloor   D   trivial window fact.  [→ timeWindow_concrete supplies it jointly with T/U.]
     nb, hnb   D   trivial (`fun _ _ => univ`, `univ_mem`).   [→ windowNbhd_concrete]
     boundD, hbdd, hbound  DS  none.  The C3ε dominator + its integrability + pointwise domination.
     L, hLnn   D   trivial once L chosen; but paired with hCross (below).
     hCross    DS  none.  Mixed second-difference `|Δ²K| ≤ L·|h||k|` of heatConvFrozen; F2FamilyDischarge
                     CONSUMES it (re-plumb). Genuine analytic input.

  ── Family 2 (boundary near-diagonal parametrix pile).
     hAnear    DS  none — ⚠ AND SHAPE-WRONG.  The witness factorizes as `gaussDdim τ (W z 0)·amp`
                     (Gaussian at the CHART IMAGE `W z 0`, not at `z`; AmplitudePackage.lean:147-152 flags
                     this as a BLOCKER).  hAnear as stated (Gaussian at `z`) holds only for a radially
                     isometric chart.  This is a genuine structural wall, not merely unproven.
     u₀,u₁,r₀,τ₀,hu₀cont,hu₀one,hu₀bdd,hu₁bdd  DS  none (all tied to hAnear).
     T,U,hUopen,htU,hUpos,hUT   D  trivial time-window choice.   [→ timeWindow_concrete]

  ── Family 3 (dominations).
     hAdom     DC  GatedWitnessPackage.gatedWitnessN1_package (4th conjunct); also
                     ConcreteDominations.gatedWitnessN1_D1_of_gateSqControl.  Pure geometry; a,b,S existential.
     hBdom     DC  GatedWitnessPackage.leviSeries_gatedWitnessN1_dominated.  ⚠ gated on hEmeas (the M1
                     joint-strong-measurability of `heatOp` of the witness); a,b,S existential.
     hEzeroE   DC  CoeffBoundsN1.heatOp_gatedWitnessN1_eq_zero_of_nonpos (needs 1 ≤ n).  [→ hEzeroE_concrete]
     hAzero    D   compose gaussDdim_eq_zero_of_nonpos through globalCutoffParametrixWitnessN + gatedKernel.
     hBcont    DS  none.  ContinuousOn of the Levi series on Ioc 0 T ×ˢ univ; only ever a hypothesis.
     hEdom     DS  none.  Width-3/2 affine `heatOp` bound; only CONSUMED (ETailRateBound).  Distinct from
                     the width-2 constant `hEboundFull` (which IS provided; see Family 6).
     hFzero    DS  none.  Levi/iterE vanishing at s ≤ 0; morally from hEzeroE but not banked.

  ── Family 4 (strip / adjacency integrabilities).
     hIlo,hIhi     DS  none.  Strip interval-integrability of the E·B pairing; only consumed.
     hII_lo,hII_hi DS  none.  Self-labeled "DATA" at their abbrev (DaLimLUWallRecon.lean:106-118).

  ── Family 5 (sliver amplitudes).
     hbnd,D0,D1,hD0,hD1nn  D  AmplitudePackage.amplitudePackage_sliver_bound.  Requires instantiating
                     pdpdH := witnessSecondXDeriv and the AmplitudeDerivativeData bundle, whose `hD2Hexpand`
                     is the hard Leibniz–Gaussian geometric identity.

  ── Family 6 (interchange trio + hEboundFull).
     pdpdH,hInterchange,hLapFull,hEcomb   DS  none.  Every occurrence at H_G is a hypothesis; the generic
                     builders (SecondOrderInterchange.hInterchange_discharge, InterchangeThreading.*) are
                     abstract in `H F`, per-fixed-`u`, and consume the UN-BANKED second-order
                     differentiation-under-∫ (Leibniz) identity.  This missing identity is the real wall.
     hEboundFull  D  EboundWiringHD1.hEboundW_from_geometry (∘ CoeffU1Fix.gatedWitnessN1_hEboundW_le_...).
                     Proven FROM GEOMETRY, but with three reshapes vs the stated slot: (i) constant C·(1+t)
                     not C; (ii) restricted τ ≤ t not all τ>0; (iii) gate a,b,S PROVIDER-CHOSEN existentials.
                     [→ hEboundFull_from_geometry_existentialGate]

  ── Family 7 (hCH + CConv facades + hgD1).
     hCH       DC  InftyRebaseCapstone.hCH_discharge_from_geometry (∘ SpatialC2.hCH_discharge).  From
                     {hg,hgi,hgpos,hg0} + centre gate/chart geometry.  [→ hCH_concrete]
     hsrc (∞)  DC  InftyRebaseCapstone.hsrc_from_geometry.  From {hg,hgi,hgpos}.  [→ hsrc_concrete]
                     (⚠ v2'/v7 carry the `∞`-form, discharged; the `⊤` analytic-solve form is unreachable.)
     hgD1      D   XUniformSliverFull.hD1_from_data (abstract engine); witness instantiation SIZE-REJECTED
                     (AssemblyLadderR5), not built.  Per-coordinate 5 data carries remain.
     CConvMetricData     D   trivially packageable from hg/hgi/hgpos; NO builder banked. No witness instance.
     CConvChartGateData  D   FlowBallInstantiation.chartGateData_flowBall builds 3/7 fields (flow-ball gate
                     only); hSmeasSet/hVmapMeas/hChartB/hSliceData carried.
     CConvSourceData     DS  none.  No builder for the Levi-series source slice.
     CConvDerivativeData D   GatedDInstantiation.derivativeData_from_geometry discharges hDmeas from
                     geometry; hlin/hDrep carried.
     CConvEnvelopeData   D   hcoef trivial; hC2fam via ConcreteGateAssembly.hC2fam_concrete_final;
                     hGateData/hGateData' (on-gate Gaussian dichotomy) have NO builder.
     uu,hu_open,hu0,Bs,Ba,Bd,Cf,Dmap   D  free parameters (uu := univ etc.); satisfiable, no provider.

  ── Family 8 (the v7 tripleHEmeas supplier block, via GatedRepSFix.tripleHEmeas_concrete_v4).
     hn        DS  trivial dimension input.
     hKSmeas   DC  ConcreteGateInstantiation.hKSmeas_concrete (Lusin–Souslin, at the flow-ball gate).
                     [→ concreteGate_carriers_concrete]
     hS0       DC  ConcreteGateInstantiation.hS0_concrete.   [→ concreteGate_carriers_concrete]
     hchrMeas  DC  ConcreteGateInstantiation.hchrMeas_concrete (from hChr).  [→ hchrMeas_concrete]
     hgiMeas   D   dischargeable given a `gi`-continuity input (not carried in v7's own signature).
     Gc,hGmeas DC  ChartRepConstruction.flowInverse_jointMeasurable_regional (Lusin–Souslin; a THEOREM).
                     [relevant to the v3/v6 Gc route; v7 reverts to raw chart measurability.]
     hcarTau,hcarField,hcarField2   DS  none.  The τ / field / field² chart-jet supplier existentials:
                     the `Pfield/Cfield/Qfield` HasDerivAt jet data + raw `uniformInverseChart`
                     measurability (the `.choose` definitional wall) + off-S vanishings (`hOffS/hOffS2`,
                     the b-vs-c radialCutoff-support geometry).  No builder produces these at H_G.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DEFINITIVE FINAL-DISTANCE MAP (what stands between the bank and `a1_R6_of_geometry`).
     See the file-final prose block `FINAL_DISTANCE_MAP` for the ordered, sized list.  Headline walls:
       (W1) hAnear shape mismatch (chart-image vs `z` Gaussian) — LARGE, structural.
       (W2) the second-order Leibniz interchange identity feeding pdpdH/hInterchange/hLapFull/hEcomb — LARGE.
       (W3) the gate-COMPATIBILITY meta-wall: each from-geometry provider (hEboundFull, hAdom, hBdom)
            CHOOSES its own (a,b,S) existentially; the endpoint needs ONE gate serving all — MED/LARGE.
       (W4) the CConv on-gate Gaussian-dichotomy carries hGateData/hGateData' — MED.
       (W5) the F2 inner s-measurability trio + hInnerCont + boundD/hbdd/hbound + hCross — MED.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InftyRebaseCapstone
import QIQTH.WitnessMeasDeriv
import QIQTH.EboundWiringHD1
import QIQTH.ConcreteGateInstantiation
import QIQTH.CoeffBoundsN1

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.PullbackMetric
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.DataPileWitnessAudit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### Family 7 — hCH and hsrc: DISCHARGED-CONCRETE from geometry.
    ############################################################################### -/

/-- **`hCH_concrete`.**  The v2'/v7 `hCH` slot — the spatial-`C²` of the concrete `N = 1` gated
    van-Vleck witness diagonal slice — DISCHARGED end-to-end from the `C^∞` metric geometry, verbatim by
    `InftyRebaseCapstone.hCH_discharge_from_geometry`.  Remaining carries are the centre gate/chart
    geometry `{hChr,hK0,hS0,hSopen,hg0}` + metric `{hg,hgi,hgpos}` (satisfiable; none is `hCH`).
    NOT `a₁ = R/6`. -/
theorem hCH_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0) (hSopen : IsOpen (S 0))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j) :
    ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) :=
  QIQTH.InftyRebaseCapstone.hCH_discharge_from_geometry g gi hChr hK S a b t hK0 hS0 hSopen
    hg hgi hgpos hg0

/-- **`hsrc_concrete`.**  The v2'/v7 `hsrc` slot at the honest `∞` level — transport-source `C^∞`
    smoothness — DISCHARGED from `{hg,hgi,hgpos}` by `InftyRebaseCapstone.hsrc_from_geometry`.
    NOT `a₁ = R/6`. -/
theorem hsrc_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)) :=
  QIQTH.InftyRebaseCapstone.hsrc_from_geometry g gi hg hgi hgpos

/-! ###############################################################################
    ### Family 1 — hAmeas: DISCHARGEABLE (reduced to the three lighter carries).
    ############################################################################### -/

/-- **`hAmeas_concrete`.**  The v2'/v7 `hAmeas` slot — base-slice ae-strong-measurability of the witness
    `z ↦ H_G τ 0 z` for every `τ` — REDUCED (via `WitnessMeasDeriv.vanVleckGatedWitness_slice_-`
    `aestronglyMeasurable`) to the three strictly lighter carries `{hKm (MeasurableSet K),
    hSm (MeasurableSet {z | 0 ∈ S z}), hIn (inner order-1 parametrix z-slice ae-meas)}`.  None of the three
    is `hAmeas`.  NOT `a₁ = R/6`. -/
theorem hAmeas_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKm : MeasurableSet K) (hSm : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hIn : ∀ τ : ℝ, AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK) τ 0 z)
      (volume : Measure (Point n))) :
    ∀ τ : ℝ, AEStronglyMeasurable
      (fun z => vanVleckGatedWitness g gi hChr hK S a b τ 0 z) (volume : Measure (Point n)) :=
  fun τ => QIQTH.WitnessMeasDeriv.vanVleckGatedWitness_slice_aestronglyMeasurable
    g gi hChr hK S a b τ 0 hKm hSm (hIn τ)

/-! ###############################################################################
    ### Family 3 — hEzeroE: DISCHARGED-CONCRETE (needs `1 ≤ n`).
    ############################################################################### -/

/-- **`hEzeroE_concrete`.**  The v2'/v7 `hEzeroE` slot — the heat operator of the witness vanishes at
    nonpositive time — DISCHARGED (needs `1 ≤ n`) by `CoeffBoundsN1.heatOp_gatedWitnessN1_eq_zero_of_-`
    `nonpos` specialized to `Θ := vanVleck g`, `u := transportCoeff …`, `Vmap := uniformInverseChart …`
    (defeq to `H_G`).  NOT `a₁ = R/6`. -/
theorem hEzeroE_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) :
    ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q = 0 := by
  intro τ hτ p q
  exact QIQTH.HeatResidualBound.heatOp_gatedWitnessN1_eq_zero_of_nonpos g gi hn K S
    (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) a b
    (uniformInverseChart g gi hChr hK) τ hτ p q

/-! ###############################################################################
    ### Family 6 — hEboundFull: DISCHARGEABLE FROM GEOMETRY (existential gate, τ ≤ t, C·(1+t)).
    ############################################################################### -/

/-- **`hEboundFull_from_geometry_existentialGate`.**  The width-2 Gaussian domination of the gated
    van-Vleck heat operator (the `hEboundFull` shape), delivered FROM GEOMETRY by
    `EboundWiringHD1.hEboundW_from_geometry`.  ⚠ Three reshapes vs the v2'/v7 slot: the constant is
    `C·(1+t)` (call it `C'`), the bound is restricted to `τ ≤ t`, and the gate parameters `a,b` and gate
    map `S` are PROVIDER-CHOSEN existentials (this is the gate-compatibility wall W3).  NOT `a₁ = R/6`. -/
theorem hEboundFull_from_geometry_existentialGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ a b C' : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C' ∧ ∃ S : Point n → Set (Point n),
      ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C' * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  QIQTH.EboundWiringHD1.hEboundW_from_geometry g gi hChr hK hg hgnd hgsymm hinvF hframeK hw hdg0 hg0 t ht

/-! ###############################################################################
    ### Family 8 — the concrete-gate supplier carriers: DISCHARGED-CONCRETE.
    ############################################################################### -/

/-- **`hchrMeas_concrete`.**  The v7 supplier binder `hchrMeas` (christoffel measurability), from the
    standing smoothness `hChr` — re-export of `ConcreteGateInstantiation.hchrMeas_concrete`.
    NOT `a₁ = R/6`. -/
theorem hchrMeas_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p) :=
  QIQTH.ConcreteGateInstantiation.hchrMeas_concrete g gi hChr

/-- **`concreteGate_carriers_concrete`.**  At the concrete flow-ball gate
    `S z = uniformFlowExp g gi hChr hK z '' Metric.ball 0 c` (`0 < c < δ₀`), the THREE v7 supplier binders
    that become provable — `hKSmeas`, `hS0`, `hchrMeas` — ALL hold at once (re-export of
    `ConcreteGateInstantiation.concreteGate_carriers_discharged`).  Discharges the SATISFIABLE
    measurability story; `K` need NOT be empty.  NOT `a₁ = R/6`. -/
theorem concreteGate_carriers_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) →
      MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
      ∧ (0 : Point n) ∈ S 0
      ∧ (∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :=
  QIQTH.ConcreteGateInstantiation.concreteGate_carriers_discharged g gi hChr hK hK0

/-! ###############################################################################
    ### Families 1,2 — the trivial time-window and neighbourhood satisfiabilities.
    ############################################################################### -/

/-- **`timeWindow_concrete`.**  The joint satisfiability of the v2'/v7 time-window family
    `{T,U,hUopen,htU,hUpos,hUT,hUfloor}` at any `t > 0`: take `T := 2t`, `U := Ioo (t/2) (3t/2)`,
    `c := t/2`.  This is a genuine satisfiability witness (never the conclusion), showing these binders
    carry no analytic content.  NOT `a₁ = R/6`. -/
theorem timeWindow_concrete (t : ℝ) (ht : 0 < t) :
    ∃ (T : ℝ) (U : Set ℝ) (c : ℝ),
      0 < T ∧ IsOpen U ∧ t ∈ U ∧ (∀ u ∈ U, 0 < u) ∧ (∀ u ∈ U, u ≤ T)
      ∧ 0 < c ∧ ∀ u ∈ U, c ≤ u := by
  refine ⟨2 * t, Set.Ioo (t / 2) (3 * t / 2), t / 2, by linarith, isOpen_Ioo,
    ⟨by linarith, by linarith⟩, ?_, ?_, by linarith, ?_⟩
  · intro u hu; exact lt_trans (by linarith) hu.1
  · intro u hu; exact le_of_lt (by linarith [hu.2])
  · intro u hu; exact le_of_lt hu.1

/-- **`windowNbhd_concrete`.**  The v2'/v7 neighbourhood family `{nb,hnb}` is trivially satisfiable
    (`nb := fun _ _ => univ`).  NOT `a₁ = R/6`. -/
theorem windowNbhd_concrete :
    ∃ nb : ℕ → ℝ → Set ℝ, ∀ (m : ℕ) (u : ℝ), nb m u ∈ 𝓝 u :=
  ⟨fun _ _ => Set.univ, fun _ _ => univ_mem⟩

end QIQTH.DataPileWitnessAudit

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.DataPileWitnessAudit
#print axioms hCH_concrete
#print axioms hsrc_concrete
#print axioms hAmeas_concrete
#print axioms hEzeroE_concrete
#print axioms hEboundFull_from_geometry_existentialGate
#print axioms hchrMeas_concrete
#print axioms concreteGate_carriers_concrete
#print axioms timeWindow_concrete
#print axioms windowNbhd_concrete
end AxiomChecks

/-!
  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## FINAL_DISTANCE_MAP — the ordered, sized list from the current bank to `a1_R6_of_geometry`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════

  Endpoint = `AssemblyV7Rethread.a1_R6_assembled_v7` with EVERY remaining DATA family discharged from
  `(g,gi,Ric)` + RNC gauge + ONE compatible gate `(a,b,S)`.  Ordered by dependency / leverage; each item
  sized SMALL / MED / LARGE.

  [1] SMALL — thread the already-DC/trivial discharges into a single concrete-`S` capstone re-thread.
      Banked & re-exported here: hCH, hsrc, hEzeroE, hchrMeas, hKSmeas, hS0, timeWindow, windowNbhd.
      Also DC elsewhere: hAdom, hBdom (mod hEmeas), Gc/hGmeas.  Blocked ONLY by the kernel-freeze on the
      ~130-binder v7 restatement (ConcreteGateInstantiation header): mechanical, no new math, but heavy
      to elaborate — needs an incremental `set`-based re-thread, NOT one monolithic `exact`.

  [2] MED — the F2 measurability/integrability chain: hAmeas (reduced here), hBmeas, hFint, hpardiff have
      providers but bottom out at the inner s-measurability trio {hMeasFII, hFmeas, hF'meas} + hInnerCont,
      which are DATA-still.  Needs a joint (s,z)-measurability + Fubini brick for `W(u−s)0z·L s z0`
      (the InnerKernelJointMeas pattern currently covers only `witnessFieldDeriv·F`).

  [3] MED — the sliver/amplitude family {hbnd,D0,D1,hD0,hD1nn}: AmplitudePackage.amplitudePackage_-
      sliver_bound closes it once the AmplitudeDerivativeData bundle (esp. `hD2Hexpand`, the
      Leibniz–Gaussian second-derivative identity) is supplied at pdpdH := witnessSecondXDeriv.

  [4] MED — the CConv bundle instances at H_G: build CConvMetricData (trivial), finish CConvChartGateData
      (4/7 fields), CConvDerivativeData (hlin/hDrep), CConvEnvelopeData (hGateData/hGateData'), and
      CConvSourceData (Levi source slice).  Partial builders exist (FlowBallInstantiation,
      GatedDInstantiation, ConcreteGateAssembly); the on-gate Gaussian dichotomy hGateData/hGateData'
      (W4) has no builder.

  [5] MED/LARGE — the gate-COMPATIBILITY meta-wall (W3): hEboundFull / hAdom / hBdom each choose their OWN
      existential (a,b,S).  The endpoint fixes ONE gate up front, so these must be re-proved for a single
      common flow-ball gate (radius chosen once).  Feasible in principle (all use the same GateSqControl
      flow-ball design) but requires unifying the radius choices — real plumbing.

  [6] LARGE — the second-order Leibniz interchange identity (W2): pdpdH/hInterchange/hLapFull/hEcomb are
      DATA-still with only abstract, per-`u` builders that consume the un-banked differentiation-under-∫
      of the frozen convolution.  This is the analytic heart of the Duhamel `Δ`-term; nothing at the
      witness produces it.

  [7] LARGE — hAnear (W1): STRUCTURAL.  The witness is Gaussian at the CHART IMAGE `W z 0`, not at `z`;
      the stated near-diagonal factorization holds only for a radially isometric chart.  Either reshape
      hAnear to the chart-image Gaussian throughout the boundary pile (and re-derive hu₀/hu₁ there), or
      supply the RNC radial-isometry input.  Also pulls hBcont, hEdom, hFzero, hIlo/hIhi/hII_lo/hII_hi
      (all DATA-still, only-consumed) which live downstream of the same boundary interface.

  [8] SMALL/MED — the residual v7 supplier jets hcarTau/hcarField/hcarField2 (DATA-still): the
      `Pfield/Cfield/Qfield` HasDerivAt chart-jet data + raw `uniformInverseChart` measurability (the
      `.choose` wall) + off-S vanishings (b-vs-c radialCutoff support).  The Gc-consumer route
      (`GcConsumerMirror.tripleHEmeas_Gc`) + the deferred `tripleHEmeas_concrete_v5` would unify the S-fix
      with the chart-wall discharge; the off-image surjectivity `hSurj` (ImageSupportDischarge) is the one
      honest geometric carry of the Gc route.

  NEXT-BRICK RECOMMENDATION: item [2]-head — the joint (s,z)-measurability + Fubini brick discharging
  {hMeasFII, hFmeas, hF'meas} for `H_G(u−s)0z · leviSeries s z 0`, promoting hAmeas/hBmeas/hFint/hpardiff
  from DISCHARGEABLE to a self-contained concrete F2 pack.  It is the smallest genuinely-DATA cluster with
  the widest downstream unblock and no structural wall (unlike W1/W2).

  NOT `a₁ = R/6`.
-/
