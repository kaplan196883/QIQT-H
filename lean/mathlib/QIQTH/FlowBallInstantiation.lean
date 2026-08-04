/-
  FlowBallInstantiation — J4-184: instantiating the J4-183 `CConvFacade` data bundles on the
  CONCRETE flow-ball gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c`, and the
  measurable-derivative-representative adapter.  Sol endgame plan (2026-08-04), steps 3–4.
  ONE brick of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is pure
  geometry / measurability plumbing: it (A) BUILDS the `CConvFacade.CConvChartGateData` bundle for
  the concrete flow-ball gate, discharging THREE of its seven fields (`hKmeasSet`, `hCover`,
  `hKmeas`) from the banked flow-ball geometry (`reachableGate_concrete`, `hKmeas_concrete_v7`) and
  carrying the remaining FOUR (`hSmeasSet`, `hVmapMeas`, `hChartB`, `hSliceData`) as honest,
  satisfiable, non-vacuous residues; and (B) supplies the product-a.e. `HasDerivAt` "good-set"
  object `goodProd_hasDerivAt_of_carries` via `ae_prod_of_ae_ae ∘ hMeasSet_of_sliceCont`, plus the
  trivial `CConvDerivativeData` packager `derivativeData_of_rep`.  Never a conclusion; no vacuous /
  unsatisfiable hypotheses; NO `sorry`; NO new axioms.

  ── PART A — the flow-ball `CConvChartGateData` builder (`chartGateData_flowBall`).
    Returns `∃ δ₀ > 0, ∀ c ∈ (0,δ₀), CConvChartGateData … (flowBallGate c) …`.  Discharged from
    geometry:
      • `hKmeasSet := hK.measurableSet`                                     (compactness);
      • `hCover`   from `reachableGate_concrete` (openness + field-`C²`) + the s-INDEPENDENT
                   coverage carry `hMemCov`;
      • `hKmeas`   from `hKmeas_concrete_v7` (its `∃ δ₀` unpacked ONCE at the top), fed by the
                   per-`p` geometry-OR-measurability disjunction `hDisj` and `hMemNear`, the latter
                   DERIVED from the same `hMemCov` (dedup: the s-layer is added by `ae_of_all`).
    Carried (each `∀ c > 0`, satisfiable, none the conclusion): `hSmeasSet`, `hVmapMeas`, `hChartB`,
    `hSliceData` — the four gate/chart measurability fields with no banked flow-ball discharge in
    this toolchain.

  ── PART B — the measurable-derivative-representative adapter.
    • `goodProd_hasDerivAt_of_carries` — from the four `hMeasSet_of_sliceCont` slice carries
      (`hSliceCont`, `hWq`, `hWa`, `hDmeas`, which certify the "good set"
      `{p | HasDerivAt (slice) (witnessFieldDeriv) (x i)}` MEASURABLE) plus the ITERATED a.e.
      `HasDerivAt` carry `hAeAe`, produces the PRODUCT-a.e. `HasDerivAt` on
      `(volume.restrict (uIoc 0 t)).prod ν`, via `JointMeasurability.ae_prod_of_ae_ae`.  This is the
      genuine new content: the `ae_ae → ae_prod` upgrade for the derivative good-set.
    • `derivativeData_of_rep` — packages `{hDmeas, hlin, hDrep}` into `CConvDerivativeData`.  The
      SPLIT (honest): `hlin` (∀ x ∈ u, POINTWISE-everywhere) rides the C²-REGULARITY chain, NOT the
      a.e. measurability chain; `hDmeas` rides the joint-measurability interface; `hDrep` is the
      coordinate representation.  So Part B's `ae_prod` object is a downstream lever, NOT a producer
      of the `∀ x ∈ u` `hlin` field.

  ── `facade_flowBall` — the combined corollary: instantiates `hCConv_discharged_from_data` at the
    flow-ball gate, building `ChartGate` from Part A and taking the other four bundles (Metric /
    Source / Derivative / Envelope, the last two `c`-indexed) as inputs.  Delivers the L1
    `∃`-`HasFDerivAt` shape at every `0 < c < δ₀`.  NOT the `C²` residue slot.  NOT `a₁ = R/6`.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CConvFacade
import QIQTH.GeomPTransportAssess
import QIQTH.GateDiffWiringMeasSet
import QIQTH.JointMeasurability

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixOrder QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.OnGateFieldRegularity
open QIQTH.HeatKernelA1 QIQTH.ResidueBound QIQTH.ExpMap QIQTH.HeatDuhamel
open QIQTH.WitnessDerivDomination
open QIQTH.WitnessDerivMeasurability QIQTH.SliceInterfaceInstantiation
open QIQTH.CoeffContWdiffLift QIQTH.HenvUInstantiation QIQTH.GcoefContinuity
open QIQTH.CConvFacade QIQTH.GeomPTransportAssess QIQTH.ConcreteGateAssembly
open QIQTH.GateDiffWiringMeasSet QIQTH.JointMeasurability QIQTH.GateSetMeasurability
open QIQTH.ChartGeneralPContinuity QIQTH.ChartFieldC2General
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.FlowBallInstantiation

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### PART A — the flow-ball `CConvChartGateData` builder.
    ############################################################################### -/

/-- **★★ `chartGateData_flowBall`.**  Builds `CConvFacade.CConvChartGateData` for the concrete
    flow-ball gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c`, at a single uniform radius
    `δ₀ > 0` and every ball radius `0 < c < δ₀`.  THREE of the seven fields are discharged from the
    banked flow-ball geometry:
      • `hKmeasSet := hK.measurableSet`;
      • `hCover` from `reachableGate_concrete` + the s-independent coverage carry `hMemCov`;
      • `hKmeas` from `hKmeas_concrete_v7` (its `∃ δ₀` unpacked once), fed by the per-`p` disjunction
        `hDisj` and `hMemNear` (DERIVED from `hMemCov`, deduplicated).
    The remaining FOUR (`hSmeasSet`, `hVmapMeas`, `hChartB`, `hSliceData`) are carried as honest,
    satisfiable residues — the gate/chart measurability fields with no banked flow-ball discharge.
    NOT `a₁ = R/6`. -/
theorem chartGateData_flowBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b t : ℝ) (u : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hDisj : ∀ c : ℝ, 0 < c → ∀ p : Point n,
        ( (∀ z ∈ K, uniformInverseChart g gi hC hK z p
              ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
          ∧ (∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
          ∧ (∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) )
        ∨ ( MeasurableSet
              (K ∩ {z : Point n |
                p ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c})
            ∧ AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p)
                ((volume : Measure (Point n)).restrict K) ))
    (hMemCov : ∀ c : ℝ, 0 < c → ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
    (hSmeasSet : ∀ c : ℝ, 0 < c → ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n |
          (Function.update x i w) ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c})
    (hVmapMeas : ∀ c : ℝ, 0 < c → ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        AEMeasurable (fun z : Point n => uniformInverseChart g gi hC hK z (Function.update x i w))
          (volume : Measure (Point n)))
    (hChartB : ∀ c : ℝ, 0 < c → ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        Measurable (fun p : ℝ × Point n =>
          uniformInverseChart g gi hC hK p.2 (Function.update x i w)))
    (hSliceData : ∀ c : ℝ, 0 < c → ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
        (p.2 ∉ K)
        ∨ (p.2 ∈ K
            ∧ (∀ q, q ∉ uniformFlowExp g gi hC hK p.2 '' Metric.ball (0 : Point n) c →
                radialCutoff a b (uniformInverseChart g gi hC hK p.2 q) = 0)
            ∧ Continuous
                (fun w : ℝ =>
                  innerKernelField g gi hC hK a b (t - p.1) p.2 (Function.update x i w)))) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      CConvChartGateData g gi hC hK
        (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b t u := by
  obtain ⟨δK, hδK, hv7⟩ := hKmeas_concrete_v7 g gi hC hK a b t u hg hgpos hu
  obtain ⟨δR, hδR, hreach⟩ := reachableGate_concrete g gi hC hK
  refine ⟨min δK δR, lt_min hδK hδR, ?_⟩
  intro c hc0 hcδ
  have hcK : c < δK := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcR : c < δR := lt_of_lt_of_le hcδ (min_le_right _ _)
  -- `hMemNear` DERIVED from the s-independent `hMemCov` (add the trivial `∀ᵐ s` layer).
  have hMemNear : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ z ∂(volume : Measure (Point n)),
        z ∈ K → x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c := by
    intro x₀ hx₀ i
    exact ae_of_all volume (fun s _hs => hMemCov c hc0 x₀ hx₀ i)
  refine
    { hKmeasSet := hK.measurableSet
      hSmeasSet := hSmeasSet c hc0
      hVmapMeas := hVmapMeas c hc0
      hCover := ?_
      hChartB := hChartB c hc0
      hSliceData := hSliceData c hc0
      hKmeas := hv7 c hc0 hcK (hDisj c hc0) hMemNear }
  -- `hCover` from `reachableGate_concrete` (openness + field-`C²`) + coverage `hMemCov`.
  intro x₀ hx₀ i
  filter_upwards [hMemCov c hc0 x₀ hx₀ i] with x hx
  filter_upwards [hx] with z hz
  intro hzK
  have hxSz : x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c := hz hzK
  obtain ⟨hopen, _hLI, hxfacts⟩ := hreach c hc0 hcR z hzK
  exact ⟨hxSz, hopen, (hxfacts x hxSz).2⟩

/-! ###############################################################################
    ### PART B — the measurable-derivative-representative adapter.
    ############################################################################### -/

/-- **★★ `goodProd_hasDerivAt_of_carries`.**  The PRODUCT-a.e. `HasDerivAt` "good-set" object.  From
    the four `hMeasSet_of_sliceCont` slice carries — which certify the good set
    `{p | HasDerivAt (w ↦ vanVleckGatedWitness … (update x i w) p.2) (witnessFieldDeriv …) (x i)}`
    MEASURABLE — together with the ITERATED a.e. `HasDerivAt` carry `hAeAe`
    (`∀ᵐ s, s ∈ uIoc → ∀ᵐ z, HasDerivAt …`), it produces the PRODUCT-a.e. `HasDerivAt` on
    `(volume.restrict (uIoc 0 t)).prod ν`, via `JointMeasurability.ae_prod_of_ae_ae` (the honest
    Fubini-direction upgrade — needs the measurable-set side-condition).  NOT `a₁ = R/6`. -/
theorem goodProd_hasDerivAt_of_carries (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ν : Measure (Point n)) [SFinite ν] (u₀ : Set (Point n))
    (hSliceCont : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ p : ℝ × Point n, Continuous
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2))
    (hWq : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ q : ℚ,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1)
            (Function.update x i (x i + (q : ℝ))) p.2))
    (hWa : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i (x i)) p.2))
    (hDmeas : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2))
    (hAeAe : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)), ∀ᵐ z ∂ν,
          HasDerivAt
            (fun w => vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z)
            (witnessFieldDeriv g gi hC hK S a b i (t - s) x z) (x i)) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ p ∂((volume.restrict (Set.uIoc 0 t)).prod ν),
        HasDerivAt
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
          (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i) := by
  intro x₀ hx₀ i
  have hMS := hMeasSet_of_sliceCont g gi hC hK S a b t ν u₀ hSliceCont hWq hWa hDmeas x₀ hx₀ i
  filter_upwards [hMS, hAeAe x₀ hx₀ i] with x hms hae
  exact ae_prod_of_ae_ae (volume.restrict (Set.uIoc 0 t)) ν hms hae

/-- **`derivativeData_of_rep`.**  Packages the three verbatim residues into
    `CConvFacade.CConvDerivativeData`.  HONEST SPLIT: `hlin` (∀ x ∈ u, pointwise-everywhere) is fed
    by the C²-REGULARITY chain (differentiability at EVERY `x ∈ u`, not merely a.e.); `hDmeas` by the
    joint-measurability interface; `hDrep` is the coordinate representation.  So the Part-B `ae_prod`
    object is a downstream lever, NOT the producer of the `∀ x ∈ u` `hlin` field.  NOT `a₁ = R/6`. -/
theorem derivativeData_of_rep (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (F : ℝ → Point n → ℝ)
    (H Fconv : ℝ → Point n → Point n → ℝ) (D : Point n → (Point n →L[ℝ] ℝ))
    (hDmeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2))
    (hlin : ∀ x ∈ u, ∀ i : Fin n,
        HasDerivAt (fun w => heatConv H Fconv t (Function.update x i w) 0)
          ((D x) (Pi.single i (1 : ℝ))) (x i))
    (hDrep : ∀ x ∈ u,
        D x = ∑ i : Fin n,
          (∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z
            ∂(volume : Measure (Point n))) • (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ)) :
    CConvDerivativeData g gi hC hK S a b t u F H Fconv D :=
  { hDmeas := hDmeas, hlin := hlin, hDrep := hDrep }

/-! ###############################################################################
    ### THE COMBINED COROLLARY — the L1 facade at the concrete flow-ball gate.
    ############################################################################### -/

/-- **★★ `facade_flowBall`.**  Instantiates `CConvFacade.hCConv_discharged_from_data` at the concrete
    flow-ball gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c`.  The `ChartGate` bundle is
    BUILT from the flow-ball geometry via `chartGateData_flowBall` (its `∃ δ₀` unpacked once); the
    other four bundles (`Metric`, `Source`, and the `c`-indexed `Derivative`/`Envelope`) are inputs.
    Delivers, at every `0 < c < δ₀`, the L1 `∃`-`HasFDerivAt` shape — VERBATIM the `hfam` (L1) slot of
    `SpatialC2.hCConv_reduction`.  This is NOT the `C²` residue slot (the `hD1 : ContDiffAt ℝ 1 D 0`
    tail remains the reported gap).  NOT `a₁ = R/6`. -/
theorem facade_flowBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b t : ℝ) (ht : 0 < t) (F : ℝ → Point n → ℝ)
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (Bs Ba Bd Cf : ℝ)
    (H Fconv : ℝ → Point n → Point n → ℝ)
    (D : ℝ → Point n → (Point n →L[ℝ] ℝ))
    (metric : CConvMetricData g gi)
    (source : CConvSourceData F t Cf)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hDisj : ∀ c : ℝ, 0 < c → ∀ p : Point n,
        ( (∀ z ∈ K, uniformInverseChart g gi hC hK z p
              ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
          ∧ (∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
          ∧ (∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) )
        ∨ ( MeasurableSet
              (K ∩ {z : Point n |
                p ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c})
            ∧ AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p)
                ((volume : Measure (Point n)).restrict K) ))
    (hMemCov : ∀ c : ℝ, 0 < c → ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
    (hSmeasSet : ∀ c : ℝ, 0 < c → ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n |
          (Function.update x i w) ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c})
    (hVmapMeas : ∀ c : ℝ, 0 < c → ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        AEMeasurable (fun z : Point n => uniformInverseChart g gi hC hK z (Function.update x i w))
          (volume : Measure (Point n)))
    (hChartB : ∀ c : ℝ, 0 < c → ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        Measurable (fun p : ℝ × Point n =>
          uniformInverseChart g gi hC hK p.2 (Function.update x i w)))
    (hSliceData : ∀ c : ℝ, 0 < c → ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
        (p.2 ∉ K)
        ∨ (p.2 ∈ K
            ∧ (∀ q, q ∉ uniformFlowExp g gi hC hK p.2 '' Metric.ball (0 : Point n) c →
                radialCutoff a b (uniformInverseChart g gi hC hK p.2 q) = 0)
            ∧ Continuous
                (fun w : ℝ =>
                  innerKernelField g gi hC hK a b (t - p.1) p.2 (Function.update x i w))))
    (deriv : ∀ c : ℝ, 0 < c → CConvDerivativeData g gi hC hK
        (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b t u F H Fconv (D c))
    (env : ∀ c : ℝ, 0 < c → CConvEnvelopeData g gi hC hK
        (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b t u Bs Ba Bd) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∃ w ∈ 𝓝 (0 : Point n), ∀ x ∈ w,
        HasFDerivAt (fun p => heatConv H Fconv t p 0) (D c x) x := by
  obtain ⟨δ₀, hδ₀, hchart⟩ := chartGateData_flowBall g gi hC hK a b t u
    metric.hg metric.hgpos hu hDisj hMemCov hSmeasSet hVmapMeas hChartB hSliceData
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  exact hCConv_discharged_from_data g gi hC hK
    (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b t ht F
    u hu_open hu0 Bs Ba Bd Cf H Fconv (D c)
    metric (hchart c hc0 hcδ) source (deriv c hc0) (env c hc0)

end QIQTH.FlowBallInstantiation

section AxiomChecks
open QIQTH.FlowBallInstantiation
#print axioms chartGateData_flowBall
#print axioms goodProd_hasDerivAt_of_carries
#print axioms derivativeData_of_rep
#print axioms facade_flowBall
end AxiomChecks
