/-
  CConvFacade — J4-183: the bundled `hCConv` L1 facade of the `a₁ = R/6` heat-kernel campaign.
  (Sol endgame plan, 2026-08-04, step 2 — "layered assembly with ONE bundled facade".)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It packages the
  already-banked geometry/measurability/envelope discharges of the concrete first-derivative
  van-Vleck witness `dH := witnessFieldDeriv` into FIVE `: Prop` data bundles and threads them,
  through the banked chain
      `shared_chart_consequences` (metric ⟹ hΘc/hΘne/huc)
        → `SliceInterfaceInstantiation.hjoint_instantiated`   (the `hjoint` G2 slot)
        → `HenvUInstantiation.henv_assembled` / `.hdomS_assembled`  (the envelope G2 slots)
        → `WitnessDerivMeasurability.g2_bundle_assembled`     (all seven G2 slots ⟹ hcont)
        → `GcoefContinuity.hCConv_L1_final`                   (partials + continuity ⟹ Fréchet),
  into the `∃`-`HasFDerivAt` L1 shape
      `∃ w ∈ 𝓝 0, ∀ x ∈ w, HasFDerivAt (fun p => heatConv H F t p 0) (D x) x`.

  Every field of every bundle is the VERBATIM hypothesis shape of the banked theorem that consumes
  it (copied, never re-formulated) — the honest analytic/measurability/geometry inputs are carried,
  NEVER the conclusion.

  ── UNIFICATIONS (documented).
    • `ν := volume` on `Point n` everywhere (the `hjoint_instantiated` generic measure = the `g2`
      inner measure = the `SFinite` witness);  the field index `i : Fin n` and neighbourhood `u` are
      threaded identically through all chains.
    • Envelope constants pinned to `κ := 2`, `C₀ := (Bs·Ba+Bd)·(√2)ⁿ` so that
      `henv_assembled` / `hdomS_assembled` produce EXACTLY the `g2_bundle_assembled` `henv` / `hdomS`
      slots (same width `2·(t−s)`, same constant `C₀`, `C₀·Cf`).

  ── GAP TO THE RESIDUE `hCConv` SLOT (honest).
    `CapstoneStatus.a1_R6_of_residue` demands `hCConv : ContDiffAt ℝ 2 (fun p ↦ heatConv … t p 0) 0`
    (a `C²` statement).  `SpatialC2.hCConv_reduction` splits that `C²` slot into TWO layers:
      (L1) `hfam : ∃ u ∈ 𝓝 0, ∀ x ∈ u, HasFDerivAt (fun p ↦ heatConv H F t p 0) (D x) x`   — THIS FILE,
      (L2) `hD1 : ContDiffAt ℝ 1 D 0`                                                        — STILL OPEN
           (the singular-second-derivative / `hEgrad` tail, Sol bricks after J4-191).
    This facade delivers L1 VERBATIM (its conclusion is defeq to `hCConv_reduction`'s `hfam` slot).
    It does NOT deliver the `C²` slot; L2 + the `hCConv_reduction` assembly remain the reported gap.

  ── CARRIED (each satisfiable, non-vacuous, NEVER the conclusion): the metric smoothness data
    `{hg, hgi, hgpos}`; the chart/gate measurability family `{hKmeasSet, hSmeasSet, hVmapMeas,
    hCover, hChartB, hSliceData, hKmeas}`; the source data `{hFjoint, hFbd, hFmeas}`; the
    derivative-representative data `{hDmeas, hlin, hDrep}` (the bundle J4-184..186 will further
    reduce); the envelope data `{hcoef, hC2fam, hGateData, hGateData'}`.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WitnessDerivMeasurability
import QIQTH.SliceInterfaceInstantiation
import QIQTH.CoeffContWdiffLift
import QIQTH.HenvUInstantiation

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixOrder QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.OnGateFieldRegularity
open QIQTH.HeatKernelA1 QIQTH.ResidueBound QIQTH.ExpMap QIQTH.HeatDuhamel
open QIQTH.WitnessDerivDomination
open QIQTH.WitnessDerivMeasurability QIQTH.SliceInterfaceInstantiation
open QIQTH.CoeffContWdiffLift QIQTH.HenvUInstantiation QIQTH.GcoefContinuity
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.CConvFacade

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### THE FIVE `: Prop` DATA BUNDLES (fields = VERBATIM banked hypothesis shapes).
    ############################################################################### -/

/-- **`CConvMetricData`.**  The ambient metric smoothness/positivity data `{hg, hgi, hgpos}` — the
    input of `CoeffContWdiffLift.{vanVleck_continuous, vanVleck_ne_zero, huc_discharged}`. -/
structure CConvMetricData (g gi : Point n → Fin n → Fin n → ℝ) : Prop where
  hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)
  hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b)
  hgpos : ∀ v : Point n, 0 < Matrix.det (g v)

/-- **`CConvChartGateData`.**  The chart/gate measurability family consumed by
    `SliceInterfaceInstantiation.hjoint_instantiated` (minus the metric, source, shared-pack and
    derivative slots), plus the bare-kernel `z`-ae-measurability family `hKmeas` consumed by
    `g2_bundle_assembled`.  Fields copied VERBATIM. -/
structure CConvChartGateData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) : Prop where
  hKmeasSet : MeasurableSet K
  hSmeasSet : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      MeasurableSet {z : Point n | (Function.update x i w) ∈ S z}
  hVmapMeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      AEMeasurable (fun z : Point n => uniformInverseChart g gi hC hK z (Function.update x i w))
        (volume : Measure (Point n))
  hCover : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ z ∂(volume : Measure (Point n)),
        z ∈ K → (x ∈ S z ∧ IsOpen (S z)
            ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x)
  hChartB : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      Measurable (fun p : ℝ × Point n =>
        uniformInverseChart g gi hC hK p.2 (Function.update x i w))
  hSliceData : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
      (p.2 ∉ K)
      ∨ (p.2 ∈ K
          ∧ (∀ q, q ∉ S p.2 →
              radialCutoff a b (uniformInverseChart g gi hC hK p.2 q) = 0)
          ∧ Continuous
              (fun w : ℝ =>
                innerKernelField g gi hC hK a b (t - p.1) p.2 (Function.update x i w)))
  hKmeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z)
          (volume : Measure (Point n))

/-- **`CConvSourceData`.**  The source-term data `{hFjoint, hFbd, hFmeas}` consumed by
    `hjoint_instantiated` (joint measurability), `g2_bundle_assembled` (`hFbd`, `hFmeas`) and the
    envelope legs (`hFbd`).  Fields copied VERBATIM. -/
structure CConvSourceData (F : ℝ → Point n → ℝ) (t Cf : ℝ) : Prop where
  hFjoint : AEStronglyMeasurable (fun p : ℝ × Point n => F p.1 p.2)
      ((volume.restrict (Set.uIoc 0 t)).prod (volume : Measure (Point n)))
  hFbd : ∀ s z, |F s z| ≤ Cf
  hFmeas : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z) (volume : Measure (Point n))

/-- **`CConvDerivativeData`.**  ⚠ THE MINIMAL "derivative-representative" bundle — the one that
    J4-184..186 will replace by the measurable explicit representative `D` (Sol plan).  Holds the
    inner-kernel measurable-slice carry `hDmeas` (consumed by `hjoint_instantiated`), the linewise
    `HasDerivAt` family `hlin` and the coordinate representation `hDrep` (both consumed by the
    `hCConv_L1_final` tail, = the banked `CConvLayerDischarge` / `PartialsToFDeriv` outputs).  Fields
    copied VERBATIM; `H`, `F(conv)`, `D` are the (generic) heat-convolution kernels + derivative map. -/
structure CConvDerivativeData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (F : ℝ → Point n → ℝ)
    (H Fconv : ℝ → Point n → Point n → ℝ) (D : Point n → (Point n →L[ℝ] ℝ)) : Prop where
  hDmeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      Measurable (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2)
  hlin : ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv H Fconv t (Function.update x i w) 0)
        ((D x) (Pi.single i (1 : ℝ))) (x i)
  hDrep : ∀ x ∈ u,
      D x = ∑ i : Fin n,
        (∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z
          ∂(volume : Measure (Point n))) • (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ)

/-- **`CConvEnvelopeData`.**  The envelope/regularity data: the coefficient positivity `hcoef`, the
    `C²` field-slot family `hC2fam` (consumed by `g2_bundle_assembled` for `hzcont`), and the two
    order-distinct on-gate/off-gate Gaussian dichotomy carries `hGateData` (`∀ᶠ x → ∀ᵐ s`, feeding
    `hdomS_assembled`) / `hGateData'` (`∀ᵐ s → ∀ᶠ x`, feeding `henv_assembled`).  Fields VERBATIM. -/
structure CConvEnvelopeData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (Bs Ba Bd : ℝ) : Prop where
  hcoef : 0 ≤ Bs * Ba + Bd
  hC2fam : ∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
      ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) x₀
  hGateData : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂(volume : Measure ℝ),
      s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
        z ∉ K ∨
        (∃ Pval : Fin n → ℝ,
          z ∈ K ∧ IsOpen (S z) ∧ x ∈ S z ∧
          (∀ k, HasDerivAt
            (fun r : ℝ => uniformInverseChart g gi hC hK z (Function.update x i r) k) (Pval k)
            (x i)) ∧
          PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i x ∧
          |(-(∑ k, uniformInverseChart g gi hC hK z x k * Pval k) / (2 * (t - s)))| ≤ Bs ∧
          |chartFieldAmp g gi hC hK a b (t - s) z x| ≤ Ba ∧
          |pd (chartFieldAmp g gi hC hK a b (t - s) z) i x| ≤ Bd ∧
          (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z x))
  hGateData' : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂(volume : Measure ℝ),
      s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
        z ∉ K ∨
        (∃ Pval : Fin n → ℝ,
          z ∈ K ∧ IsOpen (S z) ∧ x ∈ S z ∧
          (∀ k, HasDerivAt
            (fun r : ℝ => uniformInverseChart g gi hC hK z (Function.update x i r) k) (Pval k)
            (x i)) ∧
          PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i x ∧
          |(-(∑ k, uniformInverseChart g gi hC hK z x k * Pval k) / (2 * (t - s)))| ≤ Bs ∧
          |chartFieldAmp g gi hC hK a b (t - s) z x| ≤ Ba ∧
          |pd (chartFieldAmp g gi hC hK a b (t - s) z) i x| ≤ Bd ∧
          (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z x))

/-! ###############################################################################
    ### THE SHARED-CONSEQUENCES PACK (metric ⟹ hΘc/hΘne/huc, derived ONCE).
    ############################################################################### -/

/-- **`SharedChartConsequences`.**  The coefficient-continuity facts `{hΘc, hΘne, huc}` that
    `hjoint_instantiated` consumes — derivable ONCE from `CConvMetricData` via the banked geometry
    discharges. -/
structure SharedChartConsequences (g gi : Point n → Fin n → Fin n → ℝ) : Prop where
  hΘc : Continuous (vanVleck g)
  hΘne : ∀ w, vanVleck g w ≠ 0
  huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k)

/-- **`shared_chart_consequences`.**  Builds the shared pack from `CConvMetricData` via
    `vanVleck_continuous` / `vanVleck_ne_zero` / `huc_discharged`.  NOT `a₁ = R/6`. -/
theorem shared_chart_consequences {g gi : Point n → Fin n → Fin n → ℝ}
    (metric : CConvMetricData g gi) : SharedChartConsequences g gi where
  hΘc := vanVleck_continuous g metric.hg metric.hgpos
  hΘne := vanVleck_ne_zero g metric.hgpos
  huc := huc_discharged g gi metric.hg metric.hgi metric.hgpos

/-! ###############################################################################
    ### THE FACADE — the `∃`-`HasFDerivAt` L1 shape from the five bundles.
    ############################################################################### -/

/-- **★★ `hCConv_discharged_from_data`.**  The bundled facade: from the five `: Prop` data bundles
    (Metric / ChartGate / Source / Derivative / Envelope) it threads
    `shared_chart_consequences → hjoint_instantiated → henv_assembled/hdomS_assembled →
    g2_bundle_assembled → hCConv_L1_final` and produces the L1 `∃`-`HasFDerivAt` shape — VERBATIM
    the `hfam` (L1) slot of `SpatialC2.hCConv_reduction`.  Envelope constants pinned to `κ = 2`,
    `C₀ = (Bs·Ba+Bd)·(√2)ⁿ`; measure `ν = volume` throughout.  This is NOT the residue's `C²`
    `hCConv` slot — the `C¹` regularity `hD1 : ContDiffAt ℝ 1 D 0` (L2) + the `hCConv_reduction`
    assembly remain the reported gap.  NOT `a₁ = R/6`. -/
theorem hCConv_discharged_from_data
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (ht : 0 < t) (F : ℝ → Point n → ℝ)
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (Bs Ba Bd Cf : ℝ)
    (H Fconv : ℝ → Point n → Point n → ℝ) (D : Point n → (Point n →L[ℝ] ℝ))
    (metric : CConvMetricData g gi)
    (chart : CConvChartGateData g gi hC hK S a b t u)
    (source : CConvSourceData F t Cf)
    (deriv : CConvDerivativeData g gi hC hK S a b t u F H Fconv D)
    (env : CConvEnvelopeData g gi hC hK S a b t u Bs Ba Bd) :
    ∃ w ∈ 𝓝 (0 : Point n), ∀ x ∈ w,
      HasFDerivAt (fun p => heatConv H Fconv t p 0) (D x) x := by
  -- (1) the shared pack: metric ⟹ hΘc/hΘne/huc.
  have shared := shared_chart_consequences metric
  -- (2) the `hjoint` G2 slot from the geometry + chart/gate + shared pack + source + hDmeas.
  have hjoint := hjoint_instantiated g gi hC hK S a b t F (volume : Measure (Point n)) u
    metric.hg metric.hgi metric.hgpos chart.hKmeasSet chart.hSmeasSet source.hFjoint
    chart.hVmapMeas chart.hCover shared.hΘc shared.hΘne shared.huc chart.hChartB
    chart.hSliceData deriv.hDmeas
  -- (3) the envelope G2 slots (`henv`, `hdomS`) at `κ = 2`, `C₀ = (Bs·Ba+Bd)·(√2)ⁿ`.
  have henv := henv_assembled g gi hC hK S a b t ht u Bs Ba Bd env.hcoef env.hGateData'
  have hdomS := hdomS_assembled g gi hC hK S a b t ht F u Bs Ba Bd Cf env.hcoef source.hFbd
    env.hGateData
  -- (4) the full seven-slot G2 assembly ⟹ coefficient continuity (`hcont`).
  have hcont := g2_bundle_assembled g gi hC hK S a b t F u 2
    ((Bs * Ba + Bd) * (Real.sqrt 2) ^ n) Cf (by norm_num) ht
    (mul_nonneg env.hcoef (pow_nonneg (Real.sqrt_nonneg 2) n)) source.hFbd
    env.hC2fam henv chart.hKmeas source.hFmeas hjoint hdomS
  -- (5) the L1 tail: partials (`hlin`) + continuity (`hcont`) + representation (`hDrep`) ⟹ Fréchet.
  exact hCConv_L1_final H Fconv t D u hu_open hu0
    (fun i x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z
      ∂(volume : Measure (Point n)))
    deriv.hlin hcont deriv.hDrep

end QIQTH.CConvFacade

section AxiomChecks
open QIQTH.CConvFacade
#print axioms shared_chart_consequences
#print axioms hCConv_discharged_from_data
end AxiomChecks
