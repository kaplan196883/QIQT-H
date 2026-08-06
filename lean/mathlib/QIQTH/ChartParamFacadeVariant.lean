/-
  ChartParamFacadeVariant — J4-321: making the J4-320 `Wg` dissolution CONSUMABLE.  The
  chart-PARAMETRIC variant of the hCConv facade's `CConvChartGateData` bundle, instantiated at the
  piecewise chart `Wg`, with the B2 walls 2/3 (`hVmapMeas`/`hChartB`) now INTERNAL.  ONE brick of the
  `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It builds a
  DATA-STRUCTURE variant + one satisfiability builder.  No `sorry` (header prose excepted), no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.  Every carried hypothesis is
  SATISFIABLE (discharged from a banked builder or an honest on-gate / partial carry).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (N0) RECON — the chart-flow through the consumer, and the verdict.

  QUESTION.  Does the consumer `CConvConcreteThreading.hCConv_concrete_from_data` (which threads
  `CConvFacade.hCConv_discharged_from_data → SpatialC2.hCConv_reduction`) use the chart ONLY through the
  bundle's fields (chart opaque), so the variant is a pure re-statement?  ANSWER: **NO.**  The chart
  enters the consumer's PROOF in TWO structurally-independent ways.

  ── (a) THE WITNESS'S OWN INTERNAL CHART — FIXED, not a proof-side tool.  Contrary to the first-pass
     J4-320 verdict ("the witness does not mention the chart"), the concrete witness DOES contain the
     chart internally:
        `vanVleckGatedWitness g gi hC hK S a b
           = gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
               (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK))`
     (ConvApproximants, lines 161–166).  The consumer's CONCLUSION —
        `ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hC hK S a b) (leviSeries …) t p 0) 0`
     — therefore contains `uniformInverseChart g gi hC hK` LITERALLY.  The chart in the witness is FIXED
     by the capstone slot; it is NOT a proof-side representation we may swap.  (What SAVES the swap
     morally is the gate/cutoff: `gatedKernel K S` × `radialCutoff a b` kill the region where the raw
     chart and `Wg` disagree — support radius `b < c ≤ ρ`, agreement radius `ρ` — so as a FUNCTION the
     witness is chart-invariant on/off the gate.  But that is a downstream fact, not a bundle swap.)

  ── (b) THE B2 BUNDLE FIELDS FEED A CHART-HARDWIRED CONSUMER.  Four of the seven `CConvChartGateData`
     fields mention the chart EXPLICITLY as the standalone function `uniformInverseChart g gi hC hK z`:
     `hVmapMeas` (a.e.-measurable `z`-slice), `hCover` (the `ContDiffAt ℝ 2 (chart z) x` leg), `hChartB`
     (`Measurable` `z`-slice), `hSliceData` (`radialCutoff a b (chart p.2 q) = 0`).  These feed
     `SliceInterfaceInstantiation.hjoint_instantiated`, whose OWN binders — and whose internal
     `hWq_of_chartBorel` / `hWa_of_chartBorel` / `hSliceCont_of_data` sub-lemmas — HARDWIRE
     `uniformInverseChart g gi hC hK` (verbatim, SliceInterfaceInstantiation lines 338–357).  The B5
     envelope bundle (`hGateData`/`hGateData'`) and `henv_assembled`/`hdomS_assembled` likewise hardwire
     it.  So the chart is NOT an opaque bundle function in the consumer's proof.

  ── THE VERDICT: **BLOCKED-with-named-residue** (agreement-transfer sound, but not a new-file
     operation).  Substituting `W' := Wg` in a chart-PARAMETRIC B2 bundle is well-typed (this file's
     `CConvChartGateDataW`), and walls 2/3 (`hVmapMeas`/`hChartB`) DISCHARGE at `Wg` from the banked
     joint measurability (this file's `chartGateDataW_of_Wg`).  BUT re-threading the consumer with the
     `Wg`-variant bundle CANNOT be done here, because:
       • `hjoint_instantiated` demands `uniformInverseChart`-facts, not `Wg`-facts;
       • one cannot CONVERT the `Wg`-facts to `uniformInverseChart`-facts: `hVmapMeas` asks for GLOBAL
         (all-`z`, a.e.) measurability of `uniformInverseChart`, whereas the on-gate agreement
         `Wg z =ᶠ uniformInverseChart z` (`B2MeasurabilityDissolution.wg_eventuallyEq_chart_onGate`)
         holds ONLY on-gate (`z ∈ K`, `x ∈ S z`).  Off-gate the raw chart is `.choose`-junk whose
         measurability is unprovable — the very artefact `Wg` was built to route around.
     NAMED RESIDUE / the fix: a chart-PARAMETRIC `hjoint_instantiated` (a `SliceInterfaceInstantiation`
     refactor taking the chart as a parameter and using only its globally-measurable representative on
     the gate), plus the analogous refactor of `HenvUInstantiation` / `WitnessDerivMeasurability`.  That
     edits/duplicates existing files and is OUT OF SCOPE for a new-file brick.  Sound (the witness is
     chart-invariant as a function), but deferred.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (N1) WHAT THIS FILE LANDS.
    • `CConvChartGateDataW` — the chart-parametric variant of `CConvFacade.CConvChartGateData`: identical
      to the original EXCEPT the four chart-mentioning fields (`hVmapMeas`, `hCover`-C², `hChartB`,
      `hSliceData`-`radialCutoff`) take an opaque chart parameter `W' : Point n → Point n → Point n` in
      place of the hardwired `uniformInverseChart g gi hC hK z`.  The three chart-free fields
      (`hKmeasSet`, `hSmeasSet` about the gate `S`, `hKmeas` about `witnessFieldDeriv`) and the fixed
      witness-side object `innerKernelField g gi hC hK` are kept VERBATIM.
    • `chartGateDataW_of_Wg` — the instantiation at `W' := B2MeasurabilityDissolution.Wg Γ G`.  WALLS
      2/3 are DISCHARGED INTERNALLY from the banked joint measurability (`hΓ : MeasurableSet Γ`,
      `hG : Measurable G`) via `wg_vmap_aemeasurable` / `wg_chartB_measurable`; `hKmeasSet` is ND
      (`hK.measurableSet`).  Wall 1 (`hSmeasSet`, the raw gate `z`-slice — its K-restricted form does
      NOT match the raw field shape) and `hCover` / `hSliceData` / `hKmeas` are the honest carries
      (each satisfiable: `hCover`-C² at `Wg` from `wg_contDiffAt_onGate`, `hSliceData` frontier leg from
      `radialCutoff_zero_on_frontier_collar`, `hKmeas` from `hKmeas_concrete_v7`).

  ## (N2) THE RE-THREADED CONSUMER — statement + named block (NOT proved, per N0's BLOCKED verdict).
    Intended:  `hCConv_from_dataW (…) (chartW : CConvChartGateDataW g gi hC hK S a b t u (Wg Γ G))
                 (source) (deriv) (env) (hD1) :
                 ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness …) (leviSeries …) t p 0) 0`.
    BLOCKING STEP: `SliceInterfaceInstantiation.hjoint_instantiated` (and `HenvUInstantiation`'s
    `henv_assembled`/`hdomS_assembled`, `WitnessDerivMeasurability.g2_bundle_assembled`) hardwire
    `uniformInverseChart`; they do not accept a `W'`-parametrized bundle.  The fix is the
    chart-parametric refactor of those files (N0 residue).  NO sorry stub is written for this.

  ## (N3) THE RE-THREADED CAPSTONE SLOT — likewise statement-only.
    Intended:  `hCConvSlot_AT_GATE_v2` = `CConvFacadeGate.hCConvSlot_AT_GATE` with the `chart` binder
    replaced by `chartW : CConvChartGateDataW … (Wg Γ G)` + `(Γ, G, hΓ, hG)`, discharging B2 walls 2/3
    internally.  Depends on `hCConv_from_dataW` (N2), hence BLOCKED on the same residue.

  ## UPDATED hCConv WALL COUNT (B2 tranche, at the `Wg` chart-parametric bundle).
    Of the original 9 hCConv walls, the B2 cluster now reads at `CConvChartGateDataW … (Wg Γ G)`:
      • `hVmapMeas`, `hChartB` (walls 2/3): INTERNAL — discharged inside `chartGateDataW_of_Wg` from
        `MeasurableSet Γ` + `Measurable G` (banked `flowInverse_jointMeasurable_regional`).  NO LONGER
        bundle carries.
      • `hSmeasSet` (wall 1): honest carry (raw gate `z`-slice; K-restricted piece proved in J4-320).
      • `hSliceData` (wall 4): honest carry (frontier-collar leg proved; far-region + inner-field cont.
        residues).
      • `hCover`, `hKmeas`: honest carries with banked builders (`wg_contDiffAt_onGate` /
        `hKmeas_concrete_v7`).
    Remaining hCConv W-surface after this brick: `hSmeasSet`, `hSliceData` (B2 carries); `hFbd` (B3);
    `hlin`, `hDrep` (B4); `hGateData`, `hGateData'` (B5) — PLUS the N0 named residue (the chart-parametric
    `hjoint_instantiated`/envelope refactor) blocking N2/N3.
  ⚠  STILL NOT `a₁ = R/6`; every carried hypothesis is an honest satisfiable input.
-/
import QIQTH.B2MeasurabilityDissolution
import QIQTH.CConvFacade

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.OnGateFieldRegularity
open QIQTH.B2MeasurabilityDissolution
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.ChartParamFacadeVariant

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (N1) — `CConvChartGateDataW`: the chart-parametric variant of `CConvChartGateData`.
    ############################################################################### -/

/-- **★★ (N1) `CConvChartGateDataW` — the chart-PARAMETRIC variant of
    `CConvFacade.CConvChartGateData`.**  Identical to the original bundle EXCEPT the four
    chart-mentioning fields take an opaque chart parameter `W' : Point n → Point n → Point n` where the
    original hardwired `uniformInverseChart g gi hC hK z`:
      • `hVmapMeas`  : `AEMeasurable (fun z => W' z (update x i w)) volume`;
      • `hCover`     : the `ContDiffAt ℝ 2 (W' z) x` regularity leg (membership/openness of `S` unchanged);
      • `hChartB`    : `Measurable (fun p => W' p.2 (update x i w))`;
      • `hSliceData` : the off-gate cutoff-vanishing `radialCutoff a b (W' p.2 q) = 0`.
    The three chart-FREE fields (`hKmeasSet`; `hSmeasSet` about the gate `S`; `hKmeas` about
    `witnessFieldDeriv`) and the FIXED witness-side object `innerKernelField g gi hC hK` (which bakes in
    the true chart) are copied VERBATIM.  This is the data-structure half of the J4-320 facade refactor.
    ⚠ NOT `a₁ = R/6`. -/
structure CConvChartGateDataW (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n))
    (W' : Point n → Point n → Point n) : Prop where
  hKmeasSet : MeasurableSet K
  hSmeasSet : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      MeasurableSet {z : Point n | (Function.update x i w) ∈ S z}
  hVmapMeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      AEMeasurable (fun z : Point n => W' z (Function.update x i w))
        (volume : Measure (Point n))
  hCover : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ z ∂(volume : Measure (Point n)),
        z ∈ K → (x ∈ S z ∧ IsOpen (S z)
            ∧ ContDiffAt ℝ 2 (W' z) x)
  hChartB : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      Measurable (fun p : ℝ × Point n => W' p.2 (Function.update x i w))
  hSliceData : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
      (p.2 ∉ K)
      ∨ (p.2 ∈ K
          ∧ (∀ q, q ∉ S p.2 → radialCutoff a b (W' p.2 q) = 0)
          ∧ Continuous
              (fun w : ℝ =>
                innerKernelField g gi hC hK a b (t - p.1) p.2 (Function.update x i w)))
  hKmeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z)
          (volume : Measure (Point n))

/-- **★★★ (N1) `chartGateDataW_of_Wg` — the `Wg` instantiation with B2 walls 2/3 INTERNAL.**  Builds
    `CConvChartGateDataW g gi hC hK S a b t u (Wg Γ G)` — the chart-parametric variant at the piecewise
    chart `Wg Γ G` of `B2MeasurabilityDissolution` — with the two off-image chart-inverse measurability
    walls DISCHARGED internally:
      • `hVmapMeas` from `wg_vmap_aemeasurable` (needs only `MeasurableSet Γ` + `Measurable G`);
      • `hChartB`   from `wg_chartB_measurable` (same data);
    and `hKmeasSet` ND from `hK.measurableSet`.  The remaining fields are the honest satisfiable
    carries: `hSmeasSet` (the raw gate `z`-slice — wall 1, whose K-restricted piece J4-320 proved),
    `hCover` (its C² leg dischargeable at `Wg` via `wg_contDiffAt_onGate`), `hSliceData` (frontier-collar
    leg via `radialCutoff_zero_on_frontier_collar`), and `hKmeas` (via `hKmeas_concrete_v7`).  Each carry
    is a bundle field at `Wg Γ G` — never the conclusion, never vacuous.  ⚠ NOT `a₁ = R/6`. -/
theorem chartGateDataW_of_Wg (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n))
    (Γ : Set (Point n × Point n)) (G : Point n × Point n → Point n)
    (hΓ : MeasurableSet Γ) (hG : Measurable G)
    (hSmeasSet : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | (Function.update x i w) ∈ S z})
    (hCover : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → (x ∈ S z ∧ IsOpen (S z)
              ∧ ContDiffAt ℝ 2 (Wg Γ G z) x))
    (hSliceData : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
        (p.2 ∉ K)
        ∨ (p.2 ∈ K
            ∧ (∀ q, q ∉ S p.2 → radialCutoff a b (Wg Γ G p.2 q) = 0)
            ∧ Continuous
                (fun w : ℝ =>
                  innerKernelField g gi hC hK a b (t - p.1) p.2 (Function.update x i w))))
    (hKmeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀,
          AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z)
            (volume : Measure (Point n))) :
    CConvChartGateDataW g gi hC hK S a b t u (Wg Γ G) := by
  refine
    { hKmeasSet := hK.measurableSet
      hSmeasSet := hSmeasSet
      hVmapMeas := ?_
      hCover := hCover
      hChartB := ?_
      hSliceData := hSliceData
      hKmeas := hKmeas }
  · intro x₀ _hx₀ i
    refine Filter.Eventually.of_forall (fun x => ?_)
    intro w
    exact wg_vmap_aemeasurable Γ G hΓ hG (Function.update x i w)
  · intro x₀ _hx₀ i
    refine Filter.Eventually.of_forall (fun x => ?_)
    intro w
    exact wg_chartB_measurable Γ G hΓ hG (Function.update x i w)

end QIQTH.ChartParamFacadeVariant

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ChartParamFacadeVariant
#print axioms chartGateDataW_of_Wg
end AxiomChecks
