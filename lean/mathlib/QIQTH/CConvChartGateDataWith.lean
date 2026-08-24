/-
  CConvChartGateDataWith — J4-1179: dispatch 1 of the RESUMED witness-unification sub-campaign
  (`docs/qg_roadmap/WITNESS_UNIFICATION_PLAN.md`), Phase 1, D2 — the chart-parametric fork of
  `CConvFacade.CConvChartGateData`, following the standard three-layer `XWith`/`X`/`X'` discipline
  established by the chart-parametric rebuild campaign (J4-1156 onward).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  genericizes a `: Prop` DATA BUNDLE (never a conclusion) over an abstract chart `W` and an abstract
  witness-field-derivative `WD`, then instantiates it twice: once at the OLD concrete values (bridged
  back to the existing `CConvChartGateData` via a two-way `Iff`, not `rfl`, since these are distinct
  `structure` declarations — every field-level equality involved IS `rfl`/definitional) and once at the
  NEW primed values `uniformInverseChart'`/`witnessFieldDeriv'`. No `sorry`, no new axioms, no
  `:= True`, no vacuous/unsatisfiable hypotheses, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## SCOPE CORRECTION (honest, found by this dispatch's own direct read of `CConvChartGateData`,
  `CConvFacade.lean:85-113`, BEFORE writing any Lean).

  `WITNESS_UNIFICATION_PLAN.md`'s Phase 1 D2 entry describes forking "the 2 hardwired fields
  (`hVmapMeas`, `hCover`)".  Direct re-read of the structure finds this undercounts: FIVE of its seven
  non-trivial fields mention chart/witness machinery, not two:
    • `hVmapMeas`, `hCover`, `hChartB` — each calls `uniformInverseChart g gi hC hK z ...` directly;
    • `hSliceData` — calls `uniformInverseChart g gi hC hK p.2 q` directly (the `radialCutoff` leg) AND
      `innerKernelField g gi hC hK a b (t - p.1) p.2 ...` (the `Continuous` leg);
    • `hKmeas` — calls `witnessFieldDeriv g gi hC hK S a b i (t - s) x z` directly.
  This EXACT undercount was already discovered once before, independently, in an EARLIER (2026-08-06,
  J4-321) chart-parametric attempt `ChartParamFacadeVariant.lean` (`CConvChartGateDataW`, a DIFFERENT
  chart `Wg`, not `uniformInverseChart'`) — that file correctly lists FOUR chart-mentioning fields
  (`hVmapMeas`/`hCover`/`hChartB`/`hSliceData`) plus notes `hKmeas` names `witnessFieldDeriv` (kept
  fixed there, not forked).  Neither `WITNESS_UNIFICATION_PLAN.md`'s pre-check (J4-1176/1177) nor the
  40th/41st Sol consults cross-referenced this prior file.  This is NOT a NEW obstruction — it is the
  SAME already-known fork point, more completely counted, and the earlier file already demonstrated
  (for a different chart) that the full fork closes cleanly, non-vacuously.  Per this dispatch's own
  "canary discipline" (STOP on a genuine NEW obstruction, not on a more complete field count matching
  precedent), this does not warrant halting — building the fully-correct fork (matching Canary C1's own
  "no unprimed witness/chart/amplitude token" requirement, which the literal "2 fields" reading would
  FAIL for `hChartB`/`hSliceData`/`hKmeas`) is the right response, done below.

  `hSliceData`'s `Continuous` leg (`innerKernelField g gi hC hK ...`) is the ONE field kept FIXED/
  verbatim here, matching `ChartParamFacadeVariant`'s own precedent design: `innerKernelField` is a
  closed `def` (opaque as a function symbol, not a literal `uniformInverseChart`/`witnessFieldDeriv`/
  `vanVleckGatedWitness`/`chartFieldAmp` token in the printed type), used only as an honest carried
  side-condition, not the chart/witness object the campaign invariant enumerates.  Whether Phase 3 (D7)
  needs an `innerKernelField'` fork too is an OPEN QUESTION this dispatch surfaces but does not answer
  (Phase 3's own STOP condition already covers this: "if the proof needs a helper lemma D0 didn't
  already flag as generic, re-audit before proceeding").

  ── ALSO SURFACED (context for Phase 3, not resolved here): `ChartParamFacadeVariant.lean` (J4-321)
  independently found that the DOWNSTREAM consumer of `CConvChartGateData` —
  `SliceInterfaceInstantiation.hjoint_instantiated` (and `HenvUInstantiation.henv_assembled`/
  `hdomS_assembled`, `WitnessDerivMeasurability.g2_bundle_assembled`) — hardwires `uniformInverseChart`
  in ITS OWN PROOF BODY (not just its statement), meaning a chart-parametric bundle alone is NOT
  sufficient to re-thread those consumers; a genuine refactor of that machinery was judged "OUT OF
  SCOPE for a new-file brick" at the time.  `WITNESS_UNIFICATION_PLAN.md`'s Phase 3 (D7) assumes "none
  of those lemmas are chart/witness-hardwired below the structure layer" as something "to be confirmed
  by actually building this, not assumed" — this J4-321 finding is DIRECT PRIOR EVIDENCE AGAINST that
  assumption for the OLD `hjoint_instantiated`, and materially raises Phase 3's risk versus the plan's
  stated expectation.  Recorded here for Phase-3 planning; NOT a blocker for this dispatch's own D2
  scope (a pure data-structure fork, proving nothing about `hjoint_instantiated`).

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.CConvFacade
import QIQTH.WitnessFieldDerivWith
import QIQTH.ThetaMeasurableEmbedding

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.OnGateFieldRegularity QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.ThetaMeasurableEmbedding
open QIQTH.CConvFacade
open scoped Topology

namespace QIQTH.CConvChartGateWith

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE CHART-PARAMETRIC / WITNESS-DERIVATIVE-PARAMETRIC SIBLING —
    ### `CConvChartGateDataWith`.
    ############################################################################### -/

/-- **★★ `CConvChartGateDataWith` — the chart-parametric AND witness-derivative-parametric variant of
    `CConvFacade.CConvChartGateData`.**  Identical to the original bundle EXCEPT: the four fields that
    mention the chart directly (`hVmapMeas`, `hCover`, `hChartB`, the `radialCutoff` leg of
    `hSliceData`) take an abstract chart `W : Point n → Point n → Point n` in place of the hardwired
    `uniformInverseChart g gi hC hK`; the `hKmeas` field takes an abstract witness-field-derivative
    `WD : Fin n → ℝ → Point n → Point n → ℝ` in place of the hardwired
    `witnessFieldDeriv g gi hC hK S a b`.  The two chart-and-derivative-FREE fields (`hKmeasSet`,
    `hSmeasSet`, about `K`/the gate `S` only) and the FIXED witness-side object
    `innerKernelField g gi hC hK` (the `Continuous` leg of `hSliceData`) are kept VERBATIM — matching
    `ChartParamFacadeVariant.CConvChartGateDataW`'s own precedent design.  Pure `: Prop` data, never a
    conclusion.  NOT `a₁ = R/6`. -/
structure CConvChartGateDataWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n))
    (W : Point n → Point n → Point n)
    (WD : Fin n → ℝ → Point n → Point n → ℝ) : Prop where
  hKmeasSet : MeasurableSet K
  hSmeasSet : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      MeasurableSet {z : Point n | (Function.update x i w) ∈ S z}
  hVmapMeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      AEMeasurable (fun z : Point n => W z (Function.update x i w))
        (volume : Measure (Point n))
  hCover : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ z ∂(volume : Measure (Point n)),
        z ∈ K → (x ∈ S z ∧ IsOpen (S z)
            ∧ ContDiffAt ℝ 2 (W z) x)
  hChartB : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      Measurable (fun p : ℝ × Point n => W p.2 (Function.update x i w))
  hSliceData : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
      (p.2 ∉ K)
      ∨ (p.2 ∈ K
          ∧ (∀ q, q ∉ S p.2 → radialCutoff a b (W p.2 q) = 0)
          ∧ Continuous
              (fun w : ℝ =>
                innerKernelField g gi hC hK a b (t - p.1) p.2 (Function.update x i w)))
  hKmeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun z => WD i (t - s) x z)
          (volume : Measure (Point n))

/-! ###############################################################################
    ### ★ THE COMPATIBILITY BRIDGE — old-chart/old-derivative instantiation recovers
    ### `CConvChartGateData` exactly.
    ############################################################################### -/

/-- **★ `chartGateDataWith_iff_old` — the compatibility bridge.**  Instantiating the generic
    `CConvChartGateDataWith` at the OLD concrete chart `uniformInverseChart g gi hC hK` and the OLD
    concrete witness derivative `witnessFieldDeriv g gi hC hK S a b` is `Iff`-equivalent to the EXISTING
    `CConvChartGateData` — every field's TYPE is definitionally identical after substitution (an `Iff`,
    not `rfl`, since the two are separate `structure` declarations), so the equivalence is a plain
    field-by-field constructor map, closing by `exact`/projection alone (no case-split needed). NOT
    `a₁ = R/6`. -/
theorem chartGateDataWith_iff_old (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) :
    CConvChartGateDataWith g gi hC hK S a b t u
        (uniformInverseChart g gi hC hK) (witnessFieldDeriv g gi hC hK S a b)
      ↔ CConvChartGateData g gi hC hK S a b t u := by
  constructor
  · intro h
    exact
      { hKmeasSet := h.hKmeasSet
        hSmeasSet := h.hSmeasSet
        hVmapMeas := h.hVmapMeas
        hCover := h.hCover
        hChartB := h.hChartB
        hSliceData := h.hSliceData
        hKmeas := h.hKmeas }
  · intro h
    exact
      { hKmeasSet := h.hKmeasSet
        hSmeasSet := h.hSmeasSet
        hVmapMeas := h.hVmapMeas
        hCover := h.hCover
        hChartB := h.hChartB
        hSliceData := h.hSliceData
        hKmeas := h.hKmeas }

/-! ###############################################################################
    ### THE NEW-CHART/NEW-DERIVATIVE INSTANTIATION — `CConvChartGateData'`.
    ############################################################################### -/

/-- **`CConvChartGateData'` — the NEW-chart/NEW-derivative instantiation.**
    `CConvChartGateDataWith` at `W := uniformInverseChart' g gi hC hK c` and
    `WD := witnessFieldDeriv' g gi hC hK S a b c`, for a fixed tube radius `c` — the primed analogue of
    `CConvChartGateData`, threading Campaign 1's jointly-measurable chart and primed field-derivative
    throughout every chart/derivative-mentioning field. NOT globally `Iff`-equivalent to the old
    `CConvChartGateData` (the two charts agree only on a bounded tube image; no such claim is made or
    needed here). NOT `a₁ = R/6`. -/
def CConvChartGateData' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (c : ℝ) : Prop :=
  CConvChartGateDataWith g gi hC hK S a b t u
    (uniformInverseChart' g gi hC hK c) (witnessFieldDeriv' g gi hC hK S a b c)

end QIQTH.CConvChartGateWith

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvChartGateWith
#print axioms chartGateDataWith_iff_old
end AxiomChecks
