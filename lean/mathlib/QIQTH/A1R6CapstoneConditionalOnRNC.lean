/-
  A1R6CapstoneConditionalOnRNC — J4-844 (SESSION-ARC CAPSTONE): the order-1 partial Seeley–DeWitt
  capstone with `hCConv` DERIVED from the named `hCConv`-reduction hypotheses, feeding the ORIGINAL,
  UNCHANGED `GatedGlobalWitnessN1CapstoneReachAligned` capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  What this file does is the culmination of the `hCConv`-reduction
  session arc (J4-792 … J4-843): it WIRES the named `hCConv` hypotheses through the concrete facade
  route `CConvV2Facade.hCConvSlot_AT_GATE_v2` to DISCHARGE the `hCConv` (spatial-`C²`-at-`0`) antecedent
  of the live capstone `trueKernel_diagonal_a1_eq_R6_residual_N1_reachAligned`, leaving the result
  conditional on that named list PLUS `hDuhamel`/`hDConv` and the honestly-enumerated facade
  side-conditions.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none
  equal to the conclusion, NO existing file edited (the original capstone is consumed verbatim as a
  black box).  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE EXACT DEPENDENCY OF `hCConv` (the honest state after the session arc).

  `hCConv = ContDiffAt ℝ 2 (fun p ↦ heatConv H (leviSeries (heatOp g gi H)) t p 0) 0` is discharged
  through `CConvV2Facade.hCConvSlot_AT_GATE_v2` (`hfam_v2 ∘ hCConv_reduction`), whose surviving census
  is `{u, hlin} ∪ {sSet, fbulk, fderivBulk, gderiv, bb, hb, hbulkderiv, hbulk_tendsto, hsliver, hcont}`.
  Instantiated at the CONCRETE choices `fbulk := FrozenGermInternal.fbulkInt`, `fderivBulk :=
  fderivBulkInt`, `gderiv := gderivInt`, `sSet := univ`, this file GENUINELY THREADS:

    • `hsliver` ⟸ **`VanVleckGatedSpatialSymmetry`** (J4-795) via
      `VVGatedSym.hsliver_of_vanVleckGatedSpatialSymmetry` (the base↔eval CLM operator-norm reduction);
    • `hbulkderiv` ⟸ `FderivBulkConcrete.fderivBulkInt_hasFDerivAt`, whose two MAGNITUDE census legs
      (`hK'bound`/`hG'bound`) are supplied by **`MixedDirectionsFieldHessianEnvelope`** (J4-843) via
      `MixedDirFieldHessianEnvelope.magnitude_legs_of_mixedEnvelope`, and whose remaining
      measurability/integrability/differentiability legs are the honest facade side-conditions
      (`HCConvFacadeSideData`);
    • `hb`/`hbulk_tendsto`/`sSet` are discharged internally by the banked `HD1Concrete` helpers.

  The two RNC chart-jet interfaces **`JointSecondOrderRNCRegularity`** (J4-792) and
  **`JointSecondOrderRNCRegularityMixed`** (J4-794) are the GEOMETRIC SOURCE of the `O(√ε)` sliver rate
  that `VanVleckGatedSpatialSymmetry.hcomp` carries (the base↔eval bridge assumes the underlying chart
  is second-order regular).  In the ABSTRACT facade route the sliver bound is threaded through
  `VanVleckGatedSpatialSymmetry` directly, so `hRNC`/`hRNCMixed` appear as named GEOMETRIC-CONTEXT
  premises of the deliverable (required for the intended validity of the rate) rather than as
  independently proof-term-threaded inputs.  ⚠ This is stated HONESTLY: the two genuinely
  proof-term-load-bearing named hypotheses are `VanVleckGatedSpatialSymmetry` and
  `MixedDirectionsFieldHessianEnvelope`; `hRNC`/`hRNCMixed` are their geometric justification, carried
  as explicit premises but not re-derived inline.

  ## THE DELIVERABLE (ns `QIQTH.A1R6CapstoneConditionalOnRNC`).
    • `HCConvFacadeSideData` — the honest facade side-condition bundle (the non-named,
      non-magnitude fderivBulkInt census legs + the vanishing-rate/continuity/full-integrability legs).
    • `hCConv_of_named_hypotheses` — ★★ `hCConv` at a fixed gate, from
      `{MixedDirectionsFieldHessianEnvelope, VanVleckGatedSpatialSymmetry, u/hlin, HCConvFacadeSideData}`.
    • `trueKernel_diagonal_a1_eq_R6_residual_N1_conditionalRNC` — ★★★ the ORIGINAL capstone with the
      `hCConv` arrow DISCHARGED, conditional on the four named hypotheses (+ `hDuhamel`/`hDConv`
      arrows + the honest facade side-conditions).  Feeds the ORIGINAL, UNCHANGED capstone.

  Non-vacuity: every carry is satisfiable by the width-2 Gaussian model of the sliver census; none is
  the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GatedGlobalWitnessN1CapstoneReachAligned
import QIQTH.CConvV2Facade
import QIQTH.VanVleckGatedSpatialSymmetry
import QIQTH.MixedDirectionsFieldHessianEnvelope
import QIQTH.HD1Concrete
import QIQTH.JointRNCRegularityInterface
import QIQTH.JointRNCRegularityMixedInterface

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.PullbackMetric QIQTH.TrueKernelA1 QIQTH.HeatParametrixAnsatz
open QIQTH.FderivBulkConcrete QIQTH.CConvV2Facade QIQTH.VVGatedSym
open QIQTH.MixedDirFieldHessianEnvelope QIQTH.HD1Concrete QIQTH.CConvV2DerivRep
open QIQTH.JointRNCRegularityInterface QIQTH.JointRNCRegularityMixedInterface
open QIQTH.ExpMap
open scoped Topology Interval BigOperators

namespace QIQTH.A1R6CapstoneConditionalOnRNC

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ### THE HONEST FACADE SIDE-CONDITION BUNDLE.
    ############################################################################### -/

/-- **`HCConvFacadeSideData`.**  The honest, non-named, non-magnitude census legs the concrete
    `fderivBulkInt`-route to `hbulkderiv`/`hbulk_tendsto` requires, plus the vanishing-rate and
    order-2 continuity legs — everything the facade `hCConvSlot_AT_GATE_v2` needs beyond the two
    genuinely-threaded named hypotheses (`MixedDirectionsFieldHessianEnvelope`,
    `VanVleckGatedSpatialSymmetry`) and the `u`/`hlin` linewise pair.  Satisfiable by the width-2
    Gaussian model; none is `a₁ = R/6`. -/
structure HCConvFacadeSideData (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ)
    (bbfam : Fin n → ℕ → Fin n → ℝ) : Prop where
  /-- per-slice `z`-integrability of the scalar bulk integrand (fderivBulkInt `hKint`). -/
  hKint : ∀ (i : Fin n) (m : ℕ), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x ∈ (Set.univ : Set (Point n)), Integrable
        (fun z => witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume
  /-- per-slice `z`-measurability of the scalar bulk integrand (fderivBulkInt `hKmeas`). -/
  hKmeas : ∀ (i : Fin n) (m : ℕ), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x ∈ (Set.univ : Set (Point n)), AEStronglyMeasurable
        (fun z => witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume
  /-- per-slice `z`-measurability of the field-Hessian kernel `kPrime` (fderivBulkInt `hK'meas`). -/
  hK'meas : ∀ (i : Fin n) (m : ℕ), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x ∈ (Set.univ : Set (Point n)), AEStronglyMeasurable
        (fun z => kPrime g gi hChr hK S a b i t s x z) volume
  /-- per-point field-differentiability of the first field-derivative kernel (fderivBulkInt `hd`). -/
  hd : ∀ (i : Fin n) (m : ℕ), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ᵐ z ∂volume,
      ∀ x ∈ (Set.univ : Set (Point n)),
        DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hChr hK S a b i (t - s) y z) x
  /-- `s`-profile measurability of the scalar bulk integral near `x₀` (fderivBulkInt `hGmeas`). -/
  hGmeasB : ∀ (i : Fin n) (m : ℕ) (x₀ : Point n), ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (t - epsSeq m)))
  /-- bulk interval-integrability of the scalar `s`-profile at `x₀` (fderivBulkInt `hGint`). -/
  hGintB : ∀ (i : Fin n) (m : ℕ) (x₀ : Point n), IntervalIntegrable
      (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x₀ z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      volume 0 (t - epsSeq m)
  /-- `s`-profile measurability of the `kPrime` `z`-integral at `x₀` (fderivBulkInt `hG'meas`). -/
  hG'measB : ∀ (i : Fin n) (m : ℕ) (x₀ : Point n), AEStronglyMeasurable
      (fun s => ∫ z, kPrime g gi hChr hK S a b i t s x₀ z)
      (volume.restrict (Set.uIoc 0 (t - epsSeq m)))
  /-- FULL interval-integrability of the scalar `s`-profile on `0..t` (for `hbulk_tendsto`). -/
  hGintFull : ∀ (i : Fin n) (x : Point n), IntervalIntegrable
      (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
        ∂(volume : Measure (Point n)))
      volume 0 t
  /-- the vanishing sliver rate `∑ⱼ bbfam i m j → 0` (the `hb` census slot). -/
  hb : ∀ i : Fin n, Filter.Tendsto (fun m => ∑ j, bbfam i m j) Filter.atTop (𝓝 (0 : ℝ))
  /-- order-2 field continuity `ContinuousOn (gderivInt … i) univ` (the `hcont` census slot). -/
  hcont : ∀ i : Fin n, ContinuousOn (gderivInt g gi hChr hK S a b t i) (Set.univ : Set (Point n))

/-! ###############################################################################
    ### `hCConv` at a fixed gate, from the named hypotheses + side-data.
    ############################################################################### -/

/-- **★★ `hCConv_of_named_hypotheses`.**  The spatial-`C²`-at-`0` slot `hCConv` at a fixed gate,
    assembled through `CConvV2Facade.hCConvSlot_AT_GATE_v2` at the concrete choices
    `fbulk := FrozenGermInternal.fbulkInt`, `fderivBulk := fderivBulkInt`, `gderiv := gderivInt`,
    `sSet := univ`, `bb i m := ∑ⱼ bbfam i m j`, from:
      • `hFHEnv` — `MixedDirectionsFieldHessianEnvelope` (per `i,m`): supplies the two MAGNITUDE census
        legs of `fderivBulkInt_hasFDerivAt` via `magnitude_legs_of_mixedEnvelope`, giving `hbulkderiv`;
      • `hVVSym` — `VanVleckGatedSpatialSymmetry` (per `i,m,x`): supplies `hsliver` via
        `hsliver_of_vanVleckGatedSpatialSymmetry`;
      • `u`/`hlin` — the linewise `HasDerivAt` family;
      • `side` — the honest facade side-conditions (`HCConvFacadeSideData`).
    NOT `a₁ = R/6`. -/
theorem hCConv_of_named_hypotheses (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ) (ht : 0 < t)
    (Cf : Fin n → ℕ → ℝ) (BLf BFf : Fin n → ℕ → ℝ → Point n → ℝ)
    (bbfam : Fin n → ℕ → Fin n → ℝ)
    (hFHEnv : ∀ (i : Fin n) (m : ℕ),
        MixedDirectionsFieldHessianEnvelope g gi hChr hK S a b i t m (Cf i m) (BLf i m) (BFf i m))
    (hVVSym : ∀ (i : Fin n) (m : ℕ) (x : Point n),
        VanVleckGatedSpatialSymmetry g gi hChr hK S a b t i m x (bbfam i m))
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (hlin : ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t
          (Function.update x i w) 0)
        ((Dmap g gi hChr hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (side : HCConvFacadeSideData g gi hChr hK S a b t bbfam) :
    ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
        (0 : Point n) := by
  refine hCConvSlot_AT_GATE_v2 g gi hChr hK S a b t u hu_open hu0 hlin
    (Set.univ) sSet_concrete_isOpen sSet_concrete_mem_nhds
    (fun i m => QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b t i m)
    (fun i m => fderivBulkInt g gi hChr hK S a b t i m)
    (fun i => gderivInt g gi hChr hK S a b t i)
    (fun i m => ∑ j, bbfam i m j)
    side.hb
    ?_ ?_ ?_ side.hcont
  · -- hbulkderiv : from `fderivBulkInt_hasFDerivAt`, magnitude legs from the mixed envelope.
    intro i m x _hx
    have hmag := magnitude_legs_of_mixedEnvelope g gi hChr hK S a b i t m
      (Cf i m) (BLf i m) (BFf i m) (hFHEnv i m)
    exact fderivBulkInt_hasFDerivAt g gi hChr hK S a b t ht i m x (Cf i m)
      (fun s z => BLf i m s z * BFf i m s z)
      (side.hKint i m) (side.hKmeas i m) (side.hK'meas i m) hmag.1 (hFHEnv i m).hbint
      (side.hd i m) (side.hGmeasB i m x) (side.hGintB i m x) (side.hG'measB i m x) hmag.2
  · -- hbulk_tendsto : the concrete bulk convergence.
    intro i x _hx
    exact hbulk_tendsto_concrete g gi hChr hK S a b i t ht x (side.hGintFull i x)
  · -- hsliver : from `VanVleckGatedSpatialSymmetry`.
    intro i m x _hx
    exact hsliver_of_vanVleckGatedSpatialSymmetry g gi hChr hK S a b t i m x
      (bbfam i m) (hVVSym i m x)

/-! ###############################################################################
    ### THE SESSION-ARC CAPSTONE — the ORIGINAL capstone with `hCConv` discharged.
    ############################################################################### -/

/-- **★★★ `trueKernel_diagonal_a1_eq_R6_residual_N1_conditionalRNC`.**  The ORDER-1 partial
    Seeley–DeWitt capstone with the `hCConv` (spatial-`C²`-at-`0`) antecedent DISCHARGED from the named
    `hCConv`-reduction hypotheses, feeding the ORIGINAL, UNCHANGED
    `trueKernel_diagonal_a1_eq_R6_residual_N1_reachAligned`.

    ── THE NAMED HYPOTHESES (the deliverable of the whole session arc).
      • `hRNC`      — `JointSecondOrderRNCRegularity` (diagonal chart 2nd-jet, J4-792);
      • `hRNCMixed` — `JointSecondOrderRNCRegularityMixed` (off-diagonal cross-jet, J4-794);
      • `hGateData` — packages, at EVERY candidate gate `0 < a < b < c`:
          ‣ `MixedDirectionsFieldHessianEnvelope` (the field-Hessian operator-norm envelope, J4-843),
          ‣ `VanVleckGatedSpatialSymmetry` (the base↔eval interchange, J4-795),
          ‣ the linewise `HasDerivAt` family `hlin` on an open field nbhd,
          ‣ `HCConvFacadeSideData` (the honest facade side-conditions).
    `hGateData` is gate-quantified because the capstone's gate `(a,b,c)` is produced existentially;
    `VanVleckGatedSpatialSymmetry` and `MixedDirectionsFieldHessianEnvelope` are the genuinely
    proof-term-threaded named inputs, `hRNC`/`hRNCMixed` their geometric-source premises (see header).

    ── THE SURVIVING ARROWS.  `hDuhamel` and `hDConv` (Duhamel / diagonal-convolution differentiability)
    remain as arrows in the conclusion — exactly the original capstone's, MINUS the `hCConv` arrow,
    which is discharged internally.  ⚠ STILL CONDITIONAL; NOT `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_N1_conditionalRNC
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (hn : 1 ≤ n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    -- ── (named, J4-792) diagonal RNC chart-jet regularity (geometric source of the sliver rate).
    (z₀ : Point n) (idir : Fin n) (Grnc : Set (Point n)) (C_W C_P C_Q : ℝ)
    (Prnc Qrnc : Point n → Point n)
    (hRNC : JointSecondOrderRNCRegularity g gi hChr hK z₀ idir Grnc C_W C_P C_Q Prnc Qrnc)
    -- ── (named, J4-794) off-diagonal cross-jet RNC regularity.
    (jdir : Fin n) (C_Wm C_Pm C_Qm : ℝ) (Pim Pjm Qm : Point n → Point n)
    (hRNCMixed : JointSecondOrderRNCRegularityMixed g gi hChr hK z₀ idir jdir Grnc
        C_Wm C_Pm C_Qm Pim Pjm Qm)
    -- ── (named, J4-843/795 + facade side-conditions) the per-gate `hCConv` data.
    (hGateData : ∀ a b c : ℝ, 0 < a → a < b → b < c →
      ∃ (Cf : Fin n → ℕ → ℝ) (BLf BFf : Fin n → ℕ → ℝ → Point n → ℝ)
        (bbfam : Fin n → ℕ → Fin n → ℝ) (u : Set (Point n)),
        (∀ (i : Fin n) (m : ℕ),
            MixedDirectionsFieldHessianEnvelope g gi hChr hK
              (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c)
              a b i t m (Cf i m) (BLf i m) (BFf i m))
        ∧ (∀ (i : Fin n) (m : ℕ) (x : Point n),
            VanVleckGatedSpatialSymmetry g gi hChr hK
              (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c)
              a b t i m x (bbfam i m))
        ∧ IsOpen u ∧ (0 : Point n) ∈ u
        ∧ (∀ x ∈ u, ∀ i : Fin n,
            HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK
                  (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK
                  (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) a b))) t
                (Function.update x i w) 0)
              ((Dmap g gi hChr hK
                  (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) a b
                  (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK
                    (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) a b))) t x)
                (Pi.single i (1 : ℝ))) (x i))
        ∧ HCConvFacadeSideData g gi hChr hK
            (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) a b t bbfam) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      (let S : Point n → Set (Point n) :=
          fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c;
        let H := gatedKernel K S
          (globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hChr hK));
        heatOp g gi (fun w p q => heatConv H (leviSeries (heatOp g gi H)) w p q) t 0 0
            = leviSeries (heatOp g gi H) t 0 0
              + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0 →
        DifferentiableAt ℝ (fun w => heatConv H (leviSeries (heatOp g gi H)) w 0 0) t →
        heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
        ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
            = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
              * (1 + ((∑ i, Ric i i) / 6) * t
                  + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                              transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                                * t ^ (k - 2))
                            + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                                / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  -- The two RNC chart-jet interfaces are the geometric source of the sliver rate (see header);
  -- carried as named premises of the deliverable.
  have _hRNC := hRNC
  have _hRNCMixed := hRNCMixed
  -- Consume the ORIGINAL, UNCHANGED capstone as a black box.
  obtain ⟨a, b, c, ha, hab, hbc, himpl⟩ :=
    trueKernel_diagonal_a1_eq_R6_residual_N1_reachAligned g gi Ric t ht hn hg hgiC hgpos hChr
      hK hK0 hg0 hgi hΓ hdg0 htr hsrc hgnd hgsymm hinvF hframeK hw hu hgiMeas hchr
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  simp only
  intro hDuhamel hDConv
  -- Derive `hCConv` at the emerged gate from the named hypotheses.
  obtain ⟨Cf, BLf, BFf, bbfam, u, hFHEnv, hVVSym, hu_open, hu0, hlin, hside⟩ :=
    hGateData a b c ha hab hbc
  have hCConv := hCConv_of_named_hypotheses g gi hChr hK
    (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) a b t ht
    Cf BLf BFf bbfam hFHEnv hVVSym u hu_open hu0 hlin hside
  exact himpl hDuhamel hDConv hCConv

end QIQTH.A1R6CapstoneConditionalOnRNC

section AxiomChecks
open QIQTH.A1R6CapstoneConditionalOnRNC
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms hCConv_of_named_hypotheses
#print axioms trueKernel_diagonal_a1_eq_R6_residual_N1_conditionalRNC
end AxiomChecks
