/-
  KPrimeMeasurabilityScaffolding — J4-797: the MECHANICAL (measurability / z-integrability)
  legs of the `kPrime` census in `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` — the "R2′"
  residue named at cp702 (J4-796).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}; hCConv is NOT closed here.
  This brick supplies the MECHANICAL half of the R2′ residue — the measurability / z-integrability
  scaffolding around the second-field-derivative kernel `kPrime` — by MIRRORING, one order up, the
  already-banked first-derivative scaffolding `WitnessDerivMeasurability` (J4-162).  No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE BOUNDED-DEPENDENCY FINDING (why this is mechanical, not a fourth geometric wall).

  `kPrime … i t s x z = (leviSeries … s z 0) • (fderiv ℝ (fun y ↦ witnessFieldDeriv … i (t−s) y z) x)`
  (`FderivBulkConcrete.kPrime`).  Its measurability-in-`z` factors, via `AEStronglyMeasurable.smul`,
  into
    • measurability of the Levi factor `z ↦ leviSeries … s z 0` — banked-suppliable
      (`FixedGateSourceProviders.leviSource_zslice_aesm` / `leviSource_joint_aesm`), non-geometric;
    • measurability of the bare second-field-derivative kernel
      `z ↦ fderiv ℝ (fun y ↦ witnessFieldDeriv … i (t−s) y z) x`
      — carried here as an honest hypothesis, EXACTLY the second-order analog of the FIRST-order
      `WitnessDerivMeasurability.hzmeas_witness`'s carried bare-kernel family `hKmeas`
      (`∀ᶠ x, AEStronglyMeasurable (z ↦ witnessFieldDeriv … x z)`), which was itself NEVER derived
      from joint regularity — it is satisfiable from the gate/Gaussian/amplitude measurable-set-glued
      product structure, a POINTWISE-in-`z`/joint-in-`(s,z)` fact, NOT the chart's second jet.

  ⇒ The measurability / z-integrability scaffolding needs only per-`x` / per-`z` (and joint-in-`(s,z)`
    at fixed base `x₀`) bare-kernel facts.  It does NOT re-need joint `(x,z)` chart second-jet
    regularity.  The chart second jet is needed ONLY for the MAGNITUDE legs `hK'bound`
    (pointwise Gaussian envelope on the SECOND derivative) and `hG'bound` (the singular
    `‖∫z kPrime‖ ≤ C·(t−s)⁻¹` bound whose Hermite-cancellation content routes to
    `JointSecondOrderRNCRegularity`'s SECOND jet, cf. J4-792/794) — which are DELIBERATELY NOT
    supplied here; they remain the already-named geometric residue.

  ## THE DELIVERABLE (ns `QIQTH.KPrimeMeasurabilityScaffolding`).
    • `kPrime_aesm` — the pointwise `.smul` reducer: `AEStronglyMeasurable (z ↦ kPrime … x z)`
      from Levi z-measurability + bare second-derivative z-measurability.
    • `kPrime_joint_aesm` — the joint `(s,z)` `.smul` reducer at fixed base `x₀`.
    • `hK'meas_witness` — the EXACT `hK'meas` census shape (`∀ᵐ s → ∀ x ∈ univ, …`) from carried
      Levi / bare-derivative measurability families.
    • `hboundz_gaussian_int` — the EXACT `hboundz_int` census leg SUPPLIED OUTRIGHT for the honest
      order-2 Gaussian dominator `z ↦ C·G_{κ(t−s)}(z)` (`WitnessDerivDomination.envelope_integrable`);
      no `ε ≤ t` needed — every `s ∈ uIoc 0 (t−εₘ)` has `s < t`, so `κ(t−s) > 0`.
    • `hG'meas_witness` — the EXACT `hG'meas` census leg via `.integral_prod_right'` (mirrors
      `WitnessDerivMeasurability.hsmeas_witness`).
    • `kPrime_R2prime_mechanical` — ★★ the capstone conjunction of the three MECHANICAL R2′ legs
      (`hK'meas`, `hboundz_int`, `hG'meas`), exhibiting them all as reductions to {banked Levi
      measurability, honest bare second-derivative measurability, banked envelope integrability}.

  Every carry is satisfiable, non-vacuous (the width-2 Gaussian model of the sliver bricks satisfies
  the bare-kernel measurability census), and never equal to the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FderivBulkConcrete
import QIQTH.WitnessDerivDomination

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.FlatHeatEquation
open QIQTH.FderivBulkConcrete QIQTH.WitnessDerivDomination
open scoped Topology Interval BigOperators

namespace QIQTH.KPrimeMeasurabilityScaffolding

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### R1 — the pointwise / joint `.smul` reducers for `kPrime`.
    ############################################################################### -/

/-- **R1a — `kPrime_aesm`.**  Pointwise `z`-measurability of `kPrime … x z` from the Levi factor's
    `z`-measurability and the bare second-field-derivative kernel's `z`-measurability, via
    `AEStronglyMeasurable.smul` — `kPrime` is definitionally `leviSeries • fderiv`.  NOT `a₁ = R/6`. -/
theorem kPrime_aesm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t s : ℝ) (x : Point n)
    (hLevi : AEStronglyMeasurable
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      (volume : Measure (Point n)))
    (hFderiv : AEStronglyMeasurable
      (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
      (volume : Measure (Point n))) :
    AEStronglyMeasurable (fun z => kPrime g gi hC hK S a b i t s x z) (volume : Measure (Point n)) := by
  simp only [kPrime]
  exact hLevi.smul hFderiv

/-- **R1b — `kPrime_joint_aesm`.**  Joint `(s,z)`-measurability of `kPrime … x₀ ·` at fixed base
    `x₀`, on the restricted product `(volume.restrict (uIoc 0 (t−εₘ))).prod volume`, from the joint
    Levi and joint bare-derivative measurability, via `.smul`.  NOT `a₁ = R/6`. -/
theorem kPrime_joint_aesm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (x₀ : Point n)
    (hLeviJoint : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 (t - epsSeq m))).prod (volume : Measure (Point n))))
    (hFderivJoint : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - p.1) y p.2) x₀)
      ((volume.restrict (Set.uIoc 0 (t - epsSeq m))).prod (volume : Measure (Point n)))) :
    AEStronglyMeasurable
      (fun p : ℝ × Point n => kPrime g gi hC hK S a b i t p.1 x₀ p.2)
      ((volume.restrict (Set.uIoc 0 (t - epsSeq m))).prod (volume : Measure (Point n))) := by
  simp only [kPrime]
  exact hLeviJoint.smul hFderivJoint

/-! ###############################################################################
    ### R2 — `hK'meas`: the census-shaped inner `z`-ae-measurability of `kPrime`.
    ############################################################################### -/

/-- **R2 — `hK'meas_witness`.**  THE EXACT `hK'meas` census shape of
    `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` — `∀ᵐ s, s ∈ uIoc 0 (t−εₘ) → ∀ x ∈ univ,
    AEStronglyMeasurable (z ↦ kPrime … x z)` — reduced to carried Levi / bare-second-derivative
    `z`-measurability families via `kPrime_aesm`.  The bare-derivative family is the exact
    second-order analog of `WitnessDerivMeasurability`'s carried `hKmeas`.  NOT `a₁ = R/6`. -/
theorem hK'meas_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ)
    (hLeviFam : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        AEStronglyMeasurable
          (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n)))
    (hFderivFam : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ x : Point n,
        AEStronglyMeasurable
          (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
          (volume : Measure (Point n))) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x ∈ (Set.univ : Set (Point n)),
        AEStronglyMeasurable (fun z => kPrime g gi hC hK S a b i t s x z)
          (volume : Measure (Point n)) := by
  filter_upwards [hLeviFam, hFderivFam] with s hL hF hmem x _
  exact kPrime_aesm g gi hC hK S a b i t s x (hL hmem) (hF hmem x)

/-! ###############################################################################
    ### R3 — `hboundz_int`: the order-2 Gaussian dominator is z-integrable.
    ############################################################################### -/

/-- **R3 — `hboundz_gaussian_int`.**  THE EXACT `hboundz_int` census leg for the honest order-2
    Gaussian dominator `boundz s z = C·G_{κ(t−s)}(z)`: for every `s ∈ uIoc 0 (t−εₘ)` the width
    `κ(t−s)` is positive (every such `s` has `s < t`, since `s ≤ 0 ⊔ (t−εₘ) < t` — no `ε ≤ t`
    assumption), so `envelope_integrable` applies.  Mirrors `WitnessDerivDomination.hzint_witness`.
    NOT `a₁ = R/6`. -/
theorem hboundz_gaussian_int (t : ℝ) (ht : 0 < t) (m : ℕ) (κ C : ℝ) (hκ : 0 < κ) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z : Point n => C * gaussDdim (κ * (t - s)) z) (volume : Measure (Point n)) := by
  refine ae_of_all _ (fun s hmem => ?_)
  have hst : s < t :=
    lt_of_le_of_lt hmem.2 (sup_lt_iff.mpr ⟨ht, by have := epsSeq_pos m; linarith⟩)
  have hσ : 0 < κ * (t - s) := mul_pos hκ (by linarith)
  exact envelope_integrable (κ * (t - s)) hσ C

/-! ###############################################################################
    ### R4 — `hG'meas`: outer `s`-ae-measurability of `s ↦ ∫z kPrime … x₀ z`.
    ############################################################################### -/

/-- **R4 — `hG'meas_witness`.**  THE EXACT `hG'meas` census leg — `s`-ae-measurability of the
    `z`-integral `s ↦ ∫z kPrime … x₀ z` on `volume.restrict (uIoc 0 (t−εₘ))` — from the joint
    `(s,z)`-measurability of `kPrime … x₀ ·` via `AEStronglyMeasurable.integral_prod_right'`.
    Mirrors `WitnessDerivMeasurability.hsmeas_witness`.  NOT `a₁ = R/6`. -/
theorem hG'meas_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (x₀ : Point n)
    (hjoint : AEStronglyMeasurable
      (fun p : ℝ × Point n => kPrime g gi hC hK S a b i t p.1 x₀ p.2)
      ((volume.restrict (Set.uIoc 0 (t - epsSeq m))).prod (volume : Measure (Point n)))) :
    AEStronglyMeasurable
      (fun s => ∫ z, kPrime g gi hC hK S a b i t s x₀ z)
      (volume.restrict (Set.uIoc 0 (t - epsSeq m))) :=
  hjoint.integral_prod_right'

/-! ###############################################################################
    ### CAPSTONE — the three MECHANICAL R2′ legs, assembled.
    ############################################################################### -/

/-- **★★ CAPSTONE — `kPrime_R2prime_mechanical`.**  The conjunction of the THREE MECHANICAL R2′
    legs of `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` — `hK'meas`, `hboundz_int` (at the honest
    order-2 Gaussian dominator), and `hG'meas` — each exhibited as a reduction to
    {banked Levi measurability (`hLeviFam`/`hLeviJoint`, suppliable from
    `FixedGateSourceProviders.leviSource_zslice_aesm`/`leviSource_joint_aesm`), honest bare
    second-field-derivative measurability (`hFderivFam`/`hFderivJoint`, the exact second-order analog
    of `WitnessDerivMeasurability`'s carried `hKmeas`/`hjoint`), banked envelope integrability
    (`envelope_integrable`)}.  NONE of these needs joint `(x,z)` chart second-jet regularity — that is
    needed ONLY for the MAGNITUDE legs `hK'bound`/`hG'bound`, which route to
    `JointSecondOrderRNCRegularity`'s second jet and are DELIBERATELY not supplied here.
    NOT `a₁ = R/6`. -/
theorem kPrime_R2prime_mechanical (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (ht : 0 < t) (m : ℕ) (x₀ : Point n) (κ C : ℝ) (hκ : 0 < κ)
    (hLeviFam : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        AEStronglyMeasurable
          (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n)))
    (hFderivFam : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ x : Point n,
        AEStronglyMeasurable
          (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
          (volume : Measure (Point n)))
    (hLeviJoint : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 (t - epsSeq m))).prod (volume : Measure (Point n))))
    (hFderivJoint : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - p.1) y p.2) x₀)
      ((volume.restrict (Set.uIoc 0 (t - epsSeq m))).prod (volume : Measure (Point n)))) :
    (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x ∈ (Set.univ : Set (Point n)),
          AEStronglyMeasurable (fun z => kPrime g gi hC hK S a b i t s x z)
            (volume : Measure (Point n)))
    ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z : Point n => C * gaussDdim (κ * (t - s)) z) (volume : Measure (Point n)))
    ∧ AEStronglyMeasurable
        (fun s => ∫ z, kPrime g gi hC hK S a b i t s x₀ z)
        (volume.restrict (Set.uIoc 0 (t - epsSeq m))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hK'meas_witness g gi hC hK S a b i t m hLeviFam hFderivFam
  · exact hboundz_gaussian_int t ht m κ C hκ
  · exact hG'meas_witness g gi hC hK S a b i t m x₀
      (kPrime_joint_aesm g gi hC hK S a b i t m x₀ hLeviJoint hFderivJoint)

end QIQTH.KPrimeMeasurabilityScaffolding

section AxiomChecks
open QIQTH.KPrimeMeasurabilityScaffolding
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms kPrime_aesm
#print axioms kPrime_joint_aesm
#print axioms hK'meas_witness
#print axioms hboundz_gaussian_int
#print axioms hG'meas_witness
#print axioms kPrime_R2prime_mechanical
end AxiomChecks
