/-
  MixedDirectionsFieldHessianEnvelope — J4-843: the FOURTH named hypothesis of the `hCConv` reduction.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}; hCConv is NOT closed here.  This brick
  NAMES — as a single, precise, satisfiable, non-vacuous Prop-bundle — the MIXED-DIRECTIONS
  field-Hessian operator-norm envelope that J4-842 (`KPrimeMagnitudeScaffolding`) identified as the
  honest fourth input the two `kPrime` MAGNITUDE legs (`hK'bound`/`hG'bound`) reduce to, and WIRES that
  bundle forward to the exact conjunction `kPrime_R2prime_magnitude` produces.  No `sorry`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing
  file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY A FOURTH STRUCTURE (the J4-842 finding, recorded).

  The three previously-named geometric hypotheses of the `hCConv` reduction —
    `JointSecondOrderRNCRegularity` (diagonal, J4-792), `JointSecondOrderRNCRegularityMixed`
    (off-diagonal cross-jet, J4-794), `VanVleckGatedSpatialSymmetry` (R1 base↔eval, J4-795) —
  are ALL shaped to produce the ε-window **SLIVER RATE** `hsliver` (an integrated-in-`(s,z)` estimate).
  The two magnitude legs `hK'bound`/`hG'bound` are a DIFFERENT CLASS — pointwise / per-`s`
  Leibniz-DOMINATION bounds needed to establish that `fderivBulkInt` IS the Fréchet derivative
  (`hbulkderiv`), logically SEPARATE from the sliver rate.  Their natural supplier is a MIXED-directions
  field-Hessian operator-norm envelope: `‖kPrime … x z‖` is `|leviSeries|·‖fderiv(y ↦ witnessFieldDeriv
  … i (t−s) y z) x‖`, whose CLM contains ALL mixed second field derivatives `∂ⱼ∂ᵢH`, whereas the banked
  (diagonal) `SecondDerivEnvelope.witnessFieldDeriv2 = ∂ᵢ∂ᵢH` covers only the diagonal.  This bundle
  isolates precisely that mixed envelope.

  ## THE DELIVERABLE (ns `QIQTH.MixedDirFieldHessianEnvelope`).
    • `MixedDirectionsFieldHessianEnvelope` — ★★ the Prop bundle: an `x`-UNIFORM mixed-directions
      field-Hessian operator-norm envelope `BF`, a Levi magnitude bound `BL`, the per-slice `z`-mass
      bound `∫z BL·BF ≤ C·(t−s)⁻¹`, and the two per-slice `z`-integrabilities — exactly the data
      `KPrimeMagnitudeScaffolding.kPrime_R2prime_magnitude` consumes.
    • `magnitude_legs_of_mixedEnvelope` — ★★★ the wiring: the bundle yields the EXACT `hK'bound`
      (at `boundz s z := BL s z · BF s z`) and `hG'bound` census legs of
      `FderivBulkConcrete.fderivBulkInt_hasFDerivAt`.

  Non-vacuity: satisfiable by the width-2 Gaussian model of the sliver census (which supplies the Levi
  magnitude bound, the Hessian operator-norm envelope `BF`, and the `(t−s)⁻¹` `z`-mass); never equal to
  the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.KPrimeMagnitudeScaffolding

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.FlatHeatEquation
open QIQTH.FderivBulkConcrete
open scoped Topology Interval BigOperators

namespace QIQTH.MixedDirFieldHessianEnvelope

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE FOURTH NAMED HYPOTHESIS — the mixed-directions field-Hessian envelope.
    ############################################################################### -/

/-- **★★ `MixedDirectionsFieldHessianEnvelope`.**  THE PRECISE fourth input the two `kPrime` MAGNITUDE
    legs reduce to (J4-842 finding).  It bundles, on the bulk interval `(0, t−εₘ)`:
      • `hFd`   — the `x`-UNIFORM mixed-directions field-Hessian operator-norm envelope
                  `‖fderiv (y ↦ witnessFieldDeriv … i (t−s) y z) x‖ ≤ BF s z` (all `x`);
      • `hLevi` — a Levi magnitude bound `|leviSeries … s z 0| ≤ BL s z`;
      • `hkint` — per-`s`,`x` integrability of `z ↦ kPrime … x z`;
      • `hbint` — per-`s` integrability of the product dominator `z ↦ BL s z · BF s z`;
      • `hzmass`— the honest `z`-mass bound `∫z BL·BF ≤ C·(t−s)⁻¹`.
    This is EXACTLY the data `KPrimeMagnitudeScaffolding.kPrime_R2prime_magnitude` consumes; it is NOT a
    field of the three named RNC/VV geometric structures (which produce the sliver RATE, a different
    class).  Satisfiable, non-vacuous, and never the conclusion.  NOT `a₁ = R/6`. -/
structure MixedDirectionsFieldHessianEnvelope (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (C : ℝ) (BL BF : ℝ → Point n → ℝ) : Prop where
  /-- Levi magnitude bound on the bulk. -/
  hLevi : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0| ≤ BL s z
  /-- the `x`-UNIFORM mixed-directions field-Hessian operator-norm envelope. -/
  hFd : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖ ≤ BF s z
  /-- per-slice `z`-integrability of the field-Hessian kernel `kPrime`. -/
  hkint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x : Point n, Integrable (fun z => kPrime g gi hC hK S a b i t s x z) volume
  /-- per-slice `z`-integrability of the product dominator `BL·BF`. -/
  hbint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z => BL s z * BF s z) volume
  /-- the honest `z`-mass bound `∫z BL·BF ≤ C·(t−s)⁻¹`. -/
  hzmass : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      (∫ z, BL s z * BF s z) ≤ C * (t - s)⁻¹

/-! ###############################################################################
    ### THE WIRING — the bundle ⟹ the two `kPrime` MAGNITUDE legs.
    ############################################################################### -/

/-- **★★★ `magnitude_legs_of_mixedEnvelope`.**  THE WIRING: the named fourth hypothesis
    `MixedDirectionsFieldHessianEnvelope` yields the EXACT conjunction of the two MAGNITUDE census legs
    of `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` —
      • `hK'bound` at `boundz s z := BL s z · BF s z`, and
      • `hG'bound` (`‖∫z kPrime … x z‖ ≤ C·(t−s)⁻¹`),
    via `KPrimeMagnitudeScaffolding.kPrime_R2prime_magnitude`.  Together with the (banked, J4-841)
    kPrime measurability scaffolding and the two RNC/VV sliver interfaces, this exhibits every
    `kPrime`-specific census member of `fderivBulkInt_hasFDerivAt` as a reduction to named, satisfiable
    inputs.  NOT `a₁ = R/6`. -/
theorem magnitude_legs_of_mixedEnvelope (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (C : ℝ) (BL BF : ℝ → Point n → ℝ)
    (env : MixedDirectionsFieldHessianEnvelope g gi hC hK S a b i t m C BL BF) :
    (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∀ x ∈ (Set.univ : Set (Point n)),
          ‖kPrime g gi hC hK S a b i t s x z‖ ≤ BL s z * BF s z)
    ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x ∈ (Set.univ : Set (Point n)),
          ‖∫ z, kPrime g gi hC hK S a b i t s x z‖ ≤ C * (t - s)⁻¹) :=
  QIQTH.KPrimeMagnitudeScaffolding.kPrime_R2prime_magnitude g gi hC hK S a b i t m C BL BF
    env.hLevi env.hFd env.hkint env.hbint env.hzmass

end QIQTH.MixedDirFieldHessianEnvelope

section AxiomChecks
open QIQTH.MixedDirFieldHessianEnvelope
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms magnitude_legs_of_mixedEnvelope
end AxiomChecks
