/-
  KPrimeMagnitudeScaffolding — the MAGNITUDE (domination) half of the `kPrime` census in
  `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` — the two legs `hK'bound` (pointwise operator-norm
  Gaussian envelope on the SECOND field derivative) and `hG'bound` (the singular
  `‖∫z kPrime‖ ≤ C·(t−s)⁻¹` per-`s` bound).  The magnitude mirror of the MEASURABILITY scaffolding
  `KPrimeMeasurabilityScaffolding` (J4-841), one factorization deeper.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}; hCConv is NOT closed here.
  This brick supplies the MAGNITUDE half of the "R2′" residue by REDUCING the two domination legs of
  `fderivBulkInt_hasFDerivAt` to a `norm_smul` factorization plus explicitly-named, satisfiable
  envelope carries.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis,
  none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DECISIVE HONEST FINDING (why the magnitude legs do NOT reduce to the three named
     geometric interfaces — the mismatch this session set out to test).

  The three named geometric hypotheses of the `hCConv` reduction —
    `JointSecondOrderRNCRegularity` (diagonal, J4-792), `JointSecondOrderRNCRegularityMixed`
    (off-diagonal cross-jet, J4-794), `VanVleckGatedSpatialSymmetry` (R1 base↔eval, J4-795) —
  are ALL shaped to produce the ε-window **SLIVER RATE** `hsliver`
    (`dist (fderivBulkInt … i m x) (gderivInt … i x) ≤ ∑ⱼ bb j`, `bb → 0`,
     wired by `VVGatedSym.hsliver_of_vanVleckGatedSpatialSymmetry` through
     `KPrimeOpNormSliver.kPrime_opNorm_sliver_bound`).  That is an INTEGRATED-in-`(s,z)` estimate.

  The two magnitude legs `hK'bound`/`hG'bound` are a DIFFERENT CLASS: pointwise / per-`s`
  Leibniz-DOMINATION bounds needed to establish that `fderivBulkInt` IS the Fréchet derivative
  (`hbulkderiv`) — a logically SEPARATE fact from the sliver rate.  Their natural supplier is the
  pointwise second-derivative envelope `SecondDerivEnvelope.witnessFieldDeriv2_envelope_coercive`,
  NOT the RNC chart-jet structures.  Three concrete obstructions block a direct instantiation from
  the three named structures:

    (a) `‖kPrime … x z‖` is the OPERATOR norm of `leviSeries • fderiv(fun y ↦ witnessFieldDeriv …
        i (t−s) y z) x`, whose CLM components are ALL the mixed second field derivatives
        `∂ⱼ∂ᵢ H` (`j = 0,…,n−1`); `SecondDerivEnvelope.witnessFieldDeriv2 = pd_i(pd_i H)` is the
        DIAGONAL `∂ᵢ∂ᵢ` only (`EngineInstantiation.witnessFieldDeriv2`).  Bounding the operator norm
        needs a MIXED-directions envelope, which the banked (diagonal) envelope does not provide.
    (b) `witnessFieldDeriv2_envelope_coercive` carries its OWN scalar sup-bounds
        (`Bs2 / Bs1 / Ba / Bd / Bdd`) as hypotheses — distinct in SHAPE from the RNC structures'
        surface/jet fields; they are not literally any field of the three named structures.
    (c) the pointwise identity `(fderiv (fun y ↦ witnessFieldDeriv … i (t−s) y z) x)(eⱼ)
        = witnessFieldDeriv2-mixed` is itself unproven definitional content.

  ⇒ The magnitude legs are NOT re-application of the RNC/VV machinery; they route to the
    `SecondDerivEnvelope` class (a MIXED-directions extension of it).  This file therefore does the
    HONEST thing that IS available quickly: it factorizes the magnitude legs through `norm_smul` and
    reduces them to explicitly-named envelope carries, precisely relocating the residue.

  ## THE DELIVERABLE (ns `QIQTH.KPrimeMagnitudeScaffolding`).
    • `kPrime_norm_factor` — the pointwise norm-of-smul identity
        `‖kPrime … x z‖ = |leviSeries … s z 0| · ‖fderiv (fun y ↦ witnessFieldDeriv … i (t−s) y z) x‖`.
    • `hK'bound_of_envelope` — ★ the EXACT `hK'bound` census shape, from a Levi magnitude bound `BL`
      and an `x`-uniform field-Hessian operator-norm envelope `BF`, with `boundz s z := BL s z · BF s z`.
    • `hG'bound_of_envelope` — ★ the EXACT `hG'bound` census shape, from the pointwise `boundz`
      domination (i.e. `hK'bound` output) + `z`-integrabilities + the honest `z`-mass bound
      `∫z boundz s z ≤ C·(t−s)⁻¹` (the `(t−s)⁻¹` order established in `SecondDerivEnvelope` §C),
      via `norm_integral_le_integral_norm` + `integral_mono_ae`.
    • `kPrime_R2prime_magnitude` — ★★ the capstone conjunction of the two magnitude legs, exhibiting
      both as reductions to {Levi magnitude bound, field-Hessian operator-norm envelope, `z`-mass
      bound, `z`-integrabilities}.  The field-Hessian envelope `BF` is the honest residue — the
      MIXED-directions `SecondDerivEnvelope`-class input, NOT a field of the three named RNC/VV
      structures (see the finding above).  NOT `a₁ = R/6`.

  Every carry is satisfiable and non-vacuous (the width-2 Gaussian model of the sliver census supplies
  the Levi magnitude bound, the Hessian operator-norm envelope, and the `(t−s)⁻¹` `z`-mass) and never
  equal to the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FderivBulkConcrete

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.FlatHeatEquation
open QIQTH.FderivBulkConcrete
open scoped Topology Interval BigOperators

namespace QIQTH.KPrimeMagnitudeScaffolding

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### M1 — the pointwise norm-of-smul factorization for `kPrime`.
    ############################################################################### -/

/-- **M1 — `kPrime_norm_factor`.**  The pointwise operator-norm factorization of the field-Hessian
    kernel: since `kPrime` is definitionally `leviSeries • fderiv`, its CLM operator norm splits as
      `‖kPrime … x z‖ = |leviSeries … s z 0| · ‖fderiv (fun y ↦ witnessFieldDeriv … i (t−s) y z) x‖`,
    by `norm_smul` (real scalar).  This is the magnitude analog of `KPrimeMeasurabilityScaffolding`'s
    `.smul` measurability reducer.  NOT `a₁ = R/6`. -/
theorem kPrime_norm_factor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t s : ℝ) (x z : Point n) :
    ‖kPrime g gi hC hK S a b i t s x z‖
      = |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
        * ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖ := by
  simp only [kPrime, norm_smul, Real.norm_eq_abs]

/-! ###############################################################################
    ### M2 — `hK'bound`: the pointwise operator-norm envelope on `kPrime`.
    ############################################################################### -/

/-- **★ M2 — `hK'bound_of_envelope`.**  THE EXACT `hK'bound` census leg of
    `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` — `∀ᵐ s, s ∈ uIoc 0 (t−εₘ) → ∀ᵐ z, ∀ x ∈ univ,
    ‖kPrime … i t s x z‖ ≤ boundz s z` — from
      • a Levi magnitude bound `|leviSeries … s z 0| ≤ BL s z`, and
      • an `x`-UNIFORM field-Hessian operator-norm envelope
        `‖fderiv (fun y ↦ witnessFieldDeriv … i (t−s) y z) x‖ ≤ BF s z` (all `x`),
    with the honest dominator `boundz s z := BL s z · BF s z`, via `kPrime_norm_factor` + product
    monotonicity.  The Levi magnitude bound is banked-suppliable (Gaussian envelope); the field-Hessian
    operator-norm envelope `BF` is the honest MIXED-directions `SecondDerivEnvelope`-class residue
    (NOT a field of the three named RNC/VV structures — see the module header finding).  NOT `a₁ = R/6`. -/
theorem hK'bound_of_envelope (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (BL BF : ℝ → Point n → ℝ)
    (hLevi : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0| ≤ BL s z)
    (hFd : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∀ x : Point n,
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖ ≤ BF s z) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x ∈ (Set.univ : Set (Point n)),
        ‖kPrime g gi hC hK S a b i t s x z‖ ≤ BL s z * BF s z := by
  filter_upwards [hLevi, hFd] with s hL hF hmem
  filter_upwards [hL hmem, hF hmem] with z hLz hFz x _
  rw [kPrime_norm_factor g gi hC hK S a b i t s x z]
  have hBLnn : 0 ≤ BL s z := le_trans (abs_nonneg _) hLz
  exact mul_le_mul hLz (hFz x) (norm_nonneg _) hBLnn

/-! ###############################################################################
    ### M3 — `hG'bound`: the singular per-`s` bound on the `z`-integral of `kPrime`.
    ############################################################################### -/

/-- **★ M3 — `hG'bound_of_envelope`.**  THE EXACT `hG'bound` census leg — `∀ᵐ s, s ∈ uIoc 0 (t−εₘ) →
    ∀ x ∈ univ, ‖∫z kPrime … i t s x z‖ ≤ C·(t−s)⁻¹` — from
      • the pointwise domination `‖kPrime … x z‖ ≤ boundz s z` (i.e. `hK'bound`'s output),
      • per-`s`,`x` integrability of `z ↦ kPrime … x z` and of `boundz s`, and
      • the honest `z`-mass bound `∫z boundz s z ≤ C·(t−s)⁻¹` (the `(t−s)⁻¹` order the order-2 envelope
        leaves after `z`-integration, `SecondDerivEnvelope` §C),
    via `norm_integral_le_integral_norm` + `integral_mono_ae`.  NOT `a₁ = R/6`. -/
theorem hG'bound_of_envelope (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (C : ℝ) (boundz : ℝ → Point n → ℝ)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∀ x ∈ (Set.univ : Set (Point n)),
          ‖kPrime g gi hC hK S a b i t s x z‖ ≤ boundz s z)
    (hkint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x : Point n, Integrable (fun z => kPrime g gi hC hK S a b i t s x z) volume)
    (hbint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (boundz s) volume)
    (hzmass : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ z, boundz s z) ≤ C * (t - s)⁻¹) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x ∈ (Set.univ : Set (Point n)),
        ‖∫ z, kPrime g gi hC hK S a b i t s x z‖ ≤ C * (t - s)⁻¹ := by
  filter_upwards [hbound, hkint, hbint, hzmass] with s hb hki hbi hzm hmem x hx
  calc ‖∫ z, kPrime g gi hC hK S a b i t s x z‖
      ≤ ∫ z, ‖kPrime g gi hC hK S a b i t s x z‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z, boundz s z := by
        refine integral_mono_ae ((hki hmem x).norm) (hbi hmem) ?_
        filter_upwards [hb hmem] with z hz
        exact hz x hx
    _ ≤ C * (t - s)⁻¹ := hzm hmem

/-! ###############################################################################
    ### CAPSTONE — the two MAGNITUDE R2′ legs, assembled.
    ############################################################################### -/

/-- **★★ CAPSTONE — `kPrime_R2prime_magnitude`.**  The conjunction of the TWO MAGNITUDE R2′ legs of
    `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` — `hK'bound` (at `boundz s z := BL s z · BF s z`)
    and `hG'bound` — each exhibited as a reduction to {Levi magnitude bound `BL` (banked-suppliable
    Gaussian envelope), field-Hessian operator-norm envelope `BF` (the honest MIXED-directions
    `SecondDerivEnvelope`-class residue), `z`-mass bound `∫z BL·BF ≤ C·(t−s)⁻¹`, per-slice
    `z`-integrabilities}.  Together with `KPrimeMeasurabilityScaffolding.kPrime_R2prime_mechanical`
    (the measurability half, J4-841), this exhibits ALL `kPrime`-specific census members of
    `fderivBulkInt_hasFDerivAt` as reductions to named, satisfiable analytic carries — the honest
    residue being the field-Hessian operator-norm envelope `BF`, which is NOT a field of the three
    named RNC/VV geometric structures (module header finding).  NOT `a₁ = R/6`. -/
theorem kPrime_R2prime_magnitude (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (C : ℝ) (BL BF : ℝ → Point n → ℝ)
    (hLevi : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0| ≤ BL s z)
    (hFd : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∀ x : Point n,
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖ ≤ BF s z)
    (hkint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x : Point n, Integrable (fun z => kPrime g gi hC hK S a b i t s x z) volume)
    (hbint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z * BF s z) volume)
    (hzmass : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ z, BL s z * BF s z) ≤ C * (t - s)⁻¹) :
    (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∀ x ∈ (Set.univ : Set (Point n)),
          ‖kPrime g gi hC hK S a b i t s x z‖ ≤ BL s z * BF s z)
    ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x ∈ (Set.univ : Set (Point n)),
          ‖∫ z, kPrime g gi hC hK S a b i t s x z‖ ≤ C * (t - s)⁻¹) := by
  have hKb := hK'bound_of_envelope g gi hC hK S a b i t m BL BF hLevi hFd
  exact ⟨hKb, hG'bound_of_envelope g gi hC hK S a b i t m C (fun s z => BL s z * BF s z)
    hKb hkint hbint hzmass⟩

end QIQTH.KPrimeMagnitudeScaffolding

section AxiomChecks
open QIQTH.KPrimeMagnitudeScaffolding
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms kPrime_norm_factor
#print axioms hK'bound_of_envelope
#print axioms hG'bound_of_envelope
#print axioms kPrime_R2prime_magnitude
end AxiomChecks
