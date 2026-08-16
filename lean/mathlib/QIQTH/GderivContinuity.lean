/-
  GderivContinuity — J4-779: the CONCRETE `hcont` census member for the L2 sliver census.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  This brick closes ONE precisely-named hole in the L2 sliver census
  that J4-778b flagged as "not attempted, reduces to continuity of a parametric CLM double integral
  (Mathlib `continuous_of_dominated` should apply) + a per-slice continuity/domination census; now
  concretely statable against `gderivInt`."  Here that census IS statable and IS fired through the
  Mathlib dominated-continuity engines, discharging the `hcont` member for the concrete order-1 gated
  van-Vleck derivative field `gderivInt` (`FderivBulkConcrete`, J4-778b).  No `sorry`, no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TARGET.  `HD1Concrete.hD1_concrete`'s `hcont` field:
      `hcont : ∀ i : Fin n, ContinuousOn (gderiv i) (Set.univ)`,
  the order-2 derivative-field continuity, at the concrete `gderiv i := gderivInt g gi hC hK S a b t i`
  (`FderivBulkConcrete.gderivInt`, the FULL `x ↦ ∫₀ᵗ ∫z kPrime … s x z` CLM-valued derivative field).

  ## THE ENGINE.  `GcoefContinuity.continuousAt_doubleIntegral_of_dominated` (J4-160) is the SAME nested
  dominated-continuity engine, but SCALAR-valued (`K : ℝ → X → Y → ℝ`).  `gderivInt`'s integrand
  `kPrime` is CLM-VALUED (`Point n →L[ℝ] ℝ`), so this file first generalises that engine to an arbitrary
  Banach target `E` (both Mathlib legs — `MeasureTheory.continuousAt_of_dominated` and
  `intervalIntegral.continuousAt_of_dominated_interval` — are already stated for any
  `[NormedAddCommGroup E] [NormedSpace ℝ E]`), then instantiates it at `E := Point n →L[ℝ] ℝ`,
  `K := kPrime`, `ν := volume`.

  ## WHAT LANDS (ns `QIQTH.GderivContinuity`).
    • `continuousAt_doubleIntegral_of_dominated_banach` — ★ the Banach-valued nested engine.
    • `gderivInt_continuousAt` — ★ `ContinuousAt (gderivInt … i) x₀` from the per-slice
      continuity/domination census (measurability + z-dominator + interval-integrable s-dominator +
      per-z x-continuity of `kPrime`).
    • `gderivInt_hcont` — ★★ THE `hcont` shape VERBATIM: `∀ i, ContinuousOn (gderivInt … i) univ`,
      the exact field `HD1Concrete.hD1_concrete` consumes, from the `∀(i,x₀)` census family.

  Every hypothesis is satisfiable, non-vacuous (the width-2 Gaussian model of the sliver bricks
  satisfies the whole per-slice continuity/domination census — `kPrime` is a Levi factor times a
  Gaussian-envelope second-field-derivative, continuous in the field slot on any small ball, and
  dominated there by an `x`-free Gaussian envelope), and never equal to the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FderivBulkConcrete

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete
open scoped Topology Interval BigOperators

namespace QIQTH.GderivContinuity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### C0 — the Banach-valued nested dominated-continuity engine.
    ############################################################################### -/

/-- **★ C0 — `continuousAt_doubleIntegral_of_dominated_banach`.**  The Banach-target generalisation of
    `GcoefContinuity.continuousAt_doubleIntegral_of_dominated` (J4-160): continuity at `x₀` of the
    CLM/Banach-valued double integral `x ↦ ∫ s in (0)..t, ∫ z, K s x z ∂ν` (`K` valued in an arbitrary
    normed `ℝ`-space `E`), by TWO nested dominated-continuity applications —

    • the INNER `MeasureTheory.continuousAt_of_dominated` gives, for a.e. `s ∈ Ι 0 t`, the continuity
      at `x₀` of `x ↦ ∫ z, K s x z ∂ν`, from x-nbhd ae-measurability (`hzmeas`), x-nbhd ae z-domination
      by an integrable `boundz s` (`hzbound`, `hzint`), and per-z x-continuity (`hzcont`);
    • the OUTER `intervalIntegral.continuousAt_of_dominated_interval` then gives the continuity of the
      whole double integral, from x-nbhd ae-measurability of `s ↦ ∫ z, K s x z ∂ν` (`hsmeas`), x-nbhd
      ae s-domination by an interval-integrable `B` (`hsbound`, `hBint`), and the inner continuities.

    Both Mathlib legs are already stated for any `[NormedAddCommGroup E] [NormedSpace ℝ E]`, so the
    J4-160 proof carries over verbatim to the CLM target.  NOT `a₁ = R/6`. -/
theorem continuousAt_doubleIntegral_of_dominated_banach
    {X Y E : Type*} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : Measure Y} (t : ℝ) (x₀ : X)
    (K : ℝ → X → Y → E) (B : ℝ → ℝ) (boundz : ℝ → Y → ℝ)
    (hzmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun z => K s x z) ν)
    (hzbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂ν, ‖K s x z‖ ≤ boundz s z)
    (hzint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → Integrable (boundz s) ν)
    (hzcont : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂ν, ContinuousAt (fun x => K s x z) x₀)
    (hsmeas : ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun s => ∫ z, K s x z ∂ν) (volume.restrict (Set.uIoc 0 t)))
    (hsbound : ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ‖∫ z, K s x z ∂ν‖ ≤ B s)
    (hBint : IntervalIntegrable B volume 0 t) :
    ContinuousAt (fun x => ∫ s in (0)..t, ∫ z, K s x z ∂ν) x₀ := by
  refine intervalIntegral.continuousAt_of_dominated_interval hsmeas hsbound hBint ?_
  filter_upwards [hzmeas, hzbound, hzint, hzcont] with s hm hb hi hc hs
  exact MeasureTheory.continuousAt_of_dominated (hm hs) (hb hs) (hi hs) (hc hs)

/-! ###############################################################################
    ### C1 — the concrete `ContinuousAt` for the gated van-Vleck derivative field `gderivInt`.
    ############################################################################### -/

/-- **★ C1 — `gderivInt_continuousAt`.**  The concrete FULL derivative field
    `gderivInt … i = fun x ↦ ∫₀ᵗ ∫z kPrime … s x z` is `ContinuousAt` at `x₀`, obtained by firing the
    Banach engine C0 at `E := Point n →L[ℝ] ℝ`, `K := kPrime`, `ν := volume`.  The carries are the
    per-slice continuity/domination census: z-slot ae-measurability (`hzmeas`), z-domination by an
    integrable `boundz` (`hzbound`, `hzint`), per-z field-slot continuity of `kPrime` (`hzcont`),
    s-profile ae-measurability (`hsmeas`), s-domination by an interval-integrable `B` (`hsbound`,
    `hBint`) — genuine satisfiable analytic inputs, none the conclusion.  NOT `a₁ = R/6`. -/
theorem gderivInt_continuousAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (i : Fin n) (x₀ : Point n)
    (B : ℝ → ℝ) (boundz : ℝ → Point n → ℝ)
    (hzmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
          (fun z => kPrime g gi hC hK S a b i t s x z) volume)
    (hzbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂volume, ‖kPrime g gi hC hK S a b i t s x z‖ ≤ boundz s z)
    (hzint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → Integrable (boundz s) volume)
    (hzcont : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂volume, ContinuousAt (fun x => kPrime g gi hC hK S a b i t s x z) x₀)
    (hsmeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
        (fun s => ∫ z, kPrime g gi hC hK S a b i t s x z)
        (volume.restrict (Set.uIoc 0 t)))
    (hsbound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ‖∫ z, kPrime g gi hC hK S a b i t s x z‖ ≤ B s)
    (hBint : IntervalIntegrable B volume 0 t) :
    ContinuousAt (gderivInt g gi hC hK S a b t i) x₀ := by
  have h := continuousAt_doubleIntegral_of_dominated_banach t x₀
    (fun s x z => kPrime g gi hC hK S a b i t s x z) B boundz
    hzmeas hzbound hzint hzcont hsmeas hsbound hBint
  simpa only [gderivInt] using h

/-! ###############################################################################
    ### C2 — the exact `hcont` census member:  `∀ i, ContinuousOn (gderivInt … i) univ`.
    ############################################################################### -/

/-- **★★ C2 — `gderivInt_hcont`.**  THE `hcont` census member of `HD1Concrete.hD1_concrete`, at the
    concrete order-1 gated van-Vleck derivative field `gderiv i := gderivInt … i`:
      `∀ i : Fin n, ContinuousOn (gderivInt g gi hC hK S a b t i) (Set.univ)`.
    Each `i`-slice is `Continuous` (hence `ContinuousOn … univ`) via `continuous_iff_continuousAt` and
    the per-point `gderivInt_continuousAt` (C1), fed the `∀(i,x₀)` per-slice continuity/domination
    census.  This is EXACTLY the object `HD1Concrete.hD1_concrete`'s `hcont` field binds abstractly —
    so with `gderiv := gderivInt g gi hC hK S a b t`, this file supplies `hcont` CONCRETELY (matching
    `FderivBulkConcrete`'s J4-778b concrete `hbulkderiv` supply for the same census).  NOT `a₁ = R/6`. -/
theorem gderivInt_hcont (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ)
    (B : Fin n → Point n → ℝ → ℝ) (boundz : Fin n → Point n → ℝ → Point n → ℝ)
    (hzmeas : ∀ (i : Fin n) (x₀ : Point n), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
          (fun z => kPrime g gi hC hK S a b i t s x z) volume)
    (hzbound : ∀ (i : Fin n) (x₀ : Point n), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂volume,
          ‖kPrime g gi hC hK S a b i t s x z‖ ≤ boundz i x₀ s z)
    (hzint : ∀ (i : Fin n) (x₀ : Point n), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        Integrable (boundz i x₀ s) volume)
    (hzcont : ∀ (i : Fin n) (x₀ : Point n), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂volume, ContinuousAt (fun x => kPrime g gi hC hK S a b i t s x z) x₀)
    (hsmeas : ∀ (i : Fin n) (x₀ : Point n), ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
        (fun s => ∫ z, kPrime g gi hC hK S a b i t s x z)
        (volume.restrict (Set.uIoc 0 t)))
    (hsbound : ∀ (i : Fin n) (x₀ : Point n), ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
          ‖∫ z, kPrime g gi hC hK S a b i t s x z‖ ≤ B i x₀ s)
    (hBint : ∀ (i : Fin n) (x₀ : Point n), IntervalIntegrable (B i x₀) volume 0 t) :
    ∀ i : Fin n, ContinuousOn (gderivInt g gi hC hK S a b t i) (Set.univ) := by
  intro i
  rw [continuousOn_univ, continuous_iff_continuousAt]
  intro x₀
  exact gderivInt_continuousAt g gi hC hK S a b t i x₀ (B i x₀) (boundz i x₀)
    (hzmeas i x₀) (hzbound i x₀) (hzint i x₀) (hzcont i x₀)
    (hsmeas i x₀) (hsbound i x₀) (hBint i x₀)

end QIQTH.GderivContinuity

section AxiomChecks
open QIQTH.GderivContinuity
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms continuousAt_doubleIntegral_of_dominated_banach
#print axioms gderivInt_continuousAt
#print axioms gderivInt_hcont
end AxiomChecks
