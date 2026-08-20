/-
  HkintReducedToHbint — J4-875: with the now-CONCRETE field-Hessian envelope `BF`, the `hkint` field of
  `MixedDirectionsFieldHessianEnvelope` (per-slice `z`-integrability of the `kPrime` kernel) is NOT an
  independent obstruction — it REDUCES to `hbint` (integrability of the product dominator `BL·BF`) via
  the pointwise magnitude bound `‖kPrime … x z‖ ≤ BL s z · BF s z` and `Integrable.mono'`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick REDUCES the `hkint` field of
  the envelope to `hbint`, showing the remaining envelope walls funnel into the `hbint`/`hzmass`
  dominator choice.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis,
  none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FINDING (entanglement audit, post-J4-874).

  `kPrime … i t s x z = (leviSeries … s z 0) • fderiv ℝ (y ↦ witnessFieldDeriv … i (t−s) y z) x`
  (`FderivBulkConcrete.kPrime`), so `‖kPrime … x z‖ = |leviSeries … s z 0| · ‖fderiv … x‖`.  With the
  CONCRETE envelope `BF s z := ⨆ x', ‖fderiv … x'‖` (whose bound J4-874
  `hFd_concrete_ciSup_fully_closed` established for ALL `x`) and any Levi magnitude bound
  `|leviSeries| ≤ BL s z` (the `hLevi` field), the product bound `‖kPrime … x z‖ ≤ BL s z · BF s z`
  holds pointwise.  Hence, given `hbint` (`Integrable (z ↦ BL s z · BF s z)`) and the carried
  `z`-measurability of `kPrime`, `hkint` follows by `Integrable.mono'`.

  So of the five envelope fields — `hLevi`, `hFd`, `hkint`, `hbint`, `hzmass` — the concrete `BF` closes
  `hFd` (J4-874) and makes `hkint` DOWNSTREAM of `hbint` (this brick).  `hLevi` is a free Levi magnitude
  bound; the genuine remaining content is `hbint` + `hzmass` (the Gaussian `z`-moment estimate — the deep
  §C wall), which share the SAME `BL·BF` dominator.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HFdCoreContinuityClosed
import QIQTH.KPrimeMagnitudeScaffolding

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete
open scoped Topology Interval BigOperators

namespace QIQTH.HkintReducedToHbint

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### C0 — the pointwise magnitude bound `‖kPrime … x z‖ ≤ BL s z · BF s z`.
    ############################################################################### -/

/-- **★ `kPrime_norm_le_product`.**  The pointwise magnitude bound: `‖kPrime … x z‖ ≤ BL s z · BF s z`
    at the CONCRETE envelope `BF s z := ⨆ x', ‖fderiv … x'‖`, from a Levi magnitude bound
    `|leviSeries … s z 0| ≤ BL s z` and the field-Hessian bound `‖fderiv … x‖ ≤ BF s z` (the J4-874
    conclusion for THIS `x`).  `‖kPrime‖ = |leviSeries| · ‖fderiv‖` (`norm_smul`, real scalar), then
    `mul_le_mul`.  NOT `a₁ = R/6`. -/
theorem kPrime_norm_le_product (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t s : ℝ) (x z : Point n) (BLsz BFsz : ℝ)
    (hL : |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0| ≤ BLsz)
    (hF : ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖ ≤ BFsz) :
    ‖kPrime g gi hC hK S a b i t s x z‖ ≤ BLsz * BFsz := by
  have hBL0 : 0 ≤ BLsz := le_trans (abs_nonneg _) hL
  have hnorm : ‖kPrime g gi hC hK S a b i t s x z‖
      = |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
        * ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖ := by
    simp only [kPrime, norm_smul, Real.norm_eq_abs]
  rw [hnorm]
  exact mul_le_mul hL hF (norm_nonneg _) hBL0

/-! ###############################################################################
    ### C1 — the per-`(s,x)` integrability reduction.
    ############################################################################### -/

/-- **★ `kPrime_integrable_of_product`.**  Per-slice, per-base: `Integrable (z ↦ kPrime … x z)` from
    (i) `Integrable (z ↦ BL s z · BF s z)` (the `hbint` slice), (ii) `AEStronglyMeasurable
    (z ↦ kPrime … x z)` (the carried `kPrime` `z`-measurability), and (iii) the a.e. product bound
    (`kPrime_norm_le_product`, from the Levi bound and the J4-874 field-Hessian bound at THIS `x`).  Via
    `Integrable.mono'`.  NOT `a₁ = R/6`. -/
theorem kPrime_integrable_of_product (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t s : ℝ) (x : Point n) (BL BF : ℝ → Point n → ℝ)
    (hbint : Integrable (fun z => BL s z * BF s z) volume)
    (hmeas : AEStronglyMeasurable (fun z => kPrime g gi hC hK S a b i t s x z) volume)
    (hL : ∀ᵐ z ∂volume,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0| ≤ BL s z)
    (hF : ∀ᵐ z ∂volume,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖ ≤ BF s z) :
    Integrable (fun z => kPrime g gi hC hK S a b i t s x z) volume := by
  refine hbint.mono' hmeas ?_
  filter_upwards [hL, hF] with z hLz hFz
  exact kPrime_norm_le_product g gi hC hK S a b i t s x z (BL s z) (BF s z) hLz hFz

/-! ###############################################################################
    ### C2 — the `hkint` FIELD, reduced a.e. to `hbint` at the concrete `BF`.
    ############################################################################### -/

/-- **★★★ J4-875 — `hkint_reduces_to_hbint_concrete`.**  The EXACT `hkint` field of
    `MixedDirectionsFieldHessianEnvelope` (per-slice `z`-integrability of `kPrime`), at the CONCRETE
    envelope `BF s z := ⨆ x', ‖fderiv (y ↦ witnessFieldDeriv … i (t−s) y z) x'‖`, REDUCED a.e. to:
      • `hbint` — `Integrable (z ↦ BL s z · BF s z)` (the envelope's own `hbint` field);
      • `hmeas` — carried `z`-measurability of `kPrime` (the `KPrimeMeasurabilityScaffolding` family);
      • `hLevi` — the envelope's own Levi magnitude bound `|leviSeries| ≤ BL s z`;
      • `hFd`   — the envelope's own field-Hessian bound (CLOSED unconditionally by J4-874).
    So `hkint` is DOWNSTREAM of `hbint` — not an independent wall.  NOT `a₁ = R/6`. -/
theorem hkint_reduces_to_hbint_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (BL BF : ℝ → Point n → ℝ)
    (hbint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z * BF s z) volume)
    (hmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x : Point n,
          AEStronglyMeasurable (fun z => kPrime g gi hC hK S a b i t s x z) volume)
    (hLevi : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0| ≤ BL s z)
    (hFd : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∀ x : Point n,
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖ ≤ BF s z) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x : Point n, Integrable (fun z => kPrime g gi hC hK S a b i t s x z) volume := by
  filter_upwards [hbint, hmeas, hLevi, hFd] with s hbs hms hLs hFs hmem x
  refine kPrime_integrable_of_product g gi hC hK S a b i t s x BL BF
    (hbs hmem) (hms hmem x) (hLs hmem) ?_
  filter_upwards [hFs hmem] with z hz using hz x

end QIQTH.HkintReducedToHbint

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HkintReducedToHbint
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms kPrime_norm_le_product
#print axioms kPrime_integrable_of_product
#print axioms hkint_reduces_to_hbint_concrete
end AxiomChecks
