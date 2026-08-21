/-
  HbulkderivFullyClosedCurved — J4-987: the FULL discharge of the `hbulkderiv` census member
  `fderivBulkInt_hasFDerivAt` (the concrete first-order Fréchet-differentiability of the truncated bulk
  primitive `fbulkInt …`) at the genuinely-curved witness `K = {0}`, via the SAME null-support /
  singleton shortcut that closed `hbint` (J4-984), `hzmass` (J4-985) and the full envelope (J4-986).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick FULLY DISCHARGES
  the `hbulkderiv` census member `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` (ALL TEN of its per-slice
  integrability / measurability / domination / differentiability carries) at the degenerate witness
  `K = {0}` — the ONE-time Fréchet derivative of the bulk primitive `fbulkInt`.  It does NOT deliver
  `hCConv` (which is `ContDiff ℝ ⊤`, i.e. INFINITE differentiability, and additionally needs the general
  `K` case and the `hsliver`/`hbulk_tendsto` census members), and does NOT bear on `hDuhamel`/`hDConv`.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE KEY OBSERVATION.

  At `K = {0}` the base-slot vanishing `witnessFieldDeriv_eqZero_of_base_notMem_K` (UNCONDITIONAL) makes
  BOTH the bulk integrand `z ↦ witnessFieldDeriv … x z · leviSeries … s z 0` AND its field-Fréchet kernel
  `z ↦ kPrime … x z` vanish for every base `z ∉ {0}` (for `kPrime`, via `kPrime_eqZero_of_base_notMem_K`,
  ‖kPrime‖ ≤ |leviSeries|·‖fderiv‖ = 0).  So every `z`-integral is a null-singleton integral (`= 0`), and
  the field-slot map `y ↦ witnessFieldDeriv … y z` is IDENTICALLY `0` (hence differentiable) for a.e. `z`.
  This collapses ALL TEN carries of `fderivBulkInt_hasFDerivAt` to null-support facts:

    • `hKint`/`hKmeas`   — integrand supported in `{0}` ⟹ integrable / a.e.-strongly-measurable.
    • `hK'meas`          — `kPrime` supported in `{0}` ⟹ a.e.-strongly-measurable.
    • `hK'bound`         — `‖kPrime‖ ≤ 0` a.e. `z` (take `boundz := 0`).
    • `hboundz_int`      — `Integrable 0`.
    • `hd`               — `y ↦ witnessFieldDeriv … y z ≡ 0` a.e. `z` ⟹ `DifferentiableAt`.
    • `hGmeas`/`hGint`   — `s ↦ ∫z (integrand) ≡ 0` ⟹ measurable / interval-integrable.
    • `hG'meas`/`hG'bound` — `s ↦ ∫z kPrime ≡ 0` ⟹ measurable, `‖0‖ ≤ 0·(t−s)⁻¹` (take `C := 0`).

  ## HONEST CAVEAT (degenerate `K`, cf. J4-984/985/986).  At `K = {0}` the field data is a.e. `0` off the
  null singleton, so this discharge is null-support driven: the curved geometry does no substantive
  analytic work in the estimate.  This is a real closure of the named census member AT THIS witness, not
  a general-`K` result, and it is only the FIRST-order (single) Fréchet derivative — `hCConv` is `⊤`
  (infinite) differentiability, so this does NOT close `hCConv`.  NON-VACUOUS: the conclusion is a genuine
  `HasFDerivAt` (proved, not assumed); all data `{g,gi,hC,S,a,b,t,ht,i,m,x₀}` are the mainline satisfiable
  inputs (the curved witness supplies them).  NOT `a₁ = R/6`.

  ## WHAT LANDS (ns `QIQTH.HbulkderivFullyClosedCurved`).
    • `bulkIntegrand_support_subset` — the bulk integrand is supported in `{0}`.
    • `kPrime_support_subset` — `kPrime` is supported in `{0}`.
    • `hbulkderiv_fully_closed_K0` — ★★ `HasFDerivAt (fbulkInt …) (fderivBulkInt … x₀) x₀` at `K = {0}`,
      the fully-discharged `hbulkderiv` census member.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FderivBulkConcrete
import QIQTH.MixedEnvelopeFullyInhabitedCurved
import QIQTH.HZMassFullyClosedCurved

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.FderivBulkConcrete
open QIQTH.FrozenGermInternal
open QIQTH.MixedEnvelopeFullyInhabitedCurved
open QIQTH.HZMassFullyClosedCurved
open scoped Topology Interval BigOperators

namespace QIQTH.HbulkderivFullyClosedCurved

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the two null-singleton support facts at `K = {0}`.
    ############################################################################### -/

/-- **`bulkIntegrand_support_subset`.**  At `K = {0}` the scalar bulk integrand
    `z ↦ witnessFieldDeriv … x z · leviSeries … s z 0` is supported in the null singleton `{0}`:
    off `{0}` the field-`pd` factor vanishes (`witnessFieldDeriv_eqZero_of_base_notMem_K`). -/
theorem bulkIntegrand_support_subset (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b : ℝ) (i : Fin n) (t s : ℝ) (x : Point n) :
    Function.support
      (fun z => witnessFieldDeriv g gi hC
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i (t - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b)) s z 0)
      ⊆ ({(0 : Point n)} : Set (Point n)) := by
  intro z hz
  by_contra hzK
  rw [Function.mem_support] at hz
  apply hz
  rw [witnessFieldDeriv_eqZero_of_base_notMem_K g gi hC
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i (t - s) z hzK x,
    zero_mul]

/-- **`kPrime_support_subset`.**  At `K = {0}` the field-Fréchet kernel `z ↦ kPrime … x z` is supported
    in the null singleton `{0}` (`kPrime_eqZero_of_base_notMem_K`). -/
theorem kPrime_support_subset (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b : ℝ) (i : Fin n) (t s : ℝ) (x : Point n) :
    Function.support
      (fun z => kPrime g gi hC
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i t s x z)
      ⊆ ({(0 : Point n)} : Set (Point n)) := by
  intro z hz
  by_contra hzK
  rw [Function.mem_support] at hz
  exact hz (kPrime_eqZero_of_base_notMem_K g gi hC
    (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i t s x z hzK)

/-! ###############################################################################
    ### §2 — ★★ the fully-discharged `hbulkderiv` census member at `K = {0}`.
    ############################################################################### -/

/-- **★★ `hbulkderiv_fully_closed_K0`.**  THE `hbulkderiv` census member of the L2 sliver census — the
    concrete first-order Fréchet derivative `HasFDerivAt (fbulkInt … t i m) (fderivBulkInt … t i m x₀) x₀`
    — FULLY DISCHARGED at the genuinely-curved witness `K = {0}`, for ANY `g`, `gi`, gate `S`, gate
    scalars `a b`, any `0 < t`, `i`, `m`, `x₀`.  Every one of the ten per-slice carries of
    `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` is supplied from the null-singleton support facts of
    §1 (`boundz := 0`, `C := 0`).  DEGENERATE-`K` CAVEAT (honest, cf. J4-984/985/986): null-support
    driven, curved geometry does no substantive analytic work; this is the FIRST-order (single) Fréchet
    derivative only, so it does NOT close `hCConv` (which is `ContDiff ℝ ⊤`).  NON-VACUOUS: genuine
    `HasFDerivAt` conclusion, satisfiable data.  NOT `a₁ = R/6`. -/
theorem hbulkderiv_fully_closed_K0 (g gi : Point n → Fin n → Fin n → ℝ) (hn : 1 ≤ n)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ht : 0 < t) (i : Fin n) (m : ℕ) (x₀ : Point n) :
    HasFDerivAt
      (QIQTH.FrozenGermInternal.fbulkInt g gi hC
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b t i m)
      (QIQTH.FderivBulkConcrete.fderivBulkInt g gi hC
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b t i m x₀) x₀ := by
  classical
  have hn0 : 0 < n := by omega
  haveI : Inhabited (Fin n) := ⟨⟨0, hn0⟩⟩
  haveI : Nontrivial (Point n) := Pi.nontrivial
  set hK0 : IsCompact ({(0 : Point n)} : Set (Point n)) := isCompact_singleton with hK0def
  -- a.e. `z ≠ 0` (the null-singleton complement is co-null).
  have hzae : ∀ᵐ z ∂(volume : Measure (Point n)), z ∉ ({(0 : Point n)} : Set (Point n)) := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_mem_eq]
    exact measure_singleton 0
  -- 1. `hKint` — the bulk integrand is integrable (null-singleton support).
  have hKint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x ∈ (Set.univ : Set (Point n)), Integrable
        (fun z => witnessFieldDeriv g gi hC hK0 S a b i (t - s) x z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK0 S a b)) s z 0) volume :=
    ae_of_all volume (fun s _ x _ =>
      integrable_of_support_subset_singleton (μ := (volume : Measure (Point n))) _ (0 : Point n)
        (bulkIntegrand_support_subset g gi hC S a b i t s x))
  -- 2. `hKmeas` — the bulk integrand is a.e.-strongly-measurable.
  have hKmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x ∈ (Set.univ : Set (Point n)), AEStronglyMeasurable
        (fun z => witnessFieldDeriv g gi hC hK0 S a b i (t - s) x z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK0 S a b)) s z 0) volume :=
    ae_of_all volume (fun s _ x _ =>
      aestronglyMeasurable_of_support_subset_singleton (μ := (volume : Measure (Point n))) _
        (0 : Point n) (bulkIntegrand_support_subset g gi hC S a b i t s x))
  -- 3. `hK'meas` — `kPrime` is a.e.-strongly-measurable.
  have hK'meas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x ∈ (Set.univ : Set (Point n)), AEStronglyMeasurable
        (fun z => kPrime g gi hC hK0 S a b i t s x z) volume :=
    ae_of_all volume (fun s _ x _ =>
      aestronglyMeasurable_of_support_subset_singleton (μ := (volume : Measure (Point n))) _
        (0 : Point n) (kPrime_support_subset g gi hC S a b i t s x))
  -- 4. `hK'bound` — `‖kPrime‖ ≤ 0` a.e. `z` (boundz := 0).
  have hK'bound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x ∈ (Set.univ : Set (Point n)),
        ‖kPrime g gi hC hK0 S a b i t s x z‖ ≤ (fun (_ : ℝ) (_ : Point n) => (0 : ℝ)) s z := by
    refine ae_of_all volume (fun s _ => ?_)
    filter_upwards [hzae] with z hz
    intro x _
    have hkp := kPrime_eqZero_of_base_notMem_K g gi hC hK0 S a b i t s x z hz
    simp [hkp]
  -- 5. `hboundz_int` — `Integrable 0`.
  have hboundz_int : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable ((fun (_ : ℝ) (_ : Point n) => (0 : ℝ)) s) volume :=
    ae_of_all volume (fun s _ => integrable_zero (Point n) ℝ (volume))
  -- the CLM-valued `∫z kPrime` vanishes (null-singleton support), a vector-valued fact.
  have hkPint0 : ∀ (s : ℝ) (x : Point n),
      (∫ z, kPrime g gi hC hK0 S a b i t s x z) = 0 := fun s x => by
    rw [integral_congr_ae (eqZero_ae_of_support_subset_singleton (μ := (volume : Measure (Point n)))
        (fun z => kPrime g gi hC hK0 S a b i t s x z) (0 : Point n)
        (kPrime_support_subset g gi hC S a b i t s x)), integral_zero]
  -- 6. `hd` — the field-slot map is identically `0` (hence differentiable) for a.e. `z`.
  have hd : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ᵐ z ∂volume,
      ∀ x ∈ (Set.univ : Set (Point n)),
        DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hC hK0 S a b i (t - s) y z) x := by
    refine ae_of_all volume (fun s _ => ?_)
    filter_upwards [hzae] with z hz
    intro x _
    have hfun : (fun y => witnessFieldDeriv g gi hC hK0 S a b i (t - s) y z)
        = (fun _ : Point n => (0 : ℝ)) :=
      funext (fun y => witnessFieldDeriv_eqZero_of_base_notMem_K g gi hC hK0 S a b i (t - s) z hz y)
    rw [hfun]
    exact differentiableAt_const 0
  -- 7. `hGmeas` — `s ↦ ∫z (integrand)` is a.e.-strongly-measurable (it is `≡ 0`).
  have hGmeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv g gi hC hK0 S a b i (t - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK0 S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (t - epsSeq m))) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hz0 : (fun s => ∫ z, witnessFieldDeriv g gi hC hK0 S a b i (t - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK0 S a b)) s z 0)
        = (fun _ => (0 : ℝ)) := by
      funext s
      exact integral_eq_zero_of_support_subset_singleton (μ := (volume : Measure (Point n))) _
        (0 : Point n) (bulkIntegrand_support_subset g gi hC S a b i t s x)
    rw [hz0]
    exact aestronglyMeasurable_const
  -- 8. `hGint` — `s ↦ ∫z (integrand at x₀)` is interval-integrable (it is `≡ 0`).
  have hGint : IntervalIntegrable
      (fun s => ∫ z, witnessFieldDeriv g gi hC hK0 S a b i (t - s) x₀ z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK0 S a b)) s z 0)
      volume 0 (t - epsSeq m) := by
    have hz0 : (fun s => ∫ z, witnessFieldDeriv g gi hC hK0 S a b i (t - s) x₀ z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK0 S a b)) s z 0)
        = (fun _ => (0 : ℝ)) := by
      funext s
      exact integral_eq_zero_of_support_subset_singleton (μ := (volume : Measure (Point n))) _
        (0 : Point n) (bulkIntegrand_support_subset g gi hC S a b i t s x₀)
    rw [hz0]
    exact intervalIntegrable_const
  -- 9. `hG'meas` — `s ↦ ∫z kPrime (at x₀)` is a.e.-strongly-measurable (it is `≡ 0`).
  have hG'meas : AEStronglyMeasurable
      (fun s => ∫ z, kPrime g gi hC hK0 S a b i t s x₀ z)
      (volume.restrict (Set.uIoc 0 (t - epsSeq m))) := by
    have hz0 : (fun s => ∫ z, kPrime g gi hC hK0 S a b i t s x₀ z)
        = (fun _ => (0 : Point n →L[ℝ] ℝ)) := by
      funext s
      exact hkPint0 s x₀
    rw [hz0]
    exact aestronglyMeasurable_const
  -- 10. `hG'bound` — `‖∫z kPrime‖ ≤ 0·(t−s)⁻¹` (the integral is `0`; `C := 0`).
  have hG'bound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x ∈ (Set.univ : Set (Point n)),
        ‖∫ z, kPrime g gi hC hK0 S a b i t s x z‖ ≤ (0 : ℝ) * (t - s)⁻¹ := by
    refine ae_of_all volume (fun s _ x _ => ?_)
    rw [hkPint0 s x, norm_zero]
    exact le_of_eq (zero_mul _).symm
  -- fire the concrete double-integral differentiation engine with all ten carries discharged.
  exact QIQTH.FderivBulkConcrete.fderivBulkInt_hasFDerivAt g gi hC hK0 S a b t ht i m x₀ 0
    (fun (_ : ℝ) (_ : Point n) => (0 : ℝ))
    hKint hKmeas hK'meas hK'bound hboundz_int hd hGmeas hGint hG'meas hG'bound

end QIQTH.HbulkderivFullyClosedCurved

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HbulkderivFullyClosedCurved
#print axioms bulkIntegrand_support_subset
#print axioms kPrime_support_subset
#print axioms hbulkderiv_fully_closed_K0
end AxiomChecks
