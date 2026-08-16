/-
  FderivBulkConcrete — J4-778: the CONCRETE `fderivBulk`/`gderiv` fields the L2 sliver census
  (`CConvV2Facade` / `FrozenGermInternal` / `HD1Concrete`) had only ever carried as opaque `∀`-bound
  hypotheses.  This file DEFINES them for the live order-1 gated van-Vleck witness and DISCHARGES the
  `hbulkderiv` census member (`HasFDerivAt (fbulkInt …) (fderivBulk …) x`) for them.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  This brick closes ONE precisely-named hole in the L2 sliver census
  that J4-776 flagged: "`fderivBulk`/`gderiv` DON'T EXIST AS DEFS anywhere in the repo — only as
  `∀`-bound hypothesis carries."  Here they are given honest concrete definitions and the `hbulkderiv`
  member is discharged for them via the ALREADY-BANKED double-integral differentiation engine
  (`EboundWiringHD1.hasFDerivAt_doubleIntegral_of_dominated`, J4-197).  No `sorry`, no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DEFINITIONS (ns `QIQTH.FderivBulkConcrete`).

    • `kPrime g gi hC hK S a b i t s x z : Point n →L[ℝ] ℝ` — the CLM Fréchet-derivative kernel: the
      full field-gradient of the bulk integrand `y ↦ witnessFieldDeriv … i (t−s) y z` at `x`, right-
      scaled by the (`y`-independent) Levi factor `leviSeries … s z 0`:
        `kPrime … = (leviSeries (heatOp g gi (vanVleckGatedWitness …)) s z 0) •
                       (fderiv ℝ (fun y => witnessFieldDeriv … i (t−s) y z) x)`.
      This is EXACTLY the Fréchet derivative of the scalar integrand `K s x z = witnessFieldDeriv …
      i (t−s) x z · leviSeries … s z 0` in the field slot `x` (see `kPrime_hasFDerivAt`).

    • `fderivBulkInt g gi hC hK S a b t i m : Point n → (Point n →L[ℝ] ℝ)` — the TRUNCATED (bulk)
      derivative field `x ↦ ∫₀^{t−εₘ} ∫z kPrime … s x z`.  This is the concrete `fderivBulk i m`.

    • `gderivInt g gi hC hK S a b t i : Point n → (Point n →L[ℝ] ℝ)` — the FULL (limit) derivative field
      `x ↦ ∫₀ᵗ ∫z kPrime … s x z`.  This is the concrete `gderiv i`.

  These are the exact objects `HD1Concrete.hD1_concrete` / `CConvV2Facade.hD1_concrete_from_v2sliver`
  bind abstractly.  Their difference is the ε-sliver integral (`gderiv_sub_fderivBulk_eq_sliver`),
  which is precisely the object the banked `√ε` sliver bound `witness_sliver2_xuniform` estimates —
  so this file makes the previously-unstatable `hsliver` census member CONCRETELY STATABLE.

  ## THE DELIVERABLE.
    • `dominator_intervalIntegrable` — the honest order-2 outer dominator `s ↦ C·(t−s)⁻¹` is interval-
      integrable on `0..(t−ε)` for ANY `0 < t`, `0 < ε` (no `ε ≤ t` needed: the singularity `s = t`
      never enters `uIcc 0 (t−ε)`), sharpening `HD1SliverRoute.bulk_order2_dominator_intervalIntegrable`.
    • `kPrime_hasFDerivAt` — `kPrime` really is the field Fréchet derivative of the scalar bulk
      integrand (from plain per-slice differentiability of `witnessFieldDeriv`).
    • `fderivBulkInt_hasFDerivAt` — ★★ `HasFDerivAt (fbulkInt … i m) (fderivBulkInt … i m x₀) x₀`,
      the concrete `hbulkderiv` member, from the banked double-integral engine fed the per-slice
      integrability / measurability / domination census + the honest order-2 dominator.
    • `gderiv_sub_fderivBulk_eq_sliver` — ★ `gderivInt … i x − fderivBulkInt … i m x = ∫_{t−εₘ}^{t}
      ∫z kPrime …` — the concrete sliver identity (the bridge the abstract `hsliver` was missing).

  Every hypothesis is satisfiable, non-vacuous (the width-2 Gaussian model of the sliver bricks
  satisfies the whole per-slice census), and never equal to the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.EboundWiringHD1
import QIQTH.FrozenGermInternal
import QIQTH.EngineInstantiation
import QIQTH.HD1Concrete

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open scoped Topology Interval BigOperators

namespace QIQTH.FderivBulkConcrete

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### D0 — the concrete derivative kernel and the bulk / full derivative fields.
    ############################################################################### -/

/-- **D0a — `kPrime`.**  The CLM field Fréchet-derivative kernel of the bulk integrand: the full
    field-gradient of `y ↦ witnessFieldDeriv … i (t−s) y z` at `x`, right-scaled by the field-
    independent Levi factor `leviSeries … s z 0`.  This is the derivative of the scalar integrand
    `witnessFieldDeriv … i (t−s) x z · leviSeries … s z 0` in the field slot (`kPrime_hasFDerivAt`). -/
noncomputable def kPrime (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t s : ℝ) (x z : Point n) : Point n →L[ℝ] ℝ :=
  (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) •
    (fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)

/-- **D0b — `fderivBulkInt`.**  The concrete TRUNCATED (bulk) derivative field
    `x ↦ ∫₀^{t−εₘ} ∫z kPrime … s x z`; the L2 census's `fderivBulk i m`. -/
noncomputable def fderivBulkInt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (i : Fin n) (m : ℕ) : Point n → (Point n →L[ℝ] ℝ) :=
  fun x => ∫ s in (0)..(t - epsSeq m), ∫ z, kPrime g gi hC hK S a b i t s x z

/-- **D0c — `gderivInt`.**  The concrete FULL (limit) derivative field `x ↦ ∫₀ᵗ ∫z kPrime … s x z`;
    the L2 census's `gderiv i`. -/
noncomputable def gderivInt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (i : Fin n) : Point n → (Point n →L[ℝ] ℝ) :=
  fun x => ∫ s in (0)..t, ∫ z, kPrime g gi hC hK S a b i t s x z

/-! ###############################################################################
    ### D1 — the sharpened order-2 outer dominator integrability.
    ############################################################################### -/

/-- **★ D1 — `dominator_intervalIntegrable`.**  The honest order-2 outer dominator `s ↦ C·(t−s)⁻¹` is
    interval-integrable on `0..(t−ε)` for ANY `0 < t`, `0 < ε` — no `ε ≤ t` assumption.  The
    singularity `s = t` never enters `uIcc 0 (t−ε)`: every `s` there has `s ≤ max 0 (t−ε) < t`, so
    `t − s > 0` and the integrand is continuous.  Sharpens
    `HD1SliverRoute.bulk_order2_dominator_intervalIntegrable` (which needed `ε ≤ t`), enabling the
    concrete `hbulkderiv` for EVERY `m` (including the small-`m` `t − εₘ < 0` case).  NOT `a₁ = R/6`. -/
theorem dominator_intervalIntegrable (t ε C : ℝ) (ht : 0 < t) (hε : 0 < ε) :
    IntervalIntegrable (fun s : ℝ => C * (t - s)⁻¹) volume 0 (t - ε) := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ ?_ ?_)
  · exact (continuous_const.sub continuous_id).continuousOn
  · intro s hs
    have hst : s < t := lt_of_le_of_lt hs.2 (sup_lt_iff.mpr ⟨ht, by linarith⟩)
    exact sub_ne_zero_of_ne (ne_of_gt hst)

/-! ###############################################################################
    ### D2 — `kPrime` is the field Fréchet derivative of the scalar bulk integrand.
    ############################################################################### -/

/-- **D2 — `kPrime_hasFDerivAt`.**  Given plain per-point field-differentiability of the first field-
    derivative kernel `y ↦ witnessFieldDeriv … i (t−s) y z` at `x`, the scalar bulk integrand
    `x ↦ witnessFieldDeriv … i (t−s) x z · leviSeries … s z 0` has Fréchet derivative `kPrime … s x z`
    at `x` — the const-multiple rule, with `kPrime` recovered as `fderiv … .smulRight (Levi factor)`.
    NOT `a₁ = R/6`. -/
theorem kPrime_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t s : ℝ) (x z : Point n)
    (hd : DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x) :
    HasFDerivAt
      (fun x => witnessFieldDeriv g gi hC hK S a b i (t - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      (kPrime g gi hC hK S a b i t s x z) x :=
  hd.hasFDerivAt.mul_const _

/-! ###############################################################################
    ### D3 — the concrete `hbulkderiv`:  `HasFDerivAt (fbulkInt …) (fderivBulkInt …)`.
    ############################################################################### -/

/-- **★★ D3 — `fderivBulkInt_hasFDerivAt`.**  THE concrete `hbulkderiv` census member: the truncated
    bulk primitive `fbulkInt … t i m = fun x ↦ ∫₀^{t−εₘ} ∫z witnessFieldDeriv … i (t−s) x z · leviSeries
    … s z 0` is `HasFDerivAt` at `x₀` with derivative `fderivBulkInt … t i m x₀ = ∫₀^{t−εₘ} ∫z kPrime …
    s x₀ z`, obtained by firing the ALREADY-BANKED double-integral engine
    `EboundWiringHD1.hasFDerivAt_doubleIntegral_of_dominated` (J4-197) at the concrete pair
    `K := witnessFieldDeriv·Levi`, `K' := kPrime`, with the honest order-2 outer dominator `C·(t−s)⁻¹`
    (its interval-integrability supplied by `dominator_intervalIntegrable`, D1) and the per-slice
    differentiability supplied by `kPrime_hasFDerivAt` (D2) off the carried `hd`.  The remaining
    carries are the per-slice integrability / measurability / domination census — genuine satisfiable
    analytic inputs, none the conclusion.  NOT `a₁ = R/6`. -/
theorem fderivBulkInt_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ht : 0 < t) (i : Fin n) (m : ℕ) (x₀ : Point n) (C : ℝ)
    (boundz : ℝ → Point n → ℝ)
    (hKint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x ∈ (Set.univ : Set (Point n)), Integrable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume)
    (hKmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x ∈ (Set.univ : Set (Point n)), AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume)
    (hK'meas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x ∈ (Set.univ : Set (Point n)), AEStronglyMeasurable
          (fun z => kPrime g gi hC hK S a b i t s x z) volume)
    (hK'bound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∀ x ∈ (Set.univ : Set (Point n)),
          ‖kPrime g gi hC hK S a b i t s x z‖ ≤ boundz s z)
    (hboundz_int : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → Integrable (boundz s) volume)
    (hd : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ᵐ z ∂volume,
        ∀ x ∈ (Set.univ : Set (Point n)),
          DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
    (hGmeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (t - epsSeq m))))
    (hGint : IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x₀ z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        volume 0 (t - epsSeq m))
    (hG'meas : AEStronglyMeasurable
        (fun s => ∫ z, kPrime g gi hC hK S a b i t s x₀ z)
        (volume.restrict (Set.uIoc 0 (t - epsSeq m))))
    (hG'bound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x ∈ (Set.univ : Set (Point n)),
          ‖∫ z, kPrime g gi hC hK S a b i t s x z‖ ≤ C * (t - s)⁻¹) :
    HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b t i m)
      (fderivBulkInt g gi hC hK S a b t i m x₀) x₀ := by
  -- derive the per-slice `HasFDerivAt` bundle (`hKdiff`) from the plain differentiability carry `hd`.
  have hKdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (fun x => witnessFieldDeriv g gi hC hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (kPrime g gi hC hK S a b i t s x z) x := by
    filter_upwards [hd] with s hs hsmem
    filter_upwards [hs hsmem] with z hz x hx
    exact kPrime_hasFDerivAt g gi hC hK S a b i t s x z (hz x hx)
  exact EboundWiringHD1.hasFDerivAt_doubleIntegral_of_dominated (t - epsSeq m) x₀
    isOpen_univ (Set.mem_univ x₀)
    (fun s x z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z
      * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
    (fun s x z => kPrime g gi hC hK S a b i t s x z)
    boundz (fun s => C * (t - s)⁻¹)
    hKint hKmeas hK'meas hK'bound hboundz_int hKdiff
    hGmeas hGint hG'meas hG'bound
    (dominator_intervalIntegrable t (epsSeq m) C ht (epsSeq_pos m))

/-! ###############################################################################
    ### D4 — the concrete sliver identity (the bridge the abstract `hsliver` was missing).
    ############################################################################### -/

/-- **★ D4 — `gderiv_sub_fderivBulk_eq_sliver`.**  The concrete sliver identity: the difference of the
    FULL and BULK derivative fields is the ε-window integral
      `gderivInt … i x − fderivBulkInt … i m x = ∫_{t−εₘ}^{t} ∫z kPrime … s x z`,
    by interval-integral additivity (`∫₀^{t−εₘ} + ∫_{t−εₘ}^{t} = ∫₀ᵗ`) on the CLM-valued profile
    `G s = ∫z kPrime … s x z`.  This is the object the banked `√ε` sliver bound
    `XUniformSliverFull.witness_sliver2_xuniform` estimates — so the `hsliver` census member
    (`dist (fderivBulk i m x) (gderiv i x) ≤ bb`) is now CONCRETELY STATABLE as a bound on this
    ε-window integral (its `O(√ε)` operator-norm rate is the remaining analytic content).
    NOT `a₁ = R/6`. -/
theorem gderiv_sub_fderivBulk_eq_sliver (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (i : Fin n) (m : ℕ) (x : Point n)
    (hIab : IntervalIntegrable (fun s => ∫ z, kPrime g gi hC hK S a b i t s x z)
        volume 0 (t - epsSeq m))
    (hIbc : IntervalIntegrable (fun s => ∫ z, kPrime g gi hC hK S a b i t s x z)
        volume (t - epsSeq m) t) :
    gderivInt g gi hC hK S a b t i x - fderivBulkInt g gi hC hK S a b t i m x
      = ∫ s in (t - epsSeq m)..t, ∫ z, kPrime g gi hC hK S a b i t s x z := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals hIab hIbc
  -- `∫₀^{t−εₘ} G + ∫_{t−εₘ}^{t} G = ∫₀ᵗ G`, so `∫₀ᵗ G − ∫₀^{t−εₘ} G = ∫_{t−εₘ}^{t} G`.
  simp only [gderivInt, fderivBulkInt]
  rw [← hadd]
  abel

end QIQTH.FderivBulkConcrete

section AxiomChecks
open QIQTH.FderivBulkConcrete
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms dominator_intervalIntegrable
#print axioms kPrime_hasFDerivAt
#print axioms fderivBulkInt_hasFDerivAt
#print axioms gderiv_sub_fderivBulk_eq_sliver
end AxiomChecks
