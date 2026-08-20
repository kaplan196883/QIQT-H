/-
  HbintReducedToZContinuity — J4-876: the `hbint` field of `MixedDirectionsFieldHessianEnvelope`
  (per-slice `z`-integrability of the product dominator `BL·BF` at the CONCRETE envelope
  `BF s z := ⨆ x, ‖fderiv …‖`) REDUCED to its true residual — the `z`-CONTINUITY of the product
  envelope on the compact base support `K` — via the banked compact-support fact (J4-867).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick REDUCES the `hbint` field of
  the envelope to a `z`-continuity residual; it does **NOT** fully close `hbint`.  No `sorry`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing
  file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ⚠ THE HONEST FINDING — `hbint` does NOT close via the `hFd` continuous-on-compact pattern.

  J4-874 (`HFdCoreContinuityClosed`) closed `hFd` by proving the field-Hessian norm
  `x ↦ ‖fderiv (y ↦ witnessFieldDeriv … y z) x‖` is `ContinuousOn` the compact CORE — continuity in the
  **FIELD variable `x`, for FIXED base `z`** (giving, per `z`, `BddAbove` of the `x`-sup, i.e. the `⨆`
  is a genuine upper bound).  `hbint` is a DIFFERENT object: `Integrable (z ↦ BL s z · BF s z)` over the
  **BASE variable `z`**, where `BF s z := ⨆ x, ‖fderiv …‖` is itself an (uncountable) `x`-supremum.
  Closing it needs (A) `z`-MEASURABILITY of that supremum and (B) a UNIFORM-in-`z` bound of `BF` over
  the compact `K` — both of which require JOINT `(x,z)` field-Hessian control (a parametrised-supremum /
  Berge–maximum argument), NOT the per-`z` `x`-continuity `hFd` used.  This is a genuinely different (and
  harder) analytic object; the "same pattern as `hFd`" premise does not transfer.  (Consistent with the
  codebase's own firewall: `BFGaussianEnvelopeClosed` lists `hbint` as still-needed, and its
  `bf_no_uniform_gaussian_decay` no-go rules out the naive `z`-decaying envelope route.)

  ## WHAT THIS BRICK DOES — the honest reduction (isolates the true residual).

  What DOES transfer cleanly is the COMPACT-SUPPORT half.  `BF` vanishes off `K`
  (`HZMassIntegrabilityAttempt.BF_ciSup_eqZero_of_base_notMem_K`), so the product `z ↦ BL s z · BF s z`
  is supported in the compact `K` (`productEnvelope_support_subset_K`, J4-867).  A compact-support
  function is integrable over the (infinite-measure) whole space AS SOON AS it is integrable on `K`,
  and `ContinuousOn … K` on a compact `K` (finite Lebesgue measure) delivers exactly that
  (`ContinuousOn.integrableOn_compact`).  So this brick proves:

    `hbint`  ⟸  (a.e. `s ∈ uIoc 0 (t−εₘ)`)  `ContinuousOn (z ↦ BL s z · BF s z) K`.

  The residual `ContinuousOn (z ↦ BL s z · BF s z) K` is the honest remaining content of `hbint` — the
  `z`-continuity (Berge parametrised-supremum) of the concrete envelope on its compact support.  It is
  SATISFIABLE (empty gate ⟹ `BF ≡ 0`; or `BL ≡ 0` ⟹ product `≡ 0`, both `ContinuousOn` trivially) and is
  never the conclusion.  A strictly weaker `measurable + bounded-on-K` variant is also provided.  So
  `hbint` is REDUCED (its integrability scaffolding discharged), NOT closed; the deep `hzmass` Gaussian
  `z`-mass wall remains, and this brick's `z`-continuity residual is an additional (distinct) sub-wall of
  `hbint`.  NOT `a₁ = R/6`.

  ## WHAT LANDS (ns `QIQTH.HbintReducedToZContinuity`).
    • `integrable_of_continuousOn_support_subset` — ★ the generic engine: `ContinuousOn f K` + `K`
      compact + `support f ⊆ K` ⟹ `Integrable f volume`.
    • `integrable_of_bounded_measurable_support_subset` — ★ the weaker variant: `AEStronglyMeasurable f`
      + `support f ⊆ K` + `|f| ≤ M` on `K` ⟹ `Integrable f volume`.
    • `hbint_of_zContinuousOn_K` — ★★★ the `hbint` field REDUCED a.e. to the `z`-continuity residual.
    • `hbint_of_zBoundedMeasurable_K` — ★★★ the `hbint` field REDUCED a.e. to the weaker
      `z`-measurable + bounded-on-`K` residual.
    • `hbint_residual_nonvacuous` — the `z`-continuity residual is inhabited (empty gate).
-/
import Mathlib
import QIQTH.HZMassIntegrabilityAttempt

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open scoped Topology BigOperators

namespace QIQTH.HbintReducedToZContinuity

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### C0 — the generic compact-support integrability engines.
    ############################################################################### -/

/-- **★ `integrable_of_continuousOn_support_subset`.**  A function `f : Point n → ℝ` that is
    `ContinuousOn` a COMPACT set `K` and SUPPORTED in `K` is `Integrable` over the whole (infinite
    Lebesgue measure) space: `ContinuousOn.integrableOn_compact` gives `IntegrableOn f K` (compact ⟹
    finite measure), and `support f ⊆ K` upgrades `IntegrableOn f K` to `Integrable f`
    (`f = K.indicator f`, `integrable_indicator_iff`).  NOT `a₁ = R/6`. -/
theorem integrable_of_continuousOn_support_subset
    {K : Set (Point n)} (hK : IsCompact K) (f : Point n → ℝ)
    (hcont : ContinuousOn f K) (hsupp : Function.support f ⊆ K) :
    Integrable f volume := by
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hIntOn : IntegrableOn f K volume := hcont.integrableOn_compact hK
  have hind : K.indicator f = f := Set.indicator_eq_self.mpr hsupp
  rw [← hind]
  exact (integrable_indicator_iff hKmeas).mpr hIntOn

/-- **★ `integrable_of_bounded_measurable_support_subset`.**  The strictly-weaker variant: a function
    `f : Point n → ℝ` that is `AEStronglyMeasurable`, SUPPORTED in a COMPACT `K`, and BOUNDED by `M` on
    `K`, is `Integrable`.  Off `K` the value is `0` (`support ⊆ K`), so the a.e. bound `‖f‖ ≤ M·𝟙_K`
    holds everywhere; the dominator `M·𝟙_K` is integrable (`K` finite measure), and `Integrable.mono'`
    concludes.  NOT `a₁ = R/6`. -/
theorem integrable_of_bounded_measurable_support_subset
    {K : Set (Point n)} (hK : IsCompact K) (f : Point n → ℝ) (M : ℝ)
    (hmeas : AEStronglyMeasurable f volume) (hsupp : Function.support f ⊆ K)
    (hbdd : ∀ z ∈ K, ‖f z‖ ≤ M) :
    Integrable f volume := by
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hKfin : volume K < ⊤ := hK.measure_lt_top
  -- dominator `g := |M| · 𝟙_K`, integrable (`|M| ≥ 0` unconditionally, avoiding an empty-`K` case).
  have hgint : Integrable (fun z => |M| * Set.indicator K (fun _ => (1 : ℝ)) z) volume :=
    ((integrable_indicator_iff hKmeas).mpr (integrableOn_const hKfin.ne)).const_mul |M|
  refine hgint.mono' hmeas ?_
  refine ae_of_all _ (fun z => ?_)
  by_cases hz : z ∈ K
  · rw [Set.indicator_of_mem hz, mul_one]
    exact le_trans (hbdd z hz) (le_abs_self M)
  · have hz0 : f z = 0 := by
      by_contra hne; exact hz (hsupp (by simpa [Function.mem_support] using hne))
    rw [hz0, norm_zero, Set.indicator_of_notMem hz, mul_zero]

/-! ###############################################################################
    ### C1 — the `hbint` field, REDUCED a.e. to the `z`-continuity residual.
    ############################################################################### -/

/-- **★★★ J4-876 — `hbint_of_zContinuousOn_K`.**  The EXACT `hbint` field of
    `MixedDirectionsFieldHessianEnvelope`, at the CONCRETE envelope
    `BF s z := ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … i (t−s) y z) x‖`, REDUCED a.e. to the single
    residual: a.e. `s`, the product envelope `z ↦ BL s z · BF s z` is `ContinuousOn` the compact base
    support `K`.  The product is supported in `K` (`productEnvelope_support_subset_K`, J4-867), so
    `integrable_of_continuousOn_support_subset` converts the `z`-continuity to full integrability over
    the (infinite-measure) whole space.  This DISCHARGES the integrability scaffolding of `hbint`; the
    honest remaining content is the `z`-continuity (Berge parametrised-supremum) itself — a DISTINCT
    residual from the deep `hzmass` Gaussian `z`-mass wall.  NOT `a₁ = R/6`. -/
theorem hbint_of_zContinuousOn_K (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (BL : ℝ → Point n → ℝ)
    (hcont : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ContinuousOn (fun z => BL s z *
          (⨆ x : Point n,
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) K) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z => BL s z *
        (⨆ x : Point n,
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume := by
  filter_upwards [hcont] with s hconts hsU
  exact integrable_of_continuousOn_support_subset hK _ (hconts hsU)
    (productEnvelope_support_subset_K g gi hC hK S a b i (t - s) BL s)

/-- **★★★ J4-876 — `hbint_of_zBoundedMeasurable_K`.**  The `hbint` field REDUCED a.e. to the strictly
    WEAKER residual: a.e. `s`, the product envelope `z ↦ BL s z · BF s z` is `AEStronglyMeasurable` and
    BOUNDED by some `M s` on the compact `K`.  Same compact-support route via
    `integrable_of_bounded_measurable_support_subset`.  (Weaker/easier to discharge than the
    `ContinuousOn` residual, since it asks only for a `z`-measurable envelope with a uniform-on-`K`
    bound — the two genuine sub-obstructions of `hbint`.)  NOT `a₁ = R/6`. -/
theorem hbint_of_zBoundedMeasurable_K (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (BL : ℝ → Point n → ℝ) (M : ℝ → ℝ)
    (hmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        AEStronglyMeasurable (fun z => BL s z *
          (⨆ x : Point n,
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume)
    (hbdd : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z ∈ K, ‖BL s z *
          (⨆ x : Point n,
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)‖ ≤ M s) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z => BL s z *
        (⨆ x : Point n,
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume := by
  filter_upwards [hmeas, hbdd] with s hmeass hbdds hsU
  exact integrable_of_bounded_measurable_support_subset hK _ (M s) (hmeass hsU)
    (productEnvelope_support_subset_K g gi hC hK S a b i (t - s) BL s) (hbdds hsU)

/-! ###############################################################################
    ### C2 — NON-VACUITY of the residual.
    ############################################################################### -/

/-- **NON-VACUITY.**  The `z`-continuity residual of `hbint_of_zContinuousOn_K` is inhabited at the empty
    gate `S := fun _ => ∅` with `BL := fun _ _ => 0`: the product is identically `0`, hence `ContinuousOn`
    every set (in particular `K`).  So the reduction fires — no unsatisfiable antecedent (no J4-548/847
    trap).  (The genuinely non-trivial residual — `z`-continuity of the concrete `⨆`-envelope — is the
    honest Berge parametrised-supremum content that remains open.)  NOT `a₁ = R/6`. -/
theorem hbint_residual_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t : ℝ) (m : ℕ) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ContinuousOn (fun z => (fun _ _ => (0 : ℝ)) s z *
        (⨆ x : Point n,
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n)))
            a b i (t - s) y z) x‖)) K := by
  refine ae_of_all _ (fun s _ => ?_)
  simpa using (continuousOn_const : ContinuousOn (fun _ : Point n => (0 : ℝ)) K)

end QIQTH.HbintReducedToZContinuity

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HbintReducedToZContinuity
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms integrable_of_continuousOn_support_subset
#print axioms integrable_of_bounded_measurable_support_subset
#print axioms hbint_of_zContinuousOn_K
#print axioms hbint_of_zBoundedMeasurable_K
#print axioms hbint_residual_nonvacuous
end AxiomChecks
