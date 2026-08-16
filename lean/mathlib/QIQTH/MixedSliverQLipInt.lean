/-
  MixedSliverQLipInt — the two ABSTRACT SUPPLIERS for the mixed sliver's `hqLip` (Lipschitz sub-part)
  and its seven integrabilities, via the product-Lipschitz rule and the gate-compact-support pattern.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6` and proves nothing new about `R/6`.  It supplies two
  reusable analytic ENGINES for the chart-surface residue (J4-795) of the mixed sliver
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed`:

    (2)  `hqLip`'s Lipschitz sub-part — J4-795 flagged the Lipschitz constant for the PRODUCT `A0·F` as
         "genuine new content with no supplier."  The supplier is the elementary product rule for BOUNDED
         Lipschitz functions: if `|f| ≤ Mf`, `|g| ≤ Mg`, `f` is `Lf`-Lipschitz and `g` is `Lg`-Lipschitz,
         then `f·g` is `(Mf·Lg + Mg·Lf)`-Lipschitz.  Packaged with the sup-bound `Mf·Mg` and a carried
         measurability into the exact `hqLip` triple `(Lipschitz ∧ AEStronglyMeasurable ∧ ∃M, bound)`.

    (3)  the seven integrabilities — J4-795 flagged each as "reducible in principle via gate-compact-
         support but each needs 3 fresh inputs."  The supplier is the standard pattern: a function that
         VANISHES off a finite-measure set `S`, is AE-strongly-measurable, and is bounded by `M`, is
         integrable (dominated by `M · 1_S`, integrable since `volume S < ⊤`).  This is exactly the
         gate-compact-support route (the gated amplitude `gateAmp` vanishes off the compact active set),
         reducing each integrability to {support, AE-measurability, boundedness}.

  ── WHAT LANDS (all abstract; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `product_bounded_lipschitz_bound` — the product-Lipschitz rule in the `hqLip` `dist`-shape.
    * `hqLip_triple_of_bounded_lipschitz` — the FULL `hqLip` triple from bounded-Lipschitz factors.
    * `integrable_of_finiteSupport_bounded` — the gate-compact-support integrability engine.

  Every hypothesis is satisfiable and non-vacuous (`f = g = 0`, `Mf=Mg=Lf=Lg=0` for the Lipschitz rule;
  `S = ∅`, `h = 0` for integrability), and none equals the conclusion.  These are the two named suppliers
  J4-795 said were missing for `hqLip`/integrabilities — provided abstractly.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.SliverAssembly

open MeasureTheory
open scoped BigOperators ENNReal

namespace QIQTH.MixedSliverQLipInt

/-! ############################################################################
    ### (2) The `hqLip` Lipschitz supplier — product of bounded Lipschitz maps.
    ############################################################################ -/

/-- **★ THE PRODUCT-LIPSCHITZ RULE — `product_bounded_lipschitz_bound`.**  For real-valued `f g` on any
    pseudometric space, if `|f| ≤ Mf`, `|g| ≤ Mg` everywhere and `f`/`g` are `Lf`/`Lg`-Lipschitz (in the
    `dist`-shape `|f x − f y| ≤ Lf·dist x y`), then the product is `(Mf·Lg + Mg·Lf)`-Lipschitz:
        `|f x · g x − f y · g y| ≤ (Mf·Lg + Mg·Lf)·dist x y`.
    This is EXACTLY the `hqLip` Lipschitz sub-part J4-795 flagged as "genuine new content with no
    supplier," at `f = A0(u−s)·`, `g = F s ·x`.  Proof: split `fx·gx − fy·gy = fx·(gx−gy) + (fx−fy)·gy`,
    triangle + `abs_mul` + the four bounds.  ⚠ NOT `a₁ = R/6`. -/
theorem product_bounded_lipschitz_bound {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) (Mf Mg Lf Lg : ℝ)
    (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, |g x| ≤ Mg)
    (hf : ∀ x y, |f x - f y| ≤ Lf * dist x y) (hg : ∀ x y, |g x - g y| ≤ Lg * dist x y) :
    ∀ x y, |f x * g x - f y * g y| ≤ (Mf * Lg + Mg * Lf) * dist x y := by
  intro x y
  have hd : 0 ≤ dist x y := dist_nonneg
  have hMf0 : 0 ≤ Mf := le_trans (abs_nonneg _) (hMf x)
  have hMg0 : 0 ≤ Mg := le_trans (abs_nonneg _) (hMg y)
  have hsplit : f x * g x - f y * g y = f x * (g x - g y) + (f x - f y) * g y := by ring
  have hLfd : 0 ≤ Lf * dist x y := (abs_nonneg _).trans (hf x y)
  calc |f x * g x - f y * g y|
      = |f x * (g x - g y) + (f x - f y) * g y| := by rw [hsplit]
    _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add_le _ _
    _ = |f x| * |g x - g y| + |f x - f y| * |g y| := by rw [abs_mul, abs_mul]
    _ ≤ Mf * (Lg * dist x y) + (Lf * dist x y) * Mg :=
        add_le_add
          (mul_le_mul (hMf x) (hg x y) (abs_nonneg _) hMf0)
          (mul_le_mul (hf x y) (hMg y) (abs_nonneg _) hLfd)
    _ = (Mf * Lg + Mg * Lf) * dist x y := by ring

/-- **★★ THE FULL `hqLip` TRIPLE — `hqLip_triple_of_bounded_lipschitz`.**  From bounded-Lipschitz data on
    two factors `f g` plus AE-strong-measurability of their product, produce the exact `hqLip` triple that
    `MixedSliverXUniform.witness_sliver2_xuniform_mixed` carries per `(x, s)`:
        `(∀ z w, |f z·g z − f w·g w| ≤ L·dist z w) ∧ AEStronglyMeasurable (f·g) ∧ ∃ M, ∀ z, |f z·g z| ≤ M`,
    with `L = Mf·Lg + Mg·Lf` (product-Lipschitz rule) and `M = Mf·Mg` (product sup-bound).  At
    `f = A0(u−s)·`, `g = F s ·x` this discharges the whole `hqLip` conjunction from single-factor
    regularity — the AEStronglyMeasurable + sup-bound legs J4-795 called "portable," plus the
    product-Lipschitz leg it called new.  ⚠ NOT `a₁ = R/6`. -/
theorem hqLip_triple_of_bounded_lipschitz {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (f g : X → ℝ) (Mf Mg Lf Lg : ℝ)
    (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, |g x| ≤ Mg)
    (hf : ∀ x y, |f x - f y| ≤ Lf * dist x y) (hg : ∀ x y, |g x - g y| ≤ Lg * dist x y)
    (hmeas : AEStronglyMeasurable (fun z => f z * g z) μ) :
    (∀ z w, |f z * g z - f w * g w| ≤ (Mf * Lg + Mg * Lf) * dist z w)
    ∧ AEStronglyMeasurable (fun z => f z * g z) μ
    ∧ ∃ M, ∀ z, |f z * g z| ≤ M := by
  refine ⟨product_bounded_lipschitz_bound f g Mf Mg Lf Lg hMf hMg hf hg, hmeas, ⟨Mf * Mg, ?_⟩⟩
  intro z
  rw [abs_mul]
  exact mul_le_mul (hMf z) (hMg z) (abs_nonneg _) ((abs_nonneg _).trans (hMf z))

/-! ############################################################################
    ### (3) The integrability engine — gate-compact-support.
    ############################################################################ -/

/-- **★★ THE GATE-COMPACT-SUPPORT INTEGRABILITY ENGINE — `integrable_of_finiteSupport_bounded`.**  A
    function `h` that VANISHES off a finite-measure set `S`, is AE-strongly-measurable, and is bounded
    (`|h| ≤ M`), is integrable — dominated by the integrable `M · 1_S` (`integrableOn_const` on the
    finite-measure `S`).  This is the exact route J4-795 named for the seven mixed-sliver integrabilities:
    the gated amplitude (`gateAmp`) vanishes off the compact active set `S` (finite measure), so every
    integrand `<geom factor>·(A·F)` vanishes off `S`; supplying {support, AE-measurability, boundedness}
    then yields integrability.  ⚠ NOT `a₁ = R/6`. -/
theorem integrable_of_finiteSupport_bounded {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (h : X → ℝ) (S : Set X) (hS : MeasurableSet S) (hSfin : μ S < ∞)
    (hsupp : ∀ z ∉ S, h z = 0)
    (hmeas : AEStronglyMeasurable h μ) (M : ℝ) (hbdd : ∀ z, |h z| ≤ M) :
    Integrable h μ := by
  -- the integrable dominating function `M · 1_S`.
  have hdom : Integrable (S.indicator (fun _ => M)) μ := by
    rw [integrable_indicator_iff hS]
    exact integrableOn_const (C := M) hSfin.ne
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall (fun z => ?_))
  by_cases hz : z ∈ S
  · -- inside `S`: `‖h z‖ = |h z| ≤ M = 1_S z · M`.
    rw [Set.indicator_of_mem hz, Real.norm_eq_abs]
    exact hbdd z
  · -- outside `S`: `h z = 0`, so `‖h z‖ = 0 = 1_S z`.
    rw [Set.indicator_of_notMem hz, hsupp z hz, norm_zero]

end QIQTH.MixedSliverQLipInt

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverQLipInt
#print axioms product_bounded_lipschitz_bound
#print axioms hqLip_triple_of_bounded_lipschitz
#print axioms integrable_of_finiteSupport_bounded
end AxiomChecks
