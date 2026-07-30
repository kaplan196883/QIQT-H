/-
  LaplaceBeltramiFiniteReg — the FINITE-REGULARITY (`ContDiffAt ℝ 2`) Laplace–Beltrami Leibniz rule.

  Brick R1 of the RECENTER campaign (docs/qg_roadmap/RECENTER_CAMPAIGN_PLAN.md) toward the
  unconditional `a₁ = R/6` heat-kernel coefficient.  The existing product-rule chain in
  `QIQTH.LaplaceBeltramiLeibniz` is stated at `ContDiff ℝ ⊤` regularity, but the q-centered pullback
  metric is only `ContDiffOn ℝ 2`, so the residual chain must be re-provable at finite (`C²`)
  regularity.  This file supplies that foundation: `C²`-hypothesis analogues of `pd_pd_mul` and
  `laplaceBeltrami_mul`.

  The two general-base-point `PdiffAt` extractors
    • `PdiffAt_of_contDiffAt`   : `ContDiffAt ℝ 1 f x → PdiffAt f i x`
    • `PdiffAt_pd_of_contDiffAt`: `ContDiffAt ℝ 2 f x → PdiffAt (fun y => pd f m y) l x`
  are the general-point ports of the existing at-`0` extractors
  (`RNCExpansion.PdiffAt_pd_zero_of_contDiffAt2`, `PullbackMetric.PdiffAt_pd_zero_of_contDiffAt2`);
  nothing about the base point `0` was special, so they port verbatim to an arbitrary `x`.  They are
  factored out as their own lemmas so later R-bricks reuse them.

  The two main theorems then reuse the EXACT proof skeletons of `pd_pd_mul` / `laplaceBeltrami_mul`
  with the `PdiffAt` facts swapped for their `C²` versions.  As verified in the original proofs, the
  metric / Christoffel data enter ONLY as VALUES at the base point `x` (`gi x i j`,
  `christoffel g gi k i j x`), never through their derivatives, so NO metric-regularity hypothesis is
  required for `laplaceBeltrami_mul_C2`.

  No axioms, no `sorry`, no vacuous hypotheses — the `C²` regularity of `f, h` (all first/second
  partials) and the symmetry of the inverse metric at `x` are all genuinely used.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.LaplaceBeltramiLeibniz

set_option maxHeartbeats 1600000

open Finset
open QIQTH.Curvature

namespace QIQTH.LaplaceBeltrami

variable {n : ℕ}

/-- Partial differentiability at `x` along `l` from Fréchet-differentiability at `x` (general base
    point; the `x`-parametrised port of the at-`0` helper). -/
theorem pdiffAt_of_differentiableAt (f : Point n → ℝ) (l : Fin n) (x : Point n)
    (hf : DifferentiableAt ℝ f x) : PdiffAt f l x := by
  have hx : DifferentiableAt ℝ f ((Function.update x l) (x l)) := by
    rw [Function.update_eq_self]; exact hf
  exact hx.comp (x l) (hasDerivAt_update x l (x l)).differentiableAt

/-- `PdiffAt` congruence on a neighbourhood: if `f = h` near `x`, then `PdiffAt h l x → PdiffAt f l x`
    (the coordinate restriction germs agree). -/
theorem PdiffAt_congr_nhds {f h : Point n → ℝ} (l : Fin n) (x : Point n)
    (hfh : ∀ᶠ y in nhds x, f y = h y) (H : PdiffAt h l x) : PdiffAt f l x := by
  unfold PdiffAt at *
  have htend : Filter.Tendsto (fun t => Function.update x l t) (nhds (x l)) (nhds x) := by
    have hc := (hasDerivAt_update x l (x l)).continuousAt.tendsto
    rw [Function.update_eq_self] at hc
    exact hc
  exact H.congr_of_eventuallyEq (htend.eventually hfh)

/-- `pd` congruence on a neighbourhood: if `f = h` near `x`, then `pd f i x = pd h i x`. -/
theorem pd_congr_nhds {f h : Point n → ℝ} (i : Fin n) (x : Point n)
    (hfh : ∀ᶠ y in nhds x, f y = h y) : pd f i x = pd h i x := by
  simp only [pd]
  apply Filter.EventuallyEq.deriv_eq
  have htend : Filter.Tendsto (fun t => Function.update x i t) (nhds (x i)) (nhds x) := by
    have hc := (hasDerivAt_update x i (x i)).continuousAt.tendsto
    rw [Function.update_eq_self] at hc
    exact hc
  exact htend.eventually hfh

/-- **First-partial extractor at `C¹`.**  One derivative gives the first partial:
    `ContDiffAt ℝ 1 f x → PdiffAt f i x`. -/
theorem PdiffAt_of_contDiffAt (f : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 1 f x) : PdiffAt f i x :=
  pdiffAt_of_differentiableAt f i x (hf.differentiableAt (by norm_num))

/-- **Second-partial extractor at `C²` (general base point).**  Two derivatives give the second
    partial: `ContDiffAt ℝ 2 f x → PdiffAt (fun y => pd f m y) l x`.  General-point port of the at-`0`
    `RNCExpansion.PdiffAt_pd_zero_of_contDiffAt2` — nothing about `0` was special. -/
theorem PdiffAt_pd_of_contDiffAt (f : Point n → ℝ) (m l : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 2 f x) : PdiffAt (fun y => pd f m y) l x := by
  have hfd2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdf_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := hf.eventually (by norm_num)
    filter_upwards [hev] with y hy using hy.differentiableAt (by norm_num)
  have e1 : (fun y => pd f m y) =ᶠ[nhds x]
      (fun y => (fderiv ℝ f y) (Pi.single m 1)) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f m y hy
  exact PdiffAt_congr_nhds l x e1
    (pdiffAt_of_differentiableAt _ l x (hfd2.clm_apply (differentiableAt_const _)))

/-- **The second-order coordinate Leibniz rule at `C²`** — the `ContDiffAt ℝ 2` analogue of
    `LaplaceBeltramiLeibniz.pd_pd_mul`.  Same conclusion, hypotheses weakened to `C²` at the point `x`. -/
theorem pd_pd_mul_C2 (f h : Point n → ℝ) (i j : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x) :
    pd (fun y => pd (fun z => f z * h z) j y) i x
      = pd (fun y => pd f j y) i x * h x + pd f j x * pd h i x
        + pd f i x * pd h j x + f x * pd (fun y => pd h j y) i x := by
  -- `C¹` facts derived from the `C²` hypotheses
  have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by norm_num)
  have hh1 : ContDiffAt ℝ 1 h x := hh.of_le (by norm_num)
  -- first partial of the product, on the germ at `x`
  have hstep : (fun y => pd (fun z => f z * h z) j y)
      =ᶠ[nhds x] (fun y => pd f j y * h y + f y * pd h j y) := by
    -- valid on the neighbourhood where both factors are differentiable
    have hf_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
      have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 1 f y := hf1.eventually (by norm_num)
      filter_upwards [hev] with y hy using hy.differentiableAt (by norm_num)
    have hh_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ h y := by
      have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 1 h y := hh1.eventually (by norm_num)
      filter_upwards [hev] with y hy using hy.differentiableAt (by norm_num)
    filter_upwards [hf_ev, hh_ev] with y hfy hhy
    exact pd_mul f h j y (pdiffAt_of_differentiableAt f j y hfy)
      (pdiffAt_of_differentiableAt h j y hhy)
  -- `∂_i` respects the germ equality, then distribute
  rw [pd_congr_nhds i x hstep,
      pd_add (fun y => pd f j y * h y) (fun y => f y * pd h j y) i x
        ((PdiffAt_pd_of_contDiffAt f j i x hf).mul (PdiffAt_of_contDiffAt h i x hh1))
        ((PdiffAt_of_contDiffAt f i x hf1).mul (PdiffAt_pd_of_contDiffAt h j i x hh)),
      pd_mul (fun y => pd f j y) h i x (PdiffAt_pd_of_contDiffAt f j i x hf)
        (PdiffAt_of_contDiffAt h i x hh1),
      pd_mul f (fun y => pd h j y) i x (PdiffAt_of_contDiffAt f i x hf1)
        (PdiffAt_pd_of_contDiffAt h j i x hh)]
  ring

/-- **The Laplace–Beltrami Leibniz product rule at `C²`** — the `ContDiffAt ℝ 2` analogue of
    `LaplaceBeltramiLeibniz.laplaceBeltrami_mul`.  Same conclusion.

    Genuine hypotheses: `f, h ∈ C²` at `x` (all first/second partials — via `pd_pd_mul_C2` and
    `pd_mul`) and symmetry of the inverse metric at `x` (`hgisymm`, used only to symmetrise the cross
    term into the factor `2`).  As in the `C^∞` version, the metric / Christoffel data enter only as
    VALUES at `x`, so NO metric-regularity hypothesis is needed. -/
theorem laplaceBeltrami_mul_C2 (g gi : Point n → Fin n → Fin n → ℝ) (f h : Point n → ℝ) (x : Point n)
    (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x)
    (hgisymm : ∀ i j, gi x i j = gi x j i) :
    laplaceBeltrami g gi (fun y => f y * h y) x
      = f x * laplaceBeltrami g gi h x + h x * laplaceBeltrami g gi f x
        + 2 * ∑ i, ∑ j, gi x i j * (pd f i x) * (pd h j x) := by
  classical
  have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by norm_num)
  have hh1 : ContDiffAt ℝ 1 h x := hh.of_le (by norm_num)
  -- (1) split the Christoffel contraction of a product
  have hksum : ∀ i j : Fin n,
      (∑ k, christoffel g gi k i j x * pd (fun z => f z * h z) k x)
        = h x * (∑ k, christoffel g gi k i j x * pd f k x)
          + f x * (∑ k, christoffel g gi k i j x * pd h k x) := by
    intro i j
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_mul f h k x (PdiffAt_of_contDiffAt f k x hf1) (PdiffAt_of_contDiffAt h k x hh1)]
    ring
  -- (2) termwise algebraic split of the Laplace–Beltrami summand of a product
  have hterm : ∀ i j : Fin n,
      gi x i j * (pd (fun y => pd (fun z => f z * h z) j y) i x
          - ∑ k, christoffel g gi k i j x * pd (fun z => f z * h z) k x)
        = h x * (gi x i j * (pd (fun y => pd f j y) i x
              - ∑ k, christoffel g gi k i j x * pd f k x))
          + f x * (gi x i j * (pd (fun y => pd h j y) i x
              - ∑ k, christoffel g gi k i j x * pd h k x))
          + gi x i j * (pd f j x * pd h i x + pd f i x * pd h j x) := by
    intro i j
    rw [pd_pd_mul_C2 f h i j x hf hh, hksum i j]; ring
  -- (3) symmetrisation of the cross term into the factor 2
  have hcross : (∑ i, ∑ j, gi x i j * (pd f j x * pd h i x + pd f i x * pd h j x))
      = 2 * ∑ i, ∑ j, gi x i j * pd f i x * pd h j x := by
    have hsplit : (∑ i, ∑ j, gi x i j * (pd f j x * pd h i x + pd f i x * pd h j x))
        = (∑ i, ∑ j, gi x i j * (pd f j x * pd h i x))
          + (∑ i, ∑ j, gi x i j * (pd f i x * pd h j x)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hfirst : (∑ i, ∑ j, gi x i j * (pd f j x * pd h i x))
        = ∑ i, ∑ j, gi x i j * pd f i x * pd h j x := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hgisymm j i]; ring
    have hsecond : (∑ i, ∑ j, gi x i j * (pd f i x * pd h j x))
        = ∑ i, ∑ j, gi x i j * pd f i x * pd h j x :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, hfirst, hsecond]; ring
  -- (4) factor `h x`, `f x` out of the collected Δ_g f, Δ_g h double sums
  have eP : (∑ i, ∑ j, h x * (gi x i j * (pd (fun y => pd f j y) i x
        - ∑ k, christoffel g gi k i j x * pd f k x)))
      = h x * ∑ i, ∑ j, gi x i j * (pd (fun y => pd f j y) i x
        - ∑ k, christoffel g gi k i j x * pd f k x) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
  have eQ : (∑ i, ∑ j, f x * (gi x i j * (pd (fun y => pd h j y) i x
        - ∑ k, christoffel g gi k i j x * pd h k x)))
      = f x * ∑ i, ∑ j, gi x i j * (pd (fun y => pd h j y) i x
        - ∑ k, christoffel g gi k i j x * pd h k x) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
  -- assemble
  simp only [laplaceBeltrami]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm i j]
  simp only [Finset.sum_add_distrib]
  rw [eP, eQ, hcross]
  ring

end QIQTH.LaplaceBeltrami
