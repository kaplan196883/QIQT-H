/-
  LaplaceBeltramiLeibniz — the Leibniz product rule for the Laplace–Beltrami operator.

  The THIRD brick of the C4c cutoff-parametrix far-field construction toward the unconditional
  `a₁ = R/6` heat-kernel coefficient.  It isolates the algebraic split

      `Δ_g(f·h) = f·Δ_g h + h·Δ_g f + 2·g^{ij} (∂_i f)(∂_j h)`

  of the Laplace–Beltrami operator on a product.  When `f = χ` is a radial cutoff and `h = H` a
  parametrix profile, the split turns the cutoff–parametrix residual `(∂_t − Δ_g)(χ·H)` into

      `χ·(∂_t − Δ_g)H  −  H·Δ_g χ  −  2·g^{ij}(∂_i χ)(∂_j H)`,

  where the last two terms (`H·Δ_g χ` and `2 g^{ij} ∂_i χ ∂_j H`) are **annulus-supported**: they
  vanish off the support of `∂χ`, i.e. away from the cutoff transition shell.  That localisation is
  exactly what feeds the far-field Gaussian bound for the C4c cutoff-parametrix residual.

  This file builds:
    • `pd_pd_mul` — the SECOND-order coordinate product rule
      `∂_i∂_j(f·h) = (∂_i∂_j f)·h + (∂_j f)(∂_i h) + (∂_i f)(∂_j h) + f·(∂_i∂_j h)`
      (the first-order `pd_mul` already lives in `QIQTH.Curvature`);
    • `laplaceBeltrami_mul` — the Leibniz product rule for `Δ_g`, with the cross term symmetrised to
      `2·g^{ij}(∂_i f)(∂_j h)` using symmetry of the inverse metric at the base point.

  It does NOT build the far-field bound, the annulus-support estimate, nor `a₁ = R/6`.  No axioms,
  no `sorry`, no vacuous hypotheses — the `C^∞` regularity of `f, h` and the symmetry of the inverse
  metric at `x` are all genuinely used.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.LaplaceBeltrami

set_option maxHeartbeats 1600000

open Finset
open QIQTH.Curvature

namespace QIQTH.LaplaceBeltrami

variable {n : ℕ}

/-- **The second-order coordinate Leibniz rule**
    `∂_i∂_j(f·h) = (∂_i∂_j f)·h + (∂_j f)(∂_i h) + (∂_i f)(∂_j h) + f·(∂_i∂_j h)`,
    for `C^∞` fields `f, h`.  Here the mixed second partial is `pd (fun y => pd · j y) i`.
    This is the analytic input for the Laplace–Beltrami Leibniz rule below. -/
theorem pd_pd_mul (f h : Point n → ℝ) (i j : Fin n) (x : Point n)
    (hf : ContDiff ℝ ⊤ f) (hh : ContDiff ℝ ⊤ h) :
    pd (fun y => pd (fun z => f z * h z) j y) i x
      = pd (fun y => pd f j y) i x * h x + pd f j x * pd h i x
        + pd f i x * pd h j x + f x * pd (fun y => pd h j y) i x := by
  have hstep : (fun y => pd (fun z => f z * h z) j y)
      = (fun y => pd f j y * h y + f y * pd h j y) := by
    funext y
    exact pd_mul f h j y (PdiffAt_of_contDiff f hf j y) (PdiffAt_of_contDiff h hh j y)
  rw [hstep,
      pd_add (fun y => pd f j y * h y) (fun y => f y * pd h j y) i x
        ((PdiffAt_pd f hf j i x).mul (PdiffAt_of_contDiff h hh i x))
        ((PdiffAt_of_contDiff f hf i x).mul (PdiffAt_pd h hh j i x)),
      pd_mul (fun y => pd f j y) h i x (PdiffAt_pd f hf j i x) (PdiffAt_of_contDiff h hh i x),
      pd_mul f (fun y => pd h j y) i x (PdiffAt_of_contDiff f hf i x) (PdiffAt_pd h hh j i x)]
  ring

/-- **The Laplace–Beltrami Leibniz product rule**
    `Δ_g(f·h) = f·Δ_g h + h·Δ_g f + 2·g^{ij}(∂_i f)(∂_j h)`.

    The `H·Δ_g χ` and `2 g^{ij}∂_i χ ∂_j H` terms (with `f = χ` a cutoff) are the annulus-supported
    cutoff-derivative terms of the C4c cutoff-parametrix residual `(∂_t − Δ_g)(χH)`.

    Genuine hypotheses: `f, h ∈ C^∞` (so all first/second partials exist — used via `pd_pd_mul` and
    `pd_mul`), and symmetry of the inverse metric at the base point `x` (`hgisymm`, used only to
    symmetrise the cross term into the factor `2`). -/
theorem laplaceBeltrami_mul (g gi : Point n → Fin n → Fin n → ℝ) (f h : Point n → ℝ) (x : Point n)
    (hf : ContDiff ℝ ⊤ f) (hh : ContDiff ℝ ⊤ h)
    (hgisymm : ∀ i j, gi x i j = gi x j i) :
    laplaceBeltrami g gi (fun y => f y * h y) x
      = f x * laplaceBeltrami g gi h x + h x * laplaceBeltrami g gi f x
        + 2 * ∑ i, ∑ j, gi x i j * (pd f i x) * (pd h j x) := by
  classical
  -- (1) split the Christoffel contraction of a product
  have hksum : ∀ i j : Fin n,
      (∑ k, christoffel g gi k i j x * pd (fun z => f z * h z) k x)
        = h x * (∑ k, christoffel g gi k i j x * pd f k x)
          + f x * (∑ k, christoffel g gi k i j x * pd h k x) := by
    intro i j
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_mul f h k x (PdiffAt_of_contDiff f hf k x) (PdiffAt_of_contDiff h hh k x)]
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
    rw [pd_pd_mul f h i j x hf hh, hksum i j]; ring
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
