import Mathlib
import QIQTH.JacobianDet
import QIQTH.RadialRayDeriv

/-!
# The additive `log det g̃` split and its second ray-derivative decomposition

This is the FIRST piece of the van-Vleck coordinate-connection capstone.  Starting from the
matrix-product form of the pullback metric `g̃ = Jᵀ · (g∘exp) · J`
(`QIQTH.JacobianDet.expPullbackMetric_eq_jacMul`, with `J = expJacobianMat`), taking determinants
gives `det g̃ = J² · det(g∘exp)` (`det_expPullback_eq`).  Taking logs turns the multiplicative
factorization into the **additive split**
      `log det g̃ = 2 · log J + log det(g∘exp)`,
whose two summands are the exp-Jacobian piece (governing the van-Vleck / Raychaudhuri expansion `θ`)
and the metric-along-the-geodesic piece.

## What lands

* `logdet_gtilde_split` — the pointwise determinant split
  `log(det g̃(x)) = 2·log(J(x)) + log(det(g∘exp)(x))`, under positivity `0 < J(x)` and
  `0 < det(g∘exp)(x)` (the two `Real.log_mul`/`Real.log_pow` factorization hypotheses; both genuine
  positivity facts, neither assumes the conclusion).

* `logdet_gtilde_ray_secondDeriv` — along a ray `s ↦ s • v`, IF the pointwise split holds eventually
  near `s = 1` (`hsplit`, e.g. from `logdet_gtilde_split` holding for `s` near 1), and each of the two
  ray-pieces is differentiable near `1` with its first derivative twice-differentiable at `1`, then the
  **second ray-derivative decomposes additively**
      `d²/ds²[log det g̃(s•v)]|₁ = 2·LJ'' + Lg''`,
  where `LJ''`, `Lg''` are the second ray-derivatives of `log J` and `log det(g∘exp)` at `1`.

## What this is NOT

⚠ This file does the *additive-split algebra and the two-summand second-derivative bookkeeping ONLY*.
It does **not** wire the Raychaudhuri identity `θ_Y' = −Ric` / the trace connection, does **not**
prove the matrix-Jacobi ODE `B'' = −R̃ B`, and is **not** the heat-kernel coefficient `a₁ = R/6`.  It
is the first bookkeeping brick toward the target
      `d²/ds²[log det g̃(s•v)]|₁ = −2 Ric − 2 tr Θ² + 2n`.
-/

set_option maxHeartbeats 800000

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.PullbackMetric QIQTH.JacobianDet
open Matrix

variable {n : ℕ}

/-- **The additive `log det g̃` split.**  Since `g̃ = Jᵀ (g∘exp) J`, taking determinants gives
    `det g̃ = J² · det(g∘exp)` (`det_expPullback_eq`); taking logs turns this into the additive split
    `log(det g̃) = 2·log J + log(det(g∘exp))`.  The hypotheses `0 < J(x)` (`hJ`) and
    `0 < det(g∘exp)(x)` (`hD`) are the genuine positivity facts needed to distribute `Real.log` across
    the product `J² · det(g∘exp)` (`Real.log_mul` + `Real.log_pow`); neither assumes the conclusion. -/
theorem logdet_gtilde_split (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p x : Point n)
    (hJ : 0 < expJacobianDet g gi hC p x)
    (hD : 0 < (Matrix.of fun a b => g (expMap g gi hC p x) a b).det) :
    Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p x i j).det)
      = 2 * Real.log (expJacobianDet g gi hC p x)
        + Real.log ((Matrix.of fun a b => g (expMap g gi hC p x) a b).det) := by
  rw [det_expPullback_eq, Real.log_mul (pow_ne_zero 2 hJ.ne') hD.ne', Real.log_pow]
  push_cast
  ring

/-- **The second ray-derivative of `log det g̃` decomposes additively.**  Fix a direction `v` and
    consider the ray `s ↦ s • v`.  Write
      `F(s) := log(det g̃(s•v))`,   `LJ(s) := log(J(s•v))`,   `Lg(s) := log(det(g∘exp)(s•v))`.
    If the pointwise split `F =ᶠ 2·LJ + Lg` holds near `s = 1` (`hsplit`, from `logdet_gtilde_split`
    holding for `s` near `1`), each piece is differentiable near `1` (`hLJev`, `hLgev`), and each first
    ray-derivative `deriv LJ`, `deriv Lg` is again differentiable at `1` with second derivatives
    `LJ''`, `Lg''` (`hLJ2`, `hLg2`), then
      `d²/ds²[F(s)]|₁ = 2·LJ'' + Lg''`.
    All carried hypotheses are genuine (`EventuallyEq` / eventual `DifferentiableAt` / `HasDerivAt`);
    none is vacuous and none assumes the conclusion. -/
theorem logdet_gtilde_ray_secondDeriv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (hsplit : (fun s : ℝ =>
        Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))
      =ᶠ[nhds (1 : ℝ)]
        (fun s => 2 * Real.log (expJacobianDet g gi hC p (s • v))
          + Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det)))
    (hLJev : ∀ᶠ s in nhds (1 : ℝ),
        DifferentiableAt ℝ (fun u : ℝ => Real.log (expJacobianDet g gi hC p (u • v))) s)
    (hLgev : ∀ᶠ s in nhds (1 : ℝ),
        DifferentiableAt ℝ
          (fun u : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (u • v)) a b).det)) s)
    {LJ'' Lg'' : ℝ}
    (hLJ2 : HasDerivAt
        (deriv (fun s : ℝ => Real.log (expJacobianDet g gi hC p (s • v)))) LJ'' 1)
    (hLg2 : HasDerivAt
        (deriv (fun s : ℝ =>
          Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))) Lg'' 1) :
    deriv (deriv (fun s : ℝ =>
        Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))) 1
      = 2 * LJ'' + Lg'' := by
  -- Abbreviations for the two ray-pieces.
  set LJ : ℝ → ℝ := fun s => Real.log (expJacobianDet g gi hC p (s • v)) with hLJdef
  set Lg : ℝ → ℝ :=
    fun s => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det) with hLgdef
  -- First ray-derivative of the split's RHS, valid eventually near `1`.
  have hev : deriv (fun s => 2 * LJ s + Lg s)
      =ᶠ[nhds (1 : ℝ)] fun s => 2 * deriv LJ s + deriv Lg s := by
    filter_upwards [hLJev, hLgev] with s hLJs hLgs
    have h1 : HasDerivAt (fun s => 2 * LJ s + Lg s) (2 * deriv LJ s + deriv Lg s) s :=
      (hLJs.hasDerivAt.const_mul 2).add hLgs.hasDerivAt
    exact h1.deriv
  -- The LHS `deriv (deriv F) 1` equals `deriv (deriv (2·LJ + Lg)) 1` via the eventual split.
  rw [hsplit.deriv.deriv_eq, hev.deriv_eq]
  -- Second derivative of `2·(deriv LJ) + deriv Lg` at `1`.
  have h2 : HasDerivAt (fun s => 2 * deriv LJ s + deriv Lg s) (2 * LJ'' + Lg'') 1 :=
    (hLJ2.const_mul 2).add hLg2
  exact h2.deriv

end QIQTH.ExpMap
