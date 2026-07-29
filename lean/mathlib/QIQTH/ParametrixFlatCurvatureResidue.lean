/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ParametrixFlatCurvatureResidue — the (c)-side M5 `O(1/t)` isolation of piece (I)

This file supplies the **flat-Gaussian curvature-residue companion** of
`QIQTH.ParametrixDeviationCrossTerm.deviationCrossTerm_leading` (which isolated the `O(1/t)` order of
the metric-deviation cross-gradient piece (IV) of the folded-parametrix residual
`QIQTH.HeatResidualBound.parametrixResidual_offdiag_absorbed`).  Here we isolate the singular order of
the **flat-Gaussian curvature residue piece (I)**, whose coefficient is

```
  (I)-coefficient = (∂_t G − Δ_g G)(v)      -- multiplied by  P(v) = Σ_{k≤N} w_k(v) t^k  in the residual.
```

## The mechanism

By the flat heat equation (`QIQTH.FlatHeatEquation.gaussDdim_heat_eqn`) `∂_t G = Δ_flat G = Σ_i ∂_i²G`,
so the curvature residue is the metric-deviation of the Laplacian acting on the Gaussian:

```
  (∂_t − Δ_g)G = (Δ_flat − Δ_g)G
    = − Σ_{ij} (gⁱʲ − δⁱʲ) ∂_i∂_j G  +  Σ_{ijk} gⁱʲ Γᵏᵢⱼ ∂_k G .
```

Substituting the closed Gaussian derivatives `∂_i∂_j G = (vⁱvʲ/(4t²) − δⁱʲ/(2t))·G`
(`gaussDdim_pd_pd_eq`) and `∂_k G = (−vᵏ/(2t))·G` (`gaussDdim_pd_eq`) exposes the `1/t` powers.  The
`1/(4t²)` order is the deviation-weighted quadratic, and the `1/(2t)` order is the trace deviation plus
the Christoffel contraction:

```
  (∂_t − Δ_g)G(v)
      = (1/t)·G·[ ½·Σ_i (gⁱⁱ − 1) − ½·Σ_{ijk} gⁱʲ Γᵏᵢⱼ vᵏ ]           -- 1/t   order
      + (1/t²)·G·[ −¼·Σ_{ij} (gⁱʲ − δⁱʲ) vⁱvʲ ] .                       -- 1/t²  order
```

This is the **exact singular-order isolation** of piece (I): the residual coefficient is a
`(1/t)·G·(…)` plus a `(1/t²)·G·(…)`, each an explicit deviation- and Christoffel-weighted polynomial in
`(v, gⁱʲ−δⁱʲ, Γ)`, carrying the metric deviation and Christoffel symbols **symbolically**.  It MIRRORS
`deviationCrossTerm_leading`, but piece (I) genuinely carries a `1/t²` order in addition to the `1/t`
one (piece (IV) had only `1/t`, since it involved a single Gaussian gradient; piece (I) involves the
Gaussian **second** derivatives inside `Δ_g`).

## What lands

* `gaussDdim_pd_pd_eq` — the mixed coordinate second partial of the flat Gaussian,
  `∂_i∂_j G(v) = (vⁱvʲ/(4t²) − δⁱʲ/(2t))·G(v)` (the seed of the `Δ_g G` substitution).

* `flatCurvatureResidue_core` — the abstract real-arithmetic identity performing the substitution +
  regrouping into the `(1/t)·G + (1/t²)·G` normal form, for arbitrary families `(a, M, C, G)`.  Only
  `t ≠ 0` is used.

* `flatCurvatureResidue_leading` — piece (I)'s coefficient `(∂_t G − Δ_g G)(v)` isolated in the
  `(1/t)·G·(…) + (1/t²)·G·(…)` normal form, with the metric `gⁱʲ` and Christoffel `Γ` carried
  symbolically.  This is the reusable brick.

* `flatCurvatureResidue_leading_parametrix` — the specialization to piece (I) exactly as it appears in
  `parametrixResidual_offdiag_absorbed` (multiplied by the folded polynomial
  `P = Σ_{k≤N} w_k·t^k`).

## Honest scope (binding) — this is FLOOR F2, NOT F1.

⚠ This isolates the singular order **carrying `(gⁱʲ − δⁱʲ)` and `Γᵏᵢⱼ` symbolically** — it substitutes
only the Gaussian derivatives `∂G`/`∂²G` to expose the `1/t`, `1/t²` powers, exactly as
`deviationCrossTerm_leading` did for piece (IV).  It does NOT substitute the closed RNC forms
`gⁱʲ − δⁱʲ = ⅓ R_{iαjβ}vᵃvᵝ + o(r²)` (`QIQTH.RNCExpansion.rnc_gInv_hessian`) or the Christoffel 1-jet
`∂Γ(0)` (that F1 upgrade is the NEXT (c)-brick).  It does NOT perform the full M5 cancellation —
matching this coefficient against the transport leading order (piece (II)) and piece (IV) — and does
NOT give `a₁ = R/6`.  The only hypothesis is `t > 0`; it is genuine and load-bearing (without it the
`1/t`, `1/t²` are meaningless).  The metric `g`, `gi` and the point `v` are arbitrary.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.VanVleckCancellation
import QIQTH.ParametrixDeviationCrossTerm
import QIQTH.RNCInverseMetricJet
import QIQTH.LaplaceBeltrami
import QIQTH.FlatHeatEquation
import QIQTH.HeatResidualBound
import QIQTH.HeatParametrixOrder

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The mixed coordinate second partial of the flat Gaussian. -/

/-- **The mixed coordinate second partial of the flat `d`-dimensional Gaussian.**
    `∂_i∂_j G_t(v) = (vⁱvʲ/(4t²) − δⁱʲ/(2t))·G_t(v)`, at EVERY point `v` (not just the center).
    For `i = j` this is `FlatHeatEquation.gaussDdim_pd_pd_i`; for `i ≠ j` the two Gaussian gradients
    factor.  MECHANISM: `∂_j G = (−vʲ/(2t))·G` (`gaussDdim_pd_i`), then differentiate the product in
    the `i`-direction via the Leibniz rule — the coordinate factor `vʲ` contributes `−δⁱʲ/(2t)` (only
    when `i = j`) and the frozen Gaussian contributes `(−vⁱ/(2t))·(−vʲ/(2t)) = vⁱvʲ/(4t²)`.  This is
    the seed of the `Δ_g G` substitution in the curvature residue. -/
theorem gaussDdim_pd_pd_eq (t : ℝ) (ht : 0 < t) (v : Point n) (i j : Fin n) :
    pd (fun y => pd (fun z => gaussDdim t z) j y) i v
      = (v i * v j / (4 * t ^ 2) - (if i = j then (1 : ℝ) else 0) / (2 * t)) * gaussDdim t v := by
  have ht' : t ≠ 0 := ne_of_gt ht
  have hinner : (fun y => pd (fun z => gaussDdim t z) j y)
      = (fun y => (-1 / (2 * t)) * y j * gaussDdim t y) := by
    funext y; rw [gaussDdim_pd_i t ht y j]; ring
  have hstep : pd (fun y => pd (fun z => gaussDdim t z) j y) i v
      = pd (fun y => (-1 / (2 * t)) * y j) i v * gaussDdim t v
        + (-1 / (2 * t)) * v j * pd (fun y => gaussDdim t y) i v := by
    rw [hinner]
    exact pd_mul (fun y => (-1 / (2 * t)) * y j) (fun y => gaussDdim t y) i v
      (QIQTH.LaplaceBeltrami.PdiffAt_const_mul_coord (-1 / (2 * t)) j i v)
      (PdiffAt_of_contDiff _ (QIQTH.HeatParametrixOrder.gaussDdim_contDiff t) i v)
  rw [hstep,
      pd_const_mul (-1 / (2 * t)) (fun y => y j) i v (QIQTH.LaplaceBeltrami.PdiffAt_coord j i v),
      QIQTH.LaplaceBeltrami.pd_coord j i v,
      gaussDdim_pd_eq t ht v i]
  rw [show (if j = i then (1 : ℝ) else 0) = (if i = j then (1 : ℝ) else 0) from by
        by_cases h : i = j
        · subst h; rfl
        · rw [if_neg h, if_neg (fun h' => h h'.symm)]]
  field_simp
  ring

/-! ### The abstract real-arithmetic core of the isolation. -/

/-- **The abstract `(1/t) + (1/t²)` normal-form identity of the flat curvature residue.**  For
    arbitrary real families `a : Fin n → ℝ` (the coordinate `vⁱ`), `M : Fin n → Fin n → ℝ` (the
    inverse metric `gⁱʲ`), `C : Fin n → Fin n → Fin n → ℝ` (the Christoffel `Γᵏᵢⱼ`), and a scalar
    `G` (the Gaussian value), the substituted curvature residue
      `(Σ_i ∂_i²G) − Σ_{ij} M ((∂_i∂_j G) − Σ_k C·∂_k G)`,
    with the closed Gaussian second/first partials plugged in, regroups by inverse power of `t`:
      `= (1/t)·G·[ ½Σ_i(M i i − 1) − ½Σ_{ijk} M i j·C k i j·a k ]`
      `+ (1/t²)·G·[ −¼Σ_{ij}(M i j − δⁱʲ)·(a i·a j) ]`.
    Only `t ≠ 0` is used; the families are arbitrary.  This is the pure-arithmetic heart of the
    isolation, separated from the calculus. -/
theorem flatCurvatureResidue_core (t : ℝ) (ht : t ≠ 0)
    (a : Fin n → ℝ) (M : Fin n → Fin n → ℝ) (C : Fin n → Fin n → Fin n → ℝ) (G : ℝ) :
    (∑ i, (a i * a i / (4 * t ^ 2) - 1 / (2 * t)) * G)
      - (∑ i, ∑ j, M i j * ((a i * a j / (4 * t ^ 2) - (if i = j then (1 : ℝ) else 0) / (2 * t)) * G
          - ∑ k, C k i j * ((-(a k) / (2 * t)) * G)))
    = (1 / t) * G
        * ((1 / 2) * (∑ i, (M i i - 1))
            - (1 / 2) * (∑ i, ∑ j, ∑ k, M i j * C k i j * a k))
      + (1 / t ^ 2) * G
        * ((-1 / 4) * (∑ i, ∑ j, (M i j - (if i = j then (1 : ℝ) else 0)) * (a i * a j))) := by
  -- delta-collapse helpers
  have hdelta1 : (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0) * (a i * a j)) = ∑ i, a i * a i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (∑ j, (if i = j then (1 : ℝ) else 0) * (a i * a j))
        = ∑ j, (if i = j then a i * a j else 0) from
          Finset.sum_congr rfl fun j _ => by split <;> simp]
    rw [Finset.sum_ite_eq]; simp
  have hdelta2 : (∑ i, ∑ j, M i j * (if i = j then (1 : ℝ) else 0)) = ∑ i, M i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (∑ j, M i j * (if i = j then (1 : ℝ) else 0))
        = ∑ j, (if i = j then M i j else 0) from
          Finset.sum_congr rfl fun j _ => by split <;> simp]
    rw [Finset.sum_ite_eq]; simp
  -- T1 (the ∂_t = Σ_i ∂_i² part) in atoms
  have hT1 : (∑ i, (a i * a i / (4 * t ^ 2) - 1 / (2 * t)) * G)
      = (1 / (4 * t ^ 2)) * G * (∑ i, a i * a i)
        - (1 / (2 * t)) * G * (∑ _i : Fin n, (1 : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- T2 (the Δ_g G part) in atoms
  have hT2 : (∑ i, ∑ j, M i j * ((a i * a j / (4 * t ^ 2) - (if i = j then (1 : ℝ) else 0) / (2 * t)) * G
        - ∑ k, C k i j * ((-(a k) / (2 * t)) * G)))
      = (1 / (4 * t ^ 2)) * G * (∑ i, ∑ j, M i j * (a i * a j))
        - (1 / (2 * t)) * G * (∑ i, M i i)
        + (1 / (2 * t)) * G * (∑ i, ∑ j, ∑ k, M i j * C k i j * a k) := by
    have e1 : (1 / (4 * t ^ 2)) * G * (∑ i, ∑ j, M i j * (a i * a j))
        = ∑ i, ∑ j, (1 / (4 * t ^ 2)) * G * (M i j * (a i * a j)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    have e2 : (1 / (2 * t)) * G * (∑ i, M i i)
        = ∑ i, ∑ j, (1 / (2 * t)) * G * (M i j * (if i = j then (1 : ℝ) else 0)) := by
      rw [← hdelta2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    have e3 : (1 / (2 * t)) * G * (∑ i, ∑ j, ∑ k, M i j * C k i j * a k)
        = ∑ i, ∑ j, ∑ k, (1 / (2 * t)) * G * (M i j * C k i j * a k) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      exact Finset.mul_sum _ _ _
    rw [e1, e2, e3, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_sub, Finset.mul_sum,
        show M i j * ((a i * a j / (4 * t ^ 2) - (if i = j then (1 : ℝ) else 0) / (2 * t)) * G)
          = (1 / (4 * t ^ 2)) * G * (M i j * (a i * a j))
            - (1 / (2 * t)) * G * (M i j * (if i = j then (1 : ℝ) else 0)) from by ring,
        show (∑ k, M i j * (C k i j * ((-(a k) / (2 * t)) * G)))
          = -(∑ k, (1 / (2 * t)) * G * (M i j * C k i j * a k)) from by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun k _ => by ring]
    ring
  -- the two RHS deviations back to atoms
  have htr : (∑ i, (M i i - 1)) = (∑ i, M i i) - (∑ _i : Fin n, (1 : ℝ)) := by
    rw [Finset.sum_sub_distrib]
  have hdev : (∑ i, ∑ j, (M i j - (if i = j then (1 : ℝ) else 0)) * (a i * a j))
      = (∑ i, ∑ j, M i j * (a i * a j)) - (∑ i, a i * a i) := by
    rw [← hdelta1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_mul]
  -- reassemble
  rw [hT1, hT2, htr, hdev]
  field_simp
  ring

/-! ### The `O(1/t)`/`O(1/t²)` leading-order isolation of the flat curvature residue piece (I). -/

/-- **The singular-order isolation of the flat-Gaussian curvature residue (M5, piece (I)).**
    Piece (I)'s coefficient of `parametrixResidual_offdiag_absorbed`,
      `(∂_t G − Δ_g G)(v)`,
    equals the `(1/t)·G` plus `(1/t²)·G` normal form with the metric `gⁱʲ` and Christoffel `Γᵏᵢⱼ`
    carried symbolically:
      `= (1/t)·G·[ ½·Σ_i (gⁱⁱ − 1) − ½·Σ_{ijk} gⁱʲ·Γᵏᵢⱼ·vᵏ ]`
      `+ (1/t²)·G·[ −¼·Σ_{ij} (gⁱʲ − δⁱʲ)·(vⁱ·vʲ) ]`.
    MECHANISM: the flat heat equation `∂_t G = Σ_i ∂_i²G` (`gaussDdim_heat_eqn`) turns the residue into
    the metric-deviation of `Δ_g` on `G`; substitute the closed Gaussian second/first partials
    `∂_i∂_j G = (vⁱvʲ/(4t²) − δⁱʲ/(2t))·G` (`gaussDdim_pd_pd_eq`) and `∂_k G = (−vᵏ/(2t))·G`
    (`gaussDdim_pd_eq`), then regroup by inverse power of `t` (`flatCurvatureResidue_core`).  Only
    `t > 0` is used; the metric `g`, `gi` and the point `v` are arbitrary.
    ⚠ FLOOR F2: the deviation `(gⁱʲ − δⁱʲ)` and Christoffel `Γ` are carried SYMBOLICALLY — the closed
    RNC curvature forms are NOT substituted here.  NOT the full M5 cancellation, NOT `a₁ = R/6`. -/
theorem flatCurvatureResidue_leading (t : ℝ) (ht : 0 < t)
    (g gi : Point n → Fin n → Fin n → ℝ) (v : Point n) :
    (deriv (fun s => gaussDdim s v) t - laplaceBeltrami g gi (gaussDdim t) v)
      = (1 / t) * gaussDdim t v
          * ((1 / 2) * (∑ i, (gi v i i - 1))
              - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k))
        + (1 / t ^ 2) * gaussDdim t v
          * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))) := by
  have ht' : t ≠ 0 := ne_of_gt ht
  have hppE : ∀ i, pd (fun y => pd (fun z => gaussDdim t z) i y) i v
      = (v i * v i / (4 * t ^ 2) - 1 / (2 * t)) * gaussDdim t v := by
    intro i; rw [gaussDdim_pd_pd_eq t ht v i i]; simp
  have hppL : ∀ i j, pd (fun y => pd (gaussDdim t) j y) i v
      = (v i * v j / (4 * t ^ 2) - (if i = j then (1 : ℝ) else 0) / (2 * t)) * gaussDdim t v :=
    fun i j => gaussDdim_pd_pd_eq t ht v i j
  have hpL : ∀ k, pd (gaussDdim t) k v = (-(v k) / (2 * t)) * gaussDdim t v :=
    fun k => gaussDdim_pd_eq t ht v k
  rw [gaussDdim_heat_eqn t ht v, Finset.sum_congr rfl (fun i _ => hppE i)]
  simp only [laplaceBeltrami, hppL, hpL]
  exact flatCurvatureResidue_core t ht' v (fun i j => gi v i j)
    (fun k i j => christoffel g gi k i j v) (gaussDdim t v)

/-- **Piece (I) of the parametrix residual, singular-order-isolated.**  Multiplying
    `flatCurvatureResidue_leading` by the folded-parametrix polynomial
    `P = Σ_{k≤N} w_k·t^k` (`w_k = foldedCoeff Θ u k`), piece (I) exactly as it appears in
    `parametrixResidual_offdiag_absorbed` equals the `(1/t)·G + (1/t²)·G` normal form times `P`.
    The metric deviation and Christoffel stay symbolic (FLOOR F2).  Only `t > 0` is used. -/
theorem flatCurvatureResidue_leading_parametrix (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n) :
    (deriv (fun s => gaussDdim s v) t - laplaceBeltrami g gi (gaussDdim t) v)
        * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * t ^ k)
      = ((1 / t) * gaussDdim t v
            * ((1 / 2) * (∑ i, (gi v i i - 1))
                - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k))
          + (1 / t ^ 2) * gaussDdim t v
            * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))))
        * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * t ^ k) := by
  rw [flatCurvatureResidue_leading t ht g gi v]

end QIQTH.HeatResidualBound
