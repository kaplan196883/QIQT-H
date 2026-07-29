/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ParametrixDeviationCrossTerm — the (c)-side M5 `O(1/t)` isolation of piece (IV)

This file supplies the **metric-deviation companion** of
`QIQTH.ParametrixRadialTransportSplit.radialTransportTerm_leading_split`.  Where that brick isolated
the `O(1/t)` order of the RADIAL-TRANSPORT piece (II) of the folded-parametrix residual
`QIQTH.HeatResidualBound.parametrixResidual_offdiag_absorbed`, this brick isolates the `O(1/t)` order
of the **metric-deviation cross-gradient piece (IV)**:

```
  (IV) = Σᵢⱼ (gⁱʲ − δⁱʲ)·((∂ᵢG)(∂ⱼP) + (∂ⱼG)(∂ᵢP)) (v) .
```

## The mechanism

The ONLY `t`-dependence that makes (IV) singular is the Gaussian gradient
`∂ᵢG = (−vⁱ/(2t))·G` (`QIQTH.HeatResidualBound.gaussDdim_pd_eq`).  Substituting it in **both**
Gaussian-gradient factors exposes the shared `1/t`:

```
  (∂ᵢG)(∂ⱼP) + (∂ⱼG)(∂ᵢP)
      = (−1/(2t))·G·( vⁱ·∂ⱼP + vʲ·∂ᵢP ) ,
```

so, summing the `(gⁱʲ − δⁱʲ)` weight over `i,j`,

```
  (IV) = (1/t)·G · [ −½ · Σᵢⱼ (gⁱʲ − δⁱʲ)·( vⁱ·∂ⱼP + vʲ·∂ᵢP ) ] .
```

This is the **exact `1/t` isolation** of piece (IV): the residual coefficient is `(1/t)·G` times an
explicit deviation-weighted bilinear form in `(v, ∂P)` that carries the metric deviation
`(gⁱʲ − δⁱʲ)` **symbolically**.  It MIRRORS `HeatResidualBound.flatCrossTerm_eq` (which handled the
flat `δⁱʲ` part and produced the pure radial term `−(1/t)·G·(r∂_r P)`) but on the DEVIATION part
`(gⁱʲ − δⁱʲ)` — the part that `flatCrossTerm_eq` deliberately dropped.

## What lands

* `deviationCrossTerm_leading` — the abstract-field `1/t` isolation of piece (IV) for an arbitrary
  smooth field `h` (the role played by `P`).  Only `t > 0` and the Gaussian-gradient identity are
  used; the metric `gi` and the field `h` are arbitrary.  This is the reusable primitive.

* `deviationCrossTerm_leading_parametrix` — the specialization to the ACTUAL folded-parametrix
  polynomial `P = Σ_{k≤N} w_k·t^k` (`w_k = foldedCoeff Θ u k`), i.e. piece (IV) exactly as it appears
  (subtracted) in `parametrixResidual_offdiag_absorbed`, written as `(1/t)·G·[deviation bilinear form]`.

## Honest scope (binding) — this is FLOOR F2, NOT F1.

⚠ This isolates the `1/t` **carrying the metric deviation `(gⁱʲ − δⁱʲ)` symbolically**.  It does NOT
substitute the closed-form RNC second-order expansion `gⁱʲ − δⁱʲ = −⅓ R_{iαjβ} vᵃvᵝ + O(r³)`
(the explicit curvature constant): the repo carries that deviation only ABSTRACTLY as an `O(r²)` decay
hypothesis (`ResidueBound.residue_metricdev_bound`'s `hddecay`), and no closed leading-coefficient
lemma for `gⁱʲ − δⁱʲ` yet exists (the RNC inverse-metric 2-jet is a separate downstream brick — the
same Riemannian-heat-kernel content recorded in `docs/qg_roadmap/HEAT_KERNEL_GAP_PLAN.md`).  Plugging
that closed form (giving the full explicit quadratic-in-`v` curvature coefficient, F1) is the NEXT
(c)-brick.  This file does NOT perform the full M5 cancellation — matching this `1/t` coefficient
against the transport-term leading order (M5-b/c) and piece (I) — and does NOT give `a₁ = R/6`.  The
only hypothesis is `t > 0`; it is genuine and load-bearing (without it the `1/t` is meaningless).

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.VanVleckCancellation
import QIQTH.ParametrixRadialTransportSplit
import QIQTH.ResidueBound

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.HeatResidualBound

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The `O(1/t)` leading-order isolation of the metric-deviation cross-gradient piece (IV). -/

/-- **The `1/t` isolation of the metric-deviation cross-gradient (M5, piece (IV)).**
    For an arbitrary smooth field `h` (the role of the folded polynomial `P`), the metric-deviation
    cross-gradient term of `parametrixResidual_offdiag_absorbed`,
      `Σᵢⱼ (gⁱʲ − δⁱʲ)·((∂ᵢG)(∂ⱼh) + (∂ⱼG)(∂ᵢh)) (v)` ,
    equals `(1/t)·G` times the explicit deviation-weighted bilinear form in `(v, ∂h)`:
      `= (1/t)·G · [ −½ · Σᵢⱼ (gⁱʲ − δⁱʲ)·( vⁱ·∂ⱼh + vʲ·∂ᵢh ) ]` .
    MECHANISM: substitute the Gaussian gradient `∂ᵢG = (−vⁱ/(2t))·G` (`gaussDdim_pd_eq`) in BOTH
    Gaussian factors; the shared `1/t` factors out and the coordinate weights `vⁱ, vʲ` land on the
    `∂h` factors.  This MIRRORS `flatCrossTerm_eq` (the `δⁱʲ`-flat part, which collapses to the pure
    radial term `−(1/t)·G·(r∂_r h)`) but on the DEVIATION part `(gⁱʲ − δⁱʲ)` that `flatCrossTerm_eq`
    drops.  Only `t > 0` is used; the metric `gi` and the field `h` are arbitrary.
    ⚠ FLOOR F2: the deviation `(gⁱʲ − δⁱʲ)` is carried SYMBOLICALLY — the closed RNC `O(r²)` curvature
    form `−⅓R_{iαjβ}vᵃvᵝ` is NOT substituted here.  NOT the full M5 cancellation, NOT `a₁ = R/6`. -/
theorem deviationCrossTerm_leading (t : ℝ) (ht : 0 < t)
    (gi : Point n → Fin n → Fin n → ℝ) (h : Point n → ℝ) (v : Point n) :
    (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (pd (fun y => gaussDdim t y) i v * pd h j v
            + pd (fun y => gaussDdim t y) j v * pd h i v))
      = (1 / t) * gaussDdim t v
          * ((-1 / 2) * ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
              * (v i * pd h j v + v j * pd h i v)) := by
  have ht' : t ≠ 0 := ne_of_gt ht
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussDdim_pd_eq t ht v i, gaussDdim_pd_eq t ht v j]
  field_simp
  ring

/-- **Piece (IV) of the parametrix residual, `1/t`-isolated.**  Specializing
    `deviationCrossTerm_leading` to the ACTUAL folded-parametrix polynomial
    `P = Σ_{k≤N} w_k·t^k` (`w_k = foldedCoeff Θ u k`), the metric-deviation cross-gradient term (IV)
    exactly as it appears (subtracted) in `parametrixResidual_offdiag_absorbed` equals `(1/t)·G` times
    the explicit deviation-weighted bilinear form in `(v, ∂P)`.  This wires the abstract isolation to
    the residual's own piece (IV); the deviation `(gⁱʲ − δⁱʲ)` stays symbolic (FLOOR F2).  Only
    `t > 0` is used; the metric and the coefficients are arbitrary. -/
theorem deviationCrossTerm_leading_parametrix (N : ℕ) (gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n) :
    (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (pd (fun y => gaussDdim t y) i v
              * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
            + pd (fun y => gaussDdim t y) j v
              * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v))
      = (1 / t) * gaussDdim t v
          * ((-1 / 2) * ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
              * (v i * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
                  + v j * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v)) :=
  deviationCrossTerm_leading t ht gi
    (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) v

end QIQTH.HeatResidualBound
