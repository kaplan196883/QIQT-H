/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ParametrixRadialTransportSplit — the (c)-side M5 leading-order isolation brick

This file supplies the **missing linearity primitive** that lets the off-diagonal `O(1/t)` van-Vleck
cancellation (M5) read its leading singular coefficient off the residual decomposition
`QIQTH.HeatResidualBound.parametrixResidual_offdiag_absorbed`.

## Where M5 sits (the (c)-side wiring)

`parametrixResidual_offdiag_absorbed` rewrites the heat-operator residual of the folded parametrix
`H_N = G·Σ_{k≤N} w_k t^k` (with `w_k = foldedCoeff Θ u k = Θ^{−1/2}u_k`) as five pieces, of which the
**radial-transport piece (II)** carries the *only* `O(1/t)` singularity:

```
  … + (1/t)·G·radialDeriv(fun y => Σ_{k≤N} w_k(y) t^k) v + …
```

The radial (Euler) derivative there is taken of the WHOLE polynomial-in-`t` coefficient
`P = Σ_{k≤N} w_k · t^k`.  To see the `O(1/t)` order — the term the van-Vleck factor `Θ^{−1/2}` is
chosen to kill — one must **commute `radialDeriv` past the finite `Σ_k … t^k`** and peel the `k=0`
summand.  Mathlib/the repo had the `Δ_g` analogue of that commutation
(`HeatResidualBound.laplaceBeltrami_sum_pow`) but NOT the `radialDeriv` analogue.  This file adds it.

## What lands

* `radialDeriv_sum_pow` — the `radialDeriv` analogue of `laplaceBeltrami_sum_pow`: for the
  polynomial-in-`t` field `Σ_{k≤N} c_k(y) t^k`,
  `radialDeriv (Σ_k c_k · t^k) v = Σ_k radialDeriv(c_k) v · t^k`.  Pure Euler-field linearity over the
  finite sum (each `t^k` a constant).  UNCONDITIONAL beyond per-coordinate differentiability of the
  `c_k`.  Reusable primitive.

* `radialTransportTerm_leading_split` — the M5-relevant isolation: the residual's radial-transport
  term splits into its `O(1/t)` **leading van-Vleck order** (the `k=0` term) plus a genuinely regular
  (`t⁰`-and-higher) polynomial tail:
  ```
    (1/t)·G·radialDeriv(Σ_{k≤N} w_k t^k) v
      = (1/t)·G·radialDeriv(w_0) v                     -- ★ the O(1/t) singular van-Vleck term
        + G·Σ_{k<N} radialDeriv(w_{k+1}) v · t^k .      -- the regular tail
  ```
  The singular summand is exactly `(1/t)·G·radialDeriv(w_0)` with `w_0 = foldedCoeff Θ u 0`; for the
  concrete van-Vleck parametrix (`Θ = vanVleck g̃ = (det g̃)^{−1/2}`, `u_0 = 1`) this is
  `w_0 = (det g̃)^{1/4}`, and `radialDeriv(w_0) = ¼(det g̃)^{1/4}·radialDeriv(log det g̃)` is precisely
  the object connected to the Raychaudhuri expansion by `ExpMap.radialDeriv_foldedCoeff_leading` (M5-b)
  and `ExpMap.parametrixTransport_raychaudhuri_form` (M5-c).

## Honest scope (binding)

⚠ This is the **algebraic isolation of the `O(1/t)` order** only.  It does NOT perform the full M5
cancellation — matching this singular term against the flat-Gaussian curvature piece (I) and the
metric-deviation cross-gradient piece (IV) of `parametrixResidual_offdiag_absorbed`.  That matching is
the checkpointed content of M5 (it needs the RNC `O(r²)` expansion of `gⁱʲ − δⁱʲ` and `Γ`, and the
value of `radialDeriv(log det g̃)` supplied — in *first-derivative* `θ_B` form — by
`ExpMap.vanVleck_radialDeriv_ricci_form`, NOT the *second-derivative* `−Ric` Raychaudhuri ODE
`ExpMap.vanVleck_ricci_unconditional`, which is one integration too high for the leading order).  It
does NOT give `a₁ = R/6`.  Only the per-coordinate smoothness `hw` of the folded coefficients is used;
the metric is arbitrary.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.HeatResidualBound
import QIQTH.RadialDistance
import QIQTH.Curvature

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.RNCExpansion
open QIQTH.FlatHeatEquation QIQTH.HeatResidualBound

namespace QIQTH.ParametrixRadialTransportSplit

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ### #1 — the `radialDeriv` analogue of `laplaceBeltrami_sum_pow` -/

/-- **`radialDeriv` of a polynomial-in-`t` sum of fields.**
    `radialDeriv (fun y => Σ_{k≤N} c_k(y)·t^k) v = Σ_{k≤N} radialDeriv(c_k) v · t^k`.
    Linearity of the Euler radial field `r∂_r = Σᵢ vⁱ∂ᵢ` over the finite sum (each `t^k` a constant):
    per coordinate `∂ᵢ(Σ_k c_k · t^k) = Σ_k t^k · ∂ᵢc_k` (`pd_sum` + `pd_const_mul`), then contract
    against `vⁱ` and swap the two finite sums.  This is the `radialDeriv` counterpart of
    `QIQTH.HeatResidualBound.laplaceBeltrami_sum_pow`, the missing commutation that lets the
    off-diagonal residual's radial-transport term be read order-by-order.  Only per-coordinate
    differentiability of the `c_k` at `v` is used. -/
theorem radialDeriv_sum_pow (c : ℕ → Point n → ℝ) (t : ℝ) (v : Point n) (N : ℕ)
    (hc : ∀ k i, PdiffAt (c k) i v) :
    radialDeriv (fun y => ∑ k ∈ Finset.range (N + 1), c k y * t ^ k) v
      = ∑ k ∈ Finset.range (N + 1), radialDeriv (c k) v * t ^ k := by
  simp only [radialDeriv]
  -- per-coordinate: `∂ᵢ(Σ_k c_k · t^k) = Σ_k t^k · ∂ᵢc_k`
  have hpd : ∀ i, pd (fun y => ∑ k ∈ Finset.range (N + 1), c k y * t ^ k) i v
      = ∑ k ∈ Finset.range (N + 1), t ^ k * pd (c k) i v := by
    intro i
    rw [show (fun y => ∑ k ∈ Finset.range (N + 1), c k y * t ^ k)
          = (fun y => ∑ k ∈ Finset.range (N + 1), t ^ k * c k y) from
        funext (fun y => Finset.sum_congr rfl (fun k _ => by ring)),
        pd_sum (Finset.range (N + 1)) (fun k y => t ^ k * c k y) i v
          (fun k _ => PdiffAt_const_mul (t ^ k) (c k) i v (hc k i))]
    exact Finset.sum_congr rfl (fun k _ => pd_const_mul (t ^ k) (c k) i v (hc k i))
  -- contract against `vⁱ` and swap the two finite sums
  rw [show (∑ i, v i * pd (fun y => ∑ k ∈ Finset.range (N + 1), c k y * t ^ k) i v)
        = ∑ i, ∑ k ∈ Finset.range (N + 1), v i * (t ^ k * pd (c k) i v) from
      Finset.sum_congr rfl (fun i _ => by rw [hpd i, Finset.mul_sum])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-! ### #2 — isolate the `O(1/t)` leading van-Vleck order of the radial-transport term -/

/-- **The `O(1/t)` leading-order isolation of the residual radial-transport term (M5).**
    The `O(1/t)`-carrying radial-transport piece of
    `QIQTH.HeatResidualBound.parametrixResidual_offdiag_absorbed` — `(1/t)·G·radialDeriv(P)` with
    `P = Σ_{k≤N} w_k · t^k`, `w_k = foldedCoeff Θ u k` — splits into its `k=0` **leading van-Vleck
    order** plus a genuinely regular (`t⁰`-and-higher) tail:
    ```
      (1/t)·G·radialDeriv(Σ_{k≤N} w_k t^k) v
        = (1/t)·G·radialDeriv(w_0) v
          + G·Σ_{k<N} radialDeriv(w_{k+1}) v · t^k .
    ```
    The first summand `(1/t)·G·radialDeriv(w_0) v` is the ONLY `O(1/t)` singular term of the whole
    residual; it is exactly what the van-Vleck factor `Θ^{−1/2}` is chosen to cancel against pieces
    (I)+(IV).  For the concrete van-Vleck parametrix (`Θ = vanVleck g̃`, `u_0 = 1`) `w_0 = (det g̃)^{1/4}`
    and `radialDeriv(w_0)` is the object connected to the Raychaudhuri expansion `θ_B` by M5-b/M5-c
    (`ExpMap.radialDeriv_foldedCoeff_leading` / `ExpMap.parametrixTransport_raychaudhuri_form`).
    ROUTE: `radialDeriv_sum_pow` commutes `radialDeriv` past the finite sum, then `Finset.sum_range_succ'`
    peels the `k=0` term and `(1/t)·t^{k+1} = t^k` (`t > 0`) regularizes the tail.  Only the folded-coefficient
    smoothness `hw` is used; the metric is arbitrary.  NOT the full M5 cancellation, NOT `a₁ = R/6`. -/
theorem radialTransportTerm_leading_split (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    (1 / t) * gaussDdim t v
        * radialDeriv (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) v
      = (1 / t) * gaussDdim t v * radialDeriv (foldedCoeff Θ u 0) v
        + gaussDdim t v
            * ∑ k ∈ Finset.range N, radialDeriv (foldedCoeff Θ u (k + 1)) v * t ^ k := by
  have ht' : t ≠ 0 := ne_of_gt ht
  -- the regularized-tail identity `(1/t)·G·Σ w_{k+1} t^{k+1} = G·Σ w_{k+1} t^k`
  have hsum : (1 / t) * gaussDdim t v * (∑ k ∈ Finset.range N,
        radialDeriv (foldedCoeff Θ u (k + 1)) v * t ^ (k + 1))
      = gaussDdim t v * ∑ k ∈ Finset.range N,
        radialDeriv (foldedCoeff Θ u (k + 1)) v * t ^ k := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pow_succ]
    field_simp
  rw [radialDeriv_sum_pow (foldedCoeff Θ u) t v N
        (fun k i => PdiffAt_of_contDiff (foldedCoeff Θ u k) (hw k) i v),
      Finset.sum_range_succ' (fun k => radialDeriv (foldedCoeff Θ u k) v * t ^ k) N,
      pow_zero, mul_one, mul_add, hsum, add_comm]

end QIQTH.ParametrixRadialTransportSplit
