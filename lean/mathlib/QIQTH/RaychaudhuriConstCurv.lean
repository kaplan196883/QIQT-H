/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The exact van-Vleck / Raychaudhuri radial ODE for CONSTANT-curvature spaces

## What lands here (exactly, all orders, axiom-free)

In a space of **constant sectional curvature `K`** the radial Jacobi-field profile `S(r)`
(`sin(√K r)/√K` on the sphere, `sinh(√-K r)/√-K` on hyperbolic space, `r` when flat)
satisfies the scalar Jacobi ODE
  `S'' = −K · S`,  with `S(0) = 0`, `S'(0) = 1`.
Its geodesic-deviation **log-derivative** `u := S'/S` obeys the *exact* scalar **Riccati /
van-Vleck radial ODE**
  `u' = −K − u²`.
This is the honest 1-D Raychaudhuri equation, holding **to all orders in `r`** — not merely to the
2-jet.  Scaling by `(n−1)` gives the congruence expansion `θ := (n−1)·u` obeying the
Raychaudhuri expansion ODE
  `θ' = (n−1)·(−K − u²)`,
the division-free form.  In constant curvature `Ric = (n−1)K · g`, so `(n−1)K = Ric(∂_r, ∂_r)`:
the coefficient `(n−1)K` here IS the Ricci radial source term that appears abstractly in
`QIQTH.ExpMap.covariantJacobi_trace_at_center` (Raychaudhuri.lean), realized concretely for the
constant-curvature model.

The core derivation is pure one-variable calculus (quotient rule + `S'' = −K·S`):
  `u' = (S''·S − S'·S')/S² = (−K·S·S − (S')²)/S² = −K − (S'/S)² = −K − u²`.

## What this does NOT cover  (⚠ honest scope)

* This is the **constant-curvature model ONLY**.  It is NOT the general variable-curvature true
  heat kernel: the general radial ODE has a matrix Jacobi field `Y(r)` with an off-radial `Y⁻¹`
  factor (`u = Y' Y⁻¹`), and `Y⁻¹` / matrix-Jacobi machinery is the Mathlib-absent wall.
* It does NOT establish `a₁ = R/6` in general (the Seeley–DeWitt / heat-kernel coefficient),
  which remains the deferred variable-curvature gap.

Here the profile `S` and its derivatives are supplied as ordinary functions carrying explicit
`HasDerivAt` links, and the ONLY structural hypotheses are the genuine Jacobi ODE `S'' = −K·S`
and non-degeneracy `S r ≠ 0`.  Nothing assumes the conclusion.

Axiom-free.
-/
import Mathlib

namespace QIQTH.RaychaudhuriConstCurv

/-- **The exact scalar Riccati / van-Vleck radial ODE.**  For a radial Jacobi profile `S` solving
the scalar Jacobi ODE `S'' = −K·S` (constant curvature `K`), the log-derivative `u := S'/S`
satisfies `u' = −K − u²` at every point where `S ≠ 0`.  This holds to **all orders**, not just the
2-jet: it is the honest 1-D Raychaudhuri equation for the constant-curvature model.

Derivatives are carried explicitly (`Sd = S'`, `Sdd = S''`) to avoid differentiability side goals. -/
theorem jacobi_logderiv_riccati (K : ℝ) (S Sd Sdd : ℝ → ℝ)
    (hS : ∀ r, HasDerivAt S (Sd r) r)
    (hSd : ∀ r, HasDerivAt Sd (Sdd r) r)
    (hode : ∀ r, Sdd r = -K * S r)
    {r : ℝ} (hSne : S r ≠ 0) :
    HasDerivAt (fun s => Sd s / S s) (-K - (Sd r / S r) ^ 2) r := by
  have hdiv : HasDerivAt (fun s => Sd s / S s)
      ((Sdd r * S r - Sd r * Sd r) / S r ^ 2) r :=
    (hSd r).div (hS r) hSne
  convert hdiv using 1
  rw [hode r]
  field_simp

/-- **The `(n−1)`-scaled Raychaudhuri expansion ODE (division-free form).**  The congruence
expansion `θ := (n−1)·u` with `u = S'/S` obeys `θ' = (n−1)·(−K − u²)`.  In constant curvature
`(n−1)K = Ric(∂_r, ∂_r)`, so the coefficient is the Ricci radial source term.  This form is exact
and needs no `(n−1) ≠ 0`. -/
theorem raychaudhuri_constant_curvature (n : ℕ) (K : ℝ) (S Sd Sdd : ℝ → ℝ)
    (hS : ∀ r, HasDerivAt S (Sd r) r)
    (hSd : ∀ r, HasDerivAt Sd (Sdd r) r)
    (hode : ∀ r, Sdd r = -K * S r)
    {r : ℝ} (hSne : S r ≠ 0) :
    HasDerivAt (fun s => ((n : ℝ) - 1) * (Sd s / S s))
      (((n : ℝ) - 1) * (-K - (Sd r / S r) ^ 2)) r :=
  (jacobi_logderiv_riccati K S Sd Sdd hS hSd hode hSne).const_mul ((n : ℝ) - 1)

/-- **Textbook form of the Raychaudhuri expansion ODE.**  With `2 ≤ n` (so `(n−1) ≠ 0`), the
expansion `θ = (n−1)·u` satisfies `θ' = −(n−1)K − θ²/(n−1)`, matching the standard Raychaudhuri
equation `dθ/dr = −Ric(∂_r,∂_r) − θ²/(n−1)` for a hypersurface-orthogonal geodesic congruence
(shear- and vorticity-free in constant curvature). -/
theorem raychaudhuri_constant_curvature_theta (n : ℕ) (hn : 2 ≤ n) (K : ℝ) (S Sd Sdd : ℝ → ℝ)
    (hS : ∀ r, HasDerivAt S (Sd r) r)
    (hSd : ∀ r, HasDerivAt Sd (Sdd r) r)
    (hode : ∀ r, Sdd r = -K * S r)
    {r : ℝ} (hSne : S r ≠ 0) :
    HasDerivAt (fun s => ((n : ℝ) - 1) * (Sd s / S s))
      (-((n : ℝ) - 1) * K - (((n : ℝ) - 1) * (Sd r / S r)) ^ 2 / ((n : ℝ) - 1)) r := by
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    intro h; linarith
  have hbase := raychaudhuri_constant_curvature n K S Sd Sdd hS hSd hode hSne
  convert hbase using 1
  field_simp

/-- **Non-vacuity witness: the unit sphere `K = 1`.**  `S = sin`, `Sd = cos`, `Sdd = −sin`
realize the hypotheses of `jacobi_logderiv_riccati` with `K = 1` (the profile `sin r` on the unit
sphere), so the Riccati ODE `u' = −1 − u²` for `u = cos/sin = cot` genuinely applies. -/
theorem jacobiOde_sin :
    (∀ r, HasDerivAt Real.sin (Real.cos r) r) ∧
    (∀ r, HasDerivAt Real.cos ((fun r => -Real.sin r) r) r) ∧
    (∀ r, (fun r => -Real.sin r) r = -(1 : ℝ) * Real.sin r) :=
  ⟨fun r => Real.hasDerivAt_sin r, fun r => Real.hasDerivAt_cos r, fun r => by rw [neg_one_mul]⟩

end QIQTH.RaychaudhuriConstCurv
