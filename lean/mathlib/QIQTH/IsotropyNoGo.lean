/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The ISOTROPY no-go — the 2D box-product L¹ continuum is provably NOT Riemannian

The metric-from-state 2D result (`MetricRefinement2D.square_grid_scaledDist_eq_l1`) gives a continuum
limit that is the **L¹ / taxicab** metric on `[0,1]²`.  The natural next question — "is the emergent
≥2D geometry Riemannian (Euclidean)?" — has a rigorous **negative** answer for the square lattice, and
this file proves it: **the taxicab plane `(ℝ², L¹)` admits NO distance-preserving map into any real
inner-product (Euclidean/Riemannian) space** — not even up to positive rescaling.

## The invariant: metric midpoints

The obstruction is a pure 4-point metric fact (no convex geometry, no unit-ball shape):

* **Inner-product spaces have UNIQUE metric midpoints** — if `dist a m = dist m b = ½·dist a b` then `m`
  is the affine midpoint `½(a+b)`, by the parallelogram law (`inner_metric_midpoint_unique`).
* **The L¹ diamond has TWO** — `(0,0)` and `(1,1)` are at L¹-distance `2`, and BOTH `(1,0)` and `(0,1)`
  are metric midpoints (each at L¹-distance `1` from both), yet `(1,0) ≠ (0,1)`.

An isometry preserves midpoints, so the two distinct L¹ midpoints would collapse to one — contradiction.

## Consequence for the emergence program (HONEST)

This makes the anisotropy obstruction a THEOREM: a fixed square lattice (indeed the whole taxicab plane)
**cannot** GH-converge to a Euclidean/Riemannian metric — the ≥2D emergent geometry from this construction
is genuinely Finsler (L¹), not Riemannian.  (The 1D limit `[0,1]` IS Riemannian — flat, L¹=Euclidean in
1D — see `ContinuumLimit.lean`; the split happens at dimension ≥2.)  Getting an intrinsic Euclidean/
Riemannian limit needs an ISOTROPIC graph family (random-geometric or increasing-stencil, whose allowed
directions fill a Euclidean disk) — a research-grade phase (concentration/RGG infrastructure Mathlib
lacks), NOT a lattice fix (king-graph → L^∞, weighted diagonals → octagonal norm — all still polyhedral).
See `CONTINUUM_LIMIT_UNDERSTANDING.md`.  This file forbids the FALSE claim "the square grid gives a flat
Riemannian surface."  NOT GR, NOT numerical-G, NOT QG.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace QIQTH.IsotropyNoGo

open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **In an inner-product space a metric midpoint IS the affine midpoint.**  If `dist a m = r`,
`dist m b = r`, and `dist a b = 2r`, then `m = ½(a+b)` — by the parallelogram law (equality forces the
two half-vectors to coincide). -/
theorem inner_metric_midpoint_eq_affine_midpoint {a b m : E} {r : ℝ}
    (ham : dist a m = r) (hmb : dist m b = r) (hab : dist a b = 2 * r) :
    m = (1 / 2 : ℝ) • (a + b) := by
  set u : E := m - a with hu_def
  set v : E := b - m with hv_def
  have hu : ‖u‖ = r := by
    have : dist m a = r := by rwa [dist_comm] at ham
    simpa [hu_def, dist_eq_norm, norm_sub_rev] using this
  have hv : ‖v‖ = r := by
    have : dist b m = r := by rwa [dist_comm] at hmb
    simpa [hv_def, dist_eq_norm] using this
  have huv_add : u + v = b - a := by rw [hu_def, hv_def]; abel
  have huv : ‖u + v‖ = 2 * r := by
    rw [huv_add]
    have : dist b a = 2 * r := by rwa [dist_comm] at hab
    simpa [dist_eq_norm] using this
  have hpar := parallelogram_law_with_norm (𝕜 := ℝ) u v
  have hu2 : ‖u‖ ^ 2 = r ^ 2 := by rw [hu]
  have hv2 : ‖v‖ ^ 2 = r ^ 2 := by rw [hv]
  have huv2 : ‖u + v‖ ^ 2 = (2 * r) ^ 2 := by rw [huv]
  have hsq : ‖u - v‖ ^ 2 = 0 := by
    rw [hu2, hv2, huv2] at hpar; nlinarith [hpar]
  have hnorm : ‖u - v‖ = 0 := by
    rwa [pow_eq_zero_iff (two_ne_zero)] at hsq
  have huv_eq : u = v := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hmv : m - a = b - m := by rw [← hu_def, ← hv_def]; exact huv_eq
  have h2m : (2 : ℝ) • m = a + b := by
    have : m + m = a + b := by
      have := hmv; linear_combination (norm := abel) this
    rw [two_smul]; exact this
  have : m = (1 / 2 : ℝ) • ((2 : ℝ) • m) := by rw [smul_smul]; norm_num
  rw [this, h2m]

/-- **Inner-product spaces have UNIQUE metric midpoints.** -/
theorem inner_metric_midpoint_unique {a b m n : E} {r : ℝ}
    (ham : dist a m = r) (hmb : dist m b = r) (han : dist a n = r) (hnb : dist n b = r)
    (hab : dist a b = 2 * r) : m = n :=
  (inner_metric_midpoint_eq_affine_midpoint ham hmb hab).trans
    (inner_metric_midpoint_eq_affine_midpoint han hnb hab).symm

/-- The **L¹ (taxicab) distance** on `ℝ²` (Mathlib's default `ℝ × ℝ` metric is sup-like, so we state it
explicitly). -/
def l1Dist (p q : ℝ × ℝ) : ℝ := |p.1 - q.1| + |p.2 - q.2|

/-- **The isotropy NO-GO.**  There is NO distance-preserving map from the taxicab plane `(ℝ², L¹)` into
any real inner-product space `E` — the L¹ plane is not isometrically embeddable into ANY Euclidean/
Riemannian space.  (Stronger than "not isometric to `EuclideanSpace ℝ (Fin 2)`": it rules out every
inner-product target, in every dimension.)  Proof: the two distinct L¹ midpoints `(1,0)`, `(0,1)` of
`(0,0)`,`(1,1)` would have equal images by midpoint-uniqueness, but their L¹ distance `2 ≠ 0`. -/
theorem no_l1_isometric_embedding_into_inner
    (f : ℝ × ℝ → E) (hf : ∀ p q : ℝ × ℝ, dist (f p) (f q) = l1Dist p q) : False := by
  have hAD : dist (f (0, 0)) (f (1, 1)) = 2 * 1 := by rw [hf]; norm_num [l1Dist]
  have hAP : dist (f (0, 0)) (f (1, 0)) = 1 := by rw [hf]; norm_num [l1Dist]
  have hPD : dist (f (1, 0)) (f (1, 1)) = 1 := by rw [hf]; norm_num [l1Dist]
  have hAQ : dist (f (0, 0)) (f (0, 1)) = 1 := by rw [hf]; norm_num [l1Dist]
  have hQD : dist (f (0, 1)) (f (1, 1)) = 1 := by rw [hf]; norm_num [l1Dist]
  have hPQeq : f (1, 0) = f (0, 1) :=
    inner_metric_midpoint_unique hAP hPD hAQ hQD hAD
  have hPQ : dist (f (1, 0)) (f (0, 1)) = 2 := by rw [hf]; norm_num [l1Dist]
  rw [hPQeq, dist_self] at hPQ
  norm_num at hPQ

end QIQTH.IsotropyNoGo
