/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# DIMENSION-GENERIC STENCIL DISTORTION — the uniform distortion bound and its vanishing limit
(brick G3)

Third brick of the DIMENSION-GENERIC STENCIL campaign
(`docs/qg_roadmap/DIM_GENERIC_STENCIL_PLAN.md`), generalizing the proven 2D brick
`QIQTH/StencilDistortion.lean` (I3) to the d-dimensional cube `Fin d → Fin (N+1)`.  Bricks G1/G2
pinched the d-dimensional stencil hop metric between two Euclidean multiples (`m = margin d`):

    euclD x y ≤ R · dist x y            (G1, `euclD_le_R_mul_dist` + G2's `stencilD_reachable`)
    dist x y ≤ euclD x y/(R−m) + 1      (G2, `stencilD_dist_le`)

This file combines them into a **uniform two-sided pinch for the scaled hop metric**
`(R/N)·dist` against the scaled Euclidean metric `euclD/N` (`scaledD_dist_pinch`) — the additive
error `m²/(R−m) + R/N` is UNIFORM in the lattice pair, thanks to the lattice diameter bound
`euclD ≤ m·N` (G1's `euclD_le_margin_mul_N`).  It then specializes to the microscopic-stencil
schedule `R_N = Nat.sqrt N` (`scaledD_dist_sub_euclD_le`, with the explicit
`distortionErrorD d N = m²/(√N−m) + √N/N`), proves the error vanishes for every FIXED dimension
`d` (`distortionErrorD_tendsto_zero`), and packages the headline ε-N₀ statement
(`stencilD_scaled_metric_tendsto_euclD`): for each fixed `d`, the scaled stencil hop metric
converges to the Euclidean metric **uniformly in the pair of lattice points**.

## Scope firewall (HONEST)

This is finite lattice combinatorics plus elementary real limits.  The dimension `d` is an
INPUT — the chosen lattice — NOT emergent: nothing here says why physical space is
3-dimensional.  The comparison is EXTRINSIC, against a PRESUPPOSED Euclidean d-space (the
intrinsic Gromov–Hausdorff statement is brick G4).  Isotropy is inserted by hand through the
stencil rule (the Euclidean-ball edge test), NOT emergent.  The geometry is FLAT — NOT a curved
Riemannian manifold, NOT GR, NOT a numerical `G`, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.StencilDimWalk
import QIQTH.StencilDistortion
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace QIQTH.StencilDimDistortion

open QIQTH.StencilDimGraph QIQTH.StencilDimWalk Filter Topology

variable {d N R : ℕ}

/-! ## Part 1 — the pinch (fixed `d`, `N`, `R`) -/

/-- **THE PINCH (fixed `d`, `N`, `R`).**  For `R ≥ margin d + 1` and `N ≥ 1` the scaled hop
metric `(R/N)·dist` is pinched against the scaled Euclidean metric `euclD/N`, with additive
error `m²/(R−m) + R/N` (`m = margin d`) — G1's lower bound and G2's upper bound divided through
by `N`, plus the lattice diameter bound `euclD ≤ m·N` to make the error UNIFORM in `x y`. -/
theorem scaledD_dist_pinch (hR : margin d + 1 ≤ R) (hN : 1 ≤ N)
    (x y : Fin d → Fin (N + 1)) :
    euclD d N x y / (N : ℝ) ≤ ((R : ℝ) / (N : ℝ)) * ((stencilGraphD d N R).dist x y : ℝ)
    ∧ ((R : ℝ) / (N : ℝ)) * ((stencilGraphD d N R).dist x y : ℝ)
        ≤ euclD d N x y / (N : ℝ)
          + ((margin d : ℝ) ^ 2 / ((R : ℝ) - (margin d : ℝ)) + (R : ℝ) / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hRm1 : ((margin d : ℕ) : ℝ) + 1 ≤ (R : ℝ) := by exact_mod_cast hR
  have hm0 : (0 : ℝ) ≤ (margin d : ℝ) := Nat.cast_nonneg _
  have hRm : (0 : ℝ) < (R : ℝ) - (margin d : ℝ) := by linarith
  constructor
  · -- LOWER: G1 `euclD ≤ R·dist` (reachability from G2), divided by `N`
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNpos]
    exact euclD_le_R_mul_dist d N R (stencilD_reachable hR x y)
  · -- UPPER: G2 `dist ≤ euclD/(R−m) + 1`, multiplied by `R/N`, plus `euclD ≤ m·N`
    have hup : ((stencilGraphD d N R).dist x y : ℝ)
        ≤ euclD d N x y / ((R : ℝ) - (margin d : ℝ)) + 1 := stencilD_dist_le hR x y
    have heucl0 : 0 ≤ euclD d N x y := euclD_nonneg d N x y
    have hmN : euclD d N x y ≤ (margin d : ℝ) * (N : ℝ) := euclD_le_margin_mul_N d N x y
    -- clear the `(R−m)` denominator in G2
    have hup' : ((stencilGraphD d N R).dist x y : ℝ) * ((R : ℝ) - (margin d : ℝ))
        ≤ euclD d N x y + ((R : ℝ) - (margin d : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hup hRm.le
      rwa [add_mul, one_mul, div_mul_cancel₀ _ hRm.ne'] at h
    -- the polynomial (denominator-free) form of the upper bound
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
    have hpoly : (R : ℝ) * (((stencilGraphD d N R).dist x y : ℝ) * ((R : ℝ) - (margin d : ℝ)))
        ≤ euclD d N x y * ((R : ℝ) - (margin d : ℝ)) + (margin d : ℝ) ^ 2 * (N : ℝ)
          + (R : ℝ) * ((R : ℝ) - (margin d : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hup' hR0,
        mul_le_mul_of_nonneg_left hmN hm0, heucl0, hRm.le]
    -- divide back through by `N·(R−m) > 0`
    rw [← sub_nonneg]
    have key : euclD d N x y / (N : ℝ)
          + ((margin d : ℝ) ^ 2 / ((R : ℝ) - (margin d : ℝ)) + (R : ℝ) / (N : ℝ))
          - ((R : ℝ) / (N : ℝ)) * ((stencilGraphD d N R).dist x y : ℝ)
        = (euclD d N x y * ((R : ℝ) - (margin d : ℝ)) + (margin d : ℝ) ^ 2 * (N : ℝ)
            + (R : ℝ) * ((R : ℝ) - (margin d : ℝ))
            - (R : ℝ) * (((stencilGraphD d N R).dist x y : ℝ)
                * ((R : ℝ) - (margin d : ℝ))))
          / ((N : ℝ) * ((R : ℝ) - (margin d : ℝ))) := by
      have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
      have hRmne : ((R : ℝ) - (margin d : ℝ)) ≠ 0 := hRm.ne'
      field_simp
      ring
    rw [key]
    exact div_nonneg (sub_nonneg.mpr hpoly) (mul_nonneg hNpos.le hRm.le)

/-! ## Part 2 — the distortion error of the microscopic-stencil schedule `R_N = √N` -/

/-- **The distortion error** of the microscopic-stencil schedule `R_N = Nat.sqrt N` in dimension
`d`: `m²/(√N − m) + √N/N` with `m = margin d`.  For each FIXED `d`, both summands vanish as
`N → ∞`. -/
noncomputable def distortionErrorD (d N : ℕ) : ℝ :=
  (margin d : ℝ) ^ 2 / ((Nat.sqrt N : ℝ) - (margin d : ℝ)) + (Nat.sqrt N : ℝ) / (N : ℝ)

/-- **The uniform distortion bound.**  For `N ≥ (margin d + 1)²` (so
`Nat.sqrt N ≥ margin d + 1`) the scaled hop metric of the `R_N = Nat.sqrt N` stencil deviates
from the scaled Euclidean metric by at most `distortionErrorD d N`, UNIFORMLY in the lattice
pair `x y`. -/
theorem scaledD_dist_sub_euclD_le (hN : (margin d + 1) ^ 2 ≤ N)
    (x y : Fin d → Fin (N + 1)) :
    |((Nat.sqrt N : ℝ) / (N : ℝ)) * ((stencilGraphD d N (Nat.sqrt N)).dist x y : ℝ)
        - euclD d N x y / (N : ℝ)| ≤ distortionErrorD d N := by
  have hR : margin d + 1 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by rw [← pow_two]; exact hN)
  have hN1 : 1 ≤ N :=
    le_trans (Nat.one_le_pow 2 (margin d + 1) (by omega)) hN
  obtain ⟨hlo, hhi⟩ := scaledD_dist_pinch hR hN1 x y
  have hnn : 0 ≤ ((Nat.sqrt N : ℝ) / (N : ℝ))
      * ((stencilGraphD d N (Nat.sqrt N)).dist x y : ℝ) - euclD d N x y / (N : ℝ) := by
    linarith
  rw [abs_of_nonneg hnn]
  unfold distortionErrorD
  linarith

/-- **The distortion error vanishes for every fixed dimension**:
`distortionErrorD d N → 0` as `N → ∞`.  `m²/(√N−m) → 0` since `√N → ∞` and `m` is a constant,
and `√N/N ≤ 1/√(N:ℝ) → 0` by squeeze. -/
theorem distortionErrorD_tendsto_zero (d : ℕ) :
    Tendsto (distortionErrorD d) atTop (𝓝 0) := by
  -- the cast natural square root tends to infinity
  have hs : Tendsto (fun N : ℕ => ((Nat.sqrt N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp QIQTH.StencilDistortion.tendsto_natSqrt_atTop
  -- first summand: m²/(√N − m) → 0
  have h1 : Tendsto (fun N : ℕ => (margin d : ℝ) ^ 2 / ((Nat.sqrt N : ℝ) - (margin d : ℝ)))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ) - (margin d : ℝ)) atTop atTop := by
      apply Filter.tendsto_atTop_add_const_right
      exact hs
    have h4 : Tendsto
        (fun N : ℕ => (margin d : ℝ) ^ 2 * ((Nat.sqrt N : ℝ) - (margin d : ℝ))⁻¹) atTop
        (𝓝 ((margin d : ℝ) ^ 2 * 0)) := h2.inv_tendsto_atTop.const_mul ((margin d : ℝ) ^ 2)
    simpa [div_eq_mul_inv] using h4
  -- second summand: √N/N → 0, squeezed under 1/√(N:ℝ)
  have h5 : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    have hub : Tendsto (fun N : ℕ => 1 / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
      have h6 : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simp only [one_div]
      exact h6.inv_tendsto_atTop
    refine squeeze_zero' ?_ ?_ hub
    · exact Filter.Eventually.of_forall fun n => by positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
      rw [div_le_div_iff₀ hnpos hspos]
      have hle : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := Real.nat_sqrt_le_real_sqrt
      have hmul : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt hnpos.le
      nlinarith [mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg ((n : ℕ) : ℝ)), hmul]
  -- combine
  have h7 := h1.add h5
  rw [add_zero] at h7
  exact h7

/-! ## Part 3 — the G3 capstone -/

/-- **THE G3 THEOREM (uniform convergence of the scaled stencil metric to the Euclidean metric,
every fixed dimension).**  With the microscopic-stencil schedule `R_N = Nat.sqrt N`, for every
fixed dimension `d` and every `ε > 0` there is an `N₀` such that for ALL `N ≥ N₀` and ALL
lattice pairs `x y` simultaneously, the scaled hop metric `(√N/N)·dist` is within `ε` of the
scaled Euclidean metric `euclD/N`. -/
theorem stencilD_scaled_metric_tendsto_euclD (d : ℕ) :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ x y : Fin d → Fin (N + 1),
      |((Nat.sqrt N : ℝ) / (N : ℝ)) * ((stencilGraphD d N (Nat.sqrt N)).dist x y : ℝ)
          - euclD d N x y / (N : ℝ)| < ε := by
  intro ε hε
  have hev : ∀ᶠ N : ℕ in atTop, distortionErrorD d N < ε :=
    (distortionErrorD_tendsto_zero d).eventually (gt_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp (hev.and (eventually_ge_atTop ((margin d + 1) ^ 2)))
  exact ⟨N₀, fun N hN x y =>
    lt_of_le_of_lt (scaledD_dist_sub_euclD_le (hN₀ N hN).2 x y) (hN₀ N hN).1⟩

end QIQTH.StencilDimDistortion
