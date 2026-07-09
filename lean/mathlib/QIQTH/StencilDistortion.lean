/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# STENCIL DISTORTION — the uniform distortion bound and its vanishing limit (brick I3)

Third brick of the ISOTROPY campaign (`docs/qg_roadmap/ISOTROPY_STENCIL_PLAN.md`).  Bricks I1/I2
pinched the stencil hop metric between two Euclidean multiples:

    eucl x y ≤ R · dist x y            (I1, `eucl_le_R_mul_dist` + `stencil_reachable`)
    dist x y ≤ eucl x y/(R−2) + 1      (I2, `stencil_dist_le`)

This file combines them into a **uniform two-sided pinch for the scaled hop metric**
`(R/N)·dist` against the scaled Euclidean metric `eucl/N` (`scaled_dist_pinch`), specializes to
the microscopic-stencil schedule `R_N = Nat.sqrt N` (`scaled_dist_sub_eucl_le`, with the explicit
`distortionError N = 4/(√N−2) + √N/N`), proves the error vanishes
(`distortionError_tendsto_zero`), and packages the headline ε-N₀ statement
(`stencil_scaled_metric_tendsto_eucl`): the scaled stencil hop metric converges to the Euclidean
metric **uniformly in the pair of lattice points**.

## Scope firewall (HONEST)

This is finite lattice combinatorics plus elementary real limits.  The distortion bound is
uniform over lattice pairs, but the statement compares metrics on a PRESUPPOSED Euclidean plane —
it is NOT intrinsic isotropy emergence, NOT a Gromov–Hausdorff limit, NOT QG.  No axioms, no
`sorry`.
-/
import QIQTH.StencilWalk
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace QIQTH.StencilDistortion

open QIQTH.StencilGraph QIQTH.StencilWalk Filter Topology

/-! ## Part 1 — the pinch (fixed `N`, `R`) -/

/-- **The lattice diameter bound.**  Both coordinates of a lattice point lie in `[0, N]`, so the
Euclidean distance between any two lattice points is at most `√(N² + N²) ≤ 2N`. -/
lemma eucl_le_two_N {N : ℕ} (x y : Fin (N + 1) × Fin (N + 1)) :
    eucl N x y ≤ 2 * (N : ℝ) := by
  have hx1 : ((x.1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp x.1.isLt
  have hy1 : ((y.1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp y.1.isLt
  have hx2 : ((x.2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp x.2.isLt
  have hy2 : ((y.2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp y.2.isLt
  have hx1' : (0 : ℝ) ≤ ((x.1 : ℕ) : ℝ) := by positivity
  have hy1' : (0 : ℝ) ≤ ((y.1 : ℕ) : ℝ) := by positivity
  have hx2' : (0 : ℝ) ≤ ((x.2 : ℕ) : ℝ) := by positivity
  have hy2' : (0 : ℝ) ≤ ((y.2 : ℕ) : ℝ) := by positivity
  have h1 : ((x.1 : ℝ) - (y.1 : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  have h2 : ((x.2 : ℝ) - (y.2 : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  rw [eucl_eq_sqrt]
  calc Real.sqrt (((x.1 : ℝ) - (y.1 : ℝ)) ^ 2 + ((x.2 : ℝ) - (y.2 : ℝ)) ^ 2)
      ≤ Real.sqrt ((2 * (N : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (N : ℝ)])
    _ = 2 * (N : ℝ) := Real.sqrt_sq (by positivity)

/-- **THE PINCH (fixed `N`, `R`).**  For `R ≥ 3` and `N ≥ 1` the scaled hop metric `(R/N)·dist`
is pinched against the scaled Euclidean metric `eucl/N`, with additive error
`4/(R−2) + R/N` — I1's lower bound and I2's upper bound divided through by `N`, plus the lattice
diameter bound `eucl ≤ 2N` to make the error UNIFORM in `x y`. -/
theorem scaled_dist_pinch {N R : ℕ} (hR : 3 ≤ R) (hN : 1 ≤ N)
    (x y : Fin (N + 1) × Fin (N + 1)) :
    eucl N x y / (N : ℝ) ≤ ((R : ℝ) / (N : ℝ)) * ((stencilGraph N R).dist x y : ℝ)
    ∧ ((R : ℝ) / (N : ℝ)) * ((stencilGraph N R).dist x y : ℝ)
        ≤ eucl N x y / (N : ℝ) + (4 / ((R : ℝ) - 2) + (R : ℝ) / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hR3 : (3 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hR2 : (0 : ℝ) < (R : ℝ) - 2 := by linarith
  constructor
  · -- LOWER: I1 `eucl ≤ R·dist`, divided by `N`
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNpos]
    exact eucl_le_R_mul_dist N R (stencil_reachable hR x y)
  · -- UPPER: I2 `dist ≤ eucl/(R−2) + 1`, multiplied by `R/N`, plus `eucl ≤ 2N`
    have hup : ((stencilGraph N R).dist x y : ℝ) ≤ eucl N x y / ((R : ℝ) - 2) + 1 :=
      stencil_dist_le hR x y
    have heucl0 : 0 ≤ eucl N x y := by rw [eucl_eq_sqrt]; exact Real.sqrt_nonneg _
    have h2N : eucl N x y ≤ 2 * (N : ℝ) := eucl_le_two_N x y
    -- clear the `(R−2)` denominator in I2
    have hup' : ((stencilGraph N R).dist x y : ℝ) * ((R : ℝ) - 2)
        ≤ eucl N x y + ((R : ℝ) - 2) := by
      have h := mul_le_mul_of_nonneg_right hup hR2.le
      rwa [add_mul, one_mul, div_mul_cancel₀ _ hR2.ne'] at h
    -- the polynomial (denominator-free) form of the upper bound
    have hpoly : (R : ℝ) * (((stencilGraph N R).dist x y : ℝ) * ((R : ℝ) - 2))
        ≤ eucl N x y * ((R : ℝ) - 2) + 4 * (N : ℝ) + (R : ℝ) * ((R : ℝ) - 2) := by
      have hR0 : (0 : ℝ) ≤ (R : ℝ) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hup' hR0, h2N, heucl0, hR2.le]
    -- divide back through by `N·(R−2) > 0`
    rw [← sub_nonneg]
    have key : eucl N x y / (N : ℝ) + (4 / ((R : ℝ) - 2) + (R : ℝ) / (N : ℝ))
          - ((R : ℝ) / (N : ℝ)) * ((stencilGraph N R).dist x y : ℝ)
        = (eucl N x y * ((R : ℝ) - 2) + 4 * (N : ℝ) + (R : ℝ) * ((R : ℝ) - 2)
            - (R : ℝ) * (((stencilGraph N R).dist x y : ℝ) * ((R : ℝ) - 2)))
          / ((N : ℝ) * ((R : ℝ) - 2)) := by
      have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
      have hR2ne : ((R : ℝ) - 2) ≠ 0 := hR2.ne'
      field_simp
      ring
    rw [key]
    exact div_nonneg (sub_nonneg.mpr hpoly) (mul_nonneg hNpos.le hR2.le)

/-! ## Part 2 — the distortion error of the microscopic-stencil schedule `R_N = √N` -/

/-- **The distortion error** of the microscopic-stencil schedule `R_N = Nat.sqrt N`:
`4/(√N − 2) + √N/N`.  Both summands vanish as `N → ∞`. -/
noncomputable def distortionError (N : ℕ) : ℝ :=
  4 / ((Nat.sqrt N : ℝ) - 2) + (Nat.sqrt N : ℝ) / (N : ℝ)

/-- **The uniform distortion bound.**  For `N ≥ 9` (so `Nat.sqrt N ≥ 3`) the scaled hop metric of
the `R_N = Nat.sqrt N` stencil deviates from the scaled Euclidean metric by at most
`distortionError N`, UNIFORMLY in the lattice pair `x y`. -/
theorem scaled_dist_sub_eucl_le {N : ℕ} (hN : 9 ≤ N) (x y : Fin (N + 1) × Fin (N + 1)) :
    |((Nat.sqrt N : ℝ) / (N : ℝ)) * ((stencilGraph N (Nat.sqrt N)).dist x y : ℝ)
        - eucl N x y / (N : ℝ)| ≤ distortionError N := by
  have hR : 3 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hlo, hhi⟩ := scaled_dist_pinch hR hN1 x y
  have hnn : 0 ≤ ((Nat.sqrt N : ℝ) / (N : ℝ)) * ((stencilGraph N (Nat.sqrt N)).dist x y : ℝ)
      - eucl N x y / (N : ℝ) := by linarith
  rw [abs_of_nonneg hnn]
  unfold distortionError
  linarith

/-- `Nat.sqrt` tends to infinity. -/
lemma tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop :=
  Filter.tendsto_atTop_atTop.mpr fun b => ⟨b * b, fun _ hn => Nat.le_sqrt.mpr hn⟩

/-- **The distortion error vanishes**: `distortionError N → 0` as `N → ∞`.
`4/(√N−2) → 0` since `√N → ∞`, and `√N/N ≤ 1/√(N:ℝ) → 0` by squeeze. -/
theorem distortionError_tendsto_zero : Tendsto distortionError atTop (𝓝 0) := by
  -- the cast natural square root tends to infinity
  have hs : Tendsto (fun N : ℕ => ((Nat.sqrt N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop
  -- first summand: 4/(√N − 2) → 0
  have h1 : Tendsto (fun N : ℕ => 4 / ((Nat.sqrt N : ℝ) - 2)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ) - 2) atTop atTop := by
      apply Filter.tendsto_atTop_add_const_right
      exact hs
    have h4 : Tendsto (fun N : ℕ => (4 : ℝ) * ((Nat.sqrt N : ℝ) - 2)⁻¹) atTop
        (𝓝 ((4 : ℝ) * 0)) := h2.inv_tendsto_atTop.const_mul (4 : ℝ)
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

/-! ## Part 3 — the I3 capstone -/

/-- **THE I3 THEOREM (uniform convergence of the scaled stencil metric to the Euclidean
metric).**  With the microscopic-stencil schedule `R_N = Nat.sqrt N`, for every `ε > 0` there is
an `N₀` such that for ALL `N ≥ N₀` and ALL lattice pairs `x y` simultaneously, the scaled hop
metric `(√N/N)·dist` is within `ε` of the scaled Euclidean metric `eucl/N`. -/
theorem stencil_scaled_metric_tendsto_eucl :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ x y : Fin (N + 1) × Fin (N + 1),
      |((Nat.sqrt N : ℝ) / (N : ℝ)) * ((stencilGraph N (Nat.sqrt N)).dist x y : ℝ)
          - eucl N x y / (N : ℝ)| < ε := by
  intro ε hε
  have hev : ∀ᶠ N : ℕ in atTop, distortionError N < ε :=
    distortionError_tendsto_zero.eventually (gt_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hev.and (eventually_ge_atTop 9))
  exact ⟨N₀, fun N hN x y =>
    lt_of_le_of_lt (scaled_dist_sub_eucl_le (hN₀ N hN).2 x y) (hN₀ N hN).1⟩

end QIQTH.StencilDistortion
