/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# C1 + C2 — the CONTINUUM LIMIT of the entanglement chain (Hausdorff + Gromov–Hausdorff)

The metric-from-state results (`MetricRefinement.lean`) prove the chain's state-derived metric equals
the continuum metric AT the grid points — a **sampling** statement, not a limit.  This file makes the
genuine move to the continuum: the grid point sets `chainGridSet N ⊂ [0,1]` become arbitrarily fine
**ε-nets** of the unit interval (`ε = 1/(N-1) → 0`), so

* **C1 (Hausdorff, ambient):** `hausdorffDist (chainGridSet N) (Icc 0 1) → 0` — the finite entanglement
  geometries converge, in Hausdorff distance, to the continuum interval `[0,1]` (with its standard
  metric), and
* **C2 (Gromov–Hausdorff, intrinsic):** `toGHSpace (chainGridSet N) → toGHSpace (Icc 0 1)` in Mathlib's
  `GHSpace` — the *abstract* finite metric spaces converge to the continuum interval as metric spaces.

Since the chain metric is already `= |i/(N-1) − j/(N-1)|` (`chain_scaledDist_eq_interval`), the
grid sets carry exactly the restricted interval metric; C1/C2 upgrade that from sampling to a genuine
**continuum limit**.

## HONEST scope (binding)

* This is a **1D** limit.  In 1D the interval `[0,1]` with its standard metric IS a genuine flat
  Riemannian 1-manifold, and L¹ = Euclidean, so — unlike the ≥2D case — NO "taxicab ≠ Riemannian"
  caveat is needed here; the 1D continuum is honestly Riemannian (trivially, being 1-dimensional).
* It is NOT ≥2D Riemannian geometry: the 2D box-product limit is the **L¹/taxicab** square, which is
  Finsler, NOT Riemannian — the square lattice cannot GH-converge to the round metric (isotropy
  restoration is research-grade; see `CONTINUUM_LIMIT_UNDERSTANDING.md`).
* The continuum target `[0,1]` (its topology/dimension/metric) is PRESUPPOSED — this is embedded
  convergence to a chosen continuum, not intrinsic emergence of dimension/topology.
* The entanglement pattern is engineered (dynamical source open).  NOT GR, NOT numerical-G, NOT QG.
-/
import QIQTH.MetricRefinement
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace QIQTH.ContinuumLimit

open Metric Set Filter Topology

/-- **The chain grid points** `{ i/(N-1) : i ∈ Fin N } ⊂ ℝ` — the equally-spaced sample points of the
`N`-site entanglement chain, as a subset of the continuum. -/
noncomputable def chainGridSet (N : ℕ) : Set ℝ :=
  (fun i : Fin N => (i.val : ℝ) / ((N : ℝ) - 1)) '' Set.univ

/-- Each grid point lies in the unit interval `[0,1]` (for `N ≥ 2`). -/
theorem chainGridSet_subset_Icc {N : ℕ} (hN : 2 ≤ N) : chainGridSet N ⊆ Set.Icc (0 : ℝ) 1 := by
  rintro x ⟨i, -, rfl⟩
  have hden : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hile : (i.val : ℝ) ≤ (N : ℝ) - 1 := by
    have : i.val ≤ N - 1 := Nat.le_sub_one_of_lt i.isLt
    have hc : (i.val : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast this
    rwa [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at hc
  constructor
  · positivity
  · rw [div_le_one hden]; exact hile

/-- **Net density.**  Every point of `[0,1]` is within `1/(N-1)` of a chain grid point — the grid is a
`1/(N-1)`-net of the interval.  (Round `x·(N-1)` to the nearest integer; it lands in `Fin N`.) -/
theorem chainGridSet_net {N : ℕ} (hN : 2 ≤ N) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ y ∈ chainGridSet N, dist x y ≤ 1 / ((N : ℝ) - 1) := by
  have hden : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  obtain ⟨hx0, hx1⟩ := hx
  -- the nearest grid index
  set k : ℤ := round (x * ((N : ℝ) - 1)) with hk
  have hknn : 0 ≤ k := by
    rw [hk, round_eq, Int.le_floor]
    push_cast
    have : (0 : ℝ) ≤ x * ((N : ℝ) - 1) := by positivity
    linarith
  have hkle : k ≤ (N : ℤ) - 1 := by
    have hxle : x * ((N : ℝ) - 1) ≤ (N : ℝ) - 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hx1 (le_of_lt hden)]
    have : (k : ℝ) ≤ x * ((N : ℝ) - 1) + 1 / 2 := by rw [hk]; exact round_le_add_half _
    have hkr : (k : ℝ) ≤ (N : ℝ) - 1 / 2 := by linarith
    have : k ≤ (N : ℤ) - 1 := by
      by_contra hc
      push_neg at hc
      have : (N : ℤ) ≤ k := by omega
      have : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
      linarith
    exact this
  -- as a Fin N
  have hkN : k.toNat < N := by omega
  refine ⟨(k.toNat : ℝ) / ((N : ℝ) - 1), ⟨⟨k.toNat, hkN⟩, Set.mem_univ _, rfl⟩, ?_⟩
  have hktoNat : ((k.toNat : ℝ)) = (k : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hknn]
  rw [Real.dist_eq, hktoNat]
  rw [show x - (k : ℝ) / ((N : ℝ) - 1) = (x * ((N : ℝ) - 1) - (k : ℝ)) / ((N : ℝ) - 1) by
    field_simp]
  rw [abs_div, abs_of_pos hden, div_le_div_iff_of_pos_right hden]
  have hround : |x * ((N : ℝ) - 1) - (k : ℝ)| ≤ 1 / 2 := by
    rw [hk]; exact abs_sub_round _
  calc |x * ((N : ℝ) - 1) - (k : ℝ)| ≤ 1 / 2 := hround
    _ ≤ 1 := by norm_num

/-- **C1 — the Hausdorff continuum limit.**  The Hausdorff distance between the `N`-site chain grid and
the unit interval is `≤ 1/(N-1)`: the finite entanglement geometries converge, in the ambient metric,
to the continuum interval `[0,1]`. -/
theorem hausdorffDist_chainGridSet_le {N : ℕ} (hN : 2 ≤ N) :
    hausdorffDist (chainGridSet N) (Set.Icc (0 : ℝ) 1) ≤ 1 / ((N : ℝ) - 1) := by
  have hden : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  refine hausdorffDist_le_of_mem_dist (by positivity) ?_ ?_
  · -- grid points are IN the interval: distance 0 to themselves
    intro x hx
    exact ⟨x, chainGridSet_subset_Icc hN hx, by rw [dist_self]; positivity⟩
  · -- interval points are within 1/(N-1) of a grid point (net)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := chainGridSet_net hN x hx
    exact ⟨y, hy, hxy⟩

/-- **C1 (limit form) — the chain geometry CONVERGES to the continuum interval.**
`hausdorffDist (chainGridSet N) [0,1] → 0` as `N → ∞`.  This is the genuine continuum limit: no longer
a sampling equality, but convergence of the finite entanglement metric spaces to `[0,1]`. -/
theorem hausdorffDist_chainGridSet_tendsto :
    Tendsto (fun N : ℕ => hausdorffDist (chainGridSet N) (Set.Icc (0 : ℝ) 1)) atTop (𝓝 0) := by
  -- 0 ≤ hausdorffDist ≤ 1/(N-1) → 0, by squeeze
  have hbound : ∀ᶠ N : ℕ in atTop,
      hausdorffDist (chainGridSet N) (Set.Icc (0 : ℝ) 1) ≤ 1 / ((N : ℝ) - 1) := by
    filter_upwards [eventually_ge_atTop 2] with N hN using hausdorffDist_chainGridSet_le hN
  have hub : Tendsto (fun N : ℕ => 1 / ((N : ℝ) - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ((N : ℝ) - 1)) atTop atTop := by
      apply Filter.tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    simp only [one_div]
    exact h1.inv_tendsto_atTop
  refine squeeze_zero' ?_ hbound hub
  filter_upwards [eventually_ge_atTop 2] with N _ using hausdorffDist_nonneg

/-! ## C2 — the intrinsic Gromov–Hausdorff continuum limit

Packaging the interval and the chain grids as `NonemptyCompacts ℝ`, the ABSTRACT finite metric spaces
converge to the continuum interval in Mathlib's Gromov–Hausdorff space `GHSpace`.  Indexed by `n+2`
(always `≥ 2`), via `NonemptyCompacts.ghDist_le_nonemptyCompacts_dist` (GH distance `≤` ambient
Hausdorff distance) + C1. -/

open TopologicalSpace GromovHausdorff

/-- The unit interval `[0,1]` as a nonempty compact subset of `ℝ`. -/
noncomputable def iccNC : NonemptyCompacts ℝ :=
  ⟨⟨Set.Icc (0 : ℝ) 1, isCompact_Icc⟩, ⟨0, by norm_num⟩⟩

/-- The `(n+2)`-site chain grid as a nonempty compact subset of `ℝ` (finite ⟹ compact). -/
noncomputable def chainGridNC (n : ℕ) : NonemptyCompacts ℝ :=
  ⟨⟨chainGridSet (n + 2), ((Set.finite_univ).image _).isCompact⟩,
    ⟨_, Set.mem_image_of_mem _ (Set.mem_univ (⟨0, by omega⟩ : Fin (n + 2)))⟩⟩

/-- **C2 — the chain geometries converge to the continuum interval in Gromov–Hausdorff space.**
`toGHSpace (chainGridNC n) → toGHSpace iccNC` as `n → ∞`.  The *abstract* finite entanglement metric
spaces converge, as metric spaces (no pre-given ambient), to the continuum interval `[0,1]` — the
intrinsic continuum-emergence statement. -/
theorem toGHSpace_chainGridNC_tendsto :
    Tendsto (fun n : ℕ => (chainGridNC n).toGHSpace) atTop (𝓝 iccNC.toGHSpace) := by
  rw [tendsto_iff_dist_tendsto_zero]
  -- 0 ≤ dist(toGHSpace) ≤ hausdorffDist(grid(n+2), Icc) ≤ 1/(n+1) → 0
  have hle : ∀ n : ℕ, dist (chainGridNC n).toGHSpace iccNC.toGHSpace
      ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    calc dist (chainGridNC n).toGHSpace iccNC.toGHSpace
        ≤ dist (chainGridNC n) iccNC :=
          GromovHausdorff.ghDist_le_nonemptyCompacts_dist _ _
      _ = hausdorffDist (chainGridSet (n + 2)) (Set.Icc (0 : ℝ) 1) :=
          NonemptyCompacts.dist_eq
      _ ≤ 1 / (((n + 2 : ℕ) : ℝ) - 1) := hausdorffDist_chainGridSet_le (by omega)
      _ = 1 / ((n : ℝ) + 1) := by push_cast; ring
  have hub : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simp only [one_div]; exact h1.inv_tendsto_atTop
  refine squeeze_zero (fun n => dist_nonneg) hle hub

end QIQTH.ContinuumLimit
