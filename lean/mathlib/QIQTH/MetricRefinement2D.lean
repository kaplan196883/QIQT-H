/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# METRIC REFINEMENT 2D — the box-product state-metric refines the unit SQUARE (Track-2)

This is the higher-dimensional increment of the METRIC-FROM-STATE campaign, building on
`QIQTH.MetricRefinement` (the 1D chain, `pathGraph_dist : (pathGraph n).dist = Nat.dist`).  Here we
promote the one-dimensional chain to a two-dimensional grid via the **Cartesian / box product** of
graphs `G □ H`, and show three things:

1. (**box-product distance additivity**, `dist_boxProd_of_reachable`) the geodesic distance on `G □ H`
   splits as a sum of the factor distances: `(G □ H).dist (a,b) (c,d) = G.dist a c + H.dist b d`
   whenever the coordinates are reachable.  Mathlib already proves the *extended* distance version
   `SimpleGraph.edist_boxProd` (additivity at the `ℕ∞` level); we transport it to the honest
   `ℕ`-valued `dist` through `Reachable.coe_dist_eq_edist`, giving the Track-2 additivity crux.
2. (**the 2D grid = L¹ taxicab distance**, `pathGraph_grid_dist`) specializing both factors to path
   graphs, the box-product distance on the `m × n` grid is exactly the taxicab (L¹) integer distance
   `Nat.dist x₁ y₁ + Nat.dist x₂ y₂`.
3. (**the unit-square refinement**, `square_grid_scaledDist_eq_l1`) rescaling the `N × N` square grid
   by `N-1`, the state-decoded distance is exactly the restriction of the continuum **L¹ (taxicab)**
   metric on the unit square `[0,1]²` to the `N²` equally spaced grid points.

## Scope firewall (HONEST)

This is a **finite, two-dimensional** refinement statement: `N²` sample points of a grid state agree
exactly (in the discrete sense of grid-point equality, not a limiting/continuity argument) with the
unit square under the L¹ metric.  It is NOT a continuum limit theorem, and the additivity fact
(`dist_boxProd_of_reachable`) is a general-purpose graph fact with no physics content — the
"refinement" content is entirely in the algebraic identification of the rescaled box-product distance
with the restricted L¹ square metric.  The box-product *edist* additivity is Mathlib's
(`edist_boxProd`); our contribution is the `ℕ`-valued `dist` corollary and the geometric refinement.
-/
import QIQTH.MetricRefinement
import Mathlib.Combinatorics.SimpleGraph.Prod

namespace QIQTH.MetricRefinement2D

open SimpleGraph
open scoped SimpleGraph

/-! ## Part 1 — box-product distance additivity (transported from Mathlib's `edist_boxProd`) -/

/-- **Box-product distance additivity.** For reachable coordinates, the geodesic distance on the
box product `G □ H` is the sum of the factor distances.  Proof: Mathlib's `edist_boxProd` gives the
additivity at the extended (`ℕ∞`) level; transporting through `Reachable.coe_dist_eq_edist` (which
requires reachability so that no `⊤` appears) yields the `ℕ`-valued statement by a cast. -/
theorem dist_boxProd_of_reachable {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    {a c : α} {b d : β} (hac : G.Reachable a c) (hbd : H.Reachable b d) :
    (G □ H).dist (a, b) (c, d) = G.dist a c + H.dist b d := by
  have hr : (G □ H).Reachable (a, b) (c, d) := reachable_boxProd.mpr ⟨hac, hbd⟩
  -- cast the `ℕ`-distances to `ℕ∞`, use edist additivity, cast back
  have hcast : ((G □ H).dist (a, b) (c, d) : ℕ∞) = (G.dist a c : ℕ∞) + (H.dist b d : ℕ∞) := by
    rw [hr.coe_dist_eq_edist, hac.coe_dist_eq_edist, hbd.coe_dist_eq_edist, edist_boxProd]
  exact_mod_cast hcast

/-! ## Part 2 — the 2D path-graph grid is the taxicab (L¹) integer metric -/

/-- **The 2D grid distance is the taxicab (L¹) integer distance.** Specializing both factors of the
box product to path graphs and reusing the 1D `pathGraph_dist`: the geodesic distance on the `m × n`
grid `pathGraph m □ pathGraph n` is exactly `Nat.dist x₁ y₁ + Nat.dist x₂ y₂`. -/
theorem pathGraph_grid_dist {m n : ℕ} (x y : Fin m × Fin n) :
    (SimpleGraph.pathGraph m □ SimpleGraph.pathGraph n).dist x y
      = Nat.dist x.1.val y.1.val + Nat.dist x.2.val y.2.val := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rw [dist_boxProd_of_reachable (SimpleGraph.pathGraph_preconnected m x1 y1)
        (SimpleGraph.pathGraph_preconnected n x2 y2),
    QIQTH.MetricRefinement.pathGraph_dist, QIQTH.MetricRefinement.pathGraph_dist]

/-! ## Part 3 — the unit-square refinement: the grid state samples `[0,1]²` with the L¹ metric -/

/-- `Nat.dist` cast to `ℝ` is the real absolute difference — replicated locally from the 1D
`MetricRefinement` (there it is `private`).  This is the link between the discrete grid metric and the
continuum L¹ square metric. -/
private lemma natDist_cast_eq_abs (a b : ℕ) : (Nat.dist a b : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (by
      have : (a : ℝ) ≤ b := by exact_mod_cast h
      linarith)]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (by
      have : (b : ℝ) ≤ a := by exact_mod_cast h
      linarith)]

/-- **The unit-square L¹ refinement.** Rescaled by the grid length `N-1`, the box-product
state-metric between grid points `x, y` of the `N × N` square grid equals the standard **L¹ (taxicab)**
distance between their images `x/(N-1), y/(N-1) ∈ [0,1]²`.  So the metric that emerges from the 2D
grid state's box-product structure is not an ad hoc combinatorial number: it is the sample of a genuine
continuum L¹ metric on the unit square `[0,1]²` at `N²` equally spaced points — geometry (now in two
dimensions, with the taxicab metric) refining a continuum, as an OUTPUT of the state. -/
theorem square_grid_scaledDist_eq_l1 {N : ℕ} (x y : Fin N × Fin N) :
    ((SimpleGraph.pathGraph N □ SimpleGraph.pathGraph N).dist x y : ℝ) / ((N : ℝ) - 1)
      = |(x.1.val : ℝ) / ((N : ℝ) - 1) - (y.1.val : ℝ) / ((N : ℝ) - 1)|
        + |(x.2.val : ℝ) / ((N : ℝ) - 1) - (y.2.val : ℝ) / ((N : ℝ) - 1)| := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact x.1.elim0
  · have hc : (0 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [pathGraph_grid_dist, Nat.cast_add, add_div,
      div_sub_div_same, div_sub_div_same, abs_div, abs_div,
      abs_of_nonneg hc, ← natDist_cast_eq_abs, ← natDist_cast_eq_abs]

end QIQTH.MetricRefinement2D
