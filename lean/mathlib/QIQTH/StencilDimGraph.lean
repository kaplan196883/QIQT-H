/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# DIMENSION-GENERIC STENCIL GRAPH — the d-dimensional lattice, the margin, and the Euclidean
lower bound (brick G1)

First brick of the DIMENSION-GENERIC STENCIL campaign
(`docs/qg_roadmap/DIM_GENERIC_STENCIL_PLAN.md`).  The completed 2D ISOTROPY campaign (bricks
I1–I4, `QIQTH/StencilGraph.lean` and friends) is generalized here from the square
`Fin (N+1) × Fin (N+1)` to the **d-dimensional cube** `Fin d → Fin (N+1)`, embedded in
`EuclideanSpace ℝ (Fin d)`.  On this lattice we define the **increasing-stencil graph**: two
distinct lattice points are adjacent exactly when their *integer* squared Euclidean distance is
at most `R²`.  The adjacency test is a decidable integer inequality — no `Real.sqrt` enters the
graph.  The campaign's headline corollary (brick G4) specializes to `d = 3`.

## The G1 theorem (Euclidean lower bound on the hop metric)

Each hop moves at most `R` in Euclidean distance (`euclD_le_of_adj`), so by the triangle
inequality chained along any walk (`euclD_le_R_mul_walk_length`) and specialized to a shortest
walk:

    euclD x y ≤ R * (stencilGraphD d N R).dist x y        (`euclD_le_R_mul_dist`)

Connectivity of the stencil graph (hence the `Reachable` hypothesis) is deferred to brick G2,
where an explicit walk construction proves it.

## The margin

In dimension `d`, rounding a segment endpoint to the lattice moves each of the `d` coordinates
by at most `1/2`, so rounding errors scale like `√d` — a quantity we must dominate WITHOUT
`Real.sqrt` in ℕ-land.  `margin d = Nat.sqrt d + 1 = ⌊√d⌋ + 1` is the sqrt-free integer bound:
`d < (margin d)²` (`lt_margin_sq`), hence `√d ≤ margin d` over ℝ (`sqrt_le_margin`).  This is
the constant used in G2's walk estimate; here it already yields the lattice diameter bound
`euclD x y ≤ margin d · N` (`euclD_le_margin_mul_N`).

## Scope firewall (HONEST)

This is a finite combinatorial lower bound relating a graph hop-metric to Euclidean d-space.
The dimension `d` is an INPUT — the chosen lattice — NOT emergent: nothing in this campaign
says why physical space is 3-dimensional.  Isotropy is inserted by hand through the stencil
rule (the Euclidean-ball edge test), NOT emergent from a fixed local rule (impossible, per
`IsotropyNoGo`) nor from dynamics (a cited wall).  The eventual limit (brick G4) is the FLAT
cube `[0,1]^d` — NOT a curved Riemannian manifold, NOT emergent topology, NOT GR, NOT a
numerical G, NOT QG.  `Reachable` is a HYPOTHESIS here, never an axiom.  No axioms, no `sorry`.
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Sqrt

namespace QIQTH.StencilDimGraph

variable (d N R : ℕ)

/-! ## Part 1 — the integer squared distance -/

/-- integer squared Euclidean distance between lattice points of the d-cube. -/
def sqDistD (x y : Fin d → Fin (N+1)) : ℤ :=
  ∑ i, ((x i : ℤ) - (y i : ℤ))^2

/-- `sqDistD` is nonnegative — it is a sum of squares. -/
lemma sqDistD_nonneg (x y : Fin d → Fin (N+1)) : 0 ≤ sqDistD d N x y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `sqDistD` is symmetric. -/
lemma sqDistD_comm (x y : Fin d → Fin (N+1)) : sqDistD d N x y = sqDistD d N y x := by
  unfold sqDistD
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `sqDistD` of a point with itself vanishes. -/
lemma sqDistD_self (x : Fin d → Fin (N+1)) : sqDistD d N x x = 0 := by
  simp [sqDistD]

/-- `sqDistD` separates points: the sum of squares vanishes iff every coordinate agrees. -/
lemma sqDistD_eq_zero_iff (x y : Fin d → Fin (N+1)) :
    sqDistD d N x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg ((x i : ℤ) - (y i : ℤ)))).mp h
    funext i
    have hi : ((x i : ℤ) - (y i : ℤ))^2 = 0 := hall i (Finset.mem_univ i)
    have hsub : (x i : ℤ) - (y i : ℤ) = 0 := by
      exact sq_eq_zero_iff.mp hi
    have hZ : ((x i : ℕ) : ℤ) = ((y i : ℕ) : ℤ) := by
      have := sub_eq_zero.mp hsub
      exact_mod_cast this
    have hN : (x i : ℕ) = (y i : ℕ) := by exact_mod_cast hZ
    exact Fin.ext hN
  · rintro rfl
    exact sqDistD_self d N x

/-! ## Part 2 — the stencil graph -/

/-- **The d-dimensional increasing-stencil graph**: adjacent iff distinct and within Euclidean
radius `R` (integer test, no `Real.sqrt`). -/
def stencilGraphD : SimpleGraph (Fin d → Fin (N+1)) where
  Adj x y := x ≠ y ∧ sqDistD d N x y ≤ (R : ℤ)^2
  symm := fun x y ⟨hne, hle⟩ => ⟨hne.symm, by rw [sqDistD_comm d N y x]; exact hle⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- The stencil adjacency is decidable — it is an integer test on a finite function type. -/
instance : DecidableRel (stencilGraphD d N R).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ sqDistD d N x y ≤ (R : ℤ)^2))

/-! ## Part 3 — the Euclidean embedding -/

/-- the lattice point embedded in Euclidean d-space. -/
noncomputable def embD (x : Fin d → Fin (N+1)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => ((x i : ℕ) : ℝ))

/-- coordinates of the embedded lattice point. -/
lemma embD_apply (x : Fin d → Fin (N+1)) (i : Fin d) :
    embD d N x i = ((x i : ℕ) : ℝ) := rfl

/-- the Euclidean distance between embedded lattice points. -/
noncomputable def euclD (x y : Fin d → Fin (N+1)) : ℝ := dist (embD d N x) (embD d N y)

/-- The Euclidean distance between embedded lattice points, written out as a square root. -/
lemma euclD_eq_sqrt (x y : Fin d → Fin (N+1)) :
    euclD d N x y = Real.sqrt (∑ i, (((x i : ℕ) : ℝ) - ((y i : ℕ) : ℝ))^2) := by
  unfold euclD
  rw [EuclideanSpace.dist_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [embD_apply, embD_apply, Real.dist_eq, sq_abs]

/-- `euclD` is nonnegative. -/
lemma euclD_nonneg (x y : Fin d → Fin (N+1)) : 0 ≤ euclD d N x y := dist_nonneg

/-- `euclD` is symmetric. -/
lemma euclD_comm (x y : Fin d → Fin (N+1)) : euclD d N x y = euclD d N y x := dist_comm _ _

/-- **The cast bridge**: the square of the real Euclidean distance IS the integer squared
distance, cast to ℝ.  This is what lets the integer adjacency test talk to the real metric. -/
lemma euclD_sq_eq_sqDistD (x y : Fin d → Fin (N+1)) :
    euclD d N x y ^ 2 = ((sqDistD d N x y : ℤ) : ℝ) := by
  have hcast : ((sqDistD d N x y : ℤ) : ℝ)
      = ∑ i, (((x i : ℕ) : ℝ) - ((y i : ℕ) : ℝ))^2 := by
    unfold sqDistD
    push_cast
    rfl
  rw [euclD_eq_sqrt, Real.sq_sqrt (by positivity), hcast]

/-! ## Part 4 — the margin -/

/-- **The margin** `⌊√d⌋ + 1`: the sqrt-free integer upper bound for `√d`, used to dominate
d-dimensional rounding errors in brick G2 and the diameter bound below. -/
def margin (d : ℕ) : ℕ := Nat.sqrt d + 1

/-- The margin is positive. -/
lemma one_le_margin : 1 ≤ margin d := Nat.le_add_left 1 _

/-- `d < (margin d)²` — the defining property of the integer square root, in `^2` form. -/
lemma lt_margin_sq : d < (margin d)^2 := Nat.lt_succ_sqrt' d

/-- `√d ≤ margin d` over ℝ — the sqrt-free domination of `√d`. -/
lemma sqrt_le_margin : Real.sqrt (d : ℝ) ≤ (margin d : ℝ) := by
  have h : (d : ℝ) ≤ ((margin d : ℕ) : ℝ)^2 := by
    exact_mod_cast (lt_margin_sq d).le
  calc Real.sqrt (d : ℝ) ≤ Real.sqrt (((margin d : ℕ) : ℝ)^2) := Real.sqrt_le_sqrt h
    _ = ((margin d : ℕ) : ℝ) := Real.sqrt_sq (by positivity)

/-! ## Part 5 — the Euclidean lower bound (the G1 chain) -/

/-- **Each hop moves at most `R` in Euclidean distance.**  Cast the integer stencil test
`sqDistD ≤ R²` through the cast bridge and take square roots. -/
lemma euclD_le_of_adj {x y : Fin d → Fin (N+1)} (h : (stencilGraphD d N R).Adj x y) :
    euclD d N x y ≤ (R : ℝ) := by
  have hsq : euclD d N x y ^ 2 ≤ (R : ℝ)^2 := by
    rw [euclD_sq_eq_sqDistD]
    exact_mod_cast h.2
  have h0 : 0 ≤ euclD d N x y := euclD_nonneg d N x y
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq h0, Real.sqrt_sq (by positivity)] at this

/-- **Any walk of `k` hops moves at most `R·k` in Euclidean distance** — triangle inequality
chained along the walk, each hop bounded by `euclD_le_of_adj`. -/
lemma euclD_le_R_mul_walk_length {x y : Fin d → Fin (N+1)}
    (w : (stencilGraphD d N R).Walk x y) :
    euclD d N x y ≤ (R : ℝ) * w.length := by
  induction w with
  | nil => simp [euclD]
  | @cons a b c hadj p ih =>
      have htri : euclD d N a c ≤ euclD d N a b + euclD d N b c := dist_triangle _ _ _
      have h1 : euclD d N a b ≤ (R : ℝ) := euclD_le_of_adj d N R hadj
      have hlen : (((SimpleGraph.Walk.cons hadj p).length : ℕ) : ℝ) = (p.length : ℝ) + 1 := by
        rw [SimpleGraph.Walk.length_cons]; push_cast; ring
      rw [hlen, mul_add, mul_one, add_comm ((R : ℝ) * (p.length : ℝ)) (R : ℝ)]
      exact htri.trans (add_le_add h1 ih)

/-- **THE G1 THEOREM (Euclidean lower bound on the hop metric).**  If `x` and `y` are reachable
in the d-dimensional stencil graph, the Euclidean distance between their embeddings is at most
`R` times the graph hop-distance.  Connectivity (discharging `Reachable`) is brick G2. -/
theorem euclD_le_R_mul_dist {x y : Fin d → Fin (N+1)}
    (hreach : (stencilGraphD d N R).Reachable x y) :
    euclD d N x y ≤ (R : ℝ) * ((stencilGraphD d N R).dist x y : ℝ) := by
  obtain ⟨w, hw⟩ := hreach.exists_walk_length_eq_dist
  have hle := euclD_le_R_mul_walk_length d N R w
  rwa [hw] at hle

/-! ## Part 6 — the lattice diameter bound -/

/-- **The lattice diameter bound.**  Every coordinate of a lattice point lies in `[0, N]`, so
each coordinate difference is at most `N` in absolute value, the sum of squares is at most
`d·N²`, and `√(d·N²) = √d·N ≤ margin d · N`. -/
lemma euclD_le_margin_mul_N (x y : Fin d → Fin (N+1)) :
    euclD d N x y ≤ (margin d : ℝ) * (N : ℝ) := by
  have hcoord : ∀ i : Fin d, (((x i : ℕ) : ℝ) - ((y i : ℕ) : ℝ))^2 ≤ (N : ℝ)^2 := by
    intro i
    have hx : ((x i : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (x i).isLt
    have hy : ((y i : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (y i).isLt
    have hx0 : (0 : ℝ) ≤ ((x i : ℕ) : ℝ) := by positivity
    have hy0 : (0 : ℝ) ≤ ((y i : ℕ) : ℝ) := by positivity
    exact sq_le_sq' (by linarith) (by linarith)
  have hsum : (∑ i, (((x i : ℕ) : ℝ) - ((y i : ℕ) : ℝ))^2) ≤ (d : ℝ) * (N : ℝ)^2 := by
    calc (∑ i, (((x i : ℕ) : ℝ) - ((y i : ℕ) : ℝ))^2)
        ≤ ∑ _i : Fin d, (N : ℝ)^2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * (N : ℝ)^2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [euclD_eq_sqrt]
  calc Real.sqrt (∑ i, (((x i : ℕ) : ℝ) - ((y i : ℕ) : ℝ))^2)
      ≤ Real.sqrt ((d : ℝ) * (N : ℝ)^2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * (N : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ (margin d : ℝ) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right (sqrt_le_margin d) (by positivity)

end QIQTH.StencilDimGraph
