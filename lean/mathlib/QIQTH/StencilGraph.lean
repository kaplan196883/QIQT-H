/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# STENCIL GRAPH — the increasing-stencil lattice graph and its Euclidean LOWER bound (brick I1)

First brick of the ISOTROPY campaign (`docs/qg_roadmap/ISOTROPY_STENCIL_PLAN.md`).  On the finite 2D
lattice `Fin (N+1) × Fin (N+1)` we define the **increasing-stencil graph**: two distinct lattice
points are adjacent exactly when their *integer* squared Euclidean distance is at most `R²`.  The
adjacency test is a decidable integer inequality — no `Real.sqrt` enters the graph.

## The I1 theorem (Euclidean lower bound on the hop metric)

Each hop moves at most `R` in Euclidean distance (`eucl_le_of_adj`), so by the triangle inequality
chained along any walk (`eucl_le_R_mul_walk_length`) and specialized to a shortest walk:

    eucl x y ≤ R * (stencilGraph N R).dist x y        (`eucl_le_R_mul_dist`)

Connectivity of the stencil graph (hence the `Reachable` hypothesis) is deferred to brick I2, where
an explicit walk construction proves it.

## Scope firewall (HONEST)

This is a finite combinatorial lower bound relating a graph hop-metric to the Euclidean plane.  It
is NOT isotropy, NOT a continuum limit, NOT QG.  `Reachable` is a HYPOTHESIS here, never an axiom.
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace QIQTH.StencilGraph

variable (N R : ℕ)

/-- integer squared Euclidean distance between lattice points. -/
def sqDist (x y : Fin (N+1) × Fin (N+1)) : ℤ :=
  ((x.1 : ℤ) - (y.1 : ℤ))^2 + ((x.2 : ℤ) - (y.2 : ℤ))^2

/-- `sqDist` is symmetric. -/
lemma sqDist_comm (x y : Fin (N+1) × Fin (N+1)) : sqDist N x y = sqDist N y x := by
  unfold sqDist; ring

/-- **The increasing-stencil graph**: adjacent iff distinct and within Euclidean radius `R`
(integer test, no `Real.sqrt`). -/
def stencilGraph : SimpleGraph (Fin (N+1) × Fin (N+1)) where
  Adj x y := x ≠ y ∧ sqDist N x y ≤ (R : ℤ)^2
  symm := fun x y ⟨hne, hle⟩ => ⟨hne.symm, by rw [sqDist_comm N y x]; exact hle⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- The stencil adjacency is decidable — it is an integer test. -/
instance : DecidableRel (stencilGraph N R).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ sqDist N x y ≤ (R : ℤ)^2))

/-- the lattice point embedded in the Euclidean plane. -/
noncomputable def emb (x : Fin (N+1) × Fin (N+1)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(x.1 : ℝ), (x.2 : ℝ)]

/-- the Euclidean distance between embedded lattice points. -/
noncomputable def eucl (x y : Fin (N+1) × Fin (N+1)) : ℝ := dist (emb N x) (emb N y)

/-- The Euclidean distance between embedded lattice points, written out as a square root. -/
lemma eucl_eq_sqrt (x y : Fin (N+1) × Fin (N+1)) :
    eucl N x y = Real.sqrt (((x.1 : ℝ) - (y.1 : ℝ))^2 + ((x.2 : ℝ) - (y.2 : ℝ))^2) := by
  unfold eucl emb
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- **Each hop moves at most `R` in Euclidean distance.**  Cast the integer stencil test
`sqDist ≤ R²` to `ℝ` and take square roots. -/
lemma eucl_le_of_adj {x y : Fin (N+1) × Fin (N+1)} (h : (stencilGraph N R).Adj x y) :
    eucl N x y ≤ (R : ℝ) := by
  have hZ : sqDist N x y ≤ (R : ℤ)^2 := h.2
  unfold sqDist at hZ
  have hR : ((x.1 : ℝ) - (y.1 : ℝ))^2 + ((x.2 : ℝ) - (y.2 : ℝ))^2 ≤ (R : ℝ)^2 := by
    exact_mod_cast hZ
  rw [eucl_eq_sqrt]
  calc Real.sqrt (((x.1 : ℝ) - (y.1 : ℝ))^2 + ((x.2 : ℝ) - (y.2 : ℝ))^2)
      ≤ Real.sqrt ((R : ℝ)^2) := Real.sqrt_le_sqrt hR
    _ = (R : ℝ) := Real.sqrt_sq (by positivity)

/-- **Any walk of `k` hops moves at most `R·k` in Euclidean distance** — triangle inequality
chained along the walk, each hop bounded by `eucl_le_of_adj`. -/
lemma eucl_le_R_mul_walk_length {x y : Fin (N+1) × Fin (N+1)}
    (w : (stencilGraph N R).Walk x y) :
    eucl N x y ≤ (R : ℝ) * w.length := by
  induction w with
  | nil => simp [eucl]
  | @cons a b c hadj p ih =>
      have htri : eucl N a c ≤ eucl N a b + eucl N b c := dist_triangle _ _ _
      have h1 : eucl N a b ≤ (R : ℝ) := eucl_le_of_adj N R hadj
      have hlen : (((SimpleGraph.Walk.cons hadj p).length : ℕ) : ℝ) = (p.length : ℝ) + 1 := by
        rw [SimpleGraph.Walk.length_cons]; push_cast; ring
      rw [hlen, mul_add, mul_one, add_comm ((R : ℝ) * (p.length : ℝ)) (R : ℝ)]
      exact htri.trans (add_le_add h1 ih)

/-- **THE I1 THEOREM (Euclidean lower bound on the hop metric).**  If `x` and `y` are reachable in
the stencil graph, the Euclidean distance between their embeddings is at most `R` times the graph
hop-distance.  Connectivity (discharging `Reachable`) is brick I2. -/
theorem eucl_le_R_mul_dist {x y : Fin (N+1) × Fin (N+1)}
    (hreach : (stencilGraph N R).Reachable x y) :
    eucl N x y ≤ (R : ℝ) * (stencilGraph N R).dist x y := by
  obtain ⟨w, hw⟩ := hreach.exists_walk_length_eq_dist
  have hle := eucl_le_R_mul_walk_length N R w
  rwa [hw] at hle

end QIQTH.StencilGraph
