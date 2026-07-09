/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# THE INTRINSIC CONE GRAPH — the geometric graph on the polar grid and the lower bound
(brick K1, intrinsic-cone track)

Brick K1 of the INTRINSIC-CONE track (`docs/qg_roadmap/STATEWIRE2_SPHERE_INTRINSIC_CONE_PLAN.md`,
Track K).  Brick B2b (`QIQTH/ConeGH.lean`) exhibited the concentrated-positive-curvature cone
`Cone θ` as a GH limit of finite polar grids — but those clouds carried the INDUCED (pullback)
metric: exact isometric samples, honest but extrinsically metrized.  Track K builds the
**INTRINSIC story**: the geometric graph `coneGraph θ n ρ` on the polar grid, whose edges are
pure proximity (`dist x y ≤ ρ` in the cone) and whose scaled HOP metric will be shown (K2/K3)
to Gromov–Hausdorff-converge to the cone — positive curvature recovered from pure hop-counting
on a finite graph.

This brick delivers the setup:

* **The graph** (`coneGraph θ n ρ`): vertices = the polar grid `PolarGrid θ n` (apex plus
  `(n+1)·(n+2)` points), edges = distinct pairs at cone distance `≤ ρ` (the pullback metric of
  `PolarGrid θ n` IS the cone distance between the embedded points).
* **The lower bound** (`dist_le_rho_mul_dist`): each hop moves at most `ρ` in the cone
  (`dist_le_of_adj`), so chaining the triangle inequality along any walk
  (`dist_le_rho_mul_walk_length`) and specializing to a shortest walk gives
  `coneDist ≤ ρ · hopcount` — trivial but load-bearing: it is one half of the K3 pinching.
  `Reachable` stays a HYPOTHESIS here; the walk construction discharging it is brick K2.
* **The mesh and diameter facts** K2/K3 consume: `mesh θ n = 1/(n+1) + θ/(2(n+2))` with
  `mesh_pos`, the net lemma restated in mesh terms (`cone_net_mesh`), and the diameter bound
  `dist ≤ 2` on both the cone (`cone_diam`, triangle through the apex, radii `≤ 1`) and the
  grid (`polarGrid_diam`, pullback).

## Adjacency decidability is CLASSICAL

The edge test `dist x y ≤ ρ` is a real-number comparison — NOT decidable computationally.  We
provide `DecidableRel (coneGraph θ n ρ).Adj` via `Classical.dec`: the graph is a mathematical
object, not an algorithm.  This instance exists only so the state-decoder (brick K4) can
consume the graph; nothing in K1–K3 computes with it.

## Scope firewall (HONEST)

* **The cone geometry is INSERTED through the adjacency rule** (`dist x y ≤ ρ`, the cone
  metric) — exactly as isotropy was inserted through the stencil rule in the G-track.  Nothing
  about the cone is emergent from combinatorics; the combinatorics RECOVERS a geometry that was
  put in by hand.
* **`θ` is an INPUT** — a chosen deficit angle, not derived.
* **The curvature is CONCENTRATED** — an Alexandrov cone point, NOT a smooth Riemann tensor,
  NOT a Riemannian manifold.  Away from the apex the cone is flat.
* NOT GR, NOT numerical-G, NOT QG.  The walk construction (connectivity + the matching upper
  bound) is brick K2; the GH capstone is brick K3.  No axioms, no `sorry`.
-/
import QIQTH.ConeGH
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace QIQTH.ConeIntrinsicGraph

open QIQTH.ConeMetric QIQTH.ConeGH

section

variable (θ : ℝ) [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)] (n : ℕ) (ρ : ℝ)

/-! ## Part 1 — the geometric graph on the polar grid -/

/-- **The intrinsic cone graph**: the geometric graph on the polar grid `PolarGrid θ n` whose
edges join distinct points at cone distance at most `ρ` (the grid metric is the pullback along
`gridToCone`, so `dist x y` IS the cone distance between the embedded points).  Unlike the
G-track stencil (an integer test), adjacency here is a real-number comparison — the graph is a
mathematical object, not an algorithm; see the decidability note in the header. -/
noncomputable def coneGraph : SimpleGraph (PolarGrid θ n) where
  Adj x y := x ≠ y ∧ dist x y ≤ ρ
  symm := fun x y ⟨hne, hle⟩ => ⟨hne.symm, by rwa [dist_comm]⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- The adjacency of the intrinsic cone graph, unfolded. -/
lemma coneGraph_adj (x y : PolarGrid θ n) :
    (coneGraph θ n ρ).Adj x y ↔ x ≠ y ∧ dist x y ≤ ρ := Iff.rfl

/-- **Classical decidability of adjacency** — the edge test is a real-number comparison, so
this is `Classical.dec`, honest and noncomputable: the graph is a mathematical object, not an
algorithm.  Needed only so the K4 state-decoder can consume the graph. -/
noncomputable instance instDecidableRelConeGraphAdj :
    DecidableRel (coneGraph θ n ρ).Adj :=
  fun _ _ => Classical.dec _

/-! ## Part 2 — the lower bound (each hop moves at most `ρ` in the cone) -/

/-- **Each hop moves at most `ρ` in the cone** — the trivial extractor from the adjacency
rule, mirroring the G1 `euclD_le_of_adj` with the cone metric in place of `euclD`. -/
lemma dist_le_of_adj {x y : PolarGrid θ n} (h : (coneGraph θ n ρ).Adj x y) :
    dist x y ≤ ρ := h.2

set_option linter.unusedVariables false in
/-- **Any walk of `k` hops moves at most `ρ·k` in the cone** — the triangle inequality chained
along the walk, each hop bounded by `dist_le_of_adj` (the G1 walk induction, verbatim, with the
metric-space `dist_triangle` in place of the Euclidean one).  The hypothesis `0 ≤ ρ` is kept
for K2/K3 API stability (the bound is monotone data there) even though this induction happens
not to need it. -/
lemma dist_le_rho_mul_walk_length (hρ : 0 ≤ ρ) {x y : PolarGrid θ n}
    (w : (coneGraph θ n ρ).Walk x y) :
    dist x y ≤ ρ * w.length := by
  induction w with
  | nil => simp
  | @cons a b c hadj p ih =>
      have htri : dist a c ≤ dist a b + dist b c := dist_triangle a b c
      have h1 : dist a b ≤ ρ := dist_le_of_adj θ n ρ hadj
      have hlen : (((SimpleGraph.Walk.cons hadj p).length : ℕ) : ℝ)
          = (p.length : ℝ) + 1 := by
        rw [SimpleGraph.Walk.length_cons]; push_cast; ring
      rw [hlen, mul_add, mul_one, add_comm (ρ * (p.length : ℝ)) ρ]
      exact htri.trans (add_le_add h1 ih)

/-- **THE K1 LOWER BOUND (cone distance vs. hop metric).**  If `x` and `y` are reachable in
the intrinsic cone graph, the cone distance is at most `ρ` times the graph hop-distance —
one half of the K3 pinching.  Connectivity (discharging `Reachable`) is brick K2. -/
theorem dist_le_rho_mul_dist (hρ : 0 ≤ ρ) {x y : PolarGrid θ n}
    (hreach : (coneGraph θ n ρ).Reachable x y) :
    dist x y ≤ ρ * ((coneGraph θ n ρ).dist x y : ℝ) := by
  obtain ⟨w, hw⟩ := hreach.exists_walk_length_eq_dist
  have hle := dist_le_rho_mul_walk_length θ n ρ hρ w
  rwa [hw] at hle

/-! ## Part 3 — the mesh and the diameter -/

/-- **The mesh** `1/(n+1) + θ/(2(n+2))`: the net radius of the polar grid inside the cone
(brick B2b's `cone_net` bound), re-exported as a named quantity for the K2/K3 schedule. -/
noncomputable def mesh : ℝ := 1 / ((n : ℝ) + 1) + θ / (2 * ((n : ℝ) + 2))

omit [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)] in
/-- The mesh, unfolded. -/
lemma mesh_def : mesh θ n = 1 / ((n : ℝ) + 1) + θ / (2 * ((n : ℝ) + 2)) := rfl

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- The mesh is positive (needs `0 < θ`). -/
lemma mesh_pos : 0 < mesh θ n := by
  have hθ0 : (0 : ℝ) < θ := Fact.out
  have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have h2 : (0 : ℝ) < θ / (2 * ((n : ℝ) + 2)) := by positivity
  rw [mesh_def]
  linarith

/-- **The net lemma in mesh terms**: every point of the cone is within `mesh θ n` of an
embedded grid point (B2b's `cone_net`, restated). -/
lemma cone_net_mesh (p : Cone θ) :
    ∃ x : PolarGrid θ n, dist p (gridToCone θ n x) ≤ mesh θ n :=
  ConeGH.cone_net θ n p

/-- Every cone point is within `1` of the apex: the apex-to-polar distance is the radius
`r ≤ 1`. -/
lemma dist_apex_le (p : Cone θ) : dist p (none : Cone θ) ≤ 1 := by
  rcases p with _ | ⟨r, -⟩
  · rw [dist_eq_coneDist, coneDist_none_none]
    exact zero_le_one
  · rw [dist_eq_coneDist, coneDist_some_none]
    exact r.2.2

/-- **The cone diameter bound**: any two cone points are at distance `≤ 2` — triangle
inequality through the apex, both radii `≤ 1`. -/
lemma cone_diam (p q : Cone θ) : dist p q ≤ 2 := by
  have h1 : dist p (none : Cone θ) ≤ 1 := dist_apex_le θ p
  have h2 : dist q (none : Cone θ) ≤ 1 := dist_apex_le θ q
  have htri : dist p q ≤ dist p (none : Cone θ) + dist q (none : Cone θ) :=
    dist_triangle_right p q (none : Cone θ)
  linarith

/-- **The grid diameter bound**: any two grid points are at distance `≤ 2` (pullback of the
cone diameter). -/
lemma polarGrid_diam (x y : PolarGrid θ n) : dist x y ≤ 2 := by
  rw [polarGrid_dist_def]
  exact cone_diam θ _ _

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- **The mesh schedule bound** (sanity for K3): for `1 ≤ n` the mesh is at most
`(1 + θ)/n` — both summands are dominated by their `1/n` counterparts. -/
lemma mesh_le (hn : 1 ≤ n) : mesh θ n ≤ (1 + θ) / (n : ℝ) := by
  have hθ0 : (0 : ℝ) < θ := Fact.out
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) := by
    apply one_div_le_one_div_of_le hn0
    linarith
  have h2 : θ / (2 * ((n : ℝ) + 2)) ≤ θ / (n : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hn0]
    nlinarith [mul_pos hθ0 hn0]
  have hsplit : (1 + θ) / (n : ℝ) = 1 / (n : ℝ) + θ / (n : ℝ) := by ring
  rw [mesh_def, hsplit]
  exact add_le_add h1 h2

end

end QIQTH.ConeIntrinsicGraph
