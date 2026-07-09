/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# METRIC REFINEMENT — geometry refines a continuum as an OUTPUT of the entangled chain (M4)

This is the next increment of the METRIC-FROM-STATE campaign, building on `QIQTH.MetricFromState`
(M1–M3: a cut-rank profile decodes its adjacency graph, whose geodesic distance is a genuine finite
metric).  Here we specialize the carrier graph to the **path graph** `SimpleGraph.pathGraph n` — the
chain `0 — 1 — 2 — ⋯ — (n-1)` — and show two things:

1. (**the Mathlib gap**, `pathGraph_dist`) the path graph's geodesic distance is *exactly* the integer
   line distance `Nat.dist`.  Mathlib has no such lemma; we prove it here from first principles (an
   explicit increasing walk realizes the upper bound, a triangle-inequality induction over an arbitrary
   walk realizes the lower bound).
2. (**the payoff**, `chain_scaledDist_eq_interval`) the state-decoded metric on the chain, once rescaled
   by `n-1`, is *exactly* the restriction of the unit-interval distance `|x - y|` to the grid points
   `i/(n-1)`.  So the metric that emerges from the chain's entangled cut-rank profile is not an ad hoc
   combinatorial number: it is the sample of a genuine continuum metric on `[0,1]` at `n` equally spaced
   points — "geometry refines a continuum" as an OUTPUT of the state, not a hypothesis fed in.

## Scope firewall (HONEST)

This is a **finite, one-dimensional** refinement statement: `n` sample points of a chain state converge
(in the discrete sense of exact grid-point agreement, not yet a limiting/continuity argument) onto the
unit interval with the standard metric.  It is NOT a continuum limit theorem (no `n → ∞` convergence
argument is made here), NOT higher-dimensional, and does NOT touch the dynamical source of the
entanglement profile (carried by M3, itself downstream of the state-side realization open in
`MetricFromState`).  `pathGraph_dist` is a general-purpose graph fact (no physics content); the
"refinement" content is entirely in the algebraic identification of the rescaled decoded distance with
the restricted interval metric.
-/
import QIQTH.MetricFromState
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Nat.Dist

namespace QIQTH.MetricRefinement

open QIQTH.MetricFromState QIQTH.EmergentSpacetime

/-- Adjacency of the path graph is a decidable-in-principle (arithmetic) relation; supplied classically
so `explicitProfile`'s `[DecidableRel G.Adj]` requirement is met for `G = SimpleGraph.pathGraph n`. -/
noncomputable instance pathGraph_decidableRelAdj (n : ℕ) :
    DecidableRel (SimpleGraph.pathGraph n).Adj := Classical.decRel _

/-! ## Part 1 — the Mathlib gap: `(pathGraph n).dist = Nat.dist` -/

/-- An explicit walk of length `k` in the path graph from `a` to `a + k`, built by *appending* edges via
`Walk.concat` (rather than prepending via `cons`): this keeps the `Fin`-index arithmetic definitionally
aligned, since `a + 0 = a` and `a + (k+1) = (a+k) + 1` both hold by the defining recursion of `Nat.add`,
with no separate conversion lemma needed for the endpoints. -/
private def upWalk {n : ℕ} : (a k : ℕ) → (h : a + k < n) →
    (SimpleGraph.pathGraph n).Walk (⟨a, by omega⟩ : Fin n) ⟨a + k, h⟩
  | _, 0, _ => SimpleGraph.Walk.nil
  | a, k + 1, h =>
      (upWalk a k (by omega)).concat
        (show (SimpleGraph.pathGraph n).Adj (⟨a + k, by omega⟩ : Fin n) ⟨a + k + 1, h⟩ by
          rw [SimpleGraph.pathGraph_adj]; left; rfl)

private lemma upWalk_length {n : ℕ} : (a k : ℕ) → (h : a + k < n) → (upWalk a k h).length = k
  | _, 0, _ => rfl
  | a, k + 1, h => by
      show ((upWalk a k (by omega)).concat _).length = k + 1
      rw [SimpleGraph.Walk.length_concat, upWalk_length a k (by omega)]

/-- Adjacent vertices of the path graph are at integer-line distance exactly `1`. -/
private lemma natDist_eq_one_of_adj {n} {u v : Fin n} (h : (SimpleGraph.pathGraph n).Adj u v) :
    Nat.dist u.val v.val = 1 := by
  rw [SimpleGraph.pathGraph_adj] at h
  rcases h with h | h
  · rw [← h, Nat.dist_eq_sub_of_le (Nat.le_succ u.val)]; omega
  · rw [Nat.dist_comm, ← h, Nat.dist_eq_sub_of_le (Nat.le_succ v.val)]; omega

/-- **Lower bound half.** For *any* walk between `i` and `j` in the path graph, the integer-line
distance `Nat.dist` is at most the walk's length — by induction on the walk, chaining `Nat.dist`'s
triangle inequality against the length-one steps `natDist_eq_one_of_adj`. -/
private lemma natDist_le_walk_length {n} {i j : Fin n} (w : (SimpleGraph.pathGraph n).Walk i j) :
    Nat.dist i.val j.val ≤ w.length := by
  induction w with
  | nil => simp
  | @cons a b c hadj p ih =>
      have h1 : Nat.dist a.val b.val = 1 := natDist_eq_one_of_adj hadj
      have h2 : Nat.dist a.val c.val ≤ Nat.dist a.val b.val + Nat.dist b.val c.val :=
        Nat.dist.triangle_inequality a.val b.val c.val
      have h3 : (SimpleGraph.Walk.cons hadj p).length = p.length + 1 :=
        SimpleGraph.Walk.length_cons hadj p
      omega

/-- **The Mathlib gap.** The path graph's geodesic distance is exactly the integer-line distance:
`(pathGraph n).dist i j = Nat.dist i.val j.val`. Upper bound: an explicit `upWalk` (or its reverse)
realizes a walk of length `Nat.dist i.val j.val`. Lower bound: `natDist_le_walk_length` applied to a
shortest walk (`Reachable.exists_walk_length_eq_dist`, using that `pathGraph` is always preconnected). -/
theorem pathGraph_dist {n : ℕ} (i j : Fin n) :
    (SimpleGraph.pathGraph n).dist i j = Nat.dist i.val j.val := by
  refine le_antisymm ?_ ?_
  · rcases le_total i.val j.val with hij | hij
    · have hlt : i.val + (j.val - i.val) < n := by omega
      have hst : (⟨i.val, by omega⟩ : Fin n) = i := by apply Fin.ext; rfl
      have heq : (⟨i.val + (j.val - i.val), hlt⟩ : Fin n) = j := by
        apply Fin.ext; show i.val + (j.val - i.val) = j.val; omega
      have hd := SimpleGraph.dist_le ((upWalk i.val (j.val - i.val) hlt).copy hst heq)
      rw [SimpleGraph.Walk.length_copy, upWalk_length] at hd
      rw [← Nat.dist_eq_sub_of_le hij] at hd
      exact hd
    · have hlt : j.val + (i.val - j.val) < n := by omega
      have hst : (⟨j.val, by omega⟩ : Fin n) = j := by apply Fin.ext; rfl
      have heq : (⟨j.val + (i.val - j.val), hlt⟩ : Fin n) = i := by
        apply Fin.ext; show j.val + (i.val - j.val) = i.val; omega
      have hd := SimpleGraph.dist_le ((upWalk j.val (i.val - j.val) hlt).copy hst heq)
      rw [SimpleGraph.Walk.length_copy, upWalk_length] at hd
      rw [← Nat.dist_eq_sub_of_le_right hij] at hd
      rwa [SimpleGraph.dist_comm] at hd
  · have hr : (SimpleGraph.pathGraph n).Reachable i j := SimpleGraph.pathGraph_preconnected n i j
    obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
    have := natDist_le_walk_length w
    rwa [hw] at this

/-! ## Part 2 — the refinement: the chain's decoded metric samples the unit interval -/

/-- **The chain's state-decoded metric equals the integer-line distance.** Specializing `MetricFromState`
M3's explicit (edge-crossing) cut-rank profile to the path graph, and reusing `pathGraph_dist`: the
distance the entangled chain's cut-rank profile decodes back to is exactly `Nat.dist`. -/
theorem chain_decodedDist_eq {n : ℕ} {q : ℕ} (hq : 2 ≤ q) (i j : Fin n) :
    decodedDist (explicitProfile (SimpleGraph.pathGraph n) hq) i j = (Nat.dist i.val j.val : ℝ) := by
  rw [decodedDist_eq]
  unfold graphDist
  rw [pathGraph_dist]

/-- `Nat.dist` cast to `ℝ` is the real absolute difference — the link between the discrete chain metric
and the continuum interval metric. -/
private lemma natDist_cast_eq_abs (a b : ℕ) : (Nat.dist a b : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  rcases le_total a b with h | h
  · have hc : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (by linarith)]
    ring
  · have hc : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (by linarith)]

/-- **M4 — the continuum-refinement corollary.** Rescaled by the chain length `n-1`, the state-decoded
distance between grid points `i, j` of the chain equals the standard unit-interval distance between
their images `i/(n-1), j/(n-1) ∈ [0,1]`. The entangled chain's cut-rank-decoded metric is exactly the
restriction of the continuum metric `|x-y|` on `[0,1]` to `n` equally spaced points — geometry refining a
continuum, as an OUTPUT of the state (not a hypothesis fed in). -/
theorem chain_scaledDist_eq_interval {n : ℕ} (hn : 2 ≤ n) {q : ℕ} (hq : 2 ≤ q) (i j : Fin n) :
    decodedDist (explicitProfile (SimpleGraph.pathGraph n) hq) i j / ((n : ℝ) - 1)
      = |(i.val : ℝ) / ((n : ℝ) - 1) - (j.val : ℝ) / ((n : ℝ) - 1)| := by
  have hcpos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [chain_decodedDist_eq hq i j, div_sub_div_same, abs_div, abs_of_pos hcpos,
    natDist_cast_eq_abs]

end QIQTH.MetricRefinement
