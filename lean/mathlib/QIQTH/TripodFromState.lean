/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# TRIPOD FROM STATE — the end-to-end chain to the first state-decoded NON-EUCLIDEAN limit
(track W brick 2)

Brick W2 of the STATE-WIRE-2 track (`docs/qg_roadmap/STATEWIRE2_SPHERE_INTRINSIC_CONE_PLAN.md`):
the **composition** of the previously proven, axiom-free layers, glued at `G = starGraph n` —
the tripod mirror of the cube and torus state-wire bricks (`QIQTH/StencilFromState.lean`,
`QIQTH/TorusFromState.lean`):

    Bell state ──► cut-rank profile ──► decoded graph ──► decoded metric ──► GH limit = TRIPOD
    (BellCutRank +      (this file:       (MetricFromState  (this file:        (TripodGH
     ReducedDensity:    `starProfile`,     `rankMIGraph_eq`:  `starGraph_dist_   `star_toGHSpace_
     Schmidt rank =     the crossing-      `starProfile_      eq` + `scaledStar  tendsto_tripod`:
     q^boundary)        count profile)     decodes`)          _dist_eq_decoded`) the capstone)

**The new content vs the cube/torus bricks** (both proved here, from scratch):

* **The star SimpleGraph and its geodesics.**  Unlike the cube/torus, the tripod's finite
  spaces (`TripodGH.ScaledStar`) carried no `SimpleGraph` — only the hop-count function
  `starHop`.  This file builds the subdivided star graph `starGraph n` (apex ∼ innermost arm
  vertices, consecutive same-arm vertices adjacent — encoded uniformly as
  `Adj x y ↔ starHop x y = 1`, `starGraph_adj`) and proves **THE GEODESIC IDENTITY**
  `starGraph_dist_eq : (starGraph n).dist x y = starHop x y`, so the whole tripod chain is
  genuinely GRAPH-GEODESIC end to end: `≤` by an explicit one-step-closer walk construction
  (`cons` + `SimpleGraph.dist_le`, no reachability side conditions), `≥` by the hop triangle
  inequality `starHop_triangle` chained along any walk, applied to a shortest walk.
* **The decoded limit is provably NON-EUCLIDEAN.**  The Gromov–Hausdorff limit of the decoded
  geometries is the TRIPOD, which embeds isometrically in NO real inner-product space
  (`TripodGH.tripod_no_isometric_embedding_into_inner`) — the first state-decoded limit that
  is not (a subset of) a flat space.

The glue layer mirrors the torus brick verbatim:

* `starProfile n` — the explicit crossing-count cut-rank profile (bond dimension `q = 2`) of
  the star graph (`MetricFromState.explicitProfile`).
* `starProfile_decodes` — **THE DECODE**: the profile's strict rank-submultiplicativity
  pattern recovers the star graph, `rankMIGraph (starProfile n) = starGraph n`
  (`MetricFromState.rankMIGraph_eq`, a theorem, not a definition).
* `scaledStar_dist_eq_decoded` — **THE METRIC IDENTITY**: the intrinsic scaled star metric of
  `TripodGH` IS the state-decoded metric, rescaled:
  `dist x y = (1/(n+1)) · decodedDist (starProfile n) x y`.
* `starProfile_boundary_realized` — **THE BELL GROUNDING**: across EVERY cut `A`, the
  profile's boundary exponent is realized as the genuine reduced-density Schmidt rank of an
  explicit Bell-pair product state (`ReducedDensity.bell_schmidtRank_eq_pow_crossingCard`).
* `state_decoded_geometry_tendsto_tripod` — **THE END-TO-END CAPSTONE**: a family of cut-rank
  profiles, realized by Bell entanglement, whose decoded, scaled metrics are exactly the
  metrics of a sequence of finite spaces converging in Gromov–Hausdorff space to the TRIPOD —
  **the first state-decoded NON-EUCLIDEAN limit**.

## Scope firewall (HONEST)

* **The branching is INSERTED, not emergent.**  The branch point enters through the star
  adjacency of the graph the state is built on: the state/profile is CONSTRUCTED to carry the
  star correlation pattern.  The decoding is a theorem, but WHY a physical state would carry
  exactly this entanglement — the dynamical source of the profile — remains the cited open
  wall.  Nothing here derives the state (or its branching) from dynamics.
* **The tripod is a CAT(0) SINGULAR TREE** — "non-Euclidean" here means NON-MANIFOLD /
  embeds in no real inner-product space (`tripod_no_isometric_embedding_into_inner`).  It is
  NOT positive curvature, NOT a curved surface, NOT a smooth Riemannian manifold.
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.TripodGH
import QIQTH.MetricFromState
import QIQTH.BellCutRank
import QIQTH.ReducedDensity

namespace QIQTH.TripodFromState

open QIQTH.TripodGH QIQTH.MetricFromState Filter Topology

/-! ## 0 — instances: the subdivided star is a finite decidable vertex type -/

instance instDecidableEqScaledStar (n : ℕ) : DecidableEq (ScaledStar n) :=
  inferInstanceAs (DecidableEq (Option (Fin 3 × {k : Fin (n + 2) // k ≠ 0})))

instance instFintypeScaledStar (n : ℕ) : Fintype (ScaledStar n) :=
  inferInstanceAs (Fintype (Option (Fin 3 × {k : Fin (n + 2) // k ≠ 0})))

/-! ## 1 — `starHop` basics: reflexivity, symmetry, separation, triangle inequality -/

private lemma natDist_def (a b : ℕ) : Nat.dist a b = a - b + (b - a) := rfl

/-- Arm parameters are positive: the subtype `k ≠ 0` in `Fin (n+2)` gives `1 ≤ k`. -/
private lemma arm_pos {n : ℕ} (k : {k : Fin (n + 2) // k ≠ 0}) : 1 ≤ k.1.1 :=
  Nat.pos_of_ne_zero fun h0 => k.2 (Fin.ext (by rw [h0, Fin.val_zero]))

/-- The hop count vanishes on the diagonal. -/
lemma starHop_self {n : ℕ} (x : ScaledStar n) : starHop x x = 0 := by
  rcases x with _ | ⟨i, k⟩
  · rfl
  · rw [starHop_some_some, if_pos rfl, Nat.dist_self]

/-- The hop count is symmetric. -/
lemma starHop_comm {n : ℕ} (x y : ScaledStar n) : starHop x y = starHop y x := by
  rcases x with _ | ⟨i, k⟩ <;> rcases y with _ | ⟨j, l⟩
  · rfl
  · rfl
  · rfl
  · rw [starHop_some_some, starHop_some_some]
    rcases eq_or_ne i j with h | h
    · rw [if_pos h, if_pos h.symm, Nat.dist_comm]
    · rw [if_neg h, if_neg (Ne.symm h), Nat.add_comm]

/-- The hop count separates points: `starHop x y = 0 ↔ x = y`. -/
lemma starHop_eq_zero_iff {n : ℕ} {x y : ScaledStar n} : starHop x y = 0 ↔ x = y := by
  constructor
  · intro h
    rcases x with _ | ⟨i, k⟩ <;> rcases y with _ | ⟨j, l⟩
    · rfl
    · rw [starHop_none_some] at h
      have := arm_pos l
      omega
    · rw [starHop_some_none] at h
      have := arm_pos k
      omega
    · rw [starHop_some_some] at h
      rcases eq_or_ne i j with hij | hij
      · rw [if_pos hij] at h
        have hkl : k.1.1 = l.1.1 := Nat.eq_of_dist_eq_zero h
        rw [hij, Subtype.ext (Fin.ext hkl)]
      · rw [if_neg hij] at h
        have := arm_pos k
        omega
  · rintro rfl
    exact starHop_self x

/-- **The hop triangle inequality** — the ℕ counterpart of `tripodDist_triangle`, by the same
3×3 apex/arm casework, closed by `Nat.dist` unfolding + `omega`.  (Public: reusable.) -/
theorem starHop_triangle {n : ℕ} (x y z : ScaledStar n) :
    starHop x z ≤ starHop x y + starHop y z := by
  rcases x with _ | ⟨i, k⟩ <;> rcases y with _ | ⟨j, t⟩ <;> rcases z with _ | ⟨m, u⟩
  · simp
  · simp
  · simp
  · -- apex to arm point via an arm point
    simp only [starHop_none_some, starHop_some_some]
    rcases eq_or_ne j m with h | h
    · rw [if_pos h]
      simp only [natDist_def]
      omega
    · rw [if_neg h]
      omega
  · simp
  · -- arm point to arm point via the apex
    simp only [starHop_some_none, starHop_none_some, starHop_some_some]
    rcases eq_or_ne i m with h | h
    · rw [if_pos h]
      simp only [natDist_def]
      omega
    · rw [if_neg h]
  · -- arm point to apex via an arm point
    simp only [starHop_some_none, starHop_some_some]
    rcases eq_or_ne i j with h | h
    · rw [if_pos h]
      simp only [natDist_def]
      omega
    · rw [if_neg h]
      omega
  · -- arm point to arm point via an arm point
    simp only [starHop_some_some]
    rcases eq_or_ne i j with h2 | h2 <;> rcases eq_or_ne j m with h3 | h3
    · rw [if_pos h2, if_pos h3, if_pos (h2.trans h3)]
      exact Nat.dist.triangle_inequality _ _ _
    · have h1 : i ≠ m := fun h => h3 (h2.symm.trans h)
      rw [if_pos h2, if_neg h3, if_neg h1]
      simp only [natDist_def]
      omega
    · have h1 : i ≠ m := fun h => h2 (h.trans h3.symm)
      rw [if_neg h2, if_pos h3, if_neg h1]
      simp only [natDist_def]
      omega
    · rcases eq_or_ne i m with h1 | h1
      · rw [if_pos h1, if_neg h2, if_neg h3]
        simp only [natDist_def]
        omega
      · rw [if_neg h1, if_neg h2, if_neg h3]
        omega

/-! ## 2 — the star graph

Adjacency is encoded uniformly as `starHop x y = 1`, which is exactly the subdivided-star
adjacency: apex ∼ the innermost vertex of each arm (`starHop none (j,l) = l = 1`), consecutive
same-arm vertices (`Nat.dist k l = 1`), and NO cross-arm edges (`k + l ≥ 2`). -/

/-- **The subdivided star graph** on `ScaledStar n`: `x ∼ y` iff `starHop x y = 1`.
Symmetric by `starHop_comm`, loopless by `starHop_self`. -/
def starGraph (n : ℕ) : SimpleGraph (ScaledStar n) where
  Adj x y := starHop x y = 1
  symm := fun x y h => (starHop_comm y x).trans h
  loopless := ⟨fun x h => by rw [starHop_self] at h; omega⟩

/-- Adjacency in the star graph is exactly hop distance `1` (definitional). -/
lemma starGraph_adj {n : ℕ} {x y : ScaledStar n} :
    (starGraph n).Adj x y ↔ starHop x y = 1 := Iff.rfl

instance instDecidableRelStarGraphAdj (n : ℕ) : DecidableRel (starGraph n).Adj :=
  fun x y => inferInstanceAs (Decidable (starHop x y = 1))

/-! ## 3 — THE GEODESIC IDENTITY: `(starGraph n).dist = starHop`

`≤`: strong induction on `starHop x y`, prepending one edge to the inductively obtained walk
(`Walk.cons` + `SimpleGraph.dist_le` — no reachability side conditions).
`≥`: `starHop` is `1`-Lipschitz along edges (`starHop_triangle` + adjacency), so it lower
bounds the length of EVERY walk; apply to a shortest walk. -/

/-- The `m`-th arm parameter as a nonzero `Fin (n+2)`, for `1 ≤ m < n + 2`. -/
private def armK {n : ℕ} (m : ℕ) (h1 : 1 ≤ m) (h2 : m < n + 2) :
    {k : Fin (n + 2) // k ≠ 0} :=
  ⟨⟨m, h2⟩, Fin.ne_of_val_ne (by show m ≠ (0 : Fin (n + 2)).val; rw [Fin.val_zero]; omega)⟩

@[simp] private lemma armK_val {n : ℕ} (m : ℕ) (h1 : 1 ≤ m) (h2 : m < n + 2) :
    (armK (n := n) m h1 h2).1.1 = m := rfl

/-- **One geodesic step.**  Any pair at positive hop distance admits a neighbor of `x` exactly
one hop closer to `y`: down/up the shared arm, or through the apex for cross-arm pairs. -/
private lemma exists_adj_step {n : ℕ} (x y : ScaledStar n) (h : starHop x y ≠ 0) :
    ∃ z : ScaledStar n, (starGraph n).Adj x z ∧ starHop z y + 1 = starHop x y := by
  rcases x with _ | ⟨i, k⟩ <;> rcases y with _ | ⟨j, l⟩
  · exact absurd starHop_none_none h
  · -- apex to arm point: step to the innermost vertex of arm `j`
    have hl := arm_pos l
    refine ⟨some (j, armK 1 le_rfl (by omega)), ?_, ?_⟩
    · rw [starGraph_adj, starHop_none_some, armK_val]
    · rw [starHop_some_some, if_pos rfl, armK_val, starHop_none_some, natDist_def]
      omega
  · -- arm point to apex: step inward (to the apex if `k = 1`)
    have hk := arm_pos k
    by_cases hk1 : k.1.1 = 1
    · refine ⟨none, ?_, ?_⟩
      · rw [starGraph_adj, starHop_some_none]
        exact hk1
      · rw [starHop_none_none, starHop_some_none]
        omega
    · refine ⟨some (i, armK (k.1.1 - 1) (by omega) (by have := k.1.isLt; omega)), ?_, ?_⟩
      · rw [starGraph_adj, starHop_some_some, if_pos rfl, armK_val, natDist_def]
        omega
      · rw [starHop_some_none, armK_val, starHop_some_none]
        omega
  · -- arm point to arm point
    have hk := arm_pos k
    have hl := arm_pos l
    rcases eq_or_ne i j with hij | hij
    · -- same arm: move `k` one step toward `l`
      subst hij
      rw [starHop_some_some, if_pos rfl] at h
      have hne : k.1.1 ≠ l.1.1 := fun hEq => h (by rw [hEq, Nat.dist_self])
      rcases Nat.lt_or_ge k.1.1 l.1.1 with hkl | hkl
      · refine ⟨some (i, armK (k.1.1 + 1) (by omega) (by have := l.1.isLt; omega)), ?_, ?_⟩
        · rw [starGraph_adj, starHop_some_some, if_pos rfl, armK_val, natDist_def]
          omega
        · rw [starHop_some_some, if_pos rfl, armK_val, starHop_some_some, if_pos rfl,
            natDist_def, natDist_def]
          omega
      · refine ⟨some (i, armK (k.1.1 - 1) (by omega) (by have := k.1.isLt; omega)), ?_, ?_⟩
        · rw [starGraph_adj, starHop_some_some, if_pos rfl, armK_val, natDist_def]
          omega
        · rw [starHop_some_some, if_pos rfl, armK_val, starHop_some_some, if_pos rfl,
            natDist_def, natDist_def]
          omega
    · -- cross arm: descend toward the apex (reaching it at `k = 1`)
      by_cases hk1 : k.1.1 = 1
      · refine ⟨none, ?_, ?_⟩
        · rw [starGraph_adj, starHop_some_none]
          exact hk1
        · rw [starHop_none_some, starHop_some_some, if_neg hij]
          omega
      · refine ⟨some (i, armK (k.1.1 - 1) (by omega) (by have := k.1.isLt; omega)), ?_, ?_⟩
        · rw [starGraph_adj, starHop_some_some, if_pos rfl, armK_val, natDist_def]
          omega
        · rw [starHop_some_some, if_neg hij, armK_val, starHop_some_some, if_neg hij]
          omega

/-- **The geodesic walk**: an explicit walk of length `≤ starHop x y`, by strong induction on
the hop count, prepending one `exists_adj_step` edge at a time. -/
private lemma exists_walk_length_le_starHop {n : ℕ} :
    ∀ (S : ℕ) (x y : ScaledStar n), starHop x y ≤ S →
      ∃ w : (starGraph n).Walk x y, w.length ≤ starHop x y := by
  intro S
  induction S with
  | zero =>
      intro x y h
      have hxy : x = y := starHop_eq_zero_iff.mp (Nat.le_zero.mp h)
      subst hxy
      exact ⟨SimpleGraph.Walk.nil, Nat.zero_le _⟩
  | succ S ih =>
      intro x y h
      by_cases h0 : starHop x y = 0
      · have hxy : x = y := starHop_eq_zero_iff.mp h0
        subst hxy
        exact ⟨SimpleGraph.Walk.nil, Nat.zero_le _⟩
      · obtain ⟨z, hadj, hz⟩ := exists_adj_step x y h0
        obtain ⟨w, hw⟩ := ih z y (by omega)
        refine ⟨SimpleGraph.Walk.cons hadj w, ?_⟩
        rw [SimpleGraph.Walk.length_cons]
        omega

/-- **The Lipschitz lower bound**: `starHop` lower bounds the length of EVERY walk — by
induction on the walk, chaining `starHop_triangle` against the hop-`1` edges. -/
private lemma starHop_le_walk_length {n : ℕ} {x y : ScaledStar n}
    (w : (starGraph n).Walk x y) : starHop x y ≤ w.length := by
  induction w with
  | nil => rw [starHop_self]; exact Nat.zero_le _
  | @cons a b c hadj p ih =>
      have h1 : starHop a b = 1 := starGraph_adj.mp hadj
      have h2 := starHop_triangle a b c
      have h3 : (SimpleGraph.Walk.cons hadj p).length = p.length + 1 :=
        SimpleGraph.Walk.length_cons hadj p
      omega

/-- **Connectivity of the star graph** (every pair is joined by the geodesic walk). -/
theorem starGraph_connected (n : ℕ) : (starGraph n).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun x y => ?_, ⟨none⟩⟩
  obtain ⟨w, -⟩ := exists_walk_length_le_starHop (starHop x y) x y le_rfl
  exact w.reachable

/-- **THE GEODESIC IDENTITY.**  The star graph's geodesic distance IS the hop count:
`(starGraph n).dist x y = starHop x y`.  With `TripodGH.scaledStar_dist_eq` this makes the
tripod chain genuinely graph-geodesic end to end: the finite metrics converging to the tripod
are the scaled geodesic metrics of an actual `SimpleGraph`. -/
theorem starGraph_dist_eq (n : ℕ) (x y : ScaledStar n) :
    (starGraph n).dist x y = starHop x y := by
  refine le_antisymm ?_ ?_
  · obtain ⟨w, hw⟩ := exists_walk_length_le_starHop (starHop x y) x y le_rfl
    exact le_trans (SimpleGraph.dist_le w) hw
  · obtain ⟨w0, -⟩ := exists_walk_length_le_starHop (starHop x y) x y le_rfl
    obtain ⟨w, hw⟩ := w0.reachable.exists_walk_length_eq_dist
    rw [← hw]
    exact starHop_le_walk_length w

/-! ## 4 — the crossing-count cut-rank profile of the star graph -/

/-- **The star profile**: the explicit crossing-count cut-rank profile of the subdivided star
graph at bond dimension `q = 2` — boundary = the genuine edge-crossing count, defect PROVEN
(`crossingCard_pair_defect`), no carried hypotheses. -/
def starProfile (n : ℕ) : QIQTH.MetricFromState.CutRankProfile (starGraph n) :=
  explicitProfile _ (le_refl 2)

/-- The profile's boundary function is the star graph's crossing-edge count (definitional). -/
@[simp] lemma starProfile_boundary (n : ℕ) (A : Finset (ScaledStar n)) :
    (starProfile n).boundary A
      = QIQTH.MetricFromState.crossingCard (starGraph n) A := rfl

/-! ## 5 — THE DECODE: the profile recovers the star graph -/

/-- **THE DECODE.**  The strict rank-submultiplicativity pattern of the star profile — the
positive Rényi-0 mutual-information adjacency — recovers the star graph exactly:
`rankMIGraph (starProfile n) = starGraph n`.  The graph — and with it the BRANCH POINT — is an
OUTPUT of the cut-rank data (a theorem, `rankMIGraph_eq`, not a definition). -/
theorem starProfile_decodes (n : ℕ) : rankMIGraph (starProfile n) = starGraph n :=
  rankMIGraph_eq (starProfile n)

/-! ## 6 — THE METRIC IDENTITY: the GH-converging metric IS the decoded metric -/

/-- **THE METRIC IDENTITY.**  The intrinsic scaled star metric of `TripodGH` — the very metric
whose spaces GH-converge to the tripod — is exactly the state-decoded metric of the star
profile, rescaled by the edge length `1/(n+1)`:

    dist x y = (1/(n+1)) · decodedDist (starProfile n) x y.

Both sides unfold to `(1/(n+1)) · (starGraph n).dist x y`: the left by `scaledStar_dist_eq` +
the geodesic identity `starGraph_dist_eq`, the right by `decodedDist_eq` +
`graphDist G x y = (G.dist x y : ℝ)`. -/
theorem scaledStar_dist_eq_decoded (n : ℕ) (x y : ScaledStar n) :
    dist x y
      = 1 / ((n : ℝ) + 1) * QIQTH.MetricFromState.decodedDist (starProfile n) x y := by
  rw [scaledStar_dist_eq, decodedDist_eq]
  have hgd : QIQTH.EmergentSpacetime.graphDist (starGraph n) x y
      = (((starGraph n).dist x y : ℕ) : ℝ) := rfl
  rw [hgd, starGraph_dist_eq]

/-! ## 7 — THE BELL GROUNDING: the boundary exponent is a genuine Schmidt rank -/

/-- **THE BELL GROUNDING.**  Across EVERY cut `A`, the star profile's boundary function is
realized as the genuine reduced-density Schmidt rank of an explicit Bell-pair product state
(one 2-dimensional maximally-entangled pair per crossing edge):
`schmidtRank = 2 ^ boundary A`.  The decoded geometry's "area" is honest entanglement, not
merely a combinatorial count (`ReducedDensity.bell_schmidtRank_eq_pow_crossingCard`). -/
theorem starProfile_boundary_realized (n : ℕ) (A : Finset (ScaledStar n)) :
    QIQTH.ReducedDensity.schmidtRank
        (QIQTH.BellCutRank.bellFlattening ℂ 2 (Fin ((starProfile n).boundary A)))
      = 2 ^ (starProfile n).boundary A := by
  rw [starProfile_boundary]
  exact QIQTH.ReducedDensity.bell_schmidtRank_eq_pow_crossingCard 2 _ A (Fintype.card_fin _)

/-! ## 8 — THE END-TO-END CAPSTONE -/

/-- **THE PACKAGED CAPSTONE — the first state-decoded NON-EUCLIDEAN limit.**  There is a
family of cut-rank profiles — realized by explicit Bell entanglement across every cut
(`starProfile_boundary_realized`) — whose decoded, scaled metrics are EXACTLY the metrics
(`scaledStar_dist_eq_decoded`, riding the geodesic identity `starGraph_dist_eq`) of a sequence
of finite spaces converging in Gromov–Hausdorff space to the TRIPOD: entangled-state profile →
decoded graph → decoded metric → continuum limit, every arrow a theorem.  The limit provably
embeds in NO real inner-product space (`tripod_no_isometric_embedding_into_inner`) — the
decoded geometry has left the flat/Euclidean world for the first time.  (The branching is
inserted through the star adjacency the profile is built on — see the scope firewall.) -/
theorem state_decoded_geometry_tendsto_tripod :
    ∃ P : ∀ n, QIQTH.MetricFromState.CutRankProfile (starGraph n),
      (∀ n (x y : ScaledStar n),
        dist x y = 1 / ((n : ℝ) + 1) * QIQTH.MetricFromState.decodedDist (P n) x y) ∧
      Filter.Tendsto (fun n : ℕ => GromovHausdorff.toGHSpace (ScaledStar n)) Filter.atTop
        (𝓝 (GromovHausdorff.toGHSpace Tripod)) :=
  ⟨starProfile, scaledStar_dist_eq_decoded, star_toGHSpace_tendsto_tripod⟩

end QIQTH.TripodFromState
