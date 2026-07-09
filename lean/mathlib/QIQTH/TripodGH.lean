/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# THE TRIPOD — a genuinely NON-EUCLIDEAN (branching, non-manifold) Gromov–Hausdorff limit of
graph geodesics (brick B1, curvature-track first result)

First brick of the CURVATURE track (`docs/qg_roadmap/STATE_TORUS_CURVATURE_PLAN.md`, Track B).
Every Gromov–Hausdorff limit produced so far in this library — the interval, the Euclidean
d-cube (`QIQTH/StencilDimGH.lean`), the flat d-torus (`QIQTH/TorusStencilGH.lean`) — is (a
subset of) a FLAT space: locally Euclidean, isometrically embeddable in an inner-product
space.  This file produces the first limit that is provably NOT of that kind: the **TRIPOD**
`T`, the 3-armed metric tree (three unit segments glued at one branch point), realized as the
Gromov–Hausdorff limit of the intrinsic scaled hop metrics of subdivided STAR graphs:

    toGHSpace (ScaledStar n) ⟶ toGHSpace Tripod        (`star_toGHSpace_tendsto_tripod`)

via the quantitative bound `ghDist (ScaledStar n) Tripod ≤ 1/(n+1)` (`ghDist_star_le`): the
embedding of the `3(n+1)+1`-point star (apex + 3 arms subdivided into `n+1` hops of length
`1/(n+1)`) into the tripod is an EXACT isometry (`starToTripod_isometry`) whose image is a
`1/(n+1)`-net (`tripod_net`), and the finite metric IS the scaled graph-geodesic (hop-count)
metric of the subdivided star (`scaledStar_dist_eq` — the honesty lemma: `dist = hop/(n+1)`).

## The non-Euclideanness is a THEOREM, not prose

`tripod_no_isometric_embedding_into_inner`: the tripod admits NO distance-preserving map into
ANY real inner-product space — the branch point is a metric obstruction.  The invariant is the
same unique-metric-midpoint argument as `QIQTH/IsotropyNoGo.lean`: in an inner-product space
the midpoint of two points at distance 2 is UNIQUE (parallelogram law), but the tripod's apex
is simultaneously the midpoint of all three pairs of arm endpoints — so any isometric image
would collapse two arm endpoints at distance 2 to a single point.  Hence "the limit is NOT
Euclidean/flat" is a machine-checked statement.

## Scope firewall (HONEST)

* **The tripod is a CAT(0) SINGULAR TREE** — "non-flat"/"non-Euclidean" here means
  NON-MANIFOLD / NON-LOCALLY-EUCLIDEAN / embeds in no real inner-product space.  It is NOT
  positive curvature, NOT a curved surface, NOT a smooth Riemannian manifold.  (The cone with
  deficit angle — concentrated positive curvature — is the cited next candidate, not attempted
  here.)
* **The branching is INSERTED through the star topology of the graphs** — exactly as isotropy
  was inserted through the stencil rule and the torus topology through the wrap rule.  The
  theorem shows the graph-geodesic machine TRANSPORTS a chosen branching structure to the
  continuum; it does not show topology emerging from anything.
* The distances and the geometry are INPUTS; NOT emergent topology, NOT GR, NOT numerical-G,
  NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.IsotropyNoGo
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.Order.Floor.Semiring

namespace QIQTH.TripodGH

open Filter Topology

/-! ## Part 1 — the tripod

`none` is the apex (branch point); `some (i, t)` is the point at arc-length parameter
`t ∈ (0, 1]` along arm `i ∈ {0, 1, 2}`. -/

/-- **The tripod**: three unit segments glued at one branch point.  `none` = the apex,
`some (i, t)` = the point at distance `t ∈ (0,1]` along arm `i`. -/
def Tripod : Type := Option (Fin 3 × Set.Ioc (0 : ℝ) 1)

/-- **The tree metric on the tripod**: distance along the arms through the apex — same-arm
pairs at `|s - t|`, cross-arm pairs at `s + t` (through the branch point). -/
noncomputable def tripodDist : Tripod → Tripod → ℝ
  | none, none => 0
  | none, some q => q.2.1
  | some p, none => p.2.1
  | some p, some q => if p.1 = q.1 then |p.2.1 - q.2.1| else p.2.1 + q.2.1

@[simp] lemma tripodDist_none_none : tripodDist none none = 0 := rfl

@[simp] lemma tripodDist_none_some (j : Fin 3) (t : Set.Ioc (0 : ℝ) 1) :
    tripodDist none (some (j, t)) = t.1 := rfl

@[simp] lemma tripodDist_some_none (i : Fin 3) (s : Set.Ioc (0 : ℝ) 1) :
    tripodDist (some (i, s)) none = s.1 := rfl

@[simp] lemma tripodDist_some_some (i j : Fin 3) (s t : Set.Ioc (0 : ℝ) 1) :
    tripodDist (some (i, s)) (some (j, t))
      = if i = j then |s.1 - t.1| else s.1 + t.1 := rfl

/-- The key cross-arm estimate: `|a - b| ≤ a + b` for positives. -/
private lemma abs_sub_le_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : |a - b| ≤ a + b := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

private lemma tripodDist_self (x : Tripod) : tripodDist x x = 0 := by
  rcases x with _ | ⟨i, s⟩
  · rfl
  · rw [tripodDist_some_some, if_pos rfl, sub_self, abs_zero]

private lemma tripodDist_comm (x y : Tripod) : tripodDist x y = tripodDist y x := by
  rcases x with _ | ⟨i, s⟩ <;> rcases y with _ | ⟨j, t⟩
  · rfl
  · rfl
  · rfl
  · rw [tripodDist_some_some, tripodDist_some_some]
    rcases eq_or_ne i j with h | h
    · rw [if_pos h, if_pos h.symm, abs_sub_comm]
    · rw [if_neg h, if_neg (Ne.symm h), add_comm]

private lemma tripodDist_triangle (x y z : Tripod) :
    tripodDist x z ≤ tripodDist x y + tripodDist y z := by
  rcases x with _ | ⟨i, s⟩ <;> rcases y with _ | ⟨j, t⟩ <;> rcases z with _ | ⟨k, u⟩
  · simp
  · simp
  · -- apex to apex via an arm point
    simp only [tripodDist_none_none, tripodDist_none_some, tripodDist_some_none]
    linarith [t.2.1]
  · -- apex to arm point via an arm point
    simp only [tripodDist_none_some, tripodDist_some_some]
    rcases eq_or_ne j k with h | h
    · rw [if_pos h]
      have h1 : u.1 - t.1 ≤ |t.1 - u.1| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      linarith
    · rw [if_neg h]
      linarith [t.2.1]
  · simp
  · -- arm point to arm point via the apex
    simp only [tripodDist_some_none, tripodDist_none_some, tripodDist_some_some]
    rcases eq_or_ne i k with h | h
    · rw [if_pos h]
      exact abs_sub_le_add s.2.1 u.2.1
    · rw [if_neg h]
  · -- arm point to apex via an arm point
    simp only [tripodDist_some_none, tripodDist_some_some]
    rcases eq_or_ne i j with h | h
    · rw [if_pos h]
      linarith [le_abs_self (s.1 - t.1)]
    · rw [if_neg h]
      linarith [t.2.1]
  · -- arm point to arm point via an arm point
    simp only [tripodDist_some_some]
    rcases eq_or_ne i j with h2 | h2 <;> rcases eq_or_ne j k with h3 | h3
    · rw [if_pos h2, if_pos h3, if_pos (h2.trans h3)]
      exact abs_sub_le s.1 t.1 u.1
    · have h1 : i ≠ k := fun h => h3 (h2.symm.trans h)
      rw [if_pos h2, if_neg h3, if_neg h1]
      linarith [le_abs_self (s.1 - t.1)]
    · have h1 : i ≠ k := fun h => h2 (h.trans h3.symm)
      rw [if_neg h2, if_pos h3, if_neg h1]
      have h4 : u.1 - t.1 ≤ |t.1 - u.1| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      linarith
    · rcases eq_or_ne i k with h1 | h1
      · rw [if_pos h1, if_neg h2, if_neg h3]
        linarith [abs_sub_le_add s.2.1 u.2.1, t.2.1]
      · rw [if_neg h1, if_neg h2, if_neg h3]
        linarith [t.2.1]

private lemma tripodDist_eq_zero_imp : ∀ {x y : Tripod}, tripodDist x y = 0 → x = y := by
  intro x y h
  rcases x with _ | ⟨i, s⟩ <;> rcases y with _ | ⟨j, t⟩
  · rfl
  · rw [tripodDist_none_some] at h
    exact absurd h (ne_of_gt t.2.1)
  · rw [tripodDist_some_none] at h
    exact absurd h (ne_of_gt s.2.1)
  · rw [tripodDist_some_some] at h
    rcases eq_or_ne i j with hij | hij
    · rw [if_pos hij] at h
      have hst : s.1 = t.1 := sub_eq_zero.mp (abs_eq_zero.mp h)
      rw [hij, Subtype.ext hst]
    · rw [if_neg hij] at h
      exfalso
      have hs := s.2.1
      have ht := t.2.1
      linarith

/-- **The tripod is a metric space** under the tree metric. -/
noncomputable instance instMetricSpaceTripod : MetricSpace Tripod where
  dist := tripodDist
  dist_self := tripodDist_self
  dist_comm := tripodDist_comm
  dist_triangle := tripodDist_triangle
  eq_of_dist_eq_zero := tripodDist_eq_zero_imp

/-- The tripod distance, unfolded. -/
lemma dist_eq_tripodDist (x y : Tripod) : dist x y = tripodDist x y := rfl

instance instNonemptyTripod : Nonempty Tripod := ⟨none⟩

/-! ### Compactness via the three arm isometries

Each closed arm `{apex} ∪ (arm i)` is the isometric image of `[0,1]`; the tripod is the union
of the three compact arms. -/

/-- **The arm embedding** `[0,1] → Tripod`: `0 ↦ apex`, `t ↦ some (i, t)` for `t > 0`. -/
noncomputable def armEmb (i : Fin 3) (t : Set.Icc (0 : ℝ) 1) : Tripod :=
  if h : t.1 = 0 then none
  else some (i, ⟨t.1, lt_of_le_of_ne t.2.1 (Ne.symm h), t.2.2⟩)

lemma armEmb_of_eq (i : Fin 3) {t : Set.Icc (0 : ℝ) 1} (h : t.1 = 0) :
    armEmb i t = none := dif_pos h

lemma armEmb_of_ne (i : Fin 3) {t : Set.Icc (0 : ℝ) 1} (h : t.1 ≠ 0) :
    armEmb i t = some (i, ⟨t.1, lt_of_le_of_ne t.2.1 (Ne.symm h), t.2.2⟩) := dif_neg h

/-- **Each closed arm is an isometric copy of `[0,1]`** — same-arm distances are `|s - t|`
and the apex sits at distance `t` from the parameter-`t` point, exactly as in `[0,1]`. -/
theorem armEmb_isometry (i : Fin 3) : Isometry (armEmb i) := by
  refine Isometry.of_dist_eq fun a b => ?_
  rw [Subtype.dist_eq, Real.dist_eq]
  rcases eq_or_ne a.1 0 with ha | ha <;> rcases eq_or_ne b.1 0 with hb | hb
  · rw [armEmb_of_eq i ha, armEmb_of_eq i hb, dist_self, ha, hb]
    norm_num
  · rw [armEmb_of_eq i ha, armEmb_of_ne i hb, dist_eq_tripodDist, tripodDist_none_some]
    show b.1 = |a.1 - b.1|
    rw [ha, zero_sub, abs_neg, abs_of_nonneg b.2.1]
  · rw [armEmb_of_ne i ha, armEmb_of_eq i hb, dist_eq_tripodDist, tripodDist_some_none]
    show a.1 = |a.1 - b.1|
    rw [hb, sub_zero, abs_of_nonneg a.2.1]
  · rw [armEmb_of_ne i ha, armEmb_of_ne i hb, dist_eq_tripodDist, tripodDist_some_some,
      if_pos rfl]

/-- The three closed arms cover the tripod (the apex lies on every arm). -/
lemma iUnion_range_armEmb : (⋃ i : Fin 3, Set.range (armEmb i)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
  rcases x with _ | ⟨i, t⟩
  · exact ⟨0, ⟨0, by norm_num⟩, armEmb_of_eq 0 rfl⟩
  · refine ⟨i, ⟨t.1, t.2.1.le, t.2.2⟩, ?_⟩
    rw [armEmb_of_ne i (ne_of_gt t.2.1)]

/-- **The tripod is compact**: the union of three isometric copies of `[0,1]`. -/
instance instCompactSpaceTripod : CompactSpace Tripod := by
  refine isCompact_univ_iff.mp ?_
  rw [← iUnion_range_armEmb]
  haveI : CompactSpace (Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  exact isCompact_iUnion fun i => isCompact_range (armEmb_isometry i).continuous

/-! ## Part 2 — the non-Euclideanness THEOREM

The apex is simultaneously a metric midpoint of all three pairs of arm endpoints; in an
inner-product space the midpoint of a fixed pair is UNIQUE and AFFINE
(`QIQTH.IsotropyNoGo.inner_metric_midpoint_eq_affine_midpoint`), which forces two distinct
arm endpoints (at tripod distance 2) to share an image. -/

/-- **THE NON-EUCLIDEANNESS THEOREM.**  The tripod embeds isometrically in NO real
inner-product space: there is no distance-preserving map `Tripod → E` for any real
inner-product space `E`.  The branch point is a metric obstruction — the SAME unique-midpoint
invariant as `IsotropyNoGo`: the apex is a metric midpoint of each pair of arm endpoints
`A_i, A_j` (`dist O A_i = 1`, `dist A_i A_j = 2`), so its image would have to be the affine
midpoint of each pair `(f A_i, f A_j)`, forcing `f A_1 = f A_2` — but
`dist (f A_1) (f A_2) = 2 ≠ 0`.  This makes "the limit is NOT Euclidean/flat" a
machine-checked statement, not prose. -/
theorem tripod_no_isometric_embedding_into_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : Tripod → E)
    (hf : ∀ p q : Tripod, dist (f p) (f q) = dist p q) : False := by
  have hone : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := Set.mem_Ioc.mpr ⟨one_pos, le_refl 1⟩
  -- arm endpoints are at distance 1 from the apex …
  have hd0 : ∀ i : Fin 3, dist (f (some (i, ⟨1, hone⟩))) (f none) = 1 := fun i => by
    rw [hf, dist_eq_tripodDist, tripodDist_some_none]
  have hd0' : ∀ i : Fin 3, dist (f none) (f (some (i, ⟨1, hone⟩))) = 1 := fun i => by
    rw [hf, dist_eq_tripodDist, tripodDist_none_some]
  -- … and at distance 2 from each other (cross-arm, through the apex)
  have hd2 : ∀ i j : Fin 3, i ≠ j →
      dist (f (some (i, ⟨1, hone⟩))) (f (some (j, ⟨1, hone⟩))) = 2 * 1 := fun i j hij => by
    rw [hf, dist_eq_tripodDist, tripodDist_some_some, if_neg hij]
    norm_num
  -- the apex image is the affine midpoint of arms 0-1 and of arms 0-2
  have hm01 := IsotropyNoGo.inner_metric_midpoint_eq_affine_midpoint
    (hd0 0) (hd0' 1) (hd2 0 1 (by decide))
  have hm02 := IsotropyNoGo.inner_metric_midpoint_eq_affine_midpoint
    (hd0 0) (hd0' 2) (hd2 0 2 (by decide))
  have hkey := hm01.symm.trans hm02
  have h2 := congrArg (fun v : E => (2 : ℝ) • v) hkey
  simp only [smul_smul] at h2
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h2
  simp only [one_smul] at h2
  have h3 := add_left_cancel h2
  have h4 := hd2 1 2 (by decide)
  rw [h3, dist_self] at h4
  norm_num at h4

/-! ## Part 3 — the subdivided star graphs and GH convergence

`ScaledStar n` is the star graph with 3 arms of `n + 1` edges each — apex + `3(n+1)` arm
vertices at parameters `k/(n+1)`, `k = 1, …, n+1` — carrying the tripod-restricted metric,
which IS the graph-geodesic hop metric scaled by `1/(n+1)` (`scaledStar_dist_eq`). -/

/-- **The subdivided star**: apex (`none`) + 3 arms of `n + 1` vertices; `some (i, k)` is the
`k`-th vertex out along arm `i` (`k ∈ {1, …, n+1}`, encoded as a nonzero `Fin (n+2)`). -/
def ScaledStar (n : ℕ) : Type := Option (Fin 3 × {k : Fin (n + 2) // k ≠ 0})

/-- The arm parameter `k/(n+1) ∈ (0,1]` of the `k`-th subdivision vertex. -/
noncomputable def starParam (n : ℕ) (k : {k : Fin (n + 2) // k ≠ 0}) : Set.Ioc (0 : ℝ) 1 :=
  ⟨(k.1.1 : ℝ) / ((n : ℝ) + 1), by
    have hk0 : 0 < k.1.1 :=
      Nat.pos_of_ne_zero fun h0 => k.2 (Fin.ext (by rw [h0, Fin.val_zero]))
    have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    constructor
    · exact div_pos (by exact_mod_cast hk0) hc
    · rw [div_le_one hc]
      have hkle : k.1.1 ≤ n + 1 := Nat.lt_succ_iff.mp k.1.2
      exact_mod_cast hkle⟩

@[simp] lemma starParam_val (n : ℕ) (k : {k : Fin (n + 2) // k ≠ 0}) :
    (starParam n k).1 = (k.1.1 : ℝ) / ((n : ℝ) + 1) := rfl

/-- **The vertex embedding** of the subdivided star into the tripod: apex to apex, `k`-th
vertex of arm `i` to the parameter-`k/(n+1)` point of arm `i`. -/
noncomputable def starToTripod (n : ℕ) : ScaledStar n → Tripod
  | none => none
  | some (i, k) => some (i, starParam n k)

@[simp] lemma starToTripod_none (n : ℕ) : starToTripod n none = none := rfl

@[simp] lemma starToTripod_some (n : ℕ) (i : Fin 3) (k : {k : Fin (n + 2) // k ≠ 0}) :
    starToTripod n (some (i, k)) = some (i, starParam n k) := rfl

lemma starToTripod_injective (n : ℕ) : Function.Injective (starToTripod n) := by
  intro x y h
  rcases x with _ | ⟨i, k⟩ <;> rcases y with _ | ⟨j, l⟩
  · rfl
  · rw [starToTripod_none, starToTripod_some] at h
    have h' : (none : Option (Fin 3 × Set.Ioc (0 : ℝ) 1)) = some (j, starParam n l) := h
    simp at h'
  · rw [starToTripod_some, starToTripod_none] at h
    have h' : (some (i, starParam n k) : Option (Fin 3 × Set.Ioc (0 : ℝ) 1)) = none := h
    simp at h'
  · rw [starToTripod_some, starToTripod_some] at h
    have h' : (some (i, starParam n k) : Option (Fin 3 × Set.Ioc (0 : ℝ) 1))
        = some (j, starParam n l) := h
    have hpair : (i, starParam n k) = (j, starParam n l) := Option.some.inj h'
    have hij : i = j := congrArg Prod.fst hpair
    have hkl2 : starParam n k = starParam n l := congrArg Prod.snd hpair
    have hval : (k.1.1 : ℝ) / ((n : ℝ) + 1) = (l.1.1 : ℝ) / ((n : ℝ) + 1) :=
      congrArg Subtype.val hkl2
    have hc : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (k.1.1 : ℝ) = (l.1.1 : ℝ) := by
      have h3 := congrArg (fun r : ℝ => r * ((n : ℝ) + 1)) hval
      simpa only [div_mul_cancel₀ _ hc] using h3
    have hkl : k.1.1 = l.1.1 := by exact_mod_cast h2
    rw [hij, Subtype.ext (Fin.ext hkl)]

/-- **The pullback metric**: the subdivided star carries the tripod-restricted distance. -/
noncomputable instance instMetricSpaceScaledStar (n : ℕ) : MetricSpace (ScaledStar n) where
  dist x y := dist (starToTripod n x) (starToTripod n y)
  dist_self x := dist_self (starToTripod n x)
  dist_comm x y := dist_comm (starToTripod n x) (starToTripod n y)
  dist_triangle x y z :=
    dist_triangle (starToTripod n x) (starToTripod n y) (starToTripod n z)
  eq_of_dist_eq_zero := by
    intro x y h
    exact starToTripod_injective n (eq_of_dist_eq_zero h)

/-- The scaled-star distance, unfolded. -/
lemma scaledStar_dist_def {n : ℕ} (x y : ScaledStar n) :
    dist x y = dist (starToTripod n x) (starToTripod n y) := rfl

/-- **The vertex embedding is an EXACT isometry** (the star metric is the pullback). -/
theorem starToTripod_isometry (n : ℕ) : Isometry (starToTripod n) :=
  Isometry.of_dist_eq fun _ _ => rfl

instance instNonemptyScaledStar (n : ℕ) : Nonempty (ScaledStar n) := ⟨none⟩

instance instFiniteScaledStar (n : ℕ) : Finite (ScaledStar n) :=
  inferInstanceAs (Finite (Option (Fin 3 × {k : Fin (n + 2) // k ≠ 0})))

instance instCompactSpaceScaledStar (n : ℕ) : CompactSpace (ScaledStar n) :=
  Finite.compactSpace

/-! ### The honesty lemma: the finite metric IS a scaled graph-geodesic metric

`starHop` is the combinatorial hop count of the subdivided star graph (apex at hop distance
`k` from the `k`-th vertex, same-arm vertices at `|k - l|` hops, cross-arm at `k + l` hops
through the apex — the path-graph geodesic count on the star), and
`dist = starHop/(n+1)` exactly. -/

/-- **The graph-geodesic hop count** on the subdivided star: `none ↦ k` (down the arm),
same arm `|k - l|`, cross arm `k + l` (through the apex). -/
def starHop {n : ℕ} : ScaledStar n → ScaledStar n → ℕ
  | none, none => 0
  | none, some q => q.2.1.1
  | some p, none => p.2.1.1
  | some p, some q =>
    if p.1 = q.1 then Nat.dist p.2.1.1 q.2.1.1 else p.2.1.1 + q.2.1.1

@[simp] lemma starHop_none_none {n : ℕ} : starHop (none : ScaledStar n) none = 0 := rfl

@[simp] lemma starHop_none_some {n : ℕ} (j : Fin 3) (l : {k : Fin (n + 2) // k ≠ 0}) :
    starHop (none : ScaledStar n) (some (j, l)) = l.1.1 := rfl

@[simp] lemma starHop_some_none {n : ℕ} (i : Fin 3) (k : {k : Fin (n + 2) // k ≠ 0}) :
    starHop (some (i, k) : ScaledStar n) none = k.1.1 := rfl

@[simp] lemma starHop_some_some {n : ℕ} (i j : Fin 3)
    (k l : {k : Fin (n + 2) // k ≠ 0}) :
    starHop (some (i, k) : ScaledStar n) (some (j, l))
      = if i = j then Nat.dist k.1.1 l.1.1 else k.1.1 + l.1.1 := rfl

private lemma natDist_cast (a b : ℕ) : ((Nat.dist a b : ℕ) : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr ((Nat.cast_le (α := ℝ)).mpr h))]
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr ((Nat.cast_le (α := ℝ)).mpr h))]

/-- **THE HONESTY LEMMA.**  The scaled-star metric IS the graph-geodesic hop metric of the
subdivided star, scaled by the edge length `1/(n+1)`: `dist x y = starHop x y / (n+1)`.  This
keeps the "from graph geodesics" claim a theorem: the finite spaces converging to the tripod
are (scaled) combinatorial path-length metrics, not ad-hoc real assignments. -/
theorem scaledStar_dist_eq {n : ℕ} (x y : ScaledStar n) :
    dist x y = 1 / ((n : ℝ) + 1) * (starHop x y : ℝ) := by
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rcases x with _ | ⟨i, k⟩ <;> rcases y with _ | ⟨j, l⟩
  · rw [scaledStar_dist_def, starToTripod_none, dist_self, starHop_none_none]
    norm_num
  · rw [scaledStar_dist_def, starToTripod_none, starToTripod_some, dist_eq_tripodDist,
      tripodDist_none_some, starParam_val, starHop_none_some]
    ring
  · rw [scaledStar_dist_def, starToTripod_some, starToTripod_none, dist_eq_tripodDist,
      tripodDist_some_none, starParam_val, starHop_some_none]
    ring
  · rw [scaledStar_dist_def, starToTripod_some, starToTripod_some, dist_eq_tripodDist,
      tripodDist_some_some, starHop_some_some]
    rcases eq_or_ne i j with h | h
    · rw [if_pos h, if_pos h, natDist_cast]
      simp only [starParam_val]
      rw [div_sub_div_same, abs_div, abs_of_pos hc]
      ring
    · rw [if_neg h, if_neg h, Nat.cast_add]
      simp only [starParam_val]
      ring

/-! ## Part 4 — the star vertices are a `1/(n+1)`-net of the tripod -/

/-- **The net lemma.**  Every point of the tripod is within `1/(n+1)` of an embedded star
vertex: the apex maps to the apex, and the arm point at parameter `t` rounds up to the
vertex `k = ⌈t(n+1)⌉` on the same arm, at distance `|t - k/(n+1)| ≤ 1/(n+1)`. -/
theorem tripod_net (n : ℕ) (p : Tripod) :
    ∃ x : ScaledStar n, dist p (starToTripod n x) ≤ 1 / ((n : ℝ) + 1) := by
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rcases p with _ | ⟨i, t⟩
  · refine ⟨none, ?_⟩
    rw [starToTripod_none, dist_self]
    positivity
  · have ht0 : (0 : ℝ) < t.1 := t.2.1
    have ht1 : t.1 ≤ 1 := t.2.2
    have hkpos : 0 < ⌈t.1 * ((n : ℝ) + 1)⌉₊ := Nat.ceil_pos.mpr (mul_pos ht0 hc)
    have hkle : ⌈t.1 * ((n : ℝ) + 1)⌉₊ ≤ n + 1 := by
      refine Nat.ceil_le.mpr ?_
      have h := mul_le_mul_of_nonneg_right ht1 hc.le
      rw [one_mul] at h
      push_cast
      linarith
    refine ⟨some (i, ⟨⟨⌈t.1 * ((n : ℝ) + 1)⌉₊, by omega⟩,
      Fin.ne_of_val_ne (by simpa using hkpos.ne')⟩), ?_⟩
    rw [starToTripod_some, dist_eq_tripodDist, tripodDist_some_some, if_pos rfl,
      starParam_val]
    show |t.1 - (⌈t.1 * ((n : ℝ) + 1)⌉₊ : ℝ) / ((n : ℝ) + 1)| ≤ 1 / ((n : ℝ) + 1)
    have h1 : t.1 * ((n : ℝ) + 1) ≤ (⌈t.1 * ((n : ℝ) + 1)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈t.1 * ((n : ℝ) + 1)⌉₊ : ℝ) < t.1 * ((n : ℝ) + 1) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg ht0.le hc.le)
    rw [abs_sub_le_iff]
    constructor
    · have hle : t.1 ≤ (⌈t.1 * ((n : ℝ) + 1)⌉₊ : ℝ) / ((n : ℝ) + 1) := by
        rw [le_div_iff₀ hc]
        exact h1
      have hpos : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · have hle : (⌈t.1 * ((n : ℝ) + 1)⌉₊ : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) + t.1 := by
        rw [div_le_iff₀ hc, add_mul, one_div_mul_cancel hc.ne']
        linarith
      linarith

/-! ## Part 5 — the quantitative Gromov–Hausdorff bound -/

/-- **THE B1 BOUND.**  The Gromov–Hausdorff distance between the subdivided star (with its
scaled graph-geodesic metric) and the tripod is at most `1/(n+1)`: the vertex embedding is an
EXACT isometry (`ε₂ = 0`) whose image is a `1/(n+1)`-net. -/
theorem ghDist_star_le (n : ℕ) :
    GromovHausdorff.ghDist (ScaledStar n) Tripod ≤ 1 / ((n : ℝ) + 1) := by
  have key : GromovHausdorff.ghDist (ScaledStar n) Tripod
      ≤ 0 + 0 / 2 + 1 / ((n : ℝ) + 1) := by
    refine GromovHausdorff.ghDist_le_of_approx_subsets
        (s := (Set.univ : Set (ScaledStar n))) (fun z => starToTripod n z.1) ?_ ?_ ?_
    · exact fun x => ⟨x, Set.mem_univ x, le_of_eq (dist_self x)⟩
    · intro q
      obtain ⟨x, hx⟩ := tripod_net n q
      exact ⟨⟨x, Set.mem_univ x⟩, hx⟩
    · rintro ⟨x, _⟩ ⟨y, _⟩
      show |dist x y - dist (starToTripod n x) (starToTripod n y)| ≤ 0
      rw [scaledStar_dist_def, sub_self, abs_zero]
  linarith

/-! ## Part 6 — the B1 capstone -/

/-- **THE B1 CAPSTONE (Gromov–Hausdorff convergence to the TRIPOD).**  The subdivided star
graphs — abstract finite metric spaces carrying their scaled graph-geodesic hop metrics
(`scaledStar_dist_eq`) — converge in Gromov–Hausdorff space to the tripod, a compact metric
TREE whose branch point provably obstructs isometric embedding into ANY real inner-product
space (`tripod_no_isometric_embedding_into_inner`).  The first GH limit in this program that
is NOT (a subset of) a flat Euclidean space or torus — a genuinely non-Euclidean,
non-manifold limit, with the non-Euclideanness itself a theorem.  The branching is INSERTED
through the star topology of the graphs, not emergent (see the scope firewall in the
header). -/
theorem star_toGHSpace_tendsto_tripod :
    Tendsto (fun n : ℕ => GromovHausdorff.toGHSpace (ScaledStar n)) atTop
      (𝓝 (GromovHausdorff.toGHSpace Tripod)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : ∀ n : ℕ,
      dist (GromovHausdorff.toGHSpace (ScaledStar n)) (GromovHausdorff.toGHSpace Tripod)
        ≤ 1 / ((n : ℝ) + 1) := fun n => ghDist_star_le n
  have hub : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ)) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  exact squeeze_zero (fun n => dist_nonneg) hb hub

end QIQTH.TripodGH
