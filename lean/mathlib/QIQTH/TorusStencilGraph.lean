/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# TORUS STENCIL GRAPH — the cyclic d-dimensional lattice, the flat-torus embedding, the
geodesic identity, and the lower bound (brick T1)

First brick of the TORUS track (`docs/qg_roadmap/STATE_TORUS_CURVATURE_PLAN.md`, Track C): the
proven dimension-generic stencil machine (`QIQTH/StencilDimGraph.lean`, brick G1) is transplanted
from the d-cube `Fin d → Fin (N+1)` to the **cyclic d-dimensional lattice** `Fin d → ZMod N`,
embedded in the **flat continuum d-torus** `FlatTorus d = PiLp 2 (fun _ : Fin d => AddCircle 1)`
— Mathlib's genuine normed group structure on the circle, L²-multiplied.

## The wrap distance

The single new ingredient is `wrapDist a b = ((a - b).valMinAbs).natAbs` — the cyclic distance
on `ZMod N`, built from `ZMod.valMinAbs`, the **minimal-absolute integer representative** (the
unique representative in `(-N/2, N/2]`).  This one integer is simultaneously
* the sqrt-free **adjacency ingredient** (`sqDistT = Σ wrapDist²`, a decidable integer test),
* the **`AddCircle` norm value**: `‖embT x i - embT y i‖ = wrapDist (x i) (y i) / N` — the
  geodesic identity below, and
* (brick T2) the **minimizing walk lift**: `wrapDist_le_natAbs` says `valMinAbs` beats every
  other integer representative, which is exactly why the wrap-aware rounding walk is shortest.

## The T1 theorems

* `dist_embT` — **the geodesic identity**: the flat-torus distance between embedded lattice
  points is `√(Σᵢ (wrapDist (x i) (y i) / N)²)`, proved per coordinate through
  `AddCircle.norm_coe_eq_abs_iff` (the norm of a class with representative in `[-1/2, 1/2]` IS
  the representative's absolute value) and `PiLp.dist_eq_of_L2`.  This is the torus analogue of
  G1's cast bridge `euclD_sq_eq_sqDistD`.
* `dist_embT_le_of_adj` — each hop moves at most `R/N` on the torus (the embedding lands in the
  UNIT torus, so hops scale by `1/N`); chained along walks
  (`dist_embT_le_R_div_N_mul_walk_length`) and specialized to shortest walks:

      dist (embT x) (embT y) ≤ (R/N) * (torusGraphD d N R).dist x y
                                                (`dist_embT_le_R_div_N_mul_dist`)

  Connectivity (discharging the `Reachable` hypothesis) is brick T2.
* `dist_embT_le_margin_div_two` — the diameter bound: every coordinate norm is ≤ 1/2, so the
  torus distance is ≤ √d/2 ≤ `margin d / 2` (reusing G1's sqrt-free `margin`).

## Scope firewall (HONEST)

**The torus TOPOLOGY is INSERTED through the wrap rule** — the `ZMod N` cyclic structure — in
exactly the same way isotropy was inserted through the stencil rule in G1: it is NOT emergent
topology, and nothing here says why space would be periodic.  The eventual limit (brick T3) is
the FLAT torus: what changes vs the cube is only the global topology (no boundary, nontrivial
π₁), never the curvature.  The dimension `d` is an INPUT.  This is NOT GR, NOT a numerical `G`,
NOT QG.  `Reachable` is a HYPOTHESIS here, never an axiom.  No axioms, no `sorry`.
-/
import QIQTH.StencilDimGraph
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Homeomorph.Lemmas

namespace QIQTH.TorusStencilGraph

open QIQTH.StencilDimGraph

/-! ## Part 1 — the wrap distance on `ZMod N` -/

/-- **The cyclic (wrap-around) distance** on `ZMod N`: the absolute value of the
minimal-absolute integer representative of `a - b` (`ZMod.valMinAbs`, the unique representative
in `(-N/2, N/2]`). -/
def wrapDist {N : ℕ} (a b : ZMod N) : ℕ := ((a - b).valMinAbs).natAbs

/-- The wrap distance of a point to itself vanishes. -/
@[simp] lemma wrapDist_self {N : ℕ} (a : ZMod N) : wrapDist a a = 0 := by
  simp [wrapDist]

/-- The wrap distance is symmetric: `a - b` and `b - a` are negatives, and negation preserves
the absolute value of the minimal representative (`ZMod.natAbs_valMinAbs_neg` handles the even-N
boundary case `N/2` where `valMinAbs` itself is not odd). -/
lemma wrapDist_comm {N : ℕ} (a b : ZMod N) : wrapDist a b = wrapDist b a := by
  unfold wrapDist
  rw [← neg_sub b a, ZMod.natAbs_valMinAbs_neg]

/-- The wrap distance separates points. -/
lemma wrapDist_eq_zero_iff {N : ℕ} (a b : ZMod N) : wrapDist a b = 0 ↔ a = b := by
  rw [wrapDist, Int.natAbs_eq_zero, ZMod.valMinAbs_eq_zero, sub_eq_zero]

/-- The wrap distance is at most `N/2` — you can never be further than half-way around. -/
lemma wrapDist_le_half {N : ℕ} [NeZero N] (a b : ZMod N) : wrapDist a b ≤ N / 2 :=
  ZMod.natAbs_valMinAbs_le _

/-- **Minimality of the wrap distance (the 1-Lipschitz lemma)**: `valMinAbs` is the
minimal-absolute integer representative, so the wrap distance is dominated by `|k|` for EVERY
integer `k` representing `a - b`.  Any other representative differs by a nonzero multiple of
`N`, hence has absolute value ≥ `N - N/2 ≥ N/2 ≥ |valMinAbs|`.  In brick T2 this is what makes
the lifted straight-line walk project to a wrap-optimal walk. -/
lemma wrapDist_le_natAbs {N : ℕ} [NeZero N] (a b : ZMod N) (k : ℤ)
    (hk : (k : ZMod N) = a - b) : wrapDist a b ≤ k.natAbs := by
  have hdvd : (N : ℤ) ∣ k - (a - b).valMinAbs := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hk]
    ring
  obtain ⟨m, hm⟩ := hdvd
  have h1 : -(N : ℤ) < (a - b).valMinAbs * 2 := ((a - b).valMinAbs_mem_Ioc).1
  have h2 : (a - b).valMinAbs * 2 ≤ (N : ℤ) := ((a - b).valMinAbs_mem_Ioc).2
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast NeZero.pos N
  rw [wrapDist]
  rcases lt_trichotomy m 0 with hm0 | rfl | hm0
  · -- `k` sits at least a full period BELOW `valMinAbs`
    have hle : k - (a - b).valMinAbs ≤ -(N : ℤ) := by
      calc k - (a - b).valMinAbs = (N : ℤ) * m := hm
        _ ≤ (N : ℤ) * (-1) := mul_le_mul_of_nonneg_left (by omega) hNpos.le
        _ = -(N : ℤ) := by ring
    omega
  · -- `k` IS the minimal representative
    rw [mul_zero] at hm
    omega
  · -- `k` sits at least a full period ABOVE `valMinAbs`
    have hge : (N : ℤ) ≤ k - (a - b).valMinAbs := by
      calc (N : ℤ) = (N : ℤ) * 1 := (mul_one _).symm
        _ ≤ (N : ℤ) * m := mul_le_mul_of_nonneg_left (by omega) hNpos.le
        _ = k - (a - b).valMinAbs := hm.symm
    omega

/-! ## Part 1b — the circle-norm formula for `ZMod.toAddCircle`

Mathlib's `ZMod.toAddCircle : ZMod N →+ UnitAddCircle` sends `j mod N` to `j/N mod 1` — exactly
our embedding, one coordinate at a time, and an `AddMonoidHom`, so differences transport. -/

/-- **The circle-norm formula**: the `AddCircle 1` norm of `toAddCircle a` is exactly
`|valMinAbs a| / N`.  Since `|valMinAbs a| ≤ N/2`, the representative `valMinAbs a / N` lies in
`[-1/2, 1/2]`, where the circle norm IS the absolute value
(`AddCircle.norm_coe_eq_abs_iff`). -/
lemma norm_toAddCircle {N : ℕ} [NeZero N] (a : ZMod N) :
    ‖ZMod.toAddCircle a‖ = (a.valMinAbs.natAbs : ℝ) / (N : ℝ) := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have h2 : 2 * a.valMinAbs.natAbs ≤ N := by
    have h := ZMod.natAbs_valMinAbs_le a
    omega
  have habs : |((a.valMinAbs : ℤ) : ℝ)| = (a.valMinAbs.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hhalf : |((a.valMinAbs : ℤ) : ℝ) / (N : ℝ)| ≤ |(1 : ℝ)| / 2 := by
    have h2' : 2 * (a.valMinAbs.natAbs : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    rw [abs_one, abs_div, abs_of_pos hN, habs, div_le_iff₀ hN]
    linarith
  have key : ZMod.toAddCircle a
      = ((((a.valMinAbs : ℤ) : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
    conv_lhs => rw [← ZMod.coe_valMinAbs a]
    exact ZMod.toAddCircle_intCast _
  rw [key, (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr hhalf, abs_div, abs_of_pos hN,
    habs]

variable (d N R : ℕ)

/-! ## Part 2 — the integer squared wrap distance -/

/-- integer squared wrap distance between lattice points of the cyclic d-lattice. -/
def sqDistT (x y : Fin d → ZMod N) : ℤ :=
  ∑ i, ((wrapDist (x i) (y i) : ℤ))^2

/-- `sqDistT` is nonnegative — it is a sum of squares. -/
lemma sqDistT_nonneg (x y : Fin d → ZMod N) : 0 ≤ sqDistT d N x y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `sqDistT` is symmetric. -/
lemma sqDistT_comm (x y : Fin d → ZMod N) : sqDistT d N x y = sqDistT d N y x := by
  unfold sqDistT
  exact Finset.sum_congr rfl fun i _ => by rw [wrapDist_comm]

/-- `sqDistT` of a point with itself vanishes. -/
lemma sqDistT_self (x : Fin d → ZMod N) : sqDistT d N x x = 0 := by
  simp [sqDistT]

/-- `sqDistT` separates points: the sum of squares vanishes iff every coordinate agrees. -/
lemma sqDistT_eq_zero_iff (x y : Fin d → ZMod N) :
    sqDistT d N x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg ((wrapDist (x i) (y i) : ℤ)))).mp h
    funext i
    have hi : ((wrapDist (x i) (y i) : ℤ))^2 = 0 := hall i (Finset.mem_univ i)
    have h0 : wrapDist (x i) (y i) = 0 := by exact_mod_cast sq_eq_zero_iff.mp hi
    exact (wrapDist_eq_zero_iff _ _).mp h0
  · rintro rfl
    exact sqDistT_self d N x

/-! ## Part 3 — the cyclic stencil graph -/

/-- **The cyclic (torus) stencil graph**: two distinct points of the cyclic d-lattice are
adjacent exactly when their integer squared WRAP distance is at most `R²` — a decidable integer
test, no `Real.sqrt`.  The wrap rule is where the torus topology is INSERTED. -/
def torusGraphD : SimpleGraph (Fin d → ZMod N) where
  Adj x y := x ≠ y ∧ sqDistT d N x y ≤ (R : ℤ)^2
  symm := fun x y ⟨hne, hle⟩ => ⟨hne.symm, by rw [sqDistT_comm d N y x]; exact hle⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- The cyclic stencil adjacency is decidable — an integer test on a finite function type. -/
instance : DecidableRel (torusGraphD d N R).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ sqDistT d N x y ≤ (R : ℤ)^2))

/-! ## Part 4 — the flat continuum d-torus -/

/-- **The flat continuum d-torus**: the L² product of `d` copies of Mathlib's normed circle
group `AddCircle 1`. -/
abbrev FlatTorus (d : ℕ) : Type := PiLp 2 (fun _ : Fin d => AddCircle (1 : ℝ))

/-- The unit period is positive (local `Fact` instance feeding `AddCircle.compactSpace`). -/
instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The flat d-torus is compact: each `AddCircle 1` factor is compact, the pi type is compact,
and `PiLp.homeomorph` transports compactness through the (topology-preserving) `WithLp`
wrapper. -/
instance : CompactSpace (FlatTorus d) :=
  (PiLp.homeomorph 2 (fun _ : Fin d => AddCircle (1 : ℝ))).symm.compactSpace

/-- The flat d-torus is nonempty. -/
instance : Nonempty (FlatTorus d) := ⟨0⟩

/-! ## Part 5 — the torus embedding -/

/-- the lattice point embedded in the flat d-torus: coordinate `i` is the class of
`(x i).val / N` on the unit circle. -/
noncomputable def embT (x : Fin d → ZMod N) : FlatTorus d :=
  WithLp.toLp 2 (fun i => ((((x i).val : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ)))

/-- coordinates of the embedded lattice point. -/
lemma embT_apply (x : Fin d → ZMod N) (i : Fin d) :
    embT d N x i = ((((x i).val : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ)) := rfl

/-- Each coordinate of the embedding IS Mathlib's `ZMod.toAddCircle` — an `AddMonoidHom`, so
coordinate differences become `toAddCircle` of `ZMod` differences. -/
lemma embT_apply_eq_toAddCircle [NeZero N] (x : Fin d → ZMod N) (i : Fin d) :
    embT d N x i = ZMod.toAddCircle (x i) := by
  rw [embT_apply, ZMod.toAddCircle_apply]

/-! ## Part 6 — the geodesic identity -/

/-- **THE GEODESIC IDENTITY (the heart of T1).**  The flat-torus distance between embedded
lattice points is the L² combination of the per-coordinate WRAP distances, scaled by `1/N`:

    dist (embT x) (embT y) = √(Σᵢ (wrapDist (x i) (y i) / N)²)

Per coordinate: the difference of classes is `toAddCircle (x i - y i)`, whose representative
`valMinAbs (x i - y i) / N` lies in `[-1/2, 1/2]`, where the circle norm is the plain absolute
value.  This is the torus analogue of G1's cast bridge. -/
theorem dist_embT [NeZero N] (x y : Fin d → ZMod N) :
    dist (embT d N x) (embT d N y)
      = Real.sqrt (∑ i, ((wrapDist (x i) (y i) : ℝ) / (N : ℝ))^2) := by
  rw [PiLp.dist_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [dist_eq_norm, embT_apply_eq_toAddCircle, embT_apply_eq_toAddCircle, ← map_sub,
    norm_toAddCircle]
  rfl

/-! ## Part 7 — the lower bound (the T1 chain) and the diameter bound -/

/-- **Each hop moves at most `R/N` on the flat torus.**  The embedding lands in the UNIT torus,
so the integer stencil radius `R` scales to `R/N`. -/
theorem dist_embT_le_of_adj [NeZero N] {x y : Fin d → ZMod N}
    (h : (torusGraphD d N R).Adj x y) :
    dist (embT d N x) (embT d N y) ≤ (R : ℝ) / (N : ℝ) := by
  have hcast : ((sqDistT d N x y : ℤ) : ℝ) = ∑ i, ((wrapDist (x i) (y i) : ℝ))^2 := by
    unfold sqDistT
    push_cast
    rfl
  have hsum : ∑ i, ((wrapDist (x i) (y i) : ℝ) / (N : ℝ))^2 ≤ ((R : ℝ) / (N : ℝ))^2 := by
    calc ∑ i, ((wrapDist (x i) (y i) : ℝ) / (N : ℝ))^2
        = (∑ i, ((wrapDist (x i) (y i) : ℝ))^2) / (N : ℝ)^2 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => div_pow _ _ _
      _ = ((sqDistT d N x y : ℤ) : ℝ) / (N : ℝ)^2 := by rw [hcast]
      _ ≤ (R : ℝ)^2 / (N : ℝ)^2 := by
          gcongr
          exact_mod_cast h.2
      _ = ((R : ℝ) / (N : ℝ))^2 := (div_pow _ _ _).symm
  rw [dist_embT]
  calc Real.sqrt (∑ i, ((wrapDist (x i) (y i) : ℝ) / (N : ℝ))^2)
      ≤ Real.sqrt (((R : ℝ) / (N : ℝ))^2) := Real.sqrt_le_sqrt hsum
    _ = (R : ℝ) / (N : ℝ) := Real.sqrt_sq (by positivity)

/-- **Any walk of `k` hops moves at most `(R/N)·k` on the flat torus** — triangle inequality
chained along the walk, each hop bounded by `dist_embT_le_of_adj`. -/
lemma dist_embT_le_R_div_N_mul_walk_length [NeZero N] {x y : Fin d → ZMod N}
    (w : (torusGraphD d N R).Walk x y) :
    dist (embT d N x) (embT d N y) ≤ ((R : ℝ) / (N : ℝ)) * w.length := by
  induction w with
  | nil => simp
  | @cons a b c hadj p ih =>
      have htri : dist (embT d N a) (embT d N c)
          ≤ dist (embT d N a) (embT d N b) + dist (embT d N b) (embT d N c) :=
        dist_triangle _ _ _
      have h1 : dist (embT d N a) (embT d N b) ≤ (R : ℝ) / (N : ℝ) :=
        dist_embT_le_of_adj d N R hadj
      have hlen : (((SimpleGraph.Walk.cons hadj p).length : ℕ) : ℝ) = (p.length : ℝ) + 1 := by
        rw [SimpleGraph.Walk.length_cons]; push_cast; ring
      rw [hlen, mul_add, mul_one,
        add_comm (((R : ℝ) / (N : ℝ)) * (p.length : ℝ)) ((R : ℝ) / (N : ℝ))]
      exact htri.trans (add_le_add h1 ih)

/-- **THE T1 THEOREM (torus lower bound on the hop metric).**  If `x` and `y` are reachable in
the cyclic stencil graph, the flat-torus distance between their embeddings is at most `R/N`
times the graph hop-distance.  Connectivity (discharging `Reachable`) is brick T2. -/
theorem dist_embT_le_R_div_N_mul_dist [NeZero N] {x y : Fin d → ZMod N}
    (hreach : (torusGraphD d N R).Reachable x y) :
    dist (embT d N x) (embT d N y)
      ≤ ((R : ℝ) / (N : ℝ)) * ((torusGraphD d N R).dist x y : ℝ) := by
  obtain ⟨w, hw⟩ := hreach.exists_walk_length_eq_dist
  have hle := dist_embT_le_R_div_N_mul_walk_length d N R w
  rwa [hw] at hle

/-- **The torus diameter bound.**  Every coordinate wrap distance is at most `N/2`, so every
coordinate circle-norm is at most `1/2`, the sum of squares is at most `d/4`, and
`√(d/4) = √d/2 ≤ margin d / 2` — reusing G1's sqrt-free `margin`. -/
theorem dist_embT_le_margin_div_two [NeZero N] (x y : Fin d → ZMod N) :
    dist (embT d N x) (embT d N y) ≤ (margin d : ℝ) / 2 := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hcoord : ∀ i : Fin d,
      ((wrapDist (x i) (y i) : ℝ) / (N : ℝ))^2 ≤ ((1 : ℝ)/2)^2 := by
    intro i
    have h2 : 2 * wrapDist (x i) (y i) ≤ N := by
      have := wrapDist_le_half (x i) (y i)
      omega
    have h2' : 2 * (wrapDist (x i) (y i) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    have hle : (wrapDist (x i) (y i) : ℝ) / (N : ℝ) ≤ (1 : ℝ)/2 := by
      rw [div_le_iff₀ hN]
      linarith
    have h0 : (0 : ℝ) ≤ (wrapDist (x i) (y i) : ℝ) / (N : ℝ) := by positivity
    exact sq_le_sq' (by linarith) hle
  have hsum : (∑ i, ((wrapDist (x i) (y i) : ℝ) / (N : ℝ))^2) ≤ (d : ℝ) * ((1 : ℝ)/2)^2 := by
    calc (∑ i, ((wrapDist (x i) (y i) : ℝ) / (N : ℝ))^2)
        ≤ ∑ _i : Fin d, ((1 : ℝ)/2)^2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * ((1 : ℝ)/2)^2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [dist_embT]
  calc Real.sqrt (∑ i, ((wrapDist (x i) (y i) : ℝ) / (N : ℝ))^2)
      ≤ Real.sqrt ((d : ℝ) * ((1 : ℝ)/2)^2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * ((1 : ℝ)/2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ (margin d : ℝ) * ((1 : ℝ)/2) :=
        mul_le_mul_of_nonneg_right (sqrt_le_margin d) (by norm_num)
    _ = (margin d : ℝ) / 2 := by ring

end QIQTH.TorusStencilGraph
