/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# TORUS STENCIL WALK — the wrap-aware rounding walk, the pinch, and the vanishing distortion
(brick T2)

Second brick of the TORUS track (`docs/qg_roadmap/STATE_TORUS_CURVATURE_PLAN.md`): the torus
analogue of the proven dimension-generic bricks G2 (`QIQTH/StencilDimWalk.lean`) and G3
(`QIQTH/StencilDimDistortion.lean`) on the cyclic d-lattice `Fin d → ZMod N` of brick T1
(`QIQTH/TorusStencilGraph.lean`).

## The minimizing lift (what differs from G2 — the torus is SIMPLER)

Per coordinate the **minimizing integer lift** is `liftZ x y i = (y i - x i).valMinAbs` — the
minimal-absolute integer representative of the coordinate difference.  Its two defining facts,

* `((liftZ x y i : ℤ) : ZMod N) = y i - x i`  (it IS a representative), and
* `(liftZ x y i).natAbs = wrapDist (x i) (y i)`  (it is the SHORTEST one),

turn T1's minimality lemma `wrapDist_le_natAbs` into the **projection step**: the straight-line
rounding walk of G2 runs on the LIFTED segment from `(x i).val` to `(x i).val + liftZ x y i`
in ℝ and projects mod `N` — with **no box clamping at all**, because the torus has no boundary.
The geodesic identity of T1 makes the lifted segment's Euclidean length exactly
`N · dist (embT x) (embT y)`, so the SAME margin closing estimate as G2
(`(R−m)² + 2m(R−m) + m² = R²`, Cauchy–Schwarz, `√d ≤ m = margin d`) shows consecutive projected
waypoints are equal or wrap-adjacent.

## The T2 theorems

* `torusD_walk_exists` — the explicit wrap-aware walk,
  `length ≤ ⌈N·dist(embT x)(embT y) / (R − margin d)⌉₊`;
* `torusD_reachable` — connectivity of the cyclic stencil graph (discharges T1's `Reachable`
  hypothesis, so `dist_embT_le_R_div_N_mul_dist` fires unconditionally for `R ≥ margin d + 1`);
* `torusD_dist_le` — the torus upper bound on the hop metric;
* `torusD_dist_pinch` — the two-sided pinch of the scaled hop metric `(R/N)·dist` against the
  flat-torus distance, with additive error `m²/(2(R−m)) + R/N` — the `/2` comes from T1's
  diameter bound `dist(embT x)(embT y) ≤ m/2` (the torus diameter beats the cube's `m·N`);
* `torusDistortionError` / `torusD_dist_sub_le` / `torusDistortionError_tendsto_zero` — the
  explicit distortion error of the microscopic-stencil schedule `R_N = Nat.sqrt N` and its
  vanishing limit for every fixed `d`;
* `torusD_scaled_metric_tendsto` — the ε-N₀ capstone: the scaled hop metric converges to the
  flat-torus metric UNIFORMLY in the pair of lattice points.

## Scope firewall (HONEST)

**The torus TOPOLOGY is INSERTED through the wrap rule** — the `ZMod N` cyclic structure — not
emergent: nothing here says why space would be periodic.  The dimension `d` is an INPUT.  The
comparison is EXTRINSIC, against the presupposed flat continuum torus (the intrinsic
Gromov–Hausdorff statement is brick T3).  The geometry is FLAT — what changes vs the cube is
only the global topology, never the curvature.  This is NOT GR, NOT a numerical `G`, NOT QG.
No axioms, no `sorry`.
-/
import QIQTH.TorusStencilGraph
import QIQTH.StencilDimWalk
import QIQTH.StencilDimDistortion

namespace QIQTH.TorusStencilWalk

open QIQTH.StencilDimGraph QIQTH.StencilWalk QIQTH.TorusStencilGraph Filter Topology

variable {d N R : ℕ}

/-! ## Per-coordinate rounding cost (restated from `StencilDimWalk`, where these are private) -/

/-- Squares are monotone under `abs`-bounds. -/
private lemma sq_le_sq_of_abs_le {u v : ℝ} (h : |u| ≤ v) : u ^ 2 ≤ v ^ 2 :=
  sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2

/-- **One rounded step, one coordinate.**  Rounding both waypoints costs at most `1/2 + 1/2` on
top of the real displacement, so the squared rounded displacement is at most
`(real displacement)² + 2c + 1` whenever the real displacement is `≤ c` in absolute value. -/
private lemma round_diff_sq_le {s s' c : ℝ} (h : |s - s'| ≤ c) :
    (((round s : ℤ) : ℝ) - ((round s' : ℤ) : ℝ)) ^ 2 ≤ (s - s') ^ 2 + 2 * c + 1 := by
  have e1 : |((round s : ℤ) : ℝ) - s| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round s
  have e2 : |s' - ((round s' : ℤ) : ℝ)| ≤ 1 / 2 := abs_sub_round s'
  have habs : |((round s : ℤ) : ℝ) - ((round s' : ℤ) : ℝ)| ≤ |s - s'| + 1 := by
    calc |((round s : ℤ) : ℝ) - ((round s' : ℤ) : ℝ)|
        ≤ |((round s : ℤ) : ℝ) - s| + |s - ((round s' : ℤ) : ℝ)| := abs_sub_le _ _ _
      _ ≤ |((round s : ℤ) : ℝ) - s| + (|s - s'| + |s' - ((round s' : ℤ) : ℝ)|) := by
          have h3 := abs_sub_le s s' (((round s' : ℤ) : ℝ))
          linarith
      _ ≤ |s - s'| + 1 := by linarith
  have hsq := sq_le_sq_of_abs_le habs
  linarith [hsq, sq_abs (s - s'), h]

/-- **One rounded step, all `d` coordinates** (the margin closing estimate, restated from G2).
If the real step has squared Euclidean length at most `(RR − m)²` with `0 ≤ m ≤ RR` and
`d ≤ m²`, the rounded step has squared length at most `RR²`: per-coordinate rounding costs sum
to `Σ(Δreal)² + 2·Σ|Δreal| + d`, Cauchy–Schwarz bounds `Σ|Δreal| ≤ √d·(RR−m) ≤ m·(RR−m)`, and
`(RR−m)² + 2m(RR−m) + m² = RR²`. -/
private lemma round_diff_sq_sum_le {u u' : Fin d → ℝ} {m RR : ℝ}
    (hm : 0 ≤ m) (hmR : m ≤ RR) (hd : (d : ℝ) ≤ m ^ 2)
    (hsum : ∑ c, (u c - u' c) ^ 2 ≤ (RR - m) ^ 2) :
    ∑ c, (((round (u c) : ℤ) : ℝ) - ((round (u' c) : ℤ) : ℝ)) ^ 2 ≤ RR ^ 2 := by
  have hRm0 : (0 : ℝ) ≤ RR - m := by linarith
  -- Cauchy–Schwarz on the absolute real steps
  have hCS : (∑ c, |u c - u' c|) ^ 2 ≤ (d : ℝ) * ∑ c, (u c - u' c) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun c => |u c - u' c|)
    simp only [sq_abs] at h
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hA0 : 0 ≤ ∑ c, |u c - u' c| := Finset.sum_nonneg fun c _ => abs_nonneg _
  -- hence the abs-sum is at most m·(RR − m)
  have hAsq : (∑ c, |u c - u' c|) ^ 2 ≤ (m * (RR - m)) ^ 2 := by
    have h1 : (d : ℝ) * (∑ c, (u c - u' c) ^ 2) ≤ (d : ℝ) * (RR - m) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2 : (d : ℝ) * (RR - m) ^ 2 ≤ m ^ 2 * (RR - m) ^ 2 :=
      mul_le_mul_of_nonneg_right hd (sq_nonneg _)
    have h3 : m ^ 2 * (RR - m) ^ 2 = (m * (RR - m)) ^ 2 := by ring
    linarith
  have hA : (∑ c, |u c - u' c|) ≤ m * (RR - m) :=
    le_of_sq_le_sq hAsq (mul_nonneg hm hRm0)
  -- per-coordinate rounding cost, summed over the d coordinates
  have hsumle : ∑ c, (((round (u c) : ℤ) : ℝ) - ((round (u' c) : ℤ) : ℝ)) ^ 2
      ≤ ∑ c, ((u c - u' c) ^ 2 + 2 * |u c - u' c| + 1) :=
    Finset.sum_le_sum fun c _ => round_diff_sq_le (le_refl _)
  have hsplit : ∑ c, ((u c - u' c) ^ 2 + 2 * |u c - u' c| + 1)
      = (∑ c, (u c - u' c) ^ 2) + 2 * (∑ c, |u c - u' c|) + (d : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hsplit] at hsumle
  -- close: (RR − m)² + 2m(RR − m) + m² = RR²
  have hkey : (RR - m) ^ 2 + 2 * (m * (RR - m)) + m ^ 2 = RR ^ 2 := by ring
  linarith

/-! ## The minimizing lift -/

/-- **The minimizing integer lift** of the coordinate difference: the minimal-absolute integer
representative `valMinAbs` of `y i - x i`.  This is the ONLY new ingredient vs G2: the lifted
straight segment from `(x i).val` to `(x i).val + liftZ x y i` projects mod `N` to a
wrap-optimal path. -/
def liftZ (x y : Fin d → ZMod N) (i : Fin d) : ℤ := (y i - x i).valMinAbs

/-- The lift represents the coordinate difference mod `N`. -/
lemma liftZ_cast (x y : Fin d → ZMod N) (i : Fin d) :
    ((liftZ x y i : ℤ) : ZMod N) = y i - x i := ZMod.coe_valMinAbs _

/-- The absolute value of the lift IS the wrap distance — the lift is minimal. -/
lemma liftZ_natAbs (x y : Fin d → ZMod N) (i : Fin d) :
    (liftZ x y i).natAbs = wrapDist (x i) (y i) := by
  rw [wrapDist_comm]; rfl

/-- **The lifted Euclidean length is `N` times the flat-torus distance**: by T1's geodesic
identity, `Σᵢ (liftZ x y i)² = (N · dist (embT x) (embT y))²`. -/
lemma sum_liftZ_sq [NeZero N] (x y : Fin d → ZMod N) :
    ∑ i, ((liftZ x y i : ℤ) : ℝ) ^ 2
      = ((N : ℝ) * dist (embT d N x) (embT d N y)) ^ 2 := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  rw [dist_embT, mul_pow, Real.sq_sqrt (by positivity), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← liftZ_natAbs x y i, Nat.cast_natAbs, div_pow, Int.cast_abs, sq_abs]
  field_simp

/-! ## The lifted real segment and the projected rounded waypoints -/

/-- The real (lifted) segment coordinate: the `j`-th of `k` equal steps from `(x i).val` to
`(x i).val + liftZ x y i` in ℝ — G2's `seg` machinery on the minimizing lift. -/
noncomputable def segT (x y : Fin d → ZMod N) (k j : ℕ) (i : Fin d) : ℝ :=
  seg ((x i).val : ℝ) (((x i).val : ℝ) + ((liftZ x y i : ℤ) : ℝ)) k j

/-- Consecutive lifted segment coordinates differ by exactly `liftZ x y i / k`. -/
lemma segT_step (x y : Fin d → ZMod N) {k : ℕ} (hk : k ≠ 0) (j : ℕ) (i : Fin d) :
    segT x y k j i - segT x y k (j + 1) i = -(((liftZ x y i : ℤ) : ℝ) / (k : ℝ)) := by
  unfold segT
  rw [seg_step _ _ hk j, add_sub_cancel_left]

/-- **The projected rounded waypoint**: round each lifted real coordinate to the nearest
integer and cast mod `N`.  NO clamp, NO box — the torus has no boundary, the mod-`N` cast
handles everything. -/
noncomputable def wayPtT (x y : Fin d → ZMod N) (k j : ℕ) : Fin d → ZMod N :=
  fun i => ((round (segT x y k j i) : ℤ) : ZMod N)

/-- The chain starts at `x`: the segment starts at the integer `(x i).val`, rounding is exact
there, and the mod-`N` cast of the value is the point itself. -/
theorem wayPtT_zero [NeZero N] (x y : Fin d → ZMod N) (k : ℕ) : wayPtT x y k 0 = x := by
  funext i
  show ((round (segT x y k 0 i) : ℤ) : ZMod N) = x i
  rw [segT, seg_zero, round_natCast, Int.cast_natCast]
  exact ZMod.natCast_rightInverse (x i)

/-- The chain ends at `y` (for `k ≠ 0`): the segment ends at the integer
`(x i).val + liftZ x y i`, rounding is exact there, and the mod-`N` cast is
`x i + (y i - x i) = y i` by the lift fact. -/
theorem wayPtT_last [NeZero N] (x y : Fin d → ZMod N) {k : ℕ} (hk : k ≠ 0) :
    wayPtT x y k k = y := by
  funext i
  show ((round (segT x y k k i) : ℤ) : ZMod N) = y i
  rw [segT, seg_last _ _ hk]
  have hq : (((x i).val : ℝ) + ((liftZ x y i : ℤ) : ℝ))
      = ((((x i).val : ℤ) + liftZ x y i : ℤ) : ℝ) := by push_cast; ring
  rw [hq, round_intCast, Int.cast_add, Int.cast_natCast, liftZ_cast,
    ZMod.natCast_rightInverse (x i)]
  ring

/-! ## The adjacency step -/

/-- **THE T2 ADJACENCY STEP.**  For `R ≥ margin d + 1` and chunk count
`k ≥ N·dist(embT x)(embT y) / (R − margin d)`, consecutive projected rounded waypoints are
equal or wrap-adjacent: the lifted real step has squared length `≤ (R−m)²` (geodesic identity),
the margin closing estimate bounds the rounded step by `R²`, and T1's minimality lemma
`wrapDist_le_natAbs` projects the integer bound through the mod-`N` cast. -/
theorem wayPtT_step [NeZero N] (hR : margin d + 1 ≤ R) {x y : Fin d → ZMod N} {k : ℕ}
    (hk : k ≠ 0)
    (hDk : (N : ℝ) * dist (embT d N x) (embT d N y)
      ≤ (k : ℝ) * ((R : ℝ) - (margin d : ℝ)))
    {j : ℕ} (_hj : j < k) :
    wayPtT x y k j = wayPtT x y k (j + 1) ∨
      (torusGraphD d N R).Adj (wayPtT x y k j) (wayPtT x y k (j + 1)) := by
  by_cases heq : wayPtT x y k j = wayPtT x y k (j + 1)
  · exact Or.inl heq
  · right
    refine ⟨heq, ?_⟩
    have hRm : ((margin d : ℕ) : ℝ) + 1 ≤ (R : ℝ) := by exact_mod_cast hR
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hL0 : 0 ≤ (N : ℝ) * dist (embT d N x) (embT d N y) :=
      mul_nonneg (Nat.cast_nonneg _) dist_nonneg
    -- the lifted real step has squared length (N·dist/k)² ≤ (R − m)²
    have hs1 : ∑ i, (segT x y k j i - segT x y k (j + 1) i) ^ 2
        = ((N : ℝ) * dist (embT d N x) (embT d N y)) ^ 2 / (k : ℝ) ^ 2 := by
      rw [← sum_liftZ_sq x y, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [segT_step x y hk j i]
      ring
    have hsum : ∑ i, (segT x y k j i - segT x y k (j + 1) i) ^ 2
        ≤ ((R : ℝ) - (margin d : ℝ)) ^ 2 := by
      rw [hs1, div_le_iff₀ (pow_pos hkR 2)]
      nlinarith [hDk, hL0]
    -- the margin closing estimate (G2's crux, restated above)
    have hm0 : (0 : ℝ) ≤ (margin d : ℝ) := Nat.cast_nonneg _
    have hmle : ((margin d : ℕ) : ℝ) ≤ (R : ℝ) := by linarith
    have hd_le : (d : ℝ) ≤ ((margin d : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast (lt_margin_sq d).le
    have hclose := round_diff_sq_sum_le hm0 hmle hd_le hsum
    -- per coordinate: project through the mod-N cast via T1's minimality lemma
    have hcoord : ∀ i : Fin d,
        ((wrapDist (wayPtT x y k j i) (wayPtT x y k (j + 1) i) : ℤ)) ^ 2
          ≤ (round (segT x y k j i) - round (segT x y k (j + 1) i)) ^ 2 := by
      intro i
      have hcast : ((round (segT x y k j i) - round (segT x y k (j + 1) i) : ℤ) : ZMod N)
          = wayPtT x y k j i - wayPtT x y k (j + 1) i := by
        simp only [wayPtT]
        push_cast
        ring
      have h1 := wrapDist_le_natAbs (wayPtT x y k j i) (wayPtT x y k (j + 1) i) _ hcast
      have h2 : (wrapDist (wayPtT x y k j i) (wayPtT x y k (j + 1) i)) ^ 2
          ≤ (round (segT x y k j i) - round (segT x y k (j + 1) i)).natAbs ^ 2 :=
        Nat.pow_le_pow_left h1 2
      calc ((wrapDist (wayPtT x y k j i) (wayPtT x y k (j + 1) i) : ℤ)) ^ 2
          ≤ (((round (segT x y k j i) - round (segT x y k (j + 1) i)).natAbs : ℤ)) ^ 2 := by
            exact_mod_cast h2
        _ = (round (segT x y k j i) - round (segT x y k (j + 1) i)) ^ 2 := by
            rw [← Int.abs_eq_natAbs, sq_abs]
    -- sum and cast the integer adjacency test
    have hZ : sqDistT d N (wayPtT x y k j) (wayPtT x y k (j + 1))
        ≤ ∑ i, (round (segT x y k j i) - round (segT x y k (j + 1) i)) ^ 2 :=
      Finset.sum_le_sum fun i _ => hcoord i
    have hfin : ((sqDistT d N (wayPtT x y k j) (wayPtT x y k (j + 1)) : ℤ) : ℝ)
        ≤ (R : ℝ) ^ 2 := by
      calc ((sqDistT d N (wayPtT x y k j) (wayPtT x y k (j + 1)) : ℤ) : ℝ)
          ≤ ((∑ i, (round (segT x y k j i) - round (segT x y k (j + 1) i)) ^ 2 : ℤ) : ℝ) := by
            exact_mod_cast hZ
        _ = ∑ i, (((round (segT x y k j i) : ℤ) : ℝ)
              - ((round (segT x y k (j + 1) i) : ℤ) : ℝ)) ^ 2 := by
            push_cast
            rfl
        _ ≤ (R : ℝ) ^ 2 := hclose
    exact_mod_cast hfin

/-! ## The T2 walk theorems -/

/-- **THE T2 WALK (explicit construction).**  For stencil radius `R ≥ margin d + 1` and any two
points of the cyclic d-lattice, the projected rounded-segment chain is a walk in
`torusGraphD d N R` of length at most `⌈N·dist(embT x)(embT y) / (R − margin d)⌉₊`. -/
theorem torusD_walk_exists [NeZero N] (hR : margin d + 1 ≤ R) (x y : Fin d → ZMod N) :
    ∃ w : (torusGraphD d N R).Walk x y,
      w.length ≤ ⌈(N : ℝ) * dist (embT d N x) (embT d N y)
        / ((R : ℝ) - (margin d : ℝ))⌉₊ := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨SimpleGraph.Walk.nil, Nat.zero_le _⟩
  · have hRm : ((margin d : ℕ) : ℝ) + 1 ≤ (R : ℝ) := by exact_mod_cast hR
    have hRmpos : (0 : ℝ) < (R : ℝ) - (margin d : ℝ) := by linarith
    have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
    -- distinct lattice points are a positive flat-torus distance apart
    have hDpos : 0 < (N : ℝ) * dist (embT d N x) (embT d N y) := by
      refine mul_pos hN ?_
      rw [dist_embT]
      apply Real.sqrt_pos.mpr
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
      refine Finset.sum_pos' (fun c _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
      have hw : wrapDist (x i) (y i) ≠ 0 := fun h => hi ((wrapDist_eq_zero_iff _ _).mp h)
      have hwR : (0 : ℝ) < (wrapDist (x i) (y i) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hw
      exact pow_pos (div_pos hwR hN) 2
    set k := ⌈(N : ℝ) * dist (embT d N x) (embT d N y)
      / ((R : ℝ) - (margin d : ℝ))⌉₊ with hkdef
    have hkpos : 0 < k := Nat.ceil_pos.mpr (div_pos hDpos hRmpos)
    have hk0 : k ≠ 0 := hkpos.ne'
    have hDk : (N : ℝ) * dist (embT d N x) (embT d N y)
        ≤ (k : ℝ) * ((R : ℝ) - (margin d : ℝ)) := by
      have hle := Nat.le_ceil ((N : ℝ) * dist (embT d N x) (embT d N y)
        / ((R : ℝ) - (margin d : ℝ)))
      rw [← hkdef] at hle
      have h := mul_le_mul_of_nonneg_right hle hRmpos.le
      rwa [div_mul_cancel₀ _ hRmpos.ne'] at h
    -- each consecutive pair of projected waypoints is equal or wrap-adjacent
    have hstep : ∀ i, i < k → wayPtT x y k i = wayPtT x y k (i + 1) ∨
        (torusGraphD d N R).Adj (wayPtT x y k i) (wayPtT x y k (i + 1)) :=
      fun i hik => wayPtT_step hR hk0 hDk hik
    obtain ⟨w, hw⟩ := walk_of_lazy_chain (fun i => wayPtT x y k i) k hstep
    refine ⟨w.copy (wayPtT_zero x y k) (wayPtT_last x y hk0), ?_⟩
    rw [SimpleGraph.Walk.length_copy]
    exact hw

/-- **Connectivity of the cyclic stencil graph** for `R ≥ margin d + 1` — discharges the
`Reachable` hypothesis of T1's `dist_embT_le_R_div_N_mul_dist`. -/
theorem torusD_reachable [NeZero N] (hR : margin d + 1 ≤ R) (x y : Fin d → ZMod N) :
    (torusGraphD d N R).Reachable x y := by
  obtain ⟨w, -⟩ := torusD_walk_exists hR x y
  exact w.reachable

/-- **The torus upper bound on the hop metric**: for `R ≥ margin d + 1`,
`dist x y ≤ N·dist(embT x)(embT y)/(R − margin d) + 1` — the two-sided companion to T1's
`dist(embT x)(embT y) ≤ (R/N)·dist x y`. -/
theorem torusD_dist_le [NeZero N] (hR : margin d + 1 ≤ R) (x y : Fin d → ZMod N) :
    (((torusGraphD d N R).dist x y : ℕ) : ℝ)
      ≤ (N : ℝ) * dist (embT d N x) (embT d N y) / ((R : ℝ) - (margin d : ℝ)) + 1 := by
  obtain ⟨w, hw⟩ := torusD_walk_exists hR x y
  have hd : (torusGraphD d N R).dist x y
      ≤ ⌈(N : ℝ) * dist (embT d N x) (embT d N y) / ((R : ℝ) - (margin d : ℝ))⌉₊ :=
    le_trans (SimpleGraph.dist_le w) hw
  have hRm : ((margin d : ℕ) : ℝ) + 1 ≤ (R : ℝ) := by exact_mod_cast hR
  have hnn : 0 ≤ (N : ℝ) * dist (embT d N x) (embT d N y) / ((R : ℝ) - (margin d : ℝ)) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) dist_nonneg) (by linarith)
  have hceil : (⌈(N : ℝ) * dist (embT d N x) (embT d N y)
        / ((R : ℝ) - (margin d : ℝ))⌉₊ : ℝ)
      < (N : ℝ) * dist (embT d N x) (embT d N y) / ((R : ℝ) - (margin d : ℝ)) + 1 :=
    Nat.ceil_lt_add_one hnn
  have hcast : (((torusGraphD d N R).dist x y : ℕ) : ℝ)
      ≤ (⌈(N : ℝ) * dist (embT d N x) (embT d N y)
          / ((R : ℝ) - (margin d : ℝ))⌉₊ : ℝ) := by exact_mod_cast hd
  linarith

/-! ## The pinch -/

/-- **THE T2 PINCH.**  For `R ≥ margin d + 1` and `N ≥ 1` the scaled hop metric `(R/N)·dist` is
pinched against the flat-torus distance, with additive error `m²/(2(R−m)) + R/N`
(`m = margin d`) — T1's lower bound (now unconditional via `torusD_reachable`) and the torus
upper bound, made UNIFORM in `x y` by T1's diameter bound `dist(embT x)(embT y) ≤ m/2` (whence
the `/2`: the torus diameter is `m/2`, sharper than the cube's `m·N`-scaled bound). -/
theorem torusD_dist_pinch [NeZero N] (hR : margin d + 1 ≤ R) (hN : 1 ≤ N)
    (x y : Fin d → ZMod N) :
    dist (embT d N x) (embT d N y)
        ≤ ((R : ℝ) / (N : ℝ)) * ((torusGraphD d N R).dist x y : ℝ)
    ∧ ((R : ℝ) / (N : ℝ)) * ((torusGraphD d N R).dist x y : ℝ)
        ≤ dist (embT d N x) (embT d N y)
          + ((margin d : ℝ) ^ 2 / (2 * ((R : ℝ) - (margin d : ℝ))) + (R : ℝ) / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hRm1 : ((margin d : ℕ) : ℝ) + 1 ≤ (R : ℝ) := by exact_mod_cast hR
  have hm0 : (0 : ℝ) ≤ (margin d : ℝ) := Nat.cast_nonneg _
  have hRm : (0 : ℝ) < (R : ℝ) - (margin d : ℝ) := by linarith
  constructor
  · -- LOWER: T1's `dist_embT ≤ (R/N)·dist`, reachability discharged by T2
    exact dist_embT_le_R_div_N_mul_dist d N R (torusD_reachable hR x y)
  · -- UPPER: `dist ≤ N·D/(R−m) + 1`, multiplied by `R/N`, plus the diameter `D ≤ m/2`
    have hup : (((torusGraphD d N R).dist x y : ℕ) : ℝ)
        ≤ (N : ℝ) * dist (embT d N x) (embT d N y) / ((R : ℝ) - (margin d : ℝ)) + 1 :=
      torusD_dist_le hR x y
    have hD0 : 0 ≤ dist (embT d N x) (embT d N y) := dist_nonneg
    have hdiam : dist (embT d N x) (embT d N y) ≤ (margin d : ℝ) / 2 :=
      dist_embT_le_margin_div_two d N x y
    -- clear the `(R−m)` denominator in the upper bound
    have hup' : ((torusGraphD d N R).dist x y : ℝ) * ((R : ℝ) - (margin d : ℝ))
        ≤ (N : ℝ) * dist (embT d N x) (embT d N y) + ((R : ℝ) - (margin d : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hup hRm.le
      rwa [add_mul, one_mul, div_mul_cancel₀ _ hRm.ne'] at h
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
    -- the polynomial (denominator-free) form of the upper bound
    have hpoly : (R : ℝ) * (((torusGraphD d N R).dist x y : ℝ) * ((R : ℝ) - (margin d : ℝ)))
        ≤ (N : ℝ) * dist (embT d N x) (embT d N y) * ((R : ℝ) - (margin d : ℝ))
          + (margin d : ℝ) ^ 2 * (N : ℝ) / 2 + (R : ℝ) * ((R : ℝ) - (margin d : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hup' hR0,
        mul_le_mul_of_nonneg_left hdiam (mul_nonneg hm0 hNpos.le), hD0, hRm.le]
    -- divide back through by `N·(R−m) > 0`
    rw [← sub_nonneg]
    have key : dist (embT d N x) (embT d N y)
          + ((margin d : ℝ) ^ 2 / (2 * ((R : ℝ) - (margin d : ℝ))) + (R : ℝ) / (N : ℝ))
          - ((R : ℝ) / (N : ℝ)) * ((torusGraphD d N R).dist x y : ℝ)
        = ((N : ℝ) * dist (embT d N x) (embT d N y) * ((R : ℝ) - (margin d : ℝ))
            + (margin d : ℝ) ^ 2 * (N : ℝ) / 2 + (R : ℝ) * ((R : ℝ) - (margin d : ℝ))
            - (R : ℝ) * (((torusGraphD d N R).dist x y : ℝ)
                * ((R : ℝ) - (margin d : ℝ))))
          / ((N : ℝ) * ((R : ℝ) - (margin d : ℝ))) := by
      have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
      have hRmne : ((R : ℝ) - (margin d : ℝ)) ≠ 0 := hRm.ne'
      field_simp
      ring
    rw [key]
    exact div_nonneg (sub_nonneg.mpr hpoly) (mul_nonneg hNpos.le hRm.le)

/-! ## The distortion error of the microscopic-stencil schedule `R_N = √N` -/

/-- **The torus distortion error** of the microscopic-stencil schedule `R_N = Nat.sqrt N` in
dimension `d`: `m²/(2(√N − m)) + √N/N` with `m = margin d`.  For each FIXED `d`, both summands
vanish as `N → ∞`. -/
noncomputable def torusDistortionError (d N : ℕ) : ℝ :=
  (margin d : ℝ) ^ 2 / (2 * ((Nat.sqrt N : ℝ) - (margin d : ℝ)))
    + (Nat.sqrt N : ℝ) / (N : ℝ)

/-- **The uniform torus distortion bound.**  For `N ≥ (margin d + 1)²` (so
`Nat.sqrt N ≥ margin d + 1`) the scaled hop metric of the `R_N = Nat.sqrt N` cyclic stencil
deviates from the flat-torus distance by at most `torusDistortionError d N`, UNIFORMLY in the
lattice pair `x y`. -/
theorem torusD_dist_sub_le [NeZero N] (hN : (margin d + 1) ^ 2 ≤ N)
    (x y : Fin d → ZMod N) :
    |((Nat.sqrt N : ℝ) / (N : ℝ)) * ((torusGraphD d N (Nat.sqrt N)).dist x y : ℝ)
        - dist (embT d N x) (embT d N y)| ≤ torusDistortionError d N := by
  have hR : margin d + 1 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by rw [← pow_two]; exact hN)
  have hN1 : 1 ≤ N :=
    le_trans (Nat.one_le_pow 2 (margin d + 1) (by omega)) hN
  obtain ⟨hlo, hhi⟩ := torusD_dist_pinch hR hN1 x y
  have hnn : 0 ≤ ((Nat.sqrt N : ℝ) / (N : ℝ))
      * ((torusGraphD d N (Nat.sqrt N)).dist x y : ℝ)
      - dist (embT d N x) (embT d N y) := by linarith
  rw [abs_of_nonneg hnn]
  unfold torusDistortionError
  linarith

/-- **The torus distortion error vanishes for every fixed dimension**:
`torusDistortionError d N → 0` as `N → ∞`.  `m²/(2(√N−m)) → 0` since `√N → ∞` and `m` is a
constant, and `√N/N ≤ 1/√(N:ℝ) → 0` by squeeze. -/
theorem torusDistortionError_tendsto_zero (d : ℕ) :
    Tendsto (torusDistortionError d) atTop (𝓝 0) := by
  -- the cast natural square root tends to infinity
  have hs : Tendsto (fun N : ℕ => ((Nat.sqrt N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp QIQTH.StencilDistortion.tendsto_natSqrt_atTop
  -- first summand: m²/(2(√N − m)) → 0
  have h1 : Tendsto (fun N : ℕ =>
      (margin d : ℝ) ^ 2 / (2 * ((Nat.sqrt N : ℝ) - (margin d : ℝ)))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ) - (margin d : ℝ)) atTop atTop := by
      apply Filter.tendsto_atTop_add_const_right
      exact hs
    have h3 : Tendsto (fun N : ℕ => 2 * ((Nat.sqrt N : ℝ) - (margin d : ℝ))) atTop atTop :=
      h2.const_mul_atTop two_pos
    have h4 : Tendsto
        (fun N : ℕ => (margin d : ℝ) ^ 2 * (2 * ((Nat.sqrt N : ℝ) - (margin d : ℝ)))⁻¹)
        atTop (𝓝 ((margin d : ℝ) ^ 2 * 0)) :=
      h3.inv_tendsto_atTop.const_mul ((margin d : ℝ) ^ 2)
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

/-! ## The T2 capstone -/

/-- **THE T2 THEOREM (uniform convergence of the scaled cyclic-stencil metric to the flat-torus
metric, every fixed dimension).**  With the microscopic-stencil schedule `R_N = Nat.sqrt N`,
for every fixed dimension `d` and every `ε > 0` there is an `N₀` such that for ALL `N ≥ N₀` and
ALL lattice pairs `x y` simultaneously, the scaled hop metric `(√N/N)·dist` is within `ε` of
the flat-torus distance.  (`N₀ ≥ (margin d + 1)² ≥ 1` is built into the proof, so `N` is
automatically nonzero.) -/
theorem torusD_scaled_metric_tendsto (d : ℕ) :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ x y : Fin d → ZMod N,
      |((Nat.sqrt N : ℝ) / (N : ℝ)) * ((torusGraphD d N (Nat.sqrt N)).dist x y : ℝ)
          - dist (embT d N x) (embT d N y)| < ε := by
  intro ε hε
  have hev : ∀ᶠ N : ℕ in atTop, torusDistortionError d N < ε :=
    (torusDistortionError_tendsto_zero d).eventually (gt_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp (hev.and (eventually_ge_atTop ((margin d + 1) ^ 2)))
  refine ⟨N₀, fun N hN x y => ?_⟩
  have hsq : (margin d + 1) ^ 2 ≤ N := (hN₀ N hN).2
  have h1 : 1 ≤ (margin d + 1) ^ 2 := Nat.one_le_pow 2 (margin d + 1) (by omega)
  haveI : NeZero N := ⟨Nat.one_le_iff_ne_zero.mp (le_trans h1 hsq)⟩
  exact lt_of_le_of_lt (torusD_dist_sub_le hsq x y) (hN₀ N hN).1

end QIQTH.TorusStencilWalk
