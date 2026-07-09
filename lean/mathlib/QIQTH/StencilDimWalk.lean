/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# DIMENSION-GENERIC STENCIL WALK — the d-dimensional rounding walk and the hop-metric upper
bound (brick G2, the crux)

Second brick of the DIMENSION-GENERIC STENCIL campaign
(`docs/qg_roadmap/DIM_GENERIC_STENCIL_PLAN.md`), generalizing the proven 2D construction of
`QIQTH/StencilWalk.lean` (brick I2) to the d-dimensional cube `Fin d → Fin (N+1)`.  For stencil
radius `R ≥ margin d + 1` (where `margin d = ⌊√d⌋ + 1`, from brick G1) we construct, between
ANY two lattice points `x y`, an EXPLICIT walk in `stencilGraphD d N R` of length at most
`⌈euclD x y / (R − margin d)⌉₊`: chop the straight segment from `x` to `y` into
`k = ⌈euclD x y / (R − margin d)⌉₊` equal pieces and round each real waypoint to the nearest
lattice point, coordinate by coordinate.

## The d-dimensional closing estimate (the only genuinely new mathematics vs 2D)

Write `m = margin d`.  Consecutive real waypoints differ per coordinate by `Δreal_c` with
`Σ_c (Δreal_c)² = (euclD/k)² ≤ (R − m)²`.  Rounding moves each real coordinate by at most
`1/2`, so each rounded step obeys `(Δround_c)² ≤ (Δreal_c)² + 2·|Δreal_c| + 1`, and summing
over the `d` coordinates:

    Σ (Δround_c)² ≤ Σ (Δreal_c)² + 2·Σ|Δreal_c| + d.

Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) gives `(Σ|Δreal_c|)² ≤ d·Σ(Δreal_c)²
≤ d·(R−m)² ≤ m²·(R−m)² = (m·(R−m))²` — using `√d ≤ m`, i.e. `d < m²` (`lt_margin_sq`) — so
`Σ|Δreal_c| ≤ m·(R − m)`.  Hence

    Σ (Δround_c)² ≤ (R − m)² + 2·m·(R − m) + m² = R²,

so consecutive rounded waypoints are equal or stencil-adjacent: the adjacency test is
`sqDistD ≤ R²`, and plain `≤ R²` suffices (the 2D brick proved a strict `< R²`; here `≤` is
enough and cleaner).  The check stays a *sqrt-free integer* inequality throughout.

## The G2 theorems

* `stencilD_walk_exists` — the explicit walk, `length ≤ ⌈euclD x y / (R − margin d)⌉₊`;
* `stencilD_reachable` — connectivity of the d-dimensional stencil graph (discharges brick
  G1's `Reachable` hypothesis, so `euclD_le_R_mul_dist` now fires unconditionally for
  `R ≥ margin d + 1`);
* `stencilD_dist_le` — the Euclidean UPPER bound on the hop metric:
  `dist x y ≤ euclD x y / (R − margin d) + 1`.

Together with G1's lower bound, the hop metric is now PINCHED between two Euclidean multiples:
`euclD x y ≤ R · dist x y`  AND  `dist x y ≤ euclD x y / (R − margin d) + 1`.

## Scope firewall (HONEST)

This is finite lattice combinatorics: an explicit rounding construction plus integer
inequalities.  The dimension `d` is an INPUT — the chosen lattice — NOT emergent: nothing here
says why physical space is 3-dimensional.  Isotropy is inserted by hand through the stencil
rule (the Euclidean-ball edge test), NOT emergent from a fixed local rule nor from dynamics.
This is NOT a continuum limit, NOT GR, NOT a numerical `G`, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.StencilDimGraph
import QIQTH.StencilWalk
import Mathlib.Algebra.Order.Chebyshev

namespace QIQTH.StencilDimWalk

open QIQTH.StencilDimGraph QIQTH.StencilWalk

variable {d N R : ℕ}

/-! ## Per-coordinate rounding cost (restated from the 2D brick, where these are private) -/

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

/-! ## THE d-DIMENSIONAL CLOSING ESTIMATE (the crux) -/

/-- **One rounded step, all `d` coordinates.**  If the real step has squared Euclidean length
at most `(RR − m)²` with `0 ≤ m ≤ RR` and `d ≤ m²`, the rounded step has squared length at most
`RR²`: per-coordinate rounding costs sum to `Σ(Δreal)² + 2·Σ|Δreal| + d`, Cauchy–Schwarz bounds
`Σ|Δreal| ≤ √d·(RR−m) ≤ m·(RR−m)`, and `(RR−m)² + 2m(RR−m) + m² = RR²`. -/
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

/-! ## Integer waypoints on the d-dimensional lattice -/

/-- The `j`-th integer waypoint from `x` to `y`: round each coordinate of the real waypoint to
the nearest integer, clamped into `[0, N]` (the clamp is vacuous for `j ≤ k`, see
`wayPtD_coe`). -/
noncomputable def wayPtD (x y : Fin d → Fin (N + 1)) (k j : ℕ) : Fin d → Fin (N + 1) :=
  fun c => ⟨min (round (seg (x c : ℝ) (y c : ℝ) k j)).toNat N,
    Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The rounded waypoint stays in `[0, N]` as an integer (restated from the 2D brick). -/
private lemma round_seg_mem {p q : ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hpN : p ≤ (N : ℝ)) (hqN : q ≤ (N : ℝ)) {k i : ℕ} (hik : i ≤ k) :
    0 ≤ round (seg p q k i) ∧ round (seg p q k i) ≤ (N : ℤ) := by
  obtain ⟨hlo, hhi⟩ := seg_bounds hik hp0 hq0 hpN hqN
  have hr := abs_le.mp (abs_sub_round (seg p q k i))
  constructor
  · have h1 : (-1 : ℝ) < ((round (seg p q k i) : ℤ) : ℝ) := by linarith [hr.2]
    have h2 : (-1 : ℤ) < round (seg p q k i) := by exact_mod_cast h1
    omega
  · have h1 : ((round (seg p q k i) : ℤ) : ℝ) < (N : ℝ) + 1 := by linarith [hr.1]
    have h2 : round (seg p q k i) < (N : ℤ) + 1 := by exact_mod_cast h1
    omega

/-- **Clamp irrelevance.**  For `j ≤ k` the real segment coordinate lies in `[0, N]` (convexity
of the box, per coordinate), so the clamp in `wayPtD` is vacuous and the lattice coordinate
cast to `ℤ` is exactly the rounded real waypoint. -/
theorem wayPtD_coe (x y : Fin d → Fin (N + 1)) {k j : ℕ} (hjk : j ≤ k) (c : Fin d) :
    ((wayPtD x y k j c : ℕ) : ℤ) = round (seg (x c : ℝ) (y c : ℝ) k j) := by
  obtain ⟨h0, hN⟩ := round_seg_mem (p := (x c : ℝ)) (q := (y c : ℝ)) (by positivity)
    (by positivity) (by exact_mod_cast Nat.lt_succ_iff.mp (x c).isLt)
    (by exact_mod_cast Nat.lt_succ_iff.mp (y c).isLt) hjk
  show ((min (round (seg (x c : ℝ) (y c : ℝ) k j)).toNat N : ℕ) : ℤ)
      = round (seg (x c : ℝ) (y c : ℝ) k j)
  omega

/-- The chain starts at `x`. -/
theorem wayPtD_zero (x y : Fin d → Fin (N + 1)) (k : ℕ) : wayPtD x y k 0 = x := by
  funext c
  have hle := Nat.lt_succ_iff.mp (x c).isLt
  apply Fin.ext
  show min (round (seg (x c : ℝ) (y c : ℝ) k 0)).toNat N = (x c : ℕ)
  rw [seg_zero, round_natCast]
  omega

/-- The chain ends at `y` (for `k ≠ 0`): the segment endpoint is already a lattice point, so
rounding is exact. -/
theorem wayPtD_last (x y : Fin d → Fin (N + 1)) {k : ℕ} (hk : k ≠ 0) :
    wayPtD x y k k = y := by
  funext c
  have hle := Nat.lt_succ_iff.mp (y c).isLt
  apply Fin.ext
  show min (round (seg (x c : ℝ) (y c : ℝ) k k)).toNat N = (y c : ℕ)
  rw [seg_last _ _ hk, round_natCast]
  omega

/-! ## The adjacency step -/

/-- **THE G2 ADJACENCY STEP.**  For `R ≥ margin d + 1` and chunk count
`k ≥ euclD x y / (R − margin d)`, consecutive rounded waypoints are equal or
stencil-adjacent — via the d-dimensional closing estimate
`Σ(Δround)² ≤ (R−m)² + 2m(R−m) + m² = R²`. -/
theorem wayPtD_step (hR : margin d + 1 ≤ R) {x y : Fin d → Fin (N + 1)} {k : ℕ}
    (hk : k ≠ 0) (hDk : euclD d N x y ≤ (k : ℝ) * ((R : ℝ) - (margin d : ℝ)))
    {j : ℕ} (hj : j < k) :
    wayPtD x y k j = wayPtD x y k (j + 1) ∨
      (stencilGraphD d N R).Adj (wayPtD x y k j) (wayPtD x y k (j + 1)) := by
  by_cases heq : wayPtD x y k j = wayPtD x y k (j + 1)
  · exact Or.inl heq
  · right
    refine ⟨heq, ?_⟩
    have hRm : ((margin d : ℕ) : ℝ) + 1 ≤ (R : ℝ) := by exact_mod_cast hR
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    -- the real step has squared length (euclD/k)² ≤ (R − m)²
    have hD2 : euclD d N x y ^ 2 = ∑ c, (((x c : ℕ) : ℝ) - ((y c : ℕ) : ℝ)) ^ 2 := by
      rw [euclD_eq_sqrt, Real.sq_sqrt (by positivity)]
    have hs1 : ∑ c, (seg (x c : ℝ) (y c : ℝ) k j - seg (x c : ℝ) (y c : ℝ) k (j + 1)) ^ 2
        = euclD d N x y ^ 2 / (k : ℝ) ^ 2 := by
      rw [hD2, Finset.sum_div]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [seg_step _ _ hk j]
      ring
    have hsum : ∑ c, (seg (x c : ℝ) (y c : ℝ) k j - seg (x c : ℝ) (y c : ℝ) k (j + 1)) ^ 2
        ≤ ((R : ℝ) - (margin d : ℝ)) ^ 2 := by
      rw [hs1, div_le_iff₀ (pow_pos hkR 2)]
      nlinarith [hDk, euclD_nonneg d N x y]
    -- the d-dimensional closing estimate
    have hm0 : (0 : ℝ) ≤ (margin d : ℝ) := Nat.cast_nonneg _
    have hmle : ((margin d : ℕ) : ℝ) ≤ (R : ℝ) := by linarith
    have hd_le : (d : ℝ) ≤ ((margin d : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast (lt_margin_sq d).le
    have hclose := round_diff_sq_sum_le hm0 hmle hd_le hsum
    -- cast the integer adjacency test through the bridge
    have hzsum : sqDistD d N (wayPtD x y k j) (wayPtD x y k (j + 1))
        = ∑ c, (round (seg (x c : ℝ) (y c : ℝ) k j)
            - round (seg (x c : ℝ) (y c : ℝ) k (j + 1))) ^ 2 := by
      unfold QIQTH.StencilDimGraph.sqDistD
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [wayPtD_coe x y (Nat.le_of_lt hj) c, wayPtD_coe x y hj c]
    have hfin : ((sqDistD d N (wayPtD x y k j) (wayPtD x y k (j + 1)) : ℤ) : ℝ)
        ≤ (R : ℝ) ^ 2 := by
      rw [hzsum]
      push_cast
      exact hclose
    exact_mod_cast hfin

/-! ## The G2 theorems -/

/-- **THE G2 WALK (explicit construction).**  For stencil radius `R ≥ margin d + 1` and any two
lattice points of the d-cube, the rounded-segment chain is a walk in `stencilGraphD d N R` of
length at most `⌈euclD x y / (R − margin d)⌉₊`. -/
theorem stencilD_walk_exists (hR : margin d + 1 ≤ R) (x y : Fin d → Fin (N + 1)) :
    ∃ w : (stencilGraphD d N R).Walk x y,
      w.length ≤ ⌈euclD d N x y / ((R : ℝ) - (margin d : ℝ))⌉₊ := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨SimpleGraph.Walk.nil, Nat.zero_le _⟩
  · have hRm : ((margin d : ℕ) : ℝ) + 1 ≤ (R : ℝ) := by exact_mod_cast hR
    have hRmpos : (0 : ℝ) < (R : ℝ) - (margin d : ℝ) := by linarith
    -- distinct lattice points are a positive Euclidean distance apart
    have hDpos : 0 < euclD d N x y := by
      rw [euclD_eq_sqrt]
      apply Real.sqrt_pos.mpr
      obtain ⟨c, hc⟩ : ∃ c, x c ≠ y c := Function.ne_iff.mp hxy
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨c, Finset.mem_univ c, ?_⟩
      have hv : (x c : ℕ) ≠ (y c : ℕ) := fun h => hc (Fin.ext h)
      have hr : ((x c : ℕ) : ℝ) ≠ ((y c : ℕ) : ℝ) := by exact_mod_cast hv
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hr)))
    set k := ⌈euclD d N x y / ((R : ℝ) - (margin d : ℝ))⌉₊ with hkdef
    have hkpos : 0 < k := Nat.ceil_pos.mpr (div_pos hDpos hRmpos)
    have hk0 : k ≠ 0 := hkpos.ne'
    have hDk : euclD d N x y ≤ (k : ℝ) * ((R : ℝ) - (margin d : ℝ)) := by
      have hle := Nat.le_ceil (euclD d N x y / ((R : ℝ) - (margin d : ℝ)))
      rw [← hkdef] at hle
      have h := mul_le_mul_of_nonneg_right hle hRmpos.le
      rwa [div_mul_cancel₀ _ hRmpos.ne'] at h
    -- each consecutive pair of integer waypoints is equal or stencil-adjacent
    have hstep : ∀ i, i < k → wayPtD x y k i = wayPtD x y k (i + 1) ∨
        (stencilGraphD d N R).Adj (wayPtD x y k i) (wayPtD x y k (i + 1)) :=
      fun i hik => wayPtD_step hR hk0 hDk hik
    obtain ⟨w, hw⟩ := walk_of_lazy_chain (fun i => wayPtD x y k i) k hstep
    refine ⟨w.copy (wayPtD_zero x y k) (wayPtD_last x y hk0), ?_⟩
    rw [SimpleGraph.Walk.length_copy]
    exact hw

/-- **Connectivity of the d-dimensional stencil graph** for `R ≥ margin d + 1` — discharges the
`Reachable` hypothesis of brick G1's `euclD_le_R_mul_dist`. -/
theorem stencilD_reachable (hR : margin d + 1 ≤ R) (x y : Fin d → Fin (N + 1)) :
    (stencilGraphD d N R).Reachable x y := by
  obtain ⟨w, -⟩ := stencilD_walk_exists hR x y
  exact w.reachable

/-- **THE G2 THEOREM (Euclidean upper bound on the hop metric).**  For `R ≥ margin d + 1`,
`dist x y ≤ euclD x y / (R − margin d) + 1` — the two-sided companion to G1's
`euclD x y ≤ R · dist x y`: the hop metric is pinched between two Euclidean multiples. -/
theorem stencilD_dist_le (hR : margin d + 1 ≤ R) (x y : Fin d → Fin (N + 1)) :
    (((stencilGraphD d N R).dist x y : ℕ) : ℝ)
      ≤ euclD d N x y / ((R : ℝ) - (margin d : ℝ)) + 1 := by
  obtain ⟨w, hw⟩ := stencilD_walk_exists hR x y
  have hd : (stencilGraphD d N R).dist x y
      ≤ ⌈euclD d N x y / ((R : ℝ) - (margin d : ℝ))⌉₊ :=
    le_trans (SimpleGraph.dist_le w) hw
  have hRm : ((margin d : ℕ) : ℝ) + 1 ≤ (R : ℝ) := by exact_mod_cast hR
  have hnn : 0 ≤ euclD d N x y / ((R : ℝ) - (margin d : ℝ)) :=
    div_nonneg (euclD_nonneg d N x y) (by linarith)
  have hceil : (⌈euclD d N x y / ((R : ℝ) - (margin d : ℝ))⌉₊ : ℝ)
      < euclD d N x y / ((R : ℝ) - (margin d : ℝ)) + 1 :=
    Nat.ceil_lt_add_one hnn
  have hcast : (((stencilGraphD d N R).dist x y : ℕ) : ℝ)
      ≤ (⌈euclD d N x y / ((R : ℝ) - (margin d : ℝ))⌉₊ : ℝ) := by exact_mod_cast hd
  linarith

end QIQTH.StencilDimWalk
