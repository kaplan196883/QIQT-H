/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# STENCIL WALK — explicit lattice walks and the Euclidean UPPER bound (brick I2)

Second brick of the ISOTROPY campaign (`docs/qg_roadmap/ISOTROPY_STENCIL_PLAN.md`), the crux.
For stencil radius `R ≥ 3` we construct, between ANY two lattice points `x y` of
`Fin (N+1) × Fin (N+1)`, an EXPLICIT walk in `stencilGraph N R` of length at most
`⌈eucl N x y / (R − 2)⌉₊`: chop the straight segment from `x` to `y` into
`k = ⌈eucl x y / (R−2)⌉₊` equal pieces and round each real waypoint to the nearest lattice
point.  Each rounded step has integer squared displacement at most
`(R−2)² + 4(R−2) + 2 = R² − 2 < R²`, so consecutive waypoints are equal or stencil-adjacent —
the adjacency check stays a *sqrt-free integer* inequality throughout.

## The I2 theorems

* `stencil_walk_exists` — the explicit walk, `length ≤ ⌈eucl x y / (R−2)⌉₊`;
* `stencil_reachable` — connectivity of the stencil graph (discharges brick I1's `Reachable`
  hypothesis, so `eucl_le_R_mul_dist` now fires unconditionally for `R ≥ 3`);
* `stencil_dist_le` — the matching Euclidean UPPER bound on the hop metric:
  `dist x y ≤ eucl x y / (R−2) + 1`.

Together with I1's lower bound `eucl x y ≤ R · dist x y`, the hop metric is now pinched
between two Euclidean multiples — the finite two-sided comparability that the isotropy
campaign builds on.

## Scope firewall (HONEST)

This is finite lattice combinatorics: an explicit rounding construction plus integer
inequalities.  It is NOT isotropy, NOT a continuum limit, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.StencilGraph
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace QIQTH.StencilWalk

open QIQTH.StencilGraph

/-! ## A lazy chain of adjacent-or-equal vertices yields a walk (generic helper) -/

/-- **Lazy chain → walk.**  If `f 0, f 1, …, f k` is a chain in which each consecutive pair is
either equal or adjacent, there is a walk from `f 0` to `f k` of length at most `k`.  (Equal
steps are skipped via `Walk.copy`, adjacent steps appended via `Walk.concat`.) -/
lemma walk_of_lazy_chain {V : Type*} {G : SimpleGraph V} (f : ℕ → V) :
    ∀ k : ℕ, (∀ i, i < k → f i = f (i + 1) ∨ G.Adj (f i) (f (i + 1))) →
      ∃ w : G.Walk (f 0) (f k), w.length ≤ k := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨SimpleGraph.Walk.nil, Nat.zero_le _⟩
  | succ k ih =>
      intro hstep
      obtain ⟨w, hw⟩ := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
      rcases hstep k (Nat.lt_succ_self k) with heq | hadj
      · exact ⟨w.copy rfl heq, by rw [SimpleGraph.Walk.length_copy]; omega⟩
      · exact ⟨w.concat hadj, by rw [SimpleGraph.Walk.length_concat]; omega⟩

/-! ## Real waypoints along a segment -/

/-- The `i`-th of `k` equally spaced real waypoints from `p` to `q`:
`seg p q k i = p + (i/k)·(q − p)`. -/
noncomputable def seg (p q : ℝ) (k i : ℕ) : ℝ := p + (i : ℝ) / (k : ℝ) * (q - p)

lemma seg_zero (p q : ℝ) (k : ℕ) : seg p q k 0 = p := by
  unfold seg; simp

lemma seg_last (p q : ℝ) {k : ℕ} (hk : k ≠ 0) : seg p q k k = q := by
  have hkR : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  unfold seg
  rw [div_self hkR]
  ring

/-- Waypoints stay in any interval containing both endpoints. -/
lemma seg_bounds {p q : ℝ} {k i : ℕ} (hik : i ≤ k) {lo hi : ℝ}
    (hp : lo ≤ p) (hq : lo ≤ q) (hp' : p ≤ hi) (hq' : q ≤ hi) :
    lo ≤ seg p q k i ∧ seg p q k i ≤ hi := by
  have ht0 : 0 ≤ (i : ℝ) / (k : ℝ) := by positivity
  have ht1 : (i : ℝ) / (k : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hi0 : i = 0 := Nat.le_zero.mp hik
      subst hi0
      simp
    · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hiR : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
      by_contra hcon
      push Not at hcon
      have h2 := mul_lt_mul_of_pos_right hcon hkR
      rw [one_mul, div_mul_cancel₀ _ hkR.ne'] at h2
      linarith
  unfold seg
  constructor
  · linarith [mul_nonneg ht0 (sub_nonneg.mpr hq),
      mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hp)]
  · linarith [mul_nonneg ht0 (sub_nonneg.mpr hq'),
      mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hp')]

/-- Consecutive waypoints differ by exactly `−(q−p)/k`. -/
lemma seg_step (p q : ℝ) {k : ℕ} (hk : k ≠ 0) (i : ℕ) :
    seg p q k i - seg p q k (i + 1) = -((q - p) / (k : ℝ)) := by
  have hkR : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  unfold seg
  push_cast
  field_simp
  ring

/-! ## Rounding waypoints: the numeric core (sqrt-free) -/

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

/-- **One rounded step, both coordinates (THE stencil estimate).**  If the real step has squared
Euclidean length at most `(RR−2)²` with `RR ≥ 3`, the rounded step has squared length strictly
below `RR²`:  `(RR−2)² + 4(RR−2) + 2 = RR² − 2 < RR²`. -/
private lemma round_diff_sq_lt {s1 s1' s2 s2' RR : ℝ} (hRR : 3 ≤ RR)
    (hsum : (s1 - s1') ^ 2 + (s2 - s2') ^ 2 ≤ (RR - 2) ^ 2) :
    (((round s1 : ℤ) : ℝ) - ((round s1' : ℤ) : ℝ)) ^ 2
      + (((round s2 : ℤ) : ℝ) - ((round s2' : ℤ) : ℝ)) ^ 2 < RR ^ 2 := by
  have hR2 : (0 : ℝ) ≤ RR - 2 := by linarith
  have ha2 : (s1 - s1') ^ 2 ≤ (RR - 2) ^ 2 := by linarith [sq_nonneg (s2 - s2')]
  have hb2 : (s2 - s2') ^ 2 ≤ (RR - 2) ^ 2 := by linarith [sq_nonneg (s1 - s1')]
  have ha : |s1 - s1'| ≤ RR - 2 := abs_le_of_sq_le_sq ha2 hR2
  have hb : |s2 - s2'| ≤ RR - 2 := abs_le_of_sq_le_sq hb2 hR2
  have h1 := round_diff_sq_le ha
  have h2 := round_diff_sq_le hb
  nlinarith [hsum, hRR, h1, h2]

/-! ## Integer waypoints on the lattice -/

variable {N R : ℕ}

/-- The `i`-th integer waypoint from `x` to `y`: round each coordinate of the real waypoint to
the nearest integer, clamped into `[0, N]` (the clamp is vacuous for `i ≤ k`, see
`wayPt_coe_fst`). -/
private noncomputable def wayPt (x y : Fin (N + 1) × Fin (N + 1)) (k i : ℕ) :
    Fin (N + 1) × Fin (N + 1) :=
  (⟨min (round (seg (x.1 : ℝ) (y.1 : ℝ) k i)).toNat N, Nat.lt_succ_of_le (min_le_right _ _)⟩,
   ⟨min (round (seg (x.2 : ℝ) (y.2 : ℝ) k i)).toNat N, Nat.lt_succ_of_le (min_le_right _ _)⟩)

/-- The rounded waypoint stays in `[0, N]` as an integer. -/
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

/-- Bridge, first coordinate: for `i ≤ k` the clamp in `wayPt` is vacuous, and the lattice
coordinate cast to `ℤ` is exactly the rounded real waypoint. -/
private lemma wayPt_coe_fst (x y : Fin (N + 1) × Fin (N + 1)) {k i : ℕ} (hik : i ≤ k) :
    (((wayPt x y k i).1 : Fin (N + 1)) : ℤ) = round (seg (x.1 : ℝ) (y.1 : ℝ) k i) := by
  obtain ⟨h0, hN⟩ := round_seg_mem (p := (x.1 : ℝ)) (q := (y.1 : ℝ)) (by positivity)
    (by positivity) (by exact_mod_cast Nat.lt_succ_iff.mp x.1.isLt)
    (by exact_mod_cast Nat.lt_succ_iff.mp y.1.isLt) hik
  show ((min (round (seg (x.1 : ℝ) (y.1 : ℝ) k i)).toNat N : ℕ) : ℤ)
      = round (seg (x.1 : ℝ) (y.1 : ℝ) k i)
  omega

/-- Bridge, second coordinate. -/
private lemma wayPt_coe_snd (x y : Fin (N + 1) × Fin (N + 1)) {k i : ℕ} (hik : i ≤ k) :
    (((wayPt x y k i).2 : Fin (N + 1)) : ℤ) = round (seg (x.2 : ℝ) (y.2 : ℝ) k i) := by
  obtain ⟨h0, hN⟩ := round_seg_mem (p := (x.2 : ℝ)) (q := (y.2 : ℝ)) (by positivity)
    (by positivity) (by exact_mod_cast Nat.lt_succ_iff.mp x.2.isLt)
    (by exact_mod_cast Nat.lt_succ_iff.mp y.2.isLt) hik
  show ((min (round (seg (x.2 : ℝ) (y.2 : ℝ) k i)).toNat N : ℕ) : ℤ)
      = round (seg (x.2 : ℝ) (y.2 : ℝ) k i)
  omega

/-- The chain starts at `x`. -/
private lemma wayPt_zero (x y : Fin (N + 1) × Fin (N + 1)) (k : ℕ) : wayPt x y k 0 = x := by
  have h1 : min (round (seg (x.1 : ℝ) (y.1 : ℝ) k 0)).toNat N = (x.1 : ℕ) := by
    have hle := Nat.lt_succ_iff.mp x.1.isLt
    rw [seg_zero, round_natCast]
    omega
  have h2 : min (round (seg (x.2 : ℝ) (y.2 : ℝ) k 0)).toNat N = (x.2 : ℕ) := by
    have hle := Nat.lt_succ_iff.mp x.2.isLt
    rw [seg_zero, round_natCast]
    omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- The chain ends at `y` (for `k ≠ 0`). -/
private lemma wayPt_last (x y : Fin (N + 1) × Fin (N + 1)) {k : ℕ} (hk : k ≠ 0) :
    wayPt x y k k = y := by
  have h1 : min (round (seg (x.1 : ℝ) (y.1 : ℝ) k k)).toNat N = (y.1 : ℕ) := by
    have hle := Nat.lt_succ_iff.mp y.1.isLt
    rw [seg_last _ _ hk, round_natCast]
    omega
  have h2 : min (round (seg (x.2 : ℝ) (y.2 : ℝ) k k)).toNat N = (y.2 : ℕ) := by
    have hle := Nat.lt_succ_iff.mp y.2.isLt
    rw [seg_last _ _ hk, round_natCast]
    omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-! ## The I2 theorems -/

/-- **THE I2 WALK (explicit construction).**  For stencil radius `R ≥ 3` and any two lattice
points, the rounded-segment chain is a walk in `stencilGraph N R` of length at most
`⌈eucl x y / (R − 2)⌉₊`. -/
theorem stencil_walk_exists (hR : 3 ≤ R) (x y : Fin (N + 1) × Fin (N + 1)) :
    ∃ w : (stencilGraph N R).Walk x y, w.length ≤ ⌈eucl N x y / ((R : ℝ) - 2)⌉₊ := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨SimpleGraph.Walk.nil, Nat.zero_le _⟩
  · have hR3 : (3 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hR2 : (0 : ℝ) < (R : ℝ) - 2 := by linarith
    -- distinct lattice points are a positive Euclidean distance apart
    have hDpos : 0 < eucl N x y := by
      rw [eucl_eq_sqrt]
      apply Real.sqrt_pos.mpr
      have hne : x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
        by_contra hcon
        push Not at hcon
        exact hxy (Prod.ext hcon.1 hcon.2)
      have key : ∀ a b : Fin (N + 1), a ≠ b → 0 < ((a : ℝ) - (b : ℝ)) ^ 2 := by
        intro a b hab
        have hv : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
        have hr : ((a : ℕ) : ℝ) ≠ ((b : ℕ) : ℝ) := by exact_mod_cast hv
        exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hr)))
      rcases hne with h | h
      · linarith [key _ _ h, sq_nonneg ((x.2 : ℝ) - (y.2 : ℝ))]
      · linarith [key _ _ h, sq_nonneg ((x.1 : ℝ) - (y.1 : ℝ))]
    set k := ⌈eucl N x y / ((R : ℝ) - 2)⌉₊ with hkdef
    have hkpos : 0 < k := Nat.ceil_pos.mpr (div_pos hDpos hR2)
    have hk0 : k ≠ 0 := hkpos.ne'
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    have hD2 : (eucl N x y) ^ 2 = ((x.1 : ℝ) - (y.1 : ℝ)) ^ 2 + ((x.2 : ℝ) - (y.2 : ℝ)) ^ 2 := by
      rw [eucl_eq_sqrt, Real.sq_sqrt (by positivity)]
    have hDk : eucl N x y ≤ (k : ℝ) * ((R : ℝ) - 2) := by
      have hle := Nat.le_ceil (eucl N x y / ((R : ℝ) - 2))
      rw [← hkdef] at hle
      have h := mul_le_mul_of_nonneg_right hle hR2.le
      rwa [div_mul_cancel₀ _ hR2.ne'] at h
    -- each consecutive pair of integer waypoints is equal or stencil-adjacent
    have hstep : ∀ i, i < k → wayPt x y k i = wayPt x y k (i + 1) ∨
        (stencilGraph N R).Adj (wayPt x y k i) (wayPt x y k (i + 1)) := by
      intro i hik
      have hik' : i + 1 ≤ k := hik
      by_cases heq : wayPt x y k i = wayPt x y k (i + 1)
      · exact Or.inl heq
      right
      refine ⟨heq, ?_⟩
      -- the real step has squared length D²/k² ≤ (R−2)²
      have hsum : (seg (x.1 : ℝ) (y.1 : ℝ) k i - seg (x.1 : ℝ) (y.1 : ℝ) k (i + 1)) ^ 2
          + (seg (x.2 : ℝ) (y.2 : ℝ) k i - seg (x.2 : ℝ) (y.2 : ℝ) k (i + 1)) ^ 2
          ≤ ((R : ℝ) - 2) ^ 2 := by
        rw [seg_step _ _ hk0 i, seg_step _ _ hk0 i]
        have heq2 : (-(((y.1 : ℝ) - (x.1 : ℝ)) / (k : ℝ))) ^ 2
            + (-(((y.2 : ℝ) - (x.2 : ℝ)) / (k : ℝ))) ^ 2
            = (eucl N x y) ^ 2 / (k : ℝ) ^ 2 := by
          rw [hD2]
          field_simp
          ring
        rw [heq2]
        have hD2le : (eucl N x y) ^ 2 ≤ ((R : ℝ) - 2) ^ 2 * (k : ℝ) ^ 2 := by
          nlinarith [hDk, hDpos.le]
        have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
        have h := mul_le_mul_of_nonneg_right hD2le (inv_pos.mpr hk2).le
        rw [mul_assoc, mul_inv_cancel₀ hk2.ne', mul_one] at h
        rwa [div_eq_mul_inv]
      -- hence the rounded integer step passes the sqrt-free stencil test
      have hlt := round_diff_sq_lt hR3 hsum
      have hcast : ((sqDist N (wayPt x y k i) (wayPt x y k (i + 1)) : ℤ) : ℝ)
          = (((round (seg (x.1 : ℝ) (y.1 : ℝ) k i) : ℤ) : ℝ)
              - ((round (seg (x.1 : ℝ) (y.1 : ℝ) k (i + 1)) : ℤ) : ℝ)) ^ 2
            + (((round (seg (x.2 : ℝ) (y.2 : ℝ) k i) : ℤ) : ℝ)
              - ((round (seg (x.2 : ℝ) (y.2 : ℝ) k (i + 1)) : ℤ) : ℝ)) ^ 2 := by
        unfold QIQTH.StencilGraph.sqDist
        rw [wayPt_coe_fst x y hik.le, wayPt_coe_fst x y hik', wayPt_coe_snd x y hik.le,
          wayPt_coe_snd x y hik']
        push_cast
        ring
      have hfin : ((sqDist N (wayPt x y k i) (wayPt x y k (i + 1)) : ℤ) : ℝ) < (R : ℝ) ^ 2 := by
        rw [hcast]; exact hlt
      have hZ : sqDist N (wayPt x y k i) (wayPt x y k (i + 1)) < (R : ℤ) ^ 2 := by
        exact_mod_cast hfin
      exact hZ.le
    obtain ⟨w, hw⟩ := walk_of_lazy_chain (fun i => wayPt x y k i) k hstep
    refine ⟨w.copy (wayPt_zero x y k) (wayPt_last x y hk0), ?_⟩
    rw [SimpleGraph.Walk.length_copy]
    exact hw

/-- **Connectivity of the stencil graph** for `R ≥ 3` — discharges the `Reachable` hypothesis of
brick I1's `eucl_le_R_mul_dist`. -/
theorem stencil_reachable (hR : 3 ≤ R) (x y : Fin (N + 1) × Fin (N + 1)) :
    (stencilGraph N R).Reachable x y := by
  obtain ⟨w, -⟩ := stencil_walk_exists hR x y
  exact w.reachable

/-- **THE I2 THEOREM (Euclidean upper bound on the hop metric).**  For `R ≥ 3`,
`dist x y ≤ eucl x y / (R − 2) + 1` — the two-sided companion to I1's
`eucl x y ≤ R · dist x y`. -/
theorem stencil_dist_le (hR : 3 ≤ R) (x y : Fin (N + 1) × Fin (N + 1)) :
    (((stencilGraph N R).dist x y : ℕ) : ℝ) ≤ eucl N x y / ((R : ℝ) - 2) + 1 := by
  obtain ⟨w, hw⟩ := stencil_walk_exists hR x y
  have hd : (stencilGraph N R).dist x y ≤ ⌈eucl N x y / ((R : ℝ) - 2)⌉₊ :=
    le_trans (SimpleGraph.dist_le w) hw
  have hR3 : (3 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have heucl0 : 0 ≤ eucl N x y := by
    rw [eucl_eq_sqrt]; exact Real.sqrt_nonneg _
  have hnn : 0 ≤ eucl N x y / ((R : ℝ) - 2) := div_nonneg heucl0 (by linarith)
  have hceil : (⌈eucl N x y / ((R : ℝ) - 2)⌉₊ : ℝ) < eucl N x y / ((R : ℝ) - 2) + 1 :=
    Nat.ceil_lt_add_one hnn
  have hcast : (((stencilGraph N R).dist x y : ℕ) : ℝ)
      ≤ (⌈eucl N x y / ((R : ℝ) - 2)⌉₊ : ℝ) := by exact_mod_cast hd
  linarith

end QIQTH.StencilWalk
