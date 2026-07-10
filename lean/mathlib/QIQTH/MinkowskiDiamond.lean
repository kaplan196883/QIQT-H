/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# THE MINKOWSKI DIAMOND AND THE CAUSAL NO-GO — the Lorentzian target and why
# deterministic hop-counting fails (bricks L1+L2, Lorentzian ladder)

## L1 — the flat target

Lorentzian geometry's fundamental object is not a distance but the **time-separation
function** `τ`, which satisfies the **REVERSE triangle inequality**: timelike geodesics
MAXIMIZE proper time (`τ(p,q) + τ(q,r) ≤ τ(p,r)` for causal `p ≼ q ≼ r`).  This file
builds the flat 1+1-dimensional Minkowski `τ` in **null coordinates** `(u, v)`, where the
causal order is the componentwise order and `τ = √(2·Δu·Δv)`.  The engine of the reverse
triangle inequality is the reverse Cauchy–Schwarz inequality
`HawkingWick.sqrt_mul_add_le : √(ab) + √(cd) ≤ √((a+c)(b+d))` — imported and used
exactly once (`tau_reverse_triangle`).  The **equality case** of that inequality forces
proportional gaps, which gives the flat half of the midpoint invariant: **flat timelike
midpoints are UNIQUE** (`tau_midpoint_unique`) — the invariant whose *violation* in the
presence of curvature is the L4 target of the ladder.

## L2 — THE CAUSAL NO-GO (the Lorentzian twin of `IsotropyNoGo`)

On the deterministic causal lattice `Fin (N+1) × Fin (N+1)` (the discrete diamond, product
order), the unweighted longest-chain functional does NOT measure proper time: every hop
strictly increases the **rank** `u + v` by at least 1 (`rank_increase`), so the longest
chain from `(0,0)` to `(N,N)` has length EXACTLY `2N` (upper bound `chain_length_le_corner`,
achieved by the `staircase`), and the scaled hop-time of the unit diamond is `2N/N = 2` —
the *Manhattan* time, the rank.  But the continuum answer is `τ((0,0),(1,1)) = √2`, and
`2 ≠ √2` (`causal_no_go`).  **Pure order-counting on a deterministic lattice CANNOT
recover Minkowski proper time.**  This is the machine-checked reason the causal-set
program needs RANDOM sprinkling — Bombelli–Lee–Meyer–Sorkin (Phys. Rev. Lett. 59, 1987)
posit Poisson sprinkling, and Brightwell–Gregory (Phys. Rev. Lett. 66, 1991) show the
longest chain in a *sprinkled* diamond does converge to proper time.  The deterministic
fix — the WEIGHTED causal stencil — is brick L3, not this file.

## Scope firewall (MANDATORY, HONEST)

* The causal order is **INSERTED** (the lattice/product order is an input, not emergent).
* Spacetime is **NOT a metric space** — `τ` is not a distance; there is NO
  Gromov–Hausdorff statement here; all convergence-flavored statements are extrinsic
  pinches of explicit functionals.
* Everything is **1+1-dimensional**; the diamond is an **INPUT** (a chosen region).
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.HawkingWick

noncomputable section

namespace QIQTH.MinkowskiDiamond

/-! ## Part 1 (L1) — the flat Minkowski time-separation in null coordinates -/

/-- **The causal order** on 1+1 Minkowski space in null coordinates `(u, v)`:
`p ≼ q` iff both null coordinates advance.  (In null coordinates the future light cone
is the positive quadrant.) -/
def causalLE (p q : ℝ × ℝ) : Prop := p.1 ≤ q.1 ∧ p.2 ≤ q.2

theorem causalLE_refl (p : ℝ × ℝ) : causalLE p p := ⟨le_refl _, le_refl _⟩

theorem causalLE_trans {p q r : ℝ × ℝ} (hpq : causalLE p q) (hqr : causalLE q r) :
    causalLE p r := ⟨le_trans hpq.1 hqr.1, le_trans hpq.2 hqr.2⟩

theorem causalLE_antisymm {p q : ℝ × ℝ} (hpq : causalLE p q) (hqp : causalLE q p) :
    p = q :=
  Prod.ext (le_antisymm hpq.1 hqp.1) (le_antisymm hpq.2 hqp.2)

open Classical in
/-- **The flat time-separation** `τ(p, q) = √(2·Δu·Δv)` for causal pairs, `0` otherwise —
the Lorentzian proper time between `p` and `q` in null coordinates (compare
`HawkingWick.null_coords_identity`: `2uv = t² − x²`). -/
noncomputable def tau (p q : ℝ × ℝ) : ℝ :=
  if causalLE p q then Real.sqrt (2 * (q.1 - p.1) * (q.2 - p.2)) else 0

theorem tau_of_causal {p q : ℝ × ℝ} (h : causalLE p q) :
    tau p q = Real.sqrt (2 * (q.1 - p.1) * (q.2 - p.2)) := by
  unfold tau
  exact if_pos h

theorem tau_of_not_causal {p q : ℝ × ℝ} (h : ¬ causalLE p q) : tau p q = 0 := by
  unfold tau
  exact if_neg h

/-- `τ ≥ 0` always (for causal pairs the radicand is `≥ 0` automatically; otherwise `τ = 0`). -/
theorem tau_nonneg (p q : ℝ × ℝ) : 0 ≤ tau p q := by
  unfold tau
  split
  · exact Real.sqrt_nonneg _
  · exact le_refl 0

theorem tau_self (p : ℝ × ℝ) : tau p p = 0 := by
  rw [tau_of_causal (causalLE_refl p)]
  simp

/-- **CHRONOLOGICAL ⟺ strictly timelike**: for a causal pair, `τ > 0` iff both null gaps
are strictly positive. -/
theorem tau_pos_iff {p q : ℝ × ℝ} (h : causalLE p q) :
    0 < tau p q ↔ p.1 < q.1 ∧ p.2 < q.2 := by
  rw [tau_of_causal h, Real.sqrt_pos]
  constructor
  · intro hx
    have h1 := sub_nonneg.mpr h.1
    have h2 := sub_nonneg.mpr h.2
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)]

/-- **The light cone**: if either null gap vanishes, `τ = 0` (null-separated or degenerate
pairs have zero proper time). -/
theorem tau_eq_zero_of_null {p q : ℝ × ℝ} (h : p.1 = q.1 ∨ p.2 = q.2) : tau p q = 0 := by
  unfold tau
  split
  · rcases h with h | h <;> simp [h]
  · rfl

/-- **THE REVERSE TRIANGLE INEQUALITY** — timelike geodesics MAXIMIZE proper time:
for causal `p ≼ q ≼ r`, `τ(p,q) + τ(q,r) ≤ τ(p,r)`.  The engine is the reverse
Cauchy–Schwarz inequality `HawkingWick.sqrt_mul_add_le` applied to
`√(2Δu·Δv) = √((2Δu)·Δv)` — the factor `2` distributes over the added `u`-gaps. -/
theorem tau_reverse_triangle {p q r : ℝ × ℝ} (hpq : causalLE p q) (hqr : causalLE q r) :
    tau p q + tau q r ≤ tau p r := by
  have hpr := causalLE_trans hpq hqr
  rw [tau_of_causal hpq, tau_of_causal hqr, tau_of_causal hpr]
  have ha : (0 : ℝ) ≤ 2 * (q.1 - p.1) := by
    have := sub_nonneg.mpr hpq.1; linarith
  have hb : (0 : ℝ) ≤ q.2 - p.2 := sub_nonneg.mpr hpq.2
  have hc : (0 : ℝ) ≤ 2 * (r.1 - q.1) := by
    have := sub_nonneg.mpr hqr.1; linarith
  have hd : (0 : ℝ) ≤ r.2 - q.2 := sub_nonneg.mpr hqr.2
  have key := QIQTH.HawkingWick.sqrt_mul_add_le (2 * (q.1 - p.1)) (q.2 - p.2)
    (2 * (r.1 - q.1)) (r.2 - q.2) ha hb hc hd
  have hrad : (2 * (q.1 - p.1) + 2 * (r.1 - q.1)) * ((q.2 - p.2) + (r.2 - q.2))
      = 2 * (r.1 - p.1) * (r.2 - p.2) := by ring
  rw [hrad] at key
  exact key

/-! ### Flat midpoint uniqueness — the equality case

The equality case of `sqrt_mul_add_le` (in squared, polynomial form): if the two halves
`√(2ab)` and `√(2a'b')` each equal HALF the total `√(2(a+a')(b+b'))`, then squaring gives
`4ab = (a+a')(b+b') = 4a'b'`, which forces `(a−a')(b−b') = 0` (the proportionality
`ab' = a'b` of the AM–GM equality case) and hence — since the products are strictly
positive — `a = a'` and `b = b'`: the gaps split exactly in half. -/

/-- **Equality-case extraction (squared form)**: nonnegative gaps `a, b` (first leg) and
`a', b'` (second leg) with strictly positive totals, such that BOTH squared leg-times equal
a quarter of the squared total (`4ab = (a+a')(b+b')` and `4a'b' = (a+a')(b+b')`), must
split each gap exactly in half. -/
theorem midpoint_gaps_eq {a b a' b' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (hu : 0 < a + a') (hv : 0 < b + b')
    (h1 : 4 * (a * b) = (a + a') * (b + b'))
    (h2 : 4 * (a' * b') = (a + a') * (b + b')) :
    a = (a + a') / 2 ∧ b = (b + b') / 2 := by
  have hEq : a * b = a' * b' := by linarith
  -- the AM–GM equality case, polynomially: (a−a')(b−b') = 0
  have hZero : (a - a') * (b - b') = 0 := by linear_combination h1 - 2 * hEq
  have hSpos : 0 < (a + a') * (b + b') := mul_pos hu hv
  have habpos : 0 < a * b := by linarith
  have ha'b'pos : 0 < a' * b' := by linarith
  have hapos : 0 < a := by nlinarith
  have hbpos : 0 < b := by nlinarith
  have ha'pos : 0 < a' := by nlinarith
  have hb'pos : 0 < b' := by nlinarith
  rcases mul_eq_zero.mp hZero with h | h
  · -- a = a', then cancel a in ab = a'b' to get b = b'
    have haa : a = a' := by linarith
    rw [haa] at hEq
    have hbb : b = b' := mul_left_cancel₀ (ne_of_gt ha'pos) hEq
    exact ⟨by linarith, by linarith⟩
  · -- b = b', then cancel b in ab = a'b' to get a = a'
    have hbb : b = b' := by linarith
    rw [hbb] at hEq
    have haa : a = a' := mul_right_cancel₀ (ne_of_gt hb'pos) hEq
    exact ⟨by linarith, by linarith⟩

/-- **Flat midpoints are determined**: for a CHRONOLOGICAL pair `p ≺ r` (both null gaps
strictly positive), any causal midpoint `m` (with `τ(p,m) = τ(m,r) = τ(p,r)/2`) sits at
the exact coordinate midpoint.  Proof: square the two midpoint equations
(`Real.sq_sqrt`), then `midpoint_gaps_eq`. -/
theorem tau_midpoint_coords {p r m : ℝ × ℝ}
    (h1 : p.1 < r.1) (h2 : p.2 < r.2)
    (hpm : causalLE p m) (hmr : causalLE m r)
    (hm1 : tau p m = tau p r / 2) (hm2 : tau m r = tau p r / 2) :
    m.1 = (p.1 + r.1) / 2 ∧ m.2 = (p.2 + r.2) / 2 := by
  have hpr : causalLE p r := causalLE_trans hpm hmr
  have ha : 0 ≤ m.1 - p.1 := sub_nonneg.mpr hpm.1
  have hb : 0 ≤ m.2 - p.2 := sub_nonneg.mpr hpm.2
  have ha' : 0 ≤ r.1 - m.1 := sub_nonneg.mpr hmr.1
  have hb' : 0 ≤ r.2 - m.2 := sub_nonneg.mpr hmr.2
  have hradpm : 0 ≤ 2 * (m.1 - p.1) * (m.2 - p.2) := by nlinarith
  have hradmr : 0 ≤ 2 * (r.1 - m.1) * (r.2 - m.2) := by nlinarith
  have hradpr : 0 ≤ 2 * (r.1 - p.1) * (r.2 - p.2) := by nlinarith
  -- square the two midpoint equations
  have hs1 : tau p m ^ 2 = (tau p r / 2) ^ 2 := by rw [hm1]
  rw [tau_of_causal hpm, tau_of_causal hpr, div_pow, Real.sq_sqrt hradpm,
    Real.sq_sqrt hradpr] at hs1
  have hs2 : tau m r ^ 2 = (tau p r / 2) ^ 2 := by rw [hm2]
  rw [tau_of_causal hmr, tau_of_causal hpr, div_pow, Real.sq_sqrt hradmr,
    Real.sq_sqrt hradpr] at hs2
  have H := midpoint_gaps_eq ha hb ha' hb'
    (by linarith : (0 : ℝ) < (m.1 - p.1) + (r.1 - m.1))
    (by linarith : (0 : ℝ) < (m.2 - p.2) + (r.2 - m.2))
    (by linear_combination 2 * hs1) (by linear_combination 2 * hs2)
  exact ⟨by linarith [H.1], by linarith [H.2]⟩

/-- **FLAT MIDPOINT UNIQUENESS** — the flat half of the midpoint invariant (whose curved
VIOLATION is the L4 target): for a chronological pair `p ≺ r`, causal `τ`-midpoints are
UNIQUE.  Contrast `IsotropyNoGo`: the taxicab plane has TWO metric midpoints; flat
Minkowski proper time has exactly ONE. -/
theorem tau_midpoint_unique {p r m m' : ℝ × ℝ}
    (h1 : p.1 < r.1) (h2 : p.2 < r.2)
    (hpm : causalLE p m) (hmr : causalLE m r)
    (hpm' : causalLE p m') (hm'r : causalLE m' r)
    (hm1 : tau p m = tau p r / 2) (hm2 : tau m r = tau p r / 2)
    (hm1' : tau p m' = tau p r / 2) (hm2' : tau m' r = tau p r / 2) :
    m = m' := by
  have c := tau_midpoint_coords h1 h2 hpm hmr hm1 hm2
  have c' := tau_midpoint_coords h1 h2 hpm' hm'r hm1' hm2'
  exact Prod.ext (c.1.trans c'.1.symm) (c.2.trans c'.2.symm)

/-! ## Part 2 (L2) — THE CAUSAL NO-GO

The deterministic causal lattice: `Fin (N+1) × Fin (N+1)` with the strict product order.
The unweighted longest chain measures the RANK `u + v` (Manhattan time), NOT proper time. -/

/-- **One causal hop** on the lattice: causally below (componentwise `≤`) and distinct. -/
def latticeLT {N : ℕ} (x y : Fin (N + 1) × Fin (N + 1)) : Prop :=
  (x.1 ≤ y.1 ∧ x.2 ≤ y.2) ∧ x ≠ y

/-- A **causal chain** of length `k`: successive elements related by one causal hop.
(Values of `c` beyond index `k` are junk, as usual.) -/
def IsCausalChain {N : ℕ} (c : ℕ → Fin (N + 1) × Fin (N + 1)) (k : ℕ) : Prop :=
  ∀ i < k, latticeLT (c i) (c (i + 1))

/-- Each causal hop strictly increases the **rank** `u + v` by at least `1`
(componentwise `≤` plus `≠` forces at least one strict increase). -/
theorem rank_increase {N : ℕ} {x y : Fin (N + 1) × Fin (N + 1)} (h : latticeLT x y) :
    x.1.1 + x.2.1 + 1 ≤ y.1.1 + y.2.1 := by
  obtain ⟨⟨h1, h2⟩, hne⟩ := h
  have h1' : x.1.1 ≤ y.1.1 := h1
  have h2' : x.2.1 ≤ y.2.1 := h2
  have hval : x.1.1 ≠ y.1.1 ∨ x.2.1 ≠ y.2.1 := by
    by_contra hc
    simp only [not_or, not_not] at hc
    exact hne (Prod.ext (Fin.ext hc.1) (Fin.ext hc.2))
  omega

/-- **The rank bound, additive form**: along a causal chain of length `k`, the rank grows
by at least `k`. -/
theorem chain_rank {N : ℕ} (c : ℕ → Fin (N + 1) × Fin (N + 1)) (k : ℕ)
    (h : IsCausalChain c k) :
    (c 0).1.1 + (c 0).2.1 + k ≤ (c k).1.1 + (c k).2.1 := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hn : IsCausalChain c n := fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hstep := rank_increase (h n (Nat.lt_succ_self n))
    have := ih hn
    omega

/-- **THE RANK BOUND**: a causal chain is no longer than the rank gap of its endpoints —
the unweighted longest-chain functional measures `u + v`, the Manhattan time. -/
theorem chain_length_le {N : ℕ} (c : ℕ → Fin (N + 1) × Fin (N + 1)) (k : ℕ)
    (h : IsCausalChain c k) :
    k ≤ ((c k).1.1 + (c k).2.1) - ((c 0).1.1 + (c 0).2.1) := by
  have := chain_rank c k h
  omega

/-- **The corner bound**: any causal chain across the full diamond, from `(0,0)` to
`(N,N)`, has length at most `2N`. -/
theorem chain_length_le_corner {N : ℕ} (c : ℕ → Fin (N + 1) × Fin (N + 1)) (k : ℕ)
    (h : IsCausalChain c k) (h0 : c 0 = (0, 0)) (hk : c k = (Fin.last N, Fin.last N)) :
    k ≤ 2 * N := by
  have H := chain_rank c k h
  rw [h0, hk] at H
  simp only [Fin.val_last, Fin.val_zero] at H
  omega

/-- **The staircase**: first `m` hops in `u`, then `n` hops in `v` — junk-safe beyond
`m + n` (it stays at `(m, n)`). -/
def staircase {N : ℕ} (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    ℕ → Fin (N + 1) × Fin (N + 1) :=
  fun i => (⟨min i m, by omega⟩, ⟨min (i - m) n, by omega⟩)

/-- The staircase is a causal chain of length exactly `m + n`. -/
theorem staircase_chain {N : ℕ} (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    IsCausalChain (staircase m n hm hn) (m + n) := by
  intro i hi
  simp only [staircase, latticeLT, Fin.mk_le_mk, ne_eq, Prod.mk.injEq, Fin.mk.injEq,
    not_and]
  omega

theorem staircase_zero {N : ℕ} (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    staircase m n hm hn 0 = (0, 0) := by
  simp only [staircase, Prod.ext_iff, Fin.ext_iff, Fin.val_zero]
  omega

theorem staircase_end {N : ℕ} (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    staircase m n hm hn (m + n) = (⟨m, by omega⟩, ⟨n, by omega⟩) := by
  simp only [staircase, Prod.ext_iff, Fin.ext_iff]
  omega

/-! ### The no-go numerics: `2 ≠ √2` -/

/-- `2 ≠ √2` — squaring would give `4 = 2`. -/
theorem two_ne_sqrt_two : (2 : ℝ) ≠ Real.sqrt 2 := by
  intro h
  have h2 : ((2 : ℝ)) ^ 2 = 2 := by
    conv_lhs => rw [h]
    exact Real.sq_sqrt (by norm_num)
  norm_num at h2

/-- The continuum proper time across the unit diamond: `τ((0,0),(1,1)) = √2`. -/
theorem tau_unit_diamond : tau ((0 : ℝ), (0 : ℝ)) (1, 1) = Real.sqrt 2 := by
  have h : causalLE ((0 : ℝ), (0 : ℝ)) (1, 1) := ⟨by norm_num, by norm_num⟩
  rw [tau_of_causal h]
  norm_num

/-- **Upper half of the no-go**: the scaled hop-time of ANY causal chain across the
`N`-diamond is at most `2` — the Manhattan value. -/
theorem hop_time_upper {N : ℕ} (hN : 1 ≤ N) (c : ℕ → Fin (N + 1) × Fin (N + 1)) (k : ℕ)
    (h : IsCausalChain c k) (h0 : c 0 = (0, 0)) (hk : c k = (Fin.last N, Fin.last N)) :
    (k : ℝ) / N ≤ 2 := by
  have hk2 : k ≤ 2 * N := chain_length_le_corner c k h h0 hk
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hkR : (k : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hk2
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Lower half of the no-go**: the staircase chain achieves length `2N` across the
`N`-diamond, so the scaled hop-time value `2` is EXACTLY attained. -/
theorem hop_time_achieved (N : ℕ) (hN : 1 ≤ N) :
    ∃ c : ℕ → Fin (N + 1) × Fin (N + 1), IsCausalChain c (2 * N) ∧ c 0 = (0, 0) ∧
      c (2 * N) = (Fin.last N, Fin.last N) ∧ ((2 * N : ℕ) : ℝ) / N = 2 := by
  refine ⟨staircase N N le_rfl le_rfl, ?_, staircase_zero N N le_rfl le_rfl, ?_, ?_⟩
  · rw [two_mul]
    exact staircase_chain N N le_rfl le_rfl
  · rw [two_mul]
    exact staircase_end N N le_rfl le_rfl
  · have hN0 : (N : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    push_cast
    field_simp

/-- **THE CAUSAL NO-GO** — the Lorentzian twin of `IsotropyNoGo`.  On the deterministic
causal lattice, the unweighted longest-chain time across the diamond is EXACTLY `2`
(rank bound + staircase), but the continuum Minkowski proper time across the unit diamond
is `√2`, and `2 ≠ √2`: **deterministic hop-counting on the causal lattice gives the WRONG
time**.  This is why causal sets need random sprinkling (Bombelli–Lee–Meyer–Sorkin 1987;
Brightwell–Gregory 1991); the weighted deterministic fix is brick L3. -/
theorem causal_no_go (N : ℕ) (hN : 1 ≤ N) :
    (∀ c : ℕ → Fin (N + 1) × Fin (N + 1), ∀ k : ℕ, IsCausalChain c k → c 0 = (0, 0) →
        c k = (Fin.last N, Fin.last N) → (k : ℝ) / N ≤ 2) ∧
    (∃ c : ℕ → Fin (N + 1) × Fin (N + 1), IsCausalChain c (2 * N) ∧ c 0 = (0, 0) ∧
        c (2 * N) = (Fin.last N, Fin.last N) ∧ ((2 * N : ℕ) : ℝ) / N = 2) ∧
    (2 : ℝ) ≠ tau ((0 : ℝ), (0 : ℝ)) (1, 1) := by
  refine ⟨fun c k h h0 hk => hop_time_upper hN c k h h0 hk, hop_time_achieved N hN, ?_⟩
  rw [tau_unit_diamond]
  exact two_ne_sqrt_two

end QIQTH.MinkowskiDiamond
