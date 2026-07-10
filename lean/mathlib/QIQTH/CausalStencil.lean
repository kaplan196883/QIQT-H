/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# THE CAUSAL STENCIL — the weighted deterministic fix: flat spacetime continuous
# (brick L3, the Lorentzian-ladder crux)

Brick L2 (`QIQTH.MinkowskiDiamond.causal_no_go`) proved that UNWEIGHTED hop-counting on the
deterministic causal lattice measures the Manhattan time `2`, not the Minkowski proper time
`√2` — pure order-counting cannot recover proper time (the machine-checked reason the
causal-set program posits RANDOM sprinkling: Bombelli–Lee–Meyer–Sorkin, Phys. Rev. Lett. 59
(1987); Brightwell–Gregory, Phys. Rev. Lett. 66 (1991), the random-sprinkling counterpart of
this brick).  This file is the deterministic fix, mirroring the isotropy story of the stencil
campaign: weight each CHRONOLOGICAL stencil step (both null coordinates advance by `1..R`) by
ITS OWN Minkowski proper time `√(2·Δu·Δv)` and MAXIMIZE the summed weight over chains.

* **Exact upper bound — no error** (`chainWeight_le_tau`): the reverse triangle inequality,
  iterated through the reverse Cauchy–Schwarz engine `HawkingWick.sqrt_mul_add_le`, pins EVERY
  weighted chain below the endpoint proper time `√(2·Δu_total·Δv_total)`.  Timelike geodesics
  MAXIMIZE proper time, so discrete chains can only fall short — the Lorentzian signature of
  the construction.
* **The even-distribution chain** (`exists_chain_weight_ge`): distributing the null gaps
  `(m, n)` as evenly as ℕ-division allows over `k` steps yields an admissible stencil chain of
  weight at least `√(2(m−k)(n−k))` — within a vanishing error of the proper time once
  `k ≈ max(m,n)/R` steps suffice.
* **THE PINCH** (`causal_stencil_pinch`): with the microscopic schedule `R_N = Nat.sqrt N`,
  for every `ε > 0` there is `N₀` such that for ALL `N ≥ N₀` and ALL causal lattice pairs
  simultaneously: every stencil chain has scaled weight `≤ gridTau` (exactly), and EITHER the
  pair's proper time is below `ε` (near-light-cone pairs need no approximant — very-null pairs
  are not even stencil-connected, exactly as physical: chronology vs causality), OR an explicit
  chain achieves the proper time within `ε`.  **Flat spacetime continuous.**

## Scope firewall (MANDATORY, HONEST)

* The causal order AND the per-step weights are **INSERTED**: the weight `√(2ΔuΔv)`
  presupposes the local Minkowski interval.  This is the deterministic WEIGHTED alternative to
  random sprinkling, NOT the pure-order causal-set dream — L2 shows the pure-order version is
  deterministically impossible.
* The pinch is **EXTRINSIC-uniform** (explicit functionals compared on a presupposed grid),
  NOT an intrinsic Lorentzian Gromov–Hausdorff statement — no settled notion of the latter
  exists.
* Everything is **1+1-dimensional**; the diamond is an **INPUT** (a chosen region).
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.MinkowskiDiamond
import QIQTH.StencilDistortion

noncomputable section

namespace QIQTH.CausalStencil

open Filter Topology

/-! ## Part 1 — the weighted causal stencil -/

/-- **One chronological stencil step with reach `R`**: BOTH null coordinates advance, each by
`1..R`.  (Compare the unweighted causal hop `MinkowskiDiamond.latticeLT`, which allows null
moves; the stencil is chronological — strictly timelike — by construction.) -/
def stencilStep (R : ℕ) {N : ℕ} (x y : Fin (N + 1) × Fin (N + 1)) : Prop :=
  x.1.1 < y.1.1 ∧ x.2.1 < y.2.1 ∧ y.1.1 ≤ x.1.1 + R ∧ y.2.1 ≤ x.2.1 + R

/-- A **stencil chain** of length `k`: successive elements related by one stencil step.
(Values of `c` beyond index `k` are junk, as usual.) -/
def IsStencilChain (R : ℕ) {N : ℕ} (c : ℕ → Fin (N + 1) × Fin (N + 1)) (k : ℕ) : Prop :=
  ∀ i < k, stencilStep R (c i) (c (i + 1))

/-- Every stencil step is in particular a causal hop of the L2 lattice. -/
theorem stencilStep_latticeLT {N R : ℕ} {x y : Fin (N + 1) × Fin (N + 1)}
    (h : stencilStep R x y) : MinkowskiDiamond.latticeLT x y := by
  obtain ⟨h1, h2, _, _⟩ := h
  refine ⟨⟨le_of_lt h1, le_of_lt h2⟩, ?_⟩
  intro he
  rw [he] at h1
  exact lt_irrefl _ h1

/-- **THE WEIGHT** — each step carries its own (unscaled) Minkowski proper time
`√(2·Δu·Δv)`; the chain weight is the sum.  (The physical, `1/N`-scaled statements divide by
`N` at the end.) -/
noncomputable def chainWeight {N : ℕ} (c : ℕ → Fin (N + 1) × Fin (N + 1)) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k,
    Real.sqrt (2 * (((c (i + 1)).1.1 : ℝ) - ((c i).1.1 : ℝ))
      * (((c (i + 1)).2.1 : ℝ) - ((c i).2.1 : ℝ)))

/-- **The scaled grid proper time** `√(2·Δu·Δv)/N` — the continuum `MinkowskiDiamond.tau` of
the `1/N`-embedded pair (see `gridTau_eq_tau`). -/
noncomputable def gridTau {N : ℕ} (x y : Fin (N + 1) × Fin (N + 1)) : ℝ :=
  Real.sqrt (2 * ((y.1.1 : ℝ) - (x.1.1 : ℝ)) * ((y.2.1 : ℝ) - (x.2.1 : ℝ))) / N

/-- `gridTau` IS the continuum flat proper time of the embedded pair: embedding the grid in
the unit diamond by `x ↦ (x₁/N, x₂/N)`, the L1 time-separation `tau` of the images equals
`gridTau` — the comparison point of the whole brick. -/
theorem gridTau_eq_tau {N : ℕ} (hN : 1 ≤ N) {x y : Fin (N + 1) × Fin (N + 1)}
    (hu : x.1 ≤ y.1) (hv : x.2 ≤ y.2) :
    gridTau x y = MinkowskiDiamond.tau ((x.1.1 : ℝ) / N, (x.2.1 : ℝ) / N)
      ((y.1.1 : ℝ) / N, (y.2.1 : ℝ) / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hu' : x.1.1 ≤ y.1.1 := hu
  have hv' : x.2.1 ≤ y.2.1 := hv
  have huR : (x.1.1 : ℝ) ≤ (y.1.1 : ℝ) := by exact_mod_cast hu'
  have hvR : (x.2.1 : ℝ) ≤ (y.2.1 : ℝ) := by exact_mod_cast hv'
  have hcaus : MinkowskiDiamond.causalLE ((x.1.1 : ℝ) / N, (x.2.1 : ℝ) / N)
      ((y.1.1 : ℝ) / N, (y.2.1 : ℝ) / N) := by
    constructor <;> · dsimp only; gcongr
  rw [MinkowskiDiamond.tau_of_causal hcaus]
  dsimp only
  have hA : (0 : ℝ) ≤ 2 * ((y.1.1 : ℝ) - (x.1.1 : ℝ)) * ((y.2.1 : ℝ) - (x.2.1 : ℝ)) := by
    nlinarith
  have h1 : 2 * ((y.1.1 : ℝ) / N - (x.1.1 : ℝ) / N) * ((y.2.1 : ℝ) / N - (x.2.1 : ℝ) / N)
      = 2 * ((y.1.1 : ℝ) - (x.1.1 : ℝ)) * ((y.2.1 : ℝ) - (x.2.1 : ℝ)) / N ^ 2 := by
    field_simp
  rw [gridTau, h1, Real.sqrt_div hA, Real.sqrt_sq hNpos.le]

/-! ### Chain monotonicity -/

/-- Along a stencil chain the first null coordinate is monotone (in fact strictly). -/
theorem chain_fst_le {N R : ℕ} {c : ℕ → Fin (N + 1) × Fin (N + 1)} {k : ℕ}
    (h : IsStencilChain R c k) : (c 0).1.1 ≤ (c k).1.1 := by
  induction k with
  | zero => exact le_rfl
  | succ n ih =>
    have hn : IsStencilChain R c n := fun i hi => h i (Nat.lt_succ_of_lt hi)
    exact le_trans (ih hn) (le_of_lt (h n (Nat.lt_succ_self n)).1)

/-- Along a stencil chain the second null coordinate is monotone. -/
theorem chain_snd_le {N R : ℕ} {c : ℕ → Fin (N + 1) × Fin (N + 1)} {k : ℕ}
    (h : IsStencilChain R c k) : (c 0).2.1 ≤ (c k).2.1 := by
  induction k with
  | zero => exact le_rfl
  | succ n ih =>
    have hn : IsStencilChain R c n := fun i hi => h i (Nat.lt_succ_of_lt hi)
    exact le_trans (ih hn) (le_of_lt (h n (Nat.lt_succ_self n)).2.1)

/-! ## Part 2 — THE EXACT UPPER BOUND (reverse triangle inequality, iterated) -/

/-- **THE UPPER BOUND — with NO error term**: the weight of ANY stencil chain is at most the
endpoint proper time `√(2·Δu_total·Δv_total)`.  Induction on the chain; the step is the
reverse Cauchy–Schwarz inequality `HawkingWick.sqrt_mul_add_le` (the same engine as the L1
reverse triangle inequality `tau_reverse_triangle`): timelike geodesics MAXIMIZE proper time,
so the discrete zigzag can only lose. -/
theorem chainWeight_le_tau {N R : ℕ} (c : ℕ → Fin (N + 1) × Fin (N + 1)) (k : ℕ)
    (h : IsStencilChain R c k) :
    chainWeight c k ≤ Real.sqrt (2 * (((c k).1.1 : ℝ) - ((c 0).1.1 : ℝ))
      * (((c k).2.1 : ℝ) - ((c 0).2.1 : ℝ))) := by
  induction k with
  | zero => simp [chainWeight]
  | succ n ih =>
    have hn : IsStencilChain R c n := fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hstep := h n (Nat.lt_succ_self n)
    have hA : (0 : ℝ) ≤ ((c n).1.1 : ℝ) - ((c 0).1.1 : ℝ) := by
      have h1 := chain_fst_le hn
      have h2 : ((c 0).1.1 : ℝ) ≤ ((c n).1.1 : ℝ) := by exact_mod_cast h1
      linarith
    have hB : (0 : ℝ) ≤ ((c n).2.1 : ℝ) - ((c 0).2.1 : ℝ) := by
      have h1 := chain_snd_le hn
      have h2 : ((c 0).2.1 : ℝ) ≤ ((c n).2.1 : ℝ) := by exact_mod_cast h1
      linarith
    have ha : (0 : ℝ) ≤ ((c (n + 1)).1.1 : ℝ) - ((c n).1.1 : ℝ) := by
      have h2 : ((c n).1.1 : ℝ) ≤ ((c (n + 1)).1.1 : ℝ) := by exact_mod_cast le_of_lt hstep.1
      linarith
    have hb : (0 : ℝ) ≤ ((c (n + 1)).2.1 : ℝ) - ((c n).2.1 : ℝ) := by
      have h2 : ((c n).2.1 : ℝ) ≤ ((c (n + 1)).2.1 : ℝ) := by
        exact_mod_cast le_of_lt hstep.2.1
      linarith
    have key := QIQTH.HawkingWick.sqrt_mul_add_le
      (2 * (((c n).1.1 : ℝ) - ((c 0).1.1 : ℝ))) (((c n).2.1 : ℝ) - ((c 0).2.1 : ℝ))
      (2 * (((c (n + 1)).1.1 : ℝ) - ((c n).1.1 : ℝ)))
      (((c (n + 1)).2.1 : ℝ) - ((c n).2.1 : ℝ))
      (by linarith) hB (by linarith) hb
    have hrad : (2 * (((c n).1.1 : ℝ) - ((c 0).1.1 : ℝ))
          + 2 * (((c (n + 1)).1.1 : ℝ) - ((c n).1.1 : ℝ)))
        * ((((c n).2.1 : ℝ) - ((c 0).2.1 : ℝ))
          + ((((c (n + 1)).2.1 : ℝ)) - ((c n).2.1 : ℝ)))
        = 2 * (((c (n + 1)).1.1 : ℝ) - ((c 0).1.1 : ℝ))
          * (((c (n + 1)).2.1 : ℝ) - ((c 0).2.1 : ℝ)) := by
      ring
    rw [hrad] at key
    have hsum : chainWeight c (n + 1) = chainWeight c n
        + Real.sqrt (2 * (((c (n + 1)).1.1 : ℝ) - ((c n).1.1 : ℝ))
          * (((c (n + 1)).2.1 : ℝ) - ((c n).2.1 : ℝ))) := by
      simp only [chainWeight]
      exact Finset.sum_range_succ _ n
    rw [hsum]
    linarith [ih hn]

/-- **The scaled upper half of the pinch** — valid for EVERY `N ≥ 1` and EVERY reach `R`,
unconditionally: the scaled weight of any stencil chain between `x` and `y` is at most the
scaled grid proper time. -/
theorem chainWeight_div_le_gridTau {N R : ℕ} (hN : 1 ≤ N) {x y : Fin (N + 1) × Fin (N + 1)}
    (c : ℕ → Fin (N + 1) × Fin (N + 1)) (k : ℕ)
    (h : IsStencilChain R c k) (h0 : c 0 = x) (hk : c k = y) :
    chainWeight c k / N ≤ gridTau x y := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle := chainWeight_le_tau c k h
  rw [h0, hk] at hle
  rw [gridTau]
  gcongr

/-! ## Part 3 — ℕ-division floor arithmetic (the even-distribution toolkit) -/

private lemma nat_div_add_le (a b k : ℕ) (hk : 0 < k) : a / k + b / k ≤ (a + b) / k := by
  rw [Nat.le_div_iff_mul_le hk, add_mul]
  exact Nat.add_le_add (Nat.div_mul_le_self a k) (Nat.div_mul_le_self b k)

/-- Floor-division step gaps are at least the floor of the average: `⌊(i+1)m/k⌋ − ⌊im/k⌋ ≥
⌊m/k⌋`. -/
private lemma step_gap_lower (i k m : ℕ) (hk : 0 < k) :
    i * m / k + m / k ≤ (i + 1) * m / k := by
  have h := nat_div_add_le (i * m) m k hk
  rwa [← add_one_mul] at h

/-- Floor-division step gaps are at most the ceiling of the average: `⌊(i+1)m/k⌋ − ⌊im/k⌋ ≤
⌈m/k⌉ = (m+k−1)/k`. -/
private lemma step_gap_upper (i k m : ℕ) (hk : 0 < k) :
    (i + 1) * m / k ≤ i * m / k + (m + k - 1) / k := by
  rw [add_one_mul]
  have hsplit : (i * m + m) / k = i * m / k + (i * m % k + m) / k := by
    conv_lhs => rw [← Nat.div_add_mod (i * m) k, add_assoc]
    rw [Nat.mul_add_div hk]
  rw [hsplit]
  have hr : i * m % k < k := Nat.mod_lt _ hk
  exact Nat.add_le_add_left (Nat.div_le_div_right (by omega)) _

/-- The ceiling `(m+k−1)/k` fits under the reach: `m ≤ kR` forces `⌈m/k⌉ ≤ R`. -/
private lemma ceil_div_le {m k R : ℕ} (hk : 0 < k) (h : m ≤ k * R) : (m + k - 1) / k ≤ R := by
  refine Nat.lt_succ_iff.mp ?_
  rw [Nat.div_lt_iff_lt_mul hk]
  have h3 : m + k - 1 < m + k := Nat.sub_lt (by omega) one_pos
  calc m + k - 1 < m + k := h3
    _ ≤ k * R + k := Nat.add_le_add_right h k
    _ = (R + 1) * k := by ring

/-- The ceiling count covers the gap: `m ≤ R·⌈m/R⌉`. -/
private lemma le_mul_ceilDiv {m R : ℕ} (hR : 0 < R) : m ≤ R * ((m + R - 1) / R) := by
  have h1 := Nat.div_add_mod (m + R - 1) R
  have h2 := Nat.mod_lt (m + R - 1) hR
  omega

/-- The ceiling count never exceeds the gap itself: `⌈m/R⌉ ≤ m` for `m, R ≥ 1`. -/
private lemma ceilDiv_le_self {m R : ℕ} (hm : 1 ≤ m) (hR : 1 ≤ R) : (m + R - 1) / R ≤ m := by
  refine Nat.lt_succ_iff.mp ?_
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have h2 : m ≤ m * R := by
    calc m = m * 1 := (Nat.mul_one m).symm
      _ ≤ m * R := Nat.mul_le_mul le_rfl hR
  calc m + R - 1 < m + R := Nat.sub_lt (by omega) one_pos
    _ ≤ m * R + R := Nat.add_le_add_right h2 R
    _ = (m + 1) * R := by ring

/-- The real cast of a floor quotient sits above the true quotient minus one. -/
private lemma nat_div_cast_ge {m k : ℕ} (hk : 0 < k) :
    (m : ℝ) / (k : ℝ) - 1 ≤ ((m / k : ℕ) : ℝ) := by
  have hmod := Nat.div_add_mod m k
  have hlt : m % k < k := Nat.mod_lt m hk
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hcast : (k : ℝ) * ((m / k : ℕ) : ℝ) + ((m % k : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast hmod
  have hltR : ((m % k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast hlt
  rw [sub_le_iff_le_add, div_le_iff₀ hkR]
  nlinarith [hcast, hltR]

/-! ## Part 4 — THE EVEN-DISTRIBUTION CHAIN (the lower-bound construction) -/

private lemma evenCoord_le (i k m : ℕ) : min i k * m / k ≤ m := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have h1 : min i k * m ≤ k * m := Nat.mul_le_mul (min_le_right i k) le_rfl
    have h2 : min i k * m / k ≤ k * m / k := Nat.div_le_div_right h1
    rwa [Nat.mul_div_cancel_left m hk] at h2

/-- **The even-distribution chain** from `(a, b)` to `(a+m, b+n)` in `k` steps: the `i`-th
point advances each null coordinate to the floor of the even schedule, `⌊i·m/k⌋` and
`⌊i·n/k⌋` — junk-safe beyond `k` via `min`. -/
def evenChain (N a b k m n : ℕ) (ha : a + m ≤ N) (hb : b + n ≤ N) :
    ℕ → Fin (N + 1) × Fin (N + 1) :=
  fun i =>
    (⟨a + min i k * m / k,
      Nat.lt_succ_of_le (le_trans (Nat.add_le_add_left (evenCoord_le i k m) a) ha)⟩,
     ⟨b + min i k * n / k,
      Nat.lt_succ_of_le (le_trans (Nat.add_le_add_left (evenCoord_le i k n) b) hb)⟩)

/-- The even-distribution chain is an admissible stencil chain: each floor gap lies in
`[⌊m/k⌋, ⌈m/k⌉] ⊆ [1, R]` under `k ≤ m ≤ kR`. -/
theorem evenChain_isStencilChain {N a b k m n R : ℕ} (ha : a + m ≤ N) (hb : b + n ≤ N)
    (hk : 0 < k) (hkm : k ≤ m) (hkn : k ≤ n) (hRm : m ≤ k * R) (hRn : n ≤ k * R) :
    IsStencilChain R (evenChain N a b k m n ha hb) k := by
  intro i hi
  have hmin1 : min i k = i := min_eq_left hi.le
  have hmin2 : min (i + 1) k = i + 1 := min_eq_left hi
  have h1m := step_gap_lower i k m hk
  have h2m := (Nat.one_le_div_iff hk).mpr hkm
  have h3m := step_gap_upper i k m hk
  have h4m := ceil_div_le hk hRm
  have h1n := step_gap_lower i k n hk
  have h2n := (Nat.one_le_div_iff hk).mpr hkn
  have h3n := step_gap_upper i k n hk
  have h4n := ceil_div_le hk hRn
  refine ⟨?_, ?_, ?_, ?_⟩
  · show a + min i k * m / k < a + min (i + 1) k * m / k
    rw [hmin1, hmin2]
    omega
  · show b + min i k * n / k < b + min (i + 1) k * n / k
    rw [hmin1, hmin2]
    omega
  · show a + min (i + 1) k * m / k ≤ a + min i k * m / k + R
    rw [hmin1, hmin2]
    omega
  · show b + min (i + 1) k * n / k ≤ b + min i k * n / k + R
    rw [hmin1, hmin2]
    omega

theorem evenChain_zero {N a b k m n : ℕ} (ha : a + m ≤ N) (hb : b + n ≤ N) :
    (evenChain N a b k m n ha hb 0).1.1 = a ∧ (evenChain N a b k m n ha hb 0).2.1 = b := by
  constructor
  · show a + min 0 k * m / k = a
    simp
  · show b + min 0 k * n / k = b
    simp

theorem evenChain_last {N a b k m n : ℕ} (hk : 0 < k) (ha : a + m ≤ N) (hb : b + n ≤ N) :
    (evenChain N a b k m n ha hb k).1.1 = a + m
      ∧ (evenChain N a b k m n ha hb k).2.1 = b + n := by
  constructor
  · show a + min k k * m / k = a + m
    rw [min_self, Nat.mul_div_cancel_left m hk]
  · show b + min k k * n / k = b + n
    rw [min_self, Nat.mul_div_cancel_left n hk]

/-- **The weight of the even-distribution chain**: every step gap is at least the real
average minus one, so the total weight is at least `k·√(2(m/k−1)(n/k−1)) = √(2(m−k)(n−k))`. -/
theorem evenChain_weight_ge {N a b k m n : ℕ} (ha : a + m ≤ N) (hb : b + n ≤ N)
    (hk : 0 < k) (hkm : k ≤ m) (hkn : k ≤ n) :
    Real.sqrt (2 * ((m : ℝ) - k) * ((n : ℝ) - k))
      ≤ chainWeight (evenChain N a b k m n ha hb) k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  set x₀ : ℝ := (m : ℝ) / k - 1 with hx₀
  set y₀ : ℝ := (n : ℝ) / k - 1 with hy₀
  have hx₀0 : 0 ≤ x₀ := by
    rw [hx₀, sub_nonneg]
    exact (one_le_div hkpos).mpr (by exact_mod_cast hkm)
  have hy₀0 : 0 ≤ y₀ := by
    rw [hy₀, sub_nonneg]
    exact (one_le_div hkpos).mpr (by exact_mod_cast hkn)
  -- the per-step bound
  have hterm : ∀ i ∈ Finset.range k,
      Real.sqrt (2 * x₀ * y₀)
        ≤ Real.sqrt (2 * (((evenChain N a b k m n ha hb (i + 1)).1.1 : ℝ)
            - ((evenChain N a b k m n ha hb i).1.1 : ℝ))
          * (((evenChain N a b k m n ha hb (i + 1)).2.1 : ℝ)
            - ((evenChain N a b k m n ha hb i).2.1 : ℝ))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hmin1 : min i k = i := min_eq_left hi.le
    have hmin2 : min (i + 1) k = i + 1 := min_eq_left hi
    have hδu : x₀ ≤ ((evenChain N a b k m n ha hb (i + 1)).1.1 : ℝ)
        - ((evenChain N a b k m n ha hb i).1.1 : ℝ) := by
      show x₀ ≤ ((a + min (i + 1) k * m / k : ℕ) : ℝ) - ((a + min i k * m / k : ℕ) : ℝ)
      rw [hmin1, hmin2]
      push_cast
      have hg := step_gap_lower i k m hk
      have hgR : ((i * m / k : ℕ) : ℝ) + ((m / k : ℕ) : ℝ)
          ≤ (((i + 1) * m / k : ℕ) : ℝ) := by exact_mod_cast hg
      have hfloor := nat_div_cast_ge (m := m) hk
      rw [hx₀]
      linarith
    have hδv : y₀ ≤ ((evenChain N a b k m n ha hb (i + 1)).2.1 : ℝ)
        - ((evenChain N a b k m n ha hb i).2.1 : ℝ) := by
      show y₀ ≤ ((b + min (i + 1) k * n / k : ℕ) : ℝ) - ((b + min i k * n / k : ℕ) : ℝ)
      rw [hmin1, hmin2]
      push_cast
      have hg := step_gap_lower i k n hk
      have hgR : ((i * n / k : ℕ) : ℝ) + ((n / k : ℕ) : ℝ)
          ≤ (((i + 1) * n / k : ℕ) : ℝ) := by exact_mod_cast hg
      have hfloor := nat_div_cast_ge (m := n) hk
      rw [hy₀]
      linarith
    apply Real.sqrt_le_sqrt
    have hprod : x₀ * y₀ ≤ (((evenChain N a b k m n ha hb (i + 1)).1.1 : ℝ)
          - ((evenChain N a b k m n ha hb i).1.1 : ℝ))
        * (((evenChain N a b k m n ha hb (i + 1)).2.1 : ℝ)
          - ((evenChain N a b k m n ha hb i).2.1 : ℝ)) :=
      mul_le_mul hδu hδv hy₀0 (le_trans hx₀0 hδu)
    linarith [hprod]
  calc Real.sqrt (2 * ((m : ℝ) - k) * ((n : ℝ) - k))
      = (k : ℝ) * Real.sqrt (2 * x₀ * y₀) := by
        rw [hx₀, hy₀]
        rw [show 2 * ((m : ℝ) - k) * ((n : ℝ) - k)
            = (k : ℝ) ^ 2 * (2 * ((m : ℝ) / k - 1) * ((n : ℝ) / k - 1)) from by
          field_simp]
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hkpos.le]
    _ = ∑ _i ∈ Finset.range k, Real.sqrt (2 * x₀ * y₀) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ chainWeight (evenChain N a b k m n ha hb) k := Finset.sum_le_sum hterm

/-- **THE LOWER-BOUND CONSTRUCTION (b)**: under the schedule window `1 ≤ k ≤ min(m,n)` and
`max(m,n) ≤ kR`, there is an admissible stencil chain from `(a, b)` to `(a+m, b+n)` in
exactly `k` steps whose weight is at least `√(2(m−k)(n−k))`. -/
theorem exists_chain_weight_ge {N R : ℕ} (a b k m n : ℕ) (hk : 1 ≤ k)
    (hkm : k ≤ m) (hkn : k ≤ n) (hRm : m ≤ k * R) (hRn : n ≤ k * R)
    (ha : a + m ≤ N) (hb : b + n ≤ N) :
    ∃ c : ℕ → Fin (N + 1) × Fin (N + 1), IsStencilChain R c k ∧
      (c 0).1.1 = a ∧ (c 0).2.1 = b ∧ (c k).1.1 = a + m ∧ (c k).2.1 = b + n ∧
      Real.sqrt (2 * ((m : ℝ) - k) * ((n : ℝ) - k)) ≤ chainWeight c k :=
  ⟨evenChain N a b k m n ha hb,
   evenChain_isStencilChain ha hb hk hkm hkn hRm hRn,
   (evenChain_zero ha hb).1, (evenChain_zero ha hb).2,
   (evenChain_last hk ha hb).1, (evenChain_last hk ha hb).2,
   evenChain_weight_ge ha hb hk hkm hkn⟩

/-! ## Part 5 — the error calculus -/

/-- `√a − √b ≤ √(a − b)` for `b ≥ 0` — square-root subadditivity, reversed. -/
theorem sqrt_sub_sqrt_le {a b : ℝ} (hb : 0 ≤ b) :
    Real.sqrt a - Real.sqrt b ≤ Real.sqrt (a - b) := by
  rcases le_total a b with h | h
  · have h1 : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt h
    have h2 := Real.sqrt_nonneg (a - b)
    linarith
  · have hab : 0 ≤ a - b := by linarith
    have key : Real.sqrt a ≤ Real.sqrt (a - b) + Real.sqrt b := by
      have h2 : a ≤ (Real.sqrt (a - b) + Real.sqrt b) ^ 2 := by
        have e1 : Real.sqrt (a - b) ^ 2 = a - b := Real.sq_sqrt hab
        have e2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
        nlinarith [mul_nonneg (Real.sqrt_nonneg (a - b)) (Real.sqrt_nonneg b)]
      calc Real.sqrt a ≤ Real.sqrt ((Real.sqrt (a - b) + Real.sqrt b) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = Real.sqrt (a - b) + Real.sqrt b := Real.sqrt_sq (by positivity)
    linarith

/-- **The shrink estimate**: shaving `k` off both null gaps costs at most `√(2k(m+n))` of
proper time — `√(2mn) − √(2k(m+n)) ≤ √(2(m−k)(n−k))`. -/
theorem sqrt_shrink {m n k : ℝ} (hk : 0 ≤ k) (hm : k ≤ m) (hn : k ≤ n) :
    Real.sqrt (2 * m * n) - Real.sqrt (2 * k * (m + n))
      ≤ Real.sqrt (2 * (m - k) * (n - k)) := by
  have hb : (0 : ℝ) ≤ 2 * k * (m + n) := by
    have := mul_nonneg hk (add_nonneg (hk.trans hm) (hk.trans hn))
    linarith
  have h1 : Real.sqrt (2 * m * n) - Real.sqrt (2 * k * (m + n))
      ≤ Real.sqrt (2 * m * n - 2 * k * (m + n)) := sqrt_sub_sqrt_le hb
  have h2 : Real.sqrt (2 * m * n - 2 * k * (m + n))
      ≤ Real.sqrt (2 * (m - k) * (n - k)) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg k])
  linarith

/-- **The vanishing error of the `R_N = √N` schedule**: `√(4/√N + 4/N)`. -/
noncomputable def errorTerm (N : ℕ) : ℝ :=
  Real.sqrt (4 / (Nat.sqrt N : ℝ) + 4 / (N : ℝ))

theorem errorTerm_nonneg (N : ℕ) : 0 ≤ errorTerm N := Real.sqrt_nonneg _

/-- The error vanishes: `errorTerm N → 0` as `N → ∞` (both radicand summands vanish since
`Nat.sqrt N → ∞`). -/
theorem errorTerm_tendsto_zero : Tendsto errorTerm atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => 4 / ((Nat.sqrt N : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hs : Tendsto (fun N : ℕ => ((Nat.sqrt N : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp QIQTH.StencilDistortion.tendsto_natSqrt_atTop
    simpa [div_eq_mul_inv] using hs.inv_tendsto_atTop.const_mul (4 : ℝ)
  have h2 : Tendsto (fun N : ℕ => 4 / (N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul (4 : ℝ)
  have h3 := h1.add h2
  rw [add_zero] at h3
  simpa [errorTerm, Real.sqrt_zero] using h3.sqrt

private lemma sqrt_le_error_of_le {A N R : ℝ} (hN : 0 < N)
    (hA : A ≤ N ^ 2 * (4 / R + 4 / N)) :
    Real.sqrt A / N ≤ Real.sqrt (4 / R + 4 / N) := by
  have h1 : Real.sqrt A ≤ Real.sqrt (N ^ 2 * (4 / R + 4 / N)) := Real.sqrt_le_sqrt hA
  rw [Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN.le] at h1
  rw [div_le_iff₀ hN]
  linarith

/-- Near-null pairs: if `m ≤ n/R` and `n ≤ N`, the scaled proper time `√(2mn)/N` is already
inside the error budget `√(4/R + 4/N)`. -/
private lemma sqrt_prod_le_error {m n N R : ℝ} (hR : 0 < R) (hN : 0 < N)
    (hn0 : 0 ≤ n) (hnN : n ≤ N) (hmn : m ≤ n / R) :
    Real.sqrt (2 * m * n) / N ≤ Real.sqrt (4 / R + 4 / N) := by
  apply sqrt_le_error_of_le hN
  have h1 : m * n ≤ (n / R) * n := mul_le_mul_of_nonneg_right hmn hn0
  have hdiv : n / R ≤ N / R := by gcongr
  have h2 : (n / R) * n ≤ (N / R) * N := mul_le_mul hdiv hnN hn0 (div_nonneg hN.le hR.le)
  have h3 : N ^ 2 * (4 / R + 4 / N) = 4 * ((N / R) * N) + 4 * N := by
    field_simp
  nlinarith [h1, h2, h3, mul_nonneg (div_nonneg hN.le hR.le) hN.le, hN.le]

/-! ## Part 6 — THE PINCH -/

/-- **The per-`N` lower half**: for every causal pair, EITHER the scaled proper time is
already below `errorTerm N`, OR the even-distribution chain with `k = max(⌈m/R⌉, ⌈n/R⌉)`
steps (`R = Nat.sqrt N`) connects the pair and achieves the proper time up to
`errorTerm N`. -/
theorem chain_approximates {N : ℕ} (hN : 1 ≤ N) (x y : Fin (N + 1) × Fin (N + 1))
    (hu : x.1 ≤ y.1) (hv : x.2 ≤ y.2) :
    gridTau x y ≤ errorTerm N ∨
      ∃ c : ℕ → Fin (N + 1) × Fin (N + 1), ∃ k : ℕ,
        IsStencilChain (Nat.sqrt N) c k ∧ c 0 = x ∧ c k = y ∧
        gridTau x y - errorTerm N ≤ chainWeight c k / N := by
  set R := Nat.sqrt N with hRdef
  have hR : 1 ≤ R := by rw [hRdef]; exact Nat.sqrt_pos.mpr hN
  have hu' : x.1.1 ≤ y.1.1 := hu
  have hv' : x.2.1 ≤ y.2.1 := hv
  set m := y.1.1 - x.1.1 with hmdef
  set n := y.2.1 - x.2.1 with hndef
  have hmx : x.1.1 + m = y.1.1 := by omega
  have hnx : x.2.1 + n = y.2.1 := by omega
  have hmN : x.1.1 + m ≤ N := by have := y.1.isLt; omega
  have hnN : x.2.1 + n ≤ N := by have := y.2.isLt; omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hgt : gridTau x y = Real.sqrt (2 * (m : ℝ) * (n : ℝ)) / N := by
    rw [gridTau, hmdef, hndef, Nat.cast_sub hu', Nat.cast_sub hv']
  -- degenerate (null) pairs: gridTau = 0
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · left
    rw [hgt, hm0]
    simpa using errorTerm_nonneg N
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · left
    rw [hgt, hn0]
    simpa using errorTerm_nonneg N
  -- chronological pairs: the ceiling step counts
  set A := (m + R - 1) / R with hAdef
  set B := (n + R - 1) / R with hBdef
  set k := max A B with hkdef
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    exact (Nat.one_le_div_iff (by omega)).mpr (by omega)
  have hk1 : 1 ≤ k := le_trans hA1 (by rw [hkdef]; exact le_max_left A B)
  have hmA : m ≤ R * A := by rw [hAdef]; exact le_mul_ceilDiv (by omega)
  have hnB : n ≤ R * B := by rw [hBdef]; exact le_mul_ceilDiv (by omega)
  have hmkR : m ≤ k * R := by
    have h2 : R * A ≤ R * k := Nat.mul_le_mul le_rfl (by rw [hkdef]; exact le_max_left A B)
    have h3 : R * k = k * R := Nat.mul_comm R k
    omega
  have hnkR : n ≤ k * R := by
    have h2 : R * B ≤ R * k := Nat.mul_le_mul le_rfl (by rw [hkdef]; exact le_max_right A B)
    have h3 : R * k = k * R := Nat.mul_comm R k
    omega
  by_cases hcase : k ≤ m ∧ k ≤ n
  · -- STENCIL-TIMELIKE: the even-distribution chain applies
    right
    obtain ⟨hkm, hkn⟩ := hcase
    obtain ⟨c, hchain, h0u, h0v, hku, hkv, hw⟩ :=
      exists_chain_weight_ge (N := N) (R := R) x.1.1 x.2.1 k m n hk1 hkm hkn hmkR hnkR hmN hnN
    refine ⟨c, k, hchain, ?_, ?_, ?_⟩
    · exact Prod.ext (Fin.ext h0u) (Fin.ext h0v)
    · exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    · rw [hgt]
      have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
      have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      have hk0R : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hshrink := sqrt_shrink hk0R hkmR hknR
      -- the error control: √(2k(m+n))/N ≤ errorTerm N
      have herr : Real.sqrt (2 * (k : ℝ) * ((m : ℝ) + (n : ℝ))) / N ≤ errorTerm N := by
        rw [errorTerm, ← hRdef]
        apply sqrt_le_error_of_le hNpos
        have hkK : (k : ℝ) ≤ (N : ℝ) / R + 1 := by
          have h1 : k ≤ (N + R - 1) / R := by
            have h2 : A ≤ (N + R - 1) / R := by
              rw [hAdef]
              exact Nat.div_le_div_right (by omega)
            have h3 : B ≤ (N + R - 1) / R := by
              rw [hBdef]
              exact Nat.div_le_div_right (by omega)
            rw [hkdef]
            exact max_le h2 h3
          have h4 : ((k : ℕ) : ℝ) ≤ (((N + R - 1) / R : ℕ) : ℝ) := by exact_mod_cast h1
          have h5 : (((N + R - 1) / R : ℕ) : ℝ) ≤ ((N + R - 1 : ℕ) : ℝ) / (R : ℝ) :=
            Nat.cast_div_le
          have h6 : ((N + R - 1 : ℕ) : ℝ) = (N : ℝ) + (R : ℝ) - 1 := by
            have h : (1 : ℕ) ≤ N + R := by omega
            rw [Nat.cast_sub h]
            push_cast
            ring
          rw [h6] at h5
          have h7 : ((N : ℝ) + (R : ℝ) - 1) / R ≤ (N : ℝ) / R + 1 := by
            have h8 : ((N : ℝ) + (R : ℝ) - 1) / R = (N : ℝ) / R + 1 - 1 / R := by
              field_simp
            have h9 : (0 : ℝ) < 1 / R := by positivity
            linarith
          linarith
        have hmnN : (m : ℝ) + (n : ℝ) ≤ 2 * N := by
          have h8 : (m : ℝ) ≤ N := by exact_mod_cast (by omega : m ≤ N)
          have h9 : (n : ℝ) ≤ N := by exact_mod_cast (by omega : n ≤ N)
          linarith
        have hmn0 : (0 : ℝ) ≤ (m : ℝ) + (n : ℝ) := by positivity
        have hstep1 : 2 * (k : ℝ) * ((m : ℝ) + (n : ℝ))
            ≤ 2 * ((N : ℝ) / R + 1) * (2 * N) := by
          have hk0' : (0 : ℝ) ≤ (N : ℝ) / R + 1 := by positivity
          nlinarith [hkK, hmnN, hk0R, hmn0]
        have hstep2 : 2 * ((N : ℝ) / R + 1) * (2 * N) = (N : ℝ) ^ 2 * (4 / R + 4 / N) := by
          field_simp
          ring
        linarith
      have hwN : Real.sqrt (2 * ((m : ℝ) - k) * ((n : ℝ) - k)) / N
          ≤ chainWeight c k / N := by gcongr
      have hshrinkN : (Real.sqrt (2 * (m : ℝ) * (n : ℝ))
            - Real.sqrt (2 * (k : ℝ) * ((m : ℝ) + (n : ℝ)))) / N
          ≤ Real.sqrt (2 * ((m : ℝ) - k) * ((n : ℝ) - k)) / N := by gcongr
      rw [sub_div] at hshrinkN
      linarith
  · -- NEAR-NULL: the pair's proper time is inside the error budget
    left
    rw [hgt, errorTerm, ← hRdef]
    have hor : m < k ∨ n < k := by
      by_cases h : k ≤ m
      · right
        rcases not_and_or.mp hcase with h' | h'
        · omega
        · omega
      · left; omega
    rcases hor with hlt | hlt
    · -- m < k forces k = ⌈n/R⌉ and m ≤ n/R
      have hAm : A ≤ m := by
        rw [hAdef]
        exact ceilDiv_le_self (by omega) (by omega)
      have hkB : k = B := by
        rcases le_total A B with h | h
        · rw [hkdef]; exact max_eq_right h
        · exfalso
          have : k = A := by rw [hkdef]; exact max_eq_left h
          omega
      have hB1 : B = (n - 1) / R + 1 := by
        rw [hBdef]
        have h1 : n + R - 1 = (n - 1) + R := by omega
        rw [h1, Nat.add_div_right _ (by omega)]
      have hm1 : m ≤ (n - 1) / R := by omega
      have hmR : (m : ℝ) ≤ (n : ℝ) / R := by
        have h2 : ((m : ℕ) : ℝ) ≤ (((n - 1) / R : ℕ) : ℝ) := by exact_mod_cast hm1
        have h3 : (((n - 1) / R : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / (R : ℝ) := Nat.cast_div_le
        have h4 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : n - 1 ≤ n)
        have h5 : ((n - 1 : ℕ) : ℝ) / (R : ℝ) ≤ (n : ℝ) / R := by gcongr
        linarith
      have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : n ≤ N)
      exact sqrt_prod_le_error hRpos hNpos (by positivity) hnN' hmR
    · -- n < k forces k = ⌈m/R⌉ and n ≤ m/R (the mirror case)
      have hBn : B ≤ n := by
        rw [hBdef]
        exact ceilDiv_le_self (by omega) (by omega)
      have hkA : k = A := by
        rcases le_total B A with h | h
        · rw [hkdef]; exact max_eq_left h
        · exfalso
          have : k = B := by rw [hkdef]; exact max_eq_right h
          omega
      have hA1' : A = (m - 1) / R + 1 := by
        rw [hAdef]
        have h1 : m + R - 1 = (m - 1) + R := by omega
        rw [h1, Nat.add_div_right _ (by omega)]
      have hn1' : n ≤ (m - 1) / R := by omega
      have hnR : (n : ℝ) ≤ (m : ℝ) / R := by
        have h2 : ((n : ℕ) : ℝ) ≤ (((m - 1) / R : ℕ) : ℝ) := by exact_mod_cast hn1'
        have h3 : (((m - 1) / R : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) / (R : ℝ) := Nat.cast_div_le
        have h4 : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : m - 1 ≤ m)
        have h5 : ((m - 1 : ℕ) : ℝ) / (R : ℝ) ≤ (m : ℝ) / R := by gcongr
        linarith
      have hmN' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : m ≤ N)
      rw [show 2 * (m : ℝ) * (n : ℝ) = 2 * (n : ℝ) * (m : ℝ) from by ring]
      exact sqrt_prod_le_error hRpos hNpos (by positivity) hmN' hnR

/-- **THE CAUSAL-STENCIL PINCH — flat spacetime continuous (brick L3, the crux).**
With the microscopic schedule `R_N = Nat.sqrt N`, for every `ε > 0` there is `N₀` such that
for ALL `N ≥ N₀` and ALL causal lattice pairs `x ≼ y` SIMULTANEOUSLY:

* (upper, EXACT) every weighted stencil chain from `x` to `y` has scaled weight at most the
  scaled proper time `gridTau x y` — the iterated reverse triangle inequality, with no error;
* (lower, honest disjunction) EITHER `gridTau x y ≤ ε` — the pair is so close to the light
  cone that there is nothing to approximate (very-null pairs are not stencil-connected at
  all: chronology vs causality, exactly as physical) — OR an explicit even-distribution
  chain connects `x` to `y` with scaled weight within `ε` of `gridTau x y`.  For
  timelike-separated pairs at fixed direction the second disjunct eventually holds.

Contrast `MinkowskiDiamond.causal_no_go` (L2): unweighted hop-counting converges to the
Manhattan time `2 ≠ √2`; the per-step Minkowski weight is the deterministic fix — the
deterministic counterpart of Brightwell–Gregory's random-sprinkling convergence theorem. -/
theorem causal_stencil_pinch (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y : Fin (N + 1) × Fin (N + 1),
      x.1 ≤ y.1 → x.2 ≤ y.2 →
      (∀ c : ℕ → Fin (N + 1) × Fin (N + 1), ∀ k : ℕ,
          IsStencilChain (Nat.sqrt N) c k → c 0 = x → c k = y →
          chainWeight c k / N ≤ gridTau x y) ∧
      (gridTau x y ≤ ε ∨
        ∃ c : ℕ → Fin (N + 1) × Fin (N + 1), ∃ k : ℕ,
          IsStencilChain (Nat.sqrt N) c k ∧ c 0 = x ∧ c k = y ∧
          gridTau x y - ε ≤ chainWeight c k / N) := by
  have hev : ∀ᶠ N : ℕ in atTop, errorTerm N < ε :=
    errorTerm_tendsto_zero.eventually (gt_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hev.and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN x y hu hv => ?_⟩
  obtain ⟨herr, hN1⟩ := hN₀ N hN
  constructor
  · exact fun c k hc h0 hk => chainWeight_div_le_gridTau hN1 c k hc h0 hk
  · rcases chain_approximates hN1 x y hu hv with h | ⟨c, k, hc, h0, hk, hw⟩
    · exact Or.inl (le_trans h herr.le)
    · exact Or.inr ⟨c, k, hc, h0, hk, by linarith⟩

end QIQTH.CausalStencil
