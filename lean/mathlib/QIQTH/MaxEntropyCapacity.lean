/-
  The distinctive-`Q_R` frontier — the max-entropy bridge postulate + the capacity-of-entanglement gap.

  QIQT-H's only genuinely-distinctive open target is a capacity `Q_R` that differs from standard generalized
  entropy `S_gen = A/4G + S_bulk`. The settled verdict (GPT-5.5-pro scoping, 2026-07-01):

    • Such a `Q_R` CANNOT be DERIVED from QIQT-H's principles — conditional no-go: area/JLMS use the von Neumann
      entropy `S_vN`, the finite COUNT is independent of `S_vN` (`EntropyNotCardinality`), and `λ` is inert.
    • It is possible ONLY by ADDING the explicit **max-entropy bridge postulate**: gravity's capacity is `S_max`
      (= log-count = log-rank = the finite record COUNT), NOT `S_vN`.
    • That postulate makes the falsifiable, distinctive prediction `Q_R − S_gen = S_max − S_vN ≥ 0`, governed in
      the continuum by the **capacity of entanglement** `√V_gen` (modular variance) — finite-size Page-time / QES
      shifts.

  ⚠ HONEST SCOPE. The bridge is a **NEW POSTULATE, NOT a derivation**. This file proves: the count/entropy GAP and
  its nonnegativity (B1), the conditional **no-go** that `S_vN` (the area) does not fix `S_max` (the count) (B2),
  the **capacity of entanglement** and its properties (B3), and the **conditional** distinctive prediction under
  the postulate (B4). It NEVER claims QIQT-H derives a distinctive `Q_R`, never claims QG or the value of `G`; the
  continuum `√V_gen` coefficient and `G` are cited frontiers. See `QR_FRONTIER_PLAN.md` and `EntropyNotCardinality`.

  This file (B0+B1): the two entropies (`Smax` = log-count, `Svn` = Shannon/von Neumann) and the gap `≥ 0`.
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic
import QIQTH.RecordContract

namespace QIQTH
namespace MaxEntropyCapacity

open scoped BigOperators

/-- The **max-entropy / log-count capacity** `S_max = log(dim)` — the log of the number of distinguishable records
    (the COUNT layer's capacity; Rényi-0 / max entropy at full rank). This is what the max-entropy bridge
    postulate proposes gravity's capacity is — *instead of* the von Neumann entropy. -/
noncomputable def Smax (ι : Type*) [Fintype ι] : ℝ := Real.log (Fintype.card ι)

/-- The **von Neumann / Shannon entropy** of the spectrum `p` (`= −∑ pᵢ log pᵢ`) — what `S_gen` and the area
    measure (Rényi-1). -/
noncomputable def Svn {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  QIQTH.BranchLedger.Shannon Finset.univ p

/-- The **count/entropy gap** `S_max − S_vN` — the distinctive quantity the max-entropy bridge postulate predicts
    as `Q_R − S_gen`. The finite shadow of the continuum `√V_gen` (capacity-of-entanglement) prediction. -/
noncomputable def gap {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ := Smax ι - Svn p

/-- **`S_vN ≤ S_max`** — the von Neumann entropy is at most the log-count (Jensen/Gibbs, `shannon_le_log_card`).
    Equality iff the spectrum is flat (maximally mixed). -/
theorem smax_ge_svn {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) : Svn p ≤ Smax ι := by
  unfold Svn Smax
  exact QIQTH.RecordContract.shannon_le_log_card p hp h1

/-- **The count/entropy gap is nonnegative** — `S_max − S_vN ≥ 0`. The distinctive `Q_R − S_gen` the postulate
    predicts is `≥ 0`, strictly positive off the flat (maximally-mixed) spectrum. -/
theorem gap_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) : 0 ≤ gap p := by
  unfold gap; linarith [smax_ge_svn p hp h1]

/-! ### B2 — the conditional no-go: the area (`S_vN`) does not fix the count (`S_max`) -/

/-- **The no-go forcing the postulate: `S_vN` does NOT determine `S_max`.** For every dimension `N ≥ 1`, a PURE
    state (`S_vN = 0`) on `Fin N` has `S_max = log N`. So a fixed von Neumann entropy (here `0`) is compatible
    with an *arbitrarily large* log-count `S_max` (as `N → ∞`). Hence `S_vN` — what the area / `S_gen` measures —
    does **not** determine or bound the count `S_max`: a count-based `Q_R` is *independent data*, not derivable
    from the geometric `S_gen`. This is exactly why a distinctive `Q_R` requires an *added* postulate, not a
    derivation (the sharpest `EntropyNotCardinality` for the max-entropy capacity). -/
theorem svn_underdetermines_smax (N : ℕ) (hN : 0 < N) :
    ∃ p : Fin N → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ Svn p = 0 ∧ Smax (Fin N) = Real.log N := by
  classical
  refine ⟨fun i => if i = ⟨0, hN⟩ then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro i
    show (0 : ℝ) ≤ if i = (⟨0, hN⟩ : Fin N) then 1 else 0
    split_ifs <;> norm_num
  · simp
  · unfold Svn
    rw [QIQTH.RecordContract.shannon_eq_sum_negMulLog]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    show Real.negMulLog (if i = (⟨0, hN⟩ : Fin N) then 1 else 0) = 0
    split_ifs <;> simp [Real.negMulLog]
  · unfold Smax; rw [Fintype.card_fin]

/-! ### B3 — the capacity of entanglement (the prediction's quantity) -/

/-- The **capacity of entanglement** `V_gen = ∑ pᵢ(log pᵢ)² − (∑ pᵢ log pᵢ)² = Var_p(−log p)` — the variance of
    the surprisal / modular Hamiltonian. The continuum `√V_gen` governs the distinctive `Q_R − S_gen` shift the
    max-entropy bridge postulate predicts (finite-size Page-time / QES shifts); this is its finite-dim form. -/
noncomputable def capEnt {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  (∑ i, p i * (Real.log (p i)) ^ 2) - (∑ i, p i * Real.log (p i)) ^ 2

/-- **The capacity of entanglement is the variance** `∑ pᵢ(log pᵢ − μ)²` with `μ = ∑ pᵢ log pᵢ`. -/
lemma capEnt_eq_variance {ι : Type*} [Fintype ι] (p : ι → ℝ) (h1 : ∑ i, p i = 1) :
    capEnt p = ∑ i, p i * (Real.log (p i) - (∑ j, p j * Real.log (p j))) ^ 2 := by
  set μ := ∑ j, p j * Real.log (p j) with hμ
  have e : ∀ i, p i * (Real.log (p i) - μ) ^ 2
      = p i * (Real.log (p i)) ^ 2 - μ * (2 * (p i * Real.log (p i))) + μ ^ 2 * p i :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => e i)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h2 : ∑ i, μ * (2 * (p i * Real.log (p i))) = 2 * μ ^ 2 := by
    rw [← Finset.mul_sum]; rw [show ∑ i, 2 * (p i * Real.log (p i)) = 2 * μ from by
      rw [← Finset.mul_sum, ← hμ]]; ring
  have h3 : ∑ i, μ ^ 2 * p i = μ ^ 2 := by rw [← Finset.mul_sum, h1, mul_one]
  rw [h2, h3]
  unfold capEnt
  rw [← hμ]; ring

/-- **The capacity of entanglement is nonnegative** (`V_gen ≥ 0`) — it is a variance. -/
theorem capEnt_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) : 0 ≤ capEnt p := by
  rw [capEnt_eq_variance p h1]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))

/-- **`V_gen = 0` iff the surprisal is constant on the support** — i.e. the spectrum is flat (maximally mixed):
    every `pᵢ` is either `0` or has `log pᵢ = μ` (`μ = ∑ p log p`). So the capacity of entanglement vanishes
    exactly when there is *no* distinctive shift — the maximally-mixed sector. -/
theorem capEnt_eq_zero_iff {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    capEnt p = 0 ↔ ∀ i, p i = 0 ∨ Real.log (p i) = (∑ j, p j * Real.log (p j)) := by
  rw [capEnt_eq_variance p h1,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))]
  constructor
  · intro h i
    rcases mul_eq_zero.mp (h i (Finset.mem_univ i)) with h0 | hsq
    · exact Or.inl h0
    · exact Or.inr (by have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq; linarith)
  · intro h i _
    rcases h i with h0 | hlog
    · rw [h0]; ring
    · rw [hlog]; ring

/-! ### B4 — the max-entropy bridge POSTULATE + the conditional distinctive prediction -/

/-- **The MAX-ENTROPY BRIDGE POSTULATE** (a typeclass — **NEVER a Lean `axiom`**, exactly like
    `HolographicCapacityBound`): gravity's reconstruction capacity `Q_R` is the **max-entropy / log-count**
    `S_max` (the finite record COUNT), and standard generalized entropy `S_gen` is the von Neumann entropy
    `S_vN` of the spectrum. This is an ADDED assumption — it is **not derivable** (`svn_underdetermines_smax`:
    the area fixes `S_vN`, not the count) and is the *only* route to a distinctive `Q_R`. -/
class MaxEntropyCapacity {ι : Type*} [Fintype ι] (p : ι → ℝ) (Q_R S_gen : ℝ) : Prop where
  /-- The postulate: capacity = the max-entropy / log-count (not `S_vN`). -/
  capacity_is_max : Q_R = Smax ι
  /-- Standard generalized entropy is the von Neumann entropy. -/
  sgen_is_vn : S_gen = Svn p

/-- **The distinctive prediction — CONDITIONAL on the bridge postulate (NOT a derivation).** *Given* the
    max-entropy postulate, the capacity differs from standard generalized entropy by exactly the count/entropy
    gap: `Q_R − S_gen = S_max − S_vN = gap p ≥ 0`. This is the finite shadow of the continuum `√V_gen`
    (capacity-of-entanglement) prediction; the shift vanishes exactly on the flat (maximally-mixed) spectrum
    (`capEnt_eq_zero_iff`), and is strictly positive otherwise. It holds **only given the postulate** — QIQT-H
    does not *derive* a distinctive `Q_R`; it *posits* one and derives this consequence. The continuum `√V_gen`
    coefficient and the value of `G` are cited frontiers. -/
theorem distinctive_gap {ι : Type*} [Fintype ι] (p : ι → ℝ) (Q_R S_gen : ℝ)
    [h : MaxEntropyCapacity p Q_R S_gen] (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    Q_R - S_gen = gap p ∧ 0 ≤ Q_R - S_gen := by
  have hg : Q_R - S_gen = gap p := by
    unfold gap; rw [h.capacity_is_max, h.sgen_is_vn]
  exact ⟨hg, by rw [hg]; exact gap_nonneg p hp h1⟩

end MaxEntropyCapacity
end QIQTH
