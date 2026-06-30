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

end MaxEntropyCapacity
end QIQTH
