/-
  Operational record-capacity — the Holevo–Bekenstein bound (B0 foundation).

  The honest upgrade of QIQT-H's finite-record-COUNT layer from a finite-dim toy
  postulate to an *operational* distinguishability bound. The target capstone
  (`operational_record_capacity`) is

      (1 − ε) · log |ι|  ≤  Q + h₂(ε),     i.e.   log M_ε ≤ (Q + h₂(ε))/(1 − ε),

  for `M = |ι|` records ε-decodable by a common POVM under a relative-entropy /
  Holevo bound `Q`. This SURVIVES `EntropyNotCardinality` (it bounds recoverable
  mutual information, not support cardinality), and is finite as a *number* only
  under an imported energy cutoff — the Bekenstein / microcanonical bound.

  ⚠ HONEST SCOPE. This is a Holevo/Bekenstein-class bound — **standard holography,
  NOT new physics**. It does NOT derive the count from the area law, and it does
  NOT derive a `Q_R` different from standard generalized entropy (the cited
  frontier). See `OPERATIONAL_CAPACITY_PLAN.md` and `EntropyNotCardinality`.

  This file (B0): the binary entropy `h₂` and the finite record-discrimination
  model + the exact (ε=0) capacity helper. The quantitative Fano inequality (B1)
  and the Holevo glue (B2) are the next increments.
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import QIQTH.ShannonFano

namespace QIQTH
namespace OperationalCapacity

open scoped BigOperators

/-! ### B0.1 — binary (Shannon) entropy `h₂`, in nats -/

/-- Binary Shannon entropy in nats: `h₂(ε) = −ε log ε − (1−ε) log(1−ε)`
    (`= negMulLog ε + negMulLog (1−ε)`). This is the Fano penalty term. -/
noncomputable def binEntropy (ε : ℝ) : ℝ :=
  Real.negMulLog ε + Real.negMulLog (1 - ε)

@[simp] lemma binEntropy_zero : binEntropy 0 = 0 := by
  simp [binEntropy]

@[simp] lemma binEntropy_one : binEntropy 1 = 0 := by
  simp [binEntropy]

/-- `h₂` is symmetric under `ε ↦ 1−ε`. -/
lemma binEntropy_symm (ε : ℝ) : binEntropy (1 - ε) = binEntropy ε := by
  unfold binEntropy
  rw [add_comm]
  ring_nf

/-- `h₂(ε) ≥ 0` on `[0,1]` — both `negMulLog` terms are nonnegative there. -/
lemma binEntropy_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : 0 ≤ binEntropy ε := by
  have h0' : 0 ≤ 1 - ε := by linarith
  have h1' : 1 - ε ≤ 1 := by linarith
  exact add_nonneg (Real.negMulLog_nonneg h0 h1) (Real.negMulLog_nonneg h0' h1')

/-! ### B0.2 — the finite record-discrimination model -/

/-- A finite **record-discrimination model**: a finite record set `ι` with a
    classical decoding success profile `succ i ∈ [0,1]` (the probability that
    record `i`, prepared and measured by the common decoding POVM, is correctly
    identified). `ε` is the average error; `1 − ε` the average success. The
    quantum content (POVM, density matrices) enters only through the Holevo
    bound `Q` carried in the capacity theorems; this structure is the classical
    interface the Fano step consumes. -/
structure RecordModel (ι : Type*) [Fintype ι] where
  /-- Per-record decoding success probability. -/
  succ : ι → ℝ
  succ_nonneg : ∀ i, 0 ≤ succ i
  succ_le_one : ∀ i, succ i ≤ 1

namespace RecordModel

variable {ι : Type*} [Fintype ι] (M : RecordModel ι)

/-- Average decoding success under the uniform prior. -/
noncomputable def avgSucc : ℝ := (Fintype.card ι : ℝ)⁻¹ * ∑ i, M.succ i

/-- Average decoding error `ε = 1 − avgSucc`. -/
noncomputable def avgErr : ℝ := 1 - M.avgSucc

end RecordModel

/-! ### B0.3 — the exact (ε = 0) capacity helper

    The clean Bekenstein-class count bound in its simplest honest form: if the
    Holevo information of the `M` equiprobable records is bounded by `Q`
    (`log M ≤ Q` for perfectly-distinguishable records), then `M ≤ e^Q`. Pure
    `exp`-monotonicity — the substance is the Holevo bound `log M ≤ Q` (B2), and
    the ε-robustness is the Fano step (B1). Stated here so the capstone has its
    `ε = 0` corollary ready. -/

/-- **Exact record-count bound (ε = 0).** From `log M ≤ Q` (the Holevo bound for
    perfectly-distinguishable equiprobable records) the record count satisfies
    `M ≤ e^Q`. Holevo/Bekenstein-class; never claims to derive the count from the
    area law (see file header / `EntropyNotCardinality`). -/
theorem exact_record_capacity {M : ℝ} (hM : 0 < M) {Q : ℝ}
    (hlog : Real.log M ≤ Q) : M ≤ Real.exp Q := by
  calc M = Real.exp (Real.log M) := (Real.exp_log hM).symm
    _ ≤ Real.exp Q := Real.exp_le_exp.mpr hlog

end OperationalCapacity
end QIQTH
