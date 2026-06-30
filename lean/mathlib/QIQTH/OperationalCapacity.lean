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

/-- **The equiprobable ensemble's Shannon entropy is `log M`.** For a finite
    nonempty record set `s` (`M = |s|`), the uniform record law `p_i = 1/M` has
    `H(p) = log M`. This is the Holevo information `χ = S(ρ̄) − avg S(ρ_i)` of `M`
    equiprobable *perfectly-distinguishable* records (each pure, `S(ρ_i)=0`,
    `ρ̄` maximally mixed on the `M`-dim support). -/
lemma H_uniform {ι : Type*} (s : Finset ι) (hs : s.Nonempty) :
    ShannonFano.H s (fun _ => (s.card : ℝ)⁻¹) = Real.log s.card := by
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  have hne : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  unfold ShannonFano.H
  rw [Finset.sum_const, nsmul_eq_mul, Real.log_inv]
  field_simp

/-- **Exact operational record-capacity theorem (ε = 0).** If the Holevo /
    relative-entropy information `χ` of `M = |s|` equiprobable
    perfectly-distinguishable records is bounded by `Q` — and for such records
    `χ = H(uniform) = log M` (`H_uniform`) — then the record count obeys
    `M ≤ e^Q`. The bound `Q` is the **carried** Holevo / fixed-reference
    relative-entropy bound (the `D(ω‖σ_R) ≤ Q` input); the theorem turns it into
    a record-*count* bound for the distinguishable case.

    ⚠ Holevo/Bekenstein-class — **NOT new physics**, and it does **NOT** derive
    the count from the area law (`EntropyNotCardinality`: a bare entropy bound
    does not bound cardinality — here the count bound holds because `Q` bounds the
    *Holevo information of the distinguishable ensemble*, which equals `log M`,
    not merely some `S(ρ_R) ≤ Q`). The ε > 0 robust version needs the Fano step. -/
theorem exact_distinguishable_capacity {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {Q : ℝ} (hcap : ShannonFano.H s (fun _ => (s.card : ℝ)⁻¹) ≤ Q) :
    (s.card : ℝ) ≤ Real.exp Q := by
  have hpos : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  rw [H_uniform s hs] at hcap
  exact exact_record_capacity hpos hcap

/-! ### B1.1 — classical relative entropy (Gibbs inequality), the confusion-matrix workhorse

    The shortest rigorous path to the ε > 0 capstone (GPT-5.5-pro, 2026-06-30) avoids conditional entropy
    entirely: bound the decoding **confusion matrix**'s mutual information below via one binary coarse-graining to
    the event "decoded correctly," using only classical KL-nonnegativity + log-sum. The base lemma is the classical
    **Gibbs inequality** `∑ aᵢ log(aᵢ/bᵢ) ≥ 0`, proved from `log t ≤ t − 1`. -/

/-- **Classical relative entropy is nonnegative (Gibbs inequality).** For finite probability distributions `a`,
    `b` (with `b` supporting `a`), `∑ aᵢ log(aᵢ/bᵢ) ≥ 0`. Proof: the termwise bound `aᵢ − bᵢ ≤ aᵢ log(aᵢ/bᵢ)`
    (from `Real.log_le_sub_one_of_pos` applied to `bᵢ/aᵢ`), summed, with `∑(aᵢ−bᵢ) = 1−1 = 0`. The workhorse of
    the confusion-matrix record-capacity route. -/
lemma kl_nonneg {α : Type*} [Fintype α] (a b : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsupp : ∀ i, a i ≠ 0 → 0 < b i)
    (hasum : ∑ i, a i = 1) (hbsum : ∑ i, b i = 1) :
    0 ≤ ∑ i, a i * Real.log (a i / b i) := by
  have term : ∀ i ∈ Finset.univ, a i - b i ≤ a i * Real.log (a i / b i) := by
    intro i _
    rcases eq_or_lt_of_le (ha i) with h0 | hpos
    · -- a i = 0: LHS = −b i ≤ 0 = RHS
      rw [← h0]
      simp only [zero_mul]
      linarith [hb i]
    · -- a i > 0 ⟹ b i > 0
      have hbi : 0 < b i := hsupp i hpos.ne'
      have hlog : Real.log (b i / a i) ≤ b i / a i - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hinv : Real.log (a i / b i) = - Real.log (b i / a i) := by
        rw [← Real.log_inv, inv_div]
      have hmul : a i * Real.log (b i / a i) ≤ a i * (b i / a i - 1) :=
        mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
      have hcancel : a i * (b i / a i - 1) = b i - a i := by
        field_simp
      rw [hinv]
      nlinarith [hmul, hcancel]
  have hsum : ∑ i, (a i - b i) ≤ ∑ i, a i * Real.log (a i / b i) :=
    Finset.sum_le_sum term
  have hzero : ∑ i, (a i - b i) = 0 := by
    rw [Finset.sum_sub_distrib, hasum, hbsum]; ring
  linarith [hsum, hzero]

end OperationalCapacity
end QIQTH
