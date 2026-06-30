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

/-- **The termwise relative-entropy lower bound** `x − y ≤ x·log(x/y)` (the engine of every KL bound here):
    from `Real.log_le_sub_one_of_pos` applied to `y/x`. `x = 0` ⟹ `−y ≤ 0`; `x > 0` ⟹ `y > 0` and the log bound. -/
lemma mulLog_div_lower {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy : x ≠ 0 → 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0]; simp only [zero_mul]; linarith
  · have hyp : 0 < y := hy hpos.ne'
    have hlog : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hinv : Real.log (x / y) = - Real.log (y / x) := by rw [← Real.log_inv, inv_div]
    have hmul : x * Real.log (y / x) ≤ x * (y / x - 1) := mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
    have hcancel : x * (y / x - 1) = y - x := by field_simp
    rw [hinv]; nlinarith [hmul, hcancel]

/-- **Binary (2-point) relative entropy** `D₂(s‖r) = s log(s/r) + (1−s) log((1−s)/(1−r))`. The coarse-grained KL
    of the partition into "decoded correctly" (mass `s`) vs not, which lower-bounds the confusion-matrix
    mutual information in the Fano-free record-capacity route. -/
noncomputable def binaryKL (s r : ℝ) : ℝ :=
  s * Real.log (s / r) + (1 - s) * Real.log ((1 - s) / (1 - r))

/-- **Binary relative entropy is nonnegative.** Two applications of `mulLog_div_lower` to `(s,r)` and
    `(1−s, 1−r)`: the lower bounds sum to `(s−r) + ((1−s)−(1−r)) = 0`. -/
lemma binaryKL_nonneg {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    0 ≤ binaryKL s r := by
  have t1 : s - r ≤ s * Real.log (s / r) :=
    mulLog_div_lower hs0 (le_of_lt hr0) (fun _ => hr0)
  have t2 : (1 - s) - (1 - r) ≤ (1 - s) * Real.log ((1 - s) / (1 - r)) :=
    mulLog_div_lower (by linarith) (by linarith) (fun _ => by linarith)
  unfold binaryKL
  linarith [t1, t2]

/-- `s·log(s/r) = s·log s − s·log r` for `s ≥ 0`, `r ≠ 0`. Holds even at `s = 0` (both sides `0`) because of the
    leading `s` — sidesteps the `log(s/r) ≠ log s − log r` failure there. -/
lemma mul_log_div_split {s r : ℝ} (hs : 0 ≤ s) (hr : r ≠ 0) :
    s * Real.log (s / r) = s * Real.log s - s * Real.log r := by
  rcases eq_or_lt_of_le hs with h0 | hpos
  · rw [← h0]; simp
  · rw [Real.log_div hpos.ne' hr]; ring

/-- **The Fano-form success bound.** For `M > 1`, the binary relative entropy of the "decoded correctly"
    partition (success mass `s`, reference `1/M`) lower-bounds the Fano expression:
    `s·log M − h₂(1−s) ≤ D₂(s‖1/M)`. Exact identity `D₂(s‖1/M) = s·log M − h₂(1−s) − (1−s)·log(1−1/M)` plus
    `(1−s)·log(1−1/M) ≤ 0` (since `1−1/M ∈ (0,1]`, `1−s ≥ 0`). With `s = 1−ε` this is `(1−ε)log M − h₂(ε)`. -/
lemma binaryKL_success_bound {s M : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hM : 1 < M) :
    s * Real.log M - binEntropy (1 - s) ≤ binaryKL s M⁻¹ := by
  have hMpos : 0 < M := by linarith
  have hrne : (M⁻¹ : ℝ) ≠ 0 := by positivity
  have hM1 : (M⁻¹ : ℝ) < 1 := by rw [inv_lt_one₀ hMpos]; exact hM
  have h1r_pos : (0 : ℝ) < 1 - M⁻¹ := by linarith
  have h1r_le : (1 - M⁻¹ : ℝ) ≤ 1 := by
    have : (0 : ℝ) < M⁻¹ := by positivity
    linarith
  have h1rne : (1 - M⁻¹ : ℝ) ≠ 0 := ne_of_gt h1r_pos
  have hlog1r_nonpos : Real.log (1 - M⁻¹) ≤ 0 := Real.log_nonpos (le_of_lt h1r_pos) h1r_le
  have e1 : s * Real.log (s / M⁻¹) = s * Real.log s - s * Real.log M⁻¹ := mul_log_div_split hs0 hrne
  have e2 : (1 - s) * Real.log ((1 - s) / (1 - M⁻¹))
      = (1 - s) * Real.log (1 - s) - (1 - s) * Real.log (1 - M⁻¹) :=
    mul_log_div_split (by linarith) h1rne
  have hbin : binEntropy (1 - s) = -((1 - s) * Real.log (1 - s)) - s * Real.log s := by
    unfold binEntropy
    rw [show (1 : ℝ) - (1 - s) = s from by ring]
    simp only [Real.negMulLog]; ring
  have hlogr : Real.log M⁻¹ = - Real.log M := Real.log_inv M
  have hprod : (1 - s) * Real.log (1 - M⁻¹) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog1r_nonpos
  unfold binaryKL
  rw [e1, e2, hbin, hlogr]
  nlinarith [hprod]

/-! ### B1.4 — the log-sum inequality and binary coarse-graining (the data-processing side) -/

/-- `p·log(p/(q·c)) = p·log(p/q) − p·log c` for `p ≥ 0`, `q > 0` (when `p ≠ 0`), `c > 0`. The per-term identity
    behind the log-sum inequality (pull the common tilt `c` out of every term). -/
lemma mul_log_div_mul {p q c : ℝ} (hp : 0 ≤ p) (hq : p ≠ 0 → 0 < q) (hc : 0 < c) :
    p * Real.log (p / (q * c)) = p * Real.log (p / q) - p * Real.log c := by
  rcases eq_or_lt_of_le hp with h0 | hpos
  · rw [← h0]; simp
  · have hqp : 0 < q := hq hpos.ne'
    rw [Real.log_div hpos.ne' (mul_ne_zero hqp.ne' hc.ne'), Real.log_mul hqp.ne' hc.ne',
      Real.log_div hpos.ne' hqp.ne']
    ring

/-- **The log-sum inequality.** For nonnegative weights `p, q` on a finite set `s` (with `q` supporting `p`,
    `P = ∑p > 0`, `Q = ∑q > 0`): `P·log(P/Q) ≤ ∑ pₐ·log(pₐ/qₐ)`. Proof: apply `mulLog_div_lower` to each
    `(pₐ, qₐ·P/Q)` (lower bounds sum to `P − Q·(P/Q) = 0`), then pull the tilt `P/Q` out via `mul_log_div_mul`. -/
lemma logsum_le {α : Type*} (s : Finset α) (p q : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hq : ∀ a ∈ s, 0 ≤ q a)
    (hsupp : ∀ a ∈ s, p a ≠ 0 → 0 < q a)
    (hP : 0 < ∑ a ∈ s, p a) (hQ : 0 < ∑ a ∈ s, q a) :
    (∑ a ∈ s, p a) * Real.log ((∑ a ∈ s, p a) / (∑ a ∈ s, q a))
      ≤ ∑ a ∈ s, p a * Real.log (p a / q a) := by
  set P := ∑ a ∈ s, p a with hPdef
  set Q := ∑ a ∈ s, q a with hQdef
  set c := P / Q with hc
  have hcpos : 0 < c := div_pos hP hQ
  -- termwise lower bound from mulLog_div_lower at (pₐ, qₐ·c)
  have hterm : ∀ a ∈ s, p a - q a * c ≤ p a * Real.log (p a / (q a * c)) := by
    intro a ha
    refine mulLog_div_lower (hp a ha) (mul_nonneg (hq a ha) (le_of_lt hcpos)) ?_
    intro hpa; exact mul_pos (hsupp a ha hpa) hcpos
  have hsum : ∑ a ∈ s, (p a - q a * c) ≤ ∑ a ∈ s, p a * Real.log (p a / (q a * c)) :=
    Finset.sum_le_sum hterm
  -- left sum collapses: ∑(pₐ − qₐ·c) = P − Q·c = P − P = 0
  have hQc : Q * c = P := by rw [hc]; field_simp
  have hlhs : ∑ a ∈ s, (p a - q a * c) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hPdef, ← hQdef, hQc]; ring
  -- right sum pulls out the tilt: ∑ pₐ log(pₐ/(qₐc)) = ∑ pₐ log(pₐ/qₐ) − P·log c
  have hPc : P * Real.log c = ∑ a ∈ s, p a * Real.log c := by
    rw [← Finset.sum_mul, ← hPdef]
  have hrhs : ∑ a ∈ s, p a * Real.log (p a / (q a * c))
      = (∑ a ∈ s, p a * Real.log (p a / q a)) - P * Real.log c := by
    rw [hPc, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a ha => mul_log_div_mul (hp a ha) (hsupp a ha) hcpos)
  rw [hlhs, hrhs] at hsum
  -- 0 ≤ ∑ pₐ log(pₐ/qₐ) − P log c, and log c = log(P/Q)
  have : P * Real.log c = P * Real.log (P / Q) := by rw [hc]
  linarith [hsum]

/-- **Binary coarse-graining (data-processing).** For distributions `p, q` on a finite type and an event `A`
    (with both `A` and `Aᶜ` carrying positive `p`- and `q`-mass), the binary relative entropy of the
    coarse-grained `(A, Aᶜ)` law is at most the full relative entropy: `D₂(p(A)‖q(A)) ≤ ∑ pₐ log(pₐ/qₐ)`. Proof:
    `logsum_le` on `A` and on `Aᶜ`, then `∑_A + ∑_{Aᶜ} = ∑`. -/
lemma kl_partition_two {α : Type*} [Fintype α] [DecidableEq α] (p q : α → ℝ) (A : Finset α)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hsupp : ∀ a, p a ≠ 0 → 0 < q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hPA : 0 < ∑ a ∈ A, p a) (hPAc : 0 < ∑ a ∈ Aᶜ, p a)
    (hQA : 0 < ∑ a ∈ A, q a) (hQAc : 0 < ∑ a ∈ Aᶜ, q a) :
    binaryKL (∑ a ∈ A, p a) (∑ a ∈ A, q a) ≤ ∑ a, p a * Real.log (p a / q a) := by
  have hPcp : (1 : ℝ) - ∑ a ∈ A, p a = ∑ a ∈ Aᶜ, p a := by
    have h := Finset.sum_add_sum_compl A p; rw [hpsum] at h; linarith
  have hQcp : (1 : ℝ) - ∑ a ∈ A, q a = ∑ a ∈ Aᶜ, q a := by
    have h := Finset.sum_add_sum_compl A q; rw [hqsum] at h; linarith
  have hA := logsum_le A p q (fun a _ => hp a) (fun a _ => hq a) (fun a _ h => hsupp a h) hPA hQA
  have hAc := logsum_le Aᶜ p q (fun a _ => hp a) (fun a _ => hq a) (fun a _ h => hsupp a h) hPAc hQAc
  have hsplit : (∑ a ∈ A, p a * Real.log (p a / q a)) + (∑ a ∈ Aᶜ, p a * Real.log (p a / q a))
      = ∑ a, p a * Real.log (p a / q a) := Finset.sum_add_sum_compl A _
  unfold binaryKL
  rw [hPcp, hQcp]
  calc (∑ a ∈ A, p a) * Real.log ((∑ a ∈ A, p a) / (∑ a ∈ A, q a))
        + (∑ a ∈ Aᶜ, p a) * Real.log ((∑ a ∈ Aᶜ, p a) / (∑ a ∈ Aᶜ, q a))
      ≤ (∑ a ∈ A, p a * Real.log (p a / q a)) + (∑ a ∈ Aᶜ, p a * Real.log (p a / q a)) :=
        add_le_add hA hAc
    _ = ∑ a, p a * Real.log (p a / q a) := hsplit

/-! ### B3 — the operational record-capacity capstone -/

/-- **Operational record-capacity capstone (the Holevo–Bekenstein bound).** With error `ε := 1 − s`, if the
    binary "decoded-correctly" relative entropy is bounded, `D₂(s‖1/M) ≤ Q`, then
    `s·log M ≤ Q + h₂(1−s)`, i.e. **`(1 − ε)·log M ≤ Q + h₂(ε)`**, i.e. `log M_ε ≤ (Q + h₂(ε))/(1 − ε)`.

    The hypothesis `D₂(s‖1/M) ≤ Q` is the **data-processed Holevo / fixed-reference relative-entropy bound**: by
    `kl_partition_two` (binary coarse-graining to the "decoded correctly" event), `D₂(s‖1/M)` is at most the full
    confusion-matrix mutual information `I(T) = ∑ P log(P/R)`, which the Holevo bound bounds by `Q`. So the carried
    hypothesis is the Holevo bound after one classical coarse-graining — `Q` is the fixed-reference relative
    entropy `D(ω‖σ_R)`, never an area datum.

    ⚠ Holevo/Bekenstein-class — **NOT new physics**. It does **NOT** derive the count from the area law
    (`EntropyNotCardinality`: a bare `S(ρ_R) ≤ Q` does not bound the count — here the bound is on the *Holevo
    information of the decoding ensemble*). Finite as a *number* only under an imported energy cutoff (B4 =
    Bekenstein/microcanonical). Distinctive only via a `Q_R` differing from standard generalized entropy
    (the cited frontier). -/
theorem record_capacity_of_binaryKL_bound {s M Q : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hM : 1 < M)
    (hbound : binaryKL s M⁻¹ ≤ Q) :
    s * Real.log M ≤ Q + binEntropy (1 - s) := by
  have h := binaryKL_success_bound hs0 hs1 hM
  linarith

end OperationalCapacity
end QIQTH
