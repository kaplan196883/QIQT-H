/-
  RECORD UNRAVELING — the exact jump-process unraveling of the record channel:
  candidate 6 = E_λ[candidate 3], Chapman–Kolmogorov, the Born law, and BORN FORCED
  (RC campaign, brick RC3).

  Brick RC1 (`RecordChannel.lean`) built the record channel
  `T_s = e^{−s}·id + (1 − e^{−s})·dephase` on the held finite code.  THIS brick proves that
  the channel unravels EXACTLY as an (exponential jump clock, Born-selected record) process:

  • THE EXACT UNRAVELING — `unraveling_exact`:
        `T_s A = e^{−s}·A + Σ_n w_n(s)·|n⟩⟨n|`,   `w_n(s) = (1 − e^{−s})·(A n n).re`
    — with probability `e^{−s}` no record has formed (state unchanged); with probability
    `w_n(s)` the record `n` has formed (state = the pure record `recordState n`).  The
    channel IS the λ-average of the jump process: boundary-dynamics candidate 6 =
    E_λ[candidate 3], as a theorem (the §6 ⟷ §3 dictionary entry of
    `BOUNDARY_DYNAMICS_CANDIDATES.md`).
  • A GENUINE PROBABILITY LAW — `jumpWeight_nonneg`, `jumpWeight_sum`, `noJump_add_jump`:
    for a density the (no-jump, jump-to-n) weights are nonnegative and sum to 1.
  • CHAPMAN–KOLMOGOROV — `Tsem_diag_invariant`, `jumpWeight_Tsem`, `jump_law_compose`:
    the record distribution is invariant along the flow and the two-time composition
    reproduces the one-time law, `w_n(s) + e^{−s}·w_n(t) = w_n(s + t)` — the jump process
    is a consistent Markov unraveling (the finite shape of the held Kolmogorov-consistency
    layer, `CoarseGrainNaturality`; consistent with RC1's `Tsem_add`).
  • THE BORN READING — `jump_is_born`, `bornW_recordState`, `record_povm_complete`:
    conditioned on jumping, the record-selection law IS the Born law of the record POVM
    (the diagonal matrix units, a complete family of PSD effects):
    `w_n(s) = (1 − e^{−s})·bornW A (recordState n)` via the held `bornW` — the "rates =
    Born" entry of the 6 ⟷ 3 dictionary, as a theorem.
  • BORN FORCED — `unraveling_weights_unique`: ANY record-diagonal unraveling of the record
    channel (`T_s A = e^{−s}·A + Σ_n v_n(s)·recordState n`) MUST use exactly the Born
    weights, `v_n(s) = w_n(s)`.  At this channel the jump law is FORCED, not chosen — the
    finite answer to the named circularity risk of `SelectionDynamics.lean` (if the only
    equivariant μ is |Ψ|² the step is circular) and of `RC_CAMPAIGN_PLAN.md`.
  • EQUIVARIANCE — `jumpWeight_submatrix`, `jump_law_equivariant`, `recordState_submatrix`:
    relabeling the records pushes the jump law forward — the path-level shape of Gate 3's
    `equivariant_enforcement_preserves_invariance` (CITED, not imported).

  THE λ-READING.  The jump time and the selected record are exactly QIQT-H's λ — the
  actuality selector: the channel is the λ-average of single-outcome record formations,
  and single-world actuality is ONE sample path of the unraveling.

  ⚠ MANDATORY FIREWALL.  Born is forced GIVEN the channel — which was built in the record
  basis from the state; this does NOT derive Born ab initio.  The non-circularity question
  moves one level up (why THIS channel/basis — the einselection input of RC1's firewall).
  The unraveling is a finite two-time law, NOT a continuum stochastic process: no
  filtration, no SDE, no path σ-algebra beyond the finite compositions proved here.
  Finite, single code corner; the record basis is an INPUT.  NOT bulk reconstruction, NOT
  the strong holographic principle, NOT quantum gravity.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.RecordChannel
import QIQTH.RecordEquilibrium
import QIQTH.CoarseGrainNaturality

namespace QIQTH.RecordUnraveling

open QIQTH.QuantumEntropy QIQTH.Keystone QIQTH.Entropy QIQTH.RecordChannel
open QIQTH.CoarseGrainNaturality (bornW)
open scoped ComplexOrder

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## RC3.0 — diagonal entries of a PSD matrix are nonnegative reals -/

/-- Diagonal entries of a positive-semidefinite matrix have nonnegative real part. -/
theorem posSemidef_diag_re_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (n : ι) :
    0 ≤ (A n n).re := by
  have h : (0 : ℂ) ≤ A n n := hA.diag_nonneg (i := n)
  simpa using (Complex.le_def.mp h).1

/-- Diagonal entries of a positive-semidefinite matrix are REAL:
    `A n n = ((A n n).re : ℂ)` — the bridge between the complex diagonal of the state and
    the real jump weights. -/
theorem posSemidef_diag_real {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (n : ι) :
    A n n = ((A n n).re : ℂ) := by
  have h : (0 : ℂ) ≤ A n n := hA.diag_nonneg (i := n)
  have him : (A n n).im = 0 := by simpa using ((Complex.le_def.mp h).2).symm
  exact Complex.ext (by simp) (by simp [him])

/-! ## RC3.1 — the pure record states -/

/-- **The pure record state** `|n⟩⟨n|`: the diagonal indicator matrix at record `n` — the
    state of the world AFTER the jump has selected record `n`.  (Defined as a diagonal to
    ride RC1's diagonal toolkit.) -/
def recordState (n : ι) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun m => if m = n then 1 else 0)

/-- Entry formula for the record state. -/
theorem recordState_apply (n m k : ι) :
    recordState n m k = if m = k then (if m = n then (1 : ℂ) else 0) else 0 := by
  rw [recordState, Matrix.diagonal_apply]

/-- Diagonal entries of the record state: the indicator of `n`. -/
theorem recordState_apply_diag (n m : ι) :
    recordState n m m = if m = n then (1 : ℂ) else 0 := by
  rw [recordState_apply, if_pos rfl]

/-- Off-diagonal entries of the record state vanish (it is a record). -/
theorem recordState_apply_ne (n : ι) {m k : ι} (h : m ≠ k) : recordState n m k = 0 := by
  rw [recordState_apply, if_neg h]

/-- The record state is normalized: `tr |n⟩⟨n| = 1`. -/
theorem recordState_trace (n : ι) : (recordState n).trace = 1 := by
  rw [recordState, Matrix.trace_diagonal]
  simp

/-- The record state is positive semidefinite (a `{0,1}` diagonal). -/
theorem recordState_posSemidef (n : ι) : (recordState n).PosSemidef := by
  rw [recordState]
  refine Matrix.posSemidef_diagonal_iff.mpr fun m => ?_
  by_cases h : m = n
  · rw [if_pos h]; exact zero_le_one
  · rw [if_neg h]

/-- **The record state is a density** — the jump targets are genuine states. -/
theorem recordState_isDensity (n : ι) : IsDensity (recordState n) :=
  ⟨recordState_posSemidef n, recordState_trace n⟩

/-- The record state is fixed by the record readout (it is diagonal). -/
theorem dephase_recordState (n : ι) : dephase (recordState n) = recordState n := by
  rw [recordState]; exact dephase_diagonal _

/-- **The record states are record equilibria** in the sense of RC2
    (`RecordEquilibrium.IsRecordEquilibrium`): the jump targets are exactly the stationary
    configurations of the boundary dynamics. -/
theorem recordState_isRecordEquilibrium (n : ι) :
    QIQTH.RecordEquilibrium.IsRecordEquilibrium (recordState n) :=
  dephase_recordState n

/-- The record states are stationary under the record channel at every time. -/
theorem Tsem_recordState (s : ℝ) (n : ι) : Tsem s (recordState n) = recordState n :=
  Tsem_of_dephase_eq s (dephase_recordState n)

/-- **The record POVM is complete**: `Σ_n |n⟩⟨n| = 1` — the record states, read as
    EFFECTS, form a genuine POVM (PSD by `recordState_posSemidef`, complete here). -/
theorem record_povm_complete : ∑ n : ι, recordState n = (1 : Matrix ι ι ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq]
    calc ∑ k, recordState k i i = ∑ k, (if i = k then (1 : ℂ) else 0) :=
          Finset.sum_congr rfl fun k _ => recordState_apply_diag k i
      _ = 1 := by simp
  · rw [Matrix.one_apply_ne h]
    exact Finset.sum_eq_zero fun k _ => recordState_apply_ne k h

/-! ## RC3.2 — the jump weights: a genuine probability law -/

/-- **The jump weight** `w_n(s) = (1 − e^{−s})·(A n n).re`: the probability that by time
    `s` the jump clock has rung AND the record `n` has been selected. -/
noncomputable def jumpWeight (s : ℝ) (A : Matrix ι ι ℂ) (n : ι) : ℝ :=
  (1 - Real.exp (-s)) * (A n n).re

/-- Jump weights are nonnegative (PSD state, forward time). -/
theorem jumpWeight_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {s : ℝ} (hs : 0 ≤ s)
    (n : ι) : 0 ≤ jumpWeight s A n :=
  mul_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)))
    (posSemidef_diag_re_nonneg hA n)

/-- The diagonal of a density sums (in real parts) to 1. -/
theorem sum_diag_re {A : Matrix ι ι ℂ} (h : IsDensity A) : ∑ n, (A n n).re = 1 := by
  have h1 : ∑ n, A n n = 1 := by
    have h0 := h.trace_one
    rw [Matrix.trace] at h0
    exact h0
  have h2 := congrArg Complex.re h1
  rw [Complex.re_sum] at h2
  simpa using h2

/-- **The total jump probability**: for a density, `Σ_n w_n(s) = 1 − e^{−s}` — the
    probability that the jump clock has rung by time `s`, independent of the state's
    coherences. -/
theorem jumpWeight_sum {A : Matrix ι ι ℂ} (h : IsDensity A) (s : ℝ) :
    ∑ n, jumpWeight s A n = 1 - Real.exp (-s) := by
  simp only [jumpWeight]
  rw [← Finset.mul_sum, sum_diag_re h, mul_one]

/-- **The (no-jump, jump-to-n) law is a genuine probability distribution**:
    `e^{−s} + Σ_n w_n(s) = 1`. -/
theorem noJump_add_jump {A : Matrix ι ι ℂ} (h : IsDensity A) (s : ℝ) :
    Real.exp (-s) + ∑ n, jumpWeight s A n = 1 := by
  rw [jumpWeight_sum h s]; ring

/-! ## RC3.3 — THE EXACT UNRAVELING: candidate 6 = E_λ[candidate 3] -/

/-- **THE EXACT UNRAVELING — the record channel IS the λ-average of the jump process.**
    For every PSD state `A` and every time `s`,

        `T_s A = e^{−s}·A + Σ_n w_n(s)·recordState n`,

    with `w_n(s) = (1 − e^{−s})·(A n n).re` the jump weights: with probability `e^{−s}` no
    record has formed (the state is unchanged); with probability `w_n(s)` the record `n`
    has formed (the state is the pure record `|n⟩⟨n|`).  Boundary-dynamics candidate 6 =
    E_λ[candidate 3], as a theorem (`BOUNDARY_DYNAMICS_CANDIDATES.md` §6 ⟷ §3): the jump
    time and the selected record are exactly QIQT-H's λ, and single-world actuality is one
    sample path.  (PSD is used only to identify the complex diagonal `A n n` with its real
    part — the weights are REAL probabilities.) -/
theorem unraveling_exact (s : ℝ) {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    Tsem s A = Real.exp (-s) • A + ∑ n, jumpWeight s A n • recordState n := by
  ext n m
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply]
  by_cases h : n = m
  · subst h
    have hsum : ∑ k, (jumpWeight s A k • recordState k) n n
        = ((jumpWeight s A n : ℝ) : ℂ) := by
      rw [Finset.sum_eq_single n
        (fun k _ hk => by
          rw [Matrix.smul_apply, recordState_apply_diag, if_neg (Ne.symm hk), smul_zero])
        (fun hn => absurd (Finset.mem_univ n) hn),
        Matrix.smul_apply, recordState_apply_diag, if_pos rfl, Complex.real_smul, mul_one]
    rw [Tsem_apply_eq, hsum, Complex.real_smul, jumpWeight]
    rw [posSemidef_diag_real hA n]
    push_cast [Complex.ofReal_re]
    ring
  · rw [Tsem_apply_ne s A h, Complex.real_smul,
      Finset.sum_eq_zero fun k _ => by
        rw [Matrix.smul_apply, recordState_apply_ne k h, smul_zero],
      add_zero]

/-! ## RC3.4 — Chapman–Kolmogorov: the two-time law refines consistently -/

/-- The record ledger is frozen along the flow (re-export of RC1's `Tsem_apply_eq` under
    its unraveling name): the diagonal — hence the jump distribution — never moves. -/
theorem Tsem_diag_invariant (s : ℝ) (A : Matrix ι ι ℂ) (n : ι) :
    Tsem s A n n = A n n :=
  Tsem_apply_eq s A n

/-- **The jump distribution is time-invariant along the flow**: restarting the unraveling
    from the evolved state uses the SAME record weights. -/
theorem jumpWeight_Tsem (s t : ℝ) (A : Matrix ι ι ℂ) (n : ι) :
    jumpWeight t (Tsem s A) n = jumpWeight t A n := by
  simp only [jumpWeight, Tsem_apply_eq]

/-- **THE CHAPMAN–KOLMOGOROV LAW of the jump process**: P(record n by `s+t`) =
    P(record n in `[0,s]`) + P(no jump by `s`)·P(record n in the remaining `t`):

        `w_n(s) + e^{−s}·w_n(t) = w_n(s + t)`.

    Together with `unraveling_exact` and `jumpWeight_Tsem`, the jump process is a genuine
    Markov unraveling whose path law is consistent under time refinement — the finite shape
    of the held Kolmogorov-consistency layer (`CoarseGrainNaturality`), consistent with
    RC1's semigroup law `Tsem_add`. -/
theorem jump_law_compose (s t : ℝ) (A : Matrix ι ι ℂ) (n : ι) :
    jumpWeight s A n + Real.exp (-s) * jumpWeight t A n = jumpWeight (s + t) A n := by
  simp only [jumpWeight]
  rw [show -(s + t) = -s + -t from by ring, Real.exp_add]
  ring

/-! ## RC3.5 — THE BORN READING: the jump law is the Born law of the record POVM -/

/-- Trace against a record effect extracts the diagonal entry:
    `tr(A · |n⟩⟨n|) = A n n`. -/
theorem trace_mul_recordState (A : Matrix ι ι ℂ) (n : ι) :
    (A * recordState n).trace = A n n := by
  have hdiag : ∀ i, (A * recordState n) i i = if i = n then A n n else 0 := by
    intro i
    rw [recordState, Matrix.mul_diagonal]
    by_cases h : i = n
    · subst h; rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Matrix.trace]
  calc ∑ i, (A * recordState n).diag i = ∑ i, (if i = n then A n n else 0) :=
        Finset.sum_congr rfl fun i _ => (Matrix.diag_apply _ i).trans (hdiag i)
    _ = A n n := by simp

/-- **The Born weight of a record effect is the diagonal entry**:
    `bornW A (recordState n) = (A n n).re` — the held `bornW` kernel
    (`CoarseGrainNaturality`) evaluated on the record POVM. -/
theorem bornW_recordState (A : Matrix ι ι ℂ) (n : ι) :
    bornW A (recordState n) = (A n n).re := by
  rw [bornW, trace_mul_recordState]

/-- **THE BORN READING — conditioned on jumping, record selection IS the Born law.**
    The jump weight factors as (probability the clock rang) × (Born weight of the record
    effect): `w_n(s) = (1 − e^{−s})·bornW A (recordState n)`.  This is the "rates = Born"
    entry of the candidate 6 ⟷ 3 dictionary, as a theorem — and it ties the unraveling to
    the held Kolmogorov-consistency layer: the record POVM is complete
    (`record_povm_complete`), so the conditional record distribution is a genuine Born
    probability vector of `CoarseGrainNaturality`'s consistent system. -/
theorem jump_is_born (s : ℝ) (A : Matrix ι ι ℂ) (n : ι) :
    jumpWeight s A n = (1 - Real.exp (-s)) * bornW A (recordState n) := by
  rw [bornW_recordState, jumpWeight]

/-! ## RC3.6 — BORN FORCED: the weights of any record-diagonal unraveling are unique -/

/-- **BORN FORCED — the honest circularity answer.**  ANY record-diagonal unraveling of
    the record channel must use exactly the Born weights: if real weights `v` satisfy

        `T_s A = e^{−s}·A + Σ_n v_n(s)·recordState n`   for all `s ≥ 0`,

    then `v_n(s) = jumpWeight s A n = (1 − e^{−s})·(A n n).re`.  At this channel the jump
    law is FORCED, not chosen — the finite answer to the named circularity risk of
    `SelectionDynamics.lean` ("if the only equivariant μ is |Ψ|² the step is circular") and
    of `RC_CAMPAIGN_PLAN.md`: matching the frozen diagonal (`Tsem_apply_eq`) at entry
    `(n,n)` forces `(v_n(s) : ℂ) = (1 − e^{−s})·A n n`, and taking real parts pins `v`.

    ⚠ HONEST: Born is forced GIVEN the channel — which was built in the record basis from
    the state; this does NOT derive Born ab initio.  The non-circularity question moves one
    level up: why THIS channel/basis (the einselection input of RC1's firewall).
    Documented, not hidden.  (No PSD hypothesis is needed: the realness of the matched
    diagonal entries is extracted by taking real parts.) -/
theorem unraveling_weights_unique {A : Matrix ι ι ℂ} (v : ℝ → ι → ℝ)
    (hv : ∀ s ≥ 0, Tsem s A = Real.exp (-s) • A + ∑ n, v s n • recordState n) :
    ∀ s ≥ 0, ∀ n, v s n = jumpWeight s A n := by
  intro s hs n
  have h1 : Tsem s A n n
      = (Real.exp (-s) • A + ∑ k, v s k • recordState k) n n := by
    rw [hv s hs]
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Tsem_apply_eq] at h1
  have hsum : ∑ k, (v s k • recordState k) n n = ((v s n : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single n
      (fun k _ hk => by
        rw [Matrix.smul_apply, recordState_apply_diag, if_neg (Ne.symm hk), smul_zero])
      (fun hn => absurd (Finset.mem_univ n) hn),
      Matrix.smul_apply, recordState_apply_diag, if_pos rfl, Complex.real_smul, mul_one]
  rw [hsum, Complex.real_smul] at h1
  -- h1 : A n n = (e^{−s} : ℂ)·A n n + (v_n(s) : ℂ)
  have h2 : ((v s n : ℝ) : ℂ) = A n n - ((Real.exp (-s) : ℝ) : ℂ) * A n n := by
    linear_combination -h1
  have h3 : v s n = (A n n).re - Real.exp (-s) * (A n n).re := by
    have h4 := congrArg Complex.re h2
    rwa [Complex.ofReal_re, Complex.sub_re, Complex.re_ofReal_mul] at h4
  rw [jumpWeight, h3]
  ring

/-! ## RC3.7 — equivariance: relabeling the records pushes the jump law forward -/

/-- **The jump law is equivariant under every record relabeling** (any substitution — in
    particular every permutation): `w_n(s)` of the relabeled state is `w_{e n}(s)` of the
    original.  The path-level shape of Gate 3's
    `equivariant_enforcement_preserves_invariance` (CITED, not imported): the unraveling
    carries no preferred record label. -/
theorem jumpWeight_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ] (s : ℝ)
    (A : Matrix ι ι ℂ) (e : κ → ι) (n : κ) :
    jumpWeight s (A.submatrix e e) n = jumpWeight s A (e n) := by
  simp only [jumpWeight, Matrix.submatrix_apply]

/-- The jump law is equivariant under every record permutation (the `Equiv.Perm` instance
    of `jumpWeight_submatrix`). -/
theorem jump_law_equivariant (s : ℝ) (A : Matrix ι ι ℂ) (e : Equiv.Perm ι) (n : ι) :
    jumpWeight s (A.submatrix e e) n = jumpWeight s A (e n) :=
  jumpWeight_submatrix s A e n

/-- Relabeling the records pushes the jump TARGETS forward too:
    `(recordState (e n)).submatrix e e = recordState n` — with `jump_law_equivariant`, the
    whole unraveling (weights AND targets) is permutation-equivariant. -/
theorem recordState_submatrix (e : Equiv.Perm ι) (n : ι) :
    (recordState (e n)).submatrix e e = recordState n := by
  ext i j
  rw [Matrix.submatrix_apply, recordState_apply, recordState_apply]
  simp

end QIQTH.RecordUnraveling
