/-
  POINTER COMPETITION — einselection with `[H_S, A] ≠ 0`: the resonance caveat, the
  rotating-records witness, and the quantitative Zeno regime (duality campaign, brick D1a).

  Brick IC1 (`InteractingChannel.lean`) DERIVED the pointer basis — but in the measurement
  limit: the system self-Hamiltonian was dropped.  THIS brick treats the competition
  `H = H_S ⊗ 1 + A ⊗ B` honestly, in two exactly solvable strata:

  • THE COMMUTING LAYER (`[H_S, A] = 0`, general `ι, κ`) — a diagonal system Hamiltonian
    `H_S = diag h` only SHIFTS the decoherence frequencies, to
        `ν_{nmk} = (h_n − h_m) + (a_n − a_m)·b_k`
    (`reducedC_entry`, the exact solution with the folded frequency).  Einselection
    SURVIVES under the shifted resolution hypothesis (`timeAvg_reducedC_tendsto_dephase`,
    IC1's capstone verbatim over the new frequencies), the ledger is still conserved
    (`reducedC_diag`), trace and positivity are preserved.  BUT the new phenomenon is
    machine-checked: **`resonance_protects_coherence`** — the time-averaged decoherence
    factor of a pair `(n,m)` converges to the TOTAL WEIGHT of the resonant environment
    modes `{k | ν_{nmk} = 0}` (`resonantWeight`), so a resonant system spectrum leaves a
    NONVANISHING time-averaged coherence (`resonant_coherence_survives`,
    `two_mode_resonance`): **pointer bases are not generic under competition — this is the
    decoherence-free-subspace witness.**

  • THE NON-COMMUTING QUBIT, EXACTLY SOLVED — system = qubit, environment = qubit,
    `H = σ_x ⊗ 1 + λ·(σ_z ⊗ σ_z)`: the free Hamiltonian `σ_x` is maximally non-commuting
    with the monitored observable `σ_z`.  The anticommuting-pair trick
    (`sigmaX_mul_sigmaZ_add_sigmaZ_mul_sigmaX`) gives **`Hq_sq : H² = (1 + λ²)·1`**, hence
    the closed-form evolution `U_t = cos(ωt)·1 − i·(sin(ωt)/ω)·H` with `ω = √(1+λ²)`:
    unitarity (`Uq_mul_conjTranspose`, `Uq_conjTranspose_mul`), `Uq_zero`, and the genuine
    Schrödinger certification **`Uq_entry_hasDerivAt`** (`dU/dt = −i·H·U` at every entry —
    `U_t = e^{−itH}` established by calculus, NO `Matrix.exp`, the house pattern's
    non-diagonal upgrade).  Proved on this model:
    - **`records_not_invariant`** — the σ_z-record `ρ₀ = |0⟩⟨0|` is NOT invariant: the
      record population is EXACTLY `1 − sin²(ωt)/(1+λ²)` (`reducedQ_record_population`),
      which leaves 1 at `t = (π/2)/ω` for EVERY coupling λ.  **Einselection under
      competition is a REGIME, not an identity — the free Hamiltonian rotates records.**
    - **`record_deviation_le` / `zeno_strong_coupling`** — THE QUANTITATIVE ZENO BOUND:
      the record deviation is `≤ 1/(1+λ²)` UNIFORMLY IN TIME, so as `λ → ∞` (along ANY
      time path `t(λ)`) the record population returns to 1: the coupling-dominant regime
      restores the pointer basis at an explicit rate.

  Together with IC1: **the record basis emerges from the coupling WHEN the coupling
  dominates** — resonances (commuting layer) and free rotation (non-commuting layer) are
  the two machine-checked failure modes, and the strong-coupling/Zeno regime is
  quantitative.

  ⚠ MANDATORY FIREWALL.  The non-commuting stratum is qubit ⊗ qubit — the exactly
  solvable core; a general `[H_S, A] ≠ 0` competition has no closed form and is NOT
  treated (cited as the open frontier).  The commuting layer is general but DIAGONAL-`H_S`
  only.  All Cesàro statements inherit IC1's finite-recurrence honesty: pointwise
  `t → ∞` decay is impossible in finite dimensions (the repo's gate C,
  `QG/FiniteModularRecurrence.lean`, CITED not imported) — the derived statements are
  time-averaged.  The spectra `h`, `a`, `b`, the weights `w`, and the coupling `λ` are
  model INPUTS.  No Lindblad/weak-coupling derivation is attempted (a different regime,
  cited, not built).  Finite corner, single code; NOT bulk reconstruction, NOT the strong
  holographic principle, NOT quantum gravity.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.InteractingChannel

namespace QIQTH.PointerCompetition

open QIQTH.Entropy QIQTH.RecordChannel QIQTH.InteractingChannel
open scoped ComplexOrder Kronecker Matrix

set_option linter.unusedSectionVars false

/-! ## PC1 — the commuting layer: a diagonal `H_S` shifts the decoherence frequencies -/

section Commuting

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable (a : ι → ℝ) (b : κ → ℝ) (h : ι → ℝ) (w : κ → ℝ)

/-- **The folded decoherence frequency** `ν_{nmk} = (h_n − h_m) + (a_n − a_m)·b_k` — the
    single frequency of the pair `(n,m)` seen through the environment mode `k`, with the
    system-spectrum shift `h_n − h_m` folded in.  IC1's frequency is the `h ≡ 0`
    instance. -/
noncomputable def nu (n m : ι) (k : κ) : ℝ := (h n - h m) + (a n - a m) * b k

/-- The folded frequency vanishes on the diagonal. -/
theorem nu_self (n : ι) (k : κ) : nu a b h n n k = 0 := by
  simp [nu]

/-- **The competition phase unitary** `U_t = diag e^{−it(h_n + a_n·b_k)}` — the time
    evolution generated by `H = H_S ⊗ 1 + A ⊗ B` with everything diagonal (`H_S = diag h`,
    `A = diag a`, `B = diag b`), defined directly by the entry formula (the house
    `Dynamics.lean` pattern; the Hamiltonian tie is `phaseC_entry_hasDerivAt`). -/
noncomputable def phaseC (t : ℝ) : Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.diagonal fun p => Complex.exp ((-(t * (h p.1 + a p.1 * b p.2)) : ℝ) * Complex.I)

/-- Diagonal entry of the competition phase unitary. -/
theorem phaseC_apply_eq (t : ℝ) (p : ι × κ) :
    phaseC a b h t p p
      = Complex.exp ((-(t * (h p.1 + a p.1 * b p.2)) : ℝ) * Complex.I) := by
  rw [phaseC, Matrix.diagonal_apply_eq]

/-- `U_0 = 1`. -/
theorem phaseC_zero : phaseC a b h 0 = 1 := by
  rw [phaseC,
    show (fun p : ι × κ =>
        Complex.exp ((-((0 : ℝ) * (h p.1 + a p.1 * b p.2)) : ℝ) * Complex.I))
      = fun _ => (1 : ℂ) from funext fun p => by simp,
    Matrix.diagonal_one]

/-- **The group law** `U_{s+t} = U_s·U_t`. -/
theorem phaseC_add (s t : ℝ) :
    phaseC a b h (s + t) = phaseC a b h s * phaseC a b h t := by
  rw [phaseC, phaseC, phaseC, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The adjoint of the phase unitary is time reversal: `U_tᴴ = U_{−t}`. -/
theorem phaseC_conjTranspose (t : ℝ) : (phaseC a b h t)ᴴ = phaseC a b h (-t) := by
  rw [phaseC, phaseC, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **Unitarity** (right): `U_t·U_tᴴ = 1`. -/
theorem phaseC_mul_conjTranspose (t : ℝ) :
    phaseC a b h t * (phaseC a b h t)ᴴ = 1 := by
  rw [phaseC_conjTranspose, ← phaseC_add, add_neg_cancel, phaseC_zero]

/-- **Unitarity** (left): `U_tᴴ·U_t = 1`. -/
theorem phaseC_conjTranspose_mul (t : ℝ) :
    (phaseC a b h t)ᴴ * phaseC a b h t = 1 := by
  rw [phaseC_conjTranspose, ← phaseC_add, neg_add_cancel, phaseC_zero]

/-- **The competition Hamiltonian** `H = H_S ⊗ 1 + A ⊗ B = diag (h_n + a_n·b_k)` — the
    commuting (`[H_S, A] = 0`) competition of a diagonal free Hamiltonian with the
    pure-dephasing coupling. -/
noncomputable def HC : Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.diagonal fun p => ((h p.1 + a p.1 * b p.2 : ℝ) : ℂ)

/-- The competition Hamiltonian is Hermitian (a real diagonal). -/
theorem HC_isHermitian : (HC a b h).IsHermitian := by
  show (HC a b h)ᴴ = HC a b h
  rw [HC, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

/-- **The Hamiltonian tie — the entrywise Schrödinger equation**: every diagonal entry of
    the phase unitary satisfies `d/dt U_t(p,p) = −i·H(p,p)·U_t(p,p)`, so `U_t = e^{−itH}`
    in the entrywise sense established by this derivative lemma (off-diagonal entries are
    identically 0 on both sides). -/
theorem phaseC_entry_hasDerivAt (t : ℝ) (p : ι × κ) :
    HasDerivAt (fun s : ℝ => phaseC a b h s p p)
      (-(HC a b h p p) * Complex.I * phaseC a b h t p p) t := by
  set c : ℂ := -((h p.1 + a p.1 * b p.2 : ℝ) : ℂ) * Complex.I with hcdef
  have hentry : (fun s : ℝ => phaseC a b h s p p)
      = fun s : ℝ => Complex.exp (c * s) := by
    funext s
    rw [phaseC_apply_eq, hcdef]
    congr 1
    push_cast
    ring
  have hlin : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
    simpa only [mul_one, id_eq] using
      ((hasDerivAt_id ((t : ℝ) : ℂ)).const_mul c).comp_ofReal
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (c * s)) (Complex.exp (c * t) * c) t :=
    (Complex.hasDerivAt_exp (c * (t : ℂ))).comp t hlin
  have hval : -(HC a b h p p) * Complex.I * phaseC a b h t p p
      = Complex.exp (c * t) * c := by
    rw [HC, Matrix.diagonal_apply_eq, phaseC_apply_eq, hcdef,
      show ((-(t * (h p.1 + a p.1 * b p.2)) : ℝ) : ℂ) * Complex.I
        = -((h p.1 + a p.1 * b p.2 : ℝ) : ℂ) * Complex.I * (t : ℂ) from by push_cast; ring]
    ring
  rw [hentry, hval]
  exact hexp

/-- **The evolved joint state** `U_t·(ρ ⊗ ω)·U_tᴴ` under the competition dynamics
    (IC1's `joint`/`envState` REUSED, not redefined). -/
noncomputable def evolvedC (t : ℝ) (ρ : Matrix ι ι ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  phaseC a b h t * joint w ρ * (phaseC a b h t)ᴴ

/-- Entry formula for the evolved joint state (diagonal conjugation collapses to
    phases). -/
theorem evolvedC_apply (t : ℝ) (ρ : Matrix ι ι ℂ) (p q : ι × κ) :
    evolvedC a b h w t ρ p q
      = Complex.exp ((-(t * (h p.1 + a p.1 * b p.2)) : ℝ) * Complex.I)
        * (ρ p.1 q.1 * envState w p.2 q.2)
        * Complex.exp ((-(-t * (h q.1 + a q.1 * b q.2)) : ℝ) * Complex.I) := by
  rw [evolvedC, phaseC_conjTranspose]
  simp only [phaseC]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, joint_apply]

/-- Pair-index entry formula. -/
theorem evolvedC_apply_pair (t : ℝ) (ρ : Matrix ι ι ℂ) (n m : ι) (k l : κ) :
    evolvedC a b h w t ρ (n, k) (m, l)
      = Complex.exp ((-(t * (h n + a n * b k)) : ℝ) * Complex.I)
        * (ρ n m * envState w k l)
        * Complex.exp ((-(-t * (h m + a m * b l)) : ℝ) * Complex.I) :=
  evolvedC_apply a b h w t ρ (n, k) (m, l)

/-- The evolved joint state of a PSD state is PSD. -/
theorem evolvedC_posSemidef (hw : ∀ k, 0 ≤ w k) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    (t : ℝ) : (evolvedC a b h w t ρ).PosSemidef := by
  rw [evolvedC]
  exact (joint_posSemidef w hw hρ).mul_mul_conjTranspose_same (phaseC a b h t)

/-- **The reduced competition dynamics** — trace out the environment:
    `ρ ↦ Tr₂(U_t·(ρ ⊗ ω)·U_tᴴ)`. -/
noncomputable def reducedC (t : ℝ) (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  partialTraceRight (evolvedC a b h w t ρ)

/-- **The competition decoherence factor**
    `γ_{nm}(t) = Σ_k w_k·e^{−it·ν_{nmk}}` — IC1's factor with the folded frequency. -/
noncomputable def gammaC (t : ℝ) (n m : ι) : ℂ :=
  ∑ k, (w k : ℂ) * Complex.exp ((-(t * nu a b h n m k) : ℝ) * Complex.I)

/-- **THE EXACT SOLUTION WITH COMPETITION** — the reduced dynamics multiplies every
    coherence by the folded decoherence factor: `(reducedC t ρ)_{nm} = γ_{nm}(t)·ρ_{nm}`.
    A commuting self-Hamiltonian only SHIFTS the decoherence frequencies. -/
theorem reducedC_entry (t : ℝ) (ρ : Matrix ι ι ℂ) (n m : ι) :
    reducedC a b h w t ρ n m = gammaC a b h w t n m * ρ n m := by
  rw [reducedC, partialTraceRight_apply, gammaC, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [evolvedC_apply_pair, envState_apply, if_pos rfl,
    show Complex.exp ((-(t * (h n + a n * b k)) : ℝ) * Complex.I) * (ρ n m * (w k : ℂ))
        * Complex.exp ((-(-t * (h m + a m * b k)) : ℝ) * Complex.I)
      = (w k : ℂ)
        * (Complex.exp ((-(t * (h n + a n * b k)) : ℝ) * Complex.I)
          * Complex.exp ((-(-t * (h m + a m * b k)) : ℝ) * Complex.I)) * ρ n m from by ring,
    ← Complex.exp_add,
    show ((-(t * (h n + a n * b k)) : ℝ) : ℂ) * Complex.I
        + ((-(-t * (h m + a m * b k)) : ℝ) : ℂ) * Complex.I
      = ((-(t * nu a b h n m k) : ℝ) : ℂ) * Complex.I from by
        simp only [nu]; push_cast; ring]

/-- The decoherence factor is 1 on the diagonal (`Σ w = 1`) — the frequency vanishes
    there. -/
theorem gammaC_diag (hw1 : ∑ k, w k = 1) (t : ℝ) (n : ι) : gammaC a b h w t n n = 1 := by
  rw [gammaC]
  have hterm : ∀ k : κ,
      (w k : ℂ) * Complex.exp ((-(t * nu a b h n n k) : ℝ) * Complex.I) = (w k : ℂ) := by
    intro k
    rw [nu_self]
    simp
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  exact_mod_cast hw1

/-- **The ledger is still conserved under competition** — diagonal (record) entries never
    move: a commuting `H_S` cannot rewrite records. -/
theorem reducedC_diag (hw1 : ∑ k, w k = 1) (t : ℝ) (ρ : Matrix ι ι ℂ) (n : ι) :
    reducedC a b h w t ρ n n = ρ n n := by
  rw [reducedC_entry, gammaC_diag a b h w hw1, one_mul]

/-- **The reduced competition dynamics is trace-preserving.** -/
theorem reducedC_trace (hw1 : ∑ k, w k = 1) (t : ℝ) (ρ : Matrix ι ι ℂ) :
    (reducedC a b h w t ρ).trace = ρ.trace := by
  rw [Matrix.trace, Matrix.trace]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, reducedC_diag a b h w hw1]

/-- **The reduced competition dynamics is positivity-preserving.** -/
theorem reducedC_posSemidef (hw : ∀ k, 0 ≤ w k) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    (t : ℝ) : (reducedC a b h w t ρ).PosSemidef :=
  partialTraceRight_posSemidef (evolvedC_posSemidef a b h w hw hρ t)

/-! ## PC1.2 — the Cesàro time average over the folded frequencies

FIREWALL (finite recurrences, inherited from IC1): the environment is FINITE, so
pointwise `t → ∞` decay is impossible (gate C, `QG/FiniteModularRecurrence.lean`,
CITED) — the honest statements are Cesàro/time-averaged. -/

/-- The single-frequency phase is continuous (integrability feedstock). -/
theorem continuous_phaseC_exp (θ : ℝ) :
    Continuous fun t : ℝ => Complex.exp ((-(t * θ) : ℝ) * Complex.I) := by
  have h1 : Continuous fun t : ℝ => -(t * θ) := (continuous_id.mul continuous_const).neg
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp h1).mul continuous_const)

/-- **The Cesàro time average of the competition decoherence factor**
    `γ̄_{nm}(T) = (1/T)∫₀ᵀ γ_{nm}(t) dt`. -/
noncomputable def timeAvgGammaC (T : ℝ) (n m : ι) : ℂ :=
  (1 / T : ℂ) * ∫ t in (0:ℝ)..T, gammaC a b h w t n m

/-- The time-averaged decoherence factor splits over the (finite) environment modes. -/
theorem timeAvgGammaC_eq_sum (T : ℝ) (n m : ι) :
    timeAvgGammaC a b h w T n m
      = ∑ k, (w k : ℂ)
          * ((1 / T : ℂ) * ∫ t in (0:ℝ)..T,
              Complex.exp ((-(t * nu a b h n m k) : ℝ) * Complex.I)) := by
  rw [timeAvgGammaC]
  simp only [gammaC]
  have hInt : ∀ k ∈ (Finset.univ : Finset κ), IntervalIntegrable
      (fun t : ℝ => (w k : ℂ) * Complex.exp ((-(t * nu a b h n m k) : ℝ) * Complex.I))
      MeasureTheory.volume 0 T := fun k _ =>
    (continuous_const.mul (continuous_phaseC_exp (nu a b h n m k))).intervalIntegrable 0 T
  rw [intervalIntegral.integral_finsetSum hInt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

/-- On the diagonal the time average is constantly 1 (for `T ≠ 0`). -/
theorem timeAvgGammaC_diag (hw1 : ∑ k, w k = 1) {T : ℝ} (hT : T ≠ 0) (n : ι) :
    timeAvgGammaC a b h w T n n = 1 := by
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  rw [timeAvgGammaC]
  simp only [gammaC_diag a b h w hw1]
  rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one, one_div,
    inv_mul_cancel₀ hT']

/-- **The off-diagonal time average dies under the SHIFTED resolution hypothesis** —
    every folded frequency `ν_{nmk}` nonzero ⟹ each mode's Cesàro average vanishes
    (IC1's `cesaro_exp_tendsto`, REUSED verbatim over the new frequencies). -/
theorem timeAvgGammaC_tendsto_zero
    (hres : ∀ n m : ι, n ≠ m → ∀ k, nu a b h n m k ≠ 0) {n m : ι} (hnm : n ≠ m) :
    Filter.Tendsto (fun T : ℝ => timeAvgGammaC a b h w T n m) Filter.atTop (nhds 0) := by
  rw [show (fun T : ℝ => timeAvgGammaC a b h w T n m)
      = fun T : ℝ => ∑ k, (w k : ℂ)
          * ((1 / T : ℂ) * ∫ t in (0:ℝ)..T,
              Complex.exp ((-(t * nu a b h n m k) : ℝ) * Complex.I)) from
    funext fun T => timeAvgGammaC_eq_sum a b h w T n m]
  have hsum := tendsto_finsetSum (Finset.univ : Finset κ)
    (fun k _ => (cesaro_exp_tendsto (hres n m hnm k)).const_mul ((w k : ℂ)))
  simpa using hsum

/-- **The Cesàro-averaged reduced competition dynamics** — entrywise
    `γ̄_{nm}(T)·ρ_{nm}`. -/
noncomputable def timeAvgReducedC (T : ℝ) (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun n m => timeAvgGammaC a b h w T n m * ρ n m

/-- Entry formula for the averaged reduced dynamics. -/
theorem timeAvgReducedC_apply (T : ℝ) (ρ : Matrix ι ι ℂ) (n m : ι) :
    timeAvgReducedC a b h w T ρ n m = timeAvgGammaC a b h w T n m * ρ n m := rfl

/-- The entrywise definition IS the Cesàro integral of the reduced dynamics. -/
theorem timeAvgReducedC_eq_integral (T : ℝ) (ρ : Matrix ι ι ℂ) (n m : ι) :
    timeAvgReducedC a b h w T ρ n m
      = (1 / T : ℂ) * ∫ t in (0:ℝ)..T, reducedC a b h w t ρ n m := by
  simp only [reducedC_entry]
  rw [intervalIntegral.integral_mul_const, timeAvgReducedC_apply, timeAvgGammaC]
  ring

/-- **EINSELECTION SURVIVES A COMMUTING `H_S`** — under the SHIFTED resolution hypothesis
    (every folded frequency `(h_n − h_m) + (a_n − a_m)·b_k` nonzero for `n ≠ m`), the
    Cesàro time average of the competition reduced dynamics converges (entrywise,
    `T → ∞`) to RC1's `dephase`: IC1's capstone with the shifted frequencies.  The record
    basis is still the eigenbasis of the monitored observable `A` — a commuting
    self-Hamiltonian does not change WHICH basis is selected, only the resolution
    condition.  (For what happens when the hypothesis FAILS, see
    `resonance_protects_coherence`.) -/
theorem timeAvg_reducedC_tendsto_dephase (hw1 : ∑ k, w k = 1)
    (hres : ∀ n m : ι, n ≠ m → ∀ k, nu a b h n m k ≠ 0)
    (ρ : Matrix ι ι ℂ) (n m : ι) :
    Filter.Tendsto (fun T : ℝ => timeAvgReducedC a b h w T ρ n m) Filter.atTop
      (nhds (dephase ρ n m)) := by
  by_cases hnm : n = m
  · subst hnm
    rw [dephase_apply_eq]
    have heq : ∀ᶠ T : ℝ in Filter.atTop, timeAvgReducedC a b h w T ρ n n = ρ n n := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
      rw [timeAvgReducedC_apply,
        timeAvgGammaC_diag a b h w hw1 (lt_of_lt_of_le one_pos hT).ne', one_mul]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) tendsto_const_nhds
  · rw [dephase_apply_ne ρ hnm]
    have h0 := (timeAvgGammaC_tendsto_zero a b h w hres hnm).mul_const (ρ n m)
    rw [zero_mul] at h0
    exact h0.congr fun T => (timeAvgReducedC_apply a b h w T ρ n m).symm

/-! ## PC1.3 — THE RESONANCE THEOREM: pointer bases are not generic under competition -/

open Classical in
/-- **The resonant weight** of a pair `(n,m)`: the total environment weight carried by
    the RESONANT modes `{k | ν_{nmk} = 0}` — the modes whose coupling frequency is
    exactly cancelled by the system-spectrum gap `h_n − h_m`. -/
noncomputable def resonantWeight (n m : ι) : ℝ :=
  ∑ k, if nu a b h n m k = 0 then w k else 0

/-- **THE RESONANCE THEOREM — resonance protects coherence.**  The time-averaged
    decoherence factor of the pair `(n,m)` converges to the TOTAL RESONANT WEIGHT `W`:
    resonant modes contribute their full weight (constant integrand), non-resonant modes
    die by the Cesàro squeeze (`cesaro_exp_tendsto`).  With `W ≠ 0` the time-averaged
    coherence does NOT vanish (`resonant_coherence_survives`): **a resonant system
    spectrum protects coherences — pointer bases are not generic under competition; this
    is the machine-checked decoherence-free-subspace witness.** -/
theorem resonance_protects_coherence (n m : ι) :
    Filter.Tendsto (fun T : ℝ => timeAvgGammaC a b h w T n m) Filter.atTop
      (nhds ((resonantWeight a b h w n m : ℝ) : ℂ)) := by
  classical
  have hmode : ∀ k : κ, Filter.Tendsto
      (fun T : ℝ => (w k : ℂ)
        * ((1 / T : ℂ) * ∫ t in (0:ℝ)..T,
            Complex.exp ((-(t * nu a b h n m k) : ℝ) * Complex.I)))
      Filter.atTop (nhds (if nu a b h n m k = 0 then (w k : ℂ) else 0)) := by
    intro k
    by_cases hk : nu a b h n m k = 0
    · rw [if_pos hk]
      have hconst : ∀ᶠ T : ℝ in Filter.atTop,
          (w k : ℂ) * ((1 / T : ℂ) * ∫ t in (0:ℝ)..T,
            Complex.exp ((-(t * nu a b h n m k) : ℝ) * Complex.I)) = (w k : ℂ) := by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
        have hT' : (T : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le one_pos hT).ne'
        rw [show (fun t : ℝ => Complex.exp ((-(t * nu a b h n m k) : ℝ) * Complex.I))
            = fun _ : ℝ => (1 : ℂ) from funext fun t => by rw [hk]; simp,
          intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one, one_div,
          inv_mul_cancel₀ hT', mul_one]
      exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hconst) tendsto_const_nhds
    · rw [if_neg hk]
      have h0 := (cesaro_exp_tendsto hk).const_mul ((w k : ℂ))
      rw [mul_zero] at h0
      exact h0
  have hval : ((resonantWeight a b h w n m : ℝ) : ℂ)
      = ∑ k, (if nu a b h n m k = 0 then (w k : ℂ) else 0) := by
    simp only [resonantWeight]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [show (fun T : ℝ => timeAvgGammaC a b h w T n m)
      = fun T : ℝ => ∑ k, (w k : ℂ)
          * ((1 / T : ℂ) * ∫ t in (0:ℝ)..T,
              Complex.exp ((-(t * nu a b h n m k) : ℝ) * Complex.I)) from
    funext fun T => timeAvgGammaC_eq_sum a b h w T n m, hval]
  simpa using tendsto_finsetSum (Finset.univ : Finset κ) (fun k _ => hmode k)

/-- **The resonant coherence SURVIVES**: with nonzero resonant weight and a nonzero
    initial coherence, the time-averaged coherence converges to `W·ρ_{nm} ≠ 0` — the
    time-averaged reduced dynamics does NOT dephase this pair.  (Contrast the capstone
    `timeAvg_reducedC_tendsto_dephase`, whose resolution hypothesis exactly forbids
    resonant modes.) -/
theorem resonant_coherence_survives {n m : ι} (ρ : Matrix ι ι ℂ)
    (hW : resonantWeight a b h w n m ≠ 0) (hρ : ρ n m ≠ 0) :
    Filter.Tendsto (fun T : ℝ => timeAvgReducedC a b h w T ρ n m) Filter.atTop
      (nhds (((resonantWeight a b h w n m : ℝ) : ℂ) * ρ n m))
    ∧ ((resonantWeight a b h w n m : ℝ) : ℂ) * ρ n m ≠ 0 := by
  constructor
  · have h1 := (resonance_protects_coherence a b h w n m).mul_const (ρ n m)
    exact h1.congr fun T => (timeAvgReducedC_apply a b h w T ρ n m).symm
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hW) hρ

end Commuting

/-- **The concrete two-mode instance**: one resonant mode (`ν_{nm0} = 0`, weight `w 0`),
    one resolved mode (`ν_{nm1} ≠ 0`) — the time-averaged decoherence factor converges to
    `w 0`; for `w 0 ≠ 0` the pair's coherence is protected forever (in time average). -/
theorem two_mode_resonance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (b : Fin 2 → ℝ) (h : ι → ℝ) (w : Fin 2 → ℝ) {n m : ι}
    (h0 : nu a b h n m 0 = 0) (h1 : nu a b h n m 1 ≠ 0) :
    Filter.Tendsto (fun T : ℝ => timeAvgGammaC a b h w T n m) Filter.atTop
      (nhds ((w 0 : ℝ) : ℂ)) := by
  have hW : resonantWeight a b h w n m = w 0 := by
    simp only [resonantWeight, Fin.sum_univ_two, if_pos h0, if_neg h1, add_zero]
  have hlim := resonance_protects_coherence a b h w n m
  rwa [hW] at hlim

/-! ## PC2 — the non-commuting qubit competition, exactly solved

`H = σ_x ⊗ 1 + λ·(σ_z ⊗ σ_z)`: the free Hamiltonian `σ_x` is maximally non-commuting
with the monitored observable `σ_z`.  The anticommuting-pair trick makes `H² = (1+λ²)·1`,
so the evolution is in closed form — no `Matrix.exp`, the Schrödinger equation is
certified entrywise by genuine calculus. -/

section Qubit

/-- The Pauli `σ_x` matrix. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `σ_z` matrix. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `σ_x² = 1`. -/
theorem sigmaX_mul_sigmaX : sigmaX * sigmaX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ_z² = 1`. -/
theorem sigmaZ_mul_sigmaZ : sigmaZ * sigmaZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The anticommutation** `σ_xσ_z + σ_zσ_x = 0` — the algebraic heart of the
    closed-form solution. -/
theorem sigmaX_mul_sigmaZ_add_sigmaZ_mul_sigmaX :
    sigmaX * sigmaZ + sigmaZ * sigmaX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, sigmaZ, Matrix.add_apply]

/-- `σ_x` is Hermitian. -/
theorem sigmaX_conjTranspose : sigmaXᴴ = sigmaX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaX, Matrix.conjTranspose_apply]

/-- `σ_z` is Hermitian. -/
theorem sigmaZ_conjTranspose : sigmaZᴴ = sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaZ, Matrix.conjTranspose_apply]

/-- **The qubit competition Hamiltonian** `H(λ) = σ_x ⊗ 1 + λ·(σ_z ⊗ σ_z)`: a free
    system Hamiltonian `σ_x` MAXIMALLY non-commuting with the monitored observable
    `A = σ_z`, monitored by a qubit environment through `σ_z ⊗ σ_z` at coupling `λ`. -/
noncomputable def Hq (l : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  sigmaX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (l : ℂ) • (sigmaZ ⊗ₖ sigmaZ)

/-- The competition Hamiltonian is Hermitian. -/
theorem Hq_isHermitian (l : ℝ) : (Hq l).IsHermitian := by
  show (Hq l)ᴴ = Hq l
  rw [Hq, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, sigmaX_conjTranspose, sigmaZ_conjTranspose,
    show star ((l : ℝ) : ℂ) = ((l : ℝ) : ℂ) from by
      rw [Complex.star_def, Complex.conj_ofReal]]

/-- **THE ANTICOMMUTING-PAIR TRICK** — `H(λ)² = (1 + λ²)·1`: `σ_x ⊗ 1` and `σ_z ⊗ σ_z`
    anticommute and each squares to 1, so the competition Hamiltonian squares to a
    scalar.  This is what makes the non-commuting model exactly solvable. -/
theorem Hq_sq (l : ℝ) :
    Hq l * Hq l
      = ((1 + l ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  have hXX : (sigmaX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (sigmaX ⊗ₖ 1) = 1 := by
    rw [← Matrix.mul_kronecker_mul, sigmaX_mul_sigmaX, one_mul, Matrix.one_kronecker_one]
  have hZZ : (sigmaZ ⊗ₖ sigmaZ) * (sigmaZ ⊗ₖ sigmaZ)
      = (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    rw [← Matrix.mul_kronecker_mul, sigmaZ_mul_sigmaZ, Matrix.one_kronecker_one]
  have hcross : (sigmaX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (sigmaZ ⊗ₖ sigmaZ)
      + (sigmaZ ⊗ₖ sigmaZ) * (sigmaX ⊗ₖ 1) = 0 := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul, mul_one,
      ← Matrix.add_kronecker, sigmaX_mul_sigmaZ_add_sigmaZ_mul_sigmaX,
      Matrix.zero_kronecker]
  have expand : Hq l * Hq l
      = (sigmaX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (sigmaX ⊗ₖ 1)
        + (l : ℂ) • ((sigmaX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (sigmaZ ⊗ₖ sigmaZ)
            + (sigmaZ ⊗ₖ sigmaZ) * (sigmaX ⊗ₖ 1))
        + ((l : ℂ) * (l : ℂ)) • ((sigmaZ ⊗ₖ sigmaZ) * (sigmaZ ⊗ₖ sigmaZ)) := by
    rw [Hq, add_mul, mul_add, mul_add]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
    abel
  rw [expand, hXX, hcross, hZZ, smul_zero, add_zero,
    show ((1 + l ^ 2 : ℝ) : ℂ) = 1 + (l : ℂ) * (l : ℂ) from by push_cast; ring,
    add_smul, one_smul]

/-- **The competition frequency** `ω(λ) = √(1 + λ²)` — always positive: the qubit
    competition never has a vanishing gap. -/
noncomputable def omega (l : ℝ) : ℝ := Real.sqrt (1 + l ^ 2)

/-- `ω > 0` for every coupling. -/
theorem omega_pos (l : ℝ) : 0 < omega l :=
  Real.sqrt_pos.mpr (by positivity)

/-- `ω² = 1 + λ²`. -/
theorem omega_sq (l : ℝ) : omega l ^ 2 = 1 + l ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- **The closed-form evolution** `U(λ,t) = cos(ωt)·1 − i·(sin(ωt)/ω)·H(λ)` — the exact
    solution of the Schrödinger equation for the anticommuting pair (certified by
    `Uq_entry_hasDerivAt`, which establishes `U_t = e^{−itH}` without `Matrix.exp`). -/
noncomputable def Uq (l t : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((Real.cos (omega l * t) : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    - (Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ)) • Hq l

/-- `U(λ,0) = 1`. -/
theorem Uq_zero (l : ℝ) : Uq l 0 = 1 := by
  rw [Uq]
  simp

/-- The adjoint of the closed-form evolution: `Uᴴ = cos(ωt)·1 + i·(sin(ωt)/ω)·H`. -/
theorem Uq_conjTranspose (l t : ℝ) :
    (Uq l t)ᴴ
      = ((Real.cos (omega l * t) : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        + (Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ)) • Hq l := by
  rw [Uq, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, (Hq_isHermitian l).eq,
    show star (((Real.cos (omega l * t) : ℝ)) : ℂ) = ((Real.cos (omega l * t) : ℝ) : ℂ) from by
      rw [Complex.star_def, Complex.conj_ofReal],
    show star (Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ))
        = -(Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ)) from by
      simp only [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
      ring,
    neg_smul, sub_neg_eq_add]

/-- Expansion helper: `(c·1 − d·H)(c·1 + d·H) = c²·1 − d²·H²` (scalars commute with
    everything). -/
private theorem expand_mul_left {n : Type*} [Fintype n] [DecidableEq n]
    (c d : ℂ) (H : Matrix n n ℂ) :
    (c • 1 - d • H) * (c • 1 + d • H) = (c * c) • (1 : Matrix n n ℂ) - (d * d) • (H * H) := by
  rw [sub_mul, mul_add, mul_add]
  simp only [smul_mul_smul_comm, one_mul, mul_one]
  rw [mul_comm d c]
  abel

/-- Expansion helper: `(c·1 + d·H)(c·1 − d·H) = c²·1 − d²·H²`. -/
private theorem expand_mul_right {n : Type*} [Fintype n] [DecidableEq n]
    (c d : ℂ) (H : Matrix n n ℂ) :
    (c • 1 + d • H) * (c • 1 - d • H) = (c * c) • (1 : Matrix n n ℂ) - (d * d) • (H * H) := by
  rw [add_mul, mul_sub, mul_sub]
  simp only [smul_mul_smul_comm, one_mul, mul_one]
  rw [mul_comm d c]
  abel

/-- The scalar coefficient identity behind unitarity:
    `cos² + (sin/ω)²·(1+λ²) = 1` (via `ω² = 1+λ²` and `cos² + sin² = 1`). -/
theorem cos_sq_add_scaled_sin_sq (l t : ℝ) :
    Real.cos (omega l * t) ^ 2 + (Real.sin (omega l * t) / omega l) ^ 2 * (1 + l ^ 2)
      = 1 := by
  have hω : omega l ≠ 0 := (omega_pos l).ne'
  rw [div_pow, ← omega_sq l, div_mul_cancel₀ _ (pow_ne_zero 2 hω)]
  exact Real.cos_sq_add_sin_sq _

/-- **Unitarity** (right): `U·Uᴴ = 1` — from `H` Hermitian, `H² = (1+λ²)·1`, and
    `cos² + sin² = 1`. -/
theorem Uq_mul_conjTranspose (l t : ℝ) : Uq l t * (Uq l t)ᴴ = 1 := by
  rw [Uq_conjTranspose, Uq, expand_mul_left, Hq_sq, smul_smul, ← sub_smul,
    show ((Real.cos (omega l * t) : ℝ) : ℂ) * ((Real.cos (omega l * t) : ℝ) : ℂ)
        - Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ)
            * (Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ))
          * ((1 + l ^ 2 : ℝ) : ℂ)
      = ((Real.cos (omega l * t) ^ 2
          + (Real.sin (omega l * t) / omega l) ^ 2 * (1 + l ^ 2) : ℝ) : ℂ) from by
    rw [show Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ)
          * (Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ))
        = -(((Real.sin (omega l * t) / omega l : ℝ) : ℂ)
            * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ)) from by
      rw [mul_mul_mul_comm, Complex.I_mul_I, neg_one_mul]]
    push_cast
    ring,
    cos_sq_add_scaled_sin_sq, Complex.ofReal_one, one_smul]

/-- **Unitarity** (left): `Uᴴ·U = 1`. -/
theorem Uq_conjTranspose_mul (l t : ℝ) : (Uq l t)ᴴ * Uq l t = 1 := by
  rw [Uq_conjTranspose, Uq, expand_mul_right, Hq_sq, smul_smul, ← sub_smul,
    show ((Real.cos (omega l * t) : ℝ) : ℂ) * ((Real.cos (omega l * t) : ℝ) : ℂ)
        - Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ)
            * (Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ))
          * ((1 + l ^ 2 : ℝ) : ℂ)
      = ((Real.cos (omega l * t) ^ 2
          + (Real.sin (omega l * t) / omega l) ^ 2 * (1 + l ^ 2) : ℝ) : ℂ) from by
    rw [show Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ)
          * (Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ))
        = -(((Real.sin (omega l * t) / omega l : ℝ) : ℂ)
            * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ)) from by
      rw [mul_mul_mul_comm, Complex.I_mul_I, neg_one_mul]]
    push_cast
    ring,
    cos_sq_add_scaled_sin_sq, Complex.ofReal_one, one_smul]

/-- The Hamiltonian acting on the closed-form evolution:
    `H·U = cos(ωt)·H − i·(sin(ωt)/ω)·(1+λ²)·1` (via `H² = (1+λ²)·1`). -/
theorem Hq_mul_Uq (l t : ℝ) :
    Hq l * Uq l t
      = ((Real.cos (omega l * t) : ℝ) : ℂ) • Hq l
        - (Complex.I * ((Real.sin (omega l * t) / omega l : ℝ) : ℂ)
            * ((1 + l ^ 2 : ℝ) : ℂ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  rw [Uq, mul_sub, mul_smul_comm, mul_one, mul_smul_comm, Hq_sq, smul_smul]

/-- **THE SCHRÖDINGER CERTIFICATION** — every entry of the closed-form evolution solves
    `dU/dt = −i·H·U` (genuine calculus: `cos/sin` derivatives composed with `ω·t`, the
    product identity via `H² = ω²·1`).  This certifies `U_t = e^{−itH}` WITHOUT
    `Matrix.exp` — the house pattern's non-diagonal upgrade. -/
theorem Uq_entry_hasDerivAt (l t : ℝ) (p q : Fin 2 × Fin 2) :
    HasDerivAt (fun s : ℝ => Uq l s p q) (-Complex.I * (Hq l * Uq l t) p q) t := by
  have hω : omega l ≠ 0 := (omega_pos l).ne'
  have hωC : ((omega l : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
  -- real derivatives of the coefficient functions
  have hlin : HasDerivAt (fun s : ℝ => omega l * s) (omega l) t := by
    simpa using (hasDerivAt_id t).const_mul (omega l)
  have hcos : HasDerivAt (fun s : ℝ => Real.cos (omega l * s))
      (-Real.sin (omega l * t) * omega l) t :=
    (Real.hasDerivAt_cos (omega l * t)).comp t hlin
  have hsin : HasDerivAt (fun s : ℝ => Real.sin (omega l * s))
      (Real.cos (omega l * t) * omega l) t :=
    (Real.hasDerivAt_sin (omega l * t)).comp t hlin
  have hcosC : HasDerivAt (fun s : ℝ => ((Real.cos (omega l * s) : ℝ) : ℂ))
      ((-Real.sin (omega l * t) * omega l : ℝ) : ℂ) t := hcos.ofReal_comp
  have hsinC : HasDerivAt (fun s : ℝ => ((Real.sin (omega l * s) : ℝ) : ℂ))
      ((Real.cos (omega l * t) * omega l : ℝ) : ℂ) t := hsin.ofReal_comp
  -- the entry as cos·A + sin·B
  have hfun : (fun s : ℝ => Uq l s p q)
      = fun s : ℝ =>
          ((Real.cos (omega l * s) : ℝ) : ℂ)
              * ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) p q)
            + ((Real.sin (omega l * s) : ℝ) : ℂ)
              * (-(Complex.I / ((omega l : ℝ) : ℂ)) * Hq l p q) := by
    funext s
    rw [Uq, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
      smul_eq_mul]
    push_cast
    ring
  have hE : HasDerivAt
      (fun s : ℝ =>
        ((Real.cos (omega l * s) : ℝ) : ℂ)
            * ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) p q)
          + ((Real.sin (omega l * s) : ℝ) : ℂ)
            * (-(Complex.I / ((omega l : ℝ) : ℂ)) * Hq l p q))
      (((-Real.sin (omega l * t) * omega l : ℝ) : ℂ)
          * ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) p q)
        + ((Real.cos (omega l * t) * omega l : ℝ) : ℂ)
          * (-(Complex.I / ((omega l : ℝ) : ℂ)) * Hq l p q)) t :=
    (hcosC.mul_const _).add (hsinC.mul_const _)
  have hval : ((-Real.sin (omega l * t) * omega l : ℝ) : ℂ)
        * ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) p q)
      + ((Real.cos (omega l * t) * omega l : ℝ) : ℂ)
        * (-(Complex.I / ((omega l : ℝ) : ℂ)) * Hq l p q)
      = -Complex.I * (Hq l * Uq l t) p q := by
    rw [Hq_mul_Uq, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
      smul_eq_mul,
      show ((1 + l ^ 2 : ℝ) : ℂ) = ((omega l : ℝ) : ℂ) ^ 2 from by
        rw [← omega_sq l]; exact Complex.ofReal_pow _ _]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [hfun]
  exact hval ▸ hE

/-! ## PC2.2 — the reduced competition dynamics on the record, exactly computed -/

/-- The σ_z-record state `ρ₀ = |0⟩⟨0|` — the sharp record of the monitored observable. -/
def recordState : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The diagonal qubit environment state `ω = diag(w₀, w₁)`. -/
def envQ (w₀ w₁ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(w₀ : ℂ), 0; 0, (w₁ : ℂ)]

/-- **The reduced competition dynamics on the qubit**:
    `ρ ↦ Tr₂(U(λ,t)·(ρ ⊗ ω)·U(λ,t)ᴴ)` — everything explicit 4×4, exactly solvable. -/
noncomputable def reducedQ (l t w₀ w₁ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  partialTraceRight (Uq l t * (ρ ⊗ₖ envQ w₀ w₁) * (Uq l t)ᴴ)

set_option maxHeartbeats 1000000 in
/-- **THE EXACT RECORD POPULATION** — for the σ_z-record input, the surviving record
    population is EXACTLY `1 − sin²(ωt)/(1 + λ²)`: the free `σ_x` rotates the record out
    at rate set by `sin²(ωt)`, and the coupling suppresses the excursion by `1/(1+λ²)`.
    This single closed formula carries both failure and recovery: it leaves 1 at generic
    times (`records_not_invariant`) and returns to 1 uniformly as `λ → ∞`
    (`record_deviation_le`, `zeno_strong_coupling`). -/
theorem reducedQ_record_population (l t w₀ w₁ : ℝ) (hw : w₀ + w₁ = 1) :
    reducedQ l t w₀ w₁ recordState 0 0
      = ((1 - Real.sin (omega l * t) ^ 2 / (1 + l ^ 2) : ℝ) : ℂ) := by
  have hω : omega l ≠ 0 := (omega_pos l).ne'
  have htarget : (1 - Real.sin (omega l * t) ^ 2 / (1 + l ^ 2) : ℝ)
      = (w₀ + w₁)
        * (Real.cos (omega l * t) ^ 2
            + (Real.sin (omega l * t) / omega l) ^ 2 * l ^ 2) := by
    have hpos : (0 : ℝ) < 1 + l ^ 2 := by positivity
    rw [hw, one_mul, div_pow, omega_sq l, Real.cos_sq']
    field_simp
    ring
  rw [show ((1 - Real.sin (omega l * t) ^ 2 / (1 + l ^ 2) : ℝ) : ℂ)
      = (((w₀ + w₁)
          * (Real.cos (omega l * t) ^ 2
              + (Real.sin (omega l * t) / omega l) ^ 2 * l ^ 2) : ℝ) : ℂ) from by
    rw [htarget]]
  rw [reducedQ, partialTraceRight_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  simp [Uq, Hq, recordState, envQ, sigmaX, sigmaZ, Matrix.kroneckerMap_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    Complex.conj_ofReal, Complex.conj_I, -Complex.ofReal_sin, -Complex.ofReal_cos]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- **THE ROTATING-RECORDS WITNESS** — the σ_z-record is NOT invariant under the
    competition dynamics, for EVERY coupling `λ`: at `t = (π/2)/ω` the record population
    is `1 − 1/(1+λ²) < 1`.  **Einselection under competition is a REGIME, not an
    identity: the free Hamiltonian rotates records** (at `λ = 0` the record is fully
    rotated out; small couplings fail by the same explicit formula
    `reducedQ_record_population` — no continuity argument needed, the formula is exact in
    `λ`). -/
theorem records_not_invariant (l w₀ w₁ : ℝ) (hw : w₀ + w₁ = 1) :
    reducedQ l (Real.pi / 2 / omega l) w₀ w₁ recordState ≠ recordState := by
  have hω : omega l ≠ 0 := (omega_pos l).ne'
  intro hfix
  have h00 : reducedQ l (Real.pi / 2 / omega l) w₀ w₁ recordState 0 0 = 1 := by
    rw [hfix, recordState]
    simp
  rw [reducedQ_record_population l _ w₀ w₁ hw,
    show omega l * (Real.pi / 2 / omega l) = Real.pi / 2 from by
      rw [mul_comm, div_mul_cancel₀ _ hω],
    Real.sin_pi_div_two] at h00
  have hr : (1 - 1 ^ 2 / (1 + l ^ 2) : ℝ) = 1 := by exact_mod_cast h00
  rw [one_pow] at hr
  have hpos : (0 : ℝ) < 1 / (1 + l ^ 2) := by positivity
  linarith

/-- **THE QUANTITATIVE ZENO BOUND** — the record deviation is at most `1/(1+λ²)`,
    UNIFORMLY IN TIME: `‖(reducedQ λ t ρ₀)₀₀ − 1‖ ≤ 1/(1+λ²)` for ALL `t`.  The
    coupling-dominant regime restores the pointer basis at an explicit rate. -/
theorem record_deviation_le (l t w₀ w₁ : ℝ) (hw : w₀ + w₁ = 1) :
    ‖reducedQ l t w₀ w₁ recordState 0 0 - 1‖ ≤ 1 / (1 + l ^ 2) := by
  rw [reducedQ_record_population l t w₀ w₁ hw,
    show ((1 - Real.sin (omega l * t) ^ 2 / (1 + l ^ 2) : ℝ) : ℂ) - 1
      = ((-(Real.sin (omega l * t) ^ 2 / (1 + l ^ 2)) : ℝ) : ℂ) from by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sin (omega l * t) ^ 2 / (1 + l ^ 2))]
  gcongr
  exact Real.sin_sq_le_one _

/-- **THE ZENO / STRONG-COUPLING REGIME THEOREM** — as `λ → ∞`, ALONG ANY TIME PATH
    `t(λ)` whatsoever (this is the uniformity in time made precise), the record
    population returns to 1: strong monitoring freezes the record against the free
    rotation — einselection is RESTORED in the coupling-dominant regime, at the explicit
    rate `1/(1+λ²)` of `record_deviation_le`. -/
theorem zeno_strong_coupling (w₀ w₁ : ℝ) (hw : w₀ + w₁ = 1) (t : ℝ → ℝ) :
    Filter.Tendsto (fun l : ℝ => reducedQ l (t l) w₀ w₁ recordState 0 0)
      Filter.atTop (nhds 1) := by
  have hbound : Filter.Tendsto
      (fun l : ℝ => reducedQ l (t l) w₀ w₁ recordState 0 0 - 1)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (fun l => record_deviation_le l (t l) w₀ w₁ hw) ?_
    have h1 : Filter.Tendsto (fun l : ℝ => 1 + l ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun x => le_add_of_nonneg_left zero_le_one)
        (Filter.tendsto_pow_atTop (by norm_num))
    simpa [one_div] using h1.inv_tendsto_atTop
  have hsum := hbound.add (tendsto_const_nhds (x := (1 : ℂ)) (f := Filter.atTop))
  rw [zero_add] at hsum
  exact hsum.congr fun l => by ring

end Qubit

end QIQTH.PointerCompetition
