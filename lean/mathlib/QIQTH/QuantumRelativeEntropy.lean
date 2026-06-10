/-
  QuantumRelativeEntropy — finite-dimensional quantum entropy from spectral data.

  GOAL OF THIS PROGRAM (the "formalize the axioms" effort).  The QIQT-H entropy
  stack currently AXIOMATIZES quantum relative entropy and its properties over
  opaque carriers (`Donald.State/D/H/crossEnt`, `RelEntPositivity.D_nonneg`,
  `ArakiInterface.AkRelEnt/Akre_nonneg`, …).  None of these is an open problem —
  they are standard finite-dimensional / von-Neumann-algebraic quantum information
  theory (Klein 1931; Lindblad–Uhlmann 1975–77; Lieb 1973; Araki 1976).  The
  obstruction is purely that Mathlib lacks the infrastructure (matrix logarithm,
  operator convexity).  This module BEGINS building that infrastructure in finite
  dimensions, so the axioms can be replaced by theorems about concrete density
  matrices.

  DONE SO FAR (axiom-free).
    * Spectral entropy layer: a finite density matrix (`IsDensity`: positive semidefinite,
      unit trace), eigenvalues in `[0,1]` summing to `1`, the von Neumann entropy
      `S(ρ) = ∑ᵢ negMulLog(λᵢ) = −∑ᵢ λᵢ log λᵢ`, and `S(ρ) ≥ 0` — the concrete content of
      the (opaque) entropy object `Donald.H`.
    * The gating primitive Mathlib lacked: the **Hermitian matrix logarithm** `matLog`,
      built from the functional calculus `Matrix.IsHermitian.cfc Real.log` (`= U·diag(log∘λ)·U⋆`),
      and the trace workhorse `cfc_trace : tr(f(A)) = ∑ᵢ f(λᵢ)`.
    * The **quantum relative entropy** `D(ρ‖σ) = tr(ρ(log ρ − log σ))` (Umegaki) — the concrete
      realization of the opaque `Donald.D` / `ArakiInterface.AkRelEnt` — with `D(ρ‖ρ) = 0`.

  NEXT MILESTONES (documented, not yet built).
    * `tr(ρ log ρ) = ∑ λᵢ log λᵢ` (cross-term spectral expansion via `cfc_mul` on positive-definite
      states) → the entropy bridge `S(ρ) = −tr(ρ log ρ)` and the Donald structural identities.
    * Klein's inequality `D(ρ‖σ) ≥ 0` (the doubly-stochastic / Jensen route, reducing to classical
      `KL ≥ 0`) — retires `RelEntPositivity.D_nonneg` in the finite-dimensional case.
    The Araki / continuum / data-processing (Lieb) versions remain the cited frontier.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace QIQTH.QuantumEntropy

open Matrix Real BigOperators Unitary
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite-dimensional **density matrix**: positive semidefinite with unit trace.
    The concrete carrier for the opaque `Donald.State` / `ArakiInterface.NormalState`
    in finite dimensions. -/
structure IsDensity (ρ : Matrix n n ℂ) : Prop where
  /-- the state is positive semidefinite. -/
  posSemidef : ρ.PosSemidef
  /-- the state is normalized: `tr ρ = 1`. -/
  trace_one : ρ.trace = 1

namespace IsDensity

variable {ρ : Matrix n n ℂ}

/-- The spectral eigenvalues of a density matrix (real, via Hermitian spectral data). -/
noncomputable def eigenvalues (h : IsDensity ρ) : n → ℝ := h.posSemidef.1.eigenvalues

/-- Each eigenvalue of a density matrix is nonnegative (positive semidefiniteness). -/
lemma eigenvalues_nonneg (h : IsDensity ρ) (i : n) : 0 ≤ h.eigenvalues i :=
  h.posSemidef.eigenvalues_nonneg i

/-- The eigenvalues of a density matrix sum to `1` (unit trace = sum of eigenvalues). -/
lemma sum_eigenvalues (h : IsDensity ρ) : ∑ i, h.eigenvalues i = 1 := by
  have htr : ρ.trace = ∑ i, ((h.eigenvalues i : ℝ) : ℂ) :=
    h.posSemidef.1.trace_eq_sum_eigenvalues
  rw [h.trace_one] at htr
  exact_mod_cast htr.symm

/-- Each eigenvalue of a density matrix is at most `1` (it is bounded by the sum of all,
    which is `1`, since the others are nonnegative). -/
lemma eigenvalues_le_one (h : IsDensity ρ) (i : n) : h.eigenvalues i ≤ 1 := by
  calc h.eigenvalues i
      ≤ ∑ j, h.eigenvalues j :=
        Finset.single_le_sum (fun j _ => h.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = 1 := h.sum_eigenvalues

end IsDensity

/-- **Von Neumann entropy** `S(ρ) = ∑ᵢ negMulLog(λᵢ) = −∑ᵢ λᵢ log λᵢ`, defined from the
    spectral eigenvalues.  This is the concrete finite-dimensional realization of the
    (currently opaque) entropy object `Donald.H`. -/
noncomputable def vonNeumannEntropy {ρ : Matrix n n ℂ} (h : IsDensity ρ) : ℝ :=
  ∑ i, Real.negMulLog (h.eigenvalues i)

@[inherit_doc] scoped notation "S[" h "]" => vonNeumannEntropy h

/-- **Von Neumann entropy is nonnegative**, `S(ρ) ≥ 0`.  Each eigenvalue lies in `[0,1]`
    (`eigenvalues_nonneg`, `eigenvalues_le_one`), where `negMulLog` is nonnegative; the
    sum of nonnegative terms is nonnegative.  Axiom-free; the concrete content of
    "`H(ρ) ≥ 0`" that the opaque entropy stack leaves abstract. -/
theorem vonNeumannEntropy_nonneg {ρ : Matrix n n ℂ} (h : IsDensity ρ) :
    0 ≤ vonNeumannEntropy h :=
  Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg (h.eigenvalues_nonneg i) (h.eigenvalues_le_one i)

/-! ### The Hermitian matrix logarithm and relative entropy

The gating primitive Mathlib lacks for relative entropy is a matrix logarithm.  We take it from the
Hermitian functional calculus `Matrix.IsHermitian.cfc Real.log` (`= U·diag(log∘λ)·U⋆`).  The workhorse
is the trace formula `tr(f(A)) = ∑ᵢ f(λᵢ)`, from which the entropy/relative-entropy expressions reduce to
sums over eigenvalues. -/

/-- **Trace of a Hermitian functional-calculus image** equals the sum of `f` over the eigenvalues:
    `tr(f(A)) = ∑ᵢ f(λᵢ)`.  Since `f(A) = U·diag(f∘λ)·U⋆` with `U` unitary, the trace is conjugation
    invariant and collapses to the diagonal sum. -/
lemma cfc_trace {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.cfc f).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [Matrix.IsHermitian.cfc, conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  rfl

/-- **The Hermitian matrix logarithm** `log A := U·diag(log∘λ)·U⋆`, from the functional calculus.
    For a positive-definite `A` (all `λᵢ > 0`) this is the genuine operator logarithm. -/
noncomputable def matLog {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  hA.cfc Real.log

/-- **Quantum relative entropy** `D(ρ‖σ) = tr(ρ (log ρ − log σ))` (Umegaki), as a real number.
    The concrete finite-dimensional realization of the opaque `Donald.D` / `ArakiInterface.AkRelEnt`.
    (Well-behaved when `σ` is positive definite so `log σ` is genuine; the support condition
    `supp ρ ⊆ supp σ` is the standard finiteness hypothesis.) -/
noncomputable def relEntropy {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : ℝ :=
  (ρ * (matLog hρ - matLog hσ)).trace.re

/-- **Relative entropy of a state with itself vanishes**: `D(ρ‖ρ) = 0`.  Immediate, since
    `log ρ − log ρ = 0`.  The `D(ρ‖σ) = 0 ↔ ρ = σ` direction (the hard, Klein-equality case) is a
    later milestone. -/
@[simp] theorem relEntropy_self {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    relEntropy hρ hρ = 0 := by
  simp [relEntropy]

/-! ### Stage 1 toward Klein: the diagonal trace `tr(ρ log ρ) = ∑ λᵢ log λᵢ`

For a **positive-definite** `ρ` (all eigenvalues `> 0`, so `Real.log` is continuous on the spectrum),
`ρ · log ρ = (x ↦ x log x)(ρ)` by `cfc_mul`, so its trace collapses to the eigenvalue sum via `cfc_trace`. -/

/-- `Real.log` is continuous on the spectrum of a positive-definite matrix (eigenvalues `> 0`). -/
lemma continuousOn_log_spectrum {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    ContinuousOn Real.log (spectrum ℝ ρ) := by
  refine Real.continuousOn_log.mono ?_
  rw [hρ.1.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact (hρ.eigenvalues_pos i).ne'

/-- **Diagonal trace formula** `tr(ρ · log ρ) = ∑ᵢ λᵢ log λᵢ` for positive-definite `ρ`.  Since `ρ` and
    `log ρ` are both functions of `ρ`, `ρ · log ρ = (x ↦ x log x)(ρ)`; `cfc_trace` then gives the
    eigenvalue sum.  Hence `S(ρ) = −tr(ρ log ρ).re` — the entropy bridge to the spectral definition. -/
theorem trace_mul_matLog {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    (ρ * matLog hρ.1).trace
      = ∑ i, ((hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i) : ℝ) : ℂ) := by
  have hsa : IsSelfAdjoint ρ := hρ.1.isSelfAdjoint
  have key : ρ * matLog hρ.1 = hρ.1.cfc (fun x => x * Real.log x) := by
    rw [matLog, ← hρ.1.cfc_eq Real.log, ← hρ.1.cfc_eq (fun x => x * Real.log x),
      cfc_mul (fun x => x) Real.log ρ (by fun_prop) (continuousOn_log_spectrum hρ), cfc_id' ℝ ρ]
  rw [key, cfc_trace]

end QIQTH.QuantumEntropy
