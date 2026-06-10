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
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Complex.BigOperators
import QIQTH.RelEntPositivity

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

/-! ### Stage 2 toward Klein: the cross-term `tr(ρ log σ) = ∑ᵢⱼ pᵢ Sᵢⱼ log qⱼ`

`ρ = U diag(p) U⋆`, `log σ = V diag(log q) V⋆`; with `W = U⋆V` (unitary) and the overlap weights
`S i j = ‖Wᵢⱼ‖² = normSq Wᵢⱼ`, trace cyclicity collapses the product to `∑ᵢⱼ pᵢ Sᵢⱼ log qⱼ`, and `S`
is doubly stochastic (rows/cols sum to 1, from `W W⋆ = W⋆ W = 1`).  (Proof skeleton: GPT-5.5-pro.) -/

/-- Spectral form `A = U·diag(λ)·U⋆` with the eigenvalue diagonal as a `ℂ`-valued function. -/
lemma spectral_UDU {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (fun i => (hA.eigenvalues i : ℂ))
        * ((star hA.eigenvectorUnitary : Matrix n n ℂ)) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [conjStarAlgAut_apply]
  rfl

/-- Spectral form of the matrix logarithm `log A = U·diag(log λ)·U⋆`. -/
lemma matLog_UDU {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    matLog hA = (hA.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (fun j => (Real.log (hA.eigenvalues j) : ℂ))
        * ((star hA.eigenvectorUnitary : Matrix n n ℂ)) := by
  rw [matLog, Matrix.IsHermitian.cfc, conjStarAlgAut_apply]
  rfl

/-- **Trace of `diag(p)·W·diag(l)·W⋆`** = `∑ᵢⱼ pᵢ · normSq(Wᵢⱼ) · lⱼ`.  Pure index expansion
    (`trace = ∑ diagonal`, `mul_apply`, `mul_diagonal`/`diagonal_mul`, `z·star z = normSq z`). -/
lemma trace_diag_W_diag_starW (p l : n → ℝ) (W : Matrix n n ℂ) :
    (diagonal (fun i => (p i : ℂ)) * W * diagonal (fun j => (l j : ℂ)) * star W).trace
      = ∑ i, ∑ j, ((p i * Complex.normSq (W i j) * l j : ℝ) : ℂ) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply]
  rw [show (p i : ℂ) * W i j * (l j : ℂ) * star (W i j)
        = (p i : ℂ) * (l j : ℂ) * (W i j * star (W i j)) from by ring,
    show star (W i j) = (starRingEnd ℂ) (W i j) from rfl, Complex.mul_conj]
  push_cast; ring

/-- **The cross-term trace from two spectral decompositions.**  `tr(ρ·L) = ∑ᵢⱼ pᵢ · normSq(Wᵢⱼ) · lⱼ`
    where `W = U⋆V`.  Pure trace cyclicity (`trace_mul_comm`) + the diagonal expansion above. -/
lemma crossTerm_trace_of_spectral (ρ L U V : Matrix n n ℂ) (p l : n → ℝ)
    (hρ : ρ = U * diagonal (fun i => (p i : ℂ)) * star U)
    (hL : L = V * diagonal (fun j => (l j : ℂ)) * star V) :
    (ρ * L).trace
      = ∑ i, ∑ j, ((p i * Complex.normSq ((star U * V) i j) * l j : ℝ) : ℂ) := by
  have hstar : star V * U = star (star U * V) := by rw [star_mul, star_star]
  rw [hρ, hL,
    show (U * diagonal (fun i => (p i : ℂ)) * star U) * (V * diagonal (fun j => (l j : ℂ)) * star V)
      = U * (diagonal (fun i => (p i : ℂ)) * star U * V * diagonal (fun j => (l j : ℂ)) * star V)
      from by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm,
    show (diagonal (fun i => (p i : ℂ)) * star U * V * diagonal (fun j => (l j : ℂ)) * star V) * U
      = diagonal (fun i => (p i : ℂ)) * (star U * V) * diagonal (fun j => (l j : ℂ)) * (star V * U)
      from by simp only [Matrix.mul_assoc],
    hstar, trace_diag_W_diag_starW]

/-- **The cross-term `tr(ρ · log σ) = ∑ᵢⱼ pᵢ Sᵢⱼ log qⱼ`** with overlap weights
    `S i j = normSq((U_ρ⋆ U_σ) i j)` — the off-diagonal term of the relative entropy. -/
lemma crossTerm_trace {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ * matLog hσ).trace
      = ∑ i, ∑ j, ((hρ.eigenvalues i
          * Complex.normSq ((star (hρ.eigenvectorUnitary : Matrix n n ℂ)
              * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j)
          * Real.log (hσ.eigenvalues j) : ℝ) : ℂ) :=
  crossTerm_trace_of_spectral ρ (matLog hσ) _ _ _ _ (spectral_UDU hρ) (matLog_UDU hσ)

/-- The overlap weights `S i j = normSq(Wᵢⱼ)` are **row-stochastic** when `W W⋆ = 1`. -/
lemma row_sum_normSq (W : Matrix n n ℂ) (hW : W * star W = 1) (i : n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have hC : ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
    push_cast
    rw [show (∑ j, (Complex.normSq (W i j) : ℂ)) = (W * star W) i i from by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun j _ => by
            rw [Matrix.star_apply, show star (W i j) = (starRingEnd ℂ) (W i j) from rfl,
              Complex.mul_conj], hW, Matrix.one_apply_eq]
  exact_mod_cast hC

/-- The overlap weights are **column-stochastic** when `W⋆ W = 1`. -/
lemma col_sum_normSq (W : Matrix n n ℂ) (hW : star W * W = 1) (j : n) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have hC : ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
    push_cast
    rw [show (∑ i, (Complex.normSq (W i j) : ℂ)) = (star W * W) j j from by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun i _ => by
            rw [Matrix.star_apply, show star (W i j) = (starRingEnd ℂ) (W i j) from rfl, mul_comm,
              Complex.mul_conj], hW, Matrix.one_apply_eq]
  exact_mod_cast hC

/-! ### Klein's inequality: `D(ρ‖σ) ≥ 0` -/

/-- **★★ Klein's inequality (quantum relative entropy is nonnegative).**  For positive-definite density
    matrices `ρ, σ` (unit trace), `D(ρ‖σ) = tr(ρ(log ρ − log σ)) ≥ 0`.  The finite-dimensional content of
    the axiom `RelEntPositivity.D_nonneg` / `ArakiInterface.Akre_nonneg`.

    Proof (doubly-stochastic / Jensen): the diagonal term is `∑ pᵢ log pᵢ` (`trace_mul_matLog`) and the
    cross term is `∑ᵢⱼ pᵢ Sᵢⱼ log qⱼ` (`crossTerm_trace`) with `S` the doubly-stochastic overlap matrix.
    Concavity of `log` (Jensen) gives `∑ⱼ Sᵢⱼ log qⱼ ≤ log rᵢ` with `rᵢ = ∑ⱼ Sᵢⱼ qⱼ` a probability vector,
    so `D(ρ‖σ) ≥ ∑ᵢ pᵢ log(pᵢ/rᵢ) = KL(p‖r) ≥ 0` (Gibbs, `RelEntPositivity.KL_classical_nonneg`). -/
theorem relEntropy_nonneg {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    0 ≤ relEntropy hρ.1 hσ.1 := by
  set U := (hρ.1.eigenvectorUnitary : Matrix n n ℂ) with hUd
  set V := (hσ.1.eigenvectorUnitary : Matrix n n ℂ) with hVd
  set p := hρ.1.eigenvalues with hpd
  set q := hσ.1.eigenvalues with hqd
  set W := star U * V with hWdef
  set S := fun i j => Complex.normSq (W i j) with hSdef
  set r := fun i => ∑ j, S i j * q j with hrdef
  -- positivity and unit sums of the spectra
  have hp_pos : ∀ i, 0 < p i := hρ.eigenvalues_pos
  have hq_pos : ∀ j, 0 < q j := hσ.eigenvalues_pos
  have hp_sum : ∑ i, p i = 1 := by
    have h : ρ.trace = ∑ i, ((p i : ℝ) : ℂ) := hρ.1.trace_eq_sum_eigenvalues
    rw [hρ1] at h; exact_mod_cast h.symm
  have hq_sum : ∑ j, q j = 1 := by
    have h : σ.trace = ∑ j, ((q j : ℝ) : ℂ) := hσ.1.trace_eq_sum_eigenvalues
    rw [hσ1] at h; exact_mod_cast h.symm
  have hS_nn : ∀ i j, 0 ≤ S i j := fun i j => Complex.normSq_nonneg _
  -- unitarity of the eigenbases
  have hUstar : star U * U = 1 := by rw [hUd]; exact Unitary.coe_star_mul_self _
  have hUstar' : U * star U = 1 := by rw [hUd]; exact Unitary.coe_mul_star_self _
  have hVstar : star V * V = 1 := by rw [hVd]; exact Unitary.coe_star_mul_self _
  have hVstar' : V * star V = 1 := by rw [hVd]; exact Unitary.coe_mul_star_self _
  -- the overlap matrix is doubly stochastic
  have hWWstar : W * star W = 1 := by
    have h : (star U * V) * star (star U * V) = star U * (V * star V) * U := by
      rw [star_mul, star_star]; simp only [Matrix.mul_assoc]
    rw [hWdef, h, hVstar', mul_one, hUstar]
  have hstarWW : star W * W = 1 := by
    have h : star (star U * V) * (star U * V) = star V * (U * star U) * V := by
      rw [star_mul, star_star]; simp only [Matrix.mul_assoc]
    rw [hWdef, h, hUstar', mul_one, hVstar]
  have hrow : ∀ i, ∑ j, S i j = 1 := fun i => row_sum_normSq W hWWstar i
  have hcol : ∀ j, ∑ i, S i j = 1 := fun j => col_sum_normSq W hstarWW j
  -- r is a probability vector
  have hr_pos : ∀ i, 0 < r i := by
    intro i
    simp only [hrdef]
    obtain ⟨j, _, hj⟩ : ∃ j ∈ Finset.univ, 0 < S i j := by
      by_contra hc; push_neg at hc
      have : ∑ j, S i j = 0 := Finset.sum_eq_zero fun j hj => le_antisymm (hc j hj) (hS_nn i j)
      rw [hrow i] at this; norm_num at this
    exact Finset.sum_pos' (fun k _ => mul_nonneg (hS_nn i k) (hq_pos k).le)
      ⟨j, Finset.mem_univ j, mul_pos hj (hq_pos j)⟩
  have hr_sum : ∑ i, r i = 1 := by
    simp only [hrdef]
    rw [Finset.sum_comm]
    rw [show (∑ j, ∑ i, S i j * q j) = ∑ j, (∑ i, S i j) * q j from
      Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]]
    simp only [hcol, one_mul, hq_sum]
  -- relative entropy as diagonal − cross term
  have hRE : relEntropy hρ.1 hσ.1
      = (∑ i, p i * Real.log (p i)) - ∑ i, ∑ j, p i * S i j * Real.log (q j) := by
    rw [relEntropy, mul_sub, Matrix.trace_sub, Complex.sub_re, trace_mul_matLog hρ,
      crossTerm_trace hρ.1 hσ.1]
    simp only [Complex.re_sum, Complex.ofReal_re]
    rfl
  -- Jensen: ∑ⱼ Sᵢⱼ log qⱼ ≤ log rᵢ
  have hjensen : ∀ i, ∑ j, S i j * Real.log (q j) ≤ Real.log (r i) := by
    intro i
    have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
      (t := Finset.univ) (w := S i) (p := q)
      (fun j _ => hS_nn i j) (hrow i) (fun j _ => hq_pos j)
    simpa only [smul_eq_mul, hrdef] using hJ
  -- the cross term is ≤ ∑ pᵢ log rᵢ
  have hcross_le : ∑ i, ∑ j, p i * S i j * Real.log (q j) ≤ ∑ i, p i * Real.log (r i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [show (∑ j, p i * S i j * Real.log (q j)) = p i * ∑ j, S i j * Real.log (q j) from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    exact mul_le_mul_of_nonneg_left (hjensen i) (hp_pos i).le
  -- KL(p‖r) ≥ 0 and split
  have hKL : 0 ≤ ∑ i, p i * Real.log (p i / r i) := by
    simpa only [RelEntPositivity.KL] using
      RelEntPositivity.KL_classical_nonneg Finset.univ p r (fun i _ => (hp_pos i).le)
        (fun i _ => hr_pos i) hp_sum hr_sum
  have hsplit : ∑ i, p i * Real.log (p i / r i)
      = (∑ i, p i * Real.log (p i)) - ∑ i, p i * Real.log (r i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Real.log_div (hp_pos i).ne' (hr_pos i).ne', mul_sub]
  rw [hRE]; linarith [hKL, hcross_le, hsplit.symm.le, hsplit.le]

/-- **Klein's equality case** (the hard direction): for positive-definite density matrices,
    `D(ρ‖σ) = 0 ⟹ ρ = σ`.  Tracking the equalities in the doubly-stochastic / Jensen proof of
    `relEntropy_nonneg`: `D = 0` forces (i) `KL(p‖r) = 0`, hence `p = r` (Gibbs equality, via
    `log x < x − 1` for `x ≠ 1`), and (ii) the strict-Jensen equality `∑ⱼ Sᵢⱼ log qⱼ = log rᵢ`,
    hence `qⱼ = rᵢ = pᵢ` whenever `Wᵢⱼ ≠ 0` (`StrictConcaveOn.map_sum_eq_iff'`).  Together these give
    `Wᵢⱼ·qⱼ = pᵢ·Wᵢⱼ`, i.e. `W·diag(q) = diag(p)·W`, whence `σ = V·diag(q)·V⋆ = U·diag(p)·U⋆ = ρ`. -/
theorem relEntropy_eq_zero {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (hD : relEntropy hρ.1 hσ.1 = 0) :
    ρ = σ := by
  set U := (hρ.1.eigenvectorUnitary : Matrix n n ℂ) with hUd
  set V := (hσ.1.eigenvectorUnitary : Matrix n n ℂ) with hVd
  set p := hρ.1.eigenvalues with hpd
  set q := hσ.1.eigenvalues with hqd
  set W := star U * V with hWdef
  set S := fun i j => Complex.normSq (W i j) with hSdef
  set r := fun i => ∑ j, S i j * q j with hrdef
  have hp_pos : ∀ i, 0 < p i := hρ.eigenvalues_pos
  have hq_pos : ∀ j, 0 < q j := hσ.eigenvalues_pos
  have hp_sum : ∑ i, p i = 1 := by
    have h : ρ.trace = ∑ i, ((p i : ℝ) : ℂ) := hρ.1.trace_eq_sum_eigenvalues
    rw [hρ1] at h; exact_mod_cast h.symm
  have hq_sum : ∑ j, q j = 1 := by
    have h : σ.trace = ∑ j, ((q j : ℝ) : ℂ) := hσ.1.trace_eq_sum_eigenvalues
    rw [hσ1] at h; exact_mod_cast h.symm
  have hS_nn : ∀ i j, 0 ≤ S i j := fun i j => Complex.normSq_nonneg _
  have hUstar : star U * U = 1 := by rw [hUd]; exact Unitary.coe_star_mul_self _
  have hUstar' : U * star U = 1 := by rw [hUd]; exact Unitary.coe_mul_star_self _
  have hVstar : star V * V = 1 := by rw [hVd]; exact Unitary.coe_star_mul_self _
  have hVstar' : V * star V = 1 := by rw [hVd]; exact Unitary.coe_mul_star_self _
  have hWWstar : W * star W = 1 := by
    have h : (star U * V) * star (star U * V) = star U * (V * star V) * U := by
      rw [star_mul, star_star]; simp only [Matrix.mul_assoc]
    rw [hWdef, h, hVstar', mul_one, hUstar]
  have hstarWW : star W * W = 1 := by
    have h : star (star U * V) * (star U * V) = star V * (U * star U) * V := by
      rw [star_mul, star_star]; simp only [Matrix.mul_assoc]
    rw [hWdef, h, hUstar', mul_one, hVstar]
  have hrow : ∀ i, ∑ j, S i j = 1 := fun i => row_sum_normSq W hWWstar i
  have hcol : ∀ j, ∑ i, S i j = 1 := fun j => col_sum_normSq W hstarWW j
  have hr_pos : ∀ i, 0 < r i := by
    intro i
    simp only [hrdef]
    obtain ⟨j, _, hj⟩ : ∃ j ∈ Finset.univ, 0 < S i j := by
      by_contra hc; push_neg at hc
      have : ∑ j, S i j = 0 := Finset.sum_eq_zero fun j hj => le_antisymm (hc j hj) (hS_nn i j)
      rw [hrow i] at this; norm_num at this
    exact Finset.sum_pos' (fun k _ => mul_nonneg (hS_nn i k) (hq_pos k).le)
      ⟨j, Finset.mem_univ j, mul_pos hj (hq_pos j)⟩
  have hr_sum : ∑ i, r i = 1 := by
    simp only [hrdef]
    rw [Finset.sum_comm,
      show (∑ j, ∑ i, S i j * q j) = ∑ j, (∑ i, S i j) * q j from
        Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]]
    simp only [hcol, one_mul, hq_sum]
  have hRE : relEntropy hρ.1 hσ.1
      = (∑ i, p i * Real.log (p i)) - ∑ i, ∑ j, p i * S i j * Real.log (q j) := by
    rw [relEntropy, mul_sub, Matrix.trace_sub, Complex.sub_re, trace_mul_matLog hρ,
      crossTerm_trace hρ.1 hσ.1]
    simp only [Complex.re_sum, Complex.ofReal_re]
    rfl
  have hjensen : ∀ i, ∑ j, S i j * Real.log (q j) ≤ Real.log (r i) := by
    intro i
    have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
      (t := Finset.univ) (w := S i) (p := q)
      (fun j _ => hS_nn i j) (hrow i) (fun j _ => hq_pos j)
    simpa only [smul_eq_mul, hrdef] using hJ
  -- `D = 0` ⟹ the cross-term Jensen step and the Gibbs step are both equalities
  rw [hRE] at hD
  have hcrosseq : ∑ i, p i * (∑ j, S i j * Real.log (q j)) = ∑ i, p i * Real.log (r i) := by
    have hKL : 0 ≤ ∑ i, p i * Real.log (p i / r i) :=
      RelEntPositivity.KL_classical_nonneg Finset.univ p r (fun i _ => (hp_pos i).le)
        (fun i _ => hr_pos i) hp_sum hr_sum
    have hsplit : ∑ i, p i * Real.log (p i / r i)
        = (∑ i, p i * Real.log (p i)) - ∑ i, p i * Real.log (r i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Real.log_div (hp_pos i).ne' (hr_pos i).ne', mul_sub]
    have hcross_le : ∑ i, p i * (∑ j, S i j * Real.log (q j)) ≤ ∑ i, p i * Real.log (r i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hjensen i) (hp_pos i).le
    have hBeq : (∑ i, ∑ j, p i * S i j * Real.log (q j))
        = ∑ i, p i * (∑ j, S i j * Real.log (q j)) :=
      Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hBeq] at hD
    linarith [hKL, hsplit, hcross_le, hD]
  -- (i) Gibbs equality ⟹ `p = r`
  have hpr_sum : ∑ i, p i * Real.log (p i / r i) = 0 := by
    have hsplit : ∑ i, p i * Real.log (p i / r i)
        = (∑ i, p i * Real.log (p i)) - ∑ i, p i * Real.log (r i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Real.log_div (hp_pos i).ne' (hr_pos i).ne', mul_sub]
    have hBeq : (∑ i, ∑ j, p i * S i j * Real.log (q j))
        = ∑ i, p i * (∑ j, S i j * Real.log (q j)) :=
      Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hBeq] at hD; rw [hsplit]; linarith [hcrosseq, hD]
  have heachG : ∀ i, p i * Real.log (p i / r i) = p i - r i := by
    have hge : ∀ i ∈ (Finset.univ : Finset n), p i - r i ≤ p i * Real.log (p i / r i) := by
      intro i _
      have h2 : 1 - r i / p i ≤ Real.log (p i / r i) := by
        have hlog := Real.log_le_sub_one_of_pos (div_pos (hr_pos i) (hp_pos i))
        rw [show p i / r i = (r i / p i)⁻¹ by rw [inv_div], Real.log_inv]; linarith
      have h3 : p i * (1 - r i / p i) = p i - r i := by
        field_simp [(hp_pos i).ne']
      nlinarith [mul_le_mul_of_nonneg_left h2 (hp_pos i).le, h3]
    have hsumeq : ∑ i, (p i - r i) = ∑ i, p i * Real.log (p i / r i) := by
      rw [hpr_sum, Finset.sum_sub_distrib, hp_sum, hr_sum]; ring
    intro i
    exact ((Finset.sum_eq_sum_iff_of_le hge).mp hsumeq i (Finset.mem_univ i)).symm
  have hpr : ∀ i, p i = r i := by
    intro i
    by_contra hne
    have hlt : 1 - r i / p i < Real.log (p i / r i) := by
      have hlog := Real.log_lt_sub_one_of_pos (div_pos (hr_pos i) (hp_pos i)) (by
        rw [Ne, div_eq_one_iff_eq (hp_pos i).ne']; exact fun h => hne h.symm)
      rw [show p i / r i = (r i / p i)⁻¹ by rw [inv_div], Real.log_inv]; linarith
    have h3 : p i * (1 - r i / p i) = p i - r i := by
      field_simp [(hp_pos i).ne']
    nlinarith [mul_lt_mul_of_pos_left hlt (hp_pos i), h3, heachG i]
  -- (ii) strict-Jensen equality ⟹ `qⱼ = pᵢ` whenever `Wᵢⱼ ≠ 0`
  have hjeq : ∀ i, ∑ j, S i j * Real.log (q j) = Real.log (r i) := by
    have heach : ∀ i ∈ Finset.univ,
        p i * (∑ j, S i j * Real.log (q j)) = p i * Real.log (r i) :=
      (Finset.sum_eq_sum_iff_of_le
        (fun i _ => mul_le_mul_of_nonneg_left (hjensen i) (hp_pos i).le)).mp hcrosseq
    intro i
    have := heach i (Finset.mem_univ i)
    exact mul_left_cancel₀ (hp_pos i).ne' this
  have hqp : ∀ i j, W i j ≠ 0 → q j = p i := by
    intro i j hWij
    have hSij : S i j ≠ 0 := by simp only [hSdef]; exact fun h => hWij (Complex.normSq_eq_zero.mp h)
    have hjenseni : Real.log (∑ j, S i j • q j) = ∑ j, S i j • Real.log (q j) := by
      simp only [smul_eq_mul]
      rw [show (∑ j, S i j * q j) = r i from rfl, hjeq i]
    have hthis := (strictConcaveOn_log_Ioi.map_sum_eq_iff' (t := Finset.univ)
      (w := S i) (p := q) (fun j _ => hS_nn i j) (hrow i) (fun j _ => hq_pos j)).mp
      hjenseni j (Finset.mem_univ j) hSij
    simp only [smul_eq_mul] at hthis
    rw [hthis]; exact (hpr i).symm
  -- `W·diag(q) = diag(p)·W` and the spectral reconstruction `σ = ρ`
  have hWmat : W * diagonal (fun j => (q j : ℂ)) = diagonal (fun i => (p i : ℂ)) * W := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hWij : W i j = 0
    · simp [hWij]
    · rw [hqp i j hWij]; ring
  have key : V * diagonal (fun j => (q j : ℂ)) * star V
      = U * diagonal (fun i => (p i : ℂ)) * star U := by
    have h : U * (W * diagonal (fun j => (q j : ℂ))) * star V
        = U * (diagonal (fun i => (p i : ℂ)) * W) * star V := by rw [hWmat]
    rw [hWdef] at h
    rw [show U * (star U * V * diagonal (fun j => (q j : ℂ))) * star V
        = U * star U * (V * diagonal (fun j => (q j : ℂ)) * star V) by simp only [Matrix.mul_assoc],
      hUstar', Matrix.one_mul,
      show U * (diagonal (fun i => (p i : ℂ)) * (star U * V)) * star V
        = U * diagonal (fun i => (p i : ℂ)) * star U * (V * star V) by simp only [Matrix.mul_assoc],
      hVstar', Matrix.mul_one] at h
    exact h
  rw [spectral_UDU hρ.1, spectral_UDU hσ.1, ← hUd, ← hVd, ← hpd, ← hqd, key]

/-! ### The Donald structural identities (concrete) -/

/-- **Cross entropy** `crossEnt(ρ,σ) = −tr(ρ log σ)` — the concrete realization of the opaque
    `Donald.crossEnt`.  The first argument is any matrix; the second is Hermitian (for `log`). -/
noncomputable def crossEntropy (ρ : Matrix n n ℂ) {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) : ℝ :=
  -(ρ * matLog hσ).trace.re

/-- **Entropy bridge** `S(ρ) = −tr(ρ log ρ)`: the spectral von Neumann entropy equals the operator form,
    for a positive-definite density.  (`negMulLog λ = −λ log λ`, summed = `−tr(ρ log ρ)`.) -/
theorem vonNeumannEntropy_eq_neg_trace {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (h : IsDensity ρ) :
    vonNeumannEntropy h = -(ρ * matLog hρ.1).trace.re := by
  rw [vonNeumannEntropy, trace_mul_matLog hρ, Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show Real.negMulLog (hρ.1.eigenvalues i) = -(hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i))
  rw [Real.negMulLog_eq_neg]

/-- **(A1) Donald identity `D(ρ‖σ) = crossEnt(ρ,σ) − H(ρ)`** — concrete; `D_eq_crossEnt_sub_H`. -/
theorem relEntropy_eq_crossEntropy_sub_entropy {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (h : IsDensity ρ) :
    relEntropy hρ.1 hσ.1 = crossEntropy ρ hσ.1 - vonNeumannEntropy h := by
  rw [relEntropy, crossEntropy, vonNeumannEntropy_eq_neg_trace hρ h, mul_sub, Matrix.trace_sub,
    Complex.sub_re]
  ring

/-- **(A3) Donald identity `crossEnt(ρ,ρ) = H(ρ)`** — concrete; `crossEnt_self`. -/
theorem crossEntropy_self {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (h : IsDensity ρ) :
    crossEntropy ρ hρ.1 = vonNeumannEntropy h := by
  rw [crossEntropy, vonNeumannEntropy_eq_neg_trace hρ h]

/-- **(A2) Cross entropy is linear in its first argument** — concrete; `crossEnt_mixture`.
    `crossEnt(∑ pₖ ρₖ, σ) = ∑ pₖ crossEnt(ρₖ, σ)` (trace linearity), for ANY weights `p`. -/
theorem crossEntropy_sum {ι : Type*} (s : Finset ι) (p : ι → ℝ) (ρ : ι → Matrix n n ℂ)
    {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) :
    crossEntropy (∑ k ∈ s, (p k : ℂ) • ρ k) hσ = ∑ k ∈ s, p k * crossEntropy (ρ k) hσ := by
  simp only [crossEntropy]
  rw [Finset.sum_mul,
    show (∑ k ∈ s, ((p k : ℂ) • ρ k) * matLog hσ) = ∑ k ∈ s, (p k : ℂ) • (ρ k * matLog hσ) from
      Finset.sum_congr rfl fun k _ => smul_mul_assoc _ _ _,
    Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul]
  rw [Complex.re_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [Complex.re_ofReal_mul]; ring

/-! ### The concrete `DonaldSystem` instance (Hermitian matrices)

This discharges the `DonaldSystem` typeclass — the former opaque `Donald` axioms (state type,
relative entropy, entropy, cross-entropy, mixture, and the three structural identities) — for the
genuine finite-dimensional model.  `D`, `H`, `crossEnt` are the trace forms; the three identities
are `rfl` (A1, A3, definitional) and `crossEntropy_sum` (A2, trace linearity). -/

/-- The state type for the concrete Donald system: Hermitian matrices of a fixed finite dimension. -/
def HermitianMat (n : Type) [Fintype n] [DecidableEq n] : Type := {A : Matrix n n ℂ // A.IsHermitian}

/-- **The Donald relative-entropy system on Hermitian matrices.**  Realizes the `DonaldSystem`
    typeclass concretely, axiom-free — the witness that the former opaque `Donald` axioms hold for a
    genuine model (the finite-dimensional Umegaki relative entropy). -/
noncomputable instance instDonaldSystemHermitianMat {m : Type} [Fintype m] [DecidableEq m] :
    DonaldSystem (HermitianMat m) where
  D ρ σ := -((ρ.1 * matLog σ.2).trace.re) - -((ρ.1 * matLog ρ.2).trace.re)
  H ρ := -((ρ.1 * matLog ρ.2).trace.re)
  crossEnt ρ σ := -((ρ.1 * matLog σ.2).trace.re)
  mixture s p ρ := ⟨∑ k ∈ s, (p k : ℂ) • (ρ k).1, by
    show (∑ k ∈ s, (p k : ℂ) • (ρ k).1)ᴴ = ∑ k ∈ s, (p k : ℂ) • (ρ k).1
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_smul, (ρ k).2.eq]
    congr 1
    exact Complex.conj_ofReal (p k)⟩
  D_eq_crossEnt_sub_H _ _ := rfl
  crossEnt_mixture s p ρ σ := crossEntropy_sum s p (fun k => (ρ k).1) σ.2
  crossEnt_self _ := rfl

end QIQTH.QuantumEntropy
