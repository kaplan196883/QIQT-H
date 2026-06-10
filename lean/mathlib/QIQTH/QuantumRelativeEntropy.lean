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

  THIS INCREMENT (the spectral entropy layer, axiom-free).  We define a finite
  density matrix (`IsDensity`: positive semidefinite, unit trace), prove its
  eigenvalues lie in `[0,1]` and sum to `1`, define the von Neumann entropy
  `S(ρ) = ∑ᵢ negMulLog(λᵢ) = −∑ᵢ λᵢ log λᵢ`, and prove `S(ρ) ≥ 0` — the concrete
  content of the (currently opaque) entropy object `H`.

  NEXT MILESTONES (documented, not yet built).
    * Hermitian matrix logarithm `log ρ := U · diag(log λ) · U⋆` from the spectral
      theorem — the gating primitive Mathlib lacks.
    * Cross entropy `crossEnt(ρ,σ) = −tr(ρ log σ)` and relative entropy
      `D(ρ‖σ) = tr ρ(log ρ − log σ)`; the Donald structural identities
      (`D = crossEnt − H`, `crossEnt(ρ,ρ) = H(ρ)`, linearity) then become direct.
    * Klein's inequality `D(ρ‖σ) ≥ 0` (operator convexity of `x ↦ x log x`) — retires
      `RelEntPositivity.D_nonneg` in the finite-dimensional case.
    The Araki / continuum / data-processing (Lieb) versions remain the cited frontier.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace QIQTH.QuantumEntropy

open Matrix Real BigOperators
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

end QIQTH.QuantumEntropy
