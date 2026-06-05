/-
  Quantum bridge for finite Born-typicality.

  `BornTypicalityFinite` proves the Chebyshev weak law for an ABSTRACT probability
  vector `p`.  This file connects `p` to genuine quantum data: for a density
  matrix `ρ` and a finite POVM `E`, the Born weights `p k = tr(ρ Eₖ)` ARE the
  i.i.d. product weights of an N-copy product measurement.  The key lemma is the
  tensor trace factorization (no independence is smuggled in — it is DERIVED from
  the product structure of `ρ^⊗N` and `⊗ₜ E(ωₜ)`):

      tr( (⊗ₜ ρ) · (⊗ₜ E(ωₜ)) ) = ∏ₜ tr(ρ · E(ωₜ)).

  We use a direct product-basis `N`-fold tensor `kronN` (indices `Fin n → Fin d`),
  avoiding Kronecker-associativity bookkeeping.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import QIQTH.BornTypicalityFinite

namespace QIQTH
namespace BornTypicalityQuantum

open Finset Matrix

variable {n d m : ℕ}

/-- The `n`-fold tensor product of matrices `A t`, on the product basis
    `Fin n → Fin d`: `(kronN A) x y = ∏ t, A t (x t) (y t)`. -/
def kronN (A : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  fun x y => ∏ t, A t (x t) (y t)

/-- **Trace of a product tensor factorizes:** `tr(⊗ₜ A t) = ∏ₜ tr(A t)`. -/
theorem trace_kronN (A : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    (kronN A).trace = ∏ t, (A t).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, kronN]
  rw [Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset (Fin d))) (fun t j => A t j j),
    Fintype.piFinset_univ]

/-- **Tensor multiplicativity of `kronN`:** `(⊗ₜ A t)·(⊗ₜ B t) = ⊗ₜ (A t · B t)`. -/
theorem kronN_mul (A B : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    kronN A * kronN B = kronN (fun t => A t * B t) := by
  funext x y
  simp only [Matrix.mul_apply, kronN]
  rw [Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset (Fin d)))
        (fun t j => A t (x t) j * B t j (y t)), Fintype.piFinset_univ]
  exact Finset.sum_congr rfl (fun z _ => (Finset.prod_mul_distrib).symm)

/-- **The product trace factorization** (no independence smuggling):
    `tr( (⊗ₜ A t)·(⊗ₜ B t) ) = ∏ₜ tr(A t · B t)`. -/
theorem trace_kronN_mul (A B : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    (kronN A * kronN B).trace = ∏ t, (A t * B t).trace := by
  rw [kronN_mul, trace_kronN]

/- ── Born weights and the quantum→classical bridge ────────────────── -/

/-- Born weight of effect `Eₖ` in state `ρ`: `p k = (tr(ρ·Eₖ)).re`. -/
noncomputable def bornProb (ρ : Matrix (Fin d) (Fin d) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (k : Fin m) : ℝ :=
  (Matrix.trace (ρ * E k)).re

/-- For Hermitian `ρ` and `Eₖ`, `tr(ρ·Eₖ)` is real: `↑(bornProb ρ E k) = tr(ρ·Eₖ)`. -/
theorem bornProb_ofReal (ρ : Matrix (Fin d) (Fin d) ℂ) (E : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.IsHermitian) (hE : ∀ k, (E k).IsHermitian) (k : Fin m) :
    ((bornProb ρ E k : ℝ) : ℂ) = Matrix.trace (ρ * E k) := by
  apply Complex.conj_eq_iff_re.mp
  show star (Matrix.trace (ρ * E k)) = Matrix.trace (ρ * E k)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, (hE k).eq, hρ.eq,
    Matrix.trace_mul_comm]

/-- The quantum weight (Born amplitude) of an `N`-trial product-measurement history `ω`:
    `tr( ρ^⊗N · (⊗ₜ E(ωₜ)) )`. -/
noncomputable def quantumWeight (ρ : Matrix (Fin d) (Fin d) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (ω : Fin n → Fin m) : ℂ :=
  (kronN (fun _ : Fin n => ρ) * kronN (fun t => E (ω t))).trace

/-- **The quantum→classical bridge:** the `N`-copy product-measurement weight of `ω`
    equals the classical product weight of the BORN vector — `p k = tr(ρ Eₖ)` is not
    assumed, it is what the tensor structure forces.  (Hence no independence is
    smuggled in: the product structure is derived from `ρ^⊗N` and `⊗ₜ E(ωₜ)`.) -/
theorem quantumWeight_eq_w (ρ : Matrix (Fin d) (Fin d) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.IsHermitian) (hE : ∀ k, (E k).IsHermitian)
    (ω : Fin n → Fin m) :
    quantumWeight ρ E ω = ((BornTypicalityFinite.w (bornProb ρ E) ω : ℝ) : ℂ) := by
  rw [quantumWeight, trace_kronN_mul, BornTypicalityFinite.w, Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun t _ => (bornProb_ofReal ρ E hρ hE (ω t)).symm)

/-- **Quantum Born-typicality (end-to-end).**  For a Hermitian state `ρ` and
    Hermitian POVM effects `E` whose Born weights form a probability vector
    (`0 ≤ bornProb`, `∑ bornProb = 1`), the total quantum weight of the
    bad-frequency event `(count − n·p k)² ≥ (n·ε)²` over `n` product copies is at
    most `p k·(1 − p k)/(n·ε²)` — i.e. measured frequencies are typically the
    Born weights `tr(ρ Eₖ)`, with the i.i.d. product structure DERIVED (via
    `quantumWeight_eq_w`) from `ρ^⊗ⁿ` and the product POVM, not assumed. -/
theorem quantum_chebyshev_freq (ρ : Matrix (Fin d) (Fin d) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.IsHermitian) (hE : ∀ k, (E k).IsHermitian)
    (hp0 : ∀ k, 0 ≤ bornProb ρ E k) (hp1 : ∑ k, bornProb ρ E k = 1)
    (k : Fin m) {ε : ℝ} (hε : 0 < ε) (hn : 0 < n) :
    (∑ ω ∈ (univ : Finset (Fin n → Fin m)).filter
        (fun ω => ((n : ℝ) * ε) ^ 2
          ≤ (BornTypicalityFinite.count k ω - (n : ℝ) * bornProb ρ E k) ^ 2),
        quantumWeight ρ E ω).re
      ≤ bornProb ρ E k * (1 - bornProb ρ E k) / ((n : ℝ) * ε ^ 2) := by
  have hconv : (∑ ω ∈ (univ : Finset (Fin n → Fin m)).filter
        (fun ω => ((n : ℝ) * ε) ^ 2
          ≤ (BornTypicalityFinite.count k ω - (n : ℝ) * bornProb ρ E k) ^ 2),
        quantumWeight ρ E ω).re
      = ∑ ω ∈ (univ : Finset (Fin n → Fin m)).filter
          (fun ω => ((n : ℝ) * ε) ^ 2
            ≤ (BornTypicalityFinite.count k ω - (n : ℝ) * bornProb ρ E k) ^ 2),
          BornTypicalityFinite.w (bornProb ρ E) ω := by
    rw [Finset.sum_congr rfl (fun ω _ => quantumWeight_eq_w ρ E hρ hE ω),
      ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hconv]
  exact BornTypicalityFinite.chebyshev_freq (bornProb ρ E) hp0 hp1 k hε hn

end BornTypicalityQuantum
end QIQTH
