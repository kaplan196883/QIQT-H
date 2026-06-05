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
import Mathlib.Data.Complex.Basic

namespace QIQTH
namespace BornTypicalityQuantum

open Finset Matrix

variable {n d : ℕ}

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

end BornTypicalityQuantum
end QIQTH
