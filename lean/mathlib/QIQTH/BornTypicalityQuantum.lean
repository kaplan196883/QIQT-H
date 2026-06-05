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
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Positive
import QIQTH.BornTypicalityFinite

namespace QIQTH
namespace BornTypicalityQuantum

open Finset Matrix
open scoped ComplexOrder

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

/-- The coarse-grained product POVM effect of an event `S` of histories:
    `F_S = ∑_{ω ∈ S} ⊗ₜ E(ωₜ)`.  (POVM outcomes are alternatives, so the effects
    ADD — no amplitude interference.) -/
noncomputable def eventEffect (E : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (S : Finset (Fin n → Fin m)) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ ω ∈ S, kronN (fun t => E (ω t))

/-- **The event weight is a genuine quantum probability** (no amplitude summing):
    `tr( ρ^⊗ⁿ · F_S ) = ∑_{ω ∈ S} quantumWeight ρ E ω`, by trace linearity. -/
theorem trace_eventEffect_eq_sum (ρ : Matrix (Fin d) (Fin d) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (S : Finset (Fin n → Fin m)) :
    (kronN (fun _ : Fin n => ρ) * eventEffect E S).trace = ∑ ω ∈ S, quantumWeight ρ E ω := by
  rw [eventEffect, Finset.mul_sum, Matrix.trace_sum]
  rfl

/-- **Quantum Born-typicality, event-effect form.**  The quantum probability
    `tr(ρ^⊗ⁿ · F_bad)` of the coarse-grained bad-frequency POVM effect is
    `≤ p k·(1−p k)/(n·ε²)` — manifestly a probability of a POVM event, not a
    sum of amplitudes. -/
theorem quantum_chebyshev_freq_event (ρ : Matrix (Fin d) (Fin d) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.IsHermitian) (hE : ∀ k, (E k).IsHermitian)
    (hp0 : ∀ k, 0 ≤ bornProb ρ E k) (hp1 : ∑ k, bornProb ρ E k = 1)
    (k : Fin m) {ε : ℝ} (hε : 0 < ε) (hn : 0 < n) :
    (kronN (fun _ : Fin n => ρ) * eventEffect E ((univ : Finset (Fin n → Fin m)).filter
        (fun ω => ((n : ℝ) * ε) ^ 2
          ≤ (BornTypicalityFinite.count k ω - (n : ℝ) * bornProb ρ E k) ^ 2))).trace.re
      ≤ bornProb ρ E k * (1 - bornProb ρ E k) / ((n : ℝ) * ε ^ 2) := by
  rw [trace_eventEffect_eq_sum]
  exact quantum_chebyshev_freq ρ E hρ hE hp0 hp1 k hε hn

/-- `tr(vv* · E) = v* · (E v)` (rank-one trace as a quadratic form). -/
theorem trace_vecMulVec_mul_eq {N : ℕ} (v : Fin N → ℂ) (E : Matrix (Fin N) (Fin N) ℂ) :
    (vecMulVec v (star v) * E).trace = star v ⬝ᵥ (E *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Trace of a product of two PSD matrices is nonnegative** (`0 ≤ tr(ρ·E)` in `ℂ`).
    Proved via the rank-one decomposition `ρ = ∑ᵢ vᵢ vᵢ*` and the quadratic-form
    nonnegativity of the PSD `E`. -/
theorem trace_mul_nonneg {N : ℕ} {ρ E : Matrix (Fin N) (Fin N) ℂ}
    (hρ : ρ.PosSemidef) (hE : E.PosSemidef) : 0 ≤ (ρ * E).trace := by
  obtain ⟨k, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hρ
  rw [hv, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [trace_vecMulVec_mul_eq]
  exact hE.dotProduct_mulVec_nonneg (v i)

/-- **Born weights are nonnegative** (`0 ≤ tr(ρ Eₖ)`) for PSD `ρ` and PSD effects. -/
theorem bornProb_nonneg {ρ : Matrix (Fin d) (Fin d) ℂ} {E : Fin m → Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (hE : ∀ k, (E k).PosSemidef) (k : Fin m) :
    0 ≤ bornProb ρ E k := by
  have h := trace_mul_nonneg hρ (hE k)
  simpa [bornProb] using (Complex.le_def.mp h).1

/-- **The Born weights sum to one** (`∑ₖ tr(ρ Eₖ) = tr(ρ·∑E) = tr ρ = 1`), from POVM
    completeness `∑ E = 1` and unit trace `tr ρ = 1`. -/
theorem bornProb_sum (ρ : Matrix (Fin d) (Fin d) ℂ) (E : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hEsum : ∑ k, E k = 1) (hρtr : Matrix.trace ρ = 1) :
    ∑ k, bornProb ρ E k = 1 := by
  simp only [bornProb]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hEsum, Matrix.mul_one, hρtr,
    Complex.one_re]

/-- **Quantum Born-typicality for a genuine density matrix + POVM (no residual).**
    From `ρ` PSD with unit trace and a POVM `E` (each `Eₖ` PSD, `∑ E = 1`), ALL of
    Hermiticity, nonnegativity (`0 ≤ tr(ρ Eₖ)`) and normalization (`∑ bornProb = 1`)
    are discharged: the quantum probability of measuring a frequency `ε`-far from the
    Born weight `tr(ρ Eₖ)`, over `n` product copies, is `≤ p k·(1−p k)/(n·ε²)`. -/
theorem quantum_chebyshev_freq_density (ρ : Matrix (Fin d) (Fin d) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (hE : ∀ k, (E k).PosSemidef)
    (hEsum : ∑ k, E k = 1) (hρtr : Matrix.trace ρ = 1)
    (k : Fin m) {ε : ℝ} (hε : 0 < ε) (hn : 0 < n) :
    (∑ ω ∈ (univ : Finset (Fin n → Fin m)).filter
        (fun ω => ((n : ℝ) * ε) ^ 2
          ≤ (BornTypicalityFinite.count k ω - (n : ℝ) * bornProb ρ E k) ^ 2),
        quantumWeight ρ E ω).re
      ≤ bornProb ρ E k * (1 - bornProb ρ E k) / ((n : ℝ) * ε ^ 2) :=
  quantum_chebyshev_freq ρ E hρ.1 (fun k => (hE k).1) (bornProb_nonneg hρ hE)
    (bornProb_sum ρ E hEsum hρtr) k hε hn

end BornTypicalityQuantum
end QIQTH
