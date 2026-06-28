/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E4 (witness) — the Klein twist on the actual fermion parity `(−1)^N`

The abstract Klein-twist algebra (`QIQTH/Fock/Dirac/KleinTwist*.lean`) holds for any self-adjoint
involution `γ` in a ℂ-*-algebra: `Z²=γ`, `Z⁴=1`, `Z*Z=ZZ*=1`, `[Z,γ]=0`.  This module **witnesses it is
non-vacuous** on the genuine single-mode fermion parity operator `Γ = (−1)^N = diag(1, −1)` (empty mode
`+1`, occupied mode `−1`) — a concrete `2×2` self-adjoint unitary involution on the single-fermion Fock
space `ℂ²`.  So the Klein twist `Z = (1 + iΓ)/(1 + i)` of the real electron parity is a concrete operator
satisfying all four defining relations: the twisted-duality intertwiner is realized, not just postulated.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Dirac only.  (The
field-level second-quantized `Γ = (−1)^F` on the full CAR Fock + the operator-algebra twisted-duality
*theorem* `𝓕(W)'=Z𝓕(W')Z*` remain the E5 GNS frontier; this witnesses the algebra on the single mode.)
-/
import QIQTH.Fock.Dirac.KleinTwistUnitary
import QIQTH.Fock.Dirac.ModularKMS
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace QIQTH.Fock.Dirac

open Complex Matrix

/-- The **single-mode fermion parity** `Γ = (−1)^N = diag(1, −1)` — the parity operator on the
single-fermion Fock space `ℂ²` (empty mode `+1`, occupied mode `−1`). -/
def fermionParity : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]

/-- `Γ` is an **involution**: `Γ² = 1`. -/
theorem fermionParity_involutive : fermionParity * fermionParity = 1 := by
  unfold fermionParity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply]

/-- `Γ` is **self-adjoint**: `Γ* = Γ` (a real diagonal matrix). -/
theorem fermionParity_selfAdjoint : star fermionParity = fermionParity := by
  unfold fermionParity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.star_apply, Matrix.diagonal_apply, eq_comm]

/-- **Witness `Z² = Γ`** on the real fermion parity (instantiating `kleinTwist_sq`). -/
theorem electron_kleinTwist_sq :
    kleinTwist fermionParity * kleinTwist fermionParity = fermionParity :=
  kleinTwist_sq fermionParity_involutive

/-- **Witness `Z* Z = 1`** (left unitarity) on the real fermion parity. -/
theorem electron_kleinTwist_star_unitary :
    star (kleinTwist fermionParity) * kleinTwist fermionParity = 1 :=
  kleinTwist_star_mul_self fermionParity_selfAdjoint fermionParity_involutive

/-- **Witness `Z Z* = 1`** (right unitarity) on the real fermion parity — so `Z` is a genuine (two-sided)
unitary on the single-fermion space. -/
theorem electron_kleinTwist_unitary :
    kleinTwist fermionParity * star (kleinTwist fermionParity) = 1 :=
  kleinTwist_mul_star_self fermionParity_selfAdjoint fermionParity_involutive

/-- **Witness `[Z, Γ] = 0`** on the real fermion parity — the twist preserves the `(−1)^N` grading. -/
theorem electron_kleinTwist_comm :
    kleinTwist fermionParity * fermionParity = fermionParity * kleinTwist fermionParity :=
  kleinTwist_comm_gamma fermionParity

/-- **Parity is `(−1)^N`**: `Γ = 1 − 2N` on the single mode.  The fermion parity operator (the Klein-twist
input) is exactly `(−1)^N` of the number operator (the modular-Hamiltonian input, `K = βω·N`): `diag(1,−1)
= 1 − 2·diag(0,1)`.  This ties the twisted-duality grading to the modular dynamics — `Γ` and `K = βω·N` are
both functions of `N`, hence simultaneously diagonal. -/
theorem fermionParity_eq_one_sub_two_numberOp :
    fermionParity = 1 - (2 : ℂ) • numberOp := by
  unfold fermionParity numberOp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply,
      smul_eq_mul] <;> norm_num

/-- **The modular flow preserves the parity grading**: `σ_t(Γ) = Γ`.  Since `Γ = (−1)^N = diag(1,−1)` is
diagonal, the electron's real-time modular flow fixes it (`electron_sigmaDiag_fixes_diagonal`).  So the
fermion-parity grading — the `ℤ₂` structure carrying the even/odd records — is **conserved by the modular
dynamics** at the concrete operator level: a record of definite parity stays that parity under `σ_t`. -/
theorem electron_sigmaDiag_fixes_parity (β ω t : ℝ) :
    QIQTH.FiniteModularTheory.sigmaDiag (electronModeOcc β ω) t fermionParity = fermionParity :=
  electron_sigmaDiag_fixes_diagonal β ω t ![1, -1]

/-- **The Klein twist commutes with the number operator**: `Z·N = N·Z`.  Since `Z` commutes with the parity
`Γ = 1 − 2N` (`kleinTwist_comm_gamma`) and `N = (1 − Γ)/2`, the twist commutes with `N` too — both `Z` and
`N` are functions of the single conserved `N`. -/
theorem electron_kleinTwist_comm_numberOp :
    kleinTwist fermionParity * numberOp = numberOp * kleinTwist fermionParity := by
  set Z := kleinTwist fermionParity with hZ
  have h : Z * fermionParity = fermionParity * Z := kleinTwist_comm_gamma fermionParity
  rw [fermionParity_eq_one_sub_two_numberOp] at h
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc] at h
  exact smul_right_injective _ two_ne_zero (sub_right_inj.mp h)

/-- **The twisted-duality intertwiner `Z` commutes with the modular Hamiltonian `K = βω·N`**: `Z·K = K·Z`.
Since `Z` commutes with `N` (`electron_kleinTwist_comm_numberOp`) and `K = βω·N`, the Klein twist is a
**modular invariant** — it commutes with the modular Hamiltonian, hence with the modular flow `σ_t`.  So the
twisted modular duality `𝓕(W)'=Z𝓕(W')Z*` is **compatible with the modular dynamics**: the spin–statistics
twist `Z` is conserved by the boost/modular flow (the consistency of the E4 twisted duality with the E6/E9
modular tier). -/
theorem electron_kleinTwist_comm_modHamiltonian (β ω : ℝ) :
    kleinTwist fermionParity * modHamiltonian β ω
      = modHamiltonian β ω * kleinTwist fermionParity := by
  unfold modHamiltonian
  rw [mul_smul_comm, smul_mul_assoc, electron_kleinTwist_comm_numberOp]

end QIQTH.Fock.Dirac
