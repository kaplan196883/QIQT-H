/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E5/E6 — the electron mode wired into the existing Tomita–Takesaki machinery

QIQT-H already has the finite Tomita–Takesaki modular flow (`QIQTH/FiniteModularTheory.lean`:
`modAut ρ x = ρ x ⅟ρ` = `Δ`-conjugation, the KMS state `stateOf ρ x = tr(ρ x)`, and the proved
`kms_condition`) and the continuum `Δ^{it} = modFlow` (`QIQTH/Spectral/SpectralTheorem.lean`).  This
module connects the electron's **Fermi–Dirac occupation** (`QIQTH/Fock/Dirac/FermiDirac.lean`) to that
machinery: the **modular / KMS state of a single fermionic mode has Fermi–Dirac occupation**.

A single fermionic mode is a qubit; its thermal (Gibbs/KMS) density matrix is
`ρ = diag(1 − n, n)` with `n = fermiDirac β ω`, and the number operator is `N = diag(0, 1)`.  Then the
modular-state expectation `stateOf ρ N = tr(ρ N) = n = fermiDirac β ω` — the FD occupation IS the KMS
expectation of the existing finite Tomita–Takesaki state, and `ρ` is a faithful state (`tr ρ = 1`,
invertible since `0 < n < 1`) so the proved `kms_condition` / `modAut` apply to it.  This is the E6
boost-KMS content (`β = 2π` ⟹ the Unruh occupation) realized inside the project's own modular flow,
not a separate axiom.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.

HONEST scope: this is the single-mode (finite, Type I) realization — the FD occupation as the finite
KMS-state expectation, on the existing `FiniteModularTheory`.  The continuum wedge modular flow
`Δ_W^{it} = U(Λ_W(−2πt))` for the CAR net (the full E5) rides the continuum `modFlow` /
`Spectral/SpectralTheorem` + the `StandardSubspace`/crossed-product tracks; the Klein twist for the
fermionic `J` is `QIQTH/Fock/Dirac/KleinTwist*`.  Free Dirac only.
-/
import QIQTH.FiniteModularTheory
import QIQTH.Fock.Dirac.FermiDirac

namespace QIQTH.Fock.Dirac

open scoped Matrix
open Matrix

/-- The **thermal (KMS/Gibbs) density matrix of a single electron mode**: the qubit state
`ρ = diag(1 − n, n)` with occupation `n = fermiDirac β ω`. -/
noncomputable def electronModeThermalState (β ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1 - (fermiDirac β ω : ℂ), (fermiDirac β ω : ℂ)]

/-- The **number operator** of a single mode: `N = diag(0, 1)` (the projector onto the occupied
level). -/
noncomputable def numberOp : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, 1]

/-- The thermal density matrix is a **normalized state**: `tr ρ = 1` (`(1 − n) + n = 1`). -/
@[simp] theorem electronModeThermalState_trace (β ω : ℝ) :
    Matrix.trace (electronModeThermalState β ω) = 1 := by
  unfold electronModeThermalState
  rw [Matrix.trace_diagonal, Fin.sum_univ_two]
  simp

/-- **The Fermi–Dirac occupation is the modular / KMS-state expectation of the number operator.**
`stateOf ρ N = tr(ρ N) = fermiDirac β ω`.  So the electron's thermal occupation (`E6`) is exactly the
expectation of `N` in the finite Tomita–Takesaki KMS state `ω(·) = tr(ρ ·)` of
`QIQTH/FiniteModularTheory.lean` — wiring the FD occupation into the project's modular flow. -/
theorem electron_occupation_eq_fermiDirac (β ω : ℝ) :
    QIQTH.FiniteModularTheory.stateOf (electronModeThermalState β ω) numberOp
      = (fermiDirac β ω : ℂ) := by
  unfold QIQTH.FiniteModularTheory.stateOf electronModeThermalState numberOp
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two]
  simp

end QIQTH.Fock.Dirac
