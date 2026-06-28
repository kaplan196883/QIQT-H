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

/-- The electron mode's thermal state is **faithful (invertible)** — both occupations are nonzero
(`0 < n < 1`), so it is a genuine cyclic-separating modular state and the proved `kms_condition` /
`modAut_stateOf_invariant` of `FiniteModularTheory` apply to it. -/
noncomputable instance electronModeThermalState_invertible (β ω : ℝ) :
    Invertible (electronModeThermalState β ω) := by
  apply Matrix.invertibleOfIsUnitDet
  rw [electronModeThermalState, Matrix.det_diagonal, Fin.prod_univ_two]
  rw [isUnit_iff_ne_zero]
  have hn0 : (fermiDirac β ω : ℂ) ≠ 0 := by
    exact_mod_cast (fermiDirac_pos β ω).ne'
  have hn1 : (1 : ℂ) - (fermiDirac β ω : ℂ) ≠ 0 := by
    have : ((1 - fermiDirac β ω : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith [fermiDirac_lt_one β ω] : (1 - fermiDirac β ω : ℝ) ≠ 0)
    simpa using this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact mul_ne_zero hn1 hn0

/-- **The electron thermal state satisfies the Tomita–Takesaki KMS condition.**  Instantiating the
proved `FiniteModularTheory.kms_condition` for the electron mode: `ω(x·y) = ω(y·σ(x))` where
`ω = stateOf ρ` is the FD/Unruh KMS state and `σ = modAut ρ` is its modular automorphism — the defining
KMS relation, now holding for the electron. -/
theorem electron_kms_condition (β ω : ℝ) (x y : Matrix (Fin 2) (Fin 2) ℂ) :
    QIQTH.FiniteModularTheory.stateOf (electronModeThermalState β ω) (x * y)
      = QIQTH.FiniteModularTheory.stateOf (electronModeThermalState β ω)
          (y * QIQTH.FiniteModularTheory.modAut (electronModeThermalState β ω) x) :=
  QIQTH.FiniteModularTheory.kms_condition (electronModeThermalState β ω) x y

/-- **The electron's modular flow conserves its thermal (Born/Gibbs) expectations**:
`ω(σ(x)) = ω(x)` — the σ-invariance of the modular state (`modAut_stateOf_invariant`) for the electron
KMS state. -/
theorem electron_modAut_invariant (β ω : ℝ) (x : Matrix (Fin 2) (Fin 2) ℂ) :
    QIQTH.FiniteModularTheory.stateOf (electronModeThermalState β ω)
        (QIQTH.FiniteModularTheory.modAut (electronModeThermalState β ω) x)
      = QIQTH.FiniteModularTheory.stateOf (electronModeThermalState β ω) x :=
  QIQTH.FiniteModularTheory.modAut_stateOf_invariant (electronModeThermalState β ω) x

/-- **Detailed balance / the Gibbs–Boltzmann factor**: the ratio of occupied to empty probability is the
Boltzmann factor, `n/(1−n) = e^{−βω}`.  This is the multiplicative (KMS detailed-balance) form of the
Fermi–Dirac occupation — the content of the KMS condition for a single mode. -/
theorem electron_gibbs_ratio (β ω : ℝ) :
    fermiDirac β ω / (1 - fermiDirac β ω) = Real.exp (-(β * ω)) := by
  have hpos := fermiDirac_pos β ω
  have hlt := fermiDirac_lt_one β ω
  have h1 : 1 - fermiDirac β ω = Real.exp (β * ω) * fermiDirac β ω := by
    have hb := fermiDirac_kms_balance β ω
    rw [Real.exp_neg] at hb
    have he : Real.exp (β * ω) ≠ 0 := (Real.exp_pos _).ne'
    field_simp at hb ⊢
    linarith [hb]
  rw [h1, Real.exp_neg]
  rw [div_eq_iff (by positivity)]
  field_simp

end QIQTH.Fock.Dirac
