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
import QIQTH.Fock.Dirac.QuasiFreeEntropy
import QIQTH.RecordContract
import Mathlib.LinearAlgebra.Matrix.Hermitian

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

/-- **The electron's modular flow fixes its own state**: `σ(ρ) = ρ` (`modAut ρ ρ = ρ`).  The KMS state
is a fixed point of its modular automorphism. -/
@[simp] theorem electron_modAut_self (β ω : ℝ) :
    QIQTH.FiniteModularTheory.modAut (electronModeThermalState β ω) (electronModeThermalState β ω)
      = electronModeThermalState β ω := by
  unfold QIQTH.FiniteModularTheory.modAut
  rw [mul_assoc, mul_invOf_self, mul_one]

/-- **The number operator (the record/charge) is a modular invariant**: `σ(N) = N`
(`modAut ρ N = N`).  Because `N` and the thermal state `ρ` are both diagonal they commute, so the
electron's modular flow fixes the number operator — the QIQT-H statement that the modular (KMS) dynamics
**conserves the record / charge**.  (The record `N` is among the even observables of §0.) -/
@[simp] theorem electron_modAut_numberOp (β ω : ℝ) :
    QIQTH.FiniteModularTheory.modAut (electronModeThermalState β ω) numberOp = numberOp := by
  have hcomm : electronModeThermalState β ω * numberOp
      = numberOp * electronModeThermalState β ω := by
    unfold electronModeThermalState numberOp
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; ring
  unfold QIQTH.FiniteModularTheory.modAut
  rw [hcomm, mul_assoc, mul_invOf_self, mul_one]

/-! ### The genuine real one-parameter modular flow `σ_t = Δ^{it} · Δ^{−it}` for the electron -/

/-- The electron mode's occupation eigenvalues `(1 − n, n)` (a positive diagonal density),
`n = fermiDirac β ω` — the data of the real one-parameter modular flow `sigmaDiag`. -/
noncomputable def electronModeOcc (β ω : ℝ) : Fin 2 → ℝ :=
  ![1 - fermiDirac β ω, fermiDirac β ω]

/-- Both occupations are nonzero (`0 < n < 1`), so `Δ^{it}` is well-defined and the group law applies. -/
theorem electronModeOcc_ne_zero (β ω : ℝ) (i : Fin 2) : (electronModeOcc β ω i : ℂ) ≠ 0 := by
  fin_cases i
  · have h : (0 : ℝ) < 1 - fermiDirac β ω := by linarith [fermiDirac_lt_one β ω]
    simpa [electronModeOcc] using Complex.ofReal_ne_zero.mpr h.ne'
  · simpa [electronModeOcc] using Complex.ofReal_ne_zero.mpr (fermiDirac_pos β ω).ne'

/-- **The electron's genuine real-time modular flow `σ_t = Δ^{it}·Δ^{−it}` is an ℝ-action:**
`σ_s(σ_t x) = σ_{s+t} x`.  This is the real-time Tomita–Takesaki modular flow of the electron mode
(`FiniteModularTheory.sigmaDiag` at the Fermi–Dirac occupations) — the one-parameter-group property that
a single (imaginary-time) conjugation cannot state. -/
theorem electron_sigmaDiag_comp (β ω : ℝ) (s t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℂ) :
    QIQTH.FiniteModularTheory.sigmaDiag (electronModeOcc β ω) s
        (QIQTH.FiniteModularTheory.sigmaDiag (electronModeOcc β ω) t x)
      = QIQTH.FiniteModularTheory.sigmaDiag (electronModeOcc β ω) (s + t) x :=
  QIQTH.FiniteModularTheory.sigmaDiag_comp (electronModeOcc β ω) (electronModeOcc_ne_zero β ω) s t x

/-- **The modular flow fixes the number operator (record) at all modular times:** `σ_t(N) = N`.  The
genuine real-time `Δ^{it}` flow leaves the record/charge invariant (its phases rotate the off-diagonals;
the diagonal record is fixed) — record conservation under the modular FLOW, not just the KMS
conjugation. -/
theorem electron_sigmaDiag_fixes_numberOp (β ω : ℝ) (t : ℝ) :
    QIQTH.FiniteModularTheory.sigmaDiag (electronModeOcc β ω) t numberOp = numberOp := by
  have hcomm : QIQTH.FiniteModularTheory.diagPow (electronModeOcc β ω) t * numberOp
      = numberOp * QIQTH.FiniteModularTheory.diagPow (electronModeOcc β ω) t := by
    unfold QIQTH.FiniteModularTheory.diagPow numberOp
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; ring
  unfold QIQTH.FiniteModularTheory.sigmaDiag
  rw [hcomm, mul_assoc,
      QIQTH.FiniteModularTheory.diagPow_mul (electronModeOcc β ω) (electronModeOcc_ne_zero β ω) t (-t),
      show t + -t = 0 from by ring, QIQTH.FiniteModularTheory.diagPow_zero, mul_one]

/-- **The modular phase = `e^{−it·βω}`: the modular Hamiltonian eigenvalue is the mode energy `βω`.**
The ratio of `Δ^{it}`'s occupied/empty eigenvalues is the Gibbs factor raised to `it`,
`(n/(1−n))^{it} = e^{−it·βω}`.  So the modular flow rotates the off-diagonal (raising/lowering) operators
by the modular frequency `βω` — i.e. the generator of `σ_t` (the modular Hamiltonian `K`) has eigenvalue
gap `βω`, and at the Unruh value `β = 2π` this is `2π·ω` = `2π × (boost generator eigenvalue)`.  This is
the `Δ^{it} = U(boost)` content at the single-mode level (toward E9's `2π K_boost`). -/
theorem electron_modular_phase (β ω t : ℝ) :
    ((fermiDirac β ω / (1 - fermiDirac β ω) : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))
      = Complex.exp (-(Complex.I * (t : ℂ) * ((β * ω : ℝ) : ℂ))) := by
  rw [electron_gibbs_ratio,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_neg]
  congr 1
  ring

/-- The electron mode's **raising operator** `a†` (matrix unit `E_{1,0}`: empty ↦ occupied). -/
noncomputable def raisingOp : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 1 0 1

/-- **The raising operator `a†` is a modular eigenoperator**: `σ_t(a†) = (p₁^{it} p₀^{−it})·a†`.  The
real-time modular flow `Δ^{it}` rotates `a†` by the modular phase `(n/(1−n))^{it} = e^{−it·βω}`
(`electron_modular_phase`) — `a†` is an eigenvector of the modular automorphism with the modular
frequency `βω` (the boost energy at `β = 2π`).  This is the operator-level `Δ^{it} = U(boost)` action. -/
theorem electron_sigmaDiag_raising (β ω t : ℝ) :
    QIQTH.FiniteModularTheory.sigmaDiag (electronModeOcc β ω) t raisingOp
      = ((electronModeOcc β ω 1 : ℂ) ^ (Complex.I * (t : ℂ))
          * (electronModeOcc β ω 0 : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ))) • raisingOp := by
  unfold QIQTH.FiniteModularTheory.sigmaDiag QIQTH.FiniteModularTheory.diagPow raisingOp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.single,
      Matrix.smul_apply, smul_eq_mul] <;>
    ring

/-- The electron mode's **lowering operator** `a` (matrix unit `E_{0,1}`: occupied ↦ empty). -/
noncomputable def loweringOp : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 1 1

/-- **The lowering operator `a` is the dual modular eigenoperator**: `σ_t(a) = (p₀^{it} p₁^{−it})·a`.
The modular flow rotates `a` by the *inverse* modular phase `((1−n)/n)^{it} = e^{+it·βω}` — together with
`electron_sigmaDiag_raising` (`σ_t(a†) = e^{−it·βω}·a†`) this is the full modular spectral decomposition:
`a†` raises the modular energy by `βω`, `a` lowers it, and `N = a†a` is fixed
(`electron_sigmaDiag_fixes_numberOp`).  The single-mode `Δ^{it} = U(boost)` Bohr-frequency rotation. -/
theorem electron_sigmaDiag_lowering (β ω t : ℝ) :
    QIQTH.FiniteModularTheory.sigmaDiag (electronModeOcc β ω) t loweringOp
      = ((electronModeOcc β ω 0 : ℂ) ^ (Complex.I * (t : ℂ))
          * (electronModeOcc β ω 1 : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ))) • loweringOp := by
  unfold QIQTH.FiniteModularTheory.sigmaDiag QIQTH.FiniteModularTheory.diagPow loweringOp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.single,
      Matrix.smul_apply, smul_eq_mul] <;>
    ring

/-! ### The number operator is the modular generator: the canonical ladder commutators

The eigenoperator phases `e^{∓it·βω}` (`electron_sigmaDiag_raising`/`_lowering`) are `βω × (∓1)`, the
`∓1` being the number eigenvalue raised/lowered by `a†`/`a`.  This is because the modular Hamiltonian is
affine in the number operator, `K = βω·N + c·I`, so `[K, a†] = βω·a†` — the canonical commutator
`[N, a†] = a†` scaled by the modular energy `βω`.  These are the matrix facts behind that. -/

/-- **`[N, a†] = a†`** — the number operator raises `a†` by one quantum (`a†` is the raising operator).
Combined with `K = βω·N + c`, this gives `[K, a†] = βω·a†`, the source of the modular phase `e^{−it·βω}`
on `a†`. -/
theorem electron_number_raising_comm :
    numberOp * raisingOp - raisingOp * numberOp = raisingOp := by
  unfold numberOp raisingOp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.single]

/-- **`[N, a] = −a`** — the number operator lowers `a` by one quantum (`a` is the lowering operator).
With `K = βω·N + c`, `[K, a] = −βω·a`, the source of the modular phase `e^{+it·βω}` on `a`. -/
theorem electron_number_lowering_comm :
    numberOp * loweringOp - loweringOp * numberOp = -loweringOp := by
  unfold numberOp loweringOp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.single,
      Matrix.neg_apply]

/-! ### E9 — the modular Hamiltonian `K = βω·N` and the boost Hamiltonian `2πK_boost`

The modular automorphism is `σ_t = Δ^{it} = e^{−itK}` with the modular Hamiltonian `K` *affine in the
number operator*, `K = βω·N (+ c·I)` — the single-mode realization of the Bisognano–Wichmann result that
the Rindler modular Hamiltonian is `2π` times the boost generator.  The constant `c·I` is central
(commutes with everything), so it drops out of all commutators; the load-bearing object is `K = βω·N`,
whose ladder commutators `[K, a†] = βω·a†`, `[K, a] = −βω·a` reproduce the eigenoperator modular
frequencies `∓βω` (`electron_sigmaDiag_raising`/`_lowering`).  At `β = 2π` the modular energy is `2πω =
2π × (mode energy ω)` — the boost modular Hamiltonian `K_W = 2πK_boost` whose `⟨K_W⟩` feeds the
Clausius/Jacobson area relation (E9). -/

/-- The **modular Hamiltonian** `K = βω·N` of the electron mode (the number-affine generator of `Δ^{it}`,
dropping the central constant `c·I` which is immaterial to the dynamics). -/
noncomputable def modHamiltonian (β ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((β * ω : ℝ) : ℂ) • numberOp

/-- **`[K, a†] = βω·a†`** — the modular Hamiltonian raises `a†` by the modular energy `βω`.  Scaling the
canonical `[N, a†] = a†` (`electron_number_raising_comm`) by `βω`: `a†` is a modular eigenoperator with
eigenvalue `βω`, the generator-level source of the phase `σ_t(a†) = e^{−it·βω}·a†`. -/
theorem electron_modHamiltonian_raising_comm (β ω : ℝ) :
    modHamiltonian β ω * raisingOp - raisingOp * modHamiltonian β ω
      = ((β * ω : ℝ) : ℂ) • raisingOp := by
  unfold modHamiltonian
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, electron_number_raising_comm]

/-- **`[K, a] = −βω·a`** — the modular Hamiltonian lowers `a` by the modular energy `βω` (the dual of
`electron_modHamiltonian_raising_comm`), the source of `σ_t(a) = e^{+it·βω}·a`. -/
theorem electron_modHamiltonian_lowering_comm (β ω : ℝ) :
    modHamiltonian β ω * loweringOp - loweringOp * modHamiltonian β ω
      = -(((β * ω : ℝ) : ℂ) • loweringOp) := by
  unfold modHamiltonian
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, electron_number_lowering_comm, smul_neg]

/-- **The boost modular Hamiltonian `K_W = 2πK_boost` (Bisognano–Wichmann).**  At the BW inverse
temperature `β = 2π`, `[K_W, a†] = 2πω·a†` — the modular energy is `2πω = 2π × (mode energy ω)`, i.e. the
Rindler modular Hamiltonian is `2π` times the boost generator `K_boost = ω·N`.  This `2πK_boost` is the
modular-energy object whose expectation `⟨K_W⟩` enters the Clausius/Jacobson area relation `δS = δ⟨K_W⟩`
(E9, the `+2π` that wires one-particle BW into the area law). -/
theorem electron_boost_modHamiltonian_raising_comm (ω : ℝ) :
    modHamiltonian (2 * Real.pi) ω * raisingOp - raisingOp * modHamiltonian (2 * Real.pi) ω
      = ((2 * Real.pi * ω : ℝ) : ℂ) • raisingOp :=
  electron_modHamiltonian_raising_comm (2 * Real.pi) ω

/-- **The modular-energy expectation `⟨K⟩ = βω·n`.**  The KMS/modular-state expectation of the modular
Hamiltonian `K = βω·N` is `βω` times the Fermi–Dirac occupation `n = fermiDirac β ω`
(`electron_occupation_eq_fermiDirac` scaled by the linearity of `stateOf`).  This `⟨K⟩ = βω·n = β⟨E⟩` is
exactly the modular-energy term in the thermal entropy `S = log Z + β⟨E⟩` (`electron_mode_entropy`) and the
quantity whose variation is `δ⟨K⟩` in the entanglement first law `δS = δ⟨K⟩` (`electron_firstLaw`). -/
theorem electron_modHamiltonian_expectation (β ω : ℝ) :
    QIQTH.FiniteModularTheory.stateOf (electronModeThermalState β ω) (modHamiltonian β ω)
      = ((β * ω : ℝ) : ℂ) * (fermiDirac β ω : ℂ) := by
  have h := electron_occupation_eq_fermiDirac β ω
  simp only [QIQTH.FiniteModularTheory.stateOf, modHamiltonian] at h ⊢
  rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul, h]

/-- **The boost-energy expectation `⟨K_W⟩ = 2πω·n_ω` (Bisognano–Wichmann, `β = 2π`).**  The expectation of
the boost modular Hamiltonian `K_W = 2πK_boost` in the Rindler/Unruh KMS state is `2πω` times the
Rindler–Fermi occupation — the modular energy `⟨K_W⟩` that enters the Clausius/Jacobson area relation
`δS = δ⟨K_W⟩` (the electron's contribution to the `+2π`-normalized boost energy feeding the area law). -/
theorem electron_boost_modEnergy (ω : ℝ) :
    QIQTH.FiniteModularTheory.stateOf (electronModeThermalState (2 * Real.pi) ω)
        (modHamiltonian (2 * Real.pi) ω)
      = ((2 * Real.pi * ω : ℝ) : ℂ) * (rindlerOccupationFermi ω : ℂ) :=
  electron_modHamiltonian_expectation (2 * Real.pi) ω

/-- **The modular Hamiltonian `K = βω·N` is self-adjoint (Hermitian).**  A real multiple (`βω` is real,
self-adjoint in `ℂ`) of the real-diagonal number operator is Hermitian — so `K` is a genuine self-adjoint
generator and `Δ^{it} = e^{−itK}` is a *unitary* one-parameter group (the Stone/Tomita–Takesaki form of
the modular flow).  Completes the E9 single-mode generator: `K` is self-adjoint, its ladder commutators
give the modular frequencies `∓βω`, and `⟨K⟩ = βω·n`. -/
theorem electron_modHamiltonian_isHermitian (β ω : ℝ) :
    Matrix.IsHermitian (modHamiltonian β ω) := by
  have hN : Matrix.IsHermitian numberOp := by
    have hsa : IsSelfAdjoint (![0, 1] : Fin 2 → ℂ) := by
      rw [isSelfAdjoint_iff]; ext i; fin_cases i <;> simp
    unfold numberOp
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ hsa
  have hk : IsSelfAdjoint ((β * ω : ℝ) : ℂ) := by
    rw [isSelfAdjoint_iff]; exact Complex.conj_ofReal _
  unfold modHamiltonian
  exact Matrix.IsHermitian.smul hN hk

/-- **The modular-energy spectrum `K = diag(0, βω)`.**  The modular Hamiltonian is the diagonal matrix
with eigenvalues `0` (the empty mode) and `βω` (the occupied mode): the modular energy levels are exactly
`{0, βω}`, the empty state carrying zero modular energy and the occupied state carrying `βω` — the boost
energy quantum (`= 2πω` at the Bisognano–Wichmann temperature `β = 2π`), the gap that drives the modular
phase `σ_t(a†) = e^{−it·βω}·a†` (`electron_sigmaDiag_raising`). -/
theorem electron_modHamiltonian_diag (β ω : ℝ) :
    modHamiltonian β ω = Matrix.diagonal ![0, ((β * ω : ℝ) : ℂ)] := by
  unfold modHamiltonian numberOp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]

/-- **The total modular energy `Tr K = βω`.**  The trace of the modular Hamiltonian (the sum of the
modular energy levels `0 + βω`) is `βω` — at `β = 2π`, the boost energy `2πω`. -/
theorem electron_modHamiltonian_trace (β ω : ℝ) :
    Matrix.trace (modHamiltonian β ω) = ((β * ω : ℝ) : ℂ) := by
  rw [electron_modHamiltonian_diag, Matrix.trace_diagonal, Fin.sum_univ_two]
  simp

/-- **The single-mode thermal / entanglement entropy: `S = log Z + β⟨E⟩`.**  The von Neumann entropy of
the electron mode equals the log partition function plus `β` times the mean energy:
`binaryEntropy(n) = log(1 + e^{−βω}) + βω·n`, with `n = fermiDirac β ω`, `Z = 1 + e^{−βω}` and the mean
energy `⟨E⟩ = ω·n` (so `βω·n = β⟨E⟩`, and `βω·n = ⟨K⟩` is the modular-energy expectation up to the
constant `log Z`).  This is the bridge `S ↔ ⟨K⟩` — the input to the entanglement first law `δS = δ⟨K⟩`
that drives the area law. -/
theorem electron_mode_entropy (β ω : ℝ) :
    binaryEntropy (fermiDirac β ω)
      = Real.log (1 + Real.exp (-(β * ω))) + (β * ω) * fermiDirac β ω := by
  have hn0 : (0 : ℝ) < fermiDirac β ω := fermiDirac_pos β ω
  have hn1 : fermiDirac β ω < 1 := fermiDirac_lt_one β ω
  have hlogn : Real.log (fermiDirac β ω) = - Real.log (Real.exp (β * ω) + 1) := by
    unfold fermiDirac; rw [one_div, Real.log_inv]
  have h1mn_eq : 1 - fermiDirac β ω = Real.exp (β * ω) * fermiDirac β ω := by
    have hb := fermiDirac_kms_balance β ω
    rw [Real.exp_neg] at hb
    have he : Real.exp (β * ω) ≠ 0 := (Real.exp_pos _).ne'
    field_simp at hb ⊢; linarith [hb]
  have hlog1mn : Real.log (1 - fermiDirac β ω) = β * ω - Real.log (Real.exp (β * ω) + 1) := by
    rw [h1mn_eq, Real.log_mul (Real.exp_pos _).ne' hn0.ne', Real.log_exp, hlogn]; ring
  have hlogZ : Real.log (1 + Real.exp (-(β * ω))) = Real.log (Real.exp (β * ω) + 1) - β * ω := by
    rw [Real.exp_neg,
        show (1 : ℝ) + (Real.exp (β * ω))⁻¹ = (Real.exp (β * ω) + 1) / Real.exp (β * ω) by field_simp,
        Real.log_div (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  simp only [binaryEntropy, Real.negMulLog_def, hlogn, hlog1mn, hlogZ]
  ring

/-- **The Pauli per-mode capacity ceiling `S ≤ log 2`.**  The electron mode's thermal entropy is at most
`log 2` — a fermionic mode is a *qubit* (occupied or empty, Pauli exclusion), so its entropy is bounded by
the log of its `2`-dimensional state space.  The sharp **contrast with the photon**: the bosonic mode
entropy `(1+n)log(1+n) − n log n` is *unbounded* (no cutoff, `PHOTON_FIELD_PLAN` P2/P4), whereas the
electron's per-mode entropy has the hard ceiling `log 2` — the entropy-level shadow of the CAR finite
capacity `dim ⋀h = 2^n`.  (Gibbs/Jensen on the 2-outcome occupation distribution `{n, 1−n}`.) -/
theorem electron_mode_entropy_le_log2 (β ω : ℝ) :
    binaryEntropy (fermiDirac β ω) ≤ Real.log 2 := by
  set c := fermiDirac β ω with hc
  have hp0 : ∀ i : Fin 2, 0 ≤ ![c, 1 - c] i := by
    intro i; fin_cases i
    · show 0 ≤ c; rw [hc]; exact (fermiDirac_pos β ω).le
    · show 0 ≤ 1 - c; rw [hc]; linarith [fermiDirac_lt_one β ω]
  have h1 : ∑ i : Fin 2, ![c, 1 - c] i = 1 := by
    rw [Fin.sum_univ_two]; show c + (1 - c) = 1; ring
  have hkey := QIQTH.RecordContract.shannon_le_log_card (![c, 1 - c]) hp0 h1
  rw [QIQTH.RecordContract.shannon_eq_sum_negMulLog] at hkey
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Fintype.card_fin, Nat.cast_ofNat] at hkey
  rw [binaryEntropy]
  exact hkey

/-- **The entropy derivative is the modular energy (logit).**  `d/dn binaryEntropy(n) = log((1−n)/n)`
for `n ∈ (0,1)`.  At the KMS occupation `n = fermiDirac β ω` this equals `βω` (`fermiDirac_logit`) — the
differential entanglement first law `δS = (modular energy)·δn`. -/
theorem hasDerivAt_binaryEntropy {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt binaryEntropy (Real.log ((1 - x) / x)) x := by
  have hxne : x ≠ 0 := hx0.ne'
  have h1xne : (1 : ℝ) - x ≠ 0 := by linarith
  have hinner : HasDerivAt (fun n : ℝ => 1 - n) (-1) x := (hasDerivAt_id x).const_sub 1
  have h2 : HasDerivAt (fun n => Real.negMulLog (1 - n)) (Real.log (1 - x) + 1) x := by
    have h := (Real.hasDerivAt_negMulLog h1xne).comp x hinner
    convert h using 1; ring
  have key : HasDerivAt (fun n => Real.negMulLog n + Real.negMulLog (1 - n))
      (Real.log ((1 - x) / x)) x := by
    have h := (Real.hasDerivAt_negMulLog hxne).add h2
    convert h using 1
    rw [Real.log_div h1xne hxne]; ring
  exact key

/-- **The entanglement first law for the electron mode (`δS = δ⟨K⟩`).**  At the KMS/Unruh occupation the
entropy's derivative with respect to occupation IS the modular energy `βω`:
`HasDerivAt binaryEntropy (βω) (fermiDirac β ω)`.  Since `⟨K⟩ = βω·n + c`, `d⟨K⟩/dn = βω = dS/dn` — the
first law that drives the area law, realized for the electron mode. -/
theorem electron_firstLaw (β ω : ℝ) :
    HasDerivAt binaryEntropy (β * ω) (fermiDirac β ω) := by
  have h := hasDerivAt_binaryEntropy (fermiDirac_pos β ω) (fermiDirac_lt_one β ω)
  rwa [fermiDirac_logit] at h

/-! ### E6 capstone — the electron Unruh effect at the Bisognano–Wichmann temperature `β = 2π`

At `β = 2π` the finite modular flow `σ_t = Δ^{it}` (`electron_sigmaDiag_*`) is the geometric Rindler boost
(Bisognano–Wichmann), so the electron mode's KMS state is the thermal state seen by the uniformly
accelerated/Rindler observer.  The lemmas below specialize the modular tier to that temperature: the
Rindler–Fermi (Unruh) occupation, its Pauli bound (the contrast with the photon), the Unruh thermal
entropy, and the Unruh first law — tying the already-built modular flow to the boost-KMS Unruh law. -/

/-- **★ The electron Unruh occupation (Bisognano–Wichmann, `β = 2π`).**  At the boost-KMS inverse
temperature `β = 2π` — the modular temperature of the Rindler wedge, where the modular flow `σ_t = Δ^{it}`
IS the geometric boost `U(Λ_W(−2πt))` — the electron mode's number expectation in the KMS/modular state is
the **Rindler–Fermi occupation** `n_ω = 1/(e^{2πω} + 1)`: `ω(N) = rindlerOccupationFermi ω`.  The electron
Unruh effect as the modular-state expectation (E6), wiring the FD/Unruh occupation into the project's
boost-KMS modular flow at the BW temperature. -/
theorem electron_unruh_occupation (ω : ℝ) :
    QIQTH.FiniteModularTheory.stateOf (electronModeThermalState (2 * Real.pi) ω) numberOp
      = (rindlerOccupationFermi ω : ℂ) := by
  rw [electron_occupation_eq_fermiDirac]; rfl

/-- **The electron Unruh occupation obeys the Pauli bound** `0 < n_ω < 1` (`fermiDirac_mem_Ioo`): at most
one fermion per mode (Pauli exclusion).  The sharp **contrast with the photon**: the *bosonic* Unruh
occupation `1/(e^{2πω} − 1)` is unbounded — so the photon's regional capacity needs a number cutoff
(`PHOTON_FIELD_PLAN` P2/P3, `truncFockDim_*`) — whereas the fermionic `n_ω < 1` makes the electron's
per-mode capacity intrinsically finite (the CAR `dim ⋀h = 2^(dim h)`, no cutoff). -/
theorem electron_unruh_occupation_mem_Ioo (ω : ℝ) :
    rindlerOccupationFermi ω ∈ Set.Ioo (0 : ℝ) 1 :=
  fermiDirac_mem_Ioo (2 * Real.pi) ω

/-- **The electron Unruh thermal entropy** at `β = 2π`: `S(n_ω) = log(1 + e^{−2πω}) + 2πω·n_ω`
(`electron_mode_entropy` at `β = 2π`), the `log Z + β⟨E⟩` form with `n_ω` the Rindler–Fermi occupation —
the thermal entropy of the electron mode as seen by the Rindler/Unruh observer, whose first law
`δS = δ⟨K⟩` feeds the area law. -/
theorem electron_unruh_entropy (ω : ℝ) :
    binaryEntropy (rindlerOccupationFermi ω)
      = Real.log (1 + Real.exp (-(2 * Real.pi * ω)))
        + (2 * Real.pi * ω) * rindlerOccupationFermi ω :=
  electron_mode_entropy (2 * Real.pi) ω

/-- **The electron Unruh first law** `δS = δ⟨K⟩` at `β = 2π`: `HasDerivAt binaryEntropy (2πω) (n_ω)`
(`electron_firstLaw` at `β = 2π`) — the entanglement first law at the Bisognano–Wichmann/Unruh
temperature, with modular energy `2πω = 2π × (boost energy)` (the `+2π` wiring one-particle BW into the
area law). -/
theorem electron_unruh_firstLaw (ω : ℝ) :
    HasDerivAt binaryEntropy (2 * Real.pi * ω) (rindlerOccupationFermi ω) :=
  electron_firstLaw (2 * Real.pi) ω

end QIQTH.Fock.Dirac
