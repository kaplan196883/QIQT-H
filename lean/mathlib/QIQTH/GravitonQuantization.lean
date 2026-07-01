/-
  Quantizing the free graviton — the two-helicity bosonic CCR algebra (canonical quantization).

  The free linearized graviton has TWO physical polarizations, the helicity ±2 states `e_±` built kinematically in
  `EmergentDynamics.lean` (G11a: `eR_helicity`/`eL_helicity`). Canonical quantization promotes each helicity mode to
  a bosonic harmonic oscillator: a creation operator `a†_λ`, an annihilation operator `a_λ`, satisfying the canonical
  commutation relations (CCR)
      [a_λ, a†_μ] = δ_λμ,   [a_λ, a_μ] = 0,   [a†_λ, a†_μ] = 0.
  We realize this CONCRETELY (no √n analysis) in the **Bargmann–Fock holomorphic representation** on the polynomial
  ring `Fock = ℂ[X₀, X₁] = MvPolynomial (Fin 2) ℂ`, one variable per helicity: the creation operator is
  multiplication `a†_i = (X_i · )` and the annihilation operator is the partial derivative `a_i = ∂/∂X_i`. Then the
  CCR is exactly the derivation identity `[∂_i, X_j·] = δ_ij`. The vacuum is the constant `|0⟩ = 1` (annihilated by
  every `a_i`), the one-graviton states are `|1_i⟩ = a†_i|0⟩ = X_i`, and the number operator `N_i = a†_i a_i` counts
  occupation. Helicity labelling: mode `0 ↔ e_+` (helicity +2), mode `1 ↔ e_-` (helicity −2).

  ⚠ SCOPE. This is the canonical quantization of the free graviton at a SINGLE momentum mode (the two-helicity
  oscillator algebra) — the exact operator content of the quantized free graviton's polarization d.o.f. It is a
  genuine Fock representation of the CCR. What is NOT here (labelled honestly): the full momentum-space field
  `h_{μν}(x) = ∑_λ ∫d³k (a_λ(k) e^λ e^{ikx} + h.c.)` (the continuum of modes), the two-point function/propagator as a
  vacuum expectation, and interactions. The free graviton is a free field, so those are additive extensions of this
  same CCR core, one momentum mode at a time. Std-3, axiom-free.
-/
import Mathlib

namespace QIQTH.GravitonQuant

open MvPolynomial

noncomputable section

/-- The single-momentum-mode graviton **Fock space** in the Bargmann–Fock holomorphic representation:
    `ℂ[X₀, X₁]`, one polynomial variable per helicity (`X₀ ↔ e₊` helicity +2, `X₁ ↔ e₋` helicity −2). -/
abbrev Fock := MvPolynomial (Fin 2) ℂ

/-- The **creation operator** `a†_i` for helicity mode `i` — multiplication by `X_i` (raises occupation). -/
def creat (i : Fin 2) : Fock →ₗ[ℂ] Fock := LinearMap.mulLeft ℂ (X i : Fock)

/-- The **annihilation operator** `a_i` for helicity mode `i` — the partial derivative `∂/∂X_i` (lowers occupation). -/
def annih (i : Fin 2) : Fock →ₗ[ℂ] Fock := (pderiv i).toLinearMap

/-- **The canonical commutation relation** `[a_i, a†_j] = δ_ij` — the defining relation of the quantized graviton's
    two-helicity bosonic algebra. Realized as the Bargmann derivation identity `[∂_i, X_j·] = δ_ij`. -/
theorem ccr (i j : Fin 2) (p : Fock) :
    annih i (creat j p) - creat j (annih i p) = (if i = j then (1 : Fock) else 0) * p := by
  change pderiv i ((X j : Fock) * p) - (X j : Fock) * pderiv i p
    = (if i = j then (1 : Fock) else 0) * p
  rw [MvPolynomial.pderiv_mul]
  by_cases h : i = j
  · subst j; simp [MvPolynomial.pderiv_X]
  · have hji : j ≠ i := fun h' => h h'.symm
    simp [MvPolynomial.pderiv_X, h, hji]

/-- **Annihilators commute** `[a_i, a_j] = 0` (mixed partials commute — Clairaut for polynomials). -/
theorem annih_comm (i j : Fin 2) (p : Fock) : annih i (annih j p) = annih j (annih i p) := by
  change pderiv i (pderiv j p) = pderiv j (pderiv i p)
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    have hz : ∀ a b : Fin 2, (pderiv a) ((pderiv b) (X k : Fock)) = 0 := by
      intro a b
      rw [MvPolynomial.pderiv_X]
      rcases eq_or_ne k b with hk | hk
      · subst hk; simp
      · rw [Pi.single_eq_of_ne hk]; simp
    simp only [MvPolynomial.pderiv_mul, map_add, hz, mul_zero, add_zero]
    rw [hp]; ring

/-- **Creators commute** `[a†_i, a†_j] = 0` (multiplication is commutative). -/
theorem creat_comm (i j : Fin 2) (p : Fock) : creat i (creat j p) = creat j (creat i p) := by
  change (X i : Fock) * ((X j : Fock) * p) = (X j : Fock) * ((X i : Fock) * p)
  ring

/-- **The vacuum** `|0⟩ = 1` is annihilated by every annihilation operator: `a_i|0⟩ = 0`. -/
theorem annih_vacuum (i : Fin 2) : annih i (1 : Fock) = 0 := by
  change pderiv i (1 : Fock) = 0
  simpa using MvPolynomial.pderiv_C i (1 : ℂ)

/-- **The one-graviton states** `|1_i⟩ = a†_i|0⟩ = X_i` — a single graviton of helicity mode `i`. -/
theorem one_particle_state (i : Fin 2) : creat i (1 : Fock) = X i := by
  change (X i : Fock) * 1 = X i; rw [mul_one]

/-- **The number operator on one-graviton states** `N_i |1_j⟩ = δ_ij |1_i⟩` (`N_i = a†_i a_i` counts occupation of
    helicity mode `i`): a one-graviton state of helicity `j` is an eigenstate with occupation `δ_ij`. -/
theorem number_one_particle (i j : Fin 2) :
    creat i (annih i (creat j (1 : Fock))) = (if i = j then (X i : Fock) else 0) := by
  by_cases h : i = j
  · subst j; simp [creat, annih, MvPolynomial.pderiv_X]
  · have hji : j ≠ i := fun h' => h h'.symm
    simp [creat, annih, MvPolynomial.pderiv_X, h, hji]

/-! ### Q2 — the number operator and its occupation eigenstates -/

/-- The **number operator** `N_i = a†_i a_i` for helicity mode `i` — counts the occupation of that mode. -/
def numberOp (i : Fin 2) : Fock →ₗ[ℂ] Fock := creat i ∘ₗ annih i

/-- The number operator acts as `N_i p = X_i · ∂_i p`. -/
theorem numberOp_apply (i : Fin 2) (p : Fock) : numberOp i p = (X i : Fock) * pderiv i p := rfl

/-- **The occupation eigenstates** `X_i^n = |n_i⟩` diagonalize the number operator with eigenvalue `n`:
    `N_i |n_i⟩ = n |n_i⟩`. The spectrum of `N_i` is `ℕ` — bosonic occupation. -/
theorem numberOp_pow (i : Fin 2) (n : ℕ) :
    numberOp i (X i ^ n) = (n : Fock) * (X i ^ n) := by
  rw [numberOp_apply, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self, mul_one]
  cases n with
  | zero => simp
  | succ m => rw [Nat.succ_sub_one]; ring

/-- **The vacuum has zero occupation** `N_i|0⟩ = 0`. -/
theorem numberOp_vacuum (i : Fin 2) : numberOp i (1 : Fock) = 0 := by
  rw [numberOp_apply]; simp [annih_vacuum i]

/-- **One-graviton states are occupation-1 eigenstates** `N_i|1_j⟩ = δ_ij|1_i⟩`. -/
theorem numberOp_one_particle (i j : Fin 2) :
    numberOp i (X j) = (if i = j then (X i : Fock) else 0) := by
  by_cases h : i = j
  · subst j; simp [numberOp_apply, MvPolynomial.pderiv_X]
  · have hji : j ≠ i := fun h' => h h'.symm
    simp [numberOp_apply, MvPolynomial.pderiv_X, h, hji]

/-! ### Q3 — the Hamiltonian and the graviton zero-point energy -/

/-- The **total number operator** `N = N₀ + N₁` — the total graviton occupation of the mode. -/
def totalNumber : Fock →ₗ[ℂ] Fock := numberOp 0 + numberOp 1

/-- The **Hamiltonian** `H = ω(N₀ + N₁ + 1)` of the free graviton mode (`ω` the frequency; the `+1` is the two
    helicity oscillators' zero-point energy `½+½`). -/
def hamiltonian (ω : ℂ) : Fock →ₗ[ℂ] Fock := ω • (totalNumber + LinearMap.id)

/-- **The graviton zero-point energy** `H|0⟩ = ω|0⟩`: the vacuum is an eigenstate of `H` with energy `ω` (the
    irreducible zero-point energy of the two helicity oscillators). -/
theorem hamiltonian_vacuum (ω : ℂ) : hamiltonian ω (1 : Fock) = ω • (1 : Fock) := by
  simp [hamiltonian, totalNumber, numberOp_vacuum, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply]

/-- **A one-graviton state has energy `2ω`** `H|1_i⟩ = 2ω|1_i⟩` — one quantum of energy `ω` above the zero-point
    `ω`. Combined with `hamiltonian_vacuum`, the spectrum climbs by `ω` per graviton. -/
theorem hamiltonian_one_particle (ω : ℂ) (i : Fin 2) : hamiltonian ω (X i) = (2 * ω) • (X i) := by
  simp only [hamiltonian, totalNumber, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
  fin_cases i <;> simp [numberOp_one_particle] <;> module

/-! ### Q4 — helicity as the little-group charge (tying the occupation to the kinematic spin-2) -/

/-- The **helicity operator** `J = 2(N₀ − N₁)` — the rotation charge about the propagation axis. Mode `0` (`e₊`)
    carries helicity `+2`, mode `1` (`e₋`) carries helicity `−2` — the massless little-group labelling of the
    quantized graviton, matching the kinematic helicity-±2 eigenstates of `EmergentDynamics` (`eR_helicity`/
    `eL_helicity`). -/
def helicityOp : Fock →ₗ[ℂ] Fock := (2 : ℂ) • (numberOp 0 - numberOp 1)

/-- **A mode-0 graviton has helicity +2** `J|1₀⟩ = +2|1₀⟩` — the quantized realization of the spin-2 polarization
    `e₊` (helicity +2). -/
theorem helicityOp_plus : helicityOp (X 0) = (2 : ℂ) • (X 0) := by
  simp only [helicityOp, LinearMap.smul_apply, LinearMap.sub_apply]
  simp [numberOp_one_particle]

/-- **A mode-1 graviton has helicity −2** `J|1₁⟩ = −2|1₁⟩` — the quantized realization of `e₋` (helicity −2).
    Together with `helicityOp_plus`, the one-graviton states are exactly the helicity ±2 quanta. -/
theorem helicityOp_minus : helicityOp (X 1) = (-2 : ℂ) • (X 1) := by
  simp only [helicityOp, LinearMap.smul_apply, LinearMap.sub_apply]
  simp [numberOp_one_particle]

/-- **The vacuum carries zero helicity** `J|0⟩ = 0`. -/
theorem helicityOp_vacuum : helicityOp (1 : Fock) = 0 := by
  simp [helicityOp, numberOp_vacuum, LinearMap.smul_apply, LinearMap.sub_apply]

end

end QIQTH.GravitonQuant
