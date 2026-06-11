/-
  Modular relative entropy at the one-particle / standard-subspace level — Phase B (foundation).

  This is the genuine NON-finite-dimensional companion of the finite Umegaki entropy: the
  Casini–Grillo–Pontello one-particle relative entropy of a coherent state (with one-particle
  wavefunction `ξ ∈ H`) relative to the vacuum, over a standard subspace `S ⊆ H`.

  Per the GPT-5.5 consultation: DON'T build the unbounded `log Δ`.  Use the bounded RvD operator
  `R = P + Q` (`rvdRC`), whose spectrum lies in `[0,2]`, and define the entropy as the SCALAR
  spectral integral
        S(ξ) = −∫ log((2−r)/r) dμ^R_ξ(r),       μ^R_ξ = scalar spectral measure of `R` at `ξ`.
  No unbounded operators ever appear.  The integrand `log((2−r)/r)` is exactly the spectral function
  of the modular Hamiltonian `−log Δ` for the bounded modular operator `Δ = (2−R)R⁻¹`, and it is the
  GENERATOR of the continuum modular flow `Δ^{it} = U_t = u_t(R)` already built in
  `StandardSubspaceModularFlow` (`modUnitary`, `modChar t r = exp(i·t·log((2−r)/r))`).

  HONEST SCOPE: this is a genuine continuum (one-particle) object — but the full von-Neumann-algebra
  relative-entropy claim requires CCR/CAR second quantization `Γ(Δ^{it})`, which is cited, not proved.
  As a one-particle theorem it stands on the bounded modular data constructed here.
-/

import QIQTH.StandardSubspaceModularFlow

namespace QIQTH

open MeasureTheory QIQTH.StandardSubspaceModular QIQTH.SpectralTheorem
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The modular Hamiltonian's spectral function** `g(r) = log((2−r)/r)`.  On the spectrum of
    `R = P + Q` (which lies in `[0,2]`), this is the eigenvalue of `log Δ` for the bounded modular
    operator `Δ = (2−R)R⁻¹`; equivalently it is the generator of the modular flow `Δ^{it}`. -/
noncomputable def entropyDensity (r : ℝ) : ℝ := Real.log ((2 - r) / r)

/-- **The entropy density is the generator of the modular flow:** for `r ∈ (0,2)` (the interior of
    the spectrum of `R`), `u_t(r) = exp(i·t·g(r))`.  This identifies `entropyDensity` as the modular
    Hamiltonian whose flow is `modUnitary`. -/
theorem modChar_eq_exp_entropyDensity (t : ℝ) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 2) :
    modChar t r = Complex.exp (Complex.I * (t : ℂ) * (entropyDensity r : ℂ)) := by
  rw [modChar, Set.piecewise_eq_of_mem _ _ _ hr, entropyDensity]

/-- **The scalar spectral measure of `R = P + Q` at the one-particle vector `ξ`** — a finite measure
    on `spectrum ℝ R`, with total mass `‖ξ‖²`. -/
noncomputable def rvdSpecMeasure (S : StandardSubspace H) (ξ : H) :
    Measure (spectrum ℝ (rvdRC S)) :=
  (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).scalarMeasure ξ

/-- Total mass of the spectral measure is `‖ξ‖²` (so for a unit one-particle vector it is a
    probability measure on the modular spectrum). -/
theorem rvdSpecMeasure_univ (S : StandardSubspace H) (ξ : H) :
    rvdSpecMeasure S ξ Set.univ = ENNReal.ofReal (‖ξ‖ ^ 2) :=
  (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).scalarMeasure_univ ξ

/-- The spectral measure of the zero vector is the zero measure. -/
@[simp] theorem rvdSpecMeasure_zero (S : StandardSubspace H) :
    rvdSpecMeasure S (0 : H) = 0 := by
  have h := (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).scalarMeasure_smul (0 : ℂ) (0 : H)
  simpa [rvdSpecMeasure] using h

/-- **The (one-particle) modular relative entropy** of the coherent state with one-particle
    wavefunction `ξ` relative to the vacuum:
        `S(ξ) = −⟪ξ, (log Δ) ξ⟫ = −∫ log((2−r)/r) dμ^R_ξ(r)`,
    realized purely through the bounded spectral measure of `R` (no unbounded operators).

    (The Bochner integral is `0` on the non-integrable locus; the physically meaningful vectors are
    those of finite entropy, for which `g` is `μ^R_ξ`-integrable.) -/
noncomputable def cgpEntropy (S : StandardSubspace H) (ξ : H) : ℝ :=
  -∫ ω, entropyDensity ω.val ∂(rvdSpecMeasure S ξ)

/-- The vacuum coherent state (`ξ = 0`) has zero relative entropy with itself. -/
@[simp] theorem cgpEntropy_zero (S : StandardSubspace H) : cgpEntropy S (0 : H) = 0 := by
  simp [cgpEntropy]

end QIQTH
