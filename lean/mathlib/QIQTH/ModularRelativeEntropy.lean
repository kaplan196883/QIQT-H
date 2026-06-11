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

open MeasureTheory QIQTH.StandardSubspaceModular QIQTH.SpectralTheorem QIQTH.Spectral
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

/-- **Diagonal reduction of the polarized bounded-Borel form:** `B_f(x,x) = D_f(x) = ∫ f dμ_x`.
    The `x = y` case of the sesquilinear `bilinDiag`, via the degree-2 homogeneity of `diagInt`. -/
private theorem bilinDiag_self {Ω : Type*} [MeasurableSpace Ω]
    (P : ProjectionValuedMeasure Ω H) (f : Ω → ℂ) (x : H) :
    P.bilinDiag f x x = P.diagInt f x := by
  have e2 : x + x = (2 : ℂ) • x := (two_smul ℂ x).symm
  have e0 : x - x = (0 : ℂ) • x := by rw [sub_self, zero_smul]
  have ep : Complex.I • x + x = (Complex.I + 1) • x := by rw [add_smul, one_smul]
  have em : Complex.I • x - x = (Complex.I - 1) • x := by rw [sub_smul, one_smul]
  have c2 : ((‖(2 : ℂ)‖ ^ 2 : ℝ) : ℂ) = 4 := by norm_num
  have c0 : ((‖(0 : ℂ)‖ ^ 2 : ℝ) : ℂ) = 0 := by norm_num
  have cp : ((‖(Complex.I + 1)‖ ^ 2 : ℝ) : ℂ) = 2 := by
    have : (‖(Complex.I + 1)‖ ^ 2 : ℝ) = 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
        Complex.one_re, Complex.one_im]
    rw [this]; norm_num
  have cm : ((‖(Complex.I - 1)‖ ^ 2 : ℝ) : ℂ) = 2 := by
    have : (‖(Complex.I - 1)‖ ^ 2 : ℝ) = 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      norm_num [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
        Complex.one_re, Complex.one_im]
    rw [this]; norm_num
  rw [ProjectionValuedMeasure.bilinDiag, e2, e0, ep, em,
      P.diagInt_smul, P.diagInt_smul, P.diagInt_smul, P.diagInt_smul, c2, c0, cp, cm]
  ring

/-- **Operator-expectation bridge:** for any *bounded* measurable real modular observable `f` on the
    spectrum of `R`, its scalar spectral average equals the quantum expectation `re⟪ξ, f(R) ξ⟫`, where
    `f(R)` is the bounded Borel functional calculus.  In particular a bounded (regularized) modular
    Hamiltonian density gives `−∫ f dμ^R_ξ = re⟪ξ, (−f(R)) ξ⟫` — the entropy as a genuine expectation
    value of a bounded self-adjoint operator. -/
theorem rvdSpec_integral_eq_re_inner (S : StandardSubspace H) (ξ : H)
    {f : spectrum ℝ (rvdRC S) → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖(f ω : ℂ)‖ ≤ C) :
    ∫ ω, f ω ∂(rvdSpecMeasure S ξ)
      = Complex.re (inner ℂ ξ (borelFC (rvdRC S) (rvdRC_isSelfAdjoint S)
          (Complex.measurable_ofReal.comp hf) hC0 hC ξ)) := by
  rw [inner_borelFC, bilinDiag_self, ProjectionValuedMeasure.diagInt, rvdSpecMeasure]
  simp only [Function.comp_apply]
  rw [integral_complex_ofReal, Complex.ofReal_re]

/-- The vacuum coherent state (`ξ = 0`) has zero relative entropy with itself. -/
@[simp] theorem cgpEntropy_zero (S : StandardSubspace H) : cgpEntropy S (0 : H) = 0 := by
  simp [cgpEntropy]

/-- **Degree-2 homogeneity** `S(c·ξ) = ‖c‖²·S(ξ)` — the one-particle scaling of the spectral measure
    `μ^R_{c·ξ} = ‖c‖²·μ^R_ξ`, the hallmark of the coherent/one-particle structure. -/
theorem cgpEntropy_smul (S : StandardSubspace H) (c : ℂ) (ξ : H) :
    cgpEntropy S (c • ξ) = ‖c‖ ^ 2 * cgpEntropy S ξ := by
  rw [cgpEntropy, cgpEntropy, rvdSpecMeasure, rvdSpecMeasure,
      (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).scalarMeasure_smul c ξ,
      integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_neg]

end QIQTH
