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

/-! ### The bounded-spectrum case: entropy as a modular-Hamiltonian expectation -/

/-- The entropy density `ω ↦ g(ω) = log((2−ω)/ω)` is measurable on the spectrum (everywhere, with the
    junk value of `Real.log` at the endpoints). -/
theorem entropyDensity_measurable {S : StandardSubspace H} :
    Measurable (fun ω : spectrum ℝ (rvdRC S) => entropyDensity ω.val) :=
  Real.measurable_log.comp
    ((measurable_const.sub measurable_subtype_coe).div measurable_subtype_coe)

/-- **Uniform bound on the entropy density away from the spectral endpoints:** for `r ∈ [a, 2−a]`
    (`0 < a`), `|log((2−r)/r)| ≤ log((2−a)/a)`.  This is what makes `g` bounded on a modular spectrum
    that stays away from `{0, 2}` (the "regular" / finite-entropy regime). -/
theorem entropyDensity_abs_le {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (hr2 : r ≤ 2 - a) :
    |entropyDensity r| ≤ Real.log ((2 - a) / a) := by
  have hr : 0 < r := lt_of_lt_of_le ha har
  have h2r : 0 < 2 - r := by linarith
  have h2a : 0 < 2 - a := by linarith
  rw [entropyDensity, abs_le]
  refine ⟨?_, ?_⟩
  · rw [← Real.log_inv, inv_div]
    exact (Real.log_le_log_iff (div_pos ha h2a) (div_pos h2r hr)).mpr
      ((div_le_div_iff₀ h2a hr).mpr (by nlinarith))
  · exact (Real.log_le_log_iff (div_pos h2r hr) (div_pos h2a ha)).mpr
      ((div_le_div_iff₀ hr ha).mpr (by nlinarith))

/-- **The bounded-spectrum case — the modular relative entropy IS an operator expectation:**
    when the modular spectrum `σ(R) ⊆ [a, 2−a]` stays away from the endpoints `{0,2}` (`0 < a ≤ 1`),
    the entropy density `g` is bounded on `σ(R)`, so the one-particle relative entropy equals
        `S(ξ) = −⟪ξ, g(R) ξ⟫`,
    the expectation value of the bounded self-adjoint modular Hamiltonian `g(R) = log((2−R)/R)`. -/
theorem cgpEntropy_eq_neg_re_inner (S : StandardSubspace H) (ξ : H) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : ℝ) ∧ (ω : ℝ) ≤ 2 - a) :
    cgpEntropy S ξ = -Complex.re (inner ℂ ξ
      (borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) (C := Real.log ((2 - a) / a))
        (Complex.measurable_ofReal.comp entropyDensity_measurable)
        (Real.log_nonneg ((one_le_div ha).mpr (by linarith)))
        (fun ω => by
          simp only [Function.comp_apply]
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact entropyDensity_abs_le ha (hspec ω).1 (hspec ω).2) ξ)) := by
  rw [cgpEntropy, rvdSpec_integral_eq_re_inner S ξ entropyDensity_measurable]

/-! ### Finite-entropy regime (endpoint integrability)

  The density `g` diverges at the spectral endpoints (`g → +∞` as `r → 0`, `g → −∞` as `r → 2`), so the
  coherent state has FINITE relative entropy exactly when `g` is integrable against the spectral measure
  `μ^R_ξ` — i.e. when `μ^R_ξ` does not concentrate too much mass at the modular endpoints `{0,2}`. -/

/-- **Finite relative entropy:** the modular Hamiltonian density `g` is integrable against the spectral
    measure `μ^R_ξ`, so the Bochner integral defining `cgpEntropy` is a genuine finite real number. -/
def HasFiniteEntropy (S : StandardSubspace H) (ξ : H) : Prop :=
  Integrable (fun ω : spectrum ℝ (rvdRC S) => entropyDensity ω.val) (rvdSpecMeasure S ξ)

/-- **The regular regime has finite entropy:** if the modular spectrum stays away from the endpoints
    (`σ(R) ⊆ [a, 2−a]`, `0 < a`), the density `g` is bounded there, hence integrable on the finite
    spectral measure — the relative entropy is a genuine finite quantity. -/
theorem hasFiniteEntropy_of_mem_Icc (S : StandardSubspace H) (ξ : H) {a : ℝ} (ha : 0 < a)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : ℝ) ∧ (ω : ℝ) ≤ 2 - a) :
    HasFiniteEntropy S ξ := by
  haveI : IsFiniteMeasure (rvdSpecMeasure S ξ) := by
    unfold rvdSpecMeasure; infer_instance
  refine (integrable_const (Real.log ((2 - a) / a))).mono'
    entropyDensity_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs]
  exact entropyDensity_abs_le ha (hspec ω).1 (hspec ω).2

/-- The vacuum (`ξ = 0`) has finite (zero) relative entropy. -/
@[simp] theorem hasFiniteEntropy_zero (S : StandardSubspace H) : HasFiniteEntropy S (0 : H) := by
  rw [HasFiniteEntropy, rvdSpecMeasure_zero]; exact integrable_zero_measure

/-- **Finite entropy is scale-invariant** in the one-particle wavefunction: `S(c·ξ)` is finite iff
    `S(ξ)` is (for `c ≠ 0`).  Finiteness is a property of the direction, not the amplitude. -/
theorem hasFiniteEntropy_smul (S : StandardSubspace H) {c : ℂ} (hc : c ≠ 0) (ξ : H) :
    HasFiniteEntropy S (c • ξ) ↔ HasFiniteEntropy S ξ := by
  rw [HasFiniteEntropy, HasFiniteEntropy, rvdSpecMeasure, rvdSpecMeasure,
      (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).scalarMeasure_smul c ξ]
  exact integrable_smul_measure
    (ENNReal.ofReal_pos.mpr (pow_pos (norm_pos_iff.mpr hc) 2)).ne' ENNReal.ofReal_ne_top

/-! ### Toward the Casini–Grillo–Pontello sum rule (scalar skeleton)

  For a one-particle vector localized in the standard subspace (`ξ ∈ 𝒦`, i.e. `P ξ = ξ`), CGP give the
  manifestly-nonnegative form of the relative entropy
        `S(ξ) = ∫_{(0,1)} ((2−r)/r − 1)·log((2−r)/r) dμ^R_ξ ≥ 0`.
  The scalar ingredients — the reflection symmetry of the density and the pointwise nonnegativity of the
  CGP integrand — are proved here.

  GATE (the genuine Tomita content, NOT yet in the stack): the measure-theoretic step is the **spectral
  balance** `∫ F dμ^R_ξ = ∫ ((2−r)/r)·F(2−r) dμ^R_ξ` for `ξ ∈ 𝒦`, which follows from `J R J = 2 − R`
  (modular reflection of `R`) and the Tomita fixedness `ξ = J Δ^{1/2} ξ`.  Only `J U_t = U_t J`, `J T = D`,
  `J² = 1` are currently available, so `J R J = 2 − R` and the fixedness are the next standard-subspace
  theorems to build.  Note (GPT-5.5 counterexample): all-vector positivity is FALSE — a point mass at
  `r < 1` gives `cgpEntropy = −log((2−r)/r) < 0`; localization `ξ ∈ 𝒦` is essential. -/

/-- **Reflection symmetry of the entropy density:** `g(2−r) = −g(r)`.  This oddness under the modular
    reflection `r ↦ 2−r` (the spectral shadow of `J Δ J = Δ⁻¹`) is the symmetry driving the CGP sum rule. -/
theorem entropyDensity_reflect (r : ℝ) : entropyDensity (2 - r) = -entropyDensity r := by
  unfold entropyDensity
  rw [show (2 : ℝ) - (2 - r) = r by ring, ← Real.log_inv, inv_div]

/-- **The CGP positive density** `φ(r) = 1_{(0,1)}(r)·((2−r)/r − 1)·log((2−r)/r)` — the manifestly
    nonnegative integrand of the sum rule (on `(0,1)`: `(2−r)/r > 1` and `g(r) > 0`). -/
noncomputable def cgpDensity (r : ℝ) : ℝ :=
  Set.indicator (Set.Ioo 0 1) (fun r => ((2 - r) / r - 1) * entropyDensity r) r

/-- The CGP density is pointwise nonnegative. -/
theorem cgpDensity_nonneg (r : ℝ) : 0 ≤ cgpDensity r := by
  unfold cgpDensity
  rw [Set.indicator_apply]
  split_ifs with h
  · obtain ⟨h0, h1⟩ := h
    have h2r : 0 < 2 - r := by linarith
    have hgt : 1 < (2 - r) / r := by rw [lt_div_iff₀ h0]; linarith
    have hg : 0 ≤ entropyDensity r := by unfold entropyDensity; exact Real.log_nonneg hgt.le
    exact mul_nonneg (by linarith) hg
  · exact le_refl 0

/-! ### The measure reflection `μ^R_{Jη} = (2−·)_* μ^R_η`

  The first measure-theoretic step of the CGP spectral balance: the spectral measure of `R` at `Jη` is
  the pushforward of `μ^R_η` under the modular reflection `r ↦ 2−r`.  This lifts the inner-product
  reflection `reInner_modConj_cfcΩ` (`⟪Jη, f(R) Jη⟫_ℝ = ⟪η, (twΩ f)(R) η⟫_ℝ`) to the measure via the
  cfcΩ↔borelFC bridge (`cfcΩ` is literally `borelFC` of the restricted function, by `cfcCont`'s definition)
  + the operator-expectation bridge `rvdSpec_integral_eq_re_inner`. -/

open QIQTH.StandardSubspaceModular in
/-- **The cfcΩ↔borelFC bridge (operator level):** `cfcΩ f = borelFC (f∘inclΩ)`, immediate from the
    definition `cfcCont = borelFC` and its bound-independence. -/
theorem cfcΩ_eq_borelFC (S : StandardSubspace H) (f : C(Set.Icc (-covM S) (2 + covM S), ℂ))
    (hf : Measurable (fun ω : spectrum ℝ (rvdRC S) => f (inclΩ S ω))) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f (inclΩ S ω)‖ ≤ C) :
    cfcΩ S f = borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) hf hC0 hC := by
  rw [cfcΩ]; exact cfcCont_eq S (f.comp (inclΩ S)) hf hC0 hC

open QIQTH.StandardSubspaceModular in
/-- ℂ-lift of a real continuous map on the spectral interval. -/
noncomputable def ofRealΩ (S : StandardSubspace H) (F : C(Set.Icc (-covM S) (2 + covM S), ℝ)) :
    C(Set.Icc (-covM S) (2 + covM S), ℂ) :=
  ⟨fun x => (F x : ℂ), Complex.continuous_ofReal.comp F.continuous⟩

open QIQTH.StandardSubspaceModular in
/-- **The cfcΩ↔measure bridge:** `re⟪ξ, f(R) ξ⟫ = ∫ (F∘inclΩ) dμ^R_ξ` for real continuous `F`. -/
theorem cfcΩ_reInner_eq_integral (S : StandardSubspace H)
    (F : C(Set.Icc (-covM S) (2 + covM S), ℝ)) (ξ : H) :
    Complex.re (inner ℂ ξ (cfcΩ S (ofRealΩ S F) ξ)) = ∫ ω, F (inclΩ S ω) ∂(rvdSpecMeasure S ξ) := by
  have hf : Measurable (fun ω : spectrum ℝ (rvdRC S) => F (inclΩ S ω)) :=
    (F.comp (inclΩ S)).continuous.measurable
  have hC : ∀ ω : spectrum ℝ (rvdRC S), ‖((F (inclΩ S ω) : ℝ) : ℂ)‖ ≤ ‖F.comp (inclΩ S)‖ := fun ω => by
    rw [Complex.norm_real]; exact (F.comp (inclΩ S)).norm_coe_le_norm ω
  rw [rvdSpec_integral_eq_re_inner S ξ hf (norm_nonneg _) hC]
  exact congrArg (fun T : H →L[ℂ] H => Complex.re (inner ℂ ξ (T ξ)))
    (cfcΩ_eq_borelFC S (ofRealΩ S F) (Complex.measurable_ofReal.comp hf) (norm_nonneg _) hC)

open QIQTH.StandardSubspaceModular in
/-- `twΩ` of a real-lifted function is the real-lift of its reflection: `twΩ(ofRealΩ F) = ofRealΩ(F∘τ)`. -/
theorem twΩ_ofRealΩ (S : StandardSubspace H) (F : C(Set.Icc (-covM S) (2 + covM S), ℝ)) :
    twΩ S (ofRealΩ S F) = ofRealΩ S (F.comp (tauΩ S)) := by
  ext x; simp only [twΩ, ofRealΩ, ContinuousMap.star_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, RCLike.star_def, Complex.conj_ofReal]

open QIQTH.StandardSubspaceModular in
/-- **★ The measure reflection** `∫ F∘inclΩ dμ^R_{Jη} = ∫ F∘(2−·)∘inclΩ dμ^R_η` for continuous `F` —
    the spectral measure of `R` at `Jη` is the modular reflection of `μ^R_η`.  The first measure-theoretic
    step of the CGP spectral balance. -/
theorem rvdSpec_reflect (S : StandardSubspace H)
    (F : C(Set.Icc (-covM S) (2 + covM S), ℝ)) (η : H) :
    ∫ ω, F (inclΩ S ω) ∂(rvdSpecMeasure S (modConj S η))
      = ∫ ω, F (tauΩ S (inclΩ S ω)) ∂(rvdSpecMeasure S η) := by
  rw [← cfcΩ_reInner_eq_integral S F, show (fun ω => F (tauΩ S (inclΩ S ω)))
        = (fun ω => (F.comp (tauΩ S)) (inclΩ S ω)) from rfl,
      ← cfcΩ_reInner_eq_integral S (F.comp (tauΩ S)), ← twΩ_ofRealΩ]
  exact reInner_modConj_cfcΩ S (ofRealΩ S F) η

/-! ### The `h(R)`-weighting of the spectral measure

  The second measure-theoretic ingredient of the CGP balance: the spectral measure at `h(R)ξ` is `h²·`
  the spectral measure at `ξ`.  Together with the measure reflection and the bounded Tomita fixedness
  `(2−R)ξ = J(Tξ)` (for `ξ∈𝒦`), this yields the polynomial balance `∫(2−r)²F dμ_ξ = ∫r(2−r)F(2−r) dμ_ξ`. -/

open QIQTH.StandardSubspaceModular in
/-- The ℂ-lift of a real continuous map is self-adjoint (real-valued). -/
theorem ofRealΩ_star (S : StandardSubspace H) (F : C(Set.Icc (-covM S) (2 + covM S), ℝ)) :
    star (ofRealΩ S F) = ofRealΩ S F := by
  ext x; simp only [ofRealΩ, ContinuousMap.star_apply, ContinuousMap.coe_mk, RCLike.star_def,
    Complex.conj_ofReal]

open QIQTH.StandardSubspaceModular in
/-- The ℂ-lift is multiplicative. -/
theorem ofRealΩ_mul (S : StandardSubspace H) (F G : C(Set.Icc (-covM S) (2 + covM S), ℝ)) :
    ofRealΩ S (F * G) = ofRealΩ S F * ofRealΩ S G := by
  ext x; simp only [ofRealΩ, ContinuousMap.mul_apply, ContinuousMap.coe_mk, Complex.ofReal_mul]

open QIQTH.StandardSubspaceModular in
/-- `f(R)` is self-adjoint for real continuous `f`. -/
theorem cfcΩ_ofRealΩ_adjoint (S : StandardSubspace H)
    (hΩ : C(Set.Icc (-covM S) (2 + covM S), ℝ)) :
    ContinuousLinearMap.adjoint (cfcΩ S (ofRealΩ S hΩ)) = cfcΩ S (ofRealΩ S hΩ) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← cfcΩ_star, ofRealΩ_star]

open QIQTH.StandardSubspaceModular in
/-- **★ The `h(R)`-weighting:** `∫ F dμ^R_{h(R)ξ} = ∫ h²·F dμ^R_ξ` for real continuous `h, F` —
    the spectral measure at `h(R)ξ` is `h²` times that at `ξ`.  By `h(R)` self-adjoint + the
    multiplicativity `h(R)·F(R)·h(R) = (h²F)(R)`. -/
theorem cfcΩ_weight (S : StandardSubspace H)
    (hΩ F : C(Set.Icc (-covM S) (2 + covM S), ℝ)) (ξ : H) :
    ∫ ω, F (inclΩ S ω) ∂(rvdSpecMeasure S (cfcΩ S (ofRealΩ S hΩ) ξ))
      = ∫ ω, ((hΩ * hΩ) * F) (inclΩ S ω) ∂(rvdSpecMeasure S ξ) := by
  rw [← cfcΩ_reInner_eq_integral S F, ← cfcΩ_reInner_eq_integral S ((hΩ * hΩ) * F)]
  congr 1
  rw [← ContinuousLinearMap.adjoint_inner_right (cfcΩ S (ofRealΩ S hΩ)) ξ
        (cfcΩ S (ofRealΩ S F) (cfcΩ S (ofRealΩ S hΩ) ξ)), cfcΩ_ofRealΩ_adjoint]
  congr 1
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← cfcΩ_mul, ← cfcΩ_mul,
      ← ofRealΩ_mul, ← ofRealΩ_mul]
  congr 2
  ring

/-! ### The CGP polynomial spectral balance `∫(2−r)²F(r) dμ_ξ = ∫r(2−r)F(2−r) dμ_ξ`  (`ξ ∈ 𝒦`)

  Assembling the two measure engines (the reflection `μ_{Jη}=(2−·)_*μ_η` and the `h(R)`-weighting
  `μ_{h(R)ξ}=h²μ_ξ`) with the bounded Tomita fixedness `(2−R)ξ = J(Tξ)` yields the spectral balance in
  cleared-denominator (polynomial) form.  `R` and `2−R` are realized as `cfcΩ`-images of real coordinate
  functions; `T = √(R(2−R))` is handled via `rvdT_sq` (`T² = R(2−R)`), which AVOIDS the `CFC.sqrt↔cfcΩ`
  identification entirely. -/

open QIQTH.StandardSubspaceModular

/-- The real coordinate function `r` on the spectral interval. -/
def coordReal (S : StandardSubspace H) : C(Set.Icc (-covM S) (2 + covM S), ℝ) :=
  ⟨fun x => x.1, continuous_subtype_val⟩

/-- The reflected real coordinate `2 − r` on the spectral interval. -/
def twoSubCoordReal (S : StandardSubspace H) : C(Set.Icc (-covM S) (2 + covM S), ℝ) :=
  ⟨fun x => 2 - x.1, continuous_const.sub continuous_subtype_val⟩

/-- The complex coordinate is the ℂ-lift of the real coordinate. -/
theorem coordΩ_eq (S : StandardSubspace H) : coordΩ S = ofRealΩ S (coordReal S) := by ext x; rfl

/-- `R = r(R)` as a `cfcΩ`-image of the (lifted) real coordinate. -/
theorem rvdRC_eq_cfcΩ (S : StandardSubspace H) : rvdRC S = cfcΩ S (ofRealΩ S (coordReal S)) := by
  rw [← coordΩ_eq, cfcΩ_coordΩ]

/-- `2−R = (2−r)(R)` as a `cfcΩ`-image of the (lifted) reflected coordinate. -/
theorem rvdTwoSubRC_eq_cfcΩ (S : StandardSubspace H) :
    rvdTwoSubRC S = cfcΩ S (ofRealΩ S (twoSubCoordReal S)) := by
  have h : ofRealΩ S (twoSubCoordReal S) = (2 : ℂ) • 1 - coordΩ S := by
    ext x; simp only [ofRealΩ, twoSubCoordReal, coordΩ, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, ContinuousMap.coe_mk, smul_eq_mul, mul_one,
      Complex.ofReal_sub, Complex.ofReal_ofNat]
  rw [h, cfcΩ_sub, cfcΩ_smul, cfcΩ_one, cfcΩ_coordΩ, rvdTwoSubRC]

/-- **Spectral measure at `(2−R)ξ`:** `μ^R_{(2−R)ξ} = (2−r)²·μ^R_ξ` — the `h(R)`-weighting at `h = 2−R`. -/
theorem rvdSpec_twoSubR (S : StandardSubspace H) (F : C(Set.Icc (-covM S) (2 + covM S), ℝ)) (ξ : H) :
    ∫ ω, F (inclΩ S ω) ∂(rvdSpecMeasure S (rvdTwoSubRC S ξ))
      = ∫ ω, ((twoSubCoordReal S * twoSubCoordReal S) * F) (inclΩ S ω) ∂(rvdSpecMeasure S ξ) := by
  rw [rvdTwoSubRC_eq_cfcΩ]; exact cfcΩ_weight S (twoSubCoordReal S) F ξ

/-- **Spectral measure at `Tξ`:** `μ^R_{Tξ} = r(2−r)·μ^R_ξ` — via `T` self-adjoint, `T` commuting with
    `F(R)`, and `T² = R(2−R)` (`rvdT_sq`), so no square-root functional calculus is needed. -/
theorem rvdSpec_T (S : StandardSubspace H) (F : C(Set.Icc (-covM S) (2 + covM S), ℝ)) (ξ : H) :
    ∫ ω, F (inclΩ S ω) ∂(rvdSpecMeasure S (rvdT S ξ))
      = ∫ ω, ((coordReal S * twoSubCoordReal S) * F) (inclΩ S ω) ∂(rvdSpecMeasure S ξ) := by
  have hop : rvdT S * cfcΩ S (ofRealΩ S F) * rvdT S
      = cfcΩ S (ofRealΩ S ((coordReal S * twoSubCoordReal S) * F)) := by
    rw [(cfcΩ_commute_rvdT S (ofRealΩ S F)).symm.eq, mul_assoc, rvdT_sq, rvdRC_eq_cfcΩ,
        rvdTwoSubRC_eq_cfcΩ, ← cfcΩ_mul, ← cfcΩ_mul, ← ofRealΩ_mul, ← ofRealΩ_mul]
    congr 2; ring
  rw [← cfcΩ_reInner_eq_integral S F,
      ← cfcΩ_reInner_eq_integral S ((coordReal S * twoSubCoordReal S) * F)]
  congr 1
  rw [← ContinuousLinearMap.adjoint_inner_right (rvdT S) ξ (cfcΩ S (ofRealΩ S F) (rvdT S ξ)),
      show ContinuousLinearMap.adjoint (rvdT S) = rvdT S by
        rw [← ContinuousLinearMap.star_eq_adjoint]; exact (rvdT_isSelfAdjoint S).star_eq]
  congr 1
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, hop]

/-- **★★ THE CGP POLYNOMIAL SPECTRAL BALANCE** for a localized one-particle state `ξ ∈ 𝒦`:
        `∫ (2−r)²·F(r) dμ^R_ξ = ∫ r(2−r)·F(2−r) dμ^R_ξ`.
    The bounded (cleared-denominator) form of the Tomita spectral balance `∫F dμ = ∫((2−r)/r)F(2−r) dμ`.
    Chain: `μ_{(2−R)ξ}=(2−r)²μ_ξ` (`rvdSpec_twoSubR`) → `(2−R)ξ = J(Tξ)` (`modConj_rvdT_of_mem_K`) →
    `μ_{Jη}=(2−·)_*μ_η` (`rvdSpec_reflect`) → `μ_{Tξ}=r(2−r)μ_ξ` (`rvdSpec_T`). -/
theorem rvdSpec_balance (S : StandardSubspace H) (F : C(Set.Icc (-covM S) (2 + covM S), ℝ))
    {ξ : H} (hξ : projK S ξ = ξ) :
    ∫ ω, ((twoSubCoordReal S * twoSubCoordReal S) * F) (inclΩ S ω) ∂(rvdSpecMeasure S ξ)
      = ∫ ω, ((coordReal S * twoSubCoordReal S) * (F.comp (tauΩ S))) (inclΩ S ω)
          ∂(rvdSpecMeasure S ξ) := by
  rw [← rvdSpec_twoSubR S F ξ, ← modConj_rvdT_of_mem_K S hξ, rvdSpec_reflect S F (rvdT S ξ)]
  exact rvdSpec_T S (F.comp (tauΩ S)) ξ

/-! ### ★★★ The CGP relative-entropy positivity `S(ξ) ≥ 0`

  The headline theorem.  For a localized one-particle state (`ξ ∈ 𝒦`) in the regular regime
  (`σ(R) ⊆ [a, 2−a]`, so the entropy is finite), the spectral balance forces

      `S(ξ) = ∫ ((1−r)/r)·log((2−r)/r) dμ^R_ξ`,

  whose integrand is `≥ 0` on ALL of `(0,2)` (for `r < 1` both factors are `> 0`; for `r > 1` both are
  `< 0`).  No `(0,1)`-split or indicator functions are needed.  Derivation: applying `rvdSpec_balance` to the
  clamped representative of `g/(2−r)²` yields the divided balance `∫ g dμ = −∫ ((2−r)/r) g dμ`, and averaging
  gives `S(ξ) = ∫ ((1−r)/r) g dμ ≥ 0`. -/

open QIQTH.StandardSubspaceModular in
/-- The clamped representative of `g(r)/(2−r)²` on the whole spectral interval: continuous everywhere,
    and equal to `g/(2−r)²` on the regular spectral window `[a, 2−a]`.  (`g = entropyDensity` diverges at
    `{0,2}`, so the clamp `r ↦ min(max(r,a), 2−a)` is what makes a globally-continuous representative whose
    spectral integrals agree with the divided balance on `σ(R) ⊆ [a,2−a]`.) -/
noncomputable def clampF (S : StandardSubspace H) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    C(Set.Icc (-covM S) (2 + covM S), ℝ) where
  toFun x := entropyDensity (min (max x.1 a) (2 - a)) / (2 - min (max x.1 a) (2 - a))^2
  continuous_toFun := by
    have hcl : Continuous (fun x : Set.Icc (-covM S) (2 + covM S) => min (max x.1 a) (2 - a)) :=
      (continuous_subtype_val.max continuous_const).min continuous_const
    have hmem : ∀ x : Set.Icc (-covM S) (2 + covM S),
        (min (max x.1 a) (2 - a)) ∈ Set.Icc a (2 - a) := fun x =>
      ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩
    have hpr : ∀ r ∈ Set.Icc a (2 - a), (0:ℝ) < r := fun r hr => lt_of_lt_of_le ha hr.1
    have hp2r : ∀ r ∈ Set.Icc a (2 - a), (0:ℝ) < 2 - r := fun r hr => by have := hr.2; linarith
    have hinner : ContinuousOn (fun r => (2 - r) / r) (Set.Icc a (2 - a)) :=
      (continuousOn_const.sub continuousOn_id).div continuousOn_id (fun r hr => (hpr r hr).ne')
    have hlog : ContinuousOn entropyDensity (Set.Icc a (2 - a)) :=
      Real.continuousOn_log.comp hinner (fun r hr => (div_pos (hp2r r hr) (hpr r hr)).ne')
    have hden : ContinuousOn (fun r => (2 - r)^2) (Set.Icc a (2 - a)) :=
      (continuousOn_const.sub continuousOn_id).pow 2
    exact (hlog.div hden (fun r hr => (pow_pos (hp2r r hr) 2).ne')).comp_continuous hcl hmem

@[simp] theorem clampF_apply (S : StandardSubspace H) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (x : Set.Icc (-covM S) (2 + covM S)) :
    clampF S a ha ha1 x = entropyDensity (min (max x.1 a) (2 - a)) / (2 - min (max x.1 a) (2 - a))^2 :=
  rfl

open QIQTH.StandardSubspaceModular in
/-- **★★★ THE CGP RELATIVE-ENTROPY POSITIVITY.**  For a one-particle state localized in the standard
    subspace (`ξ ∈ 𝒦`, i.e. `projK S ξ = ξ`) with modular spectrum away from the endpoints
    (`σ(R) ⊆ [a, 2−a]`, the finite-entropy regime), the modular relative entropy is nonnegative:
        `0 ≤ S(ξ)`.
    This is the localized (one-particle) instance of positivity of relative entropy `S(ρ‖σ) ≥ 0`, proved
    here axiom-free from the bounded RvD Tomita–Takesaki data via the CGP spectral balance.  (Localization
    is ESSENTIAL: for a general vector a point mass at `r < 1` gives `S = −log((2−r)/r) < 0`.) -/
theorem cgpEntropy_nonneg (S : StandardSubspace H) {ξ : H} (hξ : projK S ξ = ξ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : ℝ) ∧ (ω : ℝ) ≤ 2 - a) :
    0 ≤ cgpEntropy S ξ := by
  haveI : IsFiniteMeasure (rvdSpecMeasure S ξ) := by unfold rvdSpecMeasure; infer_instance
  have hpr : ∀ ω : spectrum ℝ (rvdRC S), (0:ℝ) < (ω:ℝ) := fun ω => lt_of_lt_of_le ha (hspec ω).1
  have hp2r : ∀ ω : spectrum ℝ (rvdRC S), (0:ℝ) < 2 - (ω:ℝ) := fun ω => by
    have := (hspec ω).2; linarith
  have hincl : ∀ ω : spectrum ℝ (rvdRC S),
      ((inclΩ S ω : Set.Icc (-covM S) (2 + covM S)) : ℝ) = (ω:ℝ) := fun _ => rfl
  have hcl : ∀ ω : spectrum ℝ (rvdRC S), min (max (ω:ℝ) a) (2 - a) = (ω:ℝ) := fun ω => by
    rw [max_eq_left (hspec ω).1, min_eq_left (hspec ω).2]
  have hcl2 : ∀ ω : spectrum ℝ (rvdRC S), min (max (2 - (ω:ℝ)) a) (2 - a) = 2 - (ω:ℝ) := fun ω => by
    rw [max_eq_left (by linarith [(hspec ω).2]), min_eq_left (by linarith [(hspec ω).1])]
  have hgfun_int : Integrable (fun ω : spectrum ℝ (rvdRC S) => entropyDensity (ω:ℝ))
      (rvdSpecMeasure S ξ) := hasFiniteEntropy_of_mem_Icc S ξ ha hspec
  -- the manifestly-nonpositive density `((r−1)/r)·g` is integrable (bounded × integrable)
  have hpfun_int : Integrable (fun ω : spectrum ℝ (rvdRC S) =>
      (((ω:ℝ) - 1)/(ω:ℝ)) * entropyDensity (ω:ℝ)) (rvdSpecMeasure S ξ) := by
    refine hgfun_int.bdd_mul
      (((measurable_subtype_coe.sub measurable_const).div measurable_subtype_coe).aestronglyMeasurable)
      (c := 1/a) (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpr ω), div_le_div_iff₀ (hpr ω) ha]
    have h1 : |(ω:ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [(hspec ω).1], by linarith [(hspec ω).2]⟩
    nlinarith [h1, (hspec ω).1, ha, abs_nonneg ((ω:ℝ) - 1)]
  -- the spectral balance at the clamped representative, evaluated pointwise on `σ(R)`
  have hbal := rvdSpec_balance S (clampF S a ha ha1) hξ
  have hL : ∀ ω : spectrum ℝ (rvdRC S),
      ((twoSubCoordReal S * twoSubCoordReal S) * clampF S a ha ha1) (inclΩ S ω)
        = entropyDensity (ω:ℝ) := by
    intro ω
    simp only [ContinuousMap.mul_apply, twoSubCoordReal, ContinuousMap.coe_mk, clampF_apply, hincl, hcl]
    have hne : (2 - (ω:ℝ)) ≠ 0 := (hp2r ω).ne'
    field_simp
  have hR : ∀ ω : spectrum ℝ (rvdRC S),
      ((coordReal S * twoSubCoordReal S) * (clampF S a ha ha1).comp (tauΩ S)) (inclΩ S ω)
        = -((2 - (ω:ℝ))/(ω:ℝ)) * entropyDensity (ω:ℝ) := by
    intro ω
    simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply, coordReal, twoSubCoordReal,
      ContinuousMap.coe_mk, clampF_apply, tauΩ, hincl]
    rw [hcl2, entropyDensity_reflect, show (2:ℝ) - (2 - (ω:ℝ)) = (ω:ℝ) by ring]
    have hne : (ω:ℝ) ≠ 0 := (hpr ω).ne'
    field_simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hL),
      integral_congr_ae (Filter.Eventually.of_forall hR)] at hbal
  -- algebra:  ∫g = ∫(−Δg) = 2∫p − ∫g  ⟹  ∫g = ∫p ≤ 0  ⟹  S(ξ) = −∫g ≥ 0
  have hrp : ∀ ω : spectrum ℝ (rvdRC S),
      -((2 - (ω:ℝ))/(ω:ℝ)) * entropyDensity (ω:ℝ)
        = 2 * ((((ω:ℝ) - 1)/(ω:ℝ)) * entropyDensity (ω:ℝ)) - entropyDensity (ω:ℝ) := by
    intro ω; have hne : (ω:ℝ) ≠ 0 := (hpr ω).ne'; field_simp; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hrp),
      integral_sub (hpfun_int.const_mul 2) hgfun_int, integral_const_mul] at hbal
  have hp_nonpos : ∫ ω, (((ω:ℝ) - 1)/(ω:ℝ)) * entropyDensity (ω:ℝ) ∂(rvdSpecMeasure S ξ) ≤ 0 := by
    refine integral_nonpos (fun ω => ?_)
    rcases le_total (ω:ℝ) 1 with h | h
    · refine mul_nonpos_iff.mpr (Or.inr ⟨div_nonpos_iff.mpr (Or.inr ⟨by linarith, (hpr ω).le⟩), ?_⟩)
      exact Real.log_nonneg (by rw [le_div_iff₀ (hpr ω)]; linarith)
    · refine mul_nonpos_iff.mpr (Or.inl ⟨div_nonneg (by linarith) (hpr ω).le, ?_⟩)
      exact Real.log_nonpos (div_nonneg (hp2r ω).le (hpr ω).le)
        ((div_le_one (hpr ω)).mpr (by linarith))
  have key : ∫ ω, entropyDensity (ω:ℝ) ∂(rvdSpecMeasure S ξ)
      = ∫ ω, (((ω:ℝ) - 1)/(ω:ℝ)) * entropyDensity (ω:ℝ) ∂(rvdSpecMeasure S ξ) := by linarith
  rw [cgpEntropy]
  show (0:ℝ) ≤ -∫ ω, entropyDensity (ω:ℝ) ∂(rvdSpecMeasure S ξ)
  linarith [key, hp_nonpos]

end QIQTH
