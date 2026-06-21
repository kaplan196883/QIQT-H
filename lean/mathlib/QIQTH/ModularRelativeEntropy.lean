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
import Mathlib.Analysis.Calculus.ParametricIntegral

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

/-! ### The derivative bridge — the modular Hamiltonian as `∂_t` of the modular flow

  Toward the entropy reduction `S(ω_{W(f)Ω}‖ω_Ω) = cgpEntropy(f)`: the vacuum characteristic function's
  `t`-derivative is the relative entropy.  Two ingredients: the pointwise `t`-derivative of the modular
  character (`∂_t u_t = i·g·u_t`, the modular Hamiltonian `g = entropyDensity` emerging as the generator),
  and the complex operator-expectation bridge `⟨ξ, U_t ξ⟩ = ∫ u_t dμ^R_ξ` connecting the flow to the
  spectral measure. -/

/-- **The pointwise `t`-derivative of the modular character:** `∂_t u_t(r) = i·log((2−r)/r)·u_t(r) =
    i·entropyDensity(r)·u_t(r)` for `r ∈ (0,2)`.  The modular Hamiltonian density `g = entropyDensity` is the
    generator of the modular character flow. -/
theorem hasDerivAt_modChar (t : ℝ) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 2) :
    HasDerivAt (fun s : ℝ => modChar s r)
      (Complex.I * (entropyDensity r : ℂ) * modChar t r) t := by
  have heq : (fun s : ℝ => modChar s r)
      = fun s : ℝ => Complex.exp (Complex.I * (s : ℂ) * (entropyDensity r : ℂ)) := by
    funext s; exact modChar_eq_exp_entropyDensity s hr
  rw [heq]
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have hg : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ) * (entropyDensity r : ℂ))
      (Complex.I * (entropyDensity r : ℂ)) t := by
    have h2 := (h1.const_mul Complex.I).mul_const (entropyDensity r : ℂ)
    simpa using h2
  rw [show Complex.I * (entropyDensity r : ℂ) * modChar t r
        = Complex.exp (Complex.I * (t : ℂ) * (entropyDensity r : ℂ)) * (Complex.I * (entropyDensity r : ℂ))
      from by rw [modChar_eq_exp_entropyDensity t hr]; ring]
  exact hg.cexp

/-- **The complex operator-expectation bridge for the modular flow:** `⟨ξ, U_t ξ⟩ = ∫ u_t dμ^R_ξ` — the
    matrix element of the bounded modular unitary `U_t = Δ^{it}` is the (complex) spectral integral of the
    modular character against the scalar spectral measure of `R` at `ξ`. -/
theorem rvdSpec_modUnitary (S : StandardSubspace H) (ξ : H) (t : ℝ) :
    inner ℂ ξ (modUnitary S t ξ) = ∫ ω, modSpecFun S t ω ∂(rvdSpecMeasure S ξ) := by
  rw [modUnitary, inner_borelFC, bilinDiag_self, ProjectionValuedMeasure.diagInt, rvdSpecMeasure]

/-- **The strip extension of the modular correlation** `F_ξ(z) = ∫ u_z(ω) dμ^R_ξ(ω)` — the candidate
    bounded-holomorphic extension of `t ↦ ⟪ξ, Δ^{it} ξ⟫` to the KMS strip, obtained by integrating the
    complexified modular character `modCharC` against the scalar spectral measure of `R` at `ξ`.  Toward
    discharging the labelled one-particle KMS-uniqueness (`hUniq`), this is the function that strip-uniqueness
    (`QIQTH.StripUniqueness`) compares against any competitor's correlation. -/
noncomputable def modCorrExt (S : StandardSubspace H) (ξ : H) (z : ℂ) : ℂ :=
  ∫ ω, modCharC z (ω : spectrum ℝ (rvdRC S)).val ∂(rvdSpecMeasure S ξ)

/-- **The strip extension restricts to the modular correlation on the real axis**:
    `F_ξ(t) = ⟪ξ, Δ^{it} ξ⟫`.  Immediate from `modCharC_ofReal` (`u_{(t:ℂ)} = u_t = modChar t`) and the
    spectral form `rvdSpec_modUnitary`. -/
theorem modCorrExt_ofReal (S : StandardSubspace H) (ξ : H) (t : ℝ) :
    modCorrExt S ξ (t : ℂ) = inner ℂ ξ (modUnitary S t ξ) := by
  rw [modCorrExt, rvdSpec_modUnitary]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  exact modCharC_ofReal t ω.val

/-- **The KMS boundary flip of the strip extension** (regular regime).  On the top edge `Im z = 1` of the
    KMS strip the extension is the modular correlation weighted by `ω/(2−ω)`:
    `F_ξ(t + i) = ∫ modChar t (ω) · (ω/(2−ω)) dμ^R_ξ`.  Together with `modCorrExt_ofReal` (the bottom edge,
    `F_ξ(t) = ⟪ξ, Δ^{it} ξ⟫`) this is the boundary data the strip-uniqueness principle consumes — the two
    edges that pin the extension.  Requires the spectrum of `R` to lie in `(0,2)` (the regular regime, where
    the modular weight is finite). -/
theorem modCorrExt_kms_flip (S : StandardSubspace H) (ξ : H) (t : ℝ)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2) :
    modCorrExt S ξ ((t : ℂ) + Complex.I)
      = ∫ ω, modChar t (ω : spectrum ℝ (rvdRC S)).val
          * (((ω : spectrum ℝ (rvdRC S)).val / (2 - (ω : spectrum ℝ (rvdRC S)).val) : ℝ) : ℂ)
          ∂(rvdSpecMeasure S ξ) := by
  rw [modCorrExt]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  have h := modCharC_kms_flip (hspec ω) (t : ℂ)
  rw [modCharC_ofReal] at h
  exact h

open MeasureTheory in
/-- **The strip extension is holomorphic on the open KMS strip** (regular regime).  In the regular spectral
    regime `σ(R) ⊆ [a, 2−a]` (`0 < a ≤ 1`), at every interior point `z₀` (with `Im z₀ ∈ (0,1)`) the strip
    extension `F_ξ(z) = ∫ u_z dμ^R_ξ` is complex-differentiable, with derivative
    `∫ i·log((2−ω)/ω)·u_{z₀}(ω) dμ`.  Differentiation under the spectral integral
    (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `𝕜 = ℂ`): the `z`-derivative `i·log·u_z` is bounded
    on the whole strip by the constant `log((2−a)/a)·(2−a)/a` (the modular frequency by `abs_log_div_le`, the
    character by `modCharC_norm_le`).  Together with `modCorrExt_ofReal`/`_kms_flip` this gives the
    bounded-holomorphic strip extension the strip-uniqueness principle consumes. -/
theorem hasDerivAt_modCorrExt (S : StandardSubspace H) (ξ : H) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : spectrum ℝ (rvdRC S)).val
      ∧ (ω : spectrum ℝ (rvdRC S)).val ≤ 2 - a)
    {z₀ : ℂ} (hz0 : z₀.im ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (modCorrExt S ξ)
      (∫ ω, Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
          / (ω : spectrum ℝ (rvdRC S)).val) : ℂ)
        * modCharC z₀ (ω : spectrum ℝ (rvdRC S)).val ∂(rvdSpecMeasure S ξ)) z₀ := by
  haveI : IsFiniteMeasure (rvdSpecMeasure S ξ) := by unfold rvdSpecMeasure; infer_instance
  have hposω : ∀ ω : spectrum ℝ (rvdRC S), (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2 :=
    fun ω => ⟨lt_of_lt_of_le ha0 (hspec ω).1, lt_of_le_of_lt (hspec ω).2 (by linarith)⟩
  set μ := rvdSpecMeasure S ξ
  -- measurability of the value coordinate and of the derivative coefficient
  have hmeasC : ∀ z : ℂ, AEStronglyMeasurable
      (fun ω : spectrum ℝ (rvdRC S) => modCharC z (ω : spectrum ℝ (rvdRC S)).val) μ :=
    fun z => ((measurable_modCharC z).comp measurable_subtype_coe).aestronglyMeasurable
  have hmeasL : Measurable fun ω : spectrum ℝ (rvdRC S) =>
      (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val) / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp
      ((measurable_const.sub measurable_subtype_coe).div measurable_subtype_coe))
  -- uniform norm bound for the character on the strip
  have hCbd : ∀ {z : ℂ}, z.im ∈ Set.Ioo (0 : ℝ) 1 → ∀ ω : spectrum ℝ (rvdRC S),
      ‖modCharC z (ω : spectrum ℝ (rvdRC S)).val‖ ≤ (2 - a) / a := by
    intro z hz ω
    exact modCharC_norm_le ha0 ha1 (hspec ω).1 (hspec ω).2 (le_of_lt hz.1) (le_of_lt hz.2)
  show HasDerivAt (fun z => ∫ ω, modCharC z (ω : spectrum ℝ (rvdRC S)).val ∂μ) _ z₀
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun z ω => modCharC z (ω : spectrum ℝ (rvdRC S)).val)
    (F' := fun z ω => Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
        / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) * modCharC z (ω : spectrum ℝ (rvdRC S)).val)
    (bound := fun _ => Real.log ((2 - a) / a) * ((2 - a) / a))
    (s := Complex.im ⁻¹' Set.Ioo (0 : ℝ) 1)
    ((Complex.continuous_im.isOpen_preimage _ isOpen_Ioo).mem_nhds hz0)
    (Filter.Eventually.of_forall (fun z => hmeasC z))
    (((integrable_const ((2 - a) / a)).mono' (hmeasC z₀)
      (Filter.Eventually.of_forall (fun ω => by
        simpa using hCbd hz0 ω))))
    ((measurable_const.mul hmeasL).mul ((measurable_modCharC z₀).comp
      measurable_subtype_coe) |>.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ω z hz => ?_))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun ω z _ => hasDerivAt_modCharC (hposω ω) z))).2
  -- the domination bound on the derivative
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val) / (ω : spectrum ℝ (rvdRC S)).val)|
        * ‖modCharC z (ω : spectrum ℝ (rvdRC S)).val‖
      ≤ Real.log ((2 - a) / a) * ((2 - a) / a) := by
        apply mul_le_mul (abs_log_div_le ha0 (hspec ω).1 (hspec ω).2) (hCbd hz ω)
          (norm_nonneg _) (Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith))

/-- **The strip extension is differentiable on the open KMS strip** (regular regime): immediate from
    `hasDerivAt_modCorrExt` at every interior point.  The differentiability half of the
    bounded-holomorphic strip extension that strip-uniqueness consumes. -/
theorem differentiableOn_modCorrExt (S : StandardSubspace H) (ξ : H) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : spectrum ℝ (rvdRC S)).val
      ∧ (ω : spectrum ℝ (rvdRC S)).val ≤ 2 - a) :
    DifferentiableOn ℂ (modCorrExt S ξ) (Complex.im ⁻¹' Set.Ioo (0 : ℝ) 1) := fun z hz =>
  (hasDerivAt_modCorrExt S ξ ha0 ha1 hspec hz).differentiableAt.differentiableWithinAt

open MeasureTheory in
/-- **★★ The strip extension is differentiable on the open KMS strip AND continuous up to its closure**
    (`DiffContOnCl`), in the regular regime.  Differentiability on the open strip is
    `differentiableOn_modCorrExt`; continuity on the closed strip `{0 ≤ Im ≤ 1}` is dominated continuity of
    the integral (`continuousOn_of_dominated`: the integrand `u_z(ω)` is continuous in `z` and uniformly
    bounded by `(2−a)/a` on the closed strip).  This is the precise regularity the KMS strip-uniqueness
    principle (`QIQTH.StripUniqueness.eqOn_of_bdd_holomorphic_strip`) consumes — the bounded-holomorphic
    strip extension of the modular correlation, now fully assembled. -/
theorem diffContOnCl_modCorrExt (S : StandardSubspace H) (ξ : H) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : spectrum ℝ (rvdRC S)).val
      ∧ (ω : spectrum ℝ (rvdRC S)).val ≤ 2 - a) :
    DiffContOnCl ℂ (modCorrExt S ξ) (Complex.im ⁻¹' Set.Ioo (0 : ℝ) 1) := by
  haveI : IsFiniteMeasure (rvdSpecMeasure S ξ) := by unfold rvdSpecMeasure; infer_instance
  refine ⟨differentiableOn_modCorrExt S ξ ha0 ha1 hspec, ?_⟩
  rw [Complex.closure_preimage_im, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hmeasC : ∀ z : ℂ, AEStronglyMeasurable
      (fun ω : spectrum ℝ (rvdRC S) => modCharC z (ω : spectrum ℝ (rvdRC S)).val) (rvdSpecMeasure S ξ) :=
    fun z => ((measurable_modCharC z).comp measurable_subtype_coe).aestronglyMeasurable
  exact continuousOn_of_dominated (fun x _ => hmeasC x)
    (fun x hx => Filter.Eventually.of_forall (fun ω =>
      modCharC_norm_le ha0 ha1 (hspec ω).1 (hspec ω).2 hx.1 hx.2))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun ω => (differentiable_modCharC _).continuous.continuousOn))

open MeasureTheory in
/-- **Uniform bound on the strip extension** (regular regime): `‖F_ξ(z)‖ ≤ ((2−a)/a)·‖ξ‖²` for `z` in the
    closed KMS strip.  Integrating the character bound `modCharC_norm_le` against the finite spectral measure
    (`μ^R_ξ(univ) = ‖ξ‖²`).  This is the `‖·‖`-bound hypothesis the strip-uniqueness principle consumes
    alongside `diffContOnCl_modCorrExt`. -/
theorem modCorrExt_norm_le (S : StandardSubspace H) (ξ : H) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : spectrum ℝ (rvdRC S)).val
      ∧ (ω : spectrum ℝ (rvdRC S)).val ≤ 2 - a)
    {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ 1) :
    ‖modCorrExt S ξ z‖ ≤ (2 - a) / a * ‖ξ‖ ^ 2 := by
  haveI : IsFiniteMeasure (rvdSpecMeasure S ξ) := by unfold rvdSpecMeasure; infer_instance
  rw [modCorrExt]
  calc ‖∫ ω, modCharC z (ω : spectrum ℝ (rvdRC S)).val ∂(rvdSpecMeasure S ξ)‖
      ≤ ∫ ω, (2 - a) / a ∂(rvdSpecMeasure S ξ) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (integrable_const _) (Filter.Eventually.of_forall (fun ω => ?_))
        exact modCharC_norm_le ha0 ha1 (hspec ω).1 (hspec ω).2 hz0 hz1
    _ = (2 - a) / a * ‖ξ‖ ^ 2 := by
        rw [MeasureTheory.integral_const, smul_eq_mul, MeasureTheory.measureReal_def,
          rvdSpecMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg ‖ξ‖), mul_comm]

/-- The **device strip extension** `D_ξ(z) = ∫ d_z(ω) dμ^R_ξ(ω)` — the RvD Proposition 3.7 *device* analogue
    of `modCorrExt`, integrating the device character `devChar` (`= u_z(r)·√r`) against the scalar spectral
    measure of `R` at `ξ`.  Where `modCorrExt = ∫ u_z dμ` is bounded-holomorphic on the KMS strip ONLY in the
    regular regime `σ(R) ⊆ [a, 2−a]`, the `√r` factor tames the singularity so this device extension is bounded
    on the half-strip for EVERY standard subspace (see `devCorrExt_norm_le`). -/
noncomputable def devCorrExt (S : StandardSubspace H) (ξ : H) (z : ℂ) : ℂ :=
  ∫ ω, devChar z (ω : spectrum ℝ (rvdRC S)).val ∂(rvdSpecMeasure S ξ)

open MeasureTheory in
/-- **Uniform bound of the device strip extension on the half-strip — with NO regular-window assumption**:
    `‖D_ξ(z)‖ ≤ √2·‖ξ‖²` for every `z` with `−1/2 ≤ Im z ≤ 0`, for ANY standard subspace.  The device character
    is bounded by `√2` over the WHOLE spectrum `σ(R) ⊆ [0,2]` (`devChar_norm_le_Icc` + `rvdRC_spectrum_mem_Icc`)
    — no `σ(R) ⊆ [a,2−a]` hypothesis — integrated against the finite spectral measure (`μ^R_ξ(univ) = ‖ξ‖²`).
    This is the decisive advantage of RvD's Prop 3.7 device over the bare modular character `modCorrExt`: the
    bounded-holomorphic half-strip input the strip-uniqueness comparison needs exists for every standard
    subspace, not just the regular ones. -/
theorem devCorrExt_norm_le (S : StandardSubspace H) (ξ : H) {z : ℂ} (hz2 : z.im ≤ 0)
    (hz1 : -(1 / 2 : ℝ) ≤ z.im) : ‖devCorrExt S ξ z‖ ≤ Real.sqrt 2 * ‖ξ‖ ^ 2 := by
  haveI : IsFiniteMeasure (rvdSpecMeasure S ξ) := by unfold rvdSpecMeasure; infer_instance
  rw [devCorrExt]
  calc ‖∫ ω, devChar z (ω : spectrum ℝ (rvdRC S)).val ∂(rvdSpecMeasure S ξ)‖
      ≤ ∫ _ω, Real.sqrt 2 ∂(rvdSpecMeasure S ξ) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (integrable_const _) (Filter.Eventually.of_forall (fun ω => ?_))
        exact devChar_norm_le_Icc hz2 hz1 (rvdRC_spectrum_mem_Icc S ω)
    _ = Real.sqrt 2 * ‖ξ‖ ^ 2 := by
        rw [MeasureTheory.integral_const, smul_eq_mul, MeasureTheory.measureReal_def,
          rvdSpecMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg ‖ξ‖), mul_comm]

open MeasureTheory in
/-- **The device strip extension is holomorphic on the OPEN half-strip — with NO regular-window assumption**.
    At every interior `z₀` (`Im z₀ ∈ (−1/2, 0)`), differentiation under the spectral integral
    (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `𝕜 = ℂ`) gives
    `(devCorrExt S ξ)'(z₀) = ∫ i·log((2−ω)/ω)·d_{z₀}(ω) dμ`.  The dominators are the device's two
    *constant* (regular-window-free) bounds: `‖d_z‖ ≤ √2` (`devChar_norm_le_Icc`) for `F`, and the assembled
    `devChar_deriv_norm_le` constant for `F'`, both uniform over a slab neighborhood
    `s = {c < Im z < d}` with `[c,d] ⊂ (−1/2,0) ∋ Im z₀`.  Endpoints `ω ∈ {0,2}` of `σ(R) ⊆ [0,2]` are
    handled by `hasDerivAt_devChar_Icc` (the orbit is `z`-constant there).  This is the holomorphy half of the
    bounded-holomorphic half-strip extension that the strip-uniqueness comparison consumes — available for
    EVERY standard subspace, the decisive advantage of the RvD Prop 3.7 device. -/
theorem hasDerivAt_devCorrExt (S : StandardSubspace H) (ξ : H)
    {z₀ : ℂ} (hz0 : z₀.im ∈ Set.Ioo (-(1 / 2) : ℝ) 0) :
    HasDerivAt (devCorrExt S ξ)
      (∫ ω, Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
          / (ω : spectrum ℝ (rvdRC S)).val) : ℂ)
        * devChar z₀ (ω : spectrum ℝ (rvdRC S)).val ∂(rvdSpecMeasure S ξ)) z₀ := by
  haveI : IsFiniteMeasure (rvdSpecMeasure S ξ) := by unfold rvdSpecMeasure; infer_instance
  set μ := rvdSpecMeasure S ξ
  obtain ⟨hz0lo, hz0hi⟩ := hz0
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set c : ℝ := (z₀.im - 1 / 2) / 2 with hc
  set d : ℝ := z₀.im / 2 with hd
  have hcd_lo : -(1 / 2 : ℝ) < c := by rw [hc]; linarith
  have hcz : c < z₀.im := by rw [hc]; linarith
  have hzd : z₀.im < d := by rw [hd]; linarith
  have hd0 : d < 0 := by rw [hd]; linarith
  set β₀ : ℝ := -d with hβ₀def
  set β₁ : ℝ := -c with hβ₁def
  have hβ₀ : 0 < β₀ := by rw [hβ₀def]; linarith
  have hβ₁ : β₁ < 1 / 2 := by rw [hβ₁def]; linarith
  have hβ₁' : 0 < 1 / 2 - β₁ := by linarith
  set s : Set ℂ := Complex.im ⁻¹' Set.Ioo c d with hs
  have hz0s : z₀ ∈ s := by rw [hs, Set.mem_preimage, Set.mem_Ioo]; exact ⟨hcz, hzd⟩
  have hspec : ∀ ω : spectrum ℝ (rvdRC S), (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Icc (0 : ℝ) 2 :=
    rvdRC_spectrum_mem_Icc S
  set C : ℝ := Real.sqrt 2 * (2 / β₀ + Real.log 2) + Real.sqrt 2 * (2 / (1 / 2 - β₁) + Real.log 2)
    with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ 2 / β₀ := le_of_lt (div_pos (by norm_num) hβ₀)
    have h2 : (0 : ℝ) ≤ 2 / (1 / 2 - β₁) := le_of_lt (div_pos (by norm_num) hβ₁')
    nlinarith [Real.sqrt_nonneg 2, hlog2, h1, h2]
  have hmeasF : ∀ z : ℂ, AEStronglyMeasurable
      (fun ω : spectrum ℝ (rvdRC S) => devChar z (ω : spectrum ℝ (rvdRC S)).val) μ :=
    fun z => ((measurable_devChar z).comp measurable_subtype_coe).aestronglyMeasurable
  have hmeasL : Measurable fun ω : spectrum ℝ (rvdRC S) =>
      (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val) / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp
      ((measurable_const.sub measurable_subtype_coe).div measurable_subtype_coe))
  have hFbd : ∀ {z : ℂ}, z ∈ s → ∀ ω : spectrum ℝ (rvdRC S),
      ‖devChar z (ω : spectrum ℝ (rvdRC S)).val‖ ≤ Real.sqrt 2 := by
    intro z hz ω
    rw [hs, Set.mem_preimage, Set.mem_Ioo] at hz
    exact devChar_norm_le_Icc (le_of_lt (lt_trans hz.2 hd0))
      (le_of_lt (lt_trans hcd_lo hz.1)) (hspec ω)
  have hF'bd : ∀ {z : ℂ}, z ∈ s → ∀ ω : spectrum ℝ (rvdRC S),
      ‖Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
          / (ω : spectrum ℝ (rvdRC S)).val) : ℂ)
        * devChar z (ω : spectrum ℝ (rvdRC S)).val‖ ≤ C := by
    intro z hz ω
    rw [hs, Set.mem_preimage, Set.mem_Ioo] at hz
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hω : (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2
    · rw [hCdef]
      exact devChar_deriv_norm_le hβ₀ hβ₁
        (show z.im ≤ -β₀ by rw [hβ₀def, neg_neg]; exact le_of_lt hz.2)
        (show -β₁ ≤ z.im by rw [hβ₁def, neg_neg]; exact le_of_lt hz.1) hω
    · have hr02 : (ω : spectrum ℝ (rvdRC S)).val = 0 ∨ (ω : spectrum ℝ (rvdRC S)).val = 2 := by
        obtain ⟨h0', h2'⟩ := Set.mem_Icc.mp (hspec ω)
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hω
        exact hω.imp (fun hle => le_antisymm hle h0') (fun hge => le_antisymm h2' hge)
      have hzero : |Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
          / (ω : spectrum ℝ (rvdRC S)).val)|
          * ‖devChar z (ω : spectrum ℝ (rvdRC S)).val‖ = 0 := by
        rcases hr02 with h | h <;> rw [h] <;> simp [devChar, Real.sqrt_zero]
      rw [hzero]; exact hC0
  show HasDerivAt (fun z => ∫ ω, devChar z (ω : spectrum ℝ (rvdRC S)).val ∂μ) _ z₀
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun z ω => devChar z (ω : spectrum ℝ (rvdRC S)).val)
    (F' := fun z ω => Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
        / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) * devChar z (ω : spectrum ℝ (rvdRC S)).val)
    (bound := fun _ => C) (s := s)
    ((Complex.continuous_im.isOpen_preimage _ isOpen_Ioo).mem_nhds hz0s)
    (Filter.Eventually.of_forall (fun z => hmeasF z))
    ((integrable_const (Real.sqrt 2)).mono' (hmeasF z₀)
      (Filter.Eventually.of_forall (fun ω => by simpa using hFbd hz0s ω)))
    ((measurable_const.mul hmeasL).mul ((measurable_devChar z₀).comp
      measurable_subtype_coe) |>.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ω z hz => hF'bd hz ω))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun ω z _ => hasDerivAt_devChar_Icc (hspec ω) z))).2

/-- **Real-axis value of the device strip extension** (scalar form): `D_ξ(t) = ∫ u_t(ω)·√ω dμ^R_ξ`, the
    `√r`-weighted modular correlation.  Immediate from `devChar_ofReal` (`d_{(t:ℂ)}(r) = u_t(r)·√r`) under the
    integral.  As an operator expectation this is `⟪ξ, Δ^{it}·√R ξ⟫` (the device's `√R` regularization of the
    bare modular correlation `modCorrExt`); the operator identification needs the `borelFC`↔`CFC.sqrt` product
    bridge, deferred. -/
theorem devCorrExt_ofReal (S : StandardSubspace H) (ξ : H) (t : ℝ) :
    devCorrExt S ξ (t : ℂ)
      = ∫ ω, modChar t (ω : spectrum ℝ (rvdRC S)).val
          * (Real.sqrt (ω : spectrum ℝ (rvdRC S)).val : ℂ) ∂(rvdSpecMeasure S ξ) := by
  rw [devCorrExt]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun ω => devChar_ofReal t (ω : spectrum ℝ (rvdRC S)).val))

/-- The **device spectral symbol on the real axis** `ω ↦ d_t(ω) = u_t(ω)·√ω`, the bounded measurable
    function of `R` whose functional calculus is the real-axis device operator `Δ^{it}·√R`. -/
noncomputable def devSpecReal (S : StandardSubspace H) (t : ℝ) : spectrum ℝ (rvdRC S) → ℂ :=
  fun ω => devChar (t : ℂ) (ω : spectrum ℝ (rvdRC S)).val

theorem devSpecReal_measurable (S : StandardSubspace H) (t : ℝ) : Measurable (devSpecReal S t) :=
  (measurable_devChar (t : ℂ)).comp measurable_subtype_coe

theorem devSpecReal_norm_le (S : StandardSubspace H) (t : ℝ) (ω : spectrum ℝ (rvdRC S)) :
    ‖devSpecReal S t ω‖ ≤ Real.sqrt 2 :=
  devChar_norm_le_Icc (by norm_num [Complex.ofReal_im]) (by norm_num [Complex.ofReal_im])
    (rvdRC_spectrum_mem_Icc S ω)

/-- The **real-axis device operator** `Δ^{it}·√R = d_t(R)`, the bounded Borel functional calculus of `R` at
    the device symbol `devSpecReal` (`‖d_t‖ ≤ √2` on the spectrum, no regular window). -/
noncomputable def deviceOpReal (S : StandardSubspace H) (t : ℝ) : H →L[ℂ] H :=
  borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) (devSpecReal_measurable S t) (Real.sqrt_nonneg 2)
    (devSpecReal_norm_le S t)

/-- The **complex-`z` device operator** `d_z(R) = (2−R)^{iz} R^{−iz+1/2}` for `z` in the half-strip
    `−1/2 ≤ Im z ≤ 0`, where `‖d_z‖ ≤ √2` on `σ(R) ⊆ [0,2]` (no regular window, `devChar_norm_le_Icc` +
    `rvdRC_spectrum_mem_Icc`).  This is RvD's Proposition 3.7 *device* (verified against the rendered source):
    the operator whose `J`-image `J·(d_z(R) ζ)` is the (anti-holomorphic, since `J` is antilinear) second-slot
    vector of the Theorem 3.8 g-function `g(z) = ⟨h(z), J d_z(R) ζ⟩`.  Generalizes `deviceOpReal` (the `z = t`
    real-axis case) to the whole half-strip. -/
noncomputable def deviceOpC (S : StandardSubspace H) (z : ℂ) (hz2 : z.im ≤ 0)
    (hz1 : -(1 / 2 : ℝ) ≤ z.im) : H →L[ℂ] H :=
  borelFC (rvdRC S) (rvdRC_isSelfAdjoint S)
    ((measurable_devChar z).comp measurable_subtype_coe) (Real.sqrt_nonneg 2)
    (fun ω => devChar_norm_le_Icc hz2 hz1 (rvdRC_spectrum_mem_Icc S ω))

/-- **Total device-vector function** `z ↦ deviceOpC(z)ζ` (piece 4 of the strong holomorphy): a `dite`-total
    function on all of `ℂ`, equal to `deviceOpC(z)ζ` on the closed half-strip `{−1/2 ≤ Im z ≤ 0}` (where the
    device operator's `√2` bound holds) and `0` outside.  The totality sidesteps the `deviceOpC`-takes-proofs
    friction: `HasDerivAt (deviceVecF S ζ)` is a statement about a genuine `ℂ → H` function, provable at every
    interior `z₀` because `deviceVecF` agrees with the `borelFC` branch on a neighborhood.  Its Fréchet
    derivative is `borelFC(ω ↦ i·log((2−ω)/ω)·d_{z₀}(ω))ζ`, with `‖slope − deriv‖² = ∫‖Δ_z − ∂d‖² dμ^R_ζ → 0`
    (`borelFC_sub` + `borelFC_smul` + `borelFC_apply_norm_sq` + `tendsto_integral_devChar_remainder_sq`). -/
noncomputable def deviceVecF (S : StandardSubspace H) (ζ : H) (z : ℂ) : H :=
  if h : z.im ≤ 0 ∧ -(1 / 2 : ℝ) ≤ z.im then deviceOpC S z h.1 h.2 ζ else 0

/-- On the closed half-strip, `deviceVecF` is the device operator applied to `ζ` (proof-irrelevant `dite`). -/
theorem deviceVecF_eq_of_mem (S : StandardSubspace H) (ζ : H) {z : ℂ}
    (hz2 : z.im ≤ 0) (hz1 : -(1 / 2 : ℝ) ≤ z.im) :
    deviceVecF S ζ z = deviceOpC S z hz2 hz1 ζ := dif_pos ⟨hz2, hz1⟩

/-- **`deviceOpC` at a real point is `deviceOpReal`** (`d_{(t:ℂ)} = d_t`): the half-strip device operator
    restricts to the real-axis device operator `Δ^{it}·√R` on the boundary `Im z = 0`. -/
theorem deviceOpC_ofReal (S : StandardSubspace H) (t : ℝ) :
    deviceOpC S (t : ℂ) (by simp) (by norm_num [Complex.ofReal_im]) = deviceOpReal S t := rfl

/-- **Operator-norm bound for the complex-`z` device operator**: `‖d_z(R)‖ ≤ 2√2` uniformly on the half-strip
    `−1/2 ≤ Im z ≤ 0` (the bounded-FC norm bound `‖borelFC f‖ ≤ 2·sup‖f‖` applied to the device symbol bound
    `‖d_z‖ ≤ √2`).  This is the operator-level boundedness the g-function `g(z) = ⟨h(z), J d_z(R) ζ⟩` consumes:
    `‖g(z)‖ ≤ ‖h(z)‖·‖d_z(R)ζ‖ ≤ ‖h(z)‖·2√2·‖ζ‖`, uniform over the half-strip. -/
theorem deviceOpC_norm_le (S : StandardSubspace H) (z : ℂ) (hz2 : z.im ≤ 0)
    (hz1 : -(1 / 2 : ℝ) ≤ z.im) : ‖deviceOpC S z hz2 hz1‖ ≤ 2 * Real.sqrt 2 := by
  rw [deviceOpC, borelFC]
  exact (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC_norm_le _ _ _

open QIQTH.StandardSubspaceModular in
/-- **The device operator at `z = 0` is `√R`** (`deviceOpReal 0 = rvdSqrtR`, the device interpolation start).
    `devChar 0 = √·`, so `deviceOpReal 0 = borelFC(√·) = cfcCont(√·)`, and `cfcCont(√·)` is the *positive*
    square root of `R`: `(cfcCont √·)² = R` (`cfcCont_mul` + `cfcCont_coord`, since `√ω·√ω = ω` on `σ(R)⊆[0,∞)`),
    and `cfcCont(√·) = (cfcCont ∜·)² ≥ 0` (`cfcCont ∜·` self-adjoint as a real symbol).  `CFC.sqrt_unique` then
    identifies it with `CFC.sqrt R = rvdSqrtR`.  Hence `deviceOpReal 0 ζ = R^{1/2}ζ = ξ`, so the g-function's
    value at the origin is `g(0) = ⟪η, Jξ⟫` — the right-hand side of `GConstancy`. -/
theorem deviceOpReal_zero (S : StandardSubspace H) : deviceOpReal S 0 = rvdSqrtR S := by
  set sqrtC : C(spectrum ℝ (rvdRC S), ℂ) :=
    ⟨fun ω => (Real.sqrt (ω : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_subtype_val)⟩ with hsqrtC
  set qrtC : C(spectrum ℝ (rvdRC S), ℂ) :=
    ⟨fun ω => (Real.sqrt (Real.sqrt (ω : ℝ)) : ℂ),
      Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (Real.continuous_sqrt.comp continuous_subtype_val))⟩ with hqrtC
  have hdev : deviceOpReal S 0 = cfcCont S sqrtC := by
    rw [deviceOpReal, cfcCont]
    refine borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) _ _ _ _ _ _ ?_
    ext ω
    show devSpecReal S 0 ω = (Real.sqrt (ω : ℝ) : ℂ)
    rw [devSpecReal, Complex.ofReal_zero, devChar_zero]
  have hsq : cfcCont S sqrtC * cfcCont S sqrtC = rvdRC S := by
    rw [← cfcCont_mul]
    refine (?_ : cfcCont S (sqrtC * sqrtC) = cfcCont S _).trans (cfcCont_coord S)
    congr 1
    ext ω
    show (Real.sqrt (ω : ℝ) : ℂ) * (Real.sqrt (ω : ℝ) : ℂ) = specCoord S ω
    rw [specCoord, ← Complex.ofReal_mul, Real.mul_self_sqrt (rvdRC_spectrum_mem_Icc S ω).1]
  have hpos : 0 ≤ cfcCont S sqrtC := by
    have hsqrtC_eq : sqrtC = qrtC * qrtC := by
      ext ω
      show (Real.sqrt (ω : ℝ) : ℂ)
        = (Real.sqrt (Real.sqrt (ω : ℝ)) : ℂ) * (Real.sqrt (Real.sqrt (ω : ℝ)) : ℂ)
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
    have hsa : star (cfcCont S qrtC) = cfcCont S qrtC := by
      rw [← cfcCont_star]
      congr 1
      ext ω
      show (starRingEnd ℂ) (Real.sqrt (Real.sqrt (ω : ℝ)) : ℂ) = (Real.sqrt (Real.sqrt (ω : ℝ)) : ℂ)
      exact Complex.conj_ofReal _
    rw [hsqrtC_eq, cfcCont_mul]
    calc (0 : H →L[ℂ] H) ≤ star (cfcCont S qrtC) * cfcCont S qrtC := star_mul_self_nonneg _
      _ = cfcCont S qrtC * cfcCont S qrtC := by rw [hsa]
  rw [hdev, rvdSqrtR]
  exact (CFC.sqrt_unique hsq hpos).symm

open QIQTH.StandardSubspaceModular in
/-- **The real-axis device operator factors as `Δ^{it}·√R`**: `deviceOpReal t = modUnitary S t · rvdSqrtR`
    (the general top-edge operator identity, `deviceOpReal_zero` is the `t = 0` case).  `devChar(↑t) =
    u_t·√·` (`devChar_ofReal`), so `borelFC(devChar ↑t) = borelFC(u_t)·borelFC(√·) = Δ^{it}·√R`
    (`borelFC_mul` + `modUnitary = borelFC(u_t)` + `borelFC(√·) = rvdSqrtR` from `deviceOpReal_zero`).  Hence
    the device vector at the real axis is `deviceVec(t) = deviceOpReal t ζ = Δ^{it}(√R ζ) = Δ^{it}ξ`, so the
    g-function's top edge is `g(t) = ⟪U_t η, J Δ^{it} ξ⟫` (`gTopEdge_real`, real). -/
theorem deviceOpReal_eq (S : StandardSubspace H) (t : ℝ) :
    deviceOpReal S t = modUnitary S t * rvdSqrtR S := by
  rw [← deviceOpReal_zero S, deviceOpReal, modUnitary, deviceOpReal]
  have hpm : Measurable (fun ω => modSpecFun S t ω * devSpecReal S 0 ω) :=
    (modSpecFun_measurable S t).mul (devSpecReal_measurable S 0)
  have hpb : ∀ ω, ‖modSpecFun S t ω * devSpecReal S 0 ω‖ ≤ Real.sqrt 2 := fun ω => by
    rw [norm_mul]
    calc ‖modSpecFun S t ω‖ * ‖devSpecReal S 0 ω‖
        ≤ 1 * Real.sqrt 2 :=
          mul_le_mul (modSpecFun_norm_le S t ω) (devSpecReal_norm_le S 0 ω) (norm_nonneg _) zero_le_one
      _ = Real.sqrt 2 := one_mul _
  rw [← borelFC_mul (rvdRC S) (rvdRC_isSelfAdjoint S)
        (modSpecFun_measurable S t) zero_le_one (modSpecFun_norm_le S t)
        (devSpecReal_measurable S 0) (Real.sqrt_nonneg 2) (devSpecReal_norm_le S 0)
        hpm (Real.sqrt_nonneg 2) hpb]
  refine borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) (devSpecReal_measurable S t)
    (Real.sqrt_nonneg 2) (devSpecReal_norm_le S t) hpm (Real.sqrt_nonneg 2) hpb (funext fun ω => ?_)
  show devSpecReal S t ω = modSpecFun S t ω * devSpecReal S 0 ω
  simp only [devSpecReal, modSpecFun, devChar_ofReal, Complex.ofReal_zero, devChar_zero]

open MeasureTheory in
/-- **`L²` identity for the bounded Borel FC**: `⟪f(R)ζ, f(R)ζ⟫ = ∫ conj(f)·f dμ^R_ζ` (`= ∫|f|² dμ`, so
    `‖f(R)ζ‖² = ∫|f|² dμ^R_ζ`).  Via `⟪Aζ,Aζ⟫ = ⟪ζ, A*Aζ⟫` (`adjoint_inner_right`), `A* = borelFC(conj f)`
    (`borelFC_adjoint`), `A*·A = borelFC(conj f·f)` (`borelFC_mul`), then the spectral bridge
    `⟪ζ, g(R)ζ⟫ = ∫ g dμ^R_ζ` (`inner_borelFC`).  This is the linchpin for the strong (Fréchet) holomorphy of
    `z ↦ d_z(R)ζ`: the difference-quotient remainder `q − d` satisfies `‖q − d‖² = ∫|Δ_z − ∂_z d|² dμ^R_ζ → 0`
    by dominated convergence (the derivative is dominated by the `devChar_deriv_norm_le` constant). -/
theorem borelFC_inner_self (S : StandardSubspace H) {g : spectrum ℝ (rvdRC S) → ℂ}
    (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω, ‖g ω‖ ≤ C) (ζ : H) :
    inner ℂ (borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) hg hC0 hC ζ)
        (borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) hg hC0 hC ζ)
      = ∫ ω, (starRingEnd ℂ) (g ω) * g ω ∂(rvdSpecMeasure S ζ) := by
  have hcg : Measurable (fun ω => (starRingEnd ℂ) (g ω)) := Complex.continuous_conj.measurable.comp hg
  have hcgb : ∀ ω, ‖(starRingEnd ℂ) (g ω)‖ ≤ C := fun ω => by rw [RCLike.norm_conj]; exact hC ω
  have hpm : Measurable (fun ω => (starRingEnd ℂ) (g ω) * g ω) := hcg.mul hg
  have hpb : ∀ ω, ‖(starRingEnd ℂ) (g ω) * g ω‖ ≤ C * C := fun ω => by
    rw [norm_mul]; exact mul_le_mul (hcgb ω) (hC ω) (norm_nonneg _) hC0
  rw [← ContinuousLinearMap.adjoint_inner_right,
    borelFC_adjoint (rvdRC S) (rvdRC_isSelfAdjoint S) hg hC0 hC hcg hC0 hcgb,
    ← ContinuousLinearMap.mul_apply,
    ← borelFC_mul (rvdRC S) (rvdRC_isSelfAdjoint S) hcg hC0 hcgb hg hC0 hC hpm
      (mul_nonneg hC0 hC0) hpb,
    inner_borelFC, bilinDiag_self, ProjectionValuedMeasure.diagInt, rvdSpecMeasure]

open MeasureTheory in
/-- **`L²` isometry (real form)**: `‖f(R)ζ‖² = ∫ ‖f(ω)‖² dμ^R_ζ`.  The real-valued restatement of
    `borelFC_inner_self` (`⟪f(R)ζ,f(R)ζ⟫ = ↑‖f(R)ζ‖²`, and `conj(f)·f = ↑‖f‖²`).  This is the form the
    strong-holomorphy difference-quotient argument uses directly: `‖q_z − d‖² = ∫‖Δ_z − ∂_z d‖² dμ^R_ζ → 0`. -/
theorem borelFC_apply_norm_sq (S : StandardSubspace H) {g : spectrum ℝ (rvdRC S) → ℂ}
    (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω, ‖g ω‖ ≤ C) (ζ : H) :
    ‖borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) hg hC0 hC ζ‖ ^ 2
      = ∫ ω, ‖g ω‖ ^ 2 ∂(rvdSpecMeasure S ζ) := by
  have hcast : (∫ ω, (starRingEnd ℂ) (g ω) * g ω ∂(rvdSpecMeasure S ζ))
      = ((∫ ω, ‖g ω‖ ^ 2 ∂(rvdSpecMeasure S ζ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show (starRingEnd ℂ) (g ω) * g ω = ((‖g ω‖ ^ 2 : ℝ) : ℂ)
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  have hre := inner_self_eq_norm_sq (𝕜 := ℂ)
    (borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) hg hC0 hC ζ)
  rw [borelFC_inner_self S hg hC0 hC ζ, hcast] at hre
  simpa using hre.symm

open QIQTH.StandardSubspaceModular in
/-- **Bottom-edge `t`-translation of the device operator**: `deviceOpC(t − i/2) = Δ^{it}·deviceOpC(−i/2)`
    (the bottom-edge analogue of `deviceOpReal_eq`).  `devChar(↑t − i/2) = u_t·devChar(−i/2)` EVERYWHERE (via
    `modCharC_add`: `u_{↑t + (−i/2)} = u_{↑t}·u_{−i/2}`, no endpoint issue), so `borelFC` factors through
    `borelFC_mul` into `modUnitary t · deviceOpC(−i/2)`.  Hence the device vector along the bottom edge is
    `deviceVec(t − i/2) = Δ^{it}·deviceVec(−i/2)` — the modular flow translating the fixed bottom-edge vector. -/
theorem deviceOpC_bottomEdge_eq (S : StandardSubspace H) (t : ℝ) :
    deviceOpC S ((t : ℂ) - Complex.I / 2)
        (by simp [Complex.sub_im, Complex.div_im, Complex.I_im])
        (by rw [show ((t : ℂ) - Complex.I / 2).im = -(1 / 2) from by
              simp [Complex.sub_im, Complex.div_im, Complex.I_im]])
      = modUnitary S t * deviceOpC S (-(Complex.I / 2))
        (by simp [Complex.neg_im, Complex.div_im, Complex.I_im])
        (by rw [show (-(Complex.I / 2)).im = -(1 / 2) from by
              simp [Complex.neg_im, Complex.div_im, Complex.I_im]]) := by
  rw [deviceOpC, deviceOpC, modUnitary]
  have hpm : Measurable
      (fun ω : spectrum ℝ (rvdRC S) => modSpecFun S t ω * devChar (-(Complex.I / 2)) (ω : ℝ)) :=
    (modSpecFun_measurable S t).mul ((measurable_devChar _).comp measurable_subtype_coe)
  have hib : ∀ z : ℂ, z.im = -(1 / 2) → ∀ ω : spectrum ℝ (rvdRC S),
      ‖devChar z (ω : ℝ)‖ ≤ Real.sqrt 2 := fun z hz ω =>
    devChar_norm_le_Icc (by rw [hz]; norm_num) (by rw [hz]) (rvdRC_spectrum_mem_Icc S ω)
  have him : (-(Complex.I / 2)).im = -(1 / 2) := by simp [Complex.neg_im, Complex.div_im, Complex.I_im]
  have hpb : ∀ ω, ‖modSpecFun S t ω * devChar (-(Complex.I / 2)) (ω : ℝ)‖ ≤ Real.sqrt 2 := fun ω => by
    rw [norm_mul]
    calc ‖modSpecFun S t ω‖ * ‖devChar (-(Complex.I / 2)) (ω : ℝ)‖
        ≤ 1 * Real.sqrt 2 :=
          mul_le_mul (modSpecFun_norm_le S t ω) (hib _ him ω) (norm_nonneg _) zero_le_one
      _ = Real.sqrt 2 := one_mul _
  rw [← borelFC_mul (rvdRC S) (rvdRC_isSelfAdjoint S)
        (modSpecFun_measurable S t) zero_le_one (modSpecFun_norm_le S t)
        ((measurable_devChar _).comp measurable_subtype_coe) (Real.sqrt_nonneg 2) (hib _ him)
        hpm (Real.sqrt_nonneg 2) hpb]
  refine borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) _ (Real.sqrt_nonneg 2) _ hpm
    (Real.sqrt_nonneg 2) hpb (funext fun ω => ?_)
  show devChar ((t : ℂ) - Complex.I / 2) (ω : ℝ)
    = modSpecFun S t ω * devChar (-(Complex.I / 2)) (ω : ℝ)
  rw [devChar, devChar, modSpecFun, ← modCharC_ofReal t, ← mul_assoc, ← modCharC_add,
    show (t : ℂ) + -(Complex.I / 2) = (t : ℂ) - Complex.I / 2 from by ring]

/-- **Spectral bridge for the real-axis device operator**: `⟪ξ, (Δ^{it}·√R) ξ⟫ = ∫ d_t dμ^R_ξ` (mirrors
    `rvdSpec_modUnitary`, via `inner_borelFC`). -/
theorem rvdSpec_deviceOpReal (S : StandardSubspace H) (ξ : H) (t : ℝ) :
    inner ℂ ξ (deviceOpReal S t ξ) = ∫ ω, devSpecReal S t ω ∂(rvdSpecMeasure S ξ) := by
  rw [deviceOpReal, inner_borelFC, bilinDiag_self, ProjectionValuedMeasure.diagInt, rvdSpecMeasure]

/-- **The device strip extension as an operator expectation on the real axis**:
    `D_ξ(t) = ⟪ξ, (Δ^{it}·√R) ξ⟫` — the matrix element of the bounded real-axis device operator, the device's
    `√R`-regularized analogue of the modular bridge `rvdSpec_modUnitary` (`⟪ξ, Δ^{it} ξ⟫ = ∫ u_t dμ`). -/
theorem devCorrExt_ofReal_inner (S : StandardSubspace H) (ξ : H) (t : ℝ) :
    devCorrExt S ξ (t : ℂ) = inner ℂ ξ (deviceOpReal S t ξ) := by
  rw [rvdSpec_deviceOpReal, devCorrExt]
  rfl

open QIQTH.StandardSubspaceModular in
/-- **Derivative-norm bound of the device character on a slab** (the `‖∂_z d_z(ω)‖ ≤ C` companion to
    `devChar_slope_norm_le`): on `{−β₁ < Im w < −β₀}`, `‖i·log((2−ω)/ω)·d_w(ω)‖ ≤ C` uniformly in `ω`
    (`devChar_deriv_norm_le` for `ω ∈ (0,2)`; the coefficient vanishes for `ω ∈ {0,2}`).  This bounds the
    candidate Fréchet derivative `∂_z d` at every slab point — used as the second half of the
    dominating constant `4C²` in the strong-holomorphy dominated-convergence step. -/
theorem devCharDeriv_norm_le_slab (S : StandardSubspace H) (ω : spectrum ℝ (rvdRC S))
    {β₀ β₁ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : β₁ < 1 / 2) {w : ℂ}
    (hw : w ∈ Complex.im ⁻¹' Set.Ioo (-β₁) (-β₀)) :
    ‖Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
        / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) * devChar w (ω : spectrum ℝ (rvdRC S)).val‖
      ≤ Real.sqrt 2 * (2 / β₀ + Real.log 2) + Real.sqrt 2 * (2 / (1 / 2 - β₁) + Real.log 2) := by
  rw [Set.mem_preimage, Set.mem_Ioo] at hw
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hω : (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2
  · exact devChar_deriv_norm_le hβ₀ hβ₁ (le_of_lt hw.2) (le_of_lt hw.1) hω
  · have hr02 : (ω : spectrum ℝ (rvdRC S)).val = 0 ∨ (ω : spectrum ℝ (rvdRC S)).val = 2 := by
      obtain ⟨h0', h2'⟩ := Set.mem_Icc.mp (rvdRC_spectrum_mem_Icc S ω)
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hω
      exact hω.imp (fun hle => le_antisymm hle h0') (fun hge => le_antisymm h2' hge)
    have hzero : |Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
        / (ω : spectrum ℝ (rvdRC S)).val)| * ‖devChar w (ω : spectrum ℝ (rvdRC S)).val‖ = 0 := by
      rcases hr02 with h | h <;> rw [h] <;> simp [devChar, Real.sqrt_zero]
    rw [hzero]
    have hβ₁' : 0 < 1 / 2 - β₁ := by linarith
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, hlog2, le_of_lt (div_pos (by norm_num : (0:ℝ) < 2) hβ₀),
      le_of_lt (div_pos (by norm_num : (0:ℝ) < 2) hβ₁')]

open QIQTH.StandardSubspaceModular in
/-- **Uniform slope (Lipschitz) bound of the device character on a slab** (piece 2 of the strong-holomorphy
    dominated-convergence argument): on the open slab `s = {−β₁ < Im z < −β₀} ⊂ (−1/2,0)`,
    `‖d_z(ω) − d_{z₀}(ω)‖ ≤ C·‖z − z₀‖` with `C = √2(2/β₀+log2) + √2(2/(1/2−β₁)+log2)` the
    `devChar_deriv_norm_le` constant — UNIFORM in the spectral point `ω`.  Via the complex mean-value
    inequality `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` (`hasDerivAt_devChar_Icc` on the convex
    slab + the `devChar_deriv_norm_le` derivative bound, with `ω ∈ {0,2}` giving `d_z` `z`-constant ⇒ derivative
    `0 ≤ C`).  Hence `‖Δ_z(ω)‖ ≤ C` uniformly: the dominating constant for the dominated-convergence step. -/
theorem devChar_slope_norm_le (S : StandardSubspace H) (ω : spectrum ℝ (rvdRC S))
    {β₀ β₁ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : β₁ < 1 / 2)
    {z z₀ : ℂ} (hz : z ∈ Complex.im ⁻¹' Set.Ioo (-β₁) (-β₀))
    (hz₀ : z₀ ∈ Complex.im ⁻¹' Set.Ioo (-β₁) (-β₀)) :
    ‖devChar z (ω : spectrum ℝ (rvdRC S)).val - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val‖
      ≤ (Real.sqrt 2 * (2 / β₀ + Real.log 2) + Real.sqrt 2 * (2 / (1 / 2 - β₁) + Real.log 2))
        * ‖z - z₀‖ := by
  set s : Set ℂ := Complex.im ⁻¹' Set.Ioo (-β₁) (-β₀) with hs
  set C : ℝ := Real.sqrt 2 * (2 / β₀ + Real.log 2) + Real.sqrt 2 * (2 / (1 / 2 - β₁) + Real.log 2)
    with hCdef
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hβ₁' : 0 < 1 / 2 - β₁ := by linarith
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ 2 / β₀ := le_of_lt (div_pos (by norm_num) hβ₀)
    have h2 : (0 : ℝ) ≤ 2 / (1 / 2 - β₁) := le_of_lt (div_pos (by norm_num) hβ₁')
    nlinarith [Real.sqrt_nonneg 2, hlog2, h1, h2]
  have hconv : Convex ℝ s := by
    have heq : s = {z : ℂ | z.im < -β₀} ∩ {z : ℂ | -β₁ < z.im} := by
      ext w
      rw [hs, Set.mem_preimage, Set.mem_Ioo, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_setOf_eq]
      tauto
    rw [heq]; exact Convex.inter (convex_halfSpace_im_lt (-β₀)) (convex_halfSpace_im_gt (-β₁))
  have hbound : ∀ w ∈ s, ‖Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
        / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) * devChar w (ω : spectrum ℝ (rvdRC S)).val‖ ≤ C := by
    intro w hw
    rw [hs, Set.mem_preimage, Set.mem_Ioo] at hw
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hω : (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2
    · rw [hCdef]; exact devChar_deriv_norm_le hβ₀ hβ₁ (le_of_lt hw.2) (le_of_lt hw.1) hω
    · have hr02 : (ω : spectrum ℝ (rvdRC S)).val = 0 ∨ (ω : spectrum ℝ (rvdRC S)).val = 2 := by
        obtain ⟨h0', h2'⟩ := Set.mem_Icc.mp (rvdRC_spectrum_mem_Icc S ω)
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hω
        exact hω.imp (fun hle => le_antisymm hle h0') (fun hge => le_antisymm h2' hge)
      have hzero : |Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
          / (ω : spectrum ℝ (rvdRC S)).val)| * ‖devChar w (ω : spectrum ℝ (rvdRC S)).val‖ = 0 := by
        rcases hr02 with h | h <;> rw [h] <;> simp [devChar, Real.sqrt_zero]
      rw [hzero]; exact hC0
  exact hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w _ => (hasDerivAt_devChar_Icc (rvdRC_spectrum_mem_Icc S ω) w).hasDerivWithinAt)
    hbound hz₀ hz

open QIQTH.StandardSubspaceModular in
/-- **Pointwise difference-quotient convergence of the device character** (piece 1 of the strong-holomorphy
    dominated-convergence argument): for each spectral point `ω`, the slope
    `(d_z(ω) − d_{z₀}(ω))/(z − z₀) → i·log((2−ω)/ω)·d_{z₀}(ω)` as `z → z₀` (`z ≠ z₀`).  Immediate from
    `hasDerivAt_devChar_Icc` via `hasDerivAt_iff_tendsto_slope` (`slope_def_field`).  Fed into
    `tendsto_integral_filter_of_dominated_convergence` to drive `∫‖Δ_z − ∂_z d‖² dμ^R_ζ → 0`, hence the
    Fréchet derivative of `z ↦ deviceOpC(z)ζ` (via `borelFC_sub` + `borelFC_apply_norm_sq`). -/
theorem tendsto_devChar_slope (S : StandardSubspace H) (z₀ : ℂ) (ω : spectrum ℝ (rvdRC S)) :
    Filter.Tendsto (fun z => (devChar z (ω : spectrum ℝ (rvdRC S)).val
        - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val) / (z - z₀)) (nhdsWithin z₀ {z₀}ᶜ)
      (nhds (Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
        / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) * devChar z₀ (ω : spectrum ℝ (rvdRC S)).val)) := by
  refine (hasDerivAt_iff_tendsto_slope.mp
    (hasDerivAt_devChar_Icc (rvdRC_spectrum_mem_Icc S ω) z₀)).congr'
    (Filter.Eventually.of_forall fun z => ?_)
  rw [slope_def_field]

open QIQTH.StandardSubspaceModular MeasureTheory Filter in
/-- **Strong-holomorphy dominated convergence** (piece 3 — the heart): the `L²` remainder of the device-vector
    difference quotient vanishes, `∫‖(d_z(ω)−d_{z₀}(ω))/(z−z₀) − ∂_z d_{z₀}(ω)‖² dμ^R_ζ → 0` as `z → z₀`
    (`z ≠ z₀`), for `z₀` in the slab.  Lebesgue dominated convergence
    (`tendsto_integral_filter_of_dominated_convergence`): the integrand `→ 0` pointwise (`tendsto_devChar_slope`,
    piece 1) and is dominated by the constant `4C²` (`devChar_slope_norm_le` + `devCharDeriv_norm_le_slab`,
    piece 2: `‖Δ_z(ω)‖ ≤ C`, `‖∂d(ω)‖ ≤ C`), integrable on the finite measure `μ^R_ζ`.  Combined with
    `borelFC_sub` + `borelFC_apply_norm_sq` (`‖slope − d‖² = ∫‖Δ_z − ∂d‖² dμ`), this gives the Fréchet
    derivative of `z ↦ deviceOpC(z)ζ`. -/
theorem tendsto_integral_devChar_remainder_sq (S : StandardSubspace H) (ζ : H)
    {β₀ β₁ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : β₁ < 1 / 2) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Complex.im ⁻¹' Set.Ioo (-β₁) (-β₀)) :
    Tendsto (fun z => ∫ ω, ‖(devChar z (ω : spectrum ℝ (rvdRC S)).val
        - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val) / (z - z₀)
        - Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
          / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) * devChar z₀ (ω : spectrum ℝ (rvdRC S)).val‖ ^ 2
        ∂(rvdSpecMeasure S ζ)) (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
  haveI : IsFiniteMeasure (rvdSpecMeasure S ζ) := by unfold rvdSpecMeasure; infer_instance
  set μ := rvdSpecMeasure S ζ
  set C : ℝ := Real.sqrt 2 * (2 / β₀ + Real.log 2) + Real.sqrt 2 * (2 / (1 / 2 - β₁) + Real.log 2)
    with hCdef
  set s : Set ℂ := Complex.im ⁻¹' Set.Ioo (-β₁) (-β₀) with hs
  set d : spectrum ℝ (rvdRC S) → ℂ := fun ω => Complex.I
      * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val) / (ω : spectrum ℝ (rvdRC S)).val) : ℂ)
      * devChar z₀ (ω : spectrum ℝ (rvdRC S)).val with hd
  set F : ℂ → spectrum ℝ (rvdRC S) → ℝ := fun z ω =>
    ‖(devChar z (ω : spectrum ℝ (rvdRC S)).val - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val)
        / (z - z₀) - d ω‖ ^ 2 with hF
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hβ₁' : 0 < 1 / 2 - β₁ := by linarith
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    nlinarith [Real.sqrt_nonneg 2, hlog2, le_of_lt (div_pos (by norm_num : (0:ℝ) < 2) hβ₀),
      le_of_lt (div_pos (by norm_num : (0:ℝ) < 2) hβ₁')]
  have hmeasL : Measurable fun ω : spectrum ℝ (rvdRC S) =>
      (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val) / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp
      ((measurable_const.sub measurable_subtype_coe).div measurable_subtype_coe))
  have hmeasd : Measurable d :=
    (measurable_const.mul hmeasL).mul ((measurable_devChar z₀).comp measurable_subtype_coe)
  have hFmeas : ∀ z : ℂ, AEStronglyMeasurable (F z) μ := fun z =>
    ((((((measurable_devChar z).comp measurable_subtype_coe).sub
      ((measurable_devChar z₀).comp measurable_subtype_coe)).div measurable_const).sub
      hmeasd).norm.pow_const 2).aestronglyMeasurable
  have hdbd : ∀ ω, ‖d ω‖ ≤ C := fun ω => devCharDeriv_norm_le_slab S ω hβ₀ hβ₁ hz₀
  have hsnhd : s ∈ nhds z₀ := (Complex.continuous_im.isOpen_preimage _ isOpen_Ioo).mem_nhds hz₀
  have hconv : Tendsto (fun z => ∫ ω, F z ω ∂μ) (nhdsWithin z₀ {z₀}ᶜ) (nhds (∫ _ω, (0:ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 4 * C ^ 2)
      (Eventually.of_forall hFmeas) ?_ (integrable_const _) ?_
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hsnhd, self_mem_nhdsWithin] with z hzs hzne
      refine Eventually.of_forall fun ω => ?_
      have hz0 : 0 < ‖z - z₀‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hzne
      have hslope : ‖(devChar z (ω : spectrum ℝ (rvdRC S)).val
          - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val) / (z - z₀)‖ ≤ C := by
        rw [norm_div, div_le_iff₀ hz0]
        exact devChar_slope_norm_le S ω hβ₀ hβ₁ hzs hz₀
      have hsd : ‖(devChar z (ω : spectrum ℝ (rvdRC S)).val
          - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val) / (z - z₀) - d ω‖ ≤ 2 * C :=
        (norm_sub_le _ _).trans (by linarith [add_le_add hslope (hdbd ω)])
      have hnorm : ‖F z ω‖ = ‖(devChar z (ω : spectrum ℝ (rvdRC S)).val
          - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val) / (z - z₀) - d ω‖ ^ 2 := by
        rw [hF]; exact Real.norm_of_nonneg (by positivity)
      rw [hnorm]
      calc ‖(devChar z (ω : spectrum ℝ (rvdRC S)).val
              - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val) / (z - z₀) - d ω‖ ^ 2
          ≤ (2 * C) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsd 2
        _ = 4 * C ^ 2 := by ring
    · refine Eventually.of_forall fun ω => ?_
      have h2 : Tendsto (fun z => (devChar z (ω : spectrum ℝ (rvdRC S)).val
          - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val) / (z - z₀) - d ω)
          (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
        have h1 := (tendsto_devChar_slope S z₀ ω).sub_const (d ω)
        simpa [hd] using h1
      simpa [hF] using h2.norm.pow 2
  simpa using hconv

open QIQTH.StandardSubspaceModular in
/-- **Device-operator difference as a single `borelFC`** (first step of the slope operator-algebra):
    `deviceOpC(z) − deviceOpC(z₀) = borelFC(d_z − d_{z₀})`.  Just `borelFC_sub` read backwards, using that
    `deviceOpC` is definitionally a `borelFC` with the `√2` bound. -/
theorem deviceOpC_sub (S : StandardSubspace H) {z z₀ : ℂ}
    (hz2 : z.im ≤ 0) (hz1 : -(1 / 2 : ℝ) ≤ z.im)
    (hz02 : z₀.im ≤ 0) (hz01 : -(1 / 2 : ℝ) ≤ z₀.im) :
    deviceOpC S z hz2 hz1 - deviceOpC S z₀ hz02 hz01
      = borelFC (rvdRC S) (rvdRC_isSelfAdjoint S)
        (((measurable_devChar z).comp measurable_subtype_coe).sub
          ((measurable_devChar z₀).comp measurable_subtype_coe))
        (add_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2))
        (fun ω => (norm_sub_le _ _).trans (add_le_add
          (devChar_norm_le_Icc hz2 hz1 (rvdRC_spectrum_mem_Icc S ω))
          (devChar_norm_le_Icc hz02 hz01 (rvdRC_spectrum_mem_Icc S ω)))) :=
  (borelFC_sub (rvdRC S) (rvdRC_isSelfAdjoint S)
    ((measurable_devChar z).comp measurable_subtype_coe)
    ((measurable_devChar z₀).comp measurable_subtype_coe)
    (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)
    (fun ω => devChar_norm_le_Icc hz2 hz1 (rvdRC_spectrum_mem_Icc S ω))
    (fun ω => devChar_norm_le_Icc hz02 hz01 (rvdRC_spectrum_mem_Icc S ω))).symm

open QIQTH.StandardSubspaceModular in
/-- **Candidate Fréchet derivative operator of the device** at an interior point: `∂_z d_{z₀}(R) =
    borelFC(ω ↦ i·log((2−ω)/ω)·d_{z₀}(ω))`, the spectral operator whose symbol is the `z`-derivative of the
    device character at `z₀`.  Bounded by the `devCharDeriv_norm_le_slab` constant `C(β₀,β₁)` (the operator is
    independent of the slab `(β₀,β₁) ∋ Im z₀`, by `borelFC_congr`).  Applied to `ζ` it is the Fréchet derivative
    of `deviceVecF S ζ` at `z₀` (`hasDerivAt_deviceVecF`). -/
noncomputable def deviceDerivOpC (S : StandardSubspace H) (z₀ : ℂ) {β₀ β₁ : ℝ}
    (hβ₀ : 0 < β₀) (hβ₁ : β₁ < 1 / 2) (hz₀ : z₀ ∈ Complex.im ⁻¹' Set.Ioo (-β₁) (-β₀)) : H →L[ℂ] H :=
  borelFC (rvdRC S) (rvdRC_isSelfAdjoint S)
    ((measurable_const.mul (Complex.measurable_ofReal.comp (Real.measurable_log.comp
      ((measurable_const.sub measurable_subtype_coe).div measurable_subtype_coe)))).mul
      ((measurable_devChar z₀).comp measurable_subtype_coe))
    (by
      have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hβ₁' : 0 < 1 / 2 - β₁ := by linarith
      nlinarith [Real.sqrt_nonneg 2, hlog2, le_of_lt (div_pos (by norm_num : (0:ℝ) < 2) hβ₀),
        le_of_lt (div_pos (by norm_num : (0:ℝ) < 2) hβ₁')])
    (fun ω => devCharDeriv_norm_le_slab S ω hβ₀ hβ₁ hz₀)

open QIQTH.StandardSubspaceModular MeasureTheory in
/-- **`L²` identity for the device-vector slope remainder** (the operator-algebra heart of piece 4):
    `‖(z−z₀)⁻¹·(deviceOpC(z)ζ − deviceOpC(z₀)ζ) − deviceDerivOpC(z₀)ζ‖² = ∫‖Δ_z(ω) − ∂d(ω)‖² dμ^R_ζ`, the
    integrand of `tendsto_integral_devChar_remainder_sq`.  The slope-minus-derivative vector is a single
    `borelFC` applied to `ζ` (`deviceOpC_sub` + `borelFC_smul` + `borelFC_sub`, pushed through the CLM
    `sub_apply`/`smul_apply`), so `borelFC_apply_norm_sq` turns its norm² into the spectral `L²` integral. -/
theorem deviceOpC_slope_normSq (S : StandardSubspace H) (ζ : H)
    {β₀ β₁ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : β₁ < 1 / 2) {z z₀ : ℂ}
    (hz2 : z.im ≤ 0) (hz1 : -(1 / 2 : ℝ) ≤ z.im)
    (hz02 : z₀.im ≤ 0) (hz01 : -(1 / 2 : ℝ) ≤ z₀.im)
    (hz₀ : z₀ ∈ Complex.im ⁻¹' Set.Ioo (-β₁) (-β₀)) :
    ‖(z - z₀)⁻¹ • (deviceOpC S z hz2 hz1 ζ - deviceOpC S z₀ hz02 hz01 ζ)
        - deviceDerivOpC S z₀ hβ₀ hβ₁ hz₀ ζ‖ ^ 2
      = ∫ ω, ‖(devChar z (ω : spectrum ℝ (rvdRC S)).val - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val)
          / (z - z₀) - Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
            / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) * devChar z₀ (ω : spectrum ℝ (rvdRC S)).val‖ ^ 2
          ∂(rvdSpecMeasure S ζ) := by
  rw [← ContinuousLinearMap.sub_apply, deviceOpC_sub, ← ContinuousLinearMap.smul_apply, ← borelFC_smul,
    ← ContinuousLinearMap.sub_apply, deviceDerivOpC, ← borelFC_sub, borelFC_apply_norm_sq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  refine congrArg (fun x => ‖x‖ ^ 2) ?_
  simp only [Function.comp_apply]
  ring

open QIQTH.StandardSubspaceModular MeasureTheory Filter in
/-- **Strong (Fréchet) holomorphy of the device vector** (piece 4 COMPLETE): `z ↦ deviceOpC(z)ζ` is
    complex-differentiable at every interior point `z₀` of the open half-strip, with derivative
    `deviceDerivOpC(z₀)ζ`.  The slope-minus-derivative norm `→ 0`: its square is the remainder integral
    (`deviceOpC_slope_normSq`) which `→ 0` (`tendsto_integral_devChar_remainder_sq`), so `‖slope − deriv‖ =
    √(remainder) → √0 = 0` (`Real.sqrt` continuity), hence `slope → deriv`
    (`tendsto_iff_norm_sub_tendsto_zero`).  This defeats the holomorphy wall WITHOUT Mathlib's missing
    weak⟹strong (Dunford): the H-valued derivative is obtained from a scalar dominated-convergence integral. -/
theorem hasDerivAt_deviceVecF (S : StandardSubspace H) (ζ : H)
    {β₀ β₁ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : β₁ < 1 / 2) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Complex.im ⁻¹' Set.Ioo (-β₁) (-β₀)) :
    HasDerivAt (deviceVecF S ζ) (deviceDerivOpC S z₀ hβ₀ hβ₁ hz₀ ζ) z₀ := by
  obtain ⟨hz0lo, hz0hi⟩ := (Set.mem_preimage.mp hz₀ : z₀.im ∈ Set.Ioo (-β₁) (-β₀))
  have hz02 : z₀.im ≤ 0 := le_of_lt (hz0hi.trans (by linarith))
  have hz01 : -(1 / 2 : ℝ) ≤ z₀.im := le_of_lt (lt_of_le_of_lt (by linarith) hz0lo)
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have hR := tendsto_integral_devChar_remainder_sq S ζ hβ₀ hβ₁ hz₀
  have hsqrt : Tendsto (fun z => Real.sqrt (∫ ω, ‖(devChar z (ω : spectrum ℝ (rvdRC S)).val
        - devChar z₀ (ω : spectrum ℝ (rvdRC S)).val) / (z - z₀)
        - Complex.I * (Real.log ((2 - (ω : spectrum ℝ (rvdRC S)).val)
          / (ω : spectrum ℝ (rvdRC S)).val) : ℂ) * devChar z₀ (ω : spectrum ℝ (rvdRC S)).val‖ ^ 2
        ∂(rvdSpecMeasure S ζ))) (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hR
    simpa using h
  have hsnhd : (Complex.im ⁻¹' Set.Ioo (-β₁) (-β₀)) ∈ nhds z₀ :=
    (Complex.continuous_im.isOpen_preimage _ isOpen_Ioo).mem_nhds hz₀
  refine hsqrt.congr' ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds hsnhd, self_mem_nhdsWithin] with z hzs _
  obtain ⟨hzlo, hzhi⟩ := (Set.mem_preimage.mp hzs : z.im ∈ Set.Ioo (-β₁) (-β₀))
  have hz2 : z.im ≤ 0 := le_of_lt (hzhi.trans (by linarith))
  have hz1 : -(1 / 2 : ℝ) ≤ z.im := le_of_lt (lt_of_le_of_lt (by linarith) hzlo)
  rw [slope_def_module, deviceVecF_eq_of_mem S ζ hz2 hz1, deviceVecF_eq_of_mem S ζ hz02 hz01,
    ← Real.sqrt_sq (norm_nonneg _), deviceOpC_slope_normSq S ζ hβ₀ hβ₁ hz2 hz1 hz02 hz01 hz₀]

/-- **The device vector is holomorphic on the open half-strip** (piece 4 ⇒ `DifferentiableOn`): immediate
    from `hasDerivAt_deviceVecF` at every interior point (choosing the slab `β₀ = −Im z₀/2`,
    `β₁ = (1/2 − Im z₀)/2` around `z₀`).  This is the strong-holomorphic half-strip input the g-function
    Phragmén–Lindelöf constancy consumes — now available for the device vector of EVERY standard subspace. -/
theorem differentiableOn_deviceVecF (S : StandardSubspace H) (ζ : H) :
    DifferentiableOn ℂ (deviceVecF S ζ) (Complex.im ⁻¹' Set.Ioo (-(1 / 2) : ℝ) 0) := by
  intro z₀ hz₀
  obtain ⟨hlo, hhi⟩ := (Set.mem_preimage.mp hz₀ : z₀.im ∈ Set.Ioo (-(1 / 2) : ℝ) 0)
  refine (hasDerivAt_deviceVecF S ζ (β₀ := -z₀.im / 2) (β₁ := (1 / 2 - z₀.im) / 2)
    (by linarith) (by linarith) ?_).differentiableAt.differentiableWithinAt
  rw [Set.mem_preimage, Set.mem_Ioo]
  constructor <;> linarith

open QIQTH.StandardSubspaceModular in
/-- **Real-axis value of the device vector**: `deviceVecF(t) = Δ^{it}·√R ζ` (the top-edge value of the
    g-function).  Via `deviceVecF_eq_of_mem` (the strip contains the real axis), `deviceOpC_ofReal`
    (`d_{(t:ℂ)} = d_t`), and `deviceOpReal_eq` (`d_t = Δ^{it}·√R`).  With `ξ = √R ζ`, `J·deviceVecF(t) =
    JΔ^{it}ξ = Δ^{it}(Jξ)` is the second slot of the g-function on its real edge `g(t) = ⟪V_t η, Δ^{it}Jξ⟫`. -/
theorem deviceVecF_real_eq (S : StandardSubspace H) (ζ : H) (t : ℝ) :
    deviceVecF S ζ (t : ℂ) = modUnitary S t (rvdSqrtR S ζ) := by
  rw [deviceVecF_eq_of_mem S ζ (by simp) (by norm_num [Complex.ofReal_im]), deviceOpC_ofReal,
    deviceOpReal_eq, ContinuousLinearMap.mul_apply]

open QIQTH.StandardSubspaceModular in
/-- **The device-vector RvD g-function is HOLOMORPHIC on the open half-strip** (piece 2 of the endgame):
    `g(z) = ⟪J·d_z(R)ζ, V_z η⟫ = modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z)` is
    complex-differentiable on `{−1/2 < Im z < 0}`.  It is the continuous ℂ-bilinear form `modConjBilin`
    (`= ⟪J·,·⟫`, holomorphic by the J-cancellation) applied to the two HOLOMORPHIC curves: the device vector
    `deviceVecF` (`differentiableOn_deviceVecF`, the strong-holomorphy result) and the entire V-orbit
    `gaussSmearC` (`differentiable_gaussSmearC`).  Bilinear chain rule (`DifferentiableOn.clm_apply`).  This is
    the holomorphic strip function the Phragmén–Lindelöf constancy `g(t) = g(0) ⟹ GConstancy` consumes. -/
theorem differentiableOn_gFunction (S : StandardSubspace H) (ζ : H)
    {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) :
    DifferentiableOn ℂ (fun z => modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z))
      (Complex.im ⁻¹' Set.Ioo (-(1 / 2) : ℝ) 0) :=
  DifferentiableOn.clm_apply
    ((modConjBilin S).differentiable.comp_differentiableOn (differentiableOn_deviceVecF S ζ))
    (differentiable_gaussSmearC hn η hcont hbd).differentiableOn

open QIQTH.StandardSubspaceModular in
/-- **Device vector at the origin**: `deviceVecF(0) = √R ζ` (`= ξ`, the comparison point).  From
    `deviceVecF_real_eq` at `t = 0` (`Δ^{i·0} = 1`, `modUnitary_zero`). -/
theorem deviceVecF_zero (S : StandardSubspace H) (ζ : H) :
    deviceVecF S ζ 0 = rvdSqrtR S ζ := by
  have h := deviceVecF_real_eq S ζ 0
  rw [Complex.ofReal_zero] at h
  rw [h, modUnitary_zero, ContinuousLinearMap.one_apply]

open QIQTH.StandardSubspaceModular in
/-- **g-function value at the origin** `g(0) = ⟪J ξ, η_n⟫` (`ξ = √R ζ`, `η_n = gaussSmear`): the comparison
    point of the Phragmén–Lindelöf constancy.  With `g` constant this equals `g(t)`, the top-edge matrix
    element — the heart of RvD Theorem 3.8.  Via `deviceVecF_zero` + `gaussSmearC_zero`. -/
theorem gFunction_zero (S : StandardSubspace H) (ζ : H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (η : H) :
    modConjBilin S (deviceVecF S ζ 0) (gaussSmearC V n η 0)
      = inner ℂ (modConj S (rvdSqrtR S ζ)) (gaussSmear V n η) := by
  rw [deviceVecF_zero, gaussSmearC_zero, modConjBilin_apply]

open QIQTH.StandardSubspaceModular in
/-- **g-function value on the real axis (top edge)** `g(t) = ⟪Δ^{it}(J ξ), V_t η_n⟫` (`ξ = √R ζ`): via
    `deviceVecF_real_eq` (`d_t ζ = Δ^{it}√R ζ`), `gaussSmearC_ofReal` (`h(t) = V_t η_n`), and
    `modConj_commute_modUnitary` (`JΔ^{it} = Δ^{it}J`).  Its conjugate is the GConstancy LHS
    `⟪V_t η_n, Δ^{it}Jξ⟫`; reality (RvD top edge) makes `g(t)` equal to it. -/
theorem gFunction_real_eq (S : StandardSubspace H) (ζ : H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n)
    (η : H) (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η) (t : ℝ) :
    modConjBilin S (deviceVecF S ζ (t : ℂ)) (gaussSmearC V n η (t : ℂ))
      = inner ℂ (modUnitary S t (modConj S (rvdSqrtR S ζ))) (V t (gaussSmear V n η)) := by
  rw [deviceVecF_real_eq, gaussSmearC_ofReal hn η hcont hbd hgrp t, modConjBilin_apply,
    modConj_commute_modUnitary]

open QIQTH.StandardSubspaceModular in
/-- **Top-edge reality of the g-function** (RvD Theorem 3.8, the real-axis edge): for `ξ = √R ζ ∈ 𝒦` and the
    V-orbit staying in `𝒦`, `g(t) = ⟪Δ^{it}(Jξ), V_t η_n⟫` is REAL.  `Δ^{it}(Jξ) = J(Δ^{it}ξ)`
    (`modConj_commute_modUnitary`) with `Δ^{it}ξ ∈ 𝒦` (`modUnitary_mapsTo_K`), so `J(Δ^{it}ξ) ⊥ i𝒦`
    (`projIK_modConj_eq_zero_of_mem_K`, `J𝒦 = (i𝒦)^⊥`); pairing it against the `𝒦`-vector `V_t η_n` is real
    (`inner_real_of_mem_K_perp_IK`, RvD Prop 2.3) — and `g(t)` is the conjugate of that.  Geometric, no analysis;
    the real-axis edge of the holomorphic strip g-function feeding the Phragmén–Lindelöf constancy. -/
theorem gFunction_top_edge_real (S : StandardSubspace H) (ζ : H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ}
    (hn : 0 < n) (η : H) (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η) (hξ : projK S (rvdSqrtR S ζ) = rvdSqrtR S ζ) (t : ℝ)
    (hVη : projK S (V t (gaussSmear V n η)) = V t (gaussSmear V n η)) :
    (modConjBilin S (deviceVecF S ζ (t : ℂ)) (gaussSmearC V n η (t : ℂ))).im = 0 := by
  rw [gFunction_real_eq S ζ hn η hcont hbd hgrp t, ← modConj_commute_modUnitary, ← inner_conj_symm,
    Complex.conj_im, neg_eq_zero]
  exact inner_real_of_mem_K_perp_IK S hVη
    (projIK_modConj_eq_zero_of_mem_K S
      ((mem_K_iff_projK S _).mp (modUnitary_mapsTo_K S t _ ((mem_K_iff_projK S _).mpr hξ))))

open QIQTH.StandardSubspaceModular in
/-- **Bottom-edge value of the device vector**: `deviceVecF(t − i/2) = Δ^{it}·deviceOpC(−i/2) ζ`, the modular
    flow translating the FIXED bottom vector `deviceOpC(−i/2) ζ` (`= √(2−R) ζ` off the spectral endpoints
    `{0,2}`).  Via `deviceVecF_eq_of_mem` (the closed half-strip contains the mid-line `Im z = −1/2`) and
    `deviceOpC_bottomEdge_eq`.  This is the second-slot device vector on the bottom edge of the g-function,
    whose reality is the KMS input (`HalfStripReal`) feeding the Phragmén–Lindelöf constancy. -/
theorem deviceVecF_bottom_eq (S : StandardSubspace H) (ζ : H) (t : ℝ) :
    deviceVecF S ζ ((t : ℂ) - Complex.I / 2)
      = modUnitary S t (deviceOpC S (-(Complex.I / 2))
          (by simp [Complex.neg_im, Complex.div_im, Complex.I_im])
          (by rw [show (-(Complex.I / 2)).im = -(1 / 2) from by
                simp [Complex.neg_im, Complex.div_im, Complex.I_im]]) ζ) := by
  rw [deviceVecF_eq_of_mem S ζ
      (by simp [Complex.sub_im, Complex.div_im, Complex.I_im])
      (by rw [show ((t : ℂ) - Complex.I / 2).im = -(1 / 2) from by
            simp [Complex.sub_im, Complex.div_im, Complex.I_im]]),
    deviceOpC_bottomEdge_eq, ContinuousLinearMap.mul_apply]

open QIQTH.StandardSubspaceModular in
/-- **Diagonal operator identification of the device strip extension** (general `z` in the half-strip):
    `D_ξ(z) = ⟪ξ, deviceOpC(z) ξ⟫`.  The scalar integral `∫ d_z dμ^R_ξ` IS the diagonal expectation of the
    device operator `d_z(R)` (via `inner_borelFC` + `bilinDiag_self` + `diagInt`).  This connects the proven
    scalar holomorphy (`hasDerivAt_devCorrExt`) to the device OPERATOR — the bridge the polarization route to
    the off-diagonal `⟪w, deviceOpC(z) ζ⟫` (and thence the strong/Fréchet holomorphy of `z ↦ deviceOpC(z)ζ`)
    consumes. -/
theorem devCorrExt_inner (S : StandardSubspace H) (ξ : H) (z : ℂ) (hz2 : z.im ≤ 0)
    (hz1 : -(1 / 2 : ℝ) ≤ z.im) :
    devCorrExt S ξ z = inner ℂ ξ (deviceOpC S z hz2 hz1 ξ) := by
  rw [deviceOpC, inner_borelFC, bilinDiag_self, ProjectionValuedMeasure.diagInt, devCorrExt,
    rvdSpecMeasure]
  rfl

/-- **The device strip extension is differentiable on the open half-strip** (no regular window): immediate
    from `hasDerivAt_devCorrExt` at every interior point.  The differentiability half of the
    bounded-holomorphic half-strip extension that strip-uniqueness consumes, for ANY standard subspace. -/
theorem differentiableOn_devCorrExt (S : StandardSubspace H) (ξ : H) :
    DifferentiableOn ℂ (devCorrExt S ξ) (Complex.im ⁻¹' Set.Ioo (-(1 / 2) : ℝ) 0) := fun z hz =>
  (hasDerivAt_devCorrExt S ξ (by simpa using hz)).differentiableAt.differentiableWithinAt

open MeasureTheory in
/-- **The device strip extension is bounded-holomorphic on the CLOSED half-strip** (no regular window):
    holomorphic on the open half-strip (`differentiableOn_devCorrExt`) and continuous up to the closed
    half-strip `{−1/2 ≤ Im z ≤ 0}`.  Continuity at the edges is dominated convergence under the spectral
    integral: `‖d_z(ω)‖ ≤ √2` uniformly on the closed half-strip (`devChar_norm_le_Icc` +
    `rvdRC_spectrum_mem_Icc`), and `z ↦ d_z(ω)` is continuous (entire, `differentiable_devChar`).  This is the
    exact `DiffContOnCl` input that the half-strip one-edge uniqueness (`eqOn_of_im_zero_edge_halfStrip`)
    consumes — now available for EVERY standard subspace (the device's regular-window-free advantage). -/
theorem diffContOnCl_devCorrExt (S : StandardSubspace H) (ξ : H) :
    DiffContOnCl ℂ (devCorrExt S ξ) (Complex.im ⁻¹' Set.Ioo (-(1 / 2) : ℝ) 0) := by
  haveI : IsFiniteMeasure (rvdSpecMeasure S ξ) := by unfold rvdSpecMeasure; infer_instance
  refine ⟨differentiableOn_devCorrExt S ξ, ?_⟩
  rw [Complex.closure_preimage_im, closure_Ioo (by norm_num : (-(1 / 2) : ℝ) ≠ 0)]
  have hmeasC : ∀ z : ℂ, AEStronglyMeasurable
      (fun ω : spectrum ℝ (rvdRC S) => devChar z (ω : spectrum ℝ (rvdRC S)).val)
      (rvdSpecMeasure S ξ) :=
    fun z => ((measurable_devChar z).comp measurable_subtype_coe).aestronglyMeasurable
  exact continuousOn_of_dominated (fun x _ => hmeasC x)
    (fun x hx => Filter.Eventually.of_forall (fun ω =>
      devChar_norm_le_Icc hx.2 hx.1 (rvdRC_spectrum_mem_Icc S ω)))
    (integrable_const (Real.sqrt 2))
    (Filter.Eventually.of_forall (fun ω => (differentiable_devChar _).continuous.continuousOn))

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

open MeasureTheory in
/-- **★ Differentiation of the modular-flow matrix element:** in the regular regime (`σ(R) ⊆ [a,2−a]`),
    `d/dt|₀ ⟨ξ, U_t ξ⟩ = i·∫ entropyDensity dμ^R_ξ`.  Differentiation under the spectral integral
    (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`): the `t`-derivative `∂_t u_t = i·g·u_t` is bounded by
    the constant `log((2−a)/a)` (`g` bounded, `|u_t|=1`), the dominating function on the finite spectral
    measure.  This is the operator-theoretic Stone-generator step, done at the scalar-integral level. -/
theorem hasDerivAt_inner_modUnitary (S : StandardSubspace H) (ξ : H) {a : ℝ} (ha : 0 < a) (ha2 : a < 2)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : ℝ) ∧ (ω : ℝ) ≤ 2 - a) :
    HasDerivAt (fun t => inner ℂ ξ (modUnitary S t ξ))
      (Complex.I * ∫ ω, (entropyDensity (ω : ℝ) : ℂ) ∂(rvdSpecMeasure S ξ)) 0 := by
  haveI : IsFiniteMeasure (rvdSpecMeasure S ξ) := by unfold rvdSpecMeasure; infer_instance
  simp only [rvdSpec_modUnitary]
  have hpos : ∀ ω : spectrum ℝ (rvdRC S), (ω : ℝ) ∈ Set.Ioo (0 : ℝ) 2 := fun ω =>
    ⟨lt_of_lt_of_le ha (hspec ω).1, lt_of_le_of_lt (hspec ω).2 (by linarith)⟩
  have hconv : (Complex.I * ∫ ω, (entropyDensity ((ω : spectrum ℝ (rvdRC S)) : ℝ) : ℂ)
        ∂(rvdSpecMeasure S ξ))
      = ∫ ω, Complex.I * (entropyDensity (ω : ℝ) : ℂ) * modSpecFun S 0 ω ∂(rvdSpecMeasure S ξ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    show Complex.I * (entropyDensity (ω : ℝ) : ℂ)
      = Complex.I * (entropyDensity (ω : ℝ) : ℂ) * modSpecFun S 0 ω
    rw [show modSpecFun S 0 ω = 1 from modChar_zero (ω : ℝ), mul_one]
  rw [hconv]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (F := fun t ω => modSpecFun S t ω)
    (F' := fun t ω => Complex.I * (entropyDensity (ω : ℝ) : ℂ) * modSpecFun S t ω)
    (bound := fun _ => Real.log ((2 - a) / a)) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall (fun t => (modSpecFun_measurable S t).aestronglyMeasurable))
    ((integrable_const (1 : ℝ)).mono' (modSpecFun_measurable S 0).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => modSpecFun_norm_le S 0 ω)))
    (((measurable_const.mul (Complex.measurable_ofReal.comp entropyDensity_measurable)).mul
        (modSpecFun_measurable S 0)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ω t _ => ?_))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun ω t _ => hasDerivAt_modChar t (hpos ω)))).2
  show ‖Complex.I * (entropyDensity (ω : ℝ) : ℂ) * modSpecFun S t ω‖ ≤ Real.log ((2 - a) / a)
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, one_mul,
      show ‖modSpecFun S t ω‖ = 1 from modChar_norm t (ω : ℝ), mul_one]
  exact entropyDensity_abs_le ha (hspec ω).1 (hspec ω).2

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
