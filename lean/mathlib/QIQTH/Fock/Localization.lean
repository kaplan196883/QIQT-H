/-
  K-localization, Phase 0 — convention lock + Minkowski geometry (per K_LOCALIZATION_PLAN.md, GPT consult #6).

  The concrete spacetime localization map `K` (the last physics input for the prize) restricts the spacetime
  Fourier transform to the mass shell.  Phase 0 fixes the 1+1D Minkowski conventions and proves the geometry
  lemmas that make boost-equivariance a clean change of variables:

    * `minkowskiDot p x = p₀x₀ − p₁x₁`  (the Minkowski pairing — NOT Euclidean; soundness trap #2),
    * `massShell m θ = (m cosh θ, m sinh θ)`  (the positive mass shell in rapidity coords),
    * `lorentzBoost a`  (the proper rapidity-`a` boost),

  with the load-bearing identities `massShell_boost` (the boost shifts rapidity, `Λa(p_m θ)=p_m(θ+a)`) and
  `minkowskiDot_boost` (the pairing is boost-invariant).  Axiom-free.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

namespace QIQTH.Fock.Localization

open Real MeasureTheory

/-- 1+1D Minkowski spacetime (coordinates `(t, x) = (z 0, z 1)`). -/
abbrev V : Type := Fin 2 → ℝ

/-- **The Minkowski pairing** `η(p, x) = p₀x₀ − p₁x₁` (signature `(+,−)`). -/
def minkowskiDot (p x : V) : ℝ := p 0 * x 0 - p 1 * x 1

/-- The Minkowski square `η(z, z) = t² − x²` (positive ⇔ timelike/lightlike). -/
def minkowskiSq (z : V) : ℝ := minkowskiDot z z

/-- **The positive mass shell** in rapidity coordinates: `p_m(θ) = (m cosh θ, m sinh θ)`. -/
noncomputable def massShell (m θ : ℝ) : V := ![m * Real.cosh θ, m * Real.sinh θ]

/-- **The proper rapidity-`a` Lorentz boost** on `V`. -/
noncomputable def lorentzBoost (a : ℝ) (z : V) : V :=
  ![Real.cosh a * z 0 + Real.sinh a * z 1, Real.sinh a * z 0 + Real.cosh a * z 1]

@[simp] theorem massShell_zero (m θ : ℝ) : massShell m θ 0 = m * Real.cosh θ := rfl
@[simp] theorem massShell_one (m θ : ℝ) : massShell m θ 1 = m * Real.sinh θ := rfl
@[simp] theorem lorentzBoost_zero (a : ℝ) (z : V) :
    lorentzBoost a z 0 = Real.cosh a * z 0 + Real.sinh a * z 1 := rfl
@[simp] theorem lorentzBoost_one (a : ℝ) (z : V) :
    lorentzBoost a z 1 = Real.sinh a * z 0 + Real.cosh a * z 1 := rfl

/-- **The boost shifts rapidity on the mass shell**: `Λ_a (p_m θ) = p_m (θ + a)`.  This is the geometric
    heart of boost-equivariance (the boost acts as translation `θ ↦ θ + a` on the shell). -/
theorem massShell_boost (m a θ : ℝ) :
    lorentzBoost a (massShell m θ) = massShell m (θ + a) := by
  funext i
  fin_cases i
  · show lorentzBoost a (massShell m θ) 0 = massShell m (θ + a) 0
    rw [lorentzBoost_zero, massShell_zero, massShell_one, massShell_zero, Real.cosh_add]; ring
  · show lorentzBoost a (massShell m θ) 1 = massShell m (θ + a) 1
    rw [lorentzBoost_one, massShell_zero, massShell_one, massShell_one, Real.sinh_add]; ring

/-- **The Minkowski pairing is boost-invariant**: `η(Λ_a p, Λ_a x) = η(p, x)`. -/
theorem minkowskiDot_boost (a : ℝ) (p x : V) :
    minkowskiDot (lorentzBoost a p) (lorentzBoost a x) = minkowskiDot p x := by
  simp only [minkowskiDot, lorentzBoost_zero, lorentzBoost_one]
  linear_combination (p 0 * x 0 - p 1 * x 1) * Real.cosh_sq_sub_sinh_sq a

/-- The Minkowski square is boost-invariant. -/
theorem minkowskiSq_boost (a : ℝ) (z : V) : minkowskiSq (lorentzBoost a z) = minkowskiSq z :=
  minkowskiDot_boost a z z

/-- The mass shell lies on the positive-mass hyperbola `t² − x² = m²`. -/
theorem minkowskiSq_massShell (m θ : ℝ) : minkowskiSq (massShell m θ) = m ^ 2 := by
  simp only [minkowskiSq, minkowskiDot, massShell_zero, massShell_one]
  nlinarith [Real.cosh_sq_sub_sinh_sq θ]

/-! ### The boost as a unimodular linear map (the Jacobian for the Fourier change of variables) -/

/-- The boost matrix `[[cosh a, sinh a], [sinh a, cosh a]]`. -/
noncomputable def lorentzBoostMat (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh a, Real.sinh a; Real.sinh a, Real.cosh a]

/-- The boost packaged as an `ℝ`-linear endomorphism of `V` (via its standard matrix).  Typed on
    `Fin 2 → ℝ` (rather than the abbrev `V`) so the `volume` Haar instance synthesizes for the measure
    change-of-variables. -/
noncomputable def lorentzBoostₗ (a : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' (lorentzBoostMat a)

/-- A 2×2 `mulVec` expansion (local helper). -/
private theorem mulVec_two (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (i : Fin 2) :
    Matrix.mulVec M v i = M i 0 * v 0 + M i 1 * v 1 := by
  rw [Matrix.mulVec_eq_sum]
  fin_cases i
  · simp [Fin.sum_univ_two, Matrix.transpose_apply]; ring
  · simp [Fin.sum_univ_two, Matrix.transpose_apply]; ring

@[simp] theorem lorentzBoostₗ_apply (a : ℝ) (z : V) : lorentzBoostₗ a z = lorentzBoost a z := by
  funext i
  rw [lorentzBoostₗ, Matrix.toLin'_apply, mulVec_two, lorentzBoostMat]
  fin_cases i <;>
    simp [lorentzBoost_zero, lorentzBoost_one]

/-- **The boost is unimodular**: `det Λ_a = cosh²a − sinh²a = 1` — the change of variables `y = Λ_a x`
    in the spacetime Fourier integral has unit Jacobian (no measure correction). -/
theorem det_lorentzBoost (a : ℝ) : LinearMap.det (lorentzBoostₗ a) = 1 := by
  rw [lorentzBoostₗ, LinearMap.det_toLin', lorentzBoostMat, Matrix.det_fin_two_of]
  linear_combination Real.cosh_sq_sub_sinh_sq a

/-- **The boost preserves the Lebesgue volume** (unit Jacobian) — the measure-preservation needed for the
    Fourier change of variables in boost-equivariance.  (Stated on `Fin 2 → ℝ` explicitly so the `volume`
    Haar instance synthesizes; `V` is the same type but the reducible abbrev blocks instance search.) -/
theorem measurePreserving_lorentzBoost (a : ℝ) :
    MeasureTheory.MeasurePreserving (lorentzBoost a)
      (volume : MeasureTheory.Measure (Fin 2 → ℝ)) volume := by
  have hdet : LinearMap.det (lorentzBoostₗ a) ≠ 0 := by rw [det_lorentzBoost]; norm_num
  have hmp : MeasureTheory.MeasurePreserving (lorentzBoostₗ a)
      (volume : MeasureTheory.Measure (Fin 2 → ℝ)) volume := by
    refine ⟨(lorentzBoostₗ a).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, det_lorentzBoost]
    simp
  have hfun : (lorentzBoost a) = ⇑(lorentzBoostₗ a) := by funext z; rw [lorentzBoostₗ_apply]
  rw [hfun]; exact hmp

/-- `Λ_{-a}` is a left inverse of `Λ_a`. -/
theorem lorentzBoost_neg_left (a : ℝ) (z : V) : lorentzBoost (-a) (lorentzBoost a z) = z := by
  funext i
  fin_cases i
  · show lorentzBoost (-a) (lorentzBoost a z) 0 = z 0
    simp only [lorentzBoost_zero, lorentzBoost_one, Real.cosh_neg, Real.sinh_neg]
    linear_combination (z 0) * Real.cosh_sq_sub_sinh_sq a
  · show lorentzBoost (-a) (lorentzBoost a z) 1 = z 1
    simp only [lorentzBoost_zero, lorentzBoost_one, Real.cosh_neg, Real.sinh_neg]
    linear_combination (z 1) * Real.cosh_sq_sub_sinh_sq a

/-- `Λ_{-a}` is a right inverse of `Λ_a` (apply the previous lemma at `-a`). -/
theorem lorentzBoost_neg_right (a : ℝ) (z : V) : lorentzBoost a (lorentzBoost (-a) z) = z := by
  have := lorentzBoost_neg_left (-a) z
  rwa [neg_neg] at this

/-- The boost as a (continuous) linear equivalence of `Fin 2 → ℝ` — gives a measurable embedding. -/
noncomputable def lorentzBoostLE (a : ℝ) : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearEquiv.ofLinear (lorentzBoostₗ a) (lorentzBoostₗ (-a))
    (by ext z; simp only [LinearMap.comp_apply, lorentzBoostₗ_apply, LinearMap.id_apply,
          lorentzBoost_neg_right])
    (by ext z; simp only [LinearMap.comp_apply, lorentzBoostₗ_apply, LinearMap.id_apply,
          lorentzBoost_neg_left])

/-- The boost is a measurable embedding (it is a continuous linear equivalence). -/
theorem measurableEmbedding_lorentzBoost (a : ℝ) :
    MeasurableEmbedding (lorentzBoost a) := by
  have hmem := ((lorentzBoostLE a).toContinuousLinearEquiv).toHomeomorph.measurableEmbedding
  have h : ⇑((lorentzBoostLE a).toContinuousLinearEquiv.toHomeomorph) = lorentzBoost a := by
    funext z
    have hz : ((lorentzBoostLE a).toContinuousLinearEquiv.toHomeomorph) z = lorentzBoostₗ a z := rfl
    rw [hz, lorentzBoostₗ_apply]
  rwa [h] at hmem

/-! ### The Minkowski-Fourier wrapper and boost-equivariance (Phase 1c) -/

/-- **The Minkowski-space Fourier transform** `f̂_M(p) = ∫ e^{−i η(p,x)} f(x) dx`, with the Minkowski
    pairing in the exponent (signature `(+,−)`; soundness trap #2). -/
noncomputable def minkowskiFourier (f : V → ℂ) (p : V) : ℂ :=
  ∫ x, Complex.exp (-Complex.I * ((minkowskiDot p x : ℝ) : ℂ)) * f x

/-- **The boost action on test functions** `(β_a f)(x) = f(Λ_a x)`. -/
noncomputable def boostTest (a : ℝ) (f : V → ℂ) : V → ℂ := fun x => f (lorentzBoost a x)

/-- **Boost-equivariance of the localization (Fourier) map**: `f̂_M ∘ β_a = U_a ∘ f̂_M`, i.e.
    `(β_a f)^_M(p) = f̂_M(Λ_a p)`.  A clean change of variables `y = Λ_a x` (unit Jacobian, the boost is
    volume-preserving and a measurable embedding) plus the Minkowski-pairing boost-invariance.  This is the
    Phase-1c keystone: it makes the localization intertwine the spacetime boost with the one-particle
    action.  Holds for ANY `f` (no integrability hypothesis — `MeasurePreserving.integral_comp`). -/
theorem minkowskiFourier_boost (a : ℝ) (f : V → ℂ) (p : V) :
    minkowskiFourier (boostTest a f) p = minkowskiFourier f (lorentzBoost a p) := by
  have hcomp := (measurePreserving_lorentzBoost a).integral_comp
    (measurableEmbedding_lorentzBoost a)
    (fun y => Complex.exp (-Complex.I * ((minkowskiDot (lorentzBoost a p) y : ℝ) : ℂ)) * f y)
  simp only [minkowskiFourier, boostTest]
  rw [← hcomp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [minkowskiDot_boost]

/-! ### The localized rapidity amplitude and its boost-covariance (Phase 2a) -/

/-- **The localized rapidity amplitude** `(K f)(θ) = 2^{-1/2} · f̂_M(p_m θ)` — the value of the localization
    map on the positive mass shell, in rapidity coordinates (before the `L²` packaging).  The `1/√2` is the
    invariant-measure normalization `dp/(2ω) = dθ/2` (soundness trap #1: omitting it scales the symplectic
    form by 2). -/
noncomputable def Krep (m : ℝ) (f : V → ℂ) (θ : ℝ) : ℂ :=
  (1 / Real.sqrt 2 : ℂ) * minkowskiFourier f (massShell m θ)

/-- **The localization is boost-covariant at the amplitude level**: boosting the spacetime test function
    *translates* the localized rapidity amplitude, `(K (β_a f))(θ) = (K f)(θ + a)`.  So the Lorentz boost
    acts on the localized one-particle amplitude as the rapidity translation `θ ↦ θ + a` — exactly the
    action implemented by the one-particle unitary `OneParticle.boostUnitary`.  Immediate from the Phase-1c
    keystone `minkowskiFourier_boost` and the shell geometry `massShell_boost`. -/
theorem Krep_boost (m a : ℝ) (f : V → ℂ) (θ : ℝ) :
    Krep m (boostTest a f) θ = Krep m f (θ + a) := by
  rw [Krep, Krep, minkowskiFourier_boost, massShell_boost]

/-! ### Reality / both-frequencies structure (toward the Pauli–Jordan symplectic form, Phase 2b) -/

/-- The Minkowski pairing is odd in its first argument: `η(−p, x) = −η(p, x)`. -/
theorem minkowskiDot_neg_left (p x : V) : minkowskiDot (-p) x = - minkowskiDot p x := by
  simp only [minkowskiDot, Pi.neg_apply]; ring

/-- **Conjugation ↔ frequency reflection** for the Minkowski-Fourier transform:
    `conj(f̂_M(p)) = (conj f)^_M(−p)`.  For a REAL test function (`conj f = f`) this gives
    `conj(f̂_M(p)) = f̂_M(−p)` — the relation that makes the *full* (both-frequency) Pauli–Jordan symplectic
    form emerge from the positive-mass-shell amplitude (soundness traps #4/#6: positive shell only, both
    frequencies via conjugation). -/
theorem minkowskiFourier_conj (f : V → ℂ) (p : V) :
    (starRingEnd ℂ) (minkowskiFourier f p)
      = minkowskiFourier (fun x => (starRingEnd ℂ) (f x)) (-p) := by
  rw [minkowskiFourier, minkowskiFourier, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, ← Complex.exp_conj, minkowskiDot_neg_left, map_neg, Complex.conj_I,
    Complex.conj_ofReal, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]

/-! ### The (integral-level) symplectic form and its antisymmetry (Phase 2b) -/

/-- **The localized sesquilinear form** `⟨Kf, Kg⟩ = ∫_ℝ conj(K f θ)·(K g θ) dθ` — the would-be `L²(ℝ)`
    inner product of the localized rapidity amplitudes, written at the integral level (so it needs no `L²`
    membership).  Its imaginary part is the localized symplectic form. -/
noncomputable def Kform (m : ℝ) (f g : V → ℂ) : ℂ :=
  ∫ θ, (starRingEnd ℂ) (Krep m f θ) * Krep m g θ

/-- **Hermitian symmetry** of the localized form: `conj⟨Kf,Kg⟩ = ⟨Kg,Kf⟩`. -/
theorem Kform_conj (m : ℝ) (f g : V → ℂ) :
    (starRingEnd ℂ) (Kform m f g) = Kform m g f := by
  rw [Kform, Kform, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring

/-- **The localized symplectic form is ANTISYMMETRIC**: `Im⟨Kf,Kg⟩ = −Im⟨Kg,Kf⟩`.  This is the
    commutator-type structure (as opposed to the symmetric Wightman two-point function).  CAVEAT — do not
    over-read it: `Im⟨·,·⟩` is antisymmetric for *any* complex inner product, so antisymmetry ALONE does not
    identify this form as the Pauli–Jordan distribution.  It is the mass-shell symplectic form; its
    identification with `Δ_m` is established only once the spacelike-support theorem is proven (and the
    `1/cosh`-normalization/sign audited).  Holds for all `f, g`. -/
theorem Kform_im_antisymm (m : ℝ) (f g : V → ℂ) :
    (Kform m f g).im = -(Kform m g f).im := by
  have h := congrArg Complex.im (Kform_conj m f g)
  rw [Complex.conj_im] at h
  linarith

/-- The localized symplectic form vanishes on the diagonal (`Im⟨Kf,Kf⟩ = 0`) — an immediate consequence of
    antisymmetry, and the trivial self-consistency of microcausality. -/
theorem Kform_im_self (m : ℝ) (f : V → ℂ) : (Kform m f f).im = 0 := by
  have := Kform_im_antisymm m f f; linarith

/-! ### The L²-valued localization map (Phase 2b: the `H`-valued `K` for the Stage-2 interface) -/

/-- The Minkowski-Fourier transform of the zero function is zero. -/
@[simp] theorem minkowskiFourier_zero (p : V) : minkowskiFourier (fun _ => 0) p = 0 := by
  simp [minkowskiFourier]

/-- The localized amplitude of the zero function is the zero function. -/
theorem Krep_zero (m : ℝ) : Krep m (fun _ => (0 : ℂ)) = 0 := by
  funext θ; simp [Krep]

/-- **An `L²`-admissible test function**: a spacetime test function `f` whose localized rapidity amplitude
    `Krep m f` is square-integrable, i.e. lands in the one-particle space `L²(ℝ)`.  NOTE — "admissible" here
    is the analytic *domain* condition (`Krep m f ∈ L²`); it does NOT assert spacelike localization.  The
    `memLp` field is that domain condition; that every Schwartz / compactly-supported test satisfies it (via
    the general `1/cosh` Fourier-decay bound on the mass shell) is the isolated analytic refinement — not yet
    formalized — kept as a field so the `L²`-valued map and the Stage-2 interface proceed axiom-free. -/
structure LocalTest (m : ℝ) where
  /-- the spacetime test function. -/
  f : V → ℂ
  /-- its localized rapidity amplitude is in `L²(ℝ)` (the one-particle space). -/
  memLp : MeasureTheory.MemLp (Krep m f) 2 (volume : MeasureTheory.Measure ℝ)

/-- **The L²-valued localization map** `K : LocalTest → L²(ℝ)` — the one-particle-Hilbert-space-valued
    localization of a spacetime test function (the concrete `K` the `SpacetimeLocalization` interface
    requires).  `K L` is the `L²` class of the localized rapidity amplitude `Krep m L.f`. -/
noncomputable def K (m : ℝ) (L : LocalTest m) : Lp ℂ 2 (volume : MeasureTheory.Measure ℝ) :=
  L.memLp.toLp _

/-- **Non-vacuity witness**: the localizable-test class is inhabited (degenerately, by `f = 0`).  A
    non-degenerate inhabitant — every Schwartz function — is the isolated Schwartz–Fourier analytic
    obligation. -/
noncomputable def trivialLocalTest (m : ℝ) : LocalTest m where
  f := fun _ => 0
  memLp := by rw [Krep_zero]; exact MeasureTheory.MemLp.zero

/-! ### Measurability of the localized amplitude (part (a) of the boundedness `MemLp`) -/

/-- `p ↦ η(p,x)` is continuous. -/
theorem continuous_minkowskiDot_fst (x : V) : Continuous (fun p : V => minkowskiDot p x) := by
  unfold minkowskiDot; fun_prop

/-- `x ↦ η(p,x)` is continuous. -/
theorem continuous_minkowskiDot_snd (p : V) : Continuous (fun x : V => minkowskiDot p x) := by
  unfold minkowskiDot; fun_prop

/-- **The Minkowski-Fourier transform of an integrable function is continuous** (Riemann–Lebesgue
    continuity, via dominated convergence; the exponential has modulus one and `f` dominates). -/
theorem minkowskiFourier_continuous {f : V → ℂ} (hf : Integrable f) :
    Continuous (minkowskiFourier f) := by
  apply continuous_of_dominated (bound := fun x => ‖f x‖)
  · intro p
    refine AEStronglyMeasurable.mul ?_ hf.aestronglyMeasurable
    exact ((Complex.continuous_ofReal.comp (continuous_minkowskiDot_snd p)).const_mul
      (-Complex.I)).cexp.aestronglyMeasurable
  · intro p
    filter_upwards with x
    rw [norm_mul, show (-Complex.I * ((minkowskiDot p x : ℝ) : ℂ))
        = ((-(minkowskiDot p x) : ℝ) : ℂ) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  · exact hf.norm
  · filter_upwards with x
    exact (((Complex.continuous_ofReal.comp (continuous_minkowskiDot_fst x)).const_mul
      (-Complex.I)).cexp).mul continuous_const

/-- The mass-shell embedding `θ ↦ p_m(θ)` is continuous. -/
theorem continuous_massShell (m : ℝ) : Continuous (massShell m) := by
  unfold massShell
  refine continuous_pi (fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

/-- **The localized rapidity amplitude is continuous** for an integrable test function, hence (part (a) of
    `MemLp`) almost-everywhere strongly measurable.  The remaining part (b) — the `L²` bound from
    Schwartz–Fourier decay on the mass shell — is the isolated multi-week analytic core. -/
theorem Krep_continuous {m : ℝ} {f : V → ℂ} (hf : Integrable f) : Continuous (Krep m f) :=
  (((minkowskiFourier_continuous hf).comp (continuous_massShell m)).const_mul _)

theorem Krep_aestronglyMeasurable {m : ℝ} {f : V → ℂ} (hf : Integrable f) :
    MeasureTheory.AEStronglyMeasurable (Krep m f) (volume : MeasureTheory.Measure ℝ) :=
  (Krep_continuous hf).aestronglyMeasurable

/-! ### Boundedness, part (b): decay ⟹ L² — reducing the obligation to a `1/cosh` Fourier-decay bound -/

/-- The mass-shell hyperbola dominates the parabola: `1 + θ² ≤ cosh²θ` (since `cosh²=1+sinh²` and
    `θ² ≤ sinh²θ`). -/
theorem one_add_sq_le_cosh_sq (θ : ℝ) : 1 + θ ^ 2 ≤ Real.cosh θ ^ 2 := by
  have h1 : θ ^ 2 ≤ Real.sinh θ ^ 2 := by
    rcases le_total 0 θ with h | h
    · have hθs : θ ≤ Real.sinh θ := Real.self_le_sinh_iff.mpr h
      have hs : 0 ≤ Real.sinh θ := Real.sinh_nonneg_iff.mpr h
      nlinarith [hθs, hs, h]
    · have hsθ : Real.sinh θ ≤ θ := Real.sinh_le_self_iff.mpr h
      have hs : Real.sinh θ ≤ 0 := Real.sinh_nonpos_iff.mpr h
      nlinarith [hsθ, hs, h]
  nlinarith [Real.cosh_sq_sub_sinh_sq θ, h1]

/-- `1/cosh²` is integrable on `ℝ` (dominated by the Cauchy density `(1+θ²)⁻¹`). -/
theorem integrable_cosh_inv_sq :
    Integrable (fun θ : ℝ => (Real.cosh θ ^ 2)⁻¹) := by
  have hcont : Continuous (fun θ : ℝ => (Real.cosh θ ^ 2)⁻¹) :=
    (Real.continuous_cosh.pow 2).inv₀ (fun θ => by positivity)
  refine integrable_inv_one_add_sq.mono hcont.aestronglyMeasurable ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  gcongr
  exact one_add_sq_le_cosh_sq θ

/-- `1/cosh ∈ L²(ℝ)` — the comparison function for the localized-amplitude boundedness. -/
theorem memLp_cosh_inv : MemLp (fun θ : ℝ => (Real.cosh θ)⁻¹) 2 (volume : MeasureTheory.Measure ℝ) := by
  have hcont : Continuous (fun θ : ℝ => (Real.cosh θ)⁻¹) :=
    Real.continuous_cosh.inv₀ (fun θ => (Real.cosh_pos θ).ne')
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  refine integrable_cosh_inv_sq.congr (Filter.Eventually.of_forall fun θ => ?_)
  show (Real.cosh θ ^ 2)⁻¹ = ‖(Real.cosh θ)⁻¹‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), inv_pow]

/-- **Boundedness from a `1/cosh` decay bound**: if the localized rapidity amplitude is dominated by
    `C/cosh θ`, then it lies in `L²(ℝ)`.  This reduces the `MemLp` obligation of `LocalTest` to the sharp
    pointwise Fourier-decay estimate `‖(K f)(θ)‖ ≤ C/cosh θ` — the genuine remaining analytic content (the
    Fourier transform of a smooth test function decays on the mass shell).  The integrability is fully
    discharged here. -/
theorem Krep_memLp_of_decay {m : ℝ} {f : V → ℂ} (hfint : Integrable f) {C : ℝ}
    (hbound : ∀ θ, ‖Krep m f θ‖ ≤ C * (Real.cosh θ)⁻¹) :
    MemLp (Krep m f) 2 (volume : MeasureTheory.Measure ℝ) := by
  refine MemLp.of_le_mul (c := C) memLp_cosh_inv (Krep_aestronglyMeasurable hfint)
    (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (Real.cosh θ)⁻¹)]
  exact hbound θ

/-! ### A concrete non-degenerate localizable test: the Gaussian -/

/-- `θ² ≤ sinh²θ`. -/
theorem sq_le_sinh_sq (θ : ℝ) : θ ^ 2 ≤ Real.sinh θ ^ 2 := by
  rcases le_total 0 θ with h | h
  · nlinarith [Real.self_le_sinh_iff.mpr h, Real.sinh_nonneg_iff.mpr h, h]
  · nlinarith [Real.sinh_le_self_iff.mpr h, Real.sinh_nonpos_iff.mpr h, h]

/-- The double-rapidity hyperbola dominates the parabola: `2θ² ≤ cosh(2θ)`. -/
theorem two_sq_le_cosh_two_mul (θ : ℝ) : 2 * θ ^ 2 ≤ Real.cosh (2 * θ) := by
  nlinarith [Real.cosh_two_mul θ, sq_le_sinh_sq θ, Real.cosh_sq_sub_sinh_sq θ]

/-- `exp(−c·cosh(2θ))` is integrable on `ℝ` for `c > 0` (dominated by the Gaussian `exp(−2cθ²)`). -/
theorem integrable_exp_neg_cosh_two_mul {c : ℝ} (hc : 0 < c) :
    Integrable (fun θ : ℝ => Real.exp (-(c * Real.cosh (2 * θ)))) := by
  have hcont : Continuous (fun θ : ℝ => Real.exp (-(c * Real.cosh (2 * θ)))) := by fun_prop
  refine (integrable_exp_neg_mul_sq (show (0 : ℝ) < 2 * c by linarith)).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  nlinarith [two_sq_le_cosh_two_mul θ, hc]

/-- The 2D Gaussian test function `f(x) = exp(−(x₀²+x₁²))`. -/
noncomputable def gaussianTest : V → ℂ := fun x => Complex.exp (-((x 0 ^ 2 + x 1 ^ 2 : ℝ) : ℂ))

/-- **Explicit Minkowski-Fourier transform of the Gaussian** (Fubini over `Fin 2 → ℝ` + the 1D complex
    Gaussian Fourier integral): a separable product of two 1D Gaussian Fourier integrals. -/
theorem minkowskiFourier_gaussian (p : V) :
    minkowskiFourier gaussianTest p
      = (((π : ℂ) / 1) ^ (1 / 2 : ℂ) * Complex.exp (-(-(p 0 : ℂ)) ^ 2 / (4 * 1)))
        * (((π : ℂ) / 1) ^ (1 / 2 : ℂ) * Complex.exp (-((p 1 : ℂ)) ^ 2 / (4 * 1))) := by
  have hb : (0 : ℝ) < (1 : ℂ).re := by norm_num
  rw [minkowskiFourier]
  have key : (fun x : V => Complex.exp (-Complex.I * ((minkowskiDot p x : ℝ) : ℂ)) * gaussianTest x)
      = (fun x : V => ∏ i : Fin 2,
          (![fun y : ℝ => Complex.exp (Complex.I * (-(p 0 : ℂ)) * y) * Complex.exp (-1 * (y : ℂ) ^ 2),
             fun y : ℝ => Complex.exp (Complex.I * ((p 1 : ℂ)) * y) * Complex.exp (-1 * (y : ℂ) ^ 2)]
            i) (x i)) := by
    funext x
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, gaussianTest,
      minkowskiDot, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [key, integral_fintype_prod_volume_eq_prod, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [fourierIntegral_gaussian hb (-(p 0 : ℂ)), fourierIntegral_gaussian hb ((p 1 : ℂ))]

/-- The localized Gaussian amplitude is a **real, positive** value: `(K f)(θ) = 2^{−1/2}·π·exp(−m²cosh(2θ)/4)`. -/
theorem Krep_gaussian_eq (m θ : ℝ) :
    Krep m gaussianTest θ
      = ((1 / Real.sqrt 2 * (π * Real.exp (-(m ^ 2 * Real.cosh (2 * θ)) / 4)) : ℝ) : ℂ) := by
  rw [Krep, minkowskiFourier_gaussian, massShell_zero, massShell_one]
  simp only [div_one, mul_one]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcpow : (π : ℂ) ^ (1 / 2 : ℂ) * (π : ℂ) ^ (1 / 2 : ℂ) = (π : ℂ) := by
    rw [← Complex.cpow_add _ _ hπ]; norm_num
  have hexp : Complex.exp (-(-(↑(m * Real.cosh θ) : ℂ)) ^ 2 / 4)
      * Complex.exp (-((↑(m * Real.sinh θ) : ℂ)) ^ 2 / 4)
      = ((Real.exp (-(m ^ 2 * Real.cosh (2 * θ)) / 4) : ℝ) : ℂ) := by
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    rw [Real.cosh_two_mul]
    push_cast
    ring
  calc (1 / Real.sqrt 2 : ℂ)
        * ((π : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(-(↑(m * Real.cosh θ) : ℂ)) ^ 2 / 4)
          * ((π : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-((↑(m * Real.sinh θ) : ℂ)) ^ 2 / 4)))
      = (1 / Real.sqrt 2 : ℂ) * (((π : ℂ) ^ (1 / 2 : ℂ) * (π : ℂ) ^ (1 / 2 : ℂ))
          * (Complex.exp (-(-(↑(m * Real.cosh θ) : ℂ)) ^ 2 / 4)
            * Complex.exp (-((↑(m * Real.sinh θ) : ℂ)) ^ 2 / 4))) := by ring
    _ = (1 / Real.sqrt 2 : ℂ) * ((π : ℂ) * ((Real.exp (-(m ^ 2 * Real.cosh (2 * θ)) / 4) : ℝ) : ℂ)) := by
          rw [hcpow, hexp]
    _ = ((1 / Real.sqrt 2 * (π * Real.exp (-(m ^ 2 * Real.cosh (2 * θ)) / 4)) : ℝ) : ℂ) := by
          push_cast; ring

/-- **A concrete non-degenerate localizable test: the Gaussian** (`m ≠ 0`).  Its localized amplitude lies in
    `L²(ℝ)` — the boundedness `Krep_memLp` is genuinely satisfied by a real physical test function (not just
    the `f = 0` witness).  `‖(K f)(θ)‖² = (π²/2)·exp(−(m²/2)·cosh 2θ)`, integrable. -/
theorem gaussian_Krep_memLp {m : ℝ} (hm : m ≠ 0) :
    MemLp (Krep m gaussianTest) 2 (volume : MeasureTheory.Measure ℝ) := by
  have hmeas : MeasureTheory.AEStronglyMeasurable (Krep m gaussianTest)
      (volume : MeasureTheory.Measure ℝ) := by
    have : Continuous (Krep m gaussianTest) := by
      rw [show Krep m gaussianTest = fun θ => ((1 / Real.sqrt 2
        * (π * Real.exp (-(m ^ 2 * Real.cosh (2 * θ)) / 4)) : ℝ) : ℂ) from funext (Krep_gaussian_eq m)]
      fun_prop
    exact this.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hsq : (fun θ => ‖Krep m gaussianTest θ‖ ^ 2)
      = fun θ => (1 / 2 * π ^ 2) * Real.exp (-(m ^ 2 / 2 * Real.cosh (2 * θ))) := by
    funext θ
    rw [Krep_gaussian_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsqrt : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have hexp : (Real.exp (-(m ^ 2 * Real.cosh (2 * θ)) / 4)) ^ 2
        = Real.exp (-(m ^ 2 / 2 * Real.cosh (2 * θ))) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [mul_pow, mul_pow, hsqrt, hexp]; ring
  rw [hsq]
  exact (integrable_exp_neg_cosh_two_mul (c := m ^ 2 / 2) (by positivity)).const_mul _

/-- **A non-degenerate inhabitant of the admissible-test domain** (`m ≠ 0`): the Gaussian.  Unlike
    `trivialLocalTest` (`f=0`), this is a nonzero test whose localization `K` lies in `L²(ℝ)`, so the
    `MemLp` obligation of `LocalTest` is satisfied non-vacuously, machine-checked end to end.
    CAVEAT — this witnesses that the admissible domain is non-empty and non-degenerate; it is NOT a
    spacelike-localized observable: the Gaussian's support is all of spacetime.  It is an analytic
    admissibility witness, not a local test in the AQFT sense. -/
noncomputable def gaussianLocalTest {m : ℝ} (hm : m ≠ 0) : LocalTest m where
  f := gaussianTest
  memLp := gaussian_Krep_memLp hm

end QIQTH.Fock.Localization
