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
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

end QIQTH.Fock.Localization
