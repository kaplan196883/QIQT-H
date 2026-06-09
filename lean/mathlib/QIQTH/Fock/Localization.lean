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

end QIQTH.Fock.Localization
