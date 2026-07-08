/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.

# The Lorentz-invariant mass-shell measure as a rapidity pushforward

For a scalar field of mass `m > 0`, the one-particle Hilbert space is `L²` of the
positive mass shell with the Lorentz-invariant measure `dk / (2 ω(k))`, where
`ω(k) = √(k² + m²)`.  Parametrising the shell by rapidity `θ` via `k = m · sinh θ`
turns that measure into a *flat* half-Lebesgue measure `dθ / 2`:

  since `ω(m sinh θ) = m cosh θ` and `dk = m cosh θ · dθ`, the Jacobian `m cosh θ`
  cancels the `ω = m cosh θ` in the denominator, leaving exactly the factor `1/2`.

This file proves the exact measure identity

  `Measure.map (fun θ => m·sinh θ) ((1/2)•volume)
      = volume.withDensity (fun k => (2·√(k²+m²))⁻¹)`

i.e. the rapidity pushforward of the flat half-measure equals the mass-shell measure.

Mathematical inputs are all standard Mathlib facts (hyperbolic identities, the 1-D
change-of-variables formula `lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`);
no `axiom`s and no `sorry`.
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Arsinh

namespace QIQTH.OneParticleMeasure

open MeasureTheory
open scoped ENNReal

/-- The relativistic dispersion `ω(k) = √(k² + m²)`, kept local to avoid import cycles
with `QIQTH.KGSymplectic`. -/
noncomputable def kgOmega (m k : ℝ) : ℝ := Real.sqrt (k ^ 2 + m ^ 2)

/-- On the rapidity chart `k = m sinh θ` the on-shell energy is `ω = m cosh θ`. -/
lemma omega_rapidity {m : ℝ} (hm : 0 < m) (θ : ℝ) :
    kgOmega m (m * Real.sinh θ) = m * Real.cosh θ := by
  unfold kgOmega
  have h : (m * Real.sinh θ) ^ 2 + m ^ 2 = (m * Real.cosh θ) ^ 2 := by
    linear_combination (-(m ^ 2)) * Real.cosh_sq θ
  rw [h, Real.sqrt_sq (mul_nonneg hm.le (Real.cosh_pos θ).le)]

/-- The measure-theoretic Jacobian cancellation: the mass-shell density `(2ω)⁻¹`
times the change-of-variables factor `m cosh θ` is exactly `1/2`. -/
lemma jacobian_cancel {m : ℝ} (hm : 0 < m) (θ : ℝ) :
    (2 * kgOmega m (m * Real.sinh θ))⁻¹ * (m * Real.cosh θ) = (1 / 2 : ℝ) := by
  have hx : m * Real.cosh θ ≠ 0 := (mul_pos hm (Real.cosh_pos θ)).ne'
  rw [omega_rapidity hm θ, mul_inv, mul_assoc, inv_mul_cancel₀ hx, mul_one, one_div]

/-- **Main identity.**  For `m > 0` the rapidity pushforward of the flat half-Lebesgue
measure `(1/2)•volume` equals the Lorentz-invariant mass-shell measure
`volume.withDensity (2·√(k²+m²))⁻¹`.  This is the measure whose weighted `L²` is the
Klein–Gordon one-particle space. -/
theorem map_rapidityHalfMeasure_eq_massShellMeasure {m : ℝ} (hm : 0 < m) :
    Measure.map (fun θ : ℝ => m * Real.sinh θ)
        ((ENNReal.ofReal (1 / 2)) • (volume : Measure ℝ))
      = (volume : Measure ℝ).withDensity
          (fun k : ℝ => ENNReal.ofReal ((2 * Real.sqrt (k ^ 2 + m ^ 2))⁻¹)) := by
  have hmne : m ≠ 0 := hm.ne'
  -- the rapidity map and the mass-shell density
  set g : ℝ → ℝ := fun θ => m * Real.sinh θ with hgdef
  set dens : ℝ → ℝ≥0∞ := fun k => ENNReal.ofReal ((2 * Real.sqrt (k ^ 2 + m ^ 2))⁻¹)
    with hdensdef
  -- regularity
  have hg_meas : Measurable g := (continuous_const.mul Real.continuous_sinh).measurable
  have hdens_meas : Measurable dens := by
    rw [hdensdef]; fun_prop
  -- derivative, monotonicity and surjectivity of the rapidity map
  have hderiv : ∀ θ ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt g (m * Real.cosh θ) Set.univ θ := by
    intro θ _
    exact ((Real.hasDerivAt_sinh θ).const_mul m).hasDerivWithinAt
  have hmono : MonotoneOn g Set.univ := by
    intro a _ b _ hab
    exact mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr hab) hm.le
  have hsurj : Function.Surjective g := by
    intro k
    refine ⟨Real.arsinh (k / m), ?_⟩
    rw [hgdef]; simp only; rw [Real.sinh_arsinh]; field_simp
  have himg : g '' Set.univ = Set.univ := by
    rw [Set.image_univ, Set.range_eq_univ.mpr hsurj]
  -- test against an arbitrary measurable `φ`
  refine Measure.ext_of_lintegral _ (fun φ hφ => ?_)
  have hφg : Measurable fun θ => φ (g θ) := hφ.comp hg_meas
  -- left-hand side: pushforward of the flat half-measure
  have hLHS : ∫⁻ k, φ k ∂(Measure.map g ((ENNReal.ofReal (1 / 2)) • volume))
      = ENNReal.ofReal (1 / 2) * ∫⁻ θ, φ (g θ) ∂volume := by
    rw [lintegral_map hφ hg_meas, lintegral_smul_measure, smul_eq_mul]
  -- right-hand side: the withDensity integral
  have hRHS : ∫⁻ k, φ k ∂(volume.withDensity dens)
      = ∫⁻ k, dens k * φ k ∂volume := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hdens_meas hφ]; rfl
  -- 1-D change of variables `k = g θ`, `dk = (m cosh θ) dθ`
  have hCoV : ∫⁻ k, dens k * φ k ∂volume
      = ∫⁻ θ, ENNReal.ofReal (m * Real.cosh θ) * (dens (g θ) * φ (g θ)) ∂volume := by
    have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
      (MeasurableSet.univ) hderiv hmono (fun k => dens k * φ k)
    rw [himg, setLIntegral_univ, setLIntegral_univ] at h
    exact h
  -- pointwise: the Jacobian cancels the energy, leaving `1/2`
  have hpt : ∀ θ, ENNReal.ofReal (m * Real.cosh θ) * (dens (g θ) * φ (g θ))
      = ENNReal.ofReal (1 / 2) * φ (g θ) := by
    intro θ
    rw [hdensdef, hgdef]
    simp only
    rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hm.le (Real.cosh_pos θ).le)]
    have hj : m * Real.cosh θ * (2 * Real.sqrt ((m * Real.sinh θ) ^ 2 + m ^ 2))⁻¹
        = (1 / 2 : ℝ) := by
      rw [mul_comm]; exact jacobian_cancel hm θ
    rw [hj]
  -- assemble
  rw [hLHS, hRHS, hCoV, lintegral_congr hpt, lintegral_const_mul _ hφg]

/-- The Lorentz-invariant mass-shell measure `dk / (2 ω(k))` as a `withDensity`. -/
noncomputable def massShellMeasure (m : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun k : ℝ => ENNReal.ofReal ((2 * Real.sqrt (k ^ 2 + m ^ 2))⁻¹))

/-- The rapidity chart `θ ↦ m · sinh θ` as a homeomorphism of `ℝ` (for `m ≠ 0`), with
inverse `k ↦ arsinh (k / m)`. -/
noncomputable def rapidityHomeomorph (m : ℝ) (hm : m ≠ 0) : ℝ ≃ₜ ℝ where
  toFun := fun θ => m * Real.sinh θ
  invFun := fun k => Real.arsinh (k / m)
  left_inv := fun θ => by
    show Real.arsinh (m * Real.sinh θ / m) = θ
    rw [mul_div_cancel_left₀ _ hm, Real.arsinh_sinh]
  right_inv := fun k => by
    show m * Real.sinh (Real.arsinh (k / m)) = k
    rw [Real.sinh_arsinh, mul_div_cancel₀ _ hm]
  continuous_toFun := continuous_const.mul Real.continuous_sinh
  continuous_invFun := Real.continuous_arsinh.comp (continuous_id.div_const m)

/-- The rapidity chart as a measurable equivalence of `ℝ`. -/
noncomputable def rapidityMeasurableEquiv (m : ℝ) (hm : m ≠ 0) : ℝ ≃ᵐ ℝ :=
  (rapidityHomeomorph m hm).toMeasurableEquiv

@[simp] lemma rapidityMeasurableEquiv_apply (m : ℝ) (hm : m ≠ 0) (θ : ℝ) :
    rapidityMeasurableEquiv m hm θ = m * Real.sinh θ := by
  rw [rapidityMeasurableEquiv, Homeomorph.toMeasurableEquiv_coe]; rfl

/-- **Measure-preserving form.**  The rapidity chart carries the flat half-Lebesgue
measure `(1/2)•volume` to the mass-shell measure. -/
theorem rapidity_measurePreserving {m : ℝ} (hm : 0 < m) :
    MeasurePreserving (rapidityMeasurableEquiv m hm.ne')
      ((ENNReal.ofReal (1 / 2)) • (volume : Measure ℝ)) (massShellMeasure m) := by
  refine ⟨(rapidityMeasurableEquiv m hm.ne').measurable, ?_⟩
  have hcoe : (rapidityMeasurableEquiv m hm.ne' : ℝ → ℝ) = fun θ => m * Real.sinh θ := by
    funext θ; exact rapidityMeasurableEquiv_apply m hm.ne' θ
  rw [hcoe, massShellMeasure]
  exact map_rapidityHalfMeasure_eq_massShellMeasure hm

/-- **Rapidity change of variables for an arbitrary integrand.**  For `m > 0` and any
`H : ℝ → ℂ`, integrating `H` against the mass-shell measure equals `1/2` times the
flat rapidity integral of `H ∘ (m · sinh)`. -/
theorem integral_massShellMeasure_eq_half_rapidity {m : ℝ} (hm : 0 < m) (H : ℝ → ℂ) :
    ∫ k, H k ∂ massShellMeasure m
      = (1 / 2 : ℝ) • ∫ θ, H (m * Real.sinh θ) ∂ (volume : Measure ℝ) := by
  have hmap : Measure.map (rapidityMeasurableEquiv m hm.ne')
      ((ENNReal.ofReal (1 / 2)) • (volume : Measure ℝ)) = massShellMeasure m :=
    (rapidity_measurePreserving hm).map_eq
  calc
    ∫ k, H k ∂ massShellMeasure m
        = ∫ k, H k ∂ (Measure.map (rapidityMeasurableEquiv m hm.ne')
            ((ENNReal.ofReal (1 / 2)) • (volume : Measure ℝ))) := by rw [hmap]
    _ = ∫ θ, H (rapidityMeasurableEquiv m hm.ne' θ)
            ∂ ((ENNReal.ofReal (1 / 2)) • (volume : Measure ℝ)) :=
          integral_map_equiv (rapidityMeasurableEquiv m hm.ne') H
    _ = ∫ θ, H (m * Real.sinh θ)
            ∂ ((ENNReal.ofReal (1 / 2)) • (volume : Measure ℝ)) := by
          simp only [rapidityMeasurableEquiv_apply]
    _ = (ENNReal.ofReal (1 / 2)).toReal • ∫ θ, H (m * Real.sinh θ) ∂ (volume : Measure ℝ) := by
          rw [MeasureTheory.integral_smul_measure]
    _ = (1 / 2 : ℝ) • ∫ θ, H (m * Real.sinh θ) ∂ (volume : Measure ℝ) := by
          rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- **Conjugate-multiplication corollary** (the inner-product integrand).  Matches the
`sigmaK`/`starRingEnd ℂ` convention used elsewhere in the repo. -/
theorem massShell_conj_mul_integral_eq_half_rapidity {m : ℝ} (hm : 0 < m) (F G : ℝ → ℂ) :
    ∫ k, starRingEnd ℂ (F k) * G k ∂ massShellMeasure m
      = (1 / 2 : ℝ) • ∫ θ, starRingEnd ℂ (F (m * Real.sinh θ)) * G (m * Real.sinh θ)
            ∂ (volume : Measure ℝ) := by
  simpa using
    integral_massShellMeasure_eq_half_rapidity hm (fun k => starRingEnd ℂ (F k) * G k)

end QIQTH.OneParticleMeasure
