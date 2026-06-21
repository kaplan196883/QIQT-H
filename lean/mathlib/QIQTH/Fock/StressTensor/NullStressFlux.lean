import QIQTH.Fock.StressTensor.HorizonField

/-!
# Free-field stress tensor (Route B) — Phase 2: the null stress component and the horizon flux

`STRESS_TENSOR_FORMALIZATION_PLAN.md`, Phase 2.  On the horizon the free field is the chiral field
`horizonField m f λ`; its null-null stress-energy component is the energy density
`T_kk(λ) = |∂_λ φ_H(λ)|²`.  We work with the *formal* `λ`-derivative as its own integral object
`horizonFieldDeriv m f λ = ∫ θ, Krep m f θ · (−i·nullMom m θ) · e^{−i λ nullMom m θ} dθ`
(this IS `∂_λ horizonField`; the differentiation-under-the-integral identification is a separate analytic
lemma, deferred — it does not affect the *definition* of the flux or its covariances).

Definitions:
* `horizonFieldDeriv m f λ` — the affine derivative of the horizon field.
* `Tkk m f λ := ‖horizonFieldDeriv m f λ‖²` — the null-null stress component `T_kk` (a defined object, no
  longer a label).
* `stressFluxKK m f := ∫_ℝ λ · T_kk(λ) dλ` — the affine-weighted horizon flux `∫_H λ T_kk dλ` over the FULL
  (two-sided) horizon generator, i.e. the wedge modular/boost charge.

Covariances (the Route-B payoff that the boost = horizon dilation):
* `horizonFieldDeriv_boostTest`: `horizonFieldDeriv m (boostTest a f) λ = e^a · horizonFieldDeriv m f (e^a λ)`.
* `Tkk_boostTest`: `T_kk[boostTest a f](λ) = e^{2a} · T_kk[f](e^a λ)` — the null energy density has scaling
  dimension 2 under the horizon dilation (exactly the conformal weight of `∂_λ φ`).

These set up Phase 3: `stressFluxKK` is dilation-invariant, and equals `π · rapidityMomentum` (Mellin/
Plancherel), discharging `hTkk`.  Axiom-free.
-/

namespace QIQTH.Fock.StressTensor

open MeasureTheory
open QIQTH.Fock.Localization QIQTH.Fock.OneParticle

/-- The **affine derivative** `∂_λ` of the horizon field, as its own integral object:
    `horizonFieldDeriv m f λ = ∫ θ, Krep m f θ · (−i·nullMom m θ) · e^{−i λ nullMom m θ} dθ`. -/
noncomputable def horizonFieldDeriv (m : ℝ) (f : V → ℂ) (lam : ℝ) : ℂ :=
  ∫ θ, Krep m f θ * (-Complex.I * (nullMom m θ : ℂ))
      * Complex.exp (-Complex.I * (lam : ℂ) * (nullMom m θ : ℂ)) ∂(volume : Measure ℝ)

/-- The **null-null stress-energy component** of the field on the horizon: `T_kk(λ) = |∂_λ φ_H(λ)|²`.
    This is a *defined* real quantity (the labelled `T_kk` made concrete). -/
noncomputable def Tkk (m : ℝ) (f : V → ℂ) (lam : ℝ) : ℝ := ‖horizonFieldDeriv m f lam‖ ^ 2

/-- The **affine-weighted horizon stress flux** `∫_ℝ λ · T_kk(λ) dλ` — the (two-sided) modular/boost charge
    `K = ∫_H λ T_kk dλ` over the FULL horizon generator.  The wedge modular flow `Δ^{it}` is the *two-sided*
    boost, so the full line `∫_ℝ` (not the half line `∫_{λ>0}`) is the physically-correct object; it is also
    the one that equals the boost momentum.  Phase 3 proves `stressFluxKK = −2π · rapidityMomentum`,
    discharging `hTkk`.

    NB (GPT-5.5 consult, verified): the *half*-line flux `∫_{λ>0} λ T_kk` is NOT `const · rapidityMomentum`
    — it differs by a nonlocal Hilbert-transform term (e.g. it is strictly positive for real `K`, while
    `rapidityMomentum = Im∫K·K' = 0`).  The earlier `∫_{Ioi 0}` definition was a bug; this is the fix. -/
noncomputable def stressFluxKK (m : ℝ) (f : V → ℂ) : ℝ :=
  ∫ lam, lam * Tkk m f lam

/-- **Affine derivative under the boost↔dilation map.**  `horizonFieldDeriv m (boostTest a f) λ
    = e^a · horizonFieldDeriv m f (e^a λ)`: the boost dilates the horizon and brings down one power of
    `e^a` from the extra `nullMom` factor. -/
theorem horizonFieldDeriv_boostTest (m a : ℝ) (f : V → ℂ) (lam : ℝ) :
    horizonFieldDeriv m (boostTest a f) lam
      = (Real.exp a : ℂ) * horizonFieldDeriv m f (Real.exp a * lam) := by
  unfold horizonFieldDeriv
  simp only [Krep_boost]
  set g : ℝ → ℂ := fun u => Krep m f u * (-Complex.I * (nullMom m (u - a) : ℂ))
      * Complex.exp (-Complex.I * (lam : ℂ) * (nullMom m (u - a) : ℂ)) with hg
  have e1 : (∫ θ, Krep m f (θ + a) * (-Complex.I * (nullMom m θ : ℂ))
          * Complex.exp (-Complex.I * (lam : ℂ) * (nullMom m θ : ℂ)))
      = ∫ θ, g (θ + a) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [hg, add_sub_cancel_right]
  have e2 : (∫ θ, g (θ + a)) = ∫ u, g u := integral_add_right_eq_self g a
  have e3 : (∫ u, g u) = (Real.exp a : ℂ) * ∫ u, Krep m f u * (-Complex.I * (nullMom m u : ℂ))
          * Complex.exp (-Complex.I * ((Real.exp a * lam : ℝ) : ℂ) * (nullMom m u : ℂ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only [hg]
    rw [show ((nullMom m (u - a)) : ℂ) = (Real.exp a : ℂ) * (nullMom m u : ℂ)
          from by rw [nullMom_sub]; push_cast; ring,
       show (-Complex.I * (lam : ℂ) * ((Real.exp a : ℂ) * (nullMom m u : ℂ)))
          = (-Complex.I * ((Real.exp a * lam : ℝ) : ℂ) * (nullMom m u : ℂ))
          from by push_cast; ring]
    ring
  rw [e1, e2, e3]

/-- **The null stress component has scaling dimension 2 under the horizon dilation.**
    `T_kk[boostTest a f](λ) = (e^a)² · T_kk[f](e^a λ) = e^{2a} · T_kk[f](e^a λ)` — the conformal weight of
    `∂_λ φ`.  (Stated with `(e^a)²` for a clean proof; this is exactly `e^{2a}`.) -/
theorem Tkk_boostTest (m a : ℝ) (f : V → ℂ) (lam : ℝ) :
    Tkk m (boostTest a f) lam = (Real.exp a) ^ 2 * Tkk m f (Real.exp a * lam) := by
  unfold Tkk
  rw [horizonFieldDeriv_boostTest, Complex.norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos a).le, mul_pow]

end QIQTH.Fock.StressTensor
