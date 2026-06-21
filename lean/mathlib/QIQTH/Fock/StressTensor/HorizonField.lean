import QIQTH.Fock.StressTensor.RapidityMomentum
import QIQTH.Fock.Localization

/-!
# Free-field stress tensor (Route B) — Phase 1: the horizon field and its boost↔dilation covariance

`STRESS_TENSOR_FORMALIZATION_PLAN.md`, Phase 1.  The wedge mode `Krep m f` (a rapidity wavefunction
`θ ↦ Krep m f θ`) restricts to the horizon as a 1-D chiral field
`horizonField m f λ = ∫ θ, Krep m f θ · exp(−i λ · nullMom m θ) dθ`,
where `nullMom m θ = (m/√2)·e^{−θ}` is the null component of the on-shell momentum `massShell m θ` along the
horizon generator (read off `minkowskiDot_massShell`: `η(p_m(θ), n) ∝ m e^{−θ}` for the null `n`).

The central Phase-1 identity is the **boost↔dilation intertwining**
`horizonField m (boostTest a f) λ = horizonField m f (e^a · λ)`:
the Lorentz boost on the wedge mode acts as a **dilation** `λ ↦ e^a λ` on the horizon.  This is the
infinitesimal Bisognano–Wichmann statement at the level of the horizon field — the geometric fact Route B
needs so that the modular flow (= boost) becomes the horizon dilation, hence `K = ∫_H λ T_kk dλ` (Phase 2–3).

Proof: `Krep_boost` turns the boost into a rapidity translation `θ ↦ θ+a`, and translation-invariance of
Lebesgue measure (`integral_add_right_eq_self`) re-expresses it as the dilation, using
`nullMom m (θ−a) = e^a · nullMom m θ`.  Axiom-free.

Phase 2 (`NullStressFlux.lean`) defines `Tkk := ‖∂_λ horizonField‖²` and the flux `∫_{λ>0} λ·Tkk`; Phase 3
proves that flux equals `rapidityMomentum`, discharging `hTkk`.
-/

namespace QIQTH.Fock.StressTensor

open MeasureTheory
open QIQTH.Fock.Localization QIQTH.Fock.OneParticle

/-- The **null momentum** of the on-shell mode `massShell m θ = (m cosh θ, m sinh θ)` along the horizon
    generator: `nullMom m θ = (m/√2)·e^{−θ}`.  (The `e^{−θ}` dependence is `η(p_m(θ), n) = m(cosh θ − sinh θ)`
    for the future null `n ∝ (1,1)`, cf. `minkowskiDot_massShell`; the `/√2` is the generator normalization.) -/
noncomputable def nullMom (m θ : ℝ) : ℝ := (m / Real.sqrt 2) * Real.exp (-θ)

/-- A rapidity shift rescales the null momentum: `nullMom m (u − a) = e^a · nullMom m u`.  This is the
    seed of the boost↔dilation intertwining (the boost `θ ↦ θ+a` becomes the horizon dilation by `e^a`). -/
theorem nullMom_sub (m a u : ℝ) : nullMom m (u - a) = Real.exp a * nullMom m u := by
  unfold nullMom
  rw [show -(u - a) = a + (-u) from by ring, Real.exp_add]; ring

/-- The **horizon field**: the restriction of the wedge mode `Krep m f` to the (chiral) horizon, as a
    function of the affine parameter `λ`.  `horizonField m f λ = ∫ θ, Krep m f θ · e^{−i λ · nullMom m θ} dθ`. -/
noncomputable def horizonField (m : ℝ) (f : V → ℂ) (lam : ℝ) : ℂ :=
  ∫ θ, Krep m f θ * Complex.exp (-Complex.I * (lam : ℂ) * (nullMom m θ : ℂ)) ∂(volume : Measure ℝ)

/-- **★ Boost↔dilation intertwining (Phase 1 keystone).**  The Lorentz boost on the wedge test function acts
    on the horizon field as a *dilation* of the affine parameter:
    `horizonField m (boostTest a f) λ = horizonField m f (e^a · λ)`.
    This is the horizon-level Bisognano–Wichmann fact making the modular flow the horizon dilation. -/
theorem horizonField_boostTest (m a : ℝ) (f : V → ℂ) (lam : ℝ) :
    horizonField m (boostTest a f) lam = horizonField m f (Real.exp a * lam) := by
  unfold horizonField
  simp only [Krep_boost]
  set g : ℝ → ℂ :=
    fun u => Krep m f u * Complex.exp (-Complex.I * (lam : ℂ) * (nullMom m (u - a) : ℂ)) with hg
  have e1 : (∫ θ, Krep m f (θ + a) * Complex.exp (-Complex.I * (lam : ℂ) * (nullMom m θ : ℂ)))
      = ∫ θ, g (θ + a) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [hg, add_sub_cancel_right]
  have e2 : (∫ θ, g (θ + a)) = ∫ u, g u := integral_add_right_eq_self g a
  have e3 : (∫ u, g u)
      = ∫ θ, Krep m f θ
          * Complex.exp (-Complex.I * ((Real.exp a * lam : ℝ) : ℂ) * (nullMom m θ : ℂ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only [hg]
    rw [show (-Complex.I * (lam : ℂ) * (nullMom m (u - a) : ℂ))
          = (-Complex.I * ((Real.exp a * lam : ℝ) : ℂ) * (nullMom m u : ℂ))
        from by rw [nullMom_sub]; push_cast; ring]
  rw [e1, e2, e3]

end QIQTH.Fock.StressTensor
