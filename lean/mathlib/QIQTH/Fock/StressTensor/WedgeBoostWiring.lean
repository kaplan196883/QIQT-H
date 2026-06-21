/-
  Stress-tensor Route B → wedge boost charge: wiring the closed `T_kk` scalar into
  `wedge_hBoostCharge_of_smooth`, discharging its `hTkk` hypothesis for the free-field wedge mode `Krep`.

  With `Tkk := −(ℏ/2π)·stressFluxKK m f`, the boost-charge = stress-flux identity
  `2π/ℏ·Tkk = (2π·∫conj(Krep)·Krep').im` is exactly `boostEnergy_eq_neg_stressFlux_schwartz_closed` (Route B).
  The remaining wedge-mode regularity (`Krep ∈ L¹∩L²`, `Krep'` bounded, …) is supplied here.
-/
import QIQTH.Fock.StressTensor.L2Plancherel
import QIQTH.Fock.OneParticleBW

noncomputable section

open MeasureTheory Real Set
open QIQTH.Fock.Localization QIQTH.Fock.OneParticle QIQTH.Fock.OneParticleBW
open scoped FourierTransform

namespace QIQTH.Fock.StressTensor

/-- `exp(−|θ|)` is integrable on `ℝ` (split `Iic 0 ∪ Ioi 0`; `integrableOn_exp_Iic` + `integrableOn_exp_neg_Ioi`). -/
theorem integrable_exp_neg_abs : Integrable (fun θ : ℝ => Real.exp (-|θ|)) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · exact (integrableOn_exp_Iic 0).congr_fun
      (fun θ hθ => by rw [abs_of_nonpos (Set.mem_Iic.mp hθ), neg_neg]) measurableSet_Iic
  · exact (integrableOn_exp_neg_Ioi 0).congr_fun
      (fun θ hθ => by rw [abs_of_pos (Set.mem_Ioi.mp hθ)]) measurableSet_Ioi

/-- `(cosh θ)⁻²` is integrable on `ℝ` — dominated by `4·exp(−|θ|)` (`cosh θ ≥ ½·exp|θ|`). -/
theorem integrable_inv_cosh_sq : Integrable (fun θ : ℝ => ((Real.cosh θ) ^ 2)⁻¹) := by
  refine (integrable_exp_neg_abs.const_mul 4).mono'
    ((Real.continuous_cosh.pow 2).inv₀ (fun θ => by positivity)).aestronglyMeasurable ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hE1 : (1 : ℝ) ≤ Real.exp |θ| := Real.one_le_exp (abs_nonneg θ)
  have hcoshlb : Real.exp |θ| ≤ 2 * Real.cosh θ := by
    rw [Real.cosh_eq]
    rcases abs_cases θ with ⟨habs, _⟩ | ⟨habs, _⟩
    · rw [habs]; nlinarith [Real.exp_pos (-θ)]
    · rw [habs]; nlinarith [Real.exp_pos θ]
  rw [Real.exp_neg, show (4 : ℝ) * (Real.exp |θ|)⁻¹ = 4 / Real.exp |θ| from (div_eq_mul_inv 4 _).symm,
    le_div_iff₀ (Real.exp_pos |θ|), inv_mul_eq_div, div_le_iff₀ (by positivity : (0 : ℝ) < (Real.cosh θ) ^ 2)]
  nlinarith [hcoshlb, hE1, Real.cosh_pos θ]

/-- The free-field wedge mode `Krep m f` is integrable over rapidity (`∫‖Krep‖ ≤ const·∫cosh⁻² < ∞`). -/
theorem Krep_integrable {m : ℝ} (hm : m ≠ 0) (f : SchwartzMap V ℂ) :
    Integrable (fun θ => Krep m (⇑f) θ) volume := by
  refine (integrable_inv_cosh_sq.const_mul
    (16 * π ^ 2 * ((∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖)) / (Real.sqrt 2 * m ^ 2))).mono'
    (Krep_continuous f.integrable).aestronglyMeasurable (Filter.Eventually.of_forall fun θ => ?_)
  exact schwartz_Krep_decay_sq f hm θ

/-- The free-field wedge mode's rapidity derivative `Krep'` is bounded (`‖Krep'θ‖ ≤ C·cosh⁻¹θ ≤ C`). -/
theorem Krep_deriv_bounded {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    ∃ B : ℝ, ∀ θ : ℝ, ‖deriv (fun θ => Krep m (⇑f) θ) θ‖ ≤ B := by
  obtain ⟨C, hC, hb⟩ := Krep_deriv_norm_le hm f
  refine ⟨C, fun θ => (hb θ).trans ?_⟩
  calc C * (Real.cosh θ)⁻¹
      ≤ C * 1 := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ (Real.one_le_cosh θ)) hC
    _ = C := mul_one C

/-- **★★★★★ Route B wired into the wedge boost charge.**  For a Schwartz test function `g` (`m > 0`), the
    derivative of the modular/boost energy of the wedge mode `Krep m g` equals `i·(−stressFluxKK m g)` — i.e.
    the conserved boost Killing charge IS the (now-proven, Route-B) free-field horizon stress flux.  This
    discharges the `hTkk` hypothesis of `wedge_hBoostCharge_of_smooth` (`Tkk := −(ℏ/2π)·stressFluxKK`) using
    `boostEnergy_eq_neg_stressFlux_schwartz_closed`, with all wedge-mode regularity supplied
    (`schwartz_Krep_memLp`, `Krep_integrable`, `Krep_deriv_bounded`, `schwartz_Krep_hasDerivAt`).  Axiom-free. -/
theorem wedge_boostCharge_eq_neg_stressFlux {m : ℝ} (hm : 0 < m) (g : SchwartzMap V ℂ) :
    HasDerivAt
      (fun t : ℝ => inner ℂ ((schwartz_Krep_memLp g hm.ne').toLp (fun θ => Krep m (⇑g) θ))
        (OneParticle.boostUnitary (-(2 * Real.pi * t))
          ((schwartz_Krep_memLp g hm.ne').toLp (fun θ => Krep m (⇑g) θ))))
      (Complex.I * ((- stressFluxKK m (⇑g) : ℝ) : ℂ)) 0 := by
  obtain ⟨B, hB⟩ := Krep_deriv_bounded hm g
  have h := hasDerivAt_inner_boostUnitary_imaginary (fun θ => Krep m (⇑g) θ)
    (deriv (fun θ => Krep m (⇑g) θ)) (schwartz_Krep_memLp g hm.ne') (Krep_integrable hm.ne' g)
    ((schwartz_Krep_memLp g hm.ne').star.integrable_mul (schwartz_Krep_memLp g hm.ne'))
    (Krep_continuous g.integrable).aestronglyMeasurable
    (fun x => (schwartz_Krep_hasDerivAt m hm.le g x).differentiableAt.hasDerivAt)
    (measurable_deriv _).aestronglyMeasurable B hB
  rwa [boostEnergy_eq_neg_stressFlux_schwartz_closed hm g] at h

end QIQTH.Fock.StressTensor
