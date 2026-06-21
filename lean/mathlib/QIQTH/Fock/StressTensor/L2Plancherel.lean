/-
  Stress-tensor Route B — L² Plancherel for the classical Fourier integral (toward hFdA).

  The coincidence `⇑(𝓕_{L²}(g.toLp 2)) =ᵐ 𝓕 g` for `g ∈ L¹∩L²`, via tempered distributions + the
  multiplication formula (`real_fourier_mul_formula`) — NO density argument needed.  This is the input that
  lets the conjugate Parseval pairing be proven by the L² isometry (`Lp.inner_fourier_eq`), discharging `hFdA`.
-/
import QIQTH.Fock.StressTensor.HorizonParseval
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section

open MeasureTheory Real SchwartzMap
open QIQTH.Fock.Localization QIQTH.Fock.OneParticle
open scoped FourierTransform SchwartzMap

namespace QIQTH.Fock.StressTensor

/-- **★★★ L²-Plancherel coincidence (density-free).**  For `g ∈ L¹ ∩ L²`, the `L²` Fourier transform of
`g.toLp 2` agrees a.e. with the classical Fourier integral `𝓕 g`.  Proved WITHOUT a density argument: both,
viewed as tempered distributions, act on a complex Schwartz `Ψ` by `∫ (𝓕Ψ)·g = ∫ Ψ·(𝓕g)` — the multiplication
formula (`real_fourier_mul_formula`) — so the distributions agree, and `ae_eq_of_integral_contDiff_smul_eq`
(distribution injectivity) gives the a.e. equality.  This is the bridge that imports Mathlib's `L²` Plancherel
isometry (`Lp.inner_fourier_eq`) into the classical-`𝓕` Parseval pairing, discharging `hFdA`. -/
theorem fourier_lp_ae_eq {g : ℝ → ℂ} (h1 : Integrable g volume) (h2 : MemLp g 2 volume) :
    ⇑(𝓕 (h2.toLp) : Lp ℂ 2 volume) =ᵐ[volume] 𝓕 g := by
  have hg_cont : Continuous (𝓕 g) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ h1
  set F2 : Lp ℂ 2 volume := 𝓕 (h2.toLp) with hF2
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable one_le_two) hg_cont.locallyIntegrable
    (fun ψ hψd hψs => ?_)
  -- coerce the real test function ψ to a complex Schwartz function Ψ
  set Ψ : 𝓢(ℝ, ℂ) := (hψs.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hψd) with hΨ
  have hΨcoe : ⇑Ψ = fun x => (ψ x : ℂ) := rfl
  have hgLp : ⇑(h2.toLp) =ᵐ[volume] g := h2.coeFn_toLp
  have hps : ∀ (x : ℝ) (w : ℂ), ψ x • w = Ψ x • w := fun x w => by
    simp only [hΨcoe, Complex.real_smul, smul_eq_mul]
  calc ∫ x, ψ x • (⇑F2) x
      = ∫ x, Ψ x • (⇑F2) x := by simp_rw [hps]
    _ = Lp.toTemperedDistribution F2 Ψ := (Lp.toTemperedDistribution_apply _ _).symm
    _ = Lp.toTemperedDistribution (h2.toLp) (𝓕 Ψ) := by
        rw [hF2, ← TemperedDistribution.fourier_apply]
        exact DFunLike.congr_fun (Lp.fourier_toTemperedDistribution_eq (h2.toLp)).symm Ψ
    _ = ∫ x, (𝓕 Ψ) x • (⇑(h2.toLp) : ℝ → ℂ) x := Lp.toTemperedDistribution_apply _ _
    _ = ∫ x, 𝓕 (⇑Ψ) x * g x := by
        refine integral_congr_ae ?_
        filter_upwards [hgLp] with x hx
        rw [smul_eq_mul, hx, ← SchwartzMap.fourier_coe]
    _ = ∫ x, (⇑Ψ) x * 𝓕 g x := real_fourier_mul_formula _ g Ψ.integrable h1
    _ = ∫ x, ψ x • 𝓕 g x := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        show (⇑Ψ) x * 𝓕 g x = ψ x • 𝓕 g x
        rw [hps x (𝓕 g x), smul_eq_mul]

/-- **★★★★ Plancherel pairing for the classical Fourier transform** — the inversion-free conjugate Parseval.
    For `A, B ∈ L¹ ∩ L²`, `∫ conj(𝓕A)·𝓕B = ∫ conj(A)·B`.  Proved from Mathlib's `L²` Plancherel isometry
    (`Lp.inner_fourier_eq`) + the coincidence `fourier_lp_ae_eq` (classical `𝓕` = `L²` `𝓕` a.e.) — needing only
    `L¹ ∩ L²` membership, NOT Fourier inversion (`Continuous.fourierInv_fourier_eq`) and hence NOT
    `Integrable (𝓕 B)` (`hFdA`).  This is the drop-in replacement for `fourier_conj_parseval` that closes Route B. -/
theorem fourier_conj_parseval_L2 {A B : ℝ → ℂ}
    (h1A : Integrable A volume) (h2A : MemLp A 2 volume)
    (h1B : Integrable B volume) (h2B : MemLp B 2 volume) :
    ∫ w, (starRingEnd ℂ) (𝓕 A w) * 𝓕 B w = ∫ x, (starRingEnd ℂ) (A x) * B x := by
  have hcA := fourier_lp_ae_eq h1A h2A
  have hcB := fourier_lp_ae_eq h1B h2B
  set A2 : Lp ℂ 2 volume := h2A.toLp with hA2def
  set B2 : Lp ℂ 2 volume := h2B.toLp with hB2def
  set FA2 : Lp ℂ 2 volume := 𝓕 A2 with hFA2
  set FB2 : Lp ℂ 2 volume := 𝓕 B2 with hFB2
  calc ∫ w, (starRingEnd ℂ) (𝓕 A w) * 𝓕 B w
      = ∫ a, (starRingEnd ℂ) ((⇑FA2) a) * (⇑FB2) a := by
        refine integral_congr_ae ?_
        filter_upwards [hcA, hcB] with a ha hb; rw [ha, hb]
    _ = (inner ℂ FA2 FB2 : ℂ) := by
        rw [L2.inner_def]
        refine integral_congr_ae (.of_forall fun a => ?_)
        simp only [RCLike.inner_apply, mul_comm]
    _ = (inner ℂ A2 B2 : ℂ) := MeasureTheory.Lp.inner_fourier_eq _ _
    _ = ∫ a, (starRingEnd ℂ) ((⇑A2) a) * (⇑B2) a := by
        rw [L2.inner_def]
        refine integral_congr_ae (.of_forall fun a => ?_)
        simp only [RCLike.inner_apply, mul_comm]
    _ = ∫ x, (starRingEnd ℂ) (A x) * B x := by
        refine integral_congr_ae ?_
        filter_upwards [h2A.coeFn_toLp, h2B.coeFn_toLp] with x ha hb; rw [ha, hb]

/-! ### The L²-Plancherel chain — re-derivation of the Parseval chain with no Fourier inversion.

Each lemma mirrors its `HorizonParseval` counterpart but threads `MemLp · 2` (`A, A' ∈ L²`) instead of the
inversion hypotheses `(hdAc, hFdA)`.  The bottom of the chain (`fourier_parseval_deriv_L2`) calls
`fourier_conj_parseval_L2`.  This closes the last Route-B gate `hFdA`. -/

/-- `fourier_parseval_deriv` with `L²` membership instead of `(hdAc, hFdA)`. -/
theorem fourier_parseval_deriv_L2 (A : ℝ → ℂ)
    (hA : Integrable A) (hAd : Differentiable ℝ A) (hdA : Integrable (deriv A))
    (h2A : MemLp A 2 volume) (h2dA : MemLp (deriv A) 2 volume)
    (hff : Integrable (fun θ => (starRingEnd ℂ) (A θ) * A θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv A θ) * A θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (A θ) * deriv A θ)) :
    ∫ w, (starRingEnd ℂ) (𝓕 A w) * 𝓕 (deriv A) w
      = Complex.I * (rapidityMomentum A (deriv A) : ℂ) := by
  rw [fourier_conj_parseval_L2 hA h2A hdA h2dA]
  exact inner_deriv_eq_I_mul_rapidityMomentum A (deriv A) (fun x => (hAd x).hasDerivAt) hff h1 h2

/-- `fourier_weighted_pairing` with `L²` membership. -/
theorem fourier_weighted_pairing_L2 (A : ℝ → ℂ)
    (hA : Integrable A) (hAd : Differentiable ℝ A) (hdA : Integrable (deriv A))
    (h2A : MemLp A 2 volume) (h2dA : MemLp (deriv A) 2 volume)
    (hff : Integrable (fun θ => (starRingEnd ℂ) (A θ) * A θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv A θ) * A θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (A θ) * deriv A θ)) :
    ∫ w, (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w)
      = (1 / (2 * Real.pi) : ℂ) * (rapidityMomentum A (deriv A) : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hpd := fourier_parseval_deriv_L2 A hA hAd hdA h2A h2dA hff h1 h2
  have hstep : (∫ w, (starRingEnd ℂ) (𝓕 A w) * 𝓕 (deriv A) w)
      = (2 * (Real.pi : ℂ) * Complex.I)
          * ∫ w, (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    rw [fourier_deriv hA hAd hdA]
    simp only [smul_eq_mul]; ring
  rw [hstep] at hpd
  refine mul_left_cancel₀ h2pi ?_
  rw [hpd]; field_simp

/-- `weighted_pairing_real` with `L²` membership. -/
theorem weighted_pairing_real_L2 (A : ℝ → ℂ)
    (hA : Integrable A) (hAd : Differentiable ℝ A) (hdA : Integrable (deriv A))
    (h2A : MemLp A 2 volume) (h2dA : MemLp (deriv A) 2 volume)
    (hff : Integrable (fun θ => (starRingEnd ℂ) (A θ) * A θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv A θ) * A θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (A θ) * deriv A θ)) :
    ∫ w, w * ‖𝓕 A w‖ ^ 2 = (1 / (2 * Real.pi)) * rapidityMomentum A (deriv A) := by
  have hnorm : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hwp := fourier_weighted_pairing_L2 A hA hAd hdA h2A h2dA hff h1 h2
  have ha : (∫ w, (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w))
      = ((∫ w, w * ‖𝓕 A w‖ ^ 2 : ℝ) : ℂ) := by
    have hc : (∫ w, (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w))
        = ∫ w, ((w * ‖𝓕 A w‖ ^ 2 : ℝ) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
      show (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w) = ((w * ‖𝓕 A w‖ ^ 2 : ℝ) : ℂ)
      rw [show (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w)
            = (w : ℂ) * ((starRingEnd ℂ) (𝓕 A w) * 𝓕 A w) from by ring, hnorm (𝓕 A w)]
      push_cast; ring
    rw [hc]; exact integral_ofReal
  rw [ha] at hwp
  exact_mod_cast hwp

/-- `flux_integral_eq` with `L²` membership. -/
theorem flux_integral_eq_L2 (A : ℝ → ℂ)
    (hA : Integrable A) (hAd : Differentiable ℝ A) (hdA : Integrable (deriv A))
    (h2A : MemLp A 2 volume) (h2dA : MemLp (deriv A) 2 volume)
    (hff : Integrable (fun θ => (starRingEnd ℂ) (A θ) * A θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv A θ) * A θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (A θ) * deriv A θ)) :
    ∫ lam, lam * ‖𝓕 A (lam / (2 * Real.pi))‖ ^ 2 = 2 * Real.pi * rapidityMomentum A (deriv A) := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : (2 * Real.pi) ≠ 0 := hpos.ne'
  set φ : ℝ → ℝ := fun lam => lam * ‖𝓕 A (lam / (2 * Real.pi))‖ ^ 2 with hφ
  have hphi : ∀ x, φ (2 * Real.pi * x) = 2 * Real.pi * (x * ‖𝓕 A x‖ ^ 2) := by
    intro x
    simp only [hφ]
    rw [show (2 * Real.pi * x) / (2 * Real.pi) = x from by
      rw [mul_comm, mul_div_assoc, div_self hne, mul_one]]
    ring
  have hlem := Measure.integral_comp_mul_left φ (2 * Real.pi)
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), smul_eq_mul] at hlem
  simp only [hphi] at hlem
  rw [integral_const_mul] at hlem
  have hwpr := weighted_pairing_real_L2 A hA hAd hdA h2A h2dA hff h1 h2
  rw [show (∫ lam, φ lam) = 2 * Real.pi * (2 * Real.pi * ∫ x, x * ‖𝓕 A x‖ ^ 2) from by
    rw [hlem, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]]
  rw [hwpr]; field_simp

/-- `stressFluxKK_eq_rapMom` with `L²` membership. -/
theorem stressFluxKK_eq_rapMom_L2 (m : ℝ) (hm : 0 < m) (f : V → ℂ)
    (hA : Integrable (horizonAmp m f)) (hAd : Differentiable ℝ (horizonAmp m f))
    (hdA : Integrable (deriv (horizonAmp m f)))
    (h2A : MemLp (horizonAmp m f) 2 volume) (h2dA : MemLp (deriv (horizonAmp m f)) 2 volume)
    (hff : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * horizonAmp m f θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv (horizonAmp m f) θ) * horizonAmp m f θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * deriv (horizonAmp m f) θ)) :
    stressFluxKK m f
      = 2 * Real.pi * rapidityMomentum (horizonAmp m f) (deriv (horizonAmp m f)) := by
  have hint : (∫ lam, lam * Tkk m f lam)
      = ∫ lam, lam * ‖𝓕 (horizonAmp m f) (lam / (2 * Real.pi))‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun lam => ?_))
    show lam * ‖horizonFieldDeriv m f lam‖ ^ 2
      = lam * ‖𝓕 (horizonAmp m f) (lam / (2 * Real.pi))‖ ^ 2
    rw [horizonFieldDeriv_eq_fourier m hm f lam]
  rw [show stressFluxKK m f = ∫ lam, lam * Tkk m f lam from rfl, hint]
  exact flux_integral_eq_L2 (horizonAmp m f) hA hAd hdA h2A h2dA hff h1 h2

/-- `stressFluxKK_eq_neg_rapMom` with `L²` membership and the wedge derivative discharged. -/
theorem stressFluxKK_eq_neg_rapMom_L2 (m : ℝ) (hm : 0 < m) (f : V → ℂ) (kd : ℝ → ℂ)
    (hkd : ∀ θ, HasDerivAt (fun θ => Krep m f θ) (kd θ) θ)
    (hA : Integrable (horizonAmp m f)) (hAd : Differentiable ℝ (horizonAmp m f))
    (hdA : Integrable (deriv (horizonAmp m f)))
    (h2A : MemLp (horizonAmp m f) 2 volume) (h2dA : MemLp (deriv (horizonAmp m f)) 2 volume)
    (hff : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * horizonAmp m f θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv (horizonAmp m f) θ) * horizonAmp m f θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * deriv (horizonAmp m f) θ)) :
    stressFluxKK m f = -(2 * Real.pi) * rapidityMomentum (fun θ => Krep m f θ) kd := by
  have hrel : rapidityMomentum (horizonAmp m f) (deriv (horizonAmp m f))
      = - rapidityMomentum (fun θ => Krep m f θ) kd := by
    simp only [rapidityMomentum]
    rw [horizonAmp_inner_deriv m hm f kd hkd, Complex.neg_im]
  rw [stressFluxKK_eq_rapMom_L2 m hm f hA hAd hdA h2A h2dA hff h1 h2, hrel]; ring

/-- **★★★★★ Route B, FULLY CLOSED for the Schwartz class.**  For any Schwartz test function `f` (`m > 0`),
    `stressFluxKK m f = −2π·rapidityMomentum(Krep)(Krep')` — with NO remaining hypotheses.  The last gate
    `hFdA` is gone: the Parseval pairing is proven by the `L²` Plancherel isometry (`fourier_conj_parseval_L2`),
    which needs only `horizonAmp, deriv(horizonAmp) ∈ L²` (`horizonAmp_memLp_two` / `horizonAmp_deriv_memLp_two`),
    both already proven.  The free-field horizon stress flux equals the boost momentum, unconditionally. -/
theorem stressFluxKK_eq_neg_rapMom_schwartz_closed {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    stressFluxKK m (⇑f) = -(2 * Real.pi) *
      rapidityMomentum (fun θ => Krep m (⇑f) θ) (deriv (fun θ => Krep m (⇑f) θ)) := by
  have hkd : ∀ θ, HasDerivAt (fun θ => Krep m (⇑f) θ) (deriv (fun θ => Krep m (⇑f) θ) θ) θ := fun θ =>
    (schwartz_Krep_hasDerivAt m hm.le f θ).differentiableAt.hasDerivAt
  exact stressFluxKK_eq_neg_rapMom_L2 m hm (⇑f) (deriv (fun θ => Krep m (⇑f) θ)) hkd
    (horizonAmp_integrable hm f) (horizonAmp_differentiable hm f _ hkd)
    (horizonAmp_deriv_integrable hm f) (horizonAmp_memLp_two hm f) (horizonAmp_deriv_memLp_two hm f)
    (horizonAmp_sq_integrable hm f) (horizonAmp_deriv_mul_integrable hm f)
    (horizonAmp_mul_deriv_integrable hm f)

/-- **★★★★★ The `hTkk` scalar, FULLY CLOSED for the Schwartz class.**  The GR-bridge form: the boost energy of
    the wedge mode `(2π·∫conj(Krep)·Krep').im` equals `−stressFluxKK m f` for ANY Schwartz `f`, with no
    hypotheses.  Defining the GR chain's stress scalar by `T_kk := −(ℏ/2π)·stressFluxKK` makes the labelled
    `hTkk` an unconditional theorem: the bundled scalar IS the proven free-field horizon stress flux. -/
theorem boostEnergy_eq_neg_stressFlux_schwartz_closed {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    (2 * Real.pi * ∫ θ, (starRingEnd ℂ) (Krep m (⇑f) θ) * deriv (fun θ => Krep m (⇑f) θ) θ).im
      = - stressFluxKK m (⇑f) := by
  rw [stressFluxKK_eq_neg_rapMom_schwartz_closed hm f]
  simp only [rapidityMomentum, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

end QIQTH.Fock.StressTensor
