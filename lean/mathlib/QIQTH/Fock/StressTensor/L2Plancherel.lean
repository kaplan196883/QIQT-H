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

end QIQTH.Fock.StressTensor
