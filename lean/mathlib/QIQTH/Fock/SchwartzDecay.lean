/-
  K-localization — general Schwartz `1/cosh` decay (per GPT-5.5-pro next-step #1).

  Upgrades the localizable-test class of the mass-shell localization map `K`
  (`QIQTH.Fock.Localization`) from the single Gaussian instance to **all Schwartz functions**.

  The analytic input is the sharp decay bound

      ‖minkowskiFourier f (massShell m θ)‖ ≤ C / cosh θ      (any Schwartz f, m ≠ 0)

  obtained by writing the bespoke (no-2π Minkowski-pairing) transform as a
  `VectorFourier.fourierIntegral` for the continuous bilinear form
  `L v w = (v₀ w₀ − v₁ w₁) / (2π)` and invoking Mathlib's Fourier-decay estimate
  `VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le` (which performs the integration by
  parts).  The test vector `v = (p₀, −p₁)` extracts `L v p = (p₀² + p₁²)/(2π)`, and on the mass
  shell `p₀² + p₁² = m²(cosh²θ + sinh²θ) ≥ m² cosh²θ`, giving the `1/cosh` decay.

  Combined with `Krep_memLp_of_decay` this gives `Krep m f ∈ L²(ℝ)` for every Schwartz `f`, hence a
  non-degenerate `LocalTest` (`schwartzLocalTest`) on the full Schwartz class — the honest "local test
  class" GPT's audit asked for, replacing the Gaussian-only witness.  Axiom-free.
-/
import QIQTH.Fock.Localization
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

noncomputable section

open Real MeasureTheory Complex

namespace QIQTH.Fock.Localization

open scoped FourierTransform

/-- The continuous bilinear Minkowski pairing rescaled by `1/(2π)`:
`L v w = (v₀ w₀ − v₁ w₁) / (2π)`.  Writing the bespoke `minkowskiFourier` as a
`VectorFourier.fourierIntegral` for this `L` lets us borrow Mathlib's Fourier-decay machinery. -/
def minkBilin : V →L[ℝ] V →L[ℝ] ℝ :=
  (1 / (2 * π)) •
    (((ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ))
      - ((ContinuousLinearMap.proj 1 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 1 : V →L[ℝ] ℝ)))

@[simp] theorem minkBilin_apply (v w : V) :
    minkBilin v w = (v 0 * w 0 - v 1 * w 1) / (2 * π) := by
  simp only [minkBilin, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

/-- **Bridge**: the bespoke Minkowski-Fourier transform IS a `VectorFourier.fourierIntegral` for the
bilinear form `minkBilin` (with the standard `2π` Fourier character).  This is what lets us import
Mathlib's decay estimates. -/
theorem minkowskiFourier_eq_fourierIntegral (f : V → ℂ) (p : V) :
    minkowskiFourier f p
      = VectorFourier.fourierIntegral Real.fourierChar volume minkBilin.toLinearMap₁₂ f p := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [minkowskiFourier, VectorFourier.fourierIntegral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hscal : (Real.fourierChar (-(minkBilin.toLinearMap₁₂ x p)) : ℂ)
      = Complex.exp (-Complex.I * ((minkowskiDot p x : ℝ) : ℂ)) := by
    rw [ContinuousLinearMap.toLinearMap₁₂_apply, minkBilin_apply, Real.fourierChar_apply,
      minkowskiDot]
    congr 1
    push_cast
    field_simp
  simp only [Circle.smul_def, smul_eq_mul, hscal]

/-- `|sinh θ| ≤ cosh θ`. -/
theorem abs_sinh_le_cosh (θ : ℝ) : |Real.sinh θ| ≤ Real.cosh θ := by
  rw [abs_le]
  constructor <;>
    nlinarith [Real.cosh_sq θ, Real.cosh_pos θ, Real.sinh_sq θ,
      sq_nonneg (Real.cosh θ - Real.sinh θ), sq_nonneg (Real.cosh θ + Real.sinh θ)]

/-- **General Schwartz `1/cosh` decay** of the localized amplitude.  For any Schwartz `f` and `m ≠ 0`,
`‖Krep m f θ‖ ≤ C · (cosh θ)⁻¹` with `C = 4πS / (√2·|m|)`, where
`S = ∫‖f‖ + ∫‖D f‖` is a finite Schwartz constant.  Hence `Krep m f ∈ L²(ℝ)`. -/
theorem schwartz_Krep_memLp (f : SchwartzMap V ℂ) {m : ℝ} (hm : m ≠ 0) :
    MemLp (Krep m (⇑f)) 2 (volume : Measure ℝ) := by
  -- the finite Schwartz constant `S = ∫‖f‖ + ∫‖Df‖` (Mathlib's decay sum at k=0, n=1, expanded)
  set S : ℝ := (∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖) with hSdef
  have hSnonneg : 0 ≤ S := by
    rw [hSdef]; positivity
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hmabs : (0 : ℝ) < |m| := abs_pos.mpr hm
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  refine Krep_memLp_of_decay (f.integrable) (C := 4 * π * S / (Real.sqrt 2 * |m|)) (fun θ => ?_)
  -- abbreviations on the mass shell
  have hcosh : (0 : ℝ) < Real.cosh θ := Real.cosh_pos θ
  set p : V := massShell m θ with hp
  set v : V := ![p 0, -(p 1)] with hv
  -- Mathlib's Fourier-decay estimate, specialized to k = 0, n = 1 and the test vector v
  have key := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    (L := minkBilin) (μ := (volume : Measure V)) (f := (⇑f))
    (f.smooth ⊤) (fun k n _ _ => SchwartzMap.integrable_pow_mul_iteratedFDeriv volume f k n)
    (k := 0) (n := 1) le_top le_top v p
  -- fold the (k=0,n=1) decay sum into `S`
  have hsum : (∑ q ∈ Finset.range (0 + 1) ×ˢ Finset.range (1 + 1),
      ∫ w, ‖w‖ ^ q.1 * ‖iteratedFDeriv ℝ q.2 (⇑f) w‖) = S := by
    rw [hSdef, Finset.sum_product]
    simp [Finset.sum_range_succ, norm_iteratedFDeriv_zero]
  rw [hsum] at key
  -- simplify the constants, turn `iteratedFDeriv 0` into evaluation, rewrite back to `minkowskiFourier`
  simp only [pow_one, pow_zero, mul_one, norm_iteratedFDeriv_zero, Nat.cast_zero, mul_zero,
    zero_add] at key
  rw [← minkowskiFourier_eq_fourierIntegral] at key
  -- value of the bilinear form at the test vector: L v p = (p₀² + p₁²)/(2π)
  have hLvp : minkBilin v p = (p 0 ^ 2 + p 1 ^ 2) / (2 * π) := by
    rw [minkBilin_apply, hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hLvp, abs_of_nonneg (by positivity)] at key
  -- name the amplitude norm and the squared-momentum `A`
  set mF : ℝ := ‖minkowskiFourier (⇑f) p‖ with hmF
  have hmFnn : (0 : ℝ) ≤ mF := norm_nonneg _
  set A : ℝ := p 0 ^ 2 + p 1 ^ 2 with hA
  -- key now reads:  A/(2π) * mF ≤ ‖v‖ * 2 * S
  -- ‖v‖ ≤ |m| cosh θ
  have h0 : ‖v 0‖ ≤ |m| * Real.cosh θ := by
    have h : ‖v 0‖ = |m| * Real.cosh θ := by
      simp only [hv, Matrix.cons_val_zero, hp, massShell_zero, Real.norm_eq_abs, abs_mul,
        abs_of_pos hcosh]
    exact h.le
  have h1 : ‖v 1‖ ≤ |m| * Real.cosh θ := by
    rw [hv]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, hp, massShell_one,
      abs_neg, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_sinh_le_cosh θ) (abs_nonneg m)
  have hvnorm : ‖v‖ ≤ |m| * Real.cosh θ := by
    rw [pi_norm_le_iff_of_nonneg (by positivity), Fin.forall_fin_two]
    exact ⟨h0, h1⟩
  -- lower bound A ≥ (|m| cosh θ)²
  have ht : (0 : ℝ) < |m| * Real.cosh θ := by positivity
  have hAlb : (|m| * Real.cosh θ) ^ 2 ≤ A := by
    rw [hA, hp]
    simp only [massShell_zero, massShell_one, mul_pow, sq_abs]
    nlinarith [mul_nonneg (sq_nonneg m) (sq_nonneg (Real.sinh θ))]
  -- (1) bound ‖v‖ by |m|cosh θ:  A/(2π) * mF ≤ |m|cosh θ * 2 * S
  have key2 : A / (2 * π) * mF ≤ |m| * Real.cosh θ * 2 * S :=
    le_trans key
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hvnorm (by norm_num)) hSnonneg)
  -- (2) clear the 1/(2π):  A * mF ≤ 4πS · (|m|cosh θ)
  have key3 : A * mF ≤ 4 * π * S * (|m| * Real.cosh θ) := by
    have h := mul_le_mul_of_nonneg_right key2 hpi.le
    have e1 : A / (2 * π) * mF * (2 * π) = A * mF := by field_simp
    rw [e1] at h
    exact le_trans h (le_of_eq (by ring))
  -- (3) use A ≥ (|m|cosh θ)²:  mF · (|m|cosh θ) ≤ 4πS
  have hclean : mF * (|m| * Real.cosh θ) ≤ 4 * π * S := by
    nlinarith [key3, mul_le_mul_of_nonneg_left hAlb hmFnn, ht, hmFnn]
  -- (4) the decay bound on the amplitude
  have hmFbound : mF ≤ 4 * π * S / (|m| * Real.cosh θ) := by
    rw [le_div_iff₀ ht]; exact hclean
  -- transfer to Krep
  have hc : ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [show (1 / Real.sqrt 2 : ℂ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  show ‖(1 / Real.sqrt 2 : ℂ) * minkowskiFourier (⇑f) p‖ ≤ _
  rw [norm_mul, hc, ← hmF]
  calc 1 / Real.sqrt 2 * mF
      ≤ 1 / Real.sqrt 2 * (4 * π * S / (|m| * Real.cosh θ)) :=
        mul_le_mul_of_nonneg_left hmFbound (by positivity)
    _ = 4 * π * S / (Real.sqrt 2 * |m|) * (Real.cosh θ)⁻¹ := by
        rw [div_mul_eq_mul_div]; field_simp

/-- **A non-degenerate `LocalTest` from any Schwartz function** (`m ≠ 0`): the honest "local test
class" — every Schwartz spacetime test function is `L²`-admissible for the mass-shell localization. -/
def schwartzLocalTest (f : SchwartzMap V ℂ) {m : ℝ} (hm : m ≠ 0) : LocalTest m where
  f := ⇑f
  memLp := schwartz_Krep_memLp f hm

end QIQTH.Fock.Localization
