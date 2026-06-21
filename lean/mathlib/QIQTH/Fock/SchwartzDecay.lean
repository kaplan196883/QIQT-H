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
import Mathlib.Analysis.Distribution.TemperateGrowth

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

/-- **General Schwartz `1/cosh²` decay** of the localized amplitude (one derivative more than
`schwartz_Krep_memLp`).  For any Schwartz `f` and `m ≠ 0`,
`‖Krep m f θ‖ ≤ 16π²·S₂/(√2·m²) · (cosh θ)⁻²` with `S₂ = ∫‖f‖ + ∫‖Df‖ + ∫‖D²f‖`.  The `(cosh θ)⁻²` decay
(via the `n = 2` Fourier-decay estimate) is what makes the horizon amplitude `L¹` and differentiable at the
bifurcation surface `x = 0` (the softer Route-B regularity). -/
theorem schwartz_Krep_decay_sq (f : SchwartzMap V ℂ) {m : ℝ} (hm : m ≠ 0) (θ : ℝ) :
    ‖Krep m (⇑f) θ‖
      ≤ 16 * π ^ 2 * ((∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
          + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖)) / (Real.sqrt 2 * m ^ 2) * ((Real.cosh θ) ^ 2)⁻¹ := by
  set S : ℝ := (∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖) with hSdef
  have hSnonneg : 0 ≤ S := by rw [hSdef]; positivity
  have hcosh : (0 : ℝ) < Real.cosh θ := Real.cosh_pos θ
  set p : V := massShell m θ with hp
  set v : V := ![p 0, -(p 1)] with hv
  have key := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    (L := minkBilin) (μ := (volume : Measure V)) (f := (⇑f))
    (f.smooth ⊤) (fun k n _ _ => SchwartzMap.integrable_pow_mul_iteratedFDeriv volume f k n)
    (k := 0) (n := 2) le_top le_top v p
  have hsum : (∑ q ∈ Finset.range (0 + 1) ×ˢ Finset.range (2 + 1),
      ∫ w, ‖w‖ ^ q.1 * ‖iteratedFDeriv ℝ q.2 (⇑f) w‖) = S := by
    rw [hSdef, Finset.sum_product]
    simp [Finset.sum_range_succ, norm_iteratedFDeriv_zero]
  rw [hsum] at key
  simp only [pow_zero, mul_one, norm_iteratedFDeriv_zero, Nat.cast_zero, mul_zero, zero_add] at key
  rw [← minkowskiFourier_eq_fourierIntegral] at key
  have hLvp : minkBilin v p = (p 0 ^ 2 + p 1 ^ 2) / (2 * π) := by
    rw [minkBilin_apply, hv]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
  rw [hLvp, abs_of_nonneg (by positivity)] at key
  set mF : ℝ := ‖minkowskiFourier (⇑f) p‖ with hmF
  have hmFnn : (0 : ℝ) ≤ mF := norm_nonneg _
  set A : ℝ := p 0 ^ 2 + p 1 ^ 2 with hA
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
  have ht : (0 : ℝ) < |m| * Real.cosh θ := by positivity
  have hAlb : (|m| * Real.cosh θ) ^ 2 ≤ A := by
    rw [hA, hp]
    simp only [massShell_zero, massShell_one, mul_pow, sq_abs]
    nlinarith [mul_nonneg (sq_nonneg m) (sq_nonneg (Real.sinh θ))]
  have hv2 : ‖v‖ ^ 2 ≤ (|m| * Real.cosh θ) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hvnorm 2
  have key2 : (A / (2 * π)) ^ 2 * mF ≤ (|m| * Real.cosh θ) ^ 2 * 2 ^ 2 * S :=
    le_trans key
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv2 (by norm_num)) hSnonneg)
  have key3 : A ^ 2 * mF ≤ (|m| * Real.cosh θ) ^ 2 * (2 ^ 2 * (2 * π) ^ 2) * S := by
    have h := mul_le_mul_of_nonneg_right key2 (sq_nonneg (2 * π))
    have e1 : (A / (2 * π)) ^ 2 * mF * (2 * π) ^ 2 = A ^ 2 * mF := by field_simp
    rw [e1] at h
    calc A ^ 2 * mF ≤ (|m| * Real.cosh θ) ^ 2 * 2 ^ 2 * S * (2 * π) ^ 2 := h
      _ = (|m| * Real.cosh θ) ^ 2 * (2 ^ 2 * (2 * π) ^ 2) * S := by ring
  have hclean : mF * (|m| * Real.cosh θ) ^ 2 ≤ (2 ^ 2 * (2 * π) ^ 2) * S := by
    have hA2 : (|m| * Real.cosh θ) ^ 2 * (|m| * Real.cosh θ) ^ 2 ≤ A * A :=
      mul_le_mul hAlb hAlb (by positivity) (le_trans (by positivity) hAlb)
    have hchain : (|m| * Real.cosh θ) ^ 2 * ((|m| * Real.cosh θ) ^ 2 * mF)
        ≤ (|m| * Real.cosh θ) ^ 2 * ((2 ^ 2 * (2 * π) ^ 2) * S) :=
      calc (|m| * Real.cosh θ) ^ 2 * ((|m| * Real.cosh θ) ^ 2 * mF)
          = ((|m| * Real.cosh θ) ^ 2 * (|m| * Real.cosh θ) ^ 2) * mF := by ring
        _ ≤ (A * A) * mF := mul_le_mul_of_nonneg_right hA2 hmFnn
        _ = A ^ 2 * mF := by ring
        _ ≤ (|m| * Real.cosh θ) ^ 2 * (2 ^ 2 * (2 * π) ^ 2) * S := key3
        _ = (|m| * Real.cosh θ) ^ 2 * ((2 ^ 2 * (2 * π) ^ 2) * S) := by ring
    have := le_of_mul_le_mul_left hchain (by positivity : (0 : ℝ) < (|m| * Real.cosh θ) ^ 2)
    linarith
  have hmFbound : mF ≤ (2 ^ 2 * (2 * π) ^ 2) * S / (|m| * Real.cosh θ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact hclean
  have hc : ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [show (1 / Real.sqrt 2 : ℂ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  show ‖(1 / Real.sqrt 2 : ℂ) * minkowskiFourier (⇑f) p‖ ≤ _
  rw [norm_mul, hc, ← hmF]
  calc 1 / Real.sqrt 2 * mF
      ≤ 1 / Real.sqrt 2 * ((2 ^ 2 * (2 * π) ^ 2) * S / (|m| * Real.cosh θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hmFbound (by positivity)
    _ = 16 * π ^ 2 * S / (Real.sqrt 2 * m ^ 2) * ((Real.cosh θ) ^ 2)⁻¹ := by
        rw [show (|m| * Real.cosh θ) ^ 2 = m ^ 2 * (Real.cosh θ) ^ 2 from by rw [mul_pow, sq_abs]]
        field_simp
        ring

/-- **Schwartz `1/cosh³` decay** of the localized amplitude (the `n = 3` Fourier-decay estimate, one
derivative more than `schwartz_Krep_decay_sq`).  For any Schwartz `f` and `m ≠ 0`,
`∃ C ≥ 0, ‖Krep m f θ‖ ≤ C · (cosh θ)⁻³`.  The extra power is what gives the rapidity derivative `Krep'` the
SUPER-exponential `(cosh)⁻²` decay (`kd ~ cosh · cosh⁻³`), needed for the continuity of `deriv (horizonAmp)`
at the bifurcation surface `x = 0` (the `hdAc` gate). -/
theorem schwartz_Krep_decay_cube (f : SchwartzMap V ℂ) {m : ℝ} (hm : m ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, ‖Krep m (⇑f) θ‖ ≤ C * ((Real.cosh θ) ^ 3)⁻¹ := by
  set S : ℝ := (∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 3 (⇑f) v‖) with hSdef
  have hSnonneg : 0 ≤ S := by rw [hSdef]; positivity
  have hmabs : (0 : ℝ) < |m| := abs_pos.mpr hm
  refine ⟨2 ^ 3 * (2 * π) ^ 3 * S / (Real.sqrt 2 * |m| ^ 3),
    div_nonneg (mul_nonneg (by positivity) hSnonneg) (by positivity), fun θ => ?_⟩
  have hcosh : (0 : ℝ) < Real.cosh θ := Real.cosh_pos θ
  set p : V := massShell m θ with hp
  set v : V := ![p 0, -(p 1)] with hv
  have key := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    (L := minkBilin) (μ := (volume : Measure V)) (f := (⇑f))
    (f.smooth ⊤) (fun k n _ _ => SchwartzMap.integrable_pow_mul_iteratedFDeriv volume f k n)
    (k := 0) (n := 3) le_top le_top v p
  have hsum : (∑ q ∈ Finset.range (0 + 1) ×ˢ Finset.range (3 + 1),
      ∫ w, ‖w‖ ^ q.1 * ‖iteratedFDeriv ℝ q.2 (⇑f) w‖) = S := by
    rw [hSdef, Finset.sum_product]
    simp [Finset.sum_range_succ, norm_iteratedFDeriv_zero]
  rw [hsum] at key
  simp only [pow_zero, mul_one, norm_iteratedFDeriv_zero, Nat.cast_zero, mul_zero, zero_add] at key
  rw [← minkowskiFourier_eq_fourierIntegral] at key
  have hLvp : minkBilin v p = (p 0 ^ 2 + p 1 ^ 2) / (2 * π) := by
    rw [minkBilin_apply, hv]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
  rw [hLvp, abs_of_nonneg (by positivity)] at key
  set mF : ℝ := ‖minkowskiFourier (⇑f) p‖ with hmF
  have hmFnn : (0 : ℝ) ≤ mF := norm_nonneg _
  set A : ℝ := p 0 ^ 2 + p 1 ^ 2 with hA
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
  have hAlb : (|m| * Real.cosh θ) ^ 2 ≤ A := by
    rw [hA, hp]
    simp only [massShell_zero, massShell_one, mul_pow, sq_abs]
    nlinarith [mul_nonneg (sq_nonneg m) (sq_nonneg (Real.sinh θ))]
  have hv3 : ‖v‖ ^ 3 ≤ (|m| * Real.cosh θ) ^ 3 := pow_le_pow_left₀ (norm_nonneg v) hvnorm 3
  have key2 : (A / (2 * π)) ^ 3 * mF ≤ (|m| * Real.cosh θ) ^ 3 * 2 ^ 3 * S :=
    le_trans key
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv3 (by norm_num)) hSnonneg)
  have key3 : A ^ 3 * mF ≤ (|m| * Real.cosh θ) ^ 3 * (2 ^ 3 * (2 * π) ^ 3) * S := by
    have h := mul_le_mul_of_nonneg_right key2 (by positivity : (0 : ℝ) ≤ (2 * π) ^ 3)
    have e1 : (A / (2 * π)) ^ 3 * mF * (2 * π) ^ 3 = A ^ 3 * mF := by field_simp
    rw [e1] at h
    calc A ^ 3 * mF ≤ (|m| * Real.cosh θ) ^ 3 * 2 ^ 3 * S * (2 * π) ^ 3 := h
      _ = (|m| * Real.cosh θ) ^ 3 * (2 ^ 3 * (2 * π) ^ 3) * S := by ring
  have hclean : mF * (|m| * Real.cosh θ) ^ 3 ≤ (2 ^ 3 * (2 * π) ^ 3) * S := by
    have hA3 : ((|m| * Real.cosh θ) ^ 2) ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ (by positivity) hAlb 3
    have hchain : (|m| * Real.cosh θ) ^ 3 * ((|m| * Real.cosh θ) ^ 3 * mF)
        ≤ (|m| * Real.cosh θ) ^ 3 * ((2 ^ 3 * (2 * π) ^ 3) * S) :=
      calc (|m| * Real.cosh θ) ^ 3 * ((|m| * Real.cosh θ) ^ 3 * mF)
          = ((|m| * Real.cosh θ) ^ 2) ^ 3 * mF := by ring
        _ ≤ A ^ 3 * mF := mul_le_mul_of_nonneg_right hA3 hmFnn
        _ ≤ (|m| * Real.cosh θ) ^ 3 * (2 ^ 3 * (2 * π) ^ 3) * S := key3
        _ = (|m| * Real.cosh θ) ^ 3 * ((2 ^ 3 * (2 * π) ^ 3) * S) := by ring
    have := le_of_mul_le_mul_left hchain (by positivity : (0 : ℝ) < (|m| * Real.cosh θ) ^ 3)
    linarith
  have hmFbound : mF ≤ (2 ^ 3 * (2 * π) ^ 3) * S / (|m| * Real.cosh θ) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]; exact hclean
  have hc : ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [show (1 / Real.sqrt 2 : ℂ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  show ‖(1 / Real.sqrt 2 : ℂ) * minkowskiFourier (⇑f) p‖ ≤ _
  rw [norm_mul, hc, ← hmF]
  calc 1 / Real.sqrt 2 * mF
      ≤ 1 / Real.sqrt 2 * ((2 ^ 3 * (2 * π) ^ 3) * S / (|m| * Real.cosh θ) ^ 3) :=
        mul_le_mul_of_nonneg_left hmFbound (by positivity)
    _ = 2 ^ 3 * (2 * π) ^ 3 * S / (Real.sqrt 2 * |m| ^ 3) * ((Real.cosh θ) ^ 3)⁻¹ := by
        rw [show (|m| * Real.cosh θ) ^ 3 = |m| ^ 3 * (Real.cosh θ) ^ 3 from by rw [mul_pow]]
        field_simp

/-- **A non-degenerate `LocalTest` from any Schwartz function** (`m ≠ 0`): the honest "local test
class" — every Schwartz spacetime test function is `L²`-admissible for the mass-shell localization. -/
def schwartzLocalTest (f : SchwartzMap V ℂ) {m : ℝ} (hm : m ≠ 0) : LocalTest m where
  f := ⇑f
  memLp := schwartz_Krep_memLp f hm

/-- **`x_j · f` as a Schwartz function** — coordinate multiplication preserves the Schwartz class.  Built from
`SchwartzMap.bilinLeftCLM` with the scalar-multiplication bilinear map `(z, r) ↦ r • z` and the
temperate-growth coordinate projection `x ↦ x j`.  This is the moment-map building block: the rapidity
derivative `Krep' = kd` decomposes into mass-shell Fourier transforms of `x_j f` (each with `(cosh)⁻²` decay
by `schwartz_Krep_decay_sq`), which yields the `(cosh)⁻¹` decay of `Krep'`. -/
def coordMul (j : Fin 2) (f : SchwartzMap V ℂ) : SchwartzMap V ℂ :=
  SchwartzMap.bilinLeftCLM ((ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (ContinuousLinearMap.proj j).hasTemperateGrowth f

@[simp] theorem coordMul_apply (j : Fin 2) (f : SchwartzMap V ℂ) (x : V) :
    coordMul j f x = (x j : ℝ) • f x := by
  simp only [coordMul, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.proj_apply]

/-- `Krep` of the coordinate-multiplied test function is `(1/√2)` times the mass-shell Fourier transform of
`x_j f` — the bridge that imports the `(cosh)⁻²` decay (`schwartz_Krep_decay_sq` on `coordMul j f`) into the
`Krep'` moment decomposition. -/
theorem Krep_coordMul (j : Fin 2) (f : SchwartzMap V ℂ) (m θ : ℝ) :
    Krep m (⇑(coordMul j f)) θ
      = (1 / Real.sqrt 2 : ℂ) * minkowskiFourier (fun x => (x j : ℝ) • (⇑f) x) (massShell m θ) := by
  have hfun : (⇑(coordMul j f)) = (fun x => (x j : ℝ) • (⇑f) x) := funext (coordMul_apply j f)
  simp only [Krep, hfun]

/-- **`(cosh)⁻²` decay of the mass-shell Fourier transform of `x_j f`.**  Since `x_j f` is Schwartz
(`coordMul`), `schwartz_Krep_decay_sq` applies to it, and `minkowskiFourier(x_j f) = √2·Krep(coordMul j f)`
(`Krep_coordMul`).  This is the moment-decay input for the `(cosh)⁻¹` decay of the rapidity derivative `Krep'`. -/
theorem minkowskiFourier_coordMul_decay (j : Fin 2) (f : SchwartzMap V ℂ) {m : ℝ} (hm : m ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      ‖minkowskiFourier (fun x => (x j : ℝ) • (⇑f) x) (massShell m θ)‖ ≤ C * ((Real.cosh θ) ^ 2)⁻¹ := by
  refine ⟨Real.sqrt 2 * (16 * π ^ 2 * ((∫ v, ‖(⇑(coordMul j f)) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑(coordMul j f)) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑(coordMul j f)) v‖)) / (Real.sqrt 2 * m ^ 2)),
    by positivity, fun θ => ?_⟩
  have hd := schwartz_Krep_decay_sq (coordMul j f) hm θ
  have hM : minkowskiFourier (fun x => (x j : ℝ) • (⇑f) x) (massShell m θ)
      = (Real.sqrt 2 : ℂ) * Krep m (⇑(coordMul j f)) θ := by
    rw [Krep_coordMul, ← mul_assoc, show (Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2 : ℂ) = 1 from by
      rw [mul_one_div, div_self]; exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num), one_mul]
  rw [hM, norm_mul, show ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 from by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
  calc Real.sqrt 2 * ‖Krep m (⇑(coordMul j f)) θ‖
      ≤ Real.sqrt 2 * (16 * π ^ 2 * ((∫ v, ‖(⇑(coordMul j f)) v‖)
          + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑(coordMul j f)) v‖)
          + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑(coordMul j f)) v‖)) / (Real.sqrt 2 * m ^ 2)
          * ((Real.cosh θ) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = Real.sqrt 2 * (16 * π ^ 2 * ((∫ v, ‖(⇑(coordMul j f)) v‖)
          + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑(coordMul j f)) v‖)
          + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑(coordMul j f)) v‖)) / (Real.sqrt 2 * m ^ 2))
          * ((Real.cosh θ) ^ 2)⁻¹ := by ring

/-- **The `Krep'` moment split.**  The bare integral of the rapidity-derivative `kd = Krep'` (from
`schwartz_Krep_hasDerivAt`, modulo `1/√2`) decomposes as
`−i·m·sinh θ·𝓕(x₀ f) + i·m·cosh θ·𝓕(x₁ f)` on the mass shell.  Pointwise the integrand splits by pulling out
the real `θ`-constants, and integral linearity (each moment integrand is `L¹` since `‖e^{iη}·(x_j•f)‖ =
‖coordMul j f‖`) separates the two mass-shell Fourier transforms.  This + `minkowskiFourier_coordMul_decay`
(`(cosh)⁻²`) + `|sinh| ≤ cosh` give the `(cosh)⁻¹` decay of `Krep'`. -/
theorem kd_integral_eq_moments (m : ℝ) (f : SchwartzMap V ℂ) (θ : ℝ) :
    (∫ x, (Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))
        * (-Complex.I * ((m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ) : ℝ) : ℂ))) * (⇑f) x)
      = (-Complex.I * ((m * Real.sinh θ : ℝ) : ℂ))
          * minkowskiFourier (fun x => (x 0 : ℝ) • (⇑f) x) (massShell m θ)
        + (Complex.I * ((m * Real.cosh θ : ℝ) : ℂ))
          * minkowskiFourier (fun x => (x 1 : ℝ) • (⇑f) x) (massShell m θ) := by
  have hnorm_e : ∀ x : V, ‖Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))‖ = 1 := by
    intro x; rw [Complex.norm_exp]
    simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hmD : Continuous (fun x : V => (minkowskiDot (massShell m θ) x : ℝ)) := by
    simp only [minkowskiDot]
    exact (continuous_const.mul (continuous_apply 0)).sub (continuous_const.mul (continuous_apply 1))
  have hexpc : Continuous (fun x : V =>
      Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hmD))
  have hint : ∀ j : Fin 2, Integrable (fun x : V =>
      Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ)) * ((x j : ℝ) • (⇑f) x)) := by
    intro j
    refine ((coordMul j f).integrable.norm).mono'
      (hexpc.mul ((continuous_apply j).smul f.continuous)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, hnorm_e, one_mul, coordMul_apply]
  have hpt : ∀ x : V,
      (Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))
        * (-Complex.I * ((m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ) : ℝ) : ℂ))) * (⇑f) x
      = (-Complex.I * ((m * Real.sinh θ : ℝ) : ℂ))
          * (Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ)) * ((x 0 : ℝ) • (⇑f) x))
        + (Complex.I * ((m * Real.cosh θ : ℝ) : ℂ))
          * (Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ)) * ((x 1 : ℝ) • (⇑f) x)) := by
    intro x; simp only [Complex.real_smul]; push_cast; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add ((hint 0).const_mul _) ((hint 1).const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

/-- **★★★ `(cosh)⁻¹` decay of the rapidity derivative `Krep'` (`kd`).**  Combining the moment split
(`kd_integral_eq_moments`) with the `(cosh)⁻²` moment decay (`minkowskiFourier_coordMul_decay`) and
`|sinh θ| ≤ cosh θ`: the `m·cosh θ` prefactors meet the `(cosh)⁻²` decay to leave `(cosh)⁻¹`.  Since
`∫ (cosh θ)⁻¹ dθ = π`, this is exactly the decay that makes `kd` integrable — the analytic core of the
remaining horizon-amplitude derivative gates (`hdA`/`hdAc`/`hFdA`/`h1`/`h2`). -/
theorem kd_norm_le (m : ℝ) (hm : 0 < m) (f : SchwartzMap V ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      ‖(1 / Real.sqrt 2 : ℂ) * (∫ x, (Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))
          * (-Complex.I * ((m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ) : ℝ) : ℂ))) * (⇑f) x)‖
        ≤ C * (Real.cosh θ)⁻¹ := by
  obtain ⟨C0, hC0, hb0⟩ := minkowskiFourier_coordMul_decay 0 f hm.ne'
  obtain ⟨C1, hC1, hb1⟩ := minkowskiFourier_coordMul_decay 1 f hm.ne'
  refine ⟨1 / Real.sqrt 2 * (m * (C0 + C1)), by positivity, fun θ => ?_⟩
  have hcosh : (0 : ℝ) < Real.cosh θ := Real.cosh_pos θ
  rw [kd_integral_eq_moments, norm_mul, show ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 from by
    rw [show (1 / Real.sqrt 2 : ℂ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)],
    show (1 : ℝ) / Real.sqrt 2 * (m * (C0 + C1)) * (Real.cosh θ)⁻¹
      = (1 / Real.sqrt 2) * (m * (C0 + C1) * (Real.cosh θ)⁻¹) from by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, one_mul, Real.norm_eq_abs,
    abs_of_pos hm, abs_of_pos (Real.cosh_pos θ)]
  have e0 : m * |Real.sinh θ| * ‖minkowskiFourier (fun x => (x 0 : ℝ) • (⇑f) x) (massShell m θ)‖
      ≤ m * Real.cosh θ * (C0 * ((Real.cosh θ) ^ 2)⁻¹) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (abs_sinh_le_cosh θ) hm.le) (hb0 θ) (norm_nonneg _)
      (by positivity)
  have e1 : m * Real.cosh θ * ‖minkowskiFourier (fun x => (x 1 : ℝ) • (⇑f) x) (massShell m θ)‖
      ≤ m * Real.cosh θ * (C1 * ((Real.cosh θ) ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left (hb1 θ) (by positivity)
  refine (add_le_add e0 e1).trans (le_of_eq ?_)
  field_simp

/-- **`(cosh)⁻³` decay of the mass-shell Fourier transform of `x_j f`** (the cube version of
`minkowskiFourier_coordMul_decay`).  `schwartz_Krep_decay_cube` on the Schwartz `coordMul j f` + `Krep_coordMul`. -/
theorem minkowskiFourier_coordMul_decay_cube (j : Fin 2) (f : SchwartzMap V ℂ) {m : ℝ} (hm : m ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      ‖minkowskiFourier (fun x => (x j : ℝ) • (⇑f) x) (massShell m θ)‖ ≤ C * ((Real.cosh θ) ^ 3)⁻¹ := by
  obtain ⟨K, hK, hKb⟩ := schwartz_Krep_decay_cube (coordMul j f) hm
  refine ⟨Real.sqrt 2 * K, mul_nonneg (by positivity) hK, fun θ => ?_⟩
  have hM : minkowskiFourier (fun x => (x j : ℝ) • (⇑f) x) (massShell m θ)
      = (Real.sqrt 2 : ℂ) * Krep m (⇑(coordMul j f)) θ := by
    rw [Krep_coordMul, ← mul_assoc, show (Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2 : ℂ) = 1 from by
      rw [mul_one_div, div_self]; exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num), one_mul]
  rw [hM, norm_mul, show ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 from by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
  calc Real.sqrt 2 * ‖Krep m (⇑(coordMul j f)) θ‖
      ≤ Real.sqrt 2 * (K * ((Real.cosh θ) ^ 3)⁻¹) := mul_le_mul_of_nonneg_left (hKb θ) (by positivity)
    _ = Real.sqrt 2 * K * ((Real.cosh θ) ^ 3)⁻¹ := by ring

/-- **★★★ Super-exponential `(cosh)⁻²` decay of the rapidity derivative `Krep'`** (the cube-moment version of
`kd_norm_le`).  Combining `kd_integral_eq_moments` with the `(cosh)⁻³` moment decay
(`minkowskiFourier_coordMul_decay_cube`) and `|sinh θ| ≤ cosh θ`: the `m·cosh θ` prefactors meet `(cosh)⁻³` to
leave `(cosh)⁻²`.  This is `kd = o(e^{−θ})`, the decay that makes `deriv (horizonAmp)` continuous at `x = 0`. -/
theorem kd_norm_le_sq (m : ℝ) (hm : 0 < m) (f : SchwartzMap V ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      ‖(1 / Real.sqrt 2 : ℂ) * (∫ x, (Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))
          * (-Complex.I * ((m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ) : ℝ) : ℂ))) * (⇑f) x)‖
        ≤ C * ((Real.cosh θ) ^ 2)⁻¹ := by
  obtain ⟨C0, hC0, hb0⟩ := minkowskiFourier_coordMul_decay_cube 0 f hm.ne'
  obtain ⟨C1, hC1, hb1⟩ := minkowskiFourier_coordMul_decay_cube 1 f hm.ne'
  refine ⟨1 / Real.sqrt 2 * (m * (C0 + C1)), by positivity, fun θ => ?_⟩
  have hcosh : (0 : ℝ) < Real.cosh θ := Real.cosh_pos θ
  rw [kd_integral_eq_moments, norm_mul, show ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 from by
    rw [show (1 / Real.sqrt 2 : ℂ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)],
    show (1 : ℝ) / Real.sqrt 2 * (m * (C0 + C1)) * ((Real.cosh θ) ^ 2)⁻¹
      = (1 / Real.sqrt 2) * (m * (C0 + C1) * ((Real.cosh θ) ^ 2)⁻¹) from by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, one_mul, Real.norm_eq_abs,
    abs_of_pos hm, abs_of_pos (Real.cosh_pos θ)]
  have e0 : m * |Real.sinh θ| * ‖minkowskiFourier (fun x => (x 0 : ℝ) • (⇑f) x) (massShell m θ)‖
      ≤ m * Real.cosh θ * (C0 * ((Real.cosh θ) ^ 3)⁻¹) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (abs_sinh_le_cosh θ) hm.le) (hb0 θ) (norm_nonneg _)
      (by positivity)
  have e1 : m * Real.cosh θ * ‖minkowskiFourier (fun x => (x 1 : ℝ) • (⇑f) x) (massShell m θ)‖
      ≤ m * Real.cosh θ * (C1 * ((Real.cosh θ) ^ 3)⁻¹) :=
    mul_le_mul_of_nonneg_left (hb1 θ) (by positivity)
  refine (add_le_add e0 e1).trans (le_of_eq ?_)
  field_simp

end QIQTH.Fock.Localization
