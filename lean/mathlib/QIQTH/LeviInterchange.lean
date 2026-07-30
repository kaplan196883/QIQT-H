/-
  LeviInterchange — M6 / analytic carry: the tsum/heatConv INTERCHANGE `hInter`, discharged as an
  ABSTRACT analytic lemma from the domination + integrability + measurability machinery already in
  the repo.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET.  `TrueHeatKernel.leviSeries_volterra` (and `TrueKernelA1.trueKernel_diagonal_a1_eq_R6`)
  carry, as an explicit hypothesis, the tsum/heatConv interchange
      `hInter :  heatConv E (leviSeries E) t x y
                   = ∑' k, heatConv E (fun τ p q => (-1)^(k+1)·iterE E (k+1) τ p q) t x y`,
  documented there as "the SOLE genuinely-Mathlib-missing analytic input".  This file DISCHARGES it.

  The underlying Mathlib tool is `MeasureTheory.integral_tsum_of_summable_integral_norm`
  (`∑' i, ∫ a, F i a = ∫ a, ∑' i, F i a`, from per-`i` integrability + summability of `∫‖F i‖`).  The
  interchange is a DOUBLE application of it — once for the inner spatial `∫z`, once for the outer
  interval `∫s in 0..t` (realized as `∫ ∂(volume.restrict (Ioc 0 t))`):

    * `heatConv E (leviSeries E) = ∫ s in 0..t, ∫ z, E(t−s)x z · (∑' k, sign·iterE E (k+1) s z y)`;
    * pull `∑'` out of the inner `∫z` (`tsum_mul_left` moves `E(t−s)x z` inside, then
      `integral_tsum_of_summable_integral_norm`), giving `∫ s in 0..t, ∑' k, ∫ z, E · (sign·iterE)`;
    * pull `∑'` out of the outer `∫s` (`integral_tsum_of_summable_integral_norm` on the restricted
      measure), giving `∑' k, ∫ s in 0..t, ∫ z, E · (sign·iterE) = ∑' k, heatConv E (sign·iterE)`.

  Every integrability / summability side goal is discharged from the SAME machinery that drives the
  Neumann convergence: the width-2 domination `iterConvW_bound` (`|iterE E k| ≤ C^k·iterKernelW 2 0 k`),
  the per-step integrability family `IterConvIntegrableW` (built from `hEbound`/`hEzero`/`hEmeas` via
  `iterConvIntegrableW_of_bound_baseMeas`), the joint measurabilities `iterE_zmeas`/`conv_meas`, the
  Gaussian-convolution collapse `gaussDdim_conv`, and the model summabilities
  `scaledModelCoeff_summable` / `scaledIterKernelW_summable`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  KEY FINDING.  `hInter` is NOT genuinely Mathlib-blocked — it is ASSEMBLABLE.  The repo docs called
  it "Summable-continuity of `heatConv` under `tsum`, which Mathlib lacks cleanly"; in fact
  `integral_tsum_of_summable_integral_norm` fits both the inner Lebesgue layer and the outer interval
  layer (the latter via the `volume.restrict (Ioc 0 t)` presentation of `∫ s in 0..t`), and the
  summability of `∫‖·‖` is exactly the model domination the convergence engine already supplies.

  ⚠ HONEST SCOPE.  This discharges `hInter` down to the SAME genuine, non-vacuous carries the rest of
  the M6 tower runs on: the width-2 one-step residual bound `hEbound` (the C4c off-diagonal
  parametrix wall), the vanishing `hEzero`, the joint measurability `hEmeas` of `E`, and `C ≥ 0`,
  `0 < t`.  It does NOT discharge `hEbound`, and it is NOT `a₁ = R/6`.  No axioms beyond the standard
  three, no `sorry`, no vacuous hypotheses; every carried hypothesis is genuinely used.
-/
import Mathlib
import QIQTH.TrueHeatKernel
import QIQTH.LeviSeries
import QIQTH.HeatDuhamel
import QIQTH.ParametrixHEboundWiring
import QIQTH.IterEMeasurable
import QIQTH.ModelIntegrableW

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-- **★ THE tsum/heatConv INTERCHANGE `hInter`, DISCHARGED.**  For the width-2 one-step residual
    bound `hEbound`, the vanishing at nonpositive time `hEzero`, the joint strong measurability
    `hEmeas` of `E`, and `C ≥ 0`, `0 < t`, the space-time convolution `heatConv E (·)` commutes with
    the infinite (Levi/Neumann) sum:
        `heatConv E (leviSeries E) t x y
           = ∑' k, heatConv E (fun τ p q => (-1)^(k+1)·iterE E (k+1) τ p q) t x y`.
    Proof: a double application of `MeasureTheory.integral_tsum_of_summable_integral_norm` (inner
    Lebesgue `∫z`, outer interval `∫s in 0..t` via the restricted measure), with all
    integrability/summability side goals discharged from the width-2 domination `iterConvW_bound`, the
    per-step integrability `IterConvIntegrableW` (from `iterConvIntegrableW_of_bound_baseMeas`), the
    joint measurabilities `iterE_zmeas`/`conv_meas`, the Gaussian collapse `gaussDdim_conv`, and the
    model summabilities `scaledModelCoeff_summable`/`scaledIterKernelW_summable`.

    This CONVERTS the carried `hInter` of `leviSeries_volterra`/`trueKernel_diagonal_a1_eq_R6` into
    the same `hEbound`/`hEzero`/`hEmeas` carries the rest of the M6 tower already runs on — strictly
    reducing the analytic surface.  Still CONDITIONAL on `hEbound` (the C4c wall); NOT `a₁ = R/6`. -/
theorem heatConv_leviSeries_interchange
    (E : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (t : ℝ) (ht : 0 < t) (x y : Point n) :
    heatConv E (leviSeries E) t x y
      = ∑' k : ℕ, heatConv E (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q) t x y := by
  -- ── The per-step integrability family + domination + measurabilities. ───────────────────────
  have hInt : IterConvIntegrableW E (2 : ℝ) (0 : ℝ) C :=
    iterConvIntegrableW_of_bound_baseMeas E C hEbound hEzero hEmeas
  have dom : ∀ (k : ℕ) (τ : ℝ), 0 < τ → ∀ (p q : Point n),
      |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) τ p q := by
    intro k τ hτ p q
    exact iterConvW_bound E (2 : ℝ) (0 : ℝ) C hEbound hInt (k + 1) (by omega) τ hτ p q
  have hE_zmeas : ∀ (τ : ℝ) (p : Point n),
      AEStronglyMeasurable (fun z : Point n => E τ p z) volume := by
    intro τ p
    exact (hEmeas.comp_measurable
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  -- The unit-modulus sign factor.
  have hsgn : ∀ m : ℕ, |(-1 : ℝ) ^ m| = 1 := fun m => by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  -- ── The pointwise norm bound `‖E·(sign·iterE)‖ ≤ model`  (interior times). ───────────────────
  have hnormbd : ∀ (k : ℕ) (s : ℝ), 0 < s → s < t → ∀ z : Point n,
      ‖E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)‖
        ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
            * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y) := by
    intro k s hs0 hst z
    have hts : 0 < t - s := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, hsgn (k + 1), one_mul]
    have hEb := hEbound (t - s) x z hts
    have hIb := dom k s hs0 z y
    calc |E (t - s) x z| * |iterE E (k + 1) s z y|
        ≤ (C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z)
            * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y) :=
          mul_le_mul hEb hIb (abs_nonneg _) (le_trans (abs_nonneg _) hEb)
      _ = C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
            * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y) := by ring
  -- ── Per-`(k,s)` `z`-integrability of the actual signed integrand (interior times). ───────────
  have fkszInt : ∀ (k : ℕ) (s : ℝ), 0 < s → s < t →
      Integrable (fun z => E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)) volume := by
    intro k s hs0 hst
    obtain ⟨_, _, _, hIg, _⟩ := hInt (k + 1) (by omega) t ht x y
    have hmeas : AEStronglyMeasurable
        (fun z => E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)) volume :=
      (hE_zmeas (t - s) x).mul
        ((iterE_zmeas E hEmeas (k + 1) (by omega) s y).const_mul _)
    exact Integrable.mono' (hIg s) hmeas (ae_of_all _ (fun z => hnormbd k s hs0 hst z))
  -- ── The model `z`-integral closed form (interior times). ─────────────────────────────────────
  have hDzeq : ∀ (k : ℕ) (s : ℝ), 0 < s → s < t →
      (∫ z, C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
              * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y))
        = (C * gaussDdim (2 * t) (x - y)) * (C ^ (k + 1) * modelCoeff 0 s (k + 1)) := by
    intro k s hs0 hst
    have hts : 0 < t - s := by linarith
    have hform : (fun z => C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
              * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y))
        = fun z => (C * C ^ (k + 1)
              * (Real.Gamma (0 + 1) ^ (k + 1) / Real.Gamma (((k + 1 : ℕ) : ℝ) * (0 + 1)))
              * s ^ (((k + 1 : ℕ) : ℝ) * (0 + 1) - 1))
            * (gaussDdim (2 * (t - s)) (x - z) * gaussDdim (2 * s) (z - y)) := by
      funext z
      rw [baseKernelW_zero_apply,
          iterKernelW_eq (2 : ℝ) (0 : ℝ) (by norm_num) (by norm_num) s hs0 z y (by omega : 1 ≤ k + 1)]
      ring
    rw [hform, integral_const_mul,
        gaussDdim_conv (2 * (t - s)) (2 * s) (by linarith) (by linarith) x y,
        show 2 * (t - s) + 2 * s = 2 * t from by ring]
    unfold modelCoeff
    ring
  -- ── INNER interchange (fixed interior `s`): pull `∑'` out of `∫z`. ────────────────────────────
  have inner : ∀ s, 0 < s → s < t →
      (∫ z, E (t - s) x z * (∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y))
        = ∑' k : ℕ, ∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y) := by
    intro s hs0 hst
    -- (a) move the constant `E(t−s)x z` inside the `∑'`.
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun z =>
      (tsum_mul_left (f := fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)
        (a := E (t - s) x z)).symm))]
    -- (b) per-`k` integrability of the (signed) integrand.
    have hFint : ∀ k, Integrable
        (fun z => E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)) volume :=
      fun k => fkszInt k s hs0 hst
    -- (c) summability of `∫z ‖·‖` via the model bound.
    have hFsum : Summable
        (fun k => ∫ z, ‖E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)‖) := by
      have hDzsum : Summable
          (fun k => (C * gaussDdim (2 * t) (x - y)) * (C ^ (k + 1) * modelCoeff 0 s (k + 1))) :=
        (scaledModelCoeff_summable 0 s C le_rfl hs0 hC).mul_left _
      refine Summable.of_nonneg_of_le
        (fun k => integral_nonneg (fun z => norm_nonneg _)) (fun k => ?_) hDzsum
      obtain ⟨_, _, _, hIg, _⟩ := hInt (k + 1) (by omega) t ht x y
      calc ∫ z, ‖E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)‖
          ≤ ∫ z, C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
                * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y) :=
            integral_mono (hFint k).norm (hIg s) (fun z => hnormbd k s hs0 hst z)
        _ = (C * gaussDdim (2 * t) (x - y)) * (C ^ (k + 1) * modelCoeff 0 s (k + 1)) :=
            hDzeq k s hs0 hst
    exact (integral_tsum_of_summable_integral_norm hFint hFsum).symm
  -- ── The signed `s`-integrand as a scalar multiple of the unsigned convolution. ───────────────
  have gk_eq : ∀ k,
      (fun s => ∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y))
        = (fun s => (-1 : ℝ) ^ (k + 1) * ∫ z, E (t - s) x z * iterE E (k + 1) s z y) := by
    intro k; funext s
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun z =>
        show E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)
              = (-1 : ℝ) ^ (k + 1) * (E (t - s) x z * iterE E (k + 1) s z y) from by ring)),
        integral_const_mul]
  -- ── OUTER `hF_int`: `Integrable (g k) (volume.restrict (Ioc 0 t))`. ──────────────────────────
  have gkInt : ∀ k, Integrable
      (fun s => ∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y))
      (volume.restrict (Set.Ioc 0 t)) := by
    intro k
    rw [gk_eq k]
    obtain ⟨hI1, _, _, _, _⟩ := hInt (k + 1) (by omega) t ht x y
    have hnormOn : Integrable
        (fun s => ‖∫ z, E (t - s) x z * iterE E (k + 1) s z y‖) (volume.restrict (Set.Ioc 0 t)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hI1
    have hsig : AEStronglyMeasurable
        (fun s => ∫ z, E (t - s) x z * iterE E (k + 1) s z y) (volume.restrict (Set.Ioc 0 t)) := by
      have hjoint := conv_meas E hEmeas (k + 1) (by omega) t ht x y
      simpa only [Function.uncurry_apply_pair] using hjoint.integral_prod_right'
    exact (Integrable.mono' hnormOn hsig (ae_of_all _ (fun s => le_refl _))).const_mul _
  -- ── OUTER `hF_sum`: summability of `∫s ‖g k s‖`  via the model. ──────────────────────────────
  have gkSum : Summable
      (fun k => ∫ s, ‖∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)‖
        ∂(volume.restrict (Set.Ioc 0 t))) := by
    have hDssum : Summable (fun k => C ^ (k + 2) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 2) t x y) := by
      have h := scaledIterKernelW_summable (2 : ℝ) (0 : ℝ) t C (by norm_num) le_rfl ht hC x y
      simpa [Function.comp] using h.comp_injective Nat.succ_injective
    refine Summable.of_nonneg_of_le
      (fun k => integral_nonneg (fun s => norm_nonneg _)) (fun k => ?_) hDssum
    obtain ⟨_, _, _, _, hIsg⟩ := hInt (k + 1) (by omega) t ht x y
    -- The model `s`-integrand is integrable on `Ioc 0 t`.
    have hDzOn : Integrable
        (fun s => ∫ z, C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
          * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y))
        (volume.restrict (Set.Ioc 0 t)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hIsg
    -- The a.e. pointwise bound `‖g k s‖ ≤ ∫z model`.
    have hbnd : (fun s => ‖∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)‖)
        ≤ᵐ[volume.restrict (Set.Ioc 0 t)]
        (fun s => ∫ z, C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
          * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y)) := by
      refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
      intro hmem
      obtain ⟨hs0, hsle⟩ := hmem
      have hst2 : s < t := lt_of_le_of_ne hsle (by simpa using hst)
      calc ‖∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)‖
          ≤ ∫ z, ‖E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ z, C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
              * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y) :=
            integral_mono (fkszInt k s hs0 hst2).norm
              (by obtain ⟨_, _, _, hIg, _⟩ := hInt (k + 1) (by omega) t ht x y; exact hIg s)
              (fun z => hnormbd k s hs0 hst2 z)
    -- Integrate the bound, then evaluate the model integral in closed form.
    refine le_trans (integral_mono_ae (gkInt k).norm hDzOn hbnd) (le_of_eq ?_)
    -- `∫ s in Ioc, ∫z model = C^(k+2)·iterKernelW 2 0 (k+2) t x y`.
    have hconv : (∫ s, (∫ z, C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
            * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y))
          ∂(volume.restrict (Set.Ioc 0 t)))
        = ∫ s in (0 : ℝ)..t, ∫ z, C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
            * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y) :=
      (intervalIntegral.integral_of_le ht.le).symm
    rw [hconv]
    have hpull : ∀ s, (∫ z, C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
              * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y))
        = (C * C ^ (k + 1))
            * ∫ z, baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
                * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y := by
      intro s
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ (fun z => by ring))
    calc (∫ s in (0 : ℝ)..t, ∫ z, C * baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
            * (C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y))
        = ∫ s in (0 : ℝ)..t, (C * C ^ (k + 1))
            * ∫ z, baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
                * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y :=
          intervalIntegral.integral_congr (fun s _ => hpull s)
      _ = (C * C ^ (k + 1)) * ∫ s in (0 : ℝ)..t, ∫ z, baseKernelW (2 : ℝ) (0 : ℝ) (t - s) x z
                * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) s z y :=
          intervalIntegral.integral_const_mul _ _
      _ = (C * C ^ (k + 1))
            * heatConv (baseKernelW (2 : ℝ) (0 : ℝ)) (iterKernelW (2 : ℝ) (0 : ℝ) (k + 1)) t x y :=
          rfl
      _ = (C * C ^ (k + 1)) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 2) t x y := by
          rw [show iterKernelW (2 : ℝ) (0 : ℝ) (k + 2)
                = heatConvK (baseKernelW (2 : ℝ) (0 : ℝ)) (iterKernelW (2 : ℝ) (0 : ℝ) (k + 1))
                from iterKernelW_succ (2 : ℝ) (0 : ℝ) (by omega : 1 ≤ k + 1)]
          rfl
      _ = C ^ (k + 2) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 2) t x y := by ring
  -- ── ASSEMBLE the double interchange. ─────────────────────────────────────────────────────────
  simp only [heatConv, leviSeries]
  have hcongr : (∫ s in (0 : ℝ)..t,
        ∫ z, E (t - s) x z * (∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y))
      = ∫ s in (0 : ℝ)..t,
        ∑' k : ℕ, ∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
    intro hmem
    rw [Set.uIoc_of_le ht.le] at hmem
    obtain ⟨hs0, hsle⟩ := hmem
    exact inner s hs0 (lt_of_le_of_ne hsle (by simpa using hst))
  calc (∫ s in (0 : ℝ)..t,
          ∫ z, E (t - s) x z * (∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y))
      = ∫ s in (0 : ℝ)..t,
          ∑' k : ℕ, ∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y) := hcongr
    _ = ∫ s, (∑' k : ℕ, ∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y))
          ∂(volume.restrict (Set.Ioc 0 t)) := intervalIntegral.integral_of_le ht.le
    _ = ∑' k : ℕ, ∫ s, (∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y))
          ∂(volume.restrict (Set.Ioc 0 t)) :=
        (integral_tsum_of_summable_integral_norm gkInt gkSum).symm
    _ = ∑' k : ℕ, ∫ s in (0 : ℝ)..t,
          ∫ z, E (t - s) x z * ((-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y) := by
        refine tsum_congr (fun k => ?_)
        exact (intervalIntegral.integral_of_le ht.le).symm

end QIQTH.HeatResidualBound
