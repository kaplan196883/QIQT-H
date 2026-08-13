/-
  LeviInterchangeTrunc — J4-670: the SMALL-TIME truncated tsum/heatConv INTERCHANGE `hInter`,
  discharged from the AFFINE/TRUNCATED window bound instead of the all-τ fixed-constant bound.  ONE
  brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL — THE `hInter` ARROW ONLY.  This file ports the banked all-τ interchange
  `HeatResidualBound.heatConv_leviSeries_interchange` (`LeviInterchange.lean`) to the SMALL-TIME
  window `(0, T₀]`, exactly as `TruncatedHIntRethread` ported the per-step integrability producer.
  It closes NOTHING of the `R/6` coefficient extraction; it only makes the interchange consumable from
  the SAME truncated data the curved closure supplies (the affine `C·(1+τ)` bound collapsed to the
  FIXED constant `C·(1+T₀)` on `(0, T₀]`).

  ── THE OBSTRUCTION (recalled).  The all-τ interchange needs `hEbound` at a SINGLE fixed `C` for ALL
     `τ`; the curved provider `curvedRNC_heatOp_dom_pkg` supplies only the affine `C·(1+τ)` bound, whose
     valid constant is affine in the cutoff — no fixed-constant Gaussian majorant exists at all τ (the
     exact J4-261 obstruction the truncated `hInt` route dissolved).

  ── THE SMALL-TIME FIX (this file).  The interchange lives at a SINGLE outer time `t`, integrating the
     inner space-time convolution over `s ∈ (0, t)` with convolution times `t−s, s ∈ (0, t)`.  EVERY
     time it touches lies in `(0, t) ⊆ (0, T₀]` when `t ≤ T₀`.  So on the truncated window the
     fixed-constant bound holds, and the per-step integrability family it consumes is exactly
     `TruncatedHIntRethread.IterConvIntegrableWOn` (via the truncated producer + `iterConvW_bound_le_-`
     `trunc`).  The port is byte-for-byte the banked interchange with `IterConvIntegrableW →
     IterConvIntegrableWOn`, `iterConvW_bound → iterConvW_bound_le_trunc`, the `hEbound` calls carrying
     the extra `τ ≤ T₀` (sound because all touched times are `< t ≤ T₀`), and the `hInt` calls carrying
     the extra outer `t ≤ T₀` (the C-route verdict: `hInt` only ever touched at the outer time).

  ── WHAT STAYS CARRIED (honest residue, satisfiable, never the conclusion):  the FIXED-constant
     `τ ≤ T₀` one-step bound `hEbound`, the nonpositive-time vanishing `hEzero`, and the joint strong
     measurability `hEmeas` of `E` — the SAME three carries `TruncatedHIntRethread` runs on, each
     dischargeable from geometry at the curved witness.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses.  Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.TrueHeatKernel
import QIQTH.LeviSeries
import QIQTH.HeatDuhamel
import QIQTH.ParametrixHEboundWiring
import QIQTH.IterEMeasurable
import QIQTH.ModelIntegrableW
import QIQTH.TruncatedHIntRethread

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.TruncatedHIntRethread

namespace QIQTH.LeviInterchangeTrunc

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-- **★★★★ J4-670 — the SMALL-TIME truncated tsum/heatConv INTERCHANGE `hInter`, DISCHARGED.**  The
    truncated-window analogue of `HeatResidualBound.heatConv_leviSeries_interchange`: for the width-2
    FIXED-constant `τ ≤ T₀` one-step residual bound `hEbound`, the nonpositive-time vanishing `hEzero`,
    the joint strong measurability `hEmeas` of `E`, and `C ≥ 0`, `0 < t ≤ T₀`, the space-time
    convolution `heatConv E (·)` commutes with the infinite Levi/Neumann sum:
        `heatConv E (leviSeries E) t x y
           = ∑' k, heatConv E (fun τ p q => (-1)^(k+1)·iterE E (k+1) τ p q) t x y`.
    Proof: the banked all-τ interchange, ported to the `(0, T₀]` window — `IterConvIntegrableW →
    IterConvIntegrableWOn` (via `iterConvIntegrableWOn_of_bound_baseMeas_trunc`) and `iterConvW_bound →
    iterConvW_bound_le_trunc`, with every `hEbound`/`hInt` call carrying the extra `≤ T₀` argument
    (sound: all touched times `< t ≤ T₀`, and `hInt` is only touched at the outer time `t`).

    This CONVERTS the curved capstone's carried `hInter` arrow into the SAME FIXED-constant `τ ≤ T₀`
    `hEbound` the curved closure already supplies (`hEboundW_le` from `curvedRNC_heatOp_dom_pkg`),
    strictly reducing the analytic surface.  Still CONDITIONAL on `hEbound`; NOT `a₁ = R/6`. -/
theorem heatConv_leviSeries_interchange_trunc
    (E : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C) (T₀ : ℝ)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ T₀ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (t : ℝ) (ht : 0 < t) (htT : t ≤ T₀) (x y : Point n) :
    heatConv E (leviSeries E) t x y
      = ∑' k : ℕ, heatConv E (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q) t x y := by
  -- ── The TRUNCATED per-step integrability family + domination + measurabilities. ──────────────
  have hInt : IterConvIntegrableWOn E (2 : ℝ) (0 : ℝ) C T₀ :=
    iterConvIntegrableWOn_of_bound_baseMeas_trunc E (2 : ℝ) C T₀ (by norm_num) hEbound hEzero hEmeas
  have dom : ∀ (k : ℕ) (τ : ℝ), 0 < τ → τ ≤ T₀ → ∀ (p q : Point n),
      |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW (2 : ℝ) (0 : ℝ) (k + 1) τ p q := by
    intro k τ hτ hτT p q
    exact iterConvW_bound_le_trunc E (2 : ℝ) (0 : ℝ) C T₀ hEbound hInt (k + 1) (by omega) τ hτ hτT p q
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
    have hEb := hEbound (t - s) x z hts (by linarith)
    have hIb := dom k s hs0 (by linarith) z y
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
    obtain ⟨_, _, _, hIg, _⟩ := hInt (k + 1) (by omega) t ht htT x y
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
      obtain ⟨_, _, _, hIg, _⟩ := hInt (k + 1) (by omega) t ht htT x y
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
    obtain ⟨hI1, _, _, _, _⟩ := hInt (k + 1) (by omega) t ht htT x y
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
    obtain ⟨_, _, _, _, hIsg⟩ := hInt (k + 1) (by omega) t ht htT x y
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
              (by obtain ⟨_, _, _, hIg, _⟩ := hInt (k + 1) (by omega) t ht htT x y; exact hIg s)
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

end QIQTH.LeviInterchangeTrunc

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.LeviInterchangeTrunc
#print axioms heatConv_leviSeries_interchange_trunc
end AxiomChecks
