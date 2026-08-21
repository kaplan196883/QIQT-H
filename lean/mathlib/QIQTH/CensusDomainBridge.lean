/-
  CensusDomainBridge — J4-933: the DOMAIN-MISMATCH bridge for obstruction (ii) of J4-929's
  `hCensusBound` wall.  The banked base-slot change-of-variables (`BaseSlotChangeVariables`, J4-930)
  transports the census integrand over `ball 0 ρ`, but the LIVE census `hCensusBound` (J4-929)
  integrates over ALL of `ℝⁿ` (`∫ z, …`).  This file bridges that gap: the off-ball residue is an
  EXPONENTIALLY-SUPPRESSED Gaussian tail (`e^{−ρ²/(8λ)}`), so the full-`ℝⁿ` census is the ball census
  plus a tail that is negligible relative to the `τ^{−1/2}` rate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick — the CENSUS-shape companion of J4-922's
  `gaussian_hessian_cancel_trace_on_superset` (which bridges a superset `Ω ⊇ ball` for the FLAT trace
  integrand).  This one bridges the OTHER direction that the concrete census needs: from the CoV-covered
  `ball 0 ρ` UP to all of `ℝⁿ`, for an ARBITRARY integrand `Φ` with an off-ball single-Gaussian envelope.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise
  hypothesis, no existing banked file edited.

  ## THE EXACT DOMAIN MISMATCH (verified against the live defs).  J4-929's `hcross_of_censusIntegral_bound`
  consumes `hCensusBound : ∀ s ∈ Ioo(u−ε)u, ∀ a ∈ Icc u(u+h),
      |∫ z, deriv(fun r ↦ witness r 0 z)(a−s) · F s z 0| ≤ C_far·(u−s)^{−1/2}`,
  where `∫ z, …` is the integral over ALL of `Point n = ℝⁿ`.  The banked base-slot CoV
  `base_slot_gaussian_change_variables_of_hbaseC2` (J4-930) transports only
      `∫ z in ball 0 ρ, gaussDdim τ (uic z 0) · B z`.
  So the residue is the off-ball part `∫ z in (ball 0 ρ)ᶜ, …`.  Via `witnessTauDeriv_eq_gatedTauRepProd`
  (J4-217) the census integrand is the base-slot trace structure `(∑ᵢ(…))·gaussDdim τ (uic z 0)·A + …`,
  which the `hAcrude`-class crude-environment carries (J4-916/917) dominate by an integrable Gaussian
  envelope; off the ball `‖z‖ ≥ ρ` that envelope decays like `e^{−ρ²/(8λ)}` (`gaussDdim_tail_le_scaled`,
  J4-546).

  ## WHAT LANDS.
    • `integral_le_ball_add_offBall_dominator` — ★ THE PURE MEASURE-THEORY BRIDGE.  For `Φ` integrable
        and any integrable `D` dominating `|Φ|` off `ball 0 ρ`, and a ball bound `|∫_{ball} Φ| ≤ Bball`,
          `|∫_{ℝⁿ} Φ| ≤ Bball + ∫_{(ball 0 ρ)ᶜ} D` .
      Pure `integral_add_compl` + triangle + `setIntegral_mono_on`.
    • `offBall_gauss_tail_mass_le` — ★ THE GAUSSIAN TAIL MASS.  For `λ>0`,
          `∫_{(ball 0 ρ)ᶜ} Cenv·gaussDdim λ z ≤ Cenv·(√2)ⁿ·e^{−ρ²/(8λ)}` .
      From `gaussDdim_tail_le_scaled` (relaxed to `ρ ≤ ‖z‖`) + `∫ gaussDdim(2λ) = 1`.
    • `census_full_of_ball_bound_and_gaussEnv` — ★★ THE HEADLINE DOMAIN BRIDGE (obstruction (ii)).  For
        `Φ` integrable with an off-ball single-Gaussian envelope `|Φ z| ≤ Cenv·gaussDdim λ z` (`ρ ≤ ‖z‖`)
        and a ball bound `Bball`,
          `|∫_{ℝⁿ} Φ| ≤ Bball + Cenv·(√2)ⁿ·e^{−ρ²/(8λ)}` .
      Composes the two lemmas above — the full-`ℝⁿ` census equals the ball census plus an
      exponentially-small (in `1/λ`) Gaussian tail.
    • `census_full_of_ball_bound_and_gaussEnv_hyp_satisfiable` — non-vacuity EXHIBITED at the genuine
        integrand `Φ = gaussDdim 1` (`ρ=λ=Cenv=Bball=1`).

  ## HONEST STATUS (blunt).  This discharges obstruction (ii) — the `ball 0 ρ` vs `ℝⁿ` domain gap — as a
  reusable API brick.  It does NOT close `hCensusBound`.  The LITERAL assembly of `hCensusBound` still
  requires threading, at the concrete gated witness: the J4-217 derivative representation's `hgate`
  carry (amplitude `HasDerivAt` + `S`-membership); the base-slot CoV's left-inverse weight matching
  (`uic (V w) 0 = w` so the transported trace factor becomes the FLAT `∑ᵢ(wᵢ²/4τ²−1/2τ)`); the concrete
  transported-weight `amp·F` / `Cfield·F` global boundedness + Lipschitz inputs (feeding J4-931/932); the
  IFT open-map superset `Wbv''(ball 0 ρ) ⊇ ball 0 r`; the collapse of the `hAcrude·hFdom` Gaussian
  PRODUCT envelope to a single Gaussian for `henv` here; and the final `Bball + tail ≤ C_far·(u−s)^{−1/2}`
  rate absorption.  NONE of those are in this file, and none are among the four pieces
  {base-slot CoV, det/ratio regularity, V-transport, tail bound}.  So `hCensusBound` is NOT assembled
  modulo only `hbaseC2`.  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OffCollarTailMoment

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open scoped BigOperators

namespace QIQTH.CensusDomainBridge

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### §A — the pure measure-theory domain bridge (ball ⟶ ℝⁿ + off-ball dominator).
    ############################################################################### -/

/-- **★ `integral_le_ball_add_offBall_dominator` — THE PURE MEASURE-THEORY BRIDGE.**  For `Φ` integrable
    and any integrable `D` dominating `|Φ|` off `ball 0 ρ` (`∀ z, ρ ≤ ‖z‖ → |Φ z| ≤ D z`), together with
    a ball bound `|∫_{ball 0 ρ} Φ| ≤ Bball`,
        `|∫_{ℝⁿ} Φ| ≤ Bball + ∫_{(ball 0 ρ)ᶜ} D` .
    Route: `∫_{ℝⁿ} Φ = ∫_{ball} Φ + ∫_{ballᶜ} Φ` (`integral_add_compl`), triangle inequality, then
    `|∫_{ballᶜ} Φ| ≤ ∫_{ballᶜ} |Φ| ≤ ∫_{ballᶜ} D` (`setIntegral_mono_on`, using `ρ ≤ ‖z‖` on `ballᶜ`).
    NOT `a₁ = R/6`. -/
theorem integral_le_ball_add_offBall_dominator
    (ρ : ℝ) (Φ D : Point n → ℝ)
    (hΦint : Integrable Φ volume) (hDint : Integrable D volume)
    (hdom : ∀ z : Point n, ρ ≤ ‖z‖ → |Φ z| ≤ D z)
    (Bball : ℝ) (hball : |∫ z in Metric.ball (0 : Point n) ρ, Φ z| ≤ Bball) :
    |∫ z, Φ z| ≤ Bball + ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, D z := by
  have hballmeas : MeasurableSet (Metric.ball (0 : Point n) ρ) := measurableSet_ball
  have hcomplmeas : MeasurableSet (Metric.ball (0 : Point n) ρ)ᶜ := hballmeas.compl
  -- membership: on `ballᶜ` we have `ρ ≤ ‖z‖`.
  have hmem : ∀ z ∈ (Metric.ball (0 : Point n) ρ)ᶜ, ρ ≤ ‖z‖ := by
    intro z hz
    by_contra h
    push_neg at h
    exact hz (by rw [Metric.mem_ball, dist_zero_right]; exact h)
  -- split `∫_ℝⁿ = ∫_ball + ∫_ballᶜ`.
  have hsplit : (∫ z in Metric.ball (0 : Point n) ρ, Φ z)
      + (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, Φ z) = ∫ z, Φ z :=
    integral_add_compl hballmeas hΦint
  -- tail: `|∫_ballᶜ Φ| ≤ ∫_ballᶜ |Φ| ≤ ∫_ballᶜ D`.
  have htail : |∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, Φ z|
      ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, D z := by
    calc |∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, Φ z|
        ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, |Φ z| := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm
              (μ := volume.restrict (Metric.ball (0 : Point n) ρ)ᶜ) (f := Φ)
      _ ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, D z :=
          setIntegral_mono_on hΦint.abs.integrableOn hDint.integrableOn hcomplmeas
            (fun z hz => hdom z (hmem z hz))
  -- combine.
  calc |∫ z, Φ z|
      = |(∫ z in Metric.ball (0 : Point n) ρ, Φ z)
          + (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, Φ z)| := by rw [hsplit]
    _ ≤ |∫ z in Metric.ball (0 : Point n) ρ, Φ z|
          + |∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, Φ z| := abs_add_le _ _
    _ ≤ Bball + ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, D z := add_le_add hball htail

/-! ###############################################################################
    ### §B — the Gaussian off-ball tail mass (`e^{−ρ²/(8λ)}` suppression).
    ############################################################################### -/

/-- **★ `offBall_gauss_tail_mass_le` — THE GAUSSIAN TAIL MASS.**  For `λ > 0`, `0 ≤ ρ`, `0 ≤ Cenv`,
        `∫_{(ball 0 ρ)ᶜ} Cenv·gaussDdim λ z ≤ Cenv·(√2)ⁿ·e^{−ρ²/(8λ)}` .
    The off-ball Gaussian mass is exponentially suppressed: on `ρ ≤ ‖z‖` the kernel is dominated by the
    doubled-width kernel times `(√2)ⁿ·e^{−ρ²/(8λ)}` (the `ρ ≤ ‖z‖` variant of `gaussDdim_tail_le_scaled`,
    J4-546), whose total mass is `1` (`gaussDdim_integral_eq_one`).  NOT `a₁ = R/6`. -/
theorem offBall_gauss_tail_mass_le
    (ρ lam Cenv : ℝ) (hlam : 0 < lam) (hρ : 0 ≤ ρ) (hCenv : 0 ≤ Cenv) :
    (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, Cenv * gaussDdim lam z)
      ≤ Cenv * (Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam))) := by
  have h2lam : (0 : ℝ) < 2 * lam := by linarith
  have hcomplmeas : MeasurableSet (Metric.ball (0 : Point n) ρ)ᶜ := measurableSet_ball.compl
  -- membership: on `ballᶜ` we have `ρ ≤ ‖z‖`.
  have hmem : ∀ z ∈ (Metric.ball (0 : Point n) ρ)ᶜ, ρ ≤ ‖z‖ := by
    intro z hz
    by_contra h
    push_neg at h
    exact hz (by rw [Metric.mem_ball, dist_zero_right]; exact h)
  -- the `ρ ≤ ‖z‖` variant of the pointwise tail domination (mirrors `gaussDdim_tail_le_scaled`).
  have tail_le : ∀ z : Point n, ρ ≤ ‖z‖ →
      gaussDdim lam z ≤ Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam)) * gaussDdim (2 * lam) z := by
    intro z hz
    have hRsq : ρ ^ 2 ≤ rncRadialSq z := by
      have h1 : ρ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [hz, hρ, norm_nonneg z]
      exact le_trans h1 (norm_sq_le_rncRadialSq z)
    have hexp_le : Real.exp (-(rncRadialSq z) / (8 * lam)) ≤ Real.exp (-(ρ ^ 2) / (8 * lam)) := by
      apply Real.exp_le_exp.mpr
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith [hRsq]) (by positivity)
    rw [gaussDdim_eq_wide_mul hlam z, gaussDdimWide_eq_scaled_gaussDdim hlam z]
    have hg2 : 0 ≤ gaussDdim (2 * lam) z := gaussDdim_nonneg (2 * lam) z
    calc Real.exp (-(rncRadialSq z) / (8 * lam)) * (Real.sqrt 2 ^ n * gaussDdim (2 * lam) z)
        ≤ Real.exp (-(ρ ^ 2) / (8 * lam)) * (Real.sqrt 2 ^ n * gaussDdim (2 * lam) z) :=
          mul_le_mul_of_nonneg_right hexp_le (by positivity)
      _ = Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam)) * gaussDdim (2 * lam) z := by ring
  set C : ℝ := Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam)) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hI0 : Integrable (fun z : Point n => gaussDdim lam z) volume := gaussDdim_integrable lam hlam
  have hI2 : Integrable (fun z : Point n => gaussDdim (2 * lam) z) volume :=
    gaussDdim_integrable (2 * lam) h2lam
  -- pull the constant out, then dominate the off-ball Gaussian mass.
  have hconst : (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, Cenv * gaussDdim lam z)
      = Cenv * ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim lam z := integral_const_mul _ _
  rw [hconst]
  refine mul_le_mul_of_nonneg_left ?_ hCenv
  -- `∫_ballᶜ gaussDdim λ ≤ ∫_ballᶜ (C·gaussDdim(2λ)) ≤ C·∫_ℝⁿ gaussDdim(2λ) = C`.
  calc (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim lam z)
      ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, C * gaussDdim (2 * lam) z := by
        refine setIntegral_mono_on hI0.integrableOn (hI2.const_mul C).integrableOn hcomplmeas
          (fun z hz => ?_)
        rw [hCdef]; exact tail_le z (hmem z hz)
    _ = C * ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (2 * lam) z := integral_const_mul _ _
    _ ≤ C * ∫ z, gaussDdim (2 * lam) z := by
        refine mul_le_mul_of_nonneg_left ?_ hCnn
        exact setIntegral_le_integral hI2 (ae_of_all _ (fun z => gaussDdim_nonneg (2 * lam) z))
    _ = C * 1 := by rw [gaussDdim_integral_eq_one (2 * lam) h2lam]
    _ = C := mul_one C

/-! ###############################################################################
    ### §C — THE HEADLINE DOMAIN BRIDGE (obstruction (ii)).
    ############################################################################### -/

/-- **★★ `census_full_of_ball_bound_and_gaussEnv` — THE HEADLINE DOMAIN BRIDGE (obstruction (ii)).**  For
    `Φ` integrable with an off-ball single-Gaussian envelope `∀ z, ρ ≤ ‖z‖ → |Φ z| ≤ Cenv·gaussDdim λ z`
    and a ball bound `|∫_{ball 0 ρ} Φ| ≤ Bball`,
        `|∫_{ℝⁿ} Φ| ≤ Bball + Cenv·(√2)ⁿ·e^{−ρ²/(8λ)}` .
    The full-`ℝⁿ` census is the CoV-covered ball census `Bball` plus an EXPONENTIALLY-SUPPRESSED Gaussian
    tail — negligible relative to the `τ^{−1/2}` rate (with `λ = wL·τ`, `e^{−ρ²/(8wLτ)}` is
    super-polynomially small in `1/τ`).  Composes `integral_le_ball_add_offBall_dominator` with
    `offBall_gauss_tail_mass_le`.  NOT `a₁ = R/6`. -/
theorem census_full_of_ball_bound_and_gaussEnv
    (ρ lam Cenv Bball : ℝ) (hlam : 0 < lam) (hρ : 0 ≤ ρ) (hCenv : 0 ≤ Cenv)
    (Φ : Point n → ℝ) (hΦint : Integrable Φ volume)
    (henv : ∀ z : Point n, ρ ≤ ‖z‖ → |Φ z| ≤ Cenv * gaussDdim lam z)
    (Bball_bd : |∫ z in Metric.ball (0 : Point n) ρ, Φ z| ≤ Bball) :
    |∫ z, Φ z| ≤ Bball + Cenv * (Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam))) := by
  have hDint : Integrable (fun z : Point n => Cenv * gaussDdim lam z) volume :=
    (gaussDdim_integrable lam hlam).const_mul Cenv
  have hbridge := integral_le_ball_add_offBall_dominator ρ Φ (fun z => Cenv * gaussDdim lam z)
    hΦint hDint henv Bball Bball_bd
  calc |∫ z, Φ z|
      ≤ Bball + ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, Cenv * gaussDdim lam z := hbridge
    _ ≤ Bball + Cenv * (Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam))) := by
        gcongr
        exact offBall_gauss_tail_mass_le ρ lam Cenv hlam hρ hCenv

/-! ###############################################################################
    ### §D — non-vacuity (the hypothesis bundle is jointly satisfiable at a genuine integrand).
    ############################################################################### -/

/-- **Non-vacuity of `census_full_of_ball_bound_and_gaussEnv`.**  The hypothesis bundle is jointly
    satisfiable at the genuine, off-ball-decaying integrand `Φ = gaussDdim 1` (`ρ = λ = Cenv = Bball = 1`,
    `0 < n`): `Φ` is integrable, the envelope `|gaussDdim 1 z| ≤ 1·gaussDdim 1 z` holds by nonnegativity,
    and the ball census is `≤ 1` (below the total Gaussian mass `1`).  So the bound fires on a real
    Gaussian integrand, not a degenerate bundle.  NOT `a₁ = R/6`. -/
theorem census_full_of_ball_bound_and_gaussEnv_hyp_satisfiable :
    ∃ (ρ lam Cenv Bball : ℝ) (Φ : Point n → ℝ),
      0 < lam ∧ 0 ≤ ρ ∧ 0 ≤ Cenv ∧ Integrable Φ volume ∧
        (∀ z : Point n, ρ ≤ ‖z‖ → |Φ z| ≤ Cenv * gaussDdim lam z) ∧
        |∫ z in Metric.ball (0 : Point n) ρ, Φ z| ≤ Bball := by
  refine ⟨1, 1, 1, 1, fun z => gaussDdim 1 z, one_pos, zero_le_one, zero_le_one,
    gaussDdim_integrable 1 one_pos, ?_, ?_⟩
  · intro z _
    rw [one_mul, abs_of_nonneg (gaussDdim_nonneg 1 z)]
  · -- the ball census is nonneg and `≤ ∫_ℝⁿ gaussDdim 1 = 1`.
    have hnn : (0 : ℝ) ≤ ∫ z in Metric.ball (0 : Point n) 1, gaussDdim 1 z :=
      setIntegral_nonneg measurableSet_ball (fun z _ => gaussDdim_nonneg 1 z)
    have hle : (∫ z in Metric.ball (0 : Point n) 1, gaussDdim 1 z) ≤ ∫ z, gaussDdim 1 z :=
      setIntegral_le_integral (gaussDdim_integrable 1 one_pos)
        (ae_of_all _ (fun z => gaussDdim_nonneg 1 z))
    rw [abs_of_nonneg hnn]
    exact hle.trans (le_of_eq (gaussDdim_integral_eq_one 1 one_pos))

end QIQTH.CensusDomainBridge

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusDomainBridge
#print axioms integral_le_ball_add_offBall_dominator
#print axioms offBall_gauss_tail_mass_le
#print axioms census_full_of_ball_bound_and_gaussEnv
#print axioms census_full_of_ball_bound_and_gaussEnv_hyp_satisfiable
end AxiomChecks
