/-
  CensusFarRateAbsorb — J4-940: piece (6) of J4-929's `hCensusBound` re-audit — the
  `Bball + tail ≤ C_far·(u−s)^{−1/2}` UNIFORM RATE ABSORPTION.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  REAL-ANALYSIS / ALGEBRA brick: it absorbs J4-933's domain-bridge output
      `|∫_{ℝⁿ} Φ| ≤ Bball + Cenv·(√2)ⁿ·e^{−ρ²/(8λ)}`   (`census_full_of_ball_bound_and_gaussEnv`)
  into the SINGLE `C_far·(u−s)^{−1/2}` rate that J4-929's `hcross_of_censusIntegral_bound` consumes
  (`hCensusBound`), for a SINGLE explicit constant valid UNIFORMLY over `s ∈ Ioo(u−ε)u`,
  `a ∈ Icc u(u+h)`.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable /
  conclusion-in-disguise hypothesis, no existing banked file edited.

  ## THE EXACT SHAPES (verified against the live defs).
  • TARGET (`HCrossDerivEngineWired.hcross_of_censusIntegral_bound`, J4-929):
      `hCensusBound : ∀ s ∈ Ioo(u−ε)u, ∀ a ∈ Icc u(u+h),
          |∫ z, deriv(fun r ↦ witness r 0 z)(a−s) · F s z 0|  ≤  C_far · (u−s)^{−1/2}` .
  • SOURCE (`CensusDomainBridge.census_full_of_ball_bound_and_gaussEnv`, J4-933):
      `|∫ z, Φ z| ≤ Bball + Cenv·(√2)ⁿ·e^{−ρ²/(8λ)}`,   with (from J4-922/923/924 trace core)
      `Bball ≤ Cpair·(a−s)^{−1/2}` (the on-ball trace-cancellation rate).

  ## THE ABSORPTION ALGEBRA (why it is free and uniform).  Write `σ := u−s ∈ (0,ε]`, `τ := a−s ≥ σ`
  (since `a ≥ u`).  Two monotonicities of `x ↦ x^{−1/2}` (decreasing, `rpow_le_rpow_of_nonpos`):
    (a) `Bball ≤ Cpair·τ^{−1/2} ≤ Cpair·σ^{−1/2}`   (using `σ ≤ τ`);
    (b) `e^{−ρ²/(8λ)} ≤ 1`, and `Cenv·(√2)ⁿ = Cenv·(√2)ⁿ·(√ε·ε^{−1/2}) ≤ Cenv·(√2)ⁿ·√ε·σ^{−1/2}`
        (using `ε^{−1/2} ≤ σ^{−1/2}` from `σ ≤ ε`, and `√ε·ε^{−1/2} = 1`).
  So `Bball + tail ≤ (Cpair + Cenv·(√2)ⁿ·√ε)·σ^{−1/2}` — the tail's exponential smallness is not even
  needed: mere `e^{…} ≤ 1` plus the `σ ≤ ε` upper bound suffices, giving a SINGLE `s`-independent
      `C_far := Cpair + Cenv·(√2)ⁿ·√ε` .

  ## WHAT LANDS.
    • `rate_absorb` — ★★ THE PURE ALGEBRAIC CORE.  From `0<σ`, `σ≤τ`, `σ≤ε`, `0<lam`, `0≤Cenv`,
        `0≤Cpair`, `Bball ≤ Cpair·τ^{−1/2}`, and `L ≤ Bball + Cenv·(√2ⁿ·e^{−ρ²/(8lam)})`, conclude
        `L ≤ (Cpair + Cenv·√2ⁿ·√ε)·σ^{−1/2}`.  Reusable, integrand-free.
    • `census_far_rate_of_ball_and_gaussEnv` — ★★ THE COMPOSED BRIDGE.  Feeds
        `census_full_of_ball_bound_and_gaussEnv` (J4-933) through `rate_absorb`: for `Φ` with an off-ball
        Gaussian envelope, a ball bound `Bball ≤ Cpair·(a−s)^{−1/2}`, and the `Ioo/Icc` positions
        (`u−ε<s<u`, `u≤a`), `|∫ z, Φ z| ≤ (Cpair + Cenv·√2ⁿ·√ε)·(u−s)^{−1/2}` — EXACTLY the RHS shape of
        J4-929's `hCensusBound`, with the single explicit `C_far`.
    • `rate_absorb_hyp_satisfiable`, `census_far_rate_hyp_satisfiable` — non-vacuity EXHIBITED at genuine
        positive data (`L>0`; `Φ = gaussDdim 1`), so neither fires on a degenerate bundle.

  ## HONEST STATUS (blunt).  This discharges piece (6) — the uniform rate absorption — as a reusable
  brick, with the single explicit `C_far = Cpair + Cenv·√2ⁿ·√ε`.  It does NOT close `hCensusBound`.  The
  LITERAL assembly still requires: (a) the F-factor's own ball-local bounded+Lipschitz regularity (the
  `leviSeries` carry, `{hDuhamel,hDConv,hCConv}`-family — NOT here); and (b) `hbaseC2` (the base-slot CoV
  residual).  With piece (6) closed, `hCensusBound`'s remaining obligations reduce to exactly those two.
  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusDomainBridge

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.CensusDomainBridge
open scoped BigOperators

namespace QIQTH.CensusFarRateAbsorb

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### §A — the pure algebraic rate-absorption core.
    ############################################################################### -/

/-- **★★ `rate_absorb` — THE PURE ALGEBRAIC RATE ABSORPTION.**  For scalars with `0<σ`, `σ≤τ`, `σ≤ε`,
    `0<lam`, `0≤Cenv`, `0≤Cpair`, given the on-ball trace rate `Bball ≤ Cpair·τ^{−1/2}` and J4-933's
    domain-bridge bound `L ≤ Bball + Cenv·(√2ⁿ·e^{−ρ²/(8lam)})`,
        `L ≤ (Cpair + Cenv·√2ⁿ·√ε)·σ^{−1/2}` .
    The exponential tail is absorbed by `e^{…} ≤ 1` plus the two `x↦x^{−1/2}` monotonicities (`σ≤τ`,
    `σ≤ε`) and `√ε·ε^{−1/2}=1`.  NOT `a₁ = R/6`. -/
theorem rate_absorb
    (ε σ τ ρ lam Cenv Cpair Bball L : ℝ)
    (hε : 0 < ε) (hσ : 0 < σ) (hστ : σ ≤ τ) (hσε : σ ≤ ε)
    (hlam : 0 < lam) (hCenv : 0 ≤ Cenv) (hCpair : 0 ≤ Cpair)
    (hBball : Bball ≤ Cpair * τ ^ (-(1 : ℝ) / 2))
    (hL : L ≤ Bball + Cenv * (Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam)))) :
    L ≤ (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * σ ^ (-(1 : ℝ) / 2) := by
  have he : (-(1 : ℝ) / 2) ≤ 0 := by norm_num
  have hσnn : (0 : ℝ) ≤ σ := le_of_lt hσ
  -- (a) `Bball ≤ Cpair·σ^{−1/2}` via `τ^{−1/2} ≤ σ^{−1/2}`.
  have hτσ : τ ^ (-(1 : ℝ) / 2) ≤ σ ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hσ hστ he
  have hBball' : Bball ≤ Cpair * σ ^ (-(1 : ℝ) / 2) :=
    le_trans hBball (mul_le_mul_of_nonneg_left hτσ hCpair)
  -- (b) tail: `e^{…} ≤ 1`.
  have hexp1 : Real.exp (-(ρ ^ 2) / (8 * lam)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hnum : -(ρ ^ 2) ≤ 0 := by nlinarith [sq_nonneg ρ]
    have hden : (0 : ℝ) ≤ 8 * lam := by linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum hden
  -- `√ε · ε^{−1/2} = 1`.
  have hsqrtε : Real.sqrt ε * ε ^ (-(1 : ℝ) / 2) = 1 := by
    have h2 : Real.sqrt ε = ε ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow ε
    rw [h2, ← Real.rpow_add hε, show (1 : ℝ) / 2 + -(1 : ℝ) / 2 = 0 by norm_num, Real.rpow_zero]
  have hεσ : ε ^ (-(1 : ℝ) / 2) ≤ σ ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hσ hσε he
  have hCbnn : (0 : ℝ) ≤ Cenv * Real.sqrt 2 ^ n :=
    mul_nonneg hCenv (by positivity)
  have hCbεnn : (0 : ℝ) ≤ Cenv * Real.sqrt 2 ^ n * Real.sqrt ε :=
    mul_nonneg hCbnn (Real.sqrt_nonneg ε)
  -- tail bound: `Cenv·(√2ⁿ·e) ≤ (Cenv·√2ⁿ·√ε)·σ^{−1/2}`.
  have htail : Cenv * (Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam)))
      ≤ (Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * σ ^ (-(1 : ℝ) / 2) := by
    have step1 : Cenv * (Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam)))
        ≤ Cenv * Real.sqrt 2 ^ n := by
      have hin : Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam)) ≤ Real.sqrt 2 ^ n * 1 :=
        mul_le_mul_of_nonneg_left hexp1 (by positivity)
      calc Cenv * (Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam)))
          ≤ Cenv * (Real.sqrt 2 ^ n * 1) := mul_le_mul_of_nonneg_left hin hCenv
        _ = Cenv * Real.sqrt 2 ^ n := by ring
    have e1 : (Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * ε ^ (-(1 : ℝ) / 2)
        = Cenv * Real.sqrt 2 ^ n := by
      rw [mul_assoc, hsqrtε, mul_one]
    have step2 : Cenv * Real.sqrt 2 ^ n
        ≤ (Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * σ ^ (-(1 : ℝ) / 2) :=
      calc Cenv * Real.sqrt 2 ^ n
          = (Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * ε ^ (-(1 : ℝ) / 2) := e1.symm
        _ ≤ (Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * σ ^ (-(1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hεσ hCbεnn
    exact le_trans step1 step2
  -- combine.
  calc L ≤ Bball + Cenv * (Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam))) := hL
    _ ≤ Cpair * σ ^ (-(1 : ℝ) / 2)
          + (Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * σ ^ (-(1 : ℝ) / 2) :=
        add_le_add hBball' htail
    _ = (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * σ ^ (-(1 : ℝ) / 2) := by ring

/-! ###############################################################################
    ### §B — the composed bridge: J4-933 domain output ⟶ J4-929's `hCensusBound` rate shape.
    ############################################################################### -/

/-- **★★ `census_far_rate_of_ball_and_gaussEnv` — THE COMPOSED FAR-RATE BOUND.**  For `Φ` integrable with
    an off-ball Gaussian envelope `|Φ z| ≤ Cenv·gaussDdim lam z` (`ρ ≤ ‖z‖`), a ball bound `Bball` obeying
    the on-ball trace rate `Bball ≤ Cpair·(a−s)^{−1/2}`, and the `Ioo(u−ε)u`/`Icc u(u+h)` positions
    (`u−ε<s`, `s<u`, `u≤a`),
        `|∫ z, Φ z| ≤ (Cpair + Cenv·√2ⁿ·√ε)·(u−s)^{−1/2}` ,
    the EXACT RHS shape of J4-929's `hCensusBound`, with the single explicit `s`-independent
    `C_far = Cpair + Cenv·√2ⁿ·√ε`.  Composes `census_full_of_ball_bound_and_gaussEnv` (J4-933) with
    `rate_absorb`.  NOT `a₁ = R/6`. -/
theorem census_far_rate_of_ball_and_gaussEnv
    (u s a ε ρ lam Cenv Cpair Bball : ℝ)
    (hε : 0 < ε) (hlam : 0 < lam) (hCenv : 0 ≤ Cenv) (hCpair : 0 ≤ Cpair) (hρ : 0 ≤ ρ)
    (hslo : u - ε < s) (hshi : s < u) (hau : u ≤ a)
    (Φ : Point n → ℝ) (hΦint : Integrable Φ volume)
    (henv : ∀ z : Point n, ρ ≤ ‖z‖ → |Φ z| ≤ Cenv * gaussDdim lam z)
    (Bball_bd : |∫ z in Metric.ball (0 : Point n) ρ, Φ z| ≤ Bball)
    (hBball : Bball ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2)) :
    |∫ z, Φ z|
      ≤ (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hfull := census_full_of_ball_bound_and_gaussEnv ρ lam Cenv Bball hlam hρ hCenv Φ hΦint
    henv Bball_bd
  have hσ : 0 < u - s := by linarith
  have hστ : u - s ≤ a - s := by linarith
  have hσε : u - s ≤ ε := by linarith
  exact rate_absorb ε (u - s) (a - s) ρ lam Cenv Cpair Bball _
    hε hσ hστ hσε hlam hCenv hCpair hBball hfull

/-! ###############################################################################
    ### §C — non-vacuity (both bundles jointly satisfiable at genuine positive data).
    ############################################################################### -/

/-- **Non-vacuity of `rate_absorb`.**  The hypothesis bundle is jointly satisfiable at genuine positive
    data (`ε=σ=τ=lam=Cenv=Cpair=Bball=L=1`, `ρ=0`, so `L=1>0`, `Bball=1 ≤ 1·1^{−1/2}`, and
    `1 ≤ 1 + 1·(√2ⁿ·e⁰)`).  So the absorption fires on a real positive quantity, not a degenerate
    bundle.  NOT `a₁ = R/6`. -/
theorem rate_absorb_hyp_satisfiable :
    ∃ (ε σ τ ρ lam Cenv Cpair Bball L : ℝ),
      0 < ε ∧ 0 < σ ∧ σ ≤ τ ∧ σ ≤ ε ∧ 0 < lam ∧ 0 ≤ Cenv ∧ 0 ≤ Cpair ∧
        Bball ≤ Cpair * τ ^ (-(1 : ℝ) / 2) ∧
        L ≤ Bball + Cenv * (Real.sqrt 2 ^ n * Real.exp (-(ρ ^ 2) / (8 * lam))) ∧
        0 < L := by
  refine ⟨1, 1, 1, 0, 1, 1, 1, 1, 1, one_pos, one_pos, le_refl _, le_refl _, one_pos,
    zero_le_one, zero_le_one, ?_, ?_, one_pos⟩
  · rw [Real.one_rpow, one_mul]
  · have h0 : (0 : ℝ)
        ≤ (1 : ℝ) * (Real.sqrt 2 ^ n * Real.exp (-((0 : ℝ) ^ 2) / (8 * 1))) := by positivity
    linarith

/-- **Non-vacuity of `census_far_rate_of_ball_and_gaussEnv`.**  The hypothesis bundle is jointly
    satisfiable at the genuine off-ball-decaying integrand `Φ = gaussDdim 1` with `u=1`, `s=1/2`,
    `a=3/2` (so `u−ε<s<u`, `u≤a`, `a−s=1`), `ε=ρ=lam=Cenv=Cpair=Bball=1`.  So the far-rate bound fires
    on a real Gaussian integrand at genuine `Ioo/Icc` positions, not a degenerate bundle.  NOT
    `a₁ = R/6`. -/
theorem census_far_rate_hyp_satisfiable :
    ∃ (u s a ε ρ lam Cenv Cpair Bball : ℝ) (Φ : Point n → ℝ),
      0 < ε ∧ 0 < lam ∧ 0 ≤ Cenv ∧ 0 ≤ Cpair ∧ 0 ≤ ρ ∧
        u - ε < s ∧ s < u ∧ u ≤ a ∧ Integrable Φ volume ∧
        (∀ z : Point n, ρ ≤ ‖z‖ → |Φ z| ≤ Cenv * gaussDdim lam z) ∧
        |∫ z in Metric.ball (0 : Point n) ρ, Φ z| ≤ Bball ∧
        Bball ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2) := by
  refine ⟨1, 1/2, 3/2, 1, 1, 1, 1, 1, 1, fun z => gaussDdim 1 z,
    one_pos, one_pos, zero_le_one, zero_le_one, zero_le_one,
    by norm_num, by norm_num, by norm_num, gaussDdim_integrable 1 one_pos, ?_, ?_, ?_⟩
  · intro z _
    rw [one_mul, abs_of_nonneg (gaussDdim_nonneg 1 z)]
  · have hnn : (0 : ℝ) ≤ ∫ z in Metric.ball (0 : Point n) 1, gaussDdim 1 z :=
      setIntegral_nonneg measurableSet_ball (fun z _ => gaussDdim_nonneg 1 z)
    have hle : (∫ z in Metric.ball (0 : Point n) 1, gaussDdim 1 z) ≤ ∫ z, gaussDdim 1 z :=
      setIntegral_le_integral (gaussDdim_integrable 1 one_pos)
        (ae_of_all _ (fun z => gaussDdim_nonneg 1 z))
    rw [abs_of_nonneg hnn]
    exact hle.trans (le_of_eq (gaussDdim_integral_eq_one 1 one_pos))
  · rw [show (3 : ℝ) / 2 - 1 / 2 = 1 by norm_num, Real.one_rpow, one_mul]

end QIQTH.CensusFarRateAbsorb

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusFarRateAbsorb
#print axioms rate_absorb
#print axioms census_far_rate_of_ball_and_gaussEnv
#print axioms rate_absorb_hyp_satisfiable
#print axioms census_far_rate_hyp_satisfiable
end AxiomChecks
