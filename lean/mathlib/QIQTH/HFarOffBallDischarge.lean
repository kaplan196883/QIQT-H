/-
  HFarOffBallDischarge — the OFF-BALL spatial estimate for the `hCross` far-envelope `H_far`,
  discharging the last genuinely-open analytic step of J4-967's `hfar_of_ballrate_ftc` reduction by
  TRANSFERRING J4-933's off-ball Gaussian-tail technique into the `(c−s)`-form rate slot.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE composition brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## THE EXACT GAP (from J4-967 `HFarFromBallrate.lean`).  `hfar_of_ballrate_ftc` produces `H_far`
  (`|Φ(u+h,s) − Φ(u,s)| ≤ C_far·h·(u−s)^{−1/2}`) from an FTC-in-`c` bridge `hFTC` and a **full-domain**
  pointwise-in-`c` rate `hrate : |R c s| ≤ Cpair·(c−s)^{−1/2}`, where `R c s = ∫ z, g c s z` is the
  FULL-`ℝⁿ` rate integrand.  The on-ball rate `hballrate` (closed modulo-G2, J4-960) only bounds the
  BALL-truncated `∫_{ball 0 ρ} g c s z`.  So `hrate` needs the OFF-BALL contribution
  `∫_{(ball 0 ρ)ᶜ} g c s z` to be controlled by the same `(c−s)^{−1/2}` rate.  THAT off-ball estimate is
  exactly the open piece flagged in the J4-967 firewall (obstruction (ii)).

  ## THE TRANSFER (does J4-933's technique compose?).  YES — `census_full_of_ball_bound_and_gaussEnv`
  (J4-933, `CensusDomainBridge.lean`) bounds `|∫_{ℝⁿ} Φ| ≤ Bball + Cenv·(√2)ⁿ·e^{−ρ²/(8λ)}` from an
  off-ball single-Gaussian envelope `|Φ z| ≤ Cenv·gaussDdim λ z` and a ball bound `Bball`.  Applying it
  at each fixed `(c,s)` with `Φ := g c s`, `Bball := Cpair·(c−s)^{−1/2}`, the full-domain rate satisfies
      `|R c s| ≤ Cpair·(c−s)^{−1/2} + Cenv·(√2)ⁿ·e^{−ρ²/(8λ)}` .
  The tail is absorbed into the SAME `(c−s)^{−1/2}` rate — WITHOUT even needing the exponential decay:
  `e^{−ρ²/(8λ)} ≤ 1` and, since `c − s ≤ h + ε` on the far window (`c ≤ u+h`, `s > u−ε`),
  `1 ≤ √(h+ε)·(c−s)^{−1/2}`, giving `tail ≤ Cenv·(√2)ⁿ·√(h+ε)·(c−s)^{−1/2}`.  Hence
      `|R c s| ≤ (Cpair + Cenv·(√2)ⁿ·√(h+ε))·(c−s)^{−1/2}` ,
  EXACTLY the `hrate` shape `hfar_of_ballrate_ftc` consumes.  NOTE the DISTINCTION from J4-940
  (`census_far_rate_of_ball_and_gaussEnv`): J4-940 collapses to the `(u−s)^{−1/2}` census form
  (`hCensusBound`), which is the WRONG direction for the `hrate` slot (`(u−s)^{−1/2} ≥ (c−s)^{−1/2}`);
  this file keeps the sharper `(c−s)`-form needed to feed `hfar_of_ballrate_ftc`.

  ## WHAT LANDS.
    • `one_le_sqrt_mul_rpow` — the elementary majorization `1 ≤ √M·τ^{−1/2}` for `0 < τ ≤ M`.
    • `tail_absorb` — ★ the PURE ALGEBRAIC core: `Bball ≤ Cpair·τ^{−1/2}`, `L ≤ Bball + Cenv·(√2ⁿ·e)`,
        `0 ≤ e ≤ 1`, `0 < τ ≤ M` ⟹ `L ≤ (Cpair + Cenv·√2ⁿ·√M)·τ^{−1/2}`.  Integrand-free, reusable.
    • `far_rate_of_ball_and_gaussEnv` — ★★ the FULL-DOMAIN `(c−s)`-form rate: composes
        `census_full_of_ball_bound_and_gaussEnv` (J4-933) through `tail_absorb`.
    • `hfar_of_ballrate_offBallEnv_ftc` — ★★★ THE HEADLINE: threads the off-ball rate through
        `hfar_of_ballrate_ftc` (J4-967) to yield `H_far` from {FTC bridge, on-ball ball-rate,
        off-ball Gaussian envelope, integrability} — no separate off-ball obligation left.
    • `hfar_of_ballrate_offBallEnv_ftc_hyp_satisfiable` — non-vacuity EXHIBITED at a genuine Gaussian
        rate integrand (`g = gaussDdim 1`) with the off-ball envelope AND finite-difference genuinely active.

  ## HONEST STATUS (blunt).  This discharges the OFF-BALL spatial estimate of `H_far` AS A REUSABLE
  ADAPTER: given an off-ball single-Gaussian envelope on the concrete rate integrand `g c s = ∂_c`-kernel·F,
  the off-ball contribution is controlled by the `(c−s)^{−1/2}` rate, so `hfar_of_ballrate_ftc`'s
  `hrate` is supplied WITHOUT a separate off-ball obligation.  Consequently `H_far` is NOT open beyond
  {FTC-in-`c` bridge, on-ball `hballrate` (mod-G2), the off-ball Gaussian ENVELOPE on `g`, integrability}.
  It does NOT prove the off-ball Gaussian envelope for the CONCRETE kernel derivative (that is the
  `hAcrude`/`leviSeries` crude-environment carry, downstream of the differentiation identity `R = ∂_c Φ`),
  and it does NOT supply the FTC bridge `R = ∂_c Φ` (the `{hDuhamel, hDConv}` carry).  So this file
  discharges NONE of `{hballrate, hDuhamel, hDConv, hCConv}` as a top-level τ-carry.  `a₁ = R/6` remains
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusDomainBridge
import QIQTH.HFarFromBallrate

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open scoped BigOperators

namespace QIQTH.HFarOffBallDischarge

variable {n : ℕ}

/-! ###############################################################################
    ### §A — the elementary `(c−s)`-form majorization and the algebraic tail absorption.
    ############################################################################### -/

/-- **`one_le_sqrt_mul_rpow` — `1 ≤ √M·τ^{−1/2}` for `0 < τ ≤ M`.**  Since `τ ≤ M` and the exponent
    `−1/2 ≤ 0`, `M^{−1/2} ≤ τ^{−1/2}` (`rpow_le_rpow_of_nonpos`), and `√M·M^{−1/2} = M^{1/2−1/2} = 1`.
    NOT `a₁ = R/6`. -/
theorem one_le_sqrt_mul_rpow (M τ : ℝ) (hτ : 0 < τ) (hτM : τ ≤ M) :
    (1 : ℝ) ≤ Real.sqrt M * τ ^ (-(1 : ℝ) / 2) := by
  have hM : 0 < M := lt_of_lt_of_le hτ hτM
  have hmono : M ^ (-(1 : ℝ) / 2) ≤ τ ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hτ hτM (by norm_num)
  have hid : Real.sqrt M * M ^ (-(1 : ℝ) / 2) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hM]; norm_num
  calc (1 : ℝ) = Real.sqrt M * M ^ (-(1 : ℝ) / 2) := hid.symm
    _ ≤ Real.sqrt M * τ ^ (-(1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg M)

/-- **★ `tail_absorb` — THE PURE ALGEBRAIC TAIL ABSORPTION.**  For `0 < τ ≤ M`, `0 ≤ Cpair`,
    `0 ≤ Cenv`, `0 ≤ e ≤ 1`, an on-ball rate `Bball ≤ Cpair·τ^{−1/2}`, and a census bound
    `L ≤ Bball + Cenv·(√2ⁿ·e)`,
        `L ≤ (Cpair + Cenv·(√2ⁿ·√M))·τ^{−1/2}` .
    The `e ≤ 1` (NOT its exponential smallness) plus `1 ≤ √M·τ^{−1/2}` absorb the tail into the rate.
    NOT `a₁ = R/6`. -/
theorem tail_absorb (n : ℕ) (τ M Cpair Cenv e Bball L : ℝ)
    (hτ : 0 < τ) (hτM : τ ≤ M) (hCp : 0 ≤ Cpair) (hCenv : 0 ≤ Cenv)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hBball : Bball ≤ Cpair * τ ^ (-(1 : ℝ) / 2))
    (hL : L ≤ Bball + Cenv * (Real.sqrt 2 ^ n * e)) :
    L ≤ (Cpair + Cenv * (Real.sqrt 2 ^ n * Real.sqrt M)) * τ ^ (-(1 : ℝ) / 2) := by
  have hone := one_le_sqrt_mul_rpow M τ hτ hτM
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 ^ n := by positivity
  have htail : Cenv * (Real.sqrt 2 ^ n * e)
      ≤ (Cenv * (Real.sqrt 2 ^ n * Real.sqrt M)) * τ ^ (-(1 : ℝ) / 2) := by
    calc Cenv * (Real.sqrt 2 ^ n * e)
        ≤ Cenv * (Real.sqrt 2 ^ n * 1) := by
          have h1 : Real.sqrt 2 ^ n * e ≤ Real.sqrt 2 ^ n * 1 :=
            mul_le_mul_of_nonneg_left he1 hs2
          exact mul_le_mul_of_nonneg_left h1 hCenv
      _ = Cenv * Real.sqrt 2 ^ n := by ring
      _ ≤ Cenv * Real.sqrt 2 ^ n * (Real.sqrt M * τ ^ (-(1 : ℝ) / 2)) := by
          have := mul_le_mul_of_nonneg_left hone (mul_nonneg hCenv hs2)
          simpa using this
      _ = (Cenv * (Real.sqrt 2 ^ n * Real.sqrt M)) * τ ^ (-(1 : ℝ) / 2) := by ring
  calc L ≤ Bball + Cenv * (Real.sqrt 2 ^ n * e) := hL
    _ ≤ Cpair * τ ^ (-(1 : ℝ) / 2)
          + (Cenv * (Real.sqrt 2 ^ n * Real.sqrt M)) * τ ^ (-(1 : ℝ) / 2) :=
        add_le_add hBball htail
    _ = (Cpair + Cenv * (Real.sqrt 2 ^ n * Real.sqrt M)) * τ ^ (-(1 : ℝ) / 2) := by ring

/-! ###############################################################################
    ### §B — the full-domain `(c−s)`-form rate (census bridge ∘ tail absorption).
    ############################################################################### -/

/-- **★★ `far_rate_of_ball_and_gaussEnv` — THE FULL-DOMAIN `(c−s)`-FORM RATE.**  For a rate integrand
    `Φ` (`= g c s`) integrable with an off-ball single-Gaussian envelope `|Φ z| ≤ Cenv·gaussDdim λ z`
    (`ρ ≤ ‖z‖`), a ball rate bound `|∫_{ball 0 ρ} Φ| ≤ Cpair·τ^{−1/2}`, and `0 < τ ≤ M`,
        `|∫_{ℝⁿ} Φ| ≤ (Cpair + Cenv·(√2ⁿ·√M))·τ^{−1/2}` .
    Composes `census_full_of_ball_bound_and_gaussEnv` (J4-933) with `tail_absorb`.  NOT `a₁ = R/6`. -/
theorem far_rate_of_ball_and_gaussEnv {n : ℕ}
    (ρ lam Cenv Cpair τ M : ℝ) (Φ : Point n → ℝ)
    (hlam : 0 < lam) (hρ : 0 ≤ ρ) (hCenv : 0 ≤ Cenv) (hCp : 0 ≤ Cpair)
    (hτ : 0 < τ) (hτM : τ ≤ M)
    (hΦint : Integrable Φ volume)
    (henv : ∀ z : Point n, ρ ≤ ‖z‖ → |Φ z| ≤ Cenv * gaussDdim lam z)
    (hball : |∫ z in Metric.ball (0 : Point n) ρ, Φ z| ≤ Cpair * τ ^ (-(1 : ℝ) / 2)) :
    |∫ z, Φ z|
      ≤ (Cpair + Cenv * (Real.sqrt 2 ^ n * Real.sqrt M)) * τ ^ (-(1 : ℝ) / 2) := by
  have hcensus := QIQTH.CensusDomainBridge.census_full_of_ball_bound_and_gaussEnv
    ρ lam Cenv (Cpair * τ ^ (-(1 : ℝ) / 2)) hlam hρ hCenv Φ hΦint henv hball
  have he0 : (0 : ℝ) ≤ Real.exp (-(ρ ^ 2) / (8 * lam)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(ρ ^ 2) / (8 * lam)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    rw [div_nonpos_iff]
    exact Or.inr ⟨by linarith [sq_nonneg ρ], by linarith⟩
  exact tail_absorb n τ M Cpair Cenv (Real.exp (-(ρ ^ 2) / (8 * lam)))
    (Cpair * τ ^ (-(1 : ℝ) / 2)) (|∫ z, Φ z|) hτ hτM hCp hCenv he0 he1 le_rfl hcensus

/-! ###############################################################################
    ### §C — THE HEADLINE: `H_far` with the off-ball estimate discharged.
    ############################################################################### -/

/-- **★★★ `hfar_of_ballrate_offBallEnv_ftc` — `H_far` WITH THE OFF-BALL ESTIMATE DISCHARGED.**  For the
    full-domain rate `R c s = ∫ z, g c s z`, given
      • (hFTC)  the FTC-in-`c` bridge `Φ(u+h,s) − Φ(u,s) = ∫ c in u..(u+h), ∫ z, g c s z`,
      • (hgint) integrability of `g c s` for each far position,
      • (hlam)  a positive Gaussian width `lam c s`,
      • (henv)  the OFF-BALL single-Gaussian envelope `|g c s z| ≤ Cenv·gaussDdim (lam c s) z` (`ρ ≤ ‖z‖`),
      • (hball) the ON-BALL rate bound `|∫_{ball 0 ρ} g c s z| ≤ Cpair·(c−s)^{−1/2}` (the `hballrate` shape),
    the far-envelope `H_far` holds with `C_far = Cpair + Cenv·(√2)ⁿ·√(h+ε)`:
        `∀ s ∈ Ioo (u−ε) u, |Φ(u+h,s) − Φ(u,s)| ≤ C_far·h·(u−s)^{−1/2}` .
    Route: `far_rate_of_ball_and_gaussEnv` supplies the full-domain `(c−s)`-form `hrate` at each far
    position (`τ = c−s`, `M = h+ε`, since `c ≤ u+h`, `s > u−ε` ⟹ `0 < c−s ≤ h+ε`); `hfar_of_ballrate_ftc`
    (J4-967) then integrates it in `c`.  NOT `a₁ = R/6`. -/
theorem hfar_of_ballrate_offBallEnv_ftc {n : ℕ}
    (Φouter : ℝ → ℝ → ℝ) (g : ℝ → ℝ → Point n → ℝ) (lam : ℝ → ℝ → ℝ)
    (u ε h ρ Cpair Cenv : ℝ)
    (hε : 0 < ε) (hh : 0 ≤ h) (hρ : 0 ≤ ρ) (hCp : 0 ≤ Cpair) (hCenv : 0 ≤ Cenv)
    (hFTC : ∀ s ∈ Set.Ioo (u - ε) u,
        Φouter (u + h) s - Φouter u s = ∫ c in u..(u + h), ∫ z, g c s z)
    (hgint : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h), Integrable (g c s) volume)
    (hlam : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h), 0 < lam c s)
    (henv : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        ∀ z : Point n, ρ ≤ ‖z‖ → |g c s z| ≤ Cenv * gaussDdim (lam c s) z)
    (hball : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        |∫ z in Metric.ball (0 : Point n) ρ, g c s z| ≤ Cpair * (c - s) ^ (-(1 : ℝ) / 2)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |Φouter (u + h) s - Φouter u s|
        ≤ (Cpair + Cenv * (Real.sqrt 2 ^ n * Real.sqrt (h + ε))) * h
            * (u - s) ^ (-(1 : ℝ) / 2) := by
  set Cfar := Cpair + Cenv * (Real.sqrt 2 ^ n * Real.sqrt (h + ε)) with hCfar
  have hCfar_nn : 0 ≤ Cfar := by rw [hCfar]; positivity
  -- the full-domain `(c−s)`-form rate `hrate`, from the off-ball census bridge.
  have hrate : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
      |∫ z, g c s z| ≤ Cfar * (c - s) ^ (-(1 : ℝ) / 2) := by
    intro s hs c hc
    have hsu : s < u := hs.2
    have hcu : u ≤ c := hc.1
    have hτ : 0 < c - s := by linarith
    have hτM : c - s ≤ h + ε := by linarith [hc.2, hs.1]
    exact far_rate_of_ball_and_gaussEnv ρ (lam c s) Cenv Cpair (c - s) (h + ε) (g c s)
      (hlam s hs c hc) hρ hCenv hCp hτ hτM (hgint s hs c hc) (henv s hs c hc) (hball s hs c hc)
  exact QIQTH.HFarFromBallrate.hfar_of_ballrate_ftc Φouter (fun c s => ∫ z, g c s z)
    u ε h Cfar hε hh hCfar_nn hFTC hrate

/-! ###############################################################################
    ### §D — non-vacuity (the hypothesis bundle is jointly satisfiable, genuinely active).
    ############################################################################### -/

/-- **Non-vacuity (TEETH) of `hfar_of_ballrate_offBallEnv_ftc`.**  The full bundle {FTC bridge,
    integrability, positive width, OFF-BALL Gaussian envelope, ON-BALL rate} is JOINTLY satisfiable at the
    genuine Gaussian rate integrand `g c s z := gaussDdim 1 z` with `Φouter c s := c` (`u=0, ε=1, h=1, ρ=1,
    Cpair=√2, Cenv=1, lam=1`, `0<n` immaterial): `∫ z, g c s z = 1` (total Gaussian mass), so the FTC
    bridge is `1 = ∫ c in 0..1, 1`; the off-ball envelope holds with EQUALITY (`Cenv=1, lam=1`, genuinely
    ACTIVE — not `0 ≤ 0`); the ball rate holds since ball mass `≤ 1 ≤ √2·(c−s)^{−1/2}` on `c−s ≤ 2`; and
    the finite difference `Φouter(0+1) s − Φouter 0 s = 1 ≠ 0` (teeth: the far envelope is genuinely
    nonzero, the off-ball tail constant `Cenv·(√2)ⁿ·√2 > 0` genuinely enters).  NOT `a₁ = R/6`. -/
theorem hfar_of_ballrate_offBallEnv_ftc_hyp_satisfiable :
    ∃ (Φouter : ℝ → ℝ → ℝ) (g : ℝ → ℝ → Point n → ℝ) (lam : ℝ → ℝ → ℝ)
      (u ε h ρ Cpair Cenv : ℝ),
      0 < ε ∧ 0 ≤ h ∧ 0 ≤ ρ ∧ 0 ≤ Cpair ∧ 0 ≤ Cenv ∧
      (∀ s ∈ Set.Ioo (u - ε) u,
          Φouter (u + h) s - Φouter u s = ∫ c in u..(u + h), ∫ z, g c s z) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h), Integrable (g c s) volume) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h), 0 < lam c s) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
          ∀ z : Point n, ρ ≤ ‖z‖ → |g c s z| ≤ Cenv * gaussDdim (lam c s) z) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
          |∫ z in Metric.ball (0 : Point n) ρ, g c s z| ≤ Cpair * (c - s) ^ (-(1 : ℝ) / 2)) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, Φouter (u + h) s - Φouter u s ≠ 0) := by
  refine ⟨fun c _ => c, fun _ _ z => gaussDdim 1 z, fun _ _ => 1,
    0, 1, 1, 1, Real.sqrt 2, 1,
    one_pos, zero_le_one, zero_le_one, Real.sqrt_nonneg 2, zero_le_one, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- FTC bridge: `(0+1) − 0 = ∫ c in 0..(0+1), ∫ z, gaussDdim 1 z = ∫ c in 0..1, 1 = 1`.
    intro s _
    have hmass : (∫ z : Point n, gaussDdim 1 z) = 1 := gaussDdim_integral_eq_one 1 one_pos
    simp only [hmass, zero_add, sub_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  · -- integrability of `gaussDdim 1`.
    intro _ _ _ _; exact gaussDdim_integrable 1 one_pos
  · -- positive width.
    intro _ _ _ _; exact one_pos
  · -- off-ball envelope, with EQUALITY (genuinely active).
    intro _ _ _ _ z _
    rw [one_mul, abs_of_nonneg (gaussDdim_nonneg 1 z)]
  · -- ball rate: ball mass `≤ 1 ≤ √2·(c−s)^{−1/2}` on `c−s ≤ 2`.
    intro s hs c hc
    have hsu : s < 0 := by have := hs.2; simpa using this
    have hcu : (0 : ℝ) ≤ c := by have := hc.1; simpa using this
    have hτ : (0 : ℝ) < c - s := by linarith
    have hτM : c - s ≤ (2 : ℝ) := by
      have h1 : c ≤ (0 : ℝ) + 1 := hc.2
      have h2 : (0 : ℝ) - 1 < s := hs.1
      linarith
    -- ball mass is nonneg and `≤ 1` (total Gaussian mass).
    have hnn : (0 : ℝ) ≤ ∫ z in Metric.ball (0 : Point n) 1, gaussDdim 1 z :=
      setIntegral_nonneg measurableSet_ball (fun z _ => gaussDdim_nonneg 1 z)
    have hle1 : (∫ z in Metric.ball (0 : Point n) 1, gaussDdim 1 z) ≤ 1 := by
      have hle : (∫ z in Metric.ball (0 : Point n) 1, gaussDdim 1 z) ≤ ∫ z, gaussDdim 1 z :=
        setIntegral_le_integral (gaussDdim_integrable 1 one_pos)
          (ae_of_all _ (fun z => gaussDdim_nonneg 1 z))
      exact hle.trans (le_of_eq (gaussDdim_integral_eq_one 1 one_pos))
    -- `1 ≤ √2·(c−s)^{−1/2}` from `one_le_sqrt_mul_rpow` (`M=2`), and `√2 = √2`.
    have hone : (1 : ℝ) ≤ Real.sqrt 2 * (c - s) ^ (-(1 : ℝ) / 2) :=
      one_le_sqrt_mul_rpow 2 (c - s) hτ hτM
    rw [abs_of_nonneg hnn]
    exact hle1.trans hone
  · -- teeth: `(0+1) − 0 = 1 ≠ 0`.
    intro s _
    norm_num

end QIQTH.HFarOffBallDischarge

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HFarOffBallDischarge
#print axioms one_le_sqrt_mul_rpow
#print axioms tail_absorb
#print axioms far_rate_of_ball_and_gaussEnv
#print axioms hfar_of_ballrate_offBallEnv_ftc
#print axioms hfar_of_ballrate_offBallEnv_ftc_hyp_satisfiable
end AxiomChecks
