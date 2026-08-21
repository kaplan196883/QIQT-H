/-
  HFarFromBallrate — the exact CHARACTERIZATION of the `hCross` far-piece `H_far` as the
  FINITE-DIFFERENCE (integrated-in-`c`) form of the on-ball trace-RATE carry `hballrate`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE bridge brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## THE OBJECTS.
    • `H_far` (the OPEN chart-CoV far envelope consumed by `hcross_mixed_second_diff_split_bound`,
      J4-927) is the FINITE DIFFERENCE in the OUTPUT time `c`:
          `∀ s ∈ Ioo (u−ε) u, |Φ(u+h, s) − Φ(u, s)| ≤ C_far·h·(u−s)^{−1/2}`,
      where `Φ(c, s) := ∫ z, A(c−s) x z · B s z y`.
    • `hballrate` (the interior on-ball rate, closed MODULO G2 by `hballrate_moduloG2`, J4-960) is the
      POINTWISE-in-`c` DERIVATIVE (rate) bound, UNIFORM over the near strip `c = a ∈ Icc u (u+h)`:
          `∃ ρ Cpair, ∀ s ∈ Ioo (u−ε) u, ∀ a ∈ Icc u (u+h),
             |∫ z in ball 0 ρ, ∂_τ(kernel)(a−s)·F s z| ≤ Cpair·(a−s)^{−1/2}`.

  ## THE RELATIONSHIP (this file; gpt-5.6-sol high adversarial audit 2026-08-22).  `H_far` is
  REDUCIBLE to `hballrate` — it is the `c`-INTEGRAL of the `hballrate` rate — but this is an
  IMPLICATION, NOT an equivalence and NOT "the same content" as the on-ball `hballrate` alone.  Two
  substantive analytic obligations sit between them:
    (i)  an FTC-in-`c` bridge `Φ(u+h,s) − Φ(u,s) = ∫ c in u..(u+h), R(c,s)` (differentiation-carry
         family `{hDuhamel, hDConv}`), and
    (ii) an OFF-BALL spatial estimate: `hballrate` integrates over `ball 0 ρ`, whereas `Φ`'s `z`-integral
         is over ALL `z`.  Generically `∂_c Φ = R_ball + R_off`, so the bridge with only the BALL rate
         `R = R_ball` ADDITIONALLY asserts the off-ball contribution vanishes/cancels — a SEPARATE
         obligation, typically yielding `C_far = Cpair + C_off`, NOT the exact `Cpair`.
  Writing `R(c, s)` for the (ball-truncated) `hballrate` rate integrand (so `hballrate` is exactly
  `|R(c,s)| ≤ Cpair·(c−s)^{−1/2}` for `c ∈ Icc u (u+h)`) and GIVEN the full-domain FTC bridge
  `Φ(u+h,s) − Φ(u,s) = ∫ c in u..(u+h), R(c,s)`,
      `|Φ(u+h,s) − Φ(u,s)| = |∫_u^{u+h} R(c,s) dc| ≤ ∫_u^{u+h} Cpair·(c−s)^{−1/2} dc`
      `                    ≤ ∫_u^{u+h} Cpair·(u−s)^{−1/2} dc = Cpair·h·(u−s)^{−1/2}`,
  since `c ≥ u > s ⟹ (c−s)^{−1/2} ≤ (u−s)^{−1/2}` (rpow antitone in the base, nonpos exponent).  So
  the ADAPTER yields `H_far` with `C_far := Cpair` from a rate hypothesis `hrate` of the `hballrate`
  shape — but only once the (full-domain, off-ball-inclusive) FTC bridge is supplied as `hFTC`.

  ## WHAT THIS DOES — AND DOES NOT — DO.  `hfar_of_ballrate_ftc` (and its convolution specialization
  `hfar_of_ballrate_ftc_conv`) are the FINAL formal ADAPTER: they PROVE the exact live `H_far` argument
  shape from (i) a `hballrate`-shaped pointwise-in-`c` rate hypothesis `hrate` and (ii) an FTC-in-`c`
  identity `hFTC`.  Consequently `H_far` is NOT a wall separately-open BEYOND `{hballrate + full-domain
  FTC/differentiation + off-ball contribution}`: once a concrete full-domain FTC/decomposition and an
  off-ball bound are in hand, `H_far` is no longer an independent capstone wall.  But `hballrate` ALONE
  does NOT close `H_far` (per Sol): the FTC identification and ESPECIALLY the off-ball estimate are
  substantive analytic obligations, not carrier bookkeeping.  This file DOES NOT supply the FTC bridge
  for the concrete `Φ` (it is carried as `hFTC`), DOES NOT supply the off-ball estimate, and DOES NOT
  discharge `H_far` top-level.  It discharges NONE of `{hballrate, hDuhamel, hDConv, hCConv}` as a
  top-level τ-carry.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature

open MeasureTheory
open QIQTH.Curvature

namespace QIQTH.HFarFromBallrate

/-- **★★★ `hfar_of_ballrate_ftc` — `H_far` from the `hballrate` rate + an FTC-in-`c` bridge.**
    For ANY `Φ, R : ℝ → ℝ → ℝ`, given `0 < ε`, `0 ≤ h`, `0 ≤ Cpair`,
      • (hFTC)  the FTC-in-`c` identity `Φ(u+h, s) − Φ(u, s) = ∫ c in u..(u+h), R c s`
        (the differentiation carry — finite difference = integral of the output-time rate), and
      • (hrate) the `hballrate`-shaped pointwise-in-`c` rate `|R c s| ≤ Cpair·(c−s)^{−1/2}` for
        `c ∈ Icc u (u+h)`,
    the far-envelope `H_far` holds with `C_far = Cpair`:
        `∀ s ∈ Ioo (u−ε) u, |Φ(u+h, s) − Φ(u, s)| ≤ Cpair·h·(u−s)^{−1/2}`.
    Route: rewrite by `hFTC`, then the `c`-integral of `R` is bounded by the CONSTANT majorant
    `Cpair·(u−s)^{−1/2}` (via `(c−s)^{−1/2} ≤ (u−s)^{−1/2}`, `Real.rpow_le_rpow_of_nonpos`), whose
    interval integral over `[u, u+h]` is `Cpair·(u−s)^{−1/2}·h`.  NOT `a₁ = R/6`. -/
theorem hfar_of_ballrate_ftc (Φ R : ℝ → ℝ → ℝ) (u ε h Cpair : ℝ)
    (hε : 0 < ε) (hh : 0 ≤ h) (hCp : 0 ≤ Cpair)
    (hFTC : ∀ s ∈ Set.Ioo (u - ε) u, Φ (u + h) s - Φ u s = ∫ c in u..(u + h), R c s)
    (hrate : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        |R c s| ≤ Cpair * (c - s) ^ (-(1 : ℝ) / 2)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |Φ (u + h) s - Φ u s| ≤ Cpair * h * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro s hs
  have hsu : s < u := hs.2
  have hus : 0 < u - s := by linarith
  -- constant majorant `C = Cpair·(u−s)^{−1/2}` for `R · s` on `Ι u (u+h)`.
  have hconst : ∀ c ∈ Set.uIoc u (u + h),
      ‖R c s‖ ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2) := by
    intro c hc
    rw [Set.uIoc_of_le (by linarith)] at hc
    have hcIcc : c ∈ Set.Icc u (u + h) := ⟨le_of_lt hc.1, hc.2⟩
    rw [Real.norm_eq_abs]
    refine le_trans (hrate s hs c hcIcc) ?_
    have hmono : (c - s) ^ (-(1 : ℝ) / 2) ≤ (u - s) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hus (by linarith [hc.1]) (by norm_num)
    exact mul_le_mul_of_nonneg_left hmono hCp
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const hconst
  have hh' : |(u + h) - u| = h := by rw [add_sub_cancel_left, abs_of_nonneg hh]
  rw [hh'] at hbnd
  rw [hFTC s hs, ← Real.norm_eq_abs]
  calc ‖∫ c in u..(u + h), R c s‖
      ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2) * h := hbnd
    _ = Cpair * h * (u - s) ^ (-(1 : ℝ) / 2) := by ring

/-- **★★★ `hfar_of_ballrate_ftc_conv` — the EXACT live `H_far` argument shape.**  Specializes
    `hfar_of_ballrate_ftc` to the frozen-convolution inner integral `Φ(c, s) := ∫ z, A(c−s) x z · B s z y`,
    producing EXACTLY the `H_far` hypothesis consumed by `hcross_mixed_second_diff_split_bound` (J4-927):
        `∀ s ∈ Ioo (u−ε) u,
           |(∫ z, A(u+h−s) x z · B s z y) − (∫ z, A(u−s) x z · B s z y)| ≤ Cpair·h·(u−s)^{−1/2}`,
    from the FTC-in-`c` bridge `hFTC` (finite difference = `∫ c in u..(u+h), R c s`) and the
    `hballrate` rate `hrate`.  NOT `a₁ = R/6`. -/
theorem hfar_of_ballrate_ftc_conv {n : ℕ}
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (R : ℝ → ℝ → ℝ)
    (u ε h Cpair : ℝ) (hε : 0 < ε) (hh : 0 ≤ h) (hCp : 0 ≤ Cpair)
    (hFTC : ∀ s ∈ Set.Ioo (u - ε) u,
        (∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y)
          = ∫ c in u..(u + h), R c s)
    (hrate : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        |R c s| ≤ Cpair * (c - s) ^ (-(1 : ℝ) / 2)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |(∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y)|
        ≤ Cpair * h * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hgen := hfar_of_ballrate_ftc
    (fun c s => ∫ z, A (c - s) x z * B s z y) R u ε h Cpair hε hh hCp
    (by intro s hs; simpa using hFTC s hs) hrate
  intro s hs
  simpa using hgen s hs

/-- **Non-vacuity (TEETH) of the `hfar_of_ballrate_ftc` hypothesis bundle.**  The FTC bridge `hFTC`
    and the `hballrate`-shaped rate `hrate` are JOINTLY satisfiable at the GENUINELY SINGULAR witness
        `R c s := (c − s)^{−1/2}`,   `Φ c s := ∫ cc in (0:ℝ)..c, (cc − s)^{−1/2}`,
    with `u = 0, ε = 1, h = 1, Cpair = 1`.  The FTC identity holds because `Φ 0 s = ∫ cc in 0..0 = 0`
    (so the finite difference IS the `c`-integral), and the rate bound holds with EQUALITY
    (`|（c−s)^{−1/2}| = 1·(c−s)^{−1/2}`, the τ^{−1/2} envelope genuinely ACTIVE — NOT `0 ≤ 0`), with the
    rate integrand `R (u+h) s = (1−s)^{−1/2} ≠ 0` on the far window.  Confirms the bridge is not
    vacuously conditioned.  NOT `a₁ = R/6`. -/
theorem hfar_of_ballrate_ftc_hyp_satisfiable :
    ∃ (Φ R : ℝ → ℝ → ℝ) (u ε h Cpair : ℝ),
      0 < ε ∧ 0 ≤ h ∧ 0 ≤ Cpair ∧
      (∀ s ∈ Set.Ioo (u - ε) u, Φ (u + h) s - Φ u s = ∫ c in u..(u + h), R c s) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
          |R c s| ≤ Cpair * (c - s) ^ (-(1 : ℝ) / 2)) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, R (u + h) s ≠ 0) := by
  refine ⟨fun c s => ∫ cc in (0 : ℝ)..c, (cc - s) ^ (-(1 : ℝ) / 2),
    fun c s => (c - s) ^ (-(1 : ℝ) / 2), 0, 1, 1, 1,
    one_pos, zero_le_one, zero_le_one, ?_, ?_, ?_⟩
  · -- FTC bridge: `Φ (0+1) s − Φ 0 s = ∫ c in 0..(0+1), (c−s)^{−1/2}`.
    intro s _
    simp only [intervalIntegral.integral_same, sub_zero]
  · -- rate bound, with EQUALITY (envelope genuinely active).
    intro s hs c hc
    have hcs : (0 : ℝ) < c - s := by
      have h1 : (0 : ℝ) ≤ c := by
        have := hc.1; simpa using this
      have h2 : s < 0 := by have := hs.2; simpa using this
      linarith
    rw [one_mul, abs_of_nonneg (Real.rpow_nonneg hcs.le _)]
  · -- teeth: `R (0+1) s = (1−s)^{−1/2} ≠ 0` on the far window.
    intro s hs
    have h2 : s < 0 := by have := hs.2; simpa using this
    have hpos : (0 : ℝ) < (0 + 1) - s := by simp; linarith
    exact ne_of_gt (Real.rpow_pos_of_pos hpos _)

end QIQTH.HFarFromBallrate

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HFarFromBallrate
#print axioms hfar_of_ballrate_ftc
#print axioms hfar_of_ballrate_ftc_conv
#print axioms hfar_of_ballrate_ftc_hyp_satisfiable
end AxiomChecks
