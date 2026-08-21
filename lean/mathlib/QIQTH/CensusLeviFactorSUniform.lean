/-
  CensusLeviFactorSUniform — the `s`-UNIFORM lift of J4-942's per-`s` on-ball F-factor
  bounded+Lipschitz bundle (`CensusLeviFactorDischarge.levi_Ffactor_ball_regularity`), supplying
  EXACTLY the "uniform-in-`s` ON-ball bounded+Lipschitz `F`-regularity" that the J4-955/956 audit
  flagged as the DECISIVE missing capstone input for the modulo-G2 `hballrate` (C1) closure.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure carry-reduction / analysis-infrastructure brick.  No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable / conclusion-in-disguise hypothesis (satisfiability EXHIBITED below), no
  existing banked file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GAP (J4-955/956, gpt-5.6-sol high).  The modulo-G2 `hballrate` (C1) closure needs, over the
  census ball `‖z‖ < ρ`, an ON-BALL bounded+Lipschitz `F`-regularity
      `|F s z 0| ≤ M_on`   and   `|F s z 0 − F s w 0| ≤ L_on · dist z w`   (for `‖z‖,‖w‖ < ρ`)
  that is **UNIFORM over the time window `s ∈ Ioo (u-ε) u`**.  The census's `hSupp`/`hF` supply only an
  OFF-ball bound (`|F s z 0| ≤ MF` for `ρ ≤ ‖z‖`, J4-952), which gives NO information inside the ball;
  and — since the ball integral is LINEAR in `F` — a `Cpair` depending only on geometry canNOT be
  uniform over `F` unless a LOCAL NORM of `F` is part of the data (Sol point (B)).

  ## THE RESOLUTION (this file, under-crediting correction).  J4-942's
  `levi_Ffactor_ball_regularity` ALREADY builds precisely this ON-ball bounded+Lipschitz `F` bundle —
  but only at a FIXED `s`, with `s`-DEPENDENT constants `M_F = C_L·gaussDdim (2s) 0` and
  `L_F = L_E + K·2√s`.  It was banked BEFORE the `s`-uniformity requirement was identified, so its
  `s`-uniformity was never checked.  This file supplies the `s`-UNIFORM lift by a clean window
  floor/ceiling argument on those two `s`-dependent constants:
    • BOUNDEDNESS.  The peak constant `C_L·gaussDdim (2s) 0` blows up as `s ↓ 0`, but the window floor
      `s ≥ u - ε > 0` controls it: the banked `HeatResidualBound.B_le_MB` (peak-at-`0` +
      width-antitone) at the time floor `a := 2·(u-ε)` gives the `s`-UNIFORM constant
      `M_on := C_L·gaussDdim (2·(u-ε)) 0` for EVERY `s ∈ Ioo (u-ε) u` and EVERY `z` (the on-ball
      restriction is free slack).  This is the SAME mechanism J4-952 used for the OFF-ball `hF`.
    • LIPSCHITZ.  The resolvent constant `L_E + K·2√s` grows in `s`, but the window ceiling `s ≤ u`
      controls it via `√s ≤ √u`: `L_on := L_E + K·2√u` dominates every `L_E + K·2√s`, `s < u`.

  So the "MISSING INPUT" is DISCHARGED to the `s`-UNIFORM `LeviLipschitz` carries (the width-2
  `F`-domination `hFdom`, the Volterra `hVol`, the `E`-slice Lipschitz `hE1`, the integrability `hIz`,
  the inner-`ζ` slice difference `hSlice`), quantified over the window — the SAME
  `{hDuhamel, hDConv, hCConv}`-family analytic objects that J4-942/952 already reduce `F` to.  It is
  NOT a genuinely-new hypothesis beyond the Levi analytic data; the "LOCAL NORM of `F`" Sol demanded
  IS exactly that data (`C_L`, `L_E`, `K`).

  ## HONEST STATUS.  This brick converts J4-942's per-`s` on-ball bundle into the `s`-UNIFORM on-ball
  bundle the modulo-G2 `hballrate` capstone consumes, carrying only the `s`-uniform Levi carries.  It
  proves NONE of `{hballrate, hDuhamel, hDConv, hCConv}`: the residual glue-(3) items (CoV two-term
  fold + global truncation/measurability of `q₁,q₂`, τ↓0-uniform `chartFieldAmp` Lipschitz, uniform
  `|det|` lower bound, G2-threading) are untouched here.  `hDuhamel`/`hDConv` remain carried; `hCConv`
  unaffected.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.LeviLipschitz
import QIQTH.BoundaryAssembly
import QIQTH.ResidueBound
import QIQTH.HeatDuhamel

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.ResidueBound QIQTH.HeatDuhamel
open QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.CensusLeviFactorSUniform

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **★★★ `levi_Ffactor_ball_regularity_sUniform` — the `s`-UNIFORM on-ball bounded+Lipschitz
    `F`-regularity.**  The `s`-uniform lift of J4-942's per-`s`
    `CensusLeviFactorDischarge.levi_Ffactor_ball_regularity`.  From the `s`-UNIFORM `LeviLipschitz`
    carries over the time window — the width-2 `F`-domination `hFdom` on `(0,T]` (SAME object as J4-952),
    the Volterra `hVol`, the `E`-slice Lipschitz `hE1` (uniform `L_E`), the integrability `hIz`, the
    inner-`ζ` slice difference `hSlice` (uniform `K`) — plus the benign window side conditions
    `ε < u` (so `0 < u - ε`) and `u ≤ T`, the F-factor `z ↦ F s z 0` is bounded by the `s`-UNIFORM
    constant `M_on := C_L·gaussDdim (2·(u-ε)) 0` and pairwise-Lipschitz with the `s`-UNIFORM constant
    `L_on := L_E + K·2√u`, on the ball `‖·‖ < ρ`, UNIFORMLY over `s ∈ Ioo (u-ε) u`.
    Route: boundedness via `B_le_MB` at floor `a := 2·(u-ε)` (peak + width-antitone); Lipschitz via
    `resolvent_lipschitz_pointwise` at each `s`, ceilinged by `√s ≤ √u`.  This is EXACTLY the uniform
    on-ball `F`-input the modulo-G2 `hballrate` capstone (J4-955/956) flagged as missing.
    ⚠ NOT `a₁ = R/6`. -/
theorem levi_Ffactor_ball_regularity_sUniform
    (E F : ℝ → Point n → Point n → ℝ) (C_L Kc L_E T u ε ρ : ℝ)
    (hC_L : 0 ≤ C_L) (hKc : 0 ≤ Kc) (hL_E : 0 ≤ L_E)
    (hεu : ε < u) (huT : u ≤ T)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hVol : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        F s z 0 = - E s z 0 - heatConv E F s z 0)
    (hE1 : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z z' : Point n,
        |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * F r ζ 0) volume 0 s)
    (hSlice : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * F r ζ 0) - (∫ ζ, E (s - r) z' ζ * F r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) :
    ∃ M_on L_on : ℝ, 0 ≤ M_on ∧ 0 ≤ L_on ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < ρ → |F s z 0| ≤ M_on) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < ρ → ‖w‖ < ρ →
        |F s z 0 - F s w 0| ≤ L_on * dist z w) := by
  have hue : 0 < u - ε := by linarith
  have ha : 0 < 2 * (u - ε) := by linarith
  refine ⟨C_L * gaussDdim (2 * (u - ε)) (0 : Point n),
          L_E + Kc * (2 * Real.sqrt u),
          mul_nonneg hC_L (gaussDdim_nonneg _ _),
          by have : (0:ℝ) ≤ Kc * (2 * Real.sqrt u) := mul_nonneg hKc (by positivity); linarith,
          ?_, ?_⟩
  · -- BOUNDEDNESS: `s`-uniform via `B_le_MB` at floor `a := 2·(u-ε)`.
    intro s hs z _
    have hlo : u - ε ≤ s := le_of_lt hs.1
    have hsT : s ≤ T := le_trans (le_of_lt hs.2) huT
    have hfloor : 2 * (u - ε) / 2 ≤ s := by
      have h2 : 2 * (u - ε) / 2 = u - ε := by ring
      rw [h2]; exact hlo
    exact B_le_MB F C_L T (2 * (u - ε)) hC_L hFdom ha s hfloor hsT z
  · -- LIPSCHITZ: per-`s` resolvent bound, ceilinged by `√s ≤ √u`.
    intro s hs z w _ _
    have hs0 : 0 < s := lt_trans hue hs.1
    have hbnd := resolvent_lipschitz_pointwise E F s Kc L_E z w hs0 hKc
      (hVol s hs z) (hVol s hs w) (hE1 s hs z w) (hIz s hs z) (hIz s hs w) (hSlice s hs z w)
    -- `L_E + Kc·2√s ≤ L_E + Kc·2√u` since `s ≤ u`.
    have hsqrt : Real.sqrt s ≤ Real.sqrt u := Real.sqrt_le_sqrt (le_of_lt hs.2)
    have hcoef : L_E + Kc * (2 * Real.sqrt s) ≤ L_E + Kc * (2 * Real.sqrt u) := by
      have : Kc * (2 * Real.sqrt s) ≤ Kc * (2 * Real.sqrt u) :=
        mul_le_mul_of_nonneg_left (by linarith) hKc
      linarith
    calc |F s z 0 - F s w 0|
        ≤ (L_E + Kc * (2 * Real.sqrt s)) * dist z w := hbnd
      _ ≤ (L_E + Kc * (2 * Real.sqrt u)) * dist z w :=
          mul_le_mul_of_nonneg_right hcoef dist_nonneg

/-- **★★★ `levi_Ffactor_ball_regularity_sUniform_ball` — the `Metric.ball` phrasing.**  Identical to
    `levi_Ffactor_ball_regularity_sUniform` but with the on-ball hypotheses written as
    `z ∈ Metric.ball 0 ρ` (`= ‖z‖ < ρ`), matching the capstone's `Metric.ball` binder shape.
    ⚠ NOT `a₁ = R/6`. -/
theorem levi_Ffactor_ball_regularity_sUniform_ball
    (E F : ℝ → Point n → Point n → ℝ) (C_L Kc L_E T u ε ρ : ℝ)
    (hC_L : 0 ≤ C_L) (hKc : 0 ≤ Kc) (hL_E : 0 ≤ L_E)
    (hεu : ε < u) (huT : u ≤ T)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hVol : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        F s z 0 = - E s z 0 - heatConv E F s z 0)
    (hE1 : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z z' : Point n,
        |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * F r ζ 0) volume 0 s)
    (hSlice : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * F r ζ 0) - (∫ ζ, E (s - r) z' ζ * F r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) :
    ∃ M_on L_on : ℝ, 0 ≤ M_on ∧ 0 ≤ L_on ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∈ Metric.ball (0 : Point n) ρ, |F s z 0| ≤ M_on) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∈ Metric.ball (0 : Point n) ρ,
        ∀ w ∈ Metric.ball (0 : Point n) ρ,
        |F s z 0 - F s w 0| ≤ L_on * dist z w) := by
  obtain ⟨M_on, L_on, hMnn, hLnn, hB, hL⟩ :=
    levi_Ffactor_ball_regularity_sUniform E F C_L Kc L_E T u ε ρ
      hC_L hKc hL_E hεu huT hFdom hVol hE1 hIz hSlice
  refine ⟨M_on, L_on, hMnn, hLnn, ?_, ?_⟩
  · intro s hs z hz
    exact hB s hs z (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  · intro s hs z hz w hw
    exact hL s hs z w (by simpa [Metric.mem_ball, dist_zero_right] using hz)
      (by simpa [Metric.mem_ball, dist_zero_right] using hw)

/-! ###############################################################################
    ### NON-VACUITY (TEETH) — the `s`-uniform Levi-carry bundle is jointly satisfiable.
    ############################################################################### -/

/-- **Non-vacuity of `levi_Ffactor_ball_regularity_sUniform` — TEETH.**  The full `s`-uniform
    hypothesis bundle `{hC_L, hKc, hL_E, ε<u, u≤T, hFdom, hVol, hE1, hIz, hSlice}` is jointly
    satisfiable by the degenerate zero resolvent `E = F = 0` at `C_L = Kc = L_E = 0`, `T = 2`, `u = 2`,
    `ε = 1` (so `ε < u`, `u ≤ T`, `0 < u - ε = 1`): the Volterra identity is `0 = -0 - heatConv 0 0`,
    every bound is `0 ≤ (nonneg)`, and the integrand is `0`.  Confirms the reduction is NOT vacuously
    quantified.  ⚠ NOT `a₁ = R/6`. -/
theorem levi_Ffactor_ball_regularity_sUniform_satisfiable :
    ∃ (E F : ℝ → Point n → Point n → ℝ) (C_L Kc L_E T u ε : ℝ),
      0 ≤ C_L ∧ 0 ≤ Kc ∧ 0 ≤ L_E ∧ ε < u ∧ u ≤ T ∧
      (∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        F s z 0 = - E s z 0 - heatConv E F s z 0) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z z' : Point n,
        |E s z 0 - E s z' 0| ≤ L_E * dist z z') ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * F r ζ 0) volume 0 s) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * F r ζ 0) - (∫ ζ, E (s - r) z' ζ * F r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) := by
  refine ⟨fun _ _ _ => 0, fun _ _ _ => 0, 0, 0, 0, 2, 2, 1,
    le_refl _, le_refl _, le_refl _, by norm_num, le_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s _ _ z y; simp
  · intro s _ z; simp [heatConv]
  · intro s _ z z'; simpa using dist_nonneg
  · intro s _ z
    simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 s)
  · intro s _ z z' r hr
    have h1 : (0 : ℝ) ≤ (s - r) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by linarith [hr.2]) _
    have : (0 : ℝ) ≤ 0 * dist z z' * (s - r) ^ (-(1 : ℝ) / 2) := by
      simpa using (le_refl (0:ℝ))
    simpa using this

end QIQTH.CensusLeviFactorSUniform

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusLeviFactorSUniform
#print axioms levi_Ffactor_ball_regularity_sUniform
#print axioms levi_Ffactor_ball_regularity_sUniform_ball
#print axioms levi_Ffactor_ball_regularity_sUniform_satisfiable
end AxiomChecks
