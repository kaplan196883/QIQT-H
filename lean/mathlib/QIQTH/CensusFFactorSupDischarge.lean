/-
  CensusFFactorSupDischarge — DISCHARGE the off-ball F-factor sup carry `hF` of
  `censusBound_of_geometry_gate_supp_F_ballRate_anyS` (J4-951) to the width-2 Levi domination.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure carry-reduction brick: it eliminates the ABSTRACT F-factor sup hypothesis `hF` of the
  most-discharged any-`S` census capstone in favour of the SAME width-2 Levi Gaussian domination
  (`hFdom`) that the rest of the F-factor chain already carries (the intended
  `{hDuhamel, hDConv, hCConv}`-family object).  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis (satisfiability EXHIBITED below), none equal to the conclusion, no existing
  banked file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT `hF` IS.  The capstone `censusBound_of_geometry_gate_supp_F_ballRate_anyS` takes, alongside
  the standard geometry and the small-radius gate record, the OFF-BALL F-factor sup bound
      `hF : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF`
  for a NONNEGATIVE constant `MF` UNIFORM over the time-window `s ∈ Ioo (u - ε) u`.

  ## THE MECHANISM (banked, `B_le_MB`).  For any `F` satisfying the width-2 Gaussian domination on a
  time strip `(0, T]`
      `hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y, |F s z y| ≤ C_L · gaussDdim (2 s) (z - y)`,
  the banked `HeatResidualBound.B_le_MB` gives, for ANY time floor `a > 0` and `a/2 ≤ s ≤ T`, the
  `s`-UNIFORM peak/width bound `|F s z 0| ≤ C_L · gaussDdim a 0` (∀ z).  On the OPEN window
  `s ∈ Ioo (u - ε) u` with `0 < u - ε` and `u ≤ T` we have `u - ε ≤ s ≤ T`, so taking `a := 2·(u-ε)`
  (floor `a/2 = u-ε ≤ s`) the constant `MF := C_L · gaussDdim (2·(u-ε)) 0` works — UNIFORMLY in `s`,
  for EVERY `z` (in particular off any ball `ρ ≤ ‖z‖`, so the off-ball restriction is free slack).

  ## HONEST STATUS.  `hF` is DISCHARGED to `{ hFdom (width-2 Levi domination on (0,T]), ε < u, u ≤ T }`.
  The width-2 Levi domination `hFdom` is the SAME object the CensusLeviFactorDischarge chain reduces the
  F-factor to (intended `{hDuhamel, hDConv, hCConv}`-family); `ε < u` and `u ≤ T` are the benign
  time-window side conditions (the window sits strictly inside `(0, T]`).  This ELIMINATES `hF` as a
  standalone carry from the capstone's live dependency list, leaving only
  `{ geometry {hg, hg0, hu, h0Kmem}, small-radius gate D (D.r ≤ rAmp), hSupp, C1 hballrate, C2 hΦint }`
  plus the width-2 Levi domination.  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.BoundaryAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.ResidueBound
open QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.CensusFFactorSupDischarge

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **★★★ `hF_of_leviWidth2Dom` — the off-ball F-factor sup `hF` DISCHARGED to the width-2 Levi
    domination.**  For ANY `F : ℝ → Point n → Point n → ℝ` satisfying the width-2 Gaussian domination
    `hFdom` on a time strip `(0, T]`, and benign time-window side conditions `ε < u` (so `0 < u - ε`)
    and `u ≤ T`, there EXISTS a NONNEGATIVE constant `MF` such that the EXACT `hF` binder of
    `censusBound_of_geometry_gate_supp_F_ballRate_anyS` (J4-951) holds:
      `∀ s ∈ Set.Ioo (u - ε) u, ∀ z, ρ ≤ ‖z‖ → |F s z 0| ≤ MF`.
    Route: `MF := C_L · gaussDdim (2·(u-ε)) 0` via the banked `B_le_MB` (peak-bound + width-antitone),
    at the time floor `a := 2·(u-ε)` — UNIFORM in `s`, for EVERY `z` (the off-ball `ρ ≤ ‖z‖` is unused
    slack).  ⚠ NOT `a₁ = R/6`. -/
theorem hF_of_leviWidth2Dom (F : ℝ → Point n → Point n → ℝ) (C_L T u ε ρ : ℝ)
    (hC_L : 0 ≤ C_L)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hεu : ε < u) (huT : u ≤ T) :
    ∃ MF : ℝ, 0 ≤ MF ∧
      ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF := by
  have hue : 0 < u - ε := by linarith
  refine ⟨C_L * gaussDdim (2 * (u - ε)) (0 : Point n),
    mul_nonneg hC_L (gaussDdim_nonneg _ _), ?_⟩
  intro s hs z _
  have hlo : u - ε ≤ s := le_of_lt hs.1
  have hsT : s ≤ T := le_trans (le_of_lt hs.2) huT
  have ha : 0 < 2 * (u - ε) := by linarith
  have hfloor : 2 * (u - ε) / 2 ≤ s := by
    have : 2 * (u - ε) / 2 = u - ε := by ring
    rw [this]; exact hlo
  exact B_le_MB F C_L T (2 * (u - ε)) hC_L hFdom ha s hfloor hsT z

/-! ###############################################################################
    ### NON-VACUITY (TEETH) — the discharged bundle is jointly satisfiable.
    ############################################################################### -/

/-- **Non-vacuity of `hF_of_leviWidth2Dom` — TEETH.**  The hypothesis bundle
    `{hC_L, hFdom, ε < u, u ≤ T}` is jointly satisfiable by a GENUINE positive configuration: the zero
    factor `F ≡ 0` with `C_L := 0` satisfies the width-2 domination (`|0| = 0 ≤ 0·gaussDdim …`), and
    `ε := 1`, `u := 2`, `T := 2` give `ε < u` and `u ≤ T`.  Confirms the reduction is NOT vacuously
    quantified.  ⚠ NOT `a₁ = R/6`. -/
theorem hF_of_leviWidth2Dom_satisfiable :
    ∃ (F : ℝ → Point n → Point n → ℝ) (C_L T u ε ρ : ℝ),
      0 ≤ C_L ∧
      (∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) ∧
      ε < u ∧ u ≤ T := by
  refine ⟨(fun _ _ _ => (0 : ℝ)), 0, 2, 2, 1, 1, le_refl _, ?_, by norm_num, le_refl _⟩
  intro s _ _ z y
  simp

end QIQTH.CensusFFactorSupDischarge

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusFFactorSupDischarge
#print axioms hF_of_leviWidth2Dom
#print axioms hF_of_leviWidth2Dom_satisfiable
end AxiomChecks
