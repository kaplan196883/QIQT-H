/-
  WidthCompose32 — J4-674 census brick: the **width-3/2 production compose** shape adapter.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHY THIS FILE EXISTS (the J4-674 width verdict, in one paragraph).

  The two Duhamel/convolution capstone suppliers
    • `ConvCarriesDischarge.hDConv_gatedWitnessN1_of_delta_final`  (its `hDConv_of_delta_final` core), and
    • `DuhamelLimitWiring.hDuhamel_leviSeries_final`  (its `hDuhamel_final` core)
  each demand a near-diagonal kernel domination in the HARDCODED width-3/2 shape

      `hAdom : ∀ τ, 0 < τ → ∀ p q, |H τ p q| ≤ (A₀ + A₁·τ)·√(3/2)ⁿ·gaussDdim (3/2·τ) (p−q)`.

  This width slot is NOT parametric — it is written `gaussDdim (3 / 2 * τ)` with the explicit
  `Real.sqrt (3 / 2) ^ n` prefactor.  (J4-673's "width-2-locked" sweep was a textual FALSE NEGATIVE:
  it searched `baseKernelW`, but the supplier interfaces express width via `gaussDdim (3/2·τ)`, and
  the width-3/2 PRODUCER `WidthParametricGoodGate.gatedWitnessN1_hEboundW_le_of_good_W` is width-
  PARAMETRIC — instantiate `W_a := 3/2` and its output `baseKernelW (3/2) 0 τ p q` IS
  `gaussDdim (3/2·τ) (p−q)` by `baseKernelW_zero_apply`.)

  This file lands the **shape-transfer adapter** proving that any width-parametric `baseKernelW (3/2) 0`
  domination — with a constant envelope `Cenv` — is EXACTLY the `hAdom` binder shape the two capstones
  demand (the `√(3/2)ⁿ` prefactor is absorbed by choosing `A₀ := Cenv/√(3/2)ⁿ`, `A₁ := 0`).  The
  residual obstruction is thereby isolated to a SINGLE honest input: a global `baseKernelW (3/2) 0`
  domination of the concrete witness kernel (the `hAdom global` wall).  NOT `a₁ = R/6`.

  All theorems `std-3` (`propext`, `Classical.choice`, `Quot.sound`).  No `sorry`, no new axioms.
-/
import QIQTH.ParametrixHEboundWiring

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.ResidueBound
open QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound

namespace QIQTH.WidthCompose32

variable {n : ℕ}

/-- **★ (J4-674) The width-3/2 production compose (global form).**  A constant-envelope
    `baseKernelW (3/2) 0` domination of any kernel `H` is EXACTLY the hardcoded width-3/2 `hAdom`
    binder demanded by both `hDConv_of_delta_final` and `hDuhamel_final`: the `√(3/2)ⁿ` prefactor is
    absorbed into `A₀ := Cenv/√(3/2)ⁿ` (with `A₁ := 0`).  This isolates the remaining obstruction to
    the single input `hW` (a global width-3/2 domination of the concrete witness — the `hAdom global`
    wall).  NOT `a₁ = R/6`; the width transfer is pure algebra. -/
theorem hAdom_width32_of_baseKernelW_global
    (H : ℝ → Point n → Point n → ℝ) (Cenv : ℝ) (hCenv : 0 ≤ Cenv)
    (hW : ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ Cenv * baseKernelW (3 / 2 : ℝ) (0 : ℝ) τ p q) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
      ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (3 / 2) := Real.sqrt_pos.mpr (by norm_num)
  have hpow_pos : (0 : ℝ) < Real.sqrt (3 / 2) ^ n := pow_pos hsqrt_pos n
  have hS : Real.sqrt (3 / 2) ^ n ≠ 0 := hpow_pos.ne'
  refine ⟨Cenv / Real.sqrt (3 / 2) ^ n, 0,
    div_nonneg hCenv (le_of_lt hpow_pos), le_refl 0, ?_⟩
  intro τ hτ p q
  have hb := hW τ hτ p q
  rw [baseKernelW_zero_apply] at hb
  calc |H τ p q|
      ≤ Cenv * gaussDdim (3 / 2 * τ) (p - q) := hb
    _ = (Cenv / Real.sqrt (3 / 2) ^ n + 0 * τ)
          * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
        field_simp
        ring

/-- **★ (J4-674) The width-3/2 production compose (finite-horizon form).**  The same transfer carrying
    the honest `τ ≤ t` restriction and the good-gate producer's exact `Cenv := max B₀ B₁·(1+t)`
    envelope: the width-parametric producer
    `gatedWitnessN1_hEboundW_le_of_good_W` (at `W_a := 3/2`) outputs
    `|H τ p q| ≤ (max B₀ B₁·(1+t))·baseKernelW (3/2) 0 τ p q` on `0 < τ ≤ t`, and this lemma repackages
    it into the width-3/2 `hAdom` binder shape on that same window.  The residual gap to the capstone's
    GLOBAL `hAdom` is exactly the `τ ≤ t → ∀ τ` extension (the labelled `hAdom global` wall). -/
theorem hAdom_width32_of_baseKernelW_horizon
    (H : ℝ → Point n → Point n → ℝ) (t B₀ B₁ : ℝ) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (ht : 0 ≤ t)
    (hW : ∀ τ, 0 < τ → τ ≤ t → ∀ p q : Point n,
        |H τ p q| ≤ (max B₀ B₁ * (1 + t)) * baseKernelW (3 / 2 : ℝ) (0 : ℝ) τ p q) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
      ∀ τ, 0 < τ → τ ≤ t → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (3 / 2) := Real.sqrt_pos.mpr (by norm_num)
  have hpow_pos : (0 : ℝ) < Real.sqrt (3 / 2) ^ n := pow_pos hsqrt_pos n
  have hS : Real.sqrt (3 / 2) ^ n ≠ 0 := hpow_pos.ne'
  have hCenv : (0 : ℝ) ≤ max B₀ B₁ * (1 + t) :=
    mul_nonneg (le_trans hB₀ (le_max_left _ _)) (by linarith)
  refine ⟨(max B₀ B₁ * (1 + t)) / Real.sqrt (3 / 2) ^ n, 0,
    div_nonneg hCenv (le_of_lt hpow_pos), le_refl 0, ?_⟩
  intro τ hτ hτt p q
  have hb := hW τ hτ hτt p q
  rw [baseKernelW_zero_apply] at hb
  calc |H τ p q|
      ≤ (max B₀ B₁ * (1 + t)) * gaussDdim (3 / 2 * τ) (p - q) := hb
    _ = ((max B₀ B₁ * (1 + t)) / Real.sqrt (3 / 2) ^ n + 0 * τ)
          * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
        field_simp
        ring

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/

end QIQTH.WidthCompose32
