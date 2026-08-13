/-
  WhiteLeviMajorWire — J4-695: THE `hmajor` WIRE.  The width-`lam` per-term domination of the
  whitened Levi iterates that the width-generic M-test slot
  (`WhiteLeviMTestWidth.leviJoint_window_of_carries_width`) consumes — landed as the mechanical
  `k`-fold application of the banked convolution bound `iterConvW_bound`, then instantiated at the
  τ-gated whitened defect `whiteDefectKernel`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It wires the
  ALREADY-PROVEN width-`κ` iterated bound (`ParametrixHEboundWiring.iterConvW_bound`) into the exact
  `hmajor` shape the width-generic M-test consumes, and dissolves the whitened defect's affine `(1+t')`
  factor into a FIXED constant via the τ-gate (`whiteDefectKernel = 0` for `τ > 1`).  No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed, nothing wired into
  `QIQTH.lean` / `AxiomAudit`.

  ── WHAT THE `hmajor` SLOT IS.  `WhiteLeviMTestWidth.leviJoint_window_of_carries_width` takes
       `hmajor : ∀ u ∈ U, ∀ (k : ℕ) (τ : ℝ) (p q), 0 < τ → τ ≤ u →
                   |iterE E (k+1) τ p q| ≤ C^(k+1) · iterKernelW lam 0 (k+1) τ p q`
     and, MODULO the still-open termwise box continuity `htermBox`, emits the `hJoint` carry
     `∀ u ∈ U, ContinuousOn (fun p => leviSeries E p.1 p.2 0) (Ioc 0 u ×ˢ univ)`.  The banked
     `iterConvW_bound E lam 0 C hEbound hInt` gives EXACTLY `|iterE E k t x y| ≤ C^k·iterKernelW lam 0 k`
     for every `k ≥ 1`, `t > 0` — so setting `k := k+1` (`1 ≤ k+1`) IS the `hmajor` shape, with the
     window `(u ∈ U, τ ≤ u)` carried but unused (the bound is τ-uniform on `(0,∞)`).

  ── THE AFFINE DISSOLUTION (the honest new piece).  The whitened defect package
     (`WhiteGatePackageCombined.white_gate_package_combined`) lands the ONE-STEP bound with an affine
     time factor `C·(1+t')` on `τ ≤ t'` — NOT a fixed constant, so `iterConvW_bound` (which needs a
     single global constant) cannot ingest it directly.  But `whiteDefectKernel` is τ-GATED to `(0,1]`
     (`= 0` for `τ > 1`), so on its support `1 + t' ≤ 2` and the fixed constant `2C` works globally:
       • on `(0,1]`, `white_hEuni` gives `|whiteDefectKernel τ p q| ≤ 2C·gaussDdim(lam·τ)(p−q)`;
       • for `τ > 1`, `whiteDefectKernel = 0 ≤ 2C·baseKernelW lam 0 τ p q`.
     This is `white_hEbound_zero` — the α = 0 mirror of the banked α = −1/2 `white_hEbound_negHalf`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    • `hmajor_of_oneStep_window` — ★★ the GENERIC wire: from a fixed-constant width-`lam` one-step
      bound `hEbound` + the per-step integrability `hInt`, the exact `hmajor` slot shape for ANY `E`.
    • `white_hEbound_zero` — ★ the whitened α = 0 full-∀τ fixed-constant one-step bound.
    • `white_hInt_zero` — the α = 0 per-step integrability family at `whiteDefectKernel` (⚠ carries the
      single S1 measurability `hEmeas`, as every whitened integrability does).
    • `white_hmajor` — ★★★ the whitened `hmajor` at the τ-gated defect, from {`hpkg`, `hEmeas`}.
    • `white_leviJoint_window_modulo_termBox` — ★★★ the CAPSTONE: the whole width-`lam` `hJoint` carry
      for `whiteDefectKernel`, discharged down to EXACTLY `htermBox` (the surviving termwise-continuity
      residual) — the `hmajor` slot is GONE.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ParametrixHEboundWiring
import QIQTH.WhiteBridge
import QIQTH.WhiteLeviMTestWidth

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteLeviMTestWidth
open scoped Topology BigOperators

namespace QIQTH.WhiteLeviMajorWire

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (M1) — the GENERIC `hmajor` wire from the banked iterated bound.
    ############################################################################### -/

/-- **★★ `hmajor_of_oneStep_window` — THE GENERIC `hmajor` WIRE.**  From a FIXED-constant width-`lam`
    order-0 one-step bound `hEbound : |E τ p q| ≤ C·baseKernelW lam 0 τ p q` (all `τ > 0`) and the
    per-step integrability `hInt : IterConvIntegrableW E lam 0 C`, the exact `hmajor` slot shape of
    `WhiteLeviMTestWidth.leviJoint_window_of_carries_width`:
        `∀ u ∈ U, ∀ (k : ℕ) (τ) (p q), 0 < τ → τ ≤ u →
            |iterE E (k+1) τ p q| ≤ C^(k+1)·iterKernelW lam 0 (k+1) τ p q`.
    This IS the mechanical `k`-fold application of the banked `iterConvW_bound` (`k := k+1`, `1 ≤ k+1`);
    the window `(u ∈ U, τ ≤ u)` is carried but unused (the bound is τ-uniform).  Neither carried input
    is the conclusion.  NOT `a₁ = R/6`. -/
theorem hmajor_of_oneStep_window
    (E : ℝ → Point n → Point n → ℝ) (lam C : ℝ) (U : Set ℝ)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW lam (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW E lam (0 : ℝ) C) :
    ∀ u ∈ U, ∀ (k : ℕ) (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ u →
      |iterE E (k + 1) τ p q| ≤ C ^ (k + 1) * iterKernelW lam (0 : ℝ) (k + 1) τ p q :=
  fun _u _hu k τ p q hτ _hτu =>
    iterConvW_bound E lam (0 : ℝ) C hEbound hInt (k + 1) (Nat.le_add_left 1 k) τ hτ p q

/-! ###############################################################################
    ### (M2) — the whitened α = 0 fixed-constant one-step bound (affine dissolution).
    ############################################################################### -/

/-- **★ `white_hEbound_zero` — the whitened α = 0 FULL-∀τ fixed-constant one-step bound.**  From the
    capstone-`hpkgBound` affine shape `hpkg` (`|heatOp …| ≤ C·(1+t')·baseKernelW lam 0`), the τ-gated
    whitened defect obeys the FIXED-constant `2C` bound at every `τ > 0`:
        `|whiteDefectKernel κ hκ hKc S a b τ p q| ≤ 2C·baseKernelW lam 0 τ p q`.
    On `(0,1]` from `white_hEuni` (slice `t' = 1`); above the cap `whiteDefectKernel = 0 ≤ RHS`.  The
    α = 0 mirror of the banked `white_hEbound_negHalf`.  NOT `a₁ = R/6`. -/
theorem white_hEbound_zero (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ) (hC : 0 ≤ C)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q) :
    ∀ τ : ℝ, ∀ p q : Point n, 0 < τ →
      |whiteDefectKernel κ hκ hKc S a b τ p q| ≤ (2 * C) * baseKernelW lam (0 : ℝ) τ p q := by
  intro τ p q hτ
  by_cases hτ1 : τ ≤ 1
  · rw [baseKernelW_zero_apply]
    exact white_hEuni κ hκ hKc S a b C lam hpkg τ p q hτ hτ1
  · rw [whiteDefectKernel_zero_gt_one κ hκ hKc S a b (not_le.mp hτ1) p q, abs_zero,
      baseKernelW_zero_apply]
    exact mul_nonneg (by linarith) (QIQTH.ResidueBound.gaussDdim_nonneg _ _)

/-- **`white_hInt_zero` — the α = 0 per-step integrability family at `whiteDefectKernel`.**  Via the
    banked width-κ α-parametric producer `iterConvIntegrableW_of_bound_baseMeas_alpha_w` at `α = 0`,
    fed the fixed-constant `white_hEbound_zero`, the nonpositive-time vanishing, and the single carried
    S1 joint measurability `hEmeas`.  ⚠ CONDITIONAL on `hEmeas` (labelled; every whitened integrability
    is).  NOT `a₁ = R/6`. -/
theorem white_hInt_zero (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam : 0 < lam)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    IterConvIntegrableW (whiteDefectKernel κ hκ hKc S a b) lam (0 : ℝ) (2 * C) :=
  iterConvIntegrableW_of_bound_baseMeas_alpha_w
    (whiteDefectKernel κ hκ hKc S a b) lam (0 : ℝ) (2 * C) hlam (by norm_num)
    (fun τ p q hτ => white_hEbound_zero κ hκ hKc S a b C lam hC hpkg τ p q hτ)
    (whiteDefectKernel_zero_nonpos κ hκ hKc S a b)
    (whiteDefectKernel_stronglyMeasurable κ hκ hKc S a b hEmeas)

/-! ###############################################################################
    ### (M3) — the whitened `hmajor` + the capstone modulo `htermBox`.
    ############################################################################### -/

/-- **★★★ `white_hmajor` — THE WHITENED `hmajor`.**  The exact `hmajor` slot of
    `leviJoint_window_of_carries_width` at the τ-gated whitened defect, width `lam` (M-test constant
    `2C`), from {the capstone-`hpkgBound` `hpkg`, the single S1 `hEmeas`}:
        `∀ u ∈ U, ∀ (k) (τ) (p q), 0 < τ → τ ≤ u →
            |iterE (whiteDefectKernel …) (k+1) τ p q| ≤ (2C)^(k+1)·iterKernelW lam 0 (k+1) τ p q`.
    Route: `hmajor_of_oneStep_window` fed `white_hEbound_zero` + `white_hInt_zero`.  ⚠ CONDITIONAL on
    `hEmeas`.  NOT `a₁ = R/6`. -/
theorem white_hmajor (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam) (U : Set ℝ)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    ∀ u ∈ U, ∀ (k : ℕ) (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ u →
      |iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) τ p q|
        ≤ (2 * C) ^ (k + 1) * iterKernelW lam (0 : ℝ) (k + 1) τ p q := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  exact hmajor_of_oneStep_window (whiteDefectKernel κ hκ hKc S a b) lam (2 * C) U
    (fun τ p q hτ => white_hEbound_zero κ hκ hKc S a b C lam hC hpkg τ p q hτ)
    (white_hInt_zero κ hκ hKc S a b C lam hC hlam0 hpkg hEmeas)

/-- **★★★ `white_leviJoint_window_modulo_termBox` — THE CAPSTONE.**  For the τ-gated whitened defect
    at gate-parametric `{S, a, b, C, lam}` (`0 ≤ C`, `2 ≤ lam`, capstone-`hpkg`, S1 `hEmeas`), the
    WHOLE width-`lam` `hJoint` carry of `leviJoint_window_of_carries_width` is discharged down to
    EXACTLY the termwise-box continuity `htermBox`:
        `∀ u ∈ U, ContinuousOn (fun p => leviSeries (whiteDefectKernel …) p.1 p.2 0) (Ioc 0 u ×ˢ univ)`.
    The `hmajor` slot is GONE (supplied by `white_hmajor`); the only surviving M-test residual is
    `htermBox` (the whitened `iterE` termwise joint continuity — task-2 territory).  ⚠ CONDITIONAL on
    `hEmeas`.  NOT `a₁ = R/6`. -/
theorem white_leviJoint_window_modulo_termBox (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam) (U : Set ℝ)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    (htermBox : ∀ u ∈ U, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) u, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n =>
          iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) u ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ u ∈ U, ContinuousOn
      (fun p : ℝ × Point n => leviSeries (whiteDefectKernel κ hκ hKc S a b) p.1 p.2 0)
      (Set.Ioc (0 : ℝ) u ×ˢ (Set.univ : Set (Point n))) := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  exact leviJoint_window_of_carries_width (whiteDefectKernel κ hκ hKc S a b) (2 * C) lam
    (by linarith) hlam0 U
    (white_hmajor κ hκ hKc S a b C lam hC hlam2 U hpkg hEmeas)
    htermBox

#check @hmajor_of_oneStep_window
#check @white_hEbound_zero
#check @white_hInt_zero
#check @white_hmajor
#check @white_leviJoint_window_modulo_termBox

end QIQTH.WhiteLeviMajorWire

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteLeviMajorWire
#print axioms hmajor_of_oneStep_window
#print axioms white_hEbound_zero
#print axioms white_hInt_zero
#print axioms white_hmajor
#print axioms white_leviJoint_window_modulo_termBox
end AxiomChecks
