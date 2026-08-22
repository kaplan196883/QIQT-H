/-
  UniformInverseChartBaseSlotDisplacementGeneralQ0 — J4-1004: the CONCRETE corollary of
  `BaseSlotDerivFromAntisymEvalSlot`, instantiated at `Φ := uniformInverseChart g gi hC
  (isCompact_closedBall q₀ 1)`.  Generalizes `ChartW0Fderiv.chartW0_hasFDerivAt_zero` /
  `BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center`/`chartW0_displacement` — previously proved
  ONLY at base point `q₀ = 0` — to a GENERAL base point `q₀`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It supplies
  the concrete geodesic-inverse-chart instance of the abstract `BaseSlotDerivFromAntisymEvalSlot` brick.
  It does NOT touch `kPrime`, `heatHessMult`, the Gaussian weight, the `∫z`/`∫s` integrals, `hcomp`, or
  `herr_gate`/`hmin_gate` (which additionally need `rncRadialSq`-comparison and the compact-set-`K` GATE
  machinery re-derived at general `q₀`, a further, separate step — see HONEST DISTANCE below).  No
  `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, none equal to the conclusion, no existing
  file edited.  `hCConv`/`hcomp` NOT closed.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel,
  hDConv, hCConv}`, UNCHANGED.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE THREE INGREDIENTS FED TO THE ABSTRACT BRICK (all already banked, general `q₀`).
    (F1) `uniformInverseChart_diag_eventually g gi hC q₀` (`HCompBaseSlotAntisymmetryConcrete`, J4-1003) —
         fixed-`K = closedBall q₀ 1` diagonal vanishing near `q₀`.
    (F3) `uniformInverseChart_jointContDiffAt_diag g gi hC q₀` (`UniformFlowCoherentChartReconciliation`,
         J4-856) — joint `ContDiffAt ℝ 2` at `(q₀,q₀)` for the SAME fixed `K`.
    (F4) the EVAL-slot normalization, upgraded from the already-banked `fderiv` EQUALITY
         `uniformInverseChart_slice_fderiv_id_diag g gi hC q₀` (`JointRNCRegularityInterfaceLocal`,
         J4-856/857) to `HasFDerivAt` form via `uniformInverseChart_slice_contDiffAt_diag`'s
         differentiability.
  Feeding these three to `BaseSlotDerivFromAntisymEvalSlot`'s Step A / Step B yields the base-slot
  derivative and the QUADRATIC base-slot displacement bound, both at a GENERAL `q₀` — genuinely new
  content not previously derivable from any single banked theorem (cp884-diagnosed gap, resolved by
  COMBINING the already-banked eval-slot fact with the already-banked antisymmetry-sum fact, per Sol
  `gpt-5.6-sol` high GO, 2026-08-22).

  ## WHAT LANDS (ns `QIQTH.UniformInverseChartBaseSlotDisplacementGeneralQ0`).
    • ★★ `uniformInverseChart_baseSlot_fderiv_neg_id_general_q0` — the base-slot derivative at a GENERAL
      `q₀`:  `HasFDerivAt (fun p => uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀)
        (-Id) q₀`.  Literally generalizes `ChartW0Fderiv.chartW0_hasFDerivAt_zero`
      (`q₀ = 0`-only) to a general base point.
    • ★★★ `uniformInverseChart_baseSlot_quadratic_displacement_general_q0` — THE PAYOFF: the base-slot
      displacement is QUADRATIC at a GENERAL `q₀`:
          `∃ r > 0, C ≥ 0, ∀ p, ‖p − q₀‖ < r →
            ‖uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀ + (p − q₀)‖ ≤ C * ‖p − q₀‖²`.
      Literally generalizes `BaseVaryingIFTPackage`'s `chartW0_displacement`-fed quadratic base
      displacement (`q₀ = 0`-only) to a general base point.

  ## HONEST DISTANCE (what remains before this generalizes `herr_gate`/`hmin_gate`/`hcomp`'s `nb`
  obligation to general `q₀`).  This is the DERIVATIVE/DISPLACEMENT layer only.  `herr_gate`/`hmin_gate`
  (`HerrHminCoercivity.lean`) additionally need: (i) the `rncRadialSq`-comparison machinery
  (`chartW0_rncRadialSq_error`'s two-sided error bound) re-derived at general `q₀` from THIS quadratic
  bound (currently only proved from the `q₀ = 0`-specific `ApproximatesLinearOn` bootstrap chain, a
  DIFFERENT, stronger route than the mean-value-twice technique used here — re-deriving the two-sided
  `L·‖z-q₀‖·rncRadialSq(z-q₀)`-style error from ONLY a one-sided quadratic bound is a separate,
  non-trivial step, NOT attempted here); (ii) the compact-set GATE (`z ∈ K`) re-threading, since `K` here
  is `closedBall q₀ 1` (varies with `q₀`), unlike `HerrHminCoercivity`'s arbitrary fixed `hK`; (iii) the
  actual base-slot change-of-variables into `hcomp`'s literal `∫z`/`∫s` integral shape.  `hCConv` NOT
  closed.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT
  `a₁ = R/6`.
-/
import Mathlib
import QIQTH.BaseSlotDerivFromAntisymEvalSlot
import QIQTH.HCompBaseSlotAntisymmetryConcrete
import QIQTH.JointRNCRegularityInterfaceLocal

open Filter
open QIQTH.Curvature QIQTH.ExpMap QIQTH.JointRNCRegularityLocal QIQTH.HeatResidualBound
open QIQTH.HCompBaseSlotAntisymmetryConcrete
open scoped Topology

namespace QIQTH.UniformInverseChartBaseSlotDisplacementGeneralQ0

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The (F4) upgrade — eval-slot `fderiv` equality (J4-856) → `HasFDerivAt`.
    ############################################################################### -/

/-- **(F4) upgrade.**  The banked `fderiv`-equality form of the eval-slot normalization
    (`uniformInverseChart_slice_fderiv_id_diag`) upgraded to `HasFDerivAt`, using differentiability
    from `uniformInverseChart_slice_contDiffAt_diag`.  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_evalSlot_hasFDerivAt_id_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    HasFDerivAt (fun v => uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀ v)
      (ContinuousLinearMap.id ℝ (Point n)) q₀ := by
  have hdiff : DifferentiableAt ℝ
      (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀) q₀ :=
    (uniformInverseChart_slice_contDiffAt_diag g gi hC q₀).differentiableAt (by norm_num)
  have hfd := hdiff.hasFDerivAt
  rwa [uniformInverseChart_slice_fderiv_id_diag g gi hC q₀] at hfd

/-! ###############################################################################
    ### The two payoffs — feeding (F1)/(F3)/(F4) to the abstract brick.
    ############################################################################### -/

/-- **★★ `uniformInverseChart_baseSlot_fderiv_neg_id_general_q0`.**  The base-slot derivative at a
    GENERAL base point `q₀`:  `HasFDerivAt (fun p => uniformInverseChart … p q₀) (-Id) q₀`.
    Generalizes `ChartW0Fderiv.chartW0_hasFDerivAt_zero` (`q₀ = 0`-only) to a general base point.
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_fderiv_neg_id_general_q0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    HasFDerivAt (fun p => uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀)
      (-(ContinuousLinearMap.id ℝ (Point n))) q₀ :=
  QIQTH.BaseSlotDerivFromAntisymEvalSlot.baseSlot_fderiv_neg_id_of_antisym_evalSlot
    (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1)) q₀
    (uniformInverseChart_diag_eventually g gi hC q₀)
    (uniformInverseChart_jointContDiffAt_diag g gi hC q₀)
    (uniformInverseChart_evalSlot_hasFDerivAt_id_diag g gi hC q₀)

/-- **★★★ `uniformInverseChart_baseSlot_quadratic_displacement_general_q0` — THE PAYOFF.**  The
    base-slot displacement of the concrete geodesic inverse chart is QUADRATIC at a GENERAL base point
    `q₀`:
        `∃ r > 0, C ≥ 0, ∀ p, ‖p − q₀‖ < r →
          ‖uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀ + (p − q₀)‖ ≤ C * ‖p − q₀‖²`.
    Generalizes `BaseVaryingIFTPackage`'s `chartW0_displacement`-derived quadratic base displacement
    (`q₀ = 0`-only) to a general base point — the precise gap cp884 diagnosed, resolved by combining the
    already-banked eval-slot normalization (J4-856/857) with the already-banked antisymmetry-sum fact
    (J4-1002/1003).  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_quadratic_displacement_general_q0
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : Point n, ‖p - q₀‖ < r →
        ‖uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀ + (p - q₀)‖
          ≤ C * ‖p - q₀‖ ^ 2 :=
  QIQTH.BaseSlotDerivFromAntisymEvalSlot.baseSlot_quadratic_displacement_of_antisym_evalSlot
    (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1)) q₀
    (uniformInverseChart_diag_eventually g gi hC q₀)
    (uniformInverseChart_jointContDiffAt_diag g gi hC q₀)
    (uniformInverseChart_evalSlot_hasFDerivAt_id_diag g gi hC q₀)

end QIQTH.UniformInverseChartBaseSlotDisplacementGeneralQ0

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.UniformInverseChartBaseSlotDisplacementGeneralQ0
#print axioms uniformInverseChart_evalSlot_hasFDerivAt_id_diag
#print axioms uniformInverseChart_baseSlot_fderiv_neg_id_general_q0
#print axioms uniformInverseChart_baseSlot_quadratic_displacement_general_q0
end AxiomChecks
