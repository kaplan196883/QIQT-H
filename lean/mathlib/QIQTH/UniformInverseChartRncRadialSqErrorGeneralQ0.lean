/-
  UniformInverseChartRncRadialSqErrorGeneralQ0 — J4-1005: the TWO-SIDED `rncRadialSq` near-isometry
  comparison error, generalized from `HerrHminCoercivity`/`InverseChartDisplacement`'s base-point-`0`
  statement (`chartW0_rncRadialSq_error`) to a GENERAL base point `q₀`, by TRANSPLANTING that theorem's
  own proof verbatim (substituting `z ↦ p - q₀`, `chartW0_displacement ↦
  UniformInverseChartBaseSlotDisplacementGeneralQ0`'s J4-1004 quadratic base-slot displacement bound).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  exactly the "re-derive the two-sided `rncRadialSq` comparison error at general `q₀`" scope item this
  campaign's own J4-1004 dispatch named as next.  It does NOT touch `kPrime`, `heatHessMult`, `hcomp`,
  `herr_gate`/`hmin_gate` literally (those additionally need the compact-set-`K` GATE re-threaded — `K`
  here is `closedBall q₀ 1`, baked into `uniformInverseChart`'s THIRD argument, not an arbitrary `hK` —
  and the base-slot change-of-variables wired into `hcomp`'s literal `∫z`/`∫s` integral shape; NEITHER is
  attempted here).  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none
  equal to the conclusion, no existing file edited.  `hCConv`/`hcomp` NOT closed.  `a₁ = R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PRECISE ANSWER TO THE STANDING QUESTION (does J4-1004's ONE-SIDED bound suffice, or is the
  REVERSE direction separately needed?).

  ANSWER: the ONE-SIDED quadratic base-slot displacement bound
      `‖Φ p q₀ + (p − q₀)‖ ≤ C·‖p − q₀‖²`,   `Φ p q₀ := uniformInverseChart g gi hC (isCompact_closedBall
        q₀ 1) p q₀`
  (J4-1004, `UniformInverseChartBaseSlotDisplacementGeneralQ0.uniformInverseChart_baseSlot_quadratic_
  displacement_general_q0`) SUFFICES BY ITSELF — no reverse-direction displacement input is needed.  This
  is because the base-`0` theorem `chartW0_rncRadialSq_error` ITSELF is derived from ONLY the ONE-SIDED
  `chartW0_displacement` (`‖W₀ z + z‖ ≤ C_W‖z‖²`, EXACTLY the same one-sided shape).  The "two-sidedness"
  of `chartW0_rncRadialSq_error`'s CONCLUSION (both `≤` directions comparing `rncRadialSq(Φ)` against
  `rncRadialSq(displacement)`) comes not from a two-sided INPUT but from applying the coordinatewise
  expansion lemma `rncRadialSq_add_le (v e) : rncRadialSq (v+e) ≤ rncRadialSq v + 2n(‖v‖‖e‖) + n‖e‖²`
  TWICE, in BOTH directions: once to `W = (-z) + b` (giving the UPPER bound on `rncRadialSq W`) and once
  to `-z = W + (-b)` (giving the UPPER bound on `rncRadialSq z`, i.e. the LOWER bound on `rncRadialSq W`)
  — a purely algebraic "run the same one-sided expansion lemma from both sides" trick, NOT a genuinely
  distinct geometric input.  `rncRadialSq`, `rncRadialSq_add_le`, `rncRadialSq_neg`, `norm_sq_le_rncRadialSq`,
  `rncRadialSq_le_nsq` are ALL basepoint-agnostic (pure functions of a `Point n` vector — `rncRadialSq v :=
  ∑ i, (v i)²` — taking no basepoint argument), so the ENTIRE proof of `chartW0_rncRadialSq_error`
  transplants VERBATIM with `z ↦ u := p − q₀` and `W ↦ Φ p q₀`.  Sympy-verified
  (`docs/qg_roadmap/rnc_sympy/herrhmin_generalq0_transplant.py`): the coordinatewise expansion
  `rncRadialSq(W) − rncRadialSq(u) = −2⟨u,b⟩ + rncRadialSq(b)` is a pure function of `(u,b)` with `u`
  FREE (no property beyond its norm and the residual bound `‖b‖ ≤ C‖u‖²` is used).  Sol (`gpt-5.6-sol`,
  high, 2026-08-22) independently confirmed GO: "no conceptual gap; any friction should be elaboration,
  normalization, or rewriting only."

  ## WHAT LANDS (ns `QIQTH.UniformInverseChartRncRadialSqErrorGeneralQ0`).
    • ★★★ `uniformInverseChart_rncRadialSq_error_general_q0` — THE PAYOFF: a single `r > 0`, `L ≥ 0`
      such that for every `p` with `‖p − q₀‖ < r` (UNRESTRICTED — no compact-set membership needed,
      mirroring J4-1004's unconditional-in-`p` displacement bound):
        `rncRadialSq(p−q₀) − L·‖p−q₀‖·rncRadialSq(p−q₀)
           ≤ rncRadialSq(Φ p q₀) ≤ rncRadialSq(p−q₀) + L·‖p−q₀‖·rncRadialSq(p−q₀)`,
      `Φ p q₀ := uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀`.  Literally generalizes
      `InverseChartDisplacement.chartW0_rncRadialSq_error` (`q₀ = 0`-only) to a GENERAL base point.

  ## HONEST DISTANCE (what remains before this feeds `herr_gate`/`hmin_gate`/`hcomp`'s `nb` obligation at
  general `q₀`).  Two SEPARATE, non-trivial items, unchanged from J4-1004's own honest-distance note:
    (i) the COMPACT-SET GATE re-threading — `HerrHminCoercivity`'s `herr_gate`/`hmin_gate` are stated for
        an ARBITRARY fixed compact `K` (the base point ranges over `z ∈ K`), whereas the theorem here uses
        `K := closedBall q₀ 1`, which VARIES with `q₀` (the base point IS `q₀`, not a free-ranging `z ∈
        K`).  Generalizing `herr_gate`/`hmin_gate` themselves to "per-`q₀` gate ball" form, and reconciling
        that shape against `hcomp`'s literal per-base-point `K`-membership demand, is a separate wiring
        step, NOT attempted here.
    (ii) the actual base-slot CHANGE OF VARIABLES into `hcomp`'s literal `∫z`/`∫s` integral shape (the
        `nb`/near-carry obligation) — this theorem supplies the POINTWISE comparison input that CoV would
        need, but does not perform the CoV itself.
  `hCConv` NOT closed.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.UniformInverseChartBaseSlotDisplacementGeneralQ0
import QIQTH.InverseChartDisplacement
import QIQTH.NearIsometryBudget
import QIQTH.AmplitudeDataOnCollar

open Filter
open QIQTH.Curvature QIQTH.ExpMap QIQTH.RadialDistance QIQTH.HeatResidualBound
open QIQTH.AmplitudeDataOnCollar
open scoped Topology

namespace QIQTH.UniformInverseChartRncRadialSqErrorGeneralQ0

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE PAYOFF — the two-sided `rncRadialSq` near-isometry error at a GENERAL `q₀`.
    ############################################################################### -/

/-- **★★★ `uniformInverseChart_rncRadialSq_error_general_q0`.**  THE TWO-SIDED near-isometry error at a
    GENERAL base point `q₀`, transplanted VERBATIM from `InverseChartDisplacement.
    chartW0_rncRadialSq_error`'s proof (`z ↦ p − q₀`) using J4-1004's one-sided quadratic base-slot
    displacement bound as the sole geometric input (NO reverse-direction displacement input needed — see
    the file docstring for why).  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_rncRadialSq_error_general_q0
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∀ p : Point n, ‖p - q₀‖ < r →
      rncRadialSq (p - q₀) - L * ‖p - q₀‖ * rncRadialSq (p - q₀)
          ≤ rncRadialSq (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀)
      ∧ rncRadialSq (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀)
          ≤ rncRadialSq (p - q₀) + L * ‖p - q₀‖ * rncRadialSq (p - q₀) := by
  obtain ⟨rd, hrd, C_W, hCW0, hD1⟩ :=
    QIQTH.UniformInverseChartBaseSlotDisplacementGeneralQ0.uniformInverseChart_baseSlot_quadratic_displacement_general_q0
      g gi hC q₀
  refine ⟨min rd 1, lt_min hrd one_pos, 2 * (n : ℝ) * C_W + 3 * (n : ℝ) * C_W ^ 2,
    by positivity, ?_⟩
  intro p hpr
  have hzrd : ‖p - q₀‖ < rd := lt_of_lt_of_le hpr (min_le_left _ _)
  have hz1 : ‖p - q₀‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hpr (min_le_right _ _))
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set z : Point n := p - q₀ with hzdef
  set W : Point n := uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀ with hWdef
  -- `hD1` supplies `‖W + z‖ ≤ C_W * ‖z‖^2`; rewrite to the `‖z‖ * ‖z‖` form used below.
  have hb0 : ‖W + z‖ ≤ C_W * ‖z‖ * ‖z‖ := by
    have h := hD1 p hzrd
    rw [← hWdef, ← hzdef] at h
    calc ‖W + z‖ ≤ C_W * ‖z‖ ^ 2 := h
      _ = C_W * ‖z‖ * ‖z‖ := by ring
  set b : Point n := W + z with hbdef
  have hb : ‖b‖ ≤ C_W * ‖z‖ * ‖z‖ := hb0
  have hWeq : W = -z + b := by rw [hbdef]; abel
  have hzsq : ‖z‖ ^ 2 ≤ rncRadialSq z := norm_sq_le_rncRadialSq z
  have hz3 : ‖z‖ ^ 3 ≤ ‖z‖ * rncRadialSq z := by nlinarith [hzsq, norm_nonneg z]
  have hz4 : ‖z‖ ^ 4 ≤ ‖z‖ * rncRadialSq z := by
    have s1 : ‖z‖ ^ 4 ≤ ‖z‖ ^ 2 * rncRadialSq z := by nlinarith [hzsq, sq_nonneg (‖z‖)]
    have s2 : ‖z‖ ^ 2 * rncRadialSq z ≤ ‖z‖ * rncRadialSq z := by
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg z)
        (by linarith [hz1] : (0 : ℝ) ≤ 1 - ‖z‖)) (rncRadialSq_nonneg z)]
    linarith [s1, s2]
  have hzb : ‖z‖ * ‖b‖ ≤ C_W * (‖z‖ * rncRadialSq z) := by
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg z), hz3, hCW0, norm_nonneg z]
  have hbsq : ‖b‖ ^ 2 ≤ C_W ^ 2 * (‖z‖ * rncRadialSq z) := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg b) hb 2, hz4, sq_nonneg C_W]
  have hWn : ‖W‖ ≤ (1 + C_W) * ‖z‖ := by
    have h1 : ‖W‖ ≤ ‖z‖ + ‖b‖ := by
      rw [hWeq]
      calc ‖-z + b‖ ≤ ‖-z‖ + ‖b‖ := norm_add_le _ _
        _ = ‖z‖ + ‖b‖ := by rw [norm_neg]
    have hb1 : ‖b‖ ≤ C_W * ‖z‖ := by
      have hstep : C_W * ‖z‖ * ‖z‖ ≤ C_W * ‖z‖ * 1 :=
        mul_le_mul_of_nonneg_left hz1 (mul_nonneg hCW0 (norm_nonneg z))
      nlinarith [hb, hstep]
    nlinarith [h1, hb1]
  have hWb : ‖W‖ * ‖b‖ ≤ C_W * (1 + C_W) * (‖z‖ * rncRadialSq z) := by
    have hmul : ‖W‖ * ‖b‖ ≤ ((1 + C_W) * ‖z‖) * (C_W * ‖z‖ * ‖z‖) :=
      mul_le_mul hWn hb (norm_nonneg b) (mul_nonneg (by linarith [hCW0]) (norm_nonneg z))
    nlinarith [hmul, hz3, mul_nonneg hCW0 (by linarith [hCW0] : (0 : ℝ) ≤ 1 + C_W)]
  have hneg : rncRadialSq (-z) = rncRadialSq z := rncRadialSq_neg z
  -- the two `rncRadialSq_add_le` inequalities.
  have hU : rncRadialSq W ≤ rncRadialSq z + 2 * (n : ℝ) * (‖z‖ * ‖b‖) + (n : ℝ) * ‖b‖ ^ 2 := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_add_le (-z) b
    rw [hneg, norm_neg, ← hWeq] at h
    exact h
  have hLo : rncRadialSq z ≤ rncRadialSq W + 2 * (n : ℝ) * (‖W‖ * ‖b‖) + (n : ℝ) * ‖b‖ ^ 2 := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_add_le W (-b)
    rw [norm_neg, show W + -b = -z from by rw [hWeq]; abel, hneg] at h
    exact h
  refine ⟨?_, ?_⟩
  · -- lower
    nlinarith [hLo, mul_le_mul_of_nonneg_left hWb (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hbsq hn0, hn0, hCW0, norm_nonneg z, rncRadialSq_nonneg z]
  · -- upper
    nlinarith [hU, mul_le_mul_of_nonneg_left hzb (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hbsq hn0, hn0, hCW0, norm_nonneg z, rncRadialSq_nonneg z,
      mul_nonneg (mul_nonneg (mul_nonneg hn0 (sq_nonneg C_W)) (norm_nonneg z)) (rncRadialSq_nonneg z)]

end QIQTH.UniformInverseChartRncRadialSqErrorGeneralQ0

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.UniformInverseChartRncRadialSqErrorGeneralQ0
#print axioms uniformInverseChart_rncRadialSq_error_general_q0
end AxiomChecks

/-! ###############################################################################
    ## J4-1005 LEDGER — the two-sided `rncRadialSq` comparison error at GENERAL `q₀`.
    ###############################################################################

  ANSWERS THE STANDING QUESTION.  J4-1004's ONE-SIDED quadratic base-slot displacement bound SUFFICES
  by itself — no reverse-direction displacement input is separately needed.  `chartW0_rncRadialSq_error`
  at `q₀ = 0` is itself derived from ONLY a one-sided displacement bound (`chartW0_displacement`); its
  TWO-SIDED conclusion comes from applying the basepoint-agnostic coordinatewise expansion lemma
  `rncRadialSq_add_le` TWICE (once each direction), not from a two-sided geometric input.  The whole
  proof is a pure function of `(‖u‖, C)` for `u := p − q₀` — VERIFIED symbolically
  (`docs/qg_roadmap/rnc_sympy/herrhmin_generalq0_transplant.py`) and confirmed by Sol (`gpt-5.6-sol`,
  high, 2026-08-22, GO).

  WHAT LANDS.  `uniformInverseChart_rncRadialSq_error_general_q0` — the two-sided near-isometry error
  `rncRadialSq(p−q₀) − L‖p−q₀‖rncRadialSq(p−q₀) ≤ rncRadialSq(Φ p q₀) ≤ rncRadialSq(p−q₀) +
  L‖p−q₀‖rncRadialSq(p−q₀)` at GENERAL `q₀`, `Φ p q₀ := uniformInverseChart g gi hC (isCompact_closedBall
  q₀ 1) p q₀`, UNRESTRICTED in `p` (no compact-membership side condition — mirrors J4-1004's
  unconditional-in-`p` shape).  Proved by transplanting `InverseChartDisplacement.
  chartW0_rncRadialSq_error`'s Lean proof verbatim (`z ↦ p−q₀`).

  WHAT REMAINS (HONEST DISTANCE, unchanged from J4-1004's own note).
    (i) the compact-set-`K` GATE re-threading: `herr_gate`/`hmin_gate` (`HerrHminCoercivity.lean`) are
        stated for an ARBITRARY fixed `K` ranging over `z ∈ K`; here `K := closedBall q₀ 1` VARIES with
        the base point `q₀` itself. Reconciling the two shapes into a genuinely general-`q₀` `herr_gate`/
        `hmin_gate` is a separate wiring step.
    (ii) the base-slot CHANGE OF VARIABLES wired into `hcomp`'s literal `∫z`/`∫s` integral shape (the
        `nb`/near-carry obligation) — this brick supplies the pointwise comparison input CoV would need,
        not the CoV itself.

  `hCConv` NOT closed.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.
-/
