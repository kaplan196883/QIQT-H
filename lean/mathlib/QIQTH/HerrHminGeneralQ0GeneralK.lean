/-
  HerrHminGeneralQ0GeneralK — J4-1006: the compact-set-`K` GATE re-threading item J4-1004/1005's own
  dispatches named as remaining scope — generalizing `HerrHminCoercivity`'s (J4-455) `herr_gate`/
  `hmin_gate` from "eval point fixed at `0`, base point `z` ranging over an ARBITRARY FIXED compact `K`"
  to "eval point a GENERAL `q₀ ∈ interior K`, base point `p` ranging near `q₀`", for the SAME ARBITRARY
  FIXED `hK : IsCompact K` throughout (NOT `K := closedBall q₀ 1` varying with `q₀`, unlike J4-1004/1005).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `hCConv`/
  `hcomp` NOT closed.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PRECISE RECONCILIATION (Sol `gpt-5.6-sol`, high, 2026-08-22, GO, confirmed before writing Lean).

  J4-1004/1005's own honest-distance notes named item (i): `herr_gate`/`hmin_gate` are stated for an
  ARBITRARY FIXED `K` (base point `z` ranges over `z ∈ K`, eval point fixed at `0`), whereas J4-1004/1005
  fix `K := closedBall q₀ 1` (VARYING with `q₀`) and let the EVAL point be the general `q₀` instead.
  These are genuinely different slot assignments of `uniformInverseChart g gi hC hK : (base) → (eval) →
  Point n` (base = first argument, must be `∈ K` for the chart to be non-default; eval = second
  argument).  Reconciling them for a SINGLE arbitrary fixed `hK` requires re-deriving J4-1004/1005's
  three ingredients (F1 diagonal vanishing, F3 joint `ContDiffAt 2`, F4 eval-slot normalization) for that
  fixed `hK` instead of `isCompact_closedBall q₀ 1`.

  THE KEY FINDING (don't-undercredit): F3 and F4 ALREADY HAVE general-`K` versions banked
  (`UniformFlowCoherentChartReconciliationGeneralK.uniformInverseChart_jointContDiffAt_diag_generalK`,
  `JointRNCRegularityInterfaceLocalGeneralK.uniformInverseChart_slice_fderiv_id_diag_generalK` +
  `..._slice_contDiffAt_diag_generalK`), both quantified over an ARBITRARY compact `K` and interior base
  point `z₀ ∈ interior K` — the J4-884 generalization campaign already built exactly these.  Only F1
  (`HCompBaseSlotAntisymmetryConcrete.uniformInverseChart_diag_eventually`) lacked a general-`K` version;
  its proof uses ONLY `uniformInverseChart_huniformChart g gi hC hK` (already `∀ q ∈ K, …` for arbitrary
  `hK`) plus a neighbourhood of `q₀` inside `K` — for general `K` this neighbourhood is supplied directly
  by `q₀ ∈ interior K` (`interior K ∈ 𝓝 q₀`), a ROUTINE transplant, not new math (Sol-confirmed: "no
  global nonemptiness assumption on `interior K` is needed... compactness is irrelevant for this step").

  Feeding these three general-`K` ingredients to the ALREADY-ABSTRACT-in-`Φ` brick
  `BaseSlotDerivFromAntisymEvalSlot` (J4-1004) yields the base-slot derivative/displacement at general
  `q₀ ∈ interior K`, FIXED arbitrary `K` — literally generalizing J4-1004's `K := closedBall q₀ 1`-tied
  result.  Transplanting J4-1005's `rncRadialSq`-comparison algebra (verbatim, `Φ`-abstract in the sense
  that only the one-sided displacement bound feeds it) onto this general-`K` displacement bound yields the
  general-`K` two-sided `rncRadialSq` comparison error, from which `herr_gate`/`hmin_gate`'s exact
  derivation (shrink radius so `L‖·‖ ≤ 1/2`, upgrade via `rncRadialSq ≤ n‖·‖²`) transplants verbatim.

  ## THE UNIFORMITY QUESTION (Sol-confirmed, do NOT over-claim).  The result below is POINTWISE in `q₀`:
  `∀ q₀ ∈ interior K, ∃ r(q₀) > 0, L'(q₀) ≥ 0, ∀ p, ‖p − q₀‖ < r(q₀) → …` — each `q₀` gets its OWN
  constants.  Per Sol: this is the RIGHT foundational target now (sufficient whenever `q₀` is fixed
  before integrating/dominating over the displacement variable — the architecture the campaign's
  gate-vs-far-field re-engineering plan (J4-455's "Sol #22/J4-456" wall) actually needs, base point
  fixed per near-carry cell).  It is NOT automatically enough for a JOINT integral over `(q₀, p)` pairs
  demanding a SINGLE common radius/constant uniformly over `q₀` ranging in a compact subset — compactness
  of `K` does NOT by itself uniformize a pointwise `∀ q₀, ∃ r, L` statement (the estimate at one `q₀`
  says nothing about nearby centers without a jointly-continuous-in-`q₀` bound, which is NOT extracted
  here).  A uniform corollary over a compact `G ⊆ interior K` is a SEPARATE, NOT-attempted next step,
  flagged honestly rather than claimed.

  ALSO (Sol-confirmed, DO NOT over-claim): this does NOT supersede or literally generalize
  `herr_gate`/`hmin_gate` themselves — those work for `z` ranging over ALL of a fixed `K` (including its
  boundary, no `interior` hypothesis, eval point exactly `0`), and specialize this file's result to
  `q₀ = 0` ONLY under the extra hypothesis `0 ∈ interior K`.  This file is a DIFFERENT, complementary
  general-`q₀`-at-interior-points brick, useful for the near-carry `nb` architecture's per-base-point
  cells, not a drop-in replacement for the walled whole-`K` gates.

  ## WHAT LANDS (ns `QIQTH.HerrHminGeneralQ0GeneralK`), all for a SINGLE arbitrary fixed `hK : IsCompact K`.
    • `uniformInverseChart_diag_eventually_generalK` — (F1) general-`K` diagonal vanishing near `q₀ ∈
      interior K`.
    • `uniformInverseChart_evalSlot_hasFDerivAt_id_diag_generalK` — (F4) upgraded to `HasFDerivAt`.
    • `uniformInverseChart_baseSlot_fderiv_neg_id_generalK` / `..._quadratic_displacement_generalK` —
      Step A/B of `BaseSlotDerivFromAntisymEvalSlot`, fed F1/F3/F4, general-`K` analogue of J4-1004.
    • `uniformInverseChart_rncRadialSq_error_generalK` — THE two-sided `rncRadialSq` comparison error,
      general-`K` analogue of J4-1005.
    • `herr_gate_general_q0_generalK` / `hmin_gate_general_q0_generalK` / `herrHmin_gate_general_q0_generalK`
      — THE PAYOFF: the `HerrHminCoercivity`-style gate-restricted cubic error + coercivity, POINTWISE
      in `q₀ ∈ interior K`, for the SAME fixed `hK`.

  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.
-/
import Mathlib
import QIQTH.BaseSlotDerivFromAntisymEvalSlot
import QIQTH.JointRNCRegularityInterfaceLocalGeneralK
import QIQTH.InverseChartDisplacement
import QIQTH.AmplitudeDataOnCollar

open Filter
open QIQTH.Curvature QIQTH.ExpMap QIQTH.RadialDistance QIQTH.HeatResidualBound
open QIQTH.AmplitudeDataOnCollar
open scoped Topology

namespace QIQTH.HerrHminGeneralQ0GeneralK

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — (F1) general-`K` diagonal vanishing near an interior base point `q₀`.
    ############################################################################### -/

/-- **★ `uniformInverseChart_diag_eventually_generalK` — the (F1) discharge, general `K`.**  For an
    ARBITRARY FIXED compact `K` and `q₀ ∈ interior K`, the concrete inverse chart vanishes on the
    diagonal for every base point in a neighbourhood of `q₀`:
        `∀ᶠ q in 𝓝 q₀, uniformInverseChart g gi hC hK q q = 0`.
    Routine transplant of `HCompBaseSlotAntisymmetryConcrete.uniformInverseChart_diag_eventually`'s proof
    (there specialized to `K = closedBall q₀ 1`), using `interior K ∈ 𝓝 q₀` in place of `ball q₀ 1 ∈ 𝓝 q₀`.
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart_diag_eventually_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∀ᶠ q in 𝓝 q₀, uniformInverseChart g gi hC hK q q = 0 := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  have hmem : interior K ∈ 𝓝 q₀ := IsOpen.mem_nhds isOpen_interior hq₀
  filter_upwards [hmem] with q hq
  have hqK : q ∈ K := interior_subset hq
  obtain ⟨hgermC2, _⟩ := hspec q hqK
  have hgerm := (hgermC2 0 (by rw [norm_zero]; exact hδ₀)).1
  have h := hgerm.eq_of_nhds
  rwa [uniformFlowExp_zero g gi hC hK q hqK] at h

/-! ###############################################################################
    ### §2 — (F4) upgrade to `HasFDerivAt`, general `K`.
    ############################################################################### -/

/-- **(F4) upgrade, general `K`.**  The banked `fderiv`-equality general-`K` eval-slot normalization
    upgraded to `HasFDerivAt`, using differentiability from the general-`K` slice `ContDiffAt`.
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart_evalSlot_hasFDerivAt_id_diag_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    HasFDerivAt (fun v => uniformInverseChart g gi hC hK q₀ v)
      (ContinuousLinearMap.id ℝ (Point n)) q₀ := by
  have hdiff : DifferentiableAt ℝ (uniformInverseChart g gi hC hK q₀) q₀ :=
    (QIQTH.JointRNCRegularityLocalGeneralK.uniformInverseChart_slice_contDiffAt_diag_generalK
      g gi hC hK q₀ hq₀).differentiableAt (by norm_num)
  have hfd := hdiff.hasFDerivAt
  rwa [QIQTH.JointRNCRegularityLocalGeneralK.uniformInverseChart_slice_fderiv_id_diag_generalK
    g gi hC hK q₀ hq₀] at hfd

/-! ###############################################################################
    ### §3 — Step A/B of `BaseSlotDerivFromAntisymEvalSlot`, general `K`, general interior `q₀`.
    ############################################################################### -/

/-- **★★ `uniformInverseChart_baseSlot_fderiv_neg_id_generalK`.**  The base-slot derivative at a general
    interior base point `q₀ ∈ interior K`, for a SINGLE arbitrary fixed `hK`:
        `HasFDerivAt (fun p => uniformInverseChart g gi hC hK p q₀) (-Id) q₀`.
    General-`K` analogue of J4-1004's `..._general_q0` (there tied to `K = closedBall q₀ 1`).
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_fderiv_neg_id_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    HasFDerivAt (fun p => uniformInverseChart g gi hC hK p q₀)
      (-(ContinuousLinearMap.id ℝ (Point n))) q₀ :=
  QIQTH.BaseSlotDerivFromAntisymEvalSlot.baseSlot_fderiv_neg_id_of_antisym_evalSlot
    (uniformInverseChart g gi hC hK) q₀
    (uniformInverseChart_diag_eventually_generalK g gi hC hK hq₀)
    (uniformInverseChart_jointContDiffAt_diag_generalK
      g gi hC hK q₀ hq₀)
    (uniformInverseChart_evalSlot_hasFDerivAt_id_diag_generalK g gi hC hK hq₀)

/-- **★★★ `uniformInverseChart_baseSlot_quadratic_displacement_generalK` — THE PAYOFF.**  The base-slot
    displacement of the concrete geodesic inverse chart is QUADRATIC at a general interior base point
    `q₀ ∈ interior K`, for a SINGLE arbitrary fixed `hK`:
        `∃ r > 0, C ≥ 0, ∀ p, ‖p − q₀‖ < r → ‖uniformInverseChart g gi hC hK p q₀ + (p − q₀)‖ ≤ C‖p−q₀‖²`.
    General-`K` analogue of J4-1004's `..._general_q0` (there tied to `K = closedBall q₀ 1`).
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_quadratic_displacement_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : Point n, ‖p - q₀‖ < r →
        ‖uniformInverseChart g gi hC hK p q₀ + (p - q₀)‖ ≤ C * ‖p - q₀‖ ^ 2 :=
  QIQTH.BaseSlotDerivFromAntisymEvalSlot.baseSlot_quadratic_displacement_of_antisym_evalSlot
    (uniformInverseChart g gi hC hK) q₀
    (uniformInverseChart_diag_eventually_generalK g gi hC hK hq₀)
    (uniformInverseChart_jointContDiffAt_diag_generalK
      g gi hC hK q₀ hq₀)
    (uniformInverseChart_evalSlot_hasFDerivAt_id_diag_generalK g gi hC hK hq₀)

/-! ###############################################################################
    ### §4 — the two-sided `rncRadialSq` comparison error, general `K`, general interior `q₀`
    ###       (transplant of J4-1005's algebra onto §3's displacement bound).
    ############################################################################### -/

/-- **★★★ `uniformInverseChart_rncRadialSq_error_generalK`.**  THE TWO-SIDED near-isometry error at a
    general interior base point `q₀ ∈ interior K`, for a SINGLE arbitrary fixed `hK`, transplanted
    VERBATIM from `InverseChartDisplacement.chartW0_rncRadialSq_error` / `UniformInverseChartRnc
    RadialSqErrorGeneralQ0.uniformInverseChart_rncRadialSq_error_general_q0`'s proof (`z ↦ p − q₀`),
    using §3's general-`K` quadratic base-slot displacement bound as the sole geometric input.  NOT
    `a₁ = R/6`. -/
theorem uniformInverseChart_rncRadialSq_error_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∀ p : Point n, ‖p - q₀‖ < r →
      rncRadialSq (p - q₀) - L * ‖p - q₀‖ * rncRadialSq (p - q₀)
          ≤ rncRadialSq (uniformInverseChart g gi hC hK p q₀)
      ∧ rncRadialSq (uniformInverseChart g gi hC hK p q₀)
          ≤ rncRadialSq (p - q₀) + L * ‖p - q₀‖ * rncRadialSq (p - q₀) := by
  obtain ⟨rd, hrd, C_W, hCW0, hD1⟩ :=
    uniformInverseChart_baseSlot_quadratic_displacement_generalK g gi hC hK hq₀
  refine ⟨min rd 1, lt_min hrd one_pos, 2 * (n : ℝ) * C_W + 3 * (n : ℝ) * C_W ^ 2,
    by positivity, ?_⟩
  intro p hpr
  have hzrd : ‖p - q₀‖ < rd := lt_of_lt_of_le hpr (min_le_left _ _)
  have hz1 : ‖p - q₀‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hpr (min_le_right _ _))
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set z : Point n := p - q₀ with hzdef
  set W : Point n := uniformInverseChart g gi hC hK p q₀ with hWdef
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
  have hU : rncRadialSq W ≤ rncRadialSq z + 2 * (n : ℝ) * (‖z‖ * ‖b‖) + (n : ℝ) * ‖b‖ ^ 2 := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_add_le (-z) b
    rw [hneg, norm_neg, ← hWeq] at h
    exact h
  have hLo : rncRadialSq z ≤ rncRadialSq W + 2 * (n : ℝ) * (‖W‖ * ‖b‖) + (n : ℝ) * ‖b‖ ^ 2 := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_add_le W (-b)
    rw [norm_neg, show W + -b = -z from by rw [hWeq]; abel, hneg] at h
    exact h
  refine ⟨?_, ?_⟩
  · nlinarith [hLo, mul_le_mul_of_nonneg_left hWb (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hbsq hn0, hn0, hCW0, norm_nonneg z, rncRadialSq_nonneg z]
  · nlinarith [hU, mul_le_mul_of_nonneg_left hzb (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hbsq hn0, hn0, hCW0, norm_nonneg z, rncRadialSq_nonneg z,
      mul_nonneg (mul_nonneg (mul_nonneg hn0 (sq_nonneg C_W)) (norm_nonneg z)) (rncRadialSq_nonneg z)]

/-! ###############################################################################
    ### §5 — THE PAYOFF: `herr_gate`/`hmin_gate`-style gate-restricted bounds, general `q₀`, general `K`.
    ############################################################################### -/

/-- **★ `herr_gate_general_q0_generalK`.**  The gate-restricted cubic near-isometry error, at a general
    interior base point `q₀ ∈ interior K`, for a SINGLE arbitrary fixed `hK`:
        `∃ r > 0, L' ≥ 0, ∀ p, ‖p − q₀‖ < r →
          |rncRadialSq(uniformInverseChart g gi hC hK p q₀) − rncRadialSq(p − q₀)| ≤ L'·‖p − q₀‖³`.
    POINTWISE in `q₀` (constants may depend on `q₀`) — see the file docstring's uniformity discussion.
    `HerrHminCoercivity.herr_gate`'s derivation, transplanted verbatim onto §4. NOT `a₁ = R/6`. -/
theorem herr_gate_general_q0_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ r > (0 : ℝ), ∃ L' : ℝ, 0 ≤ L' ∧ ∀ p : Point n, ‖p - q₀‖ < r →
      |rncRadialSq (uniformInverseChart g gi hC hK p q₀) - rncRadialSq (p - q₀)| ≤ L' * ‖p - q₀‖ ^ 3 := by
  obtain ⟨r₀, hr₀, L, hL0, hbd⟩ := uniformInverseChart_rncRadialSq_error_generalK g gi hC hK hq₀
  refine ⟨r₀, hr₀, L * (n : ℝ), by positivity, ?_⟩
  intro p hpr
  obtain ⟨hlow, hup⟩ := hbd p hpr
  set W : Point n := uniformInverseChart g gi hC hK p q₀ with hWdef
  set z : Point n := p - q₀ with hzdef
  have hb0 : (0 : ℝ) ≤ rncRadialSq z := rncRadialSq_nonneg z
  have hle : rncRadialSq z ≤ (n : ℝ) * ‖z‖ ^ 2 := rncRadialSq_le_nsq z
  have hcoef : (0 : ℝ) ≤ L * ‖z‖ := mul_nonneg hL0 (norm_nonneg z)
  have herrbd : L * ‖z‖ * rncRadialSq z ≤ L * (n : ℝ) * ‖z‖ ^ 3 := by
    have := mul_le_mul_of_nonneg_left hle hcoef
    nlinarith [this]
  have habs : |rncRadialSq W - rncRadialSq z| ≤ L * ‖z‖ * rncRadialSq z :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  exact le_trans habs herrbd

/-- **★ `hmin_gate_general_q0_generalK`.**  The gate-restricted coercivity, at a general interior base
    point `q₀ ∈ interior K`, for a SINGLE arbitrary fixed `hK`:
        `∃ r > 0, ∀ p, ‖p − q₀‖ < r → ½·rncRadialSq(p − q₀) ≤ rncRadialSq(uniformInverseChart g gi hC hK p q₀)`.
    POINTWISE in `q₀`.  `HerrHminCoercivity.hmin_gate`'s derivation, transplanted verbatim onto §4.
    NOT `a₁ = R/6`. -/
theorem hmin_gate_general_q0_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ r > (0 : ℝ), ∀ p : Point n, ‖p - q₀‖ < r →
      (1 / 2 : ℝ) * rncRadialSq (p - q₀) ≤ rncRadialSq (uniformInverseChart g gi hC hK p q₀) := by
  obtain ⟨r₀, hr₀, L, hL0, hbd⟩ := uniformInverseChart_rncRadialSq_error_generalK g gi hC hK hq₀
  refine ⟨min r₀ (1 / (2 * (L + 1))), lt_min hr₀ (by positivity), ?_⟩
  intro p hpr
  set z : Point n := p - q₀ with hzdef
  have hpr₀ : ‖z‖ < r₀ := lt_of_lt_of_le hpr (min_le_left _ _)
  have hprL : ‖z‖ < 1 / (2 * (L + 1)) := lt_of_lt_of_le hpr (min_le_right _ _)
  obtain ⟨hlow, _⟩ := hbd p hpr₀
  have hb0 : (0 : ℝ) ≤ rncRadialSq z := rncRadialSq_nonneg z
  have hLz : L * ‖z‖ ≤ 1 / 2 := by
    have hstep : L * ‖z‖ ≤ L * (1 / (2 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hprL.le hL0
    have hbound : L * (1 / (2 * (L + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by linarith [hL0] : (0 : ℝ) < 2 * (L + 1))]; nlinarith [hL0]
    linarith
  have hprod : L * ‖z‖ * rncRadialSq z ≤ (1 / 2 : ℝ) * rncRadialSq z :=
    mul_le_mul_of_nonneg_right hLz hb0
  linarith

/-- **★★★ `herrHmin_gate_general_q0_generalK`.**  THE PACKAGE: a single `r > 0` and `L' ≥ 0` carrying
    BOTH gate-restricted general-`q₀`, general-`K` inputs, `p` near `q₀`:
      (I1) `|rncRadialSq(W p) − rncRadialSq(p − q₀)| ≤ L'·‖p − q₀‖³`,   and
      (I2) `½·rncRadialSq(p − q₀) ≤ rncRadialSq(W p)`,
    `W p := uniformInverseChart g gi hC hK p q₀`, POINTWISE in `q₀ ∈ interior K` (constants may depend on
    `q₀`; NO uniform-in-`q₀` claim — see file docstring).  The general-`q₀`, general-`K` analogue of
    `HerrHminCoercivity.herrHmin_gate`.  NOT `a₁ = R/6`. -/
theorem herrHmin_gate_general_q0_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ r > (0 : ℝ), ∃ L' : ℝ, 0 ≤ L' ∧ ∀ p : Point n, ‖p - q₀‖ < r →
      (|rncRadialSq (uniformInverseChart g gi hC hK p q₀) - rncRadialSq (p - q₀)| ≤ L' * ‖p - q₀‖ ^ 3)
      ∧ ((1 / 2 : ℝ) * rncRadialSq (p - q₀)
          ≤ rncRadialSq (uniformInverseChart g gi hC hK p q₀)) := by
  obtain ⟨r₀, hr₀, L, hL0, hbd⟩ := uniformInverseChart_rncRadialSq_error_generalK g gi hC hK hq₀
  refine ⟨min r₀ (1 / (2 * (L + 1))), lt_min hr₀ (by positivity), L * (n : ℝ), by positivity, ?_⟩
  intro p hpr
  set z : Point n := p - q₀ with hzdef
  set W : Point n := uniformInverseChart g gi hC hK p q₀ with hWdef
  have hpr₀ : ‖z‖ < r₀ := lt_of_lt_of_le hpr (min_le_left _ _)
  have hprL : ‖z‖ < 1 / (2 * (L + 1)) := lt_of_lt_of_le hpr (min_le_right _ _)
  obtain ⟨hlow, hup⟩ := hbd p hpr₀
  have hb0 : (0 : ℝ) ≤ rncRadialSq z := rncRadialSq_nonneg z
  have hle : rncRadialSq z ≤ (n : ℝ) * ‖z‖ ^ 2 := rncRadialSq_le_nsq z
  have hcoef : (0 : ℝ) ≤ L * ‖z‖ := mul_nonneg hL0 (norm_nonneg z)
  have herrbd : L * ‖z‖ * rncRadialSq z ≤ L * (n : ℝ) * ‖z‖ ^ 3 := by
    have := mul_le_mul_of_nonneg_left hle hcoef
    nlinarith [this]
  have hLz : L * ‖z‖ ≤ 1 / 2 := by
    have hstep : L * ‖z‖ ≤ L * (1 / (2 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hprL.le hL0
    have hbound : L * (1 / (2 * (L + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by linarith [hL0] : (0 : ℝ) < 2 * (L + 1))]; nlinarith [hL0]
    linarith
  have hprod : L * ‖z‖ * rncRadialSq z ≤ (1 / 2 : ℝ) * rncRadialSq z :=
    mul_le_mul_of_nonneg_right hLz hb0
  refine ⟨?_, by linarith⟩
  have habs : |rncRadialSq W - rncRadialSq z| ≤ L * ‖z‖ * rncRadialSq z :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  exact le_trans habs herrbd

end QIQTH.HerrHminGeneralQ0GeneralK

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HerrHminGeneralQ0GeneralK
#print axioms uniformInverseChart_diag_eventually_generalK
#print axioms uniformInverseChart_evalSlot_hasFDerivAt_id_diag_generalK
#print axioms uniformInverseChart_baseSlot_fderiv_neg_id_generalK
#print axioms uniformInverseChart_baseSlot_quadratic_displacement_generalK
#print axioms uniformInverseChart_rncRadialSq_error_generalK
#print axioms herr_gate_general_q0_generalK
#print axioms hmin_gate_general_q0_generalK
#print axioms herrHmin_gate_general_q0_generalK
end AxiomChecks

/-! ###############################################################################
    ## J4-1006 LEDGER — the compact-set-`K` GATE re-threading: `herr_gate`/`hmin_gate` at general `q₀`,
    ## SINGLE fixed arbitrary `K`, resolving J4-1004/1005's own named honest-distance item (i).
    ###############################################################################

  DON'T-UNDERCREDIT FINDING.  Two of the three ingredients (F3, F4) J4-1004's `K := closedBall q₀ 1`-tied
  construction needed ALREADY HAD general-`K` versions banked (`UniformFlowCoherentChartReconciliation
  GeneralK.uniformInverseChart_jointContDiffAt_diag_generalK`, `JointRNCRegularityInterfaceLocalGeneralK.
  uniformInverseChart_slice_fderiv_id_diag_generalK` / `..._slice_contDiffAt_diag_generalK`) from the
  earlier J4-884 generalization campaign — a fact NOT flagged in J4-1004/1005's own honest-distance notes.
  Only F1 (diagonal-vanishing) lacked a general-`K` version, and its transplant was routine (uses only the
  already-general `uniformInverseChart_huniformChart` plus `interior K ∈ 𝓝 q₀`).

  WHAT LANDS.  For a SINGLE arbitrary fixed `hK : IsCompact K`:
    • F1/F4-upgrade general-`K` (`uniformInverseChart_diag_eventually_generalK`,
      `..._evalSlot_hasFDerivAt_id_diag_generalK`).
    • Base-slot derivative `-Id` / quadratic displacement at general `q₀ ∈ interior K`
      (`..._baseSlot_fderiv_neg_id_generalK`, `..._baseSlot_quadratic_displacement_generalK`) — general-`K`
      analogue of J4-1004.
    • Two-sided `rncRadialSq` comparison error at general `q₀ ∈ interior K`
      (`uniformInverseChart_rncRadialSq_error_generalK`) — general-`K` analogue of J4-1005.
    • THE PAYOFF: `herr_gate_general_q0_generalK` / `hmin_gate_general_q0_generalK` /
      `herrHmin_gate_general_q0_generalK` — `HerrHminCoercivity`-style gate-restricted cubic error +
      coercivity, general `q₀ ∈ interior K`, SINGLE fixed `K`, POINTWISE in `q₀`.

  THE UNIFORMITY VERDICT (Sol `gpt-5.6-sol`, high, 2026-08-22, consulted BEFORE Lean).  The payoff is
  POINTWISE in `q₀`: constants `r, L'` may depend on `q₀`.  Sol confirmed this is the RIGHT target now —
  sufficient whenever `q₀` is fixed before dominating/integrating over the displacement variable (the
  per-base-point-cell architecture the gate-vs-far-field re-engineering plan needs) — and that compactness
  of `K` does NOT by itself uniformize a pointwise `∀ q₀, ∃ r, L` statement into a common-radius/constant
  claim over `q₀` ranging in a compact set (that would need a jointly-continuous-in-`q₀` bound, NOT
  extracted here). A uniform corollary over a compact `G ⊆ interior K` is flagged as a SEPARATE, explicitly
  NOT-attempted next step, not claimed.

  RELATION TO `herr_gate`/`hmin_gate` (Sol-confirmed, DO NOT over-claim).  This file does NOT supersede or
  literally generalize `HerrHminCoercivity.herr_gate`/`hmin_gate` — those hold for `z` ranging over ALL of
  `K` (boundary included, no `interior` hypothesis), eval point fixed at exactly `0`. This file's result
  specializes to that shape only at `q₀ = 0` AND only under the extra hypothesis `0 ∈ interior K`. This is
  a DIFFERENT, complementary general-interior-`q₀` brick for the near-carry `nb`'s per-base-point cells —
  it does NOT discharge `herr_gate`/`hmin_gate`'s own consumers (`SlotInstantiationVIII`, already WALLED
  per J4-455's own ledger, unrelated to this reconciliation).

  REMAINING (unchanged from J4-1004/1005's own honest-distance notes, item (ii)): the actual base-slot
  CHANGE OF VARIABLES into `hcomp`'s literal `∫z`/`∫s` integral shape (the `nb`/near-carry obligation) is
  NOT attempted here — this file supplies the pointwise-in-`q₀`, gate-restricted comparison + coercivity
  input CoV would need, not the CoV itself. Also NOT attempted: the uniform-in-`q₀` compact-cover corollary
  (flagged above, not claimed to be needed).

  `hCConv` NOT closed.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
  NOT `a₁ = R/6`.
-/
