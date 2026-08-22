/-
  HCompBaseSlotAntisymmetryConcrete — J4-1003: the CONCRETE corollary of the J4-1002 abstract
  base-slot antisymmetry quadratic-defect brick, instantiated at `Φ := uniformInverseChart g gi hC
  (isCompact_closedBall q₀ 1)`, resolving the "`hK` fixed-vs-per-base mismatch" that J4-1002's own
  dispatch flagged as the immediate blocker to landing its promised concrete corollary.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It supplies
  the concrete geodesic-inverse-chart instance of a pure real-analysis Taylor-remainder brick.  It does
  NOT touch `kPrime`, `heatHessMult`, the Gaussian weight, the `∫z`/`∫s` integrals, the base-slot change
  of variables, or `VanVleckGatedSpatialSymmetry.hcomp` itself.  No `sorry`, no new axioms, no
  `:= True`, no vacuous hypothesis, none equal to the conclusion, no existing file edited.  `hCConv`/
  `hcomp` NOT closed.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE `hK` MISMATCH (precise, resolved).  The abstract brick
  `HCompBaseSlotAntisymmetry.antisymmetryDefect_quadratic_bound Φ q₀ hdiag hjointC2` needs, with
  `Φ := uniformInverseChart g gi hC (isCompact_closedBall q₀ 1)`:
    • (F3) `ContDiffAt ℝ 2 (fun ξ => uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) ξ.1 ξ.2)
      (q₀,q₀)` — EXACTLY `uniformInverseChart_jointContDiffAt_diag g gi hC q₀`.  No mismatch.
    • (F1) `∀ᶠ q in 𝓝 q₀, uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q q = 0` — the
      diagonal-vanishing for the SAME FIXED compact set `K = closedBall q₀ 1`, with base point `q`
      RANGING near `q₀`.
  The banked diagonal-vanishing fact `JointRNCRegularityLocal.uniformInverseChart_slice_value_diag
  g gi hC q'` proves only `uniformInverseChart g gi hC (isCompact_closedBall q' 1) q' q' = 0` — the
  compact set `closedBall q' 1` is CENTERED on the same `q'` being evaluated.  It cannot supply (F1),
  which pins the center at `q₀` while the base point moves: that is the "`hK` fixed-vs-per-base
  mismatch".

  ## THE RESOLUTION (Sol gpt-5.6-sol high, GO 2026-08-22): NO globalization needed.  The mismatch is
  resolved DIRECTLY — NOT via the J4-1000 radial-truncation globalization — because the UNDERLYING germ
  fact `uniformInverseChart_huniformChart g gi hC hK` is already `∃ δ₀ > 0, ∀ q ∈ K, …` for a FIXED
  `K`.  The diagonal value `uniformInverseChart g gi hC hK q q = 0` holds for EVERY base point `q ∈ K`,
  not merely `K`'s center; `uniformInverseChart_slice_value_diag`'s specialization to `q' = center` is
  gratuitous.  `uniformInverseChart_diag_eventually` below re-runs that proof with `K = closedBall q₀ 1`
  FIXED and base point `q ∈ ball q₀ 1 ⊆ K` varying (`filter_upwards` on `ball q₀ 1 ∈ 𝓝 q₀`), yielding
  (F1) verbatim.  This shows the "mismatch" is an artefact of over-specialization, not a genuine
  local-to-global gap.

  ## WHAT LANDS (ns `QIQTH.HCompBaseSlotAntisymmetryConcrete`).
    • `uniformInverseChart_diag_eventually` — ★ (F1) discharged: `∀ᶠ q in 𝓝 q₀, uniformInverseChart
      g gi hC (isCompact_closedBall q₀ 1) q q = 0` (fixed-`K`, general-base diagonal vanishing).
    • `uniformInverseChart_antisymmetryDefect_quadratic` — ★★★ THE CONCRETE PAYOFF that J4-1002's
      docstring PROMISED but left blocked: `∃ r > 0, C ≥ 0, ∀ p, ‖p − q₀‖ < r → ‖uniformInverseChart …
      q₀ 1 p q₀ + uniformInverseChart … q₀ 1 q₀ p‖ ≤ C ‖p − q₀‖²`, feeding the abstract brick genuine
      hypotheses discharged from the coherent-chart machinery (F1 = `_diag_eventually`, F3 =
      `uniformInverseChart_jointContDiffAt_diag`).

  ## HONEST DISTANCE (what remains before this feeds `hcomp` literally).  This shrinks the near-carry
  `nb` obligation by supplying the CONCRETE base-slot antisymmetry quadratic bound for the actual
  geodesic inverse chart — the exact object `kPrime`/`gatedKernel` are built from.  It does NOT relate
  the chart's FIELD-slot JETS `P,Q` (what `heatHessMult`/`gaussComp_pd_pd_mixed` consume) to this
  defect bound, does NOT perform the base-slot change of variables (`∫z → ∫v`), does NOT touch the
  `τ`-weighted Gaussian integral or the `ds`-integration, and does NOT bridge the pointwise-to-integral
  interface with `VanVleckGatedSpatialSymmetry.hcomp`'s literal integral shape.  `hCConv` NOT closed.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HCompBaseSlotAntisymmetryQuadratic

open Filter
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.HCompBaseSlotAntisymmetryConcrete

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### 1. (F1) — fixed-`K`, general-base diagonal vanishing, resolving the `hK` mismatch.
    ############################################################################### -/

/-- **★ `uniformInverseChart_diag_eventually` — the (F1) discharge.**  For the FIXED compact set
    `K = closedBall q₀ 1`, the concrete inverse chart vanishes on the diagonal for EVERY base point in a
    neighbourhood of `q₀`:
        `∀ᶠ q in 𝓝 q₀, uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q q = 0`.
    Proof: `ball q₀ 1 ∈ 𝓝 q₀`; each such `q` lies in `K = closedBall q₀ 1`; the uniform germ fact
    `uniformInverseChart_huniformChart` (one fixed `δ₀`, `∀ q ∈ K`) at `v = 0` gives
    `uniformInverseChart … q (uniformFlowExp … q 0) = 0`, and `uniformFlowExp_zero` rewrites
    `uniformFlowExp … q 0 = q`.  This is `uniformInverseChart_slice_value_diag`'s proof with the base
    point freed inside the fixed `K` — NO radial-truncation globalization needed.  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_diag_eventually (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    ∀ᶠ q in 𝓝 q₀,
      uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q q = 0 := by
  set hK := isCompact_closedBall q₀ 1 with hKdef
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  filter_upwards [Metric.ball_mem_nhds q₀ (by norm_num : (0 : ℝ) < 1)] with q hq
  have hqK : q ∈ Metric.closedBall q₀ 1 :=
    Metric.ball_subset_closedBall hq
  obtain ⟨hgermC2, _⟩ := hspec q hqK
  have hgerm := (hgermC2 0 (by rw [norm_zero]; exact hδ₀)).1
  have h := hgerm.eq_of_nhds
  rwa [uniformFlowExp_zero g gi hC hK q hqK] at h

/-! ###############################################################################
    ### 2. (F1)+(F3) → the concrete base-slot antisymmetry quadratic bound.
    ############################################################################### -/

/-- **★★★ `uniformInverseChart_antisymmetryDefect_quadratic` — THE CONCRETE PAYOFF.**  The base-slot
    antisymmetry defect of the concrete geodesic inverse chart is QUADRATIC in the recentering distance:
        `∃ r > 0, C ≥ 0, ∀ p, ‖p − q₀‖ < r →
          ‖uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀
            + uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀ p‖ ≤ C * ‖p − q₀‖ ^ 2`.
    This is exactly the corollary J4-1002's docstring promised but left blocked on the `hK` mismatch;
    it is obtained by feeding the abstract brick `HCompBaseSlotAntisymmetry.
    antisymmetryDefect_quadratic_bound` its two genuine hypotheses:
      (F1) `uniformInverseChart_diag_eventually` (fixed-`K` diagonal vanishing near `q₀`), and
      (F3) `uniformInverseChart_jointContDiffAt_diag` (joint `ContDiffAt ℝ 2` at the diagonal).
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart_antisymmetryDefect_quadratic (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : Point n, ‖p - q₀‖ < r →
        ‖uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) p q₀
          + uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀ p‖
          ≤ C * ‖p - q₀‖ ^ 2 := by
  exact HCompBaseSlotAntisymmetry.antisymmetryDefect_quadratic_bound
    (uniformInverseChart g gi hC (isCompact_closedBall q₀ 1)) q₀
    (uniformInverseChart_diag_eventually g gi hC q₀)
    (uniformInverseChart_jointContDiffAt_diag g gi hC q₀)

end QIQTH.HCompBaseSlotAntisymmetryConcrete

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HCompBaseSlotAntisymmetryConcrete
#print axioms uniformInverseChart_diag_eventually
#print axioms uniformInverseChart_antisymmetryDefect_quadratic
end AxiomChecks
