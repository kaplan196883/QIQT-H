/-
# RECENTER brick J4-9 — `g̃`-NONDEGENERACY ON A DEFINITE BALL AROUND `0` (openness of units).

J4-8 (`RecenterAnnulusUncond.lean`) reduced the cutoff-residual annulus bounds to the CONTINUITY residue
`hgi_cont`/`hchris_cont` and supplied the bridge `expPullbackMetricInv_continuousOn_of_isUnit`: on any set
`S` where every entry `w ↦ g̃(w)_{ab}` is `ContinuousOn S` AND the assembled operator `matToCLM (g̃ w)` is
a UNIT for each `w ∈ S`, the inverse-metric entries `g̃⁻¹ w μ α` are `ContinuousOn S`.  The one missing
ingredient was the `IsUnit` (nondegeneracy) hypothesis for `w ≠ 0`.

This file discharges that ingredient on a DEFINITE ball around `0`, via OPENNESS OF UNITS — no Fréchet
derivative / inverse-function-theorem input needed:

  • the operator field `x ↦ matToCLM (g̃ x)` is `ContinuousAt 0` (its entries `x ↦ g̃(x)_{ab}` are
    `ContDiffAt ℝ 2` at `0` — `contDiffAt2_expPullbackMetric_zero` — and `matToCLM = ∑ a b · • e_{ab}`
    is a finite scalar-linear function of the entries);
  • at `0`, `matToCLM (g̃ 0) = matToCLM (g p)` is a UNIT (`metricCLMUnit0`, since `g̃(0) = g(p)`);
  • the set of units `{x | IsUnit x}` in the complete normed ring `Point n →L[ℝ] Point n` is OPEN
    (`Units.isOpen`, Mathlib `Mathlib/Analysis/Normed/Ring/Units.lean`).

Composing continuity-at-`0` with the open unit-set through `ContinuousAt.preimage_mem_nhds` gives a ball
`B(0,ρ₀)` on which `matToCLM (g̃ ·)` is a unit — i.e. `g̃` is nondegenerate near `0`.

`Target 1` (`expPullbackMetric_isUnit_near_zero`) is DERIVED (openness of units + continuity + the `0`-jet
unit).  `Target 2` (`expPullbackMetricInv_continuousOn_ball`) feeds Target 1 and
`expPullbackMetricInv_continuousOn_of_isUnit` to produce a genuine `ContinuousOn g̃⁻¹` on a ball.

══════════════════════════════════════════════════════════════════════════════════════════════════════
⚠ HONEST SCOPE (binding).  The `ρ₀` produced by openness-of-units is NON-EXPLICIT and generally SMALLER
than `expRho` (the confinement radius).  It does NOT cover the recenter chain's `∀ a b` annulus range:
annuli with outer radius `b > ρ₀` may reach conjugate points where `g̃` degenerates.  So Targets 1/2
discharge `hgi_cont`/`hchris_cont` ONLY for annuli within `ρ₀` (equivalently within `min ρ₀ expRho`), NOT
the full `∀ a b` hypothesis of `cutoffResidual_expPullback_hEboundW_uncond2`.  The full-ball nondegeneracy
(all annuli up to `expRho`) is the genuine no-conjugate-points wall — it needs `D exp_p` invertible up to
`expRho`, which the confinement radius does NOT guarantee.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no
vacuous hypotheses.
-/
import Mathlib
import QIQTH.PullbackMetricC3Uncond
import QIQTH.RecenterAnnulusUncond
import QIQTH.PullbackMetric

open Finset
open QIQTH.Curvature QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 4

/-! ### 1. ★ Target 1 — `g̃` nondegenerate on a definite ball around `0` (openness of units). -/

/-- **★ J4-9 — the pullback metric `g̃` is NONDEGENERATE on a definite ball around `0`.**
    There is `ρ₀ > 0` such that for every `x` with `‖x‖ < ρ₀`, the assembled operator
    `matToCLM (g̃ x)` is a UNIT in the operator ring `Point n →L[ℝ] Point n` (equivalently
    `det g̃(x) ≠ 0` / `g̃(x)` is invertible).

    Route (openness of units — no `fderiv`/IFT):
      • `x ↦ matToCLM (g̃ x)` is `ContinuousAt 0` (its entries `x ↦ g̃(x)_{ab}` are `ContDiffAt ℝ 2` at
        `0`, `contDiffAt2_expPullbackMetric_zero`, and `matToCLM = ∑ a b · • e_{ab}` is finite scalar-linear
        in the entries);
      • `matToCLM (g̃ 0) = matToCLM (g p)` is a unit (`metricCLMUnit0`, using `g̃(0) = g(p)` invertible);
      • the unit set `{y | IsUnit y}` is OPEN (`Units.isOpen`), so its `ContinuousAt`-preimage is a
        neighborhood of `0`, whence a ball `B(0,ρ₀)`.

    HONEST: `ρ₀` is non-explicit and generally smaller than `expRho`; this is the near-`0` nondegeneracy
    fact, NOT full-ball no-conjugate-points. -/
theorem expPullbackMetric_isUnit_near_zero (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hinv : ∀ a b, (∑ σ, g₀ p a σ * gi₀ p σ b) = if a = b then 1 else 0) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ x : Point n, ‖x‖ < ρ₀ →
      IsUnit (matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p x a b)) := by
  classical
  -- (1) the operator field `x ↦ matToCLM (g̃ x)` is `ContDiffAt ℝ 2` at `0`, hence `ContinuousAt 0`.
  have hmet_cd : ContDiffAt ℝ 2
      (fun x => matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p x a b)) 0 := by
    show ContDiffAt ℝ 2
      (fun x => ∑ a, ∑ b, expPullbackMetric g₀ gi₀ hC p x a b • elemCLM a b) 0
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro b _
    exact (contDiffAt2_expPullbackMetric_zero g₀ gi₀ hC p hg a b).smul contDiffAt_const
  have hmatCA : ContinuousAt
      (fun x => matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p x a b)) 0 :=
    hmet_cd.continuousAt
  -- (2) at `0` the assembled operator is a unit (`g̃(0) = g(p)` invertible).
  have h0unit : IsUnit (matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p 0 a b)) :=
    ⟨metricCLMUnit0 g₀ gi₀ hC p hinv, rfl⟩
  -- (3) the unit set is OPEN, so its preimage under the continuous field is a nbhd of `0`.
  have hopen : {y : Point n →L[ℝ] Point n | IsUnit y}
      ∈ nhds (matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p 0 a b)) :=
    IsOpen.mem_nhds Units.isOpen h0unit
  have hpre : (fun x => matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p x a b)) ⁻¹'
      {y : Point n →L[ℝ] Point n | IsUnit y} ∈ nhds (0 : Point n) :=
    hmatCA.preimage_mem_nhds hopen
  -- (4) extract a ball from the neighborhood.
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨ρ₀, hρ₀pos, hball⟩ := hpre
  refine ⟨ρ₀, hρ₀pos, fun x hx => ?_⟩
  have hxball : x ∈ Metric.ball (0 : Point n) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hx
  exact hball hxball

/-! ### 2. ★ Target 2 — `g̃⁻¹` `ContinuousOn` a definite ball around `0`. -/

/-- **★ J4-9 — `g̃⁻¹` is `ContinuousOn` a definite ball around `0`.**
    Feeding Target 1 (`expPullbackMetric_isUnit_near_zero`, the `IsUnit`/nondegeneracy input) and the
    bridge `expPullbackMetricInv_continuousOn_of_isUnit` (`RecenterAnnulusUncond.lean`), each entry
    `w ↦ g̃⁻¹(w)_{μα}` is `ContinuousOn (Metric.ball 0 ρ₀)` for a definite `ρ₀ > 0`.  The radius is taken
    `ρ₀ = min (openness-of-units radius) expRho`, so that BOTH the `g̃`-continuity input
    (`contDiffOn_expPullbackMetric_three_uncond`, valid on `ball expRho`) AND the nondegeneracy input hold.

    This is the `hgi_cont`-on-small-annuli producer: for annuli contained in `ball ρ₀` it discharges the
    continuity residue of `cutoffResidual_expPullback_hEboundW_uncond2`.

    HONEST: `ρ₀` is non-explicit and generally strictly less than `expRho`; this does NOT cover the recenter
    chain's `∀ a b` annulus range (annuli reaching `b > ρ₀` may hit conjugate points).  NOT `a₁ = R/6`. -/
theorem expPullbackMetricInv_continuousOn_ball (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hinv : ∀ a b, (∑ σ, g₀ p a σ * gi₀ p σ b) = if a = b then 1 else 0) (μ α : Fin n) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ContinuousOn (fun w => expPullbackMetricInv g₀ gi₀ hC p w μ α) (Metric.ball (0 : Point n) ρ₀) := by
  classical
  obtain ⟨ρU, hρUpos, hunit0⟩ := expPullbackMetric_isUnit_near_zero g₀ gi₀ hC p hg hinv
  -- take `ρ₀ = min ρU expRho` so both continuity (on `ball expRho`) and nondegeneracy (on `ball ρU`) hold.
  set ρ₀ : ℝ := min ρU (expRho g₀ gi₀ hC p) with hρ₀def
  have hρ₀pos : 0 < ρ₀ := lt_min hρUpos (expRho_pos g₀ gi₀ hC p)
  refine ⟨ρ₀, hρ₀pos, ?_⟩
  -- `g̃` entries are `ContinuousOn (ball ρ₀)` (from `ContDiffOn ℝ 3` on `ball expRho`, restricted).
  have hScont : ∀ a b, ContinuousOn
      (fun w => expPullbackMetric g₀ gi₀ hC p w a b) (Metric.ball (0 : Point n) ρ₀) := by
    intro a b
    exact ((contDiffOn_expPullbackMetric_three_uncond g₀ gi₀ hC p hg a b).continuousOn).mono
      (Metric.ball_subset_ball (min_le_right _ _))
  -- `g̃` is nondegenerate on `ball ρ₀` (contained in `ball ρU`).
  have hunit : ∀ w ∈ Metric.ball (0 : Point n) ρ₀,
      IsUnit (matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p w a b)) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hunit0 w (lt_of_lt_of_le hw (min_le_left _ _))
  exact expPullbackMetricInv_continuousOn_of_isUnit g₀ gi₀ hC p
    (Metric.ball (0 : Point n) ρ₀) hScont hunit μ α

end QIQTH.HeatResidualBound
