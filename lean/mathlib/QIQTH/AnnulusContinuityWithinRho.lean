/-
# RECENTER brick J4-11 — the "within-`ρ₀`" CONTINUITY producers for the cutoff residue.

`cutoffResidual_expPullback_hEboundW_uncond2` (`RecenterAnnulusUncond.lean`) carries the genuinely-local
continuity residue

  • `hgi_cont`    : `∀ a b i j, ContinuousOn (g̃⁻¹ · i j) {w | a²≤rncRadialSq w ∧ rncRadialSq w≤b²}`,
  • `hchris_cont` : `∀ a b k i j, ContinuousOn (Γ̃ k i j ·) {w | a²≤rncRadialSq w ∧ rncRadialSq w≤b²}`,

where `Γ̃ = christoffel (expPullbackMetric …) (expPullbackMetricInv …)`.  J4-9
(`PullbackMetricNondegNearZero.lean`) proved `g̃` NONDEGENERATE on a definite ball `B(0,ρ₀)` around `0`
(`expPullbackMetric_isUnit_near_zero`), whence `g̃⁻¹` is `ContinuousOn` that ball
(`expPullbackMetricInv_continuousOn_ball`).  Because `a₁ = R/6` is a LOCAL DIAGONAL invariant, the
parametrix cutoff may be supported in a small ball `‖v‖ < r` with `r < ρ₀`, so the continuity residue only
has to hold on annuli CONTAINED IN `B(0,ρ₀)`.

This file lands the two genuinely-reachable "within-`ρ₀`" continuity producers:

  1. `expPullbackMetricInv_continuousOn_annulus_within` — for annuli with outer radius `b < ρ₀` (and
     `0 ≤ b`), each entry `g̃⁻¹ · i j` is `ContinuousOn` the annulus.  Route: the annulus is `⊆ B(0,ρ₀)`
     (`rncRadialSq w ≤ b²` ⟹ `‖w‖ ≤ rncRadial w ≤ b < ρ₀`, via `norm_le_rncRadial`), then J4-9's
     ball-continuity restricted by `ContinuousOn.mono`.

  2. `christoffel_expPullback_continuousOn_annulus_within` — likewise `Γ̃ k i j ·` is `ContinuousOn` the
     annulus.  `Γ̃ = ½ g̃⁻¹(∂g̃+∂g̃−∂g̃)`: on `B(0,ρ₀)` the inverse metric `g̃⁻¹` is continuous (J4-9) and
     each first partial `∂g̃ = pd (g̃ ·) ·` is continuous (from the UNCONDITIONAL `ContDiffOn ℝ 3` of `g̃`
     on `ball expRho`, `contDiffOn_expPullbackMetric_three_uncond`: `pd = fderiv(·)(eₖ)` via `pd_eq_fderiv`
     and `fderiv` of a `C³` field is `C²`, hence continuous).  A finite product/sum of continuous fields is
     continuous.

Both producers are DERIVED from J4-9 (`expPullbackMetric_isUnit_near_zero`) + the `g̃`-`C³` regularity; no
new wall, no carried conclusion.

══════════════════════════════════════════════════════════════════════════════════════════════════════
⚠ HONEST SCOPE (binding).  These discharge `hgi_cont`/`hchris_cont` ONLY for annuli with `b < ρ₀`
(`ρ₀ = min (openness-of-units radius) expRho`, NON-EXPLICIT, generally `< expRho`).  They do NOT cover the
`∀ a b` annulus range of `cutoffResidual_expPullback_hEboundW_uncond2` (annuli reaching `b ≥ ρ₀` may hit
conjugate points where `g̃` degenerates — the genuine no-conjugate-points wall).  Wiring them into the core
cutoff theorem needs the J4-12 radius-constraint refactor (parameterize / shrink the cutoff radii `a b`
to `< ρ₀`).  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.RecenterAnnulusUncond
import QIQTH.PullbackMetricNondegNearZero
import QIQTH.PullbackMetricC3Uncond
import QIQTH.RadialDistance
import QIQTH.RNCDecay
import QIQTH.FlatTail

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 4

/-! ### 1. ★ `g̃⁻¹` `ContinuousOn` annuli within `ρ₀`. -/

/-- **★ J4-11 — the pullback inverse metric `g̃⁻¹` is `ContinuousOn` any annulus contained in the
    nondegeneracy ball `B(0,ρ₀)`.**  There is `ρ₀ > 0` (the J4-9 openness-of-units radius, capped at
    `expRho`) such that for every `a b` with `0 ≤ b` and `b < ρ₀`, and every `i j`, the entry
    `w ↦ g̃⁻¹(w)_{ij}` is `ContinuousOn {w | a² ≤ rncRadialSq w ∧ rncRadialSq w ≤ b²}`.

    This is exactly the `hgi_cont` hypothesis of `cutoffResidual_expPullback_hEboundW_uncond2` RESTRICTED
    to annuli with `b < ρ₀`.  Route: `rncRadialSq w ≤ b²` ⟹ `‖w‖ ≤ rncRadial w ≤ b < ρ₀`
    (`norm_le_rncRadial`), so the annulus is `⊆ Metric.ball 0 ρ₀`, on which `g̃⁻¹` is continuous by J4-9
    (`expPullbackMetric_isUnit_near_zero` + `expPullbackMetricInv_continuousOn_of_isUnit`); restrict with
    `ContinuousOn.mono`.

    HONEST: `ρ₀` non-explicit, generally `< expRho`; only annuli within `ρ₀`, NOT the full `∀ a b`
    range. NOT `a₁ = R/6`. -/
theorem expPullbackMetricInv_continuousOn_annulus_within
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hinv : ∀ a b, (∑ σ, g₀ p a σ * gi₀ p σ b) = if a = b then 1 else 0) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (a b : ℝ) (i j : Fin n), 0 ≤ b → b < ρ₀ →
      ContinuousOn (fun w => expPullbackMetricInv g₀ gi₀ hC p w i j)
        {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2} := by
  classical
  obtain ⟨ρU, hρUpos, hunit0⟩ := expPullbackMetric_isUnit_near_zero g₀ gi₀ hC p hg hinv
  set ρ₀ : ℝ := min ρU (expRho g₀ gi₀ hC p) with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; exact lt_min hρUpos (expRho_pos g₀ gi₀ hC p)
  have hleU : ρ₀ ≤ ρU := by rw [hρ₀def]; exact min_le_left _ _
  have hleE : ρ₀ ≤ expRho g₀ gi₀ hC p := by rw [hρ₀def]; exact min_le_right _ _
  -- `g̃⁻¹` continuous on `ball ρ₀` (J4-9 machinery, uniform in `i j`).
  have hScont : ∀ a b, ContinuousOn
      (fun w => expPullbackMetric g₀ gi₀ hC p w a b) (Metric.ball (0 : Point n) ρ₀) := fun a b =>
    ((contDiffOn_expPullbackMetric_three_uncond g₀ gi₀ hC p hg a b).continuousOn).mono
      (Metric.ball_subset_ball hleE)
  have hunit : ∀ w ∈ Metric.ball (0 : Point n) ρ₀,
      IsUnit (matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p w a b)) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hunit0 w (lt_of_lt_of_le hw hleU)
  have hballcont : ∀ (i j : Fin n),
      ContinuousOn (fun w => expPullbackMetricInv g₀ gi₀ hC p w i j) (Metric.ball (0 : Point n) ρ₀) :=
    fun i j => expPullbackMetricInv_continuousOn_of_isUnit g₀ gi₀ hC p
      (Metric.ball (0 : Point n) ρ₀) hScont hunit i j
  refine ⟨ρ₀, hρ₀pos, fun a b i j hb0 hb => (hballcont i j).mono ?_⟩
  -- the annulus with `b < ρ₀` is `⊆ ball ρ₀`.
  intro w hw
  rw [Metric.mem_ball, dist_zero_right]
  have h2 : rncRadial w ≤ b := by
    rw [rncRadial]
    calc Real.sqrt (rncRadialSq w) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hw.2
      _ = b := Real.sqrt_sq hb0
  calc ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
    _ ≤ b := h2
    _ < ρ₀ := hb

/-! ### 2. ★ `Γ̃` (pullback Christoffel) `ContinuousOn` annuli within `ρ₀`. -/

/-- **★ J4-11 — the pullback Christoffel `Γ̃ = christoffel g̃ g̃⁻¹` is `ContinuousOn` any annulus contained
    in the nondegeneracy ball `B(0,ρ₀)`.**  There is `ρ₀ > 0` such that for every `a b` with `0 ≤ b` and
    `b < ρ₀`, and every `k i j`, the field `w ↦ Γ̃(k i j)(w)` is
    `ContinuousOn {w | a² ≤ rncRadialSq w ∧ rncRadialSq w ≤ b²}`.

    This is exactly the `hchris_cont` hypothesis of `cutoffResidual_expPullback_hEboundW_uncond2`
    RESTRICTED to annuli with `b < ρ₀`.  Route: `Γ̃ = ½ g̃⁻¹(∂g̃+∂g̃−∂g̃)`; on `ball ρ₀` the entries `g̃⁻¹`
    are continuous (J4-9) and each partial `pd (g̃ ·) ·` is continuous — `pd f = fderiv f (eₖ)`
    (`pd_eq_fderiv`, `g̃` differentiable on the open ball) and `fderiv` of the `ContDiffOn ℝ 3` field `g̃`
    (`contDiffOn_expPullbackMetric_three_uncond`) is `ContDiffOn ℝ 2`, hence continuous.  A finite
    sum/product of continuous fields is continuous; restrict to the annulus by `ContinuousOn.mono`.

    HONEST: `ρ₀` non-explicit, generally `< expRho`; only annuli within `ρ₀`. NOT `a₁ = R/6`. -/
theorem christoffel_expPullback_continuousOn_annulus_within
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hinv : ∀ a b, (∑ σ, g₀ p a σ * gi₀ p σ b) = if a = b then 1 else 0) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (a b : ℝ) (k i j : Fin n), 0 ≤ b → b < ρ₀ →
      ContinuousOn (fun w => christoffel (expPullbackMetric g₀ gi₀ hC p)
          (expPullbackMetricInv g₀ gi₀ hC p) k i j w)
        {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2} := by
  classical
  obtain ⟨ρU, hρUpos, hunit0⟩ := expPullbackMetric_isUnit_near_zero g₀ gi₀ hC p hg hinv
  set ρ₀ : ℝ := min ρU (expRho g₀ gi₀ hC p) with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; exact lt_min hρUpos (expRho_pos g₀ gi₀ hC p)
  have hleU : ρ₀ ≤ ρU := by rw [hρ₀def]; exact min_le_left _ _
  have hleE : ρ₀ ≤ expRho g₀ gi₀ hC p := by rw [hρ₀def]; exact min_le_right _ _
  -- (a) `g̃⁻¹` entries continuous on `ball ρ₀` (J4-9 machinery).
  have hScont : ∀ a b, ContinuousOn
      (fun w => expPullbackMetric g₀ gi₀ hC p w a b) (Metric.ball (0 : Point n) ρ₀) := fun a b =>
    ((contDiffOn_expPullbackMetric_three_uncond g₀ gi₀ hC p hg a b).continuousOn).mono
      (Metric.ball_subset_ball hleE)
  have hunit : ∀ w ∈ Metric.ball (0 : Point n) ρ₀,
      IsUnit (matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p w a b)) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hunit0 w (lt_of_lt_of_le hw hleU)
  have hginv : ∀ (i j : Fin n),
      ContinuousOn (fun w => expPullbackMetricInv g₀ gi₀ hC p w i j) (Metric.ball (0 : Point n) ρ₀) :=
    fun i j => expPullbackMetricInv_continuousOn_of_isUnit g₀ gi₀ hC p
      (Metric.ball (0 : Point n) ρ₀) hScont hunit i j
  -- (b) each partial `pd (g̃ · a b) c` continuous on `ball ρ₀` (from `C³` of `g̃`).
  have hpd : ∀ (a b c : Fin n), ContinuousOn
      (fun w => pd (fun y => expPullbackMetric g₀ gi₀ hC p y a b) c w)
        (Metric.ball (0 : Point n) ρ₀) := by
    intro a b c
    have hcd3 : ContDiffOn ℝ 3 (fun x => expPullbackMetric g₀ gi₀ hC p x a b)
        (Metric.ball (0 : Point n) (expRho g₀ gi₀ hC p)) :=
      contDiffOn_expPullbackMetric_three_uncond g₀ gi₀ hC p hg a b
    -- `fderiv g̃` is `ContDiffOn ℝ 2` on the open ball, hence continuous.
    have hfd_cd : ContDiffOn ℝ 2
        (fun w => fderiv ℝ (fun x => expPullbackMetric g₀ gi₀ hC p x a b) w)
        (Metric.ball (0 : Point n) (expRho g₀ gi₀ hC p)) :=
      hcd3.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
    have hfd_cont : ContinuousOn
        (fun w => fderiv ℝ (fun x => expPullbackMetric g₀ gi₀ hC p x a b) w (Pi.single c (1 : ℝ)))
        (Metric.ball (0 : Point n) (expRho g₀ gi₀ hC p)) :=
      hfd_cd.continuousOn.clm_apply continuousOn_const
    have hdiffOn : DifferentiableOn ℝ (fun x => expPullbackMetric g₀ gi₀ hC p x a b)
        (Metric.ball (0 : Point n) (expRho g₀ gi₀ hC p)) := hcd3.differentiableOn (by norm_num)
    -- `pd = fderiv(·)(e_c)` on the open ball (`g̃` differentiable there).
    have hpd_eqOn : Set.EqOn
        (fun w => pd (fun y => expPullbackMetric g₀ gi₀ hC p y a b) c w)
        (fun w => fderiv ℝ (fun x => expPullbackMetric g₀ gi₀ hC p x a b) w (Pi.single c (1 : ℝ)))
        (Metric.ball (0 : Point n) (expRho g₀ gi₀ hC p)) := by
      intro w hw
      exact pd_eq_fderiv (fun y => expPullbackMetric g₀ gi₀ hC p y a b) c w
        (hdiffOn.differentiableAt (Metric.isOpen_ball.mem_nhds hw))
    have hpd_full : ContinuousOn
        (fun w => pd (fun y => expPullbackMetric g₀ gi₀ hC p y a b) c w)
        (Metric.ball (0 : Point n) (expRho g₀ gi₀ hC p)) := hfd_cont.congr hpd_eqOn
    exact hpd_full.mono (Metric.ball_subset_ball hleE)
  -- (c) assemble `Γ̃` on `ball ρ₀`: finite sum/product of continuous fields.
  have hchris_ball : ∀ (k i j : Fin n), ContinuousOn
      (fun w => christoffel (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p) k i j w)
        (Metric.ball (0 : Point n) ρ₀) := by
    intro k i j
    simp only [christoffel]
    refine continuousOn_const.mul ?_
    refine continuousOn_finsetSum _ (fun α _ => ?_)
    exact (hginv k α).mul (((hpd α j i).add (hpd α i j)).sub (hpd i j α))
  refine ⟨ρ₀, hρ₀pos, fun a b k i j hb0 hb => (hchris_ball k i j).mono ?_⟩
  -- annulus with `b < ρ₀` is `⊆ ball ρ₀`.
  intro w hw
  rw [Metric.mem_ball, dist_zero_right]
  have h2 : rncRadial w ≤ b := by
    rw [rncRadial]
    calc Real.sqrt (rncRadialSq w) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hw.2
      _ = b := Real.sqrt_sq hb0
  calc ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
    _ ≤ b := h2
    _ < ρ₀ := hb

end QIQTH.HeatResidualBound

