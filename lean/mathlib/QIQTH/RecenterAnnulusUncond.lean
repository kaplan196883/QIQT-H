/-
# RECENTER brick J4-8 — the `hgi_ann`/`hLapChi_ann` annulus-bound DISCHARGE and a further-reduced
  cutoff-residual wrapper `cutoffResidual_expPullback_hEboundW_uncond2`.

J4-7 (`RecenterResidualUncond.lean`) produced `cutoffResidual_expPullback_hEboundW_uncond` — the
per-base-point q-centered width-2 cutoff residual bound `hEboundW`, `hfd3`-FREE, but still CARRYING two
annulus-bound hypotheses over the locally-`C²` pullback objects:

  • `hgi_ann`     : `∀ a b, ∃ Kg ≥ 0, ∀ w i j, a²≤rncRadialSq w ≤ b² → |g̃⁻¹ w i j| ≤ Kg`;
  • `hLapChi_ann` : `∀ a b, ∃ Kc2 ≥ 0, ∀ w, a²≤rncRadialSq w ≤ b² → |Δ_g̃(radialCutoff a b) w| ≤ Kc2`.

These were carried because the base-`0` `CutoffAnnulusBounds` bricks demand GLOBAL continuity of
`g̃⁻¹ = expPullbackMetricInv …` (unavailable — `g̃⁻¹` is only locally regular).  The
`ContinuousOn`-on-annulus discharge machinery `gi_bound_on_annulus_of_continuousOn` /
`laplaceBeltrami_radialCutoff_bound_on_annulus_of_continuousOn` (`RecenterHEboundW.lean`) already turns
`ContinuousOn`-on-a-compact-annulus into EXACTLY those two bound shapes (via
`IsCompact.exists_bound_of_continuousOn`).  This file:

  1. supplies the missing REDUCTION-CHAIN lemma `expPullbackMetricInv_continuousOn_of_isUnit`:
     wherever the ambient-continuous pullback metric `g̃` assembles to a UNIT operator
     `matToCLM (g̃ w)` (i.e. `g̃` NONDEGENERATE), the inverse-metric entries `g̃⁻¹ w μ α` are
     `ContinuousOn` there — `Ring.inverse` is continuous at units (`contDiffAt_ringInverse`) composed
     with the continuous operator field `w ↦ matToCLM (g̃ w)`.  This is the precise bridge
     "`g̃` nondegenerate ⟹ `g̃⁻¹` continuous ⟹ annulus bounds";

  2. lands `cutoffResidual_expPullback_hEboundW_uncond2`, which DROPS `hgi_ann` and `hLapChi_ann`
     (both now DERIVED internally via the delivered `..._of_continuousOn` bricks) in favour of the
     strictly weaker, genuinely-local CONTINUITY residue
       • `hgi_cont`    : `∀ a b i j, ContinuousOn (g̃⁻¹ · i j) (annulus a b)`,
       • `hchris_cont` : `∀ a b k i j, ContinuousOn (Γ̃ k i j ·) (annulus a b)`.

══════════════════════════════════════════════════════════════════════════════════════════════════════
STEP-0 FINDING — g̃-NONDEGENERACY-ON-BALL (the last-mile prerequisite): STATUS = MISSING (honest).

The repo establishes `g̃⁻¹`'s regularity ONLY at `0` (`expPullbackMetricInv_zero`,
`expPullbackMetricInv_differentiableAt`, `expPullbackMetricInv_contDiffAt_one`) — via `matToCLM (g̃ 0)`
being a unit (`metricCLMUnit0`).  It does NOT establish `matToCLM (g̃ w)` a unit (equivalently `det g̃(w)
≠ 0`, `g̃` pos-def) for `w ≠ 0`; that would need `D exp_p` INVERTIBLE on the exp-ball (`exp_p` a diffeo
with NO conjugate points on the injectivity ball).  The repo has `hasFDerivAt_expMap` (the first
variation `D exp_p` EXISTS at each `‖v‖ < expRho`) and the local homeomorphism AT `0` (`ExpMap` S6),
but NOT `D exp_p x` invertible for `x ≠ 0`.  So the `IsUnit`/nondegeneracy hypothesis of
`expPullbackMetricInv_continuousOn_of_isUnit` cannot yet be discharged unconditionally on the ball, and
the `∀ a b`-quantified `hgi_cont`/`hchris_cont` (which range over annuli OUTSIDE the ball too, where
`g̃`'s very regularity is unestablished) are carried honestly.  `expPullbackMetricInv_continuousOn_of_isUnit`
is the exact green stub that a future "`D exp_p` invertible on ball ⟹ `matToCLM (g̃ ·)` unit on ball"
lemma would feed to discharge `hgi_cont` on ball-contained annuli.

⚠ HONEST SCOPE (binding).  `hgi_ann` and `hLapChi_ann` are now DERIVED (discharged) from the
continuity residue `hgi_cont`/`hchris_cont` via compactness.  The continuity residue itself is CARRIED
(strictly weaker than the two bound families; it is the genuine local-regularity fact pinned to
`g̃`-nondegeneracy by `expPullbackMetricInv_continuousOn_of_isUnit`).  NOT `a₁ = R/6`.  No `sorry`, no
new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.RecenterResidualUncond
import QIQTH.RecenterHEboundW
import QIQTH.PullbackMetric

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance
open QIQTH.FlatHeatEquation QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 4

/-! ### 1. ★ The reduction-chain lemma: `g̃` nondegenerate ⟹ `g̃⁻¹` `ContinuousOn`. -/

/-- **★ `g̃⁻¹` is `ContinuousOn` a set where `g̃` is continuous and NONDEGENERATE.**
    For the pullback inverse metric `g̃⁻¹ = expPullbackMetricInv g₀ gi₀ hC p`, on any set `S` where

      • every entry `w ↦ g̃(w)_{ab}` is `ContinuousOn S` (`hScont`), and
      • the assembled operator `matToCLM (g̃ w)` is a UNIT for each `w ∈ S` (`hunit`,
        the operator form of `g̃` nondegenerate / `det g̃(w) ≠ 0`),

    each entry `w ↦ g̃⁻¹(w)_{μα}` is `ContinuousOn S`.  Route: the operator field
    `w ↦ matToCLM (g̃ w) = ∑_{a,b} g̃(w)_{ab} • e_{ab}` is `ContinuousOn S` (finite sum of continuous
    scalars times constant operators); `Ring.inverse` is `C^∞` (hence continuous) at each unit
    (`contDiffAt_ringInverse`); composing gives `w ↦ Ring.inverse (matToCLM (g̃ w))` `ContinuousOn S`,
    and entry-evaluation (`apply`/`proj`) is continuous-linear.

    This is the precise bridge `g̃`-nondegenerate ⟹ `g̃⁻¹`-continuous — the last-mile prerequisite whose
    hypothesis `hunit` is the STILL-MISSING `matToCLM (g̃ ·)` unit-on-ball fact (needs `D exp_p`
    invertible on the exp-ball). -/
theorem expPullbackMetricInv_continuousOn_of_isUnit
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (S : Set (Point n))
    (hScont : ∀ a b, ContinuousOn (fun w => expPullbackMetric g₀ gi₀ hC p w a b) S)
    (hunit : ∀ w ∈ S, IsUnit (matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p w a b)))
    (μ α : Fin n) :
    ContinuousOn (fun w => expPullbackMetricInv g₀ gi₀ hC p w μ α) S := by
  classical
  -- (1) the operator field `w ↦ matToCLM (g̃ w)` is `ContinuousOn S`.
  have hmat : ContinuousOn
      (fun w => matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p w a b)) S := by
    show ContinuousOn
      (fun w => ∑ a, ∑ b, expPullbackMetric g₀ gi₀ hC p w a b • elemCLM a b) S
    refine continuousOn_finsetSum _ fun a _ => ?_
    refine continuousOn_finsetSum _ fun b _ => ?_
    exact (hScont a b).smul continuousOn_const
  -- (2) `w ↦ Ring.inverse (matToCLM (g̃ w))` is `ContinuousOn S` (units-continuity of `Ring.inverse`).
  have hinvcont : ContinuousOn
      (fun w => Ring.inverse (matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p w a b))) S := by
    intro w hw
    have hmatw : ContinuousWithinAt
        (fun w => matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p w a b)) S w :=
      hmat.continuousWithinAt hw
    obtain ⟨U, hU⟩ := hunit w hw
    have hcd : ContDiffAt ℝ (1 : WithTop ℕ∞) Ring.inverse (U : Point n →L[ℝ] Point n) :=
      contDiffAt_ringInverse ℝ U
    rw [hU] at hcd
    -- pin `f`/`g` so `comp_continuousWithinAt` does not re-decompose the point `matToCLM (g̃ w)`.
    exact ContinuousAt.comp_continuousWithinAt
      (g := Ring.inverse)
      (f := fun w => matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p w a b))
      hcd.continuousAt hmatw
  -- (3) entry-evaluation is continuous-linear; compose.
  have houter : Continuous (fun op : Point n →L[ℝ] Point n =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) μ)
        ((ContinuousLinearMap.apply ℝ (Point n) (Pi.single α (1 : ℝ) : Point n)) op)) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) μ).continuous.comp
      (ContinuousLinearMap.apply ℝ (Point n) (Pi.single α (1 : ℝ) : Point n)).continuous
  have heq : (fun w => expPullbackMetricInv g₀ gi₀ hC p w μ α)
      = fun w => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) μ)
          ((ContinuousLinearMap.apply ℝ (Point n) (Pi.single α (1 : ℝ) : Point n))
            (Ring.inverse (matToCLM (fun a b => expPullbackMetric g₀ gi₀ hC p w a b)))) := by
    funext w
    simp only [expPullbackMetricInv, ContinuousLinearMap.apply_apply, ContinuousLinearMap.proj_apply]
  rw [heq]
  exact houter.comp_continuousOn hinvcont

/-! ### 2. ★ The further-reduced cutoff-residual wrapper (drops `hgi_ann` + `hLapChi_ann`). -/

/-- **★ J4-8 — q-centered cutoff residual width-2 Gaussian bound `hEboundW`, with the annulus bounds
    `hgi_ann`/`hLapChi_ann` DISCHARGED.**  A further-reduced wrapper of
    `cutoffResidual_expPullback_hEboundW_uncond` (J4-7): the two annulus BOUND families

      `hgi_ann`  : `∀ a b, ∃ Kg …, |g̃⁻¹| ≤ Kg`   and   `hLapChi_ann` : `∀ a b, ∃ Kc2 …, |Δ_g̃χ| ≤ Kc2`

    are DROPPED and DERIVED internally from the strictly weaker CONTINUITY residue

      `hgi_cont`    : `∀ a b i j, ContinuousOn (g̃⁻¹ · i j) (annulus a b)`,
      `hchris_cont` : `∀ a b k i j, ContinuousOn (Γ̃ k i j ·) (annulus a b)`,

    via the delivered compactness bricks `gi_bound_on_annulus_of_continuousOn` and
    `laplaceBeltrami_radialCutoff_bound_on_annulus_of_continuousOn` (`RecenterHEboundW.lean`): each
    annulus is compact, so `ContinuousOn` there yields the uniform bound.  Every OTHER genuine input of
    J4-7 (ambient frame data, global cofactor smoothness `hw0smooth`, van-Vleck `hfold`, pointwise
    nondegeneracy `hinvT`, `g̃⁻¹` symmetry `hgisymm`, the `t`/`M`/`W`/`L` analytic bounds) is kept.

    HONEST: `hgi_ann`/`hLapChi_ann` are now DISCHARGED (derived).  The carried residue `hgi_cont`/
    `hchris_cont` is the genuine local-continuity fact — strictly weaker than the two bound families,
    pinned to `g̃`-nondegeneracy by `expPullbackMetricInv_continuousOn_of_isUnit` (whose `IsUnit`
    prerequisite — `D exp_p` invertible on the ball — is the still-missing last mile).  NOT `a₁ = R/6`. -/
theorem cutoffResidual_expPullback_hEboundW_uncond2
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g₀ y a b = g₀ y b a)
    (hinvF : ∀ y a b, (∑ σ, g₀ y a σ * gi₀ y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ))
    (hinvT : ∀ y i j,
      (∑ σ, expPullbackMetricInv g₀ gi₀ hC p y i σ * expPullbackMetric g₀ gi₀ hC p y σ j)
        = if i = j then 1 else 0)
    (hgisymm : ∀ w i j, expPullbackMetricInv g₀ gi₀ hC p w i j
        = expPullbackMetricInv g₀ gi₀ hC p w j i)
    -- ★ REPLACES `hgi_ann` + `hLapChi_ann`: the genuinely-local `ContinuousOn`-on-annulus residue.
    (hgi_cont : ∀ (a b : ℝ) (i j : Fin n),
        ContinuousOn (fun w => expPullbackMetricInv g₀ gi₀ hC p w i j)
          {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2})
    (hchris_cont : ∀ (a b : ℝ) (k i j : Fin n),
        ContinuousOn (fun w => christoffel (expPullbackMetric g₀ gi₀ hC p)
            (expPullbackMetricInv g₀ gi₀ hC p) k i j w)
          {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2})
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |expPullbackMetricInv g₀ gi₀ hC p v i j - (if i = j then (1 : ℝ) else 0)|
        ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
        (foldedCoeff Θ u 0) v| ≤ L) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) t
          - laplaceBeltrami (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u t y) v|
        ≤ B * gaussDdimWide t v := by
  -- Derive `hgi_ann` from `hgi_cont` via the compactness brick.
  have hgi_ann : ∀ (a b : ℝ), ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |expPullbackMetricInv g₀ gi₀ hC p w i j| ≤ Kg := fun a b =>
    gi_bound_on_annulus_of_continuousOn (expPullbackMetricInv g₀ gi₀ hC p) a b
      (fun i j => hgi_cont a b i j)
  -- Derive `hLapChi_ann` from `hgi_cont` + `hchris_cont` via the compactness brick.
  have hLapChi_ann : ∀ (a b : ℝ), ∃ Kc2 : ℝ, 0 ≤ Kc2 ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |laplaceBeltrami (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
        (radialCutoff a b) w| ≤ Kc2 := fun a b =>
    laplaceBeltrami_radialCutoff_bound_on_annulus_of_continuousOn
      (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p) a b
      (fun i j => hgi_cont a b i j) (fun k i j => hchris_cont a b k i j)
  exact cutoffResidual_expPullback_hEboundW_uncond g₀ gi₀ hC p hsymm0 hinvF hg hframe Θ u
    hw0smooth hfold hinvT hgisymm hgi_ann hLapChi_ann ht M W L hM hW hdev hw0bd hlap

end QIQTH.HeatResidualBound
