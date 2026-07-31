/-
# RECENTER brick J4-7 — UNCONDITIONAL (hfd3-free) wrappers of the four RNC-residual lemmas.

`QIQTH.ExpMap.expMap_fderiv3_contDiffOn_one` (`PullbackMetricC3Uncond.lean`) now proves the exp `Jet₄`
regularity obligation `hfd3` UNCONDITIONALLY (hyps only `g₀ gi₀ hC p`).  This file feeds that discharged
`hfd3` into the four downstream recenter-residual lemmas that still carried it as a hypothesis, producing
`_uncond` wrappers with `hfd3` REMOVED and every OTHER (genuine geometric / normalization) hypothesis kept:

* `christoffel_expPullback_contDiffAt_two_uncond`   ← `christoffel_expPullback_contDiffAt_two` (R4b);
* `hw0_expPullback_uncond`                          ← `hw0_expPullback` (R4c);
* `near_uncutResidual_expPullback_clean_uncond`     ← `near_uncutResidual_expPullback_clean` (R4c);
* `cutoffResidual_expPullback_hEboundW_uncond`      ← `cutoffResidual_expPullback_hEboundW` (R5).

Each proof = the original applied verbatim with `QIQTH.ExpMap.expMap_fderiv3_contDiffOn_one g₀ gi₀ hC p`
substituted at the `hfd3` argument slot.  No new axioms, no `sorry`, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.PullbackMetricC3Uncond
import QIQTH.RecenterConnectC3b
import QIQTH.RecenterConnectC3c
import QIQTH.RecenterCutoffC3

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatParametrixError
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.TimeSimplexBeta QIQTH.LeviSeries QIQTH.HeatDuhamel QIQTH.GaussianWidthTolerant
open QIQTH.RNCDecay QIQTH.RNCExpansion
open QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 4

/-- **J4-7 wrapper 1 — `Γ̃ ∈ C²` at `0`, UNCONDITIONAL (no `hfd3`).**  Drops the exp `Jet₄` regularity
`hfd3` from `christoffel_expPullback_contDiffAt_two` by feeding the discharged
`expMap_fderiv3_contDiffOn_one`.  Keeps the genuine ambient smoothness / inverse data. -/
theorem christoffel_expPullback_contDiffAt_two_uncond
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hinv : ∀ a b, (∑ σ, g₀ p a σ * gi₀ p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (a b c : Fin n) :
    ContDiffAt ℝ 2
      (fun y => christoffel (expPullbackMetric g₀ gi₀ hC p)
        (expPullbackMetricInv g₀ gi₀ hC p) a b c y) 0 :=
  christoffel_expPullback_contDiffAt_two g₀ gi₀ hC p hinv hg
    (QIQTH.ExpMap.expMap_fderiv3_contDiffOn_one g₀ gi₀ hC p) a b c

/-- **J4-7 wrapper 2 — `w₀ ∈ C³` at `0`, UNCONDITIONAL (no `hfd3`).**  Drops the exp `Jet₄` regularity
`hfd3` from `hw0_expPullback` by feeding the discharged `expMap_fderiv3_contDiffOn_one`.  Keeps the
van-Vleck normalization `hfold` and the ambient frame/smoothness data. -/
theorem hw0_expPullback_uncond
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ)) :
    ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0 :=
  hw0_expPullback g₀ gi₀ hC p hg hframe Θ u
    (QIQTH.ExpMap.expMap_fderiv3_contDiffOn_one g₀ gi₀ hC p) hfold

/-- **J4-7 wrapper 3 — clean q-centered near-diagonal residual bound, UNCONDITIONAL (no `hfd3`).**
Drops the exp `Jet₄` regularity `hfd3` from `near_uncutResidual_expPullback_clean` by feeding the
discharged `expMap_fderiv3_contDiffOn_one`.  Keeps every other genuine input (ambient frame data,
van-Vleck `hfold`, pointwise nondegeneracy `hinvT`, the `t`/`M`/`W`/`L` analytic bounds). -/
theorem near_uncutResidual_expPullback_clean_uncond
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g₀ y a b = g₀ y b a)
    (hinvF : ∀ y a b, (∑ σ, g₀ y a σ * gi₀ y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ))
    (hinvT : ∀ y i j,
      (∑ σ, expPullbackMetricInv g₀ gi₀ hC p y i σ * expPullbackMetric g₀ gi₀ hC p y σ j)
        = if i = j then 1 else 0)
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |expPullbackMetricInv g₀ gi₀ hC p v i j - (if i = j then (1 : ℝ) else 0)|
        ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
        (foldedCoeff Θ u 0) v| ≤ L) :
    ∃ b : ℝ, 0 < b ∧
      ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |deriv (fun s => heatParametrix 0 Θ u s w) t
            - laplaceBeltrami (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
                (heatParametrix 0 Θ u t) w|
          ≤ ((1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n) * gaussDdimWide t w :=
  near_uncutResidual_expPullback_clean g₀ gi₀ hC p hsymm0 hinvF hg hframe Θ u
    (QIQTH.ExpMap.expMap_fderiv3_contDiffOn_one g₀ gi₀ hC p)
    hfold hinvT ht M W L hM hW hdev hw0bd hlap

/-- **J4-7 wrapper 4 — q-centered cutoff residual width-2 Gaussian bound `hEboundW`, UNCONDITIONAL
(no `hfd3`).**  Drops the exp `Jet₄` regularity `hfd3` from `cutoffResidual_expPullback_hEboundW` by
feeding the discharged `expMap_fderiv3_contDiffOn_one`.  Keeps every other genuine input (ambient frame
data, global cofactor smoothness `hw0smooth`, van-Vleck `hfold`, pointwise nondegeneracy `hinvT`, the
carried pullback-metric continuity residue `hgisymm`/`hgi_ann`/`hLapChi_ann`, and the `t`/`M`/`W`/`L`
analytic bounds). -/
theorem cutoffResidual_expPullback_hEboundW_uncond
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
    (hgi_ann : ∀ (a b : ℝ), ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (w : Point n) (i j : Fin n),
        a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |expPullbackMetricInv g₀ gi₀ hC p w i j| ≤ Kg)
    (hLapChi_ann : ∀ (a b : ℝ), ∃ Kc2 : ℝ, 0 ≤ Kc2 ∧ ∀ w : Point n,
        a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |laplaceBeltrami (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
          (radialCutoff a b) w| ≤ Kc2)
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
        ≤ B * gaussDdimWide t v :=
  cutoffResidual_expPullback_hEboundW g₀ gi₀ hC p hsymm0 hinvF hg hframe Θ u hw0smooth
    (QIQTH.ExpMap.expMap_fderiv3_contDiffOn_one g₀ gi₀ hC p)
    hfold hinvT hgisymm hgi_ann hLapChi_ann ht M W L hM hW hdev hw0bd hlap

end QIQTH.HeatResidualBound
