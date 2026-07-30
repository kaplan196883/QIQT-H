/-
# RECENTER brick R4c — discharge the remaining CARRIED hypotheses of the q-centered near-diagonal
#   residual bound `near_uncutResidual_expPullback` (R4a), and assemble a clean q-centered `hEnear`.

R4a (`QIQTH.HeatResidualBound.near_uncutResidual_expPullback`, `RecenterConnectC3.lean`) instantiates
the abstract finite-regularity near-diagonal residual bound at the exp-pullback metric
`g̃ = expPullbackMetric g₀ gi₀ hC p`, discharging the RNC gauge / structural hypotheses from the landed
`QIQTH.PullbackMetric` lemmas but CARRYING a residual set.  R4b (`RecenterConnectC3b.lean`,
`RecenterDeWittC3.lean`) already landed:

* `hCd`          ← `christoffel_expPullback_contDiffAt_two` (needs `hfd3`);
* `hdgi0`        ← `pd_expPullbackMetricInv_zero` (needs `hinvT`);
* `hw0hessRicci` ← `hw0hessRicci_expPullback` (needs `hfold`).

This file discharges the remaining van-Vleck REGULARITY carries directly from the single van-Vleck
germ identification `hfold : foldedCoeff Θ u 0 =ᶠ[𝓝 0] (det g̃)^{−¼}`:

* **`hw0flat`** (`∂w₀(0) = 0`)  — `hw0flat_expPullback`: chain rule `∂((det g̃)^{−¼}) = −¼(det g̃)^{−⁵ᐟ⁴}∂(det g̃)`
  (`pd_comp_rpow`) with `∂(det g̃)(0) = 0` (`det_pd_first_c2`), transported by the `hfold` germ (`pd_congr`).
* **`hw0`** (`w₀ ∈ C³` at `0`)  — `hw0_expPullback`: `ContDiffAt` is germ-local (`ContDiffAt.congr_of_eventuallyEq`
  on `hfold`); `(det g̃)^{−¼} ∈ C³` from `det g̃ ∈ C³` (`det_contDiffAt3`, needs `g̃ ∈ C³` = `hfd3`) and
  `rpow_const_of_ne` (base `det g̃(0) = 1 ≠ 0`).

Then `near_uncutResidual_expPullback_clean` assembles the full q-centered `hEnear`, carrying ONLY the
genuine irreducible inputs: the ambient frame/smoothness/symmetry/inverse data, the exp `Jet₄`
regularity `hfd3`, the van-Vleck normalization `hfold`, the pointwise nondegeneracy `hinvT`
(the diffeomorphism property of `exp_p`, genuinely needed at every `y` by the abstract consumer), and
the `t`/`M`/`W`/`L` analytic bounds (`hdev`/`hw0bd`/`hlap`).  Every geometric hypothesis is discharged.

A bonus reachability lemma `foldedCoeff_locBounded_expPullback` shows `hw0bd` is derivable from `hfold`
+ continuity (so it is not irreducible).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.RecenterConnectC3
import QIQTH.RecenterConnectC3b
import QIQTH.RecenterDeWittC3
import QIQTH.PullbackMetricC3
import QIQTH.PullbackMetric
import QIQTH.RNCExpansion

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatParametrixError
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.TimeSimplexBeta QIQTH.LeviSeries QIQTH.HeatDuhamel QIQTH.GaussianWidthTolerant
open QIQTH.RNCDecay QIQTH.RNCExpansion
open QIQTH.PullbackMetric QIQTH.ExpMap

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 4

/-! ### General-order determinant regularity helper -/

/-- A finite product of `ContDiffAt ℝ m` fields is `ContDiffAt ℝ m` (general order; the order-2
    `RNCExpansion.contDiffAt_prod` is the `m = 2` specialisation). -/
private theorem contDiffAt_prod_gen {ι : Type*} (m : WithTop ℕ∞) (s : Finset ι)
    (F : ι → Point n → ℝ) (x : Point n)
    (hF : ∀ i ∈ s, ContDiffAt ℝ m (fun y => F i y) x) :
    ContDiffAt ℝ m (fun y => ∏ i ∈ s, F i y) x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty]; exact contDiffAt_const
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hF a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

/-- `C³` variant of `det_contDiffAt2`: `det ∘ g` is `ContDiffAt ℝ 3` at `0` when the entries are. -/
private theorem det_contDiffAt3 (g : Point n → Fin n → Fin n → ℝ)
    (hg3 : ∀ a b, ContDiffAt ℝ 3 (fun y => g y a b) 0) :
    ContDiffAt ℝ 3 (fun y => Matrix.det (g y)) 0 := by
  rw [show (fun y => Matrix.det (g y))
        = (fun y => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, g y (σ i) i)
      from funext (fun y => Matrix.det_apply' _)]
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul
    (contDiffAt_prod_gen 3 univ (fun i y => g y (σ i) i) 0 (fun i _ => hg3 (σ i) i))

/-! ### `hw0flat` — the van-Vleck first jet vanishes -/

/-- **R4c piece — `∂w₀(0) = 0` (discharges the carried `hw0flat`).**  For the exp-pullback metric
`g̃ = expPullbackMetric g₀ gi₀ hC p` and `w₀ = foldedCoeff Θ u 0`, every first partial of `w₀` vanishes
at `0`, given the van-Vleck germ `hfold : w₀ =ᶠ (det g̃)^{−¼}` near `0`.

Chain rule `∂_e((det g̃)^{−¼}) = −¼·(det g̃)^{−⁵ᐟ⁴}·∂_e(det g̃)` (`pd_comp_rpow`); the determinant's first
partial vanishes at `0` because `∂g̃(0) = 0` (`det_pd_first_c2`).  Transported to `w₀` by the germ. -/
theorem hw0flat_expPullback
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g₀ y a b = g₀ y b a)
    (hinvF : ∀ y a b, (∑ σ, g₀ y a σ * gi₀ y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ))
    (e : Fin n) :
    pd (foldedCoeff Θ u 0) e (0 : Point n) = 0 := by
  have hinv : ∀ a b, (∑ σ, g₀ p a σ * gi₀ p σ b) = if a = b then 1 else 0 := fun a b => hinvF p a b
  have hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => expPullbackMetric g₀ gi₀ hC p y a b) 0 :=
    fun a b => contDiffAt2_expPullbackMetric_zero g₀ gi₀ hC p hg a b
  have hdg0 : ∀ a b e', pd (fun y => expPullbackMetric g₀ gi₀ hC p y a b) e' 0 = 0 :=
    fun a b e' => pd_expPullbackMetric_at_zero g₀ gi₀ hC p hsymm0 hinv hg a b e'
  -- `det g̃(0) = 1`.
  have hdet0 : Matrix.det (expPullbackMetric g₀ gi₀ hC p 0) = 1 := by
    have hmat : expPullbackMetric g₀ gi₀ hC p 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      funext i j; rw [expPullbackMetric_at_zero, hframe, Matrix.one_apply]
    rw [hmat, Matrix.det_one]
  have hpos : 0 < Matrix.det (expPullbackMetric g₀ gi₀ hC p 0) := by rw [hdet0]; norm_num
  have hFpdiff : PdiffAt (fun y => Matrix.det (expPullbackMetric g₀ gi₀ hC p y)) e 0 :=
    QIQTH.LaplaceBeltrami.PdiffAt_of_contDiffAt _ e 0
      ((det_contDiffAt2 _ hg2).of_le (by norm_num))
  rw [pd_congr e 0 hfold,
      pd_comp_rpow (fun y => Matrix.det (expPullbackMetric g₀ gi₀ hC p y)) (-1 / 4) e 0 hFpdiff hpos,
      det_pd_first_c2 (expPullbackMetric g₀ gi₀ hC p) hg2 hdg0 e, mul_zero]

/-! ### `hw0` — the van-Vleck coefficient is `C³` -/

/-- **R4c piece — `w₀ ∈ C³` at `0` (discharges the carried `hw0`).**  For `g̃ = expPullbackMetric g₀ gi₀ hC p`
and `w₀ = foldedCoeff Θ u 0`, the coefficient is `ContDiffAt ℝ 3` at `0`, given `hfold` and the exp
`Jet₄` regularity `hfd3`.

`ContDiffAt` is germ-local (`ContDiffAt.congr_of_eventuallyEq` on `hfold`); `(det g̃)^{−¼} ∈ C³` from
`det g̃ ∈ C³` (`det_contDiffAt3`, needing `g̃ ∈ C³` = `contDiffOn_expPullbackMetric_three`, conditional
on `hfd3`) and `rpow_const_of_ne` (base `det g̃(0) = 1 ≠ 0`). -/
theorem hw0_expPullback
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hfd3 : ContDiffOn ℝ 1
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g₀ gi₀ hC p) w) z) v)
      (Metric.ball (0 : Point n) (QIQTH.ExpMap.expRho g₀ gi₀ hC p)))
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ)) :
    ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0 := by
  -- `g̃`-components are `C³` at `0` (conditional on `hfd3`).
  have hg3 : ∀ i j, ContDiffAt ℝ 3 (fun x => expPullbackMetric g₀ gi₀ hC p x i j) 0 := fun i j =>
    (contDiffOn_expPullbackMetric_three g₀ gi₀ hC p hg i j hfd3).contDiffAt
      (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (QIQTH.ExpMap.expRho_pos g₀ gi₀ hC p)))
  have hdet3 : ContDiffAt ℝ 3 (fun y => Matrix.det (expPullbackMetric g₀ gi₀ hC p y)) 0 :=
    det_contDiffAt3 _ hg3
  -- `det g̃(0) = 1 ≠ 0`.
  have hdet0 : Matrix.det (expPullbackMetric g₀ gi₀ hC p 0) = 1 := by
    have hmat : expPullbackMetric g₀ gi₀ hC p 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      funext i j; rw [expPullbackMetric_at_zero, hframe, Matrix.one_apply]
    rw [hmat, Matrix.det_one]
  have hne : (fun y => Matrix.det (expPullbackMetric g₀ gi₀ hC p y)) 0 ≠ 0 := by
    show Matrix.det (expPullbackMetric g₀ gi₀ hC p 0) ≠ 0
    rw [hdet0]; norm_num
  have hrpow : ContDiffAt ℝ 3
      (fun v => (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ)) 0 :=
    hdet3.rpow_const_of_ne hne
  exact hrpow.congr_of_eventuallyEq hfold

/-! ### `hw0bd` reachability — local boundedness of `w₀` from `hfold` + continuity -/

/-- **Bonus (reachability) — `hw0bd` is derivable, not irreducible.**  From `hfold` + continuity of
`(det g̃)^{−¼}` at `0` (value `1`), `w₀ = foldedCoeff Θ u 0` is locally bounded by `2`. -/
theorem foldedCoeff_locBounded_expPullback
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ)) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W := by
  have hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => expPullbackMetric g₀ gi₀ hC p y a b) 0 :=
    fun a b => contDiffAt2_expPullbackMetric_zero g₀ gi₀ hC p hg a b
  have hdet0 : Matrix.det (expPullbackMetric g₀ gi₀ hC p 0) = 1 := by
    have hmat : expPullbackMetric g₀ gi₀ hC p 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      funext i j; rw [expPullbackMetric_at_zero, hframe, Matrix.one_apply]
    rw [hmat, Matrix.det_one]
  have hne : (fun y => Matrix.det (expPullbackMetric g₀ gi₀ hC p y)) 0 ≠ 0 := by
    show Matrix.det (expPullbackMetric g₀ gi₀ hC p 0) ≠ 0
    rw [hdet0]; norm_num
  have hcontrpow : ContinuousAt
      (fun v => (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ)) 0 :=
    ((det_contDiffAt2 _ hg2).rpow_const_of_ne hne).continuousAt
  have habs : ContinuousAt
      (fun v => |(Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ)|) 0 :=
    hcontrpow.abs
  have hval0 : (Matrix.det (expPullbackMetric g₀ gi₀ hC p 0)) ^ (-1 / 4 : ℝ) = 1 := by
    rw [hdet0, Real.one_rpow]
  have hlt : ∀ᶠ v in nhds (0 : Point n),
      |(Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ)| < 2 :=
    habs.eventually_lt continuousAt_const (by
      show |(Matrix.det (expPullbackMetric g₀ gi₀ hC p 0)) ^ (-1 / 4 : ℝ)| < 2
      rw [hval0]; norm_num)
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [hfold, hlt] with v hv hvlt
  rw [hv]; exact hvlt.le

/-! ### The clean q-centered `hEnear` -/

/-- **★ R4c — the clean q-centered near-diagonal residual bound `hEnear`.**
Instantiates `near_uncutResidual_expPullback` (R4a) at `g̃ = expPullbackMetric g₀ gi₀ hC p` with every
GEOMETRIC hypothesis discharged: `hCd` (`christoffel_expPullback_contDiffAt_two`), `hdgi0`
(`pd_expPullbackMetricInv_zero`), `hw0hessRicci` (`hw0hessRicci_expPullback`), `hw0flat`
(`hw0flat_expPullback`), `hw0` (`hw0_expPullback`).

The carried set is the genuine irreducible residue:
* ambient frame/smoothness/symmetry/inverse data `g₀ gi₀ hC p hsymm0 hinvF hg hframe`;
* exp `Jet₄` regularity `hfd3` (the terminal recenter wall);
* van-Vleck normalization `hfold` (`Θ = √det g̃`, `u₀ = 1`);
* pointwise nondegeneracy `hinvT` (the diffeomorphism property of `exp_p`; the abstract consumer
  `near_uncutResidual_gaussianWide_ball_C3` genuinely uses the inverse relation at every `y`);
* the `t`/`M`/`W`/`L` analytic bounds `hdev`/`hw0bd`/`hlap` (the honest `O(r²)`/boundedness residue).

NOT `a₁ = R/6`. -/
theorem near_uncutResidual_expPullback_clean
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g₀ y a b = g₀ y b a)
    (hinvF : ∀ y a b, (∑ σ, g₀ y a σ * gi₀ y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    -- exp `Jet₄` regularity (the terminal recenter wall)
    (hfd3 : ContDiffOn ℝ 1
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g₀ gi₀ hC p) w) z) v)
      (Metric.ball (0 : Point n) (QIQTH.ExpMap.expRho g₀ gi₀ hC p)))
    -- van-Vleck normalization
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ))
    -- pointwise nondegeneracy (diffeomorphism property of `exp_p`)
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
          ≤ ((1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n) * gaussDdimWide t w := by
  have hinv : ∀ a b, (∑ σ, g₀ p a σ * gi₀ p σ b) = if a = b then 1 else 0 := fun a b => hinvF p a b
  exact near_uncutResidual_expPullback g₀ gi₀ hC p hsymm0 hinvF hg hframe Θ u
    (christoffel_expPullback_contDiffAt_two g₀ gi₀ hC p hinv hg hfd3)
    (pd_expPullbackMetricInv_zero g₀ gi₀ hC p hsymm0 hinvF hg hframe hinvT)
    hinvT
    (hw0_expPullback g₀ gi₀ hC p hg hframe Θ u hfd3 hfold)
    (hw0flat_expPullback g₀ gi₀ hC p hsymm0 hinvF hg hframe Θ u hfold)
    (hw0hessRicci_expPullback g₀ gi₀ hC p hsymm0 hinvF hg hframe Θ u hfold)
    ht M W L hM hW hdev hw0bd hlap

end QIQTH.HeatResidualBound
