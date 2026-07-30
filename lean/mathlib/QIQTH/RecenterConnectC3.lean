/-
# RECENTER brick R4 — connect the q-centered exp-pullback metric to the near-diagonal
#   finite-regularity residual bound.

This file instantiates the abstract near-diagonal residual bound
`QIQTH.HeatResidualBound.near_uncutResidual_gaussianWide_ball_C3` at the exp-pullback metric
`g̃ = expPullbackMetric g₀ gi₀ hC p` (with its genuine matrix inverse
`g̃⁻¹ = expPullbackMetricInv g₀ gi₀ hC p`) for a base point `p`.

The RNC gauge / structural hypotheses of the abstract theorem are DISCHARGED from the landed
`QIQTH.PullbackMetric` lemmas (exactly the discharge already used in
`kappa_eq_one_sixth_expPullback`):

* `hg`   (`g̃` is `C²` at `0`)              — `contDiffAt2_expPullbackMetric_zero`;
* `hgiC` (`g̃⁻¹` is `C²` at `0`)            — `expPullbackMetricInv_contDiffAt_two` (this file);
* `hg0`  (`g̃(0) = δ`)                      — `expPullbackMetric_at_zero` + the orthonormal frame;
* `hgi0` (`g̃⁻¹(0) = δ`)                    — `expPullbackMetricInv_zero` + (frame + `hinvF` ⟹ `gi₀ p = δ`);
* `hdg0` (`∂g̃(0) = 0`)                     — `pd_expPullbackMetric_at_zero`;
* `hΓ0`  (`Γ̃(0) = 0`)                      — `christoffel_expPullbackMetric_zero`;
* `hsymm`(`g̃` symmetric)                   — `expPullbackMetric_symm`;
* `hgauge`(cyclic RNC gauge for `g̃`)       — `gauge_pd_christoffel_expPullbackInv_zero'`.

The remaining hypotheses are CARRIED as genuine (satisfiable, e.g. by the flat metric) Props, because
they are not yet available as landed pullback lemmas:

* `hCd`   (`Γ̃` is `C²` at `0`) — needs `C³` of `g̃` (i.e. the `hfd3` Jet₄ regularity) fed through
  the Christoffel derivative; a one-step follow-up.
* `hdgi0` (`∂g̃⁻¹(0) = 0`)      — derivable from `hinvT` + `∂g̃(0)=0` + `g̃(0)=δ` by differentiating the
  matrix-inverse identity; carried here.
* `hinvT` (`g̃⁻¹·g̃ = δ` at every `y`) — the pointwise nondegeneracy of `g̃` (true where `exp_p` is a
  diffeomorphism; false at singular points, so genuinely carried).
* the van-Vleck / DeWitt data `hw0`, `hw0flat`, `hw0hessRicci`, `hw0bd`, `hlap` — the q-centered
  heat-coefficient jet (`= −⅓ Ric` etc.); the genuine R4b sub-wall.
* `hdev`  (`g̃⁻¹ = δ + O(r²)`) — the O(r²) inverse-metric deviation.

This is the metric-side R4a connection: the largest reachable green instantiation of the abstract
near-diagonal residual bound at the q-centered normal chart.  It is NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.NearResidualC3
import QIQTH.PullbackMetricC3
import QIQTH.PullbackMetric
import QIQTH.CutoffResidualFiniteReg
import QIQTH.RNCExpansion

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatParametrixError
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.TimeSimplexBeta QIQTH.LeviSeries QIQTH.HeatDuhamel QIQTH.GaussianWidthTolerant
open QIQTH.RNCDecay
open QIQTH.PullbackMetric

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **`g̃⁻¹` is `C²` at `0`.**  The exact order-2 analogue of
`QIQTH.PullbackMetric.expPullbackMetricInv_contDiffAt_one`: `matToCLM (g̃ ·)` is `C²` at `0` (its
entries are `C²`, `contDiffAt2_expPullbackMetric_zero`), `Ring.inverse` is `C^∞` at the unit
`matToCLM (g̃ 0)`, and entry-evaluation is continuous-linear.  (The `C¹` version deliberately
downgraded the metric to order 1 because its consumer `heat_a1_of_gauge_c2` needs only `C¹`; here we
keep the full `C²`, which is what the near-diagonal residual bound consumes.) -/
theorem expPullbackMetricInv_contDiffAt_two (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (μ α : Fin n) :
    ContDiffAt ℝ 2 (fun x => expPullbackMetricInv g gi hC p x μ α) 0 := by
  -- the operator field `x ↦ matToCLM (g̃ x)` is `C²` at `0` (its entries are `C²`).
  have hmet_cd : ContDiffAt ℝ (2 : WithTop ℕ∞)
      (fun x => matToCLM (fun a b => expPullbackMetric g gi hC p x a b)) 0 := by
    show ContDiffAt ℝ (2 : WithTop ℕ∞)
      (fun x => ∑ a, ∑ b, expPullbackMetric g gi hC p x a b • elemCLM a b) 0
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro b _
    exact (contDiffAt2_expPullbackMetric_zero g gi hC p hg a b).smul contDiffAt_const
  -- `Ring.inverse` is `C^∞` (hence `C²`) at the unit `matToCLM (g̃ 0)`.
  have hinv_cd : ContDiffAt ℝ (2 : WithTop ℕ∞) Ring.inverse
      (matToCLM (fun a b => expPullbackMetric g gi hC p 0 a b)) :=
    contDiffAt_ringInverse ℝ (metricCLMUnit0 g gi hC p hinv)
  have hcomp := hinv_cd.comp 0 hmet_cd
  have hfull := (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) μ).contDiff
      (n := (2 : WithTop ℕ∞))).contDiffAt).comp 0
    ((((ContinuousLinearMap.apply ℝ (Point n) (Pi.single α (1 : ℝ) : Point n)).contDiff
      (n := (2 : WithTop ℕ∞))).contDiffAt).comp 0 hcomp)
  have heq : (fun x => expPullbackMetricInv g gi hC p x μ α)
      = fun x => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) μ)
          ((ContinuousLinearMap.apply ℝ (Point n) (Pi.single α (1 : ℝ) : Point n))
            (Ring.inverse (matToCLM (fun a b => expPullbackMetric g gi hC p x a b)))) := by
    funext x
    simp only [expPullbackMetricInv, ContinuousLinearMap.apply_apply, ContinuousLinearMap.proj_apply]
  rw [heq]
  exact hfull

/-- **R4 — the near-diagonal finite-regularity residual bound, in the q-centered exp-normal chart.**

Instantiates `near_uncutResidual_gaussianWide_ball_C3` at the exp-pullback metric
`g̃ = expPullbackMetric g₀ gi₀ hC p` and its genuine inverse `g̃⁻¹ = expPullbackMetricInv g₀ gi₀ hC p`,
with the RNC gauge / structural hypotheses (`hg`/`hgiC`/`hg0`/`hgi0`/`hdg0`/`hΓ0`/`hsymm`/`hgauge`)
DISCHARGED from the landed `QIQTH.PullbackMetric` lemmas via the orthonormal frame `hframe` and the
ambient smoothness/symmetry/inverse data `hg`/`hsymm0`/`hinvF`.

The Christoffel `C²` regularity `hCd`, the inverse first-jet `hdgi0`, the pointwise nondegeneracy
`hinvT`, the O(r²) inverse deviation `hdev`, and the whole q-centered van-Vleck / DeWitt jet
(`hw0`/`hw0flat`/`hw0hessRicci`/`hw0bd`/`hlap`) are carried as GENUINE hypotheses — the R4b
DeWitt-coefficient side that is not yet a landed pullback lemma.

The conclusion is exactly the q-centered near-diagonal residual bound: the concrete `N=0` heat
parametrix residual of the pullback metric is dominated, on an explicit `b`-ball, by the width-2
wide Gaussian.  NOT `a₁ = R/6`. -/
theorem near_uncutResidual_expPullback
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g₀ y a b = g₀ y b a)
    (hinvF : ∀ y a b, (∑ σ, g₀ y a σ * gi₀ y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    -- carried: `Γ̃` is `C²` at `0` (needs `C³` of `g̃`; the R3c-1 `hfd3` Jet₄ regularity, one step on)
    (hCd : ∀ a b c, ContDiffAt ℝ 2
      (fun y => christoffel (expPullbackMetric g₀ gi₀ hC p)
        (expPullbackMetricInv g₀ gi₀ hC p) a b c y) 0)
    -- carried: `∂g̃⁻¹(0) = 0` (derivable from `hinvT` + `∂g̃(0)=0` + `g̃(0)=δ`)
    (hdgi0 : ∀ i j e,
      pd (fun y => expPullbackMetricInv g₀ gi₀ hC p y i j) e (0 : Point n) = 0)
    -- carried: pointwise nondegeneracy `g̃⁻¹·g̃ = δ` (true where `exp_p` is a diffeomorphism)
    (hinvT : ∀ y i j,
      (∑ σ, expPullbackMetricInv g₀ gi₀ hC p y i σ * expPullbackMetric g₀ gi₀ hC p y σ j)
        = if i = j then 1 else 0)
    -- carried: the q-centered van-Vleck / DeWitt heat-coefficient jet (the R4b sub-wall)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci (expPullbackMetric g₀ gi₀ hC p)
                (expPullbackMetricInv g₀ gi₀ hC p) a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel (expPullbackMetric g₀ gi₀ hC p)
                              (expPullbackMetricInv g₀ gi₀ hC p) a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel (expPullbackMetric g₀ gi₀ hC p)
                              (expPullbackMetricInv g₀ gi₀ hC p) b i i y) a 0)))
            * foldedCoeff Θ u 0 0)
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
  -- the ambient inverse relation at `p`, in the pointwise shape the pullback lemmas consume.
  have hinv : ∀ a b, (∑ σ, g₀ p a σ * gi₀ p σ b) = if a = b then 1 else 0 := fun a b => hinvF p a b
  -- `g₀ p = δ` (frame) and `g₀ p · gi₀ p = δ` force `gi₀ p = δ`.
  have hgiδ : ∀ a b, gi₀ p a b = if a = b then 1 else 0 := by
    intro a b
    have h := hinvF p a b
    simp only [hframe, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at h
    exact h
  refine near_uncutResidual_gaussianWide_ball_C3
    (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p) Θ u
    -- hg : g̃ is C² at 0
    (fun a b => contDiffAt2_expPullbackMetric_zero g₀ gi₀ hC p hg a b)
    -- hgiC : g̃⁻¹ is C² at 0
    (fun i j => expPullbackMetricInv_contDiffAt_two g₀ gi₀ hC p hinv hg i j)
    -- hCd : Γ̃ is C² at 0 (carried)
    hCd
    -- hw0 : foldedCoeff is C³ at 0 (carried)
    hw0
    -- hg0 : g̃(0) = δ
    (fun i j => by
      simp only [expPullbackMetric_at_zero, hframe, Matrix.one_apply])
    -- hgi0 : g̃⁻¹(0) = δ
    (fun i j => by
      rw [expPullbackMetricInv_zero g₀ gi₀ hC p hinv, hgiδ])
    -- hdg0 : ∂g̃(0) = 0
    (fun a b e => pd_expPullbackMetric_at_zero g₀ gi₀ hC p hsymm0 hinv hg a b e)
    -- hdgi0 : ∂g̃⁻¹(0) = 0 (carried)
    hdgi0
    -- hΓ0 : Γ̃(0) = 0
    (fun k i j => christoffel_expPullbackMetric_zero g₀ gi₀ hC p
      (expPullbackMetricInv g₀ gi₀ hC p) hsymm0 hinv hg k i j)
    -- hsymm : g̃ symmetric
    (fun y a b => expPullbackMetric_symm g₀ gi₀ hC p hsymm0 y a b)
    -- hinv (pointwise nondegeneracy, carried)
    hinvT
    -- hgauge : cyclic RNC gauge for g̃
    (fun i a b c => by
      have hg3 := gauge_pd_christoffel_expPullbackInv_zero' g₀ gi₀ hC p hsymm0 hinvF hg i a b c
      linarith [hg3])
    -- hw0flat, hw0hessRicci (carried)
    hw0flat hw0hessRicci
    ht M W L hM hW hdev hw0bd hlap

end QIQTH.HeatResidualBound
