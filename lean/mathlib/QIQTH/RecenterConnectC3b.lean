/-
# RECENTER brick R4b — shrink the carried set of `near_uncutResidual_expPullback` (R4a).

R4a (`QIQTH.HeatResidualBound.near_uncutResidual_expPullback`, `RecenterConnectC3.lean`) landed the
q-centered near-diagonal residual bound at the exp-pullback metric `g̃ = expPullbackMetric g₀ gi₀ hC p`,
discharging 8 RNC gauge hypotheses and CARRYING five structural / DeWitt facts:
`hCd` (`Γ̃ ∈ C²` at `0`), `hdgi0` (`∂g̃⁻¹(0)=0`), `hinvT` (pointwise `g̃⁻¹·g̃=δ`), `hdev` (`O(r²)`
inverse deviation), and the van-Vleck / DeWitt heat-coefficient jet
(`hw0`/`hw0flat`/`hw0hessRicci`/`hw0bd`/`hlap`).

This brick discharges the two genuinely reachable structural facts, turning them into landed lemmas
(so a future R-brick can drop `hCd` and `hdgi0` from the carried set):

* `christoffel_expPullback_contDiffAt_two`  (discharges `hCd`): the Christoffel symbols of `g̃` are
  `C²` at `0`, built from `g̃ ∈ C³` (`contDiffOn_expPullbackMetric_three`, conditional on `hfd3`) via
  the third-partial extractor, and `g̃⁻¹ ∈ C²` (`expPullbackMetricInv_contDiffAt_two`).  Carries only
  the genuine Jet₄ regularity `hfd3` (plus the ambient smoothness/inverse data).

* `pd_expPullbackMetricInv_zero`             (discharges `hdgi0`): `∂g̃⁻¹(0) = 0`, obtained by
  differentiating the matrix-inverse identity `g̃⁻¹·g̃ = δ` at `0` (Leibniz), using `∂g̃(0)=0`
  (`pd_expPullbackMetric_at_zero`) and the frame `g̃(0)=δ`.

The van-Vleck / DeWitt jet `hw0hessRicci` is a genuine sub-wall (a q-centered DeWitt-coefficient
construction, not yet in the repo) — see the module note at the bottom.  It is NOT discharged here,
and this brick does NOT claim `a₁ = R/6`.
-/
import Mathlib
import QIQTH.RecenterConnectC3
import QIQTH.PullbackMetricC3
import QIQTH.PullbackMetric
import QIQTH.RNCExpansion
import QIQTH.CutoffResidualFiniteReg

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.ExpMap
open QIQTH.PullbackMetric

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000
-- the third-jet CLM tower (`fderiv³ exp_p`) needs a deeper pending-instance depth (mirrors R3c-1).
set_option maxSynthPendingDepth 4

/-- **Third-partial extractor** (local copy of the private `OffDiagLittleOFiniteReg` helper).
`ContDiffAt ℝ 3 f x → ContDiffAt ℝ 2 (fun y => pd f m y) x`: `fderiv f` is `C²`, applying it to the
constant basis covector `eₘ` is `C²`, and this equals `pd f m` on the differentiable germ at `x`. -/
private theorem contDiffAt2_pd_of_contDiffAt3 (f : Point n → ℝ) (m : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 3 f x) : ContDiffAt ℝ 2 (fun y => pd f m y) x := by
  have hfd2 : ContDiffAt ℝ 2 (fun y => fderiv ℝ f y) x := hf.fderiv_right (m := 2) (by norm_num)
  have happ : ContDiffAt ℝ 2 (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) x :=
    hfd2.clm_apply contDiffAt_const
  have hdf_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have e1 : (fun y => pd f m y) =ᶠ[nhds x] (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f m y hy
  exact happ.congr_of_eventuallyEq e1

/-- **R4b piece 1 — `Γ̃ ∈ C²` at `0` (discharges the carried `hCd`).**  The Christoffel symbols of the
exp-pullback metric `g̃ = expPullbackMetric g₀ gi₀ hC p` (with genuine inverse
`g̃⁻¹ = expPullbackMetricInv g₀ gi₀ hC p`) are `ContDiffAt ℝ 2` at `0`.

`christoffel g̃ g̃⁻¹` is `½ ∑_α g̃⁻¹·(∂g̃-bracket)`; `C²`-of-`Γ̃` needs `C³`-of-`g̃` (through the first
partial) and `C²`-of-`g̃⁻¹`.  The former is `contDiffOn_expPullbackMetric_three` (R3c-1, conditional
on the genuine Jet₄ regularity `hfd3`) fed through the third-partial extractor; the latter is
`expPullbackMetricInv_contDiffAt_two` (R4a). -/
theorem christoffel_expPullback_contDiffAt_two
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hinv : ∀ a b, (∑ σ, g₀ p a σ * gi₀ p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hfd3 : ContDiffOn ℝ 1
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g₀ gi₀ hC p) w) z) v)
      (Metric.ball (0 : Point n) (QIQTH.ExpMap.expRho g₀ gi₀ hC p)))
    (a b c : Fin n) :
    ContDiffAt ℝ 2
      (fun y => christoffel (expPullbackMetric g₀ gi₀ hC p)
        (expPullbackMetricInv g₀ gi₀ hC p) a b c y) 0 := by
  -- `g̃`-components are `C³` at `0` (conditional on `hfd3`).
  have hg3 : ∀ i j, ContDiffAt ℝ 3 (fun x => expPullbackMetric g₀ gi₀ hC p x i j) 0 := by
    intro i j
    exact (contDiffOn_expPullbackMetric_three g₀ gi₀ hC p hg i j hfd3).contDiffAt
      (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (QIQTH.ExpMap.expRho_pos g₀ gi₀ hC p)))
  -- the first partials `∂ₖ g̃_{ij}` are `C²` at `0`.
  have hpd : ∀ i j k, ContDiffAt ℝ 2
      (fun x => pd (fun y => expPullbackMetric g₀ gi₀ hC p y i j) k x) 0 := fun i j k =>
    contDiffAt2_pd_of_contDiffAt3 (fun y => expPullbackMetric g₀ gi₀ hC p y i j) k 0 (hg3 i j)
  -- `g̃⁻¹`-entries are `C²` at `0`.
  have hgi : ∀ i j, ContDiffAt ℝ 2 (fun x => expPullbackMetricInv g₀ gi₀ hC p x i j) 0 :=
    fun i j => expPullbackMetricInv_contDiffAt_two g₀ gi₀ hC p hinv hg i j
  simp only [christoffel]
  refine contDiffAt_const.mul ?_
  refine ContDiffAt.sum (fun α _ => ?_)
  exact (hgi a α).mul (((hpd α c b).add (hpd α b c)).sub (hpd b c α))

/-- **R4b piece 2 — `∂g̃⁻¹(0) = 0` (discharges the carried `hdgi0`).**  For the exp-pullback metric
`g̃ = expPullbackMetric g₀ gi₀ hC p` with genuine inverse `g̃⁻¹ = expPullbackMetricInv g₀ gi₀ hC p`,
every first partial of `g̃⁻¹` vanishes at `0`.

Obtained by differentiating the matrix-inverse identity `∑_σ g̃⁻¹_{iσ}·g̃_{σj} = δ_{ij}` (`hinvT`) at
`0` (Leibniz `pd_mul`): the `g̃⁻¹·∂g̃` half drops because `∂g̃(0)=0`
(`pd_expPullbackMetric_at_zero`), and the surviving `∂g̃⁻¹·g̃(0)` half, with `g̃(0)=δ` (the frame),
collapses the Kronecker sum to `∂g̃⁻¹_{ij}(0)`, which must therefore equal `∂(δ_{ij}) = 0`.

`hinvT` is the pointwise nondegeneracy already carried by `near_uncutResidual_expPullback`, so this
lemma net-removes `hdgi0` from the carried set. -/
theorem pd_expPullbackMetricInv_zero
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g₀ y a b = g₀ y b a)
    (hinvF : ∀ y a b, (∑ σ, g₀ y a σ * gi₀ y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (hinvT : ∀ y i j,
      (∑ σ, expPullbackMetricInv g₀ gi₀ hC p y i σ * expPullbackMetric g₀ gi₀ hC p y σ j)
        = if i = j then 1 else 0)
    (i j e : Fin n) :
    pd (fun x => expPullbackMetricInv g₀ gi₀ hC p x i j) e (0 : Point n) = 0 := by
  -- ambient inverse relation at `p`.
  have hinv : ∀ a b, (∑ σ, g₀ p a σ * gi₀ p σ b) = if a = b then 1 else 0 := fun a b => hinvF p a b
  -- per-factor partial differentiability at `0`.
  have hPgti : ∀ σ, PdiffAt (fun x => expPullbackMetricInv g₀ gi₀ hC p x i σ) e 0 := fun σ =>
    PdiffAt_of_contDiffAt _ e 0 ((expPullbackMetricInv_contDiffAt_two g₀ gi₀ hC p hinv hg i σ).of_le
      (by norm_num))
  have hPgt : ∀ σ, PdiffAt (fun x => expPullbackMetric g₀ gi₀ hC p x σ j) e 0 := fun σ =>
    PdiffAt_of_contDiffAt _ e 0 ((contDiffAt2_expPullbackMetric_zero g₀ gi₀ hC p hg σ j).of_le
      (by norm_num))
  -- the inverse identity is a constant function of `x`, so its partial vanishes.
  have hpdF : pd (fun x => ∑ σ, expPullbackMetricInv g₀ gi₀ hC p x i σ
      * expPullbackMetric g₀ gi₀ hC p x σ j) e 0 = 0 := by
    have hconst : (fun x => ∑ σ, expPullbackMetricInv g₀ gi₀ hC p x i σ
        * expPullbackMetric g₀ gi₀ hC p x σ j) = (fun _ => (if i = j then (1 : ℝ) else 0)) := by
      funext x; exact hinvT x i j
    rw [hconst]; exact pd_const _ e 0
  -- expand the partial of the sum by the Leibniz rule.
  rw [pd_sum univ (fun σ x => expPullbackMetricInv g₀ gi₀ hC p x i σ
        * expPullbackMetric g₀ gi₀ hC p x σ j) e 0 (fun σ _ => (hPgti σ).mul (hPgt σ)),
    Finset.sum_congr rfl (fun σ _ => pd_mul (fun x => expPullbackMetricInv g₀ gi₀ hC p x i σ)
        (fun x => expPullbackMetric g₀ gi₀ hC p x σ j) e 0 (hPgti σ) (hPgt σ))] at hpdF
  -- collapse: `∂g̃(0)=0` kills the second half, the frame `g̃(0)=δ` collapses the first.
  have hgt0 : ∀ σ, expPullbackMetric g₀ gi₀ hC p 0 σ j = (if σ = j then (1 : ℝ) else 0) := fun σ => by
    rw [expPullbackMetric_at_zero g₀ gi₀ hC p σ j]; exact hframe σ j
  have hpdgt0 : ∀ σ, pd (fun x => expPullbackMetric g₀ gi₀ hC p x σ j) e 0 = 0 := fun σ =>
    pd_expPullbackMetric_at_zero g₀ gi₀ hC p hsymm0 hinv hg σ j e
  simp only [hgt0, hpdgt0, mul_zero, add_zero, mul_ite, mul_one] at hpdF
  rw [Finset.sum_ite_eq' univ j (fun σ => pd (fun x => expPullbackMetricInv g₀ gi₀ hC p x i σ) e 0)]
    at hpdF
  simpa using hpdF

end QIQTH.HeatResidualBound
