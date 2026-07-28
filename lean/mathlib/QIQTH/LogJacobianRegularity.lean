/-
  LogJacobianRegularity — the LOG of the exp-Jacobian determinant is `C²` near the centre
  (a REGULARITY FLOOR brick of the off-radial van-Vleck campaign,
  docs/qg_roadmap/JACOBI_FIELD_PLAN.md).

  Setting.  `Point n = Fin n → ℝ`; `exp_p := expMap g gi hC p`; the exp-Jacobian determinant
  `J(x) = expJacobianDet g gi hC p x = det (D exp_p)_x`.

  This file proves ONLY REGULARITY:
  * `log_expJacobianDet_contDiffOn_two` — there is a radius `r > 0` such that `x ↦ log J(x)`
    is `C²` on `Metric.ball 0 r`.

  Mechanism.
  * `J` is `C²` on the exp-ball `Metric.ball 0 (expRho g gi hC p)`
    (`QIQTH.JacobianRegularity.expJacobianDet_contDiffOn_two`);
  * `J(0) = 1 > 0` (`QIQTH.JacobianDet.expJacobianDet_zero`) and `J` is continuous at `0`, so
    `J > 0` on a neighborhood of `0` (`QIQTH.JacobianRadial.expJacobianDet_pos_nhds`); extract a
    metric ball `ball 0 ε ⊆ {J > 0}` and set `r = min ε (expRho)`, so on `ball 0 r` both
    `J` is `C²` and `J ≠ 0`;
  * `log ∘ J` is then `C²` on `ball 0 r` by `ContDiffOn.log` (chain rule, `log` smooth at ≠ 0).

  ## What this is NOT.
  This establishes only that `log J` is `C²` near the centre — hence its second radial/covariant
  derivative EXISTS off-centre.  It does NOT prove the Jacobi identity `B'' = −R̃ B`, the resc
  hypothesis, the van-Vleck radial ODE, or `a₁ = R/6`; those remain the documented geometric walls.
-/
import Mathlib
import QIQTH.ExpJacobianRegularity
import QIQTH.JacobianRadial

namespace QIQTH.JacobianRegularity

open QIQTH.Curvature QIQTH.ExpMap QIQTH.Geodesic QIQTH.PullbackMetric QIQTH.JacobianDet
open QIQTH.JacobianRadial
open Finset Matrix
open scoped Topology

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **The log exp-Jacobian determinant is `C²` on a neighborhood of the centre.**
    `J = expJacobianDet g gi hC p` is `C²` on the exp-ball `ball 0 (expRho)`
    (`expJacobianDet_contDiffOn_two`); `J(0) = 1 > 0` and `J` is continuous at `0`, so `J > 0` on a
    metric ball `ball 0 ε`; taking `r = min ε (expRho)` gives a ball on which `J` is simultaneously
    `C²` and nonvanishing, so `log ∘ J` is `C²` there by `ContDiffOn.log`.

    REGULARITY ONLY: this only shows `log J` admits a second radial/covariant derivative off-centre;
    it does NOT prove the Jacobi identity `B'' = −R̃ B`, `hresc`, the van-Vleck radial ODE, or
    `a₁ = R/6`. -/
theorem log_expJacobianDet_contDiffOn_two (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ 2 (fun x => Real.log (expJacobianDet g gi hC p x))
      (Metric.ball (0 : Point n) r) := by
  -- `J` is `C²` on the exp-ball.
  have hJ : ContDiffOn ℝ 2 (expJacobianDet g gi hC p)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
    expJacobianDet_contDiffOn_two g gi hC p
  -- `J > 0` on a metric ball `ball 0 ε` around the centre.
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (expJacobianDet_pos_nhds g gi hC p)
  -- shrink to `r = min ε (expRho)`, positive and below both `ε` and `expRho`.
  refine ⟨min ε (expRho g gi hC p), lt_min hε (expRho_pos g gi hC p), ?_⟩
  have hsub_rho : Metric.ball (0 : Point n) (min ε (expRho g gi hC p))
      ⊆ Metric.ball (0 : Point n) (expRho g gi hC p) :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hpos : ∀ x ∈ Metric.ball (0 : Point n) (min ε (expRho g gi hC p)),
      0 < expJacobianDet g gi hC p x := by
    intro x hx
    exact hεsub (Metric.ball_subset_ball (min_le_left _ _) hx)
  -- `log ∘ J` is `C²`: `J` is `C²` on the sub-ball and nonvanishing there.
  exact (hJ.mono hsub_rho).log (fun x hx => (hpos x hx).ne')

end QIQTH.JacobianRegularity
