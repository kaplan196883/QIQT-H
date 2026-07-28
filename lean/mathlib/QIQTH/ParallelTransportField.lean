/-
  ParallelTransportField — the combined geodesic + parallel-transport vector field.

  Step b of the a₁=R/6 endgame (the parallel-transport ODE, first floor).  On the extended
  phase space `Point n × Point n × Point n` (position `x`, velocity `ξ`, transported vector `e`),
  the combined autonomous field is

    F(x, ξ, e) = (ξ, −Γ(x)(ξ,ξ), −Γ(x)(ξ,e)),

  whose first two components are the geodesic system `x' = ξ`, `ξ' = −Γ(x)(ξ,ξ)` (as in
  `QIQTH.Geodesic.geodesicField`) and whose third component `e' = −Γ(x)(ξ,e)` is the
  parallel-transport equation for `e` along the geodesic.  This field is `C^∞` whenever the
  Christoffel symbols are (`contDiff_geodesicTransportField`, mirroring
  `contDiff_geodesicField`) — the ingredient for Mathlib's Picard–Lindelöf theorem to give a
  local integral curve carrying the parallel-transported frame.

  HONEST CAPTION (binding): this file only defines the field and proves its `C^∞` regularity.
  It does NOT yet prove existence (that is the next floor, via
  `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`), does NOT build
  the parallel-transported frame construction, and does NOT establish `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Geodesic

namespace QIQTH.Geodesic

open QIQTH.Curvature
open Finset

variable {n : ℕ}

/-- **The combined geodesic + parallel-transport vector field** on the extended phase space
    `Point n × Point n × Point n`.  With `z = (x, ξ, e)` (`z.1 = x` position, `z.2.1 = ξ`
    velocity, `z.2.2 = e` transported vector), the field is
    `F(x, ξ, e) = (ξ, −Γ(x)(ξ,ξ), −Γ(x)(ξ,e))`: the first two components are the geodesic system
    (`x' = ξ`, `ξ' = −∑_{j,k} Γ^i_{jk}(x) ξ^j ξ^k`) and the third is parallel transport of `e`
    along the geodesic (`e' = −∑_{j,k} Γ^i_{jk}(x) ξ^j e^k`). -/
noncomputable def geodesicTransportField (g gi : Point n → Fin n → Fin n → ℝ) :
    (Point n × Point n × Point n) → (Point n × Point n × Point n) :=
  fun z => (z.2.1,
            (fun i => -∑ j, ∑ k, christoffel g gi i j k z.1 * z.2.1 j * z.2.1 k),
            (fun i => -∑ j, ∑ k, christoffel g gi i j k z.1 * z.2.1 j * z.2.2 k))

/-- **The combined field is `C^∞`** whenever the Christoffel symbols are.  Assembled exactly as
    `contDiff_geodesicField` from the smoothness of the coordinate/velocity/transport projections
    (`contDiff_fst`/`contDiff_snd`/`contDiff_apply`) and of `christoffel` (the carried `hC`),
    through products (`ContDiff.mul`), finite sums (`ContDiff.sum`), negation, and the
    (right-nested) product/pi structure of the extended phase space (`ContDiff.prodMk`,
    `contDiff_pi`). -/
theorem contDiff_geodesicTransportField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (geodesicTransportField g gi) := by
  apply ContDiff.prodMk (contDiff_fst.comp contDiff_snd)
  apply ContDiff.prodMk
  · rw [contDiff_pi]
    intro i
    apply ContDiff.neg
    refine ContDiff.sum fun j _ => ?_
    refine ContDiff.sum fun k _ => ?_
    exact (((hC i j k).comp contDiff_fst).mul
        ((contDiff_apply ℝ ℝ j).comp (contDiff_fst.comp contDiff_snd))).mul
      ((contDiff_apply ℝ ℝ k).comp (contDiff_fst.comp contDiff_snd))
  · rw [contDiff_pi]
    intro i
    apply ContDiff.neg
    refine ContDiff.sum fun j _ => ?_
    refine ContDiff.sum fun k _ => ?_
    exact (((hC i j k).comp contDiff_fst).mul
        ((contDiff_apply ℝ ℝ j).comp (contDiff_fst.comp contDiff_snd))).mul
      ((contDiff_apply ℝ ℝ k).comp (contDiff_snd.comp contDiff_snd))

end QIQTH.Geodesic
