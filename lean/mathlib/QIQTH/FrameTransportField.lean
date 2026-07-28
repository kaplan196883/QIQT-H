/-
  FrameTransportField — the combined geodesic + WHOLE-FRAME parallel-transport vector field.

  Step b3c of the a₁=R/6 endgame (the parallel-FRAME ODE).  Where
  `QIQTH.Geodesic.geodesicTransportField` transports a SINGLE vector `e` along the geodesic, this
  file transports an ENTIRE frame `E : Fin n → Point n` (n vectors) at once.  On the extended phase
  space `Point n × Point n × (Fin n → Point n)` (position `x`, velocity `ξ`, frame `E`), the
  combined autonomous field is

    F(x, ξ, E) = (ξ, −Γ(x)(ξ,ξ), fun m ↦ −Γ(x)(ξ, E m)),

  whose first two components are the geodesic system `x' = ξ`, `ξ' = −Γ(x)(ξ,ξ)` (as in
  `QIQTH.Geodesic.geodesicField`) and whose third component `(E m)' = −Γ(x)(ξ, E m)` is the
  parallel-transport equation applied to EACH frame vector `E m` simultaneously.  This field is
  `C^∞` whenever the Christoffel symbols are (`contDiff_geodesicFrameTransportField`, mirroring
  `contDiff_geodesicTransportField`) — the ingredient for Mathlib's Picard–Lindelöf theorem to
  carry the geodesic PLUS the entire parallel frame `{e_i}` along ONE integral curve.

  HONEST CAPTION (binding): this file only defines the whole-frame field and proves its `C^∞`
  regularity.  It does NOT yet prove existence (the next floor), does NOT package the ORTHONORMAL
  frame (parallelism preserves the metric — a further floor), and does NOT establish `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Geodesic
import QIQTH.ParallelTransportField

namespace QIQTH.Geodesic

open QIQTH.Curvature
open Finset

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **The combined geodesic + WHOLE-FRAME parallel-transport vector field** on the extended phase
    space `Point n × Point n × (Fin n → Point n)`.  With `z = (x, ξ, E)` (`z.1 = x` position,
    `z.2.1 = ξ` velocity, `z.2.2 = E` the FRAME `Fin n → Point n`), the field is
    `F(x, ξ, E) = (ξ, −Γ(x)(ξ,ξ), fun m ↦ −Γ(x)(ξ, E m))`: the first two components are the geodesic
    system (`x' = ξ`, `ξ' = −∑_{j,k} Γ^i_{jk}(x) ξ^j ξ^k`) and the third transports each frame
    vector `E m` in parallel along the geodesic (`(E m)'_a = −∑_{j,k} Γ^a_{jk}(x) ξ^j (E m)^k`). -/
noncomputable def geodesicFrameTransportField (g gi : Point n → Fin n → Fin n → ℝ) :
    (Point n × Point n × (Fin n → Point n)) → (Point n × Point n × (Fin n → Point n)) :=
  fun z => (z.2.1,
            (fun i => -∑ j, ∑ k, christoffel g gi i j k z.1 * z.2.1 j * z.2.1 k),
            (fun m => fun a => -∑ j, ∑ k, christoffel g gi a j k z.1 * z.2.1 j * z.2.2 m k))

/-- **The combined whole-frame field is `C^∞`** whenever the Christoffel symbols are.  Assembled
    exactly as `contDiff_geodesicTransportField` from the smoothness of the coordinate/velocity/frame
    projections (`contDiff_fst`/`contDiff_snd`/`contDiff_apply`, the frame component using a DOUBLE
    `contDiff_apply` for the `Fin n → Point n` structure) and of `christoffel` (the carried `hC`),
    through products (`ContDiff.mul`), finite sums (`ContDiff.sum`), negation, and the (right-nested)
    product/pi structure of the extended phase space (`ContDiff.prodMk`, `contDiff_pi`). -/
theorem contDiff_geodesicFrameTransportField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (geodesicFrameTransportField g gi) := by
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
    intro m
    rw [contDiff_pi]
    intro a
    apply ContDiff.neg
    refine ContDiff.sum fun j _ => ?_
    refine ContDiff.sum fun k _ => ?_
    exact (((hC a j k).comp contDiff_fst).mul
        ((contDiff_apply ℝ ℝ j).comp (contDiff_fst.comp contDiff_snd))).mul
      ((contDiff_apply ℝ ℝ k).comp
        ((contDiff_apply ℝ (Point n) m).comp (contDiff_snd.comp contDiff_snd)))

end QIQTH.Geodesic
