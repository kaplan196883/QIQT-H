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

/-- **Local existence of the geodesic + parallel-transport integral curve (Picard–Lindelöf).**
    For any initial phase point `z₀ = (p, v, e₀) ∈ Point n × Point n × Point n` and any base time
    `t₀`, there is a curve `γ : ℝ → Point n × Point n × Point n` with `γ t₀ = z₀` solving the
    first-order autonomous system `γ' t = F(γ t)` (with `F = geodesicTransportField g gi`) on an
    open interval `(t₀ − ε, t₀ + ε)`.  Mirrors `geodesic_local_existence` exactly, swapping in the
    extended field and phase space.  The components read: `γ.1` = geodesic position, `γ.2.1` =
    velocity (`γ.1' = γ.2.1`, `γ.2.1' = −Γ(γ.1)(γ.2.1, γ.2.1)`), and `γ.2.2` = the
    PARALLEL-TRANSPORTED vector `e(t)` along the geodesic (`e'(t) = −Γ(γ.1)(γ.2.1, e)`, i.e. the
    covariant derivative of `e` along `γ.2.1` vanishes — parallelism).  Starting `z₀ = (p, v, e₀)`
    transports `e₀` along the geodesic from `p` with velocity `v`.  Uses the `C¹` Picard–Lindelöf
    lemma `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`.

    HONEST: existence only.  This does NOT yet build the orthonormal FRAME (n copies of the
    transported vector plus `parallel_orthonormal_preserved`, the next floor), does NOT discharge the
    van-Vleck carried frame data, and does NOT establish `a₁ = R/6`. -/
theorem parallelTransport_local_existence (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (z₀ : Point n × Point n × Point n) (t₀ : ℝ) :
    ∃ γ : ℝ → Point n × Point n × Point n, γ t₀ = z₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt γ (geodesicTransportField g gi (γ t)) t :=
  (((contDiff_geodesicTransportField g gi hC).of_le le_top).contDiffAt
    (x := z₀)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

end QIQTH.Geodesic
