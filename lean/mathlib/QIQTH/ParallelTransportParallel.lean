/-
  ParallelTransportParallel — the transported vector is PARALLEL along the geodesic.

  Step b3a of the a₁=R/6 endgame.  Given the geodesic + parallel-transport integral curve
  `Γc : ℝ → Point n × Point n × Point n` from `parallelTransport_local_existence` (i.e.
  `HasDerivAt Γc (geodesicTransportField g gi (Γc t)) t`), whose components are
  `Γc.1` = position, `Γc.2.1` = velocity, `Γc.2.2` = the transported vector `e`, this file proves
  that the transported vector is genuinely PARALLEL along the geodesic: its covariant derivative
  along the curve vanishes,

    covariantDerivAlong g gi (fun s => (Γc s).1) (fun s => (Γc s).2.2) t = 0,

  which is exactly the `hpar` hypothesis consumed by `parallel_orthonormal_preserved`.

  The proof extracts the two coordinate derivatives from the single vector `HasDerivAt` by
  composing with the phase-space projections (`ContinuousLinearMap.fst`/`.snd`/`.proj`, via
  `.hasFDerivAt.comp_hasDerivAt`, mirroring `covariantSecondDeriv_expand`), reads off the field's
  third component (`e' = −Γ(x)(ξ,e)`) and first component (`x' = ξ`), and cancels the connection
  term against the transport-equation velocity termwise.

  HONEST CAPTION (binding): this is a single floor of step b3 (frame construction).  It does NOT
  build the orthonormal frame, does NOT discharge the van-Vleck frame data, and does NOT establish
  `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ParallelTransportField
import QIQTH.CovariantJacobi

namespace QIQTH.Geodesic

open QIQTH.Curvature QIQTH.ExpMap
open Finset

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **The parallel-transported vector is parallel along the geodesic.**  For the geodesic +
    parallel-transport integral curve `Γc` (`HasDerivAt Γc (geodesicTransportField g gi (Γc t)) t`,
    from `parallelTransport_local_existence`), with `Γc.1` position, `Γc.2.1` velocity and
    `Γc.2.2 = e` the transported vector, the covariant derivative of `e` along the geodesic
    vanishes:  `D e / dτ = 0`.  This is the `hpar` input of `parallel_orthonormal_preserved`. -/
theorem parallelTransport_covariantDeriv_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (Γc : ℝ → Point n × Point n × Point n) {t : ℝ}
    (hΓc : HasDerivAt Γc (geodesicTransportField g gi (Γc t)) t) :
    covariantDerivAlong g gi (fun s => (Γc s).1) (fun s => (Γc s).2.2) t = 0 := by
  funext i
  rw [covariantDerivAlong_apply]
  -- derivative of the transported vector `e = Γc.2.2` (via `snd ∘ snd ∘ proj`)
  have he : HasDerivAt (fun s => (Γc s).2.2)
      ((geodesicTransportField g gi (Γc t)).2.2) t := by
    have h1 := (ContinuousLinearMap.snd ℝ (Point n) (Point n × Point n)).hasFDerivAt.comp_hasDerivAt t hΓc
    have h2 := (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt t h1
    simpa using h2
  have hec : HasDerivAt (fun s => (Γc s).2.2 i)
      ((geodesicTransportField g gi (Γc t)).2.2 i) t := by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt.comp_hasDerivAt t he
    simpa using this
  -- derivative of the position `x = Γc.1` (via `fst ∘ proj`)
  have hx : HasDerivAt (fun s => (Γc s).1)
      ((geodesicTransportField g gi (Γc t)).1) t := by
    have := (ContinuousLinearMap.fst ℝ (Point n) (Point n × Point n)).hasFDerivAt.comp_hasDerivAt t hΓc
    simpa using this
  have hxc : ∀ j, HasDerivAt (fun s => (Γc s).1 j)
      ((geodesicTransportField g gi (Γc t)).1 j) t := fun j => by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.comp_hasDerivAt t hx
    simpa using this
  -- value of the `e` derivative: the parallel-transport RHS `e' = −Γ(x)(ξ,e)`
  have hval_e : deriv (fun s => (Γc s).2.2 i) t
      = -∑ j, ∑ k, christoffel g gi i j k (Γc t).1 * (Γc t).2.1 j * (Γc t).2.2 k := by
    rw [hec.deriv]; rfl
  -- value of the position derivative: `x' = ξ`
  have hval_x : ∀ j, deriv (fun s => (Γc s).1 j) t = (Γc t).2.1 j := fun j => (hxc j).deriv
  simp only [hval_e, hval_x, Pi.zero_apply]
  ring
