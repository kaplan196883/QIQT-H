/-
  FrameTransportParallel — each COLUMN of the transported frame is PARALLEL along the geodesic.

  Step b3d of the a₁=R/6 endgame.  Given the geodesic + WHOLE-FRAME parallel-transport integral
  curve `Γc : ℝ → Point n × Point n × (Fin n → Point n)` from `parallelFrameTransport_local_existence`
  (i.e. `HasDerivAt Γc (geodesicFrameTransportField g gi (Γc t)) t`), whose components are
  `Γc.1` = position, `Γc.2.1` = velocity and `Γc.2.2 : Fin n → Point n` = the transported FRAME
  `{e_m}`, this file proves that EACH frame column `(Γc·).2.2 m` is genuinely PARALLEL along the
  geodesic: its covariant derivative along the curve vanishes,

    covariantDerivAlong g gi (fun s => (Γc s).1) (fun s => (Γc s).2.2 m) t = 0,

  which is exactly the per-column `hpar` hypothesis consumed by `parallel_orthonormal_preserved`.

  The proof mirrors the single-vector `parallelTransport_covariantDeriv_zero`, adding the frame-index
  projection: it extracts the two coordinate derivatives from the single frame `HasDerivAt` by
  composing with the phase-space projections (`ContinuousLinearMap.fst`/`.snd`/`.proj`, via
  `.hasFDerivAt.comp_hasDerivAt`), now with an extra `proj m` step to pick the `m`-th frame column,
  reads off the field's frame component (`(e_m)' = −Γ(x)(ξ,e_m)`) and first component (`x' = ξ`), and
  cancels the connection term against the transport-equation velocity termwise.

  HONEST CAPTION (binding): this is a single floor of step b3 (frame construction).  It packages the
  per-column parallel-transport data but does NOT build the orthonormal frame, does NOT discharge the
  van-Vleck frame data, and does NOT establish `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FrameTransportField
import QIQTH.CovariantJacobi
import QIQTH.ParallelTransportParallel

namespace QIQTH.Geodesic

open QIQTH.Curvature QIQTH.ExpMap
open Finset

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **Each column of the parallel-transported frame is parallel along the geodesic.**  For the
    geodesic + whole-frame parallel-transport integral curve `Γc`
    (`HasDerivAt Γc (geodesicFrameTransportField g gi (Γc t)) t`, from
    `parallelFrameTransport_local_existence`), with `Γc.1` position, `Γc.2.1` velocity and
    `Γc.2.2 : Fin n → Point n` the transported FRAME `{e_m}`, the covariant derivative of the `m`-th
    frame column `e_m = (Γc·).2.2 m` along the geodesic vanishes:  `D e_m / dτ = 0`.  This is the
    per-column `hpar` input of `parallel_orthonormal_preserved`. -/
theorem frameTransport_covariantDeriv_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (Γc : ℝ → Point n × Point n × (Fin n → Point n)) {t : ℝ}
    (hΓc : HasDerivAt Γc (geodesicFrameTransportField g gi (Γc t)) t) (m : Fin n) :
    covariantDerivAlong g gi (fun s => (Γc s).1) (fun s => (Γc s).2.2 m) t = 0 := by
  funext i
  rw [covariantDerivAlong_apply]
  -- derivative of the transported frame `E = Γc.2.2` (via `snd ∘ snd ∘ proj`)
  have he : HasDerivAt (fun s => (Γc s).2.2)
      ((geodesicFrameTransportField g gi (Γc t)).2.2) t := by
    have h1 := (ContinuousLinearMap.snd ℝ (Point n) (Point n × (Fin n → Point n))).hasFDerivAt.comp_hasDerivAt t hΓc
    have h2 := (ContinuousLinearMap.snd ℝ (Point n) (Fin n → Point n)).hasFDerivAt.comp_hasDerivAt t h1
    simpa using h2
  -- pick the `m`-th frame column (via `proj m`)
  have hem : HasDerivAt (fun s => (Γc s).2.2 m)
      ((geodesicFrameTransportField g gi (Γc t)).2.2 m) t := by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Point n) m).hasFDerivAt.comp_hasDerivAt t he
    simpa using this
  -- pick the `i`-th component of that column (via `proj i`)
  have hec : HasDerivAt (fun s => (Γc s).2.2 m i)
      ((geodesicFrameTransportField g gi (Γc t)).2.2 m i) t := by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt.comp_hasDerivAt t hem
    simpa using this
  -- derivative of the position `x = Γc.1` (via `fst ∘ proj`)
  have hx : HasDerivAt (fun s => (Γc s).1)
      ((geodesicFrameTransportField g gi (Γc t)).1) t := by
    have := (ContinuousLinearMap.fst ℝ (Point n) (Point n × (Fin n → Point n))).hasFDerivAt.comp_hasDerivAt t hΓc
    simpa using this
  have hxc : ∀ j, HasDerivAt (fun s => (Γc s).1 j)
      ((geodesicFrameTransportField g gi (Γc t)).1 j) t := fun j => by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.comp_hasDerivAt t hx
    simpa using this
  -- value of the frame-column derivative: the parallel-transport RHS `(e_m)' = −Γ(x)(ξ,e_m)`
  have hval_e : deriv (fun s => (Γc s).2.2 m i) t
      = -∑ j, ∑ k, christoffel g gi i j k (Γc t).1 * (Γc t).2.1 j * (Γc t).2.2 m k := by
    rw [hec.deriv]; rfl
  -- value of the position derivative: `x' = ξ`
  have hval_x : ∀ j, deriv (fun s => (Γc s).1 j) t = (Γc t).2.1 j := fun j => (hxc j).deriv
  simp only [hval_e, hval_x, Pi.zero_apply]
  ring

end QIQTH.Geodesic
