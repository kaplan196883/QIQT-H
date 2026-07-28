/-
  FrameCovariantDeriv — the FRAME covariant derivative (M2b-3a of the off-radial
  matrix-Jacobi campaign, `docs/qg_roadmap/MATRIX_JACOBI_PLAN.md`).

  CONTENT.  Expand a vector field in a *moving frame* `{e_i}` with scalar components `Y_i : ℝ→ℝ`,
    `ξ(s) := fun a => ∑ i, Y i s · e i s a`.
  If each frame vector `e_i` is PARALLEL along the curve `γ`
  (`covariantDerivAlong g gi γ (e i) τ = 0` — carried as the hypothesis `hpar`), then the covariant
  derivative acts as the *ordinary* derivative on the scalar components:
      `covariantDerivAlong g gi γ ξ τ = fun a => ∑ i, (deriv (Y i) τ) · e i τ a`   (`#1`)
  and, iterating,
      `covariantSecondDeriv g gi γ ξ τ = fun a => ∑ i, (deriv (deriv (Y i)) τ) · e i τ a`   (`#2`).

  REASON.  Expanding `ξ_a = ∑_i Y_i e_i^a`, the ordinary `deriv` splits (Leibniz) into
  `∑_i (deriv Y_i) e_i^a + ∑_i Y_i (deriv e_i^a)`; the connection term regroups per-`i` and combines
  with `deriv e_i^a` into exactly `(covariantDerivAlong (e_i))_a`, which is `0` by parallelism, leaving
  `∑_i (deriv Y_i) e_i^a`.

  WHERE THIS FITS.  Combined with the off-center covariant Jacobi equation (`covariant_jacobi_equation`,
  `CovariantJacobiOffCenter.lean`) and frame orthonormality, `#1`/`#2` will project the vector Jacobi
  equation onto the parallel frame, yielding the clean scalar/matrix form `Ỹ'' = −R̃ Ỹ` — that
  projection is the NEXT brick (M2b-5) and is NOT done here.

  HONEST SCOPE.  This file does NOT build the existence of a parallel frame (M2b-2); the parallelism of
  each `e_i` is CARRIED as the hypothesis `hpar`.  It does NOT do the projection to `Ỹ''=−R̃Ỹ` (M2b-5),
  and it is unrelated to the heat-kernel coefficient `a₁=R/6` (M6).  All regularity inputs (`HasDerivAt`
  of the components `Y_i` and of the frame components `e_i^a`) are carried as genuine, labelled
  hypotheses; none assume the conclusion.
-/
import Mathlib
import QIQTH.CovariantJacobi

namespace QIQTH.ExpMap

open QIQTH.Curvature
open Finset

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **Reorder a triple `Finset.univ` sum** from nesting order `j,k,i` to `i,j,k`.  Pure finite
    reindexing (two applications of `Finset.sum_comm`); no analysis. -/
private lemma sum_reorder_jki_to_ijk (F : Fin n → Fin n → Fin n → ℝ) :
    (∑ j, ∑ k, ∑ i, F i j k) = ∑ i, ∑ j, ∑ k, F i j k := by
  rw [show (∑ j, ∑ k, ∑ i, F i j k) = ∑ j, ∑ i, ∑ k, F i j k from
    Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

/-! ### #1 — the frame covariant derivative acts as the ordinary derivative on components -/

/-- **Frame covariant derivative (`#1`).**  For a field `ξ(s) = fun a => ∑ i, Y i s · e i s a` expanded
    in a PARALLEL moving frame `{e_i}` (`hpar`), the covariant derivative along `γ` acts as the ordinary
    componentwise derivative:
      `covariantDerivAlong g gi γ ξ τ = fun a => ∑ i, (deriv (Y i) τ) · e i τ a`.
    The connection term of `ξ` regroups per-`i` and, with `deriv e_i^a`, assembles exactly into
    `(covariantDerivAlong (e_i))_a = 0`, leaving only the `deriv Y_i` terms. -/
theorem covariantDerivAlong_frame_combo
    (g gi : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (Y : Fin n → ℝ → ℝ)
    (hY : ∀ i, ∀ τ, HasDerivAt (Y i) (deriv (Y i) τ) τ)
    (he : ∀ i a, ∀ τ, HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, ∀ τ, covariantDerivAlong g gi γ (e i) τ = 0)
    (τ : ℝ) :
    covariantDerivAlong g gi γ (fun s => fun a => ∑ i, Y i s * e i s a) τ
      = fun a => ∑ i, deriv (Y i) τ * e i τ a := by
  funext a
  rw [covariantDerivAlong_apply]
  show deriv (fun s => ∑ i, Y i s * e i s a) τ
        + ∑ j, ∑ k, christoffel g gi a j k (γ τ) * deriv (fun s => γ s j) τ
            * ∑ i, Y i τ * e i τ k
      = ∑ i, deriv (Y i) τ * e i τ a
  -- Leibniz derivative of the field component `a`.
  have hΞ : HasDerivAt (fun s => ∑ i, Y i s * e i s a)
      (∑ i, (deriv (Y i) τ * e i τ a + Y i τ * deriv (fun s => e i s a) τ)) τ := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hY i τ).mul (he i a τ)
  rw [hΞ.deriv]
  -- regroup the connection double-sum by pulling out the frame index `i`.
  have hcomm :
      (∑ j, ∑ k, christoffel g gi a j k (γ τ) * deriv (fun s => γ s j) τ * ∑ i, Y i τ * e i τ k)
      = ∑ i, Y i τ *
          ∑ j, ∑ k, christoffel g gi a j k (γ τ) * deriv (fun s => γ s j) τ * e i τ k := by
    simp only [Finset.mul_sum]
    rw [sum_reorder_jki_to_ijk]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => by ring)))
  rw [hcomm]
  -- parallelism: `deriv e_i^a + (connection sum)_i = (covariantDerivAlong (e_i))_a = 0`.
  have hp : ∀ i, deriv (fun s => e i s a) τ
      + ∑ j, ∑ k, christoffel g gi a j k (γ τ) * deriv (fun s => γ s j) τ * e i τ k = 0 := by
    intro i
    have h := congrFun (hpar i τ) a
    rwa [covariantDerivAlong_apply, Pi.zero_apply] at h
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hpi := hp i
  linear_combination (Y i τ) * hpi

/-! ### #2 — the frame covariant SECOND derivative -/

/-- **Frame covariant second derivative (`#2`).**  Iterating `#1`: the inner covariant derivative is
    itself a frame combination with components `deriv (Y i)`, so
      `covariantSecondDeriv g gi γ ξ τ = fun a => ∑ i, (deriv (deriv (Y i)) τ) · e i τ a`.
    Needs, additionally, the second-derivative regularity `hY2` of the components. -/
theorem covariantSecondDeriv_frame_combo
    (g gi : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (Y : Fin n → ℝ → ℝ)
    (hY : ∀ i, ∀ τ, HasDerivAt (Y i) (deriv (Y i) τ) τ)
    (hY2 : ∀ i, ∀ τ, HasDerivAt (deriv (Y i)) (deriv (deriv (Y i)) τ) τ)
    (he : ∀ i a, ∀ τ, HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, ∀ τ, covariantDerivAlong g gi γ (e i) τ = 0)
    (τ : ℝ) :
    covariantSecondDeriv g gi γ (fun s => fun a => ∑ i, Y i s * e i s a) τ
      = fun a => ∑ i, deriv (deriv (Y i)) τ * e i τ a := by
  -- inner covariant derivative, as a function of `s`, is the frame combo with components `deriv (Y i)`.
  have hinner : covariantDerivAlong g gi γ (fun s => fun a => ∑ i, Y i s * e i s a)
      = fun s => fun a => ∑ i, deriv (Y i) s * e i s a := by
    funext s
    exact covariantDerivAlong_frame_combo g gi γ e Y hY he hpar s
  unfold covariantSecondDeriv
  rw [hinner]
  exact covariantDerivAlong_frame_combo g gi γ e (fun i => deriv (Y i)) hY2 he hpar τ

end QIQTH.ExpMap
