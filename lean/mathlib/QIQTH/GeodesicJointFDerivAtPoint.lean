/-
  GeodesicJointFDerivAtPoint — the JOINT (base + velocity) FULL-PHASE-SPACE Fréchet derivative of the
  geodesic flow at an ARBITRARY base point `ξ₀`, generalizing
  `QIQTH.ExpMap.geodesicFlow_joint_hasFDerivAt_exists` (`GeodesicBasepointFrechet.lean`) from the single
  perturbation origin `ξ = 0` to any `ξ₀ : Point n × Point n`.

  MOTIVATION (plan `tranquil-stargazing-fox.md`, Task A).
  `geodesicFlow_joint_hasFDerivAt_exists` proves the joint first-order Fréchet derivative of the geodesic
  flow endpoint `fun ξ => W ξ t` — but ONLY at `ξ = 0`, a single pointwise fact.  The neighborhood-quality
  `ContDiffAt`/`ContDiffOn` upgrade (Tasks B/C of the plan) needs the derivative to EXIST at every point in
  a neighborhood of `0`, not just at `0`.  This file supplies the first ingredient: the same derivative,
  based at an arbitrary `ξ₀`.

  METHOD — coordinate-translation, NOT re-derivation.
  The original theorem is entirely ABSTRACT in the geodesic family `W`, the Jacobi solutions `V`, and the
  containing convex set `S`: it never uses that the perturbation origin is literally `0` beyond it being the
  index of the REFERENCE curve `W 0` along which the supplied Jacobi fields live.  The origin `0` is therefore
  a convenience, not a special algebraic value.  We re-instantiate the original with the SHIFTED family
  `W̃ η := W (η + ξ₀)` (so `η = 0` now indexes the reference curve `W ξ₀`) and Jacobi solutions `V` supplied
  along `W ξ₀`, obtaining `HasFDerivAt (fun η => W (η + ξ₀) t) L 0`, then compose with the translation
  `ξ ↦ ξ - ξ₀` (an isometric affine map, Fréchet derivative `id`, sending `ξ₀ ↦ 0`) via `HasFDerivAt.comp`
  to land `HasFDerivAt (fun ξ => W ξ t) L ξ₀`.  The geodesic ODE's lack of translation-invariance
  (position-dependent Christoffel symbols) is a NON-ISSUE here: the Jacobi fields along `W ξ₀` are SUPPLIED
  as hypotheses (exactly as the original supplies those along `W 0`), never obtained by naively translating
  the fields along `W 0`.

  WHAT LANDS HERE (axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited):

  * `geodesicFlow_joint_hasFDerivAt_exists_atPoint` — for the joint geodesic family `W`, an arbitrary base
    point `ξ₀`, and Jacobi solutions `V` along the reference geodesic `W ξ₀` (`V ξ 0 = ξ`), the endpoint
    `fun ξ => W ξ t` has a joint Fréchet derivative `L` at `ξ₀`, with `L ξ = V ξ t`:
    `∃ L, (∀ ξ, L ξ = V ξ t) ∧ HasFDerivAt (fun ξ => W ξ t) L ξ₀`.

  HONEST CHECKPOINT (binding): this is the base-point generalization of the JOINT first-order Fréchet
  derivative — nothing more.  `ξ₀` is arbitrary at the abstract level precisely because the validity data
  (Jacobi solutions along `W ξ₀`, the coefficient bound `K` along `W ξ₀`, tube containment) are SUPPLIED as
  hypotheses; a later neighborhood/compactness restriction on `ξ₀` will appear only when these hypotheses are
  discharged for the concrete `uniformFlowExp` (plan Tasks B/C).  It does NOT upgrade to `ContDiffAt`/
  `ContDiffOn`, NOT wire to `uniformFlowExp`, NOT build the second-order jet, and does NOT by itself
  discharge `hCConv`.
-/
import Mathlib
import QIQTH.GeodesicBasepointFrechet

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 400000

variable {n : ℕ}

/-- **Joint (base + velocity) Fréchet derivative of the geodesic flow at an ARBITRARY base point `ξ₀`.**
    The base-point generalization of `geodesicFlow_joint_hasFDerivAt_exists` (which is the `ξ₀ = 0` case).
    `V ξ` are Jacobi solutions along the reference geodesic `W ξ₀` seeded at `ξ` (`V ξ 0 = ξ`); `W ξ` are the
    perturbed geodesics with initial displacement `W ξ 0 - W ξ₀ 0 = ξ - ξ₀` from the reference.  The endpoint
    `fun ξ => W ξ t` has joint Fréchet derivative `L` (with `L ξ = V ξ t`) at `ξ₀`.

    PROOF: re-instantiate `geodesicFlow_joint_hasFDerivAt_exists` on the shifted family `W̃ η := W (η + ξ₀)`
    (its reference `W̃ 0 = W ξ₀`), then compose with the translation `ξ ↦ ξ - ξ₀` (Fréchet derivative `id`,
    sending `ξ₀ ↦ 0`). -/
theorem geodesicFlow_joint_hasFDerivAt_exists_atPoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n × Point n → ℝ → Point n × Point n}
    (ξ₀ : Point n × Point n)
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W ξ) (geodesicField g gi (W ξ τ)) τ)
    (hVode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V ξ) (fderiv ℝ (geodesicField g gi) (W ξ₀ τ) (V ξ τ)) τ)
    (hV0 : ∀ ξ : Point n × Point n, V ξ 0 = ξ)
    (hIC : ∀ ξ : Point n × Point n, W ξ 0 - W ξ₀ 0 = ξ - ξ₀)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W ξ₀ τ)‖ ≤ K)
    (hmem : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W ξ τ ∈ S) :
    ∃ L : (Point n × Point n) →L[ℝ] Point n × Point n,
      (∀ ξ : Point n × Point n, L ξ = V ξ t) ∧ HasFDerivAt (fun ξ => W ξ t) L ξ₀ := by
  -- Re-instantiate the `ξ = 0` theorem on the shifted family `W̃ η := W (η + ξ₀)`, reference `W̃ 0 = W ξ₀`.
  obtain ⟨L, hLeq, hFD⟩ :=
    geodesicFlow_joint_hasFDerivAt_exists (W := fun η => W (η + ξ₀)) (V := V)
      g gi hC hK0 ht hconv hbound2 hLip
      (fun η τ hτ => hWode (η + ξ₀) τ hτ)
      (fun η τ hτ => by simpa only [zero_add] using hVode η τ hτ)
      hV0
      (fun η => by
        simp only [zero_add]
        rw [hIC (η + ξ₀)]; abel)
      (fun τ hτ => by simpa only [zero_add] using hKb τ hτ)
      (fun η τ hτ => hmem (η + ξ₀) τ hτ)
  -- Compose with the translation `ξ ↦ ξ - ξ₀` (derivative `id`, `ξ₀ ↦ 0`).
  refine ⟨L, hLeq, ?_⟩
  have hsh : HasFDerivAt (fun ξ : Point n × Point n => ξ - ξ₀)
      (ContinuousLinearMap.id ℝ (Point n × Point n)) ξ₀ := by
    simpa using (hasFDerivAt_id ξ₀).sub_const ξ₀
  have hg : HasFDerivAt (fun η => W (η + ξ₀) t) L (ξ₀ - ξ₀) := by
    rw [sub_self]; exact hFD
  have hcomp : HasFDerivAt (fun ξ : Point n × Point n => W (ξ - ξ₀ + ξ₀) t)
      (L.comp (ContinuousLinearMap.id ℝ (Point n × Point n))) ξ₀ :=
    HasFDerivAt.comp ξ₀ (g := fun η => W (η + ξ₀) t)
      (f := fun ξ : Point n × Point n => ξ - ξ₀) hg hsh
  rw [ContinuousLinearMap.comp_id] at hcomp
  have hfun : (fun ξ : Point n × Point n => W (ξ - ξ₀ + ξ₀) t) = fun ξ => W ξ t := by
    funext ξ
    have : ξ - ξ₀ + ξ₀ = ξ := by abel
    rw [this]
  rw [hfun] at hcomp
  exact hcomp

end QIQTH.ExpMap
