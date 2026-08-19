/-
  GeodesicJointSecondFDerivAtPointLocal — the JOINT SECOND-order Fréchet derivative of the geodesic flow
  at an ARBITRARY doubled base point `Ξ₀`, with the perturbation family quantified only over a BOUNDED
  window `‖Ξ − Ξ₀‖ ≤ σ` around the base point (NOT the whole doubled phase space).

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  WHY THIS FILE EXISTS — the base-point generalization of the joint SECOND Fréchet derivative, and a
  correction to the cp708 vacuity worry.

  `GeodesicJointSecondFDeriv.doubledFlow_endpoint_joint_hasFDerivAt_exists` (plan v4, Task G) built the
  JOINT first-order Fréchet derivative of the DOUBLED (tangent-lifted) flow — equivalently the JOINT
  SECOND-order Fréchet object of the geodesic flow — at the doubled perturbation origin `Ξ = 0`.

  IMPORTANT (correcting the cp708/J4-847 worry): that theorem is ALREADY stated with the perturbation
  family quantified over the BOUNDED window `‖Ξ‖ ≤ σ` (a closed ball), NOT `∀ Ξ` over the whole doubled
  phase space.  Hence it does NOT inherit the J4-847 GLOBAL-`∀ξ` vacuity of the base-level GLOBAL Task A
  (`GeodesicJointFDerivAtPoint`, whose `hmem : ∀ ξ` forced `S = univ`).  With `‖Ξ‖ ≤ σ`, `hmem` at
  `τ = 0` only forces `S ⊇ closedBall (W 0 0) σ`, a bounded ball, on which `doubledField` genuinely IS
  Lipschitz for curved fields.  So the doubled second-order core is SATISFIABLE for curved fields; the
  concrete non-vacuity witness is banked in the companion concrete file.

  WHAT LANDS HERE (axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited):

  * `doubledFlow_endpoint_joint_hasFDerivAt_exists_atPoint` — ★ the base-point-`Ξ₀` version of the joint
    SECOND-order Fréchet derivative.  `hWode`/`hIC`/`hmem` are quantified over `‖Ξ − Ξ₀‖ ≤ σ`, so `S`
    need only contain the bounded window `closedBall (W Ξ₀ 0) σ`.  Delivers
      `∃ L, (∀ Ξ, L Ξ = V Ξ t) ∧ HasFDerivAt (fun Ξ => W Ξ t) L Ξ₀`,
    the JOINT second Fréchet derivative of the geodesic flow at the doubled base state `Ξ₀`
    (which may carry a NONZERO Jacobi seed — exactly the datum the second-order finite-basis transfer
    to `ContDiffOn ℝ 2` needs, per the plan's Task-D route).

  * `doubledFlow_endpoint_joint_snd_hasFDerivAt_exists_atPoint` — the second-variation `.2`-projection
    of the above at the base point `Ξ₀`.

  PROOF: re-instantiate `doubledFlow_endpoint_joint_hasFDerivAt_exists` on the shifted family
  `W̃ η := W (η + Ξ₀)` (reference `W̃ 0 = W Ξ₀`), translating the window `‖η‖ ≤ σ ↔ ‖Ξ − Ξ₀‖ ≤ σ`, then
  compose with the translation `Ξ ↦ Ξ − Ξ₀` (Fréchet derivative `id`, sending `Ξ₀ ↦ 0`) — the exact
  order-up mirror of `GeodesicJointFDerivAtPointLocal.geodesicFlow_joint_hasFDerivAt_exists_atPoint_local`.

  HONEST CHECKPOINT (binding): this is the base-point generalization of the JOINT second-order Fréchet
  derivative with a BOUNDED-WINDOW perturbation scope.  It is still a POINTWISE `HasFDerivAt` (at `Ξ₀`),
  NOT `ContDiffOn ℝ 1` of the doubled flow, NOT the finite-basis transfer, NOT `ContDiffOn ℝ 2` of the
  base flow, NOT the IFT inverse, NOT the RNC discharge, and does NOT bear on `hCConv`.
-/
import Mathlib
import QIQTH.GeodesicJointSecondFDeriv

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **★ Joint SECOND-order Fréchet derivative of the geodesic flow at an ARBITRARY doubled base point
    `Ξ₀`, BOUNDED-WINDOW scope.**  The base-point generalization of
    `GeodesicJointSecondFDeriv.doubledFlow_endpoint_joint_hasFDerivAt_exists`.  `hWode`/`hIC`/`hmem` are
    quantified over `‖Ξ − Ξ₀‖ ≤ σ` (`σ > 0`), so `S` need only contain the bounded window
    `closedBall (W Ξ₀ 0) σ` — genuinely satisfiable for a curved `doubledField` on a compact `S`.  The
    doubled-flow endpoint `fun Ξ => W Ξ t` has joint Fréchet derivative `L` (`L Ξ = V Ξ t`, the doubled
    endpoint Jacobi map) at `Ξ₀`. -/
theorem doubledFlow_endpoint_joint_hasFDerivAt_exists_atPoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n))}
    (Ξ₀ : (Point n × Point n) × (Point n × Point n))
    {S : Set ((Point n × Point n) × (Point n × Point n))} {σ : ℝ}
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S) (hσ : 0 < σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hWode : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ - Ξ₀‖ ≤ σ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W Ξ) (doubledField g gi (W Ξ τ)) τ)
    (hVode : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)),
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (V Ξ) (fderiv ℝ (doubledField g gi) (W Ξ₀ τ) (V Ξ τ)) τ)
    (hV0 : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), V Ξ 0 = Ξ)
    (hIC : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ - Ξ₀‖ ≤ σ →
      W Ξ 0 - W Ξ₀ 0 = Ξ - Ξ₀)
    (hmem : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ - Ξ₀‖ ≤ σ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, W Ξ τ ∈ S) :
    ∃ L : ((Point n × Point n) × (Point n × Point n)) →L[ℝ]
        ((Point n × Point n) × (Point n × Point n)),
      (∀ Ξ : ((Point n × Point n) × (Point n × Point n)), L Ξ = V Ξ t) ∧
        HasFDerivAt (fun Ξ => W Ξ t) L Ξ₀ := by
  -- window translation: `‖η‖ ≤ σ → ‖(η + Ξ₀) - Ξ₀‖ ≤ σ`.
  have hshift : ∀ η : ((Point n × Point n) × (Point n × Point n)), ‖η‖ ≤ σ →
      ‖(η + Ξ₀) - Ξ₀‖ ≤ σ := by
    intro η hη; rwa [add_sub_cancel_right]
  -- re-instantiate the base-`0` doubled second-order core on the shifted family `W̃ η := W (η + Ξ₀)`.
  obtain ⟨L, hLeq, hFD⟩ :=
    doubledFlow_endpoint_joint_hasFDerivAt_exists (W := fun η => W (η + Ξ₀)) (V := V)
      g gi hC hScompact hSconvex hσ ht
      (fun η hη τ hτ => hWode (η + Ξ₀) (hshift η hη) τ hτ)
      (fun η τ hτ => by simpa only [zero_add] using hVode η τ hτ)
      hV0
      (fun η hη => by
        simp only [zero_add]
        rw [hIC (η + Ξ₀) (hshift η hη)]; abel)
      (fun η hη τ hτ => hmem (η + Ξ₀) (hshift η hη) τ hτ)
  -- compose with the translation `Ξ ↦ Ξ − Ξ₀` (derivative `id`, `Ξ₀ ↦ 0`).
  refine ⟨L, hLeq, ?_⟩
  have hsh : HasFDerivAt (fun Ξ : (Point n × Point n) × (Point n × Point n) => Ξ - Ξ₀)
      (ContinuousLinearMap.id ℝ ((Point n × Point n) × (Point n × Point n))) Ξ₀ := by
    simpa using (hasFDerivAt_id Ξ₀).sub_const Ξ₀
  have hg : HasFDerivAt (fun η => W (η + Ξ₀) t) L (Ξ₀ - Ξ₀) := by
    rw [sub_self]; exact hFD
  have hcomp : HasFDerivAt (fun Ξ : (Point n × Point n) × (Point n × Point n) => W (Ξ - Ξ₀ + Ξ₀) t)
      (L.comp (ContinuousLinearMap.id ℝ ((Point n × Point n) × (Point n × Point n)))) Ξ₀ :=
    HasFDerivAt.comp Ξ₀ (g := fun η => W (η + Ξ₀) t)
      (f := fun Ξ : (Point n × Point n) × (Point n × Point n) => Ξ - Ξ₀) hg hsh
  rw [ContinuousLinearMap.comp_id] at hcomp
  have hfun : (fun Ξ : (Point n × Point n) × (Point n × Point n) => W (Ξ - Ξ₀ + Ξ₀) t)
      = fun Ξ => W Ξ t := by
    funext Ξ
    have : Ξ - Ξ₀ + Ξ₀ = Ξ := by abel
    rw [this]
  rw [hfun] at hcomp
  exact hcomp

/-- **Second-variation `.2`-projection of the joint second-order derivative at the base point `Ξ₀`.**
    The `.2` component of the doubled endpoint (the geodesic flow's first-variation / Jacobi field) is,
    JOINTLY in the full doubled perturbation, Fréchet-differentiable at `Ξ₀`, with derivative
    `Ξ ↦ (V Ξ t).2`.  DERIVED by post-composing the joint core with `ContinuousLinearMap.snd`. -/
theorem doubledFlow_endpoint_joint_snd_hasFDerivAt_exists_atPoint
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n))}
    (Ξ₀ : (Point n × Point n) × (Point n × Point n))
    {S : Set ((Point n × Point n) × (Point n × Point n))} {σ : ℝ}
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S) (hσ : 0 < σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hWode : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ - Ξ₀‖ ≤ σ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W Ξ) (doubledField g gi (W Ξ τ)) τ)
    (hVode : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)),
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (V Ξ) (fderiv ℝ (doubledField g gi) (W Ξ₀ τ) (V Ξ τ)) τ)
    (hV0 : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), V Ξ 0 = Ξ)
    (hIC : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ - Ξ₀‖ ≤ σ →
      W Ξ 0 - W Ξ₀ 0 = Ξ - Ξ₀)
    (hmem : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ - Ξ₀‖ ≤ σ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, W Ξ τ ∈ S) :
    ∃ L : ((Point n × Point n) × (Point n × Point n)) →L[ℝ] (Point n × Point n),
      (∀ Ξ : ((Point n × Point n) × (Point n × Point n)), L Ξ = (V Ξ t).2) ∧
        HasFDerivAt (fun Ξ => (W Ξ t).2) L Ξ₀ := by
  obtain ⟨L, hLeq, hFD⟩ := doubledFlow_endpoint_joint_hasFDerivAt_exists_atPoint g gi hC Ξ₀
    hScompact hSconvex hσ ht hWode hVode hV0 hIC hmem
  refine ⟨(ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)).comp L,
    fun Ξ => by simp [hLeq Ξ], ?_⟩
  have := (ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)).hasFDerivAt.comp
    Ξ₀ hFD
  simpa [Function.comp] using this

end QIQTH.ExpMap
