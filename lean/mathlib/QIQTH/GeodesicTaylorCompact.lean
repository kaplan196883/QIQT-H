/-
  GeodesicTaylorCompact — J3 BRICK 1: the uniform second-order Taylor remainder of the geodesic
  field on a convex COMPACT set, with the second-derivative bound OBTAINED BY COMPACTNESS.

  ODE_VARIATIONAL_PLAN.md / WHITENED_CAMPAIGN_TERMINAL.md §5.  `GeodesicSmoothDep.lean` proved the
  uniform C² Taylor remainder `geodesicField_uniform_C2_remainder`, but it CARRIES the
  second-derivative sup bound as an explicit hypothesis
      `hbound2 : ∀ x ∈ S, ‖∂²F x‖ ≤ M₂`.
  Its own honest checkpoint flags the missing structural piece: the constant `M₂` is not yet
  produced — it must come from the compactness of the region, not be assumed.  This file closes that
  gap: the geodesic field `F = geodesicField g gi` is `C^∞` (`contDiff_geodesicField`), so its second
  Fréchet derivative `∂²F = fderiv ℝ (fderiv ℝ F)` is CONTINUOUS; on a compact `S` its norm is
  bounded (`IsCompact.exists_bound_of_continuousOn`).  Feeding that derived bound in gives:

  * `geodesicField_fderiv_lipschitzOnWith` — brick (1): on a convex compact `S`, `DF = fderiv ℝ F`
    is Lipschitz there, the Lipschitz constant EXISTENTIALLY produced from the (compactness-derived)
    sup of `‖∂²F‖` — NOT a carried number.  (`lipschitzOnWith_of_nnnorm_fderiv_le` = the mean-value
    inequality for `DF`, whose derivative is `∂²F`.)

  * `geodesicField_taylor_remainder_uniform` — brick (2), ★ THE FLAGGED LEMMA: on a convex compact
    `S`, `∃ M ≥ 0, ∀ a b ∈ S, ‖F a − F b − DF(b)(a−b)‖ ≤ M·‖a−b‖²`, with `M` obtained by compactness.
    This is the second-order (quadratic) uniform remainder with NO carried second-derivative bound —
    the exact structural gap `GeodesicSmoothDep`'s checkpoint named.

  Both are axiom-clean (std-3), no `sorry`, no new axioms.  The convex-compact hypotheses are
  honestly stated and satisfiable — any closed ball `Metric.closedBall c r` in the state space is
  convex and compact (finite-dimensional), witnessing the region of the curved tube.

  HONEST FIREWALL: this is J3 REGULARITY infrastructure — it removes the carried `hbound2` from the
  second-order Taylor remainder.  It is NOT the heat-kernel coefficient `a₁ = R/6` (which remains a
  labelled carrier); it does NOT build the second-order Jacobi equation (L2), Raychaudhuri (L3), or
  numerical `G`.
-/
import Mathlib
import QIQTH.ExpMap
import QIQTH.GeodesicSmoothDep

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic

variable {n : ℕ}

/-- **The geodesic field's second Fréchet derivative is bounded on a compact set (constant produced by
    compactness).**  `F = geodesicField g gi` is `C^∞`, so its 2nd iterated Fréchet derivative
    `iteratedFDeriv ℝ 2 F` is continuous (`ContDiff.continuous_iteratedFDeriv`) into the clean
    continuous-multilinear-map norm space; on a compact `S` its norm attains a finite bound
    (`IsCompact.bddAbove_image`).  Transporting through the isometry
    `‖fderiv ℝ (fderiv ℝ F) x‖ = ‖iteratedFDeriv ℝ 2 F x‖` (`norm_iteratedFDeriv_one` +
    `norm_iteratedFDeriv_fderiv`, avoiding the nested-CLM strong-vs-norm topology diamond) gives a
    finite `M ≥ 0` bounding the second Fréchet derivative on `S`.  This is the compactness engine both
    bricks share. -/
theorem geodesicField_snd_fderiv_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hcomp : IsCompact S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M := by
  set F := geodesicField g gi with hFdef
  have hiter : Continuous (iteratedFDeriv ℝ 2 F) :=
    (contDiff_geodesicField g gi hC).continuous_iteratedFDeriv (by simp)
  obtain ⟨M, hM⟩ := hcomp.bddAbove_image hiter.norm.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  have heq : ‖fderiv ℝ (fderiv ℝ F) x‖ = ‖iteratedFDeriv ℝ 2 F x‖ := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ F), norm_iteratedFDeriv_fderiv]
  rw [heq]
  exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)

/-- **J3 brick (1) — `DF = fderiv ℝ F` is Lipschitz on a convex compact set, constant obtained by
    compactness.**  The geodesic field `F = geodesicField g gi` is `C^∞`, so its first Fréchet
    derivative `DF` is itself `C^∞`, hence its own derivative `∂²F = fderiv ℝ (fderiv ℝ F)` is
    CONTINUOUS.  On a compact `S`, `‖∂²F‖` attains a finite sup `C` (`IsCompact.exists_bound_of_
    continuousOn`); the mean-value inequality (`lipschitzOnWith_of_nnnorm_fderiv_le`, using
    convexity of `S`) then makes `DF` Lipschitz on `S` with constant `C.toNNReal`.

    The Lipschitz constant is EXISTENTIALLY produced from the compactness-derived sup — NOT a carried
    or computed number.  This is the two-point gradient bound the second-order Taylor remainder
    integrates. -/
theorem geodesicField_fderiv_lipschitzOnWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hconv : Convex ℝ S) (hcomp : IsCompact S) :
    ∃ C : NNReal, LipschitzOnWith C (fderiv ℝ (geodesicField g gi)) S := by
  set F := geodesicField g gi with hFdef
  -- `DF = fderiv ℝ F` is C^∞, hence differentiable.
  have hDFdiff : Differentiable ℝ (fderiv ℝ F) :=
    ((contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top).differentiable (by simp)
  -- the second-derivative sup bound OBTAINED BY COMPACTNESS.
  obtain ⟨M, hM0, hMbound⟩ := geodesicField_snd_fderiv_bddOn_compact g gi hC hcomp
  refine ⟨Real.toNNReal M, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hDFdiff x) (fun x hx => ?_) hconv
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M hM0]
  exact hMbound x hx

/-- **J3 brick (2), ★ THE FLAGGED LEMMA — the uniform second-order Taylor remainder of the geodesic
    field on a convex compact set, `M` obtained by compactness.**  On a convex compact
    `S ⊆ Point n × Point n`,
        `∃ M ≥ 0, ∀ a b ∈ S, ‖F a − F b − DF(b)(a − b)‖ ≤ M·‖a − b‖²`,
    where `F = geodesicField g gi` and `DF = fderiv ℝ F`.

    This is exactly the lemma flagged as THE structural gap in `GeodesicSmoothDep`'s honest
    checkpoint: the second-order (quadratic) uniform Taylor remainder with NO carried second-
    derivative bound.  `F` is `C^∞`, so `∂²F` is continuous and bounded on the compact `S` by some
    `M` (`IsCompact.exists_bound_of_continuousOn`); feeding that derived bound into the carried-`hbound2`
    remainder `geodesicField_uniform_C2_remainder` discharges the last hypothesis, producing the
    quadratic bound with `M` PRODUCED (not assumed).

    HONEST: the constant is the crude iterated-MVT `M` (not the sharp `M/2`).  Convexity + compactness
    of `S` are honestly stated and satisfiable (any `Metric.closedBall` in the finite-dimensional state
    space qualifies).  This is J3 regularity only — NOT `a₁ = R/6`. -/
theorem geodesicField_taylor_remainder_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hconv : Convex ℝ S) (hcomp : IsCompact S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ S, ∀ b ∈ S,
      ‖geodesicField g gi a - geodesicField g gi b
          - fderiv ℝ (geodesicField g gi) b (a - b)‖ ≤ M * ‖a - b‖ ^ 2 := by
  -- `∂²F` continuous (F is C^∞) ⟹ bounded on the compact `S` (constant produced by compactness).
  obtain ⟨M, hM0, hMbound⟩ := geodesicField_snd_fderiv_bddOn_compact g gi hC hcomp
  refine ⟨M, hM0, fun a ha b hb => ?_⟩
  exact geodesicField_uniform_C2_remainder g gi hC hconv hMbound ha hb

/-- **Witness: a closed ball is a valid convex compact region.**  The convex-compact hypotheses of
    the two bricks are satisfiable at the curved witness — any closed ball `Metric.closedBall c r` in
    the finite-dimensional state space `Point n × Point n` is both convex and compact, so the
    second-order remainder holds there with a compactness-produced constant. -/
theorem geodesicField_taylor_remainder_uniform_closedBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (c : Point n × Point n) (r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ Metric.closedBall c r, ∀ b ∈ Metric.closedBall c r,
      ‖geodesicField g gi a - geodesicField g gi b
          - fderiv ℝ (geodesicField g gi) b (a - b)‖ ≤ M * ‖a - b‖ ^ 2 :=
  geodesicField_taylor_remainder_uniform g gi hC (convex_closedBall c r) (isCompact_closedBall c r)

end QIQTH.ExpMap
