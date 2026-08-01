/-
# Brick-A(β) J4-62 — the FIRST uniform-over-`K` bound for the uniform-flow exp endpoint.

SCOPE (see the J4-62 report).  Piece (I) of Brick-A — uniform-over-`K` regularity/bounds of
`uniformFlowExp` and its pullback metric `uniformFlowPullbackMetric` — is a LARGE higher-order
joint-smooth-dependence sub-tower: the `expMap` residual chain consumes the pullback metric at
`ContDiffOn ℝ 3` (`contDiffOn_expPullbackMetric_three_uncond`), which is fed by the THIRD jet of
`exp` (`expMap_fderiv3_contDiffOn_one`, from `exp ∈ C⁴`).  Mirroring that for the uniform flow needs
`uniformFlowExp ∈ C⁴` JOINTLY in `(q, v)` — re-running the jet-4 + higher-variational program for the
base-point-dependent uniform tube.  Only the FIRST jet (`uniformFlowExp_hasFDerivAt`, J4-55, `C¹`) is
available.

This file lands the most-foundational rung that needs NONE of that higher regularity: the uniform
CONFINEMENT bound on the endpoint DISPLACEMENT.  It is the `C⁰`-level bounded-geometry base of the
uniform-bound layer — it certifies that, over all `q ∈ K` and `‖v‖ ≤ ρ_K`, the endpoint
`uniformFlowExp_q v` stays in a fixed compact neighbourhood of `q` (radius `C₀·ρ_K`), which is what
makes the `g`-factor `g(uniformFlowExp_q v)` of the pullback metric uniformly bounded.  It uses ONLY
the K1 uniform-tube confinement spec `uniformFlowTube_spec_conf` (a genuine geodesic-tube datum), the
uniform radius `ρ_K` and constant `C₀` — no `expRho`, no higher jets, no carried conclusion.

⚠ HONEST SCOPE.  This is a displacement bound, NOT a bound on `fderiv (uniformFlowExp q)` or on the
pullback metric (those need joint continuity of the derivative — part of the sub-tower).  No `sorry`,
no new axioms, no vacuous hypotheses, no smuggled bound.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowNondeg
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic

variable {n : ℕ}

set_option maxHeartbeats 400000

/-- **J4-62 — the uniform endpoint-displacement bound for `uniformFlowExp` over `K`.**

    There is a single `M = C₀·ρ_K ≥ 0` such that for every base point `q ∈ K` and every initial
    velocity `v` with `‖v‖ ≤ ρ_K` (`ρ_K = uniformFlowRadius`), the uniform-flow exp endpoint stays
    within `M` of `q`:
        `‖uniformFlowExp g gi hC hK q v - q‖ ≤ M`.

    Derived from the K1 uniform-tube confinement spec `uniformFlowTube_spec_conf`
    (`‖tube t - (q,0)‖ ≤ C₀·‖v‖` on `[0,1]`) at `t = 1`, projected onto the position component, then
    `‖v‖ ≤ ρ_K`.  Uses NO higher regularity of `uniformFlowExp` (only the `C⁰` tube confinement) and NO
    `expRho`.  This is the bounded-geometry base rung of Brick-A piece (I): it bounds the region where
    the ambient metric `g` is sampled inside `g̃ = uniformFlowPullbackMetric`. -/
theorem uniformFlowExp_displacement_uniform_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K, ∀ v : Point n,
      ‖v‖ ≤ uniformFlowRadius g gi hC hK →
      ‖uniformFlowExp g gi hC hK q v - q‖ ≤ M := by
  refine ⟨uniformFlowConst g gi hC hK * uniformFlowRadius g gi hC hK,
    mul_nonneg (uniformFlowConst_nonneg g gi hC hK) (uniformFlowRadius_pos g gi hC hK).le, ?_⟩
  intro q hq v hv
  -- confinement of the uniform tube at `t = 1`.
  have hconf : ‖uniformFlowTube g gi hC hK q v 1 - ((q, 0) : Point n × Point n)‖
      ≤ uniformFlowConst g gi hC hK * ‖v‖ :=
    uniformFlowTube_spec_conf g gi hC hK q hq v hv 1
      (Set.mem_Icc.mpr ⟨zero_le_one, le_refl _⟩)
  -- project onto the position component.
  have hfst : (uniformFlowTube g gi hC hK q v 1).1 - q
      = (uniformFlowTube g gi hC hK q v 1 - ((q, 0) : Point n × Point n)).1 := by
    rw [Prod.fst_sub]
  have hproj : ‖(uniformFlowTube g gi hC hK q v 1).1 - q‖
      ≤ ‖uniformFlowTube g gi hC hK q v 1 - ((q, 0) : Point n × Point n)‖ := by
    rw [hfst, Prod.norm_def]; exact le_max_left _ _
  calc ‖uniformFlowExp g gi hC hK q v - q‖
      = ‖(uniformFlowTube g gi hC hK q v 1).1 - q‖ := by rw [uniformFlowExp_eq]
    _ ≤ ‖uniformFlowTube g gi hC hK q v 1 - ((q, 0) : Point n × Point n)‖ := hproj
    _ ≤ uniformFlowConst g gi hC hK * ‖v‖ := hconf
    _ ≤ uniformFlowConst g gi hC hK * uniformFlowRadius g gi hC hK :=
        mul_le_mul_of_nonneg_left hv (uniformFlowConst_nonneg g gi hC hK)

end QIQTH.ExpMap
