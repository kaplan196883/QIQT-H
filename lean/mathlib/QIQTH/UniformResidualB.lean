/-
  UniformResidualB — J4-80 (hunif UNIFORM-B ASSEMBLER, forward-metric packet): the uniform-over-`K`
  geometric constant packet for the `uniformFlowExp` pullback metric `g̃`, welding the Brick-A(β)
  uniform packet into a single per-`q` deliverable.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## Context — the hunif chain and where this sits.

  The single remaining input to the `a₁ = R/6` capstone (`TrueKernelA1Reduced`) is the GLOBAL width-2
  residual bound `hEboundW`, which `RecenterReduction.hEboundW_of_uniform_perBasePoint` reduces to a
  per-base-point Gaussian family with a SINGLE constant `B`, uniform over the base point `q ∈ K`.  The
  per-`q` cutoff-residual bound (`RecenterCutoffC3.cutoffResidual_expPullback_hEboundW`) consumes a list
  of PULLBACK-METRIC geometric constants; the missing ingredient has always been UNIFORM-OVER-`K`
  versions of those constants.  Brick-A(β) (`uniformFlowExp` + `uniformFlowPullbackMetric`) now supplies
  the uniform-radius geometry needed to produce them.

  ## What this file DELIVERS (green, DERIVED; no `sorry`, no new axioms, no `expRho`).

  `uniformResidual_forwardMetric_packet` — from `hg` (metric regularity) + `hC` (Christoffel `C^∞`) +
  `IsCompact K` + the genuine base-metric nondegeneracy `hgnd` at the flow endpoints, produces ONE common
  radius `r₀ > 0` and ONE constant `M ≥ 0` such that, for every `q ∈ K` and `‖v‖ < r₀`, uniformly in the
  entry indices `i j`:
    * the FORWARD pullback-metric entry `g̃_{ij}` has uniform `C⁰`/`C¹`/`C²` operator-norm bounds
      `|g̃_{ij}(v)| ≤ M`, `‖D g̃_{ij}(v)‖ ≤ M`, `‖D(D g̃_{ij})(v)‖ ≤ M`
      (from `uniformFlowPullbackMetric_c2_uniform_full`, Brick-A(β) W4 capstone);
    * the flow Jacobian is invertible, `IsUnit (fderiv (uniformFlowExp g gi hC hK q) v)`
      (from `uniformFlowExp_common_nondeg_radius`, the compact-uniform (J) gate);
    * the pullback metric is nondegenerate, `IsUnit (matToCLM g̃(v))`
      (from the hinge `uniformFlowPullbackMetric_isUnit_of_fderiv_isUnit`, i.e. the congruence
      `g̃ = Jᵀ·(g∘F)·J` of units is a unit).

  This is exactly the uniform FORWARD-metric + NONDEGENERACY layer that a `uniformFlowExp`-based residual
  chain would consume.  Hypotheses are ONLY `hg`, `hC`, `IsCompact K`, and `hgnd` — the latter is a
  GENUINE geometric input (the base metric is nondegenerate at the geodesic-flow endpoints), NOT the
  conclusion, and is satisfiable (the flat metric `g = δ` gives `matToCLM δ = 1`, a unit everywhere).

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## ⚠ FIREWALL (binding, honest) — the uniform INVERSE-metric bounds are NOT delivered here.

  The per-`q` residual consumer `cutoffResidual_expPullback_hEboundW` carries its metric-side residue
  ALMOST ENTIRELY on the INVERSE metric `g̃⁻¹` (annulus bound `hgi_ann`, `Δ_g̃χ` bound `hLapChi_ann`,
  deviation `hdev`, inverse identity `hinvT`, symmetry `hgisymm`).  The genuinely missing uniform-over-`K`
  ingredient is therefore a UNIFORM bound on the `g̃⁻¹` entries:

    MISSING:  `∃ r₀>0, ∃ Kinv, ∀ q∈K, ∀ ‖v‖<r₀,
                 ‖Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b))‖ ≤ Kinv`
              (whence entrywise `|g̃⁻¹(v) i j| ≤ Kinv`).

  This packet proves `IsUnit (matToCLM g̃)` uniformly (so `g̃⁻¹` is well-defined uniformly) but NOT a
  uniform NORM bound on the inverse.  Both standard routes are blocked on missing infrastructure:

    (Route A — continuity/compactness)  `(q,v) ↦ Ring.inverse (matToCLM g̃(q,v))` is continuous where
      `g̃` is a unit, hence bounded on the compact parameter set `K ×ˢ closedBall 0 r₀` — BUT this needs
      JOINT continuity of `(q,v) ↦ uniformFlowExp q v` and `(q,v) ↦ fderiv (uniformFlowExp q) v` in the
      base point `q`.  The Brick-A packet establishes only per-`q` (in `v`) continuity/differentiability;
      NO joint-in-`q` continuity brick for `uniformFlowExp`/its `fderiv` exists in the repo.

    (Route B — congruence factorization)  `‖g̃⁻¹‖ ≤ ‖J⁻¹‖²·‖(g∘F)⁻¹‖` with `‖J⁻¹‖ ≤ 2` from the Neumann
      near-identity bound `‖fderiv − id‖ ≤ C_D·‖v‖ < 1` — BUT `uniformFlowExp_common_nondeg_radius`
      DISCARDS the constant `C_D` (returns only `IsUnit`, not the norm bound), so recovering `‖J⁻¹‖ ≤ 2`
      requires re-deriving that file's Grönwall/Neumann tail; and `‖(g∘F)⁻¹‖` needs a uniform base-metric
      inverse bound on the endpoint tube.  Not reachable in this pass.

  This file does NOT prove `hEboundW`, does NOT deliver the uniform `g̃⁻¹` bounds, and is NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import QIQTH.UniformFlowMetricC2Bound
import QIQTH.UniformFlowNondegClose
import QIQTH.UniformFlowPullback
import Mathlib

open QIQTH.Curvature QIQTH.PullbackMetric
open scoped Topology BigOperators

namespace QIQTH.ExpMap

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ J4-80 — the uniform-over-`K` FORWARD-metric + NONDEGENERACY packet for `uniformFlowExp`.**

    From `hg` (ambient-metric regularity), `hC` (Christoffel `C^∞`), `IsCompact K`, and the GENUINE
    base-metric nondegeneracy `hgnd` at the geodesic-flow endpoints, there is ONE common radius `r₀ > 0`
    and ONE constant `M ≥ 0` such that for every base point `q ∈ K`, velocity `‖v‖ < r₀`, and indices
    `i j`:
    * uniform `C⁰`/`C¹`/`C²` bounds on the forward pullback-metric entry
      `|g̃_{ij}(v)| ≤ M`, `‖D g̃_{ij}(v)‖ ≤ M`, `‖D(D g̃_{ij})(v)‖ ≤ M`;
    * the flow Jacobian is a unit, `IsUnit (fderiv (uniformFlowExp g gi hC hK q) v)`;
    * the pullback metric is a unit, `IsUnit (matToCLM g̃(v))`.

    Assembly of `uniformFlowPullbackMetric_c2_uniform_full` (Brick-A(β) W4) +
    `uniformFlowExp_common_nondeg_radius` (the (J) gate) + the hinge
    `uniformFlowPullbackMetric_isUnit_of_fderiv_isUnit` at the common radius `r₀ = min` of the two.  The
    `hgnd` input is carried HONESTLY as geometry (it is NOT the conclusion; the flat metric satisfies it).
    This delivers the uniform FORWARD-metric + nondegeneracy layer; the uniform `g̃⁻¹` NORM bounds are
    firewalled (see the file header). NOT `a₁ = R/6`. -/
theorem uniformResidual_forwardMetric_packet
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ q ∈ K, ∀ v : Point n,
      IsUnit (matToCLM (fun a b => g (uniformFlowExp g gi hC hK q v) a b))) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ i j : Fin n,
      (|uniformFlowPullbackMetric g gi hC hK q v i j| ≤ M
        ∧ ‖fderiv ℝ (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) v‖ ≤ M
        ∧ ‖fderiv ℝ (fun w => fderiv ℝ
            (fun w' => uniformFlowPullbackMetric g gi hC hK q w' i j) w) v‖ ≤ M)
      ∧ IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v)
      ∧ IsUnit (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)) := by
  obtain ⟨rC, hrC0, M, hM⟩ := uniformFlowPullbackMetric_c2_uniform_full g gi hg hC hK
  obtain ⟨ρ₀, hρ₀0, hnd⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  refine ⟨min rC ρ₀, lt_min hrC0 hρ₀0, max M 0, le_max_right _ _, ?_⟩
  intro q hq v hv i j
  have hvC : ‖v‖ < rC := lt_of_lt_of_le hv (min_le_left _ _)
  have hvρ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (min_le_right _ _)
  obtain ⟨_, _, hb0, hb1, hb2⟩ := hM q hq v hvC i j
  have hJunit : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v) := hnd q hq v hvρ
  refine ⟨⟨hb0.trans (le_max_left _ _), hb1.trans (le_max_left _ _), hb2.trans (le_max_left _ _)⟩,
    hJunit, ?_⟩
  exact uniformFlowPullbackMetric_isUnit_of_fderiv_isUnit g gi hC hK q v hJunit (hgnd q hq v)

end QIQTH.ExpMap
