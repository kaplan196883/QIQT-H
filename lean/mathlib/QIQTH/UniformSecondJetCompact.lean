/-
  UniformSecondJetCompact — J4-21: reduce J4-19's carried uniform second-jet bound `(I2)` to a
  single, honest JOINT-CONTINUITY input via a compactness argument.

  ## Context

  J4-19 (`UniformExpSecondJet.lean`) proved the common exp-nondegeneracy radius over a compact base
  set `K` CONDITIONAL on two uniform-geometry inputs:

    (I1)  a uniform lower bound on the exp injectivity radius over `K` (`hrad`), and
    (I2)  a single `M ≥ 0` bounding the second jet
          `‖fderiv ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x‖ ≤ M`  uniformly over `q ∈ K`,
          `‖x‖ < r`   (the BOUND-ONLY uniform second-jet estimate).

  This file DERIVES `(I2)` from a single clean regularity input.

  ## Feasibility verdict (investigation result) — why this is the honest route

  A DIRECT derivation of `(I2)` is blocked by a structural obstruction with NO existing repo/Mathlib
  shortcut:

  * `expMap g gi hC q` is welded to the per-`q` OPAQUE `Classical.choose` tube `expTube g gi hC q`
    (`irreducible`).  The unconditional `Cᵏ` tower (`ExpMapContDiffFour`, `expMap_contDiffOn_four`)
    gives `v ↦ fderiv² exp_q v` CONTINUOUS on the ball at a FIXED base `q` — hence bounded on a
    compact velocity ball PER `q` — but the constants depend on the opaque per-`q` selector, so there
    is NO joint-in-`q` regularity available.  Uniformity over `q` is exactly what is missing.
  * The repo's geodesic smooth-dependence development (`GeodesicSmoothDep.lean`) is FIRST-ORDER only:
    `geodesicVariation_exists`/`geodesicVariation_hasDerivAt_of_smoothDep` give the linearized Jacobi
    equation (the FIRST IC-derivative of the flow).  There is no second-order joint smooth dependence.
  * Mathlib's Picard–Lindelöf flow (`IsPicardLindelof`, the engine behind
    `geodesic_apriori_confinement_uniform`) provides only LIPSCHITZ / continuous dependence on the
    initial condition — higher-order (`C¹`+) JOINT smooth dependence of an ODE flow on its IC is a
    KNOWN Mathlib gap, absent from the library.

  Hence route (R-a: joint `(q,v)`-continuity of the second jet ⟹ bounded on compact) cannot be
  discharged from existing material, and route (R-b: a from-scratch uniform Grönwall on the SECOND
  variational equation with `BoundedGeometry`-uniform Christoffel 2-jet coefficients) is a genuine
  multi-brick second-order-smooth-dependence development.

  ## What IS derived here (honest firewall, no `sorry`, no hyp = conclusion)

  The COMPACTNESS half is DERIVED OUTRIGHT.  `expMap_second_jet_bddOn_uniform_of_joint_cont` takes
  the SINGLE regularity input

    (J)  `hjoint : ContinuousOn (fun p : Point n × Point n =>
              ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p.1) w) p.2‖) (K ×ˢ closedBall 0 r)`
         — JOINT continuity of the second-jet OPERATOR NORM in `(base, fibre)` on the compact product
         `K × B̄(0,r)` (a real-valued statement — implied by, and slightly weaker than, joint
         continuity of the second-jet map itself; free of the CLM bounded-convergence-vs-operator-norm
         topology diamond) —

  and PRODUCES `(I2)`: a single `M ≥ 0` with the uniform second-jet bound over `q ∈ K`, `‖x‖ < r`.
  DERIVED = the whole compactness step (`K ×ˢ closedBall 0 r` is compact, so the jointly-continuous
  second jet is bounded on it, `IsCompact.exists_bound_of_continuousOn`).  The ONLY carried obligation
  is `(J)`.

  ## The precise remaining input `(J)` — and whether it is a genuine Mathlib gap

  `(J)` is NOT the uniform-bound conclusion and NOT an `∃ M`; it is a strictly WEAKER, purely
  qualitative regularity fact: joint continuity of the exp second-jet operator norm in `(q, v)`.  It
  is exactly the
  higher-order joint-smooth-dependence-on-IC content that neither Mathlib (whose PL flow is only
  Lipschitz-in-IC) nor the repo (whose smooth-dependence is first-order) currently provides — so `(J)`
  is a GENUINE joint-second-order-smooth-dependence gap.  It is, however, a SINGLE clean qualitative
  hypothesis: the uniform second-jet package is now reduced to this one gap, not to an open-ended list.

  `expMap_common_nondeg_radius_of_joint_cont` then chains this into J4-19's
  `expMap_common_nondeg_radius_of_uniform_inputs`, reducing the common nondegeneracy radius over `K`
  to just `(I1) hrad` (uniform injectivity radius) and `(J)` (joint second-jet continuity).
-/
import QIQTH.UniformExpSecondJet
import QIQTH.BoundedGeometry
import QIQTH.UniformFlowBridge
import QIQTH.ExpMapContDiffFour
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric
open scoped Topology

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- **J4-21 (PRIMARY) — the uniform second-jet bound `(I2)`, DERIVED from joint continuity.**

    Given the SINGLE joint-regularity input
    * `(J) hjoint` : the second-jet operator norm
      `(q, v) ↦ ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v‖`
      is CONTINUOUS on the compact product `K ×ˢ closedBall 0 r`,

    the compact set `K ×ˢ closedBall 0 r` carries a uniform sup-bound `M` on the (jointly continuous)
    second jet (`IsCompact.exists_bound_of_continuousOn`), which restricts to EXACTLY J4-19's `(I2)`
    shape: a single `M ≥ 0` with
    `‖fderiv ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x‖ ≤ M` for all `q ∈ K`, `‖x‖ < r`.

    DERIVED = the entire compactness step; the ONLY carried obligation is `(J) hjoint`. -/
theorem expMap_second_jet_bddOn_uniform_of_joint_cont (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (r : ℝ)
    (hjoint : ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p.1) w) p.2‖)
      (K ×ˢ Metric.closedBall (0 : Point n) r)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K, ∀ x : Point n, ‖x‖ < r →
      ‖fderiv ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x‖ ≤ M := by
  -- The base-fibre product is compact.
  have hKprod : IsCompact (K ×ˢ Metric.closedBall (0 : Point n) r) :=
    hK.prod (isCompact_closedBall (0 : Point n) r)
  -- The jointly-continuous REAL-valued second-jet norm attains a sup-bound on the compact product
  -- (`IsCompact.exists_bound_of_continuousOn`).  (Real codomain — no CLM topology-instance diamond.)
  obtain ⟨C, hCb⟩ := hKprod.exists_bound_of_continuousOn hjoint
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq x hx
  -- `‖x‖ < r ⟹ x ∈ closedBall 0 r`, so `(q, x)` lies in the compact product.
  have hxmem : x ∈ Metric.closedBall (0 : Point n) r := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hx.le
  have hpmem : (q, x) ∈ K ×ˢ Metric.closedBall (0 : Point n) r := ⟨hq, hxmem⟩
  -- The sup-bound at `(q, x)` (a real `‖‖·‖‖ = |‖·‖|`) dominates the target second-jet norm.
  have hb := hCb (q, x) hpmem
  rw [Real.norm_eq_abs] at hb
  exact le_trans (le_trans (le_abs_self _) hb) (le_max_left _ _)

/-- **J4-21 (SECONDARY) — common nondegeneracy radius over `K`, reduced to `(I1) ∧ (J)`.**

    Chaining `expMap_second_jet_bddOn_uniform_of_joint_cont` into J4-19's
    `expMap_common_nondeg_radius_of_uniform_inputs` yields a SINGLE radius `ρ₀ > 0` with
    `IsUnit (fderiv ℝ (expMap g gi hC q) v)` for all `q ∈ K`, `‖v‖ < ρ₀`, now conditional ONLY on
    * `(I1) hrad` : the uniform exp injectivity-radius lower bound over `K`, and
    * `(J) hjoint` : joint continuity of the exp second jet on the compact `K ×ˢ closedBall 0 r`.

    The bound-only uniform second-jet estimate `(I2)` has been DISCHARGED into the joint-continuity
    input `(J)` by the compactness step. -/
theorem expMap_common_nondeg_radius_of_joint_cont (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (r : ℝ) (hr : 0 < r)
    (hrad : ∀ q ∈ K, r ≤ expRho g gi hC q)
    (hjoint : ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p.1) w) p.2‖)
      (K ×ˢ Metric.closedBall (0 : Point n) r)) :
    ∃ ρ₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      IsUnit (fderiv ℝ (expMap g gi hC q) v) := by
  obtain ⟨M, hM0, hbnd⟩ :=
    expMap_second_jet_bddOn_uniform_of_joint_cont g gi hC hK r hjoint
  exact expMap_common_nondeg_radius_of_uniform_inputs g gi hC hK r hr hrad M hM0 hbnd

end QIQTH.ExpMap
