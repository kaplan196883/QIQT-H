/-
  BaseFlowTruncationWindow — J4-730, J3 BRICK 6, parts (4a)+(4b)+clause (c): THE WINDOW
  SELF-CONSISTENCY, THE BAD-SET LOCALIZATION, and THE UNIFORM v-LIPSCHITZ CLAUSE.

  Continues `BaseFlowGlobalContraction` (J4-729, brick (2)+(3), banked a70a521f): the coordinate
  (sup-ball metric-projection) clamp `coordClamp z₀ r`, its `LipschitzWith 1`-ness, and the GLOBAL
  contraction of the truncated solver map `w ↦ z₀ − g (coordClamp z₀ r w)`.  The Banach fixed point of
  that map is only useful to the `hflowData` assembly once we know (a) it lands in the window (so the
  truncation is invisible there) and (b) the frontier "bad set" where the true-flow containment leg (iii)
  lives sits inside the same window (so the truncated map agrees with the true flow there, and (iii)
  transfers verbatim).  This file discharges both, plus the uniform-in-base v-slot Lipschitz clause (c).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE KEY GEOMETRIC FACT (the pivot of parts (4a)/(4b)).
    On the sup-norm closed ball `closedBall z₀ r`, the coordinate clamp `coordClamp z₀ r` is the
    IDENTITY (each coordinate deviation already lies in `[−r, r]`, so `max (−r) (min r ·)` is inert).
    Hence any fixed point of the truncated solver map that lands in `closedBall z₀ r`, and any frontier
    point that localizes into `closedBall z₀ r`, sees `coordClamp = id` — the truncation is invisible.

  ── WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited).

    * `coordClamp_eq_self_of_mem_closedBall` — the clamp is the identity on the sup-ball.
    * `truncated_fixedPoint_in_window` — ★ BRICK (4a).  Any fixed point `w = z₀ − g (coordClamp z₀ r w)`
      of the truncated solver map with `‖g (coordClamp z₀ r w)‖ ≤ B ≤ r` lands in `closedBall z₀ r`:
      `‖w − z₀‖ = ‖g (coordClamp z₀ r w)‖ ≤ B ≤ r`.  The self-consistency of the window.
    * `baseDisplacement_norm_bound` — the sup-of-`‖g u‖` supplier feeding `B`: from the banked
      ∀-base displacement bound (`uniformFlowExp_displacement_bound`, uniform `C_D`),
      `‖φ_u v − u‖ ≤ ‖v‖ + C_D·‖v‖·‖v‖` for every base `u ∈ K` (so `≤ c(1 + C_D c)` when `‖v‖ ≤ c`).
    * `badSet_subset_closedBall` — ★ BRICK (4b), localization.  With a gate-reach bound
      `∀ w, S w ⊆ closedBall w ρ` and `ρ ≤ r`, the frontier bad set `{w | z₀ ∈ frontier (S w)}` sits
      inside `closedBall z₀ r`: `z₀ ∈ frontier (S w) ⊆ closure (S w) ⊆ closedBall w ρ ⟹ dist w z₀ ≤ ρ ≤ r`.
    * `truncated_agrees_on_badSet` — ★ BRICK (4b), agreement.  On the bad set the clamp is the identity,
      so `g (coordClamp z₀ r w) = g w` — the truncated map equals the true flow, and the frontier
      containment leg (iii) transfers verbatim.
    * `uniformFlowExp_vLipschitz_uniform` — ★ CLAUSE (c).  From the banked ∀-base sharp
      ApproximatesLinearOn (`uniformFlowExp_approximatesLinearOn_sharp`, `f' = id`), the velocity-slot map
      `v ↦ φ_q v` is `(1 + C_L·c)`-Lipschitz on `ball 0 c`, UNIFORMLY over the base `q ∈ K`.

  ── THE ∀-BASE SUPPLIER / ODE-EXISTENCE VERDICT (part (4), honest checkpoint).
    Both ODE existences feeding the per-base near-id supplier chain are BANKED and PROVED, not assumed:
      • geodesic flow existence — `geodesic_apriori_confinement_uniform` (BoundedGeometryConfine.lean),
        Skolemized into `uniformFlowTube`/`uniformFlowExp` with the `HasDerivAt … geodesicField` ODE spec
        (`uniformFlowTube_spec_ode`) holding ∀ base `q ∈ K`;
      • Jacobi (linear-variational) flow existence — `geodesicJacobi_exists_hasDerivAt_Icc`
        (GenericJacobiExists.lean), a fully-proved Picard one-step + glue construction.
    Both the displacement bound and the sharp ApproximatesLinearOn are ∀-base (`∀ q ∈ K`) with UNIFORM
    constants.  So the per-base near-id derivative family the `hder` clause of
    `baseDisplacement_lipschitzOnWith_window_nearId` demands is CONSTRUCTIBLE — the residual work is the
    mechanical family-assembly plumbing (re-anchoring `BasepointFDeriv` at each `u`), NOT a missing
    existence input.  No new axiom, no `sorry`, is needed for it.

  HONEST FIREWALL: this is J3 REGULARITY infrastructure — the window self-consistency / bad-set
  localization / uniform v-Lipschitz feeding the `hflowData` assembly of the Banach solver.  It is NOT
  `a₁ = R/6` (still a labelled carrier).  It does not build the full `hflowData` record, the second-order
  jet, Raychaudhuri, or numerical `G`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.BaseFlowGlobalContraction
import QIQTH.NearIsometryBudget
import QIQTH.WhiteSharpReach

namespace QIQTH.BaseFlowTruncationWindow

open QIQTH.Curvature QIQTH.ExpMap
open QIQTH.BaseFlowGlobalContraction
open scoped NNReal

variable {n : ℕ}

/-! ### The clamp is the identity on the sup-ball — the pivot for (4a)/(4b). -/

/-- On the sup-norm closed ball `closedBall z₀ r`, the coordinate clamp `coordClamp z₀ r` is the
    identity: every coordinate deviation `w i − z₀ i` already lies in `[−r, r]`, so
    `max (−r) (min r (w i − z₀ i)) = w i − z₀ i`. -/
theorem coordClamp_eq_self_of_mem_closedBall (z₀ : Point n) (r : ℝ)
    (w : Point n) (hw : w ∈ Metric.closedBall z₀ r) :
    coordClamp z₀ r w = w := by
  have hdist : dist w z₀ ≤ r := by rwa [Metric.mem_closedBall] at hw
  funext i
  have hi : |w i - z₀ i| ≤ r := by
    have hle := dist_le_pi_dist w z₀ i
    rw [Real.dist_eq] at hle
    exact le_trans hle hdist
  rw [abs_le] at hi
  simp only [coordClamp]
  rw [min_eq_right hi.2, max_eq_right hi.1]
  ring

/-! ### BRICK (4a) — window self-consistency of the truncated fixed point. -/

/-- **★ J3 brick 6 (4a) — the truncated fixed point lands in the window.**
    Any fixed point `w = z₀ − g (coordClamp z₀ r w)` of the truncated solver map whose displacement at
    the clamped argument is bounded by `B ≤ r` lies in the sup-ball `closedBall z₀ r`.  Directly:
    `‖w − z₀‖ = ‖−g (coordClamp z₀ r w)‖ = ‖g (coordClamp z₀ r w)‖ ≤ B ≤ r`.  This is the
    self-consistency that makes the truncation invisible at the fixed point. -/
theorem truncated_fixedPoint_in_window (z₀ : Point n) (r B : ℝ)
    (g : Point n → Point n) (w : Point n)
    (hfix : w = z₀ - g (coordClamp z₀ r w))
    (hbound : ‖g (coordClamp z₀ r w)‖ ≤ B) (hBr : B ≤ r) :
    w ∈ Metric.closedBall z₀ r := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  set G : Point n := g (coordClamp z₀ r w) with hG
  have hneg : w - z₀ = -G := by rw [hfix]; abel
  rw [hneg, norm_neg]
  exact le_trans hbound hBr

/-- The `sup_{u}‖g u‖` supplier for `B` in brick (4a): from the banked ∀-base displacement bound
    (`uniformFlowExp_displacement_bound`, uniform `C_D`), the base-displacement norm
    `‖φ_u v − u‖` is bounded by `‖v‖ + C_D·‖v‖·‖v‖` at every base `u ∈ K`.  For `‖v‖ ≤ c` this is
    `≤ c(1 + C_D·c)`, so `B := c(1 + C_D·c)` feeds `truncated_fixedPoint_in_window` whenever
    `r ≥ c(1 + C_D·c)`. -/
theorem baseDisplacement_norm_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ u ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      ‖uniformFlowExp g gi hC hK u v - u‖ ≤ ‖v‖ + C_D * ‖v‖ * ‖v‖ := by
  obtain ⟨ρ₀, hρ₀, C_D, hCD0, hbnd⟩ := uniformFlowExp_displacement_bound g gi hC hK
  refine ⟨ρ₀, hρ₀, C_D, hCD0, ?_⟩
  intro u hu v hv
  have h := hbnd u hu v hv
  calc ‖uniformFlowExp g gi hC hK u v - u‖
      = ‖(uniformFlowExp g gi hC hK u v - u - v) + v‖ := by congr 1; abel
    _ ≤ ‖uniformFlowExp g gi hC hK u v - u - v‖ + ‖v‖ := norm_add_le _ _
    _ ≤ C_D * ‖v‖ * ‖v‖ + ‖v‖ := by linarith [h]
    _ = ‖v‖ + C_D * ‖v‖ * ‖v‖ := by ring

/-! ### BRICK (4b) — bad-set localization and agreement with the true flow. -/

/-- **★ J3 brick 6 (4b) — the frontier bad set localizes into the window.**
    Given a gate-reach containment `∀ w, S w ⊆ closedBall w ρ` (the banked uniform reach of the
    flow gate, `S w ⊆ closedBall w ρ`) and `ρ ≤ r`, the frontier "bad set"
    `{w | z₀ ∈ frontier (S w)}` — where the true-flow containment leg (iii) lives — is contained in the
    sup-ball `closedBall z₀ r`.  Proof: `z₀ ∈ frontier (S w) ⊆ closure (S w) ⊆ closure (closedBall w ρ)
    = closedBall w ρ`, so `dist w z₀ = dist z₀ w ≤ ρ ≤ r`. -/
theorem badSet_subset_closedBall (z₀ : Point n) (r ρ : ℝ) (hρr : ρ ≤ r)
    (Sset : Point n → Set (Point n))
    (hreach : ∀ w, Sset w ⊆ Metric.closedBall w ρ) :
    {w : Point n | z₀ ∈ frontier (Sset w)} ⊆ Metric.closedBall z₀ r := by
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  have h1 : z₀ ∈ closure (Sset w) := frontier_subset_closure hw
  have h2 : closure (Sset w) ⊆ Metric.closedBall w ρ := by
    calc closure (Sset w) ⊆ closure (Metric.closedBall w ρ) := closure_mono (hreach w)
      _ = Metric.closedBall w ρ := Metric.isClosed_closedBall.closure_eq
  have h3 : z₀ ∈ Metric.closedBall w ρ := h2 h1
  rw [Metric.mem_closedBall] at h3
  rw [Metric.mem_closedBall, dist_comm]
  exact le_trans h3 hρr

/-- **★ J3 brick 6 (4b) — the truncated map equals the true flow on the bad set.**
    On the frontier bad set (which localizes into `closedBall z₀ r` by `badSet_subset_closedBall`) the
    coordinate clamp is the identity, so `g (coordClamp z₀ r w) = g w`.  Hence the truncated flow family
    `Ψtrunc w v := g (coordClamp z₀ r w) + w` agrees with the true flow `φ_w v = g w + w` there, and the
    true-flow frontier containment leg (iii) transfers to `Ψtrunc` verbatim. -/
theorem truncated_agrees_on_badSet (z₀ : Point n) (r ρ : ℝ) (hρr : ρ ≤ r)
    (g : Point n → Point n) (Sset : Point n → Set (Point n))
    (hreach : ∀ w, Sset w ⊆ Metric.closedBall w ρ)
    {w : Point n} (hw : z₀ ∈ frontier (Sset w)) :
    g (coordClamp z₀ r w) = g w := by
  have hmem : w ∈ Metric.closedBall z₀ r :=
    badSet_subset_closedBall z₀ r ρ hρr Sset hreach hw
  rw [coordClamp_eq_self_of_mem_closedBall z₀ r w hmem]

/-! ### CLAUSE (c) — the uniform-in-base velocity-slot Lipschitz bound. -/

/-- **★ J3 brick 6 clause (c) — the uniform-in-base v-slot Lipschitz bound.**
    From the banked ∀-base sharp `ApproximatesLinearOn` of the recentring flow
    (`uniformFlowExp_approximatesLinearOn_sharp`, linear part `f' = id`, shrinking constant `C_L·c`), the
    velocity-slot map `v ↦ φ_q v` is `(1 + C_L·c)`-Lipschitz on `ball 0 c`, UNIFORMLY over the base
    `q ∈ K`:  `‖φ_q v − φ_q v'‖ ≤ ‖φ_q v − φ_q v' − (v − v')‖ + ‖v − v'‖ ≤ (C_L·c + 1)‖v − v'‖`.  This is
    the v-slot regularity clause the `hflowData (c)` leg demands. -/
theorem uniformFlowExp_vLipschitz_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ q ∈ K, ∀ c : ℝ, 0 < c → c ≤ ρ₀ →
      ∀ v ∈ Metric.ball (0 : Point n) c, ∀ v' ∈ Metric.ball (0 : Point n) c,
        dist (uniformFlowExp g gi hC hK q v) (uniformFlowExp g gi hC hK q v')
          ≤ (1 + C_L * c) * dist v v' := by
  obtain ⟨ρ₀, hρ₀, C_L, hCL0, hAL⟩ :=
    QIQTH.WhiteSharpReach.uniformFlowExp_approximatesLinearOn_sharp g gi hC hK
  refine ⟨ρ₀, hρ₀, C_L, hCL0, ?_⟩
  intro q hq c hc hcρ v hv v' hv'
  have hApprox := hAL q hq c hc hcρ v hv v' hv'
  rw [Real.coe_toNNReal (C_L * c) (mul_nonneg hCL0 hc.le)] at hApprox
  simp only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply] at hApprox
  simp only [dist_eq_norm]
  calc ‖uniformFlowExp g gi hC hK q v - uniformFlowExp g gi hC hK q v'‖
      = ‖(uniformFlowExp g gi hC hK q v - uniformFlowExp g gi hC hK q v' - (v - v')) + (v - v')‖ := by
        congr 1; abel
    _ ≤ ‖uniformFlowExp g gi hC hK q v - uniformFlowExp g gi hC hK q v' - (v - v')‖ + ‖v - v'‖ :=
        norm_add_le _ _
    _ ≤ C_L * c * ‖v - v'‖ + ‖v - v'‖ := by linarith [hApprox]
    _ = (1 + C_L * c) * ‖v - v'‖ := by ring

end QIQTH.BaseFlowTruncationWindow

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.BaseFlowTruncationWindow
#check @coordClamp_eq_self_of_mem_closedBall
#check @truncated_fixedPoint_in_window
#check @baseDisplacement_norm_bound
#check @badSet_subset_closedBall
#check @truncated_agrees_on_badSet
#check @uniformFlowExp_vLipschitz_uniform
end AxiomChecks
