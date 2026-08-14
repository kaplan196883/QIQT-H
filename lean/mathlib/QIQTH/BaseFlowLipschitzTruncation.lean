/-
  BaseFlowLipschitzTruncation — J4-728, J3 BRICK 6 (partial): THE GLOBAL LIPSCHITZ TRUNCATION,
  brick (1) — the per-base near-identity → LipschitzOnWith upgrade over a convex window.

  ODE_VARIATIONAL_PLAN.md / WHITENED_CAMPAIGN_TERMINAL.md.  The `hflowData (i)` contraction leg of
  `WhiteHsolveFlowContraction.white_hInnerCont_closed_final8` demands a GLOBAL `ContractingWith Kc`
  bound on `w ↦ z₀ − φ_w v + w`.  `BaseFlowNearId.baseFlow_endpoint_fderiv_near_id` (banked, 9898c48d)
  delivers only the derivative-AT-THE-CENTRE smallness `‖L − id‖ ≤ Dc·e^K` for the base-slot endpoint
  derivative `L = fderiv (fun δ => (W δ 1).1) 0` at ONE base point.

  ── THE PER-w UNIFORMITY VERDICT (the pivot).
    The constants `M₂` (C² field sup on the convex tube `S`), `K` (Jacobi-coefficient bound), and the
    coefficient deviation `Dc` are all WINDOW-UNIFORM — they come from compactness of the base tube, NOT
    from the particular base point.  So the near-identity bound `‖L_u − id‖ ≤ Dc·e^K` holds AT EVERY base
    `u` in the convex window with the SAME constant, by a `q`-parametric re-instantiation of
    `baseFlow_endpoint_fderiv_near_id` (re-anchoring the perturbation family at base `u`).  This makes the
    base-displacement map `u ↦ φ_u v − u` have Fréchet derivative `L_u − id` with `‖L_u − id‖ ≤ Dc·e^K`
    at every `u` in the window ⟹ by the mean-value inequality on a CONVEX window, it is
    `LipschitzOnWith (Dc·e^K)` there.

  ── WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axioms).

    * `baseDisplacement_lipschitzOnWith_window` — ★ BRICK (1).  For ANY endpoint map `F : Point n → Point n`
      and convex window `S`, from the per-base near-identity derivative package
      (`∀ u ∈ S, ∃ L, HasFDerivAt F L u ∧ ‖L − id‖ ≤ M`, `0 ≤ M`) the base-displacement map
      `u ↦ F u − u` is `LipschitzOnWith M.toNNReal` on `S`.  The derivative of `u ↦ F u − u` is `L_u − id`,
      whose norm is `≤ M` on the window; `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le` (the MVI on
      a convex set) assembles the Lipschitz bound.  Metric-agnostic; the per-base derivative package is
      exactly the window-uniform re-instantiation of `baseFlow_endpoint_fderiv_near_id` (with `M = Dc·e^K`).

    * `baseDisplacement_lipschitzOnWith_window_nearId` — ★ the `Dc·e^K`-phrased corollary matching the
      `BaseFlowNearId` output shape verbatim: with `0 ≤ Dc`, `0 ≤ K` and the per-base near-id package
      `‖L_u − id‖ ≤ Dc·e^K`, `u ↦ F u − u` is `LipschitzOnWith (Dc·Real.exp K).toNNReal` on the window.

  HONEST FIREWALL: this is J3 REGULARITY infrastructure — brick (1) of the global Lipschitz truncation
  feeding the `hflowData (i)` contraction.  It is NOT `a₁ = R/6` (still a labelled carrier).  It upgrades
  the derivative-AT-EVERY-BASE smallness to a GLOBAL Lipschitz bound on the convex window; it does NOT
  build the metric-projection clamp `Ψtrunc`, the truncated fixed-point self-consistency, or the full
  `hflowData` assembly (those are bricks (2)–(4), downstream).  It does not build the second-order jet,
  Raychaudhuri, or numerical `G`.
-/
import Mathlib
import QIQTH.Curvature

namespace QIQTH.BaseFlowLipTrunc

open QIQTH.Curvature

variable {n : ℕ}

/-! ### BRICK (1) — per-base near-identity derivative ⟹ LipschitzOnWith over a convex window. -/

/-- **★ J3 brick 6 (1) — the base-displacement map is Lipschitz on the convex window.**
    For an endpoint map `F : Point n → Point n` and a convex window `S`, if at every base `u ∈ S` the
    map `F` has a Fréchet derivative `L_u` deviating from the identity by `‖L_u − id‖ ≤ M` (with `0 ≤ M`),
    then the base-displacement map `u ↦ F u − u` is `LipschitzOnWith M.toNNReal` on `S`.

    Proof: `u ↦ F u − u` has Fréchet derivative `L_u − ContinuousLinearMap.id` at each `u ∈ S`, and
    `‖L_u − id‖ ≤ M`, so `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le` (the mean-value inequality
    on a convex set) yields the Lipschitz bound.  Metric-agnostic; `M = Dc·e^K` from the window-uniform
    re-instantiation of `baseFlow_endpoint_fderiv_near_id`. -/
theorem baseDisplacement_lipschitzOnWith_window
    (F : Point n → Point n) (S : Set (Point n)) (M : ℝ) (hM : 0 ≤ M)
    (hconv : Convex ℝ S)
    (hder : ∀ u ∈ S, ∃ L : Point n →L[ℝ] Point n,
        HasFDerivAt F L u ∧ ‖L - ContinuousLinearMap.id ℝ (Point n)‖ ≤ M) :
    LipschitzOnWith M.toNNReal (fun u => F u - u) S := by
  classical
  -- choose the per-base derivative operator.
  choose L hL using hder
  -- the candidate derivative of `u ↦ F u − u` on `S`: `L_u − id` (arbitrary off `S`).
  set f' : Point n → (Point n →L[ℝ] Point n) :=
    fun u => if h : u ∈ S then L u h - ContinuousLinearMap.id ℝ (Point n) else 0 with hf'
  refine hconv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (f' := f') ?_ ?_
  · -- `u ↦ F u − u` has derivative `f' u` within `S` at each `u ∈ S`.
    intro x hx
    have hfx : f' x = L x hx - ContinuousLinearMap.id ℝ (Point n) := by
      simp only [hf', dif_pos hx]
    rw [hfx]
    exact ((hL x hx).1.sub (hasFDerivAt_id x)).hasFDerivWithinAt
  · -- the derivative norm is `≤ M.toNNReal` on `S`.
    intro x hx
    have hfx : f' x = L x hx - ContinuousLinearMap.id ℝ (Point n) := by
      simp only [hf', dif_pos hx]
    rw [hfx, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M hM]
    exact (hL x hx).2

/-- **★ J3 brick 6 (1), `Dc·e^K` form.**  The corollary matching the `BaseFlowNearId` output shape:
    with `0 ≤ Dc`, `0 ≤ K` and the per-base near-identity package `‖L_u − id‖ ≤ Dc·Real.exp K` at every
    `u ∈ S` (the window-uniform re-instantiation of `baseFlow_endpoint_fderiv_near_id`), the
    base-displacement map `u ↦ F u − u` is `LipschitzOnWith (Dc·Real.exp K).toNNReal` on the convex
    window `S`.  Feeds the `hflowData (i)` contraction after the numeric leg `Dc·e^K < 1` (small `c`). -/
theorem baseDisplacement_lipschitzOnWith_window_nearId
    (F : Point n → Point n) (S : Set (Point n)) (Dc K : ℝ) (hDc : 0 ≤ Dc) (hK : 0 ≤ K)
    (hconv : Convex ℝ S)
    (hder : ∀ u ∈ S, ∃ L : Point n →L[ℝ] Point n,
        HasFDerivAt F L u ∧ ‖L - ContinuousLinearMap.id ℝ (Point n)‖ ≤ Dc * Real.exp K) :
    LipschitzOnWith (Dc * Real.exp K).toNNReal (fun u => F u - u) S :=
  baseDisplacement_lipschitzOnWith_window F S (Dc * Real.exp K)
    (mul_nonneg hDc (Real.exp_pos K).le) hconv hder

end QIQTH.BaseFlowLipTrunc

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.BaseFlowLipTrunc
#check @baseDisplacement_lipschitzOnWith_window
#check @baseDisplacement_lipschitzOnWith_window_nearId
end AxiomChecks
