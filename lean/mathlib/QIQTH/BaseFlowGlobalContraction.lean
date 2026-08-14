/-
  BaseFlowGlobalContraction — J4-729, J3 BRICK 6, parts (2)+(3): THE CLAMP + THE GLOBAL CONTRACTION.

  Continues `BaseFlowLipschitzTruncation` (brick (1), banked): the base-displacement map
  `g u := φ_u v − u` is `LipschitzOnWith (Dc·e^K)` on the convex window `S`
  (`baseDisplacement_lipschitzOnWith_window_nearId`).  Brick (1) alone is only a LOCAL (on-window)
  Lipschitz bound — the Banach solver `WhiteHsolveFlowContraction.hsolveFlow_of_contractionData` demands
  a GLOBAL `ContractingWith Kc` bound on `w ↦ z₀ − Ψtrunc w v + w`.  This file bridges local→global by
  precomposing `g` with a metric-projection CLAMP onto the window, then discharges the global
  contraction.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE NORM / CLAMP VERDICT (the pivot of this brick).
    `Point n = Fin n → ℝ` carries the **sup norm** (`Pi.normedAddCommGroup`), NOT the Euclidean norm.
    Therefore the RADIAL clamp `w ↦ z₀ + r·(w−z₀)/‖w−z₀‖` is NOT the metric projection onto the ball and
    is NOT 1-Lipschitz in sup norm.  The metric projection onto a **sup-norm** closed ball is the
    COORDINATE clamp
        `coordClamp z₀ r w := fun i => z₀ i + max (-r) (min r (w i − z₀ i))`,
    clamping each coordinate independently into `[−r, r]` around `z₀`.  Each coordinate map
    `t ↦ max (-r) (min r t)` is 1-Lipschitz on `ℝ`, so `coordClamp` is 1-Lipschitz in the sup norm
    (via `dist_pi_le_iff` / `dist_le_pi_dist`), and it lands in the sup-ball `closedBall z₀ r`.

  ── WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited).

    * `coordClamp` — the coordinate (sup-ball metric-projection) clamp.
    * `coordClamp_lipschitzWith_one` — ★ BRICK (2).  `coordClamp z₀ r` is globally `LipschitzWith 1`
      in the sup norm.
    * `coordClamp_mem_closedBall` — `coordClamp z₀ r w ∈ Metric.closedBall z₀ r` (for `0 ≤ r`): the
      clamp maps ONTO the sup-ball, so it maps `univ` into any window `S ⊇ closedBall z₀ r`.
    * `truncatedSolverMap_contractingWith` — ★ BRICK (3).  For a window-Lipschitz displacement
      `g : LipschitzOnWith M g S` with `M < 1`, and `closedBall z₀ r ⊆ S`, the GLOBAL truncated solver
      map `w ↦ z₀ − g (coordClamp z₀ r w)` is `ContractingWith M`.  Proof: `g ∘ coordClamp` is
      `LipschitzWith M` (window-Lipschitz `g` composed with the 1-Lipschitz clamp that maps into `S`,
      `LipschitzOnWith.comp`), then `w ↦ z₀ − ·` is a 1-Lipschitz isometry, so the whole map is
      `LipschitzWith M` with `M < 1`.
    * `truncatedSolverMap_eq` — the algebraic identity feeding the abstract solver: with
      `Ψtrunc w v := g (coordClamp z₀ r w) + w`, the solver's map `w ↦ z₀ − Ψtrunc w v + w` equals
      `w ↦ z₀ − g (coordClamp z₀ r w)`, so `truncatedSolverMap_contractingWith` supplies the solver's
      `ContractingWith Kc` clause verbatim.

  HONEST FIREWALL: this is J3 REGULARITY infrastructure — parts (2)+(3) of the global Lipschitz
  truncation feeding the `hflowData (i)` contraction leg of the Banach solver.  It is NOT `a₁ = R/6`
  (still a labelled carrier).  It does NOT build the truncated fixed-point self-consistency /
  agreement-on-the-bad-set (brick (4)) nor the per-base near-id supplier chain; it does not build the
  second-order jet, Raychaudhuri, or numerical `G`.
-/
import Mathlib
import QIQTH.Curvature

namespace QIQTH.BaseFlowGlobalContraction

open QIQTH.Curvature
open scoped NNReal

variable {n : ℕ}

/-! ### BRICK (2) — the coordinate (sup-ball metric-projection) clamp. -/

/-- The **coordinate clamp** onto the sup-norm closed ball `closedBall z₀ r`: each coordinate of
    `w − z₀` is clamped into `[−r, r]` and re-centred at `z₀`.  This is the metric projection onto the
    sup-ball (NOT the radial clamp, which is only correct for the Euclidean norm). -/
noncomputable def coordClamp (z₀ : Point n) (r : ℝ) (w : Point n) : Point n :=
  fun i => z₀ i + max (-r) (min r (w i - z₀ i))

/-- The scalar clamp `t ↦ max (-r) (min r t)` is `LipschitzWith 1` on `ℝ`. -/
theorem scalarClamp_lipschitzWith_one (r : ℝ) :
    LipschitzWith 1 (fun t : ℝ => max (-r) (min r t)) := by
  have h1 : LipschitzWith 1 (fun t : ℝ => min r t) := LipschitzWith.const_min LipschitzWith.id r
  simpa using LipschitzWith.const_max h1 (-r)

/-- **★ J3 brick 6 (2) — the coordinate clamp is `LipschitzWith 1` in the sup norm.**
    Each coordinate map is 1-Lipschitz on `ℝ`, and the sup-norm distance is the coordinatewise max
    (`dist_pi_le_iff` / `dist_le_pi_dist`), so the whole clamp is 1-Lipschitz.  This is the correct
    metric-projection replacement for the radial clamp, which is NOT 1-Lipschitz in the sup norm. -/
theorem coordClamp_lipschitzWith_one (z₀ : Point n) (r : ℝ) :
    LipschitzWith 1 (coordClamp z₀ r) := by
  apply LipschitzWith.of_dist_le_mul
  intro w w'
  rw [NNReal.coe_one, one_mul]
  have hnn : (0 : ℝ) ≤ dist w w' := dist_nonneg
  rw [dist_pi_le_iff hnn]
  intro i
  -- coordinatewise: the `z₀ i +` cancels in `dist`, leaving the scalar clamp.
  have hcoord : dist (coordClamp z₀ r w i) (coordClamp z₀ r w' i)
      = dist (max (-r) (min r (w i - z₀ i))) (max (-r) (min r (w' i - z₀ i))) := by
    simp only [coordClamp, dist_eq_norm, Real.norm_eq_abs]
    congr 1
    ring
  rw [hcoord]
  -- scalar clamp is 1-Lipschitz, then the `− z₀ i` inside cancels.
  have hs := (scalarClamp_lipschitzWith_one r).dist_le_mul (w i - z₀ i) (w' i - z₀ i)
  simp only [NNReal.coe_one, one_mul] at hs
  refine hs.trans ?_
  -- `dist (w i − z₀ i) (w' i − z₀ i) = dist (w i) (w' i) ≤ dist w w'`.
  have hshift : dist (w i - z₀ i) (w' i - z₀ i) = dist (w i) (w' i) := by
    simp only [dist_eq_norm]; congr 1; ring
  rw [hshift]
  exact dist_le_pi_dist w w' i

/-- The coordinate clamp lands in the sup-norm closed ball `closedBall z₀ r` (for `0 ≤ r`):
    every clamped coordinate deviates from `z₀` by at most `r`. -/
theorem coordClamp_mem_closedBall (z₀ : Point n) (r : ℝ) (hr : 0 ≤ r) (w : Point n) :
    coordClamp z₀ r w ∈ Metric.closedBall z₀ r := by
  rw [Metric.mem_closedBall, dist_pi_le_iff hr]
  intro i
  -- `dist (coordClamp … i) (z₀ i) = |max (-r) (min r (w i − z₀ i))| ≤ r`.
  have hcoord : dist (coordClamp z₀ r w i) (z₀ i)
      = |max (-r) (min r (w i - z₀ i))| := by
    simp only [coordClamp, dist_eq_norm, Real.norm_eq_abs]
    congr 1; ring
  rw [hcoord, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- `coordClamp z₀ r` maps `univ` into any window `S` that contains the sup-ball `closedBall z₀ r`. -/
theorem coordClamp_mapsTo (z₀ : Point n) (r : ℝ) (hr : 0 ≤ r)
    {S : Set (Point n)} (hball : Metric.closedBall z₀ r ⊆ S) :
    Set.MapsTo (coordClamp z₀ r) Set.univ S :=
  fun w _ => hball (coordClamp_mem_closedBall z₀ r hr w)

/-! ### BRICK (3) — the global contraction of the truncated solver map. -/

/-- `w ↦ z₀ − y` is a `LipschitzWith 1` isometry on `Point n`. -/
theorem constSub_lipschitzWith_one (z₀ : Point n) :
    LipschitzWith 1 (fun y : Point n => z₀ - y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [show (z₀ - x) - (z₀ - y) = y - x by abel, norm_sub_rev]

/-- **★ J3 brick 6 (3) — the GLOBAL contraction of the truncated solver map.**
    Given a window `S ⊇ closedBall z₀ r` (sup-ball) and a displacement `g` that is `LipschitzOnWith M`
    on `S` with contraction constant `M < 1`, the truncated solver map
        `w ↦ z₀ − g (coordClamp z₀ r w)`
    is globally `ContractingWith M`.

    Proof: `coordClamp z₀ r` is globally `LipschitzWith 1` (brick (2)) and maps `univ` into `S`
    (`coordClamp_mapsTo`), so `g ∘ coordClamp` is `LipschitzWith M` by `LipschitzOnWith.comp`
    (window-Lipschitz `g` after the 1-Lipschitz clamp into `S`).  Precomposing with the 1-Lipschitz
    isometry `y ↦ z₀ − y` keeps the constant `M < 1`, giving `ContractingWith M`. -/
theorem truncatedSolverMap_contractingWith
    (z₀ : Point n) (r : ℝ) (hr : 0 ≤ r)
    {S : Set (Point n)} (hball : Metric.closedBall z₀ r ⊆ S)
    (g : Point n → Point n) (M : ℝ≥0) (hM1 : M < 1)
    (hg : LipschitzOnWith M g S) :
    ContractingWith M (fun w => z₀ - g (coordClamp z₀ r w)) := by
  refine ⟨hM1, ?_⟩
  -- `g ∘ coordClamp` is globally `LipschitzWith M`.
  have hcomp_on : LipschitzOnWith (M * 1) (g ∘ coordClamp z₀ r) Set.univ :=
    hg.comp ((lipschitzOnWith_univ).2 (coordClamp_lipschitzWith_one z₀ r))
      (coordClamp_mapsTo z₀ r hr hball)
  rw [mul_one] at hcomp_on
  have hcomp : LipschitzWith M (g ∘ coordClamp z₀ r) := lipschitzOnWith_univ.1 hcomp_on
  -- precompose with the 1-Lipschitz isometry `y ↦ z₀ − y`.
  have hfull : LipschitzWith (1 * M) (fun w => z₀ - (g ∘ coordClamp z₀ r) w) :=
    (constSub_lipschitzWith_one z₀).comp hcomp
  rw [one_mul] at hfull
  exact hfull

/-- The algebraic identity feeding the abstract Banach solver.  With the truncated flow family
    `Ψtrunc w v := g (coordClamp z₀ r w) + w`, the solver's contraction map `w ↦ z₀ − Ψtrunc w v + w`
    equals the truncated solver map `w ↦ z₀ − g (coordClamp z₀ r w)`.  Hence
    `truncatedSolverMap_contractingWith` supplies the `ContractingWith Kc` clause required by
    `hsolveFlow_of_contractionData` verbatim (with `Kc = M`). -/
theorem truncatedSolverMap_eq (z₀ : Point n) (r : ℝ) (g : Point n → Point n) :
    (fun w : Point n => z₀ - (g (coordClamp z₀ r w) + w) + w)
      = (fun w => z₀ - g (coordClamp z₀ r w)) := by
  funext w
  abel

/-- **★ J3 brick 6 (3), solver-shaped.**  The `ContractingWith M` clause of
    `hsolveFlow_of_contractionData` for the truncated flow family `Ψtrunc w _ := g (coordClamp …) + w`,
    obtained by rewriting `truncatedSolverMap_contractingWith` through `truncatedSolverMap_eq`. -/
theorem truncatedSolverMap_contractingWith_solverShape
    (z₀ : Point n) (r : ℝ) (hr : 0 ≤ r)
    {S : Set (Point n)} (hball : Metric.closedBall z₀ r ⊆ S)
    (g : Point n → Point n) (M : ℝ≥0) (hM1 : M < 1)
    (hg : LipschitzOnWith M g S) :
    ContractingWith M (fun w => z₀ - (g (coordClamp z₀ r w) + w) + w) := by
  rw [truncatedSolverMap_eq]
  exact truncatedSolverMap_contractingWith z₀ r hr hball g M hM1 hg

end QIQTH.BaseFlowGlobalContraction

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.BaseFlowGlobalContraction
#check @coordClamp_lipschitzWith_one
#check @coordClamp_mem_closedBall
#check @truncatedSolverMap_contractingWith
#check @truncatedSolverMap_contractingWith_solverShape
end AxiomChecks
