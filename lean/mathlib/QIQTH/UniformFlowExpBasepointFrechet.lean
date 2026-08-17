/-
  UniformFlowExpBasepointFrechet — Brick 2 (of the hCConv base-slot-C¹ plan):
  the CONCRETE base-point (position-slot) Fréchet derivative of the `.choose`-built
  `uniformFlowExp`, in the minimal INTERIOR-POINT form directly consumable downstream.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## What Brick 2 asked for, and what it turns out already exists.

  The plan (`plans/tranquil-stargazing-fox.md`, Brick 2) asked to instantiate the ABSTRACT base-point
  Fréchet machinery at the CONCRETE tube `uniformFlowTube` / endpoint `uniformFlowExp`, supplying the
  concrete convexity / C² / Lipschitz / tube-containment data — mirroring how the velocity-direction
  case wires that same data class at the concrete flow, and (per J4-825's honest checkpoint) additionally
  handling the `q + s·u ∈ K` interior-openness needed because a perturbed base point can leave the
  compact base set `K`.

  On inspection that concrete instantiation was ALREADY BANKED (J4-731, `BaseFlowHderFamily.lean`):
  `baseFlow_hder_family` delivers, for a fixed velocity `v` with `‖v‖ ≤ ρ_K` and a convex base window
  sitting in the σ-interior of `K`, the per-base derivative package

      `∀ u ∈ window, ∃ L, HasFDerivAt (fun q => uniformFlowExp g gi hC hK q v) L u ∧ ‖L − id‖ ≤ Dc·e^{Kc}`,

  fed entirely from `uniformFlowTube_spec_ode/ic/conf` through the σ-WINDOWED base-slot Fréchet core
  `geodesicBasepoint_endpoint_hasFDerivAt_window` (which is precisely the resolution of the
  "perturbed base leaves `K`" mismatch J4-825 flagged: perturbed-tube data on `‖δ‖ ≤ σ`, Jacobi data
  global).  So the concrete-data supply Brick 2 describes is done, and — being a genuine `HasFDerivAt`
  — it is already STRONGER than J4-825's `GeodesicSmoothDepDir` directional (Gâteaux) result and than
  the abstract `GeodesicBasepointFrechet` (Brick 1) upgrade the plan sequenced.  Brick 1's abstract
  Fréchet statement is therefore NOT on the critical path for the CONCRETE object; the concrete
  base-point C¹ derivative already existed.

  ── WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited).

    * `uniformFlowExp_basepoint_hasFDerivAt` — ★ THE CAPSTONE.  For any base point `u` in the INTERIOR
      of the compact base set `K` and any velocity `v` with `‖v‖ ≤ ρ_K`, the concrete base-slot endpoint
      map `q ↦ uniformFlowExp g gi hC hK q v` has a Fréchet derivative at `u`:
          `∃ L : Point n →L[ℝ] Point n, HasFDerivAt (fun q => uniformFlowExp g gi hC hK q v) L u`.
      Consumes `baseFlow_hder_family` at the singleton window `closedBall u 0`; the interior hypothesis
      supplies the σ-ball `‖δ‖ ≤ σ ⟹ u + δ ∈ K` (`isOpen_interior` + `Metric.isOpen_iff`).

    * `uniformFlowExp_basepoint_differentiableAt` — the `DifferentiableAt` corollary: the base-slot
      C¹-at-a-point fact in exactly the shape the downstream `ContDiffAt`/`hCConv` chain consumes.

  ── HONEST FIREWALL (binding).  This is the CONCRETE base-point FIRST-order Fréchet derivative of the
  `.choose`-built `uniformFlowExp` at an interior base point.  It carries ONLY `u ∈ interior K` and
  `‖v‖ ≤ ρ_K` (both simultaneously and non-trivially satisfiable — interior nonempty for a base set with
  interior, `v` small — so NO vacuous / unsatisfiable-antecedent trap).  It does NOT (yet) deliver: a
  SECOND base-point derivative (whether `hCConv`'s `Φ` needs C¹-through-chain-rule or a genuine second
  base derivative is Brick 3's determination); the witness second-partial threading; or `hCConv` /
  `a₁ = R/6` itself.  a₁=R/6 remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
-/
import Mathlib
import QIQTH.BaseFlowHderFamily

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set

variable {n : ℕ}

/-- **★ Brick 2 CAPSTONE — the concrete base-point Fréchet derivative of `uniformFlowExp`.**
    For any base point `u` in the INTERIOR of the compact base set `K` and any velocity `v` with
    `‖v‖ ≤ ρ_K = uniformFlowRadius g gi hC hK`, the base-slot endpoint map
    `q ↦ uniformFlowExp g gi hC hK q v` has a Fréchet derivative at `u`.

    Proof: apply `baseFlow_hder_family` at the singleton window `closedBall u 0` (`c₀ = u`, `Rwin = 0`).
    The window's σ-interior hypothesis `∀ u' ∈ closedBall u 0, ∀ δ, ‖δ‖ ≤ σ → u' + δ ∈ K` reduces (the
    zero-radius ball is `{u}`) to `∀ δ, ‖δ‖ ≤ σ → u + δ ∈ K`, which the interior of `K` supplies: `K`
    interior is open (`isOpen_interior`), so `u ∈ interior K` gives a metric ball `ball u ε ⊆ K`, and
    `σ := ε/2` works.  The delivered family, specialised at `u ∈ closedBall u 0`, is the Fréchet
    derivative (the near-identity bound is discarded).  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_basepoint_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (v : Point n) (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK)
    (u : Point n) (hu : u ∈ interior K) :
    ∃ L : Point n →L[ℝ] Point n,
      HasFDerivAt (fun q => uniformFlowExp g gi hC hK q v) L u := by
  -- The interior of `K` is open; extract a metric ball around `u` inside `K`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior u hu
  -- window: singleton `closedBall u 0`; σ-radius `ε/2`.
  have hσ : (0 : ℝ) < ε / 2 := by positivity
  have hKσ : ∀ u' ∈ Metric.closedBall u (0 : ℝ), ∀ δ : Point n, ‖δ‖ ≤ ε / 2 → u' + δ ∈ K := by
    intro u' hu' δ hδ
    have hu'eq : u' = u := by
      have : dist u' u ≤ 0 := by rwa [Metric.mem_closedBall] at hu'
      exact dist_le_zero.mp this
    subst hu'eq
    have hmem : u' + δ ∈ Metric.ball u' ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : u' + δ - u' = δ := by abel
      rw [this]
      exact lt_of_le_of_lt hδ (by linarith)
    exact interior_subset (hball hmem)
  obtain ⟨Dc, Kc, _, _, hfam⟩ :=
    baseFlow_hder_family g gi hC hK v hv u 0 (ε / 2) le_rfl hσ hKσ
  obtain ⟨L, hFD, _⟩ := hfam u (Metric.mem_closedBall_self le_rfl)
  exact ⟨L, hFD⟩

/-- **The `DifferentiableAt` corollary — base-slot C¹-at-a-point of the concrete `uniformFlowExp`.**
    The shape the downstream `ContDiffAt` / `hCConv` chain consumes: at any interior base point `u`,
    for velocity `v` with `‖v‖ ≤ ρ_K`, the map `q ↦ uniformFlowExp g gi hC hK q v` is differentiable
    at `u`.  Immediate from `uniformFlowExp_basepoint_hasFDerivAt`.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_basepoint_differentiableAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (v : Point n) (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK)
    (u : Point n) (hu : u ∈ interior K) :
    DifferentiableAt ℝ (fun q => uniformFlowExp g gi hC hK q v) u := by
  obtain ⟨L, hFD⟩ := uniformFlowExp_basepoint_hasFDerivAt g gi hC hK v hv u hu
  exact hFD.differentiableAt

end QIQTH.ExpMap
