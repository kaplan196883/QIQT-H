/-
  GeodesicQuadraticBaseJet — J4-726, J3 BRICK 4: THE QUADRATIC BASE-JET.

  ODE_VARIATIONAL_PLAN.md / WHITENED_CAMPAIGN_TERMINAL.md §5.  The second-order control of the geodesic
  variation in the base parameter `s`:
      `‖Y s τ − Y 0 τ − s·V τ‖ ≤ C · s²`   uniformly for `τ ∈ [0,1]`,
  the DIRECT feeder of the `hflowData` small-window MVI (the contraction step of J3).

  This bound already existed as the intermediate `hbnd` INSIDE `geodesicVariation_exists`
  (`GeodesicSmoothDep.lean`) — the little-o extraction consumed it and threw it away.  Here it is
  EXPOSED as a standalone brick, uniform in `τ ∈ [0,1]` (not fixed `t`), with every constant produced
  by compactness of the region `S` (reusing the J4-724/725 compactness engines):

  * `geodesicVariation_quadratic_baseJet_raw` — the raw bound
    `‖Y s τ − Y 0 τ − s·V τ‖ ≤ Cn·s²·e^K` (`Cn`, `K` carried as numbers), via
    `geodesicVariation_residual_bound` (the inhomogeneous Grönwall
    `norm_le_gronwallBound_of_norm_deriv_right_le`) applied at each `τ` with the Jacobi solution
    `J = s·V`.  This is `hbnd` lifted out of `geodesicVariation_exists`, generalised over `τ`.

  * `geodesicVariation_quadratic_baseJet_compact` — ★ THE BRICK: the same bound with a single
    compactness-internal constant `C ≥ 0` (absorbing `Cn = M₂·(‖(0,w)‖·e^{K₀})²` from the C² remainder
    discharge and `e^K` from the Jacobi-coefficient bound).  Carries ONLY the honest structural data:
    `S` convex + compact, the geodesic ODE `hYode`, the Jacobi solution `hVode`/`hV0`/`hIC`, and the
    flow tube containment `hmem` — exactly the carries of the J4-725 consumer wire
    `geodesicVariation_exists_uncond_compact`.

  * `geodesicVariation_quadratic_baseJet_closedBall` — cp466 witness: the brick at
    `Metric.closedBall c r`, matching the curved-witness closedBall pattern.

  All axiom-clean (std-3), no `sorry`, no new axioms.

  HONEST FIREWALL: this is J3 REGULARITY infrastructure — the quadratic base-jet feeding the MVI.  It
  is NOT the heat-kernel coefficient `a₁ = R/6` (which remains a labelled carrier); it does NOT build
  the second-order Jacobi equation (L2), Raychaudhuri (L3), the small-window MVI contraction itself, or
  numerical `G`.  `hmem` (tube containment) stays CARRIED — see the file-end note on why the short-time
  escape-time a-priori is not derivable from `hYode` alone.
-/
import Mathlib
import QIQTH.ExpMap
import QIQTH.GeodesicSmoothDep
import QIQTH.GeodesicVariationCompact

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic

variable {n : ℕ}

/-- **J3 brick 4 (raw) — the quadratic base-jet residual bound, uniform in `τ ∈ [0,1]`.**  For a
    one-parameter family `Y` of geodesics with base velocity perturbed linearly
    (`Y s 0 − Y 0 0 = s·(0,w)`) and a Jacobi solution `V` along the base geodesic with `V 0 = (0,w)`,
    if the Jacobi coefficient is bounded (`‖DF(Y 0 τ)‖ ≤ K`) and the field obeys the uniform quadratic
    Taylor remainder (`‖F(Y s ·) − F(Y 0 ·) − DF(Y 0 ·)(Y s · − Y 0 ·)‖ ≤ Cn·s²`), then the residual
    `ρ s τ := Y s τ − Y 0 τ − s·V τ` satisfies `‖ρ s τ‖ ≤ Cn·s²·e^K` for ALL `τ ∈ [0,1]`.

    This is exactly the intermediate `hbnd` of `geodesicVariation_exists`, lifted out as a standalone
    brick and generalised from a fixed time `t` to all `τ ∈ [0,1]`.  Proof: at each `τ`, `J = s·V` is a
    Jacobi solution with `J 0 = s·(0,w) = Y s 0 − Y 0 0`, so `geodesicVariation_residual_bound` (the
    inhomogeneous Grönwall, with `C = Cn·s²`) gives the bound. -/
theorem geodesicVariation_quadratic_baseJet_raw (g gi : Point n → Fin n → Fin n → ℝ)
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {w : Point n}
    {K Cn : ℝ} (hK0 : 0 ≤ K) (hCn0 : 0 ≤ Cn)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((0, w) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hNb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ)‖ ≤ Cn * s ^ 2) :
    ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖Y s τ - Y 0 τ - s • V τ‖ ≤ Cn * s ^ 2 * Real.exp K := by
  intro s τ hτ
  -- `J = s·V` is a Jacobi solution along the base geodesic (linearity of `DF`).
  have hJ : ∀ σ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun ξ => s • V ξ)
        (fderiv ℝ (geodesicField g gi) (Y 0 σ) ((fun ξ => s • V ξ) σ)) σ := by
    intro σ hσ
    have hcs := (hVode σ hσ).const_smul s
    have he : s • fderiv ℝ (geodesicField g gi) (Y 0 σ) (V σ)
        = fderiv ℝ (geodesicField g gi) (Y 0 σ) (s • V σ) :=
      (map_smul (fderiv ℝ (geodesicField g gi) (Y 0 σ)) s (V σ)).symm
    rw [he] at hcs
    exact hcs
  -- residual vanishes at the base point (linear IC perturbation matches `V 0`).
  have h0 : Y s 0 - Y 0 0 - (fun ξ => s • V ξ) 0 = 0 := by
    simp only
    rw [hIC s, hV0]; abel
  -- the inhomogeneous Grönwall with `C = Cn·s²`.
  have hbnd := geodesicVariation_residual_bound g gi hK0
    (mul_nonneg hCn0 (sq_nonneg s)) (hYode 0) (hYode s) hJ h0 hKb (hNb s) τ hτ
  simpa using hbnd

/-- **★ J3 brick 4 — the quadratic base-jet with all constants produced by compactness.**  On a convex
    compact region `S`, the second-order control of the geodesic variation in the base parameter:
    there is a single compactness-internal constant `C ≥ 0` with
    `‖Y s τ − Y 0 τ − s·V τ‖ ≤ C·s²` for all `s` and all `τ ∈ [0,1]`.

    `C = Cn·e^K` where `Cn = M₂·(‖(0,w)‖·e^{K₀})²` (the C²-remainder discharge constant) and `K` is the
    Jacobi-coefficient bound — both produced by compactness of `S` via the J4-724/725 engines
    (`geodesicField_snd_fderiv_bddOn_compact`, `geodesicField_lipschitzOnWith_compact`,
    `geodesicField_fst_fderiv_bddOn_compact`).  The carried data is exactly that of the consumer wire
    `geodesicVariation_exists_uncond_compact`: `S` convex + compact, the geodesic ODE `hYode`, the
    supplied Jacobi solution `hVode`/`hV0`/`hIC`, and the flow tube containment `hmem`.

    This is the direct feeder of the `hflowData` small-window MVI (the J3 contraction step). -/
theorem geodesicVariation_quadratic_baseJet_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {w : Point n}
    {S : Set (Point n × Point n)} (hconv : Convex ℝ S) (hcomp : IsCompact S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((0, w) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖Y s τ - Y 0 τ - s • V τ‖ ≤ C * s ^ 2 := by
  -- `hbound2` — field C² sup bound, produced by compactness (banked engine).
  obtain ⟨M₂, hM₂0, hbound2⟩ := geodesicField_snd_fderiv_bddOn_compact g gi hC hcomp
  -- `hLip` — field Lipschitz on `S`, produced by compactness (J4-725 brick (1)).
  obtain ⟨K₀, hLip⟩ := geodesicField_lipschitzOnWith_compact g gi hC hconv hcomp
  -- `hKb`/`hK0` — Jacobi-coefficient bound, produced by compactness + base-trajectory containment.
  obtain ⟨K, hK0, hKbnd⟩ := geodesicField_fst_fderiv_bddOn_compact g gi hC hcomp
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K :=
    fun τ hτ => hKbnd (Y 0 τ) (hmem 0 τ hτ)
  -- `Cn` — the C²-remainder discharge constant (`geodesicVariation_hNb_discharge`).
  set Cn := M₂ * (‖((0, w) : Point n × Point n)‖ * Real.exp K₀) ^ 2 with hCndef
  have hCn0 : 0 ≤ Cn := mul_nonneg hM₂0 (sq_nonneg _)
  have hNb := geodesicVariation_hNb_discharge g gi hC hconv hbound2 hLip hYode hIC hmem
  refine ⟨Cn * Real.exp K, mul_nonneg hCn0 (Real.exp_pos K).le, ?_⟩
  intro s τ hτ
  have hraw := geodesicVariation_quadratic_baseJet_raw g gi hK0 hCn0
    hYode hVode hV0 hIC hKb hNb s τ hτ
  -- reassociate `Cn·s²·e^K = (Cn·e^K)·s²`.
  calc ‖Y s τ - Y 0 τ - s • V τ‖ ≤ Cn * s ^ 2 * Real.exp K := hraw
    _ = Cn * Real.exp K * s ^ 2 := by ring

/-- **cp466 witness — the quadratic base-jet at a closed-ball region.**  Instantiates
    `geodesicVariation_quadratic_baseJet_compact` at the convex compact `Metric.closedBall c r` in the
    finite-dimensional state space `Point n × Point n`, matching the curved-witness closedBall pattern.
    All constants are produced by compactness of the ball; the carried data is the geodesic ODE, the
    supplied Jacobi solution, and the flow tube containment in the ball. -/
theorem geodesicVariation_quadratic_baseJet_closedBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {w : Point n}
    (c : Point n × Point n) (r : ℝ)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((0, w) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ Metric.closedBall c r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖Y s τ - Y 0 τ - s • V τ‖ ≤ C * s ^ 2 :=
  geodesicVariation_quadratic_baseJet_compact g gi hC (convex_closedBall c r)
    (isCompact_closedBall c r) hYode hVode hV0 hIC hmem

end QIQTH.ExpMap
