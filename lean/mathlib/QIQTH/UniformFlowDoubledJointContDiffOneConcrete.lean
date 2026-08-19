/-
  UniformFlowDoubledJointContDiffOneConcrete — the JOINT `ContDiffOn ℝ 1` (neighborhood-quality C¹) of
  the concrete confined DOUBLED geodesic-flow endpoint `fun Ξ => W Ξ 1` on the doubled phase space
  `E := (Point n × Point n) × (Point n × Point n)`, assembled from the base-point second-order Fréchet
  derivative (`GeodesicJointSecondFDerivAtPointLocal`, J4-850) + the doubled Task-B
  Lipschitz-in-base-point continuity (`GeodesicJointSecondFDerivLipschitz`, J4-852) over a FIXED uniform
  control set.  This is the plan `tranquil-stargazing-fox.md` Task-D step (b): the SECOND-order analogue
  of J4-849's first-order milestone `uniformFlow_joint_contDiffOn_one`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DELIVERABLE — plan Task-D step (b), the doubled analogue of J4-849.

  * `uniformFlow_doubled_joint_contDiffOn_one_witness` — ★ with `K := Metric.closedBall q₀ 1`, base
    state `Ξ₀ := ((q₀,0),(a₀,b₀))` (ARBITRARY, in particular NONZERO, reference Jacobi seed `(a₀,b₀)`),
    the concrete confined uniform DOUBLED flow `W Ξ τ = (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ,
    Jsel Ξ.1 Ξ.2 τ)` (`Jsel` = the pad-continuous per-`(base,seed)` Jacobi field) has its endpoint
        `fun Ξ => W Ξ 1`
    jointly `ContDiffOn ℝ 1` on a genuine neighborhood `Metric.ball Ξ₀ r` (`r > 0`), for EVERY (curved)
    `g, gi`, with NO carried domain hypotheses.  Equivalently: the doubled flow's FIRST derivative
    (= the base geodesic flow's SECOND derivative) is itself `C¹` on a neighborhood — the
    NEIGHBORHOOD-quality (not merely pointwise, J4-850/851) second-order regularity.

  ## METHOD — the exact order-up mirror of `uniformFlow_joint_contDiffOn_one` (J4-849).
  A single fixed control set `S := S₁ ×ˢ S₂` (base ball × Jacobi ball) contains every confined doubled
  curve `W Ξ` whose base state lies within `δ := min 1 ρ` of `Ξ₀` (confinement + triangle + the
  homogeneous Jacobi growth bound), so the doubled Lipschitz moduli `Kg, Lg` of `doubledField` /
  `fderiv (doubledField)` and the coefficient bound `Kbd` on `S` are FIXED.  Then:
    * DifferentiableOn: the base-point second-order Fréchet derivative
      `doubledFlow_endpoint_joint_hasFDerivAt_exists_atPoint` (J4-850) at each `x ∈ ball Ξ₀ r`
      (windowed `‖Ξ − x‖ ≤ σ`, `σ := δ/2`);
    * ContinuousOn of `fderiv f`: `fderiv f x = L(x)` (`HasFDerivAt.fderiv`), and `x ↦ L(x)` is
      `C`-Lipschitz on the ball by `doubledFlow_joint_fderiv_lipschitz_in_basepoint` (J4-852) with the
      FIXED uniform moduli from `S`;
    * assemble via `contDiffOn_succ_iff_fderiv_of_isOpen` (`isOpen_ball`) + `contDiffOn_zero`.

  ## WHAT THIS FILE DOES NOT DO.
  NOT the finite-basis transfer to `ContDiffOn ℝ 2` of the BASE flow `uniformFlowExp` (Task-D step (c)),
  NOT the final `ContDiffOn ℝ 2` assembly (step (d)), NOT the IFT inverse (Task E/F), NOT discharge the
  RNC hypotheses (Task G), and does NOT bear on `hCConv`.  a₁=R/6 remains CONDITIONAL on
  {hDuhamel, hDConv, hCConv}.
-/
import Mathlib
import QIQTH.GeodesicJointSecondFDerivAtPointLocal
import QIQTH.GeodesicJointSecondFDerivLipschitz
import QIQTH.GeodesicJointFDerivLipschitz
import QIQTH.DoubledFamilyFullSupply
import QIQTH.DoubledVariationField
import QIQTH.DoubledFamilyConstruction
import QIQTH.UniformFlowNondeg
import QIQTH.BoundedGeometry

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★ Joint `ContDiffOn ℝ 1` of the concrete uniform DOUBLED geodesic-flow endpoint on a
    neighborhood of `Ξ₀ := ((q₀,0),(a₀,b₀))`.**  Plan Task-D step (b), reached in the curved-admissible
    case, with NO carried domain hypotheses (`K := Metric.closedBall q₀ 1`).  Delivers a fixed doubled
    family `W` (the confined uniform doubled flow) with the doubled ODE property on the admissibility
    window, whose endpoint `fun Ξ => W Ξ 1` is jointly `ContDiffOn ℝ 1` on `Metric.ball Ξ₀ r`. -/
theorem uniformFlow_doubled_joint_contDiffOn_one_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ a₀ b₀ : Point n) :
    ∃ (r : ℝ), 0 < r ∧
      ∃ (W : ((Point n × Point n) × (Point n × Point n)) → ℝ →
            ((Point n × Point n) × (Point n × Point n))),
        (∀ Ξ : (Point n × Point n) × (Point n × Point n),
          ‖Ξ - ((((q₀, 0), (a₀, b₀))) : (Point n × Point n) × (Point n × Point n))‖
              ≤ min 1 (uniformFlowRadius g gi hC (isCompact_closedBall q₀ 1)) →
            ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W Ξ) (doubledField g gi (W Ξ τ)) τ) ∧
        ContDiffOn ℝ 1 (fun Ξ => W Ξ 1)
          (Metric.ball ((((q₀, 0), (a₀, b₀))) : (Point n × Point n) × (Point n × Point n)) r) := by
  classical
  set hK : IsCompact (Metric.closedBall q₀ 1) := isCompact_closedBall q₀ 1 with hKdef
  set K : Set (Point n) := Metric.closedBall q₀ 1 with hKsetdef
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρpos : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hC₀0 : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  set Ξ₀ : (Point n × Point n) × (Point n × Point n) := ((q₀, 0), (a₀, b₀)) with hΞ₀def
  set M₀ : ℝ := ‖((a₀, b₀) : Point n × Point n)‖ with hM₀def
  have hM₀0 : 0 ≤ M₀ := norm_nonneg _
  -- master admissibility bound `δ`, ball radius `r`, per-point window `σ` (all `δ/2`).
  set δ : ℝ := min 1 ρ with hδdef
  have hδpos : 0 < δ := lt_min zero_lt_one hρpos
  set r : ℝ := δ / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  set σ : ℝ := δ / 2 with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; linarith
  have hq₀K : q₀ ∈ K := by rw [hKsetdef]; exact Metric.mem_closedBall_self zero_le_one
  have h0v : ‖(0 : Point n)‖ ≤ ρ := by rw [norm_zero]; exact hρpos.le
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (A) per-`(base,seed)` Jacobi families along the concrete tubes, WITH padded continuity.
  have hJselExists : ∀ (p : Point n × Point n) (w : Point n × Point n),
      ∃ J : ℝ → Point n × Point n, J 0 = w ∧
        (p.1 ∈ K → ‖p.2‖ ≤ ρ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt J
            (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK p.1 p.2 τ) (J τ)) τ) ∧
        (p.1 ∈ K → ‖p.2‖ ≤ ρ →
          ContinuousOn J (Set.Icc (-(1/2) : ℝ) (3/2))) := by
    intro p w
    by_cases hadm : p.1 ∈ K ∧ ‖p.2‖ ≤ ρ
    · have hcont : ContinuousOn (uniformFlowTube g gi hC hK p.1 p.2)
          (Set.Icc (-(1/2) : ℝ) (3/2)) := by
        intro τ hτ
        have hτIoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        exact (uniformFlowTube_spec_ode g gi hC hK p.1 hadm.1 p.2 hadm.2 τ
          hτIoo).continuousAt.continuousWithinAt
      obtain ⟨J, hJ0, hJd, hJcont⟩ :=
        geodesicJacobi_narrowpad_continuousOn g gi hC (uniformFlowTube g gi hC hK p.1 p.2) hcont w
      exact ⟨J, hJ0, fun _ _ => hJd, fun _ _ => hJcont⟩
    · exact ⟨fun _ => w, rfl, fun h1 h2 => absurd ⟨h1, h2⟩ hadm,
        fun h1 h2 => absurd ⟨h1, h2⟩ hadm⟩
  choose Jsel hJsel0 hJselode hJselcont using hJselExists
  -- the concrete perturbed doubled family (fixed function of `Ξ`).
  set W : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n)) :=
    fun Ξ τ => (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ, Jsel Ξ.1 Ξ.2 τ) with hWdef
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- window admissibility over `‖Ξ - Ξ₀‖ ≤ δ`.
  have hbaseK : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ → Ξ.1.1 ∈ K := by
    intro Ξ hΞ
    have h1 : dist Ξ.1.1 q₀ ≤ ‖Ξ - Ξ₀‖ := by
      calc dist Ξ.1.1 q₀ ≤ dist Ξ.1 Ξ₀.1 := by rw [Prod.dist_eq]; exact le_max_left _ _
        _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_left _ _
        _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
    rw [hKsetdef, Metric.mem_closedBall]
    calc dist Ξ.1.1 q₀ ≤ δ := le_trans h1 hΞ
      _ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hvelρ : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ → ‖Ξ.1.2‖ ≤ ρ := by
    intro Ξ hΞ
    have h1 : ‖Ξ.1.2‖ ≤ ‖Ξ - Ξ₀‖ := by
      calc ‖Ξ.1.2‖ = dist Ξ.1.2 Ξ₀.1.2 := by rw [hΞ₀def]; simp [dist_eq_norm]
        _ ≤ dist Ξ.1 Ξ₀.1 := by rw [Prod.dist_eq]; exact le_max_right _ _
        _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_left _ _
        _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
    calc ‖Ξ.1.2‖ ≤ δ := le_trans h1 hΞ
      _ ≤ ρ := by rw [hδdef]; exact min_le_right _ _
  have hvelδ : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ → ‖Ξ.1.2‖ ≤ δ := by
    intro Ξ hΞ
    calc ‖Ξ.1.2‖ = dist Ξ.1.2 Ξ₀.1.2 := by rw [hΞ₀def]; simp [dist_eq_norm]
      _ ≤ dist Ξ.1 Ξ₀.1 := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
      _ ≤ δ := hΞ
  have hbasedist : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ →
      dist Ξ.1.1 q₀ ≤ δ := by
    intro Ξ hΞ
    calc dist Ξ.1.1 q₀ ≤ dist Ξ.1 Ξ₀.1 := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
      _ ≤ δ := hΞ
  have hseednorm : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ →
      ‖Ξ.2‖ ≤ M₀ + δ := by
    intro Ξ hΞ
    have hz : Ξ₀.2 = ((a₀, b₀) : Point n × Point n) := rfl
    have hd : ‖Ξ.2 - ((a₀, b₀) : Point n × Point n)‖ ≤ δ := by
      calc ‖Ξ.2 - ((a₀, b₀) : Point n × Point n)‖ = dist Ξ.2 Ξ₀.2 := by rw [hz, dist_eq_norm]
        _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_right _ _
        _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
        _ ≤ δ := hΞ
    calc ‖Ξ.2‖ = ‖(Ξ.2 - ((a₀, b₀) : Point n × Point n)) + ((a₀, b₀) : Point n × Point n)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖Ξ.2 - ((a₀, b₀) : Point n × Point n)‖ + M₀ := by rw [hM₀def]; exact norm_add_le _ _
      _ ≤ δ + M₀ := by linarith [hd]
      _ = M₀ + δ := by ring
  -- window points around a base point `x ∈ ball Ξ₀ r` are admissible (`‖Ξ - Ξ₀‖ ≤ δ`).
  have hwin : ∀ x : (Point n × Point n) × (Point n × Point n), x ∈ Metric.ball Ξ₀ r →
      ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - x‖ ≤ σ → ‖Ξ - Ξ₀‖ ≤ δ := by
    intro x hx Ξ hΞx
    have hxdist : dist x Ξ₀ < r := by rwa [Metric.mem_ball] at hx
    have hxnorm : ‖x - Ξ₀‖ < r := by rwa [dist_eq_norm] at hxdist
    calc ‖Ξ - Ξ₀‖ = ‖(Ξ - x) + (x - Ξ₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖Ξ - x‖ + ‖x - Ξ₀‖ := norm_add_le _ _
      _ ≤ σ + r := by linarith
      _ = δ := by rw [hσdef, hrdef]; ring
  have hballadm : ∀ x : (Point n × Point n) × (Point n × Point n), x ∈ Metric.ball Ξ₀ r →
      ‖x - Ξ₀‖ ≤ δ := by
    intro x hx
    have hxdist : dist x Ξ₀ < r := by rwa [Metric.mem_ball] at hx
    have hxnorm : ‖x - Ξ₀‖ < r := by rwa [dist_eq_norm] at hxdist
    have : r ≤ δ := by rw [hrdef]; linarith
    linarith
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (B) the compact convex control set `S = S₁ ×ˢ S₂`.
  set R₁ : ℝ := C₀ * δ + δ with hR₁def
  have hR₁0 : 0 ≤ R₁ := by rw [hR₁def]; positivity
  set S₁ : Set (Point n × Point n) := Metric.closedBall ((q₀, 0) : Point n × Point n) R₁ with hS₁def
  have hS₁comp : IsCompact S₁ := by rw [hS₁def]; exact isCompact_closedBall _ _
  have hS₁conv : Convex ℝ S₁ := by rw [hS₁def]; exact convex_closedBall _ _
  have htubeS₁ : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s ∈ S₁ := by
    intro Ξ hΞ s hs
    have hqK : Ξ.1.1 ∈ K := hbaseK Ξ hΞ
    have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ Ξ hΞ
    have hvδ : ‖Ξ.1.2‖ ≤ δ := hvelδ Ξ hΞ
    have hbd : dist Ξ.1.1 q₀ ≤ δ := hbasedist Ξ hΞ
    rw [hS₁def, Metric.mem_closedBall]
    have hconf := uniformFlowTube_spec_conf g gi hC hK Ξ.1.1 hqK Ξ.1.2 hvρ s hs
    calc dist (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s) ((q₀, 0) : Point n × Point n)
        ≤ dist (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s) ((Ξ.1.1, 0) : Point n × Point n)
            + dist ((Ξ.1.1, 0) : Point n × Point n) ((q₀, 0) : Point n × Point n) :=
          dist_triangle _ _ _
      _ ≤ C₀ * δ + δ := by
          apply add_le_add
          · rw [dist_eq_norm]
            calc ‖uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s - ((Ξ.1.1, 0) : Point n × Point n)‖
                ≤ C₀ * ‖Ξ.1.2‖ := hconf
              _ ≤ C₀ * δ := mul_le_mul_of_nonneg_left hvδ hC₀0
          · rw [Prod.dist_eq]
            refine max_le hbd ?_
            show dist (0 : Point n) (0 : Point n) ≤ δ
            rw [dist_self]; exact hδpos.le
      _ = R₁ := by rw [hR₁def]
  obtain ⟨Kb, hKb0, hKbbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hS₁comp
  set R₂ : ℝ := (M₀ + δ) * Real.exp Kb with hR₂def
  have hR₂0 : 0 ≤ R₂ := by rw [hR₂def]; positivity
  set S₂ : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) R₂ with hS₂def
  have hS₂comp : IsCompact S₂ := by rw [hS₂def]; exact isCompact_closedBall _ _
  have hS₂conv : Convex ℝ S₂ := by rw [hS₂def]; exact convex_closedBall _ _
  set S : Set ((Point n × Point n) × (Point n × Point n)) := S₁ ×ˢ S₂ with hSdef
  have hScomp : IsCompact S := by rw [hSdef]; exact hS₁comp.prod hS₂comp
  have hSconv : Convex ℝ S := by rw [hSdef]; exact hS₁conv.prod hS₂conv
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (C) global doubled ODE / initial-condition / confinement for `W` over the admissibility window.
  have hWode_glob : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W Ξ) (doubledField g gi (W Ξ τ)) τ := by
    intro Ξ hΞ τ hτ
    have hqK : Ξ.1.1 ∈ K := hbaseK Ξ hΞ
    have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ Ξ hΞ
    have hP : HasDerivAt (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2)
        (geodesicField g gi (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ)) τ :=
      uniformFlowTube_spec_ode g gi hC hK Ξ.1.1 hqK Ξ.1.2 hvρ τ
        ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hJ : HasDerivAt (Jsel Ξ.1 Ξ.2)
        (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ)
          (Jsel Ξ.1 Ξ.2 τ)) τ :=
      hJselode Ξ.1 Ξ.2 hqK hvρ τ hτ
    exact doubledField_prod_hasDerivAt g gi hP hJ
  have hWzero : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ → W Ξ 0 = Ξ := by
    intro Ξ hΞ
    have hqK : Ξ.1.1 ∈ K := hbaseK Ξ hΞ
    have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ Ξ hΞ
    have h1 : uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 0 = Ξ.1 :=
      uniformFlowTube_spec_ic g gi hC hK Ξ.1.1 hqK Ξ.1.2 hvρ
    have h2 : Jsel Ξ.1 Ξ.2 0 = Ξ.2 := hJsel0 Ξ.1 Ξ.2
    show (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 0, Jsel Ξ.1 Ξ.2 0) = Ξ
    rw [h1, h2]
  have hmem_glob : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, W Ξ τ ∈ S := by
    intro Ξ hΞ τ hτ
    have hqK : Ξ.1.1 ∈ K := hbaseK Ξ hΞ
    have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ Ξ hΞ
    have hsδ : ‖Ξ.2‖ ≤ M₀ + δ := hseednorm Ξ hΞ
    have hmem1 : uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ ∈ S₁ := htubeS₁ Ξ hΞ τ hτ
    have hmem2 : Jsel Ξ.1 Ξ.2 τ ∈ S₂ := by
      rw [hS₂def, Metric.mem_closedBall, dist_zero_right]
      have hJode := hJselode Ξ.1 Ξ.2 hqK hvρ
      have hKbtube : ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s)‖ ≤ Kb :=
        fun s hs => hKbbd _ (htubeS₁ Ξ hΞ s hs)
      have hgrow := jacobi_field_norm_bound hKb0 hJode hKbtube τ hτ
      rw [hJsel0 Ξ.1 Ξ.2] at hgrow
      calc ‖Jsel Ξ.1 Ξ.2 τ‖ ≤ ‖Ξ.2‖ * Real.exp Kb := hgrow
        _ ≤ (M₀ + δ) * Real.exp Kb := by
            apply mul_le_mul_of_nonneg_right hsδ (Real.exp_pos _).le
        _ = R₂ := by rw [hR₂def]
    rw [hSdef, hWdef]
    exact Set.mk_mem_prod hmem1 hmem2
  -- pad continuity of the reference doubled curve `W x` for an admissible base state `x`.
  have hWcont : ∀ x : (Point n × Point n) × (Point n × Point n), ‖x - Ξ₀‖ ≤ δ →
      ContinuousOn (W x) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro x hx
    have hqK : x.1.1 ∈ K := hbaseK x hx
    have hvρ : ‖x.1.2‖ ≤ ρ := hvelρ x hx
    rw [hWdef]
    simp only
    refine ContinuousOn.prodMk ?_ ?_
    · intro τ hτ
      have hτIoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      exact (uniformFlowTube_spec_ode g gi hC hK x.1.1 hqK x.1.2 hvρ τ
        hτIoo).continuousAt.continuousWithinAt
    · exact hJselcont x.1 x.2 hqK hvρ
  -- the doubled coefficient operator along `W x` is pad-continuous.
  have hAcont : ∀ x : (Point n × Point n) × (Point n × Point n), ‖x - Ξ₀‖ ≤ δ →
      ContinuousOn (fun τ => fderiv ℝ (doubledField g gi) (W x τ)) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro x hx
    have hcd : Continuous (fderiv ℝ (doubledField g gi)) :=
      (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
    exact hcd.comp_continuousOn (hWcont x hx)
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (D) per-base-point second-order Fréchet derivative data (with the doubled-Jacobi block `V`).
  set f : ((Point n × Point n) × (Point n × Point n)) → ((Point n × Point n) × (Point n × Point n)) :=
    fun Ξ => W Ξ 1 with hfdef
  have hdata : ∀ x ∈ Metric.ball Ξ₀ r,
      ∃ (V : ((Point n × Point n) × (Point n × Point n)) → ℝ →
          ((Point n × Point n) × (Point n × Point n)))
        (L : ((Point n × Point n) × (Point n × Point n)) →L[ℝ]
          ((Point n × Point n) × (Point n × Point n))),
        (∀ Ξ : (Point n × Point n) × (Point n × Point n), V Ξ 0 = Ξ) ∧
        (∀ Ξ : (Point n × Point n) × (Point n × Point n), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (V Ξ)
            (fderiv ℝ (doubledField g gi) (W x τ) (V Ξ τ)) τ) ∧
        (∀ Ξ : (Point n × Point n) × (Point n × Point n), L Ξ = V Ξ 1) ∧
        HasFDerivAt f L x := by
    intro x hx
    have hxadm : ‖x - Ξ₀‖ ≤ δ := hballadm x hx
    -- build the doubled-Jacobi block `V` along the pad-continuous reference `W x`.
    have hVExists : ∀ Ξ : (Point n × Point n) × (Point n × Point n),
        ∃ J : ℝ → (Point n × Point n) × (Point n × Point n), J 0 = Ξ ∧
          ∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt J (fderiv ℝ (doubledField g gi) (W x τ) (J τ)) τ :=
      fun Ξ => linODE_exists_hasDerivAt_Icc_narrow
        (fun τ => fderiv ℝ (doubledField g gi) (W x τ)) (hAcont x hxadm) Ξ
    choose V hV0 hVode using hVExists
    -- windowed hypotheses around the base point `x`.
    have hWode_x : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - x‖ ≤ σ →
        ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W Ξ) (doubledField g gi (W Ξ τ)) τ :=
      fun Ξ hΞ τ hτ => hWode_glob Ξ (hwin x hx Ξ hΞ) τ hτ
    have hIC_x : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - x‖ ≤ σ →
        W Ξ 0 - W x 0 = Ξ - x := by
      intro Ξ hΞ
      rw [hWzero Ξ (hwin x hx Ξ hΞ), hWzero x hxadm]
    have hmem_x : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - x‖ ≤ σ →
        ∀ τ ∈ Set.Icc (0 : ℝ) 1, W Ξ τ ∈ S :=
      fun Ξ hΞ τ hτ => hmem_glob Ξ (hwin x hx Ξ hΞ) τ hτ
    obtain ⟨L, hLeq, hFD⟩ :=
      doubledFlow_endpoint_joint_hasFDerivAt_exists_atPoint g gi hC x hScomp hSconv hσpos
        (Set.right_mem_Icc.mpr zero_le_one) hWode_x hVode hV0 hIC_x hmem_x
    exact ⟨V, L, hV0, hVode, hLeq, hFD⟩
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (E) assemble `ContDiffOn ℝ 1` on `ball Ξ₀ r`.
  -- (1) differentiability.
  have hdiff : DifferentiableOn ℝ f (Metric.ball Ξ₀ r) := by
    intro x hx
    obtain ⟨_V, _L, _, _, _, hFD⟩ := hdata x hx
    exact hFD.differentiableAt.differentiableWithinAt
  -- fixed doubled Lipschitz moduli of `doubledField` and `fderiv (doubledField)` on `S`.
  obtain ⟨Kbd, hKbd0, hbd⟩ := doubledField_fderiv_bddOn_compact g gi hC hScomp
  obtain ⟨Kg, hLipg⟩ := doubledField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
  obtain ⟨Lg, hLip2⟩ := fderiv_doubledField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
  set C : ℝ := (Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; have : (0:ℝ) ≤ (Lg:ℝ) := NNReal.coe_nonneg Lg; positivity
  -- (2) Lipschitz continuity of `fderiv f` on the ball, via the doubled Task-B with uniform moduli.
  have hlipfderiv : LipschitzOnWith ⟨C, hC0⟩ (fderiv ℝ f) (Metric.ball Ξ₀ r) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    obtain ⟨Vx, Lx, hVx0, hVxode, hLxeq, hFDx⟩ := hdata x hx
    obtain ⟨Vy, Ly, hVy0, hVyode, hLyeq, hFDy⟩ := hdata y hy
    have hfx : fderiv ℝ f x = Lx := hFDx.fderiv
    have hfy : fderiv ℝ f y = Ly := hFDy.fderiv
    have hxadm : ‖x - Ξ₀‖ ≤ δ := hballadm x hx
    have hyadm : ‖y - Ξ₀‖ ≤ δ := hballadm y hy
    -- reference doubled geodesics solve the doubled ODE and stay in `S`.
    have hox : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (W x) (doubledField g gi (W x τ)) τ := hWode_glob x hxadm
    have hoy : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (W y) (doubledField g gi (W y τ)) τ := hWode_glob y hyadm
    have hSx : ∀ τ ∈ Set.Icc (0 : ℝ) 1, W x τ ∈ S := hmem_glob x hxadm
    have hSy : ∀ τ ∈ Set.Icc (0 : ℝ) 1, W y τ ∈ S := hmem_glob y hyadm
    have hbound := doubledFlow_joint_fderiv_lipschitz_in_basepoint g gi hLipg hLip2
      (Set.right_mem_Icc.mpr zero_le_one) hox hoy hSx hSy hKbd0
      (fun τ hτ => hbd _ (hSx τ hτ)) (fun τ hτ => hbd _ (hSy τ hτ))
      hVxode hVyode hVx0 hVy0 hLxeq hLyeq
    -- rewrite the reference initial points `W · 0 = base`.
    have hicx : W x 0 = x := hWzero x hxadm
    have hicy : W y 0 = y := hWzero y hyadm
    rw [hicx, hicy] at hbound
    rw [hfx, hfy, dist_eq_norm]
    calc ‖Lx - Ly‖
        ≤ (Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd * dist x y := hbound
      _ = (⟨C, hC0⟩ : ℝ≥0) * dist x y := by
          rw [show ((⟨C, hC0⟩ : ℝ≥0) : ℝ) = C from rfl, hCdef]
  have hcont : ContinuousOn (fderiv ℝ f) (Metric.ball Ξ₀ r) := hlipfderiv.continuousOn
  -- (3) assemble via the open-ball characterization.
  have h1eq : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
  refine ⟨r, hr, W, ?_, ?_⟩
  · exact fun Ξ hΞ τ hτ => hWode_glob Ξ hΞ τ hτ
  · rw [show (fun Ξ => W Ξ 1) = f from rfl, h1eq,
      contDiffOn_succ_iff_fderiv_of_isOpen (Metric.isOpen_ball)]
    refine ⟨hdiff, ?_, ?_⟩
    · intro h; exact absurd h (by simp)
    · rw [contDiffOn_zero]; exact hcont

end QIQTH.ExpMap
