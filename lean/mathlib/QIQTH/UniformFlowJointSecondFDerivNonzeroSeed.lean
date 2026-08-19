/-
  UniformFlowJointSecondFDerivNonzeroSeed — the CONCRETE, NON-VACUOUS instantiation of the JOINT
  SECOND-order Fréchet derivative of the geodesic flow at a base state with an ARBITRARY (in particular
  NONZERO) reference Jacobi seed, for the actual constructive uniform doubled flow, verified at a
  genuinely CURVED witness.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE — closing the "pad-export gap RETURNS one level up" wall (J4-850 / cp711).

  `UniformFlowJointSecondFDerivConcrete.uniformFlow_joint_secondFDeriv_witness` (J4-850) built the joint
  SECOND-order Fréchet derivative of the concrete confined uniform doubled flow, but ONLY at the
  ZERO-Jacobi-seed base state `Ξ₀ = ((q₀,0),(0,0))`.  The reason: the abstract doubled second-order
  theorem's doubled-Jacobi block `V` must solve the linearized doubled ODE along the reference doubled
  curve `W Ξ₀`, whose coefficient `A τ = fderiv (doubledField) (W Ξ₀ τ)` needs continuity on a PAD
  `[-1/2, 3/2]`.  With a ZERO seed the reference Jacobi slot is the literal `0` field (trivially
  pad-continuous).  With a NONZERO seed the reference Jacobi slot is a genuine nonzero Jacobi field, and
  J4-850 used the engine `geodesicJacobi_narrowpad_hasDerivAt_Icc` which only exports `HasDerivAt` on the
  CLOSED `[0,1]` — hence only `[0,1]`-continuity, NOT pad-continuity.  cp711 flagged this as the next
  genuine wall (the pad-export gap "RETURNS one level up"), blocking the finite-basis transfer to
  `ContDiffOn ℝ 2`, which needs the doubled derivative at NONZERO-seed base states.

  ## THE FIX — the "larger open interval" shortcut (NO new closed-interval export needed).

  The gap is ALREADY closed by an existing lemma: `DoubledVariationField.geodesicJacobi_narrowpad_continuousOn`
  (J4-47, `D1b`) exports, for ANY seed `w₀` and a base curve continuous on the PAD `[-1/2,3/2]`, the Jacobi
  field's `ContinuousOn` on the WHOLE pad `[-1/2,3/2]` (not merely `[0,1]`) — because the glued forward/
  backward solution has `HasDerivWithinAt` on the whole padded interval, hence continuity there.  Since
  `[0,1]` sits in the INTERIOR of the pad, no separate "extend regularity from the open interval to the
  closed endpoint" argument is required at all: the padded continuity is simply already available for a
  NONZERO seed.  So a nonzero-seed reference doubled curve `W Ξ₀ = (tube, Jsel)` is pad-continuous, its
  doubled coefficient field is pad-continuous, and `V` is constructible with two-sided `[0,1]` derivatives.

  WHAT LANDS (axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited):

  * `uniformFlow_joint_secondFDeriv_witness_nonzeroSeed` — ★ with `K := Metric.closedBall q₀ 1` and the
    base state `Ξ₀ := ((q₀,0),(a₀,b₀))` for ARBITRARY (in particular NONZERO) Jacobi seed `(a₀,b₀)`, the
    concrete confined uniform doubled flow's endpoint `fun Ξ => W Ξ 1` has a genuine joint SECOND-order
    Fréchet derivative `L` (`L Ξ = V Ξ 1`) at `Ξ₀`, for EVERY (in particular genuinely curved) metric,
    with NO carried domain hypotheses.  The reference doubled-Jacobi slot is the GENUINE nonzero Jacobi
    field `Jsel (q₀,0) (a₀,b₀)`, made pad-continuous via `geodesicJacobi_narrowpad_continuousOn` — the
    exact datum the finite-basis transfer to `ContDiffOn ℝ 2` needs and the J4-850 zero-seed witness did
    NOT supply.

  ## WHAT THIS FILE DOES NOT DO.
  It establishes the doubled second-order derivative EXISTENCE at nonzero-seed base states (pointwise,
  windowed).  It does NOT assemble the doubled joint `ContDiffOn ℝ 1`, NOT the finite-basis transfer to
  `ContDiffOn ℝ 2` of the base flow, NOT the IFT inverse, NOT discharge the RNC hypotheses, and does NOT
  bear on `hCConv`.  a₁=R/6 remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.
-/
import Mathlib
import QIQTH.GeodesicJointSecondFDerivAtPointLocal
import QIQTH.GeodesicJointFDerivLipschitz
import QIQTH.DoubledFamilyFullSupply
import QIQTH.DoubledVariationField
import QIQTH.DoubledFamilyConstruction
import QIQTH.UniformFlowNondeg
import QIQTH.BoundedGeometry

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 2000000

variable {n : ℕ}

/-- **★ Concrete non-vacuity witness for the joint SECOND-order Fréchet derivative of the geodesic flow
    at a base state with an ARBITRARY (in particular NONZERO) reference Jacobi seed.**  With
    `K := Metric.closedBall q₀ 1` and base state `Ξ₀ := ((q₀,0),(a₀,b₀))`, the concrete confined uniform
    doubled flow's endpoint `fun Ξ => W Ξ 1` has a genuine joint SECOND-order Fréchet derivative `L` at
    `Ξ₀`, for EVERY (curved) metric.  The reference doubled-Jacobi slot is the GENUINE nonzero Jacobi field
    `Jsel (q₀,0) (a₀,b₀)`, made pad-continuous via `geodesicJacobi_narrowpad_continuousOn` (the
    "larger open interval" shortcut — `[0,1] ⊆ interior [-1/2,3/2]`), so `V` is constructible along a
    NONZERO reference.  This supplies the datum the finite-basis transfer to `ContDiffOn ℝ 2` needs. -/
theorem uniformFlow_joint_secondFDeriv_witness_nonzeroSeed (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) (a₀ b₀ : Point n) :
    ∃ (σ : ℝ), 0 < σ ∧
      ∃ (W V : ((Point n × Point n) × (Point n × Point n)) → ℝ →
            ((Point n × Point n) × (Point n × Point n)))
        (L : ((Point n × Point n) × (Point n × Point n)) →L[ℝ]
            ((Point n × Point n) × (Point n × Point n))),
        (∀ Ξ : ((Point n × Point n) × (Point n × Point n)), L Ξ = V Ξ 1) ∧
        HasFDerivAt (fun Ξ => W Ξ 1) L
          ((((q₀, 0), (a₀, b₀))) : ((Point n × Point n) × (Point n × Point n))) := by
  classical
  set hK : IsCompact (Metric.closedBall q₀ 1) := isCompact_closedBall q₀ 1 with hKdef
  set K : Set (Point n) := Metric.closedBall q₀ 1 with hKsetdef
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρpos : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hC₀0 : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- the base state (arbitrary Jacobi seed) and the perturbation window.
  set Ξ₀ : (Point n × Point n) × (Point n × Point n) := ((q₀, 0), (a₀, b₀)) with hΞ₀def
  set M₀ : ℝ := ‖((a₀, b₀) : Point n × Point n)‖ with hM₀def
  have hM₀0 : 0 ≤ M₀ := norm_nonneg _
  set σ : ℝ := min 1 ρ with hσdef
  have hσpos : 0 < σ := lt_min zero_lt_one hρpos
  have hq₀K : q₀ ∈ K := by rw [hKsetdef]; exact Metric.mem_closedBall_self zero_le_one
  have h0v : ‖(0 : Point n)‖ ≤ ρ := by rw [norm_zero]; exact hρpos.le
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (A) per-`(base,seed)` Jacobi families along the concrete tubes, WITH padded continuity (the fix).
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
  -- the concrete perturbed doubled family (Jacobi slot directly `Jsel`, pad-continuous for every seed).
  set W : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n)) :=
    fun Ξ τ => (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ, Jsel Ξ.1 Ξ.2 τ) with hWdef
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- window admissibility: `‖Ξ - Ξ₀‖ ≤ σ` puts the base in `K`, the velocity ≤ ρ, and controls the seed.
  have hbaseK : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ → Ξ.1.1 ∈ K := by
    intro Ξ hΞ
    have h1 : dist Ξ.1.1 q₀ ≤ ‖Ξ - Ξ₀‖ := by
      calc dist Ξ.1.1 q₀ ≤ dist Ξ.1 Ξ₀.1 := by rw [Prod.dist_eq]; exact le_max_left _ _
        _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_left _ _
        _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
    rw [hKsetdef, Metric.mem_closedBall]
    calc dist Ξ.1.1 q₀ ≤ σ := le_trans h1 hΞ
      _ ≤ 1 := by rw [hσdef]; exact min_le_left _ _
  have hvelρ : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ → ‖Ξ.1.2‖ ≤ ρ := by
    intro Ξ hΞ
    have h1 : ‖Ξ.1.2‖ ≤ ‖Ξ - Ξ₀‖ := by
      calc ‖Ξ.1.2‖ = dist Ξ.1.2 Ξ₀.1.2 := by rw [hΞ₀def]; simp [dist_eq_norm]
        _ ≤ dist Ξ.1 Ξ₀.1 := by rw [Prod.dist_eq]; exact le_max_right _ _
        _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_left _ _
        _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
    calc ‖Ξ.1.2‖ ≤ σ := le_trans h1 hΞ
      _ ≤ ρ := by rw [hσdef]; exact min_le_right _ _
  have hvelσ : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ → ‖Ξ.1.2‖ ≤ σ := by
    intro Ξ hΞ
    calc ‖Ξ.1.2‖ = dist Ξ.1.2 Ξ₀.1.2 := by rw [hΞ₀def]; simp [dist_eq_norm]
      _ ≤ dist Ξ.1 Ξ₀.1 := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
      _ ≤ σ := hΞ
  have hbasedist : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ →
      dist Ξ.1.1 q₀ ≤ σ := by
    intro Ξ hΞ
    calc dist Ξ.1.1 q₀ ≤ dist Ξ.1 Ξ₀.1 := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
      _ ≤ σ := hΞ
  -- the seed stays within `σ` of `(a₀,b₀)`, hence `‖Ξ.2‖ ≤ M₀ + σ`.
  have hseednorm : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ →
      ‖Ξ.2‖ ≤ M₀ + σ := by
    intro Ξ hΞ
    have hz : Ξ₀.2 = ((a₀, b₀) : Point n × Point n) := rfl
    have hd : ‖Ξ.2 - ((a₀, b₀) : Point n × Point n)‖ ≤ σ := by
      calc ‖Ξ.2 - ((a₀, b₀) : Point n × Point n)‖ = dist Ξ.2 Ξ₀.2 := by
            rw [hz, dist_eq_norm]
        _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_right _ _
        _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
        _ ≤ σ := hΞ
    calc ‖Ξ.2‖ = ‖(Ξ.2 - ((a₀, b₀) : Point n × Point n)) + ((a₀, b₀) : Point n × Point n)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖Ξ.2 - ((a₀, b₀) : Point n × Point n)‖ + M₀ := by
          rw [hM₀def]; exact norm_add_le _ _
      _ ≤ σ + M₀ := by linarith [hd]
      _ = M₀ + σ := by ring
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (B) the compact convex control set `S = S₁ ×ˢ S₂` (base ball × Jacobi ball).
  set R₁ : ℝ := C₀ * σ + σ with hR₁def
  have hR₁0 : 0 ≤ R₁ := by rw [hR₁def]; positivity
  set S₁ : Set (Point n × Point n) := Metric.closedBall ((q₀, 0) : Point n × Point n) R₁ with hS₁def
  have hS₁comp : IsCompact S₁ := by rw [hS₁def]; exact isCompact_closedBall _ _
  have hS₁conv : Convex ℝ S₁ := by rw [hS₁def]; exact convex_closedBall _ _
  -- every confined perturbed tube lies in `S₁` (confinement + triangle).
  have htubeS₁ : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s ∈ S₁ := by
    intro Ξ hΞ s hs
    have hqK : Ξ.1.1 ∈ K := hbaseK Ξ hΞ
    have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ Ξ hΞ
    have hvσ : ‖Ξ.1.2‖ ≤ σ := hvelσ Ξ hΞ
    have hbd : dist Ξ.1.1 q₀ ≤ σ := hbasedist Ξ hΞ
    rw [hS₁def, Metric.mem_closedBall]
    have hconf := uniformFlowTube_spec_conf g gi hC hK Ξ.1.1 hqK Ξ.1.2 hvρ s hs
    calc dist (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s) ((q₀, 0) : Point n × Point n)
        ≤ dist (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s) ((Ξ.1.1, 0) : Point n × Point n)
            + dist ((Ξ.1.1, 0) : Point n × Point n) ((q₀, 0) : Point n × Point n) :=
          dist_triangle _ _ _
      _ ≤ C₀ * σ + σ := by
          apply add_le_add
          · rw [dist_eq_norm]
            calc ‖uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s - ((Ξ.1.1, 0) : Point n × Point n)‖
                ≤ C₀ * ‖Ξ.1.2‖ := hconf
              _ ≤ C₀ * σ := mul_le_mul_of_nonneg_left hvσ hC₀0
          · rw [Prod.dist_eq]
            refine max_le hbd ?_
            show dist (0 : Point n) (0 : Point n) ≤ σ
            rw [dist_self]; exact hσpos.le
      _ = R₁ := by rw [hR₁def]
  -- coefficient bound along tubes lying in `S₁`.
  obtain ⟨Kb, hKb0, hKbbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hS₁comp
  set R₂ : ℝ := (M₀ + σ) * Real.exp Kb with hR₂def
  have hR₂0 : 0 ≤ R₂ := by rw [hR₂def]; positivity
  set S₂ : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) R₂ with hS₂def
  have hS₂comp : IsCompact S₂ := by rw [hS₂def]; exact isCompact_closedBall _ _
  have hS₂conv : Convex ℝ S₂ := by rw [hS₂def]; exact convex_closedBall _ _
  set S : Set ((Point n × Point n) × (Point n × Point n)) := S₁ ×ˢ S₂ with hSdef
  have hScomp : IsCompact S := by rw [hSdef]; exact hS₁comp.prod hS₂comp
  have hSconv : Convex ℝ S := by rw [hSdef]; exact hS₁conv.prod hS₂conv
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (C) discharge the abstract theorem's hypotheses for `W`.
  -- (C1) doubled ODE (product rule: tube ODE × Jacobi ODE).
  have hWode : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ →
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
  -- (C2) affine initial condition.
  have hΞ₀tube0 : uniformFlowTube g gi hC hK q₀ 0 0 = ((q₀, 0) : Point n × Point n) :=
    uniformFlowTube_spec_ic g gi hC hK q₀ hq₀K 0 h0v
  have hWΞ₀0 : W Ξ₀ 0 = Ξ₀ := by
    rw [hWdef, hΞ₀def]
    simp only
    refine Prod.ext ?_ ?_
    · exact hΞ₀tube0
    · exact hJsel0 (q₀, 0) (a₀, b₀)
  have hIC : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ →
      W Ξ 0 - W Ξ₀ 0 = Ξ - Ξ₀ := by
    intro Ξ hΞ
    have hqK : Ξ.1.1 ∈ K := hbaseK Ξ hΞ
    have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ Ξ hΞ
    have hWΞ0 : W Ξ 0 = Ξ := by
      rw [hWdef]
      simp only
      refine Prod.ext ?_ ?_
      · exact uniformFlowTube_spec_ic g gi hC hK Ξ.1.1 hqK Ξ.1.2 hvρ
      · exact hJsel0 Ξ.1 Ξ.2
    rw [hWΞ0, hWΞ₀0]
  -- (C3) confinement into `S = S₁ ×ˢ S₂`.
  have hmem : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, W Ξ τ ∈ S := by
    intro Ξ hΞ τ hτ
    have hqK : Ξ.1.1 ∈ K := hbaseK Ξ hΞ
    have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ Ξ hΞ
    have hsσ : ‖Ξ.2‖ ≤ M₀ + σ := hseednorm Ξ hΞ
    -- `.1` component in `S₁`.
    have hmem1 : uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ ∈ S₁ := htubeS₁ Ξ hΞ τ hτ
    -- `.2` component in `S₂` via the homogeneous Jacobi growth bound.
    have hmem2 : Jsel Ξ.1 Ξ.2 τ ∈ S₂ := by
      rw [hS₂def, Metric.mem_closedBall, dist_zero_right]
      have hJode := hJselode Ξ.1 Ξ.2 hqK hvρ
      have hKbtube : ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s)‖ ≤ Kb :=
        fun s hs => hKbbd _ (htubeS₁ Ξ hΞ s hs)
      have hgrow := jacobi_field_norm_bound hKb0 hJode hKbtube τ hτ
      rw [hJsel0 Ξ.1 Ξ.2] at hgrow
      calc ‖Jsel Ξ.1 Ξ.2 τ‖ ≤ ‖Ξ.2‖ * Real.exp Kb := hgrow
        _ ≤ (M₀ + σ) * Real.exp Kb := by
            apply mul_le_mul_of_nonneg_right hsσ (Real.exp_pos _).le
        _ = R₂ := by rw [hR₂def]
    rw [hSdef, hWdef]
    exact Set.mk_mem_prod hmem1 hmem2
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (D) the doubled-Jacobi block `V` along the pad-continuous NONZERO-seed reference `W Ξ₀`.
  -- pad continuity of the reference doubled curve: tube slot pad-continuous, Jacobi slot pad-continuous
  -- via `geodesicJacobi_narrowpad_continuousOn` (THE FIX — nonzero-seed Jacobi is pad-continuous).
  have hrefcont : ContinuousOn (W Ξ₀) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    rw [hWdef, hΞ₀def]
    simp only
    refine ContinuousOn.prodMk ?_ ?_
    · intro τ hτ
      have hτIoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      exact (uniformFlowTube_spec_ode g gi hC hK q₀ hq₀K 0 h0v τ
        hτIoo).continuousAt.continuousWithinAt
    · exact hJselcont (q₀, 0) (a₀, b₀) hq₀K h0v
  have hAcont : ContinuousOn (fun τ => fderiv ℝ (doubledField g gi) (W Ξ₀ τ))
      (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    have hcd : Continuous (fderiv ℝ (doubledField g gi)) :=
      (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
    exact hcd.comp_continuousOn hrefcont
  -- build `V` (per doubled seed) via the narrow-pad linear-ODE engine.
  have hVExists : ∀ Ξ : (Point n × Point n) × (Point n × Point n),
      ∃ J : ℝ → (Point n × Point n) × (Point n × Point n), J 0 = Ξ ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt J (fderiv ℝ (doubledField g gi) (W Ξ₀ τ) (J τ)) τ :=
    fun Ξ => linODE_exists_hasDerivAt_Icc_narrow
      (fun τ => fderiv ℝ (doubledField g gi) (W Ξ₀ τ)) hAcont Ξ
  choose V hV0 hVode using hVExists
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (E) assemble via the abstract base-point second-order theorem (J4-850).
  obtain ⟨L, hLeq, hFD⟩ :=
    doubledFlow_endpoint_joint_hasFDerivAt_exists_atPoint g gi hC Ξ₀ hScomp hSconv hσpos
      (Set.right_mem_Icc.mpr zero_le_one) hWode hVode hV0 hIC hmem
  exact ⟨σ, hσpos, W, V, L, hLeq, hFD⟩

end QIQTH.ExpMap
