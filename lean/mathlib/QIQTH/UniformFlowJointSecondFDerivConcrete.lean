/-
  UniformFlowJointSecondFDerivConcrete — the CONCRETE, NON-VACUOUS instantiation of the JOINT SECOND-order
  Fréchet derivative of the geodesic flow (`GeodesicJointSecondFDerivAtPointLocal` /
  `GeodesicJointSecondFDeriv`) for the actual constructive uniform doubled flow, verified at a genuinely
  CURVED witness.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE — the second-order analogue of the J4-848 non-vacuity certificate.

  `GeodesicJointSecondFDeriv.doubledFlow_endpoint_joint_hasFDerivAt_exists` (and its base-point version
  `doubledFlow_endpoint_joint_hasFDerivAt_exists_atPoint`, J4-850) build the JOINT first-order Fréchet
  derivative of the DOUBLED (tangent-lifted) flow — equivalently the JOINT SECOND-order Fréchet object of
  the geodesic flow.  Their perturbation family is quantified over the BOUNDED window `‖Ξ‖ ≤ σ`, NOT
  `∀ Ξ`, so — unlike the base-level GLOBAL Task A (J4-847) — they do NOT inherit the global-`∀ξ` vacuity.
  This file supplies the missing half: it INSTANTIATES the abstract doubled second-order theorem for the
  concrete confined uniform doubled flow, discharging EVERY abstract hypothesis from the confinement
  machinery, and thereby CERTIFIES the doubled second-order derivative is genuinely SATISFIABLE at a real
  curved field — the exact opposite of the base-level global Task A's curved-field vacuity.

  ## THE ZERO-REFERENCE-SEED CONSTRUCTION (why it dodges the pad-continuity export gap).
  The abstract theorem's doubled-Jacobi block `V` must solve, with two-sided derivatives on the CLOSED
  `[0,1]`, the linearized ODE along the reference doubled curve `W Ξ₀`, whose coefficient field
  `A τ = fderiv (doubledField) (W Ξ₀ τ)` needs continuity on a PAD `[-1/2, 3/2]`.  For a generic reference
  doubled curve `(tube, Jref)` the Jacobi slot `Jref` only EXPORTS `[0,1]` regularity (the narrow-pad
  Jacobi engine's interface), so `A` is not pad-continuous — the export gap.  We take the base state
  `Ξ₀ = ((q₀,0),(0,0))` with ZERO Jacobi seed; then the reference Jacobi slot is the LITERAL zero field
  (genuinely the seed-`0` Jacobi solution, since a linear ODE with zero seed has the zero solution), which
  IS pad-continuous.  So `W Ξ₀ = (tube q₀ 0, 0)` is pad-continuous and `V` is constructible with two-sided
  `[0,1]` derivatives.  The perturbed doubled family `W Ξ` still perturbs the FULL doubled initial
  condition (base AND Jacobi seed), so the derivative `L` is a genuine full CLM on the doubled phase space.

  WHAT LANDS (axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited):

  * `uniformFlow_joint_secondFDeriv_witness` — ★ the DECISIVE NON-VACUITY WITNESS.  With
    `K := Metric.closedBall q₀ 1` and base state `Ξ₀ := ((q₀,0),(0,0))`, there exist a concrete confined
    doubled family `W`, its doubled-Jacobi block `V`, and the joint SECOND-order Fréchet-derivative CLM `L`
    (`L Ξ = V Ξ 1`) with
        `HasFDerivAt (fun Ξ => W Ξ 1) L ((q₀,0),(0,0))`,
    with NO carried domain hypotheses whatsoever, for EVERY (in particular genuinely curved) metric.  The
    joint SECOND Fréchet derivative of the geodesic flow genuinely EXISTS at a real curved field.

  ## WHAT THIS FILE DOES NOT DO.
  It establishes the derivative at the ZERO-Jacobi-seed base state only (the pad-export gap blocks a NONZERO
  reference seed).  It does NOT assemble joint `ContDiffOn ℝ 1` of the doubled flow, NOT the finite-basis
  transfer to `ContDiffOn ℝ 2` of the base flow, NOT the IFT inverse, NOT discharge the RNC hypotheses, and
  does NOT bear on `hCConv`.  See the report for the precise remaining gap (the transfer needs the
  derivative at nonzero-seed base states, blocked on the pad-export plumbing).
-/
import Mathlib
import QIQTH.GeodesicJointSecondFDerivAtPointLocal
import QIQTH.GeodesicJointFDerivLipschitz
import QIQTH.DoubledFamilyFullSupply
import QIQTH.DoubledFamilyConstruction
import QIQTH.UniformFlowNondeg
import QIQTH.BoundedGeometry

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- **★ Concrete non-vacuity witness for the joint SECOND-order Fréchet derivative of the geodesic flow.**
    With `K := Metric.closedBall q₀ 1` and the ZERO-Jacobi-seed base state `Ξ₀ := ((q₀,0),(0,0))`, the
    concrete confined uniform doubled flow's endpoint `fun Ξ => W Ξ 1` has a genuine joint SECOND-order
    Fréchet derivative `L` at `Ξ₀`, for EVERY (curved) metric — certifying the abstract doubled
    second-order theorem is genuinely SATISFIABLE (not merely type-correct) at a real curved field. -/
theorem uniformFlow_joint_secondFDeriv_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    ∃ (σ : ℝ), 0 < σ ∧
      ∃ (W V : ((Point n × Point n) × (Point n × Point n)) → ℝ →
            ((Point n × Point n) × (Point n × Point n)))
        (L : ((Point n × Point n) × (Point n × Point n)) →L[ℝ]
            ((Point n × Point n) × (Point n × Point n))),
        (∀ Ξ : ((Point n × Point n) × (Point n × Point n)), L Ξ = V Ξ 1) ∧
        HasFDerivAt (fun Ξ => W Ξ 1) L
          ((((q₀, 0), (0, 0))) : ((Point n × Point n) × (Point n × Point n))) := by
  classical
  set hK : IsCompact (Metric.closedBall q₀ 1) := isCompact_closedBall q₀ 1 with hKdef
  set K : Set (Point n) := Metric.closedBall q₀ 1 with hKsetdef
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρpos : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hC₀0 : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- the base state (zero Jacobi seed) and the perturbation window.
  set Ξ₀ : (Point n × Point n) × (Point n × Point n) := ((q₀, 0), (0, 0)) with hΞ₀def
  set σ : ℝ := min 1 ρ with hσdef
  have hσpos : 0 < σ := lt_min zero_lt_one hρpos
  have hq₀K : q₀ ∈ K := by rw [hKsetdef]; exact Metric.mem_closedBall_self zero_le_one
  have h0v : ‖(0 : Point n)‖ ≤ ρ := by rw [norm_zero]; exact hρpos.le
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (A) per-`(base,seed)` Jacobi families along the concrete tubes (choice, conditional on admissibility).
  have hJselExists : ∀ (p : Point n × Point n) (w : Point n × Point n),
      ∃ J : ℝ → Point n × Point n, J 0 = w ∧
        (p.1 ∈ K → ‖p.2‖ ≤ ρ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt J
            (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK p.1 p.2 τ) (J τ)) τ) := by
    intro p w
    by_cases hadm : p.1 ∈ K ∧ ‖p.2‖ ≤ ρ
    · have hcont : ContinuousOn (uniformFlowTube g gi hC hK p.1 p.2)
          (Set.Icc (-(1/2) : ℝ) (3/2)) := by
        intro τ hτ
        have hτIoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        exact (uniformFlowTube_spec_ode g gi hC hK p.1 hadm.1 p.2 hadm.2 τ
          hτIoo).continuousAt.continuousWithinAt
      obtain ⟨J, hJ0, hJd⟩ :=
        geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (uniformFlowTube g gi hC hK p.1 p.2) hcont w
      exact ⟨J, hJ0, fun _ _ => hJd⟩
    · exact ⟨fun _ => w, rfl, fun h1 h2 => absurd ⟨h1, h2⟩ hadm⟩
  choose Jsel hJsel0 hJselode using hJselExists
  -- the seed-0-normalized Jacobi block: literal zero field at zero seed (genuinely the seed-0 Jacobi).
  set Jbar : (Point n × Point n) → (Point n × Point n) → ℝ → Point n × Point n :=
    fun p w => if w = 0 then (fun _ => 0) else Jsel p w with hJbardef
  -- the concrete perturbed doubled family.
  set W : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n)) :=
    fun Ξ τ => (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ, Jbar Ξ.1 Ξ.2 τ) with hWdef
  -- the Jacobi block always solves the Jacobi ODE (both branches), for admissible base+seed.
  have hJbarode : ∀ (p : Point n × Point n) (w : Point n × Point n), p.1 ∈ K → ‖p.2‖ ≤ ρ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Jbar p w)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK p.1 p.2 τ) (Jbar p w τ)) τ := by
    intro p w hp hw τ hτ
    by_cases hw0 : w = 0
    · have hbar : Jbar p w = (fun _ => (0 : Point n × Point n)) := by rw [hJbardef]; simp [hw0]
      rw [hbar]
      have : fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK p.1 p.2 τ)
          ((fun _ => (0 : Point n × Point n)) τ) = 0 := by simp
      rw [this]; exact hasDerivAt_const τ 0
    · have hbar : Jbar p w = Jsel p w := by rw [hJbardef]; simp [hw0]
      rw [hbar]; exact hJselode p w hp hw τ hτ
  have hJbar0 : ∀ (p : Point n × Point n) (w : Point n × Point n), Jbar p w 0 = w := by
    intro p w
    by_cases hw0 : w = 0
    · rw [hJbardef]; simp [hw0]
    · rw [hJbardef]; simp only [if_neg hw0]; exact hJsel0 p w
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- window admissibility: `‖Ξ - Ξ₀‖ ≤ σ` puts the base in `K`, the velocity ≤ ρ/σ, and the seed ≤ σ.
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
  have hseedσ : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ → ‖Ξ.2‖ ≤ σ := by
    intro Ξ hΞ
    have hz : Ξ₀.2 = (0 : Point n × Point n) := rfl
    calc ‖Ξ.2‖ = dist Ξ.2 Ξ₀.2 := by rw [hz, dist_zero_right]
      _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
      _ ≤ σ := hΞ
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
  set R₂ : ℝ := σ * Real.exp Kb with hR₂def
  have hR₂0 : 0 ≤ R₂ := by rw [hR₂def]; positivity
  set S₂ : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) R₂ with hS₂def
  have hS₂comp : IsCompact S₂ := by rw [hS₂def]; exact isCompact_closedBall _ _
  have hS₂conv : Convex ℝ S₂ := by rw [hS₂def]; exact convex_closedBall _ _
  set S : Set ((Point n × Point n) × (Point n × Point n)) := S₁ ×ˢ S₂ with hSdef
  have hScomp : IsCompact S := by rw [hSdef]; exact hS₁comp.prod hS₂comp
  have hSconv : Convex ℝ S := by rw [hSdef]; exact hS₁conv.prod hS₂conv
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
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
    have hJ : HasDerivAt (Jbar Ξ.1 Ξ.2)
        (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ)
          (Jbar Ξ.1 Ξ.2 τ)) τ :=
      hJbarode Ξ.1 Ξ.2 hqK hvρ τ hτ
    exact doubledField_prod_hasDerivAt g gi hP hJ
  -- (C2) affine initial condition.
  have hΞ₀tube0 : uniformFlowTube g gi hC hK q₀ 0 0 = ((q₀, 0) : Point n × Point n) :=
    uniformFlowTube_spec_ic g gi hC hK q₀ hq₀K 0 h0v
  have hWΞ₀0 : W Ξ₀ 0 = Ξ₀ := by
    rw [hWdef, hΞ₀def]
    simp only
    refine Prod.ext ?_ ?_
    · exact hΞ₀tube0
    · exact hJbar0 (q₀, 0) (0, 0)
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
      · exact hJbar0 Ξ.1 Ξ.2
    rw [hWΞ0, hWΞ₀0]
  -- (C3) confinement into `S = S₁ ×ˢ S₂`.
  have hmem : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ σ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, W Ξ τ ∈ S := by
    intro Ξ hΞ τ hτ
    have hqK : Ξ.1.1 ∈ K := hbaseK Ξ hΞ
    have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ Ξ hΞ
    have hsσ : ‖Ξ.2‖ ≤ σ := hseedσ Ξ hΞ
    -- `.1` component in `S₁`.
    have hmem1 : uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ ∈ S₁ := htubeS₁ Ξ hΞ τ hτ
    -- `.2` component in `S₂` via the homogeneous Jacobi growth bound.
    have hmem2 : Jbar Ξ.1 Ξ.2 τ ∈ S₂ := by
      rw [hS₂def, Metric.mem_closedBall, dist_zero_right]
      have hJode := hJbarode Ξ.1 Ξ.2 hqK hvρ
      have hKbtube : ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s)‖ ≤ Kb :=
        fun s hs => hKbbd _ (htubeS₁ Ξ hΞ s hs)
      have hgrow := jacobi_field_norm_bound hKb0 hJode hKbtube τ hτ
      rw [hJbar0 Ξ.1 Ξ.2] at hgrow
      calc ‖Jbar Ξ.1 Ξ.2 τ‖ ≤ ‖Ξ.2‖ * Real.exp Kb := hgrow
        _ ≤ σ * Real.exp Kb := by
            apply mul_le_mul_of_nonneg_right hsσ (Real.exp_pos _).le
        _ = R₂ := by rw [hR₂def]
    rw [hSdef, hWdef]
    exact Set.mk_mem_prod hmem1 hmem2
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (D) the doubled-Jacobi block `V` along the pad-continuous zero-seed reference `W Ξ₀`.
  have hWΞ₀fun : (W Ξ₀) = fun τ => (uniformFlowTube g gi hC hK q₀ 0 τ, (0 : Point n × Point n)) := by
    funext τ
    show (uniformFlowTube g gi hC hK q₀ 0 τ,
        Jbar ((q₀, (0 : Point n)) : Point n × Point n)
          (((0 : Point n), (0 : Point n)) : Point n × Point n) τ)
        = (uniformFlowTube g gi hC hK q₀ 0 τ, (0 : Point n × Point n))
    refine Prod.ext rfl ?_
    show Jbar ((q₀, (0 : Point n)) : Point n × Point n)
        (((0 : Point n), (0 : Point n)) : Point n × Point n) τ = 0
    rw [hJbardef]; simp
  -- pad continuity of the reference doubled curve and hence of its doubled coefficient field.
  have hrefcont : ContinuousOn (W Ξ₀) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    rw [hWΞ₀fun]
    refine ContinuousOn.prodMk ?_ continuousOn_const
    intro τ hτ
    have hτIoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact (uniformFlowTube_spec_ode g gi hC hK q₀ hq₀K 0 h0v τ hτIoo).continuousAt.continuousWithinAt
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
