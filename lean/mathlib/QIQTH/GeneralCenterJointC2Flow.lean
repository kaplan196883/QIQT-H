/-
  GeneralCenterJointC2Flow — J4-890: the GENERAL-CENTER (nonzero-velocity) joint `ContDiffOn ℝ 2` of
  the concrete confined uniform geodesic EXP map, re-centered from J4-884's near-`(z₀,0)` Task D to an
  ARBITRARY interior base point `z₀ ∈ interior K` AND an ARBITRARY velocity `v₀` with `‖v₀‖ <
  uniformFlowRadius`.  This is pieces (i)+(ii) of J4-889's b-tube joint-C² frontier.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.  `a₁ = R/6` remains CONDITIONAL on
  {hDuhamel, hDConv, hCConv}.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE — the velocity-0 centering of J4-884's Task D was a CONVENIENCE, not a wall.

  J4-889 (`QuantifiedCoherentChartTube.lean`) reduced `hbint`'s residual to a chart-`C²` + in-gate open
  cover of the compact `b`-tube over `K`, and named four pieces needed to build it, the first two being
  (i) a uniform-over-`K` lower bound on the flow radius and (ii) joint `C²` of exp at NONZERO velocities
  up to `b` (J4-884's Task D is centred at velocity 0 only).

  The AUDIT that drives this file: every ABSTRACT engine Task D consumes —
  `geodesicFlow_joint_hasFDerivAt_exists_atPoint_local`, `doubledFlow_endpoint_joint_hasFDerivAt_exists_
  atPoint`, `doubledFlow_joint_fderiv_lipschitz_in_basepoint`, `geodesicJacobi_narrowpad_*` — takes an
  ARBITRARY base point / reference tube / Jacobi seed.  The ONLY place velocity-0 enters Task D's
  concrete assembly is the admissibility bookkeeping (`hbaseK`/`hvelρ`/`hvelδ`/`hUadm`), which merely
  keeps a neighbourhood inside the tube's valid domain `{(q,v) : q ∈ K, ‖v‖ ≤ ρ}`.  That neighbourhood
  exists around ANY `(z₀, v₀)` as soon as `‖v₀‖ < ρ` — piece (i).  So Task D re-runs verbatim at a
  nonzero-velocity centre — piece (ii) — with NO new machinery.

  ## THE DELIVERABLES.

  * `admissibleBall_of_normVelLt` — ★ PIECE (i).  For `z₀ ∈ interior K` and `‖v₀‖ < ρ := uniformFlow
    Radius g gi hC hK`, there is `ε > 0` with `Metric.ball (z₀,v₀) ε` entirely admissible
    (`ξ.1 ∈ K ∧ ‖ξ.2‖ ≤ ρ`).  This is the concrete witness that the EXISTING `uniformFlowRadius`
    K-uniformity (one Picard–Lindelöf datum over all of `K`, `geodesic_apriori_confinement_uniform`)
    ALREADY suffices — velocities up to any `b < ρ` are admissible for the SAME `K`, so NO further
    refinement of the confinement radius is needed for the b-tube (which carries `b < ρ` as a standing
    hypothesis in J4-889).

  * `uniformFlow_joint_contDiffOn_two_witness_generalCenter` — ★★ PIECE (ii).  For an ARBITRARY compact
    `K`, interior base point `z₀ ∈ interior K`, and ARBITRARY velocity `v₀` with `‖v₀‖ < ρ`, there is an
    OPEN neighbourhood `U` of `(z₀, v₀)` on which `fun ξ => uniformFlowExp g gi hC hK ξ.1 ξ.2` is jointly
    `ContDiffOn ℝ 2`.  The general-CENTRE second-order regularity of the constructive exp map — J4-884's
    Task D, re-centred at a nonzero velocity, over general `K`, in ONE direct construction (NO reference-
    ball transport — this simultaneously covers the general-`K` base direction, so it does not need the
    piece (iii) transport of `UniformFlowCoherentJointChartGeneralK.lean`).

  ## WHAT THIS FILE DOES NOT DO.
  It supplies the per-point general-centre joint `C²` chart (pieces (i)+(ii)); it is the LOCAL engine
  that a compactness argument (piece (iv)) would cover the compact `b`-tube `K ×ˢ closedBall 0 b` with.
  It does NOT run that finite-cover assembly, does NOT build the coherent inverse chart at a nonzero
  velocity (the IFT step, Task E-analogue), does NOT reconcile with `uniformInverseChart`, does NOT
  discharge the RNC hypotheses, and does NOT bear on `hCConv`.  a₁=R/6 remains CONDITIONAL.
-/
import Mathlib
import QIQTH.GeodesicJointFDerivAtPointLocal
import QIQTH.GeodesicJointSecondFDerivAtPointLocal
import QIQTH.GeodesicJointSecondFDerivLipschitz
import QIQTH.GeodesicJointFDerivLipschitz
import QIQTH.DoubledFamilyFullSupply
import QIQTH.DoubledVariationField
import QIQTH.DoubledFamilyConstruction
import QIQTH.GeodesicTaylorCompact
import QIQTH.SecondVariationLipschitz
import QIQTH.UniformFlowNondeg
import QIQTH.BoundedGeometry

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 8000000

variable {n : ℕ}

/-! ###############################################################################
    ### PIECE (i) — the admissible ball around a nonzero-velocity interior centre.
    ############################################################################### -/

/-- **★ PIECE (i) — an admissible ball around `(z₀, v₀)`.**  For an interior base point
    `z₀ ∈ interior K` and a velocity `v₀` with `‖v₀‖ < ρ := uniformFlowRadius g gi hC hK`, there is a
    radius `ε > 0` such that every phase point `ξ` in `Metric.ball (z₀, v₀) ε` is admissible for the
    uniform tube: its base `ξ.1 ∈ K` and its velocity `‖ξ.2‖ ≤ ρ`.  Concrete certificate that the
    EXISTING K-uniform confinement radius already suffices for velocities strictly below it — no
    refinement of the flow / near-identity radius is needed. -/
theorem admissibleBall_of_normVelLt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K)
    (v₀ : Point n) (hv₀ : ‖v₀‖ < uniformFlowRadius g gi hC hK) :
    ∃ ε > (0 : ℝ), ∀ ξ ∈ Metric.ball ((z₀, v₀) : Point n × Point n) ε,
      ξ.1 ∈ K ∧ ‖ξ.2‖ ≤ uniformFlowRadius g gi hC hK := by
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz₀)
  have hgap : 0 < ρ - ‖v₀‖ := by rw [hρdef] at hv₀ ⊢; linarith
  set ε : ℝ := min r₁ (ρ - ‖v₀‖) with hεdef
  have hεpos : 0 < ε := lt_min hr₁pos hgap
  refine ⟨ε, hεpos, ?_⟩
  intro ξ hξ
  rw [Metric.mem_ball] at hξ
  have hb : dist ξ.1 z₀ ≤ dist ξ ((z₀, v₀) : Point n × Point n) := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hv : dist ξ.2 v₀ ≤ dist ξ ((z₀, v₀) : Point n × Point n) := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  refine ⟨?_, ?_⟩
  · apply interior_subset
    apply hr₁sub
    rw [Metric.mem_ball]
    calc dist ξ.1 z₀ ≤ dist ξ ((z₀, v₀) : Point n × Point n) := hb
      _ < ε := hξ
      _ ≤ r₁ := min_le_left _ _
  · have hlt : dist ξ.2 v₀ < ε := lt_of_le_of_lt hv hξ
    have hle : ‖ξ.2 - v₀‖ < ε := by rwa [dist_eq_norm] at hlt
    calc ‖ξ.2‖ = ‖(ξ.2 - v₀) + v₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖ξ.2 - v₀‖ + ‖v₀‖ := norm_add_le _ _
      _ ≤ ε + ‖v₀‖ := by linarith
      _ ≤ (ρ - ‖v₀‖) + ‖v₀‖ := by have := min_le_right r₁ (ρ - ‖v₀‖); rw [← hεdef] at this; linarith
      _ = ρ := by ring

/-! ###############################################################################
    ### PIECE (ii) — the general-centre (nonzero-velocity) joint `ContDiffOn ℝ 2` of exp.
    ############################################################################### -/

/-- **★★ PIECE (ii) — general-CENTRE joint `ContDiffOn ℝ 2` of the concrete uniform geodesic exp map.**
    For an ARBITRARY compact `K`, an interior base point `z₀ ∈ interior K`, and an ARBITRARY velocity
    `v₀` with `‖v₀‖ < ρ := uniformFlowRadius g gi hC hK`, there is an OPEN neighbourhood `U` of
    `(z₀, v₀)` on which `fun ξ => uniformFlowExp g gi hC hK ξ.1 ξ.2` is jointly `ContDiffOn ℝ 2`, for
    EVERY (curved) metric.  This is J4-884's Task D re-centred at a NONZERO velocity over a GENERAL `K`
    — every abstract engine is velocity/base-agnostic, so the construction transplants verbatim once the
    admissibility bookkeeping is re-based at `(z₀, v₀)` (piece (i) guarantees the enclosing
    neighbourhood stays in the tube's valid domain). -/
theorem uniformFlow_joint_contDiffOn_two_witness_generalCenter (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K)
    (v₀ : Point n) (hv₀ : ‖v₀‖ < uniformFlowRadius g gi hC hK) :
    ∃ (U : Set (Point n × Point n)), IsOpen U ∧
      ((z₀, v₀) : Point n × Point n) ∈ U ∧
      ContDiffOn ℝ 2
        (fun ξ : Point n × Point n => uniformFlowExp g gi hC hK ξ.1 ξ.2) U := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρpos : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hC₀0 : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- interior ball `⊆ K`.
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz₀)
  have hgap : 0 < ρ - ‖v₀‖ := by rw [hρdef] at hv₀ ⊢; linarith
  -- neighbourhood half-radius: small enough that a `δ`-window stays base-in-`K` and velocity-≤-`ρ`.
  set δ : ℝ := min (r₁ / 2) ((ρ - ‖v₀‖) / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδler : δ ≤ r₁ / 2 := min_le_left _ _
  have hδleV : δ ≤ (ρ - ‖v₀‖) / 2 := min_le_right _ _
  -- velocity ceiling on the `δ`-window.
  set Vmax : ℝ := ‖v₀‖ + δ with hVmaxdef
  have hVmax0 : 0 ≤ Vmax := by rw [hVmaxdef]; positivity
  have hVmaxρ : Vmax ≤ ρ := by rw [hVmaxdef]; linarith
  set c : Point n × Point n := (z₀, v₀) with hcdef
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
  set W : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n)) :=
    fun Ξ τ => (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ, Jsel Ξ.1 Ξ.2 τ) with hWdef
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- s-INDEPENDENT admissibility helpers (they only use `Ξ₀.1 = c = (z₀,v₀)`, common to every seed).
  have hbaseK : ∀ (s : Point n × Point n) (Ξ : (Point n × Point n) × (Point n × Point n)),
      ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ ≤ δ → Ξ.1.1 ∈ K := by
    intro s Ξ hΞ
    have h1 : dist Ξ.1.1 z₀ ≤ ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ := by
      calc dist Ξ.1.1 z₀
            ≤ dist Ξ.1 c := by rw [hcdef, Prod.dist_eq]; exact le_max_left _ _
        _ ≤ dist Ξ ((c, s) : (Point n × Point n) × (Point n × Point n)) := by
            rw [Prod.dist_eq]; exact le_max_left _ _
        _ = ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ := dist_eq_norm _ _
    apply interior_subset
    apply hr₁sub
    rw [Metric.mem_ball]
    calc dist Ξ.1.1 z₀ ≤ δ := le_trans h1 hΞ
      _ ≤ r₁ / 2 := hδler
      _ < r₁ := by linarith
  have hvelρ : ∀ (s : Point n × Point n) (Ξ : (Point n × Point n) × (Point n × Point n)),
      ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ ≤ δ → ‖Ξ.1.2‖ ≤ ρ := by
    intro s Ξ hΞ
    have h1 : ‖Ξ.1.2 - v₀‖ ≤ ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ := by
      calc ‖Ξ.1.2 - v₀‖ = dist Ξ.1.2 v₀ := (dist_eq_norm _ _).symm
        _ ≤ dist Ξ.1 c := by rw [hcdef, Prod.dist_eq]; exact le_max_right _ _
        _ ≤ dist Ξ ((c, s) : (Point n × Point n) × (Point n × Point n)) := by
            rw [Prod.dist_eq]; exact le_max_left _ _
        _ = ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ := dist_eq_norm _ _
    calc ‖Ξ.1.2‖ = ‖(Ξ.1.2 - v₀) + v₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖Ξ.1.2 - v₀‖ + ‖v₀‖ := norm_add_le _ _
      _ ≤ δ + ‖v₀‖ := by linarith [h1]
      _ ≤ ρ := by linarith
  have hvelVmax : ∀ (s : Point n × Point n) (Ξ : (Point n × Point n) × (Point n × Point n)),
      ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ ≤ δ → ‖Ξ.1.2‖ ≤ Vmax := by
    intro s Ξ hΞ
    have h1 : ‖Ξ.1.2 - v₀‖ ≤ ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ := by
      calc ‖Ξ.1.2 - v₀‖ = dist Ξ.1.2 v₀ := (dist_eq_norm _ _).symm
        _ ≤ dist Ξ.1 c := by rw [hcdef, Prod.dist_eq]; exact le_max_right _ _
        _ ≤ dist Ξ ((c, s) : (Point n × Point n) × (Point n × Point n)) := by
            rw [Prod.dist_eq]; exact le_max_left _ _
        _ = ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ := dist_eq_norm _ _
    calc ‖Ξ.1.2‖ = ‖(Ξ.1.2 - v₀) + v₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖Ξ.1.2 - v₀‖ + ‖v₀‖ := norm_add_le _ _
      _ ≤ δ + ‖v₀‖ := by linarith [h1]
      _ = Vmax := by rw [hVmaxdef]; ring
  have hbasedist : ∀ (s : Point n × Point n) (Ξ : (Point n × Point n) × (Point n × Point n)),
      ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ ≤ δ → dist Ξ.1.1 z₀ ≤ δ := by
    intro s Ξ hΞ
    calc dist Ξ.1.1 z₀
          ≤ dist Ξ.1 c := by rw [hcdef, Prod.dist_eq]; exact le_max_left _ _
      _ ≤ dist Ξ ((c, s) : (Point n × Point n) × (Point n × Point n)) := by
          rw [Prod.dist_eq]; exact le_max_left _ _
      _ = ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ := dist_eq_norm _ _
      _ ≤ δ := hΞ
  -- global doubled ODE / initial condition (only need base/velocity admissibility, s-independent).
  have hWode_glob : ∀ (s : Point n × Point n) (Ξ : (Point n × Point n) × (Point n × Point n)),
      ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ ≤ δ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W Ξ) (doubledField g gi (W Ξ τ)) τ := by
    intro s Ξ hΞ τ hτ
    have hqK : Ξ.1.1 ∈ K := hbaseK s Ξ hΞ
    have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ s Ξ hΞ
    have hP : HasDerivAt (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2)
        (geodesicField g gi (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ)) τ :=
      uniformFlowTube_spec_ode g gi hC hK Ξ.1.1 hqK Ξ.1.2 hvρ τ
        ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hJ : HasDerivAt (Jsel Ξ.1 Ξ.2)
        (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ)
          (Jsel Ξ.1 Ξ.2 τ)) τ :=
      hJselode Ξ.1 Ξ.2 hqK hvρ τ hτ
    exact doubledField_prod_hasDerivAt g gi hP hJ
  have hWzero : ∀ (s : Point n × Point n) (Ξ : (Point n × Point n) × (Point n × Point n)),
      ‖Ξ - ((c, s) : (Point n × Point n) × (Point n × Point n))‖ ≤ δ → W Ξ 0 = Ξ := by
    intro s Ξ hΞ
    have hqK : Ξ.1.1 ∈ K := hbaseK s Ξ hΞ
    have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ s Ξ hΞ
    have h1 : uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 0 = Ξ.1 :=
      uniformFlowTube_spec_ic g gi hC hK Ξ.1.1 hqK Ξ.1.2 hvρ
    have h2 : Jsel Ξ.1 Ξ.2 0 = Ξ.2 := hJsel0 Ξ.1 Ξ.2
    show (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 0, Jsel Ξ.1 Ξ.2 0) = Ξ
    rw [h1, h2]
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (B) the doubled `ContDiffOn ℝ 1` of `fun Ξ => W Ξ 1` centered at ANY seed `s`.
  have hDbl : ∀ s : Point n × Point n,
      ContDiffOn ℝ 1 (fun Ξ => W Ξ 1)
        (Metric.ball (((c, s)) : (Point n × Point n) × (Point n × Point n)) (δ / 2)) := by
    intro s
    set Ξ₀ : (Point n × Point n) × (Point n × Point n) := (c, s) with hΞ₀def
    set M₀ : ℝ := ‖s‖ with hM₀def
    have hM₀0 : 0 ≤ M₀ := norm_nonneg _
    set r : ℝ := δ / 2 with hrdef
    have hr : 0 < r := by rw [hrdef]; linarith
    set σ : ℝ := δ / 2 with hσdef
    have hσpos : 0 < σ := by rw [hσdef]; linarith
    -- seed control and window admissibility.
    have hseednorm : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ →
        ‖Ξ.2‖ ≤ M₀ + δ := by
      intro Ξ hΞ
      have hz : Ξ₀.2 = s := rfl
      have hd : ‖Ξ.2 - s‖ ≤ δ := by
        calc ‖Ξ.2 - s‖ = dist Ξ.2 Ξ₀.2 := by rw [hz, dist_eq_norm]
          _ ≤ dist Ξ Ξ₀ := by rw [Prod.dist_eq]; exact le_max_right _ _
          _ = ‖Ξ - Ξ₀‖ := dist_eq_norm _ _
          _ ≤ δ := hΞ
      calc ‖Ξ.2‖ = ‖(Ξ.2 - s) + s‖ := by rw [sub_add_cancel]
        _ ≤ ‖Ξ.2 - s‖ + M₀ := by rw [hM₀def]; exact norm_add_le _ _
        _ ≤ δ + M₀ := by linarith [hd]
        _ = M₀ + δ := by ring
    have hwin : ∀ x : (Point n × Point n) × (Point n × Point n), x ∈ Metric.ball Ξ₀ r →
        ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - x‖ ≤ σ → ‖Ξ - Ξ₀‖ ≤ δ := by
      intro x hx Ξ hΞx
      have hxnorm : ‖x - Ξ₀‖ < r := by rw [← dist_eq_norm]; rwa [Metric.mem_ball] at hx
      calc ‖Ξ - Ξ₀‖ = ‖(Ξ - x) + (x - Ξ₀)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖Ξ - x‖ + ‖x - Ξ₀‖ := norm_add_le _ _
        _ ≤ σ + r := by linarith
        _ = δ := by rw [hσdef, hrdef]; ring
    have hballadm : ∀ x : (Point n × Point n) × (Point n × Point n), x ∈ Metric.ball Ξ₀ r →
        ‖x - Ξ₀‖ ≤ δ := by
      intro x hx
      have hxnorm : ‖x - Ξ₀‖ < r := by rw [← dist_eq_norm]; rwa [Metric.mem_ball] at hx
      have : r ≤ δ := by rw [hrdef]; linarith
      linarith
    -- control set `S = S₁ ×ˢ S₂`.
    set R₁ : ℝ := C₀ * Vmax + δ with hR₁def
    have hR₁0 : 0 ≤ R₁ := by rw [hR₁def]; positivity
    set S₁ : Set (Point n × Point n) := Metric.closedBall ((z₀, 0) : Point n × Point n) R₁ with hS₁def
    have hS₁comp : IsCompact S₁ := by rw [hS₁def]; exact isCompact_closedBall _ _
    have hS₁conv : Convex ℝ S₁ := by rw [hS₁def]; exact convex_closedBall _ _
    have htubeS₁ : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ →
        ∀ s' ∈ Set.Icc (0 : ℝ) 1, uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s' ∈ S₁ := by
      intro Ξ hΞ s' hs'
      have hqK : Ξ.1.1 ∈ K := hbaseK s Ξ hΞ
      have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ s Ξ hΞ
      have hvV : ‖Ξ.1.2‖ ≤ Vmax := hvelVmax s Ξ hΞ
      have hbd : dist Ξ.1.1 z₀ ≤ δ := hbasedist s Ξ hΞ
      rw [hS₁def, Metric.mem_closedBall]
      have hconf := uniformFlowTube_spec_conf g gi hC hK Ξ.1.1 hqK Ξ.1.2 hvρ s' hs'
      calc dist (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s') ((z₀, 0) : Point n × Point n)
          ≤ dist (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s') ((Ξ.1.1, 0) : Point n × Point n)
              + dist ((Ξ.1.1, 0) : Point n × Point n) ((z₀, 0) : Point n × Point n) :=
            dist_triangle _ _ _
        _ ≤ C₀ * Vmax + δ := by
            apply add_le_add
            · rw [dist_eq_norm]
              calc ‖uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s' - ((Ξ.1.1, 0) : Point n × Point n)‖
                  ≤ C₀ * ‖Ξ.1.2‖ := hconf
                _ ≤ C₀ * Vmax := mul_le_mul_of_nonneg_left hvV hC₀0
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
    have hmem_glob : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - Ξ₀‖ ≤ δ →
        ∀ τ ∈ Set.Icc (0 : ℝ) 1, W Ξ τ ∈ S := by
      intro Ξ hΞ τ hτ
      have hqK : Ξ.1.1 ∈ K := hbaseK s Ξ hΞ
      have hvρ : ‖Ξ.1.2‖ ≤ ρ := hvelρ s Ξ hΞ
      have hsδ : ‖Ξ.2‖ ≤ M₀ + δ := hseednorm Ξ hΞ
      have hmem1 : uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 τ ∈ S₁ := htubeS₁ Ξ hΞ τ hτ
      have hmem2 : Jsel Ξ.1 Ξ.2 τ ∈ S₂ := by
        rw [hS₂def, Metric.mem_closedBall, dist_zero_right]
        have hJode := hJselode Ξ.1 Ξ.2 hqK hvρ
        have hKbtube : ∀ s'' ∈ Set.Icc (0 : ℝ) 1,
            ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK Ξ.1.1 Ξ.1.2 s'')‖ ≤ Kb :=
          fun s'' hs'' => hKbbd _ (htubeS₁ Ξ hΞ s'' hs'')
        have hgrow := jacobi_field_norm_bound hKb0 hJode hKbtube τ hτ
        rw [hJsel0 Ξ.1 Ξ.2] at hgrow
        calc ‖Jsel Ξ.1 Ξ.2 τ‖ ≤ ‖Ξ.2‖ * Real.exp Kb := hgrow
          _ ≤ (M₀ + δ) * Real.exp Kb := by
              apply mul_le_mul_of_nonneg_right hsδ (Real.exp_pos _).le
          _ = R₂ := by rw [hR₂def]
      rw [hSdef, hWdef]
      exact Set.mk_mem_prod hmem1 hmem2
    have hWcont : ∀ x : (Point n × Point n) × (Point n × Point n), ‖x - Ξ₀‖ ≤ δ →
        ContinuousOn (W x) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
      intro x hx
      have hqK : x.1.1 ∈ K := hbaseK s x hx
      have hvρ : ‖x.1.2‖ ≤ ρ := hvelρ s x hx
      rw [hWdef]
      simp only
      refine ContinuousOn.prodMk ?_ ?_
      · intro τ hτ
        have hτIoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        exact (uniformFlowTube_spec_ode g gi hC hK x.1.1 hqK x.1.2 hvρ τ
          hτIoo).continuousAt.continuousWithinAt
      · exact hJselcont x.1 x.2 hqK hvρ
    have hAcont : ∀ x : (Point n × Point n) × (Point n × Point n), ‖x - Ξ₀‖ ≤ δ →
        ContinuousOn (fun τ => fderiv ℝ (doubledField g gi) (W x τ))
          (Set.Icc (-(1/2) : ℝ) (3/2)) := by
      intro x hx
      have hcd : Continuous (fderiv ℝ (doubledField g gi)) :=
        (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
      exact hcd.comp_continuousOn (hWcont x hx)
    -- per-base-point second-order Fréchet derivative data.
    set f : ((Point n × Point n) × (Point n × Point n)) →
        ((Point n × Point n) × (Point n × Point n)) := fun Ξ => W Ξ 1 with hfdef
    have hdata : ∀ x ∈ Metric.ball Ξ₀ r,
        ∃ (V : ((Point n × Point n) × (Point n × Point n)) → ℝ →
            ((Point n × Point n) × (Point n × Point n)))
          (L : ((Point n × Point n) × (Point n × Point n)) →L[ℝ]
            ((Point n × Point n) × (Point n × Point n))),
          (∀ Ξ : (Point n × Point n) × (Point n × Point n), V Ξ 0 = Ξ) ∧
          (∀ Ξ : (Point n × Point n) × (Point n × Point n), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt (V Ξ) (fderiv ℝ (doubledField g gi) (W x τ) (V Ξ τ)) τ) ∧
          (∀ Ξ : (Point n × Point n) × (Point n × Point n), L Ξ = V Ξ 1) ∧
          HasFDerivAt f L x := by
      intro x hx
      have hxadm : ‖x - Ξ₀‖ ≤ δ := hballadm x hx
      have hVExists : ∀ Ξ : (Point n × Point n) × (Point n × Point n),
          ∃ J : ℝ → (Point n × Point n) × (Point n × Point n), J 0 = Ξ ∧
            ∀ τ ∈ Set.Icc (0 : ℝ) 1,
              HasDerivAt J (fderiv ℝ (doubledField g gi) (W x τ) (J τ)) τ :=
        fun Ξ => linODE_exists_hasDerivAt_Icc_narrow
          (fun τ => fderiv ℝ (doubledField g gi) (W x τ)) (hAcont x hxadm) Ξ
      choose V hV0 hVode using hVExists
      have hWode_x : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - x‖ ≤ σ →
          ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W Ξ) (doubledField g gi (W Ξ τ)) τ :=
        fun Ξ hΞ τ hτ => hWode_glob s Ξ (hwin x hx Ξ hΞ) τ hτ
      have hIC_x : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - x‖ ≤ σ →
          W Ξ 0 - W x 0 = Ξ - x := by
        intro Ξ hΞ
        rw [hWzero s Ξ (hwin x hx Ξ hΞ), hWzero s x hxadm]
      have hmem_x : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖Ξ - x‖ ≤ σ →
          ∀ τ ∈ Set.Icc (0 : ℝ) 1, W Ξ τ ∈ S :=
        fun Ξ hΞ τ hτ => hmem_glob Ξ (hwin x hx Ξ hΞ) τ hτ
      obtain ⟨L, hLeq, hFD⟩ :=
        doubledFlow_endpoint_joint_hasFDerivAt_exists_atPoint g gi hC x hScomp hSconv hσpos
          (Set.right_mem_Icc.mpr zero_le_one) hWode_x hVode hV0 hIC_x hmem_x
      exact ⟨V, L, hV0, hVode, hLeq, hFD⟩
    -- differentiability + Lipschitz continuity of `fderiv f`.
    have hdiff : DifferentiableOn ℝ f (Metric.ball Ξ₀ r) := by
      intro x hx
      obtain ⟨_V, _L, _, _, _, hFD⟩ := hdata x hx
      exact hFD.differentiableAt.differentiableWithinAt
    obtain ⟨Kbd, hKbd0, hbd⟩ := doubledField_fderiv_bddOn_compact g gi hC hScomp
    obtain ⟨Kg, hLipg⟩ := doubledField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
    obtain ⟨Lg, hLip2⟩ := fderiv_doubledField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
    set Cc : ℝ := (Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd with hCcdef
    have hCc0 : 0 ≤ Cc := by
      rw [hCcdef]; have : (0:ℝ) ≤ (Lg:ℝ) := NNReal.coe_nonneg Lg; positivity
    have hlipfderiv : LipschitzOnWith ⟨Cc, hCc0⟩ (fderiv ℝ f) (Metric.ball Ξ₀ r) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      obtain ⟨Vx, Lx, hVx0, hVxode, hLxeq, hFDx⟩ := hdata x hx
      obtain ⟨Vy, Ly, hVy0, hVyode, hLyeq, hFDy⟩ := hdata y hy
      have hfx : fderiv ℝ f x = Lx := hFDx.fderiv
      have hfy : fderiv ℝ f y = Ly := hFDy.fderiv
      have hxadm : ‖x - Ξ₀‖ ≤ δ := hballadm x hx
      have hyadm : ‖y - Ξ₀‖ ≤ δ := hballadm y hy
      have hox : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (W x) (doubledField g gi (W x τ)) τ := hWode_glob s x hxadm
      have hoy : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (W y) (doubledField g gi (W y τ)) τ := hWode_glob s y hyadm
      have hSx : ∀ τ ∈ Set.Icc (0 : ℝ) 1, W x τ ∈ S := hmem_glob x hxadm
      have hSy : ∀ τ ∈ Set.Icc (0 : ℝ) 1, W y τ ∈ S := hmem_glob y hyadm
      have hbound := doubledFlow_joint_fderiv_lipschitz_in_basepoint g gi hLipg hLip2
        (Set.right_mem_Icc.mpr zero_le_one) hox hoy hSx hSy hKbd0
        (fun τ hτ => hbd _ (hSx τ hτ)) (fun τ hτ => hbd _ (hSy τ hτ))
        hVxode hVyode hVx0 hVy0 hLxeq hLyeq
      have hicx : W x 0 = x := hWzero s x hxadm
      have hicy : W y 0 = y := hWzero s y hyadm
      rw [hicx, hicy] at hbound
      rw [hfx, hfy, dist_eq_norm]
      calc ‖Lx - Ly‖
          ≤ (Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd * dist x y := hbound
        _ = (⟨Cc, hCc0⟩ : ℝ≥0) * dist x y := by
            rw [show ((⟨Cc, hCc0⟩ : ℝ≥0) : ℝ) = Cc from rfl, hCcdef]
    have hcont : ContinuousOn (fderiv ℝ f) (Metric.ball Ξ₀ r) := hlipfderiv.continuousOn
    have h1eq : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
    rw [h1eq, contDiffOn_succ_iff_fderiv_of_isOpen (Metric.isOpen_ball)]
    refine ⟨hdiff, ?_, ?_⟩
    · intro h; exact absurd h (by simp)
    · rw [contDiffOn_zero]; exact hcont
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (C) the neighborhood `U`, the base flow endpoint `Fbase`, and its admissibility.
  set U : Set (Point n × Point n) := Metric.ball (c : Point n × Point n) (δ / 2) with hUdef
  have hUopen : IsOpen U := by rw [hUdef]; exact Metric.isOpen_ball
  have hUmem : (c : Point n × Point n) ∈ U := by
    rw [hUdef]; exact Metric.mem_ball_self (by linarith)
  set Fbase : Point n × Point n → Point n × Point n :=
    fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2 1 with hFbasedef
  -- admissibility of base points in `U`.
  have hUadm : ∀ ξ ∈ U, ξ.1 ∈ K ∧ ‖ξ.2‖ ≤ ρ := by
    intro ξ hξ
    have hξn : dist ξ (c : Point n × Point n) < δ / 2 := by rwa [hUdef, Metric.mem_ball] at hξ
    have hb : dist ξ.1 z₀ ≤ dist ξ (c : Point n × Point n) := by
      rw [hcdef, Prod.dist_eq]; exact le_max_left _ _
    have hv : dist ξ.2 v₀ ≤ dist ξ (c : Point n × Point n) := by
      rw [hcdef, Prod.dist_eq]; exact le_max_right _ _
    refine ⟨?_, ?_⟩
    · apply interior_subset
      apply hr₁sub
      rw [Metric.mem_ball]
      have hlt : dist ξ.1 z₀ < δ / 2 := lt_of_le_of_lt hb hξn
      calc dist ξ.1 z₀ < δ / 2 := hlt
        _ ≤ r₁ / 4 := by linarith [hδler]
        _ < r₁ := by linarith
    · have hlt : dist ξ.2 v₀ < δ / 2 := lt_of_le_of_lt hv hξn
      have hle : ‖ξ.2 - v₀‖ < δ / 2 := by rwa [dist_eq_norm] at hlt
      calc ‖ξ.2‖ = ‖(ξ.2 - v₀) + v₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖ξ.2 - v₀‖ + ‖v₀‖ := norm_add_le _ _
        _ ≤ δ / 2 + ‖v₀‖ := by linarith
        _ ≤ ρ := by linarith [hδleV]
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (c₁) the joint FIRST derivative of `Fbase`, expressed via `Jsel`.
  have hFbaseFD : ∀ ξ ∈ U,
      ∃ L : (Point n × Point n) →L[ℝ] Point n × Point n,
        (∀ w : Point n × Point n, L w = Jsel ξ w 1) ∧ HasFDerivAt Fbase L ξ := by
    intro ξ hξ
    obtain ⟨hξ1K, hξ2ρ⟩ := hUadm ξ hξ
    have hξn : dist ξ (c : Point n × Point n) < δ / 2 := by rwa [hUdef, Metric.mem_ball] at hξ
    set rb : ℝ := δ / 2 - dist ξ (c : Point n × Point n) with hrbdef
    have hrb : 0 < rb := by rw [hrbdef]; linarith
    have hsubU : ∀ ζ : Point n × Point n, ζ ∈ Metric.ball ξ rb → ζ ∈ U := by
      intro ζ hζ
      rw [Metric.mem_ball] at hζ
      rw [hUdef, Metric.mem_ball]
      calc dist ζ (c : Point n × Point n) ≤ dist ζ ξ + dist ξ (c : Point n × Point n) :=
            dist_triangle _ _ _
        _ < rb + dist ξ (c : Point n × Point n) := by linarith
        _ = δ / 2 := by rw [hrbdef]; ring
    have hqmem : ∀ ζ ∈ Metric.ball ξ rb, ζ.1 ∈ K := fun ζ hζ => (hUadm ζ (hsubU ζ hζ)).1
    have hvmem : ∀ ζ ∈ Metric.ball ξ rb, ‖ζ.2‖ ≤ ρ := fun ζ hζ => (hUadm ζ (hsubU ζ hζ)).2
    -- control set `Sb`, suppliers.
    set Rb : ℝ := C₀ * ρ + rb with hRbdef
    set c₀ : Point n × Point n := (ξ.1, (0 : Point n)) with hc₀def
    set Sb : Set (Point n × Point n) := Metric.closedBall c₀ Rb with hSbdef
    have hSbcomp : IsCompact Sb := by rw [hSbdef]; exact isCompact_closedBall _ _
    have hSbconv : Convex ℝ Sb := by rw [hSbdef]; exact convex_closedBall _ _
    have hmem : ∀ ζ ∈ Metric.ball ξ rb, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        uniformFlowTube g gi hC hK ζ.1 ζ.2 τ ∈ Sb := by
      intro ζ hζ τ hτ
      have hconf := uniformFlowTube_spec_conf g gi hC hK ζ.1 (hqmem ζ hζ) ζ.2 (hvmem ζ hζ) τ hτ
      rw [hSbdef, Metric.mem_closedBall]
      calc dist (uniformFlowTube g gi hC hK ζ.1 ζ.2 τ) c₀
          ≤ dist (uniformFlowTube g gi hC hK ζ.1 ζ.2 τ) ((ζ.1, (0 : Point n)) : Point n × Point n)
              + dist ((ζ.1, (0 : Point n)) : Point n × Point n) c₀ := dist_triangle _ _ _
        _ ≤ C₀ * ρ + rb := by
            apply add_le_add
            · rw [dist_eq_norm]
              calc ‖uniformFlowTube g gi hC hK ζ.1 ζ.2 τ - ((ζ.1, (0 : Point n)) : Point n × Point n)‖
                  ≤ C₀ * ‖ζ.2‖ := hconf
                _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left (hvmem ζ hζ) hC₀0
            · rw [hc₀def, Prod.dist_eq]
              simp only [dist_self, max_eq_left, dist_nonneg]
              have hle : dist ζ.1 ξ.1 ≤ dist ζ ξ := by rw [Prod.dist_eq]; exact le_max_left _ _
              have hlt : dist ζ ξ < rb := by rwa [Metric.mem_ball] at hζ
              linarith
        _ = Rb := by rw [hRbdef]
    obtain ⟨M₂, hM₂0, hbound2⟩ := geodesicField_snd_fderiv_bddOn_compact g gi hC hSbcomp
    obtain ⟨Kz, hLip⟩ := geodesicField_lipschitzOnWith_of_isCompact_convex g gi hC hSbcomp hSbconv
    obtain ⟨Kbz, hKbz0, hbdz⟩ := geodesicField_fderiv_bddOn_compact g gi hC hSbcomp
    have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK ξ.1 ξ.2 τ)‖ ≤ Kbz :=
      fun τ hτ => hbdz _ (hmem ξ (Metric.mem_ball_self hrb) τ hτ)
    have hWode : ∀ ζ ∈ Metric.ball ξ rb, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (uniformFlowTube g gi hC hK ζ.1 ζ.2)
          (geodesicField g gi (uniformFlowTube g gi hC hK ζ.1 ζ.2 τ)) τ := by
      intro ζ hζ τ hτ
      exact uniformFlowTube_spec_ode g gi hC hK ζ.1 (hqmem ζ hζ) ζ.2 (hvmem ζ hζ) τ
        ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hIC : ∀ ζ ∈ Metric.ball ξ rb,
        uniformFlowTube g gi hC hK ζ.1 ζ.2 0 - uniformFlowTube g gi hC hK ξ.1 ξ.2 0 = ζ - ξ := by
      intro ζ hζ
      rw [uniformFlowTube_spec_ic g gi hC hK ζ.1 (hqmem ζ hζ) ζ.2 (hvmem ζ hζ),
        uniformFlowTube_spec_ic g gi hC hK ξ.1 hξ1K ξ.2 hξ2ρ]
    -- feed `V := fun w => Jsel ξ w` (the SAME Jacobi construction) to the abstract theorem.
    have hVode : ∀ w : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Jsel ξ w)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK ξ.1 ξ.2 τ) (Jsel ξ w τ)) τ :=
      fun w τ hτ => hJselode ξ w hξ1K hξ2ρ τ hτ
    obtain ⟨L, hLeq, hFD⟩ :=
      geodesicFlow_joint_hasFDerivAt_exists_atPoint_local
        (W := fun ζ => uniformFlowTube g gi hC hK ζ.1 ζ.2) (V := fun w => Jsel ξ w)
        g gi hC ξ hKbz0 (Set.right_mem_Icc.mpr zero_le_one) hSbconv hrb hbound2 hLip
        hWode hVode (fun w => hJsel0 ξ w) hIC hKb hmem
    exact ⟨L, hLeq, hFD⟩
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (c₃) the finite-basis reconstruction of `fderiv Fbase`.
  set e : Module.Basis (Fin n ⊕ Fin n) ℝ (Point n × Point n) :=
    (Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin n)) with hedef
  -- the coordinate map `ξ ↦ (fun j => Jsel ξ (e j) 1)` is `ContDiffOn ℝ 1` on `U`.
  have hcoordCD : ContDiffOn ℝ 1
      (fun ξ : Point n × Point n => fun j => Jsel ξ (e j) 1) U := by
    rw [contDiffOn_pi]
    intro j
    -- `ξ ↦ Jsel ξ (e j) 1 = snd (W (ξ, e j) 1)`.
    have hcompeq : (fun ξ : Point n × Point n => Jsel ξ (e j) 1)
        = fun ξ : Point n × Point n =>
            (ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n))
              ((fun Ξ => W Ξ 1) ((fun ξ' => (ξ', e j)) ξ)) := by
      funext ξ; rfl
    rw [hcompeq]
    apply (ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)).contDiff.comp_contDiffOn
    -- `(fun Ξ => W Ξ 1) ∘ (ξ ↦ (ξ, e j))` is `ContDiffOn ℝ 1` on `U`.
    apply (hDbl (e j)).comp
    · exact (contDiff_id.prodMk contDiff_const).contDiffOn
    · intro ξ hξ
      rw [Metric.mem_ball]
      have hξn : dist ξ (c : Point n × Point n) < δ / 2 := by rwa [hUdef, Metric.mem_ball] at hξ
      calc dist ((ξ, e j) : (Point n × Point n) × (Point n × Point n))
              (((c, e j)) : (Point n × Point n) × (Point n × Point n))
            = dist ξ (c : Point n × Point n) := by
              rw [Prod.dist_eq]; simp [dist_self]
        _ < δ / 2 := hξn
  -- reconstruct `ξ ↦ e.constrL (fun j => Jsel ξ (e j) 1)` as `ContDiffOn ℝ 1` (CLM-valued).
  have hreconCD : ContDiffOn ℝ 1
      (fun ξ : Point n × Point n => e.constrL (fun j => Jsel ξ (e j) 1)) U := by
    let Φ : ((Fin n ⊕ Fin n) → Point n × Point n) →ₗ[ℝ]
        ((Point n × Point n) →L[ℝ] Point n × Point n) :=
      (LinearMap.toContinuousLinearMap :
          ((Point n × Point n) →ₗ[ℝ] Point n × Point n) ≃ₗ[ℝ]
            ((Point n × Point n) →L[ℝ] Point n × Point n)).toLinearMap.comp
        (e.constr ℝ).toLinearMap
    have hΦcd : ContDiff ℝ (1 : ℕ∞) Φ.toContinuousLinearMap := Φ.toContinuousLinearMap.contDiff
    have heq : (fun ξ : Point n × Point n => e.constrL (fun j => Jsel ξ (e j) 1))
        = fun ξ => Φ.toContinuousLinearMap (fun j => Jsel ξ (e j) 1) := by
      funext ξ
      simp only [LinearMap.coe_toContinuousLinearMap', Φ, LinearMap.comp_apply,
        LinearEquiv.coe_coe, Module.Basis.constrL]
    rw [heq]
    exact hΦcd.comp_contDiffOn hcoordCD
  -- `fderiv Fbase = e.constrL (…)` on `U` (two CLMs agreeing on the basis).
  have hfderivEq : ∀ ξ ∈ U, fderiv ℝ Fbase ξ = e.constrL (fun j => Jsel ξ (e j) 1) := by
    intro ξ hξ
    obtain ⟨L, hLeq, hFD⟩ := hFbaseFD ξ hξ
    have hfd : fderiv ℝ Fbase ξ = L := hFD.fderiv
    rw [hfd]
    apply ContinuousLinearMap.coe_injective
    apply e.ext
    intro j
    simp only [ContinuousLinearMap.coe_coe, Module.Basis.constrL_basis]
    exact hLeq (e j)
  -- hence `ContDiffOn ℝ 1 (fderiv Fbase) U`.
  have hfderivCD : ContDiffOn ℝ 1 (fderiv ℝ Fbase) U := hreconCD.congr hfderivEq
  -- differentiability of `Fbase` on `U`.
  have hFbaseDiff : DifferentiableOn ℝ Fbase U := by
    intro ξ hξ
    obtain ⟨L, _, hFD⟩ := hFbaseFD ξ hξ
    exact hFD.differentiableAt.differentiableWithinAt
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (d) assemble `ContDiffOn ℝ 2 Fbase U`, then project with `fst`.
  have hFbaseCD2 : ContDiffOn ℝ 2 Fbase U := by
    have h2eq : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
    rw [h2eq, contDiffOn_succ_iff_fderiv_of_isOpen hUopen]
    refine ⟨hFbaseDiff, ?_, hfderivCD⟩
    · intro h; exact absurd h (by simp)
  refine ⟨U, hUopen, hUmem, ?_⟩
  have hexpeq : (fun ξ : Point n × Point n =>
        uniformFlowExp g gi hC hK ξ.1 ξ.2)
      = fun ξ => (ContinuousLinearMap.fst ℝ (Point n) (Point n)) (Fbase ξ) := by
    funext ξ; rfl
  rw [hexpeq]
  exact (ContinuousLinearMap.fst ℝ (Point n) (Point n)).contDiff.comp_contDiffOn hFbaseCD2

end QIQTH.ExpMap
