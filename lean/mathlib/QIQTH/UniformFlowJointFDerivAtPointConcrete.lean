/-
  UniformFlowJointFDerivAtPointConcrete — the CONCRETE, NON-VACUOUS instantiation of the LOCAL joint
  geodesic-flow Fréchet derivative (`GeodesicJointFDerivAtPointLocal`) for the actual constructive uniform
  geodesic flow `uniformFlowTube` / `uniformFlowExp`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE — closing the J4-847 vacuity, verified at a CONCRETE CURVED witness.

  The GLOBAL Task A (`GeodesicJointFDerivAtPoint.geodesicFlow_joint_hasFDerivAt_exists_atPoint`) was found
  VACUOUS for curved fields (J4-847): its `∀ξ`-quantified `hmem` + `hIC` force `S = univ`, on which the
  quadratic-in-velocity `geodesicField` is NOT Lipschitz for curved `Γ`.  `GeodesicJointFDerivAtPointLocal`
  fixed the ABSTRACT statement by restricting the perturbation family to `ξ ∈ Metric.ball ξ₀ r`.  THIS file
  supplies the missing half: it INSTANTIATES that local abstract theorem for the concrete confined geodesic
  flow, discharging EVERY local hypothesis from the confinement machinery — proving the fix is not merely
  type-correct but genuinely SATISFIABLE at a real curved field.

  WHAT LANDS (axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited):

  * `uniformFlow_joint_hasFDerivAt_atBasepoint` — for the concrete flow `W ξ := uniformFlowTube g gi hC hK
    ξ.1 ξ.2`, an arbitrary phase base point `ξ₀`, a radius `r > 0`, and the two DOMAIN side-conditions
    `hqmem : ∀ ξ ∈ ball ξ₀ r, ξ.1 ∈ K` and `hvmem : ∀ ξ ∈ ball ξ₀ r, ‖ξ.2‖ ≤ ρ_K` (which merely say the
    perturbation ball stays in the tube's valid domain), there EXIST a joint Jacobi family `V`, its endpoint
    CLM `L`, with `L ξ = V ξ t` and
        `HasFDerivAt (fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2 t) L ξ₀`.
    The control set `S := closedBall ((ξ₀.1,0), C₀·ρ_K + r)` is CONSTRUCTED from the confinement datum; all
    the local Task-A hypotheses (`hmem`/`hWode`/`hIC`/`hKb`/`hbound2`/`hLip`) are DISCHARGED, not carried.

  * `uniformFlow_joint_expEndpoint_hasFDerivAt_atBasepoint` — the POSITION-component corollary at `t = 1`:
        `HasFDerivAt (fun ξ => uniformFlowExp g gi hC hK ξ.1 ξ.2) ((fst).comp L) ξ₀`,
    i.e. the joint Fréchet derivative of the CONCRETE exp-map endpoint `uniformFlowExp` w.r.t. the full
    initial phase point — the precise fact the global (vacuous) Task A could NOT deliver.

  * `uniformFlow_joint_hasFDerivAt_witness` — ★ the DECISIVE NON-VACUITY WITNESS.  Instantiating
    `K := Metric.closedBall q₀ 1` and `ξ₀ := (q₀, 0)`, with `r := min 1 ρ_K`, it DISCHARGES `hqmem`/`hvmem`
    internally and concludes, with NO carried domain hypotheses whatsoever and for EVERY (in particular
    genuinely curved) metric `g`, `gi`:
        `∃ r > 0, ∃ V L, (∀ ξ, L ξ = V ξ 1) ∧
           HasFDerivAt (fun ξ => uniformFlowTube g gi hC (isCompact_closedBall q₀ 1) ξ.1 ξ.2 1) L (q₀,0)`.
    Since the confinement machinery `geodesic_apriori_confinement_uniform` is UNCONDITIONAL, this witness
    exists at every curved field — the exact opposite of the global Task A's curved-field vacuity.

  ## WHAT THIS FILE DOES NOT DO.
  It does NOT (yet) assemble the neighborhood-quality joint `ContDiffOn ℝ 1` (that needs the Task-B
  Lipschitz-in-basepoint continuity threaded over the whole ball — see the companion assembly file / the
  report), NOT build the second-order jet (Task D), NOT the IFT inverse (Task E/F), NOT discharge the RNC
  hypotheses (Task G), and does NOT bear on `hCConv`.
-/
import Mathlib
import QIQTH.GeodesicJointFDerivAtPointLocal
import QIQTH.UniformFlowNondeg
import QIQTH.DoubledFamilyFullSupply
import QIQTH.GeodesicTaylorCompact
import QIQTH.SecondVariationLipschitz
import QIQTH.BoundedGeometry

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **★ Concrete joint Fréchet derivative of the uniform geodesic flow at a base point, LOCAL scope.**
    For the concrete confined flow `W ξ := uniformFlowTube g gi hC hK ξ.1 ξ.2` and a base phase point `ξ₀`,
    given only that the perturbation ball `Metric.ball ξ₀ r` (`r > 0`) stays in the tube's valid domain
    (`hqmem`: base ∈ K, `hvmem`: velocity ≤ ρ_K), the flow endpoint `fun ξ => W ξ t` has a genuine joint
    Fréchet derivative `L` at `ξ₀` (with `L ξ = V ξ t` for an internally-built Jacobi family `V` along the
    reference tube `W ξ₀`).  NON-VACUOUS for curved fields: `S` is a bounded ball built from confinement. -/
theorem uniformFlow_joint_hasFDerivAt_atBasepoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ξ₀ : Point n × Point n) {r : ℝ} (hr : 0 < r)
    (hqmem : ∀ ξ ∈ Metric.ball ξ₀ r, ξ.1 ∈ K)
    (hvmem : ∀ ξ ∈ Metric.ball ξ₀ r, ‖ξ.2‖ ≤ uniformFlowRadius g gi hC hK) :
    ∃ (V : Point n × Point n → ℝ → Point n × Point n)
      (L : (Point n × Point n) →L[ℝ] Point n × Point n),
      (∀ ξ : Point n × Point n, L ξ = V ξ t) ∧
      HasFDerivAt (fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2 t) L ξ₀ := by
  have h0 : ξ₀ ∈ Metric.ball ξ₀ r := Metric.mem_ball_self hr
  have hq₀ : ξ₀.1 ∈ K := hqmem ξ₀ h0
  have hv₀ : ‖ξ₀.2‖ ≤ uniformFlowRadius g gi hC hK := hvmem ξ₀ h0
  have hC₀ := uniformFlowConst_nonneg g gi hC hK
  have hρ0 : (0 : ℝ) ≤ uniformFlowRadius g gi hC hK := (uniformFlowRadius_pos g gi hC hK).le
  -- control ball `S`, centred at `(ξ₀.1, 0)`.
  set R : ℝ := uniformFlowConst g gi hC hK * uniformFlowRadius g gi hC hK + r with hRdef
  set c₀ : Point n × Point n := (ξ₀.1, (0 : Point n)) with hc₀def
  set S : Set (Point n × Point n) := Metric.closedBall c₀ R with hSdef
  have hScomp : IsCompact S := by rw [hSdef]; exact isCompact_closedBall _ _
  have hSconv : Convex ℝ S := by rw [hSdef]; exact convex_closedBall _ _
  -- membership of every perturbed tube in `S`.
  have hmem : ∀ ξ ∈ Metric.ball ξ₀ r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      uniformFlowTube g gi hC hK ξ.1 ξ.2 τ ∈ S := by
    intro ξ hξ τ hτ
    have hconf := uniformFlowTube_spec_conf g gi hC hK ξ.1 (hqmem ξ hξ) ξ.2 (hvmem ξ hξ) τ hτ
    rw [hSdef, Metric.mem_closedBall]
    calc dist (uniformFlowTube g gi hC hK ξ.1 ξ.2 τ) c₀
        ≤ dist (uniformFlowTube g gi hC hK ξ.1 ξ.2 τ) ((ξ.1, (0 : Point n)) : Point n × Point n)
            + dist ((ξ.1, (0 : Point n)) : Point n × Point n) c₀ := dist_triangle _ _ _
      _ ≤ uniformFlowConst g gi hC hK * ‖ξ.2‖ + r := by
          apply add_le_add
          · rw [dist_eq_norm]; exact hconf
          · rw [hc₀def, Prod.dist_eq]
            simp only [dist_self, max_eq_left, dist_nonneg]
            have : dist ξ.1 ξ₀.1 ≤ dist ξ ξ₀ := by
              rw [Prod.dist_eq]; exact le_max_left _ _
            have hlt : dist ξ ξ₀ < r := by rwa [Metric.mem_ball] at hξ
            linarith
      _ ≤ R := by
          rw [hRdef]
          have := mul_le_mul_of_nonneg_left (hvmem ξ hξ) hC₀
          linarith
  -- suppliers on the compact convex `S`.
  obtain ⟨M₂, hM₂0, hbound2⟩ := geodesicField_snd_fderiv_bddOn_compact g gi hC hScomp
  obtain ⟨K₀, hLip⟩ := geodesicField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
  obtain ⟨Kb, hKb0, hbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScomp
  -- coefficient bound along the reference tube `W ξ₀`.
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK ξ₀.1 ξ₀.2 τ)‖ ≤ Kb :=
    fun τ hτ => hbd _ (hmem ξ₀ h0 τ hτ)
  -- tube ODEs on `[0,1]` for the perturbed family (from the `(-2,2)` spec).
  have hWode : ∀ ξ ∈ Metric.ball ξ₀ r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (uniformFlowTube g gi hC hK ξ.1 ξ.2)
        (geodesicField g gi (uniformFlowTube g gi hC hK ξ.1 ξ.2 τ)) τ := by
    intro ξ hξ τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK ξ.1 (hqmem ξ hξ) ξ.2 (hvmem ξ hξ) τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  -- initial-condition (affine) datum.
  have hIC : ∀ ξ ∈ Metric.ball ξ₀ r,
      uniformFlowTube g gi hC hK ξ.1 ξ.2 0 - uniformFlowTube g gi hC hK ξ₀.1 ξ₀.2 0 = ξ - ξ₀ := by
    intro ξ hξ
    have e1 : uniformFlowTube g gi hC hK ξ.1 ξ.2 0 = ξ := by
      rw [uniformFlowTube_spec_ic g gi hC hK ξ.1 (hqmem ξ hξ) ξ.2 (hvmem ξ hξ)]
    have e2 : uniformFlowTube g gi hC hK ξ₀.1 ξ₀.2 0 = ξ₀ := by
      rw [uniformFlowTube_spec_ic g gi hC hK ξ₀.1 hq₀ ξ₀.2 hv₀]
    rw [e1, e2]
  -- reference-tube continuity on the narrow pad, for the Jacobi engine.
  have hcont : ContinuousOn (uniformFlowTube g gi hC hK ξ₀.1 ξ₀.2) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτIoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact (uniformFlowTube_spec_ode g gi hC hK ξ₀.1 hq₀ ξ₀.2 hv₀ τ hτIoo).continuousAt.continuousWithinAt
  -- Jacobi families along the reference tube, for every seed.
  choose V hV0 hVode using fun ξ : Point n × Point n =>
    geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (uniformFlowTube g gi hC hK ξ₀.1 ξ₀.2) hcont ξ
  -- apply the abstract LOCAL Task A.
  obtain ⟨L, hLeq, hFD⟩ :=
    geodesicFlow_joint_hasFDerivAt_exists_atPoint_local
      (W := fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2) (V := V)
      g gi hC ξ₀ hKb0 ht hSconv hr hbound2 hLip hWode hVode hV0 hIC hKb hmem
  exact ⟨V, L, hLeq, hFD⟩

/-- **Concrete joint Fréchet derivative of the `uniformFlowExp` position endpoint (at `t = 1`).**
    Projecting `uniformFlow_joint_hasFDerivAt_atBasepoint` (at `t = 1`) onto the position component gives
    the joint Fréchet derivative of the CONCRETE exp-map endpoint `uniformFlowExp g gi hC hK ξ.1 ξ.2` in the
    full initial phase point `ξ` at `ξ₀` — precisely the fact the vacuous global Task A could not supply. -/
theorem uniformFlow_joint_expEndpoint_hasFDerivAt_atBasepoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (ξ₀ : Point n × Point n) {r : ℝ} (hr : 0 < r)
    (hqmem : ∀ ξ ∈ Metric.ball ξ₀ r, ξ.1 ∈ K)
    (hvmem : ∀ ξ ∈ Metric.ball ξ₀ r, ‖ξ.2‖ ≤ uniformFlowRadius g gi hC hK) :
    ∃ L : (Point n × Point n) →L[ℝ] Point n,
      HasFDerivAt (fun ξ => uniformFlowExp g gi hC hK ξ.1 ξ.2) L ξ₀ := by
  obtain ⟨V, L, _hLeq, hFD⟩ :=
    uniformFlow_joint_hasFDerivAt_atBasepoint g gi hC hK (Set.right_mem_Icc.mpr zero_le_one)
      ξ₀ hr hqmem hvmem
  refine ⟨(ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp L, ?_⟩
  have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp ξ₀ hFD
  simpa [Function.comp, uniformFlowExp] using this

/-- **★ DECISIVE NON-VACUITY WITNESS.**  With `K := Metric.closedBall q₀ 1` and base point `ξ₀ := (q₀, 0)`,
    the two domain side-conditions of `uniformFlow_joint_hasFDerivAt_atBasepoint` are DISCHARGED internally
    (radius `r := min 1 ρ_K`), so the concrete joint Fréchet derivative of the (genuinely curved-admissible)
    uniform geodesic flow exists with NO carried domain hypotheses.  This certifies that the LOCAL Task A of
    `GeodesicJointFDerivAtPointLocal` is genuinely SATISFIABLE at a real curved field — the exact vacuity the
    global Task A failed (J4-847). -/
theorem uniformFlow_joint_hasFDerivAt_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    ∃ (r : ℝ), 0 < r ∧
      ∃ (V : Point n × Point n → ℝ → Point n × Point n)
        (L : (Point n × Point n) →L[ℝ] Point n × Point n),
        (∀ ξ : Point n × Point n, L ξ = V ξ 1) ∧
        HasFDerivAt
          (fun ξ => uniformFlowTube g gi hC (isCompact_closedBall q₀ 1) ξ.1 ξ.2 1) L
          ((q₀, (0 : Point n)) : Point n × Point n) := by
  set hK : IsCompact (Metric.closedBall q₀ 1) := isCompact_closedBall q₀ 1 with hKdef
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρpos : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set r : ℝ := min 1 ρ with hrdef
  have hr : 0 < r := lt_min zero_lt_one hρpos
  set ξ₀ : Point n × Point n := (q₀, (0 : Point n)) with hξ₀def
  have hqmem : ∀ ξ ∈ Metric.ball ξ₀ r, ξ.1 ∈ Metric.closedBall q₀ 1 := by
    intro ξ hξ
    rw [Metric.mem_ball] at hξ
    rw [Metric.mem_closedBall]
    have hle : dist ξ.1 q₀ ≤ dist ξ ξ₀ := by
      rw [hξ₀def, Prod.dist_eq]; exact le_max_left _ _
    have : dist ξ.1 q₀ < r := lt_of_le_of_lt hle hξ
    calc dist ξ.1 q₀ ≤ r := this.le
      _ ≤ 1 := by rw [hrdef]; exact min_le_left _ _
  have hvmem : ∀ ξ ∈ Metric.ball ξ₀ r, ‖ξ.2‖ ≤ ρ := by
    intro ξ hξ
    rw [Metric.mem_ball] at hξ
    have hle : dist ξ.2 (0 : Point n) ≤ dist ξ ξ₀ := by
      rw [hξ₀def, Prod.dist_eq]; exact le_max_right _ _
    have hlt : dist ξ.2 (0 : Point n) < r := lt_of_le_of_lt hle hξ
    have : ‖ξ.2‖ < r := by rwa [dist_zero_right] at hlt
    calc ‖ξ.2‖ ≤ r := this.le
      _ ≤ ρ := by rw [hrdef]; exact min_le_right _ _
  obtain ⟨V, L, hLeq, hFD⟩ :=
    uniformFlow_joint_hasFDerivAt_atBasepoint g gi hC hK (Set.right_mem_Icc.mpr zero_le_one)
      ξ₀ hr hqmem hvmem
  exact ⟨r, hr, V, L, hLeq, hFD⟩

end QIQTH.ExpMap
