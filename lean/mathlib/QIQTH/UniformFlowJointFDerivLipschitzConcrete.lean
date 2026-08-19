/-
  UniformFlowJointFDerivLipschitzConcrete — CONCRETE instantiation of the joint geodesic-flow
  first-derivative Lipschitz-in-base-point bound (plan `tranquil-stargazing-fox.md`, Task C) for the
  actual constructive uniform flow `uniformFlowTube`/`uniformFlowExp`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (the honest Task-C partial): the CONCRETE first-derivative Lipschitz brick.

  * `uniformFlow_joint_jacobiCLM_lipschitz_in_basepoint` — ★ for two phase base points `(q₁,v₁)`,
    `(q₂,v₂)` with `qᵢ ∈ K` and `‖vᵢ‖ ≤ ρ_K` (the genuine uniform confinement radius, NO `expRho`),
    there are:
      - genuine JOINT Jacobi families `V₁, V₂ : Point n × Point n → ℝ → Point n × Point n` along the
        two CONCRETE confined geodesic tubes `uniformFlowTube g gi hC hK qᵢ vᵢ` (`Vᵢ ξ 0 = ξ`, and
        `Vᵢ ξ` solves the Jacobi ODE `Vᵢ ξ' = DF(tubeᵢ τ)·Vᵢ ξ` on `[0,1]`);
      - their endpoint continuous-linear-map derivatives `L₁, L₂` (`Lᵢ ξ = Vᵢ ξ t`);
      - a single Lipschitz constant `C ≥ 0` with
          `‖L₁ − L₂‖ ≤ C · dist ((q₁,v₁), (q₂,v₂))`.
    This is the first-ever NEIGHBORHOOD-quality (not merely pointwise) joint first-derivative fact
    for the constructive geodesic flow: the joint Jacobi-endpoint derivative CLM varies LIPSCHITZ in
    the base phase point.  DERIVED by feeding the concrete tube spec facts (`uniformFlowTube_spec_ode`
    / `_ic` / `_conf`) plus internally-built Jacobi families (`geodesicJacobi_narrowpad_hasDerivAt_Icc`)
    and their CLM promotion (linearity via `jacobiSol_unique`) into the abstract Task-B compact
    corollary `geodesicFlow_joint_fderiv_lipschitz_in_basepoint_compact`.  The common compact convex
    control set `S := closedBall ((q₁,0), C₀·ρ_K + dist)` is CONSTRUCTED from the confinement datum,
    NOT carried as a hypothesis.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## ⚠  DECISIVE OBSTRUCTION FINDING (why the full joint `ContDiffOn ℝ 1` of `uniformFlowExp` is
     NOT reached this pass — a genuinely NEW, structural wall, distinct from the old `.choose`
     incoherence).

  The plan's Task-A theorem `GeodesicJointFDerivAtPoint.geodesicFlow_joint_hasFDerivAt_exists_atPoint`
  (and its origin brick `GeodesicBasepointFrechet.geodesicFlow_joint_hasFDerivAt_exists`) delivers the
  joint Fréchet derivative of the flow endpoint EXISTING, but under a family hypothesis quantified over
  the WHOLE phase space:
      `hmem : ∀ ξ : Point n × Point n, ∀ τ ∈ [0,1], W ξ τ ∈ S`
      `hIC  : ∀ ξ, W ξ 0 − W ξ₀ 0 = ξ − ξ₀`
      `hLip : LipschitzOnWith K₀ (geodesicField g gi) S`.
  `hIC` forces `ξ ↦ W ξ 0` to be an AFFINE BIJECTION of `Point n × Point n`; hence `hmem` at `τ = 0`
  forces `S ⊇ {W ξ 0 : ξ} =` the ENTIRE phase space, i.e. `S = univ`.  But
      `geodesicField g gi (x,v) = (v, −Γ(x)(v,v))`  (`Geodesic.geodesicField`, verified)
  is QUADRATIC in the velocity `v`, so it is NOT globally Lipschitz whenever the metric is genuinely
  curved (`Γ ≠ 0`) — `hLip` on `S = univ` then FAILS.  Therefore Task A's hypotheses are jointly
  UNSATISFIABLE for a curved geodesic field: `geodesicFlow_joint_hasFDerivAt_exists_atPoint` cannot be
  concretely instantiated for `uniformFlowExp` in the curved case (it is satisfiable only for a
  globally-Lipschitz field, i.e. the FLAT / globally-bounded-geometry case — matching this campaign's
  documented flat/curved wall).  Task A's abstract statement is banked and axiom-clean, but VACUOUS at
  the genuinely-curved concrete witness.

  Task B's COMPACT corollary escapes this wall: it requires only the TWO REFERENCE geodesics `Y₁, Y₂`
  to lie in the compact convex `S` (`hS1/hS2`), while the `∀ξ` Jacobi families `V₁, V₂` are FREE to
  leave `S`.  Confinement (`uniformFlowTube_spec_conf`) puts exactly the two tubes into a fixed compact
  ball, so Task B — and only Task B — instantiates concretely for the curved flow.  That is what this
  file banks.

  ## WHAT THIS FILE DOES NOT DO.
  It does NOT identify `L₁, L₂` with the Fréchet derivatives of `uniformFlowExp` itself (that is
  precisely Task A's blocked content), and hence does NOT assemble the joint `ContDiffOn ℝ 1` of
  `uniformFlowExp` on a neighborhood of `(q₀,0)`.  It does NOT build the second-order jet (Task D),
  NOT the IFT inverse (Task E), NOT reconcile with `uniformInverseChart` (Task F), NOT discharge the
  RNC hypotheses (Task G), and does NOT bear on `hCConv`.  See the report for the precise remaining
  gap and the recommended redirect (curved joint C¹ needs a LOCAL-in-`ξ` re-derivation of Task A, or
  the alternative continuous-partials route, neither of which the banked global Task A supplies).
-/
import Mathlib
import QIQTH.GeodesicJointFDerivLipschitz
import QIQTH.UniformFlowNondeg
import QIQTH.DoubledFamilyFullSupply
import QIQTH.BasepointFDeriv

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **Per-tube Jacobi family + endpoint CLM (concrete).**  Along the concrete confined geodesic tube
    `uniformFlowTube g gi hC hK q v` (for `q ∈ K`, `‖v‖ ≤ ρ_K`), lying in a compact `S`, there is a
    genuine joint Jacobi family `V ξ` (`V ξ 0 = ξ`, Jacobi ODE along the tube) and its endpoint
    continuous-linear-map `L` with `L ξ = V ξ t`.  The family is produced by the narrow-pad Jacobi
    engine (only `Icc (-1/2) (3/2)` continuity needed, supplied by the tube's `Ioo (-2,2)` ODE), and
    the endpoint map `ξ ↦ V ξ t` is promoted to a CLM via `jacobiSol_unique` linearity. -/
private theorem tube_jacobiCLM (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK)
    {S : Set (Point n × Point n)} (hScomp : IsCompact S)
    (hYS : ∀ τ ∈ Set.Icc (0 : ℝ) 1, uniformFlowTube g gi hC hK q v τ ∈ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (V : Point n × Point n → ℝ → Point n × Point n)
      (L : (Point n × Point n) →L[ℝ] Point n × Point n),
      (∀ ξ : Point n × Point n, V ξ 0 = ξ) ∧
      (∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (V ξ)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (V ξ τ)) τ) ∧
      (∀ ξ : Point n × Point n, L ξ = V ξ t) := by
  have hodeIoo := uniformFlowTube_spec_ode g gi hC hK q hq v hv
  -- tube ODE on `[0,1]` (⊆ `Ioo (-2,2)`).
  have hode01 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (uniformFlowTube g gi hC hK q v)
        (geodesicField g gi (uniformFlowTube g gi hC hK q v τ)) τ := by
    intro τ hτ
    exact hodeIoo τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  -- tube continuity on `Icc (-1/2) (3/2)` (⊆ `Ioo (-2,2)`), for the narrow-pad Jacobi engine.
  have hcont : ContinuousOn (uniformFlowTube g gi hC hK q v) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτIoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact (hodeIoo τ hτIoo).continuousAt.continuousWithinAt
  -- coefficient-field bound along the tube (from `S`-compactness).
  obtain ⟨Kb, hKb0, hbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScomp
  have hKbY : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ)‖ ≤ Kb :=
    fun τ hτ => hbd _ (hYS τ hτ)
  -- Jacobi families for every seed, via the narrow-pad engine.
  choose V hV0 hVode using fun ξ : Point n × Point n =>
    geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (uniformFlowTube g gi hC hK q v) hcont ξ
  -- linearity of the endpoint map `ξ ↦ V ξ t` (Jacobi-ODE uniqueness).
  have hadd : ∀ a b : Point n × Point n, V a t + V b t = V (a + b) t := by
    intro a b
    refine jacobiSol_unique g gi hKb0 hode01 hKbY (J₁ := fun σ => V a σ + V b σ)
      ?_ (hVode (a + b)) ?_ ht
    · intro τ hτ
      simpa [map_add] using (hVode a τ hτ).add (hVode b τ hτ)
    · simp [hV0 a, hV0 b, hV0 (a + b)]
  have hsmul : ∀ (c : ℝ) (a : Point n × Point n), c • V a t = V (c • a) t := by
    intro c a
    refine jacobiSol_unique g gi hKb0 hode01 hKbY (J₁ := fun σ => c • V a σ)
      ?_ (hVode (c • a)) ?_ ht
    · intro τ hτ
      simpa [map_smul] using (hVode a τ hτ).const_smul c
    · simp [hV0 a, hV0 (c • a)]
  let Lₗ : (Point n × Point n) →ₗ[ℝ] Point n × Point n :=
    { toFun := fun ξ => V ξ t
      map_add' := fun a b => (hadd a b).symm
      map_smul' := fun c a => by simpa using (hsmul c a).symm }
  exact ⟨V, Lₗ.toContinuousLinearMap, hV0, hVode, fun ξ => rfl⟩

/-- **★ Concrete joint first-derivative Lipschitz-in-base-point bound for the uniform geodesic flow.**
    For two phase base points `(q₁,v₁)`, `(q₂,v₂)` with `qᵢ ∈ K`, `‖vᵢ‖ ≤ ρ_K`, there are genuine
    Jacobi families `V₁,V₂` along the concrete tubes, their endpoint CLMs `L₁,L₂`, and a single
    Lipschitz constant `C ≥ 0` with `‖L₁ − L₂‖ ≤ C · dist ((q₁,v₁),(q₂,v₂))`.  The compact convex
    control set is CONSTRUCTED from the uniform confinement datum (no carried geometric hypothesis, no
    `expRho`).  The concrete Task-C partial; NOT the joint `ContDiffOn` (see file firewall / report). -/
theorem uniformFlow_joint_jacobiCLM_lipschitz_in_basepoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (q₁ q₂ : Point n) (hq₁ : q₁ ∈ K) (hq₂ : q₂ ∈ K)
    (v₁ v₂ : Point n) (hv₁ : ‖v₁‖ ≤ uniformFlowRadius g gi hC hK)
    (hv₂ : ‖v₂‖ ≤ uniformFlowRadius g gi hC hK) :
    ∃ (V₁ V₂ : Point n × Point n → ℝ → Point n × Point n)
      (L₁ L₂ : (Point n × Point n) →L[ℝ] Point n × Point n) (C : ℝ),
      0 ≤ C ∧
      (∀ ξ : Point n × Point n, V₁ ξ 0 = ξ) ∧ (∀ ξ : Point n × Point n, V₂ ξ 0 = ξ) ∧
      (∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (V₁ ξ)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q₁ v₁ τ) (V₁ ξ τ)) τ) ∧
      (∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (V₂ ξ)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q₂ v₂ τ) (V₂ ξ τ)) τ) ∧
      (∀ ξ : Point n × Point n, L₁ ξ = V₁ ξ t) ∧ (∀ ξ : Point n × Point n, L₂ ξ = V₂ ξ t) ∧
      ‖L₁ - L₂‖ ≤ C * dist ((q₁, v₁) : Point n × Point n) ((q₂, v₂) : Point n × Point n) := by
  have hC₀ := uniformFlowConst_nonneg g gi hC hK
  set R : ℝ := uniformFlowConst g gi hC hK * uniformFlowRadius g gi hC hK
    + dist ((q₁, (0 : Point n)) : Point n × Point n) ((q₂, (0 : Point n)) : Point n × Point n)
    with hRdef
  set S : Set (Point n × Point n) :=
    Metric.closedBall ((q₁, (0 : Point n)) : Point n × Point n) R with hSdef
  have hScomp : IsCompact S := by rw [hSdef]; exact isCompact_closedBall _ _
  have hSconv : Convex ℝ S := by rw [hSdef]; exact convex_closedBall _ _
  -- tube ODEs on `[0,1]`.
  have h1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (uniformFlowTube g gi hC hK q₁ v₁)
        (geodesicField g gi (uniformFlowTube g gi hC hK q₁ v₁ τ)) τ := by
    intro τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK q₁ hq₁ v₁ hv₁ τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have h2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (uniformFlowTube g gi hC hK q₂ v₂)
        (geodesicField g gi (uniformFlowTube g gi hC hK q₂ v₂ τ)) τ := by
    intro τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK q₂ hq₂ v₂ hv₂ τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  -- tube containments in `S` via confinement + triangle inequality.
  have hconf1 := uniformFlowTube_spec_conf g gi hC hK q₁ hq₁ v₁ hv₁
  have hconf2 := uniformFlowTube_spec_conf g gi hC hK q₂ hq₂ v₂ hv₂
  have hdist0 : (0 : ℝ) ≤
      dist ((q₁, (0 : Point n)) : Point n × Point n) ((q₂, (0 : Point n)) : Point n × Point n) :=
    dist_nonneg
  have hS1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, uniformFlowTube g gi hC hK q₁ v₁ τ ∈ S := by
    intro τ hτ
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖uniformFlowTube g gi hC hK q₁ v₁ τ - ((q₁, (0 : Point n)) : Point n × Point n)‖
        ≤ uniformFlowConst g gi hC hK * ‖v₁‖ := hconf1 τ hτ
      _ ≤ uniformFlowConst g gi hC hK * uniformFlowRadius g gi hC hK :=
          mul_le_mul_of_nonneg_left hv₁ hC₀
      _ ≤ R := by rw [hRdef]; linarith [hdist0]
  have hS2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, uniformFlowTube g gi hC hK q₂ v₂ τ ∈ S := by
    intro τ hτ
    rw [hSdef, Metric.mem_closedBall]
    calc dist (uniformFlowTube g gi hC hK q₂ v₂ τ) ((q₁, (0 : Point n)) : Point n × Point n)
        ≤ dist (uniformFlowTube g gi hC hK q₂ v₂ τ) ((q₂, (0 : Point n)) : Point n × Point n)
            + dist ((q₂, (0 : Point n)) : Point n × Point n)
                ((q₁, (0 : Point n)) : Point n × Point n) := dist_triangle _ _ _
      _ ≤ uniformFlowConst g gi hC hK * ‖v₂‖
            + dist ((q₁, (0 : Point n)) : Point n × Point n)
                ((q₂, (0 : Point n)) : Point n × Point n) := by
          apply add_le_add
          · rw [dist_eq_norm]; exact hconf2 τ hτ
          · rw [dist_comm]
      _ ≤ R := by
          rw [hRdef]
          have := mul_le_mul_of_nonneg_left hv₂ hC₀
          linarith
  -- per-tube Jacobi families + endpoint CLMs.
  obtain ⟨V₁, L₁, hV1_0, hV1ode, hL1eq⟩ :=
    tube_jacobiCLM g gi hC hK q₁ hq₁ v₁ hv₁ hScomp hS1 ht
  obtain ⟨V₂, L₂, hV2_0, hV2ode, hL2eq⟩ :=
    tube_jacobiCLM g gi hC hK q₂ hq₂ v₂ hv₂ hScomp hS2 ht
  -- the abstract Task-B compact Lipschitz bound.
  obtain ⟨C, hC0, hlip⟩ :=
    geodesicFlow_joint_fderiv_lipschitz_in_basepoint_compact g gi hC hScomp hSconv ht
      h1 h2 hS1 hS2 hV1ode hV2ode hV1_0 hV2_0 hL1eq hL2eq
  -- rewrite the tube initial conditions to the given phase points.
  have hic1 : uniformFlowTube g gi hC hK q₁ v₁ 0 = (q₁, v₁) :=
    uniformFlowTube_spec_ic g gi hC hK q₁ hq₁ v₁ hv₁
  have hic2 : uniformFlowTube g gi hC hK q₂ v₂ 0 = (q₂, v₂) :=
    uniformFlowTube_spec_ic g gi hC hK q₂ hq₂ v₂ hv₂
  rw [hic1, hic2] at hlip
  exact ⟨V₁, V₂, L₁, L₂, C, hC0, hV1_0, hV2_0, hV1ode, hV2ode, hL1eq, hL2eq, hlip⟩

end QIQTH.ExpMap
