/-
  UniformFlowJointContDiffOneConcrete — the JOINT `ContDiffOn ℝ 1` (neighborhood-quality C¹) of the
  concrete confined geodesic-flow endpoint `fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2 t`, assembled from
  the LOCAL Task A pointwise Fréchet derivative (`GeodesicJointFDerivAtPointLocal`) + the Task-B
  Lipschitz-in-base-point continuity (`GeodesicJointFDerivLipschitz`) over a FIXED uniform control set.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DELIVERABLE — plan Task C's ORIGINAL goal, now reached (curved-admissible).

  * `uniformFlow_joint_contDiffOn_one` — for a base phase point `ξ₀`, radius `r > 0`, and the two DOMAIN
    side-conditions (`hqmem`: base ∈ K, `hvmem`: velocity ≤ ρ_K on `ball ξ₀ r`), the concrete flow endpoint
        `fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2 t`
    is jointly `ContDiffOn ℝ 1` on `Metric.ball ξ₀ r` — the first NEIGHBORHOOD-quality (not merely
    pointwise) joint C¹ regularity of the constructive geodesic flow.

  * `uniformFlow_joint_contDiffOn_one_witness` — ★ the DECISIVE NON-VACUITY witness: with `K :=
    Metric.closedBall q₀ 1`, `ξ₀ := (q₀,0)`, `r := min 1 ρ_K`, the domain conditions are discharged
    internally, so the joint C¹ holds with NO carried domain hypothesis, for EVERY (curved) `g, gi`.

  ## METHOD — pointwise derivative (LOCAL Task A) + Lipschitz continuity of it (Task B), over a FIXED `S`.
  The single control set `S := closedBall ((ξ₀.1,0), C₀·ρ_K + r)` contains every confined tube whose base
  lies in `ball ξ₀ r` (confinement + triangle), so the Lipschitz moduli `Kg, Lg, Kbd` of `geodesicField`
  and its derivative on `S` are FIXED — making the Task-B bound `‖L(x) − L(y)‖ ≤ C·dist(x,y)` UNIFORM over
  the ball.  Then:
    * DifferentiableOn: `uniformFlow_joint_hasFDerivAt_atBasepoint`-style pointwise derivative at each `x`
      (LOCAL Task A on the sub-ball `ball x (r − dist(x,ξ₀))`);
    * ContinuousOn of `fderiv f`: `fderiv f x = L(x)` (the endpoint Jacobi CLM, by `HasFDerivAt.fderiv`),
      and `x ↦ L(x)` is `C`-Lipschitz on the ball by `geodesicFlow_joint_fderiv_lipschitz_in_basepoint`
      (fed the per-base Jacobi families `V_x, V_y` along the two reference tubes, uniform moduli from `S`);
    * assemble via `contDiffOn_succ_iff_fderiv_of_isOpen` (`isOpen_ball`) + `contDiffOn_zero`.

  ## WHAT THIS FILE DOES NOT DO.
  NOT a second-order jet (Task D), NOT the IFT inverse (Task E/F), NOT discharge the RNC hypotheses
  (Task G), and does NOT bear on `hCConv`.  a₁=R/6 remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.
-/
import Mathlib
import QIQTH.GeodesicJointFDerivAtPointLocal
import QIQTH.GeodesicJointFDerivLipschitz
import QIQTH.UniformFlowJointFDerivAtPointConcrete
import QIQTH.UniformFlowNondeg
import QIQTH.DoubledFamilyFullSupply
import QIQTH.GeodesicTaylorCompact
import QIQTH.SecondVariationLipschitz
import QIQTH.BoundedGeometry

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 1200000

variable {n : ℕ}

/-- **Per-base-point derivative data for the concrete flow (on a fixed control set `S`).**  For a base
    phase point `x ∈ ball ξ₀ r` (with the global domain conditions `hqmem`/`hvmem` and global membership
    `hSmem` into the fixed compact convex `S`), builds a joint Jacobi family `V` along the reference tube
    `uniformFlowTube g gi hC hK x.1 x.2`, its endpoint CLM `L` (`L ξ = V ξ t`), and the pointwise Fréchet
    derivative `HasFDerivAt (fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2 t) L x` — all discharged via the
    LOCAL Task A on the sub-ball `ball x (r − dist x ξ₀)`. -/
private theorem tube_perbase_deriv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {S : Set (Point n × Point n)} (hScomp : IsCompact S) (hSconv : Convex ℝ S)
    (ξ₀ : Point n × Point n) {r : ℝ}
    (hqmem : ∀ ξ ∈ Metric.ball ξ₀ r, ξ.1 ∈ K)
    (hvmem : ∀ ξ ∈ Metric.ball ξ₀ r, ‖ξ.2‖ ≤ uniformFlowRadius g gi hC hK)
    (hSmem : ∀ ξ ∈ Metric.ball ξ₀ r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      uniformFlowTube g gi hC hK ξ.1 ξ.2 τ ∈ S)
    (x : Point n × Point n) (hx : x ∈ Metric.ball ξ₀ r) :
    ∃ (V : Point n × Point n → ℝ → Point n × Point n)
      (L : (Point n × Point n) →L[ℝ] Point n × Point n),
      (∀ ξ : Point n × Point n, V ξ 0 = ξ) ∧
      (∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (V ξ)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK x.1 x.2 τ) (V ξ τ)) τ) ∧
      (∀ ξ : Point n × Point n, L ξ = V ξ t) ∧
      HasFDerivAt (fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2 t) L x := by
  have hxdist : dist x ξ₀ < r := by rwa [Metric.mem_ball] at hx
  have hxK : x.1 ∈ K := hqmem x hx
  have hxv : ‖x.2‖ ≤ uniformFlowRadius g gi hC hK := hvmem x hx
  set rx : ℝ := r - dist x ξ₀ with hrxdef
  have hrx : 0 < rx := by rw [hrxdef]; linarith
  -- the sub-ball around `x` sits inside `ball ξ₀ r`.
  have hsub : ∀ ζ : Point n × Point n, ζ ∈ Metric.ball x rx → ζ ∈ Metric.ball ξ₀ r := by
    intro ζ hζ
    rw [Metric.mem_ball] at hζ ⊢
    calc dist ζ ξ₀ ≤ dist ζ x + dist x ξ₀ := dist_triangle _ _ _
      _ < rx + dist x ξ₀ := by linarith
      _ = r := by rw [hrxdef]; ring
  -- reference-tube continuity for the Jacobi engine.
  have hcont : ContinuousOn (uniformFlowTube g gi hC hK x.1 x.2) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτIoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact (uniformFlowTube_spec_ode g gi hC hK x.1 hxK x.2 hxv τ hτIoo).continuousAt.continuousWithinAt
  choose V hV0 hVode using fun ξ : Point n × Point n =>
    geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (uniformFlowTube g gi hC hK x.1 x.2) hcont ξ
  -- suppliers on the fixed compact convex `S`.
  obtain ⟨M₂, _hM₂0, hbound2⟩ := geodesicField_snd_fderiv_bddOn_compact g gi hC hScomp
  obtain ⟨K₀, hLip⟩ := geodesicField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
  obtain ⟨Kb, hKb0, hbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScomp
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK x.1 x.2 τ)‖ ≤ Kb :=
    fun τ hτ => hbd _ (hSmem x hx τ hτ)
  -- perturbed-family ODE / IC / membership on the sub-ball.
  have hWode : ∀ ξ ∈ Metric.ball x rx, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (uniformFlowTube g gi hC hK ξ.1 ξ.2)
        (geodesicField g gi (uniformFlowTube g gi hC hK ξ.1 ξ.2 τ)) τ := by
    intro ξ hξ τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK ξ.1 (hqmem ξ (hsub ξ hξ)) ξ.2 (hvmem ξ (hsub ξ hξ)) τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hIC : ∀ ξ ∈ Metric.ball x rx,
      uniformFlowTube g gi hC hK ξ.1 ξ.2 0 - uniformFlowTube g gi hC hK x.1 x.2 0 = ξ - x := by
    intro ξ hξ
    rw [uniformFlowTube_spec_ic g gi hC hK ξ.1 (hqmem ξ (hsub ξ hξ)) ξ.2 (hvmem ξ (hsub ξ hξ)),
      uniformFlowTube_spec_ic g gi hC hK x.1 hxK x.2 hxv]
  have hmem : ∀ ξ ∈ Metric.ball x rx, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      uniformFlowTube g gi hC hK ξ.1 ξ.2 τ ∈ S :=
    fun ξ hξ τ hτ => hSmem ξ (hsub ξ hξ) τ hτ
  obtain ⟨L, hLeq, hFD⟩ :=
    geodesicFlow_joint_hasFDerivAt_exists_atPoint_local
      (W := fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2) (V := V)
      g gi hC x hKb0 ht hSconv hrx hbound2 hLip hWode hVode hV0 hIC hKb hmem
  exact ⟨V, L, hV0, hVode, hLeq, hFD⟩

/-- **★ Joint `ContDiffOn ℝ 1` of the concrete uniform geodesic-flow endpoint on `ball ξ₀ r`.**  Plan
    Task C's original goal, reached in the curved-admissible case: given only that the perturbation ball
    stays in the tube's valid domain (`hqmem`/`hvmem`), the concrete flow endpoint
    `fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2 t` is jointly `C¹` on `Metric.ball ξ₀ r`. -/
theorem uniformFlow_joint_contDiffOn_one (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ξ₀ : Point n × Point n) {r : ℝ} (hr : 0 < r)
    (hqmem : ∀ ξ ∈ Metric.ball ξ₀ r, ξ.1 ∈ K)
    (hvmem : ∀ ξ ∈ Metric.ball ξ₀ r, ‖ξ.2‖ ≤ uniformFlowRadius g gi hC hK) :
    ContDiffOn ℝ 1 (fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2 t) (Metric.ball ξ₀ r) := by
  have hC₀ := uniformFlowConst_nonneg g gi hC hK
  have hρ0 : (0 : ℝ) ≤ uniformFlowRadius g gi hC hK := (uniformFlowRadius_pos g gi hC hK).le
  -- fixed control set `S`, covering every confined tube with base in `ball ξ₀ r`.
  set R : ℝ := uniformFlowConst g gi hC hK * uniformFlowRadius g gi hC hK + r with hRdef
  set c₀ : Point n × Point n := (ξ₀.1, (0 : Point n)) with hc₀def
  set S : Set (Point n × Point n) := Metric.closedBall c₀ R with hSdef
  have hScomp : IsCompact S := by rw [hSdef]; exact isCompact_closedBall _ _
  have hSconv : Convex ℝ S := by rw [hSdef]; exact convex_closedBall _ _
  have hSmem : ∀ ξ ∈ Metric.ball ξ₀ r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
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
            have hle : dist ξ.1 ξ₀.1 ≤ dist ξ ξ₀ := by rw [Prod.dist_eq]; exact le_max_left _ _
            have : dist ξ ξ₀ < r := by rwa [Metric.mem_ball] at hξ
            linarith
      _ ≤ R := by
          rw [hRdef]
          have := mul_le_mul_of_nonneg_left (hvmem ξ hξ) hC₀
          linarith
  -- fixed Lipschitz moduli of `geodesicField` and its derivative on `S`.
  obtain ⟨Kg, hLipg⟩ := geodesicField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
  obtain ⟨Lg, hLip2⟩ := fderiv_geodesicField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
  obtain ⟨Kbd, hKbd0, hbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScomp
  set f : Point n × Point n → Point n × Point n :=
    fun ξ => uniformFlowTube g gi hC hK ξ.1 ξ.2 t with hfdef
  -- abbreviate the per-base derivative data.
  have hdata : ∀ x ∈ Metric.ball ξ₀ r,
      ∃ (V : Point n × Point n → ℝ → Point n × Point n)
        (L : (Point n × Point n) →L[ℝ] Point n × Point n),
        (∀ ξ : Point n × Point n, V ξ 0 = ξ) ∧
        (∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (V ξ)
            (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK x.1 x.2 τ) (V ξ τ)) τ) ∧
        (∀ ξ : Point n × Point n, L ξ = V ξ t) ∧ HasFDerivAt f L x :=
    fun x hx => tube_perbase_deriv g gi hC hK ht hScomp hSconv ξ₀ hqmem hvmem hSmem x hx
  -- (1) differentiability on the ball.
  have hdiff : DifferentiableOn ℝ f (Metric.ball ξ₀ r) := by
    intro x hx
    obtain ⟨_V, _L, _, _, _, hFD⟩ := hdata x hx
    exact hFD.differentiableAt.differentiableWithinAt
  -- the uniform Lipschitz constant for the derivative map.
  set C : ℝ := (Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; have : (0:ℝ) ≤ (Lg:ℝ) := NNReal.coe_nonneg Lg; positivity
  -- (2) continuity of `fderiv f` on the ball (indeed Lipschitz), via Task B with uniform moduli.
  have hlipfderiv : LipschitzOnWith ⟨C, hC0⟩ (fderiv ℝ f) (Metric.ball ξ₀ r) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    obtain ⟨Vx, Lx, hVx0, hVxode, hLxeq, hFDx⟩ := hdata x hx
    obtain ⟨Vy, Ly, hVy0, hVyode, hLyeq, hFDy⟩ := hdata y hy
    have hfx : fderiv ℝ f x = Lx := hFDx.fderiv
    have hfy : fderiv ℝ f y = Ly := hFDy.fderiv
    -- reference-tube ODE / membership / coefficient bound at `x` and `y`.
    have hox : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (uniformFlowTube g gi hC hK x.1 x.2)
          (geodesicField g gi (uniformFlowTube g gi hC hK x.1 x.2 τ)) τ := by
      intro τ hτ
      exact uniformFlowTube_spec_ode g gi hC hK x.1 (hqmem x hx) x.2 (hvmem x hx) τ
        ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hoy : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (uniformFlowTube g gi hC hK y.1 y.2)
          (geodesicField g gi (uniformFlowTube g gi hC hK y.1 y.2 τ)) τ := by
      intro τ hτ
      exact uniformFlowTube_spec_ode g gi hC hK y.1 (hqmem y hy) y.2 (hvmem y hy) τ
        ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hSx : ∀ τ ∈ Set.Icc (0 : ℝ) 1, uniformFlowTube g gi hC hK x.1 x.2 τ ∈ S := hSmem x hx
    have hSy : ∀ τ ∈ Set.Icc (0 : ℝ) 1, uniformFlowTube g gi hC hK y.1 y.2 τ ∈ S := hSmem y hy
    -- the Task-B abstract operator-norm Lipschitz bound with the FIXED uniform moduli.
    have hbound := geodesicFlow_joint_fderiv_lipschitz_in_basepoint g gi hLipg hLip2 ht
      hox hoy hSx hSy hKbd0
      (fun τ hτ => hbd _ (hSx τ hτ)) (fun τ hτ => hbd _ (hSy τ hτ))
      hVxode hVyode hVx0 hVy0 hLxeq hLyeq
    -- rewrite the reference initial points `Y 0 = base`.
    have hicx : uniformFlowTube g gi hC hK x.1 x.2 0 = x :=
      uniformFlowTube_spec_ic g gi hC hK x.1 (hqmem x hx) x.2 (hvmem x hx)
    have hicy : uniformFlowTube g gi hC hK y.1 y.2 0 = y :=
      uniformFlowTube_spec_ic g gi hC hK y.1 (hqmem y hy) y.2 (hvmem y hy)
    rw [hicx, hicy] at hbound
    rw [hfx, hfy, dist_eq_norm]
    calc ‖Lx - Ly‖
        ≤ (Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd * dist x y := hbound
      _ = (⟨C, hC0⟩ : ℝ≥0) * dist x y := by
          rw [show ((⟨C, hC0⟩ : ℝ≥0) : ℝ) = C from rfl, hCdef]
  have hcont : ContinuousOn (fderiv ℝ f) (Metric.ball ξ₀ r) := hlipfderiv.continuousOn
  -- (3) assemble `ContDiffOn ℝ 1` on the open ball.
  have h1eq : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
  rw [hfdef, h1eq, contDiffOn_succ_iff_fderiv_of_isOpen (Metric.isOpen_ball)]
  refine ⟨hdiff, ?_, ?_⟩
  · intro h; exact absurd h (by simp)
  · rw [contDiffOn_zero]; exact hcont

/-- **★ NON-VACUITY witness for the joint C¹.**  With `K := Metric.closedBall q₀ 1`, `ξ₀ := (q₀,0)`,
    `r := min 1 ρ_K`, the domain conditions are discharged internally, so the concrete uniform geodesic-flow
    endpoint is jointly `ContDiffOn ℝ 1` on a genuine neighborhood of `(q₀,0)`, for EVERY (curved) `g, gi`. -/
theorem uniformFlow_joint_contDiffOn_one_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (r : ℝ), 0 < r ∧
      ContDiffOn ℝ 1
        (fun ξ => uniformFlowTube g gi hC (isCompact_closedBall q₀ 1) ξ.1 ξ.2 t)
        (Metric.ball ((q₀, (0 : Point n)) : Point n × Point n) r) := by
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
    have hle : dist ξ.1 q₀ ≤ dist ξ ξ₀ := by rw [hξ₀def, Prod.dist_eq]; exact le_max_left _ _
    calc dist ξ.1 q₀ ≤ r := (lt_of_le_of_lt hle hξ).le
      _ ≤ 1 := by rw [hrdef]; exact min_le_left _ _
  have hvmem : ∀ ξ ∈ Metric.ball ξ₀ r, ‖ξ.2‖ ≤ ρ := by
    intro ξ hξ
    rw [Metric.mem_ball] at hξ
    have hle : dist ξ.2 (0 : Point n) ≤ dist ξ ξ₀ := by rw [hξ₀def, Prod.dist_eq]; exact le_max_right _ _
    have hlt : ‖ξ.2‖ < r := by rw [← dist_zero_right]; exact lt_of_le_of_lt hle hξ
    calc ‖ξ.2‖ ≤ r := hlt.le
      _ ≤ ρ := by rw [hrdef]; exact min_le_right _ _
  exact ⟨r, hr, uniformFlow_joint_contDiffOn_one g gi hC hK ht ξ₀ hr hqmem hvmem⟩

end QIQTH.ExpMap
