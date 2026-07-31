/-
  UniformExpSecondJet — J4-19: toward discharging J4-18's carried uniform second-jet input `hjet`.

  MISSION.  J4-18 (`UniformExpJacobian.lean`) proved the common nondegeneracy radius `ρ₀`
  CONDITIONAL on a firewalled input `hjet`: a single `M ≥ 0` and radius `r > 0` such that for all
  `q ∈ K`, `‖x‖ < r`, the second jet `y ↦ fderiv ℝ (expMap g gi hC q) y` is BOTH differentiable at
  `x` AND has `‖fderiv ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x‖ ≤ M`.  J4-19's goal is to DERIVE
  `hjet`, converting J4-18's theorems from conditional to unconditional over compact `K`.

  ## Feasibility verdict (investigation result)

  A DIRECT/UNCONDITIONAL derivation of the full uniform `M` is a genuinely LARGE (multi-brick) R3
  derivation with NO existing repo shortcut, for a structural reason:

  * `expMap g gi hC q` is defined (`ExpMap.lean`) from the per-`q` `Classical.choose` selectors
    `expRho g gi hC q`, `expConst g gi hC q`, `expTube g gi hC q` (all marked `irreducible`).  The
    map is the genuine geodesic endpoint ONLY on the per-`q` injectivity ball `‖v‖ < expRho q`, and
    the entire per-`p` `Cᵏ` tower (`ExpMapContDiff*`, the `Kstar`/`Kstar2` second-jet tube bounds in
    `ExpJet4DFull`) produces constants that depend on these opaque per-`q` selectors.
  * The repo has NO uniform-over-`K` lower bound on `expRho` and NO uniform-over-`K` upper bound on
    `expConst`.  `geodesic_apriori_confinement_uniform` (`BoundedGeometryConfine.lean`) does give a
    SINGLE `ρ, C₀` valid for all `q ∈ K`, but for a DIFFERENT (re-constructed) tube family, not the
    `.choose` tube `expMap` is welded to.
  * Hence R1 (instantiate an existing explicit `‖D² exp_q‖` bound and uniformize the Christoffel jets
    via `BoundedGeometry`) fails at the tube constants; and R2 (joint `(q,x)`-continuity of the
    second jet ⟹ bounded on compact) is blocked by the per-`q` `.choose` — there is no joint-in-`q`
    regularity of `expMap` in the repo.

  ## What IS derived here (honest firewall, no `sorry`, no hyp = conclusion)

  The differentiability half of `hjet` is DERIVED OUTRIGHT from the landed UNCONDITIONAL C⁴ tower
  (`expMap_contDiffOn_four`), given only a UNIFORM injectivity-radius input.  Concretely
  `expMap_second_jet_bddOn_uniform` takes two GENUINE uniform-geometry inputs —

    (I1) `hrad : ∀ q ∈ K, r ≤ expRho g gi hC q`   — a uniform lower bound on the exp injectivity
         radius over `K` (a real `BoundedGeometry`/`geodesic_apriori_confinement_uniform`-flavoured
         geometric fact, NOT yet a repo lemma because `expRho` is a per-`q` opaque `.choose`); and
    (I2) `hbnd : ∀ q ∈ K, ∀ x, ‖x‖ < r → ‖fderiv ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x‖ ≤ M`
         — the BOUND-ONLY uniform second-jet estimate (the uniform-Grönwall / joint-flow content) —

  and PRODUCES exactly J4-18's `hjet` shape, with the `DifferentiableAt` conjunct PROVED (not
  assumed) from `expMap_contDiffOn_four` on the ball `‖x‖ < r ≤ expRho q`.  This strictly reduces
  J4-18's carried obligation from the mixed statement `{differentiable ∧ bound}` to the two clean
  geometric inputs `{uniform radius (I1)} ∧ {uniform bound (I2)}`: the differentiability is now a
  theorem.

  `expMap_common_nondeg_radius_of_uniform_inputs` then feeds this into J4-18's
  `expMap_common_nondeg_radius`, giving the common nondegeneracy radius modulo `(I1) ∧ (I2)`.

  ## What is NOT closed (the precise remaining brick)

  The uniform bound `(I2)` — a single `M` bounding `‖fderiv² exp_q‖` over `q ∈ K` — and the uniform
  radius `(I1)` are NOT derived here.  They are the genuine remaining work: either (a) a bridge
  identifying `expMap g gi hC q` with the uniform geodesic flow of
  `geodesic_apriori_confinement_uniform` on a uniform ball (⟹ joint smoothness ⟹ bounded second jet
  on a compact `q`-ball), or (b) a from-scratch uniform Grönwall on the second variational equation
  with `BoundedGeometry`-uniform Christoffel-jet coefficients.  Both are multi-brick.  NOTHING here
  fakes them; the conclusions carry them as clearly-labelled inputs.
-/
import Mathlib
import QIQTH.UniformExpJacobian
import QIQTH.ExpMapContDiffFour

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- **J4-19 (differentiability half of `hjet`, DERIVED).**  From the UNCONDITIONAL C⁴ regularity of
    the `q`-centered exponential map (`expMap_contDiffOn_four`), the second jet
    `y ↦ fderiv ℝ (expMap g gi hC q) y` is differentiable at every `x` on the injectivity ball
    `‖x‖ < expRho g gi hC q`, uniformly in `q`.

    Route: `expMap_contDiffOn_four` gives `ContDiffOn ℝ 4 (expMap g gi hC q)` on the open ball;
    `ContDiffOn.fderiv_of_isOpen` drops it to `ContDiffOn ℝ 3 (fun y => fderiv ℝ (exp_q) y)`, whose
    `differentiableOn` gives `DifferentiableAt` at any interior point (`IsOpen.mem_nhds`). -/
theorem expMap_secondJet_differentiableAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q : Point n) {x : Point n} (hx : ‖x‖ < expRho g gi hC q) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x := by
  set s : Set (Point n) := Metric.ball (0 : Point n) (expRho g gi hC q) with hsdef
  have hopen : IsOpen s := by rw [hsdef]; exact Metric.isOpen_ball
  have hxmem : x ∈ s := by rw [hsdef, Metric.mem_ball, dist_zero_right]; exact hx
  -- `exp_q ∈ C⁴` on the open ball ⟹ `fderiv exp_q ∈ C³` on it.
  have hcd4 : ContDiffOn ℝ 4 (expMap g gi hC q) s := expMap_contDiffOn_four g gi hC q
  have hF1cd3 : ContDiffOn ℝ 3 (fun y => fderiv ℝ (expMap g gi hC q) y) s :=
    hcd4.fderiv_of_isOpen hopen (by norm_num)
  -- `C³ ⟹ differentiable on the ball ⟹ differentiable at the interior point `x`.
  have hdiffOn : DifferentiableOn ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) s :=
    hF1cd3.differentiableOn (by norm_num)
  exact (hdiffOn x hxmem).differentiableAt (hopen.mem_nhds hxmem)

/-- **J4-19 (PRIMARY) — assemble J4-18's `hjet` shape, differentiability DERIVED.**

    Given the two GENUINE uniform-geometry inputs
    * `(I1) hrad` : `r ≤ expRho g gi hC q` for all `q ∈ K` (a uniform lower bound on the exp
      injectivity radius over `K`), and
    * `(I2) hbnd` : the BOUND-ONLY uniform second-jet estimate
      `‖fderiv ℝ (fun y => fderiv ℝ (exp_q) y) x‖ ≤ M` for all `q ∈ K`, `‖x‖ < r`,

    this produces EXACTLY J4-18's `hjet` conjunction, with the `DifferentiableAt` conjunct PROVED
    from `expMap_contDiffOn_four` (via `expMap_secondJet_differentiableAt`, using `‖x‖ < r ≤
    expRho q`).  DERIVED = the differentiability; the bound `(I2)` and radius `(I1)` are the carried
    uniform-geometry inputs (see file header for the precise remaining brick). -/
theorem expMap_second_jet_bddOn_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (_hK : IsCompact K)
    (r : ℝ) (_hr : 0 < r)
    (hrad : ∀ q ∈ K, r ≤ expRho g gi hC q)
    (M : ℝ) (_hM0 : 0 ≤ M)
    (hbnd : ∀ q ∈ K, ∀ x : Point n, ‖x‖ < r →
      ‖fderiv ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x‖ ≤ M) :
    ∀ q ∈ K, ∀ x : Point n, ‖x‖ < r →
      DifferentiableAt ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x ∧
      ‖fderiv ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x‖ ≤ M := by
  intro q hq x hx
  refine ⟨?_, hbnd q hq x hx⟩
  -- `‖x‖ < r ≤ expRho q`, so `x` is in the injectivity ball; differentiability is a theorem.
  exact expMap_secondJet_differentiableAt g gi hC q (lt_of_lt_of_le hx (hrad q hq))

/-- **J4-19 (SECONDARY) — the common nondegeneracy radius modulo the two uniform-geometry inputs.**

    Feeding the assembled `hjet` (from `expMap_second_jet_bddOn_uniform`) into J4-18's
    `expMap_common_nondeg_radius` gives a SINGLE radius `ρ₀ > 0` with `IsUnit (fderiv ℝ (exp_q) v)`
    for all `q ∈ K`, `‖v‖ < ρ₀`, now conditional ONLY on the uniform injectivity radius `(I1) hrad`
    and the bound-only uniform second-jet estimate `(I2) hbnd` — the differentiability half of
    J4-18's original `hjet` has been discharged. -/
theorem expMap_common_nondeg_radius_of_uniform_inputs (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (r : ℝ) (hr : 0 < r)
    (hrad : ∀ q ∈ K, r ≤ expRho g gi hC q)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hbnd : ∀ q ∈ K, ∀ x : Point n, ‖x‖ < r →
      ‖fderiv ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x‖ ≤ M) :
    ∃ ρ₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      IsUnit (fderiv ℝ (expMap g gi hC q) v) :=
  expMap_common_nondeg_radius g gi hC hK r hr M hM0
    (expMap_second_jet_bddOn_uniform g gi hC hK r hr hrad M hM0 hbnd)

end QIQTH.ExpMap
