/-
  VelocityJacobiBaseDep — J4-34: the base-velocity dependence of the first velocity Jacobi field, and
  the two DERIVED endpoints of the second-velocity-jet identification `(h3)` / `hid`.

  ## Context

  `VelocitySecondJetId` (J4-33) built the VELOCITY-slot first jet `(h1)` and second-order Taylor jet
  `(h2)` of the geodesic-flow endpoint, DERIVED, and REDUCED `(J)` / the unconditional common exp-nondeg
  radius over a compact `K` (via `FlowVelocityJacobiField.expMap_common_nondeg_radius_of_velocity_ode_data`)
  to the SINGLE residual input `(h3)` = `hid` — the second-order velocity jet IDENTIFICATION

    `hid : (fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v) a b = (Zf q v a b 1).1`,

  i.e. the flow-endpoint velocity 2-jet `fderiv²(Fam q)(v)` applied to `(a,b)` equals the POSITION
  endpoint of the second-order velocity variation field `Zf`.

  ## Route (ii) and what is genuinely reachable in a single file

  `Fam q w = (Y_{q,w} 1).1` is the geodesic-endpoint position (exp-map-shaped); by `(h1)`/J4-33 the
  first velocity jet is the endpoint velocity-Jacobi map `fderiv(Fam q)(w)(a) = (V_{q,w,a} 1).1`, where
  `V_{q,w,a}` is the first velocity Jacobi field along the base geodesic `Y_{q,w}` (base velocity `w`,
  seed `(0,a)`).  Route (ii) differentiates this ONCE MORE in the base velocity `w`: the second-order
  velocity jet `fderiv²(Fam q)(v)` is the derivative of the Jacobi SOLUTION OPERATOR `w ↦ fderiv(Fam q)(w)`
  in the base velocity, at `w = v`.  As `w` varies, the base geodesic `Y_{q,w}` varies, so
  `∂_w[V_{q,w,a}]|_v · b` solves the INHOMOGENEOUS linearized geodesic ODE
      `Z' = DF(Y_{q,v})·Z + Src`,   `Z 0 = 0`,   `Src = D²F(Y_{q,v})(∂_w Y_{q,v}·b, V_{q,v,a})`,
  which is exactly the ODE `Zf` solves.

  IRREDUCIBLE FRONTIER — `(h3a)` (FIREWALLED, NOT built here).  The genuinely-unbuilt content is the
  CLM-valued Fréchet differentiability of the Jacobi solution operator in the base velocity:
      `HasFDerivAt (fun w => fderiv ℝ (Fam q) w) B v`   with   `B a b = (Zf q v a b 1).1`.
  This is a full SECOND-order smooth-dependence proof, one parameter-order up from the first-order
  smooth dependence `BasepointSmoothDep`/`GeodesicSmoothDep` build for the geodesic flow itself.  A
  quotient-residual (little-o) argument for the Jacobi linear ODE needs the flow's SECOND-order velocity
  Taylor expansion composed through the `C²` field — i.e. the parametric-smooth-dependence residual-
  Grönwall and `C²`-remainder engines, which are hard-coded to `geodesicField g gi` in `GeodesicSmoothDep`
  and NOT abstract over the (doubled tangent) vector field.  The geometry-free Lipschitz difference-
  bound `BasepointJetModulus.linODE_twopoint_diff_bound` yields only LIPSCHITZ dependence-in-parameter,
  never differentiability, so `(h3a)` cannot be closed by the abstract engine alone.  This is exactly the
  same class of carried parameter-`C²` regularity the tower already carries elsewhere (compare
  `VelocitySecondJetId.flowVelocity_endpoint_secondOrder_taylor`'s hypothesis
  `hEdiff2 : ∀ x ∈ Sδ, DifferentiableAt ℝ (fderiv ℝ (fun d => W d t)) x` — the differentiability of the
  first jet in the parameter, carried as genuine regularity data).

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion) — the two ENDPOINTS of `(h3a)`

  * `secondVariation_endpoint_unique` — **(h3b) the ODE-uniqueness that PINS the base-velocity derivative
    field to `Zf`.**  Any two phase-space fields solving the SAME inhomogeneous linearized geodesic ODE
    `Z' = DF(Y)·Z + Src` on `[0,1]` with the SAME seed at `0` agree on all of `[0,1]` (in particular at the
    endpoint `t = 1`).  DERIVED from `BasepointJetModulus.linODE_twopoint_diff_bound` with
    `Dcoef = Dsrc = 0` (`A₁ = A₂ = DF(Y)`, `b₁ = b₂ = Src`), the second field's uniform bound extracted by
    `IsCompact.exists_bound_of_continuousOn` (continuity of the ODE solution on the compact `[0,1]`); the
    resulting bound is `(0·Xb + 0)·exp K = 0`.  This is precisely the step `∂_w V = Zf` once `∂_w V` is
    known to solve the second-variation ODE — the `q = q'` diagonal of the two-point engine.

  * `hid_of_firstJet_hasFDerivAt` — **(h3c) the formal CLM chaining bridge.**  From the CLM-valued
    base-velocity smooth dependence `HasFDerivAt (fun w => fderiv ℝ (Fam) w) B v` (the `(h3a)` firewall) and
    the value identification `B a b = (Zf a b 1).1`, DERIVE the `hid` predicate
    `(fderiv ℝ (fun w => fderiv ℝ Fam w) v) a b = (Zf a b 1).1`.  Purely formal:
    `HasFDerivAt.fderiv` turns the smooth dependence into `fderiv (fun w => fderiv Fam w) v = B`, then the
    value identification closes it.  This is "everything after the `(h3a)` firewall".

  HONEST CHECKPOINT (binding).  This lands the two DERIVED endpoints of the second-velocity-jet
  identification — the ODE-uniqueness `(h3b)` that pins the base-velocity derivative to `Zf`, and the
  formal chaining `(h3c)` that assembles `hid` once the CLM smooth dependence is supplied.  It DOES NOT
  build `(h3a)` — the CLM Fréchet differentiability of the Jacobi solution operator in the base velocity —
  which is the irreducible parametric-smooth-dependence residual (a full second-order smooth-dependence
  tower for the doubled tangent field, requiring the field-specific residual-Grönwall / `C²` engines that
  may not be re-derived in a single file).  Hence `(J)` is NOT fully discharged here; it is REDUCED to
  `(h3a)`.  It does NOT carry `hid`/the conclusion as a hypothesis of any theorem, NOT build the covariant
  `D²/dτ²`, NOT Raychaudhuri (L3), NOT `a₁ = R/6`.
-/
import QIQTH.VelocitySecondJetId
import QIQTH.FlowVelocityJacobiField
import QIQTH.BasepointFDeriv
import QIQTH.BasepointJacobi2
import QIQTH.BasepointSmoothDep
import QIQTH.BasepointJetModulus
import QIQTH.JacobiEquation
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **(h3b) — the second-variation ODE-uniqueness that pins `∂_w V` to `Zf`.**  Let `Z, Z'` both solve
    the inhomogeneous linearized geodesic ODE along the SAME base geodesic `Y`,
        `Z'  = DF(Y)·Z  + Src`  and  `Z''  = DF(Y)·Z' + Src`  on `[0,1]`,
    with the SAME seed `Z 0 = Z' 0` and the base-curve coefficient bounded `‖DF(Y τ)‖ ≤ K`.  Then
    `Z t = Z' t` for all `t ∈ [0,1]` (in particular `Z 1 = Z' 1`).

    DERIVED from `linODE_twopoint_diff_bound` at the `q = q'` diagonal (`A₁ = A₂ = DF(Y)`,
    `b₁ = b₂ = Src`, hence `Dcoef = Dsrc = 0`): with any uniform bound `Xb` on the second solution
    (extracted from continuity of the ODE solution on the compact `[0,1]`), the difference is
    `‖Z t − Z' t‖ ≤ (0·Xb + 0)·exp K = 0`.  This is exactly the identification `∂_w V = Zf` once the
    base-velocity derivative `∂_w V` of the first Jacobi field is known to solve the second-variation
    ODE with the matching seed. -/
theorem secondVariation_endpoint_unique (g gi : Point n → Fin n → Fin n → ℝ)
    {Y Z Z' Src : ℝ → Point n × Point n} {K : ℝ} (hK0 : 0 ≤ K)
    (hZ : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Z (fderiv ℝ (geodesicField g gi) (Y τ) (Z τ) + Src τ) τ)
    (hZ' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Z' (fderiv ℝ (geodesicField g gi) (Y τ) (Z' τ) + Src τ) τ)
    (h0 : Z 0 = Z' 0)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y τ)‖ ≤ K) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Z t = Z' t := by
  -- the second solution is continuous on the compact `[0,1]`, hence uniformly bounded there.
  have hcont : ContinuousOn Z' (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hZ' t ht).continuousAt.continuousWithinAt
  obtain ⟨Xb, hXb⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont
  -- the two-point difference bound at the `q = q'` diagonal collapses to `0`.
  have hbnd := linODE_twopoint_diff_bound (E := Point n × Point n)
    (A₁ := fun τ => fderiv ℝ (geodesicField g gi) (Y τ))
    (A₂ := fun τ => fderiv ℝ (geodesicField g gi) (Y τ))
    (X₁ := Z) (X₂ := Z') (b₁ := Src) (b₂ := Src)
    (K := K) (Dcoef := 0) (Xb := Xb) (Dsrc := 0) hK0
    hZ hZ' h0 hKb
    (fun τ _ => by simp)
    hXb
    (fun τ _ => by simp)
  intro t ht
  have hzero : ‖Z t - Z' t‖ ≤ 0 := by
    have := hbnd t ht
    simpa using this
  have : Z t - Z' t = 0 := by
    have := le_antisymm hzero (norm_nonneg _)
    exact norm_eq_zero.mp this
  exact sub_eq_zero.mp this

/-- **(h3c) — the formal CLM chaining bridge for `hid`.**  Once the `(h3a)` firewall is supplied — the
    CLM-valued Fréchet differentiability of the first velocity jet in the base velocity,
    `HasFDerivAt (fun w => fderiv ℝ Fam w) B v`, with the value identification `B a b = (Zf a b 1).1` —
    the second-order velocity jet identification `hid` follows formally:
        `(fderiv ℝ (fun w => fderiv ℝ Fam w) v) a b = (Zf a b 1).1`.

    DERIVED: `HasFDerivAt.fderiv` gives `fderiv (fun w => fderiv ℝ Fam w) v = B`; applying to `(a,b)` and
    rewriting by the value identification closes it.  This is "everything after the `(h3a)` firewall" — no
    special second-derivative API is needed, since `fun w => fderiv ℝ Fam w` is an ordinary map into the
    normed space `Point n →L[ℝ] Point n` and its `fderiv` lives in `Point n →L[ℝ] (Point n →L[ℝ] Point n)`,
    applied as `B a b`. -/
theorem hid_of_firstJet_hasFDerivAt {Fam : Point n → Point n}
    {Zf : Point n → Point n → ℝ → Point n × Point n}
    {B : Point n →L[ℝ] Point n →L[ℝ] Point n} {v : Point n}
    (hFD : HasFDerivAt (fun w => fderiv ℝ Fam w) B v)
    (hBval : ∀ a b : Point n, B a b = (Zf a b 1).1) :
    ∀ a b : Point n, (fderiv ℝ (fun w => fderiv ℝ Fam w) v) a b = (Zf a b 1).1 := by
  have hfd : fderiv ℝ (fun w => fderiv ℝ Fam w) v = B := hFD.fderiv
  intro a b
  rw [hfd]
  exact hBval a b

end QIQTH.ExpMap
