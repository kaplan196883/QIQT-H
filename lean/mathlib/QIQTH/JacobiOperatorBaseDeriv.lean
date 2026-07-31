/-
  JacobiOperatorBaseDeriv — J4-36: applying the ABSTRACT autonomous first-order smooth-dependence
  engine (`QIQTH.AutonomousDep.autonomousField_variation_exists_uncond`) to the DOUBLED tangent field
  `G` of the geodesic system, delivering the `(h3a)` CORE — the directional (scalar) smooth dependence
  of the doubled geodesic/Jacobi flow on its base initial condition.

  ## Context

  `VelocityJacobiBaseDep` / `VelocitySecondJetId` / `FlowVelocityJacobiField` reduced `(J)` (the
  unconditional common exp-nondeg radius over a compact `K`, via
  `expMap_common_nondeg_radius_of_velocity_ode_data`) to the SINGLE residual input `hid` — the
  second-order velocity jet IDENTIFICATION.  Per `VelocityJacobiBaseDep`, `hid` is DERIVED (via
  `hid_of_firstJet_hasFDerivAt`) from the `(h3a)` firewall

      `HasFDerivAt (fun w => fderiv ℝ (Fam q) w) B v`   with   `B a b = (Zf q v a b 1).1`,

  the CLM-valued Fréchet differentiability of the geodesic Jacobi SOLUTION OPERATOR in its base
  velocity `w`.  The GPT-5.5 route to `(h3a)`: first-order smooth dependence of the DOUBLED tangent
  field

      `G(Y, V) = (F(Y), DF(Y)·V)`,   `F = geodesicField g gi`,

  whose integral curves are the geodesic flow paired with a Jacobi field.  The abstract engine
  `autonomousField_variation_exists_uncond` (`AutonomousSmoothDep`) is exactly the reusable machine to
  apply to `G`.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `doubledField` — the doubled tangent field `G : E → E` on `E = State × State`
    (`State = Point n × Point n`), `G p = (F p.1, DF(p.1)·p.2)`.

  * `contDiff_doubledField` — **`G` is `C^∞`.**  DERIVED structurally: the first component is
    `F ∘ fst` (`contDiff_geodesicField`), the second is the bilinear application
    `(DF ∘ fst)·snd` (`ContDiff.clm_apply` with `contDiff_fderiv_geodesicField`).  This is the (a)
    ingredient — the `C²`-regularity input of the engine is fully derived from `hC`, NOT carried as an
    opaque bound.

  * `doubledField_variation_exists_uncond` — **the `(h3a)` CORE (b):** the directional (scalar)
    smooth dependence of the doubled flow on its base initial condition.  For a doubled family
    `Y : ℝ → ℝ → E` of integral curves of `G` on `[0,1]` (base IC perturbed linearly `Y s 0 − Y 0 0 =
    s·p`) staying in a COMPACT CONVEX `S`, and a supplied linearized-ODE solution `V` (`V 0 = p`),
    `HasDerivAt (fun s => Y s t) (V t) 0`.  DERIVED by specialising
    `autonomousField_variation_exists_uncond` to `Φ := G`, with ALL of the engine's field-regularity
    hypotheses (`hdiff`, `hdiff2`, `hbound2`, `hLip`, `hKb`) DISCHARGED from `contDiff_doubledField`
    plus compactness/convexity of `S` (continuity ⇒ bounded on compact; `Convex.lipschitzOnWith_of_
    nnnorm_fderiv_le`).  The second-factor component of `V t` is the base-IC derivative of the Jacobi
    field endpoint — the analytic content of `(h3a)`.

  ## HONEST CHECKPOINT (binding) — `(h3a)` CORE vs the CLM upgrade / `hid` / `(J)`

  What the engine delivers is a DIRECTIONAL (scalar `s`) `HasDerivAt` of the doubled flow, one supplied
  perturbation direction `p` at a time.  This is the analytic CORE of `(h3a)`.  It is NOT yet the
  `(h3a)` firewall in the shape `hid_of_firstJet_hasFDerivAt` consumes, which is the CLM-valued
  `HasFDerivAt (fun w => fderiv ℝ (Fam q) w) B v` with `B a b = (Zf q v a b 1).1`.  The remaining,
  genuinely-intricate plumbing (NOT built here, honestly firewalled):

    (c) the CLM UPGRADE — assembling the per-direction scalar `HasDerivAt` (uniformly in the
        perturbation direction, with the `V`-component linearity from `jacobiSol_unique` mirrored one
        order up) into the operator-valued `HasFDerivAt (fun w => fderiv ℝ Fam w) B v`, and PROJECTING
        the `E`-valued flow onto the Jacobi (second-factor) `V`-component;

    (d) the IDENTIFICATION of that projected base-IC derivative with `(Zf … 1).1` via
        `secondVariation_endpoint_unique` (ODE-uniqueness `∂_w V = Zf`), then `hid_of_firstJet_
        hasFDerivAt` ⇒ `hid` ⇒ `expMap_common_nondeg_radius_of_velocity_ode_data` ⇒ `(J)`.

  Therefore `(J)` is NOT discharged here; it is REDUCED from `(h3a)` to `(h3a)`'s CLM-upgrade/
  projection/identification residual (c)+(d), with the doubled-field smooth-dependence CORE now a
  compiled theorem via the abstract engine.  This file does NOT smuggle `hid`/`hbnd`/`hweld`; it does
  NOT build the covariant `D²/dτ²`, NOT Raychaudhuri (L3), NOT `a₁ = R/6`.
-/
import QIQTH.AutonomousSmoothDep
import QIQTH.VelocityJacobiBaseDep
import QIQTH.VelocitySecondJetId
import QIQTH.FlowVelocityJacobiField
import QIQTH.UniformFlowBridge
import QIQTH.BoundedGeometry
import QIQTH.ExpMapContDiff2
import QIQTH.JacobiEquation
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **The doubled tangent field** `G` of the geodesic system on `E = State × State`
    (`State = Point n × Point n`).  With `F = geodesicField g gi`,
        `G (P, W) = (F P, DF(P)·W)`,
    i.e. `G p = (F p.1, fderiv ℝ F p.1 p.2)`.  Its integral curves are the geodesic flow paired with a
    Jacobi field: if `(P s, W s)` solves `(P, W)' = G (P, W)` then `P` is a geodesic-flow trajectory
    and `W` solves the linearized (Jacobi) ODE `W' = DF(P)·W` along `P`. -/
noncomputable def doubledField (g gi : Point n → Fin n → Fin n → ℝ) :
    ((Point n × Point n) × (Point n × Point n)) → ((Point n × Point n) × (Point n × Point n)) :=
  fun p => (geodesicField g gi p.1, fderiv ℝ (geodesicField g gi) p.1 p.2)

/-- **The doubled tangent field is `C^∞`.**  DERIVED structurally from `hC`: the first component is
    `F ∘ fst` (`contDiff_geodesicField` composed with `contDiff_fst`), and the second component is the
    bilinear application `p ↦ (DF(p.1))(p.2) = ((DF ∘ fst) p)(snd p)`, `C^∞` by `ContDiff.clm_apply`
    (`contDiff_fderiv_geodesicField ∘ fst` in the operator slot, `contDiff_snd` in the vector slot). -/
theorem contDiff_doubledField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (doubledField g gi) := by
  refine ContDiff.prodMk ?_ ?_
  · exact (contDiff_geodesicField g gi hC).comp contDiff_fst
  · exact ContDiff.clm_apply ((contDiff_fderiv_geodesicField g gi hC).comp contDiff_fst)
      contDiff_snd

/-- **Uniform bound on `DG` over a compact set.**  `fderiv ℝ (doubledField g gi)` is continuous
    (`doubledField` is `C^∞`), hence bounded on any compact `S`. -/
theorem doubledField_fderiv_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set ((Point n × Point n) × (Point n × Point n))} (hS : IsCompact S) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (doubledField g gi) z‖ ≤ Kb := by
  have hcont : Continuous (fderiv ℝ (doubledField g gi)) :=
    (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
  obtain ⟨C, hCb⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hCb z hz).trans (le_max_left _ _)⟩

/-- **Uniform bound on `D²G` over a compact set.**  `fderiv ℝ (fderiv ℝ (doubledField g gi))` is
    continuous (`doubledField` is `C^∞`, so `DG` and `D²G` are), hence bounded on any compact `S`.
    This is the `hbound2` input of the abstract engine, DERIVED (not carried). -/
theorem doubledField_fderiv2_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set ((Point n × Point n) × (Point n × Point n))} (hS : IsCompact S) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S,
      ‖fderiv ℝ (fderiv ℝ (doubledField g gi)) z‖ ≤ Kb := by
  have hcont : Continuous (fderiv ℝ (fderiv ℝ (doubledField g gi))) :=
    ((contDiff_doubledField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
      (by simp)
  obtain ⟨C, hCb⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hCb z hz).trans (le_max_left _ _)⟩

/-- **The `(h3a)` CORE — directional smooth dependence of the DOUBLED geodesic/Jacobi flow on its base
    initial condition.**  Let `G = doubledField g gi` on `E = State × State`, and let `Y : ℝ → ℝ → E`
    be a one-parameter family of integral curves of `G` on `[0,1]` whose base initial condition is
    perturbed linearly (`Y s 0 − Y 0 0 = s·p`), staying inside a COMPACT CONVEX set `S`.  Let
    `V : ℝ → E` solve the linearized ODE `V' = DG(Y 0 τ)·V` along the base doubled trajectory with
    `V 0 = p`.  Then the base-IC derivative of the doubled-flow endpoint EXISTS and equals `V t`:
        `HasDerivAt (fun s => Y s t) (V t) 0`.

    DERIVED by specialising `QIQTH.AutonomousDep.autonomousField_variation_exists_uncond` to `Φ := G`.
    ALL of the engine's autonomous-field regularity inputs are DISCHARGED from `contDiff_doubledField`
    together with the compactness/convexity of `S`:
      * `hdiff` / `hdiff2` — `G` and `DG` differentiable, from `C^∞`;
      * `hbound2` — `‖D²G‖ ≤ M₂` on `S`, from continuity of `D²G` on the compact `S`
        (`doubledField_fderiv2_bddOn_compact`);
      * `hLip` — `G` Lipschitz on the convex `S`, from `‖DG‖ ≤ K₀` on `S`
        (`doubledField_fderiv_bddOn_compact` + `Convex.lipschitzOnWith_of_nnnorm_fderiv_le`);
      * `hKb` — `‖DG(Y 0 τ)‖ ≤ K` along the base curve, since `Y 0 τ ∈ S`.
    The remaining carried inputs are the genuine base ODE / tube data (`hYode`, `hVode`, `hV0`, `hIC`,
    `hmem`) and `hC`.

    HONEST: this is the DIRECTIONAL (scalar `s`, one perturbation direction `p`) core of `(h3a)`.  It
    is not yet the operator-valued `HasFDerivAt (fun w => fderiv ℝ Fam w) B v` that
    `hid_of_firstJet_hasFDerivAt` consumes — that CLM upgrade + `V`-component projection + `Zf`
    identification (c)+(d) remain firewalled (see the module checkpoint). -/
theorem doubledField_variation_exists_uncond (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → (Point n × Point n) × (Point n × Point n)}
    {V : ℝ → (Point n × Point n) × (Point n × Point n)}
    {p : (Point n × Point n) × (Point n × Point n)}
    {S : Set ((Point n × Point n) × (Point n × Point n))}
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (doubledField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (doubledField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = p)
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • p)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  set G : ((Point n × Point n) × (Point n × Point n)) → ((Point n × Point n) × (Point n × Point n)) :=
    doubledField g gi with hGdef
  -- (a) `G` is `C^∞`; extract the engine's regularity inputs.
  have hGcd : ContDiff ℝ (⊤ : WithTop ℕ∞) G := contDiff_doubledField g gi hC
  have hdiff : ∀ x ∈ S, DifferentiableAt ℝ G x :=
    fun x _ => (hGcd.differentiable (by simp)).differentiableAt
  have hGcd' : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ G) :=
    hGcd.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top
  have hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ G) x :=
    fun x _ => (hGcd'.differentiable (by simp)).differentiableAt
  -- `hbound2`: `‖D²G‖ ≤ M₂` on the compact `S`.
  obtain ⟨M₂, _hM₂0, hbound2⟩ := doubledField_fderiv2_bddOn_compact g gi hC hScompact
  -- `‖DG‖ ≤ Kf` on the compact `S`, feeding both `hLip` and `hKb`.
  obtain ⟨Kf, hKf0, hKfbd⟩ := doubledField_fderiv_bddOn_compact g gi hC hScompact
  set K₀ : NNReal := ⟨Kf, hKf0⟩ with hK₀def
  have hLip : LipschitzOnWith K₀ G S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hdiff x (by trivial))
      (fun x hx => by rw [← NNReal.coe_le_coe]; simpa [hK₀def] using hKfbd x hx)
      hSconvex
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ G (Y 0 τ)‖ ≤ Kf :=
    fun τ hτ => hKfbd (Y 0 τ) (hmem 0 τ hτ)
  -- (b) apply the abstract autonomous first-order smooth-dependence engine to `Φ := G`.
  exact QIQTH.AutonomousDep.autonomousField_variation_exists_uncond G hKf0 ht hSconvex
    hdiff hdiff2 hbound2 hLip hYode hVode hV0 hIC hKb hmem

end QIQTH.ExpMap
