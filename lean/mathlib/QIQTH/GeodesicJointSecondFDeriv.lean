/-
  GeodesicJointSecondFDeriv — the JOINT SECOND-order Fréchet derivative of the geodesic flow, obtained by
  ONE MORE "doubling" (`genericDoubled`) applied to the JOINT phase-space flow, exactly mirroring this
  session's velocity-only C¹→C²→C³ doubling climb (`UniformFlowThirdFDeriv.genericDoubled` /
  `quadrupledField`) but carried on the FULL combined phase space `ξ = (δq, δv)` instead of the
  velocity-only slot.

  MOTIVATION (plan `tranquil-stargazing-fox.md` v4, Task G; ledger `JET4_TOWER_PLAN.md`).
  Brick 1 (`GeodesicBasepointFrechet.geodesicFlow_joint_hasFDerivAt(_exists)`, commit `aa082139`) built the
  JOINT (base + velocity) FIRST-order Fréchet derivative of the geodesic flow endpoint `fun ξ => W ξ t`
  on the combined phase space `E = Point n × Point n`, with field `geodesicField g gi : E → E`.  The
  Rosenberg §2.5 textbook route (`refs/Rosenberg_Laplacian.ocr.txt`, exp-map-is-smooth) proves higher-order
  smoothness of the flow by applying the SINGLE ODE-smooth-dependence theorem to the COMBINED phase point
  `(x,v) ∈ TM` and its tangent lift — NOT by gluing separately-built marginals.  In Lean the tangent-lift
  device is `genericDoubled`:  `genericDoubled Φ z = (Φ z.1, fderiv ℝ Φ z.1 z.2)`, and
  `doubledField g gi = genericDoubled (geodesicField g gi)` (`JacobiOperatorBaseDeriv.doubledField`).  The
  integral curves of `doubledField` are the geodesic flow paired with its own Jacobi (first-variation)
  field, so the JOINT first-order Fréchet derivative of the DOUBLED flow endpoint is precisely the JOINT
  SECOND-order object of the base flow (its `.2` slot differentiates the first-variation field).

  The repo already has the abstract, FIELD-AGNOSTIC first-jet engine
  `UniformFlowSecondFDeriv.autonomousFlow_endpoint_hasFDerivAt_window_exists (Φ : E → E)` and its
  `doubledField`-instantiation `doubledFlow_endpoint_baseVelocity_hasFDerivAt_exists` — but the latter fixes
  the perturbation index to `P := Point n` and the seed to the VELOCITY slot only.  Task G is exactly the
  JOINT-seed version: take `P := E × E` (the full doubled phase space) and `seed := id`, so the doubled
  flow's initial condition is perturbed in ALL directions simultaneously.

  WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited):

  * `doubledFlow_endpoint_joint_hasFDerivAt_exists` — **the joint SECOND-order Fréchet-derivative core.**
    For a family `W : (E×E) → ℝ → (E×E)` of `doubledField`-integral curves whose FULL doubled initial
    condition is perturbed linearly (`W Ξ 0 − W 0 0 = Ξ`, arbitrary `Ξ ∈ (E×E)`) and doubled-linearized
    (Jacobi-of-Jacobi) solutions `V Ξ` along the base doubled curve `W 0` (`V Ξ 0 = Ξ`), the doubled-flow
    endpoint `fun Ξ => W Ξ t` is Fréchet-differentiable at `Ξ = 0`, with derivative the continuous-linear
    endpoint linearized map `Ξ ↦ V Ξ t`.  This is `geodesicFlow_joint_hasFDerivAt_exists` applied ONE
    ORDER UP — to `genericDoubled (geodesicField g gi) = doubledField g gi` — on the doubled phase space,
    which is the mathematical content of "the JOINT second Fréchet derivative of the geodesic flow."

  * `doubledFlow_endpoint_joint_snd_hasFDerivAt_exists` — **the second-variation projection.**  The `.2`
    component of the doubled endpoint (the base flow's first-variation / Jacobi field) has, JOINTLY in the
    full doubled perturbation `Ξ`, Fréchet derivative `Ξ ↦ (V Ξ t).2` at `0` — the precise shape
    "`D_Ξ` of (`D` of the flow)" that carries the base flow's second-order data.

  * `doubledFlow_endpoint_baseVelocity_ofJoint` — the velocity-slot doubled derivative recovered as the
    RESTRICTION of the joint one to the velocity subspace, bridging back to
    `doubledFlow_endpoint_baseVelocity_hasFDerivAt_exists`'s register.

  HONEST FIREWALL (binding).  This is the JOINT first-order Fréchet derivative of the DOUBLED (= tangent-
  lifted) flow — equivalently the JOINT SECOND-order Fréchet object of the geodesic flow — carrying only
  the SAME genuine regularity the joint first-order core carries (`S` compact convex, the doubled field's
  own `C²`/Lipschitz bounds — discharged here from `hC` via `contDiff_doubledField` /
  `doubledField_fderiv{,2}_bddOn_compact`, so NO field-regularity hypotheses are carried), plus the
  supplied doubled-flow ODE/IC/confinement data and the supplied doubled-Jacobi solutions.  It does NOT
  wire to the concrete `.choose`-built `uniformFlowExp` / `uniformInverseChart` (that concrete SECOND-order
  SUPPLY — the joint analogue of the still-firewalled R2-a/quadruple-flow supply — is NOT built here), does
  NOT produce `fderiv (fun ξ => W ξ t)` as a FUNCTION of the base point `ξ` (the `.choose`-incoherence
  wall), does NOT build the witness mixed partial, is NOT Raychaudhuri, is NOT `a₁ = R/6`, and does NOT by
  itself discharge `hCConv`.
-/
import Mathlib
import QIQTH.UniformFlowSecondFDeriv
import QIQTH.JacobiOperatorBaseDeriv

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 800000

section JointSecondOrder

variable {n : ℕ}

/-- Shorthand for the doubled (tangent-lifted) phase space `E × E`, `E = Point n × Point n`. -/
local notation "E2 " n => (Point n × Point n) × (Point n × Point n)

/-- **Joint SECOND-order Fréchet-derivative core (Task G).**  The field-agnostic first-jet engine
    `autonomousFlow_endpoint_hasFDerivAt_window_exists` applied to `Φ := doubledField g gi`
    (`= genericDoubled (geodesicField g gi)`) with the FULL doubled phase space as the perturbation index
    (`P := (Point n × Point n) × (Point n × Point n)`) and `seed := id` (all directions perturbed
    simultaneously).  Discharges every field-regularity input of the engine from `hC`
    (`contDiff_doubledField`; `doubledField_fderiv2_bddOn_compact`; `doubledField_fderiv_bddOn_compact`
    + `Convex.lipschitzOnWith_of_nnnorm_fderiv_le`; `hKb` along the base curve).

    Given a family `W Ξ` of doubled integral curves on the window `‖Ξ‖ ≤ σ` whose doubled IC is perturbed
    linearly and IDENTICALLY `W Ξ 0 − W 0 0 = Ξ`, and globally-defined doubled-linearized solutions `V Ξ`
    (`V Ξ 0 = Ξ`) along the fixed base doubled curve `W 0`, the doubled-flow endpoint `Ξ ↦ W Ξ t` is
    Fréchet-differentiable at `0`, its derivative the continuous-linear endpoint doubled-Jacobi map
    `Ξ ↦ V Ξ t`.  This is the JOINT second-order Fréchet derivative of the geodesic flow. -/
theorem doubledFlow_endpoint_joint_hasFDerivAt_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n))}
    {S : Set ((Point n × Point n) × (Point n × Point n))} {σ : ℝ}
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S) (hσ : 0 < σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hWode : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ‖ ≤ σ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W Ξ) (doubledField g gi (W Ξ τ)) τ)
    (hVode : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)),
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (V Ξ) (fderiv ℝ (doubledField g gi) (W 0 τ) (V Ξ τ)) τ)
    (hV0 : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), V Ξ 0 = Ξ)
    (hIC : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ‖ ≤ σ → W Ξ 0 - W 0 0 = Ξ)
    (hmem : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ‖ ≤ σ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, W Ξ τ ∈ S) :
    ∃ L : ((Point n × Point n) × (Point n × Point n)) →L[ℝ]
        ((Point n × Point n) × (Point n × Point n)),
      (∀ Ξ : ((Point n × Point n) × (Point n × Point n)), L Ξ = V Ξ t) ∧
        HasFDerivAt (fun Ξ => W Ξ t) L 0 := by
  have h0σ : ‖(0 : ((Point n × Point n) × (Point n × Point n)))‖ ≤ σ := by
    rw [norm_zero]; exact hσ.le
  -- (a) `G = doubledField` is `C^∞`; discharge the engine's regularity inputs (mirrors the
  --     velocity-only `doubledFlow_endpoint_baseVelocity_hasFDerivAt_exists`).
  have hGcd : ContDiff ℝ (⊤ : WithTop ℕ∞) (doubledField g gi) := contDiff_doubledField g gi hC
  have hdiff : ∀ x ∈ S, DifferentiableAt ℝ (doubledField g gi) x :=
    fun x _ => (hGcd.differentiable (by simp)).differentiableAt
  have hGcd' : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (doubledField g gi)) :=
    hGcd.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top
  have hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ (doubledField g gi)) x :=
    fun x _ => (hGcd'.differentiable (by simp)).differentiableAt
  obtain ⟨M₂, _hM₂0, hbound2⟩ := doubledField_fderiv2_bddOn_compact g gi hC hScompact
  obtain ⟨Kf, hKf0, hKfbd⟩ := doubledField_fderiv_bddOn_compact g gi hC hScompact
  set K₀ : NNReal := ⟨Kf, hKf0⟩ with hK₀def
  have hLip : LipschitzOnWith K₀ (doubledField g gi) S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hdiff x (by trivial))
      (fun x hx => by rw [← NNReal.coe_le_coe]; simpa [hK₀def] using hKfbd x hx)
      hSconvex
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (doubledField g gi) (W 0 τ)‖ ≤ Kf :=
    fun τ hτ => hKfbd (W 0 τ) (hmem 0 h0σ τ hτ)
  -- (b) apply the abstract Fréchet first-jet capstone to `Φ := doubledField g gi` with the FULL joint
  --     seed `id` (the whole doubled phase space is the perturbation index).
  set seed : ((Point n × Point n) × (Point n × Point n)) →L[ℝ]
      ((Point n × Point n) × (Point n × Point n)) :=
    ContinuousLinearMap.id ℝ ((Point n × Point n) × (Point n × Point n)) with hseeddef
  have hseednorm : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖seed Ξ‖ = ‖Ξ‖ := by
    intro Ξ; rw [hseeddef]; simp
  have hV0' : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), V Ξ 0 = seed Ξ := by
    intro Ξ; rw [hseeddef]; simpa using hV0 Ξ
  have hIC' : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ‖ ≤ σ →
      W Ξ 0 - W 0 0 = seed Ξ := by
    intro Ξ hΞ; rw [hseeddef]; simpa using hIC Ξ hΞ
  exact autonomousFlow_endpoint_hasFDerivAt_window_exists (doubledField g gi) hKf0 hσ ht hSconvex
    hdiff hdiff2 hbound2 hLip hseednorm hWode hVode hV0' hIC' hKb hmem

/-- **Second-variation projection of the joint second-order derivative.**  The `.2` component of the
    doubled endpoint (the geodesic flow's first-variation / Jacobi field) is, JOINTLY in the full doubled
    perturbation `Ξ`, Fréchet-differentiable at `0`, with derivative `Ξ ↦ (V Ξ t).2` — the precise
    "`D_Ξ` of (the flow derivative)" shape carrying the base flow's SECOND-order data.  DERIVED by
    post-composing the joint core with the second-projection `ContinuousLinearMap.snd`. -/
theorem doubledFlow_endpoint_joint_snd_hasFDerivAt_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n))}
    {S : Set ((Point n × Point n) × (Point n × Point n))} {σ : ℝ}
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S) (hσ : 0 < σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hWode : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ‖ ≤ σ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (W Ξ) (doubledField g gi (W Ξ τ)) τ)
    (hVode : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)),
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (V Ξ) (fderiv ℝ (doubledField g gi) (W 0 τ) (V Ξ τ)) τ)
    (hV0 : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), V Ξ 0 = Ξ)
    (hIC : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ‖ ≤ σ → W Ξ 0 - W 0 0 = Ξ)
    (hmem : ∀ Ξ : ((Point n × Point n) × (Point n × Point n)), ‖Ξ‖ ≤ σ →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, W Ξ τ ∈ S) :
    ∃ L : ((Point n × Point n) × (Point n × Point n)) →L[ℝ] (Point n × Point n),
      (∀ Ξ : ((Point n × Point n) × (Point n × Point n)), L Ξ = (V Ξ t).2) ∧
        HasFDerivAt (fun Ξ => (W Ξ t).2) L 0 := by
  obtain ⟨L, hLeq, hFD⟩ := doubledFlow_endpoint_joint_hasFDerivAt_exists g gi hC hScompact hSconvex
    hσ ht hWode hVode hV0 hIC hmem
  refine ⟨(ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)).comp L,
    fun Ξ => by simp [hLeq Ξ], ?_⟩
  have := (ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)).hasFDerivAt.comp
    (0 : ((Point n × Point n) × (Point n × Point n))) hFD
  simpa [Function.comp] using this

/-- **Velocity-slot restriction of the joint second-order derivative.**  The joint doubled derivative `L`
    precomposed with the velocity-subspace inclusion `δ ↦ (0, δ)` recovers the velocity-only doubled
    derivative register (`doubledFlow_endpoint_baseVelocity_hasFDerivAt_exists`): the velocity-slice map
    `δ ↦ W (0, δ) t` has Fréchet derivative `L.comp (inr ..)` at `0`. -/
theorem doubledFlow_endpoint_baseVelocity_ofJoint
    {W : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n))}
    {L : ((Point n × Point n) × (Point n × Point n)) →L[ℝ]
      ((Point n × Point n) × (Point n × Point n))} {t : ℝ}
    (hFD : HasFDerivAt (fun Ξ => W Ξ t) L 0) :
    HasFDerivAt
      (fun δ : (Point n × Point n) => W ((0, δ) : (Point n × Point n) × (Point n × Point n)) t)
      (L.comp (ContinuousLinearMap.inr ℝ (Point n × Point n) (Point n × Point n))) 0 := by
  have hinr : HasFDerivAt
      (fun δ : (Point n × Point n) => ((0, δ) : (Point n × Point n) × (Point n × Point n)))
      (ContinuousLinearMap.inr ℝ (Point n × Point n) (Point n × Point n)) 0 :=
    (ContinuousLinearMap.inr ℝ (Point n × Point n) (Point n × Point n)).hasFDerivAt
  have hFD0 : HasFDerivAt (fun Ξ => W Ξ t) L
      ((ContinuousLinearMap.inr ℝ (Point n × Point n) (Point n × Point n)) 0) := by
    simpa using hFD
  simpa [Function.comp] using hFD0.comp (0 : (Point n × Point n)) hinr

end JointSecondOrder

end QIQTH.ExpMap
