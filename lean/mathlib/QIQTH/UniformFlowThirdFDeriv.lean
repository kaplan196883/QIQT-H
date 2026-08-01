/-
  UniformFlowThirdFDeriv — J4-72 (Brick-A β): the C³ layer's W2 groundwork for `uniformFlowExp`.

  Mirrors the C² climb ONE ORDER UP.  The C² layer closed the per-seed SECOND jet
  (`uniformFlowExp_fderiv_apply_hasFDerivAt`, R2-b) by feeding the base-velocity-perturbed CONFINED
  doubled uniform-tube supply (R2-a) into the field-agnostic first-jet engine
  (`autonomousFlow_endpoint_hasFDerivAt_window_exists`) with `Φ := doubledField g gi`, then projecting
  the `.2.1` doubled-endpoint component (via the scalar-slot value-id).

  W2 (the per-seed THIRD jet) is, provably, ONE MORE doubling: the engine differentiates the endpoint it
  calls `W`, NOT the linearized endpoint it calls `V`; to differentiate the doubled-linearized (=
  second-variation) endpoint one must make it part of a NEW `W` by passing to the doubling of
  `doubledField` — the QUADRUPLED field
      `Φ̃ = genericDoubled (doubledField g gi)`,   `genericDoubled Φ z = (Φ z.1, fderiv ℝ Φ z.1 z.2)`,
  on the quadruple phase space `((P×P)×(P×P)) × ((P×P)×(P×P))`.  Reusing only the R2-a/R2-b derivative is
  insufficient: its `.2.1` is exactly the second jet and its `.2.2` is the Jacobi VELOCITY, neither the
  third jet (adversarially confirmed).

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no smuggled 3rd-order conclusion, no `expRho`)

  * `uniformFlowExp_fderiv_apply_differentiableOn` (**W2-pre**) — the applied SECOND-jet map
        `w ↦ fderiv ℝ (uniformFlowExp g gi hC hK q) w b`
    is `DifferentiableOn ℝ` the FULL uniform velocity ball `B(0, ρ_K)`.  DERIVED directly from R2-b
    (`uniformFlowExp_fderiv_apply_hasFDerivAt` holds at EVERY interior velocity).  This makes
    `fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u b) w` a GENUINE derivative on the ball — the
    prerequisite for even stating the scalar-slot third jet `w ↦ fderiv (…) w a`.

  * `genericDoubled` + `contDiff_genericDoubled` + `genericDoubled_fderiv_bddOn_compact` +
    `genericDoubled_fderiv2_bddOn_compact` (**W2-infra, field-agnostic**) — the GENERIC tangent-lift
    (Jacobi doubling) of an arbitrary field `Φ : E → E`, with its `C^∞` regularity and its compact-sup
    bounds on `‖DΦ̃‖` and `‖D²Φ̃‖`.  These are EXACTLY the engine-regularity inputs (`hdiff`/`hdiff2`/
    `hbound2`/`hLip`/`hKb`) that the future quadruple-flow supply consumes — the C² climb obtained the
    analogous inputs from the `doubledField`-specialized `contDiff_doubledField` /
    `doubledField_fderiv{,2}_bddOn_compact`; this is that regularity ONE ORDER UP, reusably.

  * `contDiff_quadrupledField` + `quadrupledField_fderiv_bddOn_compact` +
    `quadrupledField_fderiv2_bddOn_compact` (**W2-infra, instantiated**) — the concrete quadrupled field
    `genericDoubled (doubledField g gi)` is `C^∞` with compact-sup `DΦ̃`/`D²Φ̃` bounds, from `hC`.  This
    is the quadruple field's full regularity, ready to feed the abstract engine.

  ## HONEST FIREWALL (binding) — what W2/W3/W4 still need

  The per-seed THIRD-jet EXISTENCE
      `∃ L₃, HasFDerivAt (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u b) w a) L₃ v`
  is NOT closed here.  What remains for W2 is the QUADRUPLE-flow SUPPLY (the R2-a construction one order
  up): the quadruple tube `W̃ δ = ((tube(v+δ), Jf δ), doubled-linearized field)` as a genuine
  `Φ̃`-integral curve on the window, confined in a compact convex product ball, with the base-velocity
  linear IC and the `Φ̃`-linearized field; feeding `autonomousFlow_endpoint_hasFDerivAt_window_exists Φ̃`
  (whose regularity inputs THIS file supplies), extracting the third-jet component, and transferring by a
  scalar-slot value-id (a `clm_fderiv_value_of_directional`/`hid_of_doubled_data` analogue one order up).
  CARRIED.  W3 (uniform `‖B₃‖ ≤ M₃j`, from W1's `Z₃` cubic bound read at `τ = 1` + a polarization
  assembly) and W4 (`uniformFlowExp ∈ C³ ⟹ g̃ ∈ C²` + residual Raychaudhuri wiring) CARRIED as before.

  This file does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.  NO `expRho`.
-/
import QIQTH.UniformFlowThirdJet
import QIQTH.UniformFlowHessianDiag
import QIQTH.UniformFlowSecondSupply
import QIQTH.UniformFlowSecondFDeriv
import QIQTH.UniformFlowHessian
import QIQTH.JacobiOperatorFDeriv
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

/-! ### W2-infra (field-agnostic) — the generic tangent lift (Jacobi doubling) and its regularity -/

section GenericTangentLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The generic tangent lift (Jacobi doubling) of a field.**  For `Φ : E → E`,
    `genericDoubled Φ (z) = (Φ z.1, (fderiv ℝ Φ z.1) z.2)` on `E × E` — the field whose integral curves
    are `(x, ξ)` with `x` a `Φ`-integral curve and `ξ` the `Φ`-linearized (variation/Jacobi) field along
    it.  Field-agnostic generalization of `doubledField` (which is `genericDoubled geodesicField`). -/
noncomputable def genericDoubled (Φ : E → E) : E × E → E × E :=
  fun z => (Φ z.1, fderiv ℝ Φ z.1 z.2)

/-- **The generic tangent lift is `C^∞`.**  DERIVED structurally: the first component is `Φ ∘ fst`, the
    second the bilinear application `z ↦ (fderiv ℝ Φ z.1)(z.2) = ((fderiv ℝ Φ ∘ fst) z)(snd z)`, `C^∞` by
    `ContDiff.clm_apply` (`fderiv ℝ Φ` is `C^∞` by `ContDiff.fderiv_right`).  Mirrors
    `contDiff_doubledField` one order up.  NO hypotheses beyond `Φ ∈ C^∞`. -/
theorem contDiff_genericDoubled {Φ : E → E} (hΦ : ContDiff ℝ (⊤ : WithTop ℕ∞) Φ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (genericDoubled Φ) := by
  refine ContDiff.prodMk ?_ ?_
  · exact hΦ.comp contDiff_fst
  · exact ContDiff.clm_apply
      ((hΦ.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).comp contDiff_fst) contDiff_snd

/-- **Uniform bound on `DΦ̃` over a compact set.**  `fderiv ℝ (genericDoubled Φ)` is continuous
    (`genericDoubled Φ` is `C^∞`), hence bounded on any compact `S`.  This is the `hLip`/`hKb` engine
    input one order up.  DERIVED. -/
theorem genericDoubled_fderiv_bddOn_compact {Φ : E → E}
    (hΦ : ContDiff ℝ (⊤ : WithTop ℕ∞) Φ) {S : Set (E × E)} (hS : IsCompact S) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (genericDoubled Φ) z‖ ≤ Kb := by
  have hcont : Continuous (fderiv ℝ (genericDoubled Φ)) :=
    (contDiff_genericDoubled hΦ).continuous_fderiv (by simp)
  obtain ⟨C, hCb⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hCb z hz).trans (le_max_left _ _)⟩

/-- **Uniform bound on `D²Φ̃` over a compact set.**  `fderiv ℝ (fderiv ℝ (genericDoubled Φ))` is
    continuous (`genericDoubled Φ` is `C^∞`, so `DΦ̃` and `D²Φ̃` are), hence bounded on any compact `S`.
    This is the `hbound2` engine input one order up.  DERIVED. -/
theorem genericDoubled_fderiv2_bddOn_compact {Φ : E → E}
    (hΦ : ContDiff ℝ (⊤ : WithTop ℕ∞) Φ) {S : Set (E × E)} (hS : IsCompact S) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S,
      ‖fderiv ℝ (fderiv ℝ (genericDoubled Φ)) z‖ ≤ Kb := by
  have hcont : Continuous (fderiv ℝ (fderiv ℝ (genericDoubled Φ))) :=
    ((contDiff_genericDoubled hΦ).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
      (by simp)
  obtain ⟨C, hCb⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hCb z hz).trans (le_max_left _ _)⟩

end GenericTangentLift

/-! ### W2-infra (instantiated) — the concrete quadrupled field `genericDoubled (doubledField g gi)` -/

section QuadrupledField

variable {n : ℕ}

/-- **The quadrupled field is `C^∞`.**  `Φ̃ = genericDoubled (doubledField g gi)` on the quadruple phase
    space is `C^∞`, since `doubledField g gi` is (`contDiff_doubledField`).  This is the concrete W2
    quadruple-flow field's regularity, from `hC`.  DERIVED. -/
theorem contDiff_quadrupledField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (genericDoubled (doubledField g gi)) :=
  contDiff_genericDoubled (contDiff_doubledField g gi hC)

/-- **Uniform bound on `DΦ̃` for the quadrupled field over a compact set.**  DERIVED. -/
theorem quadrupledField_fderiv_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (((Point n × Point n) × (Point n × Point n)) × ((Point n × Point n) × (Point n × Point n)))}
    (hS : IsCompact S) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (genericDoubled (doubledField g gi)) z‖ ≤ Kb :=
  genericDoubled_fderiv_bddOn_compact (contDiff_doubledField g gi hC) hS

/-- **Uniform bound on `D²Φ̃` for the quadrupled field over a compact set.**  DERIVED. -/
theorem quadrupledField_fderiv2_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (((Point n × Point n) × (Point n × Point n)) × ((Point n × Point n) × (Point n × Point n)))}
    (hS : IsCompact S) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S,
      ‖fderiv ℝ (fderiv ℝ (genericDoubled (doubledField g gi))) z‖ ≤ Kb :=
  genericDoubled_fderiv2_bddOn_compact (contDiff_doubledField g gi hC) hS

end QuadrupledField

/-! ### W2-pre — `DifferentiableOn` of the applied second-jet map on the full velocity ball -/

section AppliedSecondJetRegularity

variable {n : ℕ}

/-- **W2-pre — the applied SECOND-jet map is `DifferentiableOn` the uniform velocity ball.**  For
    `q ∈ K` and each seed `b`, the map `w ↦ fderiv ℝ (uniformFlowExp g gi hC hK q) w b` is
    `DifferentiableOn ℝ` on `Metric.ball 0 (uniformFlowRadius g gi hC hK)`.  DERIVED directly from R2-b
    (`uniformFlowExp_fderiv_apply_hasFDerivAt`), which supplies a Fréchet derivative at EVERY interior
    velocity.  This makes `fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u b) w` a genuine derivative on
    the ball — the prerequisite for the scalar-slot third jet.  NO `expRho`. -/
theorem uniformFlowExp_fderiv_apply_differentiableOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (b : Point n) :
    DifferentiableOn ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w b)
      (Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
  intro v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  obtain ⟨L₂, hL₂⟩ := uniformFlowExp_fderiv_apply_hasFDerivAt g gi hC hK q hq v hv b
  exact hL₂.differentiableAt.differentiableWithinAt

end AppliedSecondJetRegularity

end QIQTH.ExpMap
