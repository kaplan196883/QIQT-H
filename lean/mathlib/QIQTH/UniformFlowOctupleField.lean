/-
  UniformFlowOctupleField — Plan v6 Task I (C³ climb, brick 1): the octupled field regularity and the
  FIELD-AGNOSTIC block formula for the second component of `D(genericDoubled Φ)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  NOT `a₁ = R/6`.  One infrastructure brick of the Plan-v6 climb to the FOURTH
  velocity-jet of `uniformFlowExp` (⟹ `D³φ` continuity ⟹ `C³`), re-deriving regularity DIRECTLY on the
  uniform tube with NO `expRho`.

  The uniform-tube variational tower climbs one velocity-derivative order per `genericDoubled` doubling:
      `geodesicField` → D¹,  `doubledField = genericDoubled geodesicField` → D²,
      `quadrupledField = genericDoubled doubledField` → D³ (banked, unconditional).
  The FOURTH jet (⟹ C³) needs the OCTUPLED field
      `octupledField := genericDoubled (genericDoubled (doubledField g gi))`
  on the 8-fold phase space, with its `C^∞` + `‖DΦ̃‖`/`‖D²Φ̃‖`-bounded-on-compact regularity supply.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms, NO `expRho`).
    • `genericDoubled_fderiv_snd_apply` — ★ the FIELD-AGNOSTIC block formula (mirror of the depth-1
        `JacobiOperatorFDeriv.doubledField_fderiv_snd_apply`, generalised to an arbitrary `C^∞` field
        `Φ : E → E`):  `((fderiv ℝ (genericDoubled Φ) e) u).2 = DΦ(e.1)·u.2 + D²Φ(e.1)(u.1)(e.2)`.
        This is the coupling that makes every doubled-linearized field a "second-variation ODE"; being
        field-agnostic, it instantiates at every doubling depth (the depth-2 quadrupled-field instance
        feeds the fourth-jet value-identity).
    • `contDiff_octupledField` / `octupledField_fderiv_bddOn_compact` /
        `octupledField_fderiv2_bddOn_compact` — the 8-fold field's `C^∞` + compact operator bounds
        (delegations to the field-agnostic `genericDoubled_*` engine at `Φ := quadrupledField`).

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.UniformFlowThirdFDeriv

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped Topology

set_option maxHeartbeats 1000000

/-! ### The FIELD-AGNOSTIC block formula for `D(genericDoubled Φ)`'s second component. -/

section GenericBlock

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Field-agnostic block formula for the second component of `D(genericDoubled Φ)`.**  For a `C^∞`
    field `Φ : E → E`, with `Φ̃ = genericDoubled Φ` (`Φ̃ (P,W) = (Φ P, DΦ(P)·W)`), the second
    `E`-component of the Fréchet derivative applied to a direction `u` decomposes as
        `((fderiv ℝ Φ̃ e) u).2 = fderiv ℝ Φ e.1 u.2 + fderiv ℝ (fderiv ℝ Φ) e.1 u.1 e.2`.
    DERIVED via `HasFDerivAt.clm_apply` + `HasFDerivAt.prodMk`.  Mirrors
    `JacobiOperatorFDeriv.doubledField_fderiv_snd_apply` one abstraction up — instantiates at any
    doubling depth.  NO `expRho`. -/
theorem genericDoubled_fderiv_snd_apply {Φ : E → E}
    (hΦ : ContDiff ℝ (⊤ : WithTop ℕ∞) Φ) (e u : E × E) :
    ((fderiv ℝ (genericDoubled Φ) e) u).2
      = fderiv ℝ Φ e.1 u.2 + fderiv ℝ (fderiv ℝ Φ) e.1 u.1 e.2 := by
  have hΦdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hdΦdiff : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).differentiable (by simp)
  have hF : HasFDerivAt Φ (fderiv ℝ Φ e.1) e.1 := (hΦdiff e.1).hasFDerivAt
  have hdF : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) e.1) e.1 := (hdΦdiff e.1).hasFDerivAt
  -- first component `p ↦ Φ p.1`
  have h1 : HasFDerivAt (fun p : E × E => Φ p.1)
      ((fderiv ℝ Φ e.1).comp (ContinuousLinearMap.fst ℝ _ _)) e :=
    hF.comp e (hasFDerivAt_fst)
  -- CLM-valued factor `c p = DΦ p.1`, derivative `(D²Φ e.1) ∘ fst`
  have hc : HasFDerivAt (fun p : E × E => fderiv ℝ Φ p.1)
      ((fderiv ℝ (fderiv ℝ Φ) e.1).comp (ContinuousLinearMap.fst ℝ _ _)) e :=
    hdF.comp e (hasFDerivAt_fst)
  have hu : HasFDerivAt (fun p : E × E => p.2) (ContinuousLinearMap.snd ℝ E E) e :=
    hasFDerivAt_snd
  have h2 := hc.clm_apply hu
  have hprod : HasFDerivAt (genericDoubled Φ)
      (((fderiv ℝ Φ e.1).comp (ContinuousLinearMap.fst ℝ _ _)).prod
        (((fderiv ℝ Φ e.1).comp (ContinuousLinearMap.snd ℝ E E))
          + ((fderiv ℝ (fderiv ℝ Φ) e.1).comp (ContinuousLinearMap.fst ℝ _ _)).flip e.2)) e :=
    h1.prodMk h2
  rw [hprod.fderiv]
  simp [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

end GenericBlock

/-! ### The octupled field `genericDoubled quadrupledField` and its regularity supply. -/

section OctupledField

variable {n : ℕ}

-- The octupled field is spelled out as `genericDoubled (genericDoubled (doubledField g gi))`
-- throughout, to match the `genericDoubled_*` engine hypotheses exactly.

/-- **The octupled field is `C^∞`.**  `Φ̃̃ = genericDoubled (genericDoubled (doubledField g gi))` on the
    8-fold phase space is `C^∞`, since the quadrupled field is (`contDiff_quadrupledField`).  DERIVED. -/
theorem contDiff_octupledField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (genericDoubled (genericDoubled (doubledField g gi))) :=
  contDiff_genericDoubled (contDiff_quadrupledField g gi hC)

/-- **Uniform bound on `DΦ̃̃` for the octupled field over a compact set.**  DERIVED. -/
theorem octupledField_fderiv_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (((((Point n × Point n) × (Point n × Point n)) × ((Point n × Point n) × (Point n × Point n))) ×
        (((Point n × Point n) × (Point n × Point n)) × ((Point n × Point n) × (Point n × Point n)))))}
    (hS : IsCompact S) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S,
      ‖fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi))) z‖ ≤ Kb :=
  genericDoubled_fderiv_bddOn_compact (contDiff_quadrupledField g gi hC) hS

/-- **Uniform bound on `D²Φ̃̃` for the octupled field over a compact set.**  DERIVED. -/
theorem octupledField_fderiv2_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (((((Point n × Point n) × (Point n × Point n)) × ((Point n × Point n) × (Point n × Point n))) ×
        (((Point n × Point n) × (Point n × Point n)) × ((Point n × Point n) × (Point n × Point n)))))}
    (hS : IsCompact S) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S,
      ‖fderiv ℝ (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))) z‖ ≤ Kb :=
  genericDoubled_fderiv2_bddOn_compact (contDiff_quadrupledField g gi hC) hS

end OctupledField

end QIQTH.ExpMap
