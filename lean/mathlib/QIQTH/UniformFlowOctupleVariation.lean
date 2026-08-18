/-
  UniformFlowOctupleVariation — Plan v6 Task I (C⁴ climb, brick 3): the directional smooth dependence
  of the OCTUPLED flow on its base initial condition — one order up from
  `UniformFlowQuadrupleVariation.quadrupledField_variation_exists_uncond`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  NOT `a₁ = R/6`.  A field-regularity instance feeding the fifth-jet
  value-identity (the `Z1↑`-analogue one order up), re-derived DIRECTLY on the uniform tube (NO `expRho`).

  ── WHAT LANDS (DERIVED; NO `sorry`, NO new axioms, NO `expRho`).
    • `octupledField_variation_exists_uncond` — for a one-parameter family `Y : ℝ → ℝ → St8` of
        `octupledField = genericDoubled (genericDoubled (doubledField g gi))`-integral curves whose base
        IC is perturbed linearly (`Y s 0 − Y 0 0 = s·p`), confined in a compact convex `S`, and an
        `octupledField`-linearized field `V` along the base curve with seed `p`, the base-IC derivative
        of the octupled-flow endpoint EXISTS and equals `V t`:  `HasDerivAt (fun s => Y s t) (V t) 0`.
      DERIVED by specialising the field-agnostic `AutonomousDep.autonomousField_variation_exists_uncond`
      at `Φ := octupledField`, discharging all engine regularity inputs from `contDiff_octupledField`
      + `octupledField_fderiv{,2}_bddOn_compact`.  This is the directional (scalar `s`) smooth-dependence
      engine the fifth-jet value-identity consumes.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowOctupleField
import QIQTH.UniformFlowOctupleSupply
import QIQTH.AutonomousSmoothDep
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.AutonomousDep
open scoped Topology NNReal

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 4000000
set_option maxSynthPendingDepth 20

variable {n : ℕ}

/-- **Directional smooth dependence of the OCTUPLED flow on its base initial condition.**  For
    `Φ = octupledField = genericDoubled (genericDoubled (doubledField g gi))` on the 8-fold phase space,
    a family `Y` of `Φ`-integral curves on `[0,1]` with base IC perturbed linearly (`Y s 0 − Y 0 0 = s·p`)
    inside a compact convex `S`, and `V` a `Φ`-linearized field along the base curve with `V 0 = p`, the
    base-IC derivative of the endpoint exists and equals `V t`:  `HasDerivAt (fun s => Y s t) (V t) 0`.
    Mirror of `quadrupledField_variation_exists_uncond` one order up; all regularity discharged from
    `contDiff_octupledField`. -/
theorem octupledField_variation_exists_uncond (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → St8 n} {V : ℝ → St8 n} {p : St8 n} {S : Set (St8 n)} {σ : ℝ}
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ)
    (hYode : ∀ s ∈ Set.Icc (-σ) σ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (genericDoubled (genericDoubled (doubledField g gi)) (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi))) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = p)
    (hIC : ∀ s ∈ Set.Icc (-σ) σ, Y s 0 - Y 0 0 = s • p)
    (hmem : ∀ s ∈ Set.Icc (-σ) σ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  set G : St8 n → St8 n := genericDoubled (genericDoubled (doubledField g gi)) with hGdef
  have hGcd : ContDiff ℝ (⊤ : WithTop ℕ∞) G := contDiff_octupledField g gi hC
  have hdiff : ∀ x ∈ S, DifferentiableAt ℝ G x :=
    fun x _ => (hGcd.differentiable (by simp)).differentiableAt
  have hGcd' : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ G) :=
    hGcd.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top
  have hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ G) x :=
    fun x _ => (hGcd'.differentiable (by simp)).differentiableAt
  obtain ⟨M₂, _hM₂0, hbound2⟩ := octupledField_fderiv2_bddOn_compact g gi hC hScompact
  obtain ⟨Kf, hKf0, hKfbd⟩ := octupledField_fderiv_bddOn_compact g gi hC hScompact
  set K₀ : NNReal := ⟨Kf, hKf0⟩ with hK₀def
  have hLip : LipschitzOnWith K₀ G S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hdiff x (by trivial))
      (fun x hx => by rw [← NNReal.coe_le_coe]; simpa [hK₀def] using hKfbd x hx)
      hSconvex
  have h0mem : (0 : ℝ) ∈ Set.Icc (-σ) σ := ⟨by linarith, hσ.le⟩
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ G (Y 0 τ)‖ ≤ Kf :=
    fun τ hτ => hKfbd (Y 0 τ) (hmem 0 h0mem τ hτ)
  exact QIQTH.AutonomousDep.autonomousField_variation_exists_uncond G hKf0 ht hσ hSconvex
    hdiff hdiff2 hbound2 hLip hYode hVode hV0 hIC hKb hmem

end QIQTH.ExpMap
