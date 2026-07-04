/-
  THE MODULAR CONJUGATION J6 (THE_MODULAR_CONJUGATION_PLAN.md) — J COMMUTES WITH THE
  MODULAR GROUP: `JΔ^{it} = Δ^{it}J`.

  Deliverables:
  • `jRaw_flowRaw` — the raw exchange `J(U_t x) = U_t(Jx)` on `⨁` (componentwise J2
    `cornerFlow_jStage`; the flow acts IN PLACE, no stage shift, so the diagonal induction
    closes it);
  • `towerJ_towerFlow` — the exchange on the FULL completion, `J(U_t ξ) = U_t(Jξ)`
    (completion induction + the raw exchange, the J4 `towerJ_involutive` template);
  • `towerJ_towerModUnitary` ★ — **`JΔ^{it} = Δ^{it}J`** pointwise, via the
    IDENTIFICATION `towerFlow = towerModUnitary` (ID4).

  THE ORDER GUARD (the campaign's sign check, verified on eigenvectors in the consult
  against `towerModUnitary_of_single`): the correct commutation is `JΔ^{it} = Δ^{it}J`,
  NOT `JΔ^{it} = Δ^{−it}J`. The antilinearity of J flips the `i` (conj e^{itλ} = e^{−itλ}),
  and `JΔJ = Δ⁻¹` flips it back — the two flips cancel, landing on `+t`. Stage-level
  shadow: J2's `cornerFlow_jStage`, where the ᴴ inside `jStage` reverses the
  `ρ^{it}`-sandwich AND conjugates its entries (`(ρ^{it})ᴴ = ρ^{−it}`), restoring `+t`.

  HONEST SCOPE: the commutation of the constructed anti-unitary with the constructed
  modular group ONLY — stated POINTWISE (the composite `J ∘ Δ^{it}` mixes the ring-homs
  `starRingEnd ℂ` and `id`, so no bundled `∘L` composition is attempted). NO Tomita II
  inclusion (J7–J8), no unbounded Δ^{1/2}, no J M J = M′ claim. Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.ConjPre
import QIQTH.TowerGNS.Flow
import QIQTH.TowerGNS.Identification

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The raw exchange (everything at `⨁` — the R3 lesson) -/

/-- **The raw exchange**: the raw conjugation commutes with the raw flow —
    `J(U_t x) = U_t(Jx)` on the raw direct sum. Both maps act IN PLACE (same stage, no
    stage shift), so `DirectSum.induction_on` reduces to a pure component, where the
    exchange is exactly J2's stage-level law `cornerFlow_jStage`. -/
theorem jRaw_flowRaw (t : ℝ) (x : ⨁ C : Finset M, DiamondAlg L C) :
    jRaw L ω β (flowRaw L ω β t x) = flowRaw L ω β t (jRaw L ω β x) := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero (flowRaw L ω β t), map_zero (jRaw L ω β), map_zero (flowRaw L ω β t)]
  | of C a => rw [flowRaw_of, jRaw_of, jRaw_of, flowRaw_of, cornerFlow_jStage]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (flowRaw L ω β t), map_add (jRaw L ω β), h₁, h₂,
      map_add (jRaw L ω β), map_add (flowRaw L ω β t)]

/-! ### The exchange on the completion -/

/-- **The conjugation commutes with the transported flow on the FULL completion**:
    `J(U_t ξ) = U_t(Jξ)` — completion induction (both sides continuous) + the raw
    exchange on the dense coerced core. Stated POINTWISE (the composite mixes the
    ring-homs `starRingEnd ℂ` and `id`). -/
theorem towerJ_towerFlow (t : ℝ) (ξ : TowerGNS L ω β) :
    towerJ L ω β (towerFlow L ω β t ξ) = towerFlow L ω β t (towerJ L ω β ξ) := by
  induction ξ using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [towerFlow_coe, towerJ_coe, towerJ_coe, towerFlow_coe]
    have h : jPre L ω β (flowPre L ω β t x) = flowPre L ω β t (jPre L ω β x) :=
      jRaw_flowRaw L ω β t x
    rw [h]

/-! ### ★ J6 CAPSTONE — `JΔ^{it} = Δ^{it}J` -/

/-- **★ J COMMUTES WITH THE MODULAR GROUP**: `J Δ^{it} ξ = Δ^{it} J ξ` for every `t` and
    every `ξ` — the exchange with the transported flow, rewritten through the
    IDENTIFICATION `towerFlow = towerModUnitary` (ID4).

    THE ORDER GUARD (sign verified on eigenvectors in the consult): this is the CORRECT
    commutation — `JΔ^{it} = Δ^{it}J`, NOT `Δ^{−it}J`. The antilinearity of J flips the
    `i` once (conj e^{itλ} = e^{−itλ}), and `JΔJ = Δ⁻¹` flips it back; the two flips
    cancel. Stated POINTWISE — no mixed-ring-hom `∘L` bundling is attempted. -/
theorem towerJ_towerModUnitary (t : ℝ) (ξ : TowerGNS L ω β) :
    towerJ L ω β (towerModUnitary L ω β t ξ)
      = towerModUnitary L ω β t (towerJ L ω β ξ) := by
  rw [← towerFlow_eq_towerModUnitary]
  exact towerJ_towerFlow L ω β t ξ

end QIQTH.TowerGNS
