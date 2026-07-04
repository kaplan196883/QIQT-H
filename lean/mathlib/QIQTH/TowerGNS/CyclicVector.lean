/-
  THE REPRESENTATION R8 (THE_REPRESENTATION_PLAN.md) — THE CYCLIC VECTOR IMPLEMENTS THE STATES,
  AND ITS ORBIT IS DENSE.

  `towerRep_cyclicVec_of`: π_C(a) Ω = ↑(of C a) — acting on the cyclic vector reproduces the
  pure tower components (the pre-level image lands at the propositionally-equal-but-not-defeq
  stage `C ⊔ ∅`; `cornerEmbed_one` + the germ identity glue it back to stage `C` WITHOUT any
  type-cast across `Finset.union_empty`).

  CAPSTONE `towerRep_inner_cyclicVec`: ⟪Ω, π_C(a) Ω⟫ = φ_C(a) — THE VECTOR STATE OF Ω IS THE
  GIBBS STATE at every stage: the GNS triple (H, π, Ω) implements the entire compatible family
  of finite-corner Gibbs states on one Hilbert space.

  CAPSTONE `dense_span_towerRep_cyclicVec`: the linear span of the orbit {π_C(a) Ω} is dense —
  Ω is CYCLIC for the tower representation: every pure component ↑(of C a) is in the orbit by
  `towerRep_cyclicVec_of`, every coerced pre-vector is a finite sum of pure components (raw
  `DirectSum` induction + additivity of the coercion), and the coerced pre-space is dense in
  the completion (`Completion.denseRange_coe`).

  HONEST SCOPE: cyclicity + the state identity ONLY — Ω is NOT claimed separating (no
  faithfulness/modular statement is made here).

  LEAN ARCHITECTURE (the R3 lesson, binding): raw `⨁` computations are entered by `show` in
  application position only — the synonym is never crossed by `rw`.
-/
import Mathlib
import QIQTH.TowerGNS.Representation

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The orbit of the cyclic vector is the tower of pure components -/

/-- **π_C(a) Ω = ↑(of C a)** — acting on the cyclic vector by any corner element reproduces
    the pure tower component. The pre-level image lands at stage `C ⊔ ∅` (propositionally `C`,
    NOT definitionally); `cornerEmbed_one` + `mul_one` reduce the matrix and the germ identity
    glues the stage — no type-cast across `Finset.union_empty` is ever taken. -/
theorem towerRep_cyclicVec_of (C : Finset M) (a : DiamondAlg L C) :
    towerRep L ω β C a (towerCyclicVec L ω β)
      = ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β) := by
  rw [towerRep_apply, towerCyclicVec, towerRepCLM_coe]
  have h1 : towerLeftMul L ω β C a (towerOf L ω β ∅ 1)
      = towerOf L ω β (C ⊔ ∅) (cornerEmbed L C (C ⊔ ∅) Finset.subset_union_left a) := by
    show leftMulRaw L C a (DirectSum.of (fun C : Finset M => DiamondAlg L C) ∅ 1)
        = DirectSum.of (fun C : Finset M => DiamondAlg L C) (C ⊔ ∅)
            (cornerEmbed L C (C ⊔ ∅) Finset.subset_union_left a)
    rw [leftMulRaw_of, cornerEmbed_one, mul_one]
  rw [h1]
  exact towerGerm L ω β Finset.subset_union_left a

/-! ### R8 CAPSTONE — the vector state of Ω is the Gibbs state -/

/-- **R8 CAPSTONE — THE CYCLIC VECTOR IMPLEMENTS THE STATES**:
    `⟪Ω, π_C(a) Ω⟫ = φ_C(a) = tr(ρ_C a)` — the vector state of Ω under the tower
    representation IS the finite-corner Gibbs state, at EVERY stage simultaneously: the GNS
    triple (TowerGNS, towerRep, Ω) implements the whole compatible family on one Hilbert
    space. (Ω is NOT claimed separating.) -/
theorem towerRep_inner_cyclicVec (C : Finset M) (a : DiamondAlg L C) :
    ⟪towerCyclicVec L ω β, towerRep L ω β C a (towerCyclicVec L ω β)⟫_ℂ
      = stateOf (gibbsDensity L C ω β) a := by
  rw [towerRep_cyclicVec_of, towerCyclicVec, inner_coe_of_of,
    pairInner_embed L ω β ∅ C C (Finset.empty_subset C) subset_rfl,
    cornerEmbed_refl, cornerEmbed_one, gnsInner, Matrix.conjTranspose_one, one_mul]

/-! ### R8 CAPSTONE — cyclicity: the orbit of Ω spans a dense subspace -/

/-- Every coerced pre-space vector lies in the span of the orbit of Ω: raw `DirectSum`
    induction — the pure components are IN the orbit (`towerRep_cyclicVec_of`), and the
    coercion is additive. -/
theorem towerCoe_mem_span_towerRep_cyclicVec (x : ⨁ C : Finset M, DiamondAlg L C) :
    towerCoe L ω β x ∈ Submodule.span ℂ
      {v : TowerGNS L ω β | ∃ (C : Finset M) (a : DiamondAlg L C),
        v = towerRep L ω β C a (towerCyclicVec L ω β)} := by
  induction x using DirectSum.induction_on with
  | zero =>
    have h0 : towerCoe L ω β (0 : ⨁ C : Finset M, DiamondAlg L C) = 0 :=
      UniformSpace.Completion.coe_zero (α := TowerPre L ω β)
    rw [h0]
    exact Submodule.zero_mem _
  | of C v =>
    exact Submodule.subset_span ⟨C, v, (towerRep_cyclicVec_of L ω β C v).symm⟩
  | add x₁ x₂ h₁ h₂ =>
    rw [towerCoe_add_raw]
    exact Submodule.add_mem _ h₁ h₂

/-- **R8 CAPSTONE — Ω IS CYCLIC**: the linear span of the orbit `{π_C(a) Ω}` is DENSE in the
    tower Hilbert space — every coerced pre-vector is a finite sum of pure components, all in
    the span, and the coerced pre-space is dense in the completion. Cyclicity in the honest
    sense: density of the span, nothing more (Ω is NOT claimed separating). -/
theorem dense_span_towerRep_cyclicVec :
    Dense (↑(Submodule.span ℂ
      {v : TowerGNS L ω β | ∃ (C : Finset M) (a : DiamondAlg L C),
        v = towerRep L ω β C a (towerCyclicVec L ω β)}) : Set (TowerGNS L ω β)) := by
  refine Dense.mono ?_ UniformSpace.Completion.denseRange_coe
  rintro w ⟨x, rfl⟩
  exact towerCoe_mem_span_towerRep_cyclicVec L ω β x

end QIQTH.TowerGNS
