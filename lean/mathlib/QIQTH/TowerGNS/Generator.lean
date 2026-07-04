/-
  G1 + G2 (THE_GENERATOR_PLAN.md) — THE SELF-ADJOINT STONE GENERATOR OF THE TRANSPORTED
  TOWER FLOW, AND THE CYCLIC VECTOR AS A ZERO-MODE.

  `towerGen := stoneGen (towerFlow)` — the general Stone-generator theorem
  (`QIQTH/Spectral/Stone.lean`, `QIQTH/Spectral/Garding.lean`) instantiated with the five
  held Track-B facts about the transported flow: the group law (`towerFlow_comp`, oriented
  here as the NAMED adapter `towerFlow_compL`), `U_0 = 1` (`towerFlow_zero`), unitarity
  (`towerFlow_inner`), the isometry bound (`towerFlow_norm_eq`), and strong continuity
  (`continuous_towerFlow_apply`). The result: `towerGen` is a genuine SELF-ADJOINT unbounded
  operator (`LinearPMap`, `K = K†` in Mathlib's adjoint sense) — `towerGen_isSelfAdjoint`.

  G2: the cyclic vector is a ZERO-MODE — the flow fixes Ω exactly (`towerFlow_cyclicVec`),
  so its orbit is constant, hence Ω lies in the smooth domain
  (`towerCyclicVec_mem_stoneDomain`) and `towerGen Ω = 0` (`towerGen_cyclicVec`), pinned by
  `stoneGen_eq_of_hasDerivAt`.

  HONEST SCOPE (binding): `towerGen` is the Stone generator of the TRANSPORTED flow — not
  constructed from the limit state's Tomita operator; NOT claimed to be a modular
  Hamiltonian in the Tomita sense. No Δ, J, S, separating property, KMS-at-the-limit, von
  Neumann type, spectral resolution (PVM) of the unbounded `towerGen`, or exponential
  recovery `U_t = exp(it·towerGen)` is claimed anywhere in this file.
-/
import Mathlib
import QIQTH.TowerGNS.FlowContinuity
import QIQTH.Spectral.Stone
import QIQTH.Spectral.Garding

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open QIQTH.Spectral
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### G1 — the named orientation adapter, the generator, self-adjointness -/

/-- **The group law in `∘L` form**: `U_{s+t} = U_s ∘L U_t` — the Stone `hgrp` hypothesis.
    The NAMED orientation adapter (never inlined): the held `towerFlow_comp` is stated as
    `U_t ∘L U_s = U_{t+s}`, so the Stone shape is its `symm` at the right instantiation. -/
theorem towerFlow_compL (s t : ℝ) :
    towerFlow L ω β (s + t) = towerFlow L ω β s ∘L towerFlow L ω β t :=
  (towerFlow_comp L ω β s t).symm

/-- **★ THE TOWER GENERATOR** — the Stone generator of the TRANSPORTED flow — not
    constructed from the limit state's Tomita operator; NOT claimed to be a modular
    Hamiltonian in the Tomita sense. -/
noncomputable def towerGen : (TowerGNS L ω β) →ₗ.[ℂ] (TowerGNS L ω β) :=
  QIQTH.Spectral.stoneGen (towerFlow L ω β)

/-- **★★★ The tower generator is SELF-ADJOINT**: `IsSelfAdjoint (towerGen L ω β)` — the
    general `stoneGen_isSelfAdjoint` instantiated with the five held Track-B facts (group
    law via the named adapter `towerFlow_compL`, `U_0 = 1`, unitarity, the isometry bound,
    strong continuity). So `towerGen` is a genuine self-adjoint unbounded operator
    (`K = K†` in Mathlib's `LinearPMap` adjoint sense) — obtained by TRANSPORT; no Tomita
    object of the limit state is used or claimed. -/
theorem towerGen_isSelfAdjoint : IsSelfAdjoint (towerGen L ω β) :=
  stoneGen_isSelfAdjoint (towerFlow L ω β) (towerFlow_compL L ω β) (towerFlow_zero L ω β)
    (fun t a b => towerFlow_inner L ω β t a b)
    (fun t y => le_of_eq (towerFlow_norm_eq L ω β t y))
    (fun y => continuous_towerFlow_apply L ω β y)

/-! ### G2 — the cyclic vector is a zero-mode -/

/-- **The cyclic vector lies in the smooth domain**: the flow fixes Ω exactly
    (`towerFlow_cyclicVec`), so the orbit `t ↦ U_t Ω` is the CONSTANT function, hence
    differentiable at `0`. -/
theorem towerCyclicVec_mem_stoneDomain :
    towerCyclicVec L ω β ∈ QIQTH.Spectral.stoneDomain (towerFlow L ω β) := by
  show DifferentiableAt ℝ (fun t : ℝ => towerFlow L ω β t (towerCyclicVec L ω β)) 0
  have h : (fun t : ℝ => towerFlow L ω β t (towerCyclicVec L ω β))
      = fun _ => towerCyclicVec L ω β :=
    funext fun t => towerFlow_cyclicVec L ω β t
  rw [h]
  exact differentiableAt_const _

/-- **★ THE ZERO-MODE**: `towerGen Ω = 0` — the orbit of the cyclic vector is constant, so
    its derivative at `0` is `0 = I • 0`, and `stoneGen_eq_of_hasDerivAt` pins the
    generator's value. (Transport, not Tomita: no Δ, J, S, or separating property is
    claimed.) -/
theorem towerGen_cyclicVec :
    towerGen L ω β ⟨towerCyclicVec L ω β, towerCyclicVec_mem_stoneDomain L ω β⟩ = 0 := by
  refine stoneGen_eq_of_hasDerivAt (towerFlow L ω β) (towerCyclicVec L ω β) 0
    (towerCyclicVec_mem_stoneDomain L ω β) ?_
  have h : (fun t : ℝ => towerFlow L ω β t (towerCyclicVec L ω β))
      = fun _ => towerCyclicVec L ω β :=
    funext fun t => towerFlow_cyclicVec L ω β t
  rw [h, smul_zero]
  exact hasDerivAt_const 0 _

end QIQTH.TowerGNS
