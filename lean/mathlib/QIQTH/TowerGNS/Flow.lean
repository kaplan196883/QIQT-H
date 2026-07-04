/-
  B3 + B4 (THE_TRANSPORT_AND_ACCOUNTING_PLAN.md) — THE TRANSPORTED FLOW ON THE TOWER
  HILBERT SPACE: a one-parameter unitary group, fixing the cyclic vector, displaying the
  finite-stage KMS boundary identity.

  `towerFlow t := (flowPre t).completion` — the per-corner Gibbs modular flows, glued by the
  tower and extended to the completion, form a ONE-PARAMETER UNITARY GROUP on `TowerGNS`:
  `towerFlow_zero` (U_0 = 1), `towerFlow_comp` (U_t U_s = U_{t+s}), `towerFlow_inner`
  (⟪U_t ξ, U_t η⟫ = ⟪ξ, η⟫), `towerFlow_adjoint` (U_t† = U_{−t}), and the capstone
  `towerFlow_mem_unitary`.

  HONEST SCOPE (binding): the flow is defined by TRANSPORT of the finite-stage flows — it is
  NOT constructed from a Tomita operator of the limit state. No Δ, no J, no S, no separating
  property, and no von Neumann type is claimed anywhere in this file.

  B4: the flow fixes the cyclic vector (`towerFlow_cyclicVec`: U_t Ω = Ω), so the vector
  state of Ω is invariant under conjugation by the flow (`towerFlow_vectorState`), and the
  FINITE-STAGE KMS boundary identity is displayed on the limit space
  (`towerState_kms_boundary`) — a restatement of the held finite `gibbs_kms_condition`
  through the GNS dictionary `towerRep_inner_cyclicVec`, NOT strip analyticity and NOT a
  KMS property of a state of the limit algebra.

  LEAN ARCHITECTURE (the R3 lesson, binding): the working lemmas (`flowRaw_zero`,
  `flowRaw_comp`, `rawInner_flowRaw_neg`) live at the RAW `⨁` type; completion-level proofs
  use the GNS-file incantations verbatim (`UniformSpace.Completion.induction_on` with
  `isClosed_eq <;> fun_prop`); the synonym is crossed only in application position.
-/
import Mathlib
import QIQTH.TowerGNS.FlowPre
import QIQTH.TowerGNS.CyclicVector

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The raw group laws (everything at `⨁` — the R3 lesson) -/

/-- The raw flow at time `0` is the identity (componentwise `cornerFlow_zero`). -/
theorem flowRaw_zero (x : ⨁ C : Finset M, DiamondAlg L C) :
    flowRaw L ω β 0 x = x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero (flowRaw L ω β 0)]
  | of C a => rw [flowRaw_of, cornerFlow_zero]
  | add x₁ x₂ h₁ h₂ => rw [map_add (flowRaw L ω β 0), h₁, h₂]

/-- The raw flow is a real one-parameter group (componentwise `cornerFlow_comp`). -/
theorem flowRaw_comp (t s : ℝ) (x : ⨁ C : Finset M, DiamondAlg L C) :
    flowRaw L ω β t (flowRaw L ω β s x) = flowRaw L ω β (t + s) x := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero (flowRaw L ω β s), map_zero (flowRaw L ω β t),
      map_zero (flowRaw L ω β (t + s))]
  | of C a => rw [flowRaw_of, flowRaw_of, flowRaw_of, cornerFlow_comp]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (flowRaw L ω β s), map_add (flowRaw L ω β t), h₁, h₂,
      map_add (flowRaw L ω β (t + s))]

/-- **The raw adjoint relation for the flow**: `⟪U_{−t} x, y⟫ = ⟪x, U_t y⟫` — insert
    `U_t` on both slots by the raw isometry, then collapse `U_t ∘ U_{−t} = U_0 = id`. -/
theorem rawInner_flowRaw_neg (t : ℝ) (x y : ⨁ C : Finset M, DiamondAlg L C) :
    rawInner L ω β (flowRaw L ω β (-t) x) y
      = rawInner L ω β x (flowRaw L ω β t y) := by
  calc rawInner L ω β (flowRaw L ω β (-t) x) y
      = rawInner L ω β (flowRaw L ω β t (flowRaw L ω β (-t) x)) (flowRaw L ω β t y) :=
        (rawInner_flowRaw L ω β t (flowRaw L ω β (-t) x) y).symm
    _ = rawInner L ω β x (flowRaw L ω β t y) := by
        rw [flowRaw_comp, add_neg_cancel, flowRaw_zero]

/-! ### B3 — the transported flow on the completion -/

/-- **THE TRANSPORTED FLOW** — the per-corner Gibbs modular flows, glued by the tower and
    extended to the completion by `ContinuousLinearMap.completion`. Defined by TRANSPORT,
    not constructed from a Tomita operator of the limit state — no Δ, J, S, separating
    property, or type is claimed. -/
noncomputable def towerFlow (t : ℝ) : TowerGNS L ω β →L[ℂ] TowerGNS L ω β :=
  (flowPre L ω β t).completion

@[simp] theorem towerFlow_coe (t : ℝ) (x : TowerPre L ω β) :
    towerFlow L ω β t (x : TowerGNS L ω β)
      = ((flowPre L ω β t x : TowerPre L ω β) : TowerGNS L ω β) :=
  (flowPre L ω β t).completion_apply_coe x

/-- `U_0 = 1` (completion induction + the raw identity law). -/
theorem towerFlow_zero : towerFlow L ω β 0 = 1 := by
  ext c
  induction c using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [ContinuousLinearMap.one_apply, towerFlow_coe]
    have h : flowPre L ω β 0 x = x := flowRaw_zero L ω β x
    rw [h]

/-- **The one-parameter group law**: `U_t ∘ U_s = U_{t+s}` (completion induction + the raw
    group law, which holds at the SAME stage — no germ gluing needed). -/
theorem towerFlow_comp (t s : ℝ) :
    towerFlow L ω β t ∘L towerFlow L ω β s = towerFlow L ω β (t + s) := by
  ext c
  induction c using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [ContinuousLinearMap.comp_apply, towerFlow_coe, towerFlow_coe, towerFlow_coe]
    have h : flowPre L ω β t (flowPre L ω β s x) = flowPre L ω β (t + s) x :=
      flowRaw_comp L ω β t s x
    rw [h]

/-- **The flow preserves the inner product**: `⟪U_t ξ, U_t η⟫ = ⟪ξ, η⟫` (double completion
    induction + the raw isometry `rawInner_flowRaw`). -/
theorem towerFlow_inner (t : ℝ) (ξ η : TowerGNS L ω β) :
    ⟪towerFlow L ω β t ξ, towerFlow L ω β t η⟫_ℂ = ⟪ξ, η⟫_ℂ := by
  induction ξ, η using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [towerFlow_coe, towerFlow_coe, UniformSpace.Completion.inner_coe,
      UniformSpace.Completion.inner_coe, towerInner_def, towerInner_def]
    exact rawInner_flowRaw L ω β t x y

/-- **The adjoint of the flow is the reversed flow**: `U_t† = U_{−t}` (`eq_adjoint_iff` +
    double completion induction + the raw adjoint relation). -/
theorem towerFlow_adjoint (t : ℝ) :
    ContinuousLinearMap.adjoint (towerFlow L ω β t) = towerFlow L ω β (-t) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (towerFlow L ω β (-t))
    (towerFlow L ω β t)).mpr fun ξ η => ?_).symm
  induction ξ, η using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [towerFlow_coe, towerFlow_coe, UniformSpace.Completion.inner_coe,
      UniformSpace.Completion.inner_coe, towerInner_def, towerInner_def]
    exact rawInner_flowRaw_neg L ω β t x y

/-- **B3 CAPSTONE — the transported flow is a one-parameter UNITARY group**: `U_t` is a
    unitary element of the bounded operators at every `t` — `U_t† U_t = U_{−t+t} = U_0 = 1`
    and `U_t U_t† = U_{t+(−t)} = U_0 = 1`. (Transport, not Tomita: no Δ, J, S, or
    separating property is claimed.) -/
theorem towerFlow_mem_unitary (t : ℝ) :
    towerFlow L ω β t ∈ unitary (TowerGNS L ω β →L[ℂ] TowerGNS L ω β) := by
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint, towerFlow_adjoint]
  refine ⟨?_, ?_⟩
  · show towerFlow L ω β (-t) ∘L towerFlow L ω β t = 1
    rw [towerFlow_comp, neg_add_cancel, towerFlow_zero]
  · show towerFlow L ω β t ∘L towerFlow L ω β (-t) = 1
    rw [towerFlow_comp, add_neg_cancel, towerFlow_zero]

/-! ### B4 — the flow and the cyclic vector: invariance + the finite-stage KMS boundary
identity displayed on the limit space -/

/-- **The flow fixes the cyclic vector**: `U_t Ω = Ω` — Ω is the unit of the trivial corner
    and the per-corner flow is unital (`cornerFlow_one`). -/
theorem towerFlow_cyclicVec (t : ℝ) :
    towerFlow L ω β t (towerCyclicVec L ω β) = towerCyclicVec L ω β := by
  rw [towerCyclicVec, towerFlow_coe]
  have h1 : flowPre L ω β t (towerOf L ω β ∅ 1) = towerOf L ω β ∅ 1 := by
    show flowRaw L ω β t (DirectSum.of (fun C : Finset M => DiamondAlg L C) ∅ 1)
        = DirectSum.of (fun C : Finset M => DiamondAlg L C) ∅ 1
    rw [flowRaw_of, cornerFlow_one]
  rw [h1]

/-- **The vector state of Ω is invariant under conjugation by the flow**:
    `⟪Ω, U_t T U_{−t} Ω⟫ = ⟪Ω, T Ω⟫` for EVERY bounded operator `T` — `U_{−t} Ω = Ω`
    kills the inner factor and the outer `U_t` moves across the inner product as
    `U_t† = U_{−t}`, which fixes Ω again. -/
theorem towerFlow_vectorState (t : ℝ) (T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) :
    ⟪towerCyclicVec L ω β,
        (towerFlow L ω β t ∘L T ∘L towerFlow L ω β (-t)) (towerCyclicVec L ω β)⟫_ℂ
      = ⟪towerCyclicVec L ω β, T (towerCyclicVec L ω β)⟫_ℂ := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, towerFlow_cyclicVec,
    ← ContinuousLinearMap.adjoint_inner_left, towerFlow_adjoint, towerFlow_cyclicVec]

/-- **B4 CAPSTONE — the FINITE-STAGE boundary KMS identity, displayed on the limit space**:
    `⟪Ω, π_C(x·y) Ω⟫ = ⟪Ω, π_C(y·σ(x)) Ω⟫` at every finite stage `C` — the held finite
    `gibbs_kms_condition` restated through the GNS dictionary `towerRep_inner_cyclicVec`.

    HONEST SCOPE (binding): this is the FINITE-STAGE boundary identity displayed on the
    limit space — NOT strip analyticity, and NOT a KMS property of a state of the limit
    algebra. `σ = modAut (gibbsDensity)` is the finite imaginary-time modular shift of the
    stage-`C` Gibbs density; no limit-state modular object is constructed or claimed. -/
theorem towerState_kms_boundary (C : Finset M) (x y : DiamondAlg L C) :
    ⟪towerCyclicVec L ω β, towerRep L ω β C (x * y) (towerCyclicVec L ω β)⟫_ℂ
      = ⟪towerCyclicVec L ω β,
          towerRep L ω β C (y * modAut (gibbsDensity L C ω β) x)
            (towerCyclicVec L ω β)⟫_ℂ := by
  rw [towerRep_inner_cyclicVec, towerRep_inner_cyclicVec]
  exact gibbs_kms_condition L C ω β x y

end QIQTH.TowerGNS
