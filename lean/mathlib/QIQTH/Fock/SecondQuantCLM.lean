/-
  SecondQuantCLM — repackaging the free-field modular flow Γ(Δ^{it}) as a bounded
  OPERATOR on the Fock Hilbert space (continuation of the Stage-4 capstone).

  `secondQuantModFlowH` is a `Fock H → Fock H` function (`Completion.map`).  To
  replay `ContinuumLambda`'s `Ad(Δ^{it})` persistence machinery at the FIELD
  level we need it as a bounded operator `Fock H →L[ℂ] Fock H`.  This file bundles
  it, using the existing `clmLift` (the `ContinuousLinearMap.extend` of a bounded
  `FockPre` operator, from `WeylCLM.lean`):

    * `secondQuantModCLM S t : Fock H →L[ℂ] Fock H` — `Γ(Δ^{it})` as a continuous
      linear map; `secondQuantModCLM_apply` shows it agrees with the function
      `secondQuantModFlowH` on all of `Fock H`.
    * `secondQuantModCLM_zero` / `secondQuantModCLM_mul` — `Γ` is a one-parameter
      group of bounded operators: `Γ(Δ^{i·0}) = 1`, `Γ(Δ^{is})·Γ(Δ^{it}) = Γ(Δ^{i(s+t)})`.

  This is the operator-algebra packaging the field-level `Ad(Γ)` persistence
  needs; the adjoint relation `Γ(Δ^{it})⋆ = Γ(Δ^{-it})` (unitarity) and then the
  field-level persistence follow next.  Axiom-free.
-/

import QIQTH.Fock.WeylCLM
import QIQTH.ContinuumLambdaFock

namespace QIQTH.Fock

open QIQTH.StandardSubspaceModular
open UniformSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`Γ(Δ^{it})` as a bounded operator** on the Fock Hilbert space — the bundled
    lift of the one-particle modular flow's second quantization. -/
noncomputable def secondQuantModCLM (S : StandardSubspace H) (t : ℝ) :
    Fock H →L[ℂ] Fock H :=
  clmLift (secondQuantModFlowₗᵢ S t).toContinuousLinearMap

/-- The bounded operator `secondQuantModCLM` agrees with the function
    `secondQuantModFlowH` everywhere. -/
theorem secondQuantModCLM_apply (S : StandardSubspace H) (t : ℝ) (x : Fock H) :
    secondQuantModCLM S t x = secondQuantModFlowH S t x := by
  refine Completion.induction_on x
    (isClosed_eq (secondQuantModCLM S t).continuous
      (secondQuantModFlowH_isometry S t).continuous) (fun φ => ?_)
  rw [secondQuantModCLM, clmLift_coe, secondQuantModFlowH,
      Completion.map_coe (secondQuantModFlowₗᵢ S t).isometry.uniformContinuous]
  rfl

/-- **`Γ(Δ^{i·0}) = 1`.** -/
theorem secondQuantModCLM_zero (S : StandardSubspace H) :
    secondQuantModCLM S 0 = 1 := by
  ext x
  rw [secondQuantModCLM_apply, secondQuantModFlowH_zero, ContinuousLinearMap.one_apply]

/-- **The one-parameter group law for the bounded operators**
    `Γ(Δ^{is})·Γ(Δ^{it}) = Γ(Δ^{i(s+t)})`. -/
theorem secondQuantModCLM_mul (S : StandardSubspace H) (s t : ℝ) :
    secondQuantModCLM S s * secondQuantModCLM S t = secondQuantModCLM S (s + t) := by
  ext x
  rw [ContinuousLinearMap.mul_apply, secondQuantModCLM_apply, secondQuantModCLM_apply,
      secondQuantModCLM_apply, secondQuantModFlowH_add]

/- ── Operator unitarity: Γ(Δ^{it})⋆ = Γ(Δ^{-it}) ───────────────────────────-/

/-- `Γ(Δ^{it})` preserves the norm (it is the bundled lift of an isometric flow). -/
theorem secondQuantModCLM_norm (S : StandardSubspace H) (t : ℝ) (x : Fock H) :
    ‖secondQuantModCLM S t x‖ = ‖x‖ := by
  have h0 : secondQuantModFlowH S t 0 = 0 := by
    rw [← secondQuantModCLM_apply]; exact map_zero _
  have hd := (secondQuantModFlowH_isometry S t).dist_eq x 0
  rw [dist_eq_norm, dist_eq_norm, h0, sub_zero, sub_zero, ← secondQuantModCLM_apply] at hd
  exact hd

/-- `Γ(Δ^{it})` bundled as a `LinearIsometry` on the Fock Hilbert space — so it
    preserves the inner product. -/
noncomputable def secondQuantModLI (S : StandardSubspace H) (t : ℝ) :
    Fock H →ₗᵢ[ℂ] Fock H where
  toLinearMap := (secondQuantModCLM S t).toLinearMap
  norm_map' := secondQuantModCLM_norm S t

/-- **`Γ(Δ^{it})⋆ = Γ(Δ^{-it})`.**  The adjoint of the free-field modular flow is
    the inverse flow — derived from inner-product preservation and
    `Γ(Δ^{it})∘Γ(Δ^{-it}) = id`. -/
theorem secondQuantModCLM_adjoint (S : StandardSubspace H) (t : ℝ) :
    ContinuousLinearMap.adjoint (secondQuantModCLM S t) = secondQuantModCLM S (-t) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hLI : ∀ a, (secondQuantModLI S t) a = secondQuantModCLM S t a := fun _ => rfl
  have hinv : secondQuantModCLM S t (secondQuantModCLM S (-t) x) = x := by
    rw [secondQuantModCLM_apply, secondQuantModCLM_apply, secondQuantModFlowH_rightInv]
  have hpres := (secondQuantModLI S t).inner_map_map (secondQuantModCLM S (-t) x) y
  rw [hLI, hLI, hinv] at hpres
  exact hpres.symm

/-- **`Γ(Δ^{it})` is unitary** on the Fock Hilbert space — the genuine free-field
    modular unitary group. -/
theorem secondQuantModCLM_unitary (S : StandardSubspace H) (t : ℝ) :
    secondQuantModCLM S t ∈ unitary (Fock H →L[ℂ] Fock H) := by
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.star_eq_adjoint, secondQuantModCLM_adjoint,
        secondQuantModCLM_mul, neg_add_cancel, secondQuantModCLM_zero]
  · rw [ContinuousLinearMap.star_eq_adjoint, secondQuantModCLM_adjoint,
        secondQuantModCLM_mul, add_neg_cancel, secondQuantModCLM_zero]

/-- **Audit conclusion.**  `Γ(Δ^{it})` repackaged as a bounded operator on the
    Fock Hilbert space — a one-parameter group (`secondQuantModCLM_zero/_mul`),
    UNITARY (`secondQuantModCLM_adjoint`: `Γ⋆ = Γ(-t)`; `secondQuantModCLM_unitary`),
    agreeing with the function `secondQuantModFlowH`.  NO project axioms.  This is
    the genuine free-field modular unitary group; next, the field-level `Ad(Γ)`
    persistence replays the `ContinuumLambda` `modAutOp` machinery. -/
theorem secondQuantModCLM_audit : True := trivial

end QIQTH.Fock
