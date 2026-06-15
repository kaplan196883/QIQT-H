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

/-- **Audit conclusion.**  `Γ(Δ^{it})` repackaged as a bounded operator on the
    Fock Hilbert space, a one-parameter group (`secondQuantModCLM_zero/_mul`),
    agreeing with the function `secondQuantModFlowH`.  NO project axioms.  Next:
    the adjoint relation `Γ(Δ^{it})⋆ = Γ(Δ^{-it})` (unitarity) and the field-level
    `Ad(Γ)` persistence. -/
theorem secondQuantModCLM_audit : True := trivial

end QIQTH.Fock
