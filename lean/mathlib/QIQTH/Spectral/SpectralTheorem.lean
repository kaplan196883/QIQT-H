/-
  Phase 1.3 of the Tomita–Takesaki roadmap (TOMITA_TAKESAKI_ROADMAP.md):
  the BOUNDED SPECTRAL THEOREM — constructing a projection-valued measure from a
  bounded self-adjoint operator `T : H →L[ℂ] H` (`PVM_of_selfAdjoint`).

  Now reachable on Mathlib v4.30 (both earlier-feared blockers are absent):
    • `cfc` works on `T` — `CStarAlgebra (H →L[ℂ] H)` is a registered instance
      (`Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap.lean`);
    • the Riesz–Markov REPRESENTATION theorem exists
      (`MeasureTheory.RealRMK.integral_rieszMeasure`);
    • multiplicativity of the bounded-Borel FC is proved (`Spectral/PVM.lean`,
      `boundedFC_mul`), giving the PVM laws.

  Construction (in progress): scalar measure `μ_x := rieszMeasure (f ↦ ⟪x, cfc f x⟫)`
  → polarize → `E(B)` via the Riesz form → `ProjectionValuedMeasure` laws → `∫ id dE = T`.

  This file begins with a validation that `cfc` fires on a self-adjoint `B(H)` operator.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic

namespace QIQTH.SpectralTheorem

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Validation:** the continuous functional calculus fires on a bounded self-adjoint
    operator on a complex Hilbert space — `cfc id T = T`.  (Confirms the `cfc` instance
    resolves via `CStarAlgebra (H →L[ℂ] H)`, the entry point for the spectral theorem.) -/
example (T : H →L[ℂ] H) (_hT : IsSelfAdjoint T) : cfc (id : ℝ → ℝ) T = T := cfc_id ℝ T

end QIQTH.SpectralTheorem
