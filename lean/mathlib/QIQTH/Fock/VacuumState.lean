/-
  F3 (part) — the quasifree vacuum state on the bosonic Fock space.

  The vacuum vector `Ω` of the Fock space (`FockSpace.lean`, F2) defines the **vacuum state**
  `ω₀(T) = Re⟪Ω, T Ω⟫` — a positive, normalized, additive `ℝ`-functional on `B(Fock H)`.  This is
  exactly the `ω : A →+ ℝ` that `StateNetMeasure.EffectStateNet` consumes, now for the genuine
  continuum free field (the Fock space over the one-particle space `H`).  It is the state that feeds
  the F6 covariant typicality measure (`FOCK_CCR_FOUNDATION_PLAN.md`).

  This is the vacuum *vector* state; its characterization as the **quasifree** state
  `ω₀(W f) = exp(−‖f‖²/2)` on the Weyl operators `W f` is the remaining F3 field content (the Weyl/CCR
  algebra).  Axiom-free.
-/
import QIQTH.Fock.FockSpace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Tactic

namespace QIQTH.Fock

open scoped ComplexInnerProductSpace InnerProductSpace
open Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The **vacuum state** on `B(Fock H)`: `ω₀(T) = Re⟪Ω, T Ω⟫`. -/
noncomputable def vacuumState (T : Fock H →L[ℂ] Fock H) : ℝ :=
  RCLike.re (inner ℂ (Fock.vacuum : Fock H) (T Fock.vacuum))

@[simp] theorem vacuumState_zero : vacuumState (0 : Fock H →L[ℂ] Fock H) = 0 := by
  simp [vacuumState]

/-- The vacuum state is additive. -/
theorem vacuumState_add (x y : Fock H →L[ℂ] Fock H) :
    vacuumState (x + y) = vacuumState x + vacuumState y := by
  simp only [vacuumState, ContinuousLinearMap.add_apply, inner_add_right, map_add]

/-- The vacuum state bundled as an additive `ℝ`-functional on `B(Fock H)` — the `ω : A →+ ℝ` that
    `EffectStateNet` consumes. -/
noncomputable def vacuumStateHom : (Fock H →L[ℂ] Fock H) →+ ℝ where
  toFun := vacuumState
  map_zero' := vacuumState_zero
  map_add' := vacuumState_add

/-- **Positivity**: the vacuum state is nonnegative on positive operators. -/
theorem vacuumState_nonneg (T : Fock H →L[ℂ] Fock H) (hT : T.IsPositive) :
    0 ≤ vacuumState T :=
  hT.re_inner_nonneg_right Fock.vacuum

/-- **Normalization**: `ω₀(1) = ⟪Ω,Ω⟫ = 1` (the vacuum is a unit vector). -/
theorem vacuumState_one : vacuumState (1 : Fock H →L[ℂ] Fock H) = 1 := by
  unfold vacuumState
  rw [ContinuousLinearMap.one_apply, Fock.inner_vacuum]
  simp

/-- **The vacuum state is a STATE**: positive (above), additive, and `ω₀(1) = 1`. -/
theorem vacuumStateHom_one : (vacuumStateHom : (Fock H →L[ℂ] Fock H) →+ ℝ) 1 = 1 :=
  vacuumState_one

end QIQTH.Fock
