/-
  QIQT-H Theorem 7 — No-signaling from AQFT microcausality + locality.
  Mathlib-rooted variant.
  -------------------------------------------------------------------
  The standalone Theorem7.lean already needs no real-arithmetic
  infrastructure — it is a pure algebraic-equality argument over an
  abstract observable algebra.  The Mathlib variant therefore looks
  very similar.  The benefit of Mathlib here is having
  `Subalgebra`/`StarSubalgebra` available for the *next* step:
  closing the microcausality ⇒ locality gap (currently a comment
  block in the standalone variant).

  This file keeps the same abstract setup as the standalone variant
  but uses Mathlib equality lemmas where applicable.  Discharging
  the microcausality ⇒ locality gap is left as TODO — it requires
  formalising von-Neumann–algebra commutants, which Mathlib does
  not yet have (only general `Subalgebra.commutant` exists).
-/

import Mathlib.Algebra.Algebra.Basic

namespace QIQTH
namespace Theorem7

/-- Abstract setup for the QIQT-H no-signaling theorem.
    Identical to the standalone variant; see comments there. -/
structure Setup where
  Obs : Type
  Val : Type
  ω : Obs → Val
  AliceSetting : Type
  AliceOutcome : Type
  BobSetting : Type
  E : AliceSetting → AliceOutcome → Obs
  Ψ : BobSetting → Obs → Obs
  inA : Obs → Prop
  alice_effect_inA : ∀ (x : AliceSetting) (a : AliceOutcome), inA (E x a)
  locality : ∀ (y : BobSetting) (X : Obs), inA X → Ψ y X = X

namespace Setup
variable (S : Setup)

/-- The QIQT-H joint-experiment prediction. -/
def P (x : S.AliceSetting) (a : S.AliceOutcome) (y : S.BobSetting) : S.Val :=
  S.ω (S.Ψ y (S.E x a))

/-- The "Alice alone" prediction. -/
def PAlice (x : S.AliceSetting) (a : S.AliceOutcome) : S.Val :=
  S.ω (S.E x a)

/-- **QIQT-H Theorem 7 (no-signaling).** -/
theorem no_signaling
    (x : S.AliceSetting) (a : S.AliceOutcome) (y : S.BobSetting) :
    S.P x a y = S.PAlice x a := by
  show S.ω (S.Ψ y (S.E x a)) = S.ω (S.E x a)
  rw [S.locality y (S.E x a) (S.alice_effect_inA x a)]

/-- Two Bob-settings yield identical Alice-marginals. -/
theorem alice_marginal_independent_of_bob
    (x : S.AliceSetting) (a : S.AliceOutcome) (y₁ y₂ : S.BobSetting) :
    S.P x a y₁ = S.P x a y₂ := by
  rw [S.no_signaling x a y₁, S.no_signaling x a y₂]

end Setup

end Theorem7
end QIQTH
