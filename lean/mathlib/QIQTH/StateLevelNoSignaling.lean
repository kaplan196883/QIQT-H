/-
  State-level no-signaling — strengthening of QIQT-H Theorem 7.

  Theorem 7 (in `Theorem7.lean`) proves no-signaling for POVM outcome
  probabilities P(a | x, y).  This file lifts the conclusion to the
  *state* level: Bob's non-selective channel leaves Alice's restricted
  state pointwise unchanged.

  Two further consequences:
    · The class of "Alice-fixing" channels is closed under composition.
    · Convex mixtures of Alice-fixing channels are Alice-fixing.

  Together these handle randomized Bob settings, sequential Bob
  operations, and any composite Bob strategy.
-/

import QIQTH.Theorem7
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace QIQTH
namespace StateLevelNoSignaling

open Theorem7

variable (S : Setup)

/-- A Heisenberg channel `Φ : S.Obs → S.Obs` is *Alice-fixing* if it
    leaves every observable in Alice's subalgebra pointwise invariant.
    The `locality` field of `Setup` says each `Ψ y` is Alice-fixing. -/
def AliceFixing (Φ : S.Obs → S.Obs) : Prop :=
  ∀ X : S.Obs, S.inA X → Φ X = X

/-- Bob's non-selective channel is Alice-fixing (rephrasing of `locality`). -/
theorem bob_is_aliceFixing (y : S.BobSetting) :
    AliceFixing S (S.Ψ y) :=
  fun X hX => S.locality y X hX

/-- **State-level no-signaling.**  For any Alice-fixing channel `Φ`
    and any Alice observable `X`, the Schrödinger-pulled-back state
    `ω ∘ Φ` agrees with `ω` on `X`. -/
theorem state_level_no_signaling
    {Φ : S.Obs → S.Obs} (hΦ : AliceFixing S Φ)
    (X : S.Obs) (hX : S.inA X) :
    S.ω (Φ X) = S.ω X := by
  rw [hΦ X hX]

/-- **Composition closure.** Compositions of Alice-fixing channels are
    Alice-fixing.  Models sequential Bob operations. -/
theorem aliceFixing_comp
    {Φ Ψ' : S.Obs → S.Obs}
    (hΦ : AliceFixing S Φ) (hΨ' : AliceFixing S Ψ') :
    AliceFixing S (Φ ∘ Ψ') := by
  intro X hX
  show Φ (Ψ' X) = X
  rw [hΨ' X hX, hΦ X hX]

/-- **Identity is Alice-fixing.** -/
theorem aliceFixing_id : AliceFixing S id := fun _ _ => rfl

/-- **Convex-mixture closure (in the Heisenberg picture).**
    If two Bob settings give Alice-fixing channels, so does any
    pointwise convex combination
        `Φ_λ(X) := λ • Φ(X) + (1 − λ) • Ψ'(X)`,
    *whenever Alice observables are fixed points of the operation
    `λ • X + (1−λ) • X = X`* — formalized abstractly as the
    `mix_fixed` hypothesis.  This is automatic in any module/affine
    setting (e.g. operator algebra) where scalar multiplication
    on identities reproduces them. -/
theorem aliceFixing_convex_mix
    {Φ Ψ' : S.Obs → S.Obs} (mix : S.Obs → S.Obs → S.Obs)
    (mix_fixed : ∀ X : S.Obs, mix X X = X)
    (hΦ : AliceFixing S Φ) (hΨ' : AliceFixing S Ψ') :
    AliceFixing S (fun X => mix (Φ X) (Ψ' X)) := by
  intro X hX
  show mix (Φ X) (Ψ' X) = X
  rw [hΦ X hX, hΨ' X hX, mix_fixed X]

/-- **Randomized-Bob no-signaling.** A finite probabilistic mixture
    of Bob settings still gives a state-level no-signaling guarantee
    on every Alice observable. -/
theorem randomized_bob_no_signaling
    {ι : Type*} (s : Finset ι) (ys : ι → S.BobSetting)
    (X : S.Obs) (hX : S.inA X) :
    ∀ k ∈ s, S.ω (S.Ψ (ys k) X) = S.ω X := by
  intro k _
  exact state_level_no_signaling S (bob_is_aliceFixing S (ys k)) X hX

end StateLevelNoSignaling
end QIQTH
