/-
WeylBitBell.lean — OP3b concrete Bell embedding: no-signaling FROM the record measure (2026-06-15)

`ContextualitySafe` verified the OP3b Bell-marginal check at the level of the abstract CHSH / no-signaling
theorems. This file closes the remaining gap: it derives the no-signaling Bell marginal **from the actual
Weyl-bit record measure** (`weylBitNet`/`WeylBitMeasure`), not from a generic POVM.

Setup (the genuine free-field Bell configuration): Alice's mode `u` and Bob's mode `v`, spacelike separated
hence symplectically orthogonal (`Im⟪u,v⟫ = 0`). The joint Born weight of the record outcomes
`(σ_A,σ_B)` is `P(σ_A,σ_B | u,v) = ‖A(u,σ_A) A(v,σ_B) Ω‖²` — exactly the two-bit `bornWeight` of the record
net. No-signaling is the statement that summing out Bob's outcome leaves Alice's marginal independent of
Bob's mode/setting `v`:

  `∑_{σ_B} ‖A(u,σ_A) A(v,σ_B) Ω‖² = ‖A(u,σ_A) Ω‖²`   — independent of `v`.

Mechanism, entirely from the record measure: the spacelike bits commute (`bitOp_comm`, the field's
microcausality), so Bob's bit can be moved outermost and summed via `bit_normSq_sum` (the same normalization
identity that is the engine of the whole construction). Results:

- `bell_no_signaling_alice` — Alice's marginal `= ‖A(u,σ_A)Ω‖²`, with no `v`-dependence.
- `bell_no_signaling_setting_indep` — explicitly: two different Bob settings `v, v'` give the *same* Alice
  marginal (the operational no-signaling statement: Bob's choice cannot affect Alice's statistics).
- `bell_no_signaling_bob` — the symmetric statement for Bob.

So the record measure itself is no-signaling — the positive half of contextuality-safety, now derived
concretely (the no-global-value-map half is the abstract Bell, `ContextualitySafe`). Axiom-free.
HONEST SCOPE: this is the no-signaling content of the embedding; exhibiting record correlations that *attain*
a CHSH/Tsirelson violation within this commuting-bit free-field model (vs. the cited singlet `Tsirelson.lean`)
is the remaining piece.
-/
import QIQTH.Fock.WeylBitMeasure
import Mathlib.Tactic

namespace QIQTH.Fock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

open scoped InnerProductSpace

/-- **No-signaling from the record measure (Alice's marginal).** For spacelike modes (`Im⟪u,v⟫ = 0`),
summing Bob's record outcome out of the joint Born weight gives Alice's single-mode Born weight
`‖A(u,σ_A) Ω‖²` — manifestly independent of Bob's mode `v`. Derived purely from the field's microcausality
(`bitOp_comm`, the spacelike bits commute) plus the normalization identity `bit_normSq_sum`. -/
theorem bell_no_signaling_alice (u v : H) (h : Complex.im ⟪u, v⟫_ℂ = 0) (sA : ℂ) :
    ‖bitOp u sA (bitOp v 1 (vac H))‖ ^ 2 + ‖bitOp u sA (bitOp v (-1) (vac H))‖ ^ 2
      = ‖bitOp u sA (vac H)‖ ^ 2 := by
  rw [bitOp_comm u v sA 1 h (vac H), bitOp_comm u v sA (-1) h (vac H)]
  exact bit_normSq_sum v (bitOp u sA (vac H))

/-- **Operational no-signaling: Bob's setting cannot affect Alice's statistics.** Two different Bob modes
`v, v'` (each spacelike to Alice's `u`) yield the *same* Alice marginal — Bob's free choice of what to
measure leaves Alice's record distribution unchanged. This is the no-signaling Bell marginal of the genuine
free-field record measure. -/
theorem bell_no_signaling_setting_indep (u v v' : H)
    (hv : Complex.im ⟪u, v⟫_ℂ = 0) (hv' : Complex.im ⟪u, v'⟫_ℂ = 0) (sA : ℂ) :
    ‖bitOp u sA (bitOp v 1 (vac H))‖ ^ 2 + ‖bitOp u sA (bitOp v (-1) (vac H))‖ ^ 2
      = ‖bitOp u sA (bitOp v' 1 (vac H))‖ ^ 2 + ‖bitOp u sA (bitOp v' (-1) (vac H))‖ ^ 2 := by
  rw [bell_no_signaling_alice u v hv sA, bell_no_signaling_alice u v' hv' sA]

/-- **No-signaling, Bob's marginal (symmetric).** Summing Alice's record outcome gives Bob's single-mode
Born weight, independent of Alice's mode `u`. -/
theorem bell_no_signaling_bob (u v : H) (h : Complex.im ⟪v, u⟫_ℂ = 0) (sB : ℂ) :
    ‖bitOp v sB (bitOp u 1 (vac H))‖ ^ 2 + ‖bitOp v sB (bitOp u (-1) (vac H))‖ ^ 2
      = ‖bitOp v sB (vac H)‖ ^ 2 :=
  bell_no_signaling_alice v u h sB

end QIQTH.Fock
