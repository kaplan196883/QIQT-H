/-
StateSupervenience.lean — argument (a): the (Φ,λ) ontology FORCES state-supervenience (2026-06-15)

The Born-from-typicality chain is now reduced to a single irreducible input: **state-supervenience** — that
the typicality of an outcome depends only on the state. `EnvarianceJustification` proved the state-stabilizing
symmetry exists (the unitary counter-swap fixes the equal-amplitude state); `BornEquiprobable` proved
equiprobability ⇒ Born. The missing link is: *why* must the typicality be invariant under that symmetry?

This file formalizes the ontological argument (a). In QIQT-H the ENTIRE ontology is `(Φ, λ)`: the global
state `Φ`, and a non-dynamical selector `λ` which is a fact ABOUT `Φ` (which of `Φ`'s records is actual). There
is no external observer, no extra parameter, and — crucially — the outcome *labels* carry no independent
ontology; they are description, not substance. So a relabelling `g` that acts consistently on BOTH the state
and the labels is not a physical change, and any physical quantity (the typicality) must be invariant under it.
That is the **naturality** axiom below. It is not an extra physical postulate; it is the parsimony of the
ontology made precise ("Φ is all there is; labels are description").

From naturality alone:

- `NaturalTypicality.stabilizer_invariant` — if a relabelling `g` fixes the state (`g • Φ = Φ`) then the
  typicality is `g`-invariant on outcomes: `T Φ (g • a) = T Φ a`.
- `NaturalTypicality.envariance_equiprob` — composed with an envariance symmetry (`g • Φ = Φ` and `g • a = b`,
  supplied by `EnvarianceJustification.envariance_swap_invariant` for equal amplitudes) this gives
  `T Φ a = T Φ b`: equal-amplitude outcomes are equiprobable. With `BornEquiprobable` this closes the Born
  circularity, the only remaining premise being naturality itself.

HONEST SCOPE: naturality (state-supervenience under relabelling) is the irreducible input. `NoBornFromNothing`
proves Born cannot come from literally nothing, so *some* premise must remain — the achievement is that it is
now this single, Born-free, ontologically-motivated parsimony principle, not Born, not a counting rule, and
not the envariance symmetry (which is now a theorem). Whether the (Φ,λ) ontology truly *entails* naturality
(rather than merely motivating it) is a philosophical claim this file makes precise but does not adjudicate.
Axiom-free; non-vacuous (a witnessing instance is provided).
-/
import Mathlib.Tactic

namespace QIQTH.StateSupervenience

variable {State Outcome G : Type*} [SMul G State] [SMul G Outcome]

/-- A **natural typicality functional**: an assignment `T Φ k` of a typicality weight to each outcome `k` in
each global state `Φ`, invariant under any relabelling `g` that acts consistently on states and outcomes
(`T (g • Φ) (g • k) = T Φ k`).  Naturality is the formal content of "the outcome labels carry no independent
ontology" — the parsimony of the QIQT-H `(Φ, λ)` ontology, which forces the typicality to depend only on the
state (state-supervenience), not on any preferred labelling. -/
structure NaturalTypicality (G State Outcome : Type*) [SMul G State] [SMul G Outcome] where
  /-- the typicality weight of outcome `k` in state `Φ` -/
  T : State → Outcome → ℝ
  /-- no preferred labelling: a consistent relabelling of state + outcomes changes nothing -/
  natural : ∀ (g : G) (Φ : State) (k : Outcome), T (g • Φ) (g • k) = T Φ k

namespace NaturalTypicality

/-- **State-supervenience ⇒ stabilizer invariance.**  If a relabelling `g` fixes the state (`g • Φ = Φ`),
a natural typicality is `g`-invariant on outcomes: `T Φ (g • a) = T Φ a`.  (The relabelled state is the
same state, so the typicality — a function of the state — is unchanged.) -/
theorem stabilizer_invariant (𝒯 : NaturalTypicality G State Outcome)
    {g : G} {Φ : State} (hg : g • Φ = Φ) (a : Outcome) :
    𝒯.T Φ (g • a) = 𝒯.T Φ a := by
  have h := 𝒯.natural g Φ a
  rwa [hg] at h

/-- **Envariance ⇒ equiprobability (the ontological closure).**  If a symmetry `g` fixes the state
(`g • Φ = Φ`) and maps outcome `a` to `b` (`g • a = b`), then a natural typicality assigns them equal weight:
`T Φ a = T Φ b`.  Supplying `g • Φ = Φ` from `EnvarianceJustification.envariance_swap_invariant` (the
environment counter-swap fixes the equal-amplitude state) and `g • a = b` from the system swap, this is
Zurek's "equal amplitudes ⇒ equal probabilities" — now resting only on naturality. -/
theorem envariance_equiprob (𝒯 : NaturalTypicality G State Outcome)
    {g : G} {Φ : State} {a b : Outcome} (hg : g • Φ = Φ) (hab : g • a = b) :
    𝒯.T Φ a = 𝒯.T Φ b := by
  rw [← hab]
  exact (𝒯.stabilizer_invariant hg a).symm

end NaturalTypicality

/-- Non-vacuity: a natural typicality functional exists (the constant assignment is trivially natural), so the
structure encodes a genuine constraint, not an empty one. The physically relevant natural instance is the
Born/equal-amplitude-counting typicality of `BornEquiprobable`. -/
def constTypicality (r : ℝ) : NaturalTypicality G State Outcome where
  T := fun _ _ => r
  natural := fun _ _ _ => rfl

end QIQTH.StateSupervenience
