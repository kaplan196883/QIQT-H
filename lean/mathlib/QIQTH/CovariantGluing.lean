/-
CovariantGluing.lean — OP3b: a covariant MEASURE exists, a covariant SELECTOR cannot (2026-06-15)

The λ-gluing question (Open Problem 3b): can the per-region actual records be stitched into ONE
Lorentz-covariant actual history λ? The resolution established this session (paper_strategy/56, and pro):
**a covariant measure ≠ a covariant selector.** SO(3) has an invariant probability measure on S² but no
invariant point; likewise the LAW governing λ is Poincaré-covariant while a sampled λ generically breaks the
symmetry. So λ must be a symmetry-breaking *sample* of a covariant law, NOT an equivariant function Φ ↦ λ.

The POSITIVE half — the covariant σ-additive Born measure exists — is already machine-checked for the 1+1D
free field (`Fock.weylBit_typicality_lorentzBoost_invariant`: the typicality measure is the same in every
Lorentz frame). This file supplies the MISSING half: the **no-go** that a covariant *selector* cannot exist
when the symmetric state's actual histories are not themselves symmetric. Together they make the "measure not
selector" dichotomy rigorous — which is exactly the OP3b conceptual content.

- `selector_image_fixed` — an equivariant selector sends a symmetry-fixed state to a symmetry-fixed history.
- `no_covariant_selector` — hence if a symmetry fixes the state but fixes NO history (the actual histories
  form a nontrivial orbit), there is NO covariant selector: the gluing cannot be an equivariant function.
- `bool_swap_no_selector` — the finite S²-analog witness (Bool histories swapped by the symmetry): no
  covariant selector, while the uniform measure on the two histories is trivially invariant.

So OP3b's honest status: the covariant LAW glues (the measure is covariant, machine-checked); the covariant
POINT does not (no equivariant selector, machine-checked here). λ is a contingent, symmetry-breaking sample —
not a covariant function — and that is forced, not a defect. Axiom-free.
-/
import Mathlib.Tactic

namespace QIQTH.CovariantGluing

variable {State History : Type*}

/-- An equivariant **covariant selector** sends a symmetry-fixed state to a symmetry-fixed history: if the
symmetry `(actS, actH)` fixes the state `Φ` (`actS Φ = Φ`) and `σ` is equivariant
(`σ (actS Φ) = actH (σ Φ)`), then `σ Φ` is fixed by `actH`. (The realized history inherits every symmetry of
the state it is selected from.) -/
theorem selector_image_fixed (actS : State → State) (actH : History → History)
    (σ : State → History) (equiv : ∀ Φ, σ (actS Φ) = actH (σ Φ))
    {Φ : State} (hΦ : actS Φ = Φ) : actH (σ Φ) = σ Φ := by
  have h := equiv Φ
  rw [hΦ] at h
  exact h.symm

/-- **The no-go: no covariant selector.** If a symmetry `(actS, actH)` fixes the state `Φ` but fixes **no**
history (every history is moved, `actH h ≠ h`), then there is no equivariant selector `σ` — assuming one
yields a contradiction. So λ cannot be a Poincaré-equivariant function of `Φ`: when the symmetric global
state has only symmetry-breaking actual histories, the gluing is necessarily a contingent SAMPLE of the
covariant law, not a covariant point. -/
theorem no_covariant_selector (actS : State → State) (actH : History → History)
    (σ : State → History) (equiv : ∀ Φ, σ (actS Φ) = actH (σ Φ))
    {Φ : State} (hΦ : actS Φ = Φ) (hno : ∀ h : History, actH h ≠ h) : False :=
  hno (σ Φ) (selector_image_fixed actS actH σ equiv hΦ)

/-- **Finite S²-analog (non-vacuity).** Take the symmetry to swap two actual histories (`History = Bool`,
`actH = not`) while fixing the unique symmetric state (`State = Unit`, `actS = id`). The swap fixes no
history (`not b ≠ b`), so no covariant selector exists. Yet a covariant *measure* trivially does — the
uniform weight `1/2` is `not`-invariant (`uniform_invariant`). This is the exact dichotomy: invariant
measure, no invariant point. -/
theorem bool_swap_no_selector (σ : Unit → Bool) (equiv : ∀ u, σ u = Bool.not (σ u)) : False :=
  no_covariant_selector id Bool.not σ (fun u => equiv u) (Φ := ()) rfl (by decide)

/-- The covariant **measure** half (trivial, by contrast with the no-go): the uniform probability weight on
the (swapped) histories is invariant under the symmetry. Covariant measures are easy; covariant selectors are
obstructed — that asymmetry is the content of OP3b. -/
theorem uniform_invariant (b : Bool) :
    (fun _ : Bool => (1 : ℝ) / 2) (Bool.not b) = (fun _ : Bool => (1 : ℝ) / 2) b := rfl

end QIQTH.CovariantGluing
