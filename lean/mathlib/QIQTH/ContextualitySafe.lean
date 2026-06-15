/-
ContextualitySafe.lean — OP3b: the λ-measure is contextuality-safe (the Bell-marginal check) (2026-06-15)

The covariant-gluing programme must pass a mandatory sanity check (the roadmap's "CHSH/Fine" guardrail): the
glued record measure must NOT secretly provide a global value-map over incompatible measurement settings —
that would be a Fine/Bell global joint distribution, which for super-classical (Tsirelson) correlations does
not exist. A contextuality-*safe* construction assigns joint values only within a single ACTUAL context
(compatible, spacelike-commuting records), where a no-signaling joint always exists.

This file assembles the verified Bell / no-signaling machinery into that statement. An `LHVModel` (in `Bell`)
is exactly a **global value-map**: per hidden value λ it fixes ±1 outcomes for ALL FOUR CHSH settings
`(a₁,a₂,b₁,b₂)` at once — a noncontextual assignment over incompatible measurements, i.e. precisely the
"covariant global selector over all settings" λ must not be.

- `no_global_record_valuemap` — any global value-map has `|CHSH| ≤ 2`, so none reproduces a correlation
  `> 2` (the quantum/record Tsirelson value `2√2`). Repackages `not_lhv_if_chsh_gt_two`.
- `single_lambda_bounded` — even a single actuality value assigning all four settings is `CHSH ≤ 2` (local);
  so a λ fixing all counterfactual outcomes could not carry the quantum record correlation. Values must be
  assigned per ACTUAL context, not globally. (`chsh_pointwise`.)
- `contextuality_safe` — existence form: there is a quantum/record correlation `> 2` that no global value-map
  matches (`qiqth_violates_bell`). So λ-actual-context-only is *forced* (no global map can exist), while on
  each compatible context the bipartite record marginals are no-signaling
  (`NoSignalingGeneral.bipartite_no_signaling`, for arbitrary entangled ρ). The construction therefore dodges
  the Fine/Bell global-distribution obstruction exactly by being actual-context-only, and stays operationally
  no-signaling — passing the OP3b Bell-marginal check.

HONEST SCOPE: this verifies contextuality-safety at the level of the abstract CHSH / no-signaling theorems
(the guardrail). The concrete embedding of a full Bell experiment inside the Weyl-bit *record net* (deriving
these marginals from the λ-measure itself) is the remaining OP3b increment. Axiom-free.
-/
import QIQTH.Bell
import QIQTH.NoSignalingGeneral
import Mathlib.Tactic

namespace QIQTH.ContextualitySafe

open QIQTH.Bell

/-- **No global record value-map reproduces a super-classical correlation.** An `LHVModel` is a global
value-map — it fixes ±1 outcomes for all four (incompatible) CHSH settings at once. Every such map has
`|CHSH| ≤ 2`, so none can reproduce a `predicted` correlation with `|predicted| > 2` (the quantum/record
Tsirelson value `2√2`). So λ cannot be a noncontextual value-map over incompatible settings. -/
theorem no_global_record_valuemap {Λ : Type*} [Fintype Λ] (M : LHVModel Λ)
    {predicted : ℝ} (hP : 2 < |predicted|) (hrep : M.chsh = predicted) : False :=
  not_lhv_if_chsh_gt_two predicted hP M hrep

/-- **A single actuality value assigning all four settings is local (CHSH ≤ 2).** A single λ that fixed ±1
outcomes for every (incompatible) setting is CHSH-bounded by 2, hence could not carry the quantum record
correlation `2√2`. Values must therefore be assigned per ACTUAL context, not globally over all settings. -/
theorem single_lambda_bounded (a₁ a₂ b₁ b₂ : ℝ)
    (ha₁ : a₁ = 1 ∨ a₁ = -1) (ha₂ : a₂ = 1 ∨ a₂ = -1)
    (hb₁ : b₁ = 1 ∨ b₁ = -1) (hb₂ : b₂ = 1 ∨ b₂ = -1) :
    |a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂| ≤ 2 :=
  chsh_pointwise a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂

/-- **Contextuality-safety (the OP3b Bell-marginal check).** There is a quantum/record correlation exceeding
the classical bound 2 (Tsirelson) that NO global value-map (`LHVModel`) can match. Combined with the fact
that on each compatible context the bipartite record marginals are no-signaling
(`NoSignalingGeneral.bipartite_no_signaling`), this is the safety statement: assigning values only to the
ACTUAL (compatible) context is *forced* — no global noncontextual joint exists — and remains operationally
no-signaling. λ thus dodges the Fine/Bell global-distribution obstruction by being actual-context-only, not
by smuggling a non-quantum assumption. -/
theorem contextuality_safe :
    ∃ predicted : ℝ, 2 < |predicted| ∧
      ∀ {Λ : Type*} [Fintype Λ] (M : LHVModel Λ), M.chsh ≠ predicted :=
  qiqth_violates_bell

end QIQTH.ContextualitySafe
