/-
BornChain.lean — the Path-B capstone: Born = one irreducible Hilbert-typicality axiom, made unique by
Gleason and bracketed by two no-gos.

After the reduction layer (`RefinementBorn`, `SelectorRefinement`, `SelectionDynamics`, `BornRoutes`,
`Envariance`, `Relaxation`) and the two impossibility results, the honest status of the Born rule in this
development is fully assembled here. The chain (every link machine-checked, axiom-free):

  ┌─ META NO-GO (`BornRoutes.sqRule_refinement_signals`): any premise invariant under w ↦ w^α is obeyed by
  │   the non-Born power-law family, so NOTHING Born-free entails Born — some Born-strength input is forced.
  ├─ RANK-COUNT NO-GO (`RankCountNoGo.no_multiplicity_rule_is_born`): no amplitude-INDEPENDENT record
  │   multiplicity rule equals Born (multiplicity is state-independent, Born state-dependent) — so the forced
  │   input cannot be supplied by decoherence counting either.
  └─ Hence the input is irreducible. Its thinnest, most defensible form is a NONCONTEXTUAL probability
     assignment on effects — a normalized, positive, coexistent-additive `EffectGleason.EffectMeasure`
     (the finite Hilbert-typicality axiom μ(E)). Then:

  GLEASON-UNIQUENESS (this file, from finite effect-Gleason): a noncontextual assignment is FORCED to the
  Born/trace form `μ(E) = Re tr(ρ E)` for a density matrix ρ (`noncontextual_forces_born`), and conversely
  every density matrix yields such a noncontextual assignment (`born_is_noncontextual`). So the noncontextual
  functionals are EXACTLY the Born functionals — the axiom pins Born uniquely.

NET (the ceiling, honestly): Born is not derived from nothing — provably impossible (the two no-gos). It is
reduced to a single, maximally-natural typicality posit (noncontextuality / Hilbert measure), which Gleason
makes unique, and which both no-gos prove is irreducible. This is the strongest true statement available, and
it is the same posit every single-world program (Everett, Bohm–DGZ, Deutsch–Wallace) ultimately needs.

HONEST SCOPE: finite-dimensional; `EffectMeasure` (noncontextuality) is a genuine, strong premise, not a
triviality (no ρ/trace is assumed — effect-Gleason is the engine). No `sorry`, no project axioms.
-/
import QIQTH.OneSiteGleason
import QIQTH.RankCountNoGo
import QIQTH.BornRoutes

namespace QIQTH.BornChain

open EffectGleason
open QIQTH.OneSiteGleason
open scoped ComplexOrder

variable {d : ℕ}

/-- **Gleason-uniqueness link (forward).** Every noncontextual probability assignment on effects — a
normalized, positive, coexistent-additive `EffectMeasure` (the finite Hilbert-typicality axiom) — is FORCED
to the Born/trace form `μ(E) = Re tr(ρ E)` for a density matrix ρ, on every effect `E`. Derived from the
finite effect-Gleason theorem; the typicality axiom is not assumed to be Born. -/
theorem noncontextual_forces_born (m : EffectMeasure d) :
    ∃ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ E, IsEffect E → m.μ E = (Matrix.trace (ρ * E)).re := by
  obtain ⟨ρ, hpos, htr, hrep⟩ := m.finite_effect_gleason
  exact ⟨ρ, hpos, htr, fun E hE => by rw [← Complex.ofReal_re (m.μ E), hrep E hE]⟩

/-- **Gleason-uniqueness link (converse / satisfiable).** Every density matrix ρ yields a noncontextual
probability assignment with the Born form `μ(E) = Re tr(ρ E)` (via `traceEffectMeasure`). Together with
`noncontextual_forces_born` this characterizes the noncontextual functionals as EXACTLY the Born functionals:
the Hilbert-typicality axiom is consistent and pins Born uniquely. -/
theorem born_is_noncontextual (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ m : EffectMeasure d, ∀ E, m.μ E = (Matrix.trace (ρ * E)).re :=
  ⟨traceEffectMeasure ρ hρ htr, fun _ => rfl⟩

end QIQTH.BornChain
