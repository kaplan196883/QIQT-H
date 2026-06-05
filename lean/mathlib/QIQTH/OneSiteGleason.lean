/-
# Deriving the single-trial Born law from non-contextuality (prize: the real content)

GPT-5.5-pro's verification of the prize join correctly flagged that `BornJoin.oneSite`
(the single-trial calibration `mass{value = a} = p a`) is a bare ASSUMPTION — the Born law
put in by hand.  This file removes that assumption for the single-trial law: it DERIVES that
the outcome probabilities are Born weights `tr(ρ Pₐ)` from a genuinely weaker, motivated
premise — NON-CONTEXTUALITY.

A non-contextual probability assignment on a finite-dimensional system is exactly an
`EffectGleason.EffectMeasure`: a functional `μ` on effects (0 ≤ E ≤ 1) that is normalized
(`μ 1 = 1`), nonnegative, and additive on COEXISTENT effects (`μ(E+F) = μ E + μ F` whenever
`E+F` is still an effect) — i.e. the probability of an outcome does not depend on which
compatible measurement it is read off from.  The finite effect-Gleason theorem
(`finite_effect_gleason`, axiom-free) then FORCES `μ E = tr(ρ E)` for a density matrix `ρ`.

So for ANY measurement `{Pₐ}` (effects), a non-contextual assignment gives `μ(Pₐ) = tr(ρ Pₐ)`:
the single-trial law is Born, DERIVED — not assumed.  This is the honest replacement for the
bare one-site calibration, and the genuine "(a) effect-Gleason on the PVM" half of the path
to a real (non-tautological) no-collapse Born result.  Axiom-free (standard three only).

(What is STILL assumed downstream, per the honest scope of `BornJoin`: independence across
trials, the world measure, and that the ensemble's marginal actually IS such a non-contextual
`EffectMeasure`.  Those remain open.) -/
import QIQTH.EffectGleason
import QIQTH.BornTypicalityQuantum
import Mathlib.Tactic

namespace QIQTH.OneSiteGleason

open EffectGleason
open scoped ComplexOrder

variable {d : ℕ}

/-- **The single-trial Born law is FORCED by non-contextuality.**  For a non-contextual
    probability assignment `m` (an `EffectMeasure`) and ANY measurement `{Pₐ}` of effects, the
    outcome probabilities `m.μ(Pₐ)` are the Born weights `Re tr(ρ Pₐ)` of a density matrix `ρ`
    — DERIVED from the effect-Gleason theorem, not assumed.  This is the honest content behind
    `BornJoin.oneSite`: the single-trial law is Born because any non-contextual normalized
    additive assignment is (finite effect-Gleason).

    HONEST CAVEAT (GPT-5.5-pro verification): the premise `EffectMeasure` is STRONG — precisely a
    normalized, positive, finitely-additive (on coexistent effects) state on the whole quantum
    effect algebra.  "Non-contextuality" is fair only with that qualifier (probability of an effect
    depends on the operator, not the POVM context, plus coarse-graining additivity).  It is not
    syntactically Born (no ρ/trace assumed) — effect-Gleason is the real engine — but it is a
    genuine assumption, not a triviality.  For a measurement one also reads `∑ₐ Pₐ = 1` (used in
    `forced_isProbVector`); here only `IsEffect (Pₐ)` is needed for the Born form per outcome. -/
theorem oneSite_forced (m : EffectMeasure d) {ι : Type*}
    (P : ι → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ a, IsEffect (P a)) :
    ∃ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ a, m.μ (P a) = (Matrix.trace (ρ * P a)).re := by
  obtain ⟨ρ, hpos, htr, hrep⟩ := m.finite_effect_gleason
  refine ⟨ρ, hpos, htr, fun a => ?_⟩
  have h := hrep (P a) (hP a)
  rw [← Complex.ofReal_re (m.μ (P a)), h]

/-- The forced single-trial law `a ↦ m.μ(Pₐ)` is a genuine probability vector: nonnegative
    (effect-measure positivity) and summing to one (POVM completeness + additivity). -/
theorem forced_isProbVector (m : EffectMeasure d) {ι : Type*} [Fintype ι]
    (P : ι → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ a, IsEffect (P a)) (hsum : ∑ a, P a = 1) :
    (∀ a, 0 ≤ m.μ (P a)) ∧ ∑ a, m.μ (P a) = 1 :=
  ⟨fun a => m.nonneg (P a) (hP a), m.mu_sum_of_povm P hP hsum⟩

/-- **Non-contextual assignments ARE the Born/trace forms (converse to effect-Gleason).**
    Every density matrix `ρ` (PSD, unit trace) defines an `EffectMeasure` `E ↦ Re tr(ρ E)`:
    normalized (`tr ρ = 1`), nonnegative (`trace_mul_nonneg`), and additive (trace linearity).
    So the non-contextuality premise of `oneSite_forced` is concrete and SATISFIABLE — and the
    non-contextual functionals are exactly the Born functionals. -/
noncomputable def traceEffectMeasure (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) : EffectMeasure d where
  μ := fun E => (Matrix.trace (ρ * E)).re
  normalized := by rw [Matrix.mul_one, htr]; exact Complex.one_re
  nonneg := fun E hE => by
    have h := BornTypicalityQuantum.trace_mul_nonneg hρ hE.1
    simpa using (Complex.le_def.mp h).1
  additive := fun E F _ _ _ => by
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

@[simp] theorem traceEffectMeasure_apply (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (E : Matrix (Fin d) (Fin d) ℂ) :
    (traceEffectMeasure ρ hρ htr).μ E = (Matrix.trace (ρ * E)).re := rfl

end QIQTH.OneSiteGleason
