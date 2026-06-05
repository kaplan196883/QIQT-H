/-
# Wiring non-contextuality into the join: the single-trial law `p` is FORCED Born

The prize join (`BornJoin.finite_noCollapseBornRepresentation`) left the single-trial law
`p` as an ARBITRARY probability vector (GPT-5.5-pro red flag #4 — "p unjoined").  Here we
remove that freedom: if the ensemble's outcome law `p` is the value of a NON-CONTEXTUAL
assignment (an `EffectGleason.EffectMeasure`) on an actual measurement `{Pₐ}`, then
effect-Gleason FORCES `p a = Re tr(ρ Pₐ)` — the genuine quantum Born weight of a density
matrix `ρ`, not a free parameter.

`finite_noCollapseBorn_fromNoncontextuality` then states the whole representation with `p`
derived: unique actual history + single-trial law forced Born + Born product law + typicality.
What is STILL assumed (honest scope): independence across trials (`indep`), the world measure
(`ProbMass`), and that the ensemble's single-trial statistics ARE a non-contextual effect
assignment (`hcal`).  Non-contextuality is the motivated premise doing the work; the Born
WEIGHTS are no longer put in by hand.  Axiom-free (standard three only). -/
import QIQTH.BornJoin
import QIQTH.OneSiteGleason
import Mathlib.Tactic

namespace QIQTH.BornJoinGleason

open BornJoin OneSiteGleason EffectGleason BornTypicalityFinite Finset
open scoped ComplexOrder

variable {m n d : ℕ}

/-- **The ensemble's single-trial law is FORCED Born by non-contextuality.**  If `p` coincides
    with the values of a non-contextual assignment `M` (an `EffectMeasure`) on a measurement
    `{Pₐ}`, then `p a = Re tr(ρ Pₐ)` for a density matrix `ρ` — derived via effect-Gleason, not
    assumed.  `p` is therefore not a free parameter. -/
theorem ensemble_p_isBorn (E : ActualEnsemble m n) (M : EffectMeasure d)
    (P : Fin m → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ a, IsEffect (P a))
    (hcal : ∀ a, M.μ (P a) = E.p a) :
    ∃ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ a, E.p a = (Matrix.trace (ρ * P a)).re := by
  obtain ⟨ρ, hpos, htr, hb⟩ := oneSite_forced M P hP
  exact ⟨ρ, hpos, htr, fun a => by rw [← hcal a]; exact hb a⟩

/-- **No-collapse Born representation with the single-trial law DERIVED (not assumed).**
    Given the prize ensemble PLUS non-contextuality of the single-trial statistics (the law `p`
    is the value of a non-contextual effect assignment `M` on a measurement `{Pₐ}`), there is a
    density matrix `ρ` such that: (i) every world has a UNIQUE actual pointer-value history
    (capacity + selector, no collapse); (ii) the single-trial law is the Born weight
    `Re tr(ρ Pₐ)` — FORCED by effect-Gleason; (iii) the world-mass of each history is the Born
    PRODUCT law; (iv) atypical-frequency histories carry vanishing world-mass.  The Born weights
    are no longer a free parameter — only NON-CONTEXTUALITY + independence (+ the world measure)
    are assumed. -/
theorem finite_noCollapseBorn_fromNoncontextuality (E : ActualEnsemble m n)
    (M : EffectMeasure d) (P : Fin m → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ a, IsEffect (P a))
    (hcal : ∀ a, M.μ (P a) = E.p a) (k : Fin m) {ε : ℝ} (hε : 0 < ε) (hn : 0 < n) :
    ∃ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      (∀ ω : E.Ω, ∃! h : Fin n → Fin m,
          ∀ t, ∃ r ∈ (E.V ω t).config.active, (E.V ω t).ctx.valueOf r = h t)
      ∧ (∀ a, E.p a = (Matrix.trace (ρ * P a)).re)
      ∧ (∀ h : Fin n → Fin m,
          E.P.massSet ((univ : Finset E.Ω).filter (fun ω => E.actualHist ω = h)) = w E.p h)
      ∧ E.P.massSet ((univ : Finset E.Ω).filter (fun ω =>
          ((n : ℝ) * ε) ^ 2 ≤ (count k (E.actualHist ω) - (n : ℝ) * E.p k) ^ 2))
          ≤ E.p k * (1 - E.p k) / ((n : ℝ) * ε ^ 2) := by
  obtain ⟨ρ, hpos, htr, hborn⟩ := ensemble_p_isBorn E M P hP hcal
  obtain ⟨huniq, hpush, htyp⟩ := E.finite_noCollapseBornRepresentation k hε hn
  exact ⟨ρ, hpos, htr, huniq, hborn, hpush, htyp⟩

/-- **No-collapse Born representation tied to a concrete density matrix (interface, not a
    reduction).**  Same conclusion as `finite_noCollapseBorn_fromNoncontextuality` with `M`,
    `hcal` discharged via `traceEffectMeasure ρ`; the only quantum input is `hp` (the single-trial
    law IS `tr(ρ Pₐ)`).  HONEST CAVEAT (GPT-5.5-pro verification): as a standalone Born DERIVATION
    this trace path is CIRCULAR — `traceEffectMeasure ρ` is built FROM `ρ` via the Born formula
    and Gleason then recovers a density matrix, so `hp` already asserts `p` is Born.  This is an
    INTERFACE/specialization theorem (convenient when the state is known), NOT an assumption
    reduction.  The genuine reduction is the non-trace path `ensemble_p_isBorn` /
    `finite_noCollapseBorn_fromNoncontextuality`, where `M` is an INDEPENDENTLY given non-contextual
    effect measure and Born is forced by effect-Gleason. -/
theorem finite_noCollapseBorn_trace (E : ActualEnsemble m n)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (htrρ : ρ.trace = 1)
    (P : Fin m → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ a, IsEffect (P a))
    (hp : ∀ a, E.p a = (Matrix.trace (ρ * P a)).re) (k : Fin m) {ε : ℝ} (hε : 0 < ε) (hn : 0 < n) :
    (∀ ω : E.Ω, ∃! h : Fin n → Fin m,
        ∀ t, ∃ r ∈ (E.V ω t).config.active, (E.V ω t).ctx.valueOf r = h t)
    ∧ (∀ a, E.p a = (Matrix.trace (ρ * P a)).re)
    ∧ (∀ h : Fin n → Fin m,
        E.P.massSet ((univ : Finset E.Ω).filter (fun ω => E.actualHist ω = h)) = w E.p h)
    ∧ E.P.massSet ((univ : Finset E.Ω).filter (fun ω =>
        ((n : ℝ) * ε) ^ 2 ≤ (count k (E.actualHist ω) - (n : ℝ) * E.p k) ^ 2))
        ≤ E.p k * (1 - E.p k) / ((n : ℝ) * ε ^ 2) := by
  obtain ⟨_, _, _, huniq, _, hpush, htyp⟩ :=
    finite_noCollapseBorn_fromNoncontextuality E (OneSiteGleason.traceEffectMeasure ρ hρ htrρ)
      P hP (fun a => by rw [OneSiteGleason.traceEffectMeasure_apply]; exact (hp a).symm) k hε hn
  exact ⟨huniq, hp, hpush, htyp⟩

end QIQTH.BornJoinGleason
