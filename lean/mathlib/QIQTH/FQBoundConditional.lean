/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The FQ bound, conditional on the JLMS / dual-weight-trace inputs (Phase 6 algebraic core)

P4's deliverable is the holographic area floor `S(ρ_R) ≤ A/4ℓ_P²`.  Per the campaign plan it is the JLMS identity
`K̃ = A_edge·(1/4ℓ_P²) + K_bulk` together with relative-entropy positivity.  The **crossed-product dual-weight
trace** that defines those expectations is a genuine Mathlib-grade frontier (Phase 5).  This file isolates the
**purely algebraic core** of the bound — what follows from the JLMS decomposition and positivity *alone* — as
axiom-free *conditional* theorems whose hypotheses are exactly the Phase-5 / JLMS obligations (theorem arguments,
**not** axioms).  This is the highest-leverage P4 increment per a GPT-5.5-pro strategy audit (2026-06-27): it
delivers the headline inequality conditionally and pins down precisely what the trace must supply.

HONEST SCOPE.  The value of `G` / the edge normalization `⟨A_edge⟩ = A/4ℓ_P²` is the **carried UV datum**: the
coefficient `c` (`= 1/4ℓ_P²`) is a free real parameter here, never assigned a value.  Self-adjointness is **not**
positivity, so area-positivity, where it matters, is an explicit hypothesis.  The `1/4` *ratio* is derived
elsewhere (`SakharovRatio`); it is not re-asserted here.  Free scalar only.
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith

namespace QIQTH.FQBound

open scoped ENNReal

/-- **The FQ bound from a nonnegative slack (real form).**  If the entropy plus a nonnegative `slack` is at most the
    `areaTerm`, then the entropy is at most the `areaTerm`: `0 ≤ slack` and `S + slack ≤ areaTerm` ⟹ `S ≤ areaTerm`.
    The `slack` is the relative-entropy / bulk-modular remainder, which the JLMS analysis must show is `≥ 0`. -/
theorem fq_bound_of_slack {S areaTerm slack : ℝ} (hslack : 0 ≤ slack)
    (hmaster : S + slack ≤ areaTerm) : S ≤ areaTerm := by linarith

/-- **The FQ bound from the JLMS first law + relative-entropy positivity (real form).**
    With the JLMS decomposition of the modular Hamiltonian's expectation `⟨K̃⟩ = ⟨A_edge⟩·c + ⟨K_bulk⟩`
    (`= areaExp·c + bulk`, where `c = 1/4ℓ_P²` is the carried UV datum) and the first law `S = ⟨K̃⟩ − D(ρ‖σ)` with
    relative-entropy positivity `0 ≤ D` (the one-particle shadow of which is the proved `cgpEntropy_nonneg`), the
    entropy obeys the **FQ bound** `S ≤ ⟨A_edge⟩·c + ⟨K_bulk⟩`.  This is P4's BOUND derived, modulo the Phase-5
    trace supplying `areaExp`, `bulk`, `D`, and the first law as a theorem. -/
theorem fq_bound_of_jlms {S relEnt areaExp bulk c : ℝ} (hrel : 0 ≤ relEnt)
    (hfirst : S = areaExp * c + bulk - relEnt) : S ≤ areaExp * c + bulk := by linarith

/-- **The pure area floor when the bulk term is absorbed:** if additionally `⟨K_bulk⟩ ≤ 0` (the bulk modular energy
    is non-positive in the regime considered) the bound collapses to `S ≤ ⟨A_edge⟩·c` — the bare area floor.
    Recorded to make the bulk-sign assumption explicit (a GPT-5.5-pro red flag). -/
theorem fq_bound_area_only {S relEnt areaExp bulk c : ℝ} (hrel : 0 ≤ relEnt) (hbulk : bulk ≤ 0)
    (hfirst : S = areaExp * c + bulk - relEnt) : S ≤ areaExp * c := by linarith

/-- **The FQ bound from a nonnegative slack (`ℝ≥0∞` form).**  Avoids real subtraction with possible infinities
    (GPT-5.5-pro red flag): in `ℝ≥0∞`, `S + slack ≤ areaTerm` ⟹ `S ≤ areaTerm`, since `S ≤ S + slack`
    (`le_self_add`). -/
theorem fq_bound_of_slack_ennreal {S areaTerm slack : ℝ≥0∞} (hmaster : S + slack ≤ areaTerm) :
    S ≤ areaTerm := le_trans le_self_add hmaster

end QIQTH.FQBound
