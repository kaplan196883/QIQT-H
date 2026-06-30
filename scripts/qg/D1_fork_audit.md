# D1 — the fork audit: which horn is QIQT-H committed to?

**Date:** 2026-06-30. **Plan:** `FINITE_MATTER_OR_ENTROPY_PLAN.md` D1. **Question:** does QIQT-H's actual
postulate base commit to **(B) literal finite *matter*** (a finite-dim regional Hilbert space) or **(A) finite
*entropy/records*** over covariant (Type III₁) matter?

## What the postulate actually says (citing exact code)

**The capacity postulate — `QIQTH/FQBoundMicro.lean`:**
```lean
class HolographicCapacityBound (R : Type*) [Fintype R] (areaTerm : ℝ) where
  bound : Real.log (Fintype.card R) ≤ areaTerm        -- log|𝓗_R| ≤ A/4ℓ_P², the ≤ form
```
Its **own module header** is explicit about the reading:
- *"It is the **regional operational capacity** `Q_R = log N_R` — the number `N_R` of [distinguishable
  states/records] … it is **NOT** [the] global Hilbert-space dimension."*
- *"… a **type-III local algebra** …, and its log-capacity is **bounded** by the area term"* — i.e. the matter
  algebra is acknowledged Type III₁ (no trace, no finite dimension), and capacity is a *bound on it*.
- *"area-operator fluctuations make exact `log dim = ⟨A⟩/4` **suspect** — hence `HolographicCapacityBound`"* (the
  `≤` form, not `=`).

**The rigorous, load-bearing content is an ENTROPY bound** — `area_floor_vonNeumann`:
```lean
theorem area_floor_vonNeumann [HolographicCapacityBound n areaTerm] (h : IsDensity ρ) :
    vonNeumannEntropy h ≤ areaTerm
```
i.e. `S_vN(ρ_R) ≤ A/4ℓ_P²`. The dynamical sibling (`Phase5Master`/`FQBoundCGP`) is also an entropy/JLMS bound.

**The records — `QIQTH/LorentzSelection.lean`:** `RecordedHistoryNet.card_le : Fintype.card (P.X D) ≤ N D`,
`N D ≈ exp(Q_D)`. This is a finite cardinality bound on the **decoherent record fibre** `P.X D` (the einselected
pointer sectors, carrying the decoherence measure `ω`) — a *coarse-grained classical* structure, **not** the
matter field's modes.

**The Lean proxies — `Matrix n n ℂ`, `CornerConstruction` (`P·End(𝓗_R)·P`, `𝓗_R` finite-dim).** The
*formalization* works in genuinely finite-dimensional Hilbert spaces — a Fork-B-flavoured **proxy** — but these
are explicitly labelled finite proxies for the continuum (Type III) field (`no_finiteDim_CCR`,
`finiteDim_scaling_forces_zero`, the truncation-defect guards), not a claim that matter *is* finite-dim.

## Verdict: QIQT-H is committed to **Fork A** (operational/entropy), with Fork B only as gloss + proxy

QIQT-H is a **mix in language but not in load-bearing content**:

| Layer | Reading | Fork |
|---|---|---|
| Rigorous capacity bound (`area_floor_vonNeumann`, `Phase5Master`) | `S_vN(ρ_R) ≤ A/4ℓ_P²` — an **entropy** bound | **A** |
| Records (`LorentzSelection.card_le`) | finite **decoherent record** count (coarse-grained, einselected) | **A** (records = the entropy-bounded distinguishable content) |
| Postulate *header* gloss | "finite **effective dimension** `log|𝓗_R|`" | B-flavoured **heuristic**, self-flagged "suspect" |
| Lean **proxies** (`Matrix n n ℂ`, the corner) | finite-dim Hilbert space | B-flavoured **proxy** for the Type III field |

**The literal finite-*matter* reading (B) is NOT a load-bearing rigorous commitment.** The module header itself
disclaims it ("operational capacity, NOT Hilbert-space dimension"; "type-III local algebra"; the `=` form is
"suspect"), the rigorous theorems bound **von Neumann entropy**, and the finite cardinality lives on the
**decoherent records**, not the matter modes. Fork B survives only as (i) heuristic language ("finite effective
dimension") and (ii) finite-dimensional formal *proxies* explicitly marked as such.

## Consequence

The red-team's structural no-gos (Type III₁ has no atoms / no finite trace; non-compact Lorentz has no
finite-dim unitary reps) bite **only** the Fork-B heuristic/proxy reading — which QIQT-H does **not** rigorously
require. So the honest resolution (D4/D5) is to **restate the postulate cleanly as Fork A**: a holographic bound
on the *operational/entropy* content (`S_ren ≤ Q_R`) and the *distinguishable-record* count over a covariant Type
III₁ matter algebra — **dropping the "finite effective dimension" gloss** and demoting the finite-dim Lean models
to acknowledged proxies. That removes the structural objections at the honest cost of the "finite matter Hilbert
space" framing — which the code already disclaims.

**Open sub-question handed to D2/D3:** confirm that the finite-*matter* reading is genuinely untenable (D2: a
finite-dim matter Hilbert space + exact Lorentz boost + `H ≥ 0` ⟹ trivial dynamics, strengthening I1) and that
the Fork-A capacity is genuinely entropy-not-count (D3: bounded entropy ⇏ bounded cardinality). Then D4 restates
the distinctive claim. Never claim QG or the value of `G`; the `1/4` ratio is derived (`SakharovRatio.lean`).
