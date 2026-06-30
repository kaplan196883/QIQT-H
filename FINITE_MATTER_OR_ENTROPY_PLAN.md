# Finite matter or finite entropy? — resolving the red-team dilemma

**Status:** ACTIVE PLAN (2026-06-30), forced by the GPT-5.5-pro adversarial red-team (commit 6e6daba). The
red-team retracted "QIQT-H escapes CPSUV" and exposed a **dilemma**: the CPSUV "escape" is either
- **(A) VACUOUS** — matter stays ordinary infinite-mode Type III₁ QFT (propagators unmodified), and "finite
  capacity" is only finite *renormalized entropy* in a trace, doing **no matter-UV work**; or
- **(B) REOPENS** — capacity is made literal/operational (a finite per-region matter structure), which restricts
  states and likely **destroys Type III₁ / reintroduces a preferred frame**, regenerating the LV term.

Plus structural no-gos against (B): **Type III₁ has no atoms / no finite trace**; **noncompact Lorentz has no
nontrivial finite-dim unitary reps**; **generalized entropy ≠ log dim** (category error). Red-team odds for the
substantive "finite matter + exact Lorentz" claim: **10–20%**.

**This plan decides which fork QIQT-H is actually on, tests each horn against the no-gos, and states honestly what
QIQT-H must become.** The expected (red-team) outcome: Fork B (finite *matter*) is dead; QIQT-H is Fork A (finite
*entropy/records* over covariant matter), and its distinctive content is the **(Φ,λ) record-selection ontology +
the holographic entropy bound**, NOT a finite matter Hilbert space — which would require honestly restating the
"finite information" framing. We test that, we don't assume it.

## 0. Honest invariants
- Never claim QG or the value of `G`. The `1/4` *ratio* is derived (`SakharovRatio.lean`).
- The red-team verdict is the **starting point**, not the enemy: be willing to conclude QIQT-H must **drop literal
  finite-matter capacity**. A clean negative result (Fork B dead) is a WIN — it tells us what the theory is.
- Ship green Lean increments / reproducible audits; checkpoint honestly. No `sorry`.

## 1. The two forks, precisely
- **Fork A — finite renormalized entropy.** Matter = standard covariant (Type III₁) QFT, propagators unmodified.
  "Capacity" = `S_ren(ρ_D) ≤ Q_D = A(∂D)/4ℓ_P²` (a Type II *trace-entropy* bound, à la CLPW). **Consistent** with
  exact Lorentz (no matter-UV cutoff). **Question:** is this distinctive, or just "QFT + the Bousso bound + a
  selection rule"? What is QIQT-H's irreducible new claim on this fork?
- **Fork B — finite matter capacity.** A literal finite per-diamond matter structure (finite-dim local Hilbert /
  `card ≤ exp Q_D` on matter states). **Question:** is it killed by the no-gos (Lorentz finite-rep, Type III,
  trace≠card)?

## 2. The decisive increments (most-tractable-first)

### D1 — the fork audit *(markdown verdict; days)*
Read QIQT-H's actual postulates: P4 (`qiqth_capacity_qr_vs_qmax`), the record net (`LorentzSelection.card_le`),
`FQBoundMicro`/`Phase5Master`, the (Φ,λ) ontology. **Verdict:** which fork is QIQT-H *committed* to — does it
assert a literal finite matter Hilbert space (B), or a finite record/entropy bound over covariant matter (A)?
Cite exact code/postulates. **PASS** = an unambiguous fork assignment. (Likely: a *mix* — the records are
finite-atomic (B-flavoured) but the matter substrate is the covariant free-field (A-flavoured); the audit must
say precisely where the "finite" lives.)

### D2 — the finite-matter ⟹ no-exact-Lorentz no-go *(Lean; strengthen I1; tractable)*
Formalize the rep-theoretic kill of Fork B: a **literal finite-dimensional matter Hilbert space cannot carry
exact, nontrivial Lorentz boosts with a positive Hamiltonian.** Build on I1 (`no_exact_finite_boost`: on finite-
dim, `[K,P]=i·H`, `H⪰0 ⟹ H=0`). New `QIQTH/QG/FiniteMatterNoLorentz.lean`: package it as "finite-dim local
matter + exact boost generator + `H≥0` ⟹ trivial dynamics", i.e. **Fork B with exact Lorentz forces `H=0`
(no dynamics).** **PASS** = Fork B (finite matter + exact Lorentz + nontrivial `H`) is machine-checked
impossible ⟹ QIQT-H must be Fork A (or give up *exact* Lorentz for approximate). Axiom-free, std-3, budget 0.

### D3 — generalized-entropy ≠ cardinality *(Lean; the K1 counterexample; tractable)*
Formalize the trace→cardinality counterexample (`TRACE_CARDINALITY_SCOPE.md` K1): **bounded entropy does NOT
bound record count.** `QIQTH/QG/EntropyNotCardinality.lean`: for every `Q > 0` and every `N`, a weighted record
distribution (`N` atoms, weights `tᵢ = e^Q/N`) has `S = Q` (Shannon/trace entropy `= log ∑tᵢ`) independent of
`N`. So `S_ren ≤ Q_D ⇏ card ≤ exp Q_D` — confirming Fork A's capacity is an **entropy bound, not a state count**
(the red-team category-error point), and a literal cardinality bound needs an extra (min-cell) hypothesis.
**PASS** = the counterexample is machine-checked ⟹ Fork A capacity is genuinely entropy-only. Axiom-free.

### D4 — Fork A distinctiveness audit *(markdown verdict; days–week)*
GIVEN Fork A (the likely survivor): what is QIQT-H's **irreducible distinctive claim** beyond "covariant QFT +
holographic entropy bound + a selection postulate"? Candidates: (i) the (Φ,λ) record-selection ontology (one
world, Born from typicality) — which is REAL and machine-checked and **does not need finite matter**; (ii) the
P4-MICRO/Sakharov area-law derivation (the 1/4 ratio) — also entropy-level, fork-A-safe. **Verdict:** restate
the "finite information / finite capacity" framing honestly as **finite holographic ENTROPY + a record-selection
ontology**, NOT a finite matter Hilbert space. What survives the red-team, what must be reworded in the
papers/site.

### D5 — the resolution + consult *(markdown; consult GPT-5.5-pro)*
Synthesize D1–D4 into the honest resolution: which fork, what QIQT-H is, what is retracted, what is reinforced.
Consult GPT-5.5-pro (adversarial) to confirm the resolution survives a second red-team. **Deliverable:** the
corrected program statement + a punch-list of papers/site/memory edits.

## 3. Honest difficulty + expected outcome
D1, D4, D5 are audits/synthesis (days). D2, D3 are tractable Lean no-gos (build on I1 + K1; days–week). The whole
fork-resolution is **weeks**, not years — it is a *clarification*, not a construction. **Expected outcome
(red-team):** Fork B dies on D2 (finite matter + exact Lorentz ⟹ trivial); QIQT-H is Fork A; the distinctive
claim is the (Φ,λ) ontology + holographic entropy, and "finite capacity" must be reworded as finite *entropy*,
not finite *matter*. If D1 instead finds QIQT-H *requires* literal finite matter, then D2 shows the program is in
serious tension with exact Lorentz and must either go approximate-Lorentz or be rethought — also a decisive,
honest outcome.

## 4. Verification
Lean: `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = std-3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`. Audits: a markdown
verdict citing exact code/postulates. One commit per increment with the
`Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; update §5.

## 5. Progress log
- **2026-06-30** — plan created (post red-team).
- **2026-06-30 — D1 ✅ DONE** (`scripts/qg/D1_fork_audit.md`): the fork audit. **Verdict: QIQT-H is committed to
  Fork A (operational/entropy), with Fork B only as gloss + proxy.** The rigorous capacity bound is a *von
  Neumann ENTROPY* bound (`area_floor_vonNeumann`: `S_vN(ρ_R) ≤ A/4ℓ_P²`); `HolographicCapacityBound`'s own header
  disclaims the matter reading (*"operational capacity Q_R=log N_R, NOT Hilbert-space dimension"*; *"type-III
  local algebra"*; exact `log dim=⟨A⟩/4` *"suspect"*); the finite cardinality lives on the **decoherent records**
  (`LorentzSelection.card_le`, the einselected `P.X D`), not matter modes; the finite-dim `Matrix`/corner models
  are acknowledged **proxies**. ⟹ the red-team's structural no-gos hit only the Fork-B gloss/proxy, which QIQT-H
  does NOT rigorously require. Honest resolution: restate the postulate as Fork A (drop "finite effective
  dimension").
- **2026-06-30 — D2 ✅ DONE** (`QIQTH/QG/FiniteMatterNoLorentz.lean`): the Fork-B no-go, machine-checked.
  `FinitePoincareRep` (a finite-dim rep of `[K,P]=iH`, `[K,H]=iP`, `H⪰0`); **`finitePoincare_trivial`: forces
  `H=0` AND `P=0`** (total triviality — strengthens I1's `H=0` via the second relation); `no_finitePoincareRep_
  of_nontrivial_energy` (a nonzero positive `H` admits no consistent exact boost). ⟹ literal finite-MATTER
  capacity + exact Lorentz + nonzero positive energy is **impossible** in finite dim (the rep-theoretic shadow of
  "non-compact Lorentz has no nontrivial finite-dim unitary rep"). **Fork B is untenable; QIQT-H must be Fork A.**
  Axiom-free (std 3), full `QIQTH` green, budget 0; wired in.
- **2026-06-30 — D3 ✅ DONE** (`QIQTH/QG/EntropyNotCardinality.lean`): bounded entropy does NOT bound cardinality,
  machine-checked. `traceEntropy_uniform_weighted` (a uniform `N`-atom state with trace weights `e^Q/N` has
  trace-entropy EXACTLY `Q` for all `N`); **`entropy_bound_not_cardinality_bound`** (∀ Q, ∀ N≥1, ∃ an `N`-atom
  probability family with `S_τ = Q` — cardinality unbounded at fixed entropy). ⟹ `S_τ ≤ Q_D ⇏ card ≤ exp Q_D`:
  **Fork A's capacity is genuinely an ENTROPY bound, not a literal state count** (a cardinality bound needs an
  extra minimal-cell/Holevo hypothesis). Axiom-free (std 3), full `QIQTH` green, budget 0; wired in.
- **NEXT → D4** (Fork A distinctiveness audit — the irreducible claim = (Φ,λ) ontology + holographic *entropy*;
  restate "finite capacity" as finite entropy not finite matter), then D5 (resolution + adversarial re-check).
