# The distinctive `Q_R` frontier — the max-entropy bridge + the capacity-of-entanglement gap

**Status:** ✅ COMPLETE (2026-07-01) — Track A (sharpened guardrail, all surfaces) + Track B (the axiom-free
no-go + capacity-of-entanglement gap + the max-entropy bridge postulate & its conditional prediction) both done. **Origin:** the GPT-5.5-pro adversarial scoping consult on QIQT-H's *only*
genuinely-distinctive open target (a capacity `Q_R` differing from standard generalized entropy
`S_gen = A/4G + S_bulk`). **Verdict (settled, take as given):**

- **A distinctive `Q_R` cannot be DERIVED** from QIQT-H's own principles. Conditional no-go: given (1) area/JLMS/GSL
  use the **von Neumann** entropy `S_vN` + relative entropy, (2) the finite **count** is *independent* data not
  fixed by `S_vN` (`EntropyNotCardinality`), (3) `λ` is **inert** (so it cannot back-react on geometry), any
  count-based `Q_R` is necessarily *non-geometric bookkeeping*, *standard Rényi/one-shot physics*, or *a new
  postulate*. Routes (B) einselected-record-count and (D) (Φ,λ)-back-reaction are **dead**; (C) finite-`N` log
  corrections have no QIQT-H-predicted coefficient.
- **The one surviving route is an explicit POSTULATE, not a derivation** — the "max-entropy / one-shot" bridge:
  **gravitational/reconstruction capacity is the smooth max-entropy `H_max^ε` (≈ log-rank, Rényi-0) of the finite
  Type-I record algebra, NOT `S_vN`.** QIQT-H's finite-**count** layer points naturally at `S_max`, not `S_vN`.
- **It makes a sharp, falsifiable, distinctive prediction:** `Q_R − S_gen = S_max − S_vN ≥ 0` (the count/entropy
  gap), governed in the continuum by `Q_R^ε − S_gen ≈ z_ε·√(V_gen) + O(log A)`, where `V_gen = Var(K_gen)` is the
  **capacity of entanglement** (modular variance, measurable from Rényi data near `n=1`) — showing up as finite-size
  Page-time / QES-transition shifts in random tensor networks, JT/SYK, finite-dim holographic codes.

**This plan builds the HONEST version of that frontier, in QIQT-H's tractable style:** (1) the conditional no-go
(derivation is impossible), (2) the finite, classical **count/entropy gap** and the **capacity of entanglement**
with their key properties, (3) the explicit **max-entropy bridge postulate** + its conditional distinctive
prediction (the gap), all axiom-free, with the continuum `√V_gen` coefficient and the value of `G` as cited
frontiers.

**Honest invariants (enforce every increment):** NO `sorry`; `#print axioms` = std-3; budget 0. The bridge is a
**NEW POSTULATE, NOT a derivation** — never say QIQT-H *derives* a distinctive `Q_R`; the prediction is
**conditional on the postulate**; never claim nature picks it, never claim QG or the value of `G`; the continuum
`√V_gen` form and the coefficient are **cited frontiers**; cite `EntropyNotCardinality` as the no-go that forces
the postulate.

---

## Track A — the honesty guardrail (docs)

State consistently across inventory §2/§9, ledger (row C7/new C8), website (`open-problems`/`theory`), paper §1.1a:

> *Deriving a `Q_R` distinct from standard generalized entropy is **impossible** from QIQT-H's principles
> (conditional no-go: `S_vN`-area + count-independence + λ-inertness). It is possible **only** by adding the explicit
> **max-entropy bridge postulate** — gravity's capacity is `S_max` (the finite record **count**), not `S_vN`. That
> postulate (a new assumption, NOT a derivation) makes the falsifiable prediction `Q_R − S_gen = S_max − S_vN`,
> governed by the **capacity of entanglement** `√V_gen` — finite-size Page-time/QES shifts. The coefficient and the
> value of `G` are cited frontiers.*

PASS = every surface states it the same way, with "postulate not derivation" explicit and `EntropyNotCardinality` cited.

---

## Track B — Lean (`QIQTH/MaxEntropyCapacity.lean`)

Finite-dim / classical (work on the eigenvalue/RT **spectrum** `p : ι → ℝ`, a finite probability distribution).
Reuse `ShannonFano.H` (`= −∑ p log p = S_vN`), `negMulLog`, `vonNeumannEntropy_le_log_card`/`shannon_le_log_card`,
and the `OperationalCapacity` KL machinery. Each phase an axiom-free green checkpoint.

### B0 — spectrum + the two entropies *(tractable)*
- `Smax p := Real.log (support card)` (= log-rank = Rényi-0 = the **count** capacity). `Svn := ShannonFano.H univ p`.
- `gap p := Smax p − Svn p` (the count/entropy gap — the distinctive quantity).

### B1 — `smax_ge_svn` + `gap_nonneg` *(near-free; reuse `shannon_le_log_card`)*
`Svn p ≤ Smax p` (Shannon ≤ log support), so `gap p ≥ 0`. Equality iff the spectrum is flat (maximally mixed).

### B2 — the conditional no-go `svn_underdetermines_smax` *(the honest negative; mirrors `EntropyNotCardinality`)*
For any `Q : ℝ` and any `N`, ∃ a spectrum with `Svn = Q` but `Smax` (log-rank) arbitrarily large — i.e. the area
(which fixes `S_vN` via JLMS) does **NOT** fix the count `S_max`. Hence a count-based `Q_R` is **independent** of
the geometric `S_gen` and cannot be derived from it. *(Reuse `EntropyNotCardinality.traceEntropy_uniform_weighted`
or build directly: a near-flat spectrum on `N` points with one tunable atom.)*

### B3 — the capacity of entanglement `V_gen` *(the prediction's quantity; classical variance)*
- `capEnt p := (∑ p_i (log p_i)²) − (∑ p_i log p_i)²` (= `Var_p(−log p)` = modular variance).
- `capEnt_nonneg` (variance ≥ 0 — Cauchy–Schwarz / `inner_mul_le_norm`, or `Finset.inner_mul_le_norm`-style).
- `capEnt_zero_iff_flat` (= 0 iff spectrum flat ⟺ `gap = 0` ⟺ `Svn = Smax`).

### B4 — the bridge postulate + the conditional distinctive prediction *(the payoff)*
- `class MaxEntropyCapacity` (the **postulate**, a typeclass like `HolographicCapacityBound`, never a Lean axiom):
  `Q_R = Smax p` — gravity's capacity is the max-entropy/count.
- `distinctive_gap` (conditional theorem): under `MaxEntropyCapacity`, `Q_R − Sgen = Smax − Svn = gap p ≥ 0`, with
  `gap = 0 ⟺ capEnt = 0 ⟺ flat`. So the postulate predicts a **strictly positive** capacity gap exactly when the
  spectrum is non-flat (the generic case) — the finite shadow of the `√V_gen` prediction. Docstring: NEW POSTULATE,
  conditional, the continuum `√V_gen` coefficient + value of `G` are frontiers.

### B5 — wire-in + audit + point Track-A docs at the built theorems
`QIQTH.lean` import, `AxiomAudit.lean` pins (std-3), `axiom_budget_check.sh` budget 0; flip the guardrails to the
theorem names.

PASS = the no-go (`svn_underdetermines_smax`), the gap (`gap_nonneg`), the capacity of entanglement
(`capEnt_nonneg`/`_zero_iff_flat`), and the conditional `distinctive_gap` all proved axiom-free; docs state
"postulate not derivation."

---

## Verification (per increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.MaxEntropyCapacity` green; `#print axioms` std-3;
`bash scripts/axiom_budget_check.sh` budget 0; ONE commit per increment with the `Co-Authored-By: Claude Opus 4.8
<noreply@anthropic.com>` trailer; push via schannel; update the Progress log. Website edits build green (66 pages).
NO `sorry`. Never claim a *derivation*, QG, the value of `G`, or that nature picks the postulate.

## Honest scale
B0–B3 are days (finite-dim classical, most pieces exist). B4 is the conditional packaging. The whole thing is the
**honest distinctive frontier**: it proves derivation is impossible (the no-go), builds the distinctive *quantity*
(the count/entropy gap = capacity of entanglement), and states the *one postulate* that would make QIQT-H
distinctive — with its falsifiable prediction — clearly labelled as a postulate, not a result. The continuum
`√V_gen` coefficient, the value of `G`, and any data comparison stay cited frontiers.

## Progress log
- **2026-07-01** — plan created from the GPT-5.5-pro distinctive-`Q_R` consult.
- **2026-07-01 — Track A ✅ DONE (the sharpened guardrail).** Updated inventory §2 (added the "distinctive `Q_R`
  is a POSTULATE not a derivation" bullet), ledger row C7 (sharpened "open frontier" → "cannot derive; max-entropy
  bridge postulate"), website `open-problems` (the honest-edge paragraph), and paper §1.1a — all stating: a `Q_R`
  ≠ `S_gen` **cannot be derived** (conditional no-go: `S_vN`-area + count-independence + λ-inertness); possible
  only via the explicit **max-entropy bridge postulate** (`Q_R = S_max`, the count), a *new postulate not a
  derivation*, predicting the capacity-of-entanglement gap `Q_R − S_gen = S_max − S_vN ~ √V_gen`; coefficient + `G`
  = frontiers; `EntropyNotCardinality` cited. Website builds green (66 pages). **NEXT → Track B Lean bottom-up
  (B0 spectrum/two-entropies → B1 gap≥0 → B2 the no-go `svn_underdetermines_smax` → B3 capacity of entanglement →
  B4 the bridge postulate + conditional prediction → B5 wire-in).**
- **2026-07-01 — B0+B1 ✅ DONE** (`QIQTH/MaxEntropyCapacity.lean`, axiom-free std-3, wired into `QIQTH.lean` +
  `AxiomAudit.lean`, budget 0). Built the two entropies — `Smax ι = log(dim)` (the log-count / max-entropy
  capacity, what the bridge postulate proposes gravity uses) and `Svn p = BranchLedger.Shannon` (the von Neumann
  entropy `S_gen`/the area measures) — the `gap = Smax − Svn` (the distinctive `Q_R − S_gen`), and `smax_ge_svn`
  / `gap_nonneg` (`S_vN ≤ S_max`, gap `≥ 0`, via the existing `RecordContract.shannon_le_log_card` Jensen bound;
  equality iff flat). Header carries the full honest scope (postulate not derivation; cites `EntropyNotCardinality`).
  **NEXT → B2: the conditional no-go `svn_underdetermines_smax` (∀ Q N, ∃ spectrum with `Svn = Q` but `Smax`
  arbitrarily large — the area fixes `S_vN`, not the count; mirrors `EntropyNotCardinality`) → B3 capacity of
  entanglement → B4 the bridge postulate + conditional prediction.**
- **2026-07-01 — B2 ✅ DONE (the conditional no-go — the honest core).** Built `svn_underdetermines_smax`: for
  every dimension `N ≥ 1`, a **pure state** (`S_vN = 0`) on `Fin N` has `S_max = log N` — so a fixed von Neumann
  entropy is compatible with arbitrarily large log-count (`N → ∞`). Hence the area (which fixes `S_vN` via JLMS)
  does **not** fix the count `S_max`: a count-based `Q_R` is *independent data*, not derivable from `S_gen`. This
  is the sharpest `EntropyNotCardinality` for the max-entropy capacity — and the result that **forces** the bridge
  to be a *postulate, not a derivation*. Axiom-free std-3, pinned, budget 0 (Dirac state; `negMulLog 0 = negMulLog
  1 = 0`). **NEXT → B3: the capacity of entanglement `capEnt p = ∑ p(log p)² − (∑ p log p)²` (= Var(−log p)) +
  `capEnt_nonneg` + `capEnt_zero_iff_flat` → B4 the bridge postulate `MaxEntropyCapacity` + conditional
  `distinctive_gap`.**
- **2026-07-01 — B3 ✅ DONE (the capacity of entanglement).** Built `capEnt p = ∑ p(log p)² − (∑ p log p)²`
  (= `Var_p(−log p)`, the finite `V_gen` governing the continuum `√V_gen` prediction), `capEnt_eq_variance`
  (= `∑ p(log p − μ)²`, the variance identity, μ = `∑ p log p`), and **`capEnt_nonneg`** (`V_gen ≥ 0` — it's a
  variance, sum of `p·(·)²`). Axiom-free std-3, pinned, budget 0. **NEXT → B4: the bridge postulate `class
  MaxEntropyCapacity` (`Q_R = Smax`, a typeclass NEVER a Lean axiom) + the conditional `distinctive_gap` (under
  the postulate, `Q_R − S_gen = gap ≥ 0`) — the finite shadow of the `√V_gen` prediction; plus `capEnt_zero_iff_*`
  (the "no shift iff maximally mixed" characterization). Then B5 wire-in + point docs at the theorems.**
- **2026-07-01 — B4 ✅ DONE (the postulate + the conditional prediction — the payoff).** Built the bridge
  postulate `class MaxEntropyCapacity p Q_R S_gen` (a **typeclass, NEVER a Lean axiom**: `capacity_is_max`
  `Q_R = Smax`, `sgen_is_vn` `S_gen = Svn`), the conditional theorem **`distinctive_gap`** (GIVEN the postulate,
  `Q_R − S_gen = S_max − S_vN = gap ≥ 0` — the finite shadow of the `√V_gen` prediction), and `capEnt_eq_zero_iff`
  (the shift vanishes iff the surprisal is flat = maximally mixed). Axiom-free std-3, pinned, budget 0. **The
  mathematical content of the frontier is COMPLETE**: the no-go (B2) proves it can't be derived, and B4 packages
  the *one postulate* that makes it distinctive + its conditional, falsifiable consequence. **NEXT → B5 only:
  point the Track-A guardrails (inventory/ledger/site/paper) at the built theorem names
  (`svn_underdetermines_smax`, `distinctive_gap`, `capEnt_nonneg`).**
- **2026-07-01 — B5 ✅ DONE; PLAN COMPLETE.** Pointed the Track-A guardrails (inventory §2, ledger, paper §1.1a,
  website `open-problems`) at the built, axiom-free theorem names (`svn_underdetermines_smax`, `gap_nonneg`,
  `capEnt_nonneg`/`_eq_zero_iff`, `distinctive_gap` under `MaxEntropyCapacity`). Website builds green (66 pages).
  **Both tracks complete.** The honest distinctive-`Q_R` frontier is now a machine-checked package: the **no-go**
  proves it can't be derived; the **max-entropy bridge postulate** (a typeclass, never an axiom) + the
  **conditional prediction** `distinctive_gap` are the one postulate that would make QIQT-H distinctive + its
  falsifiable, capacity-of-entanglement consequence. Honest rail held throughout: *postulate, not derivation*;
  the `√V_gen` coefficient and the value of `G` stay cited frontiers; never claimed QG or that nature picks it.
- **2026-07-01 — numerical illustration (`scripts/qr/maxent_pagecurve.py`).** A standard random-tensor-network /
  Haar Page-curve simulation that *conditionally* checks the postulate's prediction (NOT a claim about nature):
  **(A)** the distinctive shift `gap = S_max − S_vN` and the scale `√V_gen` both **peak at the Page transition**
  (`dA ≈ dB`) and **vanish for near-flat spectra** (small subsystem) — matching `capEnt_eq_zero_iff`; **(B)** the
  shift scales as `√(n·V_gen)` for `n` copies (the second-order / one-shot law), verified by sampling the n-copy
  surprisal (`std(X_n)/√n → √V_gen`; the smooth-max-entropy shift matches `√(n·V_gen)·z_ε` with ratio → 1 as
  `n → ∞`). Reproducible (seeded); plot at `scripts/qr/maxent_pagecurve.png`. Confirms the predicted shift is
  well-defined, spectrum-dependent, and governed by `√V_gen` — turning it into physics still needs the postulate's
  coefficient fixed + an independent holographic comparison (the cited frontier).
