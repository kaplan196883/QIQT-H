# B2 — seeded-fault instrument ablation (reproducible record)

Backs cs.AI paper §3.8. A controlled set of 7 declarations (5 seeded faults + 2 sound controls)
is run past each loop instrument; the deterministic instruments are scored by their actual
specification (verified by running their logic), and the **reviewer** config is a single **blind**
GPT-5.5-Pro pass (it was not told which items are faults).

## The fault set (D1–D7)

| ID | Kind | Intended verdict |
|---|---|---|
| D1 | clearly-labelled BW interface axiom | SOUND (acceptable cited assumption) |
| D2 | Gleason-type axiom omitting positivity | UNSOUND — false (the §4.5 Case-1 pattern) |
| D3 | axiom with `(h_alg : True)` antecedent, false conclusion | UNSOUND — inconsistent (the §4.5 Case-2 pattern) |
| D4 | ordinary proved lemma | SOUND |
| D5 | theorem whose hypothesis *is* the conclusion (Born) | UNSOUND — circular / over-strong |
| D6 | `def P := True` + `axiom : P` | UNSOUND — vacuous |
| D7 | theorem closed by `sorry` | UNSOUND — incomplete |

(Exact Lean text archived in git history of `paper_cs_ai/_faults_scratch.lean`, commit prior to deletion.)

## Deterministic instruments (verified by running each instrument's logic)

- **Compiler (green `lake build`)**: every well-typed declaration builds; `sorry` only warns. Catches
  **0/5** faults as build failures.
- **Axiom budget** (`axiom_budget_check.sh`: fail on `sorryAx`, or any `^axiom ` over budget 0):
  flags D1, D2, D3, D6 (each adds an `axiom` → count > 0) and D7 (`sorryAx`). But this flags an
  *added axiom for disclosure* — it cannot tell a **false** axiom (D2) from a **legit** one (D1) —
  and it **misses D5** (an over-strong hypothesis adds no axiom and no `sorry`).
- **Vacuity lint** (`vacuity_lint.sh`: grep `:= True | ↦ True | → True | ,True$`): catches **D6 only**
  (`def IsTensorMultiplicative … := True`). It does **not** match D3's `(h_alg : True)` *binder* form
  (verified) — the lint covers definitional `:= True` vacuity, not arbitrary trivial binders.

Net: the two faults that no deterministic instrument identifies *as unsound* are **D2** (false but
well-typed axiom — budget sees only "an axiom") and **D5** (circular/over-strong hypothesis —
invisible to all three).

## Reviewer config (blind GPT-5.5-Pro, single pass)

Verbatim verdicts:

- D1: **SOUND** — explicit BW interface axiom; acceptable scoped assumption.
- D2: **UNSOUND** — naive Gleason lacks positivity; finite additivity + certainty don't characterize Born.
- D3: **UNSOUND** — instantiate α=β=Bool, r=id, T=not ⇒ false = true.
- D4: **SOUND** — exact application of `decohere_orthogonal`; no extra assumption.
- D5: **UNSOUND** — circular: the hypothesis is precisely `SatisfiesBorn`'s defining Born equality.
- D6: **UNSOUND** — predicate is `True`; proves only a vacuous placeholder.
- D7: **UNSOUND** — uses `sorry`; unchecked, violates policy.

**Score:** 5/5 faults caught (D2, D3, D5, D6, D7); 0/2 sound controls misflagged (D1, D4 correctly
SOUND). The two faults invisible to the deterministic instruments — D2 and D5 — were both caught.

## Detection matrix

| | D1 sound | D2 false ax | D3 incons | D4 sound | D5 circular | D6 vacuous | D7 sorry |
|---|---|---|---|---|---|---|---|
| Compiler green | builds | builds | builds | builds | builds | builds | warns |
| + Axiom budget | flags* | flags* | flags* | — | **miss** | flags* | catch |
| + Vacuity lint | — | — | **miss** | — | **miss** | catch | — |
| + Reviewer | sound✓ | **catch** | **catch** | sound✓ | **catch** | catch | catch |

`flags*` = budget flags an added axiom for *disclosure* (correct for D1, but does not identify D2/D3
as unsound). The reviewer catches the semantic residue (D2, D5) the structural instruments cannot.

## Honesty caveats

- n = 7 (5 faults, 2 controls); a **single** blind pass; a **single** model/version (GPT-5.5-Pro);
  faults hand-designed and relatively clear-cut. This is an **indicative** catch-rate profile, not a
  definitive rate, and there is selection bias toward legible faults.
- Subtler faults are harder: the historical §4.5 Case 1 took the reviewer **three** passes, so a
  perfect single-pass score here should not be read as 100% on arbitrary faults.
- The deterministic-instrument cells are determinate (verified against each script's logic); the
  reviewer cell is stochastic and version-specific.
