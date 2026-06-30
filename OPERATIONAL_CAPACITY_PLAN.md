# Operational record-capacity — plan (the Holevo–Bekenstein bound) + the honesty guardrail

**Status:** ACTIVE (2026-06-30). **Origin:** an adversarial GPT-5.5-pro consult on whether QIQT-H's *finite-count*
capacity layer can be made non-trivial. **Verdict (take as settled):**

- **Literal finite regional cardinality is provably DEAD** relative to the entropy layer — `EntropyNotCardinality`
  already proves entropy ⇏ count (∞ many orthogonal pure states have `S=0` and are exactly distinguishable; smear
  them and ∞ many stay ε-distinguishable). You cannot derive a finite record count from `S(ρ_R) ≤ Q`.
- **The only sound "operational count" is a Holevo capacity, not a cardinality:** from a fixed-reference relative
  entropy bound `D_{A(R)}(ω‖σ_R) ≤ Q`, the number of records ε-decodable by a common POVM obeys
  **`log M_ε ≤ (Q + h₂(ε)) / (1 − ε)`** (Holevo + Donald + Fano); exact records (`ε=0`) ⟹ `M ≤ e^Q`. This **survives**
  `EntropyNotCardinality` because it bounds *recoverable mutual information*, not support cardinality.
- It becomes a genuine *finite number* only under an **energy constraint** (`Tr(ρH) ≤ E`, finite `Z(β)`):
  `log M_ε ≤ S_max(E)/(1−ε)`, `S_max(E) = inf_β {βE + log Z(β)}` — i.e. the **Bekenstein bound / microcanonical
  density of states**. Standard holography; the finiteness is the *imported* energy cutoff, **not** derived from the
  area law.
- **Honest consequence:** QIQT-H's count layer is **not derivable** from its own entropy/area postulate; its
  operational form is **Holevo/Bekenstein-class — no new physics** — *unless* the program can derive a `Q_R`
  *different* from standard generalized entropy (the option-3 frontier, NOT in scope here).

**This plan does two things:** (Track A) make that honesty explicit across the docs; (Track B) build the
operational Holevo record-capacity theorem in Lean — a real, non-vacuous upgrade of the count layer from
"finite-dim toy postulate" to "operational distinguishability bound," clearly labelled Bekenstein-class.

**Honest invariants (enforce every increment):** NO `sorry`; `#print axioms` = standard-3; budget 0; NEVER claim
this derives the count from the area law, derives a new `Q_R`, or is new physics beyond Holevo/Bekenstein; the
`EntropyNotCardinality` no-go is cited as the guardrail; the option-3 "new `Q_R`" target stays a **cited frontier**.

---

## Track A — the honesty guardrail (doc edits, cheapest first)

Add, consistently, the statement *"the finite-record-count layer is **not derivable** from the entropy/area bound
(`EntropyNotCardinality`); its operational form is the **Holevo/Bekenstein** distinguishability bound
`log M_ε ≤ (Q+h₂(ε))/(1−ε)` — Bekenstein-class, not new physics; QIQT-H is distinctive here only if it derives a
`Q_R` differing from standard generalized entropy, which it does not (cited frontier)."*

- **A-1 `LEAN_RESULTS_INVENTORY.md` §2** — extend the two-layer ⚠-note with the "count not derivable / operational
  = Holevo–Bekenstein" guardrail + a pointer to the new theorem once built.
- **A-2 `CLAIMS_LEDGER.md`** — add a row (C-section) for the operational bound + update the "claims we DON'T make"
  guardrail (✗ "the count layer is derived from the area law"; ✗ "the operational capacity is new physics").
- **A-3 website** (`open-problems` and/or `theory`/`reach`) — one honest paragraph: the count layer needs an
  energy/Bekenstein import; operationally it's the Holevo bound; distinctive only via a new `Q_R` (open).
- **A-4 paper** (`QIQT_Foundations_Paper.md` §1.1a or §11.4) — the same, as a short scoped note.

PASS = every surface states the count-layer status the same way, with `EntropyNotCardinality` cited.

---

## Track B — the Lean operational record-capacity theorem

New file: **`QIQTH/OperationalCapacity.lean`** (finite-dim / Type-I model first — honest shadow, exactly as the
P4-MICRO floor is). Build bottom-up; each phase an axiom-free green checkpoint.

**Existing pieces to reuse (verified):** `Donald.lean` (Donald's identity), `HolevoCoarseGraining.lean`
(`I_Hol_nonneg`, `donald_deficit`, `holevo_coarse_le_fine`), `ShannonFano.lean` (partial Fano-step:
`H_bound_imp_max_lb`, `single_record_certain`), `QuantumRelativeEntropy`/`QuantumEntropy` (relEntropy, vonNeumann,
`shannon_le_log_card`, `negMulLog`), `RelEntPositivity`/Klein.

### Phase B0 — binary entropy `h₂` + the discrimination model *(scaffolding, tractable)*
- `binEntropy (ε) := negMulLog ε + negMulLog (1-ε)` with `binEntropy_nonneg`, `binEntropy_le_log2`,
  `binEntropy_zero` (`h₂(0)=0`). (Reuse `negMulLog` lemmas.)
- A **record-discrimination model** structure: a finite record set `ι`, states `ρ : ι → Density H`, a uniform prior,
  a decoding POVM `E : ι → (H →L H)` (PVM/effects, `∑ E i = 1`, `0 ≤ E i`), and average success
  `psucc := (1/|ι|) ∑ i, ⟪ρ i, E i⟫ ≥ 1 − ε`.

### Phase B1 — the quantitative **Fano inequality** *(the main NEW piece; classical, finite)*
`fano_inequality`: for the induced input→decoded-output channel with error `ε`, the conditional entropy obeys
`H(X|Y) ≤ binEntropy ε + ε · log(|ι| − 1)`; equivalently the mutual information
`I(X;Y) ≥ (1 − ε)·log|ι| − binEntropy ε`. Route: standard grouping/data-processing on Shannon entropy; `ShannonFano`
already has the `δ=0` and Rényi-∞ pieces — extend to the quantitative bound. *(If the full `ε log(M−1)` term proves
heavy, the weaker `H(X|Y) ≤ binEntropy ε + ε log|ι|` suffices for the capacity theorem and is easier.)*

### Phase B2 — accessible information ≤ Holevo χ ≤ Q *(reuse + glue)*
`accessible_le_holevo`: the decoded mutual information `I(X;Y) ≤ χ(ensemble)` (Holevo bound — the measurement
data-processing form), and `holevo_le_relEnt`: `χ ≤ Q` when each `D(ρ_i‖σ) ≤ Q` via Donald's identity
(`χ = ∑ p_i D(ρ_i‖ρ̄) ≤ ∑ p_i D(ρ_i‖σ)`, the Donald deficit ≥ 0 already in `HolevoCoarseGraining.donald_deficit`).

### Phase B3 — **the capstone**: the operational record-capacity bound
`operational_record_capacity`: in the discrimination model with relative-entropy bound `Q` and success `≥ 1−ε`,
**`(1 − ε)·log|ι| ≤ Q + binEntropy ε`**, i.e. `log M_ε ≤ (Q + h₂(ε))/(1−ε)`. Immediate from B1 (Fano) + B2 (Holevo).
Corollary `exact_record_capacity` (`ε = 0`): `log|ι| ≤ Q`, i.e. `|ι| ≤ e^Q`.

### Phase B4 — the energy / Bekenstein form *(the honest "finite number" version)*
`microcanonical_capacity`: given a finite-rank energy cutoff `P_{H≤E}` of rank `d(E)` (or finite `Z(β)` with
`Tr(ρH) ≤ E`), exact records satisfy `M ≤ d(E)` and `log M_ε ≤ S_max(E)/(1−ε)` with
`S_max(E) = inf_β (βE + log Z(β))`. **Docstring states explicitly: this is the Bekenstein/microcanonical bound; the
finiteness is the *imported* energy cutoff, NOT derived from the area law.**

### Phase B5 — wire-in + audit
Add to `QIQTH.lean` imports + `AxiomAudit.lean` (`#print axioms` per terminal theorem, expect standard-3); run
`scripts/axiom_budget_check.sh` (budget 0). Update Track A docs to point at the now-built theorem names. Add the
**option-3 frontier** note (deriving a `Q_R` ≠ standard generalized entropy from QIQT-H dynamics) as cited-not-built.

PASS = `operational_record_capacity` + `exact_record_capacity` proved axiom-free; the energy form built or honestly
checkpointed; every docstring labels it Holevo/Bekenstein-class, not new physics.

---

## Verification (per increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.OperationalCapacity` green; `#print axioms` standard-3;
`bash scripts/axiom_budget_check.sh` budget 0; ONE commit per increment with the `Co-Authored-By: Claude Opus 4.8
<noreply@anthropic.com>` trailer; push via schannel; update the Progress log below. Website edits build green
(66 pages). NO `sorry`. Never claim QG, the value of G, a new `Q_R`, or new physics.

## Honest scale
B0–B3 are days (finite-dim info theory, most pieces exist; Fano B1 is the real lemma). B4 (energy/Bekenstein) is
moderate (finite-rank cutoff is easy; the `inf_β` Legendre form is more). The whole thing is an **honest upgrade of
the count layer to an operational Holevo bound** — genuinely buildable, genuinely Bekenstein-class, and genuinely
*not* new physics. The distinctive-content question (option 3) is untouched and stays the cited frontier.

## Progress log
- **2026-06-30** — plan created from the GPT-5.5-pro consult. Verified the reusable pieces exist (`Donald`,
  `HolevoCoarseGraining`, `ShannonFano`, relEntropy/Shannon).
- **2026-06-30 — Track A ✅ DONE (the honesty guardrail, all 4 surfaces).** Added the "count layer NOT derivable
  from the entropy/area bound; operational form = Holevo–Bekenstein, NOT new physics; distinctive only via a new
  `Q_R` = cited frontier" guardrail to: inventory §2 (extended the two-layer ⚠-note), `CLAIMS_LEDGER.md` (new row
  C7 + two "claims we DON'T make" guardrails), website `open-problems.md` (the fork div), and paper §1.1a (the
  two-layer note). Website builds green (66 pages). `EntropyNotCardinality` cited everywhere as the guardrail.
  **NEXT → Track B Lean (B0 binEntropy + discrimination model → B1 quantitative Fano → B2 Holevo glue → B3
  capstone → B4 energy/Bekenstein → B5 wire-in).**
- **2026-06-30 — B0 ✅ DONE** (`QIQTH/OperationalCapacity.lean`, axiom-free std-3, wired into `QIQTH.lean` +
  `AxiomAudit.lean`, budget 0). Built: `binEntropy` (h₂ in nats) with `binEntropy_zero/_one/_symm/_nonneg`; the
  `RecordModel` finite record-discrimination structure (`succ`/`avgSucc`/`avgErr`); and the exact (ε=0) capacity
  helper `exact_record_capacity` (`log M ≤ Q ⟹ M ≤ e^Q`, exp-monotonicity — the Bekenstein-class count bound's
  ε=0 corollary). Header carries the full honest scope (Holevo/Bekenstein-class, NOT new physics, does not derive
  the count from the area law, cites `EntropyNotCardinality`). **NEXT → B1: the quantitative Fano inequality
  `H(X|Y) ≤ binEntropy ε + ε·log(M−1)` (the main new lemma — heavier; extend `ShannonFano`'s partial content) →
  B2 accessible ≤ Holevo χ ≤ Q (reuse Donald/HolevoCoarseGraining) → B3 capstone.**
- **2026-06-30 — B1-exact ✅ DONE** (the exact ε=0 capstone, axiom-free std-3, pinned, budget 0). Built
  `H_uniform` (the equiprobable record law has `H = log M` — the Holevo info of `M` perfectly-distinguishable
  equiprobable records) and `exact_distinguishable_capacity`: a capacity bound `Q` on that distinguishable
  ensemble (`χ = log M ≤ Q`) gives the record-**count** bound `M ≤ e^Q`. This is the honest ε=0 operational
  record-capacity theorem, fully self-contained — `Q` enters as the carried Holevo/relative-entropy bound, and
  the count bound holds because `Q` bounds the *Holevo info of the distinguishable ensemble* (= `log M`), NOT
  merely some `S(ρ_R) ≤ Q` (which `EntropyNotCardinality` forbids from bounding the count). Docstring keeps the
  Bekenstein-class / not-new-physics / not-from-area-law scope.
  **NEXT → B1-full: the ε > 0 robustness — the quantitative Fano inequality `H(X|Y) ≤ h₂(ε) + ε·log(M−1)`.
  ⚠ HONEST BLOCKER NOTE: this needs conditional/joint Shannon-entropy infrastructure (joint law, `H(X,Y)`,
  `H(X|Y)`) that neither `ShannonFano` nor Mathlib packages — a real multi-lemma build, not a 10-min increment.
  Options for the loop: (i) build the minimal joint/conditional-entropy layer then Fano; (ii) land the weaker
  `H(X|Y) ≤ h₂(ε) + ε·log M` form (suffices for the capacity bound, slightly easier); (iii) if both stall,
  checkpoint and proceed to B4 (the energy/Bekenstein finite-rank cutoff, which is independent and may be more
  tractable). Then B2 (Holevo glue) + B3 (full capstone).**
- **2026-06-30 — B1-route chosen + B1.1 ✅ DONE (GPT-5.5-pro consult).** Consulted on the shortest rigorous Lean
  path; verdict: the **confusion-matrix Fano-free route** is shortest — avoid conditional entropy entirely, bound
  the decoding confusion matrix's mutual info below via ONE binary coarse-graining to "decoded correctly," all
  reducing to `Real.log_le_sub_one_of_pos`. Built the workhorse **`kl_nonneg`** (classical Gibbs inequality
  `∑ aᵢ log(aᵢ/bᵢ) ≥ 0` for finite distributions, via the termwise bound `aᵢ−bᵢ ≤ aᵢ log(aᵢ/bᵢ)`). Axiom-free
  std-3, pinned, budget 0. **NEXT (confusion-matrix route, in order): `logsum_le` (log-sum, from `kl_nonneg` by
  normalizing) → `kl_partition_two` (binary coarse-graining) → `diag_mass_product` (`∑ Rᵢᵢ = 1/M`, the killer
  simplification) → `binaryKL_success_bound` (`D₂(s‖1/M) ≥ (1−ε)log M − h₂(ε)`) → `confusionMI_ge_fano` →
  capstone `record_capacity_of_confusionMI_bound`: `(1−ε)·log M ≤ Q + binEntropy ε`.**
- **2026-06-30 — B1.2 ✅ DONE.** Extracted `mulLog_div_lower` (the termwise engine `x − y ≤ x·log(x/y)`, from
  `Real.log_le_sub_one_of_pos`) and defined `binaryKL` (`D₂(s‖r)`) + proved `binaryKL_nonneg` (two applications
  of the engine, lower bounds sum to 0). Axiom-free std-3, pinned, budget 0. **NEXT → `binaryKL_success_bound`:
  `binaryKL s (1/M) ≥ s·log M − binEntropy(1−s)` (M ≥ 2). NOTE: needs s=0 / s=1 / s∈(0,1) case handling because
  `log(s·M) = log s + log M` fails at s=0 — deliberate, not rushed. Then `logsum_le` (from `mulLog_div_lower`,
  unnormalized form) → `kl_partition_two` → `diag_mass_product` → `confusionMI_ge_fano` → capstone.**
