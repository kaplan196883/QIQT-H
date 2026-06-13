# QIQT-H — Status of the Born rule (Gap 3), Lean-verified

**As of:** 2026-06-13. **Scope:** the precise state of "Born from typicality" (GAP 3 of
`48_GAP_PRIZE_List.md`), what is machine-checked, and exactly what remains.

**Lean verification re-run this date (definitive):** `lake build QIQTH.AxiomAudit` → **exit 0, "Build
completed successfully (3829 jobs)", zero `error:` lines**. The named theorems below exist with the stated
signatures; the files carry **no `sorry`/`admit`** (`sorryAx` count 0); the **raw project-axiom count is 0**
— the whole development is axiom-free (budget 0; the earlier "budget 33" of continuum/operator-algebra
interface axioms has been fully retired). Every theorem is covered by a `#print axioms` line in
`QIQTH/AxiomAudit.lean` (795 audited), each reporting only the standard classical foundations
`[propext, Classical.choice, Quot.sound]`.

---

## 0. The one-line answer

The relativistically-covariant **machinery** for Born is built and machine-checked; what is missing is the
**principle that selects the exponent 2**. Born has been *reduced* to a minimal, motivated premise
(non-contextuality + independent preparation + the prepared state), not *eliminated* — and a no-go theorem
shows some such extra premise is unavoidable. It is therefore a **conditional representation theorem, not a
derivation**.

---

## 1. What is machine-checked (axiom-free, no `sorry`)

### A. The finite no-collapse → Born representation
- `QIQTH.PointerValue.existsUnique_actualValue`, `existsUnique_actualHistory` (`ValueSelection.lean`) —
  capacity ⇒ a **unique actual value** per region and a unique actual value-history over `n` trials.
- `QIQTH.BornJoin.ActualEnsemble.pushforward_eq_w` (`BornJoin.lean`) — the actual-history pushforward is the
  **Born product law** `∏ₜ p(hₜ)`.
- `actualHistory_typical`, `actualHistory_typical_world` — atypical frequencies carry Chebyshev-small
  weight.
- `finite_noCollapseBornRepresentation` — the three joined: unique actual history + Born product law +
  typicality, no collapse.

### B. The reductions (each "Born by hand" input replaced by a motivated premise)
- `QIQTH.OneSiteGleason.oneSite_forced` (`OneSiteGleason.lean`) — a **non-contextual** probability
  assignment (a normalized, additive-on-coexistent-effects `EffectMeasure`) is **forced** to `Re tr(ρ Pₐ)`
  via effect-Gleason. *Non-contextuality ⇒ single-trial Born* (derived, not assumed).
- `traceEffectMeasure` — the converse: every density matrix **is** a non-contextual effect measure (the
  premise is concrete and satisfiable).
- `QIQTH.BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality` (`BornJoinGleason.lean`) — full
  representation with `p` **derived** (Born weights no longer free).
- `BornTypicalityFinite.w_history_factorizes` — *product preparation ⇒ trial independence* (named as the
  irreducible input; independence cannot be derived from less — no-signaling alone permits correlations).
- `BornJoin.ActualEnsemble.history_law_unique` — the posited world-measure adds **no observable freedom**;
  the actual-history law is unique given `p` + independence.

### C. The covariant continuum typicality measure (OP3b, 1+1D free field)
- `QIQTH.KolmogorovFiniteFiber.exists_isLimit` (`KolmogorovFiniteFiber.lean`) — a **σ-additive** probability
  measure μ∞ over histories, the general (correlated/entangled) finite-fiber Kolmogorov extension.
- `QIQTH.StateNetMeasure.exists_typicalityMeasure` — state-agnostic: any additive state ω on the effect net
  yields the unique μ∞ (Born marginals, no-signaling).
- `QIQTH.Fock.Localization.Kform_im_eq_zero_of_spacelike` / `K_im_inner_eq_zero_smooth`
  (`Fock/PauliJordan.lean`, `Fock/LocalizedWitness.lean`) — **microcausality**: the full Pauli–Jordan
  oscillatory-cancellation wall, machine-checked.
- `QIQTH.Fock.Localization.localized_typicality_poincare_invariant` + `K_poincare_equivariant` +
  `poincareIsometry_comp` (`Fock/TranslationCovariance.lean`) — μ∞ is invariant under **every connected
  Poincaré element** of `ℝ^{1,1}⋊SO⁺(1,1)`, and `(a,b)↦U(a,b)` is a genuine **group representation**.
- `QIQTH.Fock.…localized_microcausality_nonvacuous`, `K_gaussian_ne_zero` (`Fock/LocalizedWitness.lean`) —
  a concrete, non-degenerate two-region spacelike witness; the construction is non-vacuous.

**Net:** a microcausal, provably-nontrivial, σ-additive, **connected-Poincaré-covariant** typicality
measure on the 1+1D relativistic free field whose marginals are Born — exists and is verified.

---

## 2. The honest verdict, and the no-go

This is a **representation**, not a **derivation**, for one decisive reason:

> **You cannot obtain Born from unitarity + finite capacity alone.** Countermodel: for any α≠1, the law
> `pᵢ^(α) ∝ ‖Pᵢψ‖^{2α}` is *also* support-preserving and certainty-preserving, yet non-Born. So
> "no-collapse + capacity" pins neither the exponent nor additivity; an **extra principle is mathematically
> mandatory.**

The extra principle currently entering is **non-contextuality** (additivity over coexistent effects), which
is exactly Gleason's hypothesis and is precisely what the no-go says capacity cannot supply. The program has
*reduced* Born to {non-contextuality, independent preparation, the prepared state ρ} — the irreducible
inputs any account needs — but has not derived those from the QIQT-H core.

Two further honesty points carried in the Lean docstrings (per GPT-5.5-pro review):
- the trace path `finite_noCollapseBorn_trace` is **circular as a standalone derivation**
  (`traceEffectMeasure` is built *from* ρ via Born; Gleason recovers ρ) — it is an *interface* theorem; the
  non-trace path (`fromNoncontextuality`, independent M) is the genuine reduction;
- the continuum μ∞ is built **from** the Born weights (the quasifree vacuum / `bornPMF` is the per-trial
  input), so it *represents* Born covariantly — it does not *derive* it.

---

## 3. What is left — exactly two conceptual gaps (+ one cited input)

### Gap 3a — A non-circular typicality measure (the decisive one)
μ∞ is presently constructed from the Born weights. A genuine derivation needs a measure μ on the
microscopic initial conditions / λ-histories defined **independently of Born** (a natural / equivariant
measure on the microstate space), plus a theorem that its **typical** frequencies equal `|c_k|²`. Until μ
is specified without reference to the Born weights, this is a target, not a derivation. *Open research
problem; sharply stated.*

### Gap 3b — Non-contextuality from records (ties to H2)
The single-trial law is forced only by a non-contextuality premise — the very thing the no-go forbids
deriving from capacity. Closing it means **deriving non-contextuality from the structure of
capacity-saturated distinguishable records** (the H2 / spectrum-broadcast-structure side): show that the
record algebra of a capacity-saturated region admits only a non-contextual valuation. *Research-grade;
bridges Born back to the H2 crux.*

### Gap 3c — The continuum normal-state realization (cited, not a Lean gap)
ω as a genuine **normal state on a Type III₁** relativistic-QFT net with Bisognano–Wichmann. The 1+1D
free-field construction bypasses most of this explicitly, but the general statement is the shared physics
frontier (Buchholz–Wichmann; Mathlib lacks normal states / predual / Type III). Cited, not formalizable in
current Mathlib.

---

## 4. What would actually close it

- **Closing 3a** (a typicality measure independent of Born + a typicality theorem) would make Born a genuine
  *derivation* within the program — the single highest-value move.
- **Closing 3b** (non-contextuality from records) would connect Born to the H2 crux and remove the last
  assumed premise.
- Either one suffices to upgrade "representation" → "derivation"; the no-go guarantees you need at least one
  of them — capacity alone will never do it.

**Recommendation:** further Lean plumbing on the *representation* yields diminishing returns. The real work
is conceptual: 3a (define the microstate typicality measure) and 3b (records ⇒ non-contextuality). These
are the genuine open problems behind the website's Gap 3 and the `/selection` typicality-circularity note.

---

## 5. Refined plan — the exact missing premise (GPT-5.5-pro cross-check, 2026-06-13)

The §3 split into "3a typicality" and "3b non-contextuality" is **superseded** by a sharper, verified
decomposition. Gaps 3a and 3b are **not parallel**: kinematic typicality collapses into the same
extra-principle requirement as 3b, and that principle can be named exactly.

### The 3-layer chain (replaces 3a/3b)
1. **Records / SBS ⇒ definite, context-independent pointer outcomes** — qualitative single world. Redundant
   broadcast makes all fragment readouts functions of one classical pointer variable `K` (quantum
   Darwinism / spectrum-broadcast structure, Ollivier–Poulin–Zurek; Korbicz et al.). **No quantitative
   Born.**
2. **A measure principle ⇒ `p_k = |c_k|²`** — the one thing actually owed.
3. **Typicality-is-explanatory / self-location ⇒ the one actual λ-history shows Born frequencies** — an
   **irreducible postulate** (à la Dürr–Goldstein–Zanghì), not a theorem. Survives regardless of 1–2.

### The exact missing premise — refinement indifference (the key result)
Records do **not** supply layer 2. The decisive counterexample: the `α=2` record measure
`μ₂(k) = w_k² / Σⱼ w_j²` (with `w_k = ‖P_kψ‖²`) satisfies **every** record fact — definite outcomes,
redundant-fragment agreement, support- and certainty-preservation, pointer-label permutation symmetry,
product independence, and even uniformity on equal weights — yet for `w = (⅓, ⅔)` it returns `(⅕, ⅘) ≠`
Born. So **`SBS records ⇏ Born`**.

What kills the whole `α`-family is precisely **refinement / coarse-graining indifference**: writing the
rule as `p_k = f(w_k)/Σ f(w_j)`, the requirement that splitting an outcome of weight `x+y` into exclusive
sub-records of weights `x, y` leave the coarse event's probability unchanged forces
`f(x+y) = f(x) + f(y)`, hence (with regularity / on rationals) `f(t) = C·t`, hence **Born**. Refinement
additivity *is* the exponent-fixer. Records give the Boolean pointer algebra; they do **not** give this
additivity (the `α=2` measure violates exactly it). Envariance (Zurek) is a valid *conditional* theorem,
but its load-bearing assumption *is* this refinement indifference — so Schlosshauer–Fine's objection stands
unless the premise is added explicitly.

**Reframed open physics question (sharp):** *does the finite-capacity / H2 structure give any reason to
expect refinement indifference?* That, not "a non-circular typicality measure," is the real target.

### The honest Lean sequence (supersedes §4's recommendation)
Build the *isolation* — prove exactly what's owed and that records don't supply it:
1. `SBS_to_BooleanRecordAlgebra` — exact SBS support/orthogonality ⇒ all redundant readouts are functions
   of one classical `K` (layer 1).
2. `AlphaRecordCountermodel` — the `α=2` measure satisfies all layer-1 facts but violates Born and
   refinement additivity. **The load-bearing negative result: `records ⇏ Born`.**
3. `RefinementIndifference_implies_Born_rational` — uniformity on equal fine-records + additivity under
   coarse-graining ⇒ `p_k = m_k/M` (Zurek's fine-graining stripped to its real assumption).
4. *(optional)* the Hilbert-level envariance swap identity; then irrational extension by continuity.

This makes the contribution sharp and unattackable: *we prove which extra axiom Born needs (refinement
indifference), that the QIQT-H record structure does not supply it, and that with it Born follows.* Lean
file: `QIQTH/RefinementBorn.lean`.

### Status (this date) — Steps 1–3 done, axiom-free
- **Step 1** `QIQTH/SBSBoolean.lean` — layer-1 objectivity, Born-free (orthogonality only):
  `record_unique` (a nonzero state can't lie in two orthogonal sectors) ⇒ `fragments_co_referential`
  (redundant SBS readouts agree ⇒ functions of one classical pointer `K₀`). Definiteness, no Born weights.
- **Steps 2–3** `QIQTH/RefinementBorn.lean` — `alphaSq_ne_born` (records ⇏ Born), `additive_fMeasure_eq_born`
  (refinement additivity ⇒ Born), `alphaSq_refinement_violation` (the exact failing premise).

All built green, `#print axioms` = standard-three.

### Route 4 — no-signaling under refinement (this date, GPT-5.5-pro cross-check)
Both gpt-5.5 and gpt-5.5-pro independently confirmed: capacity / H2 / χ_R do **not** force refinement
additivity (the `α`-family can be decorated with *every* QIQT-H structure — capacity saturation, SBS,
definiteness, *and* product independence, since `(w_i v_j)^α = w_i^α v_j^α`). The χ_R route is a dead end:
relative entropy gives `D = Σ w_k χ_R^k − H(w) ≈ Q_R − H(w)`, a Shannon/KL (`w·log w`) term, not Born-linear;
and a low-weight branch still holds a capacity-saturated record (`χ_R^k ≈ Q_R` independent of `w_k`). The
`(Φ,λ)` *determinism makes it worse* (a `λ∈[0,1]` interval-partition realises any `α` deterministically).

The cleanest, least-ad-hoc form of the missing premise is **no-signaling under remote refinement**: if a
spacelike-separated choice to refine an ancillary record could change a local coarse frequency, that is
operational signaling. Machine-checked (`QIQTH/RefinementBorn.lean`, axiom-free):
- `RefinementNatural f` — the coarse prob of a merged outcome = sum of the fine probs (`p ∝ f`).
- `refinementNatural_additive` — **no-signaling + `f>0` ⇒ `f(x+y)=f x+f y`**; compose with
  `additive_fMeasure_eq_born` ⇒ Born. So *no-signaling under refinement ⇒ Born*.
- `sq_not_refinementNatural` — the `α=2` rule is **not** refinement-natural (it would signal); the
  `α`-family is exactly excluded by no-signaling.

Also machine-checked: `id_refinementNatural` (Born *is* refinement-natural) — completing the **iff: among
rules `p ∝ f`, refinement-natural ⟺ Born.**

**Net honest claim:** QIQT-H reduces Born to **no-signaling under record refinement** — an independently
mandatory relativistic principle, not an ad-hoc measure postulate — and machine-checks that it suffices and
that nothing weaker (capacity/χ_R/determinism) does.

### Does the existing microcausality discharge it? — investigated, NO (directionality finding)
The corpus's no-signaling theorems (`NoSignalingGeneral.bipartite_no_signaling`: `∑_b tr(ρ(E⊗F_b)) =
tr(ρ(E⊗1))`; `FreeFieldNet.bornNet_no_signaling`: the product-Born marginal `∑ p(y)p(·) = p(y)`) are the
**converse direction** — `Born ⇒ no-signaling`. They *presuppose* the Born/trace functional and show it is
no-signaling **because the trace is linear / the measure normalised**. They do **not** constrain the
candidate `f`-family, so they do **not** discharge the route-4 premise (`no-signaling ⇒ Born`), which is the
genuinely load-bearing converse. `id_refinementNatural` is their abstract counterpart (easy direction);
`refinementNatural_additive` is the hard one they do not give. So a genuine derivation must impose
no-signaling on the **selector `λ`'s marginals** (not on the already-Born functional) — i.e. show the actual
`(Φ,λ)` outcome statistics are remote-refinement-invariant from microcausality of the net. That is the real
remaining target; the existing theorems confirm consistency but cannot close it.

### The selector (λ) layer — machine-checked (`QIQTH/SelectorRefinement.lean`, axiom-free)
Formalises the marginal of a deterministic selector over a fixed, Born-agnostic typicality measure `μ`
(`marg μ sel k = μ`-mass of `{ω : sel ω = k}`), and proves the two pieces GPT-5.5-pro identified:
- **The Born-free bridge** `readout_invariant_marg`: if a remote refinement `R` leaves the local readout
  unchanged (`XL ∘ R = XL` — selector-level microcausality), the local marginal is invariant — selector
  no-signaling, with **no** Born/trace input. **This `XL∘R=XL` is exactly the Gap-2 bridge a genuine
  derivation needs**; it does not follow from operator-net microcausality automatically (one must show the
  actual *selector* commutes, not just the observables). No Bell/Fine obstruction (context + its refinement
  are compatible).
- **The separation / independence result** `Countermodel.alphaSq_selector_signals` (by `decide`): a
  deterministic α=2 selector over a fixed **uniform** measure on 15 microstates has coarse cell `12` for a
  merged outcome but fine cells `5,5` (total `10`); `12 ≠ 10`, so selector no-signaling **fails** — while the
  trace no-signaling theorem is untouched. **Proves existing microcausality does NOT force selector
  no-signaling**, so Gap 3 is genuinely *not* already closed; it reduces to the `XL∘R=XL` bridge (Gap 2).

**Bottom line:** `Born ⟺ selector-marginal no-signaling` (machine-checked iff at the rule level), and
selector no-signaling `⟸` the microcausal bridge `XL∘R=XL`, which is **not** supplied by the operator net
alone — it is a statement about the actual `(Φ,λ)` dynamics. **Gap 3 (Born) thus reduces to a precise
Gap-2 (dynamical-realization) condition**, and that reduction is now axiom-free in Lean. Whether the
`(Φ,λ)` dynamics actually delivers `XL∘R=XL` is the open frontier (and, per the Bell/Fine caveat, it can
only hold at the *averaged-marginal* level, not as a pointwise local valuation — consistent with
QIQT-H being contextual-but-no-signaling, [[qiqth_observer_is_wavefunction]] / the not-superdeterministic
stance).

## 6. The Gap-2 roadmap — how the dynamics could deliver the bridge (GPT-5.5-pro, 2026-06-13)

**Corrected reduction (three premises, not two):**
> **Born ⟸ selector-locality + local Gleason/Busch additivity + state-anchoring/affinity.**

The two-refinement decomposition (verified non-circular by pro):
- **Remote refinement** (Bob splits his outcome): Alice's marginal unchanged ⟸ **selector-locality** — the
  local marginal factors through the local reduced state `ρ_A`. Machine-checked: `local_factor_remote_invariant`
  (`SelectorRefinement.lean`, milestone 1) — selector-locality + `ρ_A`-preservation ⇒ remote no-signaling.
- **Local refinement** (Alice splits her own outcome): additivity over Alice's orthogonal local projectors =
  **Gleason/Busch** on `A(O_A)` ⇒ `g(ρ_A,P) = tr(σ(ρ_A)P)`.

**Two failure modes pro flagged (the corrections to the naive sketch):**
1. **Microcausality ⇏ selector-locality.** Operator-net locality gives `ρ_A`-invariance and Born-*linear*
   expectations, **not** invariance of the deterministic selector's μ-measure. Selector-locality is an extra
   *equilibrium/screening* condition on `(Φ,λ)` (a Bohmian-quantum-equilibrium analogue) — the genuine Gap-2
   content, not free from microcausality. And it is **not** Born by itself: `g(ρ)=tr(ρ²/tr(ρ²)·P)` is
   selector-local but non-Born.
2. **Local Gleason ⇏ Born.** It gives `tr(σ(ρ)·)` for *some* density-op map `σ`, not `σ(ρ)=ρ`. **State-anchoring**
   (affinity under classical mixtures + pure-state certainty) is the extra step forcing `σ(ρ)=ρ`.

**Weak vs strong locality (the Bell guardrail).** "Alice's record reads only local data" has two meanings:
the **weak/marginal** form (`μ`-marginal factors through `ρ_A`) is Bell-compatible and is what we want; the
**strong/pointwise** form (the actual outcome is a local function of local hidden data) is Bell-*forbidden*
(deterministic pointwise locality + measurement independence ⇒ CHSH ≤ 2, violated by QM). So the target is the
weak μ-pushforward form; `λ` stays *ontically contextual*, only the marginals are local. (Same structure as
Bohm/DGZ: equilibrium no-signaling at the marginal level, nonlocal individual outcomes.)

**Corrected Lean ladder:**
1. `selector-locality ⇒ remote no-signaling` — **done** (`local_factor_remote_invariant`).
2. local additivity ⇒ `g(ρ,E)=tr(σ(ρ)E)` (reuse `OneSiteGleason.oneSite_forced`); **then** affinity +
   pure-state certainty ⇒ `σ(ρ)=ρ` (state-anchoring) — medium, reuses existing effect-Gleason.
3. **derive selector-locality from a `(Φ,λ)` λ-dynamics model**, as an exact μ-pushforward / cylinder-event
   theorem `(π_A)_* μ_{ρ_AB,y} = ν_{ρ_A}` — the real Gap-2 build (a Lean model of the selection dynamics
   respecting the local-algebra/causal structure). Plus a **Bell guardrail** theorem (pointwise-local
   deterministic selector + measurement independence ⇒ CHSH ≤ 2) so the derivation can't accidentally prove a
   locality too strong to reproduce quantum correlations.

**Honest status of the literature (pro):** there is **no** known theorem "microcausal deterministic HV +
fixed equivariant μ ⇒ Born local marginals." The closest is Bohm/DGZ (equivariant `|Ψ|²` ⇒ equilibrium
no-signaling — but `|Ψ|²` *is* Born) and Valentini (non-equilibrium ⇒ signaling, so equilibrium is essential);
relativistic collapse (Tumulka rGRWf, Bedingham) builds Born in by construction. So step 3 is genuine new
territory, not a citation away.

**Net:** the global "measure principle" is now **localized** — to local operational non-contextuality
(Gleason, its most defensible form) plus a *derivable-in-principle* selector-locality (μ-equilibrium) plus
state-anchoring. Steps 1 done, 2 reuses existing machinery, 3 is the real Gap-2 frontier.

## 7. Milestone-3 plan + first attack (this date)

Milestone 3 = "derive selector-locality from `(Φ,λ)` dynamics" is the real Gap-2 program. Planned in phases,
each an axiom-free Lean checkpoint:

**Phase 3a — the equilibrium core (DONE).** The honest re-statement of the bridge: the Bell-compatible route
asks not for pointwise readout-locality (`XL∘R=XL`, which Bell forbids — see 3b) but for the remote dynamics
to **preserve the typicality measure** (equivariance). Machine-checked: `equivariant_marg_invariant`
(`SelectorRefinement.lean`) — a `μ`-preserving bijection `R` (the remote refinement) leaves **every**
local-readout marginal invariant, with `λ` allowed to be globally correlated. **This isolates the exact
load-bearing Gap-2 input: `(R)_*μ = μ`** (Bohmian-quantum-equilibrium / DGZ equivariance; Valentini:
non-equilibrium ⇒ signaling, so equivariance is essential). It does *not* follow from operator-net
microcausality (which is about commuting observables, not the measure).

**Phase 3b — the Bell guardrail (ALREADY IN THE CORPUS).** `Bell.chsh_pointwise` + the CHSH-LHV bound
`|CHSH| ≤ 2` (`Bell.lean`) vs. the quantum violation `2√2` (`Tsirelson.lean`) make the guardrail precise: a
*pointwise-local deterministic* selector is a local hidden-variable model, hence `|CHSH| ≤ 2`, hence cannot
reproduce QM. So the derivation **must** use the weak/equivariance route (3a), never strong factorization.
`λ` is ontically contextual; only its marginals are local. No new build needed — cite these.

**Phase 3c — derive equivariance from a concrete `(Φ,λ)` dynamics (THE FRONTIER, multi-step).** The remaining
question is sharp: *does the QIQT-H selection dynamics preserve a fixed, Born-agnostic `μ`?* Sub-steps:
1. A finite Lean model of the selection map: global state, microstate space `Ω`, a deterministic selector
   built from the unitary evolution + the record/SBS structure, and a remote-refinement action `R` on `Ω`.
2. Prove the action `R` is `μ`-preserving for the *intended* dynamical `μ` — i.e. exhibit the equivariance
   `(R)_*μ = μ` from the unitarity + microcausality of the model (the analogue of DGZ's equivariance proof
   for `|Ψ|²`, but for the QIQT-H selector). **This is the load-bearing, genuinely-open step.**
3. Feed it through `equivariant_marg_invariant` ⇒ selector no-signaling ⇒ (with §6's local-Gleason +
   state-anchoring) Born.
   The honest risk (pro): if the only available equivariant `μ` is `|Ψ|²` itself (as in Bohm), step 2 is
   circular; the non-circular hope is a Valentini-style relaxation of a Born-agnostic `μ` to equivariance
   under the dynamics — itself contested and a research program.

**Status:** 3a done (axiom-free), 3b in corpus, 3c is the open Gap-2 frontier — now reduced to the single
sharp question "is the QIQT-H selection dynamics `μ`-equivariant?", with `equivariant_marg_invariant` waiting
to consume the answer.

**3c scaffold + first model result** (`QIQTH/SelectionDynamics.lean`, axiom-free): the `SelectionModel`
structure (microstate space + Born-agnostic `μ` + deterministic selector + bijective remote action `R` +
equivariance `(R)_*μ=μ`); `SelectionModel.no_signaling` (wires any equivariant model to 3a); and `uniformModel`
— the Born-agnostic instance where uniform `μ` is preserved by **any** bijection, so the remote no-signaling
half is reachable with a measure assuming nothing about Born.

**★ `born_from_uniform` — uniform typicality REPRODUCES Born (machine-checked).** A deterministic selector over
the *Born-agnostic uniform* measure with `M·w_k` fine microstates per outcome `k` has normalised marginal
exactly `w_k`. This is the Zurek envariance route realised as a selection model: uniform counting ⇒ Born,
axiom-free, with the **sole residual made explicit** — that the fine-graining encodes the weights
(`count = M·w_k`), which is precisely the refinement-additivity premise of `RefinementBorn`. So both the
remote half (no-signaling, via equivariance) and piece **(i)** (Born marginals, via fine-graining) now have
concrete machine-checked model instances over a Born-agnostic `μ`.

The genuinely open piece is **(ii)**: that the *actual* dynamical `μ` is both equivariant **and** fine-grains
with `count = M·w_k` *as a consequence of the unitary/record dynamics* rather than by stipulation — i.e. a
concrete microcausal selection model deriving the weight-encoding (the DGZ/Valentini-type theorem). The
explicit `FineSpace` (`Σ k, Fin (m k)`) is stubbed for the next increment (deriving its fiber cardinality
`= m k` needs a short `Sigma.fst`-reduction lemma).
