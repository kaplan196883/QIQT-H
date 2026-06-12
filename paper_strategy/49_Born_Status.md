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

### Status of step 2 (this date)
`QIQTH/RefinementBorn.lean` started — the `α=2` countermodel and the additivity ⇒ Born positive theorem;
see that file. The conceptual residue (whether capacity motivates refinement indifference) is the genuine
open problem.
