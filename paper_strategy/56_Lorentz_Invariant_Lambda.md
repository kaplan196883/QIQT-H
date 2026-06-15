# 56 — Lorentz-invariant λ: no-foliation ⟹ a covariant MEASURE (not a selector) (2026-06-14)

Question: what Lorentz-invariant constructions of the actuality selector λ are possible, given the
commitments — single absolute world, NO preferred foliation, NO superdeterminism, Lorentz-invariant,
Bell-nonlocal, no collapse? Consult (gpt-5.5; pro 520'd) checked against standard rep theory / AQFT
contextuality results + our machine-checked 1+1D measure, per Lean > papers > pro.

## The elimination (strong lore, NOT a clean theorem)

The commitments rule out Many-Worlds (single outcome), superdeterminism (rejected), preferred-foliation
Bohm/GRW (no foliation), and Lorentz-invariant stochastic collapse / Tumulka rGRWf (no collapse). What's left
is the **retrocausal / all-at-once block** branch — or give up the absolute world (relational / RQM / QBism).
This is *strong lore + conditional no-gos* (Bell/Fine 1982 / Kochen–Specker / Gisin 2011 / Wharton–Argaman
RMP 2020), **not** a theorem "no-foliation+no-superdeterminism+Bell ⟹ retrocausal." Say "strongly pressures,"
not "forces."

## CORRECTION 1 (the big one): covariant MEASURE ≠ covariant SELECTOR

Rigorous (not opinion): $SO(3)$ has an invariant probability *measure* on $S^2$ but **no** invariant *point*.
Likewise a Lorentz-invariant *measure* on histories can exist while almost every sampled history breaks
Lorentz symmetry — the **law** is covariant, the **realization** is not. So:

> The earlier "make-or-break = existence of a covariant global SECTION λ (Roberts Ȟ¹)" was a **category
> error.** You do NOT need (and generally cannot have) a covariant *selector* (an equivariant map Φ ↦ chosen
> world). λ is a **sample** from a covariant law, not an equivariant function. An individual actual world is
> not Lorentz-invariant (no actual world is); only the law is. This dissolves the "no covariant section" worry.

**★ Now machine-checked (2026-06-15, `QIQTH/CovariantGluing.lean`, NO axioms at all).** Both halves of the
dichotomy are formal: the covariant MEASURE exists (`Fock.weylBit_typicality_lorentzBoost_invariant`, 1+1D
free field), and a covariant SELECTOR cannot (`no_covariant_selector`: an equivariant `σ : Φ ↦ λ` sends a
symmetry-fixed state to a symmetry-fixed history, so if the symmetric state's actual histories form a
nontrivial orbit — no fixed history — no covariant selector exists; finite S²-analog witness
`bool_swap_no_selector`). So OP3b's conceptual core is settled: λ is necessarily a symmetry-breaking *sample*
of a covariant law, not a covariant function — that's forced, not a defect. Still open (the genuine
frontier): the global *consistent-set/realm* gluing over a poset without a ⊤-chart (net cohomology) and the
interacting/Type III₁ case; the contextuality-safety (Bell-embedded marginals) check.

## CORRECTION 2: the obstruction is CONTEXTUALITY, not Roberts cohomology

The real obstruction to a global actuality assignment is **Bell/Fine/Kochen–Specker / Abramsky–Brandenburger
contextuality-sheaf** global-section non-existence — NOT Roberts net cohomology (which classifies DHR
charges/sectors; wrong target). Escape: **λ assigns values only to ACTUAL decohered records in the ACTUAL
context (actual settings)** — never a noncontextual value-map over all counterfactual settings (that dies to
Bell/Fine/KS instantly). ⇒ The OP3b "Roberts Ȟ¹ / covariant global section" framing (PROGRAM_STATUS §4a, from
an earlier consult) is **mis-targeted** and should be corrected to: covariant σ-additive measure on
compatible *actual-record* histories.

**★ Now machine-checked (2026-06-15, `QIQTH/ContextualitySafe.lean`, axiom-free) — the Bell-marginal check
passes.** Assembled from the verified CHSH/no-signaling machinery: `no_global_record_valuemap` (a global
value-map = `LHVModel` over all four incompatible settings has `|CHSH| ≤ 2`, so none reaches the quantum
record value `2√2`), and `contextuality_safe` (a correlation `> 2` exists with NO global value-map). Combined
with `NoSignalingGeneral.bipartite_no_signaling` (per-compatible-context marginals no-signal, arbitrary ρ):
assigning values only to the ACTUAL context is *forced* (no global noncontextual joint exists) and *consistent*
(no-signaling). So λ dodges the Fine/Bell global-distribution obstruction by being actual-context-only, not by
smuggling a non-quantum assumption — the mandatory CHSH/Fine guardrail is satisfied.

**★★ Concrete embedding now machine-checked too (2026-06-15, `QIQTH/Fock/WeylBitBell.lean`, axiom-free).** The
no-signaling marginal is now derived FROM the actual Weyl-bit record measure (not the abstract CHSH theorems):
for spacelike modes (`Im⟪u,v⟫=0`), `∑_{σ_B} ‖A(u,σ_A)A(v,σ_B)Ω‖² = ‖A(u,σ_A)Ω‖²` — Alice's marginal,
independent of Bob's mode `v` (`bell_no_signaling_alice`); two Bob settings give the same Alice marginal
(`bell_no_signaling_setting_indep`); symmetric for Bob. Mechanism: spacelike bits commute (`bitOp_comm`,
microcausality) so Bob's bit moves outermost and sums via `bit_normSq_sum`. So the genuine record measure IS
no-signaling.

**★★★ STATE-INDEPENDENT (frontier push, 2026-06-15, `bell_no_signaling_state`).** The proof uses only
microcausality + normalization, neither of which depends on the state — so no-signaling holds for **ANY**
global state `ψ`, **entangled ones included**. This is the honest "causality always, Bell-violation iff
entangled" split: relativistic no-signaling is a state-independent property of the record dynamics, while Bell
*violation* enters purely through the state's entanglement (state-dependent, via the abstract Tsirelson —
never through signaling). So no entangled choice of `Φ` ever lets the record net signal.

FRONTIER STATUS: (a) the global gluing over a no-⊤ poset is ALREADY done at the measure level
(`KolmogorovFiniteFiber.exists_isLimit`, arbitrary index `Finset ι` directed by ⊆ — no top needed); the
"net cohomology" worry was dissolved by the measure-not-section correction. (b) Type III₁ / continuum is a
genuine multi-year Mathlib wall (no unbounded-operator / Type-III infrastructure; prior consults: do NOT
expand the TT tower); not pushed — would need decades of infra or axioms against the ratchet. (c) The one
remaining achievable-but-substantial piece: record correlations ATTAINING a CHSH/Tsirelson violation for an
entangled `Φ` within the Fock/record framework (the cited singlet `Tsirelson.lean` reaches 2√2; connecting it
to the record net is the open increment). The no-signaling side (this file) is now complete and
state-independent.

## The decisive object — and it's largely DONE for 1+1D (good news)

The right target (pro): a genuine **Poincaré-covariant σ-additive Kolmogorov measure** ℙ on Γ(𝓡), the space
of compatible global *actual-record* histories — Γ(𝓡)≠∅, projective consistency, σ-additive extension,
contextuality-safe (actual-only), covariance of the *law*. **For the 1+1D free field this is essentially what
we machine-checked**: `KolmogorovFiniteFiber.exists_isLimit` (σ-additive Kolmogorov extension on histories),
`StateNetMeasure.exists_typicalityMeasure` (state-agnostic μ∞), `localized_typicality_poincare_invariant`
(covariant law) + no-signaling/microcausality. λ = a SAMPLE from μ∞ (one compatible actual-record history),
which individually breaks Lorentz symmetry — exactly as it should.

The construction families (all all-at-once, all giving the covariant *law* not a selector): decoherent
histories + decoherence-functional measure (Gell-Mann–Hartle; `WeylBitMeasure`-style μ); Kent final-boundary
beables; Wharton–Sutherland / two-state-vector block. They converge on "covariant measure on actual-record
histories; λ a sample."

## Residual open pieces (corrected, narrower than before)

1. **Confirm μ∞ is "actual-decohered-records-only"** (contextuality-safe — on the effect/recorded-history
   net, not a KS value-map over all settings). Almost certainly yes; verify by embedding a nontrivial Bell
   experiment in the free-field detector model and checking the marginals.
2. **Realm / consistent-set selection** — μ(α)=⟨C_α†C_α⟩ is a probability only on a decoherent family
   (off-diagonal D(α,β)≈0); choosing the consistent set covariantly is the residual.
3. **Beyond 1+1D free/coherent** (interacting / general Type III₁).
4. **State the retrocausality honestly:** Bell measurement-independence holds for λ's *past* component but
   fails for the *complete block* λ — retrocausal/all-at-once, NOT conspiratorial superdeterminism.

## Net

The read is mostly right; but the construction is "λ = a sample (compatible actual-record history) from a
**covariant measure**," NOT "a canonically-selected covariant section." The obstruction is contextuality
(dodged by actual-only assignment), not Roberts cohomology. And the decisive object — a covariant σ-additive
Born measure on actual-record histories — **is already machine-checked for the 1+1D free field**. The frontier
is narrower than stated: (1)+(2)+(4) above, then the continuum/interacting generalization. Decisive next
target: verify the 1+1D μ∞ is contextuality-safe (Bell-experiment-embedded marginals) — i.e. that what we
built IS the covariant measure, with λ-as-sample the correct reading.
