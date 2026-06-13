# 51 — Attempt to derive Q^eff non-circularly (2026-06-13)

**Goal.** Find an effective capacity `Q^eff` — the capacity actually relevant to maintaining a coherent
superposition — that is (a) **non-circular** (set by the framework + fundamental constants, not fitted to
data) and (b) **small enough to bite** in some accessible regime, so finite `Q_max` is *not* merely
empirically equivalent to QM. (Context: `50_Born_Attack_Routes.md`, the empirical-status downgrade in
`08`/`PUBLICATION_STRATEGY`/`PROGRAM_STATUS` — GPT-5.5 verdict that finite `Q_max` alone is empirically
equivalent to QM.)

## Candidates that fail (all confirm empirical equivalence)

| candidate `Q^eff` | magnitude | verdict |
|---|---|---|
| holographic area `A/4ℓ_P²` | ~10⁶⁶ bits/cm² | far too large — null |
| Bekenstein bound of the system `2πRE/ℏc` | ~10¹⁸ bits (100 nm, 10⁻¹⁷ kg) | far too large — null |
| entanglement entropy actually generated | small, but saturates `Q_R` never | null |
| per-pointer subspace (O(1) bits) | O(1) | forbids *observed* large-molecule interference — excluded |

Every *geometric / information-theoretic* capacity is either astronomically above the few-bit which-path
record (→ no effect) or O(1) (→ over-predicts, excluded). This is the wall: there is no Goldilocks scale from
a kinematic information capacity.

## The one candidate that survives — the gravitational / geometry-distinction capacity

**QIQT-H-native argument.** The Macroscopic Definiteness Conjecture forbids a region from holding two
macroscopic *records* at once. The gravitational field **is** a macroscopic, redundantly-broadcast record —
it is everywhere, encoding the mass configuration. So two gravitationally-distinct branches are two
macroscopic *geometric* records, and superposing them is superposing two distinct holographic capacities
`Q_R` — which the single-record bound forbids. **The geometry is what must become definite first.**

This is non-circular: the scale is set by `G` and `ℏ`, no fitted parameter. The decoherence sets in when the
two branches' geometries differ "by one record's worth", set by the gravitational self-energy of the
difference of the two mass densities,
`E_Δ = G ∫∫ Δρ(r) Δρ(r') / |r−r'| d³r d³r'` (with `Δρ = ρ₁ − ρ₂`),
giving a decoherence time
`τ ~ ℏ / E_Δ` — **the Diósi–Penrose rate.**

**Quantitative.** For `τ ~ 1 s` we need `E_Δ ~ ℏ ~ 10⁻³⁴ J`; with `E_Δ ~ Gm²/R` and `R ~ 10⁻⁶ m` this gives
`m ~ 10⁻¹⁵ kg` — the **Penrose mass scale** (~10⁻¹⁴ kg), the target of next-generation levitated
optomechanics / matter-wave interferometry (MAQRO). Not yet excluded; testable in the coming decade.

## Honest verdict

This is the **only** non-circular `Q^eff` that lands in a *testable* window rather than 10⁻⁶⁰-unobservable or
already-excluded. Net claim:

> QIQT-H is empirically equivalent to standard QM in every channel **except the gravitational one**, where
> superposing geometries = superposing capacities (forbidden by the same bound) ⇒ gravitational decoherence
> at the Diósi–Penrose scale.

**Three honest limits (do not overclaim):**
1. **Converges with Diósi–Penrose — does not beat it.** If correct, QIQT-H's testable content *is*
   gravitational decoherence; it adds a *holographic rationale* ("can't superpose two `Q_R`"), not a novel
   signature. DP-confirmation would support the reading; DP-exclusion would constrain QIQT-H.
2. **The capacity → `E_Δ/ℏ` link is a dimensional/heuristic match, not a derivation.** The *scale* coincides
   with DP and the framework *points at* gravity; the *rate* `E_Δ/ℏ` has **not** been derived from the
   capacity bound. That derivation is the real open task.
3. Status upgrade: from "empirically equivalent, full stop" → **"empirically equivalent except possibly in
   the gravitational channel, where it makes a DP-scale, conjectural, testable prediction."** Genuine
   progress on the falsifiability question; not a clean win.

**Next steps (if pursued):** (i) GPT-5.5-pro stress-test of the capacity→`E_Δ/ℏ` link — is it derivable or
just a scale-coincidence? (ii) the precise distinguishability/record criterion for "two geometries count as
two records" (when does ΔA of the causal-diamond screens exceed one record?); (iii) compare the resulting
mass/coherence-time curve against current matter-wave (Arndt) and levitated-optomechanics bounds and the
MAQRO projection. Until (i)–(ii) are done, this is a **candidate**, not a derivation — flagged as such.
