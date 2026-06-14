# 57 — The λ construction, and where Q_max actually is (the stage / realm) (2026-06-15)

## The λ construction (final, corrected form)

**λ = a single μ-typical, complete 4D history of actual records — one compatible global section of the
decohered-record net over the causal-diamond poset — *sampled* from the Poincaré-covariant
decoherence-functional measure μ_Φ.** Four steps:

1. **Stage (covariant, no foliation):** the causal-diamond poset; for each diamond D the Boolean algebra
   `B_Φ(D)` of decohered, redundantly-broadcast **actual records** (NOT a value-map over all observables).
2. **Space of worlds Ω:** compatible global actual-record histories (one record per diamond, consistent on
   bulk overlaps) — each ω a complete 4D record history, no slice.
3. **Law (covariant measure):** the decoherence functional `μ_Φ(α)=‖C_α Φ‖²` (Born by construction),
   σ-additively extended; Poincaré-covariant as a *law* (`μ_{U_gΦ}(gα)=μ_Φ(α)`), valid on a decoherent family.
4. **λ:** one ω sampled from μ_Φ — a *contingent fact*, not an equivariant function (covariant MEASURE ≠
   covariant SELECTOR; cf. `56`). Individual λ breaks Lorentz symmetry; only the law is covariant.

Machine-checked for the 1+1D free field: `KolmogorovFiniteFiber` (σ-additive extension, **finite fibers**),
`StateNetMeasure`, `localized_typicality_poincare_invariant`, no-signaling/microcausality.

## Where Q_max is (and is NOT)

- **NOT in the measure** — Born comes from the decoherence functional (pure QM).
- **NOT in "one outcome per run"** — the histories framework gives that for free (sampling one history).
- **Q_max is in the STAGE — the record algebra `B_Φ(D)`.** Its three jobs there:
  1. **Finiteness** — at most `e^{Q_R}` distinguishable records/diamond; this is what makes the σ-additive
     measure *constructible* (the machine-checked `KolmogorovFiniteFiber` uses **finite fibers**).
  2. **Area-grain / covariance** — records resolvable within the boundary capacity (holographic, covariant).
  3. **Single-macroscopic-per-diamond** — the actuality capacity exclusion (`CoreNoCollapse`/`CapacityModel`).
- **Distinctive role: realm-selection grain.** Decoherent histories' biggest open problem is realm selection
  (Dowker–Kent: wildly many consistent sets, no selection rule). Q_max offers a physical grain — the realm is
  the holographically-resolvable, finitely-many, area-bounded records. This is a genuine contribution to the
  gap decoherent histories has.

Net: **Q_max says *which records exist and how many* (the stage); the decoherence functional says *with what
weight* (Born); λ says *which one is actual* (the sample).** Three pieces, three jobs.

## Honest analysis of "Q_max selects a unique consistent realm"

Brutal, before attempting the proof: **a capacity bound limits the NUMBER of records (cardinality ≤ e^{Q_R});
it does not by itself pick the BASIS.** Many distinct maximal orthonormal record families have the same
cardinality (e.g. the standard and Hadamard bases of ℂ² are both 2-element ONBs). So **capacity ALONE cannot
select a unique realm** — finiteness ≠ uniqueness. The basis-selection is done by **einselection**
(decoherence / the predictability sieve: the pointer observable that commutes with the interaction, e.g.
`[H_int, σ_z]=0` in the collisional model `CollisionalGamma`). So the truthful claim is:

> **Q_max + einselection ⇒ a unique, finite, single-macroscopic consistent realm.** Einselection supplies the
> basis; Q_max supplies finiteness + the area-grain + single-macroscopic exclusion. Q_max *alone* does not.

This is the same pattern as everywhere else: capacity is *structure/finiteness*, not *selection* — selection
needs an extra input (here einselection, exactly as actuality needed λ). The proof target is therefore the
**pair**: (a) NO-GO — capacity alone underdetermines the realm (a ≥2-distinct-realm countermodel); (b)
CONDITIONAL — given the einselected pointer basis, the capacity-bounded realm is unique. Status: see
`QIQTH/RealmSelection.lean`.

## Is the λ-measure CONSISTENT? (the decoherent-histories sense) — now machine-checked for the free field

"Consistent" is overloaded; the load-bearing sense is the decoherent-histories one: a family of
histories is a **consistent set** (Gell-Mann–Hartle) iff the decoherence functional
`D(α,β) = ⟪vec α, vec β⟫` obeys `Re D(α,β) = 0` for `α ≠ β` — exactly the condition that makes the
Born weights `D(α,α) = ‖vec α‖²` satisfy the probability **sum rules** (additivity under coarse-graining).

**Result (`QIQTH/Fock/WeylBitConsistency.lean`, axiom-free, 2026-06-15):** the genuine Weyl-bit Born
net (`WeylBitMeasure`, the σ-additive μ∞ on the continuum free field) is a **consistent set**, proved
*exactly* — no `N → ∞` environment limit:
- `medium_decoherence_bit` — the atom: `Re⟪A(u,1)ψ, A(u,−1)ψ⟫ = 0` for one Weyl bit. The bit operators
  `A(u,s)=(I+sW(u))/2` are NOT orthogonal projectors, so the *full* `D` does not vanish — only its real
  part, which is exactly medium decoherence. It is the SAME content as the normalization `bit_normSq_sum`
  (since `A(u,1)ψ + A(u,−1)ψ = ψ`, Pythagoras forces the cross term to zero).
- `medium_decoherence_context` — the same in any commuting context (single-bit coarse-graining): the whole
  projective Born family `bornWeight_*_marginal`/`bornWeight_coarse` rests on a consistent set.
- `bell_consistency_alice/bob` + `bell_marginal_sum_rule` — the two-record (Bell) configuration is a
  consistent set on each wing; the wing marginals are additive (the marginal probability is well-defined).

**Honest scope.** This is MEDIUM (weak) decoherence `Re D = 0` — precisely the sum-rule condition — and it
holds EXACTLY here. STRONG decoherence (full `D = 0`: `Im D → 0` and *every* multi-bit pair) is the
separate environmental-redundancy / SBS statement (`SBSBoolean`, Quantum Darwinism), the cited mechanism.
Consistency ≠ uniqueness (Dowker–Kent): uniqueness needs einselection (`RealmSelection`). So the chain is:
einselection picks the basis → `WeylBitConsistency` makes that realm a consistent set (sum rules hold) →
Q_max makes it finite + single-macroscopic → μ∞ is a genuine covariant Born probability → λ is a sample.

## Corrections propagated

- The OP3b "Roberts net cohomology / covariant global section" framing (PROGRAM_STATUS §4a) is **mis-targeted**
  (cf. `56`): λ is a *sample* from a covariant *measure*, not a covariant *section*; the obstruction is
  *contextuality* (Bell/Fine/KS, dodged by actual-records-only), not Roberts cohomology.
