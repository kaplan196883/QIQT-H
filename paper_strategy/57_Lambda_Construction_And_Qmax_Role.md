# 57 — The λ construction, and where Q_max actually is (the stage / realm) (2026-06-15)

## The λ construction (final, corrected form)

**λ = a single μ-distributed, complete 4D record history — one compatible global history of the
decohered-record net over the causal-diamond poset — *sampled* from the Poincaré-covariant
decoherence-functional measure μ_Φ.** Four steps:

1. **Stage (covariant, no foliation):** the causal-diamond poset; for each diamond D the Boolean algebra
   `B_Φ(D)` of decohered, redundantly-broadcast **candidate record alternatives** (NOT "actual" — they
   become actual only once λ selects; and NOT a value-map over all observables). QIQT-H **posits** that
   `Q_max` bounds their number (`≤ e^{Q_R}`) — an added actuality-layer assumption, NOT a theorem derived
   from the holographic entropy bound (which constrains distinguishable states, not a Boolean record algebra).
2. **Space of worlds Ω:** compatible global record histories (one record per diamond, consistent on
   bulk overlaps) — each ω a complete 4D history, no slice.
3. **Law (covariant measure):** the decoherence functional `μ_Φ(α)=‖C_α Φ‖²` — **Born is INPUT here**
   (it is the assumed weight, not derived), σ-additively extended; Poincaré-covariant as a *law*
   (`μ_{U_gΦ}(gα)=μ_Φ(α)`), valid on a decoherent family.
4. **λ:** one ω sampled from μ_Φ — a *contingent fact*, not an equivariant function (covariant MEASURE ≠
   covariant SELECTOR; cf. `56`). A generic sampled λ is not a Poincaré fixed point (ordinary sample
   non-invariance); only the law is covariant.

**Honest framing (per the 2026-06-15 GPT-5.5-pro review, checked against Lean + the Bell/contextuality
literature):** the construction is explicitly **contextual AND Bell-nonlocal / global**. Assigning values
only to actually-decohered records in the actual context dodges Kochen–Specker / Fine (no noncontextual
counterfactual value-map), but it does **not** dodge Bell: any QM-reproducing single-world theory violates
Bell *local causality* (`P(a,b|x,y,Λ_past) ≠ P(a|…)P(b|…)`). No-signaling / microcausality are *operational*
constraints and do NOT rescue local causality — conflating them is a category error. So λ must be advertised
as a global/contextual block (retrocausal or all-at-once), not a locally-causal one.

Machine-checked for the 1+1D free field: `KolmogorovFiniteFiber` (σ-additive extension, **finite fibers**),
`StateNetMeasure`, `localized_typicality_poincare_invariant`, no-signaling/microcausality.

## Where Q_max is (and is NOT)

- **NOT in the measure** — Born comes from the decoherence functional (pure QM).
- **NOT in "one outcome per run"** — the histories framework gives that for free (sampling one history).
- **Q_max is in the STAGE — the record algebra `B_Φ(D)`.** Its jobs there:
  1. **Finiteness** — at most `e^{Q_R}` distinguishable records/diamond; this is what makes the σ-additive
     measure *constructible* (the machine-checked `KolmogorovFiniteFiber` uses **finite fibers**).
  2. **Area-grain / covariance** — records resolvable within the boundary capacity (holographic, covariant).
  - **NOT a single-macroscopic *exclusion*** — see the 2026-06-15 correction below. Q_max does NOT forbid two
    actual records by information-counting; that "records add ⇒ overflow Q_R" claim is a category error.
    Single-macroscopic-ness is supplied by **λ + local single-valuedness**, not by the capacity bound.
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

"Consistent" is overloaded; the load-bearing sense is the decoherent-histories one. **Terminology (the
Gell-Mann–Hartle hierarchy, corrected per a 2026-06-15 GPT-5.5-pro review checked against GMH):**
`Re D(α,β) = 0` is **weak decoherence / consistency**; `D(α,β) = 0` (real AND imaginary parts) is
**medium**; **strong** additionally requires *records* (orthogonal record states). A family of histories
is a **consistent set** iff `Re D = 0` — exactly the condition that makes the Born weights
`D(α,α) = ‖vec α‖²` satisfy the probability **sum rules** (additivity under coarse-graining). (Born is
INPUT here — the weight is `‖vec α‖²` by construction; these results show the weights are *consistent*,
not a derivation of Born. Also the `A(u,s)` are *effects*/Kraus operators, NOT projectors — a
generalized-measurement history; the genuine projector/Boolean-record content is the separate `SBSBoolean`.)

**Result (`QIQTH/Fock/WeylBitConsistency.lean`, axiom-free, 2026-06-15):** the genuine Weyl-bit Born
net (`WeylBitMeasure`, the σ-additive μ∞ on the continuum free field) is a **consistent set** (WEAK
decoherence), proved *exactly* — no `N → ∞` environment limit:
- `weak_decoherence_bit` — the atom: `Re⟪A(u,1)ψ, A(u,−1)ψ⟫ = 0` for one Weyl bit. The bit operators
  `A(u,s)=(I+sW(u))/2` are NOT orthogonal projectors, so the *full* `D` does not vanish — only its real
  part, which is exactly the weak/consistency condition. It is the SAME content as the normalization
  `bit_normSq_sum` (since `A(u,1)ψ + A(u,−1)ψ = ψ`, Pythagoras forces the cross term to zero) — i.e. an
  exact *algebraic* consistency property of the substrate, NOT physical macroscopic decoherence.
- `weak_decoherence_context` — the same in any commuting context (single-bit coarse-graining): the whole
  projective Born family `bornWeight_*_marginal`/`bornWeight_coarse` rests on a consistent set.
- `bell_consistency_alice/bob` + `bell_marginal_sum_rule` — the two-record (Bell) configuration is a
  consistent set on each wing; the wing marginals are additive (the marginal probability is well-defined).

**Update — the multi-bit-differing residual is now closed (full `D = 0`) for orthogonal modes**
(`QIQTH/Fock/WeylBitStrongDecoherence.lean`, axiom-free, 2026-06-15). Weak consistency alone is fragile
under composition (Diósi: two independent systems with imaginary off-diagonals can compose to a real one),
so robustness needs full `D = 0` — which is exactly what this file delivers. The residual flagged below
(pairs differing in more than one bit, whose real parts only *summed* to zero) is now proved to vanish
*exactly* when the record modes are orthogonal:
- `vacuum_bit_strong_decoherence` — a single Weyl bit on the vacuum is EXACTLY orthogonal (full `D = 0`,
  not merely weak `Re D = 0`), because the vacuum Weyl one-point function `⟪Ω,W(u)Ω⟫ = exp(−½‖u‖²)` is real.
- `bell_two_bit_strong_decoherence` — for orthogonal record modes `⟪u,v⟫ = 0` (the physical "distinct /
  spacelike records" condition), the maximally-different Bell history vectors `vec(+,+)` and `vec(−,−)`
  are exactly orthogonal. So the full Bell config has `D = 0` (GMH *medium*; and with orthogonal records,
  *strong*), not just weak consistency. (The theorem names say "strong" colloquially = off-diagonals
  vanish entirely with orthogonal records.) Mechanism: the Gaussian overlaps collapse via
  `weylCoeff v 0 · weylCoeff v w · exp⟪v,v⟫ = 1`. For NON-orthogonal modes the cross term is nonzero,
  `∝ Re⟪u,v⟫` (the mode/record overlap) — the genuine record-overlap correction, suppressed by
  SBS/redundancy (cited).

**The overlap correction is now an EXACT formula + a witnessed countermodel** (same file):
- `bitOp_vac_expVec_cross_eq` — the exact value with NO orthogonality assumption:
  `⟪A(v,1)Ω, A(v,−1) e(w)⟫ = weylCoeff(v,0)·(exp⟪v,w⟫ − exp(−⟪v,w⟫))/4 = ½ exp(−½‖v‖²) sinh⟪v,w⟫`. It
  vanishes iff `⟪v,w⟫ = 0`, so the `=0` lemma is exactly its orthogonal special case; the nonzero value is
  the record-overlap correction `∝ Re⟪v,w⟫`.
- `strong_decoherence_needs_orthogonality` — a witnessed countermodel over `H = ℂ` (`v = w = 1`): the cross
  term `= exp(−½)(exp 1 − exp(−1))/4 ≠ 0`. So orthogonality is **necessary**: overlapping records are NOT
  strongly decoherent.

**Redundancy restores strong decoherence (the SBS / Quantum-Darwinism limit)** — `QIQTH/SBSSuppression.lean`,
axiom-free. A macroscopic pointer is redundantly imprinted on `N` fragments, each with per-fragment overlap
of modulus `≤ r < 1`; the joint off-diagonal FACTORS as `∏ z k` and is suppressed:
- `offdiagonal_norm_le` — `‖∏ z k‖ ≤ rᴺ` (exponential bound).
- `offdiagonal_tendsto_zero` — the joint off-diagonal → 0 as redundancy `N → ∞`. So records only partially
  resolved per fragment become *fully* (strongly) decohered once broadcast macroscopically (`D → 0`).

**Honest scope.** MEDIUM decoherence `Re D = 0` (the sum-rule condition) holds EXACTLY for *all* contexts;
STRONG decoherence `D = 0` holds exactly for orthogonal record modes (and on the vacuum), with the exact
overlap correction known for the non-orthogonal case. The remaining `Im D → 0` for *non-orthogonal* records
is then delivered by **redundancy** (the `rᴺ → 0` suppression law): the abstract Quantum-Darwinism mechanism
is now machine-checked; its physical input (macroscopic records ARE redundantly broadcast with bounded
per-fragment overlap `r < 1`) remains the cited assumption.
Consistency ≠ uniqueness (Dowker–Kent): uniqueness needs einselection (`RealmSelection`). So the chain is:
einselection picks the basis → `WeylBitConsistency` makes that realm a consistent set (sum rules hold) →
Q_max makes the record set **finite** (NOT single-macroscopic by itself — see correction below) → μ∞ is a
genuine covariant Born probability → λ is a sample (and λ + local single-valuedness gives single-macroscopic).

## ★ Correction 2026-06-15 — "Q_max single-macroscopic exclusion" is a CATEGORY ERROR

Two GPT-5.5-pro consults (checked vs Bousso/Bekenstein + decoherence theory). Wherever this note said Q_max
provides a "single-macroscopic exclusion" / "actuality capacity exclusion," that is **withdrawn**. Q_max does
NOT forbid two actual records:
- **Category error:** the holographic bound counts independent d.o.f. (joint entropy / code-dimension), NOT a
  sum of redundant classical records — R redundant Quantum-Darwinism imprints of one fact have joint entropy
  `H(X)`, not `R·H(X)` (compressible). So "actual classical records add ⇒ overflow Q_R" is invalid.
- **A^{3/4} structural gap:** ordinary record-carrier entropy is capped at `S ~ (A/ℓ_P²)^{3/4}` (max thermal
  entropy before BH collapse), `≈10^91.5` vs `Q_max ~10^122` — a permanent ~31-order gap (only black holes
  reach `A/4`, and a BH has no records); `I₀ ≈ Q_R` is false by ~31 orders; the universe runs at `~10^-18`
  of capacity even cosmologically (`2×10^104 ≪ 10^122`).
- **The exclusion is λ + local single-valuedness**, not capacity: a classical carrier holds ONE value, and
  "one value" is the single-world claim supplied by λ (decoherence ≠ definiteness; it gives branch structure +
  suppressed interference, not actuality). Theorem-level: unitary linearity + finite capacity can't select a
  branch.

So Q_max's role here is the **finite stage only** (finiteness, area-grain, realm grain) — *not* the
single-macroscopic exclusion. The realm-grain contribution (a physical Dowker–Kent grain via finiteness)
stands; the *exclusion* claim does not. Propagated to memory, PROGRAM_STATUS, the foundations paper §7.6 +
Theorem 4, and qiqt.org.

## Corrections propagated

- The OP3b "Roberts net cohomology / covariant global section" framing (PROGRAM_STATUS §4a) is **mis-targeted**
  (cf. `56`): λ is a *sample* from a covariant *measure*, not a covariant *section*; the obstruction is
  *contextuality* (Bell/Fine/KS, dodged by actual-records-only), not Roberts cohomology.
