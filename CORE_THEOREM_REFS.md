# Supporting arXiv literature for the QIQT-H core theorem

Collected 2026-06 (via Playwright/arXiv) while drafting `QIQTH/CoreNoCollapse.lean`.
TeX sources downloaded to `refs/arxiv_sources/<id>/` (tarballs git-ignored; extract
with `tar xzf <id>.tar.gz`). All are open-access arXiv preprints.

Per the GPT-5.5-pro strategic review (2026-06): the **Tomita–Takesaki / Type-III
tower is NOT the load-bearing part** of the "finite Q_max removes collapse" claim.
The load-bearing content is the finite-capacity exclusion + selector + Born/typicality
+ collapse-as-conditionalization, formalized in `QIQTH/CoreNoCollapse.lean`. These
references ground each block.

## Tier 1 — directly grounds the finite-capacity / record-exclusion core

- **arXiv:2601.19703** — Strasberg, Schindler, Wang, Winter, *Approximate
  Decoherence, Recoherence and Records in Isolated Quantum Systems* (Jan 2026).
  **THE anchor.** Decoherent-histories framework; proves (geometric, robust,
  Hilbert-space fact) that a family of N almost-orthogonal history vectors cannot be
  approximated by orthogonal record vectors once N → D, so the number of *identifiable*
  records `N_detectable ≪ D ≪ N_max`. They name the open **"branch selection problem"**:
  *how does the multiverse select the few branches that have observers aware of their
  history?* — which is **exactly** the question QIQT-H's `(Q_max, λ)` answers. Our
  `coactual_subsingleton` is the (cleaner, exact) capacity-exclusion fact; QIQT-H is a
  proposed resolution of their problem. Use for: motivation of the capacity bound, and
  the honest statement that single-outcome needs a *selection* principle beyond decoherence.

- **arXiv:2509.17775** — *Functional Information in Quantum Darwinism: An Operational
  Measure of Objectivity* (2026). Capacity-aware framework: adequacy predicate via the
  **Holevo bound**, capacity-limited plateaus `FI ≲ log₂ N`. Use for: a concrete
  information-theoretic `cost`/`Q_max` model justifying the saturation premise
  `cost > Q_max/2` (the one genuinely physical input of our core theorem).

## Tier 2 — Born rule / typicality (the across-run frequency layer)

- **arXiv:1910.08049** — *Typicality in the foundations of statistical physics and
  Born's rule*. Grounds the typicality measure μ over runs (cf. `QIQTH.BornTypicality`,
  `BornConcentration`).
- **arXiv:2302.02086** — *The Born Rule — Axiom or Result?* Born from a single
  non-contextuality assumption (Gleason-flavored; cf. `QIQTH.GleasonSelector`).
- **arXiv:1308.5384** — *Derivation of the Born rule based on the minimal set of
  assumptions* (entanglement-first route).

## Tier 3 — collapse-as-conditionalization / retrospective Born

- **arXiv:2010.15101** — *Observations of wavefunction collapse and the retrospective
  application of the Born rule*. Grounds `QMRecords.joint_eq_weight_mul_cond`
  (sequential Born = weight × conditional; collapse recovered by conditioning).
- **arXiv:1601.01214** — *Scheme of a Derivation of Collapse from Quantum Dynamics*
  (Born as a consequence of dynamics).
- **arXiv:1702.01845** — *Updating the Born rule* (a rule subsuming Born + collapse,
  knowledge-based).

## Tier 4 — decoherence does NOT by itself give single outcomes (the gap we fill)

- **arXiv:1308.4055** — *Why decoherence solves the measurement problem* (and the
  standard counter-view). Use for: framing why a *separate* selection/capacity
  principle is needed — decoherence kills interference, not multiplicity.

## How each maps to `CoreNoCollapse.lean`

| Block | Lean object | Reference |
|---|---|---|
| finite-capacity exclusion (core) | `coactual_subsingleton`, `RecordContext.cost_gt_half` | 2601.19703, 2509.17775 |
| single outcome (no collapse) | `exactly_one_actual`, `qiqth_single_outcome_no_collapse` | 2601.19703 (branch selection) |
| Born weights / typicality | `QMRecords.weight`; `GleasonSelector`/`BornTypicality` | 1910.08049, 2302.02086 |
| collapse = conditionalization | `QMRecords.joint_eq_weight_mul_cond` | 2010.15101, 1702.01845 |
| why decoherence is insufficient | (motivation for `Selection`/`λ`) | 1308.4055 |

## Capacity model — the saturation premise is now DERIVED (`QIQTH/CapacityModel.lean`)

The saturation premise `cost r > Q_max/2` is no longer assumed for the concrete
"orthogonal-records-in-a-finite-register" model. With records realized as an
orthonormal family of pointer states (frames) in a finite-dim register of dimension
`D = finrank`:
- `orthonormal_card_le_finrank` : #records ≤ D (the raw capacity fact — Strasberg's
  `N_detectable ≤ D`, here exact via `Orthonormal.linearIndependent` + card ≤ finrank);
- `capacity_total` : `∑ⱼ recDim j ≤ D` (capacity additive and bounded — DERIVED);
- `macroscopic_subsingleton` : at most ONE record with `D < 2·recDim j` — the
  saturation premise of `CoreNoCollapse` is now a **theorem**;
- `capacity_exactly_one` : capacity + selector ⇒ exactly one macroscopic record.

What remains as transparent physical modelling (NOT a hidden assumption): the choice
that a "complete macroscopic record" is one occupying `> D/2` of the register
(`Macroscopic D label j := D < 2·recDim j`). Reducing even this to first principles
is **Tier B** (below).

## Tier B design — the bridge theorem, grounded (TeX in refs/arxiv_sources/)

GPT-5.5-pro's soundness review (2026-06) named the open content: a **bridge theorem**
`CompleteRecord r → cost > Q_max/2` derived from *independent* record-quality
conditions (decoherence/redundancy/accessibility), with an *information* (not rank)
cost. The objectivity literature supplies the exact mechanism.

**Definitions to formalize (Korbicz–Horodecki, "Roads to objectivity", arXiv:2007.04276;
"Objectivity through state broadcasting", arXiv:1305.3247):**
- *Objectivity* (Zurek): the state of `S` is objective iff many observers can determine
  it independently and without perturbing it.
- *Spectrum Broadcast Structure (SBS)* — the UNIQUE state structure compatible with
  operational objectivity:
  `ρ_{S:E_obs} = ∑ᵢ pᵢ |i⟩⟨i|_S ⊗ ρ^{E₁}_i ⊗ … ⊗ ρ^{E_{R}}_i`,  with the family
  `{ρ^{Eₖ}_i}ᵢ` having **pairwise-orthogonal supports** (perfect distinguishability) in
  each observed fragment `k`.
- *Redundancy* `R_δ = 1/f_δ`: the number of disjoint environment fragments each carrying
  (≈ full) information about the pointer outcome.

**Why this gives the bridge (and fixes the rank-vs-information flaw):**
An objective record of an `n`-outcome pointer, broadcast (SBS) to `R` fragments, forces
each fragment to perfectly distinguish `n` alternatives, so the broadcast support has
Hilbert dimension `≥ nᴿ` (TENSOR product — dims MULTIPLY), i.e. **information cost
`≥ R·log n` bits**. With a finite information capacity `Q_max` (Holevo / functional
information, arXiv:2509.17775; or Bekenstein/holographic), `cost(complete record)
= R·log n` and "macroscopic" = large redundancy `R` ⟹ `cost > Q_max/2` ⟹ at most one.
So the threshold is DERIVED from redundancy + the tensor (information) capacity, not
assumed. Two objective records of NON-commuting observables cannot share one SBS (it is
diagonal in a single pointer basis) — objectivity itself einselects the basis.

**Lean implementation — `QIQTH/SBSBridge.lean` (DONE, axiom-free):**
- `fragment_finrank_ge` : perfect distinguishability of `n` outcomes ⇒ fragment
  dimension `≥ n` (orthonormal record states; `card ≤ finrank`). PROVED.
- `broadcast_finrank_ge` : broadcasting TENSORS the fragments, so dimensions MULTIPLY
  (`finrank (A⊗B)=finrank A·finrank B`); two fragments ⇒ broadcast dim `≥ n²`. PROVED —
  this is the information/tensor model (fixes the rank-vs-information flaw).
- `infoCost R n := R·log n`, with `infoCost_eq_log_broadcastDim : = log(nᴿ)` (information
  adds across the `R` redundant copies). PROVED.
- `SBSContext` + `toRecordContext` : the BRIDGE — cost `j := R j·log(n j)` (broadcast
  information), and `cost_gt_half` is PROVED from `R j ≥ R_macro` + the capacity relation
  `Q_max/2 < R_macro·log 2`.  Instantiates `CoreNoCollapse.RecordContext`.
- `sbs_single_outcome` : Tier-B single-outcome theorem — saturation DERIVED from
  redundancy, cost a genuine broadcast information, not a stipulated ">half register".

**Honest residual.** The capacity relation `Q_max/2 < R_macro·log 2` is the transparent
physical input (the accessible-information capacity `Q_max` is small vs a macroscopic
record's broadcast information — Holevo/Bekenstein), now a relation between `Q_max` and the
macroscopic-redundancy scale rather than a circular ">half" stipulation.  DEFERRED (genuine
multi-session research): full SBS with mixed fragment states + von-Neumann-entropy cost, the
SBS uniqueness theorem, and the non-commuting-basis (objectivity einselects the basis) result
— a constructive answer to the Strasberg–Winter "branch selection problem".

**Tier B references (TeX downloaded):**
- arXiv:2007.04276 — Korbicz, *Roads to objectivity: QD, SBS, strong QD* (review; SBS
  theorem, objectivity/redundancy/non-disturbance definitions). THE definitional anchor.
- arXiv:1305.3247 — *Objectivity through state broadcasting* (origin of SBS).
- arXiv:2509.17775 — functional-information / Holevo capacity (the `Q_max` model).
- arXiv:2601.19703 — Strasberg–Winter branch-selection (the open problem SBS answers).
