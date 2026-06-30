# QIQT-H claims ledger — every public claim → its Lean ground-truth entry + status

**Purpose.** The single cross-reference that closes the alignment loop (`ALIGNMENT_PLAN.md`, area A4). Each
headline claim made in public (the paper `QIQT_Foundations_Paper.md` and the website `website/src/pages/*`) is
mapped to its supporting entry in `LEAN_RESULTS_INVENTORY.md` (the audited ground truth) **with the same
qualifier**. A claim is **aligned** iff the inventory supports it with the matching status. Built 2026-06-30
after A1 (code-comment hygiene), A2 (website), and A3 (paper) landed.

**Status legend** (from the inventory):
- **[AF]** axiom-free, standard-3 only, **unconditional**.
- **[AF·cond:H]** axiom-free std-3, **conditional** on a named hypothesis/typeclass `H` (a labelled premise,
  never a Lean `axiom`).
- **[no-go]** an honest **negative** theorem.
- **[frontier]** **NOT built** — explicitly cited/checkpointed (an open obligation, no theorem).
- **[re-derivation]** a machine-checked re-derivation of a *standard* result (true & verified, not unique to QIQT-H).

> **The one-line honest scope** (inventory §9): *a rigorously machine-verified single-world interpretation + a
> substantial formalized operator-algebra/entropy library + a re-derivation of induced-gravity results* — modest
> on novel physics, strong on rigor and breadth. "Finite capacity" has **two provably-distinct layers** — a record
> **count** (`card R ≤ e^{Q_R}`, finite-dim model) and a finite **entropy** bound (`S_vN+S_rel ≤ Q_R`, continuum
> Type III₁), with `EntropyNotCardinality` proving the entropy bound is *not* a count — and is **never** a
> finite-matter theory (D2/D3).

---

## A. The substrate-level meta-claims

| # | Public claim | Appears in | Inventory entry | Status | Aligned |
|---|---|---|---|---|---|
| A1 | "Machine-checked, **axiom-free**: every audited theorem depends only on `propext`/`Classical.choice`/`Quot.sound`; no `sorry`; no project axioms; CI budget 0." | abstract; `formalization`, `index`, `about` | §0 (zero raw `axiom`, zero `sorry`, budget-check = 0) | **[AF]** | ✓ |
| A2 | "The budget genuinely fell **57 → … → 0** by real discharge, not relabeling." | abstract; §11.4 banner | §0 (verified across Entropy/ tower + top-level clusters) | fact | ✓ |
| A3 | "**~296 files / ~3,300 theorems**; the `#print axioms` audit carries **2,213 directives over 256 modules**." | abstract; §11.4 banner; `formalization` (scale line) | §0 (~2,213 directives; 296 files) — counted directly in A3 | fact | ✓ (numbers corrected in A3; were stale 830/192/2,010) |
| A4 | "Axiom-free does **not** mean the physical postulates are derived — FQ/P4, KMS/Clausius, P5, the value of G stay labelled hypotheses/frontiers." | abstract; §11.2a table; `formalization` note | §0, §8 | honest scope | ✓ |
| A5 | "A vacuity lint guards against `True`-antecedent trivialization; one benign indiscrete-preorder site remains." | §11.2a | §0 (`LorentzWitness.lean:180`, the only `:= True`) | [scaffold] | ✓ |

## B. Born rule / single-world selection (Φ, λ)

| # | Public claim | Appears in | Inventory entry | Status | Aligned |
|---|---|---|---|---|---|
| B1 | "Born is **reduced to one premise (P5)**, *not derived* from unitarity." | abstract; §1.1a (P2, P5); `formalization`, `ladder`, `selection`, `born` | §1 (`positive_ray_certain_forces_born`; Born reduced to P5) | **[AF·cond:P5]** | ✓ |
| B2 | "A positive, normalized, ray-certain weight **is** the Born functional (Born from positivity)." | abstract; §11.4.0 | §1 `EffectGleason.finite_effect_gleason`, `GleasonSelector.positive_ray_certain_forces_born` | **[AF]** | ✓ |
| B3 | "The equiprobable measure over an equal-amplitude orthonormal fine-graining has outcome-marginal exactly \|c_k\|²." | §1.1a; `born` | §1 `BornEquiprobable.born_from_equiprobability` (Zurek amplitude→count, Pythagoras) | **[AF]** | ✓ |
| B4 | "Across-run Born statistics are Chebyshev-typical under the canonical measure." | abstract; §7.4 | §1 `BornTypicality.qiqth_born_typicality_conditional`, `BornTypicalityFinite.chebyshev_freq` | **[AF·cond:P5]** | ✓ |
| B5 | "Single outcomes are the work of **λ + decoherence, NOT capacity**." (H2 retired) | abstract; §1.1a (108); §5–§7, §10, §11 (post-A3) | §1, §7 (`NoConcentration`, `RealmSelection.capacity_underdetermines_realm`) | **[no-go]** + interpretation | ✓ (A3 propagated the retraction through the body) |
| B6 | "The structural axioms do **not** single out Born (a selection premise is unavoidable & non-vacuous)." | abstract; §11.4 | §1 `NoBornFromNothing`, `EquivarianceGap`, `OperationalNoGo` | **[no-go]** | ✓ |

## C. Finite capacity / holographic area floor

| # | Public claim | Appears in | Inventory entry | Status | Aligned |
|---|---|---|---|---|---|
| C1 | "The area floor `S_vN(ρ_R) ≤ Q_R` is a **theorem** (finite-dim max-entropy), given the finite-capacity postulate." | §1.1a (96); `theory`, `born` | §2 `FQBoundMicro.area_floor_vonNeumann`, conditional on `HolographicCapacityBound` | **[AF·cond:HolographicCapacityBound]** | ✓ |
| C2 | "The bound is on the **von Neumann** entropy (not Shannon record-count); only `≤` is needed; `N_R` is the **regional** cutoff of a Type III₁ algebra." | §1.1a (96) | §2 (`HolographicCapacityBound` vs `…Exact`; regional, not global) | **[AF·cond]** | ✓ |
| C3 | "'Finite capacity' has **two provably-distinct machine-checked layers**: a record **COUNT** (`card R ≤ e^{Q_R}`) in the finite-dim model and a finite **ENTROPY** bound (`S_vN+S_rel ≤ Q_R`) in the continuum Type III₁ setting — **never** a finite matter Hilbert space." | §1.1a (96 two-layer note, 110 fork); `idea`, `theory`, `open-problems` | §2 (two-layer ⚠-note: `HolographicCapacityBound` = count vs `Phase5Master` = entropy); §9 | **[AF·cond]** (both layers) + **[no-go]** (D2/D3) | ✓ |
| C4 | "Finite matter + exact Lorentz ⟹ H=0 ∧ P=0 (literal finite-matter reading untenable)." | §1.1a (110) | §2 `FiniteMatterNoLorentz.finitePoincare_trivial` (D2) | **[no-go]** | ✓ |
| C5 | "A bounded entropy does **not** imply bounded cardinality — **the bridge proving the two C3 layers are inequivalent** (the continuum entropy bound is *not* a record count)." | §1.1a (96, 110 fork); `idea`, `theory` | §2 `EntropyNotCardinality.entropy_bound_not_cardinality_bound` (D3) | **[no-go]** | ✓ |
| C7 | "The count layer is **not derivable** from the entropy/area bound; the operational record count is a **Holevo–Bekenstein** capacity `log M_ε ≤ (Q+h₂(ε))/(1−ε)` (finite only via an imported energy cutoff) — **not new physics**; distinctive only via a `Q_R` ≠ standard generalized entropy (open frontier)." | §1.1a; `idea`, `theory`, `open-problems`; `OPERATIONAL_CAPACITY_PLAN.md` | §2 guardrail; `OperationalCapacity.lean` — `record_capacity`, `exact_distinguishable_capacity`, `gibbs_entropy_bound` (**PROVED, axiom-free**) | **[AF]** (the bound) + **[frontier]** (a new `Q_R`) | ✓ |
| C6 | "Capacity is **kinematic** — it bounds S(ρ_R) and feeds the field equations — not a mechanism for single outcomes." | §1.1a; §6.8 banner; §7.5; `born`, `about` | §2, §7 (`measure_needs_only_finiteness`) | scope | ✓ |

## D. Gravity / Sakharov 1/4 / Einstein equation

| # | Public claim | Appears in | Inventory entry | Status | Aligned |
|---|---|---|---|---|---|
| D1 | "The **1/4** ratio is machine-checked — but as a **re-derivation** of standard Sakharov/induced-gravity, *not* unique to finiteness; heat-kernel coefficients cited, G carried." | §1.1a (96); `theory`, `realisations`, `statements/gr` | §3 `SakharovRatio.sakharov_ratio` | **[AF] + [re-derivation]** | ✓ (A2/A3 made "re-derivation" explicit) |
| D2 | "The Einstein field equations follow for an explicit free Klein–Gordon field on a pp-wave background — **conditional & free-field only**." | §1.1a (89); `formalization`, `statements/gr` | §3 `WedgeKMSToGR.qiqt_gr_freefield`, `qiqt_gr_ppwave_showcase` | **[AF·cond: matter-EoM + P4 + localization map]** | ✓ |
| D3 | "Every geometric/curvature/area-kinematic step (Christoffel→Ricci→Einstein, ∇·G=0, Raychaudhuri) is discharged; the carried inputs are the matter EoM, P4, and the localization map (Gap 2)." | §1.1a (89); `formalization` note | §3 (all diff-geo [AF]; area law + localization map [frontier]) | **[AF·cond]** | ✓ (A2 fixed the stale "BW package cited" note) |
| D4 | "matter conservation ∇·T=0 is **derived** for the KG stress tensor (free field)." | `formalization`; §1.1a | §3 / §6d (free-field [AF]; carried for the general capstone) | **[AF]** (free field) | ✓ (A2 fixed "is a physical postulate") |
| D5 | "P4-MICRO alone is **not** GR — a microstate count can't supply a temperature; the thermal/BW input is irreducible." | §1.1a (96); `theory`, `open-problems` | §3 (`GRFromMicro` header), §9 | scope | ✓ |
| D6 | "The value of **G**/ℓ_P is a carried UV datum, never derived." | §1.1a (89, 96); everywhere gravity is discussed | §3, §8 (value of G = frontier) | **[frontier]** | ✓ |

## E. Modular / Tomita–Takesaki / one-particle BW / Lorentz (OP3b)

| # | Public claim | Appears in | Inventory entry | Status | Aligned |
|---|---|---|---|---|---|
| E1 | "The one-particle **Bisognano–Wichmann** is a **fully unconditional** Lean theorem (Reeh–Schlieder discharged)." | §1.1a; `formalization` (85), `statements/gr` | §6c `oneParticleBW_niceWedge_unconditional` (Wiener–Tauberian + Pauli–Jordan) | **[AF]** | ✓ |
| E2 | "A genuine axiom-free **bounded Tomita–Takesaki** / crossed-product operator-algebra layer; the three modular generators are self-adjoint (Stone)." | `formalization`; §1.1a | §4 (RvD modular objects; `stoneGen_isSelfAdjoint`, `clockEnergy/momentumOp/modularGen_isSelfAdjoint`) | **[AF]** | ✓ (A1 fixed the "carried frontier" under-claim) |
| E3 | "A σ-additive **boost-invariant typicality measure** on the 1+1D free field (OP3b)." | `open-problems`; §11.4.3b | §5 `weylBit_typicality_lorentzBoost_invariant`, `FreeFieldTypicality.freeFieldMeasure_boost_invariant` | **[AF]** | ✓ |
| E4 | "A covariant measure exists, but a covariant **selector cannot** — the honest no-go." | §11.4.3b; `open-problems` | §5 `CovariantGluing.no_covariant_selector` | **[no-go]** | ✓ |
| E5 | "Operational **no-signaling** holds (bipartite / general); but no-signaling ≠ Lorentz-covariance of the beable." | §7.7, §11.4.3b | §5 `Theorem7.no_signaling`, `NoSignalingGeneral.bipartite_no_signaling` | **[AF]** | ✓ |
| E6 | "The **Type II dual-weight trace** / continuum Type III₁ classification / vN-algebra (vs one-particle) relative entropy is the cited **frontier**." | `formalization` (290–291); §11.4.3 | §4, §8 | **[frontier]** | ✓ |

## F. Corner / free SM fields / emergent spacetime (transport, not construction)

| # | Public claim | Appears in | Inventory entry | Status | Aligned |
|---|---|---|---|---|---|
| F1 | "The field's records are faithfully transported into the **capacity corner** P·End(H_R)·P (never the ambient identity), Born-weighted & area-bounded." | §1.1a (102); `realisations` | §6 `CornerConstruction` (`encoded_npoint`, `born_readout_entropy_le_area`, no-overclaim guards) | **[AF]** | ✓ |
| F2 | "Free **Standard-Model** content (CAR fermions, truncated-CCR gauge/Higgs, stress tensor) transports into the corner; bosonic modes carry an *explicit* truncation defect." | §1.1a (104); `realisations` | §6 `FreeFieldCorner.sm_free_field_in_corner`; §6d | **[AF]** | ✓ |
| F3 | "QIQT-H **accepts** a field algebra and **bounds** its records — it does **not construct** the field; capacity is a constraint, not a generator." | §1.1a (98, 100, 102, 104) | §6 (transport, not construction) | scope | ✓ |
| F4 | "Finite proto-spacetime: min-cut entanglement area is **not a metric** (triangle-inequality violation); a provably-metric replacement is given." | §1.1a (104, 106); `open-problems` | §6 `EmergentSpacetime.minCut_area_not_metric`, `embedDist_isPseudometric` | **[AF]** + **[no-go]** | ✓ |
| F5 | "Emergent **gravity** (dynamics), **not** emergent **spacetime** (the 3+1 manifold); interacting SM and the background-independent manifold are cited frontiers." | §1.1a (104, 106) | §6, §8 | **[frontier]** | ✓ |

## G. The Lieb / DPI / strong-subadditivity tower (the under-credited breadth)

| # | Public claim | Appears in | Inventory entry | Status | Aligned |
|---|---|---|---|---|---|
| G1 | "A **complete axiom-free** operator-convexity → Lieb's concavity → DPI → strong-subadditivity tower (`QIQTH/Entropy/`, 19 files) — the finite-dim Carlen machinery Mathlib lacks." | abstract (formal-verification para); `formalization` (Lieb table) | §6b (19 files, GENUINELY COMPLETE) | **[AF]** | ✓ (credited in A2 site + A3 paper) |
| G2 | "`strong_subadditivity` and `condMutualInfo_nonneg` are the capstones, standard-3." | `formalization`; AxiomAudit pins | §6b; §0 (pinned in A1) | **[AF]** | ✓ |
| G3 | "Donald's identity + the entire `ArakiInterface` relative-entropy layer (11 axioms discharged) + `EntropyBridge` + DPI + Klein positivity are theorems." | abstract; §11.4 banner | §6b, §6e | **[AF]** | ✓ (A1 fixed the ArakiInterface/RelEntPositivity "remain axioms" under-claims) |

## H. Lorentz naturalness (CPSUV) — the adversarially-tested frontier

| # | Public claim | Appears in | Inventory entry | Status | Aligned |
|---|---|---|---|---|---|
| H1 | "A naive 'finite capacity = local Lorentz-violating cutoff' is **excluded** (CPSUV: a sharp 3-momentum cutoff radiatively generates Δc²≠0); the escape condition is the matter kernel being Lorentz-scalar." | §1.1a (110); `open-problems` (Gap 4) | §5 / QG (`WardSpeedSplitting`) | **[AF]** | ✓ |
| H2 | "Whether QIQT-H **escapes** CPSUV is **NOT established** (~10–20%); the literal finite-matter horn faces a fork; the earlier 'escapes CPSUV' verdict was **retracted**." | §1.1a (110); `open-problems` | §7 (retraction discipline); §8 | scope + **[frontier]** | ✓ |

---

## Final consistency pass (A4)

**Method.** Every row above was checked in both directions: (i) the public wording carries the inventory's
qualifier (no `[AF]` claim for a `[frontier]` item; no unconditional claim for an `[AF·cond:H]` item); (ii) the
inventory entry exists at the cited file:line. The A1–A3 commits fixed the misalignments found; the residuals
below are tracked, not silent.

**Cross-source agreement (paper ⇄ site ⇄ inventory):**
- **Born reduced to P5** — consistent across abstract/§1.1a/§11.4, `formalization`/`ladder`/`selection`/`born`,
  inventory §1. ✓
- **H2 retired (single outcomes = λ + decoherence)** — after A3, consistent across the *whole* paper body
  (§1.1a, §5, §6.4, §6.8, §6.10, §7.5, §7.6, §10, §11) and the site (`about`/`born`/`idea`/`index`); inventory
  §1/§7. ✓ *(A3 was the load-bearing fix: §1.1a had the retraction but the body still contradicted it in ~10
  places.)*
- **1/4 = re-derivation of standard Sakharov, G carried** — consistent across §1.1a/`theory`/`realisations`/
  `statements/gr`, inventory §3. ✓
- **Audit scale (296 files / ~3,300 thms / 2,213 directives / 256 modules / budget 0)** — now identical in the
  abstract, the §11.4 banner, the `formalization` scale line, and inventory §0. ✓ *(was 830/192/2,010 in two
  places before A3.)*
- **One-particle BW unconditional; Type II trace = frontier** — consistent across `formalization`/§1.1a,
  inventory §4/§6c. ✓ *(A1 fixed the AxiomAudit "carried frontier" under-claim; A2 fixed the site "BW package
  cited" over-claim.)*
- **Lieb/DPI/SSA tower credited** — now in the abstract, `formalization`, inventory §6b. ✓ *(was uncredited.)*
- **Capacity postulate = two provably-distinct layers (count vs entropy)** — now identical across inventory §2/§9,
  plan §0 #1, `idea`/`theory`, and paper §1.1a. ✓ *(verified 100% from the hypothesis classes: `HolographicCapacityBound`
  = `log card R ≤ areaTerm` (count) vs `Phase5Master` = `S_vN+cgp ≤ areaTerm` (entropy); `EntropyNotCardinality`
  proves them inequivalent. Earlier surfaces glossed it as a single "finite entropy" or single "cardinality" claim.)*

**Claims we deliberately DO NOT make** (the honesty boundary — never assert these):
- ✗ "QIQT-H gives quantum gravity" / derives the value of **G** or ℓ_P. (Inventory §8 frontier; G is carried.)
- ✗ "An axiom-free **area law**." The area floor is **[AF·cond:HolographicCapacityBound]**; the area *form*
  (`S∝A`) is the conditional Sakharov bridge, not unconditional.
- ✗ "Finite **matter** Hilbert space" / "finite capacity forbids two records." (Retired; D2/D3 no-gos.)
- ✗ Conflating the **finite entropy** bound with a **finite record count** (or stating either alone as "the"
  postulate). `EntropyNotCardinality` proves the continuum entropy bound is *not* a count; the two are distinct
  layers — see C3. (This is the conflation that made the AdS/CFT "realises finiteness" reasoning fail.)
- ✗ "The **count layer is derived** from the area/entropy bound." It is not (the no-go forbids it); a finite
  operational count needs an **imported energy cutoff** and is then the **Bekenstein** bound — see C7.
- ✗ "The operational record-capacity bound is **new physics**." It is Holevo/Bekenstein-class; distinctive only
  if QIQT-H had a `Q_R` differing from standard generalized entropy — which it **cannot derive** (conditional
  no-go: `S_vN`-area + count-independence + λ-inertness). The only route is the explicit **max-entropy bridge
  postulate** (`Q_R = S_max`, the count, not `S_vN`) — a *new postulate, not a derivation* — predicting the
  capacity-of-entanglement gap `Q_R − S_gen = S_max − S_vN ~ √V_gen` — the no-go (`svn_underdetermines_smax`),
  the gap (`gap_nonneg`), the capacity of entanglement (`capEnt_nonneg`/`_eq_zero_iff`), and the conditional
  prediction (`distinctive_gap` under the `MaxEntropyCapacity` typeclass) are **PROVED axiom-free** in
  `MaxEntropyCapacity.lean`; the `√V_gen` coefficient + `G` = frontier (`QR_FRONTIER_PLAN.md`).
- ✗ "Born **derived** from unitarity." (Reduced to P5.)
- ✗ "The 1/4 is a **novel** result." (A machine-checked re-derivation of standard induced gravity.)
- ✗ "QIQT-H **escapes** CPSUV / is established Lorentz-natural." (~10–20%; the "escapes" verdict was retracted.)
- ✗ "Continuum Type III₁ / Type II trace / interacting SM / the 3+1 manifold are done." (Cited frontiers, §8.)

**Residual completeness gap (tracked, low risk — now substantially closed):** `#print axioms` is transitive, so
any lemma feeding an audited downstream theorem is already certified — soundness risk was always low; the gap was
in per-terminal-result coverage. The **headline terminal capstones backing this ledger are now individually
pinned** (verified std-3 via probe before pinning): the GR/crossed-product capstones and `SakharovRatio.sakharov_ratio`
were already pinned; A1 pinned the two Entropy/ capstones (`strong_subadditivity`, `condMutualInfo_nonneg`); and a
follow-up A4 pass pinned the `ValueSelection` actual-value/actual-history terminals (rows B5/§1), the Entropy/
Lieb–DPI tower rungs `trace_function_convex`/`star_inv_subadditive`/`gmean_mono`/`lieb_superadditive`/
`dpi_mixed_unitary`/`partial_trace_dpi` (row G1), the Einstein capstones `jacobson_einstein_equation_of_state`/
`einstein_tensor_eq_of_state` (rows D2/D3), and the crossed-product `covariance`/`modularAut_mul` (rows E2/E6).
What remains unpinned is minor, non-headline, and transitively certified.

**Verdict.** Every headline public claim now maps to an inventory entry with a matching qualifier; the paper, the
site, and the inventory agree on the load-bearing scope (Born→P5, H2 retired, 1/4 = re-derivation, finite =
entropy not matter, capacity conditional, the breadth credited). The alignment areas A1–A4 are complete.
