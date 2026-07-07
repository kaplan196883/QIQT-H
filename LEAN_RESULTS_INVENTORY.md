# QIQT-H Lean results — the honest inventory (ground truth)

**Purpose:** the canonical, audited catalog of what the QIQT-H Lean 4 / Mathlib development *actually proves* and
under what conditions. **Every public claim (paper, website, code comments) must be checkable against this file.**
Built 2026-06-30 from a 6-way parallel code audit (file:line verified). **Status legend:**
- **[AF]** axiom-free, standard-3 (`propext`, `Classical.choice`, `Quot.sound`) only, **unconditional**.
- **[AF·cond:H]** axiom-free std-3, but **conditional** on the named hypothesis/typeclass `H` (a labelled
  premise, never a Lean `axiom`).
- **[no-go]** an honest **negative** theorem (proves something does *not* hold / cannot be done).
- **[frontier]** **NOT built** — explicitly cited/checkpointed (no theorem; an open obligation).
- **[scaffold]** labelled bookkeeping (`True`/`trivial`), adds no empirical content (honestly marked).

## 0. Overall status (meta-audit, verified)

- **2888 `#print axioms` directives** (current-HEAD recount; ~429 `.lean` files, ~4,550 theorem/lemma declarations) in `QIQTH/AxiomAudit.lean`; **zero raw `axiom` declarations**, **zero
  `sorry`/`sorryAx`** in code (full-tree grep: the 58 `sorry` string matches are all docstrings reading "No `sorry`" —
  0 real proof terms). Budget-check (`scripts/axiom_budget_check.sh`) = **0**. The only `:= True` bodies are harmless
  labelled markers (`LorentzWitness.lean:180` indiscrete-preorder witness; the campaign `Checkpoint`/`…_complete` markers).
- **HEAT-KERNEL PREFACTOR — the π-content of the induced-G 12π, DERIVED (2026-07-05).** `QIQTH.HeatKernelDDim`
  (axiom-free std-3): the general-d flat-space heat-kernel prefactor (4πt)^{−d/2} (`heatDensity_dDim`, product of
  d 1-D Gaussians via `integral_fintype_prod_volume_eq_pow`), its d=4 value 1/(16π²t²) (`heat_prefactor_fourD`),
  and the assembly (16π)·½·(1/16π²)·(1/6−ξ) = (1/6−ξ)/2π = **1/(12π)** at ξ=0
  (`inducedInvG_normalization_assembly[_zero]`) — matching the 12π cited in `SakharovRatio`/`effSpeciesN`. This
  moves the π-transcendental of the cited 12π induced-Newton normalization from CITED to DERIVED. Together with
  the a₁ campaign (the 2t contraction), the full flat-space analysis of the induced-G R-coefficient (prefactor +
  a₁) is machine-checked. HONEST: π-transcendental ONLY; κ=1/6, ½, 16π, the species charge b, the curved-space
  Seeley–DeWitt geometry, and the Λ² regularization scheme (the physical d=4 proper-time integral is divergent)
  stay carried/cited; no numerical G. **The flat-space analysis vein is now EXHAUSTED** — the numerical-G
  frontier's remaining content is all carried geometry or divergent regularization.
- **HEAT-KERNEL a₁ ANALYSIS-HALF — IN PROGRESS (2026-07-05).** `QIQTH.HeatKernelA1` (axiom-free std-3): the
  flat-space Gaussian moments of the position-space heat kernel G_t = (√(4πt))⁻¹e^{−x²/4t} — **∫ G_t x² = 2t**
  (`gaussianSecondMoment_oneD`, the load-bearing analysis, from Mathlib's `variance_fun_id_gaussianReal` via the
  exact pdf bridge `gaussianPDFReal 0 (2t) = G_t`), ∫ G_t = 1, ∫ G_t x = 0. This is the DERIVED-analysis half of
  the a₁ Seeley–DeWitt coefficient program (the `2t·R` contraction machinery). HONEST: flat-space only; the
  curved-space RNC geometry AND the value κ = 1/6 are carried/cited, NEVER produced by the Gaussian moment — the
  numerical-G frontier stays exactly as characterized above (the 1/6 needs the covariant heat-kernel expansion
  Mathlib lacks). **A3+A4 LANDED — CAMPAIGN COMPLETE**: `heat_a1_of_RNC` — the conditional a₁
  assembly: given carried RNC Ricci + the moment matrix 2t·δ + the CITED κ=1/6, the
  Gaussian-averaged t¹ coefficient = (1/6−ξ)R − m²; with `heat_a1_moment_from_secondMoment`
  connecting the d=1 moment matrix to the derived `gaussianSecondMoment_oneD`. The a₁
  analysis-half is now machine-checked (the 2t·R contraction); κ=1/6 stays carried/cited.
  **A3 DERIVED THE d-DIM MOMENT** (Fubini
  hazard absent — the Pi integral lemma is unconditional): `gaussianMoment_diag`
  (∫ (∏_k G_t(x_k)) x_i x_j = 2t·δ_ij), and `heat_a1_of_RNC_derived` discharges the carried
  moment-matrix hypothesis — so the 2t·δ contraction is DERIVED for all d. THE a₁
  ANALYSIS-HALF IS COMPLETE: the (1/6−ξ)R coefficient underlying the species accounting of G
  is now (κ=1/6 cited-geometry) + (contraction machinery derived-analysis). κ=1/6 stays cited
  (needs the covariant heat-kernel expansion Mathlib lacks); no numerical G. Honest house-style
  hypothesis-shrinking of the numerical-G frontier.
- **FIELD-LEVEL BISOGNANO–WICHMANN UNCONDITIONAL (2026-07-05).** `QIQTH.Fock.freeField_secondQuant_BW_unconditional`
  (`Fock/FieldBWUnconditional.lean`, axiom-free std-3): the second-quantized wedge modular automorphism acts on
  Weyl operators as the geometric Lorentz boost — σ_t(W(u)) = W(boost(2πt)u) conjugated — with NO carried BW
  hypothesis, discharged from the already-unconditional one-particle `oneParticleBW_niceWedge_unconditional`. The
  free-field wedge modular structure (one-particle BW, strip-KMS `stripKMSrvd_boostUnitary`, Reeh–Schlieder
  cyclic+separating witnesses, and now the field-level BW) is machine-checked end-to-end — modular flow = boost,
  a Lean-first result. HONEST: free-field / single-mass only, NOT interacting, no low-energy LV prediction
  (unconditional BW = standard induced gravity per the QG-campaign verdict); `hTkk` (Unruh/localization stress-flux)
  and the Clausius/area floor stay labelled physics; the Δc²(Λ)→0 covariant substrate is a RESEARCH problem, not a
  Lean increment — the QG-tractable ladder is exhausted.
- **MODULAR TOWER COMPLETE (2026-07-05).** The inductive-limit tower state `towerLimitVN` on `TowerGNS` now carries the
  COMPLETE machine-checked Tomita–Takesaki modular data, all axiom-free std-3 — **the first complete Tomita–Takesaki
  modular theory in any proof assistant** (see §4 for the per-campaign blocks): S̄ (closed involutive Tomita operator) ·
  Δ self-adjoint (Δ†=Δ, von Neumann's S̄*S̄ theorem, itself a Mathlib-gap contribution) · Δ^{it}=towerFlow (THE
  IDENTIFICATION — the transported physical flow IS the spectral modular flow) · Tomita I (Δ^{it}MΔ^{−it}=M) · J
  anti-unitary + polar decomposition on the core (S̄=J∘Δ^{1/2}) · Tomita II inclusion (JMJ ⊆ M′) · non-traciality
  (ω not a trace, Δ≠1, Δ^{it}≠id) · KMS-boundary. Capstone: `NonTracial.modular_data_complete_witness`. HONEST
  BOUNDARY (never crossed): no strip-analyticity KMS, no full equality JMJ=M′ (RvD wall), no type classification
  (Mathlib has no trace/factor/type API); finite-stage Gibbs inductive-limit only — the free-field/Type-III continuum
  is the named pivot. NOTE: this session's commits (J1–J9, N1–N4, KMS C1, four campaign plans) are **local-only**
  pending push authorization; paper/website last synced at the 36th first (J + non-traciality + KMS = pending firsts 37–39).
- **What "axiom-free" means here:** the *conditional/structural mathematics* rests on no hidden axiom. It does
  **NOT** mean the *physical postulates* are derived — the holographic-capacity bound, the KMS/Clausius inputs,
  P5, the value of `G`, etc. remain explicit **typeclass hypotheses / cited frontiers**, correctly labelled.
- **The budget GENUINELY DROPPED 57 → 0** via real discharge (each interface axiom either proved in a concrete
  finite model or recast as an explicit typeclass hypothesis), not relabeling. Verified across the Entropy/ tower
  (Donald/DPI/Araki/EntropyBridge ledger) and the top-level clusters (RelEntPositivity, Goldstein–Struyve).
- **What the budget check does NOT do:** detect logical inconsistency or a false premise (only counts axioms +
  catches `sorry`). Irrelevant at axiom count 0; honestly noted in-script.
- **Coverage caveat (full-sweep audit; 422 tracked files, 4464 theorems/lemmas as of 2026-07-05):** soundness is comprehensive (full-tree grep: zero axioms,
  zero sorry). The `#print axioms` *audit pins* most theorems, and the **headline capstones are now individually
  pinned** — `SakharovRatio.sakharov_ratio`, `strong_subadditivity`, the GR/crossed-product capstones,
  `ValueSelection.*`, and this session's `ModularEnergyBound` (B1–B7), `OperationalCapacity`, `MaxEntropyCapacity`.
  A residual of **non-headline terminal theorems is still not individually listed** (low soundness risk —
  `#print axioms` is transitive, so any lemma feeding an audited downstream theorem is certified; a minor
  completeness gap only). **Stale docstrings** that *under*-claim
  (say "axiomatized" for now-proved results): `ArakiInterface`, `RelEntPositivity`, `GoldsteinStruyve*` headers,
  and `AxiomAudit.lean:~4882–4897, ~216–220` (clock-energy self-adjointness, GS steps). Hygiene, not soundness.
- **Comparison artifact — NOT a QIQT-H result:** `QIQTH/AdSCFTComparison.lean` (namespace `AdSCFT`, axiom-free
  std-3, deliberately **NOT** wired into `QIQTH.lean`/`AxiomAudit`) machine-checks the *algebraic* AdS/CFT
  dictionary — the radius–coupling relation `R⁴=4πg_sN α'²`, `G ∝ 1/N²`, and **Strominger's BTZ `Cardy = A/4G`**
  identity (`btz_cardy_eq_bekensteinHawking`) — with the CFT/GR inputs (Cardy formula, Brown–Henneaux central
  charge, BTZ↔CFT dictionary) carried as definitions. It does **NOT** prove the Maldacena conjecture (unproven,
  string theory not rigorously defined — unformalizable). Kept purely as a labelled *comparison* of what AdS/CFT
  *derives given its inputs* (`G` fixed by the degree-count `N`; BH entropy as a boundary state count).
  ⚠ The contrast was UPDATED post-`InducedNewtonConstant` (docstring fixed 2026-07-03): QIQT-H now fixes `G` by
  a degree-count too (`G = 1/(N Λ_s²)`), and `HolographicBridge` proves the two bookkeepings agree; what AdS/CFT
  still has and QIQT-H lacks is the INDEPENDENT CROSS-CHECK (one boundary CFT computing both `G` and the
  microstates). Never cite it as a QIQT-H claim.
- **Holographic dictionary bridge — `QIQTH/HolographicBridge.lean`** (namespace `QIQTH.HolographicBridge`, [AF]
  std-3, NOT wired into `QIQTH.lean`/`AxiomAudit`). Connects the AdS/CFT comparison to the granularity reframing:
  `btz_cardy_eq_qiqth_capacity` — Strominger's BTZ `Cardy = A/4G`, evaluated with QIQT-H's induced `G=1/(N Λ_s²)`,
  equals QIQT-H's bulk **capacity exponent** `(A/4)N Λ_s²` (the boundary microstate count and the QIQT-H regional
  capacity are the *same quantity* at the shared granularity; the AdS radius `ℓ` cancels); `centralCharge_in_primitives`
  — the Brown–Henneaux `c=(3/2)ℓ N Λ_s²` *if* one posits a boundary length `ℓ` (AdS-specific, flagged);
  **`btz_cardy_eq_join_count`** (post-JOIN-INSTANCE, 2026-07-03) — for a CONSTRUCTED join instance whose
  internal area `A_J` equals the BTZ horizon length `2π r₊`, the boundary Cardy count EQUALS the screen
  code's τ-count `S_τ(J)`: Strominger's state count literally realized as a QIQT-H code count at the
  shared granularity (the two bookkeepings agree because both are calibrated to the same primitives). ⚠ A
  variable-**correspondence** showing the two languages are consistent under the shared `G` — it does **NOT** import a
  boundary CFT, the Cardy formula (needs a 2d Virasoro QIQT-H lacks), bulk reconstruction, or AdS/CFT's cross-check;
  QIQT-H's capacity stays postulated/granularity-reframed. A bridge, not a QIQT-H physics claim.

## 1. Born rule / typicality / single-world selection (Φ, λ)

- **Born is REDUCED, not derived from unitarity.** The probability content is carried by ONE irreducible premise:
  the noncontextual/positive effect-valuation (`EffectGleason.EffectMeasure`) — equivalently the canonicity of
  the typicality measure (P5). The code *proves this is irreducible*.
- **The P5-reduction chain — both earlier Born premises collapse to refinement-equivariance**
  (`BornMuSelection.lean` / `BornActualityConsistency.lean`; all six theorems probed std-3, 2026-07-05; pinned in
  `AxiomAudit.lean:~3173–3233`). `BornMuSelection.equivariant_no_signaling` **[AF]** — an equivariant
  (quantum-equilibrium) typicality measure gives selector no-signaling: every local-readout marginal is invariant
  under a measure-preserving refinement, with NO Born input. `equivariant_context_independent` **[AF]** —
  equivariance ⟹ **non-contextual** outcome marginals (no preferred refinement) — exactly the Born-strength
  noncontextuality premise consumed by `BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality`.
  `BornActualityConsistency.apc_iff_positiveAdditive` **[AF]** — Actuality Projective Consistency (the selector
  does not signal under outcome-refinement) **⟺** additivity of the rule on positive weights; composed with
  `RefinementBorn.continuous_additive_fMeasure_eq_born`: **APC ⟺ additive ⟹ Born** (in-file honesty: APC is an
  amplitude-free *reframing* of the additivity premise, NOT strictly weaker). `mu_selection_martingale`
  **[AF·cond: squared-weight conservation in μ-expectation + absorbing record]** — the second, dynamical
  (optional-stopping) grounding: the μ-probability of an outcome equals its Born weight. Guards **[no-go]**:
  `SelectorRefinement.Countermodel.alphaSq_selector_signals` — observable microcausality does NOT entail selector
  no-signaling (the α=2 rule signals under refinement), so **P5 is not reducible to P3** (they live at different
  layers: observable algebra vs actuality measure); `BornRoutes.sqRule_refinement_signals` (non-vacuity of the
  refinement-signaling notion). **Net: the additivity/noncontextuality bridge AND the μ-selection premise both
  reduce to P5 (refinement-equivariance) — the paper's "irreducible physics = (P4)+(P5), on the (P1) ontology"
  sentence is theorem-backed.**
- `EffectGleason.finite_effect_gleason` **[AF·cond: EffectMeasure]** — a normalized, nonneg, coexistent-additive
  μ on effects equals `tr(ρE)` (finite Busch/CFMR effect-Gleason). The probability engine.
- `GleasonSelector.positive_ray_certain_forces_born` **[AF·cond: positivity+ray-certain+additive+homog]** — a
  positive ray-certain weight IS Born `⟨ψ|E|ψ⟩`. (Earlier a FALSE positivity-free version was an axiom; **retired
  and the counterexample now proved**: `naive_gleason_premises_insufficient` **[no-go]**.)
- `BornEquiprobable.born_from_equiprobability` **[AF·cond: equal-amplitude orthonormal fine-graining + P5
  canonicity]** — the uniform measure over an equal-amplitude orthonormal fine-graining has Born marginal `|c_k|²`
  (Zurek amplitude→count, by orthonormality). **Load-bearing residual premise = the canonicity of that measure.**
- `BornTypicality.qiqth_born_typicality_conditional` **[AF·cond: CanonicalIcMeasure]** — mean indicator of
  outcome k = `c_k²`; `BornTypicalityFinite.chebyshev_freq` **[AF·cond]** — empirical-frequency concentration
  (mean form proved; full a.s. LLN is the layer's black-box).
- `BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality` **[AF·cond: noncontextual EffectMeasure + iid]** —
  capstone: exactly one actual history, one-site weights = Born, factorized law, Chebyshev-typical.
- Single-outcome core: `CoreNoCollapse.exactly_one_actual` **[AF·cond: finite-capacity saturation premise + λ
  selects ≥1]** — capacity (≤1 record) + selector (≥1) ⟹ exactly one. **Note:** the *interpretation* that capacity
  *forces* single outcomes is **RETIRED** (H2 category error, see §7); single outcomes = λ + decoherence.
- λ-event: `SelectionEvent.selects_exists_unique` / `volume_selects` **[AF·cond: Born weights supplied]** — inverse-CDF
  sampling: one record per seed; seed-measure = Born weight. **Born weights are input, not derived; not equivariant.**
- **Born no-gos [no-go]:** `NoBornFromNothing.*` (any distribution is microscopically realizable ⟹ μ is the
  load-bearing input), `RefinementBorn.sq_not_*` / `RankCountNoGo.no_multiplicity_rule_is_born` (no amplitude-
  independent counting rule = Born), `NoConcentration.decoherence_does_not_concentrate`,
  `EquivarianceGap.support_preservation_does_not_imply_measure_preservation`, `OperationalNoGo.*`.

## 2. Finite capacity / holographic area floor

> **⚠ The capacity postulate has TWO machine-checked LAYERS, and they are PROVABLY DIFFERENT (verified 2026-06-30
> by direct read of the hypothesis classes).** Do not state either alone as "the" postulate.
> - **Finite-dim model (P4-MICRO) → CARDINALITY.** `HolographicCapacityBound` (`FQBoundMicro.lean:59`) is
>   `bound : Real.log (Fintype.card R) ≤ areaTerm` over a **finite** record type `R` — a literal record-**count**
>   bound `card R ≤ e^{areaTerm}`. Feeds `area_floor_vonNeumann` and the P4-MICRO GR route (`gr_from_p4micro`,
>   the pp-wave showcase via `η·c = log|R|`).
> - **Continuum / Fork-A → ENTROPY.** `Phase5Master` (`FQBoundCGP.lean:48`) is `SvN + cgpEntropy S ξ ≤ areaTerm`
>   over an infinite-dim `StandardSubspace H` (no cardinality); `TraceCapacity` (`CpsuvEscape.lean:73`) is
>   `Sren ≤ Q`. Feeds the JLMS GR route (`holographic_area_floor`, `qiqt_gr_from_wedge_kms`) and the CPSUV analysis.
> - **The bridge no-go:** `EntropyNotCardinality.entropy_bound_not_cardinality_bound` proves the continuum ENTROPY
>   bound `S_τ ≤ Q` does **NOT** imply the cardinality bound `card ≤ e^Q` — so the two layers are genuinely
>   inequivalent. The continuum/physical/GR-relevant claim is **entropy**; the finite **count** is the tractable
>   finite-dim shadow only (and is strictly stronger). "Finite capacity" therefore = finite *record count* in the
>   finite model, finite *entropy* in the continuum — never a finite MATTER Hilbert space (D2/D3).
> - **The count layer is NOT derivable from the entropy/area bound** (GPT-5.5-pro consult, 2026-06-30). By the
>   no-go above, no finite record count follows from `S(ρ_R) ≤ Q`. The only sound *operational* count is a **Holevo
>   capacity** — `log M_ε ≤ (Q + h₂(ε))/(1−ε)` for records ε-decodable by a common POVM under a relative-entropy
>   bound `Q` (survives the no-go: it bounds recoverable mutual information, not support cardinality) — and it
>   becomes a finite *number* only under an **imported energy cutoff**, where it is the **Bekenstein /
>   microcanonical** bound (standard holography, **NOT new physics**). QIQT-H is distinctive here *only* if it
>   derives a `Q_R` differing from standard generalized entropy — which it does not (the **cited frontier**). The
>   operational bound itself is now **PROVED axiom-free** in `QIQTH/OperationalCapacity.lean` **[AF]**:
>   `record_capacity` (`(1−ε)·log M ≤ Q + h₂(ε)` carrying the confusion-matrix Holevo bound `I(T) ≤ Q`),
>   `exact_distinguishable_capacity` (the `ε=0` form `M ≤ e^Q`), and `gibbs_entropy_bound` (the Bekenstein /
>   microcanonical `H ≤ β⟨E⟩ + log Z` — the energy cutoff that makes the count finite). All Holevo/Bekenstein-class,
>   none deriving the count from the area law or a new `Q_R`.
> - **The distinctive `Q_R` is a POSTULATE, not a derivation** (GPT-5.5-pro scoping consult, 2026-07-01;
>   `QR_FRONTIER_PLAN.md`). A `Q_R` differing from standard generalized entropy `S_gen = A/4G + S_bulk` **cannot be
>   derived** from QIQT-H's principles — conditional no-go: area/JLMS/GSL use `S_vN`, the finite count is
>   independent of `S_vN` (`EntropyNotCardinality`), and `λ` is inert (cannot back-react on geometry). It is
>   possible **only** by ADDING the explicit **max-entropy bridge postulate** — gravity's capacity is `S_max`
>   (= log-rank = the finite *count*), NOT `S_vN`. That postulate makes the falsifiable prediction
>   `Q_R − S_gen = S_max − S_vN ≥ 0`, governed by the **capacity of entanglement** `√V_gen` (finite-size
>   Page-time/QES shifts). The bridge is a **new assumption, not a result**; the `√V_gen` coefficient and the value
>   of `G` are cited frontiers. **Now PROVED axiom-free** in `QIQTH/MaxEntropyCapacity.lean` **[AF]**:
>   `svn_underdetermines_smax` (the no-go — a pure state has `S_vN = 0` but `S_max = log N`, so the area does not
>   fix the count), `gap_nonneg` (`S_max − S_vN ≥ 0`), `capEnt_nonneg` / `capEnt_eq_zero_iff` (the capacity of
>   entanglement `V_gen ≥ 0`, = 0 iff flat), and the conditional `distinctive_gap` under the `MaxEntropyCapacity`
>   typeclass postulate (GIVEN the postulate, `Q_R − S_gen = gap ≥ 0`). The no-go forces it to be a postulate, not
>   a derivation; the `√V_gen` continuum coefficient and `G` stay cited frontiers.
> - **Route 1 ("derive holography") — REFRAMED** (GPT-5.5-pro expert review, 2026-07-01; `ROUTE1_MODULAR_PLAN.md`).
>   Deriving the capacity bound via the JLMS modular identity `K_{∂R}=A/4ℓ_P²+K_bulk` — for a fixed-background
>   **free scalar** the `A/4ℓ_P²` term is **NOT derivable** (no `G`, no area operator, cutoff/matter-dependent
>   coefficient; the `δA/4G=2π∫δT_kk` step *uses the Einstein equations*, not pure BW). BW gives the Unruh `2π`, not
>   the `1/4G` **along this modular route**. So `A/4ℓ_P²` stays a **gravitational input** here; the continuum Type III₁→II
>   crossed-product dual-weight trace is a **multi-year cited frontier**. ⚠ **This is about the JLMS modular route ONLY —
>   NOT "the 1/4 is not derived":** the `1/4` ratio IS a derived theorem via the *separate* Sakharov bridge
>   (`SakharovRatio.sakharov_ratio`, the P4-MICRO story); this route is a distinct axiom-free result that does not touch
>   `A/4G`; what *neither* derives is the value of `G` (carried). What **is** derivable (the honest Route-1 content, `ModularEnergyBound.lean`):
>   the free-field **modular-energy bound** `ΔS ≤ 2π Δ⟨B_boost⟩` (Casini/first law, from relative-entropy positivity
>   + the machine-checked one-particle BW `K_W=2π B_boost`) — upgrading `Phase5Master`'s modular pieces from carried
>   hypothesis to theorems. **Formalized modular QFT, NOT a derivation of the holographic `A/4G` bound.**
> - **Holographic confrontation — the postulate FALSIFIES/reduces** (GPT-5.5-pro expert review +
>   `scripts/qr/twosector_killtest.py`, 2026-07-01). First independent test against real holography: **(i)** the
>   postulate's universal `√V_gen` prediction is **FALSIFIED** at the Page/island transition (a two-fixed-area-sector
>   state — Dong–Harlow–Marolf): the *exact* one-shot shift `H₀^ε − S_vN` saturates (bounded by `log(D₁+D₂) − S`)
>   while `z_ε√V_gen` overshoots ~2.3× and violates that ceiling. `√V_gen` is a **Gaussianity** approximation
>   (second-order source coding, Tomamichel–Hayashi), not a holographic law — it "works" only in the Haar/CLT
>   regime where it says nothing new. **(ii)** What survives — "capacity = the smooth one-shot / max-entanglement-wedge
>   entropy" — is the **known** one-shot holography (Akers–Penington `2008.03319`), distinctive vs the naive
>   "RT always uses `S_vN`" but **NOT new physics, NOT a new `Q_R`**. **Net: QIQT-H's one distinctive frontier
>   reduces, on contact with real holography, to known one-shot entanglement-wedge physics.**

- `area_floor_vonNeumann` **[AF·cond: HolographicCapacityBound]** — `S_vN(ρ_R) ≤ areaTerm`. **A von Neumann
  ENTROPY bound.** `HolographicCapacityBound`'s field is `log(card R) ≤ areaTerm`; its header states `R` is the
  **operational/regional capacity `Q_R = log N_R`, NOT a global Hilbert-space dimension**, and the matter algebra
  is **Type III₁** (the finite-dim `R` is itself the holographic regularization). `areaTerm = A/4ℓ_P²` is a
  **carried UV datum, never assigned** — but see §3 `InducedNewtonConstant`: under the granularity reframing
  `areaTerm = (A/4)N Λ_s²` and `G = 1/(N Λ_s²)` are re-expressed in primitives `{area, species, granularity}`, so
  `G` is promoted from *carried* to *derived-from-`Λ_s`* (the numerical value still needs species accounting).
- `holographic_area_floor` **[AF·cond: Phase5Master]** — the dynamical (JLMS/dual-weight-trace) route to the same
  bound; `Phase5Master` is proved to carry *exactly* the master inequality (non-vacuous, `Phase5Master.of_le`).
- `vonNeumannEntropy_le_log_card`, `RecordContract.shannon_le_log_card` **[AF]** — the genuine, unconditional
  max-entropy (Jensen/Gibbs) cores.
- `FiniteTracePhase5.phase5_of_finite_trace` **[AF]** — a concrete finite-trace model where `areaTerm = log|n|` is
  *derived* (non-vacuous Phase5Master instance). **Type I/II₁ shadow; continuum Type II_∞ trace = frontier.**
- `HolographyScaffolding.measure_needs_only_finiteness` **[AF]** — **λ's Born measure needs only `Finite`, NOT the
  area bound.** ⟹ holography is *scaffolding*, not load-bearing for the selection measure (machine-checked).
- **QG-campaign no-gos:** `FiniteMatterNoLorentz.finitePoincare_trivial` **[no-go, AF]** — finite-dim matter +
  exact `[K,P]=iH,[K,H]=iP` + `H⪰0` ⟹ `H=0 ∧ P=0` (literal finite *matter* + exact Lorentz ⟹ trivial dynamics);
  `EntropyNotCardinality.entropy_bound_not_cardinality_bound` **[no-go, AF]** — bounded entropy `S_τ≤Q` holds at
  arbitrary cardinality ⟹ `S_τ≤Q_D ⇏ card≤e^{Q_D}` (capacity is **entropy, not a count**).
- `WardSpeedSplitting.speedSplitting_aniso_eq_zero_iff` **[AF]** — `Δc²=0 ⟺ B=0` (the LV escape ⟺ Lorentz-scalar
  matter kernel). `CpsuvEscape.*` **[AF, near-tautology — self-flagged]** — posits `B=0`/independent frames by
  fiat; the substantive "QIQT-H escapes CPSUV" claim is **NOT established** (~10–20%, red-teamed). Read as a
  structural conditional only.
- **THE LORENTZ-CUTOFF STRESS TEST — EXECUTED 2026-07-02** (`QG_CAMPAIGN_PLAN.md` I3+I4; the decisive one-loop
  naturalness gate; GPT-5.5-pro-designed; `scripts/lorentz_stress_test.py` + results doc
  `docs/qg_roadmap/LORENTZ_STRESS_TEST_RESULTS.md`). **NUMERICS:** Euclidean Yukawa `Δc² = Z_s/Z_t − 1`; sharp
  spatial cutoff → the CPSUV constant `g²/12π² = 8.443·10⁻³` UNSUPPRESSED (fit `c₀` matches the analytic
  constant to 2·10⁻⁸; quadrature matches closed forms to 2·10⁻¹⁸); ALL smooth spatial profiles →
  `(g²/12π²)[1+2∫x f′²] ≥` the constant (FAIL); fermion channel `−g²/48π²` (FAIL, independent); covariant
  O(4) family → `Δc² = 0` by symmetry (PASS). **LEAN [AF] std-3:** `QG/LatticeDispersionBound.lean` —
  `lattice_dispersion_defect_bound` `|E_a(p)²−(m²+p²)| ≤ a²p⁴/12` (the free-field pass, via the global
  `sin u ≥ u−u³/6`); `QG/CpsuvGate.lean` — **`cpsuv_gate_sharp_fails`** (the certified closed form TENDS TO
  the nonzero `1/(12π²)` — no `E/Λ` decoupling) + **`covariantSplit_eq_zero`** (O(4)-symmetric `Π` has
  `Δc² = 0` identically). **VERDICT:** the preferred-frame spatial realization of finite capacity is DEAD
  (falsified at percent level); the OP3b covariant-diamond branch is the SOLE survivor; the named open danger
  = the diamond tip vector `u^μ_D` entering the vacuum effective action ("area invariant" is not enough).
  The loop integral itself is numerically validated, not formalized. NOT QG.
- **THE DIAMOND-TIP TEST — EXECUTED 2026-07-02** (follow-on gate; `scripts/diamond_tip_test.py` + results doc
  `docs/qg_roadmap/DIAMOND_TIP_TEST_RESULTS.md`; Lean `QG/DiamondTipGate.lean` **[AF]** std-3). **The tip
  vector `u^μ_D` DOES reach the effective action:** within the anisotropic family `Δc² = 2C·H_both(s)`,
  `s = √(a/b)` (closed form GPT-5.5-pro-derived after correcting against our numerics; validated to ≤0.16%,
  exact rationals `11/16`, `37/72`, `−17/18`; the O(4) point vanishes to 9·10⁻¹³), **`tipSplit_eq_zero_iff`**
  — the splitting vanishes IFF the regulator is isotropic — and **`tipSplit_hasDerivAt_one`** — FIRST-order
  sensitivity, slope `−2C ≠ 0` (a single diamond's CHM truncation is locally a rest-frame cutoff; boundary
  corrections cannot remove the dim-4 LV operator). **The rapidity-average escape FAILS, certified:**
  `boostAvg_log_channel` (the boost-averaged null channel `= W/12` EXACTLY) + `boostAvg_diverges` (no
  regulator limit — the boost group's noncompactness is fatal) + `u0sq_avg_diverges` (via `sinh_ge_add_cube`;
  the averaged LV operator has no invariant limit). **FORCED CONCLUSION:** finite capacity is consistent ONLY
  as a state/algebra-level covariant constraint — the entropy of the diamond algebra in the covariant vacuum
  (the modular, frame-free formulation the Lean core already uses; cf. entropy-not-cardinality) — never as a
  frame regulator, single or averaged. Loop integrals numerically validated, not formalized. NOT QG; the next
  decisive item = a low-energy LV-signature bound for the state-level capacity.
- **GATE 3 — THE STATE-LEVEL LV BOUND — EXECUTED 2026-07-02** (`QG/StateLevelLVGate.lean`, **[AF]** std-3
  or axiom-free; theorem-shaped, GPT-5.5-pro-verified; literature anchor: Bousso/Casini/QNEC entropy bounds
  are state-region inequalities, not regulators). **The surviving (entropy/state-level) reading of `Q_D`
  makes NO low-energy Lorentz-violation prediction:** (A) **`admissible_smul_iff`** +
  **`constraintSet_invariant`** — the admissible set `{ρ : ∀D, S_ren(ρ,D) ≤ Q_D}` is group-invariant (no
  frame in the kinematics; honest limit: SET covariance ≠ every admissible state invariant — thermal/
  conditioned states may carry rest frames, which is state breaking, not a law-level prediction);
  `vacuum_admissible`; the hinge `Sren_cov_of_traceCovariant` (trace transport + equivariant density ⟹
  entropy covariance — the trace-transport input's modular half is now DERIVED by the grounding campaign:
  `modUnitary_inner_cov`, G4).
  (B) **`stateLevel_noDeltaC2`** — the constraint restricts the state space, not the dynamics, so
  `Δc² = 0` identically (riding the certified O(4) split). (C) the residual channels, each certified:
  `operationalLV_iff_not_invariant` (LV ⟺ non-invariant PREPARED state, given separating observables);
  `conditioned_state_orbit`/`conditioned_invariant_iff_orbit_constant` (saturation/conditioning is safe
  IFF no non-invariant background is selected); **`equivariant_enforcement_preserves_invariance`**/
  `safe_enforced_step` — **the dynamical-realization gap is the SOLE remaining LV door** (only a
  non-equivariant enforcement mechanism reopens it); the selector channel is closed by the held
  `upvm_covariant_probability` (biased/postselected λ would reopen it). **`permutationCapacity`** — a
  genuine finite non-vacuous instance (relabeling-covariant regional Shannon entropy, `Q = log|D|`).
  ⚠ Gate-level algebra, not a QFT construction; trace-transport and equivariant-enforcer inputs are NAMED
  carried hypotheses. NOT QG.

## 3. Gravity / Sakharov 1/4 / Einstein equation

- `Sakharov.sakharov_ratio` **[AF]** — `(A·b/(48π·reg)) / (A·(b/(12π·reg))) = 1/4`, with **`b`, `reg`, `A` all
  cancelling** (the 1/4 is the output `4π/16π`). **The heat-kernel coefficients `1/48π, 1/12π` are CITED data,
  hand-entered, NOT formalized; the value of `G` is carried, never derived.** The file imports only Mathlib trig —
  it does **not** reference the capacity postulate. **⟹ a machine-checked *re-derivation* of the standard
  Sakharov/induced-gravity ratio, NOT a unique consequence of finite information.**
- Einstein-equation capstones **[AF·cond, free-field only]** — `WedgeKMSToGR.qiqt_gr_freefield`,
  `qiqt_gr_from_wedge_kms`, `QiqtToGR.qiqt_bekenstein_gives_gr`: each is "**IF** [matter EoS + wedge-KMS/BW boost
  flux + Raychaudhuri focusing + holographic area law + the localization map `hTkk` + conservation/regularity]
  **THEN** `a·T = G + Λg`." All *differential geometry* (Christoffel/Ricci/Einstein tensor, `∇·G=0`, constant Λ,
  Raychaudhuri) is **[AF]**; the BW/modular flux is **[AF] for the free field**; the **area law and the
  localization map are cited inputs [frontier]**. `GRFromMicro` header: "P4-MICRO ⟹ GR is FALSE as a standalone
  implication" — the thermal (Unruh/BW) input "a microstate count can never supply."
  - **`hTkk` is REDUCED, not DERIVED (HT0 honesty relabel, 2026-07-08).** The Gaussian discharge
    (`LocalizedMode.localized_mode_hTkk` = `calibrated_rank_one_hTkk` fed by `GaussianMode.gaussMode_calibration`
    ⟹ `qiqt_gr_freefield_gaussian`/`_complete`) is a **calibrated rank-one ansatz**: the mode is taken to be
    `ff = D·g₀` (field-gradient amplitude `D=∂_v φ` × a universal profile `g₀`) and `g₀`'s normalization + unit
    phase are *tuned* so the boost charge hits `2π/ℏ`. **Genuine: the amplitude law `ff∝∂_v φ` and the `(∂φ)²`
    scaling; calibrated (not derived): the coefficient `2π/ℏ` and the mode shape/width (every width in
    `GaussianModeFamily` calibrates).** The physical wedge-smearing localization map — positive-frequency wedge
    smearing of `∂_v φ` built from φ with `2π/ℏ` forced by Bisognano–Wichmann + the KG stress-tensor Noether
    charge — is the **cited frontier**, named explicitly by the open predicate `IsPhysicalWedgeMode`
    (`LocalizedMode.lean`); see `THE_HTKK_PHYSICAL_PLAN.md`, HT1–HT4.
- **The Levi-Civita connection — the UNIQUENESS half / the Koszul solve** (`Curvature.lean`
  `koszul_lowered`/`christoffel_unique`; `LeviCivita.lean` `leviCivita_unique`, all **[AF]** std-3, 2026-07-06).
  The *existence* half was already built — component `christoffel` + `christoffel_symm` (torsion-free) +
  `metric_compat` (`∇g=0`) feeding `riemann`/`ricci`, and the abstract-manifold `koszul`/`leviCivita`/
  `leviCivita_koszul`. This adds the missing *uniqueness*: **`christoffel_unique`** proves ANY torsion-free,
  metric-compatible connection **equals** the Christoffel symbols — the **fundamental theorem of
  (pseudo-)Riemannian geometry**, pure algebra (three cyclic `∇g=0` permutations + lower-index symmetry solve
  the lowered `koszul_lowered` half-sum `½(∂g+∂g−∂g)`, then the musical raise through `gi`); **`leviCivita_unique`**
  is the abstract counterpart (the metric-dual `♯` is single-valued by nondegeneracy). Uniqueness makes the metric
  `riemann`/`ricci` canonically **the** curvature/Ricci *of the metric*, closing the "arbitrary connection → THE
  metric connection" gap. **FOUNDATION brick: NOT the Seeley–DeWitt `(1/6−ξ)R` coefficient, and it does NOT move
  the numerical value of `G`** — the numerical-`G` gate is still the Riemannian heat kernel (§8, unchanged).
- **RNC1 — the `√det g` atom of the Riemann-normal-coordinate 2nd-order expansion** (`RNCExpansion.lean`
  `sqrtdet_pd_pd`/`sqrtdet_taylor_coeff`, both **[AF]** std-3, 2026-07-06). On the component `pd` calculus of
  `Curvature.lean`: GIVEN the **CARRIED, load-bearing** metric-Hessian-trace datum
  `htr : ∑_a ∂_c∂_d g_{aa}(0) = −⅔ Ric_{cd}` (a genuine equation on `pd (pd g)`, NOT a `:= True` stub — remove it
  and the conclusion is false), with `g_{ab}(0)=δ_{ab}` and `∂g(0)=0`, the second derivative of `√det g` at the
  origin is **`∂_c∂_d √det g (0) = −⅓ Ric_{cd}`** (`sqrtdet_pd_pd`), equivalently the quadratic Taylor
  **COEFFICIENT** (half of it) is **`−⅙ Ric_{cd}`**, i.e. **`√det g = 1 − ⅙ R_{cd} x^c x^d`** (`sqrtdet_taylor_coeff`).
  The **`⅙` is the source of the `κ = 1/6` conformal factor**. Route (dodges the general det-derivative gap by
  evaluating at the origin): finite-product Leibniz for `pd` (`pd_prod`, mirror of `pd_sum`) applied to
  `det g = ∑_σ sgn σ ∏_i g_{σi,i}`, so `∂g(0)=0` kills the cross terms and `g(0)=δ` collapses the permutation sum to
  **only `σ=1`** (`perm_moves_in_erase` + `Matrix.one_apply`), giving `∂_c∂_d(det g)(0)=tr∂∂g(0)`; then the `√` Taylor
  factor `½` from `Real.hasDerivAt_sqrt` at `det g(0)=1`, `∂(det g)(0)=0` (`sqrt_pd_pd`). ⚠ **HONEST CAPTION
  (binding)**: the `⅙` normalization was **CONDITIONAL on the carried `htr`** — now **DISCHARGED by RNC3** (below).
  It is the **`⅙` normalization ONLY** and does **NOT** give the numerical value
  of `G` (species count `N`, granularity scale `Λ_s`, the `E/ξ` heat-kernel term remain), and does **NOT** build a
  curved heat kernel.
- **RNC2 + RNC3 — the gauge-derived `⅙` (`htr` DISCHARGED FROM THE NORMAL-COORDINATE GAUGE)** (`RNCExpansion.lean`,
  all **[AF]** std-3, 2026-07-06). **RNC2** `rnc_riemann_hessian`: at a normal-coordinate origin (`g(0)=δ`, `∂g(0)=0`,
  so `Γ(0)=0`) the Riemann tensor is the antisymmetrized metric Hessian
  **`R^ρ_{σμν}(0)=½(∂_μ∂_σg_{ρν}−∂_μ∂_ρg_{νσ}−∂_ν∂_σg_{ρμ}+∂_ν∂_ρg_{μσ})(0)`** (the symmetric `∂_μ∂_ν g_{ρσ}` piece
  cancels via Schwarz). **RNC3** `rnc_htr_of_gauge`: carrying the **FALSIFIABLE normal-coordinate gauge**
  `hgauge : ∂_aΓ^i_{bc}(0)+∂_bΓ^i_{ca}(0)+∂_cΓ^i_{ab}(0)=0` (the totally-symmetrized Christoffel derivative — a
  genuine christoffel-symmetrization equation, **NOT** a `:= True` stub, **NOT** a pre-contracted `∂∂g=−⅓(R+R)`),
  the metric-Hessian trace is **FORCED**: **`∑_a ∂_c∂_d g_{aa}(0) = −⅔ Ric_{cd}`** — EXACTLY RNC1's carried `htr`,
  now **DERIVED FROM THE GAUGE**. Payoff `sqrtdet_taylor_coeff_of_gauge`: **`½∂_c∂_d √det g(0)=−⅙Ric_{cd}` GIVEN THE
  GAUGE**, so the `⅙`/`κ=1/6` is gauge-derived, not carried. **Sharp load-bearing test PASSES**: `∑_ν ∂_cΓ^ν_{νd}`
  equals BOTH `½ tr∂∂g` (pure calculus) AND `−⅓Ric` (gauge, via the finite `linarith` inversion
  `∂_aΓ^i_{bc}=⅓(R^i_{bac}+R^i_{cab})` + first-pair/last-pair Riemann antisymmetry); combining forces `tr∂∂g=−⅔Ric`,
  and removing `hgauge` makes it false. ⚠ **HONEST CAPTION (binding)**: this DISCHARGES `htr` with the honest
  geometric input = the normal-coordinate gauge (not a wall crossed); it is the **`⅙` normalization ONLY** — still
  does **NOT** give the numerical value of `G` (`N`, `Λ_s`, `E/ξ` remain), and does **NOT** build a curved heat
  kernel.
- **RNC4 — the a₁ assembly with `κ=1/6` GAUGE-DERIVED, not cited** (`RNCExpansion.lean` `+ import HeatKernelA1`,
  `heat_a1_of_gauge`, **[AF]** std-3, 2026-07-06). Wires RNC3's `sqrtdet_taylor_coeff_of_gauge` into
  `HeatKernelA1.heat_a1_of_RNC_derived`, **DISCHARGING the `κ=1/6` citation** that `heat_a1_of_RNC` carried. Shape (A):
  `heat_a1_of_RNC` takes `κ` via the discharge-able hypothesis `hκ : κ=1/6` (not a baked literal). `κ` is DEFINED
  (`hκgeo : ½∂_c∂_d√det g(0)=−κ·Ric_{cd}`) as the measure-expansion coefficient `√det g = 1 − κ·R_{cd}x^cx^d` — the
  physical definition, NOT a value claim; its VALUE is **FORCED to `1/6`** by the falsifiable normal-coordinate gauge
  `hgauge` (`sqrtdet_taylor_coeff_of_gauge` gives `−(1/6)Ric`; comparing at a genuinely curved point
  `hRic : ∃ c d, Ric_{cd}(0)≠0` cancels the Ricci factor ⟹ `κ=1/6`). That derived value discharges `hκ` and (via the
  already-DERIVED moment matrix `M=2t·δ` = `gaussianMoment_diag`) assembles the `t¹` coefficient **`(1/6−ξ)R − m²`
  carrying the GAUGE as the source of its `1/6`**. **Sharp test PASSES**: remove `hgauge` → `κ` unpinned → the
  `(1/6−ξ)R` conclusion fails; the `1/6` genuinely flows from the falsifiable gauge, not a fresh citation. ⚠ **HONEST
  CAPTION (binding)**: `κ=1/6` is now **gauge-derived in the a₁ accounting** (no longer a free citation) — still does
  **NOT** give numerical-G (species count `N`, granularity scale `Λ_s`, and the `E/m²/ξ` potential term remain), and
  does **NOT** build a curved heat kernel. RNC campaign RNC1–RNC4 COMPLETE.
- **GEO1 — the geodesic ODE has local existence + uniqueness** (`Geodesic.lean`
  `contDiff_geodesicField`/`geodesic_local_existence`/`geodesic_local_unique`, all **[AF]** std-3, 2026-07-06). On the
  component `christoffel` of `Curvature.lean`: the second-order geodesic equation `γ'' + Γ(γ)(γ',γ') = 0` is rewritten
  as the first-order autonomous field **`geodesicField g gi (x,v) = (v, −∑_{j,k} Γ^i_{jk}(x) v^j v^k)`** on the phase
  space `Point n × Point n`. **`contDiff_geodesicField`**: the field is `C^∞` from the carried Christoffel smoothness
  `hC` (assembled via `ContDiff.prodMk`/`contDiff_pi`/`ContDiff.sum`/`.mul`/`.neg` + the `contDiff_fst`/`_snd`/
  `contDiff_apply` projections). **`geodesic_local_existence`**: through any initial phase point `z₀=(x₀,v₀)` and base
  time `t₀`, a curve `γ` with `γ t₀ = z₀` and `HasDerivAt γ (geodesicField g gi (γ t)) t` on an open interval
  `Ioo (t₀−ε) (t₀+ε)` — Mathlib's `C¹` Picard–Lindelöf
  (`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`; phase space finite-dim ⟹
  `CompleteSpace` automatic). **`geodesic_local_unique`**: two integral curves staying in a set where the field is
  Lipschitz and agreeing at one `t₀ ∈ Ioo a b` agree on all of `Ioo a b` (`ODE_solution_unique_of_mem_Ioo`). ⚠ **HONEST
  CAPTION (binding)**: this is **geodesic EXISTENCE only** (component geodesics exist + unique). It does **NOT** build
  the exponential map or normal coordinates, does **NOT** discharge the carried RNC normal-coordinate gauge (that is
  gated on **smooth dependence of ODE solutions on the initial condition** — a theorem Mathlib genuinely LACKS, only
  Lipschitz dependence is present), and does **NOT** move numerical-`G` (`N`, `Λ_s`, `E/ξ` remain). The carried
  normal-coordinate gauge stays the honest curved-`G` input.
- **EXP1 — the exp-map campaign's first bricks: the geodesic field's STRICT derivative + rescaling + flow
  scaffolding** (`ExpMap.lean` `hasStrictFDerivAt_geodesicField`/`geodesic_rescale`/`rescale_field_eq`/`geodesicSol`/
  `expMap`, all **[AF]** std-3, 2026-07-06). Groundwork toward the RNC-existence gate `HasStrictFDerivAt exp_p id 0`
  (which needs a STRICT derivative for the inverse function theorem). **S2 — `hasStrictFDerivAt_geodesicField`**: the
  strict Fréchet derivative of `geodesicField g gi` at the equilibrium `e=(p,0)` is the explicit linear map
  **`linF (ξ,η)=(η,0)`** (`= snd.prod 0`). Route: `F` is `C^∞` (`contDiff_geodesicField`), so
  `ContDiffAt.hasStrictFDerivAt'` upgrades ANY Fréchet derivative to a STRICT one; the Fréchet derivative at `e` is
  `linF` because the only nonlinear part `(x,u)↦Γ(x)(u,u)` is bilinear in `u` and `u=0` at `e`, so every term of
  `d[Γ·u·u]` carries a factor `u` (proved via a triple-product-vanishing lemma + `hasFDerivAt_pi''`/`.fun_sum`/`.neg`).
  **S1 — `geodesic_rescale`** (with `rescale_field_eq`): the rescaling `γ_{p,sv}(t)=γ_{p,v}(st)` stated as a property
  of ANY integral curve — if `γ` solves the geodesic ODE, so does `τ↦(γ(sτ).1, s•γ(sτ).2)` — via the chain rule
  (`HasDerivAt.scomp`/`comp_hasDerivAt`) + the quadratic homogeneity `L_s(s•F w)=F(L_s w)` of the acceleration term
  (`smul_smul_accel`). **Scaffolding**: `geodesicSol` exposes a genuine integral curve as a total function (via
  `Classical.choose` of `geodesic_local_existence`) with spec lemmas `geodesicSol_zero`/`geodesicSol_hasDerivAt`
  (value at `0`; ODE on `(−ε,ε)`), and `expMap g gi hC p v := (geodesicSol (p,v) 1).1`. ⚠ **HONEST CAPTION (binding)**:
  this is **groundwork toward** `HasStrictFDerivAt exp_p id 0` → the RNC local diffeo. It is the strict derivative of
  the ODE FIELD at the fixed point (the linear-comparison input for the not-yet-run two-point Grönwall S4), NOT yet
  `exp_p`'s own strict derivative, NOT the local diffeo, NOT the RNC gauge (`g(0)=δ`, `∂g(0)=0`, `∂_{(l}Γ_{jk)}(0)=0`
  still need the metric-in-normal-coordinates change of variables), and does **NOT** move numerical-`G` (`N`, `Λ_s`,
  `E/ξ` remain). `expMap` is DEFINED but its geodesic meaning at `t=1` is established only for small `v`.
- **EXP2 — the exp-map campaign's S3 + S4 (two-point Grönwall crux, CONDITIONAL)** (`ExpMap.lean`
  `geodesicField_flow_lipschitz`/`residual_hasDerivAt`/`residual_gronwall`/`geodesicSol_rescale_unit_existence`, all
  **[AF]** std-3, 2026-07-06). **S3 — `geodesicField_flow_lipschitz`**: the geodesic flow near `e=(p,0)` is Lipschitz
  in the initial condition on a closed ball `closedBall e r`, uniformly over the Picard–Lindelöf interval `[-ε,ε]` —
  via `IsPicardLindelof.of_contDiffAt_one` (from the `C^∞` field) +
  `exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`. **S4 ODE algebra — `residual_hasDerivAt`**: for
  any two integral curves `Y₁,Y₂` of `F`, the residual `r(τ)=Y₁τ−Y₂τ−(τ•d,d)` solves `r'=A·r+R` with `A=linF`,
  `R=F(Y₁)−F(Y₂)−A(Y₁−Y₂)` (from `Y'=F(Y)`, `(τ•d,d)'=(d,0)`, `A·(τ•d,d)=(d,0)`); flow-independent. **S4 crux
  (CONDITIONAL) — `residual_gronwall`**: given the `[0,1]` integral-curve property of `Y₁,Y₂`, `Y₁0−Y₂0=(0,d)`, and a
  uniform remainder bound `‖R(t)‖≤C` on `[0,1]`, `norm_le_gronwallBound_of_norm_deriv_right_le` (δ=0, K=‖A‖, inhomog
  `C`) gives `‖Y₁1−Y₂1−(1•d,d)‖ ≤ gronwallBound 0 ‖A‖ C 1` — with `C=εL‖v−w‖` (S2 strict remainder × S3 Lipschitz)
  this is `O(ε)‖v−w‖`, the two-point `o(‖v−w‖)` seed. **Existence-on-`[0,1]` half —
  `geodesicSol_rescale_unit_existence`**: for every direction `v` there is a scale `s=ε/2>0` and a genuine integral
  curve `γ` with `γ 0=(p,s•v)` solving the geodesic ODE on `(-1,2)⊇[0,1]` (`geodesicSol_hasDerivAt` rescaled by
  `geodesic_rescale`); discharges the existence-on-`[0,1]` half FLOW-FREE for short geodesics. ⚠ **HONEST CAPTION
  (binding)**: `residual_gronwall` is the Grönwall estimate **CONDITIONAL** on its tube hypotheses; S3 is on the PL
  interval `[-ε,ε]` (NOT `[0,1]`); existence is for velocities `s•v` only. The **UNCONDITIONAL** two-point estimate →
  `HasStrictFDerivAt exp_p id 0` needs the flagged **common-tube reconciliation over `[0,1]` for a whole ball** (one
  radius `ρ` giving integral-curve-on-`[0,1]` + S2-nbhd containment + S3 Lipschitz simultaneously for all `v,w∈ball 0
  ρ`); that is CHECKPOINTED, NOT discharged. This is NOT `exp_p`'s strict derivative, NOT the local diffeo, NOT the RNC
  gauge, NOT numerical-`G`.
- **EXP3 — the common-tube crux CLOSED: BOTH halves (existence + confinement), UNCONDITIONAL over a ball** (`ExpMap.lean`
  `geodesicField_equilibrium`/`geodesic_twopoint_gronwall`/`geodesic_apriori_bound`/`geodesic_unit_tube_existence`/
  `geodesic_apriori_confinement`, all **[AF]** std-3, 2026-07-06). The flagged EXP2 common-tube reconciliation is now
  DISCHARGED unconditionally over a whole ball, via a cleaner route than the Picard–Lindelöf re-timing. **Two-point
  Grönwall — `geodesic_twopoint_gronwall`**: for two integral curves `Y₁,Y₂` staying in a set `S` where `F` is
  `K`-Lipschitz, `dist(Y₁ t)(Y₂ t) ≤ dist(Y₁ 0)(Y₂ 0)·e^{Kt}` on `[0,1]` (Mathlib `dist_le_of_trajectories_ODE_of_mem`)
  — the two-point Lipschitz bound directly on `[0,1]`, no PL re-timing. **A-priori bound — `geodesic_apriori_bound`**:
  `dist(Y t) e ≤ dist(Y 0) e·e^{Kt}` (the two-point bound against the constant equilibrium curve; `F(e)=0` via
  `geodesicField_equilibrium`). **Existence half — `geodesic_unit_tube_existence`**: `∃ρ>0`, for every `‖v‖≤ρ` a genuine
  integral curve through `(p,v)` on `(-2,2)⊇[0,1]` — the `C¹` lemma
  `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` gives a UNIFORM existence time `ε` over
  a ball at `e`, and rescaling `s=ε/2` (`geodesic_rescale`) stretches `(-ε,ε)` to `(-2,2)`, dissolving the
  `[-ε,ε]`-vs-`[0,1]` interval mismatch. **Confinement half — `geodesic_apriori_confinement`**: `∃ρ,C₀`, the tube
  through `(p,v)` stays `‖Y t − e‖ ≤ C₀‖v‖` on `[0,1]` (so `Y_v(t)→e` uniformly as `v→0`) — the Picard–Lindelöf flow's
  equilibrium trajectory is CONSTANT (`α e = e`, by ODE uniqueness against the constant curve on the flow's compact
  range where `F` is Lipschitz), so its Lipschitz-in-IC bounds the rescaled tube; dodges the a-priori clopen
  circularity. ⚠ **HONEST CAPTION (binding)**: this CLOSES both halves of the flagged common-tube crux (existence +
  confinement) unconditionally over a ball. What remains for **`HasStrictFDerivAt exp_p id 0`** is PURE ASSEMBLY (no
  missing Mathlib theorem): a definitional bridge pinning `expMap` to the confined tube endpoint (the current
  `Classical.choose`-of-local-existence value at `t=1` is not the geodesic endpoint) + the `isLittleO` `η`-juggling
  feeding confinement + the S2 strict remainder + `geodesic_twopoint_gronwall` + `residual_gronwall`. This is NOT yet
  `exp_p`'s strict derivative, NOT the local diffeo, NOT the RNC gauge, NOT numerical-`G`.
- **EXP4 — the exp-map campaign CLOSED: `exp_p`'s STRICT derivative at `0` + local C¹ diffeo (normal coordinates exist
  as a chart)** (`ExpMap.lean` `exists_confined_tube_family`/`expTube_spec`/`gronwallBound_zero_linear`/
  `hasStrictFDerivAt_expMap`/`expMap_localInverse`, all **[AF]** std-3, 2026-07-06). **Definitional bridge (route a):**
  `expMap` is REDEFINED from the confined `[0,1]` tube — `exists_confined_tube_family` skolemizes EXP3's
  `geodesic_apriori_confinement` into ONE tube-valued function `expTube` (selectors `expRho`/`expConst`/`expTube` +
  spec `expTube_spec`: the tube starts at `(p,v)`, solves the geodesic ODE on `(-2,2)⊇[0,1]`, and stays
  `expConst·‖v‖`-close to `(p,0)` on `[0,1]` for `‖v‖≤expRho`), and `expMap g gi hC p v := (expTube p v 1).1` — the
  genuine geodesic endpoint for small `v` (the old `geodesicSol`-based `expMap` was retired). **S5 —
  `hasStrictFDerivAt_expMap`**: `HasStrictFDerivAt (expMap g gi hC p) (ContinuousLinearMap.id ℝ (Point n)) 0`, the
  two-point `‖exp_p v − exp_p w − (v−w)‖ = o(‖v−w‖)`. Assembly through `hasStrictFDerivAt_iff_isLittleO`/`isLittleO_iff`:
  for `c>0`, `η=c/(M+1)` with `M=e^{K}·β`, `β=gronwallBound 0 ‖A‖ 1 1` (`gronwallBound_zero_linear` = the `ε`-linearity
  of the Grönwall bound); confinement puts `Y_v(t),Y_w(t)` in the S2 `η`-nbhd, the S2 strict field remainder
  (`hasStrictFDerivAt_geodesicField`) gives `‖R‖≤η‖Y_v−Y_w‖`, `geodesic_twopoint_gronwall` gives `‖Y_v−Y_w‖≤e^{K}‖v−w‖`,
  `residual_gronwall` propagates to `‖r(1)‖≤c‖v−w‖`, and the position projection `π₁ r(1) = exp_p v − exp_p w − (v−w)`
  closes the little-o. **S6 — `expMap_localInverse`**: the inverse function theorem
  `HasStrictFDerivAt.toOpenPartialHomeomorph` (with `id=↑(ContinuousLinearEquiv.refl …)` invertible) yields an
  `OpenPartialHomeomorph φ` with `⇑φ=expMap`, `0∈φ.source`, and a continuous local inverse `φ.symm` with
  `HasStrictFDerivAt φ.symm id (expMap 0)` (via `to_localInverse`/`localInverse_def`/`refl_symm`/`coe_refl`). `φ.symm`
  IS the normal-coordinate chart. ⚠ **HONEST CAPTION (binding)**: `exp_p` a local C¹ diffeo ⟹ **normal coordinates
  EXIST as a chart** around `p`. This does **NOT** derive the RNC gauge IN those coordinates (`g(0)=δ`, `∂g(0)=0`,
  `∂_{(l}Γ_{jk)}(0)=0` still need the metric-in-normal-coordinates change of variables), does **NOT** build a curved
  heat kernel, and does **NOT** move numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP5 — the exp map's RADIAL 2-jet is `−Γ(p)` (honest normal-coordinate brick)** (`ExpMap.lean`
  `expMap_radial_accel`, **[AF]** std-3, 2026-07-06). For a fixed direction `v`, the radial curve `t ↦ exp_p(t•v)` has
  **first `t`-derivative `v`** at `0` and **second `t`-derivative `−Γ(p)(v,v)`** at `0`:
  `HasDerivAt (fun t:ℝ => expMap g gi hC p (t•v)) v 0` ∧
  `HasDerivAt (deriv (fun t:ℝ => expMap g gi hC p (t•v))) (−fun i => ∑ j ∑ k christoffel g gi i j k p * v j * v k) 0`.
  Route (flow-free): a scale `s>0` with `‖s•v‖≤expRho` gives the confined tube `Y := expTube p (s•v)`; geodesic
  homogeneity (`geodesic_rescale`) + local uniqueness (`geodesic_local_unique`, on a compact-image Lipschitz ball
  bounding both `Y` and its rescaling on `(-1,3/2)`) identify `exp_p(t•v) = (Y (t/s)).1` on a `𝓝 0`-neighbourhood
  (EventuallyEq); projecting the ODE `Y' = (Y.2, −∑Γ(Y.1)(Y.2,Y.2))` onto position (deriv = velocity `(Y τ).2`) then
  velocity (deriv = acceleration), evaluated at `τ=0` where `Y 0 = (p, s•v)`, the two `1/s` chain-rule factors cancel
  the two `s` in `s•v`, leaving exactly `−Γ(p)(v,v)`; the `deriv`-of-`deriv` transfer is `Filter.EventuallyEq.deriv` +
  `HasDerivAt.congr_of_eventuallyEq`. ⚠ **HONEST CAPTION (binding)**: this is the exp map's **RADIAL 2-jet only** — the
  radial DIAGONAL, **NOT** the RNC gauge (which needs the off-radial Jacobian field / higher jets = the Mathlib-absent
  smooth-dependence-on-IC theorem). It does **NOT** discharge `hgauge`, **NOT** build normal-coordinate metric jets,
  **NOT** move numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET1 — the exp map's FRÉCHET value 2-jet at `0` (`exp_p(v) = p + v − ½Γ_p(v,v) + o(‖v‖²)`)** (`ExpMap.lean`
  `expMap_value_two_jet`, with `christoffel_bilin_bound`/`christoffel_quad_diff_bound`/`gronwallBound_zero_one_le_exp`,
  all **[AF]** std-3, 2026-07-06). The full VECTOR (uniform-over-directions) 2-jet, not just the radial diagonal:
  `(fun v => expMap g gi hC p v − p − v + ½·(fun i => ∑ⱼ∑ₖ christoffel g gi i j k p * v j * v k)) =o[𝓝 0] (fun v => ‖v‖²)`.
  Route (equilibrium-anchored, flow-free — GPT-5.5-pro diagonal form): the confined geodesic tube `Y = expTube p v`
  (`expTube_spec`) is compared to the explicit model curve `M(t) = (p + t·v − ½t²·Γ_p(v,v), v − t·Γ_p(v,v))`; the residual
  `q = Y − M` has `q 0 = 0` and `q'(t) = geodesicField(Y t) − M'(t) = ((q t).2, Γ_p(v,v) − Γ_{(Y t).1}((Y t).2,(Y t).2))`.
  The a-priori confinement (`‖Y t − (p,0)‖ ≤ C₀‖v‖`) plus the **LOCAL Christoffel bounds** — value bound `Mc` and
  **Lipschitz-in-base-point** `Lc` on `closedBall p (C₀·expRho)`, both from `ContDiff → bounded/exists_lipschitzOnWith` on
  the compact ball — give `‖q'(t)‖ ≤ (1 + Bcoef‖v‖)‖q t‖ + Acoef‖v‖³` on `[0,1]` (the crux
  `christoffel_quad_diff_bound`, the base-point Lipschitz is what turns the naïve `O(‖v‖²)` into `O(‖v‖³)`); the
  inhomogeneous Grönwall bound (`norm_le_gronwallBound_of_norm_deriv_right_le` + `gronwallBound_zero_linear` +
  `gronwallBound_zero_one_le_exp` = `gronwallBound 0 K 1 1 ≤ e^K`) yields `‖q 1‖ ≤ Cfinal·‖v‖³`, and projecting the
  position component `π₁ q 1 = exp_p v − p − v + ½Γ_p(v,v)` gives `‖·‖ ≤ Cfinal‖v‖³`, packaged into `o(‖v‖²)` via
  `isLittleO_iff` + `‖v‖ → 0`. ⚠ **HONEST CAPTION (binding)**: this is the **Fréchet value 2-jet of `exp_p` at `0`** — a
  step toward discharging the RNC gauge. It does **NOT** yet discharge `hgauge`, **NOT** build the pullback metric,
  **NOT** move numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET2 — the exp map's FRÉCHET value 3-jet at `0`** (`ExpMap.lean` `expMap_value_three_jet`, **[AF]** std-3,
  DONE 2026-07-06): `exp_p(v) − p − v + ½Γ_p(v,v) − ⅙·a₃(v) = o[𝓝 0](‖v‖³)`, with the cubic coefficient the true
  `γ'''(0)`: `a₃(v)_i = −∑_{j,k,l} ∂_l Γ^i_{jk}(p) v_j v_k v_l + ∑_{j,k} Γ^i_{jk}(p)(Γ_p(v,v)_j v_k + v_j Γ_p(v,v)_k)`
  (the honest symmetry-free form; when the metric is symmetric, `Γ^i_{jk}=Γ^i_{kj}`, the second sum equals the prompt's
  `2∑_{j,k} Γ^i_{jk} Γ_p(v,v)_j v_k`). Route (one order up from EXP-JET1, same equilibrium-anchored residual-ODE +
  inhomogeneous Grönwall): the tube `Y=expTube p v` is compared to the cubic model
  `M(t)=(p+tv−½t²Γv+⅙t³a₃, v−tΓv+½t²a₃)`, residual `r₃=Y−M` solves `r₃'=A·r₃+Err`
  (`Err=Γv−t·a₃−Γ_{(Y t).1}((Y t).2,(Y t).2)`, from `expJet2_residual_deriv_eq`). The exact O(‖v‖³)-cancellation
  regroups `Err = [−t²·Γ_p(Γv,Γv)] + [t·∂Γ(v,v,v) − ∂Γ(u*,u*,X−p)] − Rem + [Γ_X(u*,u*) − Γ_X(U,U)]`
  (`u*=v−t·Γv`, `X=(Y t).1`, `U=(Y t).2`) via three new sum-algebra helpers — `bilin_sub_smul_expand` (bilinear
  expansion of `Γ_p(v−xw, v−xw)`), `tri_shared_telescope` (trilinear telescope `x·∂Γ(v,v,v)−∂Γ(u*,u*,d)`),
  `bilin_taylor_repack` (repackaging the `christoffel_taylor_bound` remainder into `bilin_sup_bound` shape). The cheap
  confinement-derived tube first-order bounds `‖(Y t).2−v‖`, `‖(Y t).1−p−t·v‖ = O(‖v‖²)` (MVT via
  `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) feed the `∂Γ` cancellation; the SECOND-order Christoffel Taylor
  remainder (`christoffel_taylor_bound`) is the new analytic ingredient. Result `‖Err(t)‖ ≤ Acoef·‖v‖⁴ + Bcoef·‖v‖·‖r₃‖`,
  then `norm_le_gronwallBound_of_norm_deriv_right_le` + `gronwallBound_zero_one_le_exp` give `‖r₃ 1‖ ≤ Cfinal·‖v‖⁴`, and
  the position projection at `t=1` closes the `o(‖v‖³)`. ⚠ **HONEST CAPTION (binding)**: this is the **Fréchet value
  3-jet of `exp_p` at `0`**; it does **NOT** discharge `hgauge`, **NOT** build the pullback metric, **NOT** move
  numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET3a — SETUP for the localized first-variation / operator-valued fundamental solution** (`ExpMap.lean`, all
  **[AF]** std-3, budget 0, DONE 2026-07-07): flow-independent groundwork toward the Jacobian-field expansion (EXP-JET3,
  `fderiv exp_p y = 1 + B(y,·) + ½T(y,y,·) + o(‖y‖²)`). **KEY FINDING:** Mathlib's Picard–Lindelöf
  `IsPicardLindelof f t₀ x₀ a r L K` is ALREADY nonautonomous (`f : ℝ → E → E`); the autonomous corollaries wrap
  `(fun _ ↦ f)`. So the nonautonomous fundamental solution `Φ_v` (`Φ'=DF(Y_v(t))·Φ`, `Φ 0=1`) is **not blocked by a
  missing theorem** — building it is a large instantiation + assembly effort. Landed: `expJetIota` (`ι h=(0,h)`, `inr`),
  `expJetPi` (`π (x,u)=x`, `fst`); `geodesicField_differentiable` / `hasFDerivAt_geodesicField_fderiv` (`DF=fderiv F`
  exists everywhere ⇒ the Jacobi coefficient `A_v(t)=DF(Y_v(t))` is honest, never junk `fderiv`);
  `expJet_linVariation_residual_deriv` (the residual identity `R'=DF(Y₁)·R+N`, `N=F(Y₂)−F(Y₁)−DF(Y₁)(Y₂−Y₁)`, for
  `R=(Y₂−Y₁)−J` and ANY Jacobi solution `J`, pure calculus + `DF` linearity); and the analytic ingredient
  `geodesicField_uniform_C1_remainder` (UNIFORM first-order/C¹ Taylor remainder of `F` on any convex compact `S`:
  `∀ε>0 ∃δ>0`, `‖F a−F b−DF(b)(a−b)‖ ≤ ε‖a−b‖` for `a,b∈S`, `‖a−b‖<δ`; Heine–Cantor uniform continuity of `fderiv F` +
  `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` on the segment). ⚠ **CHECKPOINTED (EXP-JET3b):** the `Φ_v`
  construction (nonautonomous `IsPicardLindelof` instantiation for `Ψ_v t M=(DF(Y_v t)).comp M`, uniform over the ball)
  and the target `HasFDerivAt (expMap g gi hC p) (π∘(Φ_v 1)∘ι) v` little-o are NOT yet built. ⚠ **HONEST CAPTION
  (binding):** flow-independent SETUP toward EXP-JET3 → discharging `hgauge`; it does **NOT** build `Φ_v`, **NOT** give
  the localized first variation, **NOT** the Jacobian expansion, **NOT** the pullback metric, **NOT** numerical-`G`
  (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET3b — the operator field `Ψ_v` + Picard–Lindelöf data + the LOCAL fundamental solution `Φ_v`** (`ExpMap.lean`,
  all **[AF]** std-3, budget 0, PARTIAL 2026-07-07): the operator-valued Jacobi field `expJetPsi` (`Ψ_v t M=DF(Y_v t)∘M`
  on `State →L State`), its linearity data `expJetPsi_norm_sub_le` (`‖Ψ_v t M−Ψ_v t N‖ ≤ ‖DF(Y_v t)‖·‖M−N‖`) /
  `expJetPsi_norm_le` (operator-norm submultiplicativity), `expTube_continuousOn` (the confined tube is continuous on
  `[0,1]`), the uniform Jacobi bound `expJet_fderiv_tube_bddAbove` (`‖DF(Y_v t)‖ ≤ KdF` on `[0,1]`, compactness of
  `fderiv F ∘ Y_v`), the time-continuity `expJetPsi_continuousOn`, and **`expJetFund_local`** — the LOCAL operator-valued
  fundamental solution `Φ_v` on a short `[0,T]` (`Φ_v 0=1`, `Φ_v' t=Ψ_v t (Φ_v t)`) via the FULL operator-normed
  `IsPicardLindelof` instantiation (`a=1, r=0, L=2·KdF, K=KdF, T=min 1 (1/(2(KdF+1)))`). ⚠ **THE INTERVAL OBSTRUCTION
  (the exact checkpoint):** Mathlib's PL carries `mul_max_le : L·max(tmax−t₀, t₀−tmin) ≤ a−r`; for the LINEAR operator ODE
  the field bound is `L=KdF·(1+a)` (linear growth), so reaching `t=1` in ONE application needs `KdF<1` — FALSE for the
  general tube. A single application reaches only `T ≲ 1/KdF`; the `[0,1]` extension needs concatenating `≈⌈KdF⌉` local
  solutions (Grönwall-glued continuation) — **Mathlib has NO continuation theorem** (no global existence for
  globally-Lipschitz fields; time-rescaling scales `KdF` identically). ⚠ **STILL CHECKPOINTED:** `Φ_v(1)` (the
  concatenation) and the first-variation residual Grönwall `HasFDerivAt (expMap g gi hC p) (L v) v`, `L v := π∘(Φ_v 1)∘ι`.
  ⚠ **HONEST CAPTION (binding):** operator field + PL data + LOCAL Φ_v — a step toward the Jacobian expansion → `hgauge`;
  does **NOT** reach `Φ_v(1)`, **NOT** the localized first variation, **NOT** the pullback metric, **NOT** numerical-`G`
  (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET3b global scaffolding — the SHIFTED normalized local propagator (the `[0,1]` concatenation brick)**
  (`ExpMap.lean`, all **[AF]** std-3, budget 0, 2026-07-07): `expJetFund_shifted` — for a `[0,1]`-uniform Jacobi bound
  `KdF` (threaded EXTERNALLY so a single `N` with `2(KdF+1)≤N` fixes the step) and ANY subinterval `[t₀,t₀+T] ⊆ [0,1]`
  with `2·KdF·T ≤ 1`, the NORMALIZED propagator `U_j` (`U_j(t₀)=1`, `U_j' t = Ψ_v t (U_j t) = DF(Y_v t)∘U_j t` on
  `[t₀,t₀+T]`) via the SHIFTED operator-normed `IsPicardLindelof` centred at the identity on `closedBall(1,1)`
  (generalizes `expJetFund_local`'s `t₀=0` case); and `expJetFund_shifted_integral` — the same packaged with continuity
  on the interval **and the LOCAL INTEGRAL EQUATION** `U_j(t) = 1 + ∫_{t₀}^t Ψ_v(s)(U_j s) ds` (derived from the
  derivative law by FTC-2 `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, integrand continuous by
  `ContinuousOn.clm_comp`), which is the exact brick the global integral-equation gluing consumes. ⚠ This DISCHARGES the
  "no Mathlib continuation theorem" worry into a pure ASSEMBLY: each `[τ_j,τ_{j+1}]` is a normalized `U_j`, glued by
  right-multiplication `M_{j+1}:=U_j(τ_{j+1})∘M_j`, `seg_j:=U_j∘M_j` (inherits the shifted integral eq via
  `ContinuousLinearMap.integral_comp_comm`), and the GLOBAL integral equation `Φ_v(t)=1+∫_0^t Ψ_v(s)(Φ_v s) ds` on
  `[0,τ_j]` proved by induction on `j` (`intervalIntegral.integral_add_adjacent_intervals` +
  `intervalIntegral.integral_congr`), then FTC on `[0,1]`. ⚠ **STILL CHECKPOINTED:** that partition induction, `Φ_v(1)`,
  and the first-variation residual Grönwall `HasFDerivAt (expMap g gi hC p) (L v) v`, `L v:=π∘(Φ_v 1)∘ι`. ⚠ **HONEST
  CAPTION (binding):** the concatenation building block (one subinterval, both differential + local integral form) — a
  step toward the Jacobian-field expansion → `hgauge`; does **NOT** reach `Φ_v(1)`, **NOT** the localized first
  variation, **NOT** the pullback metric, **NOT** numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET3b STEP A — the `[0,1]` operator-valued fundamental solution `Φ_v`** (`ExpMap.lean`, all **[AF]** std-3,
  budget 0, DONE 2026-07-07): **`expJetFund`** — for `‖v‖ ≤ expRho` an operator-valued curve
  `Φ_v : ℝ → (State →L State)` with `Φ_v 0 = 1`, `ContinuousOn Φ_v [0,1]`, the GLOBAL integral equation
  `Φ_v t = 1 + ∫₀ᵗ Ψ_v s (Φ_v s) ds` on `[0,1]`, AND the derivative law
  `HasDerivWithinAt Φ_v (Ψ_v t (Φ_v t)) (Icc 0 1) t` for every `t ∈ [0,1]`.  Built by concatenating `N ≥ 2(KdF+1)`
  shifted normalized propagators (private `expJetFund_glue`, finite induction on the partition `τ j = j/N`): the glued
  curve on `[0,τ_{j+1}]` is `Φ_{j+1}(t)=if t≤τ_j then Φ_j t else U_j(t)∘Φ_j(τ_j)` (`U_j` from
  `expJetFund_shifted_integral`), the GLOBAL integral equation pasted from the sub-interval one by
  `intervalIntegral.integral_add_adjacent_intervals` + `integral_congr` + right-composition/integral commutation
  (`ContinuousLinearMap.intervalIntegral_comp_comm`, `RM=(compL).flip (Φ_j τ_j)`), continuity glued by
  `ContinuousOn.union_of_isClosed`; the derivative law from the integral equation by FTC-1
  (`intervalIntegral.integral_hasDerivWithinAt_right`, `𝓝[Icc 0 1]` FTCFilter via `Fact (t∈Icc 0 1)`).  Reusable helper
  `expJetPsi_comp_continuousOn` (integrand continuity on any `A ⊆ [0,1]`).  ⚠ This discharges the earlier "no Mathlib
  continuation theorem" checkpoint into a COMPLETED assembly. ⚠ **STILL CHECKPOINTED:** the first-variation residual
  Grönwall `HasFDerivAt (expMap g gi hC p) (L v) v`, `L v:=expJetPi∘(Φ_v 1)∘expJetIota` (Step B). ⚠ **HONEST CAPTION
  (binding):** the `[0,1]` fundamental solution — a step toward the localized first variation → the Jacobian-field
  expansion → `hgauge`; does **NOT** yet give the first variation, **NOT** the Jacobian 2-jet expansion, **NOT** the
  pullback metric, **NOT** numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET3b STEP B — the localized first variation `HasFDerivAt exp_p (L v) v`** (`ExpMap.lean`, **[AF]** std-3,
  budget 0, DONE 2026-07-07): **`hasFDerivAt_expMap`** — for `‖v‖ < expRho`,
  `HasFDerivAt (expMap g gi hC p) (expJetPi.comp ((Φ_v 1).comp expJetIota)) v` with `Φ_v` THE `[0,1]` fundamental
  solution (`expJetFund`, stated existentially in `Φ_v`).  The Jacobi field `J_k(t)=Φ_v(t)(0,k)`
  (`HasDerivWithinAt.clm_apply` on the `Φ_v` derivative law, `J_k 0=(0,k)`) transports the first variation; the
  residual `R_k=(Y_{v+k}−Y_v)−J_k` (`R_k 0=0`, `R_k'=DF(Y_v)R_k+N_k`) has `‖N_k(t)‖≤ε·‖Y_{v+k}−Y_v‖≤ε·Ctw·‖k‖`
  (`geodesicField_uniform_C1_remainder` on a fixed convex-compact ball + the two-point `geodesic_twopoint_gronwall`,
  `Ctw=e^{Ktube}`); the inhomogeneous Grönwall `norm_le_gronwallBound_of_norm_deriv_right_le` (Icc→Ici via
  `mono_of_mem_nhdsWithin`) gives `‖R_k 1‖≤ε·Ctw·β'·‖k‖≤c·‖k‖`, and `exp_p(v+k)−exp_p(v)−L v·k=expJetPi(R_k 1)` closes
  the `isLittleO`. ⚠ This CLOSES the checkpointed first-variation residual Grönwall. ⚠ **HONEST CAPTION (binding):**
  the localized first variation (the genuine subtlety of EXP-JET3); does **NOT** yet give the full Jacobian 2-jet
  expansion `fderiv exp_p y = 1 + B(y,·) + …`, **NOT** the pullback metric, **NOT** numerical-`G`.
- **EXP-JET3c — the closed-form Fréchet derivative of the geodesic field** (`ExpMap.lean` `geodesicField_fderiv_apply`,
  **[AF]** std-3, budget 0, 2026-07-07): `DF(x,u)(ξ,η) = (η, i ↦ −∑_{jk}[(∑_l ∂_l Γ^i_{jk}(x)·ξ_l)·u_j·u_k
  + Γ^i_{jk}(x)·η_j·u_k + Γ^i_{jk}(x)·u_j·η_k])`. Product-rule (`HasFDerivAt.mul`) on the quadratic-in-`u`,
  Christoffel-composed acceleration term `−∑_{jk} Γ^i_{jk}(x)·u_j·u_k`, with `fderiv Γ^i_{jk}(x)·ξ=∑_l ∂_l Γ^i_{jk}(x)·ξ_l`
  (`fderiv_apply_eq_sum_pd`). The honest closed form of the Jacobi coefficient `A_v(t)=DF(Y_v t)` — the foundation for
  identifying the order-0/1/2 coefficients (`A₀=DF(e)=linF`, `A₁`, `A₂`) of the uniform `DF(Y_y t)` expansion. ⚠ **HONEST
  CAPTION (binding):** the pointwise closed-form Jacobi coefficient; does **NOT** give the uniform order-2 `DF` expansion,
  **NOT** the Jacobian 2-jet, **NOT** the pullback metric, **NOT** numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET3c (STEP 1 ingredient) — the uniform-in-`t` tube value 2-jet** (`ExpMap.lean` `expTube_value_two_jet` +
  helper `gronwallBound_zero_le_exp`, **[AF]** std-3, budget 0, 2026-07-07): for `‖v‖ ≤ ρ`, `∀ t∈[0,1]`,
  `‖expTube p v t − (p+t·v−½t²Γ_p(v,v), v−t·Γ_p(v,v))‖ ≤ C·‖v‖³` — the WHOLE confined geodesic tube's value 2-jet,
  uniform in `t` and exposing BOTH phase components (`expMap_value_two_jet` only projected the position endpoint at
  `t=1`). This is the tube 2-jet `Y_v(t)−e = S₁(t,v)+S₂(t,v)+O(‖v‖³)`, `S₁=(t·v,v)`, `S₂=(−½t²Γ_p(v,v),−t·Γ_p(v,v))` —
  the value-jet input the operator-valued Jacobian 2-jet's uniform `DF(Y_v t)` expansion consumes (compose
  `geodesicField_fderiv_apply` at `(x,u)=Y_v(t)` with it). Same equilibrium-anchored residual-ODE + inhomogeneous
  Grönwall as `expMap_value_two_jet`, but Grönwall applied at every `t∈[0,1]` (new reusable helper
  `gronwallBound_zero_le_exp`: `gronwallBound 0 K ε t ≤ ε·e^K` uniform in `t∈[0,1]`) and no position projection.
  ⚠ **HONEST CAPTION (binding):** the uniform-in-`t` full-phase-vector value 2-jet of the tube; does **NOT** give the
  operator `DF` expansion, **NOT** the Jacobian 2-jet, **NOT** the pullback metric, **NOT** numerical-`G` (`N`, `Λ_s`,
  `E/ξ` remain).
- **EXP-JET3c (STEP 1 core) — the operator-norm `‖DF(x,u) − A₀‖` bound** (`ExpMap.lean`
  `geodesicField_fderiv_sub_linF_opNorm_le`, **[AF]** std-3, budget 0, 2026-07-07): given `|Γ^i_{jk}(x)| ≤ Mc` and
  `|∂_l Γ^i_{jk}(x)| ≤ Nc`, `‖DF(x,u) − A₀‖ ≤ Nc·n³·‖u‖² + 2·(Mc·n²)·‖u‖` (`A₀ = linF = DF(e)`). The Jacobi
  coefficient `DF(x,u)` differs from `A₀` only in its acceleration block: `(DF(x,u)−A₀)(ξ,η) = (0, Acc)` (velocity
  slots cancel), `Acc = −∑_{jk}[(∑_l ∂_lΓ·ξ_l)u_j u_k + Γ·η_j u_k + Γ·u_j η_k]`, split into the ∂Γ-trilinear form
  (`christoffel_pd_trilin_bound`) + two Γ-bilinear forms (`christoffel_bilin_bound`), `‖ξ‖,‖η‖ ≤ ‖(ξ,η)‖`, closed by
  `ContinuousLinearMap.opNorm_le_bound`. Composed with `expTube_value_two_jet` (`‖u‖=‖(Y_v t).2‖=O(‖v‖)`) this is the
  ORDER-0 remainder `‖DF(Y_v t) − A₀‖ ≤ C·‖v‖` of the uniform `DF(Y_v t)` expansion. ⚠ **HONEST CAPTION (binding):**
  the operator-norm "`A₀` is leading" bound; does **NOT** identify the order-1/2 coefficients `A₁, A₂`, **NOT** the
  full Jacobian 2-jet, **NOT** the pullback metric, **NOT** numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET3c (STEP 1, order-0 composed) — the uniform-in-`t` order-0 `DF` expansion along the tube** (`ExpMap.lean`
  `expJet_fderiv_tube_order0`, **[AF]** std-3, budget 0, 2026-07-07): `∃ ρ>0, ∃ C≥0, ∀ ‖v‖≤ρ, ∀ t∈[0,1],
  ‖DF(Y_v t) − A₀‖ ≤ C·‖v‖` (`A₀=linF=DF(e)`, `Y_v=expTube p v`). Composes the pointwise
  `geodesicField_fderiv_sub_linF_opNorm_le` with the a-priori confinement (`‖(Y_v t).2‖ ≤ C₀‖v‖`,
  `(Y_v t).1 ∈ closedBall p (C₀ρ)`, from `expTube_spec`): the Christoffel value bound `Mc` and `∂Γ` value bound `Nc`
  are uniform over the compact confinement ball (`christoffel_pd_contDiff` → continuity → bounded), and
  `Nc·n³‖u‖²+2Mc·n²‖u‖ ≤ C·‖v‖` via `‖u‖≤C₀‖v‖≤C₀ρ` (`C=Nc·n³·C₀²·ρ+2·Mc·n²·C₀`). The ORDER-0 (leading `A₀`) term of
  the uniform `DF(Y_y t)=A₀+A₁(t,y)+A₂(t,y)+o(‖y‖²)` expansion, now stated as a theorem. ⚠ **HONEST CAPTION
  (binding):** the order-0 remainder; does **NOT** identify the order-1/2 coefficients `A₁, A₂`, **NOT** the Jacobian
  2-jet, **NOT** the pullback metric, **NOT** numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET3c (STEP 1, order-1 anchoring) — the tube Jacobi coefficient is `O(‖v‖²)`-close to the fixed `DF(p,v)`**
  (`ExpMap.lean` `expJet_fderiv_tube_order1`, with engine `geodesicField_fderiv_two_pt_opNorm_le` + generic helper
  `bilin_two_pt_diff_bound`; all **[AF]** std-3, budget 0, 2026-07-07): `∃ ρ>0, ∃ C≥0, ∀ ‖v‖≤ρ, ∀ t∈[0,1],
  ‖DF(Y_v t) − DF(p,v)‖ ≤ C·‖v‖²` (`Y_v=expTube p v`). ANCHORS the order-1 coefficient: `DF(Y_v t) = DF(p,v) + O(‖v‖²)`
  UNIFORMLY in `t`, so the FIXED `t`-independent operator `DF(p,v)` carries the order-1 part `A₁`, reducing the
  remaining EXP-JET3c work to expanding the single fixed `DF(p,v) = A₀ + A₁ + (order-2 ∂Γ)`. The engine
  `geodesicField_fderiv_two_pt_opNorm_le`: `‖DF(x,u) − DF(x',u')‖ ≤ Nc·n³(‖u‖²+‖u'‖²) + 2(Mc·n²‖u−u'‖ + Dc·n²‖u'‖)`
  (velocity slots cancel; ∂Γ block via `christoffel_pd_trilin_bound` at each point; the two Γ-bilinear blocks via
  `bilin_two_pt_diff_bound`). Composed at `(Y_v t)` vs `(p,v)` with the confinement, Christoffel value/Lipschitz/∂Γ
  bounds on the ball, and the tube 2-jet `‖(Y_v t).2 − v‖ ≤ D₂‖v‖²` (`expTube_value_two_jet` + `christoffel_bilin_bound`).
  ⚠ **HONEST CAPTION (binding):** the order-1 anchoring; does **NOT** give the model Jacobian `K_y`, the residual
  Grönwall, the projected Jacobian 2-jet `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)`, the pullback metric, or
  numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET3c (STEP 1, coefficient identification) — the anchored order-2 decomposition `DF(p,v) = A₀ + A₁(v) + A₂(v)`**
  (`ExpMap.lean` `geodesicField_fderiv_anchored_eq` + composed `expJet_fderiv_tube_order2`; CLM building blocks
  `matVecCLM`, `expJetA1`, `expJetA2`; all **[AF]** std-3, budget 0, 2026-07-07): the fixed `t`-independent Jacobi
  coefficient at the base point splits EXACTLY (a degree-≤2 polynomial in `v`, **no remainder**) as
  `A₀ + A₁(v) + A₂(v)`, with `A₀ = linF = DF(e)`, `A₁(v)(ξ,η) = (0, i↦−∑_{jk}Γ^i_{jk}(p)(η_j v_k + v_j η_k))` (the
  velocity-bilinear Γ part, `expJetA1`), `A₂(v)(ξ,η) = (0, i↦−∑_{jk}(∑_l ∂_lΓ^i_{jk}(p) ξ_l)v_j v_k)` (the ∂Γ-trilinear
  part, `expJetA2`). Read off from `geodesicField_fderiv_apply` at `(p,v)` by regrouping the acceleration double-sum
  into the three coefficient arrays (`ContinuousLinearMap.ext` + Finset algebra / `pd_trilin_reorder`). Composed with
  `expJet_fderiv_tube_order1` this gives the **uniform-in-`t` order-2 expansion with IDENTIFIED coefficients**,
  `expJet_fderiv_tube_order2`: `∃ ρ>0, ∃ C≥0, ∀ ‖v‖≤ρ, ∀ t∈[0,1], ‖DF(Y_v t) − (linF + expJetA1 v + expJetA2 v)‖ ≤ C·‖v‖²`
  — the uniform expansion the model Jacobian `K_v` will integrate against. ⚠ **HONEST CAPTION (binding):** the `A₁,A₂`
  coefficient identification + uniform order-2 expansion; does **NOT** give the model Jacobian `K_v` (from the
  triangular ODEs), the residual operator Grönwall, the projected Jacobian 2-jet `L y = 1 − Γ_p(y,·) + ½T(y,y,·) +
  o(‖y‖²)`, the pullback metric, or numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **EXP-JET3c (STEP 2, order-0 model propagator `K₀`)** (`ExpMap.lean` `linF_comp_linF`, `expJetK0`,
  `expJetK0_hasDerivAt_ode`, all **[AF]** std-3, budget 0, 2026-07-07): the equilibrium linearization is **nilpotent**
  (`A₀²=0`, `linF_comp_linF`), so the model propagator `K₀(t) = 1 + t·A₀` (`expJetK0`) is the EXACT (truncated Peano)
  fundamental solution of the equilibrium operator ODE `K₀' = A₀·K₀`, `K₀(0)=1` (`expJetK0_hasDerivAt_ode` +
  `expJetK0_zero`).  The order-0 brick of the model Jacobian `K_v = K₀ + K₁ + K₂`.  ⚠ **HONEST CAPTION:** does **NOT**
  give `K₁,K₂` (the order-1/2 operator-integral corrections), the residual operator Grönwall, the projected 2-jet
  `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)`, the pullback metric, or numerical-`G`.
- **EXP-JET3c (STEP 2, order-1/2 model propagators `K₁`, `K₂`)** (`ExpMap.lean` `expJetK1`, `expJetK1_hasDerivAt_ode`,
  `expJetK2`, `expJetK2_hasDerivAt_ode` + helpers `expJetA1_comp_linF`, `linF_comp_linF_comp`,
  `expJetA1_comp_linF_comp`, all **[AF]** std-3, budget 0, 2026-07-07): because `A₀²=0` and `A₁A₀=0`, the
  variation-of-constants integrals collapse to POLYNOMIALS — `K₁(t)=t·A₁+(t²/2)·A₀A₁` (`expJetK1`) and
  `K₂(t)=t·A₂+(t²/2)·(A₁²+A₂A₀+A₀A₂)+(t³/6)·A₀(A₁²+A₂A₀)` (`expJetK2`) — DEFINED directly and VERIFIED to solve the
  triangular equilibrium ODEs `K₁'=A₀K₁+A₁K₀` (`expJetK1_hasDerivAt_ode`), `K₂'=A₀K₂+A₁K₁+A₂K₀`
  (`expJetK2_hasDerivAt_ode`) by differentiation (bypassing the operator Bochner integral).  Completes the model
  Jacobian `K_v = K₀+K₁+K₂` bricks.  ⚠ **HONEST CAPTION:** does **NOT** give the residual operator Grönwall
  `‖(Φ_v 1) − K_v(1)‖ ≤ C‖v‖²`, the projected 2-jet `L v = 1 − Γ_p(v,·) + ½T(v,v,·) + o(‖v‖²)`, the pullback metric,
  or numerical-`G`.
- **EXP-JET3c (STEP 2, operator-norm + residual-identity toolkit)** (`ExpMap.lean` `matVecCLM_opNorm_le`,
  `expJetA1_opNorm_le`, `expJetA2_opNorm_le`, `expJetK0_opNorm_le`, `expJetK1_opNorm_le`, `expJetPi_opNorm_le`,
  `expJetIota_opNorm_le`, `expJet_residual_identity`, all **[AF]** std-3, budget 0, 2026-07-07): the reusable bricks the
  operator residual Grönwall consumes — sup-norm CLM bound `‖matVecCLM c‖ ≤ n·b`, the coefficient bounds `‖A₁‖ ≤ 2n²Mc‖v‖`
  (order-1) / `‖A₂‖ ≤ n³Nc‖v‖²` (order-2), the propagator bounds `‖K₀‖,‖K₁‖` on `[0,1]`, `‖π‖,‖ι‖ ≤ 1`, and the CLM ring
  identity `D·Φ−(A₀K₀+(A₀K₁+A₁K₀)) = D·(Φ−(K₀+K₁))+((D−(A₀+A₁))·(K₀+K₁)+A₁·K₁)`.  ⚠ **HONEST CAPTION + TWO CHECKPOINTS:**
  the residual Grönwall + projected jet are **NOT** landed.  **(1) Math gap:** the committed STEP-1 anchoring is only
  `Θ(‖v‖²)`-accurate (the true order-2 Jacobi coefficient `Ã₂(t,v)` is `t`-DEPENDENT — the tube-drift Γ-cross-terms the
  fixed `A₂` misses), so the anchored model gives the Jacobian's LINEAR term `−Γ_p^{sym}(v,·)` exactly but only an
  `O(‖v‖²)` (1-jet) remainder — **NOT** the `o(‖v‖²)` order-2 `½T(v,v,·)` 2-jet.  **(2) Compile intractability:** the
  monolithic operator-valued Grönwall exceeds 32M heartbeats (CLM-Banach instance-search/`whnf` blowup in the large local
  context); FIX = a small-context helper `expJet_residual_gronwall`.  Does **NOT** give the jet, the pullback metric, or
  numerical-`G`.
- **EXP-JET3c (STEP 3 — the JACOBIAN 1-JET of the geodesic exp-map)** (`ExpMap.lean` `expJet_residual_gronwall`,
  `expJet_fderiv_tube_bddAbove_unif`, `expJetOneJetModel`, `expJet_proj_model_one`, `hasFDerivAt_expMap_jacobian_one_jet`
  + 5 small-context CLM helpers, all **[AF]** std-3, budget 0, DONE 2026-07-07): **`hasFDerivAt_expMap_jacobian_one_jet`** —
  `(fun v => fderiv exp_p v − (id + expJetOneJetModel v)) =O[𝓝 0] ‖v‖²`, i.e. `fderiv exp_p v = id − Γ_p^sym(v,·) + O(‖v‖²)`
  (`expJetOneJetModel v = ½·matVecCLM c₁ = −Γ_p^sym(v,·)`). Route: the small-context, `F`-abstract inhomogeneous Grönwall
  `expJet_residual_gronwall` (`‖E 1‖≤C·e^K`, dodges the 32M-heartbeat CLM whnf blowup); a UNIFORM-in-`v` `‖DF(Y_v t)‖≤Kstar`
  (`expJet_fderiv_tube_bddAbove_unif`, confinement into a fixed compact ball ⟹ `e^{Kstar}` uniform ⟹ genuine `IsBigO` over
  `𝓝 0`); the operator residual `E_v=Φ_v−(K₀+K₁)` with `E'=DF∘E+N`, `‖N‖≤Cconst‖v‖²` (order-2 tube bound + `A₁,A₂,K₁`
  opNorms) ⟹ `‖E_v 1‖≤Cconst‖v‖²e^{Kstar}`; the exact projected model identity `expJet_proj_model_one`
  (`π∘(K₀(1)+K₁(1))∘ι = id + expJetOneJetModel v`); residual `fderiv exp_p v − (id+model) = π∘(E_v 1)∘ι`. Delivers **TWO of
  the three RNC gauge conditions** in the pullback metric: `g̃(0)=δ`, `∂g̃(0)=0`. ⚠ **HONEST CAPTION (binding)**: the
  Jacobian 1-jet — does **NOT** give the Jacobian 2-jet (`½T` term: the anchored `A₂` is `t`-dependent-wrong at order 2,
  GPT-5.5-pro-confirmed; and differentiating the value 3-jet is NOT Lean-sound), **NOT** the pullback metric's `∂∂g̃`,
  **NOT** the gauge discharge, **NOT** a curved heat kernel, **NOT** numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- **Route-(c) Lemma 5 — cubic diagonal-vanishing ⟹ full symmetrization** (`Polarization.lean` `sixSym_eq_incl_excl`,
  `trilinear_diag_zero_fullSymm`, **[AF]** std-3, budget 0, 2026-07-07): for a trilinear continuous `T : V →L V →L V →L W`,
  `(∀x, T x x x = 0) ⟹` the six-fold argument symmetrization vanishes, via the inclusion–exclusion identity
  `∑_{σ∈S₃} T aσ bσ cσ = P(a+b+c)−P(a+b)−P(a+c)−P(b+c)+P(a)+P(b)+P(c)` (`P x:=T x x x`), pure `ℝ`-multilinearity + `abel`.
  The polarization step of the GPT-5.5-pro **radial-gauge route** that turns the radial identity `DΓ̃₀(v)(v,v)=0` (from
  differentiating `Γ̃(s·v)(v,v)=0` at `s=0` — radial geodesics are straight in normal coords) into the symmetrized RNC
  gauge `∂_(l Γ̃^i_{jk)}(0)=0` — **bypassing the Jacobian 2-jet entirely**. ⚠ **HONEST**: standalone algebra; the gauge
  discharge still needs Lemmas 1–4 (radial straightness + the pullback-Christoffel transform); **NOT** the gauge, **NOT**
  numerical-`G`.
- **Route-(c) the RNC-gauge ALGEBRAIC SIDE COMPLETE** (`RNCGauge.lean` `dGammaDiag`/`GaugeJet`/`gaugeTri`/`gaugeJet_of_diag`/
  `sum3_sym_contract`/`rncDΓ`/`expMap_rncDΓ_diag_zero`/`rncGaugeJet`; `RNCGaugeExp.lean` `a3rawArr_contract_eq_a3`/
  `exp_rncGaugeJet`; all **[AF]** std-3, budget 0, 2026-07-07; commits 1b09321, 2da77e5, 692d6b4): the symmetrized
  normal-coordinate gauge is a PROVEN algebraic identity for the RNC-Christoffel linearization. `gaugeJet_of_diag`:
  `(∀ v i, ∑_{ljk} dΓ l i j k v_l v_j v_k = 0) ⟹ GaugeJet dΓ` (packages the cubic form as a trilinear CLM `gaugeTri`, reads
  Polarization Lemma 5 at basis vectors). `sum3_sym_contract`: the diagonal `v³`-contraction is invariant under permuting an
  array's 3 lower indices (⟹ symmetrizing the cubic coefficient preserves the diagonal — the NON-vacuity engine; the raw
  coefficient would be pointwise-zero). `rncGaugeJet : GaugeJet (rncDΓ Γ dΓ1)` for the formal linearization
  `rncDΓ = A3sym + ∂Γ − χ²A − χ²B` (abstract Γ, ∂Γ). `a3rawArr_contract_eq_a3` GROUNDS it: `∑ a3rawArr v³ = a₃(v)_i`, the
  EXACT value-3-jet cubic of `expMap_value_three_jet`, so `exp_rncGaugeJet` is the gauge for the genuine exp-derived formal
  Christoffel jet. ⚠ **HONEST CEILING (binding)**: route-c reduces the RNC gauge to this proven ALGEBRAIC identity, but does
  **NOT** reach `κ=1/6` for the actual pullback metric `g̃`: both instantiating `heat_a1_of_gauge` at `g:=g̃` (needs
  `ContDiff ℝ ⊤ g̃`, hence **`ContDiff exp_p`**) and the bridge `rncDΓ = pd(christoffel g̃ g̃i) 0` reduce to smooth
  dependence of `exp_p` on the initial velocity — the Mathlib gap (only pointwise `HasFDerivAt exp_p` near 0 is proved). The
  algebraic gauge is DISCHARGED; the metric-instantiation is the cited `ContDiff exp_p` frontier. **NOT** a curved heat
  kernel, **NOT** numerical-`G` (`N`, `Λ_s`, `E/ξ` remain).
- `GaussianStateEntropy` **[AF]** per-mode Srednicki entropy; the **lattice area-law SCALING `S∝A` is [frontier]**.
- **The entropy AREA LAW `S∝A` — from CARRIED assumption to THEOREM (for an explicit boundary-local model)**
  (`BoundaryGaussianAreaLaw.lean`, all **[AF]** std-3, budget 0, 2026-07-07; commits eec26a2, ca12397; THE_STRONG_G_PLAN
  SG2/3/5/6): the single biggest strengthening of the induced-G derivation — `1/G = N·Λ_s²` is an AREA law ONLY because
  `S∝A`, which was previously CARRIED. Now: model the boundary of an `L×L×L` cube as `6L²` plaquettes (`card_cubeBoundary`),
  each carrying the SAME Srednicki modes `ν₀` (the boundary-locality hypothesis, carried as the index type — NOT an axiom);
  **`boundary_entropy_area_law`** proves `boundaryEntropy = (A/a₀²)·gaussStateEntropy ν₀` = literally `S∝A` (constant
  `gaussStateEntropy ν₀/a₀²`, reusing the per-mode Srednicki entropy). VOLUME-LAW GUARD **`bulk_entropy_volume_law`**
  (`= L³·gaussStateEntropy`, contrast `6L²`) proves finite Gaussian modes give a VOLUME law unless boundary-localized ⟹ the
  boundary-locality hypothesis is genuinely load-bearing (mirrors the regulator-rigidity guard). **`boundary_entropy_eq_area_over_4G`**
  (SG6): the conditional Bekenstein–Hawking bridge `S = A/(4·G)` for `G = inducedG N_eff Λ_s = 1/(N_eff Λ_s²)`, GIVEN the
  calibration `gaussStateEntropy ν₀ = N_eff/4` (per-site capacity = species/4, explicit hypothesis). ⚠ **HONEST CEILING
  (binding)**: proves `S∝A` for THIS explicit boundary-local Gaussian model only; does **NOT** prove Srednicki's free-scalar
  vacuum area law, **NOT** that the actual QIQT-H vacuum realizes/flows to this model (the remaining physical postulate,
  sharply isolated by the volume-law guard), **NOT** the calibration `N_eff/4` (the boundary-channel↔species matching),
  **NOT** `Λ_s`, **NOT** a curved heat kernel, **NOT** numerical `G` (`N`, `Λ_s`, `c_i`, κ remain). The strengthening is
  precise: previously "ASSUME `S∝A`", now "PROVE `S∝A` for an explicit boundary model; ASSUME the vacuum flows to it".
  SG1 grounding (`GaussModeEntropyDerived.lean` `gaussModeEntropy_eq_thermal_shannon`, commit 65f0725): the per-mode entropy
  IS the Shannon/von Neumann entropy of the thermal geometric occupation law (`−∑ p_k log p_k = gaussModeEntropy`), so the
  area-law entropy is grounded in first principles, not an ad-hoc formula.
- **SCOPE FIREWALL — the induced-G package predicts NO numerical `G` without an external scale** (`ScopeAudit.lean`,
  **[AF]** std-3, budget 0, 2026-07-07): **`inducedG_rescale_degeneracy`** (`inducedG (N/q²)(qΛ) = inducedG N Λ` — `G`
  depends only on the combination `N·Λ²`; neither `N` nor `Λ` separately pinned) + **`any_positive_G_realizable`**
  (`∀ N>0 G>0, ∃ Λ>0, inducedG N Λ = G` — every positive `G` is realizable). A NEGATIVE theorem (mirrors the
  `dyadic_covariance_insufficient` / `bulk_entropy_volume_law` guards) making the honesty a machine-checked fact: the value
  of `G` REQUIRES the external input `Λ_s`; it is NOT an output of the mechanism alone. Guards the manuscript against "we
  derive the value of Newton's constant" — proven is "given `N` and `Λ_s`, the model outputs `1/G = N·Λ_s²`". ⚠ The induced-G
  Lean story is at its NATURAL CEILING (GPT-5.5-pro 2026-07-07): remaining frontiers F1 vacuum↔model, F2 `N_eff/4`
  calibration, F3 `Λ_s`, F4 `κ=1/6` (=ContDiff³ exp_p tower), F5 Weyl/vector `c_i` (spin wall), F6 Tier-2 substrate⟹geometry+G.
- **The granularity-scale reframing — `G` delivered as an output** (`InducedNewtonConstant.lean`, namespace
  `QIQTH.InducedG`, all **[AF]** std-3; author-endorsed 2026-07-01). Posits a fundamental **record-granularity scale
  `Λ_s`** (`a₀=1/Λ_s`) as the primitive *in place of* `ℓ_P`, and DERIVES `G` from it + the species count `N` via the
  Sakharov/Dvali species bound `1/G = N Λ_s²`: `inducedG_delivers` (`G·(N Λ_s²)=1` — `G` is the output),
  `planckLength_sq_eq_inducedG` (`ℓ_P²=G`), `inducedG_mul_N` (`G·N=1/Λ_s²`, the analogue of AdS/CFT `1/G∝N²`),
  `inducedG_strictAntitone_in_N` (more species ⟹ weaker gravity), and the honest crux
  `inducedG_ratio_is_pure_number` (`G/a₀²=1/N` — the genuinely-*derived* content is DIMENSIONLESS; `Λ_s` is the one
  carried scale, by dimensional necessity — a length cannot come from a count, exactly as AdS/CFT carries `α'`), plus
  `capacity_exponent_in_primitives` (`A/4G=(A/4)N Λ_s²` — the capacity exponent in `{area,species,granularity}`, no
  longer presupposing `G`). ⚠ **Exact algebra**: it moves `G` from *carried* to *derived-from-`{Λ_s, N}`* (a better
  primitive), but does **NOT** compute the numerical value of `G` — that needs the full species-coefficient accounting
  (induced-EH coefficients, good to `O(1)`) which is a **[frontier]**, and it is an effective, not UV-complete, relation.
  **Species-coefficient toy** (making that frontier concrete): `effSpeciesN`/`inducedInvG` — `1/G = N_eff Λ²` with
  `N_eff = (n_s c_s + n_f c_f + n_v c_v)/12π`; `inducedInvG_eq_inv_inducedG` (recovers the earlier `inducedG` with
  `N = N_eff`), `effSpeciesN_add_scalars` (the species sum is additive), `inducedInvG_scales_Lambda_sq`. ⚠ **CITED-
  coefficient bookkeeping** (the `c_i` are hand-entered heat-kernel data, like `sakharov_ratio`); it makes the "numerical
  `G`" step concrete (*compute `N_eff` from the field content*) but does **NOT** compute the value of `G` (needs the
  real SM content + real cutoff + exact coefficients).
  **Bridge to the holographic dictionary (`HolographicBridge.lean`, [AF], see §0):** with this induced `G`, the AdS/CFT
  boundary Cardy microstate count of a BTZ horizon *equals* QIQT-H's bulk capacity exponent `(A/4)N Λ_s²`
  (`btz_cardy_eq_qiqth_capacity`; AdS radius cancels) — a *correspondence* (the two holographic bookkeepings agree
  under the shared `G`), NOT an import of a boundary CFT / Cardy formula / cross-check.
- **Toy holographic-screen code — `QIQTH/HolographicScreenCode.lean`** (namespace `QIQTH.ScreenCode`, [AF] std-3;
  `HOLOGRAPHIC_SCREEN_CODE_PLAN.md`). ⚠ **A TOY KINEMATIC INTERFACE, NOT gravity, NOT a QG claim — it does NOT close
  the "mechanism gap"** (GPT-5.5-pro consult). It turns the regional-capacity **postulate into a theorem GIVEN a
  local packing constraint**: `area_law_of_packing` (local `logDim e ≤ areaWt e/4G` on each screen link ⟹ regional
  `codeCap ≤ screenArea/(4G)` — the area law reduced to a *local* packing law), with `area_dim_independent` (large
  area, **zero** code dimension — area is an INDEPENDENT charge, NOT the `area:=log dim` tautology) and
  `area_law_saturation` (equality in the horizon-like tight-packing sector), `mincut_area_law` (the RT-flavored
  min-cut bound over a supplied cut family), and `codeCap_unbounded_at_fixed_area` (the packing constraint is
  **load-bearing** — without it, capacity is unbounded at fixed area, so the area law is *not* free). ⚠ The `1/4G` is **carried** locally
  (not derived); the screen is **fixed** (NOT background-independent); and **gravitons / dynamical Einstein (Stage 3)
  + non-circular `G`** are the genuine QG frontiers this does **not** touch (cited). It is the honest "interface into
  which a real microscopic model could plug," never a gravity claim.
- **The graviton-wall attack — `QIQTH/EmergentDynamics.lean`** (namespace `QIQTH.GravDyn`, all **[AF]** std-3;
  `GRAVITON_WALL_PLAN.md`, GPT-5.5-pro-verified). ⚠ **A CONDITIONAL FINITE SKELETON of emergent (linearized)
  dynamics — NOT solved QG, does NOT close the mechanism gap.** The FGHMVR "entanglement first law ⟹ linearized
  Einstein" logic + a QIQT-H-native finite null-focusing route, G1–G7: **G1** `allBall_firstLaw_iff_residual_zero`
  (first law at every probe ⟺ residual = 0, over a carried separating-probe family + Iyer–Wald identity); **G2**
  `eq_zero_of_decoder`/`separating_of_decoder` (finite Radon inversion ⟹ separating); **G3** `secondDiff_tailK_eq`
  (the discrete null modular kernel `Δ²K = T_kk`, anchoring to `wedge_boostCharge_eq_neg_stressFlux`); **G4**
  `EdgeRefinement`/`refinement_preserves_area_and_capacity`/`regional_bound_invariant_under_refinement`/
  `property_preserved_along_moves` (**toy** background independence, with the required weight-preserving cut
  correspondence — NOT continuum); **G5** `LambdaRG_invariant`/`InducedG_pos` (discrete RG dimensional transmutation:
  `Λ_s` from dimensionless `{b,g0}` — a **relation**, not the value of `G`); **G6** `secondDiff_of_area_firstLaw`/
  `nullFocusing_of_areaLink` (⚠⚠ **CONDITIONAL BOOKKEEPING** — the finite null Einstein equation `R_kk = 8πG T_kk`
  **given** the carried area–stress link `hAK`, which **carries the Einstein content and is NEVER derived**;
  `RkkDisc` a discrete proxy, not Ricci); **G7a** `symForm_proportional_to_minkowski_of_null_quad_zero` (a symmetric
  form vanishing on the null cone is `φ·η` — the pointwise linearized Einstein residual) + **G7b**
  `residual_vanishes_of_metric_form` (the boundary-condition plug). **G11a — the linearized graviton's KINEMATICS
  (complete, KINEMATIC only, NOT the quantized graviton):** the two transverse-traceless polarizations `e₊,e×`
  (`polPlus/polCross_isSymm/_transverse/_traceless`) are linearly independent (`graviton_polarizations_indep`);
  they carry **spin 2 / helicity ±2** — under a rotation by θ the doublet mixes by `R(2θ)`
  (`polPlus_helicity`/`polCross_helicity`, the double-angle signature), and the circular polarizations `e_± = e₊ ± i·e×`
  are **eigenvectors with eigenvalue `e^{∓2iθ}`** (`eR_helicity`/`eL_helicity` — helicity ±2 as explicit eigenvalues,
  diagonalizing the mixing); and the physical space is **exactly 2-dimensional** via the explicit gauge quotient
  (`tt_decomposition` ≤2 + `polarizations_not_gauge` ≥2 ⟹ `{e₊,e×}` a basis of TT-mod-gauge, the `D(D−3)/2=2` count).
  **G11b — the PROPAGATOR LEVEL (first step past kinematics, tree-level TENSOR STRUCTURE only, NOT quantized):**
  `kUp_null` (`k·k=0` — the graviton is **massless**, the propagator pole `1/k²` at `k²=0`) + the **physical-state
  projector** `physProj Π(h)=½(⟪e₊,h⟫e₊+⟪e×,h⟫e×)` = the TT polarization sum `½∑_λ e^λ⊗e^λ` = **the numerator of the
  harmonic-gauge graviton propagator**: `physProj_polPlus`/`_polCross` (fixes the physical pols), `physProj_idempotent`
  (`Π²=Π`), `physProj_gauge` (kills pure gauge), `physProj_trace` (kills the trace), and the capstone
  `physProj_extracts_physical` (on any symmetric TT `h`, `Π h = h₁₁·e₊ + h₁₂·e×` — extracts the physical helicity
  content, gauge projected out).
  **G11c — THE GRAVITON PROPAGATES (classical field EOM, genuine calculus, NOT quantized):** `graviton_null_wave`
  (a null-profile field `h(t,z)=f(t−z)` — each TT component — satisfies the 1+1 wave equation `∂²_t h = ∂²_z h`),
  `graviton_dalembertian_zero` (equivalently the massless d'Alembertian `−∂²_t+∂²_z` annihilates it), and
  `graviton_cos_wave` (the concrete sinusoidal wave `cos(t−z)`, non-vacuous). The graviton is a wave travelling at
  `c` — consistent with masslessness. `HasDerivAt`-based (hypotheses = C²: `Differentiable f`, `Differentiable
  (deriv f)`).
  ⚠ **Linearized ≠ full**; the quantized
  graviton (G11/G12), continuum ball modular Hamiltonians (G8), RT/extremal-area emergence (G9), Iyer–Wald geometry
  (G10), `hTkk`, interacting matter, and the numerical `G` are the cited research **frontiers** — this is the honest
  finite skeleton that advances *toward* the mechanism, never a claim of having crossed it.

- **The quantized free graviton — `QIQTH/GravitonQuantization.lean`** (namespace `QIQTH.GravitonQuant`, all **[AF]**
  std-3; `GRAVITON_QUANTIZATION_PLAN.md`). **Canonical quantization of the free graviton's two helicity modes** as
  bosonic oscillators, realized concretely on the **Bargmann–Fock space** `Fock = ℂ[X₀,X₁] = MvPolynomial (Fin 2) ℂ`
  (one variable per helicity; `0↔e₊` helicity +2, `1↔e₋` helicity −2): creation `creat i = (X_i·)` (a†_i),
  annihilation `annih i = ∂/∂X_i` (a_i). **`ccr`** — the canonical commutation relation `[a_i,a†_j] = δ_ij` (the
  defining relation, realized as the Bargmann identity `[∂_i, X_j·] = δ_ij`); **`annih_comm`** `[a_i,a_j]=0`
  (Clairaut, by `MvPolynomial` induction — Mathlib has no `pderiv_comm`); **`creat_comm`** `[a†_i,a†_j]=0`;
  **`annih_vacuum`** `a_i|0⟩=0` (vacuum `|0⟩=1`); **`one_particle_state`** `|1_i⟩=a†_i|0⟩=X_i`;
  **`number_one_particle`** `N_i|1_j⟩=δ_ij|1_i⟩` (the number operator `N_i=a†_i a_i` counts occupation). ⚠ **Free
  graviton, single momentum mode** — the exact operator content of the quantized graviton's polarization d.o.f. as a
  genuine Fock rep of the CCR; the full momentum-space field `h_{μν}(x)=∑_λ∫(a_λ(k)e^λe^{ikx}+h.c.)` and interactions
  are additive extensions of this same CCR core (Q1–Q6 all landed; the momentum continuum = more modes of the same
  algebra, a follow-on; interactions = frontier). **Q2** — the number operator `N_i=a†_i a_i`
  (`numberOp`) with occupation eigenstates `X_i^n=|n_i⟩`, `numberOp_pow` (`N_i|n_i⟩=n|n_i⟩`, spectrum ℕ),
  `numberOp_vacuum`/`numberOp_one_particle`. **Q3** — the Hamiltonian `H=ω(N₀+N₁+1)` (`hamiltonian`), the graviton
  **zero-point energy** `hamiltonian_vacuum` (`H|0⟩=ω|0⟩`) and one-graviton energy `hamiltonian_one_particle`
  (`H|1_i⟩=2ω|1_i⟩`). **Q4** — the **helicity operator** `J=2(N₀−N₁)` (`helicityOp`): `helicityOp_plus`/`_minus`
  give one-graviton helicity `±2`, tying the quantized occupation to the kinematic spin-2 eigenstates. **Q5** — the
  ladder operators (`creat_pow` raising, `annih_pow_succ` lowering) + the **coherent state** `coherent α = e^{αX}` in
  the Bargmann–Fock completion `ℂ⟦X⟧` with `annih_coherent` (`a|α⟩=α|α⟩`, the quantum→classical bridge). **Q6** — the
  free-field **two-point function** `twoPoint` (`⟨0|a_i a†_j|0⟩=δ_ij`, the propagator residue) via the vacuum
  functional `vacExp`, `vacExp_vacuum` (`⟨0|0⟩=1`). **Q1–Q6 = the complete quantized free graviton** (CCR ·
  occupation · Hamiltonian+zero-point · helicity · ladder+coherent · two-point). Standard free-field QFT,
  machine-checked — NOT a claim of quantum gravity (free · single-mode→continuum additive · classical≠interacting).

- **The bridge, increment A1 — `QIQTH/LinearizedEinstein.lean`** (namespace `QIQTH.LinEinstein`, all **[AF]** std-3;
  `BRIDGE_PLAN.md`, GPT-5.5-pro-verified; sign conventions in the header, `linEinsteinCoeff` = the physical
  coefficient). **The full flat-background linearized Einstein tensor** in plane-wave symbol form (`∂ → k` exact per
  mode): `ricciSymbol`/`einsteinSymbol` — defined for **every** wavevector `k` and perturbation `e` (the assembly
  `residual`, not only on-shell modes). **`einsteinSymbol_gauge`**/`ricciSymbol_gauge` — pure gauge `e = k⊙ξ` gives
  `δG = 0` *identically* (any `k`): linearized diffeomorphism invariance. **`bianchi_einsteinSymbol`** — the
  **linearized Bianchi identity** `k^μ(δG)_{μν} = 0` identically (every `k, e`; the engine behind B1 stress-energy
  conservation and the G7b `φ`-removal). **`einsteinSymbol_tt`** — transverse+traceless ⟹ `δG = (−k²/2)•e` (the
  TT-gauge reduction, momentum-space "`δG=−½□h`", tying to G11c). **`graviton_solves_linearized_einstein`** — null
  `kDown` + any polarization combo `a•e₊+b•e×` ⟹ `δG = 0`: **the quantized free graviton (Q1–Q6, whose polarization
  content is exactly the TT sector) is provably the graviton of general relativity.**
  **`einsteinSymbol_eq_zero_iff_massless`** + **`einstein_iff_dispersion`** — the converse: for a nonzero TT
  polarization `δG = 0 ⟺ k² = 0`, and on the z-directed family `⟺ ω² = κ²` — linearized Einstein *forces*
  propagation at the speed of light. ⚠ Linearized ≠ full; vacuum; free; flat background — anchors the graviton to
  GR; does NOT derive gravity (bridge ingredient D = the cited open frontier).

- **The bridge, increment B1 — `QIQTH/MatterCoupling.lean`** (namespace `QIQTH.MatterCoupling`, all **[AF]** std-3;
  `BRIDGE_PLAN.md`). **Matter coupling ⟺ stress-energy conservation** (the first half of Weinberg), plane-wave
  symbols: `couple e T = ∑ e_{μν}T^{μν}` (the symbol of `∫h_{μν}T^{μν}`), `divT k T ν = k_μT^{μν}` (the symbol of
  `∂_μT^{μν}`). **`couple_gauge`** — the gauge variation of the coupling equals `2∑_ν ξ_ν (k_μT^{μν})` exactly
  (symmetric `T`). **`couple_gauge_invariant_iff_conserved`** — **the iff**: the graviton–matter coupling is
  invariant under every linearized diffeomorphism ⟺ the stress-energy is conserved — gauge consistency of the
  coupling and conservation of the source are the SAME condition. **The Bianchi payoff:**
  `einstein_source_conserved` (the index-raised linearized Einstein tensor is *identically* conserved, via A1's
  Bianchi identity) ⟹ **`source_conserved_of_einstein_eq`** — any stress tensor sourced by the linearized Einstein
  equation `δG^{μν} = κT^{μν}` is automatically conserved: the geometry side forces exactly the conservation law
  the coupling side demands (the linearized consistency triangle: gauge invariance ⟺ conservation ⟸ Bianchi).
  ⚠ Linearized; free ≠ interacting; universality of the coupling (one `G` for all species) is B2; `κ`/`G` carried.

- **The bridge, increment C1 — `QIQTH/WedgeBoostClausius.lean`** (namespace `QIQTH.WedgeBoost`, all **[AF]** std-3;
  `BRIDGE_PLAN.md`). **The wedge modular Hamiltonian as the geometric boost — the Clausius datum, packaged.**
  `WedgeBoostPackage S ξ` bundles the geometric (Rindler) boost flow with the **carried Bisognano–Wichmann
  identification** `hBW : V_t ξ = Δ^{it} ξ` (a structure field, never a Lean axiom — exactly `WedgeKMSFlux` input
  #3 isolated). **`boost_correlator_hasDerivAt`** — the geometric boost correlator inherits the *derived* modular
  derivative (`hasDerivAt_inner_modUnitary`): `d/dt⟪ξ,V_tξ⟫|₀ = i·(−S)` with `S = cgpEntropy S ξ` the modular
  entanglement entropy. **`boost_flux_unique`** — the Clausius/heat-flux datum is **forced** (derivative
  uniqueness): any candidate flux `c` must equal `−S` — `δ⟨K_boost⟩ = −δS` is not a choice.
  **`boost_correlator_im_hasDerivAt`** — the real (physical) form: `d/dt Im⟪ξ,V_tξ⟫|₀ = −S`. ⚠ BW carried; the
  Rindler-weight formula (`2π∫x¹T₀₀`) packaged only at the correlator-derivative level the existing theorems
  support; free-field/RvD standard-subspace setting; NOT the area law (bridge ingredient D).

- **The bridge, increment A2 — `QIQTH/AreaEmergence.lean`** (namespace `QIQTH.AreaMap`, all **[AF]** std-3;
  `BRIDGE_PLAN.md`). **The emergence map: the SUPPLIED linearized area functional, wired to the screen code.**
  `ScreenSurface` (finite area elements: weight `w_a ≥ 0` = the `√γ` element + tangent frame `(e₁ᵃ,e₂ᵃ)`) and the
  discretized area variation `areaVar Σ h = ½∑_a w_a(h(e₁ᵃ,e₁ᵃ)+h(e₂ᵃ,e₂ᵃ))` (= `½∫√γ γ^{ab}h_{ab}`).
  **`areaProbe`** — `δA_Σ` bundled as a *linear* functional `→ₗ[ℝ]` of `h` (the exact probe shape the FGHMVR
  skeleton `G1` consumes). **`screenArea_eq_bg_add_areaVar`** — the wiring: a `ScreenCut` whose (independent) area
  charge is SUPPLIED as the geometrically perturbed weight `w_a(1+½tr_Σh)` has `screenArea = (background area) +
  δA_Σ(h)` — the code's area charge and the geometric area variation become ONE object under the carried
  identification. **`area_probes_separate`** — **the separating witness**: a symmetric `h` whose area variation
  vanishes at *every* ray surface is zero — area probes genuinely reconstruct the metric perturbation, making
  G1's separating-family hypothesis **non-vacuous with geometric (area) probes**. ⚠ The map is SUPPLIED (a carried
  hypothesis, never an axiom); deriving it from a substrate = bridge ingredient D; linearized only.

- **The bridge, increment B2a — `QIQTH/SoftGraviton.lean`** (namespace `QIQTH.SoftGraviton`, all **[AF]** std-3;
  `BRIDGE_PLAN.md`). **The soft-graviton Ward identity** — the algebraic core of Weinberg 1964–65. The soft factor
  `S(ε) = ∑_i η_i g_i (p_i·ε·p_i)/(p_i·q)` (incoming/outgoing signs `η_i`, couplings `g_i`; TAKEN as given — its
  S-matrix derivation is carried QFT input). **`quadForm_gaugeShiftK`** — the longitudinal (residual-gauge) shift
  evaluates as `p·(q⊙ξ)·p = 2(p·q)(p·ξ)`. **`softFactor_gauge_shift`** — the gauge variation of the soft factor
  is *exactly* `2ξ·P` with `P = ∑_i η_i g_i p_i` (the soft denominators cancel against the longitudinal
  numerator). **`soft_gauge_invariant_iff_ward`** — **the iff**: longitudinal decoupling (the soft factor is
  invariant under every residual-gauge shift of the polarization) ⟺ the **Weinberg sum rule** `∑_i η_i g_i p_i^μ
  = 0`. The consistency of massless spin-2 emission and the weighted-momentum sum rule are the SAME statement.
  ⚠ Algebraic identity only — NOT the analytic soft theorem; universality (all `g_i` equal ⟸ momentum
  conservation + a rich scattering family) is B2b.

- **The bridge, increment B2b — `QIQTH/SoftGraviton.lean` (extension)** (all **[AF]** std-3; `BRIDGE_PLAN.md`).
  **Universality — the equivalence principle.** `RichFamily` (the genericity hypothesis: the kernel of
  `c ↦ ∑c_ip_i` is exactly the momentum-conservation line `ℝ·η` — CARRIED kinematics input).
  **`universality`** — the Ward sum rule + generic momenta + `η_i ≠ 0` ⟹ **all couplings `g_i` equal**: every
  species couples to the massless spin-2 field with one universal charge. **`ward_of_universal`** — the converse
  consistency (universal coupling + momentum conservation ⟹ Ward). **`equivalence_principle`** — **the B2
  capstone**: longitudinal decoupling of the soft graviton ⟹ Ward sum rule ⟹ (generic family) ⟹ universal
  coupling — **Weinberg's theorem at the algebraic level, end-to-end, machine-checked**.
  **`witness_rich`/`witness_conserved`** — a concrete 5-momentum configuration satisfying `RichFamily` + momentum
  conservation (non-vacuity; kinematic witness, not an on-shell physical process). ⚠ The soft factor and
  genericity are carried QFT/kinematics inputs; the analytic soft theorem is not claimed. **Ingredient B (universal
  coupling) is COMPLETE.**

- **The bridge, increment C2a — `QIQTH/CHMKernel.lean`** (namespace `QIQTH.CHM`, all **[AF]** std-3;
  `BRIDGE_PLAN.md`). **The CHM ball kernel geometry.** `chmWeight` `β(r) = (R²−r²)/2R` (the ball modular flow's
  local inverse temperature): nonneg on the ball (`chmWeight_nonneg`), **vanishes at the entangling sphere**
  (`chmWeight_boundary` — the flow fixes the edge), center value `R/2`, factorization `(R−r)(R+r)/2R`.
  **`chmWeight_edge_slope`** — `β′(R) = −1`: **the unit surface-gravity normalization**, exactly the Rindler
  weight's slope at the wedge edge — why the SAME `2π` appears in the wedge (C1) and ball modular Hamiltonians,
  so the Clausius datum transports consistently. **`cke_tt`/`cke_tx`/`cke_xx_diag`/`cke_xx_off`** — the diamond
  **conformal Killing equation** `∂_μζ_ν + ∂_νζ_μ = −(2t/R)·η_{μν}` for `ζ₀=(t²+|x|²−R²)/2R`, `ζᵢ=−t·x_i/R`,
  verified by genuine real calculus (`deriv`/`HasDerivAt`, all component classes) — the CHM flow is a conformal
  symmetry of flat space. **`zeta0_restrict`** — `ζ₀|_{t=0} = −β`: the flow's local temperature IS the kernel.
  ⚠ Kernel GEOMETRY only — the CHM theorem (ball modular Hamiltonian `= 2π∫βT₀₀` for a CFT vacuum) is
  conformal-QFT input, carried at C2b as `CHMCompatible`; not generic QFT.

- **The bridge, increment C2b — `QIQTH/BallClausius.lean`** (namespace `QIQTH.BallModular`, all **[AF]** std-3;
  `BRIDGE_PLAN.md`). **The conditional CHM transport: the Clausius datum at EVERY ball.** `BallModularFamily`
  bundles, per ball of a probe family, a standard subspace + probe state + geometric conformal (CHM) flow with
  the **carried `hCHM` = `CHMCompatible`** identification (each ball's geometric flow acts on the state as its
  modular flow — the conformal transport of BW; CFT-vacuum input, a structure field, never an axiom); rides C1
  per ball via `toWedgePackage`. **`ball_correlator_hasDerivAt`** — every ball inherits the derived Clausius
  datum `d/dt⟪ξ_B,W^B_tξ_B⟫|₀ = i·(−S_B)`. **`ball_flux_unique`** — the per-ball datum is FORCED (derivative
  uniqueness). **`ballHeatFlux`/`ballHeatFlux_spec`** — the ball-indexed first-law data `δ⟨K_B⟩ = −S_B`, exactly
  the `δK : Ball → ℝ` input the assembly feeds into the FGHMVR skeleton `G1`. ⚠ `hCHM` carried (CFT-vacuum, not
  generic QFT); the Clausius/area law `δS = δA/4G` and the value of `G` remain the separate carried inputs of the
  assembly. **Ingredient C (modular → geometric) is COMPLETE.**

- **The joins, J3 — `QIQTH/CHMTransport.lean`** (`QIQTH.BallModular`, **[AF]** std-3;
  `HYPOTHESIS_DELETION_PLAN.md`). **The abstract CHM transport theorem — C2b's `hCHM` SHRUNK.**
  **`CHMTransportData`** — the named carried analytic inputs: the wedge (`W`, `vac`, `boost`) with **ONE**
  carried massless wedge-BW datum `hBW` (the `m>0` BW theorem is NEVER instantiated at `m=0` — the binding
  correction); per-ball conformal unitaries `U : Ball → (H ≃ₗᵢ[ℂ] H)` with the wedge→ball geometric conjugacy
  `hflow` (the ball state is DEFINED as `U B vac` — vacuum-preserving covariance is definitional, not carried);
  and the carried modular transport `hmodVac` (Tomita functoriality) in its SMALLEST pointwise-on-vacuum form
  (`hmodVac_of_operator_conj` shows it is the weakest of the conjugacy forms).
  **`hCHM_of_conformal_transport`** — the CHM identification at EVERY ball is a **theorem** of these inputs;
  **`toBallModularFamily`** — C2b's carried per-ball `hCHM` field is DERIVED; **`transport_ballHeatFlux_spec`**
  — the forced Clausius datum end-to-end. **HYPOTHESIS SHRUNK: hCHM (a per-ball physics identification) → hBW
  (one wedge datum) + hmodVac (functoriality) + geometry.** ⚠ Follow-ons: derive `hmodVac` from the RvD tower — **DONE
  (the grounding campaign, G2–G4: `hmodVac` is DELETED via `CHMTransportDataOfCarrierMap`; residue = the
  geometric carrier-conjugacy data)**; the genuine massless wedge BW (1+1 chiral current /
  3+1 conformal scalar) remains. Free-field one-particle setting; NOT a derivation of gravity.

- **The bridge, increment ASM — `QIQTH/BridgeAssembly.lean`** (namespace `QIQTH.BridgeASM`, all **[AF]** std-3;
  `BRIDGE_PLAN.md` — **THE CAMPAIGN CAPSTONE, 9/9 increments complete**). **The FGHMVR skeleton assembled with the
  bridge's real parts.** `symmMat` (the symmetric sector); **`einsteinSymbol_isSymm`** (the Einstein residual of a
  symmetric perturbation is symmetric). **`rayProbe` + `rayProbe_separating`** — A2's geometric area functionals
  as G1's probe family, with the separating hypothesis now a **proven** geometric fact (not carried).
  **`bridge_firstLaw_iff_einstein`** — the assembled skeleton: given the carried Iyer–Wald identity, the
  entanglement first law `δS = δK` at every probe **⟺** `einsteinSymbol k h = 0` (linearized vacuum Einstein).
  **`bridge_conditional`** — the Jacobson-shape capstone: carried **Clausius/area law** `δS = δA/4G` + carried
  **modular-geometric matching** `δK = δA/4G` (the C1/C2b forced Clausius data) + carried **Iyer–Wald** ⟹ **the
  emergent graviton satisfies linearized vacuum Einstein** — "entanglement + area law ⟹ Einstein" machine-checked
  end-to-end from real parts. ⚠ **CONDITIONAL**: every derived piece is a theorem (A1 anchor+Bianchi; A2
  probes+separation; B1/B2 coupling+equivalence principle; C1/C2 forced Clausius); every physical input an
  explicit hypothesis (Clausius/area law, Iyer–Wald, BW/CHM, genericity, `G`). NOT a derivation of gravity —
  ingredient D (background independence, nonlinear completion, area law from counting, value of `G`) is the cited
  open frontier. Linearized, free, flat.

- **The joins, J2 — `QIQTH/CHMSymbolProbe.lean`** (`QIQTH.CHM`, **[AF]** std-3; `HYPOTHESIS_DELETION_PLAN.md`).
  **The CHM kernel-moment normalization + the bridge refactor — the Iyer–Wald input SHRUNK.**
  **`chmRadialMass3_eq`** — the radial mass of the C2a ball kernel, `∫₀^R 4πr²·β_R(r) dr = 4πR⁴/15`
  (one-variable calculus, `β_R(r) = (R²−r²)/2R`); `chmRadialMass3_pos`. **`CHMSymbolProbe3`** — the
  kernel-weighted symbol pairing at the pure algebraic symbol level (constant radial density, no plane-wave
  phase), normalized by the kernel mass; **`CHMSymbolProbe3_eq`** / **`CHMSymbolProbe3_einstein_eq_areaVar`** —
  it EQUALS the ray area probe `areaVar (raySurf v)`. **`bridge_conditional_probe`** — the assembly consuming
  the DERIVABLE probe: the carried `hIW` FACTORS as (physical deficit = kernel probe) ∘ (kernel probe =
  areaVar); the second factor is now a **theorem**; the residual carried input is `hDeficit` — the
  identification of the physical first-law deficit with the CHM kernel probe, stated once (the FGHMVR content,
  not derivable from the held pieces). **HYPOTHESIS SHRUNK: hIW → hDeficit.** ⚠ Conditional; linearized, free,
  flat; NOT a derivation of gravity.

- **Earns-gravity E1 — `QIQTH/FreeFieldWedgePackage.lean`** (`QIQTH.EarnGravity`, **[AF]** std-3;
  `MICROTHEORY_EARNS_GRAVITY_PLAN.md`). **BW discharged into the bridge for the free field:**
  `freeFieldWedgePackage` — the C1 `WedgeBoostPackage.hBW` identification is a THEOREM here (wired from the
  unconditional one-particle Bisognano–Wichmann), for every state; `freeField_clausius_unconditional` — the wedge
  Clausius datum `δ⟨K_boost⟩ = −δS` forced with **no external BW premise** (domain/spectral conditions remain).
  ⚠ Free field, positive mass, nice wedge; the Clausius/area law and `G` stay the separate carried inputs.

- **Earns-gravity E2 — `QIQTH/AreaDecoder.lean`** (`QIQTH.AreaMap`, **[AF]** std-3;
  `MICROTHEORY_EARNS_GRAVITY_PLAN.md`). **The metric reconstructed FROM the code's area data** — the explicit
  decoder inverting A2's emergence map: `reconstruct` (`h_ii = 2A(e_i)`, `h_ij = A(e_i+e_j)−A(e_i)−A(e_j)`,
  polarization); **`reconstruct_areaVar`** — `reconstruct(v ↦ δA_ray(v)(h)) = h` for symmetric `h` (the emergent
  perturbation is a FUNCTION of ray-probe area measurements; `einsteinSymbol` applies to it verbatim);
  **`reconstruct_unique`** — the area data determines the metric. ⚠ Pointwise tensor reconstruction in a chosen
  basis, NOT a smooth global metric field; symmetry required; linearized, finite/model level.

- **Earns-gravity E3 — `QIQTH/CalibratedAreaLaw.lean`** (`QIQTH.EarnGravity`, **[AF]** std-3;
  `MICROTHEORY_EARNS_GRAVITY_PLAN.md`). **`calibrated_entanglement_cut_area_law` — the Strominger-shape join,
  in-model.** `screen_cut_eq` (the verifier-required cut-indexing lemma: Track C's directed `cut` of the canonical
  two-layer screen graph = the link sum, no double counting); `inducedScreenArea := 4G·cut(wEnt,S)` — the area
  **INDUCED** from the calibrated entanglement cut (the separate `areaWt` label deleted); the capstone — under the
  carried local calibration `log D_e = wEnt e`: **`log #microstates = screenArea/(4G)`** (count and geometry as
  two computations of one calibrated weight family); `uniform_realizes_area_law` — the maximum-entropy (uniform)
  record realizes the count (Jacobson's equilibrium regime, via `shannon_uniform_eq_log_card`). ⚠ **NOT a
  derivation of area from entanglement** — the calibration carries the physical content (deleting it = continuum
  trace + background independence); the no-calibration guard (`codeCap_unbounded_at_fixed_area`) stays in force;
  finite/model level; `G > 0`.

- **Earns-gravity E4 — `QIQTH/CodeEquilibrium.lean`** (`QIQTH.EarnGravity`, **[AF]** std-3;
  `MICROTHEORY_EARNS_GRAVITY_PLAN.md`). **Code equilibrium ⟹ first law ⟹ Einstein — the dynamics rung.**
  `RayPathFamilyRealizes` — a state path PER RAY (one path is not enough), each through its own reference, with
  per-ray BW identification + analytic derivative data (carried structure fields, never axioms), realizing the
  ray's first-law datum. **`rayFamily_firstLaw`** — equilibrium (relative-entropy stationarity, B4′) forces
  `δS = δK` at EVERY ray probe. **`clausius_sign_adapter`** — the explicit `K ↦ −K` orientation bridge between
  the first-law (`δS = δ⟨K_σ⟩`) and Clausius (`δ⟨K⟩ = −δS`) conventions. **`code_equilibrium_einstein`** — the
  capstone: a code at per-ray relative-entropy equilibrium, with the carried Iyer–Wald identity, has an emergent
  perturbation satisfying **linearized vacuum Einstein** — Jacobson's equation-of-state with the state the code's
  equilibrium. ⚠ Conditional (BW/analytic/Iyer–Wald carried); linearized, free, finite/model level; NOT QG.

- **Earns-gravity E5 — `QIQTH/DeserRung.lean`** (`QIQTH.EarnGravity`, **[AF]** std-3;
  `MICROTHEORY_EARNS_GRAVITY_PLAN.md` — **CAMPAIGN COMPLETE, E1–E5**). **The Deser rung: the graviton sources
  itself consistently (second order).** `gravStress` — the graviton's own Isaacson/radiation-form stress symbol
  `T^{μν}_GW = k^μk^ν·⟨e,e⟩_η`; `gravStress_symm`; **`gravStress_conserved`** — on-shell (null `k`, the
  graviton's own masslessness) the self-stress is conserved `k_μT^{μν}=0`;
  **`deser_selfcoupling_consistent`** — hence, by B1's iff, the coupling of the graviton TO ITS OWN stress is
  invariant under every linearized diffeomorphism: second-order self-sourcing is gauge-consistent — the first
  order of Deser's bootstrap toward nonlinear GR (which B2's equivalence principle forces the field to attempt);
  `gravStress_traceless` (pure radiation on-shell). ⚠ First bootstrap order only — the full nonlinear iteration
  and its quantum completion are NOT built; plane-wave symbol level; free, flat; NOT QG.

- **The joins, J4 — `QIQTH/FormalDeser.lean`** (`QIQTH.FormalDeser`, **[AF]** std-3;
  `HYPOTHESIS_DELETION_PLAN.md` — **JOINS CAMPAIGN COMPLETE, J1–J4**). **The formal Deser system: consistency
  PROPAGATION, honestly** (per the binding correction: NO tower positing conservation per order).
  **`FormalDeserSystem`** — order-indexed `L n`/`div n` (nonlinear products shift momenta: order `n` lives at
  `n•k`), the **proven** linear Bianchi `div n ∘ L n = 0`, the lower-order source (`S_depends_lt`), and ONE
  carried coefficient field `formalBianchi_step` — an identity in the history (holds whether or not anything
  solves), the coefficient-Bianchi content, carried until the nonlinear Einstein coefficients are formalized.
  **`next_source_conserved`** — the PROPAGATION THEOREM: a tower solving through order `N` forces the
  order-(N+1) source conserved — conservation DERIVED, never posited. **`extend_of_solver`** — with a solver
  (right inverse on conserved sources) the bootstrap extends order by order: formally unobstructed.
  **`einsteinDeserSystem`** — the instantiation with the HELD symbols: `L n = einsteinSymbol (n•k)`,
  `div n = kContract (n•k)`, the `bianchi` field DISCHARGED by `bianchi_einsteinSymbol` at every harmonic;
  `einstein_next_source_conserved` end-to-end. **HYPOTHESIS SHRUNK: the per-order conservation tower → the
  single coefficient identity `formalBianchi_step`; the linear Bianchi input DELETED (a held theorem).**
  ⚠ Consistency propagation only; order 2 remains the concrete Deser theorem (E5); the nonlinear Einstein
  coefficients are the cited frontier. NOT a nonlinear completion; NOT QG.

- **The operator emergence map, Q1 — `QIQTH/OperatorEmergence.lean`** (`QIQTH.OperatorEmergence`, **[AF]**
  std-3; `OPERATOR_EMERGENCE_PLAN.md` — the bridge's Tier-1 item 1: "graviton = quantized area fluctuation",
  theorem-shaped). Carrier `Op = Module.End ℂ Fock` (polynomial Bargmann–Fock — never a CLM completion).
  **`areaDataM`/`reconstructM`** — the ray-probe area data and decoder over ANY ℂ-module;
  **`reconstruct_areaDataM`** — the module-level decoder identity; **`qMode = a + a†`**; **`hHat`** — the
  operator-valued metric perturbation (real plus/cross polarizations, symmetric). CAPSTONE
  **`reconstruct_hHat`** — the decoder inverts the QUANTIZED area map at operator level: the metric operator
  is a function of its own area-fluctuation observables, entrywise in `End(Fock)`. ⚠ Fixed momentum,
  linearized, free; the code join is Q5 (expectation-level ONLY — the finite-code CCR isometry is obstructed
  by the trace argument); NOT QG. **Q2 LANDED**: `ccr_op` (the CCR at operator level), `comm_linObs` (the
  master c-number commutator of linear observables), the area observables `areaOp`/`areaMomCan`/`areaPair`;
  **`comm_area_area = 0`** — equal-time areas COMMUTE (the naive noncommutativity claim is CUT, per the
  binding correction); **`comm_area_mom`** — the canonical pair `[Â(Σ),Π̂Can(Σ′)] = i·areaPair·1` (where
  the quantum structure actually lives); **`vacuum_area_pair`** — `⟨0|Â(Σ)Â(Σ′)|0⟩ = areaPair(Σ,Σ′)`:
  the vacuum's quantized area fluctuations, quantitative and honest. **Q3 LANDED**: the `LinExpr`
  expression layer (two interpretations: `toOp` = the operator, proven; `cohExpect` = the coherent
  expectation — u-rule grounded by the held `annih_coherent` eigenvalue relation, v-rule = Bargmann
  adjointness, cited; the polynomial Bargmann inner product = named follow-on); CAPSTONES
  **`coherent_hHat`** (`⟨α|ĥ|α⟩ = classicalH(α) = Σ_λ 2Re(α_λ)·pol^λ`) and **`coherent_area`**
  (`⟨α|Â(Σ)|α⟩ = areaVar(Σ, classicalH α)` — the exact `δA` input the assembled bridge consumes): **the
  classical emergence map is the coherent shadow of the operator map.** **Q4 LANDED**: the explicit
  monomial-scaling flow (`scaleU = aeval(z•X)`, no Stone) with the DERIVED Heisenberg phases
  (`heis_annih`/`heis_creat`/`heis_q` — `U_z q U_z⁻¹ = qModeT`, the chain rule `annih_scaleU` by
  induction); `qModeT_harmonic`; the coefficientwise ODE layer `OpHasDerivAt`; CAPSTONES **`qModeT_wave`**
  + **`hHatT_wave`** — the operator WAVE EQUATION `ḧ + ω²ĥ = 0`, coefficientwise (the graviton wave
  equation as an operator identity of the emergence map) — and **`comm_areaT`** — the time-separated area
  commutator `[Â_Σ(t), Â_Σ′(s)] = 2i·sin(ω(s−t))·areaPair·1` (vanishing at equal times, per the honest
  Q2 structure). **Q5 LANDED — CAMPAIGN COMPLETE (Q1–Q5)**: `areaTotOp = A₀·1 + Â` (total-to-total, per
  the binding correction); **`coherent_areaTot_re`** (`⟨α|Â_tot(Σ)|α⟩ = A₀ + δA_Σ(h(α))`); CAPSTONE
  **`code_count_eq_fock_area_expect`** — given the held calibration and the NAMED carried `hJoin` (the
  code's induced screen area = the coherent total-area expectation; the emergence-map identification,
  stated once), `log #microstates = ⟨α|Â_tot(Σ)|α⟩/4G` — **the screen code's counting and the graviton's
  area operator agree as two computations of one number.** ⚠ The join is expectation-level FOREVER (the
  finite-code CCR isometry is obstructed by the trace argument); the code Hilbert space is NOT Fock;
  fixed momentum, linearized, free; NOT QG. Carried: `hJoin`, the calibration; the Bargmann-adjointness
  grounding of the coherent v-rule was DELETED by the grounding campaign (G1 below).

- **The grounding campaign, G1–G5 — `QIQTH/BargmannPairing.lean` + `QIQTH/ModularTransport.lean`**
  (**[AF]** std-3; `GROUNDING_PLAN.md` — **CAMPAIGN COMPLETE**). **Carried hinges in multiple landed
  results deleted at once.**
  - **G1 (`BargmannPairing.lean`)** — the operator-emergence coherent v-rule GROUNDED:
    **`bargmann_adjoint`** (creation adjoint to annihilation on the polynomial Bargmann–Fock space,
    `⟨p, X_l·q⟩_B = ⟨∂_l p, q⟩_B`, by monomial-linearity), the polynomial-level coherent reproducing rule
    (`coeffFamilyPair_cohCoeff`: `⟨coh α, p⟩_B = p(conj α)`) and creation rule (`cohPair_X_mul`); the
    completion-level identification stays cited (honest boundary for a polynomial carrier).
  - **G2** — the RvD operator transports under unitary conjugacy: `starProj_transport` (real orthogonal
    projections, by the uniqueness characterization under the ℝ-isometry), `carrierMap_mulI` (`i𝒦`
    automatic from ℂ-linearity), `rvdRC_transport` (`R_{S′} = U R_S U⁻¹`); membership-form carrier
    hypotheses (`CarrierMap`) so payoff sites never touch `Submodule.map`.
  - **G3 (the crux)** — **the unitary covariance of the spectral theorem and Borel calculus**, new tower
    infrastructure: `conjUStarAlgHom` + **`cfc_conjU`** (continuous FC covariance, Mathlib `map_cfc`);
    **`specMeasure_conjU`** (the RMK scalar measures transport as pushforwards — C_c tests
    Tietze-extended to ambient symbols); `specProj_conjU` (the spectral projections transport),
    `pvmScalarMeasure_conjU`, `diagInt`/`bilinDiag` transport; CAPSTONE **`borelFC_conjU`** —
    `f(UTU⁻¹) = U·(f∘e)(T)·U⁻¹` for bounded measurable symbols (the honest scalar-measure route; the
    generator-uniqueness shortcut rejected at design time).
  - **G4 (the payoffs)** — **`modUnitary_transport`**: `Δ^{it}_{S′} = U Δ^{it}_S U⁻¹` under carrier
    conjugacy. **J3's `hmodVac` carried field DELETED** (`CHMTransportDataOfCarrierMap` — the transport
    data is built from GEOMETRIC carrier conjugacy alone; residue = the geometry itself + the massless
    wedge BW); **Gate 3's `Sren_cov` hinge fed by a derived theorem** (`modUnitary_inner_cov` — the
    modular correlators are carrier-covariant); **the ball-Clausius per-ball modular input replaced by
    per-ball geometry** (`ball_modUnitary_cov`). ⚠ NOT QG; no wall crossed.

- **THE KEYSTONE (THE COUNT), K0 — `QIQTH/Keystone.lean`** (**[AF]** std-3; `KEYSTONE_PLAN.md` — the
  remaining QG-shaped problem, laddered honestly; K0–K6 in progress). **K0 — the finite trace-entropy
  substrate:** `maxMixed = N⁻¹·1` w.r.t. the UNNORMALIZED counting trace (the binding correction);
  `maxMixed_eigenvalues` (constant spectrum); **`vonNeumannEntropy_maxMixed`** (`S(maxMixed) = log N` —
  the entropy half of the count) + **`vonNeumannEntropy_le_log_card`** (the Gibbs/Jensen GUARD: `S ≤ log N`
  for every density, so the count equality is claimed only at maximal mixing). **K2a LANDED**: `LinkDims`/`Micro`/
  `card_micro` (= Π D_e); `DiamondAlg` + the UNNORMALIZED `tauCount`; **`tau_recordProj`** (`τ(P_R) = |R|`
  — the trace COUNTS records) + `tau_top`; the TRACE-DEFINED weight `wEntTau e = log D_e`;
  **`K2a_count_capstone`** — `S(maxMixed) = log N_C = Σ_e log D_e = inducedScreenAreaTau/(4G)` as a
  theorem (G only through the normalization); **`count_matches_external_weights_iff`** — pointwise
  external-weight matching IS the old calibration (stated honestly, never deleted). **K2b LANDED — THE COUNT IN
  THE HELD CORE**: `flatClock` (the mass-`N_C` clock window, a genuine `ExpTest`); `Iexp_flatClock = N`;
  **`tauMonomial_uniform_eq_tauCount`** — `τ₀(π(x)·q_{N_C}(L)) = Tr x`: **the counting trace IS the
  restriction of the constructed crossed-product trace τ₀** (the held W3a monomial formula at the uniform
  matter state, t = 0), not a new postulate; `tau0_recordProj_eq_card` (`τ₀ counts records`);
  **`wEntTau_eq_log_tau0Dim`** — **THE CALIBRATION IS A THEOREM** (the link weight IS the log of the link
  fiber's τ₀-dimension — trace-defined, nothing calibrated); CAPSTONE **`K2b_tau0_capstone`** —
  `S(record corner) = log dim_{τ₀}(𝒟_C) = A_τ(C)/4G` in the finite record corner of the constructed core.
  ⚠ The finite branch exactly as scoped; Walls 1–5 stand (continuum algebras, external-area matching,
  Type III₁/II∞, normal weights, value of G). **K5 LANDED**: `vonNeumannEntropy_unitary_conj` (trace-preserving
  unitaries preserve the count — Gate-3's finite instantiation), `tauCount_conj`,
  **`tau0_dual_scaled`** (the dual action SCALES the τ₀-count by `e^{−s}` — the held W3a exact
  scaling at work), CAPSTONE **`K5_dual_covariant_count`** — `S(θ_s·) = S(·) − s`: the honest
  dual-covariance law with transported area. **K1 LANDED** (`KeystoneOperator.lean`): `clockMul`
  (bounded-symbol multiplication operators on the crossed-product space), the product law, the WEYL
  COVARIANCE `λ_t∘M_g = M_{g(·+t)}∘λ_t`, and `repMonomial` (the represented core monomial as a
  genuine operator). **K3 LANDED**: `tauCount_norm_le_sum_diag` (finite-corner boundedness of the
  counting trace — the norm-closure extension trivial in finite dimension) + the K3 AUDIT FIX — the
  carried `DualWeightTraceExtension` interface was VACUOUS (an abelian collapse witness `M = ℂ`,
  `τ = re`, `embed = tau ω` satisfied it for ANY algebra); STRENGTHENED with `embed_mul` (multiplicative
  embedding), killing the witness (the core trace is not multiplicative); no fake finite-corner instance
  shipped — Wall 3 (the σ-weak/normal-weight vN extension) stands, now carried non-vacuously.
  **K6 CHECKPOINT — CAMPAIGN COMPLETE (the two honest sentences, verbatim):**
  HAVE: "every finite code screen realized as a finite record corner of the constructed crossed-product
  core has S_{τ₀} = log dim_{τ₀}(𝒟_C) = Σ_e log dim_{τ₀}(P_e) = A_τ(C)/4G; in the code instance
  dim_{τ₀}(P_e) = D_e, so the calibration is a theorem (trace-defined weight) and the count-built area
  operator gives the join by construction — no hClausius/hGeom/hCalib/hJoin carried in this branch."
  HAVE NOT (Walls 1–5, named): continuum QFT diamond algebras ARE these corners; external geometric
  area = count-built area; Type III₁/II_∞ continuum structure in Lean; σ-weak/normal weights; the value
  of G. ⚠ NOT QG solved; no wall crossed.

- **THE JOIN INSTANCE, JI1 — `QIQTH/JoinInstance.lean`** (**[AF]** std-3; `JOIN_INSTANCE_PLAN.md` — delete
  `hJoin` by construction: the bridge at the finite level; JI1–JI7 in progress). **JI1 — the local area
  decomposition:** `localAreaVar` (the per-element linearized share `δA_a = ½w_a(h(e₁,e₁)+h(e₂,e₂))`) with
  `sum_localAreaVar` (the shares sum to the held `areaVar`); `A0Split` — the NAMED apportionment of the
  global background area (honest DATA per the binding verdict: no canonical per-link split of a global
  constant; the uniform split is an optional policy constructor, never pretended-derived); CAPSTONE
  **`sum_localArea`** — `∑_a (β_a + δA_a) = A₀ + areaVar S h`: the carried `hJoin`'s RHS decomposed per
  link (the algebraic core of the join). **JI2 LANDED — `hJoin` IS A THEOREM FOR THE CONSTRUCTED
  DICTIONARY**: `tauWEnt` (the geometry-defined weight `A^loc_a/(4G)`), `tauDim = exp(wEnt)` (REAL
  positive trace-dimension — no integrality, the Type II lesson), **`hcal_tau`** (the calibration is a
  theorem at the τ level, `Real.log_exp`), CAPSTONE **`hJoin_tau`** — the exact Q5 hypothesis shape
  `inducedScreenArea G S.elems wEnt = A₀ + areaVar S (classicalH pol α)` supplied by construction
  (geometry → code; no smuggling). **JI3 LANDED — THE DICTIONARY LIVES IN THE HELD CORE**:
  `tauMonomial_flatClock_zero` (the general mass lemma `τ₀(π(x)·q_r(L)) = ω(x)·r`), CAPSTONE
  **`exists_tau0_corner_of_posReal`** (every positive real is a REALIZED τ₀ corner value, window
  witness explicit — per the binding qualifier, the free window mass, never subcorners of one fixed
  fiber+window), `tau0_link_witness`/`tau0_total_witness` (each `Dτ_a` by its own window; the total
  `∏Dτ_a` by the product-mass window). **JI4 LANDED — THE GENERIC EXACT REPLACEMENT FOR `hJoin`**:
  `dimTau = ∏ Dτ_a` + `Stau = log dimTau`; `Stau_eq_sum_wEnt`; CAPSTONE **`Stau_eq_area_over_4G`** —
  `S_τ(J) = (A₀ + areaVar S (classicalH pol α))/(4G)` for ARBITRARY graviton data (count and geometry
  as two computations of one number, NOTHING carried — the join is the construction);
  `Stau_eq_inducedScreenArea_over_4G` (the exact Q5 interface shape via `hJoin_tau`). **JI5 LANDED —
  THE OLD Q5 CAPSTONE WITH NO `hJoin` HYPOTHESIS**: `NatRealizable` (the NAMED realizability datum —
  integer dims whose logs are the geometry-defined weights; honest design-condition data),
  `NatRealizable.tauDim_eq` (where realizable, `Dτ_a = D_a` — the two levels agree), CAPSTONE
  **`code_count_eq_fock_area_expect_noJoin`** — `log #microstates = ⟨α|Â_tot(Σ)|α⟩/(4G)` with the
  join SUPPLIED by `hJoin_tau`, not carried. **JI6 LANDED — THE TWO NORMALIZATIONS ARE ONE FORMULA**:
  `AJoin` (the instance's own total area, INTERNAL), CAPSTONE **`Stau_eq_capacity_primitives`** — with
  the DERIVED `G = 1/(N·Λs²)`, `S_τ(J) = (A_J/4)·N·Λs²` (the count-built and induced-G normalizations
  meet in `{area, species, granularity}`); `tauWEnt_le_patch_capacity` (the patch bound);
  `localArea_eq_log_cost`/`qubit_area_cost` (one nat costs `4/(N·Λs²)` of area; one qubit
  `4·log 2/(N·Λs²)`). **JI7 CHECKPOINT — CAMPAIGN COMPLETE (the two honest sentences, verbatim):**
  HAVE: "after JI1–JI6, `hJoin` is no longer a hypothesis for the constructed τ join or for
  nat-realizable finite-code joins, and the count normalization rewrites to `(A_J/4)·N·Λs²` with local
  capacity corollaries." HAVE NOT: "no theorem says arbitrary external real geometry has exact natural
  link dimensions, no asymptotic approximation is included, and no canonical `A0` split is asserted
  beyond the named apportionment data/policy." ⚠ NOT QG solved; no wall crossed; the CCR-isometry
  obstruction is permanent (the join is expectation-level forever).

- **THE EMBEDDING, EM1 — `QIQTH/Embedding.lean`** (**[AF]** std-3; `THE_EMBEDDING_PLAN.md` — the
  matter-side dictionary: the N-mode truncated free-field diamond algebra IS a counted record corner;
  EM1–EM7 in progress). **EM1 — the mode dictionary aliases:** `ModeAssignment` (mode labels + per-mode
  truncation cutoffs — NAMED finite data, never constructed from the continuum), `toLinkDims` (a LINK IS
  A FIELD MODE), `FieldMicro`/`TruncatedFockBasis`/`FieldDiamondAlg` with rfl dictionary theorems (the
  identification is DEFINITIONAL — `Micro L C = (e : C) → Fin (D e)` IS a multi-mode truncated Fock
  basis); `card_truncatedFockBasis` (= Π cutoffs); CAPSTONE **`truncated_field_diamond_entropy`** —
  the keystone count READ as the truncated field diamond's entropy, `S = Σ_k log D_k = A_τ(C)/4G` with
  links = modes. **EM2 LANDED — THE SINGLE-MODE ALGEBRAS EMBED**: `sameOff`/`updMode`/`zeroMicro` (the
  dependent-update toolkit, casts hidden), **`sum_mode_fiber`** (the reusable fiber-sum engine),
  `modeOp` (the direct-entry coordinate embedding — A on fiber k, delta elsewhere; never Kronecker),
  the transport package `modeOp_one/add/smul/star/mul` (mul via the fiber-sum lemma), CAPSTONE
  **`modeOp_injective`** — each single-mode truncated-oscillator algebra genuinely embeds into the
  diamond algebra. **EM3 LANDED — THE PER-MODE OSCILLATORS**: `modeLowering`/`numberOp`/`topProjMode`
  (a_k, N_k, P_top,k), `raising_mul_lowering` (N_k = a_k†a_k), CAPSTONE **`mode_ladder_commutator`** —
  the honest per-mode truncation defect `[a_k, a_k†] = 1 − D_k·P_top,k` (the held single-mode theorem
  TRANSPORTED through the embedding; exact CCR permanently impossible); `occupationProj` +
  **`occupationProj_joint_eigen`** (the finite spectrum reading: N_k eigenvalue n_k on every occupation
  projector); the ladder relations `[N_k, a_k] = −a_k`, `[N_k, a_k†] = a_k†` (by adjoints).
  **EM4 LANDED — THE CROSS-MODE ALGEBRA**: `sameOff2` + `modeOp_mul_apply_of_ne` (the two-coordinate
  product entry), CAPSTONE **`modeOp_commute_of_ne`** — THE one generic theorem (coordinate operators at
  different modes commute); corollaries `[a_k,a_j] = [a_k,a_j†] = [N_k,a_j] = 0` (k ≠ j) — the BOSONIC
  sector (pi-fiber ladders commute; fermionic CAR needs the held graded layer, cut per the verdict).
  **EM5 LANDED — RECORDS ARE OCCUPATION POINTER-BASIS SUBSETS**: `occupationProj`
  star/idempotent/orthogonal + `sum_occupationProj_eq_one` (complete pointer basis), CAPSTONE
  **`recordProj_eq_sum_occupationProj`** (every keystone record projector = the sum of its microstates'
  occupation projectors — the theorem, not a slogan); `field_record_tau0` (the field record trace through
  the constructed τ₀); **`encoded_mode_ladder_commutator`** — the corner transport with the HONEST
  identity `[ι_V(a_k), ι_V(a_k)†] = P − D_k·ι_V(P_top,k)`, `P = VVᴴ` never the ambient 1.
  **EM6 LANDED — CAPACITY AS CONSTRAINT**: `capacityBound` (Σ log D_k ≤ Area/4G — selecting admissible
  assignments, NEVER a generator), CAPSTONE **`field_entropy_le_area_of_capacity`** (admissible ⟹
  S ≤ Area/4G), `field_entropy_eq_area_of_saturation` (equality for the CHOSEN assignment),
  `localModeArea = 4G·log D_k` + `sum_localModeArea` (the per-mode reading of A_τ),
  `mode_count_le_area_of_qubit_capacity` (|C|·log 2 ≤ Area/4G). **EM7 LANDED — CAMPAIGN COMPLETE**: `LocalizedModeFrame` (the supplied witness — CERTIFIES a named
  finite mode list against the diamond's standard subspace, never constructs), CAPSTONE
  **`truncated_field_count_eq_fock_area_expect_noJoin`** — THE FINITE-LEVEL BRIDGE END TO END:
  `log #(truncated Fock basis) = ⟨α|Â_tot(Σ)|α⟩/(4G)`, composing field → corner → count → area →
  graviton with NO join hypothesis.
  **EM7 CHECKPOINT (the two honest sentences, verbatim):** HAVE: "the N-mode truncated free-field
  diamond algebra IS a counted record corner — the occupation basis is Micro, the per-mode truncated
  oscillators embed with their honest defect ([a,a†] = 1 − D·P_top), records are occupation projectors,
  the count S = Σ log D_k = A/4G reads as the truncated field diamond's entropy, capacity
  bounds/saturates the cutoffs as a constraint, and the mode dictionary composes with the join instance
  end-to-end (field → corner → count → area → graviton expectation)." HAVE NOT: "no exact finite CCR
  (the truncation defect is permanent); no Type III₁ finite corner (the cutoff→continuum limit is THE
  wall, never claimed); no construction of continuum-localized modes from the standard subspace (mode
  membership is named finite data, at most CERTIFIED by a supplied localization witness); capacity is a
  constraint, not a generator." ⚠ NOT QG solved; no wall crossed.

- **THE DYNAMICS, DY1 — `QIQTH/Dynamics.lean`** (**[AF]** std-3; `THE_DYNAMICS_PLAN.md` — the code's
  time evolution + the independent cross-check + the conjecture; DY1–DY7 in progress). **DY1 — the
  diagonal dynamics core:** `energy`/`Hcode` (`Hcode_apply_diag`: H diagonal with entry
  E(n) = Σ ω_k n_k); `phaseUnitary` (group law) + `alpha = U_t A U_{−t}` with THE ENTRY FORMULA
  **`alpha_entry`** (`α_t(A)(n,m) = e^{it(E(n)−E(m))}·A(n,m)` — no Stone, no Matrix.exp, per the
  binding verdict); `alpha_zero/add/mul/star` (a one-parameter group of ⋆-automorphisms);
  **`alpha_diagonal`/`alpha_recordProj` — RECORDS ARE STATIONARY** (H is a function of the N_k — the
  honesty point, stated not hidden); CAPSTONE **`alpha_modeLowering`/`alpha_modeRaising`** — the
  nontrivial dynamics: the ladders rotate at their mode frequencies, `α_t(a_k) = e^{−iω_k t}·a_k`.
  **DY2 LANDED — THE EXPLICIT THERMAL STATE**: `ZMode`/`pMode` (positive, normalized per-mode
  Boltzmann weights), `gibbsWeight` (the product weight, normalized via the occupation-basis
  product-sum interchange), `gibbsDensity` (explicit product diagonal — no matrix exponential),
  CAPSTONE **`gibbs_isDensity`** (PSD + unit trace) + **`gibbs_stationary`** (the flow preserves the
  diagonal, so tr(ρ_β·α_t(A)) = tr(ρ_β·A)). **DY3 LANDED — THE KMS BRIDGE**: `sigmaDiag_entry` +
  `log_gibbsWeight`, CAPSTONE **`sigmaDiag_gibbs_eq_alpha_rescale`** — the Gibbs state's MODULAR flow
  IS the rescaled PHYSICAL flow, `σ_s^{ρ_β} = α_{−βs}` (the partition function cancels; the flow is
  never defined by modAut — the bridge runs the other way, per the verdict); `gibbs_kms_condition`
  (the held finite Tomita–Takesaki applied to the explicit density, via the `gibbsInvertible`
  instance); **`gibbsDensity_zero_eq_maxMixed`** (β = 0: the thermal tower and the keystone counting
  tower share their ground floor). **DY4 LANDED — THE GIBBS MARGINAL IS AGAIN GIBBS**:
  `restrictMicro`/`marginalWeight` (region = subset of MODE labels; diagonal ⟹ classical
  marginalization, no operator partial trace), CAPSTONE **`marginal_gibbsWeight`** (the complement
  modes sum to 1 mode-by-mode) + **`reduced_gibbsDensity_eq`** (the reduced density IS the region's
  own Gibbs density — diagonal, product over k ∈ R). **DY5 LANDED — THE REGION ENTROPY FORMULA**:
  **`eigenvalues_sum_diagonal`** (NEW reusable spectral fact: eigenvalue sums of a real diagonal
  matrix are entry sums, via the diagonal charpoly) + `vonNeumannEntropy_diagonal` (diagonal vN =
  Shannon); `shannon_gibbsWeight` (product additivity); CAPSTONE **`entropy_gibbs_region`** —
  `S(ρ_{β,R}) = S_micro(R,β) = Σ_{k∈R} s_k(βω_k)`; **`Smicro_zero`** (saturation: `= Σ log D_k`) +
  **`Smicro_le_count`** (all-β bound; no arbitrary-β area equality claimed).
  **DY6 LANDED — THE SATURATED CONDITIONAL SAKHAROV CROSS-CHECK** (`QIQTH/CrossCheck.lean`,
  CALIBRATION-FREE, grep-verified): `InducedCrossCheckData` (the macro side as INDEPENDENT
  Sakharov/species/cell data — structure fields, never axioms), `ofSpecies` (with the derived
  `G_ind = 1/(N_eff·Λs²)` the quarter-G identity is the held theorem; only species/cell matching
  remains input), `S_micro_le_inducedQuarterG` (all β), CAPSTONE
  **`S_micro_zero_eq_inducedQuarterG`** — `S_micro(R,0) = A_ind/4G_ind`: the micro side computed
  from the code Hamiltonian, the macro side supplied independently, NO keystone calibration in the
  proofs; equality at SATURATION ONLY (arbitrary-β equality false, never claimed); the one-loop
  continuum version = the named frontier. **DY7 LANDED — CAMPAIGN COMPLETE**
  (`QIQTH/Conjectures.lean` + docs mirror): **`FlatSpaceRecordGravityCorrespondence`** — THE
  FLAT-SPACE RECORD-CODE/GRAVITY CORRESPONDENCE as a named Prop (for every region: micro record
  entropy = one-loop conical entropy = area/4G_ind with G_ind the Sakharov constant of the SAME
  field content — one microscopic system computing both states and G); `finiteEvidence_holds`
  (DY1–DY6 bundled, every field a landed theorem); `continuumClaim` — NO proof field, NO axiom, NO
  instance (stated, never assumed).
  **DY7 CHECKPOINT (the two honest sentences, verbatim):** HAVE: "a finite, axiom-free diagonal
  code dynamics, explicit Gibbs/KMS states, product-mode reductions, and a saturated conditional
  induced-gravity cross-check whose proof does not use the trace/wEnt area calibration." HAVE NOT:
  "a finite proof of a continuum one-loop heat-kernel area law or an equality between finite
  thermal entropy at arbitrary β and an induced geometric area; that remains the named continuum
  frontier/conjecture." ⚠ NOT QG solved; no wall crossed.

- **THE DECOUPLING SHADOW, DS1 — `QIQTH/Decoupling/TruncatedCCR.lean`** (**[AF]** std-3;
  `THE_DECOUPLING_SHADOW_PLAN.md` — the finite forced core of the dictionary, from the Maldacena
  primary-source lesson: two sides as surviving descriptions of ONE parent under ONE limit;
  **DS1–DS7 COMPLETE**). **DS1 — bounded-sector CCR recovery** (the weak half of the decoupling
  argument, honest finite form): `lowering_matrixElement_stable` (ladder entries at fixed
  occupations are D-INDEPENDENT), `commutator_matrixElement_stabilizes` (`⟨m|[a_D,a_D†]|n⟩ = δ_mn`
  below the top — the defect invisible at bounded occupations), CAPSTONE
  **`commutator_eventually_exact`** (the `∀ᶠ D in atTop` form — the free-oscillator sector FORCED
  by the cutoff limit). ⚠ Forces neither the screen geometry nor G; NOT a full decoupling
  derivation. **DS2 LANDED — THE SINGLE-MODE GIBBS LIMITS** (QIQT-H's first genuine
  `Filter.Tendsto` theorems): `tendsto_Zgeom` (Z_D → 1/(1−q)), `tendsto_meanN` (⟨N⟩_D → q/(1−q) —
  the PLANCK value), CAPSTONE **`tendsto_defectExpect`** (the truncation-defect expectation
  D·q^{D−1}/Z_D → 0 at fixed βω > 0 — the state-level decoupling half), `ZMode_eq_Zgeom` (the
  bridge: the code's own thermal partition function IS the truncated geometric sum at q = e^{−βω}).
  Fixed positive temperature only. **DS3 LANDED — ENTROPY REGIMES + THE GUARD**:
  `tendsto_thermalEntropy_planck` (fixed x > 0: S_D → the free Planck oscillator entropy,
  `planck_form` = x/(e^x−1)), `tendsto_thermalEntropy_saturation` (fixed D: S_D → log D as x → 0⁺),
  CAPSTONES **`guard_entropy_saturates`** + **`guard_defect_survives`** — THE REGIME-SEPARATION
  GUARD: along ANY schedule x_D·D → 0 capacity saturates BUT the truncation-defect expectation
  tends to 1, NOT 0 — exact saturated capacity is provably NOT the positive-temperature
  free-oscillator limit (the two decoupling halves live in different regimes, as a THEOREM).
  **DS4 LANDED — THE FINITE-PRODUCT LIFTS**: `planckEntropy`/`productEntropy`, CAPSTONE
  **`tendsto_productEntropy`** (the product thermal entropy → the finite-mode free-field value
  along any all-modes-growing cutoff schedule), `tendsto_totalDefect` (the total defect dies),
  `tendsto_gibbsWeight_fixedOccupation` (every fixed occupation's Gibbs weight → the free-field
  Boltzmann weight — the state-level product decoupling). Finite mode sets only.
  **DS5 LANDED — REAL LOG-VALUATION RIGIDITY** (`QIQTH/Rigidity/LogValuationReal.lean`): the
  classical monotone-additive Cauchy rigidity done by hand — **`monotone_additive_eq_smul`**
  (monotone additive on ℝ is linear; ℚ-linearity + the rational squeeze), CAPSTONE
  **`monotone_logValuation`** (a monotone product-to-sum valuation on ℝ>0 is κ·log, κ ≥ 0 — the
  positive-real half of the forced weight dictionary). Next: DS6 (the finite-corner rigidity + the
  ν₂ counterexample). **DS6 LANDED — THE FORCED WEIGHT DICTIONARY**:
  **`finiteCorner_valuation_rigidity`** (a monoidal valuation monotone under ALL isometric
  embeddings is κ·log — the double-log squeeze), **`forced_weight_product`** (on product record
  corners A = κ·Σ log D_k — the keystone/join/embedding weight is RIGID under refinement
  naturality, no longer a constructed choice; κ is where 4G lives and stays input),
  **`nu2_counterexample`** (ν₂ is additive + divisibility-monotone but NOT ∝ log — the strong
  hypotheses are NECESSARY). **DS7 LANDED — CAMPAIGN COMPLETE** (`Decoupling/DecouplingShadow.lean`):
  `RefinementNaturalValuation` + **`.forced`** (package thm 2: THE FORCED WEIGHT κ·Σ log D_k),
  `FreeSectorEvidence` + **`decouplingShadow_holds`** (package thm 1: the free sector survives the
  cutoff limit — CCR stabilization, Planck occupation/entropy, defect death, THE GUARD — every
  field a landed theorem), **`saturated_entropy_eq_forced_area`** (package thm 3: the code's β = 0
  entropy = the forced area over κ; κ = the 4G slot, input).
  **DS7 CHECKPOINT (the two honest sentences, verbatim):** HAVE: "The capacity-limit theorem
  forces the oscillator/free-field sector only in the bounded-occupation or positive-temperature
  sense; it does not force the screen geometry or Newton constant." HAVE NOT: "The tower-rigidity
  theorem forces the logarithmic capacity weight only under monoidal, monotone refinement
  naturality; without those hypotheses there are explicit finite counterexamples." ⚠ NOT a full
  decoupling derivation (the join geometry, species match, and G remain parent data); NOT QG
  solved; no wall crossed.

- **THE TOWER, T1 — `QIQTH/Tower/AWFingerprint.lean`** (**[AF]** std-3; `THE_TOWER_PLAN.md` — the
  first machine-checked contact with the Type III₁ wall via the ITPFI/Araki–Woods route; the code
  tower's Gibbs product states ARE Araki–Woods input data; Fable-5 self-consult verified; T1–T8 in
  progress). **T1 — the AW data + fingerprint predicates + κ-bridge:** `gibbsEigen` (positive,
  normalized eigenvalue lists) with the UNIFORM weight bounds (`λ₀ > 1−e^{−a}` via
  `Z(1−q) = 1−q^D < 1`, `λ₁ > e^{−b}(1−e^{−a})`) and the EXACT ratio `λ₁/λ₀ = e^{−x}` (the Z
  cancels — never approximated); **`IsTailModularExponent`** + **`AWFingerprintIII1`** (the NAMED
  WITNESS PREDICATES, additive in κ — never the verbatim AW r∞; the tail quantifier and uniform δ
  are load-bearing, with the drifting-frequency and vanishing-weight counterexamples documented);
  the κ-bridge **`kappaOf_gibbsEigen`** (the fingerprint exponents ARE the held corner modular
  eigen-exponents, `= x(j−i)`) + `exp_kappaOf`. ⚠ Arithmetic about eigenvalue lists ONLY — no vN
  algebra, no ratio set of an algebra, no type classification constructed or claimed.
  **T2 LANDED — KRONECKER DENSITY**: **`dense_closure_pair`** — the additive subgroup of ℝ
  generated by two reals with irrational ratio is DENSE (`AddSubgroup.dense_or_cyclic`; the cyclic
  case forces a rational ratio). Classical arithmetic, no operator content — the engine of T3.
  **T3 LANDED — THE CENTERPIECE** (`Tower/Centerpiece.lean`):
  **`gibbsTower_awFingerprint_III₁`** — THE ARAKI–WOODS III₁ FINGERPRINT OF THE CODE'S GIBBS
  TOWER: two frequencies occurring infinitely often at irrational ratio (uniform bounds,
  D_k ≥ 2) ⟹ `AWFingerprintIII1` — an ARITHMETIC theorem about eigenvalue lists (T1's EXACT
  modular exponents feeding T2's Kronecker density); the operator reading rests on the three
  CITED facts (α)(β)(γ) — Araki–Woods 1968, Connes 1973 — never proved, no vN algebra
  constructed; **`gibbsTower_awFingerprint_III₁_sqrtTwo`** — the HYPOTHESIS-FREE alternating
  {√2, 1} qubit instance (`irrational_sqrt_two` — the vacuity guard). THE FIRST MACHINE-CHECKED
  CONTACT WITH THE TYPE III₁ WALL, at fingerprint level. **T4 LANDED — THE POWERS GUARD**
  (`Tower/PowersGuard.lean`): `tail_exponent_constant_mem` (constant frequency ⟹ every tail
  exponent ∈ sℤ — the fractional-part gap), CAPSTONE **`gibbsTower_constant_not_fingerprint`**
  (the constant tower FAILS the fingerprint — sℤ not dense). THE SEPARATION: with T3 the predicate
  holds for two-frequency irrational towers and provably fails for single-frequency towers —
  neither vacuous nor universal (the Powers III_{e^{−s}} reading cited, Powers 1967; no algebra
  type claimed). **T5 LANDED — THE INFINITE-MODE GIBBS MEASURE** (`Tower/GibbsLimit.lean`):
  `boltzMeasure` (single-mode Boltzmann, singleton = ofReal gibbsEigen),
  **`gibbsLimitMeasure := Measure.infinitePi`** — the σ-ADDITIVE probability measure on the
  infinite occupation-configuration space via the held product/Kolmogorov machinery
  (IsProjectiveLimit + uniqueness), CAPSTONE **`gibbsLimit_marginal_singleton`** — the finite
  marginals ARE the code's own DY Gibbs weights (`pMode_eq_gibbsEigen` closing the
  parametrizations via DS2). Classical (diagonal) limit object ONLY — no quantum state on the
  infinite system. **T6 LANDED — NON-ATOMICITY (the quantum reading is FALSE)**
  (`Tower/NonAtomic.lean`): `gibbsEigen_le_ceiling` (uniform ceiling 1/(1+e^{−b}) < 1),
  CAPSTONE **`gibbsLimitMeasure_singleton_eq_zero`** — the cylinder squeeze: under 0 ≤ βω_k ≤ b,
  D_k ≥ 2 EVERY singleton is null (depth-N cylinder mass ≤ c^N → 0), bundled as Mathlib
  **`NoAtoms`**. Hence no diagonal-density ("diagState") reading of the T5 limit exists — FALSE,
  not deferred; the vacuum-atom dichotomy (Σe^{−βω_k} < ∞ ⟹ atom) cited only. **T7 LANDED —
  THE FINITE OPERATOR TOWER** (`Tower/CornerEmbed.lean`): **`cornerEmbed`** (C ⊆ C′) is a unital
  ⋆-homomorphism (one/mul/star/add/smul), mode-compatible (`cornerEmbed_modeOp`),
  state-compatible (`cornerEmbed_stateOf` = DY4's Gibbs marginal in operator form) and
  MODULAR-FLOW EQUIVARIANT (CAPSTONE **`cornerEmbed_sigmaDiag`**: σ_s^{C′}∘ι = ι∘σ_s^C via the
  kappaOf eigen-law `kappaOf_gibbsWeight_of_sameOffSub`) — the state-compatible
  modular-equivariant refinement tower = the ITPFI tower DATA, as a family of finite-dimensional
  maps only (no limit algebra, no type claim). **T8 — CAMPAIGN COMPLETE (8/8)**
  (`Tower/Checkpoint.lean`). CHECKPOINT (verbatim): HAVE "the machine-checked arithmetic content
  of the Araki–Woods III₁ criterion for the code's Gibbs tower, including a hypothesis-free
  concrete instance, the Powers-guard separation, the σ-additive infinite-mode Gibbs measure
  with its non-atomicity, and the state-compatible modular-equivariant finite refinement tower;
  the inference to an actual III₁ factor is cited (Araki–Woods 1968; Connes 1973), never
  proved." HAVE NOT "the ITPFI von Neumann algebra, its ratio set, its type, any inductive limit
  or weak closure, any quantum state on the infinite system, or any continuum-limit completion —
  none are constructed or classified here.

- **THE CLOSURE, C1 — `QIQTH/VonNeumann/InvariantProjection.lean`** (**[AF]** std-3;
  `THE_CLOSURE_PLAN.md` — the von Neumann bicommutant/density campaign, the convergent blocker of
  the continuum program). `orbitSubmodule`/`orbitClosure` (cyclic subspaces with the orthogonal
  projection instance attached); **`starProjection_mem_centralizer`** — the star projection onto a
  closed A-invariant subspace lies in the commutant A′ for a unital ⋆-subalgebra A ⊆ B(H)
  (⋆-closure is load-bearing — upper-triangular counterexample documented). The elementary engine
  of the double-commutant theorem; no density or bicommutant statement yet. **C2 LANDED —
  `QIQTH/VonNeumann/GeneratedBy.lean`** (**[AF]** std-3): **`VonNeumannAlgebra.generatedBy S :=
  (S ∪ S*)″`** — the von Neumann algebra generated by a set, packaged as a genuine Mathlib
  `VonNeumannAlgebra` (bicommutant field from X‴ = X′), with generators-subset, MINIMALITY
  (`generatedBy_le`), the star-closed collapse, and the Galois lemma **`centralizer_adjoin`**
  ((adjoin ℂ S)′ = (S ∪ S*)′, pair-trick induction). The project can now NAME its limit algebras;
  purely algebraic — density is C7. **C3 LANDED — `QIQTH/VonNeumann/DensityOne.lean`**
  (**[AF]** std-3): SINGLE-VECTOR DENSITY **`bicommutant_apply_mem_orbitClosure`** — an element
  of the double centralizer maps every vector into that vector's closed orbit (unitality
  load-bearing, A = {0} counterexample documented), with the ε-approximation form. **C4 LANDED — THE RISK
  LUMP CLEARED** (`QIQTH/VonNeumann/Amplification.lean`, **[AF]** std-3): the frozen PiLp
  amplification interface — coordinate inclusions/projections with **adjoint ι = π**, the
  coordinate decomposition Σ ι∘π = 1, the diagonal embedding with its algebra + ⋆-law
  (`star_diagCLM`), entrywise extensionality (`clm_ext_of_entries`), coordinate norm bound.
  Pure finite Hilbert-sum operator API. **C5 LANDED** (`QIQTH/VonNeumann/MatrixCommutant.lean`,
  **[AF]** std-3): the two minimal matrix-commutant lemmas — ENTRIES (S ∈ (diag A)′ ⟹ entries
  π i ∘ S ∘ ι j ∈ A′) and ASSEMBLY (T ∈ A″ + entries in A′ ⟹ diag T commutes) — plus
  diagHom/diagAlg and CAPSTONE **`diag_mem_bicommutant`** (T ∈ A″ ⟹ diag T ∈ (diag A)″), the
  amplification of the bicommutant. **C6 LANDED** (`QIQTH/VonNeumann/DensityN.lean`, **[AF]**
  std-3): N-VECTOR DENSITY **`bicommutant_sotApprox`** — a bicommutant element is
  norm-approximable by ONE algebra element uniformly over any finite vector tuple (the full
  quantifier content of the density half of the double-commutant theorem). **C7 LANDED — THE
  CENTERPIECE (green first try)** (`QIQTH/VonNeumann/Bicommutant.lean`, **[AF]** std-3): ★ **THE
  VON NEUMANN DOUBLE-COMMUTANT THEOREM** ★ — **`vonNeumann_double_commutant`** /
  **`mem_centralizer_centralizer_iff_sotApprox`**: for a unital ⋆-subalgebra A ⊆ B(H), the
  double centralizer A″ EQUALS the set of operators SOT-approximable from A (the concrete
  `SOTApprox` predicate; converse via the ![x, Sx] tuple), plus idempotence and
  **`generatedBy_carrier_eq`** (generated vN algebra = SOT closure of the generated ⋆-algebra).
  A genuine Mathlib gap closed (Mathlib's `VonNeumannAlgebra` has no bicommutant theorem);
  the file is Mathlib-styleable. **C8 LANDED (green first try)**
  (`QIQTH/VonNeumann/CrossedProductClosure.lean`, **[AF]** std-3): **`crossedProductVN`** — the
  crossed product M⋊_σℝ packaged as a genuine `VonNeumannAlgebra` on L²(ℝ;H) (generated by
  matterRep ∪ clockTransl), with membership lemmas + the SOT-approximability carrier
  characterization. PACKAGING ONLY — the dual-weight trace is NOT claimed to extend to the
  closure (`DualWeightTraceExtension` stays the carried frontier). **C9 LANDED (green first try)**
  (`QIQTH/VonNeumann/DirectedUnionVN.lean`, **[AF]** std-3): **`limitVN`** — the directed-union
  limit von Neumann algebra (`unionStarSubalgebra` + `generatedBy`), with stage inclusions and
  the SOT-approximability membership characterization (`mem_limitVN_iff`). The refinement-tower
  limit in its HONEST form: for any hypothesized common representation on one B(H) — the
  DiamondAlg tower's own instantiation awaits the deferred tower-GNS campaign; no ITPFI factor
  constructed. **C10 LANDED — STRETCH SHIPPED (cut not needed)**
  (`QIQTH/VonNeumann/WOTClosure.lean`, **[AF]** std-3):
  **`wotClosure_image_eq_image_bicommutant`** — the WOT closure IS the bicommutant (in Mathlib's
  `H →WOT[ℂ] H` copy, about ofCLM images): with C7, **WOT closure = SOT closure = A″** — the
  full classical double-commutant statement, machine-checked. **C11 — CAMPAIGN COMPLETE
  (11/11, the C10 stretch INCLUDED)** (`VonNeumann/Checkpoint.lean`). CHECKPOINT (verbatim):
  HAVE "We have the von Neumann double-commutant theorem as an axiom-free Lean theorem over
  current Mathlib — for every unital ⋆-subalgebra A of the bounded operators on a complex
  Hilbert space, the double centralizer A″ equals the set of operators approximable from A in
  norm on every finite tuple of vectors (and, in the shipped WOT increment, the weak-operator
  closure) — packaged as `VonNeumannAlgebra.generatedBy` with membership lemmas, and
  instantiated to present the project's crossed-product representation and any
  commonly-represented refinement tower as genuine `VonNeumannAlgebra`s." HAVE-NOT "We do not
  have Kaplansky density, normal states, preduals or the σ-weak topology, type classification,
  or the inductive-limit (tower-GNS) Hilbert space — the ITPFI tower's limit algebra is packaged
  only relative to a hypothesized common representation, and the crossed-product dual-weight
  trace is not claimed to extend from the algebraic core to the weak closure.

- **THE REPRESENTATION, R1 — `QIQTH/TowerGNS/EmbedTrans.lean`** (**[AF]** std-3;
  `THE_REPRESENTATION_PLAN.md` — the tower-GNS campaign: the T5/T7 corner tower on ONE Hilbert
  space, towards `towerLimitVN`). Tower FUNCTORIALITY: **`cornerEmbed_trans`** (embeddings
  compose along C ⊆ C′ ⊆ C″) via **`sameOffSub_split`** + `restrictMicro_trans`; the linear
  bundling `cornerEmbedₗ` + sub/zero. The one missing T7 lemma; pure finite combinatorics.
  **R2 LANDED** (`TowerGNS/StageInner.lean`, **[AF]** std-3): the per-stage GNS form
  **`gnsInner K x y = φ_K(xᴴy)`** — conjugate symmetry, POSITIVITY (0 ≤ ⟪x,x⟫ via the trace
  cycle + PSD conjugation), slot linearity; **`pairInner`** (the stabilized pairing at C ⊔ C′)
  with CAPSTONE **`pairInner_embed`** — the pairing is STAGE-STABLE (any common upper stage
  agrees: R1 functoriality + ⋆/mul + T7 state compatibility). **R3 LANDED — THE PRE-HILBERT
  SPACE** (`TowerGNS/PreSpace.lean`, **[AF]** std-3): **`TowerPre := ⨁ (C : Finset M),
  DiamondAlg L C`** with the semidefinite stabilized pairing (the degeneracy IS the direct-limit
  gluing — no quotient), stage collapse + **`rawInner_eq_collapse`**, positivity, the
  `PreInnerProductSpace.Core` → seminormed → `InnerProductSpace` chain in the GNS-file order,
  and **`TowerGNS := UniformSpace.Completion (TowerPre …)`** — the Hilbert space of the tower.
  **R4 LANDED — THE GERM IDENTITY** (`TowerGNS/Germ.lean`, **[AF]** std-3): **`towerGerm`** —
  in the completion, ↑(of C′ (ι a)) = ↑(of C a) (the difference is a null vector; the metric
  completion identifies it — the direct-limit gluing with no quotient); the cyclic vector
  **Ω := ↑(of ∅ 1)** with ⟪Ω,Ω⟫ = 1 (DY2 normalization) and ‖Ω‖ = 1. The compatibility engine
  for the representation (R7). **R5 LANDED — THE GNS BOUND** (`TowerGNS/StageBound.lean`,
  **[AF]** std-3): `frobNormSq` (Frobenius constant), **`frobBound`** (c(a)•1 − aᴴa PSD via
  rowwise Cauchy–Schwarz), **`cornerEmbed_posSemidef`** (PSD transport through the ⋆-hom),
  CAPSTONE **`gnsInner_leftMul_le`** — the GNS boundedness inequality re ⟪ιa·x, ιa·x⟫ ≤
  c(a)·re ⟪x,x⟫ (Frobenius bound, NOT the C*-norm — π bounded, never claimed contractive).
  **R6 LANDED** (`TowerGNS/LeftMul.lean`, **[AF]** std-3): the bounded pre-operator —
  `leftMulRaw` (left multiplication after embedding, per component), **`collapse_leftMul`**
  (the stage collapse intertwines), the norm bound **‖T_a x‖ ≤ √c(a)·‖x‖**, and
  **`towerLeftMul`** via `LinearMap.mkContinuous`. **R7 LANDED — THE ⋆-REPRESENTATION**
  (`TowerGNS/Representation.lean`, **[AF]** std-3): **`towerRep C₀ : DiamondAlg L C₀ →⋆ₐ[ℂ]
  (TowerGNS →L TowerGNS)`** — every corner algebra acts on the ONE Hilbert space as a unital
  ⋆-algebra homomorphism (laws in the completion via the germ; star via the adjoint relation),
  with CAPSTONE **`towerRep_cornerEmbed`** (π_{C′} ∘ cornerEmbed = π_C — the tower acts
  coherently through every stage). **R8 LANDED** (`TowerGNS/CyclicVector.lean`, **[AF]** std-3):
  **`towerRep_inner_cyclicVec`** — ⟪Ω, π_C(a)Ω⟫ = φ_C(a): every corner Gibbs state IS the
  vector state of the unit cyclic vector Ω; **`dense_span_towerRep_cyclicVec`** — Ω is CYCLIC
  (the orbit span is dense). Ω not claimed separating. **R9 — CAMPAIGN COMPLETE (9/9)** (`TowerGNS/LimitVN.lean` +
  `Checkpoint.lean`, **[AF]** std-3): ★ **`towerLimitVN`** ★ — the GENUINE directed-union limit
  von Neumann algebra of the code tower on TowerGNS (`limitVN` of the towerRep ranges, monotone
  via towerRep_cornerEmbed), with **`mem_towerLimitVN_iff`** (SOT-approximation from the finite
  stages) and the ℕ-instantiation **`freqTowerLimitVN`** (the QIQT frequency tower). CHECKPOINT
  (verbatim): HAVE "One Hilbert space — the completion of the semidefinite Gibbs-GNS pre-space
  on the direct sum of all finite corners — carrying compatible unital ⋆-representations of
  every corner algebra (π_{C′} ∘ cornerEmbed = π_C for all C ⊆ C′), a unit cyclic vector Ω
  implementing every corner Gibbs state as a vector state (⟪Ω, π_C(a)Ω⟫ = φ_C(a)), and the
  directed-union limit von Neumann algebra towerLimitVN = limitVN of the representation images,
  with membership characterized by SOT-approximation from the finite stages — all axiom-free."
  HAVE NOT "The type of towerLimitVN is not classified — no factor, no ITPFI identification, no
  III₁ claim is made or proved (the T3 fingerprint stays arithmetic; Araki–Woods 1968 and Connes
  1973 stay cited, never invoked); Ω is not shown separating, the modular theory of the limit
  state on the completion is not constructed, and the representations are not shown isometric.

- **THE TRANSPORT+ACCOUNTING, B1 — `QIQTH/TowerGNS/FlowPre.lean`** (**[AF]** std-3;
  `THE_TRANSPORT_AND_ACCOUNTING_PLAN.md`): the per-corner Gibbs modular flow `cornerFlow` with
  its full ⋆-automorphism + state-invariance law kit, all through the rescale bridge (no
  cpow/diagPow anywhere); CAPSTONE **`gnsInner_cornerFlow`** (the GNS form is flow-invariant) +
  **`cornerFlow_cornerEmbed`**. **B2 LANDED**: `flowRaw` (componentwise,
  same-stage) with CAPSTONE **`rawInner_flowRaw`** — the flow is an ISOMETRY of the pre-space —
  and `flowPre` (mkContinuous, ‖U_t x‖ = ‖x‖). **B3+B4 LANDED** (`TowerGNS/Flow.lean`):
  **`towerFlow`** — THE ONE-PARAMETER UNITARY GROUP on TowerGNS (U_0 = 1, group law, U_t† =
  U_{−t}, `towerFlow_mem_unitary`), **U_tΩ = Ω**, the Ω vector state conjugation-invariant, and
  **`towerState_kms_boundary`** (the finite-stage boundary KMS identity displayed on the limit
  space — NOT strip analyticity, NOT a KMS state of the limit algebra). **B5+B6 LANDED**
  (`TowerGNS/FlowCovariance.lean`): THE IMPLEMENTATION THEOREM **`towerFlow_conj_towerRep`**
  (U_t π_C(a) U_{−t} = π_C(σ_t a); covariance EXACT at pre-level, no germ) and CAPSTONE
  **`towerLimitVN_flow_invariant`** — the limit von Neumann algebra is INVARIANT under its
  transported dynamics (SOTApprox.conj + stages-onto-stages). towerLimitVN has its dynamics.
  **A1 LANDED**
  (`Rigidity/RegulatorRigidity.lean`): THE REGULATOR RIGIDITY THEOREM —
  **`speciesRegulator_forced`**: the Sakharov/Dvali FORM 1/G = N_eff·Λ² is FORCED for any
  positive, monotone, shared-covariance species family (κ an OUTPUT via DS5's log-valuation
  rigidity; ONE dimensional calibration pins κ = 2), with the dyadic counterexample showing
  weakened covariance breaks it and the non-vacuity instance = the held `inducedInvG` by rfl.
  The c_i numbers stay CITED Seeley–DeWitt data. **A2 LANDED** (`HeatKernelOneD.lean`):
  **`heatDensity_oneD`** — the FIRST DERIVED (not cited) heat-kernel-type coefficient in the
  repository ((1/2π)∫e^{−tk²} = 1/√(4πt), from Mathlib's Gaussian integral), plus
  `cutoff_moment`/`inducedInvG_as_integral` (the held Λ² as a derived momentum integral).
  1D/free/Gaussian; the 4D c_i stay cited. **A3 LANDED — TRACK A COMPLETE**
  (`SpeciesCrossCheck.lean`): **`species_sakharov_ratio`** (the mixed-field-content 1/4 — the
  ENTIRE species sum cancels) + CAPSTONE **`speciesEntropy_eq_capacity`** (S_ent = A/(4G), ONE
  shared species datum feeding both bookkeepings) + the BTZ chain. A CONSISTENCY chain over one
  shared cited datum — NOT an independent cross-check; the c_i stay cited Seeley–DeWitt data.
  Track A checkpoint sentences verbatim in the file. **B7 LANDED — STRETCH SHIPPED**
  (`TowerGNS/FlowContinuity.lean`): CAPSTONE **`continuous_towerFlow_apply`** — the transported
  flow is a STRONGLY CONTINUOUS one-parameter unitary group on TowerGNS (ε/3 + density + the
  uniform isometry; the difference-norm in collapsed closed form; no cpow). The door to the held
  Spectral/Stone tower is open; the generator is NOT claimed. **B8/A4 — CAMPAIGN COMPLETE (11/11)**: the Track B
  HAVE/HAVE-NOT stanza verbatim in `TowerGNS/Checkpoint.lean` (HAVE: the transported flow as a
  one-parameter unitary group — U_0 = 1, group law, U_t* = U_{−t}, U_tΩ = Ω, the implementation
  theorem, towerLimitVN invariance, all axiom-free; PLUS strong continuity, the B7 stretch
  shipped. HAVE NOT: no Tomita Δ/J, Ω not shown separating, no strip KMS — only the finite-stage
  boundary identity — no Stone generator, no type classified; U_t defined by TRANSPORT). Track A
  sentences verbatim in `SpeciesCrossCheck.lean`. Both tracks complete.

- **THE GENERATOR, G1+G2 — `QIQTH/TowerGNS/Generator.lean`** (**[AF]** std-3;
  `THE_GENERATOR_PLAN.md`): **`towerGen := stoneGen (towerFlow)`** — the SELF-ADJOINT UNBOUNDED
  GENERATOR of the tower's transported modular dynamics (`towerGen_isSelfAdjoint`, the
  five-argument instantiation of the held Stone theorem — two adapters only); THE ZERO-MODE
  **`towerGen_cyclicVec`** (Ω ∈ dom(K), KΩ = 0). NOT log Δ / NOT a Tomita modular Hamiltonian
  (verbatim docstring); no PVM of the unbounded K; no exp-recovery (the wall open by design).
  **G3 LANDED — THE EXPLICIT CORE**: CAPSTONE
  **`towerGen_of`** — towerGen ↑(of C a) = ↑(of C ([H_C, a])) with H_C = diagonal(log
  gibbsWeight) (`cornerGenMatrix_eq_commutator`): THE GENERATOR IS COMPUTED on every pure
  component, every coerced pre-vector is in the domain, and **`dense_stoneDomain`** holds
  CONSTRUCTIVELY (no Gårding mollification). **G4+G6 — CAMPAIGN COMPLETE**: `towerGen_comm_towerFlow` (K U_s = U_s K; the domain
  flow-invariant). CHECKPOINT (verbatim, in `TowerGNS/Checkpoint.lean`): HAVE — the self-adjoint
  unbounded generator (five held Track-B facts instantiating the held Stone theorem); the
  zero-mode (Ω ∈ dom, KΩ = 0); the explicit dense core (towerGen ↑(of C a) = ↑(of C ([H_C, a])),
  H_C = diagonal(log gibbsWeight), density constructive); flow covariance. HAVE NOT — towerGen
  is NOT log Δ / NOT a Tomita modular Hamiltonian; no Δ/J/S, no separating property, no
  KMS-at-the-limit, no type; no PVM of the unbounded towerGen; no exp-recovery (the recovery
  wall open by design).

- **THE SEPARATION, S1+S2 — `QIQTH/TowerGNS/RightMul.lean`** (**[AF]** std-3;
  `THE_SEPARATION_PLAN.md` — towards Ω cyclic AND separating): the weight-exchange identity
  (T7's kappaOf lemma exponentiated), the √ρ infrastructure, THE ENGINE
  **`cornerEmbed_mul_sqrtGibbs`** (the half-power intertwining), and CAPSTONE
  **`gnsInner_rightMul_le`** — right multiplication by a corner element is BOUNDED with the
  weighted Frobenius constant Σ‖a n m‖²(w_m/w_n) (never claimed contractive). **S3+S4 LANDED**: `rightMulRaw`/`towerRightMul`/
  **`towerRightMulCLM`** (the bounded right action on TowerGNS, norm ≤ √(weighted Frobenius));
  CAPSTONE **`towerRightMul_cyclicVec`** — R_aΩ = ↑(of C a) = π_C(a)Ω: the right orbit of Ω IS
  the left orbit. **S5–S8 — CAMPAIGN COMPLETE (8/8)**
  (`TowerGNS/Separation.lean`): ★ **Ω IS CYCLIC AND SEPARATING FOR towerLimitVN** ★ — CAPSTONE
  **`towerCyclicVec_separating`** (T ∈ towerLimitVN, TΩ = 0 ⟹ T = 0; via the deep-stage
  left-right exchange, the pure-bicommutant `commute_of_mem_limitVN`, and ext_on over R8's
  density) + Ω cyclic for the limit + `towerLimitVN_eq_of_apply_cyclicVec` — THE STANDARD-FORM
  HYPOTHESIS PAIR of Tomita–Takesaki theory, axiom-free. CHECKPOINT (verbatim in
  Checkpoint.lean): HAVE the pair + the bounded right action in the commutant; HAVE NOT — no
  Tomita S₀/Δ/J, no KMS-at-limit, no type: separation is the HYPOTHESIS for that theory, not
  the theory; the right action never claimed contractive, no ⋆-anti-representation laws.

- **THE TOMITA OPERATOR, T0_1–T0_3 — `QIQTH/TowerGNS/Tomita.lean`** (**[AF]** std-3;
  `THE_TOMITA_PLAN.md`): **`towerTomita₀ : TowerGNS →ₛₗ.[starRingEnd ℂ] TowerGNS`** — the
  Tomita operator S₀ on its classical orbit domain (a DENSE submodule), as a genuine
  conjugate-linear (semilinear) LinearPMap: well-defined BY SEPARATION, S₀Ω = Ω, the computed
  core **S₀ ↑(of C a) = ↑(of C aᴴ)**, involutive, and **CLOSABLE in the sequence sense**
  (TₙΩ → 0 ∧ Tₙ*Ω → v ⟹ v = 0 — via the commutant-side right multiplications). The
  closure/Δ/J/KMS/type NOT constructed or claimed. **T0_4+T0_5 LANDED**: CAPSTONE
  **`towerRightMulCLM_adjoint`** (adjoint R_a = R_{(rightConj² a)ᴴ}) with the modAut bridge —
  **the adjoint parameter IS the finite σ₋ᵢ image of aᴴ, COMPUTED** (not analytically
  continued); **`tomita_adjoint_pairing`** — the classical ⟪T*Ω, R_aΩ⟫ = ⟪R_a†Ω, TΩ⟫ on the
  dense pure-component family. **T0_6 — CAMPAIGN COMPLETE (6/6)**. CHECKPOINT
  (verbatim in Checkpoint.lean): HAVE — S₀ on its classical orbit domain: well-defined (Ω
  separating), conjugate-linear, involutive, densely defined; the computed core S₀ ↑(of C a) =
  ↑(of C aᴴ); the commutant adjoints R_a† = R_{ρaᴴρ⁻¹} (the finite σ₋ᵢ, COMPUTED); the
  classical pairing on a dense family; closable in the graph-limit sense. HAVE NOT — the
  closure S̄ not constructed as an object (Mathlib's LinearPMap closure/adjoint theories are
  id-only; a conjugate-linear closure theory is not built here); no polar decomposition, no Δ,
  no J, no KMS of the limit state, no type.

- **THE CONJUGATE CLOSURE, CC1–CC4 — `QIQTH/TowerGNS/ConjClosure.lean`** (**[AF]** std-3,
  ABSTRACT — Mathlib-only imports; `THE_CONJUGATE_CLOSURE_PLAN.md`): the four new theorems of
  the σ-semilinear closure theory via the ℝ-reduction — **`realRestrict`** (the ℝ-view of a
  conjugate-linear partial map; no Mathlib helper existed), **`isClosable_of_seq`** (the
  sequence-closability bridge — absent from Mathlib even for id), **`ConjHomogeneous.closure`**
  and **`GraphSymm.closure`** (conjugate-homogeneity and the involution survive closure — the
  twisted-map and swap-homeomorphism engines; NO adjoint anywhere). **CC5 LANDED — S̄ AS AN OBJECT**
  (`TowerGNS/TomitaBar.lean`): **`towerTomitaBar`** — the closure of the Tomita operator:
  CLOSED, extends S₀ with the orbit domain a CORE, S̄Ω = Ω, S̄↑(of C a) = ↑(of C aᴴ), dense
  domain, conjugate-homogeneous (twist-guarded), FULLY INVOLUTIVE with ker = ⊥ and range =
  domain. **CC7 — CAMPAIGN COMPLETE** (CC6 semilinear
  re-bundle CUT, pre-authorized non-necessity). CHECKPOINT (verbatim in Checkpoint.lean): HAVE —
  S̄ as an object with the four new abstract theorems (the ℝ-restriction view, the
  sequence-closability bridge — new to Mathlib even for id — and the two transfer theorems);
  closed, orbit-core, Ω-fixing, conjugate-transpose on the core, twist-guarded, fully involutive,
  ker = ⊥, range = domain; no real inner product, no adjoint anywhere. HAVE NOT — Δ/J/polar not
  constructed (the Δ contract is the named next campaign); no σ-semilinear graph theory (the
  ℝ-reduction sidesteps it — the σ-graph stays Mathlib's open TODO); no KMS-at-limit, no type.

- **THE MODULAR OPERATOR, M1+M2 — `QIQTH/TowerGNS/ConjAdjoint.lean`** (**[AF]** std-3,
  ABSTRACT; `THE_MODULAR_OPERATOR_PLAN.md`): the ∃-Riesz CONJUGATE-LINEAR ADJOINT —
  `conjAdjointDom` (witness domain, twist derived) + **`conjAdjoint g hd : E →ₛₗ.[starRingEnd ℂ]
  E`** (uniqueness by density; one spec lemma; NO toDual, NO CLM extension, NO boundedness
  predicate, NO completeness) + sequence-form closedness + the equalizer core-extension lemma.
  **M3 LANDED** (`ModularOp.lean`): **`towerTomitaF`**
  — Tomita's F at the tower: the pairing pushed from the orbit core to all of dom S̄ by the
  equalizer; F COMPUTED on pure components (F↑(of C b) = ↑(of C ((rightConj² b)ᴴ))); FΩ = Ω;
  dense domain; twist-guarded. **M4+M5 LANDED — THE HEADLINE**: **`towerModularOp`
  — Δ := F∘S̄, ℂ-linear**, SYMMETRIC (IsFormalAdjoint Δ Δ), POSITIVE (⟪Δx,x⟫ = ‖S̄x‖² ≥ 0),
  ΔΩ = Ω, dense domain — and ★ **Δ↑(of C a) = ↑(of C (modAut ρ_C a))** ★: the modular operator
  of the tower limit state ACTS AS THE FINITE MODULAR AUTOMORPHISM on the pure-component core —
  the modular operator of the physics, computed. **M6+M7 — CAMPAIGN COMPLETE (7/7)**: Δ ≤ Δ†, Δ†
  closed, Δ IsClosable (the Mathlib hookup). CHECKPOINT (verbatim in Checkpoint.lean): HAVE —
  Tomita's F on the ∃-Riesz domain (no real inner product, no dual machinery, no completeness)
  and Δ := F∘S̄: ℂ-linear, SYMMETRIC, POSITIVE (⟪Δx,x⟫ = ‖S̄x‖²), CLOSABLE, ΔΩ = Ω, and
  COMPUTED — Δ↑(of C a) = ↑(of C (modAut ρ_C a)), the modular operator of the physics. HAVE
  NOT — Δ† = Δ (von Neumann's S̄*S̄ theorem, absent from Mathlib — the named next target); no
  J/polar/Δ^{1/2}/Δ^{it}; no KMS-at-limit; no type.

**THE VON NEUMANN CAMPAIGN (ACTIVE, THE_VON_NEUMANN_PLAN.md)** — Δ† = Δ (von Neumann's S̄*S̄
  theorem, absent from Mathlib). **VN1 LANDED**: `QIQTH/VonNeumann/SelfAdjointCriterion.lean` —
  `isSelfAdjoint_of_isFormalAdjoint_of_one_add_surjective`: densely defined + symmetric +
  ran(1+A) = ⊤ ⟹ IsSelfAdjoint A, over any RCLike field, Mathlib-only imports (a reusable
  Mathlib-gap kernel; green first try). **VN2 LANDED**: `GraphDecomposition.lean` —
  `exists_pairing_of_isClosed`: for closed T and any h, ∃ x ∈ dom T with ⟪a, h−x⟫ = ⟪Ta, Tx⟫
  ∀ a ∈ dom T — the von Neumann graph orthogonal decomposition in WithLp 2 (E×E),
  RCLike-generic, no adjoint anywhere (green first try). **VN4 LANDED**: `ModularSurjective.lean` —
  the ConjHomogeneous i-twist (`conj_pairing_of_re_pairing`: re-pairing ⟹ full ℂ-pairing) and
  ★ `towerModularOp_one_add_surjective`: **ran(1+Δ) = ⊤** — VN2 at ℝ on the closed S̄, the
  real orthogonality upgraded by the i-twist to the ∃-Riesz F-domain membership verbatim
  (green first try; the rclikeToReal letI trap never bit). **VN5 LANDED — ★ Δ† = Δ ★**:
  `ModularSelfAdjoint.lean` — `towerModularOp_isSelfAdjoint`: the tower modular operator is
  GENUINELY SELF-ADJOINT (Mathlib LinearPMap.adjoint sense; VN1 kernel at ℂ + the VN4 range
  condition), with adjoint_eq, closed, closure = self, trivial kernel, and the resolvent
  bound ‖x‖ ≤ ‖x + Δx‖ (green first try). **VN3 LANDED**: `AdjointComp.lean` — the standalone
  VON NEUMANN THEOREM: `vonNeumann_isSelfAdjoint` — for closed densely defined T over any
  RCLike field, T†T (two-layer domain) is densely defined AND self-adjoint; with
  `vonNeumann_dense_domain` and `adjointComp_one_add_surjective` (green first try; the whole
  campaign is four consecutive one-shots). **VN6 — CAMPAIGN COMPLETE (6/6, one session,
  four first-try-green increments)**. CHECKPOINT (verbatim in Checkpoint.lean): HAVE — Δ of
  the tower limit state is genuinely SELF-ADJOINT (Mathlib adjoint sense), positive, closed,
  densely defined, ΔΩ = Ω, acting as the finite modular automorphism on the core, with
  ran(1+Δ) = ⊤; plus the abstract Mathlib-absent von Neumann theorem (T†T self-adjoint, any
  RCLike field). HAVE NOT — no Δ^{1/2}/J/polar; no spectral resolution of unbounded Δ; no
  Δ^{it}/KMS-at-limit (and NO claim towerGen = log Δ); no Tomita theorem at the algebra
  level; no type. CONSUMER CONTRACT: (1+Δ)⁻¹ CLM contraction → PVM_of_selfAdjoint →
  boundedFC ((1−r)/r)^{it} → Δ^{it} = the next campaign.

**THE RESOLVENT CAMPAIGN (ACTIVE, THE_RESOLVENT_PLAN.md)** — (1+Δ)⁻¹ and Δ^{it}.
  **R1 LANDED**: `TowerGNS/Resolvent.lean` — towerResolvent = (1+Δ)⁻¹ as an
  everywhere-defined CLM contraction with the full API (Rh + Δ(Rh) = h, R(x+Δx) = x,
  Δ∘R = 1−R, injective, dense range = dom Δ, ‖Rh‖ ≤ ‖h‖); green first try. **R2 LANDED**: `ResolventOrder.lean` — R is
  self-adjoint, positive with 0 ≤ R ≤ 1 (Loewner), ‖R‖ ≤ 1, spectrum ⊆ [0,1], RΩ = ½Ω
  (green first try). **R3 LANDED IN FULL**: `Spectral/PVMEigen.lean` —
  the abstract PVM eigenvector/atom calculus: E finite additivity/complement; the generic
  T = borelFC T (coord) (operator-level spectral theorem); THE KERNEL ATOM (Injective T ⟹
  E(val⁻¹{0}) = 0); eigenvector localization + E({r})x = x + capstone
  borelFC_apply_eigenvector (f(T)x = f(r)•x). **R4 LANDED**: `TowerGNS/ModularUnitary.lean` —
  towerModUnitary t := borelFC of the junk-value-1 piecewise ((1−r)/r)^{it} on the
  resolvent: U0 = 1, U(s+t) = UsUt, adjoint = U(−t), unitary, isometric, cocycle inner
  identity (green first try; NO claim U = towerFlow). **R5 LANDED**: `ModularUnitaryCont.lean` —
  Δ^{it} is STRONGLY CONTINUOUS, fixes Ω (U_tΩ = Ω via the eigenvector calculus at
  RΩ = ½Ω), and E({0}) = 0 (the kernel atom) — a genuine strongly continuous one-parameter
  unitary group with the honesty pair (green first try; still NO claim U = towerFlow).
  **R6 LANDED**: `ModularUnitaryComm.lean` — R =
  borelFC(coord); U_t commutes with R; U_t preserves dom Δ; Δ(U_t x) = U_t(Δx) on the whole
  domain — the spectral flow is consistent with the modular operator (green first try).
  **R7 — CAMPAIGN COMPLETE (7/7 core, ALL
  first-try-green)**. CHECKPOINT (verbatim in Checkpoint.lean): HAVE — towerResolvent =
  (1+Δ)⁻¹ self-adjoint contraction, 0 ≤ R ≤ 1, trivial kernel, dense range = dom Δ,
  spectrum ⊆ [0,1], RΩ = ½Ω, Δ∘R = 1−R; and **Δ^{it} := towerModUnitary — a strongly
  continuous one-parameter unitary group** (U0 = 1, U(s+t) = UsUt, U⋆ = U(−t)) fixing Ω,
  commuting with R and Δ (preserving dom Δ), E({0}) = 0; plus the abstract PVM supplement
  (T = ∫λ dE, kernel atom, eigenvector calculus). HAVE NOT — NO claim towerModUnitary =
  towerFlow (towerGen = log Δ — the exponential-recovery wall, the named next campaign); no
  KMS-at-limit; no Tomita theorem (U_t not shown to implement automorphisms of
  towerLimitVN); no Δ^{1/2}/J/polar; no type.

**THE IDENTIFICATION CAMPAIGN (ACTIVE, THE_IDENTIFICATION_PLAN.md)** — towerFlow = Δ^{it}
  via the eigenvector route (ρ diagonal by construction ⟹ matrix units are simultaneous
  eigenvectors of modAut/cornerFlow/Δ/R/U_t; dense-span extension). **ID1 LANDED**:
  `ModularEigenbasis.lean` — modAut ρ (single n m c) = (w_n/w_m)•single n m c (the finite
  modular eigenbasis) + the towerFlow pure-component sum identity extracted (green first
  try). **ID2 LANDED**: `ModularEigenvectors.lean` —
  pure matrix-unit components are eigenvectors of Δ (eigenvalue w_n/w_m) and R (eigenvalue
  (1+w_n/w_m)⁻¹), with the general transport Δx = δ•x ⟹ Rx = (1+δ)⁻¹•x (green first try).
  **ID3 LANDED**: `ModularUnitaryEigen.lean` — U_t acts
  diagonally on the eigenbasis (exp(I·t·log δ) on Δ-eigenvectors; on matrix-unit components
  the scalar matches cornerFlow_single character-for-character; green first try). **ID4 LANDED — ★★ THE EXPONENTIAL-RECOVERY
  WALL IS CROSSED ★★**: `Identification.lean` — towerModUnitary_eq_towerFlow (the
  transported physical flow IS the spectral modular flow of Δ, as operators) +
  towerGen = stoneGen(Δ^{it}) (green first try). **ID5 — CAMPAIGN COMPLETE (5/5, ALL
  first-try green)**: `TomitaFirstHalf.lean` — Δ^{it} implements the modular automorphisms
  (Δ^{it} π(a) Δ^{−it} = π(σ_t a)) and preserves the limit algebra:
  **Δ^{it} towerLimitVN Δ^{−it} = towerLimitVN — TOMITA'S THEOREM, FIRST HALF**, for the
  tower limit state. CHECKPOINT (verbatim in Checkpoint.lean): HAVE — towerFlow = Δ^{it}
  as operators; towerGen = generator of Δ^{it}; the modular theory of the physics equals
  the modular theory of the state. HAVE NOT — J/polar (JMJ = M′ = the natural next
  campaign, same eigenbasis method); no strip-KMS; no type; finite-stage Gibbs
  inductive-limit only.

**THE MODULAR CONJUGATION CAMPAIGN (ACTIVE, THE_MODULAR_CONJUGATION_PLAN.md)** — J, the
  polar decomposition on the core, Tomita II (inclusion). **J1 LANDED**: `JStage.lean` —
  the finite J layer: jStage = √ρ·aᴴ·√ρ⁻¹ with the verified eigenbasis scalar √(w_m/w_n),
  the polar-core trio, and the single-stage anti-isometry (green first try). **J2 LANDED**: `JEmbed.lean` — the cross-stage
  law (jStage commutes with the stage embedding, via THE ENGINE E1) + J commutes with the
  finite modular flow (green first try). **J3 LANDED**: `ConjPre.lean` — **towerJ exists**:
  the σ-semilinear (starRingEnd ℂ) completion of the norm-preserving jPre, no ℝ-reduction
  (Mathlib's CLM.completion is σ-generic); with the raw anti-isometry (green first try).
  **J4 LANDED**: `ModularConj.lean` — towerJ is a
  genuine involutive ANTI-UNITARY fixing Ω (⟪Jξ,Jη⟫ = ⟪η,ξ⟫, J² = 1, JΩ = Ω, conj-smul
  twist, bijective isometry; eigenbasis action √(w_m/w_n) flipped+conjugated; green first
  try). **J5 LANDED**: `PolarCore.lean` — **THE POLAR
  DECOMPOSITION ON THE CORE**: S̄ = J∘Δ^{1/2} and F = Δ^{1/2}∘J on pure components (order
  guard positive: the compositions provably differ), Δ^{1/2}² = Δ-core (green first try;
  honest: core-level identity, no unbounded Δ^{1/2}). **J6 LANDED**: `ConjFlow.lean` — J commutes with
  the full modular group: JΔ^{it} = Δ^{it}J (the correct sign — antilinearity flips i,
  JΔJ = Δ⁻¹ flips back; green first try). **J7 LANDED**: `ConjImplements.lean` — J conjugates
  left multiplication into right multiplication: **J π_C(a) J = R_{jStage a}**
  (jconj_towerRep), with jconj := J∘T∘J the ℂ-linear double-conjugation and the SOTApprox
  transport for J8 (green first try). **J8 LANDED — ★★ J M J ⊆ M′ ★★**:
  `TomitaSecondHalf.lean` — TOMITA'S THEOREM, SECOND HALF (INCLUSION): J conjugates
  towerLimitVN into its commutant (jconj_limitVN_mem_commutant), via the SOT transport of
  J π(a) J = R_{jStage a}; Ω separating for the commutant (green first try). The REVERSE
  inclusion (full equality J M J = M′) is NOT proved — Tomita's hard half, named RvD route.
  **J9 — CAMPAIGN COMPLETE (9/9, ALL first-try
  green)**. CHECKPOINT (verbatim in Checkpoint.lean): HAVE — J is a global anti-unitary
  (towerJ = completion of jStage a = √ρ·aᴴ·√ρ⁻¹, no ℝ-reduction; J² = 1, JΩ = Ω,
  ⟪Jξ,Jη⟫ = ⟪η,ξ⟫, conj-smul twist, eigenbasis √(w_m/w_n)); the polar decomposition
  S̄ = J∘Δ^{1/2} and F = Δ^{1/2}∘J on the core; JΔ^{it} = Δ^{it}J; and Tomita's second half
  (inclusion): J·towerLimitVN·J ⊆ towerLimitVN′, Ω separating for M′. HAVE NOT — the reverse
  inclusion / full equality J M J = M′ (Tomita's hard half, named RvD route); no unbounded
  Δ^{1/2}; no strip-KMS; no type; finite-stage Gibbs inductive-limit only. THE FULL MODULAR
  DATA (S̄, Δ, Δ†=Δ, Δ^{it}=physical flow, Tomita I, J, polar-on-core, Tomita II inclusion)
  now stands machine-checked for the tower limit state — the first Tomita–Takesaki modular
  theory in any proof assistant.

**THE NON-TRACIALITY CAMPAIGN (ACTIVE, THE_NON_TRACIALITY_PLAN.md)** — the tower state is a
  genuine non-tracial KMS state (Δ ≠ 1). BINDING VERDICT: state non-traciality + modular
  non-triviality ONLY — NOT a type classification, NOT "not type II" as an algebra
  statement. **N1 LANDED**: `NonTracial/FiniteNonTrace.lean` — ω(E_nm·E_mn) = w_n ≠ w_m =
  ω(E_mn·E_nm): the Gibbs state is not a trace. **N2 LANDED**: `TowerNonTrace.lean` — the tower vacuum
  vector state is non-tracial: ⟪Ω, π(E_nm)π(E_mn)Ω⟫ = w_n ≠ w_m = ⟪Ω, π(E_mn)π(E_nm)Ω⟫
  (green first try). **N3 LANDED**: `ModularNonTrivial.lean` — pure matrix-unit components
  are nonzero, **Δ ≠ 1** (towerModularOp_ne_id) and **Δ^{it} = towerFlow ≠ id**
  (towerModUnitary_ne_id, phase exp(iπ) = −1) on a nonzero eigenvector when the weights
  differ (green first try). **N4 — CAMPAIGN COMPLETE (N1–N4)**: `NonTracial/Checkpoint.lean` — the
  verbatim HAVE/HAVE-NOT. THE TOWER STATE IS A GENUINE NON-TRACIAL KMS STATE: ω is not a
  trace, Δ ≠ 1, Δ^{it} = towerFlow ≠ id — the Powers "not-the-tracial-case" separation.
  HONEST: NOT a type classification, NOT "not type II" as an algebra statement, no type
  III/S-invariant (needs crossed-product/flow-of-weights machinery absent from Mathlib);
  Araki–Woods/Connes/Buchholz–Wichmann stay CITED.

**THE KMS-BOUNDARY CAMPAIGN (COMPLETE, THE_KMS_BOUNDARY_PLAN.md)** — the tower vacuum is a
  KMS-boundary state. K1 (`towerState_kms_boundary`) + K2 (`towerFlow_vectorState`) ALREADY
  EXISTED from the flow campaign (verified axiom-clean); C1 capstone landed:
  `NonTracial/ModularDataComplete.lean` — `modular_data_complete_witness` bundles
  KMS-boundary + non-traciality + Δ≠1 from w_n ≠ w_m, with the full MODULAR DATA COMPLETE
  index + honest HAVE/HAVE-NOT. **THE TOWER'S TOMITA–TAKESAKI MODULAR THEORY IS COMPLETE**
  (S̄, Δ, Δ†=Δ, Δ^{it}=flow, Tomita I, J, polar-on-core, Tomita II inclusion, non-traciality,
  KMS-boundary — the first complete such in any proof assistant). HAVE NOT: strip-analyticity
  KMS, J M J = M′ equality (RvD wall), type III (Mathlib has no type API). PIVOT POINT: the
  tower is exhausted; next honest moves = free-field-sector port or the Δc² physics test.

## 4. Modular / crossed-product / Type II (more built-out than "finite shadows")

- **Genuine, axiom-free, UNBOUNDED machinery [AF]:** `Spectral.stoneGen_isSelfAdjoint` (unbounded Stone, via
  Gårding-mollifier density + deficiency indices — Mathlib lacks this); `PVM_of_selfAdjoint` (bounded);
  `boundedFC_mul` (bounded Borel FC multiplicativity); `fcOp` (unbounded `∫f dE`).
- **Weyl pair at the spectral level [AF] std-3** (`PositionPVM`/`PVMConj`/`MomentumPVM`): the abstract
  bounded-Borel functional calculus of the position PVM IS the concrete multiplication operator —
  `boundedFC_positionPVM_eq_mulOp : Φ_position(φ) = M_φ` (matched via sesquilinear forms: `⟪z,M_φ z⟫ = ∫φ‖z‖²
  = diagInt φ z`, whose polarization is `boundedFC`). `conj_boundedFC` (+ `conj_bilinDiag`) — the whole Borel
  calculus is covariant under unitary conjugation, `Φ_{UPU⁻¹}(φ) = U∘Φ_P(φ)∘U⁻¹`. Combined:
  `boundedFC_momentumPVM_eq_fourier_conj_mulOp : f(P) = ℱ∘M_f∘ℱ⁻¹` (since `momentumPVM = positionPVM.conj ℱ`).
  This NAMES the momentum generator spectrally, completing the canonical Weyl pair `X = ∫x dE`, `P = ∫k dÊ` at
  the bounded-calculus level. **CAPSTONE NOW COMPLETE:** `translationLp_eq_boundedFC_momentumPVM :
  momentumPVM.boundedFC(e^{itk}) = τ_{−t/(2π)}`, i.e. `e^{itP} = τ_{−t/(2π)}` — the `ℱ M_{e^{itk}} ℱ⁻¹` Fourier
  transfer is discharged. Built from `modSymbol_hasTemperateGrowth` (`e^{isx}` is an admissible Schwartz
  multiplier — `dⁿ/dxⁿ e^{isx}=(is)ⁿe^{isx}` has constant norm `|s|ⁿ`), the function-level duality
  `fourier_modSymbol_smul : 𝓕(e^{itv}f)(x)=𝓕f(x−t/2π)` (pointwise exp-kernel integrands), and the L² state
  identity `fourier_modulationLp_apply : ℱ(e^{itX}g)=τ_{−t/2π}(ℱg)` by density off `SchwartzMap.toLp`
  (`SchwartzMap.toLp_fourier_eq` + `DenseRange.induction_on`). The `2π` is the honest normalization of Mathlib's
  Fourier kernel `e^{−2πi x·ξ}` — `e^{itP}` is translation by `−t/(2π)`, not `t`. **DUAL + CCR PAIR COMPLETE
  (2026-07-06):** `modulationLp_eq_boundedFC_positionPVM : e^{isX} = boundedFC positionPVM(e^{isx})` (the
  position-side twin, immediate from `boundedFC_positionPVM_eq_mulOp` + `modulationLp := mulOp(modSymbol)`) and
  `positionOp_isSelfAdjoint : IsSelfAdjoint (stoneGen modulationLp)` (`PositionGenerator.lean`, the Fourier-dual
  twin of the existing `momentumOp_isSelfAdjoint`). So the canonical CCR pair `(X, P)` is complete at the
  self-adjoint-generator level, each named on its own PVM (`X=∫x dE` generates modulation, `P=∫k dÊ` generates
  translation), with the group-level Weyl relation `weyl_relation` already proven. ⚠ COSMETIC for QG (the GR-chain
  momentum datum is already wired via the self-adjoint `momentumOp`, `MomentumGenerator.lean`); this only names
  the generators spectrally.
- **One-particle RvD Tomita–Takesaki [AF]** on a genuine `StandardSubspace` (IsCyclic+IsSeparating): `J²=1`,
  `JRJ=2−R` (the `JΔJ=Δ⁻¹` shadow), `modUnitary = Δ^{it}` with group law + strong continuity, `Δ^{it}𝒦=𝒦`,
  `JΔ^{it}=Δ^{it}J`; `modularGen_isSelfAdjoint` (self-adjoint modular Hamiltonian K) with `Δ^{it}=e^{−itK}`.
- **Crossed product M⋊_σℝ [AF]:** `modularAut` σ_t (one-param *-automorphism group); `matterRep` π(a); `clockTransl`
  λ_t; covariance `λ_{−t}π(a)λ_t = π(σ_t a)`; `clockEnergy_isSelfAdjoint` (A_edge); **`dressedModularGen_
  isSelfAdjoint` (K̃ = K_bulk + A_edge self-adjoint)**.
- **The wall, rung W1 — `QIQTH/DualAction.lean`** (`QIQTH.StandardSubspaceModular`, **[AF]** std-3;
  `TYPE_II_TRACE_PLAN.md`). **The Takesaki dual action θ_s of the crossed product**, implemented by the fiberwise
  phase unitary `V_s` (`(V_sξ)(x) = e^{isx}·ξ(x)` on `L²(ℝ;H)`; group law, inverse): `dualAction s T := V_{−s}TV_s`.
  **`dualAction_matter`** — θ_s fixes the matter `π(a)`; **`dualAction_clock`** — θ_s phases the clock,
  `θ_s(λ_t) = e^{ist}·λ_t` — **the vector-valued Weyl relation**; `dualAction_add` (group law), `dualAction_mul`
  (conjugation multiplicativity). The action against which the dual-weight trace scales (`τ∘θ_s = e^{−s}τ`, the
  ladder's later rungs). ⚠ On the represented operators `B(L²(ℝ;H))`; the vN closure and the full CPW trace stay
  the carried frontier below.

- **The wall, rung W1.5 — `QIQTH/LogClockWeight.lean`** (`QIQTH.TypeIITrace`, **[AF]** std-3;
  `TYPE_II_TRACE_PLAN.md`). **The log-clock weight integral — the exact `e^{−s}` scaling engine.** `ExpTest`
  (bounded measurable compact-support log-clock symbols; closed under the dual shift `θ_s : f ↦ f(·+s)` and clock
  modulation `modMul` = the symbol of `λ_t·f(L)`); `expTest_integrable`; `Iexp f = ∫e^x f(x)dx` — the CPW density
  on the **log-clock** spectral variable (the binding consult correction: never the clock position).
  **`Iexp_dualShift`** — the EXACT scaling `Iexp(f(·+s)) = e^{−s}·Iexp f` (pure change of variables, no
  regularization) — the `τ∘θ_s = e^{−s}τ` mechanism to which every later trace rung reduces;
  `Iexp_dualShift_modMul` (the W3a monomial form). ⚠ Symbol/integral level; the operator representation and the
  trace functional are the later rungs; vN closure + full CPW trace stay the carried frontier below.

- **The wall, rung W2 — `QIQTH/ZClockRegression.lean`** (`QIQTH.TypeIITrace`, **[AF]** std-3;
  `TYPE_II_TRACE_PLAN.md`). **The ℤ-clock regression: shift quasi-invariance ≠ dual-circle invariance,
  machine-checked.** On banded ℤ×ℤ core kernels with the exponential diagonal weight `zWeight = ∑e^n·A(n,n)`:
  **`zWeight_shift_quasiInvariant`** — conjugation by the SHIFT (the discrete log-clock translation) scales the
  weight by exactly `e^{−1}` (the ℤ mirror of `τ∘θ_s = e^{−s}τ`); **`zWeight_dualCircle_invariant`** — the TRUE
  dual action of `M⋊ℤ` (the circle phases) leaves the weight INVARIANT. The binding consult distinction — the
  scaling belongs to the shift, never the dual action — is now a pair of theorems. Plus positivity
  (`zWeight_nonneg_of_diag_nonneg`) and window stability (`diagSum_superset`). ⚠ Banded-kernel core (the honest
  domain); the operator/vN packaging stays with the ℝ-clock ladder.

- **The wall, rung W3a — `QIQTH/MonomialTrace.lean`** (`QIQTH.TypeIITrace`, **[AF]** std-3;
  `TYPE_II_TRACE_PLAN.md`). **The monomial trace formula — `τ₀∘θ_s = e^{−s}·τ₀`, exact.** `tauMonomial` — the
  dual-weight trace on normal-ordered core monomials `π(a)·λ_t·f(L)`, `:= ω(a)·∫e^x e^{itx}f(x)dx` (the consult's
  log-clock normal form; the forbidden position-diagonal form never appears). **`dualAction_monomial`** — the
  operator-level phase justification `θ_s(π(a)λ_t) = e^{ist}·π(a)λ_t` (W1's identities composed).
  **`Iexp_modMul_dualShift_comm`** — the modulation/shift Weyl interchange. **`tauMonomial_dual`** — the
  capstone: `e^{its}·τ₀(a,t,f(·+s)) = e^{−s}·τ₀(a,t,f)` — the CPW relative invariance on the monomial core,
  EXACT, no regularization (the Weyl phase cancels against the density shift). ⚠ Trace-functional level;
  traciality and positivity are W3b (the eigen-core); the operator `f(L)` representation and the vN closure stay
  with the later rungs / the carried extension.

- **The wall, rung W3b — `QIQTH/EigenCore.lean`** (`QIQTH.TypeIITrace`, **[AF]** std-3;
  `TYPE_II_TRACE_PLAN.md`). **The eigen-core: the dual weight is a TRACE.** `EigenTerm (κ, a, F)` (= `π(a)·F(L)`,
  `a` a modular eigenoperator) with data-level *-operations (`mul` via the covariance relation
  `F(L)π(b) = π(b)F(L−κ_b)`, `star`, `theta`). **`eigen_tau_dual`** — the scaling `τ₀(θ_s x) = e^{−s}·τ₀(x)`.
  **`eigen_tau_trace`** — **traciality** `τ₀(xy) = τ₀(yx)`: at zero total frequency the carried matter KMS-eigen
  factor `ω(ab) = e^κ·ω(ba)` cancels EXACTLY against the `∫e^r` change of variables (`Iexp_shiftMul_swap`); off
  it both sides vanish (carried frequency conservation) — **the Type II mechanism: a KMS matter state becomes a
  trace after the log-clock dressing**, machine-checked. **`eigen_tau_star_mul_nonneg`** — **positivity**
  `τ₀(x*x) ≥ 0`: the `x*x` symbol is the pointwise norm-square (`star_mul_symbol`), the weight integral a nonneg
  real, times the carried matter positivity. ⚠ The KMS-eigen law, frequency conservation, and matter positivity
  are CARRIED hypotheses (the modular-matter inputs — provable for the finite corner, abstract here);
  single-term/pair level; the vN closure stays the carried frontier below.

- **The wall, rung W4 — `QIQTH/TraceCapacityFromCore.lean`** (`QIQTH.TypeIITrace`, **[AF]** std-3;
  `TYPE_II_TRACE_PLAN.md` — **CAMPAIGN COMPLETE, W1–W4, 6/6 rungs**). **The capacity interfaces fed by the
  CONSTRUCTED trace.** `CoreDensity` (normalized star-square core densities, positive by W3b).
  **`phase5_from_core_trace`** — a `Phase5Master` certificate whose nonnegative JLMS remainder is **realized** as
  the constructed `τ₀(r*·r)` (W3b's positivity theorem powering the previously-posited field; the JLMS balance
  stays the carried area/calibration input). **`traceCapacity_from_core`** — a `TraceCapacity` certificate whose
  bound `S_ren ≤ Q` is a **theorem** (the slack is the constructed trace value). **`DualWeightTraceExtension`** —
  the CARRIED vN-extension typeclass (normal weights/affiliated operators = the genuine remaining frontier;
  a named hypothesis, never an axiom); `extension_preserves_density_mass`. ⚠ **The wall is NOT crossed**: the
  dual-weight trace exists with exact scaling, traciality, and positivity ON THE ALGEBRAIC CORE; the von Neumann
  closure, the continuum count, and black-hole matching remain carried/cited.

- **The joins, J1 — `QIQTH/FiniteCornerEigen.lean`** (`QIQTH.TypeIITrace`, **[AF]** std-3;
  `HYPOTHESIS_DELETION_PLAN.md`). **The finite corner DISCHARGES the eigen-core matter inputs** — W3b's three
  carried hypotheses become THEOREMS of the concrete corner `Matrix ι ι ℂ`, `ω = tr(diag p ·)`, matrix units
  `E_ij` with modular frequency `κ_ij = log p_i − log p_j`: **`sigmaDiag_single`** (the eigen law
  `σ_t(E_ij) = e^{itκ_ij}E_ij` under the finite modular flow `ρ^{it}·ρ^{−it}`), **`finiteCorner_kms_E`** (the
  KMS-eigen law, unconditional), **`finiteCorner_freq_E`** (frequency conservation — AUTOMATIC from the
  matrix-unit index loop, `κ_ij + κ_ji = 0`, no nondegeneracy), **`finiteCorner_pos`**
  (`ω(A*A) = ∑ p_m‖A_km‖² ≥ 0`). Capstones: **`finiteCorner_tau_trace`** and **`finiteCorner_tau_pos`** — the
  constructed dual-weight trace's traciality and positivity hold on the `finiteCornerTerm` family with **NO
  matter hypotheses** (hkms/hfreq/hpos DELETED for this model). ⚠ The finite (Type I) corner is the concrete
  witness, not the continuum matter algebra; diagonal `ρ` (general PosDef via eigenbasis transport = follow-on);
  the vN closure stays carried.

- **The Type II dual-weight TRACE `τ∘θ_s = e^{−s}τ`** — now BUILT on the algebraic core (rungs W1–W4 above: exact scaling + traciality + positivity), with the vN-closure half still the [frontier] (the carried `DualWeightTraceExtension`); bridged by the
  non-vacuous `Phase5Master` interface (never an axiom). Also frontier: vN double-commutant closure of the crossed
  product; full vN-algebra (vs one-particle) relative entropy via `Γ(Δ^{it})`; continuum Type III₁ classification.
- Araki/Umegaki relative entropy **[AF]** finite-dim (Type I shadow); `ModularRelativeEntropy.cgpEntropy` is the
  **genuine continuum one-particle** CGP entropy with `cgpEntropy_nonneg` **[AF·cond: ξ∈𝒦, spectral bounds]**
  (all-vector positivity is FALSE — honestly noted).
- **The free-field MODULAR-ENERGY bound `ModularEnergyBound.lean` (Route 1 reframed, B1–B7, all [AF] std-3)** — the
  honest, derivable content of the JLMS route (`ROUTE1_MODULAR_PLAN.md`). K_σ = −log σ; ⟨K_σ⟩_ρ = crossEntropy(ρ,σ):
  - **B1 `modular_relEnt_identity`** — Umegaki: `D(ρ‖σ) = (⟨K_σ⟩_ρ−⟨K_σ⟩_σ) − (S(ρ)−S(σ))`.
  - **B2 `modular_casini_bound`** — `S(ρ)−S(σ) ≤ ⟨K_σ⟩_ρ−⟨K_σ⟩_σ` (from Klein positivity).
  - **B3 `finiteCorner_wedge_Casini_BW`** — with `K_σ = 2π K_boost + c·1` (BW/KMS, carried as an **explicit
    hypothesis** — the modular-invariant-corner caveat): `ΔS ≤ 2π Δ⟨K_boost⟩` (the Unruh modular bound).
  - **B4 `finiteCorner_firstLaw`** — the first law `δS = δ⟨K_σ⟩` as relative-entropy stationarity (`D'=0` at ρ₀).
  - **B4′ `finiteCorner_firstLaw_boostEnergy`** — the explicit first law `δS = 2π δ⟨K_boost⟩` (scalar-derivative hyps).
  - **B6 `modular_casini_saturation`** / **B6′ `finiteCorner_wedge_saturation_BW`** — **rigidity**: the bound is
    saturated iff `ρ = σ` (via faithfulness `relEntropy_eq_zero`).
  - **B7a `finiteCorner_wedge_BW_deficit_eq_relEntropy`** — exact deficit `2π Δ⟨K_boost⟩ − ΔS = D(ρ‖σ)`;
    **B7b `…_Casini_BW_strict`** (strict off the reference); **capstone `freeField_modularEnergyBound_finiteCorner_BW`**
    (bundle: bound ∧ exact-deficit ∧ rigidity).
  - ⚠ **Scope:** FORMALIZED MODULAR QFT, **NOT** a derivation of `A/4G` via the JLMS *modular route* (no `G`, no area
    operator in a free scalar; `A/4G` stays a gravitational input here — the continuum Type II trace where it lives
    is the [frontier] above). This is **distinct from the `1/4`**, which *is* derived (§3, Sakharov `sakharov_ratio`);
    neither derives the value of `G`. Upgrades `Phase5Master`'s modular pieces from carried hypothesis to theorems.

## 5. Lorentz covariance / records / Open Problem 3b

- **This thread is covariance of the (Φ,λ,μ) MEASURE/SELECTION layer — NOT the radiative Lorentz naturalness of
  interacting matter** (different question, §2/Gap-4).
- `LorentzSelection.evaluation_covariance` / `LorentzSelectionStrong.group_evaluation_covariance` **[AF·cond:
  RecordedHistoryNet / GroupAction]** — the selector is Poincaré-covariant: `A_{gD}[U_gΦ,g·λ] = g·A_D[Φ,λ]`.
- `RecordedHistoryNet.card_le` **[AF·cond]** — `card(P.X D) ≤ N D ≈ exp(Q_D)`, `Q_D=A(∂D)/4ℓ_P²`: a **cardinality
  bound on the finite DECOHERENT RECORD fibre** (pointer sectors), **not** matter modes; Type III matter
  acknowledged.
- `CovariantGluing.no_covariant_selector` **[no-go, AF, unconditional]** — a covariant *measure* exists but a
  covariant *selector* cannot (the S² obstruction). λ is a symmetry-breaking *sample* of a covariant law.
- `FreeFieldTypicality.freeFieldMeasure_boost_invariant` **[AF·cond: boost-invariant per-region state]** — the
  typicality measure is boost-invariant (genuine, but **Type I / finite-mode**).
- `LorentzWitness` / `DiamondSwapNet` **[AF]** — genuine **non-vacuous** witnesses (a real 2-outcome Born system
  ψ=(3/5,4/5); a non-trivial geometry-moving orbit) — refuting "only the trivial one-point net satisfies the
  interface." But finite/toy; the **continuum Type III₁ realization (OP3b proper) is [frontier]**, honestly stated.
- No-signaling: `NoSignalingGeneral.bipartite_no_signaling` **[AF, unconditional]** (any finite bipartite ρ);
  `Theorem7.no_signaling` **[AF·cond: locality field]** (microcausality⟹locality gap is a TODO).
- **Self-flagged caveat:** bare "a RecordedHistoryNet exists" is vacuous (one-point net); the genuine OP3b is the
  realization problem, correctly stated open.

## 6. Corner construction / free SM fields / emergent spacetime (transport, not construction)

- `FreeFieldCorner.sm_free_field_in_corner` **[AF·cond: supplied isometry V + supplied field algebra]** —
  transports a *supplied* free-SM-content algebra into the capacity-bounded corner + area-bounds its records.
  **"Transport, NOT construction; capacity is a constraint, NOT a generator"** (docstring).
- No-overclaim guards **[AF]:** `encoded_CAR_ambient_forces_full` (ambient-1 CAR ⟹ P=1); `minCut_area_not_metric`
  (min-cut violates triangle ineq — repaired by `embedDist_isPseudometric`); `finiteDim_scaling_forces_zero` (no
  exact finite dilation/boost); `no_finiteDim_CCR` (exact finite bosonic CCR impossible); the photon truncation
  carries an *explicit surviving defect*.
- Emergent-geometry Track C **[AF·cond: supplied entanglement data]** — two provable metrics, finite RT
  inequality, CMI/Markov, first law, causal skeleton, certificate. **Finite proto-geometry with error tags, NOT a
  4D manifold [frontier].**

## 6b. Entropy/ — the DPI / Lieb-concavity / operator-convexity tower (19 files) — GENUINELY COMPLETE

**This was understated in earlier summaries.** `QIQTH/Entropy/` is a **complete, axiom-free, finite-dimensional
implementation of the entire Carlen DPI–Lieb machinery that Mathlib lacks** — a serious formalized-math
contribution independent of the physics interpretation. All **[AF]** (hypotheses are intrinsic data: `PosDef`,
`IsHermitian`, `IsDensity`, `t∈[0,1]`), no `sorry`, no project axioms:
- `peierls_inequality`, `trace_function_convex` (§2 trace-convexity); `matrix_sqrt_le_sqrt` (Löwner–Heinz via a
  CStarMatrix bridge); `star_inv_subadditive` (**Ando joint convexity**), `gmean_superadditive` (geometric-mean
  concavity); `commute_rpow_mul` and `tensor_rpow_superadditive` (matrix facts Mathlib lacks, proved from
  scratch); **`lieb_superadditive` (Lieb's concavity theorem, the deepest result)**; `relEntropy_subadditive`
  (joint convexity of quantum relative entropy); `dpi_mixed_unitary` + `partial_trace_dpi` (**DPI**, via a
  from-scratch discrete-Weyl 1-design); **`strong_subadditivity`** + `condMutualInfo_nonneg`.
- **The axiom budget GENUINELY DROPPED to 0 via real discharge** (not relabeling): Donald 29→21, DPI 21→17,
  ArakiInterface 17→…→6, EntropyBridge 6→0 (ledger in `axiom_budget_check.sh`).
- **[frontier]:** fully-general CPTP DPI (beyond mixed-unitary + partial-trace); Type II/III continuum relative
  entropy. **Hygiene gap CLOSED (verified 2026-07-02):** `strong_subadditivity` / `condMutualInfo_nonneg` ARE
  pinned in `AxiomAudit.lean` (lines ~7577–7578) and probe std-3; the earlier "not yet pinned" note was stale.

## 6c. Fock/ — second quantization (39 files) — more built-out than "one-particle shadows"

**Also understated earlier.** Genuine continuum second-quantized constructions, all **[AF]**:
- Bosonic **Fock space** (`expKernel_posSemidef'`, Schur/Hadamard), bounded **Weyl operators** + CCR
  microcausality, the **second-quantized modular flow `Γ(Δ^it)`** (unitary group + automorphism `σ_t`, Tomita at
  field level), conditional only on a genuine *Mathlib* `StandardSubspace` (not a project postulate), discharged
  for the free-field wedge.
- **★ `oneParticleBW_niceWedge_unconditional` — the one-particle Bisognano–Wichmann, FULLY UNCONDITIONAL,
  axiom-free** (both Reeh–Schlieder inputs discharged internally: wedge-totality via an L²-Wiener–Tauberian
  theorem, separating via Pauli–Jordan symplectic non-degeneracy). `freeField_oneParticle_hFlux` wires the **+2π
  flux into GR** (axiom-free up to the labelled localization map `hTkk`).
- **★ `weylBit_typicality_lorentzBoost_invariant` — a σ-additive boost-invariant typicality measure on the
  continuum 1+1D free field [AF]**, non-vacuous via genuine spacelike Pauli–Jordan (`K_im_inner_eq_zero_of_
  spacelike`) — the literal OP3b deliverable at the free-field level. Continuum-λ selection on the Fock vacuum
  (`field_selects_exists_unique`, Born = vacuum-state weights) **[AF]**.
- **[frontier]:** the local von Neumann algebra `M(W)` / Type III₁ factor property / crossed-product→FQ; the
  localization map (Gap 2).

## 6d. Fock/Dirac/, Fock/Photon/, Fock/StressTensor/ (35 files) — free-field second quantization

All **[AF]** (PhysLean dependency verified to introduce **no extra axioms**), **free-field only**:
- **Electron:** CAR Fock (`finrank_CARFock = 2ⁿ`), **genuine `{a,a†}` anticommutator via PhysLean WickAlgebra**,
  the **Klein-twist algebra** (`Z²=Γ`, witnessed on full CAR Fock), functorial fermionic modular flow `Γ₋(Δ^it)`
  + finite KMS with **genuine spectral von Neumann entropy** and first law; concrete 4×4 Dirac γ (`{γμ,γν}=2η`).
- **Photon:** PhysLean-grounded gauge-invariant records (gauge/Lorentz/EOM-invariant), **BRST cohomology** with
  observable descent, helicity (`dim=2`), finite capacity + the explicit truncation defect, edge/center entropy.
- **Stress tensor:** the KG null stress `T_kk` as a *defined* object, and **★ `wedge_boostCharge_eq_neg_
  stressFlux`** — the conserved boost charge **IS** the free-field horizon stress flux, **discharging the
  `conserv`/`hTkk` input of the QIQT→GR chain for the explicit KG field** (heavy Fourier/Plancherel analysis).
- **[frontier]:** interacting matter / SM / mass gap; the full-Fock Klein-twist *commutant theorem* (needs Fock
  GNS adjoint); antilinear modular conjugation; indefinite-metric BRST physics (no-ghost); the Dirac
  one-particle propagator wiring.

## 6e. Remaining top-level discharge (Bell / Tsirelson / Goldstein–Struyve / interface axioms)

- **All former interface-axiom clusters discharged to std-3** (no project axioms): `DPI_inequality` (theorem,
  mixed-unitary class), `donald_identity` (over `DonaldSystem` typeclass + concrete instance), `ArakiInterface`
  (fully discharged — Holevo `IHol_le_Shannon` + Klein equality both proved), `EntropyBridge` (→0, + the honest
  `fq_ambiguity_counterexample`), `RelEntPositivity` (axioms removed, Gibbs proved).
- **Bell/Tsirelson [AF]:** `chsh_le_two` (LHV CHSH ≤ 2, rigorous); `tsirelson_rigorous` / `singlet_chsh_abs_gt_two`
  (explicit 4D singlet giving 2√2 > 2). `ContextualitySafe.no_global_record_valuemap`.
- **Goldstein–Struyve [AF]:** `schur_classification_real` **fully proved** (was an axiom), with non-vacuity
  countermodels certifying each hypothesis is load-bearing.
- **⚠️ `CapacityModel.capacity_exactly_one` — sound but definitionally-loaded:** "≤1 macroscopic record" is proved,
  but the physical load sits entirely in *defining* `Macroscopic := recDim > D/2`. This is the **retired-H2
  intuition** formalized; the Lean is honest (supplies λ as the selective input), but paper/site prose must keep
  the H2-retired caveat (capacity does NOT select outcomes — λ + decoherence does).

## 7. The honest no-go / retraction inventory (discipline)

`NoBornFromNothing`, `NoConcentration`, `EquivarianceGap`, `OperationalNoGo`, `RealmSelection.capacity_
underdetermines_realm`, `H1H2Audit.H1_does_not_imply_H2`, `FQDynamicsNoGo`, `CovariantGluing.no_covariant_
selector`, `minCut_area_not_metric`, `no_finiteDim_CCR`, `finiteDim_scaling_forces_zero`, the QG-campaign no-gos
(`no_exact_finite_boost`, `finite_modular_spectrum_ne_real_line`, `finitePoincare_trivial`, `entropy_bound_not_
cardinality_bound`). **Retracted/retired** (honestly, in-repo): the positivity-free Gleason axiom; the
Macroscopic-Definiteness/H2 reading (capacity forbids multi-record); the "escapes CPSUV" verdict.

## 8. Cited frontiers (NOT done — never claim these as results)

Type II dual-weight trace; continuum Type III₁ classification; vN-algebra (vs one-particle) relative entropy;
lattice area-law SCALING `S∝A`; the localization map `hTkk` smearing construction; the heat-kernel coefficients
(cited data); the value of `G`/`ℓ_P`; OP3b continuum realization (Poincaré net from a fixed QFT); interacting SM /
YM mass gap / SSB; the 4D background-independent manifold; λ's dynamical Lorentz-covariant law; the radiative
Lorentz-naturalness of interacting matter (CPSUV escape — open, ~10–20%).

**WILLIAMSON N-mode symplectic diagonalization — ✅ UNCONDITIONAL & COMPLETE (2026-07-06).** `QIQTH.Williamson`
(`WilliamsonNormalForm.lean`, axiom-free std-3). Williamson is now UNCONDITIONAL: `williamson_exists` /
`williamsonDecomp_of_posDef (M) (hM : M.PosDef) : WilliamsonDecomp M` carry NO hypothesis beyond `M.PosDef`. The
last carry `YoulaDecomp` FELL (W8–W12) — the genuine-attempt-before-declaring discipline cracking a wall that
four assessments had called research-grade: `youla_pairing` is the REAL antisymmetric block normal form
(skew-adjoint `a` on an even-dim real inner-product space ⟹ an orthonormal basis pairing `a` into ν-rotation
blocks), proved via the REAL route after the complex-Schur route (W7 `iA_isHermitian`) stalled — `T := A*A`
symmetric ≤ 0 (real spectral thm), each positive eigenspace carries a complex structure hence is even-dim
(`antisymm_eigenspace_even`, a `det`-sign argument), and a `finrank` dimension-halving induction
(`youla_pairing_aux`: minimal-Rayleigh eigenvector block extraction + `skewAdjoint_orthogonal_invariant` recursion
+ `OrthonormalBasis.mk` gluing); `youlaDecomp_of_antisymm` bridges it to `Matrix (l⊕l)(l⊕l) ℝ`. **Both
`youla_pairing` (the real antisymmetric normal form) and `williamson_exists` (the symplectic normal form) are
Mathlib-FIRSTS.** W13 `williamson_entropy_symplectic_invariant`: the Gaussian entanglement entropy
`∑ gaussModeEntropy νᵢ = gaussStateEntropy` depends on `M` ALONE (equal charpoly of `−(J·M)²` ⟹ equal `{νᵢ²}`
multiset ⟹ equal entropy) — a genuine, well-defined physical entropy, not an artifact of the chosen
diagonalization. **HONEST:** this is the diagonalization TOOL + entropy WELL-DEFINEDNESS, **NOT** the area-law
SCALING `S∝A` (Srednicki boundary-mode-domination for the free-field lattice covariance — still a cited analytic
frontier, area/volume-blind and untouched by Williamson). ⟨The W1–W7 "in progress / carried YoulaDecomp /
plateaus here / NOT unconditional" narrative below is SUPERSEDED by the above; retained for provenance.⟩ The
original scoping (max-flow lesson: attempt the core, carry the analytic frontier): W1: the `WilliamsonDecomp` structure (symplectic S with
Sᵀ M S = D⊕D, symplectic eigenvalues ν), symplectic-form algebra ((det S)² = 1 from Sᵀ J S = J; block-diagonal
det = (∏ν)²), reusing Mathlib's `symplecticGroup`/`orthogonalGroup`. W2: the CARRIED `YoulaDecomp` (the real
antisymmetric skew normal form Oᵀ A O = [[0,D],[−D,0]] — absent from Mathlib, the analytic frontier / `haug`
analogue, a structure never an axiom). **CAMPAIGN COMPLETE (W1–W6, honest)**: W3 delivered `williamsonAux_antisymm` (√M·J·√M
  antisymmetric — the real CFC.sqrt entry point) and honestly CARRIES the S-construction
  (block-diagonalization) as `hconstr`, the haug analogue; W4/W5 the entropy connection —
  `WilliamsonDecomp.entropy = ∑ gaussModeEntropy` over the symplectic spectrum, nonneg under
  the Heisenberg floor, = the repo's `gaussStateEntropy` — THE SYMPLECTIC SPECTRUM FEEDS THE
  GAUSSIAN ENTANGLEMENT ENTROPY (the QG/holography payoff). HONEST: the WilliamsonDecomp
  framework + symplectic algebra + antisymm entry point + entropy bridge, **S-CONSTRUCTION now DERIVED** (`williamson_of_youla`): given M.PosDef + a YoulaDecomp of √M·J·√M, the
  symplectic congruence S = √M⁻¹·O·E is CONSTRUCTED and both Sᵀ M S = D⊕D and S·J·Sᵀ = J proven (the sign fix:
  a block-swapped root reconciles Mathlib's J with Youla's orientation). W3's carried S-construction is retired —
  Williamson is now conditional on YoulaDecomp ALONE (the real-antisymmetric normal form, absent from Mathlib).
  **Youla spectral entry point DERIVED** (W7): `iA_isHermitian` (i·A_ℂ Hermitian for real antisymmetric A ⟹ the
  complex spectral theorem applies) + `iA_conj_antifixed` (the ±ν pairing seed). HONEST CHECKPOINT: the real-block
  assembly (real-Schur O = [Re col, Im col] from conjugate eigenvector pairs + the multiplicity pairing across the
  Sum split) is a genuine Mathlib gap — the real normal form for antisymmetric matrices — pinned as the frontier,
  not faked. Williamson plateaus here: the S-construction and the spectral entry point are derived; the real-block
  assembly is the precisely-characterized remaining wall.
  ⟨SUPERSEDED — Williamson IS now unconditional (see the ✅ header above); only the area-law S∝A
  scaling remains the separate cited frontier.⟩

**MAX-FLOW=MIN-CUT — ✅ COMPLETE & UNCONDITIONAL (M1–M12), Ford–Fulkerson gap DISCHARGED (2026-07-05).** `QIQTH.QG.MaxFlowMinCut`
(axiom-free std-3): a genuine ATTEMPT at the Ford–Fulkerson wall on the repo's own flow/cut framework
(EmergentSpacetime `IsSTFlow`/`flowValue`/`cutCapacity`, weak duality already done). M1 the algebraic saturation
lemma (a flow saturating a cut's forward boundary with zero backflow has flowValue = cutCapacity); M2 the residual
graph `ResidualStep` + reachable set `residualCut` (ReflTransGen) + closure; ★ M3 `residualCut_saturates` — if the
sink t is NOT residual-reachable from s, the residual-reachable set IS a saturating cut. With
`ExactRT.exact_rt_of_saturating`, exact RT (max-flow = min-cut) now holds CONDITIONAL ONLY on `t ∉ residualCut`
(the no-augmenting-path condition, M4) + the CARRIED existence of a maximum flow (M5). This SHARPENS the cited
Ford–Fulkerson gap from "a witness exists" to one sharp combinatorial condition + one carried existence input.
HONEST: not an unconditional max-flow theorem; finite (V→V→ℝ) network model, not continuum RT. **M4+M5 CAMPAIGN COMPLETE**: exact_rt_of_maxFlow
(maximality + carried haug ⟹ t∉residualCut) + ★ exact_rt_maxFlow_mincut (THE CAPSTONE:
max-flow = min-cut conditional ONLY on the carried haug) + singleEdge_augment_forward (the
one-edge augmentation CONSTRUCTED, mechanism real). The combinatorial content of
max-flow=min-cut is machine-checked on the tower's flow/cut framework; the Ford–Fulkerson gap
is reduced to the single carried haug (general augmenting-path ⟹ bigger flow, the analytic
frontier, single-edge case discharged). First green crossing of a wall confirmed unbuilt in
Lean (Isabelle prior art only) — a genuine wall, mostly crossed. **M6 (deepening)**: `twoEdge_augment_forward` — a two-edge forward residual path
yields a strictly larger flow, machine-checking the interior-vertex conservation crux (the mechanism the general
haug needs); the general n-edge mixed-direction ReflTransGen-walk augmentation stays carried with the exact
obstruction pinned (walk revisits ⟹ naive-induction slack consumption ⟹ need simple-path extraction). + **M7**: `forwardAugPath_augments` derives the augmentation for ARBITRARY-length forward simple paths
(a degree-structured edge set: interior in-deg = out-deg ⟹ conservation preserved; value up by ε at s) — the
full forward-path augmentation MECHANISM, lifting the M6 hand-built cases to all lengths and removing the
vertex-revisit obstruction for forward paths. So max-flow = combinatorial core (M1-M3) + the FULL forward-path
augmentation (M4-M7) + only the extraction (walk ⟹ path degree-structure), mixed-direction, and existence carried. **M8**: the extraction's degree-structure is now DERIVED —
`SimpleForwardPath.toForwardAugPath` builds the degree-structured edge set from an injective simple path
(injectivity ⟹ interior in-deg = out-deg = 1 via fibre counting), ε is derived internally, and a simple forward
path ⟹ a bigger flow (`augment_of_simpleForwardPath`); only the DIRECTED DEDUP (ReflTransGen walk ⟹
SimpleForwardPath) stays carried — Mathlib's `Walk.bypass`/`toPath` are undirected, so unusable here. **M9**: the directed dedup DERIVED — `simpleForwardPath_of_reachable` (a forward residual walk ⟹ a
SimpleForwardPath, via the minimal-walk splice-shortens argument `dedup_aux` + nodup→injective conversion — the
directed analogue of `Walk.bypass`, absent from Mathlib) and the capstone `forwardReachable_augments` (forward
residual reachability ⟹ a strictly larger flow — the forward Ford–Fulkerson haug, FULLY DERIVED). **Max-flow's
ENTIRE FORWARD side is now machine-checked** (combinatorial core + augmentation mechanism + directed dedup);
**M10** derives the mixed-direction augmentation: `residualAugPath_augments` — a typed
degree-structured residual path (Pf forward + Pb backward edges) yields a strictly larger flow (g = f ± ε, all
four IsSTFlow fields derived, the ±ε conservation via linear_combination — outgoing step +ε, incoming −ε
regardless of type). ForwardAugPath is the Pb = ∅ case. So max-flow's ENTIRE augmentation mechanism (forward +
mixed) is now derived; **M11** discharges the mixed extraction: `residualReachable_augments` (general residual reachability ⟹
a bigger flow — the FULL Ford–Fulkerson haug DERIVED, via the Pf/Pb tagging of a SimpleResidualPath + M10's mixed
augmentation) and ★★ `exact_rt_maxFlow_mincut_unconditional` — **max-flow = min-cut conditional on ONLY the
existence of a maximum flow**. The entire combinatorial + augmentation content (both directions) is now derived;
built one honest
increment at a time — including directed path-dedup theory Mathlib lacks. **M12 — CAMPAIGN COMPLETE**:
`exists_maxSTFlow` (a max flow EXISTS — the flow set is a nonempty compact polytope in V→V→ℝ via Heine–Borel,
flowValue continuous, IsCompact.exists_isMaxOn) and ★★ **`maxFlow_min_cut` — the finite max-flow = min-cut
theorem, UNCONDITIONAL** (carrying ONLY cap-nonneg, the standard definitional hypothesis; the entire M1–M12
pipeline machine-checked with NO carried mathematical hypotheses). A genuine wall FULLY CROSSED — not in Mathlib.
HONEST: the finite (V→V→ℝ) network model, NOT continuum RT, NOT QG; and the repo's ExactRT Ford–Fulkerson
gap is now DISCHARGED: `exact_rt_unconditional` feeds the proved saturating witness into
`ExactRT.exact_rt_of_saturating`, so the full exact-RT optimality statement holds UNCONDITIONALLY (only
cap-nonneg), and ExactRT.lean's docstring is updated — the previously-cited Ford–Fulkerson frontier is a
machine-checked theorem, not a citation. A Tier-3 RT frontier item (holographic entanglement = min-cut) closed
for the finite network model.

**The three frontier libraries — ECOSYSTEM STATUS (2026-07-05, web-verified).** Checked whether the Mathlib-grade
gaps blocking the remaining frontier already exist anywhere: (1) **Riemannian heat kernel / Seeley–DeWitt** (blocks
κ=1/6, hence numerical G) — NO formalization in any proof assistant, AND doubly-blocked: its prerequisite
(geodesics / exponential map / Riemann curvature tensor) is an *acknowledged* "big gap remaining in mathlib4",
an ACTIVELY-MAINTAINED area (maintainer Michael Rothgang). Realistic route: WATCH/contribute to Mathlib's
diff-geo effort, then the RNC expansion + heat kernel become a normal (large) project on top — cheaper than
self-building the whole stack. (2) **Max-flow–min-cut / Ford–Fulkerson / Menger** (blocks exact RT) — NOT in
Mathlib, but PRIOR ART exists in Isabelle/HOL (Lochbihler countable-network; Lammich–Sefidgar refinement) +
Mizar — portable but a substantial Lean port; **now BUILT in-repo (`maxFlow_min_cut`, unconditional) rather than
ported.** (3) **Williamson symplectic normal form** — NOT in Mathlib4, but **now BUILT from scratch in QIQTH (a
Mathlib-first: `williamson_exists` / `youla_pairing`, UNCONDITIONAL as of 2026-07-06)** — so it no longer *blocks*;
only the Srednicki area-law SCALING `#{ν>½} ∝ A` remains the frontier. Net: of the three ecosystem gaps, max-flow
and Williamson are now proved in-repo (neither reused from elsewhere); only the heat-kernel / Seeley–DeWitt route
(1) stays gated on Mathlib's own open diff-geo frontier.

**Area-law `S ∝ A` frontier — CHARACTERIZED as a genuine wall (2026-07-05, consult-verified).** The entropy
machinery is complete to its honest ceiling: `GaussianStateEntropy` (the per-mode Srednicki entropy
`(ν+½)log(ν+½)−(ν−½)log(ν−½)` with full calculus, the total-as-sum, `gaussStateEntropy_eq_sum_active` = "entropy
counts entangled modes", one-mode Williamson ν=√det with the Heisenberg floor) + the DY region-entropy chain
(`entropy_gibbs_region` S = ∑_{k∈R} modeEntropy, `Smicro_le_count` S ≤ ∑ log D_k). But the SCALING S ∝ A is NOT
buildable and — the sharp point — NOT honestly carriable: **the Lean entropy machinery is IDENTICAL for an area
law and a volume law** (both give "S ≤ (mode count)·(per-mode max)"), so the entire S∝A-vs-S∝V distinction lives
in the boundary-mode count `#{ν>½} ∝ A`. Carrying that count as a hypothesis carries the WHOLE theorem — a
decorative tautology, NOT the heat-kernel-a₁ house style (there the derived analytic number 1/48π multiplied an
INDEPENDENT carried geometric integral; here the derived side is area/volume-blind and contributes nothing the
carried count doesn't). The un-carriable content — the correlation-decay eigenvalue localization giving
#active ∝ Area — is Srednicki's asymptotic analysis, needing N-mode Williamson (a Mathlib-grade gap) + the
continuum limit. **General criterion (reusable): an increment is load-bearing only if the DERIVED side carries
non-vacuous content the carried geometry does not** — the heat-kernel a₁/prefactor pass; the area-law fails.
STOP for this vein.

**Numerical-`G` frontier — PRECISELY CHARACTERIZED (2026-07-05, consult-verified).** `G` is DERIVED as the
relation `G = 1/(N Λ_s²)` with the dimensionless content `G/a₀² = 1/N` a theorem (`InducedG`, §3) — `G` is an
output, not a carried input. What blocks the *numerical value* is exactly ONE piece, now named: the induced `1/G`
factorizes as `[(4π)^{-d/2}·Γ-factor·Λ²]_flat × [(1/6−ξ)·spin]_curved`; the flat bracket is already derived
(`heatDensity_oneD` = the `(4πt)^{-d/2}` prefactor, `cutoff_moment` = the `Λ²`) but feeds the a₀ vacuum-energy /
normalization, NOT the R-coefficient; the load-bearing number in every species `c_i` is the **`(1/6−ξ)` conformal-
coupling factor** — the R-term of the a₁ Seeley–DeWitt coefficient, which exists only because R≠0 and is a
coincidence-limit of the covariant heat-kernel expansion in Riemann normal coordinates. Mathlib at this pin has
**no Riemannian heat kernel, no Seeley–DeWitt recursion, and not even a stock Riemann tensor** (`ManifoldCurvature.lean`
notes this), so the `c_i` stay cited data. The gate is a specific multi-year library (a Riemannian heat kernel),
NOT a tractable increment; any flat-space `d`-general prefactor lemma would be buildable-but-DECORATIVE (wrong
coefficient / a refactor of the cited datum) — do NOT build it and bill it as sharpening `G`.

## 9. The honest one-paragraph scope (what the code supports)

QIQT-H's machine-checked content is: **a single-world (Φ,λ) interpretation with the Born rule REDUCED to one
named premise (P5/noncontextual-canonical-measure)** — not derived from unitarity; **a holographic ENTROPY bound
`S_vN ≤ A/4ℓ_P²` conditional on the finite-capacity postulate** over a Type III₁ matter algebra — where the
postulate has **two provably-distinct layers** (see §2): a finite record **count** `card R ≤ e^{A/4ℓ_P²}` in the
finite-dim model, and a finite **entropy** bound `S_vN + S_rel ≤ A/4ℓ_P²` in the continuum/Fork-A setting (the
`EntropyNotCardinality` no-go proves the entropy bound is *not* a count) — the finiteness is on
*records/entropy*, **never** a finite matter Hilbert space (D2/D3); **a genuine axiom-free one-particle Tomita–
Takesaki + crossed-product operator-algebra layer** (the *unconditional* one-particle Bisognano–Wichmann is a
real theorem; only the Type II trace is frontier); **a covariant record-selection layer** with the honest
`no_covariant_selector` and an **axiom-free boost-invariant typicality measure on the 1+1D free field**; **the
free-field SM content (CAR/gauge/stress-tensor) transported into the capacity corner**; **a complete axiom-free
formalization of the Lieb-concavity / DPI / strong-subadditivity tower** (a genuine contribution to formalized
mathematics, Mathlib-grade); and **a machine-checked re-derivation of the Sakharov 1/4 ratio and a conditional,
free-field Einstein equation** (standard induced-gravity/Jacobson physics, not unique to finiteness) — with the
value of `G`, formerly the one carried datum, now **promoted from carried to derived** as the *relation*
`G = 1/(N Λ_s²)` under the granularity reframing (§3 `InducedNewtonConstant`, [AF]): P4-MICRO's carried inputs
collapse to a single scale `Λ_s`, though the *numerical value* still needs the species-coefficient accounting
(frontier); **the complete free graviton** — linearized kinematics (exactly-2 via the gauge quotient, helicity ±2
as explicit eigenvalues), the propagator numerator + masslessness + the classical wave equation, and canonical
quantization (CCR/occupation/zero-point/coherent/two-point) — standard free-field QFT machine-checked, NOT quantum
gravity; and **the assembled linearized bridge** (`BRIDGE_PLAN.md`, 9/9): entanglement first law at every probe ⟺
linearized Einstein, from real parts (the graviton anchored to `δG=0 ⟺ k²=0`, coupling ⟺ conservation, Weinberg's
equivalence principle, forced wedge/ball Clausius data, proven-separating area probes) — CONDITIONAL on the
explicitly carried Clausius/area law, Iyer–Wald, BW/CHM, genericity, and `G` (ingredient D = the open frontier). "Finite
capacity" is a **finite record-*count*** statement in the finite-dim model and a **finite-*entropy*** statement in the
continuum/Fork-A setting (provably distinct — `EntropyNotCardinality`), **never** a finite-matter theory; its
load-bearing role is in the gravity/area thread, *not* the selection mechanism (`measure_needs_only_finiteness`).

**Net (the calibrated read, now full-coverage):** the *distinctive new physics* claim ("finite information as
fundamental") is the weakest part and should be scoped down to finite *entropy*. But the *genuine, substantial,
machine-checked* content is larger than a "repackaging" verdict implies: the **full formal verification at
~429-file / ~4,550-theorem scale**, the **Lieb-concavity/DPI/SSA tower** (Mathlib lacks it), the **unconditional
one-particle BW + the OP3b boost-invariant measure**, and the **Born reduction** are all real and unusual. The
honest framing is: *a rigorously machine-verified single-world interpretation + a substantial formalized
operator-algebra/entropy library + a re-derivation of induced-gravity results* — modest on novel physics, strong
on rigor and breadth.
