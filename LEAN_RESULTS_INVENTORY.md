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

- **~2263 `#print axioms` directives** in `QIQTH/AxiomAudit.lean`; **zero raw `axiom` declarations**, **zero
  `sorry`/`sorryAx`** in code. Budget-check (`scripts/axiom_budget_check.sh`) = **0**. The only `:= True` body in
  the whole tree is a harmless indiscrete-preorder witness (`LorentzWitness.lean:180`).
- **What "axiom-free" means here:** the *conditional/structural mathematics* rests on no hidden axiom. It does
  **NOT** mean the *physical postulates* are derived — the holographic-capacity bound, the KMS/Clausius inputs,
  P5, the value of `G`, etc. remain explicit **typeclass hypotheses / cited frontiers**, correctly labelled.
- **The budget GENUINELY DROPPED 57 → 0** via real discharge (each interface axiom either proved in a concrete
  finite model or recast as an explicit typeclass hypothesis), not relabeling. Verified across the Entropy/ tower
  (Donald/DPI/Araki/EntropyBridge ledger) and the top-level clusters (RelEntPositivity, Goldstein–Struyve).
- **What the budget check does NOT do:** detect logical inconsistency or a false premise (only counts axioms +
  catches `sorry`). Irrelevant at axiom count 0; honestly noted in-script.
- **Coverage caveat (full-sweep audit, 299 files):** soundness is comprehensive (full-tree grep: zero axioms,
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
  *derives given its inputs* (`G` fixed by the degree-count `N`; BH entropy as a boundary state count) vs what
  QIQT-H *carries* (`G` a free UV datum). Never cite it as a QIQT-H claim.
- **Holographic dictionary bridge — `QIQTH/HolographicBridge.lean`** (namespace `QIQTH.HolographicBridge`, [AF]
  std-3, NOT wired into `QIQTH.lean`/`AxiomAudit`). Connects the AdS/CFT comparison to the granularity reframing:
  `btz_cardy_eq_qiqth_capacity` — Strominger's BTZ `Cardy = A/4G`, evaluated with QIQT-H's induced `G=1/(N Λ_s²)`,
  equals QIQT-H's bulk **capacity exponent** `(A/4)N Λ_s²` (the boundary microstate count and the QIQT-H regional
  capacity are the *same quantity* at the shared granularity; the AdS radius `ℓ` cancels); `centralCharge_in_primitives`
  — the Brown–Henneaux `c=(3/2)ℓ N Λ_s²` *if* one posits a boundary length `ℓ` (AdS-specific, flagged). ⚠ A
  variable-**correspondence** showing the two languages are consistent under the shared `G` — it does **NOT** import a
  boundary CFT, the Cardy formula (needs a 2d Virasoro QIQT-H lacks), bulk reconstruction, or AdS/CFT's cross-check;
  QIQT-H's capacity stays postulated/granularity-reframed. A bridge, not a QIQT-H physics claim.

## 1. Born rule / typicality / single-world selection (Φ, λ)

- **Born is REDUCED, not derived from unitarity.** The probability content is carried by ONE irreducible premise:
  the noncontextual/positive effect-valuation (`EffectGleason.EffectMeasure`) — equivalently the canonicity of
  the typicality measure (P5). The code *proves this is irreducible*.
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
- `GaussianStateEntropy` **[AF]** per-mode Srednicki entropy; the **lattice area-law SCALING `S∝A` is [frontier]**.
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

## 4. Modular / crossed-product / Type II (more built-out than "finite shadows")

- **Genuine, axiom-free, UNBOUNDED machinery [AF]:** `Spectral.stoneGen_isSelfAdjoint` (unbounded Stone, via
  Gårding-mollifier density + deficiency indices — Mathlib lacks this); `PVM_of_selfAdjoint` (bounded);
  `boundedFC_mul` (bounded Borel FC multiplicativity); `fcOp` (unbounded `∫f dE`).
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

- **The Type II dual-weight TRACE `τ∘θ_s = e^{−s}τ` is the ONE genuine [frontier]** — not built; bridged by the
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
299-file / ~3300-theorem scale**, the **Lieb-concavity/DPI/SSA tower** (Mathlib lacks it), the **unconditional
one-particle BW + the OP3b boost-invariant measure**, and the **Born reduction** are all real and unusual. The
honest framing is: *a rigorously machine-verified single-world interpretation + a substantial formalized
operator-algebra/entropy library + a re-derivation of induced-gravity results* — modest on novel physics, strong
on rigor and breadth.
