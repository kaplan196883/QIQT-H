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

- **~2213 `#print axioms` directives** in `QIQTH/AxiomAudit.lean`; **zero raw `axiom` declarations**, **zero
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
- **Coverage caveat (full-sweep audit, 296 files):** soundness is comprehensive (full-tree grep: zero axioms,
  zero sorry). The `#print axioms` *audit pins* most theorems but **~55 modules' terminal theorems are not
  individually listed** (e.g. `SakharovRatio`, `strong_subadditivity`, the GR/crossed-product capstones,
  `ValueSelection`). Low soundness risk (`#print axioms` is transitive — any lemma feeding an audited downstream
  theorem is certified), but a real completeness gap for terminal results. **Stale docstrings** that *under*-claim
  (say "axiomatized" for now-proved results): `ArakiInterface`, `RelEntPositivity`, `GoldsteinStruyve*` headers,
  and `AxiomAudit.lean:~4882–4897, ~216–220` (clock-energy self-adjointness, GS steps). Hygiene, not soundness.

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

- `area_floor_vonNeumann` **[AF·cond: HolographicCapacityBound]** — `S_vN(ρ_R) ≤ areaTerm`. **A von Neumann
  ENTROPY bound.** `HolographicCapacityBound`'s field is `log(card R) ≤ areaTerm`; its header states `R` is the
  **operational/regional capacity `Q_R = log N_R`, NOT a global Hilbert-space dimension**, and the matter algebra
  is **Type III₁** (the finite-dim `R` is itself the holographic regularization). `areaTerm = A/4ℓ_P²` is a
  **carried UV datum, never assigned**.
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
- **The Type II dual-weight TRACE `τ∘θ_s = e^{−s}τ` is the ONE genuine [frontier]** — not built; bridged by the
  non-vacuous `Phase5Master` interface (never an axiom). Also frontier: vN double-commutant closure of the crossed
  product; full vN-algebra (vs one-particle) relative entropy via `Γ(Δ^{it})`; continuum Type III₁ classification.
- Araki/Umegaki relative entropy **[AF]** finite-dim (Type I shadow); `ModularRelativeEntropy.cgpEntropy` is the
  **genuine continuum one-particle** CGP entropy with `cgpEntropy_nonneg` **[AF·cond: ξ∈𝒦, spectral bounds]**
  (all-vector positivity is FALSE — honestly noted).

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
  entropy. **Hygiene gap:** `strong_subadditivity` / `condMutualInfo_nonneg` are sorry-free but **not yet in
  `AxiomAudit.lean`** (add `#print axioms`).

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
`S_vN ≤ A/4ℓ_P²` conditional on the finite-capacity postulate** over a Type III₁ matter algebra (the finiteness
is on *entropy/records*, not a finite matter Hilbert space — D2/D3); **a genuine axiom-free one-particle Tomita–
Takesaki + crossed-product operator-algebra layer** (the *unconditional* one-particle Bisognano–Wichmann is a
real theorem; only the Type II trace is frontier); **a covariant record-selection layer** with the honest
`no_covariant_selector` and an **axiom-free boost-invariant typicality measure on the 1+1D free field**; **the
free-field SM content (CAR/gauge/stress-tensor) transported into the capacity corner**; **a complete axiom-free
formalization of the Lieb-concavity / DPI / strong-subadditivity tower** (a genuine contribution to formalized
mathematics, Mathlib-grade); and **a machine-checked re-derivation of the Sakharov 1/4 ratio and a conditional,
free-field Einstein equation** (standard induced-gravity/Jacobson physics, not unique to finiteness). "Finite
capacity" is honestly a **finite-entropy/holographic** statement, **not** a finite-matter theory; its
load-bearing role is in the gravity/area thread, *not* the selection mechanism (`measure_needs_only_finiteness`).

**Net (the calibrated read, now full-coverage):** the *distinctive new physics* claim ("finite information as
fundamental") is the weakest part and should be scoped down to finite *entropy*. But the *genuine, substantial,
machine-checked* content is larger than a "repackaging" verdict implies: the **full formal verification at
296-file / ~3300-theorem scale**, the **Lieb-concavity/DPI/SSA tower** (Mathlib lacks it), the **unconditional
one-particle BW + the OP3b boost-invariant measure**, and the **Born reduction** are all real and unusual. The
honest framing is: *a rigorously machine-verified single-world interpretation + a substantial formalized
operator-algebra/entropy library + a re-derivation of induced-gravity results* — modest on novel physics, strong
on rigor and breadth.
