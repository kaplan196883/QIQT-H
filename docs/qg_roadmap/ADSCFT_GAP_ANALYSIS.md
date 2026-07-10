# AdS/CFT gap analysis — what QIQT-H has and misses vs Maldacena's quantum geometry

**Date:** 2026-07-10. **Sources:** Maldacena, *The Large N Limit of Superconformal Field Theories and
Supergravity* (hep-th/9711200, `refs/arxiv_sources/conffo.tex`, read in full) × a detailed pass of
`LEAN_RESULTS_INVENTORY.md` (the graviton stack, the bridge, the operator-emergence and Keystone/JoinInstance
campaigns, the Lorentz gates). Supersedes any earlier informal statement that "QIQT-H has no graviton" —
that was WRONG; the corrected inventory-verified position is below.

## 1. The five load-bearing mechanisms of AdS/CFT (from the paper itself)

- **M1 — an independently defined microscopic theory.** N=4 SYM exists first: a complete, unitary,
  non-gravitational QFT. Gravity is then *found inside it*: "it includes in its Hilbert space the states of
  type IIB supergravity… in particular the theory contains gravitons."
- **M2 — a derivation engine.** The decoupling limit: ONE physical system (N D3-branes), TWO descriptions
  (gauge theory / near-horizon supergravity); α′→0 keeps both alive — the identification is *forced*.
- **M3 — a Lorentz-scalar capacity quantum number.** N is a flux/rank integer; geometry size in Planck
  units ∝ N^{1/4}; the radius is quantized because the 5-form flux is quantized; 1/N = quantum-gravity
  effects (Hawking radiation is a 1/N effect).
- **M4 — scale as an emergent dimension.** U = energy scale, radial motion = RG flow; states ↔ geometries
  (vacuum ↔ AdS, thermal ↔ black hole, Higgsing ↔ multi-center metric).
- **M5 — symmetry protection.** Superconformal group = AdS isometries; non-renormalization theorems pin the
  dictionary's coefficients quantitatively.

## 2. What QIQT-H already has (inventory-verified, all [AF] std-3 unless noted)

**The graviton stack — this exists and is substantial:**
- Kinematics (G11a–c, `EmergentDynamics.lean`): TT polarizations, helicity ±2 as explicit eigenvalues,
  the D(D−3)/2 = 2 count via the gauge quotient, the physical-state projector (= the harmonic-gauge
  propagator numerator), masslessness, and classical wave propagation at c.
- **The quantized free graviton** (Q1–Q6, `GravitonQuantization.lean`): the two helicity modes as a genuine
  Fock representation of the CCR (Bargmann–Fock), number/Hamiltonian/helicity operators, zero-point energy,
  ladder + coherent states, two-point function.
- **The GR anchor** (`LinearizedEinstein.lean`): full linearized Einstein tensor, gauge invariance, the
  Bianchi identity; `graviton_solves_linearized_einstein` AND the converse (`δG = 0 ⟺ k² = 0` — Einstein
  forces propagation at c). The quantized graviton IS provably the graviton of general relativity
  (linearized).
- **The equivalence principle** (`SoftGraviton.lean` B2a/B2b): longitudinal decoupling ⟹ Weinberg sum
  rule ⟹ universal coupling — Weinberg's theorem at the algebraic level, end-to-end.
- **Self-consistency** (`DeserRung.lean` E5 + `FormalDeser.lean` J4): the graviton sources itself
  gauge-consistently at second order; formal conservation-propagation of the Deser bootstrap (the nonlinear
  Einstein coefficients = cited frontier).
- **Quantized geometry, honestly quantified** (`OperatorEmergence.lean` Q1–Q5): the metric OPERATOR ĥ
  reconstructed from its own quantized area observables; `[Â(Σ), Π̂(Σ′)] = i·areaPair` (equal-time areas
  commute — the honest structure); the vacuum's area two-point function; the operator wave equation;
  coherent states = classical geometries (the classical emergence map is the coherent shadow) — so geometry
  superpositions DO exist at the linearized free level (superpose coherents in Fock).
- **The count ⟷ geometry join as theorems** (Keystone K0–K6 + JoinInstance JI1–JI7): in the constructed
  crossed-product core the calibration (`wEntTau_eq_log_tau0Dim`) and the join (`Stau_eq_area_over_4G`)
  are THEOREMS — `S_τ = (A₀ + δA)/4G` with nothing carried in that branch; `Stau_eq_capacity_primitives`
  meets the induced-G normalization (`S_τ = (A/4)NΛ_s²`). Walls 1–5 named (continuum algebras, external
  area matching, Type III₁/II∞, normal weights, value of G).
- The bridge capstone (`BridgeAssembly.lean`): entanglement first law at every probe ⟺ linearized vacuum
  Einstein, with every derived piece a theorem and every physical input a named hypothesis
  (Clausius/area law, Iyer–Wald→hDeficit, BW/CHM — the latter substantially shrunk by the
  transport/grounding campaigns).

**The M3 slot (capacity):** the Lorentz gates (2026-07-02) forced finite capacity to be a state-level
Lorentz scalar — structurally the same slot as Maldacena's N (an internal rank, never a frame cutoff;
AdS/CFT is the existence proof that this surviving branch can be a real theory). `inducedG_mul_N`
(`G·N = 1/Λ_s²`) is the analogue of `1/G ∝ N²`; `btz_cardy_eq_qiqth_capacity` is the correspondence-level
check (two holographic bookkeepings agree under shared G).

**The AREA LAW is DERIVED, not postulated (correction, 2026-07-10 — supersedes any "the holographic bound
is branding/input" framing, which predates the SG/DS/JI theorem layer).** The bound's physical *value*
(`Q_R = A/4ℓ_P²` as nature's number) and the area *law* (S∝A with the 1/4G structure) are different
claims; the second is a theorem, in three independent machine-checked senses:
1. **The form is FORCED** (`forced_weight_product` + `finiteCorner_valuation_rigidity`, DS6/DS7): any
   monoidal, embedding-monotone, refinement-natural area valuation MUST be `κ·Σ log D_e` — the
   logarithmic boundary-additive form of the area law is a rigidity theorem of information composition
   (ν₂ counterexample proving the hypotheses necessary); only κ (the 4G slot) is a normalization.
2. **The scaling is PROVED, with the guard proving the premise load-bearing**
   (`boundary_entropy_area_law` + `bulk_entropy_volume_law`): the boundary-local Gaussian model provably
   has S = (A/a₀²)·s₀, while the SAME modes provably give a VOLUME law unless boundary-localized — the
   theorem pair isolates boundary locality as exactly the property producing area scaling (not circular).
3. **The full S = A/4G is a theorem in the constructed core with nothing carried in that branch**
   (`wEntTau_eq_log_tau0Dim` — the calibration IS a theorem; `Stau_eq_area_over_4G`,
   `K2b_tau0_capstone`): count and geometry as two computations of one number, the join by construction
   ("no hClausius/hGeom/hCalib/hJoin carried in this branch").
The honest residue is NOT the area law but its physical instantiation: that nature's vacua realize the
boundary-local structure (F1 — Srednicki's free-scalar vacuum area law not formalized), the external
geometric area = the count-built area (Wall 2), and Λ_s (F3). Net: QIQT-H is a candidate *explanation*
of the weak holographic principle — capacity composes logarithmically and records live on boundaries ⟹
S∝A — rather than an importer of it; what it still lacks is the STRONG principle (boundary dynamics
generating the bulk), which is gaps 1–2 below.

**The M4 shadow:** state-decoded geometry (cut-rank → metric → GH limit), graph-RT/min-cut, flow/cut
duality, and the Lorentzian target-side (τ, reverse triangle, dS₂).

**Plus one thing AdS/CFT does not have:** a machine-checked assumption ledger. Nobody has formalized any
of AdS/CFT; every carried hypothesis here is named in Lean.

## 3. The genuine gaps, ranked — each VERIFIED against the Lean sources (searched 2026-07-10)

1. **[vs M1] The graviton is quantized by hand, not found in the spectrum — and the repo PROVED the finite
   obstruction.** Our graviton is the canonical quantization of the linearized field on a flat background
   — constructed directly, not discovered as a composite excitation of an independently defined
   non-gravitational theory. The join between the code and the graviton is expectation-level, and the
   inventory records the theorem-level reason: **the finite-code CCR isometry is obstructed by the trace
   argument — the code Hilbert space is NOT Fock, "expectation-level FOREVER" at fixed finite capacity.**
   This is exactly where Maldacena's N→∞ enters: the CFT contains gravitons only in the large-N limit,
   where the Hilbert space is big enough (Type-III/infinite-dimensional) to carry an approximate graviton
   Fock sector. **The missing object = the large-capacity limit in which the record/code theory develops
   the graviton sector inside itself** — the same wall as Walls 1–5 (continuum, Type III₁) and the
   dynamical source, seen from the AdS/CFT side.
   *Lean-verified status: the wall STANDS but is actively LADDERED, far beyond what an earlier draft
   credited* — the von Neumann **double-commutant theorem** is an axiom-free Lean theorem (C1–C11, a
   genuine Mathlib gap closed, WOT = SOT = A″), the crossed product `M⋊_σℝ` and directed-union limit are
   packaged as genuine `VonNeumannAlgebra`s, the tower-GNS representation is complete (R9), the Type II
   dual-weight trace holds on the algebraic core (W1–W4: exact scaling `τ∘θ_s = e^{−s}τ`, traciality,
   positivity; vN extension carried non-vacuously), and the code's Gibbs tower carries a machine-checked
   **Araki–Woods III₁ fingerprint** (T1–T8, with the Powers-guard separation and a hypothesis-free √2
   instance; the inference to an actual III₁ factor cited, never claimed). What remains missing is the
   limit ALGEBRA itself (ITPFI factor, type classification, normal weights) and the graviton sector
   inside it.
2. **[vs M2] The derivation engine — PARTIALLY BUILT, at the honest finite level.** An earlier draft said
   "no derivation engine"; that was too strong. **The Decoupling Shadow campaign (DS1–DS7 COMPLETE,
   `QIQTH/Decoupling/`)** formalizes the finite forced core of Maldacena's structure — *one parent, two
   surviving descriptions of one limit*: (i) the free-oscillator sector is FORCED by the cutoff limit
   (CCR matrix elements stabilize, `commutator_eventually_exact`; thermal data → the Planck values; the
   truncation defect dies); (ii) the dictionary's local weight is RIGID (`forced_weight_product`: any
   monoidal, embedding-monotone, refinement-natural area valuation is `κ·Σ log D_k` — with the `ν₂`
   counterexample proving the hypotheses necessary); (iii) the saturated area law survives given the κ
   (= 4G) normalization; plus the REGIME-SEPARATION GUARD (`guard_defect_survives`: saturated capacity is
   provably NOT the positive-temperature free limit — the two decoupling halves live in different regimes,
   as a theorem). The DS7 checkpoint states the honest boundary verbatim: the capacity limit forces the
   free sector only; **it does not force the screen geometry or Newton constant** — the strong half of
   Maldacena's argument (the geometry side surviving the SAME limit, i.e. the actual duality) is the
   remaining gap. `AdSCFTComparison.lean` (a labelled comparison artifact, deliberately unwired) pins what
   AdS/CFT still uniquely has: ONE microscopic system computing both `G` and the microstate count, so
   `S = A/4G` is a consistency theorem of a single theory rather than two bookkeepings calibrated to
   shared primitives.
3. **[vs M5→M1] Interactions and the nonlinear/quantum completion — VERIFIED ABSENT beyond Deser order 2.**
   Deser order 2 is a theorem (E5); beyond is formal conservation-propagation with one carried coefficient
   identity (J4); the interacting quantized graviton and matter loops do not exist in the repo. (In
   AdS/CFT the full interacting theory is the definition.)
4. **[vs M4] No emergent scale-dimension — stands, with the RT substrate now UNCONDITIONAL.** The decoded
   geometries are spatial and single-scale; the holographic radial direction — entanglement-at-all-scales
   becoming a dimension, U = RG scale — has no theorem. The closest built pieces: **`maxFlow_min_cut`
   (M1–M12 COMPLETE, unconditional finite max-flow = min-cut — a genuine wall fully crossed, not in
   Mathlib) feeding `exact_rt_unconditional`** (exact RT optimality on the finite network model), and
   `LambdaRG_invariant` (discrete RG dimensional transmutation — a relation, not the value of G). These
   give the bulk-reconstruction SUBSTRATE (entanglement = min-cut geometry, exactly) but not the
   scale-as-dimension theorem.
5. **[vs M5] No protection — VERIFIED ABSENT.** Searched: no non-renormalization/protected-quantity
   content exists (the held Ward identities — soft-graviton, speed-splitting — are consistency
   conditions, not protection). This is why `N_eff/4`, `Λ_s`, and the heat-kernel `c_i` stay unpinned and
   the induced-G story sits at its natural ceiling, while Maldacena's dictionary is quantitatively rigid
   (probe actions fixed by symmetry).
6. **[vs M3] One relation, not a 1/N tower — VERIFIED ABSENT.** `G = 1/(NΛ_s²)` and
   `S_τ = (A/4)NΛ_s²` are held; no systematic 1/N expansion (quantum-gravity corrections organized order
   by order — Hawking radiation as a 1/N effect), no backreaction, no topology change.

## 4. The verdict (one sentence, corrected after the Lean sweep)

QIQT-H holds the *kinematic and algebraic* layers of a holographic correspondence — the gate-surviving
N-like scalar capacity, G ∝ 1/N, the linearized quantized graviton provably of GR with the equivalence
principle and quantized area fluctuations, the count ⟷ geometry join as theorems in the constructed core,
the WEAK half of the decoupling argument as theorems (free sector forced + the rigid weight dictionary),
unconditional exact RT on the finite flow model, and the machine-checked ladder up to the Type III₁
fingerprint — but misses what makes AdS/CFT a *duality*: the STRONG half of decoupling (the geometry/G
side surviving the same limit from one parent), the limit algebra in which the graviton sector lives
inside the theory (blocked at finite capacity by the repo's own trace-argument obstruction — the
large-capacity limit IS the missing step), the interacting/nonlinear completion, the scale-as-dimension
theorem, the protection that pins coefficients, and any 1/N tower.

## 5. Constructive closing note

Maldacena's final page names "relate Euclidean CFTs to de Sitter spacetimes" as the open extension — still
unsolved. The repo's L4 (dS₂ τ-structure) is target-side work on exactly that corner. And the sharpest
repo-native reformulation of gap 1: **find the limit (capacity → ∞ with the right scaling) in which the
expectation-level join of `code_count_eq_fock_area_expect` upgrades to an approximate CCR isometry** —
the finite trace obstruction tells you precisely what must diverge and how. That is a theorem-shaped
question, in the repo's own language, whose answer in AdS/CFT is "N → ∞ at fixed g·N".

## 6. POST-RC UPDATE (2026-07-10, same day — after the boundary-dynamics campaign)

The RC campaign (`RC_CAMPAIGN_PLAN.md`: RC1 `73fd89c4` + RC2 `ef64ea39` + RC3 `a63c9b73`, all [AF]
std-3) moved **gap 1's M1 prerequisite** — and only that. Revised status:

- **Gap 1 [vs M1] — the boundary side is no longer a ledger; it is an OPEN QUANTUM SYSTEM.** Before
  RC, the "independently defined microscopic theory" column had bookkeeping plus a free diagonal flow
  that provably freezes records (`alpha_diagonal`). Now the boundary has: a dissipative semigroup
  under which records FORM (exponential convergence to the readout), a second law WITH its equality
  case (production zero ⟺ record, Klein faithfulness), equilibria that are dynamically characterized,
  Lyapunov-STABLE, and (E4-conditionally) linearized-Einstein
  (`boundary_dynamics_equilibria_are_geometry`), and a single-world stochastic layer: the channel is
  EXACTLY the λ-average of a Born-jump process, with the Born weights FORCED given the channel
  (`unraveling_exact`, `unraveling_weights_unique`). In Maldacena-comparison terms: the boundary
  theory now has its thermalization/decoherence sector as theorems — the analogue of knowing the
  boundary system relaxes to the thermal (black-hole-dual) states. **What gap 1 still needs, sharpened
  by RC:** (i) the INTERACTING upgrade — a unitary coupling from which the record basis and the
  dephasing EMERGE (einselection derived, not inserted; the pointer basis is RC1's named input);
  (ii) the capacity → ∞ limit in which the code carries an approximate graviton CCR (the trace
  obstruction stands untouched); (iii) with (i)+(ii), the graviton found INSIDE the spectrum. The
  three are really one composite object: a genuine interacting microscopic theory with a controlled
  large-capacity limit — i.e., the CFT slot.
  **IC1 update (2026-07-11, `0f2f23b0`): component (i) has its FIRST BRICK.** The pure-dephasing
  interacting model derives the record basis from the coupling (`timeAvg_reduced_tendsto_dephase`:
  the Cesàro average of the interacting reduced dynamics IS the record channel, in A's eigenbasis;
  uniqueness + necessity guard). Einselection is no longer inserted — at the time-averaged level,
  in the measurement limit. Still open within (i): the self-Hamiltonian competition
  (`[H_S, A] ≠ 0`); and (ii)+(iii) — the capacity → ∞ limit and the graviton inside — are untouched.
- **Gaps 2–6: unchanged today** (strong-half decoupling; interactions beyond Deser-2;
  scale-as-dimension; protection; 1/N tower).

**Distance, honestly quantified by mechanism:** M3 (scalar capacity ↔ N): relation held, tower
missing. M1 (boundary theory): first rung BUILT (dynamics + thermodynamics + single-world layer),
interacting core + limit missing. M2 (derivation engine): weak half theorems, strong half missing.
M4 (scale-dimension): substrate unconditional (exact RT), theorem missing. M5 (protection): nothing.
The remaining distance is concentrated in ONE composite object — the interacting boundary theory
with its large-capacity limit — everything else is scaffolded, shadowed, or first-rung-built around
it.

## 7. THE STRONG-PRINCIPLE PROXIMITY LEDGER (2026-07-11, post-IC1 — the calibrated answer to
## "are we close to the strong holographic principle?")

The strong principle = a boundary theory whose dynamics GENERATES the bulk. Decomposed into its
requirements, with verified status:

| Requirement | Status |
|---|---|
| A boundary theory that EXISTS (states + dynamics) | ✅ BUILT (RC1–IC1): open quantum system — free flow + record channel, second law with rigidity, derived pointer basis (Cesàro), Born-jump unraveling with Born forced |
| Its equilibria are the geometric states | ✅ BUILT, conditional: stationary ∧ Lyapunov-stable ∧ linearized-Einstein (`boundary_dynamics_equilibria_are_geometry`; E4's carried BW/Iyer–Wald inputs) |
| The weak principle (S = A/4G as LAW) | ✅ DERIVED (§2: rigidity + boundary-Gaussian + constructed-core join) |
| An INTERACTING boundary theory | 🟡 first brick only — IC1 is the measurement limit; `[H_S, A] ≠ 0` pointer competition open |
| The graviton INSIDE the boundary Hilbert space | ❌ blocked at finite capacity by the trace-obstruction theorem; needs capacity → ∞ — the core of the CFT slot |
| Boundary evolution generating BULK TIME EVOLUTION | ❌ statics only ("equilibria are geometry"), not dynamics ("boundary relaxation = bulk motion") |
| The radial/scale dimension | ❌ substrate only (exact RT unconditional); no scale-as-dimension theorem |

**The calibrated statement:** the boundary side has crossed from "no candidate theory" (a ledger) to
"a boundary proto-theory with the right statics and thermodynamics" — roughly two rungs up a ladder
whose remaining height contains the genuinely hard physics: the interacting completion, the
large-capacity limit dissolving the trace obstruction (which Maldacena received from string theory
for free — N=4 SYM predated the duality), the graviton found inside, and bulk dynamics from
boundary dynamics. None of today's theorems should be read as PROXIMITY to the strong principle;
they are the first machine-checked evidence that QIQT-H's version of it is CONSTRUCTIBLE rather
than merely conjecturable — the remaining distance is, for the first time, theorem-shaped.

**The nearest reachable rung (named, composable from held pieces):** the STATICS → DYNAMICS upgrade.
The repo holds the area decoder (`reconstruct`/`reconstruct_areaVar`), the RC relaxation flow
(`Tsem`), and the first-law bridge — so the theorem "the boundary relaxation trajectory `T_s ρ`
induces, through the area probes, a TRAJECTORY of emergent metric perturbations `h(s)`, with its
evolution law inherited from the flow" is composable without new machinery. That would be the first
machine-checked instance of boundary dynamics driving bulk geometry IN TIME — small, honest, and
exactly on the strong-principle axis. (Not yet built; the named candidate next brick.)

⚠ Scope firewall: this document compares architectures; it claims no new physics, no derivation of a
duality, and does not modify any result's honest labels. NOT QG.
