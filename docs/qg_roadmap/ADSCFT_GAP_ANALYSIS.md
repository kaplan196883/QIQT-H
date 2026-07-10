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

**The M4 shadow:** state-decoded geometry (cut-rank → metric → GH limit), graph-RT/min-cut, flow/cut
duality, and the Lorentzian target-side (τ, reverse triangle, dS₂).

**Plus one thing AdS/CFT does not have:** a machine-checked assumption ledger. Nobody has formalized any
of AdS/CFT; every carried hypothesis here is named in Lean.

## 3. The genuine gaps, ranked (each stated against the mechanism it blocks)

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
2. **[vs M2] No derivation engine.** There is no "brane" — no single object with two descriptions whose
   common limit forces a duality. Everything held is correspondence-checking (Cardy = capacity) or
   conditional assembly, never a two-descriptions-of-one-system derivation. This is the difference between
   a *dictionary* (held, partially as theorems) and a *duality* (not held).
3. **[vs M5→M1] Interactions and the nonlinear/quantum completion.** Deser order 2 is a theorem; beyond
   is formal propagation with one carried coefficient identity; the interacting quantized graviton and
   matter loops do not exist in the repo. (In AdS/CFT the full interacting theory is the definition.)
4. **[vs M4] No emergent scale-dimension.** The decoded geometries are spatial and single-scale; the
   holographic radial direction — entanglement-at-all-scales becoming a dimension, U = RG scale — has no
   theorem (graph-RT is the closest toy).
5. **[vs M5] No protection.** No supersymmetry/non-renormalization analogue pins coefficients — the reason
   `N_eff/4`, `Λ_s`, and the heat-kernel `c_i` stay unpinned and the induced-G story sits at its natural
   ceiling, while Maldacena's dictionary is quantitatively rigid (probe actions fixed by symmetry).
6. **[vs M3] One relation, not a 1/N tower.** `G = 1/(NΛ_s²)` and `S_τ = (A/4)NΛ_s²` are held; the
   systematic 1/N expansion (quantum-gravity corrections organized order by order — Hawking radiation as
   a 1/N effect), backreaction, and topology change are absent.

## 4. The verdict (one sentence)

QIQT-H holds the *kinematic and algebraic* layers of a holographic correspondence — the gate-surviving
N-like scalar capacity, G ∝ 1/N, the linearized quantized graviton provably of GR with the equivalence
principle and quantized area fluctuations, the count ⟷ geometry join as theorems in the constructed core,
and geometry-recovery limits up to dS₂ — but misses everything that makes AdS/CFT a *duality*: an
independently defined microscopic theory whose spectrum contains the graviton (blocked at finite capacity
by the repo's own trace-argument obstruction — the large-capacity limit IS the missing step), a
decoupling-style derivation, the interacting/nonlinear completion, the emergent radial dimension, and the
protection that pins coefficients.

## 5. Constructive closing note

Maldacena's final page names "relate Euclidean CFTs to de Sitter spacetimes" as the open extension — still
unsolved. The repo's L4 (dS₂ τ-structure) is target-side work on exactly that corner. And the sharpest
repo-native reformulation of gap 1: **find the limit (capacity → ∞ with the right scaling) in which the
expectation-level join of `code_count_eq_fock_area_expect` upgrades to an approximate CCR isometry** —
the finite trace obstruction tells you precisely what must diverge and how. That is a theorem-shaped
question, in the repo's own language, whose answer in AdS/CFT is "N → ∞ at fixed g·N".

⚠ Scope firewall: this document compares architectures; it claims no new physics, no derivation of a
duality, and does not modify any result's honest labels. NOT QG.
