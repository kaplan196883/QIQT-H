# The Bridge — assembling the emergent, universally-coupled, linearized graviton

**Status:** ACTIVE (2026-07-02). **GPT-5.5-pro-VERIFIED: RECOMMEND IMPLEMENTATION** (with the required edits — all
applied below). **Goal:** build the *bridge* between QIQT-H's two completed sides — the **graviton-as-a-particle**
(the quantized free graviton, Q1–Q6 + kinematics G11a–c) and the **mechanism** (the holographic screen code + the
modular/entanglement machinery) — by assembling the **entanglement → linearized-Einstein** template (Van Raamsdonk;
FGHMVR 2013; Jacobson 2015) from the concrete pieces QIQT-H already holds.

**Background (explicit, per the verification):** this is a **flat-space, Jacobson-style linearized bridge** —
`minkMetric`, null plane waves, `□h = 0`. It is NOT literal AdS/FGHMVR (that residual would carry cosmological-constant
terms); the FGHMVR *logical skeleton* (G1) is background-agnostic and is what gets instantiated.

## ⚠ HONEST SCOPE (read first — the load-bearing verdict)

**This plan does NOT solve quantum gravity and does NOT claim to.** The bridge in *full* = an **emergent** +
**universally-coupled** + **interacting** + **background-independent** graviton derived from the substrate. This plan
builds only the **linearized, first-order, free-field** skeleton — ingredients **A, B, C** — as a **conditional
assembly**: theorem schemas over EXPLICIT physical inputs, never derivations from the free graviton alone. The carried
physical inputs (each a structure field / theorem hypothesis, NEVER a Lean axiom): the **Clausius/area law**
`δS = δA/4G = δ⟨K⟩` (the one irreducible input), **CHM conformal compatibility**, the **Iyer–Wald identity**, the
**separating probe family**, and the **value of `G`** (species). Removing those is ingredient **D** = the open
quantum-gravity problem (out of scope / unformalized here — background independence, the nonlinear/second-order
completion (known conditional derivations exist, e.g. Faulkner et al 2017 — not built here), the UV, the microstate
derivation of `S=A/4G`). **Never claim QG solved, the mechanism gap closed, the area law derived, universal `G`
derived, or background independence.** Every theorem: NO `sorry`; `#print axioms` std-3; budget 0; honest labels.

## What the bridge needs, and what QIQT-H already holds

| Ingredient | Physics | Held (verified) | Gap to build |
|---|---|---|---|
| **A** emergence: area↔graviton | `h_{μν}` anchored to linearized GR; area variation a functional of `h` | graviton Q1–Q6; `h_{μν}` + 2 helicity pols; `physProj`; screen `screenArea`; `kUp_null`; `graviton_null_wave` | the full `G⁽¹⁾` anchor + the supplied `δA(h)` functional |
| **B** universal coupling | massless spin-2 + Lorentz + soft factorization ⟹ universal coupling (Weinberg 1964–65) = equivalence principle | masslessness `kUp_null`; helicity ±2 | `hT` gauge-invariance ⟺ `∂T=0`; the soft Ward identity + universality lemma |
| **C** modular→geometric | wedge `K` = weighted boost energy (BW); ball `K` via CHM (conformal) | free-field modular flow DONE (`modK`, `Δ^{it}=e^{−itK}`, `hasDerivAt_inner_modUnitary` derived); Sakharov 1/4 | C1 packaging; the CHM ball kernel under a `CHMCompatible` hypothesis |
| **D** — OUT OF SCOPE / unformalized | background independence · nonlinear/2nd-order completion · UV · area law from counting · value of `G` | — | not this plan; cited, never claimed |

## Increments (GPT-5.5-pro-recommended order; each axiom-free, green, one commit)

- [x] **A1 — the full linearized Einstein anchor ✅** (`QIQTH/LinearizedEinstein.lean`, `QIQTH.LinEinstein`, all [AF]
  std-3, wired + pinned, budget 0; sign conventions documented in the header, `linEinsteinCoeff` = the physical
  coefficient). The **full flat-background linearized Einstein tensor** in plane-wave-symbol form (`∂ → k` exactly
  per mode): `ricciSymbol`/`einsteinSymbol` defined for **every** `(k, e)` (the ASM `residual`).
  **`einsteinSymbol_gauge`**/`ricciSymbol_gauge` — pure gauge `e = k⊙ξ` ⟹ `δG = 0` *identically* (any `k`;
  linearized diffeo invariance). **`bianchi_einsteinSymbol`** — the **linearized Bianchi identity** `k^μ(δG)_{μν}=0`
  identically (every `k, e`; the structural engine behind B1-conservation and the G7b `φ`-removal).
  **`einsteinSymbol_tt`** — TT ⟹ `δG = (−k²/2)•e` (the reduction "δG = −½□h", tying to G11c `graviton_null_wave`).
  **`graviton_solves_linearized_einstein`** — null `kDown` + the quantized graviton's polarization content
  `a•e₊+b•e×` ⟹ `δG = 0`: **the field quantized in Q1–Q6 provably solves linearized vacuum Einstein — it IS the
  graviton of GR.** **`einsteinSymbol_eq_zero_iff_massless`** + **`einstein_iff_dispersion`** — the converse: for
  nonzero TT, `δG = 0 ⟺ k² = 0 ⟺ ω² = κ²` (Einstein *forces* light-cone propagation). ⚠ Linearized, vacuum, free,
  flat. (An initial thinner duplicate `BridgeLinearizedGR.lean` was consolidated into this richer module.)
- [x] **B1 — coupling ⟺ conservation ✅** (`QIQTH/MatterCoupling.lean`, `QIQTH.MatterCoupling`, all [AF] std-3,
  wired + pinned, budget 0). `couple e T = ∑ e_{μν}T^{μν}` (the symbol of `∫h·T`), `divT k T ν = k_μT^{μν}` (the
  symbol of `∂_μT^{μν}`). **`couple_gauge`** — the gauge variation of the coupling is exactly `2∑ ξ_ν(k_μT^{μν})`
  (symmetric `T`; proved by `linear_combination` over the 6 symmetry relations).
  **`couple_gauge_invariant_iff_conserved`** — **THE IFF**: the coupling is gauge invariant for every `(e, ξ)` ⟺ the
  stress-energy is conserved. **The Bianchi payoff:** `einstein_source_conserved` — the raised linearized Einstein
  tensor is *identically* conserved (via A1's `bianchi_einsteinSymbol`), so `source_conserved_of_einstein_eq` — any
  `T` sourced by `δG^{μν} = κT^{μν}` is AUTOMATICALLY conserved: the geometry side forces exactly the conservation
  law the coupling side demands. The linearized consistency triangle closes. ⚠ Linearized; free ≠ interacting;
  universality is B2; `κ`/`G` carried.
- [ ] **C1 — the wedge modular Hamiltonian is the weighted boost.** Package the DONE free-field results as: `K_wedge`
  generates the geometric boost with the **Rindler weight** (`K = 2π∫_{x¹>0} x¹ T_{00}` schematically — the weighted
  boost energy, NOT an unweighted `2π∫T_kk`), using exactly the existing derived theorem
  (`hasDerivAt_inner_modUnitary` = the modular-derivative datum) + the BW identification (carried hypothesis #3 of
  `WedgeKMSFlux`). Honest: the *weight formula* is packaged at the level the existing theorems support.
- [ ] **A2 — the emergence map (supplied geometric functional).** The linearized area variation
  `δA_Σ(h) = ½∫_Σ √γ γ^{ab} e_a^μ e_b^ν h_{μν}` (finite/discretized form) as a SUPPLIED functional of `h` — wire
  `δ(screenArea)` to it. Area is a functional of `h`, NOT the full metric data: any reconstruction claim requires a
  **separating family** of surfaces (a carried hypothesis, exactly like G1's probes). Deriving the map is D.
- [ ] **B2a — the soft Ward identity.** Finite algebraic core: the soft factor `∑_i η_i g_i (p_i·ε·p_i)/(p_i·q)`
  (incoming/outgoing signs `η_i`); longitudinal decoupling `ε_{μν} → ε_{μν} + q_μξ_ν + q_νξ_μ` forces
  **`∑_i η_i g_i p_i^μ = 0`**. NOT the full analytic soft theorem — the algebraic identity only.
- [ ] **B2b — universality on connected components.** Given momentum conservation `∑_i η_i p_i^μ = 0` and a
  sufficiently rich connected scattering family (carried hypothesis), `∑_i η_i g_i p_i^μ = 0` at generic momenta
  forces **all `g_i` equal** on each connected species component — the equivalence principle as a finite theorem.
- [ ] **C2a — the ball conformal Killing vector algebra.** The CHM kernel weight `(R² − |x|²)/2R` and its conformal
  Killing structure on the ball — the finite geometry (`K_B = 2π∫_{|x|<R} ((R²−|x|²)/2R) T_{00}` schematically).
- [ ] **C2b — conditional CHM transport.** Under a **`CHMCompatible`** hypothesis (conformal covariance — CHM is a
  CFT-vacuum statement, NOT generic QFT and not automatic for the free graviton), transport the wedge modular
  Hamiltonian to the ball: `δ⟨K_ball⟩` geometric — the input G1 consumes at every ball. Checkpoint what the
  free-field/conformal-image case genuinely supports.
- [ ] **ASM — G1 with real parts (vacuum + sourced).** Instantiate `allBall_firstLaw_iff_residual_zero` with
  `residual = G⁽¹⁾(h)` (A1, full — vacuum form) and the sourced form `residual = G⁽¹⁾_{μν} − 8πG T_{μν}` (where B1/B2
  supply conservation/universality of the source), `δK = δ⟨K_ball⟩` (C2b, conditional), `δS = δA/4G` (A2 + the
  CARRIED Clausius/area law): the first law at every ball ⟺ the emergent graviton satisfies linearized Einstein.
  ⚠ CONDITIONAL on the carried inputs; the linearized skeleton assembled from real objects — NOT a derivation of
  gravity (that needs D).

## Per-increment discipline
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` std-3 (physical bridges =
hypotheses/structure fields, NEVER Lean axioms); `bash scripts/axiom_budget_check.sh` budget 0; wire `QIQTH.lean` +
`AxiomAudit.lean`; ONE commit on main with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer;
push via schannel; update this Progress log + `LEAN_RESULTS_INVENTORY.md`. Consults: `mcp__OpenAI__ask` model
`gpt-5.5-pro`.

## Progress log
- **2026-07-02** — plan created (bridge = A emergence + B universal coupling + C modular-geometric, linearized; D out
  of scope). **GPT-5.5-pro verification: RECOMMEND IMPLEMENTATION**; all 7 required edits applied (flat background
  explicit; A1 = full `G⁽¹⁾` + TT reduction + corollary; A2 = supplied area functional + separating family; B2 split
  into Ward identity + universality with `η_i` signs; C1/C2 weighted-boost/CHM-kernel formulas + `CHMCompatible`
  conditional; carried inputs as hypotheses not axioms; D phrased out-of-scope). Order re-cut per the verification:
  A1 → B1 → C1 → A2 → B2a → B2b → C2a → C2b → ASM. NEXT → A1.
- **2026-07-02 — A1 ✅ LANDED** (`LinearizedEinstein.lean`, after consolidation): the full `G⁽¹⁾` symbol
  (`ricciSymbol`/`einsteinSymbol`, every `(k,e)` — the ASM residual) + gauge invariance IDENTICALLY (pure-gauge and
  additive forms, any `k`) + the **linearized Bianchi identity** `k^μ(δG)_{μν}=0` identically + the TT reduction
  `einsteinSymbol_tt` (`δG=(−k²/2)•e` = "δG=−½□h") + the capstone `graviton_solves_linearized_einstein` (null `kDown`
  + any `a•e₊+b•e×` ⟹ `δG=0`) + the CONVERSE `einstein_iff_dispersion` (nonzero TT: `δG=0 ⟺ ω²=κ²`, light-cone
  dispersion) — **the quantized graviton (Q1–Q6) is provably the graviton of GR**. All [AF] std-3, budget 0.
  (Two parallel A1 builds raced; the thinner duplicate `BridgeLinearizedGR.lean` was removed and the richer module
  kept — a follow-up commit restored the module file the consolidation intended.) NEXT → B1 (coupling ⟺ conservation).
- **2026-07-02 — B1 ✅ LANDED** (`MatterCoupling.lean`): the coupling⟺conservation **iff**
  (`couple_gauge_invariant_iff_conserved` — gauge invariance of `∫h·T` for every `(e,ξ)` ⟺ `k_μT^{μν}=0`; the gauge
  variation is exactly `2∑ξ_ν(k_μT^{μν})`, `couple_gauge`) + **the Bianchi payoff** (`einstein_source_conserved` —
  the raised `δG` is identically conserved via A1's Bianchi; `source_conserved_of_einstein_eq` — any `T` sourced by
  `δG^{μν}=κT^{μν}` is AUTOMATICALLY conserved: geometry forces exactly the conservation the coupling demands; the
  linearized consistency triangle closes). All [AF] std-3, wired + pinned, budget 0. NEXT → C1 (wedge modular
  Hamiltonian = the weighted boost, packaging the DONE free-field modular results).
