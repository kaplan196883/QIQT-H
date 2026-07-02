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
- [x] **C1 — the wedge modular Hamiltonian is the geometric boost ✅** (`QIQTH/WedgeBoostClausius.lean`,
  `QIQTH.WedgeBoost`, all [AF] std-3, wired + pinned, budget 0). **`WedgeBoostPackage`** — the geometric boost flow
  + the **carried BW identification** `hBW : V_t ξ = Δ^{it} ξ` as a structure field (never an axiom; =
  `WedgeKMSFlux` input #3 isolated). **`boost_correlator_hasDerivAt`** — the geometric boost correlator inherits
  the DERIVED modular derivative: `d/dt⟪ξ,V_tξ⟫|₀ = i·(−S)`, `S = cgpEntropy` (the entanglement entropy).
  **`boost_flux_unique`** — the Clausius/heat-flux datum is **forced** by derivative uniqueness: any candidate `c`
  with `d/dt⟪ξ,V_tξ⟫|₀ = i·c` must equal `−S`. **`boost_correlator_im_hasDerivAt`** — the real (physical) form
  `d/dt Im⟪ξ,V_tξ⟫|₀ = −S`. ⚠ BW carried; the Rindler weight (`2π∫x¹T₀₀`) packaged at the level the existing
  theorems support (the correlator-derivative datum); free-field/RvD setting; not the area law (D).
- [x] **A2 — the emergence map (supplied geometric functional) ✅** (`QIQTH/AreaEmergence.lean`, `QIQTH.AreaMap`,
  all [AF] std-3, wired + pinned, budget 0). `ScreenSurface` (finite area elements: weight `w_a ≥ 0` + tangent frame)
  and the **SUPPLIED** discretized area variation `areaVar Σ h = ½∑ w_a(h(e₁ᵃ,e₁ᵃ)+h(e₂ᵃ,e₂ᵃ))`. **`areaProbe`** —
  `δA_Σ` is a *linear* functional of `h` (the exact `→ₗ[ℝ]` probe shape G1 consumes). **The wiring**
  (`screenArea_eq_bg_add_areaVar`): a `ScreenCut` whose independent area charge is supplied as the geometrically
  perturbed weight `w(1+½tr_Σh)` has `screenArea = (background) + δA_Σ(h)` — the code's charge and the geometric
  area become ONE object under the carried identification (`hwt`). **The separating witness**
  (`area_probes_separate`): a symmetric `h` with vanishing area variation at every ray surface is ZERO — area
  probes genuinely reconstruct the perturbation, making G1's separating-family hypothesis **non-vacuous with
  geometric probes**. ⚠ The map is supplied, never derived (deriving it = D); linearized only.
- [x] **B2a — the soft Ward identity ✅** (`QIQTH/SoftGraviton.lean`, `QIQTH.SoftGraviton`, all [AF] std-3, wired
  + pinned, budget 0). The soft factor `S(ε)=∑η_i g_i(p_i·ε·p_i)/(p_i·q)` (TAKEN as given — its S-matrix derivation
  is carried QFT input). **`quadForm_gaugeShiftK`** — the longitudinal shift evaluates as `p·(q⊙ξ)·p = 2(p·q)(p·ξ)`.
  **`softFactor_gauge_shift`** — the gauge variation is EXACTLY `2ξ·P`, `P = ∑η_i g_i p_i` (the denominators cancel
  against the longitudinal numerator). **`soft_gauge_invariant_iff_ward`** — **THE IFF**: longitudinal decoupling
  (the soft factor gauge-invariant for every `ξ`) ⟺ the Weinberg sum rule `∑_i η_i g_i p_i^μ = 0`. ⚠ Algebraic
  identity only — NOT the analytic soft theorem; universality (all `g_i` equal) is B2b.
- [x] **B2b — universality (the equivalence principle) ✅** (`QIQTH/SoftGraviton.lean` extension, all [AF] std-3,
  pinned, budget 0). **`RichFamily`** — the genericity hypothesis (the kernel of `c ↦ ∑c_ip_i` is exactly the
  momentum-conservation line `ℝ·η`), CARRIED. **`universality`** — Ward sum rule + generic momenta + `η_i ≠ 0` ⟹
  **all `g_i` equal**: one universal charge for every species. **`ward_of_universal`** — the converse consistency.
  **`equivalence_principle`** — **the B2 capstone**: longitudinal decoupling of the soft graviton ⟹ Ward ⟹
  (generic) ⟹ universal coupling — Weinberg's theorem at the algebraic level, end-to-end.
  **`witness_rich`/`witness_conserved`** — a concrete 5-momentum configuration satisfying `RichFamily` +
  conservation (non-vacuity; a kinematic witness, not an on-shell physical process). ⚠ Soft factor + genericity
  carried; NOT the analytic soft theorem.
- [x] **C2a — the ball conformal Killing vector algebra ✅** (`QIQTH/CHMKernel.lean`, `QIQTH.CHM`, all [AF] std-3,
  wired + pinned, budget 0). **`chmWeight`** `β(r)=(R²−r²)/2R` — nonneg on the ball, **vanishes at the entangling
  sphere**, center `R/2`, factorization `(R−r)(R+r)/2R`. **`chmWeight_edge_slope`** — `β′(R) = −1`: **the unit
  surface-gravity normalization** (= the Rindler weight's slope; why the SAME `2π` appears in wedge and ball, so
  the Clausius datum transports C1↔C2). **`cke_tt/tx/xx_diag/xx_off`** — the diamond **conformal Killing equation**
  `∂_μζ_ν+∂_νζ_μ = −(2t/R)η_{μν}` for `ζ₀=(t²+|x|²−R²)/2R`, `ζᵢ=−tx_i/R`, verified by genuine real calculus
  (`deriv`/`HasDerivAt`, all component classes). **`zeta0_restrict`** — `ζ₀|_{t=0} = −β`: the flow's local
  temperature IS the kernel. ⚠ Kernel geometry only; the CHM theorem itself is conformal-QFT input carried at C2b.
- [x] **C2b — conditional CHM transport ✅** (`QIQTH/BallClausius.lean`, `QIQTH.BallModular`, all [AF] std-3,
  wired + pinned, budget 0). **`BallModularFamily`** — per ball: standard subspace + probe state + geometric
  conformal flow, with the CARRIED **`hCHM`** = `CHMCompatible` (each ball's geometric flow acts on the state as
  its modular flow — the conformal transport of BW; CFT-vacuum input, structure field, never an axiom). Rides C1
  per ball (`toWedgePackage`). **`ball_correlator_hasDerivAt`** — the Clausius datum at EVERY ball:
  `d/dt⟪ξ_B,W^B_tξ_B⟫|₀ = i·(−S_B)`. **`ball_flux_unique`** — forced per ball. **`ballHeatFlux`** +
  **`ballHeatFlux_spec`** — the ball-indexed first-law data `δ⟨K_B⟩ = −S_B`, EXACTLY the `δK : Ball → ℝ` input
  ASM feeds into G1. ⚠ `hCHM` carried (CFT-vacuum, not generic QFT); the area law + `G` stay ASM's carried inputs.
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
- **2026-07-02 — C1 ✅ LANDED** (`WedgeBoostClausius.lean`): the geometric wedge boost packaged against the DONE
  modular flow — the carried BW identification as a structure field (`WedgeBoostPackage.hBW`), the boost correlator
  inheriting the derived modular derivative `d/dt⟪ξ,V_tξ⟫|₀ = i·(−S)` (`boost_correlator_hasDerivAt`), the
  Clausius datum FORCED by derivative uniqueness (`boost_flux_unique`: any flux candidate = −S), and the real form
  (`boost_correlator_im_hasDerivAt`). All [AF] std-3, wired + pinned, budget 0. NEXT → A2 (the emergence map:
  supplied area functional δA(h) + separating family).
- **2026-07-02 — A2 ✅ LANDED** (`AreaEmergence.lean`): the supplied linearized area functional `δA_Σ(h)` (linear —
  `areaProbe`, the G1 probe shape), the screen-code wiring (`screenArea_eq_bg_add_areaVar`: code area charge =
  background + δA under the carried identification), and the SEPARATING WITNESS (`area_probes_separate`: area
  probes at all ray surfaces reconstruct a symmetric perturbation — G1's separating-family hypothesis is
  non-vacuous with geometric probes). All [AF] std-3, wired + pinned, budget 0. NEXT → B2a (the soft Ward
  identity).
- **2026-07-02 — B2a ✅ LANDED** (`SoftGraviton.lean`): the soft-graviton Ward identity — the gauge variation of
  the soft factor is exactly `2ξ·(∑η_i g_i p_i)` (`softFactor_gauge_shift`, denominators cancel), so longitudinal
  decoupling ⟺ the Weinberg sum rule `∑η_i g_i p_i^μ = 0` (`soft_gauge_invariant_iff_ward`, an iff). All [AF]
  std-3, wired + pinned, budget 0. NEXT → B2b (universality on connected components: momentum conservation + a
  rich scattering family ⟹ all `g_i` equal — the equivalence principle).
- **2026-07-02 — B2b ✅ LANDED** (`SoftGraviton.lean` extension): UNIVERSALITY — `universality` (Ward + generic
  momenta (`RichFamily`, carried) + `η_i≠0` ⟹ all couplings equal), `equivalence_principle` (the B2 capstone:
  decoupling ⟹ Ward ⟹ universal — Weinberg end-to-end at the algebraic level), `ward_of_universal` (converse),
  `witness_rich`/`witness_conserved` (concrete non-vacuity). All [AF] std-3, pinned, budget 0. **Ingredient B is
  COMPLETE.** NEXT → C2a (the ball conformal Killing weight / CHM kernel geometry).
- **2026-07-02 — C2a ✅ LANDED** (`CHMKernel.lean`): the CHM ball kernel geometry — the weight β(r)=(R²−r²)/2R
  (nonneg, boundary-vanishing, factorized), the UNIT surface-gravity edge slope β′(R)=−1 (the C1↔C2 2π-consistency),
  the diamond conformal Killing equation verified by real calculus (all component classes), and ζ₀|_{t=0}=−β.
  All [AF] std-3, wired + pinned, budget 0. NEXT → C2b (conditional CHM transport under CHMCompatible) → ASM.
- **2026-07-02 — C2b ✅ LANDED** (`BallClausius.lean`): the conditional CHM transport — `BallModularFamily` with
  the carried `hCHM` (= `CHMCompatible`), riding C1 per ball; the Clausius datum forced at EVERY ball
  (`ball_correlator_hasDerivAt`, `ball_flux_unique`); `ballHeatFlux`/`ballHeatFlux_spec` = the ball-indexed
  `δK : Ball → ℝ` first-law data for G1. All [AF] std-3, wired + pinned, budget 0. **Ingredient C is COMPLETE.**
  NEXT → ASM (the final assembly: instantiate G1 with residual = einsteinSymbol, δK = ballHeatFlux, δS = δA/4G
  CARRIED).
