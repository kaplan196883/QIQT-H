# Companion formalization paper — DETAILED COMPOSER-READY OUTLINE

**Working title:** *Machine-checked coherent-state Araki relative entropy in bounded modular theory*
(alt: *A Lean 4 formalization of bounded standard-subspace Tomita–Takesaki theory and the coherent-state
Araki relative entropy*). **Avoid** any title implying "formal verification of QIQT-H."

**Target venue:** arXiv `math.OA` (primary) + `cs.LO` cross-list (or `quant-ph`). Short math/formal-methods
preprint, **~7,500 words / 12–14 pp**. This is the **primary citable artifact** for the Lean work; the
QIQT-H foundations paper cites it. **Audience:** operator algebraists + formal-methods. **No QIQT-H physics
commitments enter** — it stands alone as a contribution to formalized modular theory.

**Artifact:** commit `4720763a7b59`, `leanprover/lean4:v4.30.0`, aggregator `QIQTH`; freeze a Zenodo DOI.
Appendix A = `paper_strategy/45_Theorem_Paper_Index.md` (the theorem↔Lean map). **Style guide:** see
`paper_strategy/02_arXiv_quant-ph_Writing_Standards_Guide.md`; math-OA conventions (definition/theorem/proof
environments, `\Delta`, `\sigma_t`, standard modular notation).

**Scope discipline (carry through every section):** we machine-check the *modular / relative-entropy
calculus* for the *free-field coherent sector*; we do NOT formalize Type III classification, unbounded GNS,
general two-state relative modular operators, or any QIQT-H physical postulate. Use "no `sorry` and no axioms
beyond the standard classical foundations (`propext`, `Classical.choice`, `Quot.sound`)" — never bare
"axiom-free."

**Total: ~7,500 words.** Word counts are targets (±10%).

---

## §0. Abstract — 200 words

- **Content:** one-paragraph statement of what is formalized (bounded standard-subspace Tomita–Takesaki +
  coherent-state Araki relative entropy of a free field), the headline result (the CGP identity
  `S_Araki(ω_{W(f)Ω}‖ω_Ω) = S_CGP(f)`), the verification status (`no sorry`, standard classical axioms only),
  and the novelty claim ("to our knowledge the first machine-checked development of standard-subspace modular
  theory and coherent-state relative entropy").
- **Citations:** none (abstract).
- **Write LAST.** Quality check: standalone, accurate, no overclaim.

## §1. Introduction — 1,200 words

### 1.1 Modular theory and relative entropy: ubiquity and difficulty — 450 words
- **Content:** Tomita–Takesaki modular theory and Araki relative entropy are central tools in AQFT, quantum
  information, and recent entropy-bound / holography work. Their *continuum* forms are analytically delicate
  (unbounded `Δ`, closable antilinear `S`, domain questions), which makes them prime — and hard — targets for
  formalization. Mathlib has rich CFC and a structural `StandardSubspace`/`VonNeumannAlgebra` but no modular
  flow, no relative entropy, no unbounded operator theory.
- **Citations:** Takesaki (Tomita–Takesaki); Bratteli–Robinson; Araki 1976/77; Ohya–Petz; Witten 2018 RMP
  (modular theory in QFT); Tanimoto 2026 (Mathlib `StandardSubspace`); Mathlib community.
- **Argument:** set up the gap — these results are *used* everywhere but their continuum forms are unverified.

### 1.2 The bounded standard-subspace approach as a formalization-friendly route — 400 words
- **Content:** the Rieffel–Van Daele bounded-operator approach to Tomita–Takesaki builds `J` and the modular
  flow from a standard subspace using only *bounded* operators (`R = P+Q`, `Δ = (2−R)/R`), sidestepping the
  unbounded-operator theory Mathlib lacks. This makes a substantial, genuinely continuum (one-particle) slice
  *machine-checkable now*. Casini–Grillo–Pontello / Longo show the coherent-state relative entropy reduces to
  a one-particle spectral integral — exactly the sweet spot.
- **Citations:** Rieffel–Van Daele 1977; Longo (standard subspaces lecture notes); Casini–Grillo–Pontello
  2019; Longo 2019 (entropy of coherent excitations).
- **Argument:** justify the methodological choice (bounded RvD) as what makes the project feasible.

### 1.3 Contributions and non-goals — 350 words
- **Content:** enumerate the six machine-checked results (finite Araki=Umegaki; bounded TT; CGP entropy +
  positivity; Fock modular flow; relative modular operator + Connes cocycle; the entropy reduction). State
  the verification discipline. State **non-goals explicitly** (no Type III, no unbounded GNS, no general
  two-state relative modular operator, no holographic/physical postulates). Relation to existing Mathlib.
- **Citations:** de Moura–Ullrich (Lean 4); Mathlib.
- **Argument:** sharp contribution list + honest scope; forward-reference the section map.

## §2. Bounded standard-subspace modular setup — 1,000 words

### 2.1 Standard subspaces and the RvD operators — 350 words
- **Content:** definitions: standard subspace `𝒦 ⊆ H` (cyclic + separating), projections `P` (onto `𝒦`),
  `Q` (onto `i𝒦`), `R = P+Q` with `0 ≤ R ≤ 2`, injectivity; the polar factor `T = √R√(2−R)`. State the Lean
  realizations (`rvdRC`, `rvdT`) and the type-level setup (general complex Hilbert `H`).
- **Citations:** Rieffel–Van Daele 1977; Tanimoto 2026 (Mathlib `StandardSubspace`, `IsSeparating`,
  `IsCyclic`).

### 2.2 Modular conjugation, reflection, fixedness — 350 words
- **Content:** `J = modConj` (antiunitary, `J²=1`); the modular reflection `JRJ = 2−R`
  (`modConj_rvdRC_modConj`, the bounded form of `JΔJ=Δ⁻¹`); bounded Tomita fixedness `J(Tξ)=(2−R)ξ` for
  `ξ∈𝒦` (`modConj_rvdT_of_mem_K`, the bounded encoding of `ξ=JΔ^{1/2}ξ`, avoiding unbounded `Δ^{1/2}`).
- **Citations:** Rieffel–Van Daele; Longo (standard subspaces).
- **Argument:** these are the Tomita relations in bounded form — the foundation everything rests on.

### 2.3 The continuum modular flow and its functional calculus — 300 words
- **Content:** `Δ^{it} = u_t(R)`, `u_t(r)=exp(it·log((2−r)/r))` (`modUnitary`); group law, unitarity, strong
  continuity (`modUnitary_add/_unitary/_stronglyContinuous`); the bounded Borel / continuous FC of `R`
  (PVM scalar measure, `cfcΩ`) used throughout. State `modUnitary_mapsTo_K` (`U_t𝒦⊆𝒦`).
- **Citations:** Mathlib CFC; Conway (functional calculus, optional).
- **Quality marker:** state precisely that NO unbounded `log Δ` is constructed.

## §3. The finite Araki/Umegaki convention lock — 700 words

### 3.1 The Hilbert–Schmidt relative modular operator — 300 words
- **Content:** finite-dim setup: `Δ = L_σ R_ρ⁻¹` on HS space; `log Δ = L_{logσ} − R_{logρ}`
  (`log_relMod`, via CFC under the `*`-hom `A↦L_A` and `[L,R]=0`).
- **Citations:** Araki 1977; Umegaki 1962.

### 3.2 The convention-lock theorem — 250 words
- **Content:** `arakiEntropy_eq_relEntropy`: `S_Araki(ρ‖σ) = −⟨ρ^½,(logΔ)ρ^½⟩_HS = tr ρ(logρ−logσ)`
  (= Umegaki). Why a convention lock matters (slot/sign sensitivity). State the result as a **Proposition**.
- **Citations:** Umegaki 1962; Ohya–Petz; Araki.

### 3.3 A formalization-craft note: the instance diamond — 150 words
- **Content:** brief note on the CFC instance-diamond dodge (eigenvalue route) — a reusable lesson for
  matrix-CFC formalization. Keep short; signals the paper has formal-methods value too.
- **Citations:** Mathlib (Matrix CFC, `HermitianFunctionalCalculus`).

## §4. The CGP one-particle relative entropy and its positivity — 1,200 words

### 4.1 The entropy as a bounded scalar spectral integral — 350 words
- **Content:** `cgpEntropy S ξ := −∫ log((2−r)/r) dμ^R_ξ`; the spectral measure `μ^R_ξ` of `R` at `ξ`; the
  point that NO unbounded `log Δ` is built — but the integrand `log((2−r)/r)` is bounded *only* on a regular
  window `σ(R)⊆[a,2−a]` (state this honestly). Operator-expectation form `−re⟨ξ,g(R)ξ⟩` in the regular
  regime (`cgpEntropy_eq_neg_re_inner`). Finite-entropy regime.
- **Citations:** Casini–Grillo–Pontello 2019; Longo 2019.

### 4.2 The CGP spectral balance — 350 words
- **Content:** `rvdSpec_balance`: `∫(2−r)²F dμ = ∫r(2−r)F(2−r)dμ` for `ξ∈𝒦`. The chain that proves it:
  R/2−R as cfcΩ-images, `μ_{(2−R)ξ}=(2−r)²μ_ξ`, the measure reflection `μ_{Jη}=(2−·)_*μ_η`, the Tomita
  fixedness, and the key trick `μ_{Tξ}=r(2−r)μ_ξ` via `T²=R(2−R)` (avoids the `CFC.sqrt↔cfcΩ` identification).
- **Citations:** CGP; Longo.
- **Argument:** this is the analytic heart; emphasize the bounded route.

### 4.3 Positivity of the one-particle relative entropy — 500 words
- **Content:** `cgpEntropy_nonneg`: `0 ≤ cgpEntropy S ξ` for localized `ξ∈𝒦` in the regular regime. The
  clamped-representative technique; the manifestly-signed form `S(ξ)=∫((1−r)/r)·log((2−r)/r) dμ` with integrand
  `≥0` on all of `(0,2)` (no `(0,1)`-split needed — cleaner than the textbook split). **Emphasize: localization
  `ξ∈𝒦` is ESSENTIAL** — a general vector with a spectral point mass at `r<1` gives `cgpEntropy<0`. State as a
  **Theorem**.
- **Citations:** CGP 2019; Longo 2019; Araki (positivity of relative entropy).
- **Quality marker:** the essentiality of localization is the non-obvious, citable content.

## §5. The free-field (Fock) modular flow — 900 words

### 5.1 The bosonic Fock layer and second quantization — 300 words
- **Content:** recap the (existing, axiom-free) Fock layer: exponential vectors `e(f)`,
  `⟨e(f),e(g)⟩=exp⟨f,g⟩`, the generic functor `Γ` (`secondQuantPre`); vacuum `Ω=e(0)`.
- **Citations:** Parthasarathy (§19, second quantization); Bratteli–Robinson (CCR/Fock).

### 5.2 Γ(Δ^{it}) as the field-level modular flow — 300 words
- **Content:** `secondQuantModFlowH = Γ(Δ^{it})`: one-parameter group of isometries
  (`secondQuantModFlowH_add`), vacuum-fixing, strongly continuous on coherent vectors
  (`secondQuantModFlowH_continuous_expVec`). The coherent-map continuity lemma as a building block.
- **Citations:** Parthasarathy; Araki–Woods (free-field modular, optional).

### 5.3 Tomita's theorem at the field level — 300 words
- **Content:** `secondQuantModFlowH_weylH`: `σ_t(W(u)) = Γ(Δ^{it})W(u)Γ(Δ^{-it}) = W(Δ^{it}u)` (modular flow
  maps the CCR/Weyl algebra onto itself); the vacuum is the modular state (`weylVacuum_modFlow_invariant`).
- **Citations:** Tomita–Takesaki (Takesaki); Bisognano–Wichmann 1975/76 (geometric modular flow, free field).
- **Argument:** this is `σ_t(M)=M` for the free field, machine-checked.

## §6. Coherent-state relative modular operator and Connes cocycle — 1,000 words

### 6.1 The relative modular operator of a coherent state — 350 words
- **Content:** `relModFlowH = Δ_{W(f)Ω|Ω}^{it} = W(f)Γ(Δ^{it})W(f)*` (Araki `Δ_{uΩ|Ω}=uΔ_Ω u*` for `u∈M`).
  **State the convention + the requirement `W(f)∈M`** (f in the real standard subspace) explicitly. One-parameter
  group (`relModFlowH_add`).
- **Citations:** Araki 1973 (relative modular operator); Connes 1973.

### 6.2 The Connes cocycle in closed form — 350 words
- **Content:** `connesCocycleH = W(f)W(−Δ^{it}f)` (the cocycle `[Dω_{W(f)Ω}:Dω_Ω]_t` in closed Weyl-product
  form), `connesCocycleH_zero` (`u_0=id`). Note the cocycle is a product of Weyl unitaries — the
  Araki/Connes formula for a coherent excitation.
- **Citations:** Connes 1973 (Radon–Nikodym cocycle); Araki.

### 6.3 The cocycle chain rule — 300 words
- **Content:** `connesCocycleH_chain`: `u_{s+t}=u_s σ_s(u_t)` (`σ_s=Ad Γ(Δ^{is})`) — the defining identity of
  a genuine Connes cocycle (Radon–Nikodym). Falls out of the Tomita covariance + group law.
- **Citations:** Connes 1973.
- **Quality marker:** stress this confirms the object IS a Connes cocycle, not just notation.

## §7. The entropy reduction — 1,100 words

### 7.1 The vacuum characteristic function — 350 words
- **Content:** `relModFlow_vacuum_char`: `⟨Ω,Δ_rel^{it}Ω⟩ = exp(⟨f,Δ^{it}f⟩−⟨f,f⟩)` — the bounded generating
  function. Proof technique: push `relModFlowH` to the pre-Fock level (where the maps are genuinely linear),
  where the coherent vector is `weylCoeff(−f,0)·weylCoeff(f,−Δ^{it}f)·e(f−Δ^{it}f)`, then `fockInner` +
  Weyl-coefficient collapse.
- **Citations:** Longo 2019; CGP.

### 7.2 Differentiation under the spectral integral — 350 words
- **Content:** `hasDerivAt_modChar` (`∂_t u_t = i·g·u_t`, `g=entropyDensity`) + `rvdSpec_modUnitary` (the
  complex operator-expectation bridge `⟨ξ,U_t ξ⟩=∫u_t dμ`) → `hasDerivAt_inner_modUnitary`
  (`d/dt|₀⟨ξ,U_t ξ⟩=i∫g dμ`), via Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the
  constant dominating bound `log((2−a)/a)` on the regular window (finite spectral measure). The Stone-generator
  step done at scalar-integral level.
- **Citations:** Mathlib (parametric integral / dominated derivative); Stone's theorem (background).

### 7.3 The reduction theorem — 400 words
- **Content:** `hasDerivAt_relModFlow_vacuum`: `d/dt|₀⟨Ω,Δ_rel^{it}Ω⟩ = −i·cgpEntropy(f)`, i.e.
  `S_Araki(ω_{W(f)Ω}‖ω_Ω) = S_CGP(f)` — the Casini–Grillo–Pontello identity, machine-verified. Chain rule on
  §7.1 + §7.2 + `∫entropyDensity dμ=−cgpEntropy`. State as the **headline Theorem**. Connect to positivity
  (§4.3): the coherent-state relative entropy is `≥0`.
- **Citations:** CGP 2019; Longo 2019; Araki.
- **Quality marker:** the headline; explicitly the CGP result, end-to-end machine-checked.

## §8. Non-goals, limitations, and future work — 500 words

### 8.1 What is and is not covered — 250 words
- **Content:** explicit limitations: NOT formalized = general (non-coherent) two-state relative modular
  operator (needs unbounded GNS — the Mathlib gap); full-Fock strong continuity (density+ε/3, mechanical but
  pending); Type III classification; interacting QFT; **and (one sentence) the QIQT-H holographic capacity
  axiom, Macroscopic Definiteness postulate, and Born-rule problem — these are physics, not part of this
  artifact.**
- **Citations:** Buchholz–Wichmann (Type III₁, cited frontier); CPW 2022 (context only).

### 8.2 Toward Mathlib and future formalization — 250 words
- **Content:** the bounded modular library is a candidate upstream Mathlib contribution; the next frontier is
  unbounded modular operators (general states / Type III). Brief reflection on the bounded-RvD strategy as a
  template for formalizing operator-algebra results that current libraries can't reach via the unbounded route.
- **Citations:** Mathlib; Conway / Reed–Simon (unbounded operators, the gap).

## Appendix A — Theorem ↔ Lean index
- Paste `paper_strategy/45_Theorem_Paper_Index.md` (paper symbol → Lean name → `file:line`). NOT word-counted.

## Appendix B — Reproducibility
- `#print axioms` output for all headline theorems; build instructions; pinned commit `4720763a7b59`,
  toolchain `v4.30.0`; Zenodo DOI; license. NOT word-counted.

---

## PRODUCTION CHECKLIST (Phase-4 prerequisites — now satisfied)
- [x] Section titles + **word counts** (this revision).
- [x] **3rd-level subsection structure** with content guidance (this revision).
- [x] **Key citations** per subsection (this revision).
- [x] Argument-structure notes (this revision).
- [x] Theorem index appendix ready (`45`).
- [ ] Freeze Zenodo DOI at `4720763a7b59`.
- [ ] Build the bibliography (`.bib`): RvD 1977, Longo (std subspaces + 2019), CGP 2019, Araki 1973/76/77,
      Umegaki 1962, Connes 1973, Bisognano–Wichmann 1975/76, Takesaki, Bratteli–Robinson, Parthasarathy,
      Ohya–Petz, Witten 2018, Tanimoto 2026, de Moura–Ullrich, Mathlib, Buchholz–Wichmann, CPW 2022.
- [ ] **Composer Decision Point 1:** confirm this outline + the arXiv-quant-ph/math-OA standards loaded →
      begin Phase-4 systematic writing (Introduction first, Abstract last).
