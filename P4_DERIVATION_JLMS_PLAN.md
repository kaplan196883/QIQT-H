# Deriving (P4): the JLMS / crossed-product route — turn the holographic capacity from postulate into theorem

**Status:** PLAN (not started). **Track:** GR (foundations). **Goal:** relocate **(P4)** — the holographic
capacity law `η·A(∂R) = log|R|`, currently *postulated* — toward a **theorem** about the modular/edge algebra
of one local Rindler wedge / causal diamond, via the **JLMS** identity
```
K_∂R  =  A_edge / 4ℓ_P²  +  K_bulk   (+ const)
```
where `K_∂R = −log Δ` is the (full) modular Hamiltonian, `A_edge` is an area/edge operator, and `K_bulk` is the
matter modular Hamiltonian.  This is the **highest-value upgrade** identified in the GR analysis: it converts
P4 from "assert the number" into "the modular Hamiltonian decomposes with an area edge term," reducing the
holographic capacity to the spectral content of `A_edge`.

## 0. Why this, and the honest frontier (stated up front)

Per the foundations analysis (and the GPT-5.5-pro adjudication): the area `A/4ℓ_P²` is the **von Neumann /
modular entanglement entropy** of the *pre-selection* state `Φ`, **not** a count of decohered records. The only
consistent reading of `log|R|` is the effective modular rank `e^{S(ρ_R)}` / an edge-mode degeneracy. So a
*derivation* of P4 must be an **algebraic entropy statement** on the modular algebra, not a counting argument.

**Fatal-vs-hard boundary (GPT rank-1 obstruction):** the *UV completion fixing the universal coefficient
`1/4ℓ_P²`* is the one genuinely fatal obstruction — without a microscopic theory, no algebraic manipulation
produces the `1/4`.  **This plan does NOT claim to derive `1/4`.**  Its deliverable is the **JLMS *structure***:
the decomposition `K_∂R = A_edge/4ℓ_P² + K_bulk` as a *theorem of the modular algebra*, with `A_edge` a genuine
edge operator and the coefficient carried as the single labelled input — so P4 is reduced from "a postulated
number" to "the spectral normalization of `A_edge`," the irreducible UV datum.  That is a real reduction (it
turns a scalar postulate into a sharply-located operator statement) without overclaiming.

## 1. What already exists (build on, do not rebuild)

Verified in `lean/mathlib/QIQTH/`:
- **RvD bounded modular objects** (`StandardSubspaceModular.lean`, `StandardSubspaceModularFlow.lean`): `Δ`, `J`,
  `Δ^{it}` via `borelFC` of the RvD operator `R` on a standard subspace; the RvD identities
  (`commute_projK_of_commute_R_D`, `commute_rvdPmQ_of_commute_modConj_rvdT`, the `borelFC_*` algebra: `_adjoint`,
  `_mul`, `_comm`, `_inner_self`).
- **One-particle modular / relative entropy** (`ArakiModularEntropy.lean`, `ModularRelativeEntropy.lean`):
  `cgpEntropy` with `cgpEntropy_eq_neg_re_inner`, `cgpEntropy_nonneg`, `cgpEntropy_smul`, `cgpEntropy_zero`,
  `cgpDensity_nonneg` — the Casini–Grillo–Pontello one-particle (non-Type-I) relative-entropy functional.
- **Bisognano–Wichmann** (machine-checked): the wedge modular flow **is** the geometric boost
  (`Fock.oneParticleBW_*`, `freeField_oneParticle_hFlux`), so `K_wedge = (2π/ℏ)·B_boost` is already a theorem on
  the one-particle space.
- **Araki relative entropy on Hilbert–Schmidt** (Phase A done, per roadmap): the relative modular operator on
  HS space (`ArakiEntropy.lean`).

## 2. Stages (each axiom-free, green-building, one commit)

### Stage 1 — the modular Hamiltonian as an operator `QIQTH/ModularHamiltonian.lean`
Define `K := −log Δ` on the RvD setup via `borelFC` of `R` (the function `λ ↦ −log((2−r)/r)` of the RvD `R`),
and prove the basics: `K` self-adjoint, `Δ^{it} = e^{itK}` (consistency with the existing `borelFC` modular
flow), and `⟨ξ, K ξ⟩` = the modular energy.  **Build on:** `borelFC_adjoint`, `borelFC_inner_self`, the RvD
`Δ`-formula.  **Risk: medium** (bounded Borel `log` of `R`; `R` has spectrum in `(0,2)` so `log Δ` is genuinely
unbounded — may need the bounded-resolvent / form-domain route, or restrict to a bounded spectral window first).

### Stage 2 — the first law of entanglement `δS = δ⟨K⟩`  *(the engine)*
Using `cgpEntropy` (the one-particle relative entropy `S(ω‖σ)`), prove the **first-law / Clausius form**: for a
one-parameter family of states through the reference, `d/dt S(ω_t‖σ)|₀ = d/dt ⟨K⟩_t|₀` (the relative entropy's
first variation is the modular-energy variation, since `S(ω‖σ) = ⟨K⟩_ω − S_vN` and `S_vN` is stationary at the
reference).  **Build on:** `cgpEntropy_eq_neg_re_inner`, `cgpEntropy_nonneg` (Klein), and the Stage-1 `K`.  This
is the *exact* modular analog of the `EntropyDeriv` first-law work already done for the finite record law — and
it is the boundary-side dual of the bulk Clausius relation the GR chain uses.  **Risk: medium.**

### Stage 3 — the area/edge operator + the JLMS decomposition *(the target form)*
Introduce an **edge operator** `A_edge` on the wedge algebra (the boundary term of the boost charge — the
geometric part of `K` localized at the entangling surface `∂R`), and state the **JLMS decomposition**
`K_∂R = c·A_edge + K_bulk` with `c = 1/4ℓ_P²` **carried** (the UV coefficient, §0).  Prove the *structural*
content that is a theorem: `K_∂R − K_bulk` is supported on `∂R` (commutes with the bulk-localized algebra), i.e.
the modular Hamiltonian splits into a bulk part and an edge part — the JLMS *form*, with `A_edge` defined as the
edge part and `c` its labelled spectral normalization.  **Build on:** the BW boost-charge split (the boost
generator = bulk integral + boundary term) already in the GR development.  **Risk: high** (defining `A_edge`
honestly without smuggling the area; the cleanest is `A_edge := (K_∂R − K_bulk)/c` and then the *content* is
that this object is geometric — equals the surface area — which is exactly the cited frontier).

### Stage 4 — reduce (P4) to the edge spectral statement *(the deliverable)*
Package: **given** the JLMS decomposition (Stage 3) **and** the edge-operator normalization `⟨A_edge⟩ = A(∂R)`
(the one carried UV datum), the FQ bound `S(ρ_R) ≤ A/4ℓ_P²` is the statement `S_vN ≤ ⟨K_∂R − K_bulk⟩/c`, i.e.
relative-entropy positivity (`cgpEntropy_nonneg`) **plus** the edge normalization.  So **P4 is reduced**:
the holographic *bound* follows from Klein positivity (a theorem) once the edge operator's expectation is the
area — turning P4 from "postulate the entropy law" into "postulate the area-operator normalization
`⟨A_edge⟩ = A`," a strictly sharper and more localized input.  **Risk: low** once Stages 2–3 land (compose
existing positivity).

## 3. Honest deliverable (what this does and does NOT achieve)
- **Does:** relocate P4 from a scalar entropy postulate to the JLMS operator identity + the single edge-operator
  normalization `⟨A_edge⟩ = A/4ℓ_P²`; derive the *bound* side from Klein positivity (`cgpEntropy_nonneg`); make
  the first-law engine `δS = δ⟨K⟩` a machine-checked modular theorem (the boundary dual of the bulk Clausius
  relation).  This is the "equation of state → toward statistical mechanics" step, one local wedge at a time.
- **Does NOT:** derive the `1/4ℓ_P²` coefficient (GPT rank-1 fatal obstruction — needs the UV micro-theory),
  nor produce an *independent* boundary CFT, nor reconstruct the bulk geometry from boundary entanglement
  (the AdS/CFT arrow).  Those remain the cited frontier.  No counting of actualized records anywhere — `K` and
  `A_edge` are operators on the pre-selection modular algebra, per the §0 internal-consistency constraint.

## 4. Verification (per stage)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = standard 3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per stage
with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel.  After each
landing, run `python scripts/lean-track-refresh.py --skip-unchanged` and commit `reports/` if it prints CHANGES.

## Progress log
- (none yet — Stage 1 next)
