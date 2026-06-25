# Scoping the Type II crossed-product frontier — toward an honest area operator

**Status:** SCOPE (maps the campaign; identifies the minimal first increment). **Track:** GR / continuum.
**Goal:** lay out the concrete path from the JLMS engine (Stages 1–2 done: `K` pinned to BW flow, `S = ⟨K⟩`)
to a **genuine, independently-defined area edge operator** `A_edge`, via the Chandrasekaran–Longo–
Penington–Witten / Witten **crossed-product Type II** construction — the step that unblocks JLMS Stage 3 and
moves (P4) from postulate toward theorem.

## 0. The physics target (what the construction delivers)

The matter wedge algebra `M` is Type III₁ (no trace, divergent entropy).  Crossing it with its modular
automorphism flow `σ_t` (which we **already have** as `modUnitary S t = Δ^{it}`) gives
```
M̃ = M ⋊_σ ℝ     (Type II_∞, with a faithful semifinite trace τ)
```
Concretely one adjoins an **observer/clock** with energy operator `X` conjugate to modular time, and the
**dressed modular Hamiltonian** is `K̃ = K + X`.  The area operator is the trace-renormalization of `M̃`:
in CLPW the generalized entropy `S_gen = ⟨X⟩ + S_out + const`, with the `const` the area term `A/4G`.  The key
point for us: **`X` (the clock energy) is an *independently defined* operator** — so the JLMS split
```
K̃ = K + c·A_edge,     A_edge := X / c
```
is **not vacuous** (unlike `A_edge := (K − K_bulk)/c` with no independent `K_bulk`).  `A_edge` becomes a real
operator the moment the crossed product exists; the only residual frontier is the *geometric* identification
`X ↔ area` and the coefficient `1/4ℓ_P²` (GPT rank-1, the UV datum — still carried, not derived here).

## 1. What Mathlib / the project has vs. lacks

**Have (build on):**
- the modular flow `modUnitary S t : H →L[ℂ] H` — a strongly-continuous one-parameter **unitary group**
  (`modUnitary_add` group law, `modUnitary_unitary`, strong continuity) — *this is the `σ_t` we cross by;*
- `Mathlib.MeasureTheory.Function.LpSpace` — vector-valued `L²(ℝ; H)` (Bochner), the crossed-product Hilbert
  space `H ⊗ L²(ℝ) ≅ L²(ℝ; H)`;
- `VonNeumannAlgebra`, `.commutant` (structural), `ContinuousLinearMap.adjoint`, positive operators;
- the spectral/`borelFC` machinery (for functions of `X`).

**Lack (the campaign):** the crossed product *as a von Neumann algebra*, its **trace**, the Type II
classification, and the area-as-trace-shift renormalization.  None of these are in Mathlib.

## 2. The MINIMAL first increment — the covariant representation + the clock energy

The smallest piece that is (a) genuinely a step, (b) buildable on existing infrastructure, and (c) the home of
`A_edge`:  the **covariant representation of the crossed product on `L²(ℝ; H)`**, with the clock-energy operator.

### Increment 1a — the crossed-product Hilbert space and the two generating families
*New file `QIQTH/CrossedProduct.lean`.*  On `L²(ℝ; H)`:
- **the represented matter** `π(a)` for a bounded `a : H →L[ℂ] H`:
  `(π(a) ξ)(s) = σ_{-s}(a) (ξ s)` with `σ_{-s}(a) = modUnitary S (-s) ∘ a ∘ modUnitary S s` — fiberwise the
  modular-conjugated operator (bounded, `‖σ_{-s}(a)‖ = ‖a‖`, so `π(a)` is bounded);
- **the modular translations** `λ_t` : `(λ_t ξ)(s) = ξ(s − t)` — a unitary group (translation on `L²(ℝ)`).

### Increment 1b — the covariance relation (the defining identity)
Prove the crossed-product covariance
```
λ_t ∘ π(a) ∘ λ_{-t} = π(σ_t a)
```
(directly from `(λ_t π(a) λ_{-t} ξ)(s) = σ_{-(s-t)}(a)(ξ s) = σ_t(σ_{-s}(a))(ξ s) = π(σ_t a)ξ(s)`, using the
`modUnitary` group law).  This is the algebraic heart of `M ⋊_σ ℝ` and uses **only** the existing modular flow.
**Risk: medium** (the `L²(ℝ; H)` fiberwise-operator boundedness/measurability plumbing is the real work; the
covariance algebra itself is the `modUnitary_add` group law).

### Increment 1c — the clock energy `X` and the dressed generator
Define `X` = the generator of `λ_t` (translation generator = momentum `p` on `L²(ℝ)`, via Stone / the existing
`borelFC` route), tensored to `L²(ℝ; H)`.  Then **`A_edge := X / c`** is a genuine, independently-defined
self-adjoint operator, and the dressed modular generator is `K̃ = K + X` (the constraint).  Deliver the JLMS
split as `K̃ = K + c·A_edge` with `A_edge` a real operator — *unblocking Stage 3 honestly*.  The geometric
content `A_edge = area` and the coefficient `1/4ℓ_P²` stay the labelled UV frontier (NOT smuggled).

## 3. The subsequent (harder) campaign steps — mapped, not scheduled

2. **The Type II trace `τ`** on the crossed product (the dual weight / Takesaki construction): `τ(x)` finite on
   a corner, `τ ∘ σ̃_s = e^{-s} τ` (the scaling that *defines* Type II_∞).  *The deep analytic step.*
3. **Finite renormalized entropy** `S_τ(ρ) = −τ(h_ρ log h_ρ)` — finite where the Type III entropy diverged;
   the "removes one infinity (entropy)" win, now *internal* to QIQT-H rather than cited.
4. **The area normalization** `⟨A_edge⟩ = A(∂R)` and the JLMS relation `K̃ = A/4ℓ_P² + K_bulk` as a theorem of
   the trace — at which point (P4)'s *bound* follows from `cgpEntropy_nonneg` (Stage-2 positivity) + the
   normalization.  **The coefficient `1/4` remains the one carried UV input** (fatal obstruction, §0).

## 4. Honest scale
Steps 2–4 are a genuine **multi-month, Mathlib-grade** undertaking (crossed-product vN algebras, the dual-weight
trace, Type II classification — open Mathlib targets in their own right).  **Increment 1 (1a–1c) is the
tractable, self-contained, independently-valuable first step:** it builds the covariant representation + the
clock energy on existing infrastructure, makes `A_edge` a real operator, and unblocks JLMS Stage 3 — without
the trace.  Value lands there; the rest is the long arc.  Nothing here claims the `1/4` or the geometric
area identification — those are the cited UV frontier throughout.

## 5. Verification (per increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = standard 3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per
increment with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel.

## Progress log
- **Increment 1a-0 ✅** (`QIQTH/CrossedProduct.lean`) — the **modular automorphism** `σ_t(a) = Δ^{it} a Δ^{-it}`
  (`modularAut`) built from the existing modular unitary flow, proved a **one-parameter group of unital
  `*`-homomorphisms**: `modularAut_zero` (σ₀=id), `modularAut_one` (σ_t 1 = 1), `modularAut_mul` (multiplicative),
  `modularAut_add` (the cocycle/group law σ_{s+t}=σ_s∘σ_t), `modularAut_star` (`*`-preserving). This is the
  ℝ-action the crossed product `M ⋊_σ ℝ` is formed by — promoting the modular *flow* (unitaries) to the modular
  *automorphism* (of operators), the action-side foundation. Axiom-free (std 3); wired into AxiomAudit; budget 0.
- **Increment 1a/1b/1c ⛔ BLOCKED (honest checkpoint, after investigation)** — the `L²(ℝ; H)` covariant
  representation is the campaign's first genuine multi-week chunk, not a loop increment. Precise findings:
  - **`λ_t` (clock translations):** Mathlib *has* the machinery — `MeasureTheory.DomMulAct`/`DomAddAct`
    (`Mathlib/MeasureTheory/Function/LpSpace/DomAct/Basic.lean`) acts on `Lp E p μ` by precomposition with a
    measure-preserving map, so `ℝᵈᵃᵃ` translates `L²(ℝ;H)`. But it is an *un-bundled action* (and
    `Lp.compMeasurePreserving` is only an `AddMonoidHom`); turning it into a usable continuous-ℂ-linear
    **unitary group** (the covariance needs `λ_{-t} = λ_t⁻¹`) is real bundling work.
  - **`π(a)` (the matter representation):** a **genuine Mathlib gap.** It is operator-valued *post*-composition
    `ξ(s) ↦ σ_{-s}(a)(ξ s)` — `DomAct` only does *pre*-composition (the translations). No operator-valued `Lp`
    multiplication exists; it must be built from scratch (fiberwise `AEStronglyMeasurable` of `s ↦ σ_{-s}(a)(ξ s)`
    + the `Lp` bound `‖π(a)ξ‖ ≤ ‖a‖·‖ξ‖`). This is the heart of 1a/1b and the real wall.
  - **`X = A_edge` (the generator):** unbounded — needs Stone's theorem / unbounded-self-adjoint operators
    (the same cited TT frontier `K` hit in JLMS Stage 1).

  So the derivation honestly stops at the **action-side foundation (1a-0)**: the modular automorphism `σ_t` is a
  machine-checked one-parameter group of unital `*`-automorphisms — the concrete ℝ-action the crossed product is
  built from. The spatial crossed product (covariant rep) + the clock energy await the Bochner-`Lp`
  operator-valued infrastructure (build) and Stone's theorem (frontier).

### Status — Increment 1a-0 delivered; the spatial crossed product is the multi-week build
**Delivered (axiom-free, budget 0):** the modular automorphism `σ_t` (`modularAut`) as a one-parameter group of
unital `*`-homomorphisms — the action `M ⋊_σ ℝ` is formed by, promoted from the modular unitary flow.
**Frontier (recorded, not faked):** the covariant representation `π`/`λ` on `L²(ℝ;H)` (π(a) = an operator-valued
`Lp`-multiplication build; λ_t = a unitary-group bundling of the existing `DomAddAct`), the clock energy
`X = A_edge` (Stone/unbounded), and beyond that the Type II trace (steps 2–4). All the multi-week arc, with the
`1/4` coefficient the cited UV datum throughout.
