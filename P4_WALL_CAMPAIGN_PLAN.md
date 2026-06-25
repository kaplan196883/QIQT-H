# The Wall — campaign plan to build the Type II infrastructure that derives (P4)

**Status:** CAMPAIGN PLAN (multi-month → multi-year, Mathlib-grade). **Track:** GR / continuum.
**Goal:** build the operator-algebra infrastructure that turns the holographic capacity **(P4)** from a postulate
into a **theorem** — the area operator of the gravitationally-dressed crossed-product Type II algebra, and the
JLMS identity `K_∂R = A/4ℓ_P² + K_bulk`.  This expands `CROSSED_PRODUCT_TYPE_II_SCOPE.md` (Increment 1a-0 done:
the modular automorphism `σ_t`) into the full phased build, and is the goal-directed specialization of the
general continuum Tomita–Takesaki tower (`TOMITA_TAKESAKI_ROADMAP.md`).

## 0. Honest scale and the one thing this does NOT deliver

This is a **research-grade campaign**: several phases (unbounded operators, Stone's theorem, the dual-weight
trace) are open Mathlib targets in their own right.  **Value lands incrementally** — each phase is a
self-contained, axiom-free, independently-valuable checkpoint (Phase 1 alone is contributed Mathlib
infrastructure; Phase 5 alone gives finite renormalized entropy *internal* to QIQT-H).  Nothing is a monolith
that only pays off at the end.

**What it will NOT deliver, ever, by construction:** the **`1/4ℓ_P²` coefficient.** That is the UV datum (GPT
rank-1 fatal obstruction) — it requires a microscopic theory that fixes the entropy density, which no approach
(including AdS/CFT) derives from below for general screens.  The campaign reduces (P4) to **the single edge-
operator normalization `⟨A_edge⟩ = A(∂R)/4ℓ_P²`** and derives the *bound* side from positivity — it does not and
cannot manufacture the coefficient.  Stated up front so no phase is mistaken for "deriving gravity from nothing."

## 1. What exists (the foundations to build on)

- **Modular flow** `modUnitary S t = Δ^{it}` — strongly-continuous one-parameter unitary group (group law,
  adjoint, unitarity, strong continuity all proved).
- **Modular automorphism** `modularAut S t` (Increment 1a-0) — the `*`-automorphism group `σ_t` to cross by.
- **Modular Hamiltonian** spectral function `kFn = −entropyDensity` + generator identity `Δ^{it} = e^{−itK}`
  (JLMS Stage 1); the **first law** `cgpEntropy = ∫ kFn dμ = ⟨K⟩` (JLMS Stage 2); Klein positivity
  `cgpEntropy_nonneg`.
- **Spectral machinery**: `PVM_of_selfAdjoint`, `borelFC` (bounded Borel functional calculus), `rvdRC`
  (`R = P+Q`), `scalarMeasure`/`specMeasure`.
- **Mathlib**: `MeasureTheory.Lp` (Bochner vector-valued), `DomMulAct`/`DomAddAct` (Lp action by
  measure-preserving translation), `VonNeumannAlgebra` + `.commutant` (structural), `ContinuousLinearMap.adjoint`,
  `LinearPMap` (unclosed unbounded maps), CFC.
- **Mathlib LACKS (the wall)**: operator-valued `Lp` multiplication, unbounded self-adjoint operator theory,
  Stone's theorem, von Neumann **crossed products**, the **dual-weight trace**, Type II classification.

## 2. The phases (each an axiom-free checkpoint; ref §s in brackets)

### Phase 1 — operator-valued `Lp` multiplication: the matter representation `π(a)`  *(TRACTABLE, the first brick)*
*New file `QIQTH/CrossedProduct/MatterRep.lean`.*  Build the fiberwise postcomposition on `L²(ℝ; H)`:
1. **1.1 — the fiber map.** For a bounded-measurable family `T : ℝ → (H →L[ℂ] H)` with `sup ‖T s‖ ≤ M`, the
   pointwise map `ξ ↦ (s ↦ T s (ξ s))` is `AEStronglyMeasurable` (compose `T` measurable with `ξ`'s
   representative; the operator-application is continuous).  Take `T s := σ_{-s}(a) = modularAut S (-s) a`,
   `M = ‖a‖` (since `‖σ_{-s}(a)‖ = ‖a‖`, unitary conjugation).
2. **1.2 — the `Lp` bound ⟹ `π(a)` as a CLM.** `‖T s (ξ s)‖ ≤ ‖a‖·‖ξ s‖` pointwise ⟹ `eLpNorm(π(a)ξ) ≤
   ‖a‖·eLpNorm(ξ)` ⟹ `MemLp`; bundle `π(a) : L²(ℝ;H) →L[ℂ] L²(ℝ;H)` with `‖π(a)‖ ≤ ‖a‖`.
3. **1.3 — `π` is a unital `*`-homomorphism.** `π(a·b) = π(a)·π(b)`, `π(a⋆) = π(a)⋆`, `π(1) = 1`, `π` ℂ-linear
   and bounded (uses `modularAut_mul`/`_one`/`_star` fiberwise).
**Risk: medium** (the `Lp`-quotient + `AEStronglyMeasurable` plumbing is the real work; no unbounded operators).
**Buys:** the matter side of the crossed product, and contributed Mathlib infrastructure (operator-valued `Lp`
multiplication) of independent value.

### Phase 2 — the translation unitary group `λ_t`  *(TRACTABLE)*
*New file `QIQTH/CrossedProduct/Translation.lean`.*  Bundle the existing `DomAddAct` Lp-action into a continuous
ℂ-linear **unitary group**: `λ_t : L²(ℝ;H) →L[ℂ] L²(ℝ;H)` from `DomAddAct.mk t • ·`, with `λ_0 = 1`,
`λ_{s+t} = λ_s ∘L λ_t` (from `compMeasurePreserving_comp` + additivity of translation), isometry
(`norm_compMeasurePreserving`), and unitarity (`λ_{-t} = λ_t⁻¹`).  **Risk: low–medium** (bundling an
`AddMonoidHom` action up to a CLM unitary group; `measurePreserving_add_right` for volume).
**Buys:** the clock translation group — the `L²(ℝ)` clock factor.

### Phase 3 — the covariance relation + the crossed product  *(TRACTABLE given 1–2)*
*New file `QIQTH/CrossedProduct/Covariance.lean`.*  Prove the defining identity
```
λ_t ∘L π(a) ∘L λ_{-t} = π(σ_t a)          (= π(modularAut S t a))
```
(fiberwise: `(λ_t π(a) λ_{-t} ξ)(s) = σ_{-(s-t)}(a)(ξ s) = σ_t(σ_{-s}(a))(ξ s)`, via `modularAut_add`).  Define
the crossed product `M ⋊_σ ℝ` as the von Neumann algebra generated by `π(M) ∪ λ(ℝ)` (using Mathlib
`VonNeumannAlgebra` generation / double commutant).  **Risk: medium** (the covariance is the `modularAut_add`
algebra; assembling the generated vN algebra is structural).  **Buys:** the crossed product algebra itself.

### Phase 4 — unbounded self-adjoint operators + Stone's theorem  *(FRONTIER — open Mathlib target)*
*New file `QIQTH/Spectral/Unbounded.lean` (+ Stone).*  The generators `K` (modular Hamiltonian) and `X` (clock
energy) are unbounded.  [Conway Ch. X; Takesaki §1]
1. **4.1** closed densely-defined operators via `LinearPMap`; adjoint `T†`, `IsSelfAdjoint` for unbounded `T`;
   the **Cayley transform** `U = (T−i)(T+i)⁻¹` ↔ self-adjoint `T`, transporting the Phase-1/PVM spectral theorem.
2. **4.2 — Stone's theorem**: strongly-continuous one-parameter unitary group `t ↦ U_t` ↔ self-adjoint generator
   `A` with `U_t = e^{itA}`.  Apply to `modUnitary` ⟹ `K = −log Δ` as a genuine self-adjoint operator
   (completing JLMS Stage 1's spectral function to an operator); apply to `λ_t` ⟹ the **clock energy `X`**.
3. **4.3** define `A_edge := X / c` — a genuine, independently-defined self-adjoint operator (NOT vacuous), and
   the dressed modular generator `K̃ = K + X`.  **This is where Increment 1c lands, frontier-gated on Stone.**
**Risk: high** (unbounded operator theory + Stone is a multi-week Mathlib-grade build).  **Buys:** the area edge
operator as a real operator; `A_edge` exists.

### Phase 5 — the dual-weight trace + Type II  *(DEEP FRONTIER)*
*New file `QIQTH/CrossedProduct/Trace.lean`.*  [Takesaki; CLPW; Witten]  Construct the canonical
faithful-normal-semifinite **trace `τ`** on `M ⋊_σ ℝ` (the dual weight of the modular state), and prove the
**Type II_∞ defining scaling** `τ ∘ θ_s = e^{−s} τ` (`θ` the dual action).  Then the **finite renormalized
entropy** `S_τ(ρ) = −τ(h_ρ log h_ρ)` — finite where the Type III matter entropy diverged (the "one infinity
removed", now *internal* to QIQT-H rather than the cited CLPW result).  **Risk: very high** (the dual-weight
trace is research-grade).  **Buys:** finite regional entropy from first principles in QIQT-H.

### Phase 6 — the area operator, JLMS, and the FQ bound  *(THE PAYOFF)*
*New file `QIQTH/CrossedProduct/JLMS.lean`.*  With the trace (Phase 5):
1. **6.1** the area normalization `⟨A_edge⟩ = A(∂R)` — **the one carried UV datum** (`1/4ℓ_P²`, §0).
2. **6.2** the **JLMS relation** `K̃ = A_edge·(1/4ℓ_P²) + K_bulk` as a theorem of the trace (the crossed-product
   modular Hamiltonian splits into the edge/area part and the bulk matter part).
3. **6.3** the **FQ bound** `S(ρ_R) ≤ A/4ℓ_P²` from `cgpEntropy_nonneg` (JLMS Stage 2 positivity) + the
   normalization — **(P4)'s bound becomes a theorem**, conditional only on the edge normalization.
**Risk: medium given 1–5.**  **Buys:** (P4) reduced from postulate to "the area-operator normalization," with
the bound derived — the campaign's goal.

## 3. Dependency graph
```
Phase 1 (π(a)) ─┐
Phase 2 (λ_t) ──┴─→ Phase 3 (covariance, crossed product) ─→ Phase 5 (trace) ─→ Phase 6 (JLMS, FQ bound)
Phase 4 (unbounded + Stone) ───────────────────────────────┘  (K̃, A_edge as operators feed Phases 5–6)
```
Phases 1–3 are **tractable** (bounded operators, existing Lp/vN infrastructure) and independently valuable.
Phase 4 (Stone) and Phase 5 (trace) are the **frontiers**.  Phase 6 is the payoff once 4–5 land.

## 4. Realistic stopping points (value at each)
- **After Phase 1:** operator-valued `Lp` multiplication — contributed Mathlib infrastructure.
- **After Phase 3:** the crossed product `M ⋊_σ ℝ` as a Lean object — the gravitational dressing exists.
- **After Phase 4:** `A_edge` is a genuine operator — JLMS Increment 1c done; the "is it vacuous?" objection closed.
- **After Phase 5:** finite renormalized regional entropy, internal to QIQT-H (not cited from CLPW).
- **After Phase 6:** (P4) reduced to the edge normalization + the bound derived — the goal, with only the
  `1/4` coefficient carried as the irreducible UV datum.

## 5. Verification (per phase/sub-step)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = standard 3 (or a clearly
labelled cited input with an `AxiomAudit` note); `bash scripts/axiom_budget_check.sh` budget 0 (never raised
without a written audit justification); wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per sub-step with
the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; refresh `reports/`.

## 6. Cross-check references
Conway (spectral theorem, Stone, unbounded ops); Takesaki (modular theory, crossed products, dual weights);
Rieffel–Van Daele (bounded RvD modular objects — already used); Chandrasekaran–Longo–Penington–Witten 2022 +
Witten "Gravity and the crossed product" (the Type II area construction); Sorce arXiv:2302.01958 (type
classification).  Aligns with `TOMITA_TAKESAKI_ROADMAP.md` (this is its goal-directed, area-operator-focused
specialization).

## Progress log
- **Phase 0 (foundations) ✅** — modular flow, modular automorphism `σ_t` (Increment 1a-0), the JLMS modular-energy
  engine (Stages 1–2), spectral/`borelFC` machinery — all in place and axiom-free.
- **Phase 1.1 ✅** (`QIQTH/CrossedProductRep.lean`) — the matter-rep fiber `s ↦ σ_{-s}(a)(ξ s) = Δ^{-is} a Δ^{is}(ξ s)`
  is `AEStronglyMeasurable` on `L²(ℝ;H)` (`aesm_matterFiber`), via `aesm_modUnitary_comp` (the modular flow along a
  measurable time reparametrization preserves measurability) and the generic helper
  `stronglyMeasurable_uncurry_clmFamily` (the uncurry of a strongly-continuous CLM family is strongly measurable —
  stated for an opaque family so `modUnitary`'s `borelFC` is never unfolded). `H` separable (`SecondCountableTopology`),
  the physical one-particle assumption. Axiom-free (std 3); wired into AxiomAudit; budget 0.
  - *Overcoming the wall:* the earlier `whnf`/`isDefEq` blowup was **not** the uncurry lemma (which builds in
    isolation) — it was a **divergent instance search from a missing `BorelSpace H`** (needed by the pushforward
    `comp_aemeasurable`). Fix: (i) generic opaque-family helper (no `modUnitary` unfolding), (ii) `[BorelSpace H]`
    present, (iii) `maxHeartbeats 1000000`. The operator-valued `Lp`-measurability route is therefore tractable.
- **Phase 1.2 (Lᵖ membership) ✅** (`CrossedProductRep.lean`) — `norm_modularAut_apply_le` (the contraction
  `‖σ_t(a) v‖ ≤ ‖a‖·‖v‖`, from the modular unitaries being isometries) + `memLp_matterFiber`: for `ξ ∈ L²(ℝ;H)`,
  the fiber `s ↦ σ_{-s}(a)(ξ s) ∈ L²` (Phase-1.1 measurability + domination via `MemLp.of_le_mul`). Axiom-free
  (std 3); wired into AxiomAudit; budget 0.
- **NEXT: Phase 1.2 (bundling)** — `matterRep S a : L²(ℝ;H) →L[ℂ] L²(ℝ;H)`, `ξ ↦ (memLp_matterFiber).toLp`, with
  `map_add`/`map_smul` (a.e. fiberwise linearity) and `‖π(a)‖ ≤ ‖a‖` (`LinearMap.mkContinuous`). Then 1.3 (`π` a
  unital `*`-homomorphism). Standard `Lp`-bundling work.
