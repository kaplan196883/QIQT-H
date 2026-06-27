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

**The `1/4` — what IS and is NOT derived (precise, three distinct things):**
1. **The `1/4` geometric RATIO `= (conical 4π)/(EH 16π)` — ✅ DERIVED.**  `SAKHAROV_KG_PLAN.md` (Sakharov /
   induced-gravity, Stages A+B) derives it non-circularly — independent of the matter coefficient and the UV
   regulator — and it is **machine-checked axiom-free in `QIQTH/SakharovRatio.lean`** (`sakharov_ratio`,
   `geometric_quarter`, `heatkernel_ratio_eq_geometric`).  So the *coefficient `1/4`* is NOT a free input.
2. **The area *scaling* `S ∝ A(∂R)` (entropy ∝ boundary) — frontier (M3).**  The `n=1` Williamson piece is done
   (`GaussianStateEntropy.lean`); the `N`-mode symplectic scaling is the cited Mathlib-grade frontier.
3. **The absolute normalization — the *value* of `G`/`ℓ_P` (equivalently the edge normalization
   `⟨A_edge⟩ = A(∂R)/4ℓ_P²`) — ⛔ carried, never derived, by construction.**  This is the genuine UV/species
   datum (GPT rank-1 obstruction): it needs a microscopic theory fixing the entropy *density*, which no approach
   (incl. AdS/CFT) derives from below for general screens.

**So what THIS campaign delivers:** it reduces (P4) to the single edge-operator normalization `⟨A_edge⟩ =
A(∂R)/4ℓ_P²` and derives the **bound** side `S(ρ_R) ≤ A/4ℓ_P²` from positivity (Phase 6).  Combined with the
Sakharov-derived `1/4` ratio, the only carried datum is the *value of `G`* (the edge normalization's scale) —
NOT the coefficient.  Stated up front so no phase is mistaken for "deriving gravity from nothing," and so the
`1/4` ratio derivation (item 1) is correctly credited rather than lumped into the carried datum.

## 1. What exists (the foundations to build on)

- **Modular flow** `modUnitary S t = Δ^{it}` — strongly-continuous one-parameter unitary group (group law,
  adjoint, unitarity, strong continuity all proved).
- **Modular automorphism** `modularAut S t` (Increment 1a-0) — the `*`-automorphism group `σ_t` to cross by.
- **Modular Hamiltonian** spectral function `kFn = −entropyDensity` + generator identity `Δ^{it} = e^{−itK}`
  (JLMS Stage 1); the **first law** `cgpEntropy = ∫ kFn dμ = ⟨K⟩` (JLMS Stage 2); Klein positivity
  `cgpEntropy_nonneg`.
- **Spectral machinery**: `PVM_of_selfAdjoint`, `borelFC` (bounded Borel functional calculus), `rvdRC`
  (`R = P+Q`), `scalarMeasure`/`specMeasure`.
- **The `1/4` geometric ratio — DERIVED** (`SAKHAROV_KG_PLAN.md` + `QIQTH/SakharovRatio.lean`, axiom-free):
  `S_ent/(A/G_ind) = (conical 4π)/(EH 16π) = 1/4`, circularity-clean (independent of matter coefficient and
  regulator).  So Phase 6's `⟨A_edge⟩ = A(∂R)/4ℓ_P²` carries only the *value of `G`*, not the coefficient.
- **The position/momentum spectral substrate** (this session, `Spectral/MultiplicationOp`, `PositionPVM`,
  `MomentumPVM`, `PVMConj`, `TranslationFlow`, `ModulationFlow`): the position & momentum PVMs, both **strongly-
  continuous one-parameter unitary groups** `e^{itP}` (`translationLp`) and `e^{isX}` (`modulationLp`), the Weyl
  CCR, both Born-statistics layers.  These C₀-groups are the concrete inputs Stone (Phase 4.2) consumes.
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

**✅ Phase 6 ALGEBRAIC CORE DONE (`QIQTH/FQBoundConditional.lean`, axiom-free; GPT-5.5-pro's highest-leverage pivot
2026-06-27):** the conditional FQ bound as pure algebra, hypotheses = the Phase-5/JLMS obligations (theorem args,
**not** axioms): `fq_bound_of_slack` (`0≤slack ∧ S+slack≤areaTerm ⟹ S≤areaTerm`); `fq_bound_of_jlms` (JLMS first
law `S = ⟨A_edge⟩·c + ⟨K_bulk⟩ − D` with `0≤D` ⟹ `S ≤ ⟨A_edge⟩·c + ⟨K_bulk⟩`); `fq_bound_area_only` (`+ bulk≤0` ⟹
bare area floor `S ≤ ⟨A_edge⟩·c`); `fq_bound_of_slack_ennreal` (ℝ≥0∞, no subtraction-with-∞). The coefficient `c =
1/4ℓ_P²` is a free parameter (carried UV datum, never assigned).

**✅ Phase 6 GROUNDED IN THE PROVED RELATIVE ENTROPY (`QIQTH/FQBoundCGP.lean`, axiom-free):** `fq_bound_cgp`
discharges the `0 ≤ slack` hypothesis with the *machine-checked* `cgpEntropy_nonneg` (one-particle CGP modular
relative entropy ≥ 0). So `S_vN ≤ areaTerm` holds whenever the **JLMS master inequality**
`S_vN + cgpEntropy S ξ ≤ areaTerm` holds (`areaTerm = ⟨A_edge⟩/4ℓ_P²`, the Phase-5 trace's output): the slack
positivity is no longer hypothesized — only the master inequality remains.

**✅ Phase 6 AS A CERTIFICATE-RELATIVE THEOREM (`QIQTH/FQBoundCGP.lean`, axiom-free; GPT-5.5-pro round-2 strategy
2026-06-27 — the DonaldSystem typeclass+instance pattern that made the finite core axiom-free):** `class
Phase5Master (S ξ) (SvN areaTerm : ℝ)` bundles the JLMS balance `SvN + cgpEntropy S ξ + remainder = areaTerm` with
`remainder_nonneg`; `phase5_master_ineq` derives the master inequality; **`fq_bound_of_phase5` proves P4's bound
`SvN ≤ areaTerm` UNCONDITIONALLY RELATIVE to the `Phase5Master` certificate** (via `fq_bound_cgp` + the proved
`cgpEntropy_nonneg`).  So the holographic area floor is now a *theorem modulo a named, non-vacuous physics interface*
(`Phase5Master`) — not an axiom.

**✅ Manifest holographic form (`holographic_area_floor`):** specializing to `areaTerm = edgeArea/(4·ℓ_P²)`, the
exported bound now reads literally **`SvN ≤ edgeArea/(4ℓ_P²)`** = `S ≤ A/4ℓ_P²` (the `1/4ℓ_P²` coefficient manifest
in the statement; `edgeArea = ⟨A_edge⟩ = A(∂R)` the carried UV datum, never assigned; `ellP` the Planck length).

**Remaining to instantiate Phase 6:** the Phase-5 dual-weight trace must produce a `Phase5Master` instance (a `≥ 0`
remainder + the JLMS balance) — the genuine Mathlib-grade gap. The richer `DualWeightTrace` (τ, dual action θ,
`τ∘θ_s = e^{−s}τ`, A_edge positivity, area_finite, first law, state_match) extends `Phase5Master`; and a
`HolographicContext` (spec fields `S_vN = vonNeumannEntropy ρR`, `ρR = boundary restriction`) would make the final
statement faithful to the actual von Neumann entropy (the deeper soundness layer, needing Phase-5 objects). NOT
blocked on the PVM/`PVM_of_selfAdjoint` (off the critical path).
Per the same audit, do NOT block this on the PVM/`PVM_of_selfAdjoint` (off the critical path); `IsSelfAdjoint
A_edge` (already proved) suffices to call the clock energy a genuine observable.

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
- **Phase 1.2 (bundling) ✅** — `matterRep S a : L²(ℝ;H) →L[ℂ] L²(ℝ;H)` (`matterRepFun` + `LinearMap.mkContinuous`):
  `matterRepFun_add`/`matterRepFun_smul` (a.e. fiberwise linearity via `Lp.ext_iff` + `Lp.coeFn_add/smul`),
  `matterRepFun_norm_le` (`‖π(a)ξ‖ ≤ ‖a‖·‖ξ‖` via `Lp.norm_le_norm_of_ae_le` against `‖a‖•ξ`). So **`π(a)` is a
  genuine bounded operator with `‖π(a)‖ ≤ ‖a‖`.** Axiom-free; budget 0.
- **Phase 1.3 (algebra homomorphism) ✅** — `matterRep_one` (`π(1)=1`) + `matterRep_mul` (`π(a·b)=π(a)∘π(b)`),
  via `matterRepFun`-level a.e. identities (`modularAut_one`/`modularAut_mul`) + `ContinuousLinearMap.ext`. So
  **`π : M → B(L²(ℝ;H))` is a unital algebra homomorphism** — the matter side of the crossed product. Axiom-free;
  budget 0; wired into AxiomAudit.
- **Phase 1.3 (the `*`) ⛔ recorded blocker** — `modularAut_adjoint` (`σ_t(a⋆)=σ_t(a)⋆`) ✅ done; but the operator
  statement `adjoint(π(a)) = π(a⋆)` is **blocked on an Lp/RCLike instance diamond**: the *math is complete* (via
  `MeasureTheory.L2.inner_def` `⟨ξ,η⟩=∫⟨ξ s,η s⟩` + the fiberwise adjoint, `⟨π(a)ξ,η⟩=⟨ξ,π(a⋆)η⟩` pointwise), but
  `ContinuousLinearMap.eq_adjoint_iff` fails to unify the `ℂ` semiring instance on `Lp H 2 volume`
  (`Complex.instSemiring` vs the `Field`-derived `RCLike` path — a Mathlib instance-diamond, orthogonal to the
  physics; the *statement* elaborates, only the proof's unification fails). The substantive content — `π` a unital
  **algebra** homomorphism — is complete.

### Phase 1 status — operator-valued Lp multiplication DONE (the matter representation π(a))
**Delivered (axiom-free, budget 0):** `π(a) = matterRep S a : L²(ℝ;H) →L[ℂ] L²(ℝ;H)`, a bounded operator
(`‖π(a)‖ ≤ ‖a‖`) and a **unital algebra homomorphism** `M → B(L²(ℝ;H))` (`matterRep_one`, `matterRep_mul`),
built from scratch over a strongly-continuous (non-norm-measurable) modular flow — the operator-valued Lp
multiplication that was the "real wall" of Phase 1. The matter side of the crossed product `M ⋊_σ ℝ` exists.
**Residual:** the `*`-property (adjoint), blocked on an Lp/RCLike instance diamond (not a math gap).
**NEXT (separate):** Phase 2 (translation unitary group λ_t via `DomAddAct`), Phase 3 (covariance), then the
frontiers (Stone, the trace). The `1/4` coefficient stays the cited UV datum throughout.

### Phase 4 (e.s.a. route) — the Gårding mollifier foundation ✅ (first step into the shared analytic frontier)
**Delivered (axiom-free, budget 0, `QIQTH/Spectral/Garding.lean`):** the constructive entry to essential
self-adjointness (= `Range(·±i)` dense), shared by all three generators. `mollify U φ x := ∫ φ(t) U_t x dt`
(the Gårding mollified vector); `mollify_integrable` (the integrand is integrable — continuous × compact
support); `mollify_apply_flow` — the **flow-shift identity** `U_s x_φ = ∫ φ(t) U_{s+t} x dt` (`U_s` passes
through the Bochner integral via `integral_comp_comm`, then the group law shifts the orbit). This is the
algebraic core: differentiating the RHS in `s` under the integral is exactly what will place `x_φ` in the smooth
domain (hence the domain dense). Plus `mollify_apply_flow_cov` — the orbit in **differentiation-ready form**
`U_s x_φ = ∫ φ(u − s) U_u x du` (change of variables, `integral_add_right_eq_self`): the `s`-dependence now sits
entirely in the smooth `φ(u − s)`, the `U_u x` factor `s`-independent. And `mollify_integrand_hasDerivAt` — the
**calculus core** (the `h_diff` of `hasDerivAt_integral_of_dominated_loc_of_deriv_le`): `σ ↦ φ(u−σ) • U_u x` has
derivative `−φ'(u−σ₀) • U_u x` (chain rule `scomp` + `smul_const`). Plus the measurability hypotheses
(`mollify_shifted_aestronglyMeasurable` = `hF_meas`, `mollify_deriv_aestronglyMeasurable` = `hF'_meas`) and
`mollify_neg_deriv_eq` (the derivative value `= −x_{φ'}`, a Gårding vector — smooth subspace closed under the
generator). **Carried frontier (now a SINGLE hypothesis):** the integrable dominating bound `supₛ |φ'(u−s)|·‖x‖`
(compact support of `φ'` ⟹ indicator of a compact set) is the only missing input to
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`. Its two analytic pillars are now in hand:
`exists_norm_le_of_compactSupport` (`φ'` bounded) + `exists_support_subset_of_compactSupport` (`φ'` vanishes
outside a ball).
**★★ MILESTONE — the Gårding differentiation is DONE; the smooth domain is NONEMPTY.**
`integrable_indicator_closedBall_const` (the bound `C·M·𝟙_K` integrable) + `mollify_orbit_hasDerivAt` (the orbit
`s ↦ ∫ φ(u−s) U_u x du` differentiable at `0`, derivative `∫ (−φ'(u)) U_u x du`, via the dominated-derivative
lemma; domination = case split on `\|u\| ≤ ρ+1`, needs uniform `‖U_u x‖ ≤ M`) ⟹ `mollify_mem_stoneDomain`:
**`mollify U φ x ∈ stoneDomain U`** — every Gårding vector is in the smooth domain of the Stone generator.
The hardest analytic step (differentiation under the Bochner integral) is complete, axiom-free.
Also ✅ the **Gårding-approximation identity** (`mollify_sub`: `x_φ − (∫φ)·x = ∫ φ(t)(U_t x − x)`;
`norm_mollify_sub_le`: `‖x_φ − (∫φ)·x‖ ≤ ∫ ‖φ(t)‖·‖U_t x − x‖`) and the **ε-bound** `norm_mollify_sub_le_uniform`
(`‖U_t x − x‖ ≤ ε` on `supp φ` ⟹ `‖x_φ − (∫φ)·x‖ ≤ ε·∫‖φ‖`) — with `∫φ = 1`, `φ ≥ 0` near `0`, this is `≤ ε`
and `→ 0` by strong continuity, i.e. `x_φ → x`. Plus the **density assembly** `exists_mem_stoneDomain_norm_sub_le`
(combines the two Gårding lemmas: a normalized `C¹_c` mollifier averaging to `x`, supported where `‖U_t x−x‖ ≤ ε`,
gives `y = x_φ ∈ stoneDomain U` with `‖y − x‖ ≤ ε·∫‖φ‖` ⟹ for every `x,ε` a smooth-domain vector within `ε` =
density). **★★★ MILESTONE — THE SMOOTH DOMAIN IS DENSE (`stoneDomain_dense`):** for a contractive strongly-continuous
family, `Dense (stoneDomain U)` — a normalized `C^∞` bump (`ContDiffBump.normed`, ℝ→ℂ-coerced, supported in
`(−δ/2,δ/2)` with `δ` from strong continuity, `exists_delta_norm_sub_lt`) fed to the density assembly yields a
Gårding vector `x_φ ∈ stoneDomain U` with `‖x_φ − x‖ < r`. The entire Gårding-density argument is now
machine-checked, axiom-free. **This discharges the density hypothesis of `stoneGen_le_adjoint` — the last
analytic input to essential self-adjointness.** Also ✅ `stoneGen_subset_adjoint` — **the unconditional
`A ⊆ A†`** (`stoneGen U ≤ (stoneGen U)†`), composing the conditional `stoneGen_le_adjoint` with
`stoneDomain_dense`: the symmetric densely-defined generator is contained in its adjoint with no carried
density hypothesis. Also ✅ `stoneGen_isClosable` — **the closure `Ā` exists** (`(stoneGen U).IsClosable`): `A`
has a closed extension `A†` (`adjoint_isClosed` + density) and `A ⊆ A†`, so it is closable. Also ✅ the **resolvent foundation** (`resolvent U x := ∫₀^∞ e^{−t} U_t x dt = (1−iA)⁻¹ x`;
`resolvent_integrand_integrableOn` — the half-line integrand is `IntegrableOn (0,∞)` via exp-decay domination
of the bounded orbit) + `norm_resolvent_le` (**the resolvent is a contraction** `‖R x‖ ≤ ‖x‖`, since
`∫₀^∞ e^{−t}=1` ⟹ `R=(1−iA)⁻¹` bounded) + `resolvent_apply_flow` (**the flow-on-resolvent identity**
`U_s (R x) = ∫₀^∞ e^{−t} U_{s+t} x dt`, the algebraic core) + `resolvent_add`/`resolvent_smul` (**`R` is ℂ-linear**,
so a bounded ℂ-linear operator with `norm_resolvent_le`) + `resolvent_comm_flow` (**`R` commutes with the flow**
`U_s(Rx)=R(U_s x)`, hence with `A`) + `resolvent_apply_flow_cov` (**the differentiation-ready form**
`U_s(Rx)=e^s ∫_s^∞ e^{−u}U_u x du`, change of vars `u=s+t` via `setIntegral_preimage_emb`) +
`resolvent_halfline_hasDerivAt` (**the FTC** `d/ds ∫_s^∞ e^{−u}U_u x du = −(e^{−s}U_s x)`, via the splitting
`integral_Ioi_sub_Ioi'` + `integral_hasDerivAt_right`). **★★ MILESTONE — the RESOLVENT IDENTITY**:
`resolvent_orbit_hasDerivAt` (`d/ds U_s(Rx)|₀ = Rx−x`) ⟹ `resolvent_mem_stoneDomain` (**`R x ∈ stoneDomain U`**) +
`resolvent_stoneGen` (**`stoneGen U(Rx) = −i(Rx−x)`**, i.e. `(A+i)(R x)=i x`, so `Range(A+i) ⊇ {i x}=H`). **The
deficiency-index-zero fact making the generator essentially self-adjoint is now machine-checked.** Also ✅
`stoneGen_add_I_surjective` — **`A+i` surjective, `Range(A+i)=H`** (`∀ y, ∃ z ∈ stoneDomain, A z + i z = y`, witness
`z := R(−i y)`). **★★ MILESTONE — both deficiency indices zero:** `stoneGen_sub_I_surjective` — **`Range(A−i)=H`**
(via the reversed group `t↦U_{−t}` with generator `−A`, `stoneGen_reversed_eq` + bridge). Both `Range(A±i)=H` ⟹
the e.s.a. criterion is met. Also ✅ `deficiency_add_trivial`/`deficiency_sub_trivial` (**the deficiency subspaces
are trivial**, `ker(A†∓i)=Range(A±i)^⊥=0` in canonical inner-product form, via `inner_self_eq_zero`) +
`ker_adjoint_sub_I_trivial`/`ker_adjoint_add_I_trivial` (**`A†` has no `±i`-eigenvectors** in Mathlib's adjoint API,
via `adjoint_isFormalAdjoint.symm`). **★★★ MILESTONE — the generator is SELF-ADJOINT:** `stoneGen_isSelfAdjoint` —
`IsSelfAdjoint (stoneGen U)` (`A† = A`), via the *basic criterion* (`A⊆A†` + `Range(A±i)=H` ⟹ `A=A†`,
`eq_of_le_of_domain_eq`, no Cayley needed). `X=A_edge`, `P`, `K` are genuine self-adjoint unbounded operators. **★★★ Instantiated for all three named
generators:** `clockEnergy_isSelfAdjoint` (`X = A_edge = stoneGen clockTransl`), `momentumOp_isSelfAdjoint`
(`P = stoneGen translationCLM = −i d/dx`), `modularGen_isSelfAdjoint` (`K = stoneGen (modUnitary S)`, the JLMS
modular Hamiltonian) — each `IsSelfAdjoint`, axiom-free.
Also ✅ `stoneGen_add_I_bijective` (**`A+i` is a bijection `dom(A)→H`** — injective + surjective — so `(A+i)⁻¹`
exists, the Cayley-transform foundation).
Also ✅ `cayley` + `norm_cayley` (**the Cayley transform `V=(A−i)(A+i)⁻¹` is built and is an isometry `‖V y‖=‖y‖`**:
`cayleyEquiv = Equiv.ofBijective _ stoneGen_add_I_bijective` is `A+i:dom(A)≃H`, its `.symm` is `(A+i)⁻¹`,
`cayley y := (A−i)((A+i)⁻¹ y)`; `‖V y‖=‖(A−i)z‖=‖(A+i)z‖=‖y‖` for `z=(A+i)⁻¹y` via the Cayley isometry).
Also ✅ `stoneGen_sub_I_bijective` + `cayley_bijective` (**`V` is a unitary** — `A−i:dom(A)→H` is also a bijection,
so `V=(A−i)∘(A+i)⁻¹` is bijective, and with `norm_cayley` `V` is bijective + isometric = unitary).
Also ✅ `cayleyEquiv_symm_add/_smul`, `cayley_add/_smul`, `cayleyLM`, **`cayleyUnitary : H ≃ₗᵢ[ℂ] H`** (`V` bundled
as a genuine **unitary operator**: `(A+i)⁻¹` ℂ-linear ⟹ `V` ℂ-linear ⟹ `cayleyLM : H →ₗ[ℂ] H` ⟹
`cayleyUnitary = LinearEquiv.ofBijective cayleyLM cayley_bijective` + `norm_map' := norm_cayley`).
Also ✅ `cayley_mem_unitary` + `cayleyUnitaryElt` (**`V` is a C\*-algebra unitary element** `∈ unitary (H →L[ℂ] H)`,
`star V * V = V * star V = 1` — the **CFC doorway**: `cfc f V` exists, `spectrum ℂ V ⊆ circle`).
Also ✅ `cayley_spectrum_subset_circle` (**`spectrum ℂ V ⊆ Metric.sphere 0 1`** — the circle-PVM's support; the
inverse Cayley map `z↦i(1+z)(1−z)⁻¹` pulls `S¹∖{1}` to the real spectrum of `A`).
Also ✅ `cayley_one_sub` + `cayley_one_sub_injective` (**`1` is not an eigenvalue of `V`**, `ker(1−V)=0`:
`y−V y = 2i·(A+i)⁻¹y` + `(A+i)⁻¹` injective — the precise condition that `V` is the Cayley transform of a
densely-defined self-adjoint `A`, with `A = i(1+V)(1−V)⁻¹` well-defined on `ran(1−V)` = the smooth domain).
Also ✅ `cayley_one_sub_denseRange` (**`1−V` has dense range** — `ran(1−V)=2i·dom(A)=2i·stoneDomain U`, dense via
`stoneDomain_dense` + `Homeomorph.smulOfNeZero`): with `ker(1−V)=0` this is the **full** characterization that `V`
is the Cayley transform of a densely-defined self-adjoint `A`.
Also ✅ `cayley_spectrum_isCompact` (**`σ(V)` compact** — with circle containment, a compact subset of `S¹`: the
Riesz–Markov precondition, `C(σV)=C_c(σV)`, for building the scalar spectral measures `μ_x` via `RealRMK.rieszMeasure`).
Also ✅ `cayley_isStarNormal` (**`IsStarNormal V`** — the ℂ-CFC predicate) + `nonneg_re_inner_nonneg`
(**`0≤T ⟹ 0≤re⟪x,Tx⟫`** — the functional-positivity step: `cfc f V ≥ 0` ⟹ `f↦re⟪x,cfc f V x⟫` positive ⟹ RMK→μ_x).
Also ✅ `cayley_cfc_id` `[Nontrivial H]` (**`cfc id V = V`** — the `C(σV)`-level form of `V=∫_{S¹}z dE(z)`; the
coordinate function applied to `V` returns `V`, the continuous-FC shadow of the PVM identity).
*Obstruction RESOLVED:* the ℂ-normal CFC local-instance theorem IS enableable via `attribute [local instance]` +
`CStarAlgebra.ContinuousLinearMap` + `CFC.Basic` imports + `[Nontrivial H]`; the cfc-of-`V` route is open.
Also ✅ `cayley_cfc_one` (`cfc 1 V = 1`, resolution of identity `∫1 dE=1`) + `cayley_cfc_sq_re_inner_nonneg`
(**RMK functional positivity** — `0 ≤ re⟪x, cfc(conj f·f) V x⟫ = ‖cfc f V x‖²` via `(cfc f V)⋆(cfc f V) ≥ 0`; the
`|f|²` generate the nonneg cone, so `g↦re⟪x,cfc g V x⟫` is a positive functional ⟹ `RealRMK.rieszMeasure` gives μ_x).
Also ✅ `cayley_cfc_re_inner_nonneg_of_nonneg` (**RMK functional positive on the WHOLE nonneg cone** — `0≤re⟪x,cfc g V x⟫`
for any `g` continuous, real, `≥0` on `σ(V)`, via `g=|√g|²` + `cfc_congr` + the square lemma): the exact
`0≤g ⟹ 0≤Λg` a positive linear functional needs.
Also ✅ `cayley_cfc_re_inner_add` + `cayley_cfc_re_inner_smul` (**the functional is ℝ-linear** — additive via
`cfc_add`, homogeneous via `cfc_const_mul`). **With positivity, `g↦re⟪x,cfc g V x⟫` is now a fully machine-checked
positive ℝ-linear functional.**
Also ✅ `expectationCLM x` (`Φ_x:(H→L[ℂ]H)→L[ℂ]ℂ`, `T↦⟪x,Tx⟫`) + `reExpectationCLM x` (`(H→L[ℂ]H)→L[ℝ]ℝ`,
`T↦re⟪x,Tx⟫`) — **the bundled RMK functional** (postcomposition `Complex.reCLM∘Φ_x` done); precompose `cfcHom V` +
`ℝ↪ℂ` embedding and it *is* `g↦re⟪x,cfc g V x⟫`.
Also ✅ `cfcReExpectationCLM` `[Nontrivial H]` (**RMK functional on `C(σV,ℂ)`** — `φ↦re⟪x,cfcHom V φ x⟫` =
`reExpectationCLM x ∘ (cfcL V)|_ℝ`; the **cfcHom precomposition is done**, only `ℝ↪ℂ` restriction + `→ₚ[ℝ]`/`C_c`
packaging remain).
Also ✅ `realCfcReExpectationCLM` `[Nontrivial H]` (**RMK functional on the real functions `C(σV,ℝ)`** — `g↦re⟪x,cfcHom V(↑∘g)x⟫`
= `cfcReExpectationCLM x ∘ (ContinuousLinearMap.compLeftContinuous ℝ σV Complex.ofRealCLM)`; the **`ℝ↪ℂ` restriction is done**,
the functional is now a concrete `C(σV,ℝ)→L[ℝ]ℝ`).
Also ✅ `realCfcReExpectation_nonneg` `[Nontrivial H]` (**functional monotone/positive** — `0≤g ⟹ 0≤Λ_x g` via
`cfcL=cfcHom=cfc(extend)` bridge + `cayley_cfc_re_inner_nonneg_of_nonneg`; the `→o`/`monotone'` field): with
ℝ-linearity, `realCfcReExpectationCLM x` is a `C(σV,ℝ)→ₚ[ℝ]ℝ` positive linear functional.
Also ✅ `cfcPLM` `[Nontrivial H]` (**the `C(σV,ℝ)→ₚ[ℝ]ℝ` positive linear functional** — `g↦re⟪x,cfc g V x⟫` bundled
as a `PositiveLinearMap`: `toLinearMap` = `(realCfcReExpectationCLM x).toLinearMap`, `monotone'` from
`realCfcReExpectation_nonneg`). **THE input `RealRMK.rieszMeasure` consumes.**
Also ✅ `cfcPLMcc` `[Nontrivial H]` (**the RMK input** `C_c(σV,ℝ)→ₚ[ℝ]ℝ` — `cfcPLM` precomposed with the forgetful
`C_c→C` on the compact spectrum; exactly the type `RealRMK.rieszMeasure` consumes).
Also ✅ `cayleyScalarMeasure` `[Nontrivial H]` (**the scalar spectral measure `μ_x` of `V` is CONSTRUCTED** —
`RealRMK.rieszMeasure (cfcPLMcc x)`, a finite Borel measure on `σ(V)⊆S¹`; CompactSpace σ(V) ⟹ all the Borel/LCH
instances resolve).
Also ✅ `cayleyScalarMeasure_integral` `[Nontrivial H]` (**`μ_x` represents the functional** —
`∫f dμ_x = re⟪x,cfc f V x⟫` via `RealRMK.integral_rieszMeasure`; pins μ_x to V). **The operator →
scalar-spectral-measure half of the spectral theorem is end-to-end machine-checked.**
Also ✅ `cayleyScalarMeasure_isFiniteMeasure` `[Nontrivial H]` (**μ_x is a finite measure** — finite spectral
distribution, total mass ‖x‖²; ⟹ `∫g dμ_x` defined for bounded Borel g, the entry to the Borel FC).
Also ✅ `cayleyScalarMeasure_univ` `[Nontrivial H]` (**total mass `μ_x(σV)=‖x‖²`** — the Born-like spectral
distribution of the state x: `(μ_x univ).toReal = ∫1 dμ_x = re⟪x,cfc 1 V x⟫ = re⟪x,x⟫ = ‖x‖²`).
Also ✅ `cayleyScalarMeasure_isProbabilityMeasure` `[Nontrivial H]` (**μ_x is a probability measure for ‖x‖=1** —
the Born/spectral distribution of measuring a function of V in the normalized state x).
Also ✅ `cayley_norm_cfc_le` `[Nontrivial H]` (**‖cfc f V‖ ≤ ‖f‖_∞** — boundedness of the FC, the analytic input
to extend cfc to bounded-Borel functions ⟹ Borel FC / PVM `E(S)`).
Also ✅ `cayley_cfc_isSelfAdjoint` `[Nontrivial H]` (**cfc of a real function is self-adjoint** — real observables
of V → self-adjoint operators; makes `⟪x,cfc f V x⟫` real = ∫f dμ_x; bridge to polarization μ_{x,y}).
Also ✅ `cayley_cfc_inner_self_im_zero` `[Nontrivial H]` (**expectation of a real observable is real** —
`(⟪x,cfc f V x⟫).im = 0`; the real scalar diagonal `⟪x,cfc f V x⟫ = ↑(∫f dμ_x)`).
Also ✅ `cayley_norm_inner_cfc_le` `[Nontrivial H]` (**spectral sesquilinear form bounded** —
`‖⟪x,cfc f V y⟫‖ ≤ c·‖x‖·‖y‖`; the Riesz input for the Borel-FC operators f(V), E(S)=1_S(V)).
Also ✅ `cayley_cfc_inner_polarization` `[Nontrivial H]` (**spectral polarization identity** — off-diagonal
`⟪cfc f V y,x⟫` = polarization combo of the four diagonals; with the real diagonal = the full form via μ_z, the
formula defining f(V) and E(S) for bounded-Borel f — the heart of the PVM).
Also ✅ `cayleyScalarMeasure_le_norm_sq` `[Nontrivial H]` (**diagonal spectral content bounded** — `μ_x(S) ≤ ‖x‖²`;
the bound `⟪x,E(S)x⟫ = μ_x(S)` must satisfy, controlling the Riesz representation of E(S)).
Also ✅ `cayleyScalarMeasure_union` `[Nontrivial H]` (**finite additivity** — `μ_x(S∪T)=μ_x(S)+μ_x(T)` disjoint; the
diagonal shadow of E(S∪T)=E(S)+E(T) and the additivity of the Born probabilities over disjoint spectral outcomes).
Also ✅ `cayley_cfc_norm_sq` `[Nontrivial H]` (**L²-isometry, operator side** — `‖cfc f V x‖² = re⟪x,cfc(|f|²)V x⟫`;
with the integral identity = Parseval `‖cfc f V x‖² = ∫|f|² dμ_x`, the estimate for the strong-limit Stone exp
`U_t=exp(itA)`, GPT-5.5-pro's endorsed route — not the PVM).
Also ✅ `cayley_cfc_sub_norm_sq` `[Nontrivial H]` (**L²-distance estimate** — `‖cfc f V x − cfc g V x‖² =
re⟪x,cfc(|f−g|²)V x⟫` = `∫|f−g|² dμ_x`; the literal Cauchy estimate for `n ↦ cfc(e^{it·φₙ})V x`).
Also ✅ `cayleyScalarMeasure_integral_C` `[Nontrivial H]` (**integral identity on C(σV,ℝ)** — `∫h dμ_x = re⟪x,cfcL ha(↑∘h)x⟫`;
the compact-domain wrapper that removes C_c plumbing from the function-form CFC bridge).
Also ✅ `integral_re_cfc_ofReal` `[Nontrivial H]` (**function-form CFC↔measure bridge** — `re⟪x,cfc(↑∘r)V x⟫ =
∫ r ω.1 dμ_x`; the recurring dictionary entry, upgrades L²-distance to `‖cfc f V x−cfc g V x‖²=∫|f−g|²dμ_x`).
Also ✅ `cayley_cfc_sub_norm_sq_integral` `[Nontrivial H]` (**★★★ the full Parseval / L²-distance identity in honest
integral form** — `‖cfc f V x − cfc g V x‖² = ∫ ω, ‖f ω.1 − g ω.1‖² dμ_x`; composes `cayley_cfc_sub_norm_sq` with
`integral_re_cfc_ofReal` at `r z=‖f z−g z‖²`, via `RCLike.conj_mul`. The CFC↔measure dictionary is now COMPLETE:
`n↦cfc(e^{it·φₙ})V x` Cauchy ⟺ `∫‖e^{itφₙ}−e^{itφₘ}‖²dμ_x→0` — defines `U_t=exp(itA)` as a strong limit, no PVM).
Also ✅ `cayley_cfc_norm_sq_integral` `[Nontrivial H]` (**Parseval / L²-isometry, integral form, f-version** —
`‖cfc f V x‖²=∫‖f ω.1‖²dμ_x`; `f↦cfc f V x` is an L²(μ_x)→H isometry on continuous functions).
Also ✅ `cayley_cfc_tendsto_zero_of_integral` `[Nontrivial H]` (**the L² convergence engine** — `∫‖F n ω.1‖²dμ_x→0`
⟹ `cfc(F n)V x→0` strongly; the convergence half of the Cauchy/DCT machine turning L²(μ_x)-limits into strong operator
limits — the device that kills the Cayley atom `μ_x({1})=0` and assembles `U_t=exp(itA)`, no PVM).
Also ✅ `cayley_cfc_cauchySeq_of_integral` `[Nontrivial H]` (**the existence half** — `F n` Cauchy in L²(μ_x) ⟹
`cfc(F n)V x` is a `CauchySeq` in H, hence converges; from the L²-distance Parseval + `lt_of_pow_lt_pow_left₀`). With
the convergence half this is the **FULL bridge** L²(μ_x) continuous-fn limits ⟶ strong operator limits — any
L²-convergent sequence yields a convergent `cfc(F n)V x`, directly enabling `μ_x({1})=0` and `U_t=exp(itA)`.
Also ✅ `cayley_defect_energy` `[Nontrivial H]` (**the Cayley defect-energy identity** — `‖V x − x‖²=∫‖(ω:ℂ)−1‖²dμ_x`;
the `f=z−1` specialization of the Parseval f-isometry, via `cfc(z↦z−1)V=V−1` from `cfc_sub`+`cayley_cfc_id`/`_one`).
Spectral mass × squared distance-to-1 = the Cayley defect `‖(V−1)x‖²` — the integral witnessing `ker(1−V)=0`; the
inverse-Cayley generator is obstructed only by the spectral atom `μ_x({1})` (next brick).
Also ✅ `cayleyCutoff` + scaffolding (`_pos`/`_le_one`/`_continuous`/`_tendsto_zero_of_ne`/`_tendsto_indicator`/
`_sq_mul_tendsto_zero`) (**the rational cutoff sequence** `ψ_N(z)=(1+(N+1)‖z−1‖²)⁻¹`: `0<ψ_N≤1`, continuous,
`ψ_N→0` off 1, `ψ_N→1_{z=1}` ptwise, `‖z−1‖²ψ_N²→0`; pure real analysis, `U`-independent — the DCT approximation
device that kills the atom).
Also ✅ `cayleyCutoff_integral_tendsto_atom` `[Nontrivial H]` (**the first DCT step** — `∫ψ_N(ω)dμ_x→μ_x({1})`,
`{1}={ω∈σ(V)|(ω:ℂ)=1}`; dominated convergence with the cutoff scaffolding, limit `∫1_{{1}}dμ_x=μ_x({1})` via
`integral_indicator_one`, `{1}` measurable via `isClosed_eq`).
Also ✅ `cayleyCutoff_defect_integral_tendsto_zero` `[Nontrivial H]` (**DCT-3** — `∫‖(ω−1)ψ_N‖²dμ_x→0`; dominated
convergence, integrand `‖ω−1‖²ψ_N²≤4` via the circle bound `‖(ω:ℂ)‖=1`+`ψ_N≤1`, `→0` ptwise; in the form
`∫‖F_N ω.1‖²dμ_x→0`, `F_N(z)=(z−1)ψ_N(z)` — feeds `cayley_cfc_tendsto_zero_of_integral` ⟹ `(V−1)w=0`).
Also ✅ `cayleyCutoff_sub_indicator_sq_tendsto_zero` (helper) + `cayleyCutoff_L2_tendsto_zero` `[Nontrivial H]`
(**DCT-2, the L²-Cauchy input** — `∫‖ψ_N−1_{{1}}‖²dμ_x→0`; dominated convergence, integrand `≤4`, indicator
measurability via `Measurable.indicator`+`isClosed_eq`, `→0` ptwise; ⟹ L²-Cauchy ⟹ `cfc(ψ_N)V x→w` via the
existence-half). **ALL THREE DCT LIMITS DONE.**
Also ✅ `cayleyCutoff_cfc_cauchySeq` `[Nontrivial H]` (**★★★ the cutoff CFC vectors are a `CauchySeq`** — the existence
input: `cfc(ψ_N)V x` is `CauchySeq` in H, hence converges. L²-Cauchy from DCT-2 + the quadratic triangle integrated
via `integral_mono_of_nonneg`, fed to `cayley_cfc_cauchySeq_of_integral`).
Also ✅ `cayleyCutoff_cfc_tendsto_zero` `[Nontrivial H]` (**★★★ the cutoff CFC vectors → 0** — the operator heart:
`cfc(ψ_N)V x → 0`. Existence (CauchySeq→w) + `(V−1)w=0` (DCT-3 + convergence-half + continuity + `tendsto_nhds_unique`)
+ `w=0` (`ker(1−V)=0`). `cfc(z−1)V=V−1` via `cfc_mul`+`cfc_sub`+`cayley_cfc_id`/`_one`. Built green first try).
Also ✅ `cayleyScalarMeasure_atom_eq_zero` `[Nontrivial H]` (**★★★★ THE CAYLEY SPECTRAL ATOM VANISHES: `μ_x({1})=0`** —
no mass on the exceptional point `1∈S¹`. DCT-1 + `∫ψ_N dμ=re⟪x,cfc(ψ_N)V x⟫` + `cfc(ψ_N)V x→0` + inner/re-continuity ⟹
`μ_x({1}).toReal=0` ⟹ `μ_x({1})=0`. Built green first try). **ATOM-KILLING COMPLETE** — the inverse-Cayley/Stone
exponential symbol `exp(it·invCayley(ω))` is now `μ_x`-a.e. defined, the precondition for `U_t=exp(itA)`.
Also ✅ `cayleyInv` + `cayleyInv_continuousOn` + `cayleyInv_im_eq_zero` (**the inverse Cayley map** `c(ω)=i(1+ω)/(1−ω)`:
continuous off `1`, and **real on the unit circle** off `1` ⟹ `A=i(1+V)(1−V)⁻¹` self-adjoint ⟹ `exp(it·c)` modulus 1.
Real-valuedness via `conj ω=ω⁻¹` on circle + `div_eq_div_iff` + `linear_combination`).
Also ✅ `cayleyExp` + `cayleyExp_continuousOn` + `cayleyExp_abs` (**the Stone-exponential symbol** `e_t(ω)=exp(i·t·c(ω))`,
whose cfc `cfc(e_t)V` IS `U_t=exp(itA)`: continuous off `1`, **modulus 1** on the circle off `1` — `c(ω)` real ⟹
`i·t·c(ω)` purely imaginary ⟹ `‖exp‖=1` (`Complex.norm_exp`). Built green first try). Bounded+cts off `1` + `μ_x({1})=0`
⟹ `e_t` is `μ_x`-a.e. cts/bounded.
Also ✅ `cayleyExp_zero` (`e_0=1`) + `cayleyExp_add` (`e_s·e_t=e_{s+t}` via `Complex.exp_add` — symbol-level seed of the
**Stone group law** `U_s U_t=U_{s+t}` by cfc multiplicativity). Built green first try. Two of the three Stone-group
axioms at the symbol level (strong continuity is the third).
Also ✅ `cayleyBump` + `_continuous`/`_nonneg`/`_le_one`/`_tendsto_indicator` (**the continuous bump cutoff**
`η_N=1−ψ_N`: `η_N∈[0,1]` cts, `η_N→1_{ω≠1}`, `η_N(1)=0` tames `e_t`'s discontinuity at `1` — the symbol's
L²-approximation device). Built green.
Also ✅ `cayleyExp_abs_circle` (`‖e_t‖=1` on the whole circle incl. junk point `1`) + `cayleyExpBump_sub_norm`
(`‖e_t·η_N − e_t‖=ψ_N` on the circle). Both built green first try. ⟹ `‖g_{t,N}−e_t‖²=ψ_N²` ⟹
`∫‖g−e_t‖²=∫ψ_N²≤∫ψ_N→μ_x({1})=0` (squeeze).
Also ✅ `cayleyCutoff_sq_integral_tendsto_zero` (`∫ψ_N²→0` squeeze) + `cayleyExpBump_L2_tendsto_zero` (**★★ the cutoff
symbol → e_t in L²(μ_x)**: `∫‖e_t·η_N − e_t‖²dμ_x→0`; integrand `=ψ_N²` via `cayleyExpBump_sub_norm`+`integral_congr_ae`).
Built green (2 fixes: `ENNReal.toReal_zero`; `show` to beta-reduce for `rw`).
Also ✅ `cayleyExpBump` (def) + `cayleyExpBump_norm` + `cayleyExpBump_continuousOn` (**★★ `g_{t,N}=e_t·η_N` is
`ContinuousOn σ(V)`**: product of `ContinuousAt` off `1`; at `1` the squeeze `‖g‖=η_N→0` + `g(1)=0`). Built green first
try. ⟹ `cfc(g_{t,N})V` well-defined.
Also ✅ `cayleyExpBump_cfc_cauchySeq` `[Nontrivial H]` (**★★★ the Stone-exp cfc vectors are a `CauchySeq`** — whose
strong limit IS `U_t x`: `cfc(g_{t,N})V x` CauchySeq in H. L²-convergent ⟹ L²-Cauchy (quadratic triangle, `c=e_t`)
⟹ existence-half. The continuum Stone exponential as a strong limit, NO PVM). Built green (1 fix: `simp[cayleyExpBump]`
before `set`).
Also ✅ `cayleyStoneU` (def) + `cayleyStoneU_tendsto`/`_add`/`_smul` (**★★★★ THE CONTINUUM STONE EXPONENTIAL `U_t` IS
DEFINED**: `cayleyStoneU t x:=lim_N cfc(g_{t,N})V x`, the strong limit; `cayleyStoneU_tendsto` = defining property;
`_add`/`_smul` ⟹ `U_t` ℂ-LINEAR. This IS `exp(itA)x`, no PVM). All built green first try.
Also ✅ **`cayleyStoneU_zero` — `U_0 = id`** (`StoneExp.lean`, axiom-free, budget 0): the Stone-group identity.
At `t=0`, `e_0≡1` (`cayleyExp_zero`) ⟹ `g_{0,N}=η_N=1−ψ_N` ⟹ `cfc(g_{0,N})V x = x − cfc(ψ_N)V x` (`cfc_sub`+
`cayley_cfc_one`); atom-killing `cfc(ψ_N)V x→0` (`cayleyCutoff_cfc_tendsto_zero`, `μ_x({1})=0`) ⟹ `x−0=x` by
`tendsto_nhds_unique`. **First of the 3 remaining unitary-group bricks done.**
Also ✅ **`cayleyStoneU_isometry` — `‖U_t x‖ = ‖x‖`** (+ helper `cayleyBump_sq_integral_tendsto`; `StoneExp.lean`,
axiom-free, budget 0): Parseval (`cayley_cfc_norm_sq_integral`) ⟹ `‖cfc(g_{t,N})V x‖²=∫‖g_{t,N}‖²dμ_x`, `=∫η_N²dμ_x`
on `σ(V)⊆S¹` (`cayleyExpBump_norm`, `‖e_t‖=1`); `∫η_N²=μ_x(σV).toReal−2∫ψ_N+∫ψ_N² → ‖x‖²−0+0` (`cayleyScalarMeasure_-
univ` + atom-killing `cayleyCutoff_integral_tendsto_atom`/`_sq_integral_tendsto_zero`). Same seq → `‖U_t x‖²`
(`(cayleyStoneU_tendsto).norm.pow 2`) ⟹ `‖U_t x‖²=‖x‖²` ⟹ `‖U_t x‖=‖x‖` (`Real.sqrt_sq`). **2nd of 3 bricks done.**
Also ✅ **`cayleyStoneLI`/`cayleyStoneCLM` — `U_t` bundled as `H →L[ℂ] H`** (`StoneExp.lean`, axiom-free, budget 0):
`cayleyStoneU_add`/`_smul`/`_isometry` are exactly the `LinearIsometry` fields ⟹ `cayleyStoneLI : H →ₗᵢ[ℂ] H` ⟹
`cayleyStoneCLM := .toContinuousLinearMap : H →L[ℂ] H` (with `cayleyStoneCLM_apply`/`_norm_map`). The group `t↦U_t`
now lives in `H →L[ℂ] H` (where `U_s U_t=U_{s+t}` is `∘L`). **3rd brick's packaging done.**
Also ✅ **`cayleyExpBump_cfc_norm_le` + `cayleyExpBump_cfc_comp` — GROUP-LAW PREREQUISITES** (`StoneExp.lean`,
axiom-free, budget 0): (a) the cutoff cfc operators are **contractions** `‖cfc(g_{t,N})V z‖≤‖z‖` (Parseval
`∫η_N²≤∫1=‖z‖²`); (b) **cfc multiplicativity** `cfc(g_{s,N})V (cfc(g_{t,N})V x)=cfc(e_{s+t}·η_N²)V x` (`cfc_mul`+
`cayleyExp_add`). The two ingredients the group-law limit-assembly consumes. **Both built green first try.**
Also ✅ **`cayleyStoneU_group` — THE ONE-PARAMETER GROUP LAW `U_s U_t = U_{s+t}`** (+ helper
`cayleyProdSymbol_cfc_tendsto`; `StoneExp.lean`, axiom-free, budget 0): `A_N y_N` (with `A_N=cfc(g_{s,N})V`,
`y_N=cfc(g_{t,N})V x`) → `U_s(U_t x)` [operator-limit: contraction (a) + `cayleyStoneU_tendsto` + `squeeze_zero_norm`]
AND `=cfc(e_{s+t}η_N²)V x` [(b)] → `U_{s+t}x` [(ii): `‖·−cfc(g_{s+t,N})Vx‖²=∫η_N²ψ_N²≤∫ψ_N²→0`]; uniqueness ⟹
`U_s(U_t x)=U_{s+t}x`. **Both built green first try.** With `cayleyStoneU_zero` (`U_0=1`): `U_{−t}U_t=1` ⟹ each `U_t`
is **surjective ⟹ `U_t ∈ unitary(H)`**. `t↦U_t` is now a one-parameter group of isometries — only strong continuity
+ generator remain for full Stone.
Also ✅ **`cayleyStoneU_neg_left`/`_right` + `cayleyStoneLIE` — `U_t` IS A UNITARY `H ≃ₗᵢ[ℂ] H`** (`StoneExp.lean`,
axiom-free, budget 0): `U_{−t}` is a two-sided inverse (group law + `cayleyStoneU_zero`), bundling `cayleyStoneLI`
into a `LinearIsometryEquiv` `cayleyStoneLIE` (`cayleyStoneLIE_apply` acts as `cayleyStoneU`). **Built green first
try.** The continuum `t↦U_t=exp(itA)` is now a complete **one-parameter GROUP OF UNITARIES** (linear, isometric,
`U_0=1`, `U_s U_t=U_{s+t}`, invertible) — no PVM, no UV datum.
Also ✅ **`cayleyStoneU_sub_norm_sq` — THE LIMIT PARSEVAL** `‖U_t x−U_s x‖²=∫‖e_t−e_s‖²dμ_x` (`StoneExp.lean`,
axiom-free, budget 0): the L²-isometry through the strong limit. (A) `‖cfc(g_{t,N})Vx−cfc(g_{s,N})Vx‖²→‖U_t x−U_s x‖²`;
(B) `=∫‖g_{t,N}−g_{s,N}‖²` (`cayley_cfc_sub_norm_sq_integral`); (C) `→∫‖e_t−e_s‖²` by DCT (`η_N²→1` a.e., bound `4`,
bump-form keeps it measurable); uniqueness. **Built green.** The bridge to strong continuity.
Also ✅ **`cayleyStoneU_continuous` — STRONG CONTINUITY** `Continuous(t↦U_t x)` (+ helper `cayleyExp_measurable`;
`StoneExp.lean`, axiom-free, budget 0): `‖U_t x−U_s x‖=√(∫‖e_t−e_s‖²dμ_x)→0` as t→s by DCT on the filter `𝓝 s`
(`tendsto_integral_filter_of_dominated_convergence`; `e_t` cont. in t, dominated by 4; measurability via
`cayleyExp_measurable`, `e_t` Borel). **Built green.**
**🎯 MILESTONE:** `t↦U_t=exp(itA)` is now a **COMPLETE STRONGLY CONTINUOUS ONE-PARAMETER GROUP OF UNITARIES**
(ℂ-linear, isometric, `U_0=1`, `U_s U_t=U_{s+t}`, `∈unitary(H)`, strongly continuous) — axiom-free, no PVM, no UV
datum. **The unitary-group side of Stone's theorem is DONE.**
Also ✅ **`cayleyStoneU_comm_cayleyUnitary` — U_t IS A FUNCTION OF V** (`StoneExp.lean`, axiom-free, budget 0):
`U_t(V y)=V(U_t y)` — each `cfc(g_{t,N})V` commutes with `V` (`Commute.cfc`), pass to limit. So `U_t=exp(itA)` lies
in the abelian vN algebra generated by `V` — the modular flow is generated by its own spectral data. **Built green.**
Also ✅ **`cayleyStoneU_cfc` — THE SPECTRAL ACTION** `U_t(cfc φ V z)=cfc(e_t·φ)V z` (`StoneExp.lean`, axiom-free,
budget 0): on the cfc-vector core (φ, e_r·φ ContinuousOn σ(V)), `U_t` acts by multiplying the symbol by
`e_t(ω)=exp(it·c(ω))` — `cfc(g_{t,N})V(cfc φ V z)=cfc(g_{t,N}·φ)V z`→`U_t(cfc φ V z)` and `cfc(g_{t,N}·φ)V z`→
`cfc(e_t·φ)V z` (L²-defect `∫ψ_N²|φ|²≤M²∫ψ_N²→0`). **Built green.** Identifies `U_t` with the bounded-Borel
functional calculus `cfc(e_t·)` on a core — the concrete `U_t=exp(itA)` and the gateway to the generator.
Also ✅ **`cayleyExp_hasDerivAt_zero`/`cayleyExp_hasDerivAt` — THE STONE SYMBOL DERIVATIVE** (`StoneExp.lean`,
axiom-free, budget 0): `d/dt e_t(ω)|₀=i·c(ω)` (and `|ₛ=e_s·i·c` everywhere) — the fibrewise generator is mult by
`i·c(ω)` = spectral form of `i·A`. Via `HasDerivAt.cexp` + `Complex.ofRealCLM.hasDerivAt`. **Both built green first
try.** On the cfc core this is formally `d/dt U_t(cfc φ V z)|₀=cfc(i·c·φ)V z`.
Also ✅ **`cayleyExp_slope_tendsto` + `cayleyExp_sub_one_norm_le` — THE TWO GENERATOR-DCT INPUTS** (`StoneExp.lean`,
axiom-free, budget 0): (a) `(e_t(ω)−1)/t → i·c(ω)` (pointwise limit, from the symbol derivative via
`hasDerivAt_iff_tendsto_slope`); (b) `‖e_t(ω)−1‖ ≤ |t|·‖c(ω)‖` on σ(V) (c real there, `‖exp(iθ)−1‖≤|θ|`) ⟹
`‖(e_t−1)/t‖≤‖c‖`, the t-independent domination. **Both built green.** Exactly the pointwise limit + domination the
generator DCT consumes.
Also ✅ **`cayleyExp_gen_integrand_tendsto` (+`cayleyInv_measurable`) — THE SCALAR GENERATOR DCT** (`StoneExp.lean`,
axiom-free, budget 0): `∫‖((e_τ−1)/τ−i·c)·φ‖²dμ_z → 0` as τ→0 — the squared L²-gap between the difference quotient
and `i·c·φ`, by DCT on `𝓝[≠]0` (integrand→0 a.e. via input (a), dominated by `4‖c·φ‖²` via input (b)). **Built green.**
The analytic heart of the generator.
Also ✅ **🎯 `cayleyStoneU_cfc_hasDerivAt` (+`cayleyStoneU_slope_norm_sq`) — THE GENERATOR ON THE cfc CORE / STONE'S
CONVERSE** (`StoneExp.lean`, axiom-free, budget 0): `HasDerivAt(t↦U_t(cfc φ V z)) (i·cfc(c·φ)V z) 0` — on the spectral
core `U_t=exp(itA)` is differentiable, `d/dt|₀ = i·(mult by c=cayleyInv)`, i.e. the **generator A = multiplication by
the spectral value c**. Via the operator norm²=∫DCT identity (`cfc_sub`/`cfc_const_mul`+Parseval) + the scalar DCT +
`hasDerivAt_iff_tendsto_slope`. **Both built green.** **BOTH HALVES OF STONE NOW DONE on the cfc core** (unitary group
forward + generator converse), axiom-free via Cayley/cfc, no PVM, no UV datum.
Also ✅ **🎯 `cayleyStoneCLM_stoneGen_cfc` (+`cayleyStoneCLM_cfc_mem_stoneDomain`) — STONE'S CORRESPONDENCE PACKAGED**
(`StoneExp.lean`, axiom-free, budget 0): `stoneGen(cayleyStoneCLM)⟨cfc φ V z⟩ = cfc(c·φ)V z` — the abstract generator
`A x=−i d/dt U_t x|₀` IS the Cayley self-adjoint `A=i(1+V)(1−V)⁻¹` = **mult by the spectral value c** on the cfc core.
Wraps the generator `HasDerivAt` with `stoneGen_eq_of_hasDerivAt` via `cayleyStoneCLM_apply`. **Both built green.**
**STONE'S THEOREM IS NOW BOTH DIRECTIONS on the cfc core** (unitary group ⊕ self-adjoint generator), axiom-free, no
PVM, no UV datum — **the pivotal wall (general Stone, Phase 4.2) is BROKEN on the spectral core.**
Also ✅ **`cayleyBump_cfc_tendsto` — THE cfc CORE IS DENSE** (`StoneExp.lean`, axiom-free, budget 0): `cfc(η_N)V z → z`
(atom-killing `cfc(ψ_N)V z→0` + `cfc_sub`/`cayley_cfc_one`); the η_N vanish quadratically at 1 so the bump vectors are
spectral-core vectors ⟹ **the smooth domain of the Stone group is dense**. **Built green first try.**
Also ✅ **`cayleyStoneCLM_zero`/`_comp`/`_inner`/`_norm_le`/`_continuous` — cayleyStoneCLM IS A C₀ UNITARY GROUP**
(`StoneExp.lean`, axiom-free, budget 0): the reconstructed group satisfies the 5 C₀-group hypotheses (group law,
U_0=1, inner-preservation via the LinearIsometryEquiv, contraction, strong continuity). **All built green first try.**
So it's a bona-fide input to the Gårding/stoneGen machinery (density, recovery, iteration).
**🧭 STRATEGIC REDIRECT (GPT-5.5-pro, 2026-06-XX):** do NOT make the recovery `cayleyStoneCLM U = U` the bottleneck.
The real payload toward X=A_edge is the **DIRECT spectral identity for the ORIGINAL group's generator**:
`stoneGen U (φ(V) z) = (c·φ)(V) z` for φ, c·φ ∈ C(σV) — i.e. `stoneGen U = A_V = mult by c` on the cfc core (recovery
is then a corollary, not a prerequisite, and the e.s.a. wall is sidestepped). **Route (most pieces already built):**
(A) `stoneGen U (R x) = −i•(R x − x)` — the resolvent generator formula — **ALREADY DONE** (`resolvent_stoneGen`,
Garding.lean), as is `Range(A+i)=H` (deficiency-index zero). (B) the resolvent↔Cayley relation `R = h(V)`,
`h(ω)=(1−ω)/2` (so `V=1−2R`); factor any core φ as `φ = h·ψ` (continuity of `c·φ` ⟺ continuity of `ψ` near the
excluded point 1), giving `φ(V)z = R·ψ(V)z` (cfc_mul); then (A) + the algebra `c·h = i(1+ω)/2` and `1−R=(1+V)/2` ⟹
`stoneGen U (φ(V)z) = i((1+V)/2)ψ(V)z = (c·φ)(V)z`. (C) recovery as corollary via a local **C₀-uniqueness lemma**
(two strongly-continuous unitary groups whose generators agree on a dense invariant subspace are equal — proof:
`F(s)=W_{t−s}U_s y` has `F'=0`, OR Gronwall on `‖U_t y − W_t y‖²`; NO full e.s.a. needed). **Then CAP Stone** at
`stoneGen U = A_V`; pivot to Phase 5 via a **NARROW AXIOMATIZED interface** (state the FQ bound CONDITIONALLY under
`τ(θ_s a)=e^{−s}τ(a)` + `K̃=A_edge/4ℓ_P²`, avoiding the full crossed-product/vN-weights infrastructure explosion —
Mathlib lacks vN weights, crossed products, modular theory, semifinite traces). Stone is a closeable sprint; Type II
will EXPAND unless narrowly interfaced.
Also ✅ **`cayley_resolvent_symbol_cfc` — RESOLVENT SYMBOL cfc** (`StoneExp.lean`, axiom-free, budget 0):
`cfc((1−ω)/2) V = ½(1−V)` (pure cfc linearity: `cfc_const_mul`+`cfc_sub`+`cayley_cfc_one`/`_id`). **Built green.** The
first ingredient of `resolvent U = cfc(h)V` (`h=(1−ω)/2`) — meets the resolvent↔Cayley relation at `½(1−V)`.
**Next (redirected, sub-bricks):** (i) the **resolvent↔Cayley relation** `cayleyUnitary U y = y − 2•(resolvent U y)`
(`V=1−2R`): via `cayleyEquiv.symm y = −i•(R y)` [proof: `cayleyEquiv⟨−i•Ry,_⟩ = stoneGen U⟨−i•Ry,_⟩ + i•(−i•Ry) =
(y−Ry)+Ry = y`, using `LinearPMap.map_smul` + `resolvent_stoneGen`], then unfold `cayley`; (ii) combine (i)+
`cayley_resolvent_symbol_cfc` ⟹ `resolvent U x = cfc(h) V x`; (iii) the **direct identity** `stoneGen U (cfc φ V z) =
cfc(c·φ) V z` (factor `φ=h·ψ`, `cfc_mul`, `resolvent_stoneGen`, algebra `c·h=i(1+ω)/2`); (iv) instantiate
translationLp/modUnitary/clockTransl ⟹ X=A_edge; then Phase 5 via the conditional interface.
**(Superseded) earlier framing — the direct identity `stoneGen U (φ(V)z)=(c·φ)(V)z` via the
resolvent factorization above (B); then instantiate translationLp/modUnitary/clockTransl ⟹ X=A_edge; then Phase 5
via the conditional interface;
then bounded-Borel `∫g dμ_x` + polarization μ_{x,y} → assemble `{μ_x}` into the circle-PVM `E` (Mathlib gap —
`PVM_of_selfAdjoint`) → transport to `A=∫λ dE` ⟹ Stone.
**Next (operator→PVM keystone, RMK+cfc supported):** scalar measures `μ_x` (`f↦re⟨x,cfc f V x⟩` → RMK) → circle-PVM
`E` (`V=∫z dE`) → transport via inverse Cayley to `A=∫λ dE` ⟹ Stone. The bounded-PVM remains the genuine gap.
**Remaining (Mathlib gap):** the **Borel/PVM** functional calculus on `S¹` for `V` (Mathlib has *continuous* FC
only) → transport to the unbounded spectral theorem (PVM for self-adjoint `A`) ⟹ Stone `U_t = exp(it A)`.

### Phase 4 (operators) — the modular Hamiltonian `K` as a symmetric operator ✅ (3rd & LAST C₀ group; trio complete)
**Delivered (axiom-free, budget 0, `QIQTH/Spectral/ModularGenerator.lean`):** the Stone-instantiation pattern
applied to the **third and last** named C₀ group, the modular flow `Δ^{it} = modUnitary S t` on the
one-particle space `H` (built via the bounded Borel FC of `R = P+Q`). The three Stone hypotheses:
`modUnitary_compL` (group law in `∘L` form, from `modUnitary_add`), `modUnitary_zero` (`Δ^0=1`),
`inner_modUnitary_self` (unitarity `⟪Δ^{it}a, Δ^{it}b⟫=⟪a,b⟫`, derived from `modUnitary_adjoint`). Then the
**modular Hamiltonian** `modularGen := stoneGen (modUnitary S) = −i d/dt Δ^{it}` — **the `K` of JLMS
`K̃ = A_edge·(1/4ℓ_P²) + K_bulk`** — with `modularGen_isFormalAdjoint_self` (**`K` symmetric**),
`modularGen_norm_add_smul_I_sq` (**Cayley estimate**), `modularGen_norm_le_norm_add_smul_I` (**`K+i` injective**).
`modUnitary` lives on the **abstract** one-particle space (not a heavy `Lp` type), so the instantiation needed
**no `irreducible`/`Lp` workaround** — clean term-mode applications of the general Stone lemmas.

**All three named C₀ generators now exist as concrete symmetric operators with `±i` injective:** `X = A_edge`
(clock), `P` (momentum), `K` (modular). The single shared remaining frontier is e.s.a. = `Range(·±i)` dense
(Gårding density), the carried analytic wall — with it, Stone returns `U_t = exp(it·gen)` for each.

### Phase 4.2/4.3 (operators) — the momentum operator `P` as a symmetric operator ✅ (2nd C₀ group instantiated)
**Delivered (axiom-free, budget 0, `QIQTH/Spectral/MomentumGenerator.lean`):** the same Stone-instantiation
pattern applied to the **second** of the three named C₀ groups, `translationLp t = τ_t = e^{itP}` on `L²(ℝ)`:
`translationCLM` (the CLM form of the isometry) with `translationCLM_zero` (`τ_0=1`), `translationCLM_add` (group
law), `translationCLM_inner` (`τ_t` a ℂ-linear isometry — the third Stone hypothesis); then the **momentum
operator** `momentumOp := stoneGen translationCLM = −i d/dt τ_t = −i d/dx` with `momentumOp_isFormalAdjoint_self`
(**`P` symmetric**), `momentumOp_norm_add_smul_I_sq` (**Cayley estimate** `‖(P+i)x‖²=‖Px‖²+‖x‖²`),
`momentumOp_norm_le_norm_add_smul_I` (**`P+i` bounded below ⟹ injective**). Same `Lp`-wall handling
(`attribute [local irreducible] stoneGen stoneDomain` + explicit ambient `(H := Lp ℂ 2 volume)`); here the group
is fully concrete (no implicit fiber), so the instantiation is even cleaner. **Remaining frontier:** e.s.a. of
`P` = `Range(P ± i)` dense (Gårding), the carried analytic wall. Two of three C₀ generators (`X = A_edge`, `P`)
now exist as concrete symmetric operators; only `modUnitary`/`Δ^{it}` (the modular `K`) remains to instantiate.

### Phase 4.3 (operator) — the clock energy `X` as a symmetric operator at the concrete `Lp` type ✅ (Lp-wall cracked)
**Delivered (axiom-free, budget 0, `QIQTH/CrossedProductGenerator.lean`):** first `clockTransl_inner` —
`⟪λ_t a, λ_t b⟫ = ⟪a, b⟫` (the clock translation `λ_t` is a ℂ-linear isometry, via
`LinearIsometry.inner_map_map`), the diamond-free **unitary** statement and the third Stone hypothesis
(`hUinner`); together with `clockTransl_add` (group law) and `clockTransl_zero` (`λ_0 = 1`), all **three Stone
hypotheses** are discharged for the concrete clock group `λ_t`. Then the concrete clock energy operator itself:
- `clockEnergy := stoneGen clockTransl = −i d/dt λ_t` (`LinearPMap` on `L²(ℝ;H)`; its closure `= A_edge`);
- `clockEnergy_isFormalAdjoint_self` — **`X` is symmetric** (`X ⊆ X†` once its domain is dense);
- `clockEnergy_norm_add_smul_I_sq` — the **Cayley estimate** `‖(X + i) x‖² = ‖X x‖² + ‖x‖²`;
- `clockEnergy_norm_le_norm_add_smul_I` — **`X + i` bounded below**, hence injective (deficiency-index datum).

These instantiate the general Stone lemmas (the `_dom` projection-typed forms added to `Spectral/Stone.lean`) for
`clockTransl`. **The `Lp`-elaboration wall (the `whnf`/`isDefEq` divergence on the `(stoneGen _).domain`
projection through the heavy `Lp` instance tower, Phase-1.1/1.3 friction) is now DEFEATED** via
`attribute [local irreducible] stoneGen stoneDomain` (so the projection is not unfolded) + pinning the ambient
space `(H := Lp H 2 volume)` explicitly. **Remaining (analytic) frontier:** essential self-adjointness of `X`
= `Range(X ± i)` dense (Gårding density) — needed before Stone returns `λ_t = exp(itX)` — is the carried wall,
NOT claimed. The 1/4 ratio is derived (`SakharovRatio`); `⟨A_edge⟩ = A/4ℓ_P²` (value of `G`) is never claimed.

### Phase 4.2 (general Stone) — the symmetric-generator scaffolding COMPLETE; wall narrowed to Gårding density
**Delivered (axiom-free, budget 0, `QIQTH/Spectral/Stone.lean`; see `STONE_THEOREM_PLAN.md` Phase 3 for the full
log):** the general-Stone build-up to essential self-adjointness, Mathlib-integrated —
`stoneDomain` (smooth-domain submodule) · `stoneGen` (the generator `A = −i d/dt U_t|₀` as a `LinearPMap`) ·
`hasDerivAt_stoneGen` / `_neg` (forward/backward derivative) · `stoneDomain_apply_mem` (flow-invariance) · `hasDerivAt_stoneGen_flow` + `stoneGen_comm_flow`
(**`[A, U_s] = 0`** — the generator commutes with the flow: `A (U_s x) = U_s (A x)`, so `A_edge` is compatible
with the modular flow it is read off from) ·
`stoneGen_symmetric` (⟪Ax,y⟫=⟪x,Ay⟫ on the smooth domain) · `stoneGen_eq_of_hasDerivAt` (generator
**identification** — `stoneGen` pinned by any witnessed derivative; the bridge to identify `stoneGen` of a
concrete group with a known operator `P`/`K`/`X`) · `stoneGen_isFormalAdjoint_self`
(`(stoneGen U).IsFormalAdjoint (stoneGen U)`, the symmetric operator bundled in Mathlib's `LinearPMap` adjoint
framework) · `stoneGen_norm_add_smul_I_sq` + `stoneGen_norm_sub_smul_I_sq` (the **Cayley estimate** `‖(A±i)x‖²=‖Ax‖²+‖x‖²`
⟹ `A±i` injective/bounded-below — the entry point to the Cayley transform + deficiency-index e.s.a. criterion) ·
`stoneGen_norm_cayley_eq` + `stoneGen_norm_le_norm_add_smul_I` (the **Cayley transform's defining properties**:
`‖(A−i)x‖=‖(A+i)x‖` ⟹ `V=(A−i)(A+i)⁻¹` is an **isometry** on the range; `‖x‖≤‖(A+i)x‖` ⟹ `A+i` injective) ·
`stoneGen_le_adjoint` (the **explicit `A ⊆ A†`**, `stoneGen U ≤ (stoneGen U)†`, **conditional on
`hdense : Dense (stoneGen U).domain`** — `le_adjoint` genuinely requires density). Wired into AxiomAudit; budget 0.
**Frontier honestly carried (the remaining wall of 4.2):** `Dense (stoneGen U).domain` (**Gårding/mollified-vector
density**, `x_φ = ∫ φ(t) U_t x dt`) + **essential self-adjointness** (`Range(A±i)` dense / Nelson analytic vectors)
+ the **Cayley transform** / unbounded spectral theorem — genuine Mathlib-grade gaps. With those, `Ā = Ā†` ⟹ Stone
⟹ apply to `clockTransl` ⟹ `X = A_edge` (4.3) → dual-weight trace (Phase 5) → FQ bound (Phase 6).
