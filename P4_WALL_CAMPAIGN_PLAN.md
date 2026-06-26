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
**Remaining (Mathlib gap):** the unbounded spectral theorem (PVM for self-adjoint `A`) ⟹
`Ā = Ā†` (e.s.a.) ⟹ Cayley/unbounded spectral theorem ⟹ Stone `U_t = exp(it Ā)`. Mathlib has none of these; Cayley
injectivity in Stone.lean.

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
