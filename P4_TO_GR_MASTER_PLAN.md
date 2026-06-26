# Master plan — closing `P4 → GR` for the free field (the ordered roadmap over all sub-campaigns)

**Status:** MASTER ROADMAP (sequences the detailed sub-plans; execute next-unfinished-increment-first).
**Track:** GR / continuum. **Goal:** drive the whole remaining arc that turns the holographic capacity **(P4)**
into a theorem and closes a single end-to-end **`P4 → GR` for the free field** — ordered by tractability so value
lands every increment. This plan does **not** restate the sub-plans; it *orders* them and records the fusion points.

## 0. Where we are (verified) and what "all of it" means

`P4 → GR` is currently an **axiom-free *conditional* theorem** (`qiqt_gr_freefield`): given the modular/KMS
structure (✅ discharged for the free field) **and** the Clausius/area floor `S = A/4G` **and** the Gap-2
localization map, the Einstein equation follows (Jacobson). Two parallel routes feed the floor, each with one wall:

- **Route A — the coefficient (`1/4`).** Sakharov/induced-gravity: ✅ `SAKHAROV_KG_PLAN.md` (A+B+C…C⁴) derives the
  `1/4` as the geometric `(conical 4π)/(EH 16π)` ratio, non-circularly, and machine-checks the Gaussian
  entropy formula `S = Σᵢ S(νᵢ)` + a concrete entangled instance + `ν` from a covariance matrix (`n=1`). **Wall:
  the `N`-mode Williamson area-*scaling* (`Σ ∝ boundary`).**
- **Route B — the operator + the bound.** Crossed-product Type II: ✅ `P4_WALL_CAMPAIGN_PLAN.md` (Phases 0–3:
  `σ_t`, `π(a)`, `λ_t`, covariance, crossed product) + Phase 4.1 (the Stone hypothesis). **Wall: Stone's theorem
  (Phase 4.2/4.3) → the trace (Phase 5) → JLMS/FQ bound (Phase 6).**

**"All of it"** = grind both walls down and fuse: Stone (`STONE_THEOREM_PLAN.md`) gives the operators `K`, `X`;
Williamson gives the area-scaling; the trace + JLMS give the bound `S ≤ A/4`; Gap-2 wires modular flow to
geometry — leaving only the **`1/4` UV datum / species value of `G`** as the irreducible carried input (never
derived, per `P4_WALL_CAMPAIGN_PLAN.md` §0). No `1/4` is ever *claimed*; we deliver the operators, the bound, and
the mechanism.

## 1. Execution order (most-tractable-first; each item = its detailed sub-plan)

**M1 — Stone Phase 1: unbounded functional calculus `∫ f dE` on a PVM.**  `STONE_THEOREM_PLAN.md` Phase 1.
The tractable keystone — rides the existing `PVM_of_selfAdjoint` + `boundedFC`. Builds genuine unbounded
self-adjoint operators. *Buys:* the spectral-integral infrastructure. **(START HERE.)**

**M2 — Stone Phase 2: the modular Hamiltonian `K` + `Δ^{it}=e^{−itK}`.**  `STONE_THEOREM_PLAN.md` Phase 2.
`K = ∫ log(r/(2−r)) dE_R` from the bounded RvD `R`; Stone for `K` directly (no general theorem). *Buys:* **JLMS
Stage 1 closed** — the highest-value near-term win.

**M3 — Williamson, the `N`-mode area-scaling (Route A wall).**  `SAKHAROV_KG_PLAN.md` §2-C frontier.
Symplectic eigenvalues of the `2N×2N` lattice covariance → `gaussStateEntropy ∝ boundary`. The genuine
linear-algebra frontier (symplectic eigenvalues absent from Mathlib); attempt the `2`-mode and small-`N` cases,
checkpoint honestly. *Buys:* the entropy area law → wires Sakharov's `1/4` into a derived `S = A/4G`.

**M4 — Stone Phases 3–4: general Stone → the clock energy `X = A_edge`.**  `STONE_THEOREM_PLAN.md` Phases 3–4.
Generator of an abstract unitary group via Cayley + the unitary spectral theorem; apply to `λ_t`. The
multi-month frontier. *Buys:* `A_edge` a genuine operator → **unblocks crossed-product Phase 4.2/4.3**.

**M5 — Wall Phases 5–6: the dual-weight trace + JLMS + the FQ bound.**  `P4_WALL_CAMPAIGN_PLAN.md` Phases 5–6.
Trace `τ` on `M ⋊_σ ℝ`, Type II∞ scaling, finite renormalized entropy; the JLMS split `K̃ = A_edge·(1/4ℓ_P²) +
K_bulk`; the FQ bound `S(ρ_R) ≤ A/4ℓ_P²` from `cgpEntropy_nonneg` + the edge normalization. *Buys:* **(P4)'s
bound becomes a theorem** (conditional only on the edge normalization = the UV datum).

**M6 — Gap-2: the localization map.**  The GR-chain residual independent of Stone/Williamson — connect the
abstract modular flow to the geometric boost/area (the labelled `hS/hK` hypotheses of the GR capstone). *Buys:*
the last non-coefficient input of `qiqt_gr_freefield`.

**M7 — Fusion: `P4 → GR` closed for the free field.**  Replace the labelled `S = A/4G` floor of `qiqt_gr_freefield`
with M3 (area law) + M5 (FQ bound), and the localization with M6; the Einstein equation then follows with only
the **`1/4` / value-of-`G` (species)** carried as the UV datum. *Buys:* the goal — one end-to-end conditional-only-
on-the-UV-datum `P4 → GR`.

## 2. Dependency graph
```
M1 (unbounded FC) ─┬─→ M2 (K, Δ^{it}=e^{−itK})  ──────────────→ JLMS Stage 1 ┐
                   └─→ M4 (general Stone → X=A_edge) ─→ M5 (trace, JLMS, FQ bound) ┤
M3 (Williamson area-scaling, Route A) ────────────────────────────────────────────┼─→ M7 (P4→GR closed)
M6 (Gap-2 localization) ───────────────────────────────────────────────────────────┘
```
M1→M2 and M3 are reachable now; M4 (Stone proper) and M5 (trace) are the deep frontiers; M6 is independent; M7 is
the payoff once the floor (M3/M5) and localization (M6) land.

## 3. Per-increment discipline (every commit)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = standard 3 (or a clearly
labelled cited input with an `AxiomAudit` note); `bash scripts/axiom_budget_check.sh` budget 0 (never raised
without written justification); wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per sub-step with the
`Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; refresh `reports/`; update
the relevant sub-plan's Progress log **and** this file's checklist. **Ship green increments; checkpoint honestly
at each frontier (M3 Williamson, M4 Stone, M5 trace) — leave green, record the blocker, move to the next tractable
item.** Never claim the `1/4`.

## 4. Progress checklist
- [x] **M1 ✅ COMPLETE** — unbounded FC `∫ f dE` on a PVM (`QIQTH/Spectral/UnboundedFC.lean`): the operator
  `fcOp` exists as a ℂ-linear, symmetric unbounded operator on its domain, axiom-free, end-to-end from the
  bounded FC + truncation limits; bounded-compat `fcOp = boundedFC(↑f)` ties it back to `boundedFC`.
  **Symbol-linearity complete ✅** — `∫·dE` is linear in the *integrand*: additive (`fcOp_add`), ℂ-homogeneous in
  the vector (`fcOp_smul`), and **negates with the symbol** `∫(−f)dE = −∫f dE` (`fcOp_neg`, via `fcTrunc_neg` +
  `boundedFC_neg` + `fcEnergy_neg`) — Mathlib-quality completeness of the unbounded functional calculus. Details: **Domain ✅** (the
  finite-energy `fcDomain P f` as a ℂ-submodule: `fcEnergy` `‖c‖²`-homogeneous + sub-additive via the
  parallelogram law). **Bounded-symbol bridge ✅** (`mem_fcDomain_of_bounded`/`fcDomain_eq_top_of_bounded`:
  `|f|≤C ⟹ ∫f²dμ_x ≤ C²‖x‖² ⟹ fcDomain f = ⊤` — the consistency tie to `boundedFC`; `K`'s domain is proper
  only because `log` is unbounded). **L²(μ_x) bridge ✅** (`mem_fcDomain_iff_integrable_sq`: `x ∈ fcDomain f
  ↔ f square-integrable vs μ_x` — the domain *is* the `L²` condition, opening Mathlib's Cauchy–Schwarz / `f·g
  ∈ L¹` for the operator). Axiom-free, budget 0, wired. NEXT: the operator `fcLinear` on the domain (Riesz rep
  of the bounded antilinear `y ↦ ∫ f dμ_{x,y}`, bounded via the now-available L² Cauchy–Schwarz) + symmetry +
  self-adjointness; then `∫g dE = boundedFC g`. **L¹-on-domain ✅** (`integrable_of_mem_fcDomain`: `f ∈ L¹(μ_x)`
  on the domain via `L²⊆L¹` + `μ_x` finite — the diagonal expectation `⟨x,(∫f dE)x⟩ = ∫ f dμ_x` converges).
  **Real-symbol self-adjointness ✅** (`boundedFC_isSelfAdjoint`: `f̄=f ⟹ boundedFC f` self-adjoint, via the
  polarized form's conj-symmetry — the symmetry seed for `K` and half the norm identity
  `‖boundedFC g x‖²=∫|g|²dμ_x`). **Operator route chosen: truncation limits** `Kx := lim boundedFC(fₙ)x`
  (reuses the built `boundedFC` + L²-Cauchy; no cross-measure). **Truncation L²-convergence ✅**
  (`fcTrunc` `=f·𝟙_{|f|≤n}` + `fcTrunc_lintegral_sub_sq_tendsto`: on the domain `∫|f−fₙ|²dμ_x → 0` by
  dominated convergence, dominated by `f²∈L¹` — the L²-Cauchy engine). **boundedFC adjoint ✅**
  (`boundedFC_adjoint`: `(boundedFC g)† = boundedFC(conj∘g)` — the bounded FC is a `*`-hom). **Polarization
  diagonal ✅** (`bilinDiag_self`: `B_g(x,x) = ∫ g dμ_x`). **Diagonal expectation ✅** (`inner_boundedFC_self`:
  `⟨x,(∫h dE)x⟩ = ∫ h dμ_x` — the JLMS first-law `⟨K⟩` at the bounded level, from `inner_boundedFC`+
  `bilinDiag_self`). **Operator identity `T†T=boundedFC(|g|²)` ✅** (`boundedFC_adjoint_mul_self`: composing
  `boundedFC g` with its adjoint gives the FC of `ḡ·g`, via adjoint+`boundedFC_mul`; the proof-irrelevance of the
  `Measurable`/bound hypotheses made the instance-matching go through). **★ THE NORM IDENTITY ✅**
  (`norm_boundedFC_sq`: `‖boundedFC g x‖² = ∫|g|²dμ_x` — the `re`/`∫` diagonal of `T†T`, via
  `inner_boundedFC_self` + `conj z·z=‖z‖²` + `integral_ofReal`). The keystone converting truncation
  L²-convergence into operator-image Cauchy-ness. **Difference-norm ✅** (`boundedFC_sub` +
  `norm_boundedFC_sub_sq`: `‖boundedFC g₁ x − boundedFC g₂ x‖²=∫|g₁−g₂|²dμ_x` — the concrete Cauchy bound).
  **Cauchy integrand bound ✅** (`fcTrunc_diff_sq_le`: `(fₘ−fₙ)²≤2(f−fₘ)²+2(f−fₙ)²`). **Bochner tail-conv ✅**
  (`fcTrunc_integral_sub_sq_tendsto`: `∫|f−fₙ|²dμ_x → 0` real, from the lintegral version via
  `∫g=(∫⁻ofReal g).toReal` + `toReal` continuity). **⚠ CHECKPOINT — the Bochner integral-bound lemma
  `∫(fₘ−fₙ)²≤2∫(f−fₘ)²+2∫(f−fₙ)²` hit a `whnf` elaboration blowup** (heartbeats diverge past 800k) in the
  `Integrable.mono`/`integral_mono` chain over the `Measure.ofMeasurable`-defined `scalarMeasure x` — the same
  pathology class as `CrossedProductRep`. **✅ WORKAROUND LANDED** — the bound at the `lintegral` (ℝ≥0∞) level
  `fcTrunc_diff_lintegral_le` (`∫⁻ofReal((fₘ−fₙ)²) ≤ 2∫⁻ofReal((f−fₘ)²)+2∫⁻ofReal((f−fₙ)²)`, via
  `lintegral_mono`/`_add_left`/`_const_mul`) builds clean — confirming the blowup was Bochner-`Integrable`-
  specific; `lintegral` over `scalarMeasure` elaborates fine. **Operator sequence + diff-norm bridge ✅**
  (`fcSeq hf n x := boundedFC(fₙ)x` the ℂ-truncation operator; `fcSeq_norm_sub_sq`:
  `‖fcSeq m x − fcSeq n x‖² = (∫⁻ofReal((fₘ−fₙ)²)dμ_x).toReal` — via `norm_boundedFC_sub_sq` + the real-coercion
  `‖↑a−↑b‖²=(a−b)²` + `∫g=(∫⁻ofReal g).toReal`; calc form to beat the symbol-lambda beta-redexes). NEXT:
  `‖fcSeq m x − fcSeq n x‖² ≤ (2A_m+2A_n).toReal → 0`. **Squared-norm bound + ★ CauchySeq ✅**
  (`fcSeq_norm_sub_sq_le`: `‖fcSeq m x−fcSeq n x‖² ≤ 2A_m+2A_n` real, finiteness from the domain via `toReal`
  monotone; `fcSeq_cauchySeq`: `boundedFC(fₙ)x` is `CauchySeq` on the domain — `Metric.cauchySeq_iff` + the
  bound + `A_k→0` + `lt_of_pow_lt_pow_left₀`). **So the strong limit exists (H complete).** **★ THE OPERATOR ✅**
  (`fcOp hf x := limUnder (boundedFC(fₙ)x)`; `fcSeq_tendsto_fcOp`: `boundedFC(fₙ)x → fcOp x` on the domain via
  `CauchySeq.tendsto_limUnder`; `fcOp_add` + `fcOp_smul`: additive + ℂ-homogeneous — **a linear operator
  `∫ f dE` on `D(∫f dE)`**). **★ SYMMETRY ✅** (`fcOp_symmetric`: `⟨(∫f dE)x, y⟩ = ⟨x, (∫f dE)y⟩` on the domain
  — each `boundedFC(fₙ)` self-adjoint (`f` real) + `inner`-continuity of the limit). **M1 ESSENTIALLY COMPLETE:
  the unbounded FC `∫ f dE` exists as a linear, symmetric operator on its domain — axiom-free, end-to-end from
  the bounded FC.** (Optional wrap-up: bounded-compat `∫g dE = boundedFC g`; formal `LinearPMap`+`IsSelfAdjoint`
  packaging.) NEXT → **M2**: `E_R := PVM_of_selfAdjoint R`; `K := fcOp` at `log(r/(2−r))` (symmetric via
  `fcOp_symmetric`); `Δ^{it} = boundedFC(((2−r)/r)^{it}) = e^{−itK}` (the FC exponential law, Stone Phase 2.1)
  → JLMS Stage 1 closed.
- [x] **M2 ✅ COMPLETE** — `K` operator + `Δ^{it}=e^{−itK}` (JLMS Stage 1). `K=∫f dE` operator + operator-level
  first law `⟨K⟩=cgpEntropy` + the **STONE generator `d/dt(boundedFC(e^{itf})x)|₀ = i·(∫f dE)x`**
  (`hasDerivAt_boundedFC_expSymbol`) = the operator `Δ^{it}=e^{−itK}`, all axiom-free. (Original detail:)
  **Operator-level first law ✅**
  (`fcOp_inner_self`: `⟨x,(∫f dE)x⟩ = ∫ f dμ_x` on the domain — bounded diagonals `⟨x,boundedFC(fₙ)x⟩=∫fcTrunc f n
  dμ` converge by inner-continuity + the L¹ tail-conv `fcTrunc_integral_tendsto` via Bochner DCT, which builds
  clean — `tendsto_integral_of_dominated_convergence` ≠ the `integral_mono` chain that blew up). For
  `K=∫log(r/(2−r))dE_R` this is the OPERATOR `⟨K⟩=∫kFn dμ=cgpEntropy`. **★ INSTANTIATION ✅**
  (`QIQTH/ModularHamiltonianOp.lean`: `modK S := E_R.fcOp (kFn∘val)` with `E_R = PVM_of_selfAdjoint (rvdRC S)`
  — **the modular Hamiltonian `K = −log Δ` as a genuine operator** (the doc-flagged Tomita–Takesaki frontier, now
  built); `modK_inner_self`: `⟨ξ, K ξ⟩ = cgpEntropy S ξ` — the OPERATOR-level JLMS first law `⟨K⟩=S`, using
  `rvdSpecMeasure = E_R.scalarMeasure` (def) + `cgpEntropy_eq_integral_kFn`). **JLMS Stage 1 closed at the
  operator level.** **K a symmetric linear operator ✅** (`modK_symmetric` `K=K†`, `modK_add`, `modK_smul`).
  **M2 SUBSTANTIVELY DELIVERED: the modular Hamiltonian `K` is a genuine ℂ-linear symmetric unbounded operator
  with `⟨K⟩ = cgpEntropy` — discharging the doc-flagged Tomita–Takesaki frontier.** **⚠ REMAINING M2 FRONTIER
  (checkpointed):** `Δ^{it} = e^{−itK}` as an *operator* identity. The spectral-level `modChar_eq_exp_neg_kFn`
  (`modChar t r = e^{−it·kFn r}`) + `modChar`'s strongly-continuous unitary-group structure already exist;
  lifting to `= e^{−itK}` at the operator level is **Stone generator-reconstruction** (group → generator
  derivative `d/dt boundedFC(e^{itf})x|₀ = i·Kx`) — the same gap as M4 general Stone, recorded as frontier.
  **Partial: the FC-exponential UNITARY GROUP ✅** (`boundedFC_expSymbol_add`: group law `boundedFC(e^{i(s+t)f}) =
  boundedFC(e^{isf})·boundedFC(e^{itf})`; `boundedFC_expSymbol_adjoint_mul`: unitarity
  `boundedFC(e^{itf})†·boundedFC(e^{itf})=1` via `boundedFC_adjoint_mul_self` with `|e^{itf}|²=1`). So for any PVM,
  `exp(itK)` is a one-parameter **unitary** group — the **full bounded-operator content of `Δ^{it}=e^{−itK}`**;
  only the generator-derivative link `d/dt(·)|₀ = i·K` to `K` (Stone reconstruction) stays the gap.
  (Group axioms complete: `boundedFC_expSymbol_zero` identity + `_add` composition + `_adjoint_mul` inverse.)
  **STONE-GENERATOR ATTACK underway** (foundations ✅, all axiom-free): the difference identity
  `‖boundedFC(e^{itf})x − x‖² = ∫|e^{itf}−1|² dμ_x` (`expSymbol_sub_one_norm_sq`); the uniform L² domination
  `‖e^{itf}−1‖ ≤ |t|·|f|` ⟹ `‖(e^{itf}−1)/t‖ ≤ |f|` (`norm_expSymbol_sub_one_le`); the pointwise derivative
  `d/dt e^{itc}|₀ = ic` (`hasDerivAt_expSymbol`).
  **ANALYTIC HEART NOW LANDED ✅ (axiom-free, green):** the `t→0` **L²-convergence of the difference quotient**
  `∫‖(e^{itf}−1)/t − if‖² dμ_x → 0` (`expSymbol_diffQuotient_lintegral_tendsto`) — proved via the **sequential
  `lintegral` dominated-convergence route** (dodging the recurring Bochner-over-`scalarMeasure` whnf wall):
  pointwise `(e^{itc}−1)/t → ic` from the new slope tendsto `expSymbol_slope_tendsto` (`hasDerivAt_iff_tendsto_slope`),
  dominated by `4f²` from `norm_expSymbol_sub_one_div_le` (`‖(e^{itf}−1)/t‖ ≤ |f|` for ALL `t`, incl `t=0`),
  finite by `x ∈ fcDomain f`. This was *the* genuine multi-fire core.
  **OPERATOR ASSEMBLY — steps 1 & 2 NOW LANDED ✅ (axiom-free, green):**
  • **step 1** `complexSymbol_fcTrunc_lintegral_tendsto`: for a bounded symbol `h`, `∫‖h − i·↑fcTrunc_m‖² → ∫‖h − i·↑f‖²`
    (lintegral DCT, dominated by `2C²+2f²`) — the `m→∞` truncation half.
  • **step 2 (CRUX)** `dist_boundedFC_smul_fcOp_sq`: `‖boundedFC(h)x − i·(∫f dE)x‖² = ∫‖h − i·↑f‖² dμ_x` — the operator
    distance to `i·fcOp x` **equals** the `L²` symbol distance to `i·f`, collapsing the double-limit to a SINGLE limit
    (limit-uniqueness: `i·fcSeq_m x → i·fcOp x` + `norm_boundedFC_sub_sq` + step 1). This replaces the messy
    ε–δ triangle entirely.
  • **step 3 CAPSTONE NOW LANDED ✅ (axiom-free, green)** `hasDerivAt_boundedFC_expSymbol`:
    `d/dt(boundedFC(e^{itf})x)|₀ = i·(∫f dE)x` — the strongly-continuous one-parameter unitary group
    `t↦boundedFC(e^{itf})` has generator `i·K` (`K=∫f dE`): **the operator `Δ^{it}=e^{−itK}`**. Assembled exactly as
    planned: `slope g 0 t = (↑t)⁻¹•boundedFC(e^{itf}−1)x` (`boundedFC_sub`/`_smul`, proof-irrelevance via defeq-`exact`,
    `Complex.coe_smul`/`ofReal_inv` for the `↑(t⁻¹)` bridge) ⟹ via the distance identity
    `‖slope − i·fcOp x‖² = (∫⁻‖(e^{itf}−1)/t − if‖²).toReal` ⟹ `→ 0` (heart, `lintegral_congr` bridges `(↑t)⁻¹(e^{itf}−1)`
    to `(e^{itf}−1)/t`) ⟹ `‖·‖→0` (`Real.sqrt_sq`) ⟹ `slope → i·fcOp x`. **The full STONE generator reconstruction
    for the bounded-self-adjoint PVM is now axiom-free.** Closes `Δ^{it}=e^{−itK}` (M2) and abstract M4 Stone.
  • **MODULAR SPECIALIZATION NOW LANDED ✅ (axiom-free, green)** `hasDerivAt_modFlow` (`ModularHamiltonianOp.lean`):
    the modular flow `t ↦ boundedFC(e^{it·kFn}(R)) ξ` (= `modChar(−t) = Δ^{−it}` on the spectrum, by
    `modChar_eq_exp_neg_kFn`) has Stone generator `i·modK = iK` — **the operator `Δ^{it}=e^{−itK}` pinned to the
    genuine RvD modular Hamiltonian `K = modK`**. A direct specialization of the general capstone to
    `E_R = PVM_of_selfAdjoint (rvdRC S)`, symbol `kFn ∘ val` (one-liner: the capstone's RHS `i·E_R.fcOp(kFn∘val)ξ` IS
    `i·modK ξ` by definition). **The operator half of the Tomita–Takesaki `Δ^{it}=e^{−itK}` frontier is fully discharged.**
  • **STRONG CONTINUITY NOW LANDED ✅ (axiom-free, green)** — `continuousAt_boundedFC_expSymbol` (at `0`, a free
    corollary of the `HasDerivAt` capstone) + `continuousAt_boundedFC_expSymbol'` (at every `t₀`, via the group law
    `U_{t₀+s}=U_{t₀}U_s`) + `continuousAt_modFlow` (modular specialization). **Resolves the strong-continuity step
    the earlier Bochner-`tendsto_integral_of_dominated_convergence` route could not** (the recurring `whnf` wall,
    previously reverted): the `lintegral`-built `HasDerivAt` delivers it for free. With group law + unitarity +
    generator + strong continuity, the modular flow is now a **full `C₀` one-parameter unitary group with generator
    `iK`** — the complete operator Stone package, axiom-free.
  • **UNITARITY (norm-preservation) NOW EXPLICIT ✅** — `norm_boundedFC_expSymbol` (`‖boundedFC(e^{itf})x‖=‖x‖`,
    from `U⋆U=1`) + `norm_modFlow` (`‖Δ^{it}ξ‖=‖ξ‖`): the modular flow preserves the norm of every vector, completing
    `Δ^{it}` as a genuine `C₀` one-parameter **unitary** group (group law + generator `iK` + strong continuity +
    norm-preservation), axiom-free.
  • **INFINITESIMAL JLMS FIRST LAW NOW LANDED ✅ (axiom-free, green)** — `hasDerivAt_inner_boundedFC_expSymbol`
    (`d/dt⟪η,boundedFC(e^{itf})x⟫|₀ = ⟪η,i·(∫f dE)x⟫`, generator ∘ `HasDerivAt.inner`) + `hasDerivAt_modFlow_inner`:
    **`d/dt⟨ξ,Δ^{it}ξ⟩|₀ = i·S`** where `S = cgpEntropy` (combining the generator `iK` with the operator first law
    `⟨K⟩=S`, `modK_inner_self`). This ties the entire `C₀` modular-flow Stone package **directly to the entanglement
    entropy** — the infinitesimal JLMS first law at the operator level.
  • **CANONICAL `Δ^{it}=e^{−itK}` (generator `−iK`) NOW LANDED ✅** — `hasDerivAt_modChar`: the flow
    `boundedFC(e^{it·(−kFn)}(R)) = modChar(t) = Δ^{it}` on the spectrum has Stone generator `−i·modK = −iK`, i.e.
    `Δ^{it}=e^{−itK}` *literally* (textbook sign). Uses the new symbol-linearity `fcOp_neg` (`∫(−kFn)dE = −modK`)
    on top of the general capstone — the canonical statement now sits directly in the library.
  • **REAL-VALUED (PHYSICAL) FIRST LAW NOW LANDED ✅** — `hasDerivAt_modFlow_inner_im`:
    `d/dt Im⟪ξ,Δ^{−it}ξ⟫|₀ = S` (`= cgpEntropy`). Since the correlator's derivative `i·S` is purely imaginary, the
    entropy is precisely the `t`-derivative of the **imaginary part** of the modular correlator — a real observable
    (the real part is stationary at `t=0`). The operator first law in its physical, real-valued form.
  • **UNIFICATION — `K = modK` IS the generator of the crossed-product's `Δ^{it}` ✅ (axiom-free, green)** —
    `modUnitary_eq`: the crossed-product modular unitary `modUnitary S t` (= `borelFC(modChar t)`, on which the
    modular automorphism `σ_t(a)=Δ^{it}aΔ^{−it}` and the crossed product `M ⋊_σ ℝ` are built) is *definitionally*
    `(PVM_R).boundedFC` of `modSpecFun S t`, and `modSpecFun S t ω = modChar t ω.val = e^{it·(−kFn ω.val)}` (by
    `modChar_eq_exp_neg_kFn` on the spectrum `(0,2)`; both `=1` off it). Hence `hasDerivAt_modUnitary`:
    `d/dt(modUnitary S t · ξ)|₀ = −i·modK ξ` — **the Stone generator of the actual crossed-product `Δ^{it}` is the
    unbounded-FC modular Hamiltonian `K = modK`**. This bridges the M2 Stone work to the M5 crossed-product/Wall:
    `borelFC ≡ (PVM_of_selfAdjoint).boundedFC` is the load-bearing definitional identity.
  • **`modUnitary` `C₀`-package COMPLETE ✅** — `continuousAt_modUnitary` (`t ↦ modUnitary S t ξ` continuous at
    every `t₀`, domain `ξ`) is the last piece: with `modUnitary_add` (group), `modUnitary_unitary`, the generator
    `−iK` (`hasDerivAt_modUnitary`) and strong continuity, the crossed-product's `Δ^{it}` is now a full
    `C₀` one-parameter unitary group **with a known generator** — exactly the Stone-theorem package the Wall rests on.
  • **GR-CHAIN LOCALIZATION IDENTITY DERIVED ✅ (bridges M2 → M6/M7)** — `hasDerivAt_inner_modUnitary`:
    `d/dt⟪ξ, modUnitary S t ξ⟫|₀ = i·(−S)`. This is **exactly** the modular-correlation-derivative hypothesis bundled
    into `WedgeKMSToGR.WedgeKMSFlux` (line 65 — the per-null-generator localization input of the Bekenstein→GR chain),
    now *derived* from the operator modular machinery (generator `−iK` + first law `⟨K⟩=S`) rather than assumed. It
    identifies the GR heat-flux datum `kd = −cgpEntropy S ξ` (the modular entropy) — the first-law/Clausius datum at
    the operator level. The modular Stone work now feeds directly into the GR derivation chain's labelled inputs.
  • **`modUnitary` strongly-continuous group form ✅** (`continuous_modUnitary`: the textbook `Continuous` `C₀`-group statement).
  • **FLOW IS `C¹` EVERYWHERE ✅** — `continuous_boundedFC_expSymbol` (general strongly-continuous form) +
    `hasDerivAt_boundedFC_expSymbol'`: `d/dt(U_t x)|_{t₀} = U_{t₀}(i·K x)` at **every** `t₀` (not just `0`), via the
    group law `U_t = U_{t₀}U_{t−t₀}` (`comp_sub_const` for the shift + `restrictScalars`/`comp_hasDerivAt` for the
    `U_{t₀}`-application). The FC-exponential group is `C¹` on the whole line: `U_t' = i·U_t·K` — the complete
    differentiable-Stone-group statement.
  • **`modUnitary` `C¹` everywhere ✅** (`hasDerivAt_modUnitary'`: `d/dt(modUnitary S t ξ)|_{t₀} = Δ^{it₀}(−iK ξ)` at
    every `t₀`) — the crossed-product `Δ^{it}` is now a fully smooth (`C¹`) `C₀` one-parameter unitary group with
    generator `−iK`. Specializes the general `hasDerivAt_boundedFC_expSymbol'` via `modUnitary_eq` + `fcOp_neg`.

  **WedgeKMSFlux derivation-status map (precise):** the GR chain's `WedgeKMSFlux` bundle (per null generator) has 6
  inputs; the modular Stone machinery now provides one of the two `HasDerivAt` data:
    1. wedge carrier `S.toClosedSubmodule = closure(span wedgeGenSet)` — geometric input (wedge localization);
    2. `V t = boostUnitary(−2πt)` — definitional;
    3. `(MapsTo ∧ StripKMS → modUnitary = V)` — the **Bisognano–Wichmann identification** (physical input);
    4. `StripKMS V D` — the KMS/strip-analyticity input;
    5. boost derivative `d/dt⟪ξ,boostUnitary(−2πt)ξ⟫|₀ = i·(2π/ℏ)·T_kk` — **frontier**: `boostUnitary = translationFlow.unitary`,
       so this is the *translation generator* (momentum), needing the Fourier/momentum PVM (the same clock-`X` wall);
       the multiplication-FC Stone does NOT reach it;
    6. modular derivative `d/dt⟪ξ,modUnitary S t ξ⟫|₀ = i·kd` — **DERIVED ✅** (`hasDerivAt_inner_modUnitary`, `kd=−S`).
  So the chain's `hFlux` (via `HasDerivAt.unique` on #5 vs #6 under BW #3) reads `2π/ℏ·T_kk = −S` (Clausius), and #6 is
  now ours. Remaining: #5 (translation generator / Fourier frontier) + #1/#3/#4 (geometric/physical wedge inputs).

  **Momentum-PVM frontier (toward #5) — brick 1 STARTED ✅** (`QIQTH/Spectral/MultiplicationOp.lean`): the bounded
  **multiplication operator `M_φ`** on `L²(μ)` for any bounded measurable `φ` (`‖φ‖≤C`): `(M_φ f)(s)=φ s·f s`, a
  ℂ-linear CLM with `‖M_φ‖≤C` (`mulOp`, via `MemLp.of_le_mul` + `mkContinuous`; mirrors `matterRep` for the scalar
  case). This is the foundation of the **position PVM** `E(A)=M_{𝟙_A}` → (Fourier-conjugated) the **momentum/translation
  generator** = the `boostUnitary` generator (#5). Honest scope: this is a sustained multi-fire build (position PVM
  σ-additivity → scalarMeasure → Fourier-Plancherel conjugation → the generator), and even completing #5 leaves the
  GR chain gated on the physical inputs #1/#3/#4. Axiom-free, budget 0, full build green.
  **Brick 2 — the `*`-algebra + the spectral projection ✅**: `M_φ∘M_ψ = M_{φ·ψ}` (`mulOp_mul`), `M_c = c·1`
  (`mulOp_const`), `mulOp_congr` (symbol-determined), and the spectral projection `E(A) = M_{𝟙_A}` (`indMul`) is
  **idempotent** `E(A)²=E(A)` (`indMul_idempotent`, since `𝟙_A·𝟙_A=𝟙_A`).
  **Brick 3 — the `*`-structure ✅**: adjoint `M_φ* = M_φ̄` (`mulOp_adjoint`, via the `L²` inner product
  `⟪M_φ̄ f,g⟫=⟪f,M_φ g⟫`) ⟹ `E(A)` is **self-adjoint** (`indMul_isSelfAdjoint`, `𝟙_A` real). **With idempotency,
  `E(A)` is now an ORTHOGONAL PROJECTION** — the spectral projection of the position observable. Next bricks:
  σ-additivity (`E(⋃Aₙ)=Σ E(Aₙ)` strong) → `scalarMeasure` `⟨f,E(A)f⟩=∫_A|f|²` → the PVM; then Fourier conjugation.
  **Brick 4 — the projection-valued content ✅**: `E(univ)=1` (`indMul_univ`), `E(∅)=0` (`indMul_empty`), and
  **`E(A)·E(B)=E(A∩B)`** (`indMul_inter`, via `mulOp_mul` + `𝟙_A·𝟙_B=𝟙_{A∩B}`) — commuting orthogonal projections,
  disjoint ⟹ orthogonal `E(A)E(B)=0`. This is the finitely-additive **PV-content** of the position PVM.
  **Brick 5 — the scalar spectral measure ✅**: `⟪f, E(A) f⟫ = ∫_A conj(f)·f dμ = ∫_A ‖f‖² dμ` (`indMul_inner_self`,
  via `L2.inner_def`) — the `L²` mass of `f` on `A` (= `‖E(A)f‖²≥0`); as `A` varies, the `‖f‖²`-weighted scalar
  spectral measure `μ_f`.
  **Brick 6 — finite additivity ✅**: `M_φ+M_ψ=M_{φ+ψ}` (`mulOp_add`) ⟹ `E(A⊔B)=E(A)+E(B)` for disjoint `A,B`
  (`indMul_union_disjoint`, via `𝟙_{A∪B}=𝟙_A+𝟙_B`) — the finitely-additive projection-valued measure. Next bricks:
  σ-additivity (countable / strong `E(⋃Aₙ)=Σ E(Aₙ)`) → bundle the `ProjectionValuedMeasure`; then Fourier conjugation.
  **Brick 7 — symbol-linearity complete ✅**: `M_φ−M_ψ=M_{φ−ψ}` (`mulOp_sub`), `M_{c·φ}=c·M_φ` (`mulOp_smul`). With
  add/mul/const/adjoint/congr, **`M_·` is now a complete unital `*`-algebra homomorphism** (bounded measurable
  functions → CLM on `L²`) — Mathlib-quality multiplication-operator infrastructure.
  **Brick 8 — the scalar spectral measure (real/nonneg) ✅**: `‖E(A) f‖² = ∫_A ‖f‖² dμ` (`norm_indMul_sq`, via
  `inner_self_eq_norm_sq` + `L2.inner_def` + `integral_re`) — the `L²` mass of `f` on `A`. So `μ_f(A) = ∫_A ‖f‖²` is
  the genuine (real, nonnegative) scalar spectral measure of the position PVM, and the key quantitative input to
  σ-additivity (the tail `∫_{A_N} ‖f‖² → 0`).
  **Brick 9 — σ-additivity of the scalar measure (continuity from above) ✅**: for antitone `Bₙ`,
  `‖E(Bₙ)f‖²=∫_{Bₙ}‖f‖² → ∫_{⋂Bₙ}‖f‖²` (`norm_indMul_tendsto_iInter`, via `norm_indMul_sq` +
  `tendsto_setIntegral_of_antitone`, `‖f‖²∈L¹`). In particular `Bₙ↓∅ ⟹ ‖E(Bₙ)f‖→0` — the measure-tail driving the
  position PVM's operator σ-additivity. Next: the operator σ-additivity (`E(⋃Aₙ)f=∑E(Aₙ)f` via finite-additivity +
  this tail) → bundle the `ProjectionValuedMeasure`; then Fourier conjugation → momentum PVM → boost generator.
  NB the Bochner-over-`scalarMeasure` DCT route hits a `whnf` wall — the `lintegral`/`HasDerivAt` route is the way.
  **Brick 10 — subtractivity `E(B)=E(A)+E(B\A)` for `A⊆B` ✅**: the operator-level finite-additive decomposition
  `B=A⊔(B\A)` (`indMul_sdiff`, via `indSymbol_sdiff` `𝟙_B=𝟙_A+𝟙_{B\A}` + `mulOp_add`). Equivalently `E(B)−E(A)=E(B\A)`
  — the difference operator that turns the scalar measure-tail (brick 9) into the genuine operator σ-additivity
  `‖E(Bₙ)f−E(⋃)f‖²=∫_{(⋃)\Bₙ}‖f‖²→0`. Next: assemble `indMul_tendsto_iUnion` (operator σ-additivity, monotone `Bₙ↑⋃`)
  from this + brick 9 → bundle the `ProjectionValuedMeasure`; then Fourier conjugation → momentum PVM → boost generator.
  **Brick 11 — OPERATOR σ-ADDITIVITY (continuity from below / strong convergence) ✅**: for monotone `Bₙ↑⋃ₖBₖ`,
  `E(Bₙ)f → E(⋃ₖBₖ)f` in `L²` (`indMul_tendsto_iUnion`). Proof: `‖E(Bₙ)f−E(⋃)f‖²=‖E((⋃)\Bₙ)f‖²=∫_{(⋃)\Bₙ}‖f‖²`
  (subtractivity brick 10 + `norm_indMul_sq` brick 8), and `(⋃)\Bₙ↓∅` so the tail `→∫_∅=0` (brick 9 engine,
  `tendsto_setIntegral_of_antitone`), then `‖·‖²→0 ⟹ ‖·‖→0` (`Real.sqrt` continuity). THE genuine countable-additivity
  (strong-convergence) property of the position PVM — the last structural brick before bundling the
  `ProjectionValuedMeasure`. Next: bundle the `PVContent`/`ProjectionValuedMeasure` record (PV-content from
  univ/empty/inter/finite-additivity bricks + this σ-additivity) → Fourier conjugation → momentum PVM → boost generator.
  **Brick 12 — pairwise orthogonality of the spectral projections ✅**: for disjoint measurable `A,B`,
  `E(A)∘E(B)=0` (`indMul_comp_disjoint`, via `E(A)E(B)=E(A∩B)=E(∅)=0`) and `⟪E(A)x,E(B)x⟫=0`
  (`indMul_inner_orthogonal`, self-adjointness + the composition). The projected components live in orthogonal
  subspaces `L²(A)⟂L²(B)` — the orthogonality input to the UNCONDITIONAL (pairwise-disjoint) σ-additivity in
  `HasSum` form that the `ProjectionValuedMeasure` record's `hasSum_iUnion` field demands. Next: range-additivity
  `∑_{n<N}E(Aₙ)=E(⋃_{n<N}Aₙ)` → `Summable` via `OrthogonalFamily.summable_iff_norm_sq_summable` (∑‖E(Aₙ)x‖²=‖E(⋃)x‖²
  bounded by ‖x‖²) → identify the limit with `E(⋃)x` (brick 11) → bundle the `ProjectionValuedMeasure`.
  **Brick 13 — finite (range) additivity over a `Finset` ✅**: for pairwise-disjoint measurable `A`,
  `∑_{i∈s}E(Aᵢ)=E(⋃_{i∈s}Aᵢ)` (`indMul_biUnion_disjoint`, `Finset` induction via `indMul_union_disjoint` +
  set-congruence `indMul_set_congr` — the projection depends only on the set, measurability proof-irrelevant).
  The discrete additivity feeding the unconditional `HasSum` σ-additivity (partial sums = projection onto the
  partial union). **FRONTIER (honest checkpoint):** the `ProjectionValuedMeasure.hasSum_iUnion` bundle now needs
  the **Hilbert orthogonal-summability bridge** — `Summable (fun n => E(Aₙ)x)` from `∑‖E(Aₙ)x‖²<∞` via
  `OrthogonalFamily` of the ranges `L²(Aₙ)` (brick 12 orthogonality) `.summable_iff_norm_sq_summable`, then
  identify `∑'` with `E(⋃)x` (brick 11). That orthogonal-family setup (subspaces + isometric inclusions +
  the summability lemma) is the genuine Mathlib-grade step; bricks 8–13 supply all its inputs. Left green here.
  **Brick 14 — the remaining orthogonal-summability inputs ✅**: `norm_sq_eq_integral` (`‖x‖²=∫‖x a‖²`, read off
  `E(univ)=1`), `norm_indMul_le` (`‖E(A)x‖≤‖x‖` — the projection is contractive, via `∫_A≤∫`; gives the uniform
  bound `∑‖E(Aₙ)x‖²≤‖x‖²`), and `indMul_inner_orthogonal'` (`⟪E(A)x,E(B)y⟫=0` for ALL `x,y` on disjoint `A,B` —
  the two-vector orthogonality the `OrthogonalFamily` of ranges `L²(Aₙ)` requires). With bricks 11–13, ALL inputs
  to `hasSum_iUnion` are now in hand. Next: assemble `OrthogonalFamily.summable_iff_norm_sq_summable` → `HasSum`
  → bundle the `ProjectionValuedMeasure` record.
  **Brick 15 — SUMMABILITY of the spectral components (the analytic heart) ✅**: for pairwise-disjoint measurable
  `A`, `Summable (fun n => E(Aₙ)x)` in `L²` (`summable_indMul`). The vectors `E(Aₙ)x` live in the pairwise-**orthogonal**
  ranges `L²(Aₙ)`, assembled as an `OrthogonalFamily` of submodule ranges (brick 14 two-vector orthogonality); and
  `∑‖E(Aₙ)x‖²≤‖x‖²` (finite partial sums `= ‖E(⋃ᵢ₌₀ⁿAᵢ)x‖²≤‖x‖²` by `OrthogonalFamily.norm_sum` Pythagoras + brick 13
  range-additivity + brick 14 contractivity), so `OrthogonalFamily.summable_iff_norm_sq_summable` gives `Summable`.
  This is the orthogonal-family bridge the `hasSum_iUnion` bundle needed — the genuine Mathlib-grade step, now landed.
  Next: identify `∑' = E(⋃)x` (range partial sums `= E(⋃ᵢ₌₀ⁿAᵢ)x → E(⋃)x` via brick 11 + `HasSum.tendsto_sum_nat`,
  uniqueness of limits) → bundle the `ProjectionValuedMeasure` record.
  **Brick 16 — THE POSITION PVM BUNDLED ✅ (`ProjectionValuedMeasure` complete)**: `hasSum_indMul_iUnion`
  (`∑ₙE(Aₙ)x=E(⋃Aₙ)x` in `HasSum` form — `summable_indMul` brick 15 + range partial sums `E(⋃ᵢ₌₀ⁿAᵢ)x→E(⋃)x`
  via brick 11 + uniqueness of limits) closes the last structure field, and `positionPVM :
  ProjectionValuedMeasure α (Lp ℂ 2 μ)` (`QIQTH/Spectral/PositionPVM.lean`) bundles `E(A)=M_{𝟙_A}` with ALL fields
  discharged: self-adjoint idempotents (bricks 2–3), `E(∅)=0`/`E(univ)=1`/`E(A∩B)=E(A)E(B)` (brick 4), strong
  `HasSum` σ-additivity (bricks 8–15). **The canonical position PVM is now a genuine `ProjectionValuedMeasure`,
  axiom-free (standard 3), budget 0 — the multiplication-PVM frontier (bricks 1–16) is COMPLETE.** It is the
  Mathlib-contributable spectral measure of the position operator on `L²(μ)`. Next frontier: Fourier-Plancherel
  **PVM unitary conjugation ✅ (the Fourier mechanism, unitary-generic)** — `QIQTH/Spectral/PVMConj.lean`,
  axiom-free, budget 0, full build green: for any `ProjectionValuedMeasure P` and unitary `U : H ≃ₗᵢ[ℂ] H`,
  `(P.conj U).E A = U ∘ P.E A ∘ U⁻¹` is again a genuine `ProjectionValuedMeasure`. All fields transport —
  self-adjoint (`U†=U⁻¹`, `E†=E`), idempotent (`U⁻¹U=1`), `∅↦0`, `univ↦UU⁻¹=1`, multiplicative, σ-additive
  (`U` continuous-linear ⟹ `HasSum` preserved via `HasSum.mapL`). This is THE general mechanism by which the
  Fourier–Plancherel transform carries `positionPVM` to the **momentum PVM**. **Honest checkpoint:** the
  conjugation construction is complete and reusable; instantiating `U` with the concrete `L²` Fourier transform
  (`Real.fourierIntegral` + Plancherel as a `≃ₗᵢ`) is the next, **Mathlib-Fourier-gated**, step. And even the
  momentum PVM / generator (#5), once built, leaves the GR chain gated on the physical wedge inputs #1/#3/#4.
  **THE MOMENTUM PVM BUILT ✅** — `QIQTH/Spectral/MomentumPVM.lean`, axiom-free (standard 3 — even through
  Mathlib's Plancherel), budget 0, full build green: `momentumPVM = positionPVM.conj (Lp.fourierTransformₗᵢ ℝ ℂ)`,
  i.e. `Ê(A) = ℱ E(A) ℱ⁻¹`. The Mathlib-Fourier gate is **CLEARED** — Mathlib ships the `L²` Fourier transform as
  a unitary `MeasureTheory.Lp.fourierTransformₗᵢ : Lp ℂ 2 ≃ₗᵢ[ℂ] Lp ℂ 2`, so the conjugation construction yields
  the momentum PVM with **no further work** — a genuine `ProjectionValuedMeasure ℝ (Lp ℂ 2 volume)`, the spectral
  measure of the momentum operator `P = ℱXℱ⁻¹` on `L²(ℝ)` (built for the canonical 1D case; generalizes verbatim).
  **Remaining toward #5 (honest):** extracting the *unbounded generator* `P = ∫ k dÊ(k)` (Stone's theorem on the
  momentum PVM) so the one-parameter group `e^{itP}` = spatial translation feeds the `boostUnitary` generator — the
  unbounded-FC / Stone frontier. And the GR chain beyond `#5` stays gated on the physical wedge inputs `#1/#3/#4`.
  **Position PVM scalar measure = the Born `|ψ|²` position distribution ✅** (`QIQTH/Spectral/PositionPVM.lean`,
  axiom-free, budget 0): `positionPVM_norm_sq` (`‖E(A)x‖²=∫_A‖x‖²`) and `positionPVM_scalarMeasure`
  (`(scalarMeasure x)(A)=ENNReal.ofReal(∫_A‖x‖²)`). The position PVM's scalar spectral measure **is** the
  (unnormalized) position-probability distribution `|ψ(a)|²dμ(a)` of the state — the **Born rule for position**
  read directly off the bundled `ProjectionValuedMeasure` (corollary of bricks 8 + 16). A clean physical payoff of
  the PVM construction, independent of the Stone / physical-input frontiers.
  **Spectral-measure covariance under unitary conjugation + the Born momentum distribution ✅**
  (`PVMConj.lean` + `MomentumPVM.lean`, axiom-free, budget 0): `norm_conj_E` (`‖(P.conj U).E A x‖=‖P.E A (U⁻¹x)‖`,
  `U` isometry) and `conj_scalarMeasure` (`(P.conj U).scalarMeasure x = P.scalarMeasure (U⁻¹x)`) — spectral
  measures transform covariantly under unitary conjugation. Instance `momentumPVM_scalarMeasure`: the
  momentum-space Born mass of `x` equals the **position** mass of `ℱ⁻¹x`, i.e. `|x̂(k)|²` is the
  momentum-probability density — the **Born rule for momentum** as the Fourier image of the Born rule for
  position. Completes the position↔momentum PVM Born picture, axiom-free.
  **The translation operator / one-parameter group on L²(ℝ) ✅** (`QIQTH/Spectral/TranslationFlow.lean`,
  axiom-free, budget 0): `translationLp t` (`(τ_t f)(x)=f(x+t)`) is a ℂ-linear isometry
  (`Lp.compMeasurePreservingₗᵢ` + volume translation-invariance), with `coeFn_translationLp` (pointwise action),
  `norm_translationLp` (isometry/unitarity), and `translationLp_add` (**the GROUP LAW** `τ_s∘τ_t=τ_{s+t}`,
  ae-composition via `QuasiMeasurePreserving.tendsto_ae.eventually`). So `t↦τ_t` is the one-parameter unitary
  group whose generator is the momentum operator `P` (`e^{itP}=τ_t`) — the kinematic object behind
  `WedgeKMSFlux #5`.
  **Strong continuity ✅ — `t↦τ_t` is now a STRONGLY-CONTINUOUS one-parameter unitary group (the full Stone
  hypothesis)**: `continuous_translationLp` (`t↦τ_t F` continuous `ℝ→L²(ℝ)` for every `F`, via `ContinuousMap.curry`
  of the jointly-continuous `(t,x)↦x+t` + `Continuous.compMeasurePreservingLp`). With the group law + unitarity,
  `t↦τ_t` is a genuine `C₀`-group. **ONLY REMAINING for #5 (honest checkpoint):** identify the generator with the
  momentum PVM, `P=∫k dÊ(k)` (Stone's theorem — the unbounded-FC frontier). The C₀-group, the momentum PVM, and the
  position↔momentum Born picture are all in hand; the generator-extraction (Stone) is the single remaining Lean
  step before `#5`, after which the GR chain stays gated only on the physical wedge inputs `#1/#3/#4` + the `1/4` UV datum.
  **The translation UNITARY group (`≃ₗᵢ` packaging) ✅** (`TranslationFlow.lean`, axiom-free, budget 0):
  `translationLp_zero` (`τ_0=id`) + `translationUnitary t` — `τ_t` as a genuine `≃ₗᵢ[ℂ]` unitary, invertible with
  inverse `τ_{-t}` (via `LinearIsometryEquiv.ofSurjective` + the group law), with `translationUnitary_apply`/
  `_symm_apply`. Upgrades the isometry semigroup to a one-parameter **unitary** group — the form the
  conjugation/modular machinery consumes (e.g. `positionPVM.conj (translationUnitary t)` is the translation-
  covariance of the position observable). The Stone generator `P` remains the single Lean frontier for `#5`.
  **Translation-covariance of the position observable (scalar level) ✅** (`QIQTH/Spectral/PositionCovariance.lean`,
  axiom-free, budget 0): `translationUnitary_coe_apply`/`_symm_coe_apply` (the unitary as a CLM acts by `τ_{±t}`)
  and `positionPVM_conj_translation_scalarMeasure` — `((positionPVM.conj (τ_t)).scalarMeasure x)(A) =
  ∫_A ‖(τ_{-t}x)(a)‖² da`: conjugating the position PVM by translation-by-`t` shifts the Born position
  distribution to that of the translated state `τ_{-t}x`. The covariance that makes the translation generator
  (momentum) conjugate to position.
  **Translation-covariance — the OPERATOR (full Weyl) form ✅** (`PositionCovariance.lean`, axiom-free, budget 0):
  `positionPVM_conj_translationUnitary` — `(positionPVM.conj (τ_t)).E A = positionPVM.E ((·+t)⁻¹A)`, i.e.
  `τ_t E(A) τ_t⁻¹ = E(A−t)`. Proof: `τ_t M_{𝟙_A} τ_{-t} = M_{𝟙_{(·+t)⁻¹A}}` via the indicator-shift
  `𝟙_A(x+t)=𝟙_{(·+t)⁻¹A}(x)` (preimage membership is defeq) + the three `coeFn`s of `τ_{-t}, M_{𝟙_A}, τ_t`
  composed through the measure-preserving shift `·+t`. **The position spectral projection transforms covariantly
  under translation** — exactly the relation making the translation generator (momentum `P`) canonically conjugate
  to position `X`, the kinematic backbone of `#5`. (The earlier scalar-level covariance follows as a corollary.)
  Original next line: Fourier-Plancherel
  conjugation `ℱ : L²→L²` carries `positionPVM` to the **momentum PVM**, whose generator is the translation/boost
  generator (`WedgeKMSFlux #5`) — gated, beyond the PVM infrastructure, on the physical wedge inputs #1/#3/#4.
- [~] **M3** — Williamson `N`-mode area-scaling (frontier; small-`N` first). **`n=1` done ✅**: `oneModeSympEig=√det`
  + Heisenberg floor `ν≥½` (Stage C⁴) + **symplectic invariance** `√det(SMSᵀ)=ν` for `S∈Sp(2,ℝ)` (Stage C⁵,
  `oneModeSympEig_symplectic_invariant` — `ν` is a basis-independent physical invariant). The `N`-mode normal-form
  reduction (diagonalizing the `2N×2N` covariance by a symplectic transformation) stays the labelled Mathlib-grade frontier.
- [~] **M4** — general Stone → `X = A_edge`. **Abstract Stone reconstruction ✅** (`hasDerivAt_boundedFC_expSymbol`:
  the bounded-self-adjoint PVM's FC-exponential group has generator `i·∫f dE`, axiom-free). Remaining = the
  geometric identification `X = A_edge` (the edge-of-wedge boost generator) — the physical-input frontier.
- [~] **M5** — dual-weight trace + JLMS + FQ bound. **Crossed-product Phases 1–4.1 ✅** (`CrossedProduct*.lean`):
  matter rep `π(a)` (Phase 1), clock translation group `λ_t` with group law + isometry + two-sided inverse (Phase 2),
  covariance `λ_{-t}π(a)λ_t=π(σ_t a)` + the generated algebra (Phase 3), and **strong continuity of `λ_t`** (Phase 4.1,
  `clockTransl_stronglyContinuous`). Remaining frontiers: (4.2) the **clock generator `X`** — Stone for the *translation*
  group, which needs the momentum PVM / Fourier conjugation (the multiplication-FC Stone `hasDerivAt_boundedFC_expSymbol`
  does NOT apply: translation ≠ a multiplication FC on a position PVM); (5) the **dual-weight trace** `τ`; (6) the FQ
  bound payoff. Also recorded blocker: `λ_t`'s explicit `adjoint = λ_{-t}` hits the Lp/RCLike adjoint-instance diamond
  (unitarity is already exhibited diamond-free via isometry + two-sided inverse — sufficient for Phase 3).
- [ ] **M6** — Gap-2 localization map
- [ ] **M7** — fusion: `P4 → GR` closed for the free field (UV datum carried)

### Frontier-survey checkpoint (post-Stone build-out)
The tractable operator-algebra infrastructure around the Stone/modular machinery is now **built out and exhausted**:
M1 ✅, M2 ✅ (full `C₀` modular-flow Stone package: generator `iK` + group law + unitarity + strong continuity),
M3 `n=1` ✅ (eigenvalue + floor + symplectic invariance), M5 crossed-product Phases 1–4.1 ✅. Every remaining step is a
genuine Mathlib-grade frontier or gated on a recorded blocker:
- **M3 `N`-mode** — symplectic eigenvalues of a `2N×2N` covariance (Williamson normal form): a spectral/linear-algebra
  Mathlib gap. (Decoupled-block sum is available but would be *fake* area-law progress — not taken.)
- **M4 geometric `X=A_edge`** — Bisognano–Wichmann boost identification: physical input, not a Lean lemma.
- **M5 clock `X` / trace** — momentum PVM (Fourier) + the dual-weight trace: open targets.
- **`λ_t` adjoint** — gated on the Lp/RCLike adjoint diamond.
No fake increment was forced and no frontier claimed prematurely.

## 5. Honest scope (unchanged, restated)
Multi-month, research-grade; M4 (Stone) and M5 (trace) and M3 (Williamson) are open Mathlib targets. Value lands
incrementally: M2 alone closes JLMS Stage 1; M5 alone gives finite regional entropy; M7 is the goal. The **`1/4`
coefficient / the value of `G` (species problem)** is the irreducible UV datum — derived nowhere, carried
honestly. Free scalar only; universality across species (contact terms) NOT claimed; mechanism, not micro-theory.

## 6. Sub-plan index
`STONE_THEOREM_PLAN.md` (M1–M2, M4) · `SAKHAROV_KG_PLAN.md` (Route A / M3) · `P4_WALL_CAMPAIGN_PLAN.md` (Route B /
M5) · `PHASE4_GENERATOR_PLAN.md` (the Stone hypothesis, ✅ checkpoint) · the GR chain capstone `qiqt_gr_freefield`
(M6–M7).
