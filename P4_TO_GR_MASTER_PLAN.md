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
- [~] **M1** — unbounded FC `∫ f dE` on a PVM (`QIQTH/Spectral/UnboundedFC.lean`). **Domain ✅** (the
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
  (`boundedFC_adjoint`: `(boundedFC g)† = boundedFC(conj∘g)` — the bounded FC is a `*`-hom). NEXT: assemble the
  norm identity `‖boundedFC g x‖²=∫|g|²dμ_x` (= adjoint + `boundedFC_mul` + the diagonal `bilinDiag g x x =
  ∫g dμ_x`) ⟹ `boundedFC(fₙ)x` Cauchy ⟹ the limit operator `fcLinear` + symmetry; then `∫g dE = boundedFC g`.
- [ ] **M2** — `K` operator + `Δ^{it}=e^{−itK}` (JLMS Stage 1 closed)
- [ ] **M3** — Williamson `N`-mode area-scaling (frontier; small-`N` first)
- [ ] **M4** — general Stone → `X = A_edge` (frontier)
- [ ] **M5** — dual-weight trace + JLMS + FQ bound
- [ ] **M6** — Gap-2 localization map
- [ ] **M7** — fusion: `P4 → GR` closed for the free field (UV datum carried)

## 5. Honest scope (unchanged, restated)
Multi-month, research-grade; M4 (Stone) and M5 (trace) and M3 (Williamson) are open Mathlib targets. Value lands
incrementally: M2 alone closes JLMS Stage 1; M5 alone gives finite regional entropy; M7 is the goal. The **`1/4`
coefficient / the value of `G` (species problem)** is the irreducible UV datum — derived nowhere, carried
honestly. Free scalar only; universality across species (contact terms) NOT claimed; mechanism, not micro-theory.

## 6. Sub-plan index
`STONE_THEOREM_PLAN.md` (M1–M2, M4) · `SAKHAROV_KG_PLAN.md` (Route A / M3) · `P4_WALL_CAMPAIGN_PLAN.md` (Route B /
M5) · `PHASE4_GENERATOR_PLAN.md` (the Stone hypothesis, ✅ checkpoint) · the GR chain capstone `qiqt_gr_freefield`
(M6–M7).
