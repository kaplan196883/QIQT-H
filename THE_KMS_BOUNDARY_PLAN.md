# THE KMS-BOUNDARY CAMPAIGN — the tower vacuum is a KMS-boundary state (closing the modular tower)

**Status:** COMPLETE (2026-07-05) — K1+K2 ALREADY EXISTED (flow campaign B4/B6, verified); C1 capstone landed. Axiom-free std-3, budget 0. **Loop:** fe280fa3. **Commits LOCAL ONLY** (session no-push).
**Consult:** fable high-reasoning agent abec4770106bf5f53 (2026-07-05) — verdict: (K) is a
short closing campaign (K1 + K2 + C1), THEN the tower's tractable modular theory is COMPLETE
and the honest move is a PIVOT off the tower. Do NOT open (R) — the RvD commutant wall.

## Binding verdict

Earned: the ALGEBRAIC / boundary β-KMS identity ω(π(x)π(y)) = ω(π(y)π(σ(x))) for the tower
vacuum ω against the FINITE modular automorphism σ = modAut(ρ_C) (= the imaginary-time
translate σ_{−iβ}). NOT earned: the Kubo–Martin–Schwinger STRIP-ANALYTICITY at the limit
(holomorphy of t ↦ ω(π(a)Δ^{it}π(b)Ω) on 0≤Im t≤β and its boundary identification), the
continuation σ_{−iβ} = analytic-continuation-of-Δ^{it} (modAut is imaginary-time-only;
cornerFlow is real-t-only); no full equality J M J = M′ (only the inclusion); no type.

## Deciding fact (verified)

`kms_condition` (FiniteModularTheory.lean:158): stateOf ρ (x*y) = stateOf ρ (y * modAut ρ x),
stateOf ρ a = trace(ρ*a), modAut ρ x = ρ*x*⅟ρ. Specialized: `gibbs_kms_condition`
(Dynamics.lean:369) at the Gibbs density. Transports cleanly: towerRep is ⋆ₐ-hom (map_mul),
towerRep_inner_cyclicVec (CyclicVector.lean:62) = ⟪Ω,π(a)Ω⟫ = stateOf ρ a, gibbsInvertible
live. The K1 proof is TowerNonTrace.lean's body with gibbs_kms_condition in the final exact.

## The increments

- [x] **K1 — ALREADY EXISTED as `towerState_kms_boundary` (Flow.lean:179, B4 capstone) ✅** — the discipline check found it already built + pinned; verified axiom-clean std-3. No new work.
  ~~KMSBoundary.lean~~:
  `towerVacuum_kms_boundary (C) (x y : DiamondAlg L C) : ⟪Ω, π_C(x)(π_C(y)Ω)⟫ =
  ⟪Ω, π_C(y)(π_C(modAut (gibbsDensity L C ω β) x) Ω)⟫`. Route: ← ContinuousLinearMap.mul_apply
  ×2, ← map_mul (towerRep) ×2, towerRep_inner_cyclicVec ×2, exact gibbs_kms_condition.
- [x] **K2 — ALREADY EXISTED as `towerFlow_vectorState` (Flow.lean, B6, general-T form) ✅** — verified axiom-clean std-3. No new work.
  ~~real-flow corollary~~:
  `towerVacuum_flow_invariant (C) (t) (a) : ⟪Ω, π_C(cornerFlow C t a)Ω⟫ = ⟪Ω, π_C(a)Ω⟫`.
  Route: towerFlow_conj_towerRep (π(σ_t a) = U_t π(a) U_{−t}) + towerFlow_cyclicVec ×2
  (U_{−t}Ω = Ω) + adjoint_inner_left. The honest real-flow companion to K1.
- [x] **C1 — `QIQTH/NonTracial/ModularDataComplete.lean`: the capstone checkpoint** ✅ DONE
  (packaging, no new math, risk NIL): a docstring bundling the full tower modular data
  (S̄, Δ, Δ†=Δ, Δ^{it}=towerFlow, Tomita I, J, polar-on-core, Tomita II inclusion,
  non-traciality, KMS-boundary) into one paper-ready HAVE/HAVE-NOT theorem-list; a trivial
  marker theorem; AxiomAudit note; plan → COMPLETE. THEN report: the tower is exhausted,
  pivot required (user decision: free-field sector vs the Δc² physics test).

## The checkpoint language (C1, verbatim)

HAVE: "The tower vacuum state ω (the vector state of the cyclic-separating Ω) satisfies the
algebraic KMS boundary identity ω(π_C(x)π_C(y)) = ω(π_C(y)π_C(σ(x))) at every finite stage
C, where σ = modAut(ρ_C) is the finite modular automorphism (conjugation by the Gibbs
density ρ_C = the imaginary-time modular translate σ_{−iβ}). Combined with the already-proved
real modular flow Δ^{it}=towerFlow, its exact covariance U_t π_C(a) U_{−t} = π_C(σ_t a), its
fixing of Ω, and its state invariance, the tower vacuum is a KMS-boundary state for its
modular automorphism. Axiom-free, std-3. With this, the tower limit state carries the COMPLETE
machine-checked Tomita–Takesaki modular data: S̄ (closed involutive Tomita operator), Δ
self-adjoint (Δ†=Δ, von Neumann's theorem), Δ^{it}=towerFlow (the physical flow, the
identification), Tomita I (Δ^{it}MΔ^{−it}=M), J anti-unitary with polar decomposition on the
core, Tomita II inclusion (JMJ ⊆ M′), non-traciality (ω not a trace, Δ≠1), and the
KMS-boundary identity — the first complete Tomita–Takesaki modular theory in any proof
assistant."

HAVE-NOT: "This is the algebraic/boundary KMS relation w.r.t. the modular AUTOMORPHISM, NOT
the Kubo–Martin–Schwinger strip-analyticity at the thermodynamic limit: the holomorphy of
t ↦ ω(π(a)Δ^{it}π(b)Ω) on 0≤Im t≤β and the identification of its boundary with the
imaginary-time endpoint are not formalized, and σ_{−iβ} = (analytic continuation of Δ^{it})
is not proved. No full commutant equality J M J = M′ (only the inclusion J M J ⊆ M′, the
reverse being the Rieffel–van Daele wall); no type classification (III₁/Connes invariant —
Mathlib has no tracial-state/type API); everything remains the finite-stage Gibbs
inductive-limit state — the free-field / Type-III continuum objects are untouched, and are
the named pivot."

## Per-increment discipline

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit
on main with the Co-Authored-By: Claude Opus 4.8 trailer; **LOCAL ONLY — no push until the
user says so**; update this checklist + Progress log AND LEAN_RESULTS_INVENTORY.md; NO sorry;
NEVER claim strip-KMS, a type, or J M J = M′ equality; explicit git paths only (Lean + plan
+ inventory + audit — NEVER the stray website edits in the tree); check sibling jobs first.

## Progress log

- **2026-07-05** — Scoped (consult: K1 5-line transport of gibbs_kms_condition, K2 real-flow
  corollary, C1 capstone; then PIVOT — the tower is exhausted, (R) is the RvD wall). THE
  NON-TRACIALITY campaign closed immediately prior.

- **2026-07-05** — **CAMPAIGN COMPLETE.** The discipline check ("verify what exists before
  claiming an increment") found K1 = `towerState_kms_boundary` and K2 = `towerFlow_vectorState`
  ALREADY BUILT and pinned during the flow campaign (B4/B6) — both verified axiom-clean std-3,
  no re-work. C1 landed: ModularDataComplete.lean — `modular_data_complete_witness`, a
  compile-verified bundle deriving KMS-boundary + non-traciality + Δ≠1 from the one datum
  w_n ≠ w_m, plus the full MODULAR DATA COMPLETE index + verbatim HAVE/HAVE-NOT docstring.
  **THE TOWER'S TRACTABLE TOMITA–TAKESAKI MODULAR THEORY IS NOW COMPLETE** (S̄, Δ, Δ†=Δ,
  Δ^{it}=flow, Tomita I, J, polar-on-core, Tomita II inclusion, non-traciality, KMS-boundary
  — the first such in any proof assistant). PIVOT REQUIRED: (R) full J M J = M′ is the RvD
  commutant wall; strip-KMS and type III are Mathlib-machinery walls; the honest high-value
  moves are the free-field-sector port or the Δc² physics test — a USER DECISION.
