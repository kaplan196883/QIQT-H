# Chart-parametric rebuild plan — full `uniformInverseChart` → `uniformInverseChart'` rebuild

Status: AUTHORIZED (user-commissioned 2026-08-24, overriding `gpt-5.6-sol`'s 30th/31st/32nd-consult
"do not grind, do not spike" recommendation with eyes open — see J4-1153/1154/1155). Dispatch 1 = J4-1156.
This file is the discoverable record of the plan so future dispatches do not re-derive it from scratch.

## Why this exists

`hWmeas` (raw joint measurability of `uniformInverseChart` in the field point) is decisively UNCLOSABLE
against the existing `Exists.choose`-built chart (J4-1145). A non-opaque replacement chart
`uniformInverseChart'` already exists (J4-1147–1149, `ThetaMeasurableEmbedding.lean` /
`ThetaChartContDiff.lean` / `ThetaChartGatedInstantiation.lean`) with DERIVED joint measurability and
`ContDiffAt ℝ 2` regularity, but it agrees with the old chart only on a bounded tube image, not globally
(J4-1150) — so it cannot discharge `hWmeas` for the LITERAL existing capstone theorems, which are
hardwired to the old chart in both their definitions and their conclusions. The only honest route is a
full chart-parametric rebuild of the witness-definition chain, ending in a genuinely FRESH primed
capstone (not a patch to the existing one).

## Root-definition inventory (confirmed by direct grep + read, J4-1153 + J4-1156)

Exactly TWO definitions call `uniformInverseChart g gi hC hK` DIRECTLY (not transitively):

1. **`chartFieldAmp`** (`QIQTH/NormalFormDischarge.lean:125-132`) — 3 literal inline calls; first-order
   algebraic (`radialCutoff`, `vanVleck^(-1/2)`, two `transportCoeff` terms), no derivatives inside its
   own body. NOT already chart-generic.
2. **`vanVleckGatedWitness`** (`QIQTH/ConvApproximants.lean:161-166`) — passes `uniformInverseChart g gi
   hC hK` as the `Vmap : Point n → Point n → Point n` argument of `globalCutoffParametrixWitnessN`
   (`OrderNResidual.lean:148-150`), which is ALREADY chart-generic (no `uniformInverseChart` reference in
   its own body at all) — genericizing this root is a one-argument threading, not a rebuild.

Everything else in the ~360-file transitive-reference count (`witnessFieldDeriv`, `witnessFieldDeriv2`,
`hDConv_gatedWitnessN1_epsFamily`, `HgateSatAudit`/`GatedRepSFix`/`HEmeasBorelAudit`, etc.) calls
`uniformInverseChart` only THROUGH these two roots — confirmed `gatedKernel`, `globalCutoffParametrixWitnessN`,
`radialCutoff`, `transportCoeff`, `heatParametrix` are all already chart-agnostic.

## Discipline (per `gpt-5.6-sol`'s 33rd consult, 2026-08-24, GO verdict)

At every root/derived definition `X`, build a THREE-LAYER API:
1. `XWith` — chart-generic, takes an abstract `W : Point n → Point n → Point n`.
2. the OLD `X` — left UNCHANGED (never edited).
3. `X'` — `XWith` instantiated at `uniformInverseChart' g gi hC hK c` (the new chart).

Plus a **compatibility bridge**: `XWith ... (uniformInverseChart g gi hC hK) = X ...`, ideally `rfl`
(pure unfolding — confirms genericization changed nothing about the existing banked definition).

**Never** attempt to prove `X' = X` globally (false in general — the two charts agree only on a bounded
tube image, per `uniformInverseChart'_eqOn_uniformInverseChart`). New files only; never edit existing
banked files (including `chartFieldAmp`/`vanVleckGatedWitness` themselves).

## Phased plan

### Phase 0 — Guardrails and live-cone inventory
- Task A: the compatibility discipline above (bridges only through the bounded-tube theorem; no global
  old↔new equality attempted anywhere).
- Task B: trace backward from `tripleHEmeas_concrete_v4`/`v5`, `gatedWitness_hEboundW_final_gen`,
  `gatedWitness_hEboundW_unconditional'`; classify every node as D (definition body mentions an old
  root), S (theorem statement mentions an old root), or P (proof mentions an old root, statement already
  generic). Fork/generalize only this LIVE CONE, not the full 360-file set.

### Phase 1 — Introduce the two generic roots and new-chart instances (Task A = `vanVleckGatedWitness`
first — it feeds the derivative chain and is cheaper since its callee is already chart-generic; Task B =
`chartFieldAmp` second). **LANDED — see J4-1156 below.**

### Phase 2 — Parameterize the computational witness/derivative spine
- Task A: fork `witnessFieldDeriv`, `witnessFieldDeriv2`, the epsilon-family definitions feeding
  `hDConv_gatedWitnessN1_epsFamily`, and anything built directly from them, via the same `XWith`/`X'`
  pattern threading the abstract chart through.
- Task B: at each existing theorem whose CONCLUSION names an old root, add a generic sibling whose
  conclusion names the `With` version; keep the old theorem as-is or as a thin wrapper.
- Task C: produce the first CLOSED new-chart diamond — one nontrivial theorem relating the new witness
  derivative to `chartFieldAmp'`/`chartFieldAmpWith`, the first genuine mathematical canary (not just
  definitional threading).

### Phase 3 — Rebuild the local analytic and derivative suppliers
- Task A: extract old-chart-specific facts used inside proofs into explicit hypotheses on an abstract
  `W` (matching the `huniformChart` shape where possible) rather than strengthening to global claims.
- Task B: instantiate those suppliers at `uniformInverseChart'` via `uniformInverseChart'_huniformChart`
  / `_contDiffAt` / `_eqOn_uniformInverseChart` (every use of the last one needs an explicit bounded-tube
  membership witness).
- Task C: rebuild the first/second witness-derivative theorem chain and the epsilon-family results
  purely in terms of primed/generic objects.

### Phase 4 — Rebuild the measurability/audit chain (HIGHEST RISK PHASE)
- Task A: genericize the EARLIEST `hWmeas`-consuming audit theorem (in the `HgateSatAudit` /
  `GatedRepSFix` / `HEmeasBorelAudit` import-order lineage — follow actual import order, not the name
  order) over an abstract `W` + `hWmeas : Measurable (fun w => W w.2.2 w.2.1)`.
- Task B: push genericity through each subsequent audit structure the same way; instantiate primed
  copies at `W := uniformInverseChart' g gi hC hK c`, discharging the generic `hWmeas` hypothesis via
  `uniformInverseChart'_joint_measurable`.
- Task C: land a primed measurability audit with NO `hWmeas` hypothesis remaining and no raw
  `uniformInverseChart` reference.

### Phase 5 — Generic concrete triple and summit connection
- Task A: a chart-parametric `tripleHEmeas_concrete_v4_gen` (generic `W`, generic hypotheses) — refactor
  the existing proof rather than reproduce it where practical.
- Task B: instantiate at the new chart → `tripleHEmeas_concrete_v4'`.
- Task C: feed the new triple into `gatedWitness_hEboundW_final_gen` → the primed unconditional summit,
  WITHOUT requiring global old/new witness identification.

### Phase 6 — Compatibility, cleanup, isolation check
- Task A: preserve all old APIs unchanged (wrappers where a generic proof replaces an old one).
- Task B: prove new-path isolation — grep audit confirming the primed chain references raw
  `uniformInverseChart` only inside compatibility-bridge lemmas, never inside the live primed proof path.
- Task C: final full build + `#print axioms` on every primed terminal theorem.

## Dispatch sizing (per 33rd Sol consult, revised down from the 30th/31st/32nd consults' 45-80+ estimate)

| Phase | Realistic dispatches |
|---|---:|
| Phase 0–1 (inventory, generic roots, bridges, primed roots) | 2–3 |
| Phase 2 (computational witness/derivative spine) | 4–7 |
| Phase 3 (local analytic and derivative suppliers) | 6–10 |
| Phase 4 (measurability/audit chain) | 8–14 |
| Phase 5 (generic concrete triple and summit) | 6–10 |
| Phase 6 (compatibility and final validation) | 3–5 |
| **Total** | **29–49** (optimistic 22–30, contingency tail 50–60) |

The main residual risk is downstream, not at the two roots: theorem CONCLUSIONS may hardcode old
definitions further down the chain, audit structures may bundle old concrete fields inseparably, the
extra tube-radius parameter `c` of `uniformInverseChart'` must propagate cleanly, and local derivative
proofs may lean on old-chart-specific lemmas not yet expressed in the abstract `huniformChart` shape.

## Named canary checkpoints — STOP AND RE-EVALUATE if any of these trip

- **C0 — RootBridge** (dispatch 1–2): `vanVleckGatedWitnessWith ... (uniformInverseChart ...) =
  vanVleckGatedWitness ...` and the `chartFieldAmp` analogue must close by `rfl` (or unfold+`simp` at
  worst). **PASSED, both `rfl`, this dispatch (J4-1156).** Failure would mean the root inventory is
  incomplete or one of the old definitions hides dependent proof data not visible in its apparent body —
  re-inventory immediately, do not proceed to Phase 2.
- **C1 — FirstDerivativeDiamond** (target dispatch 5–7): the first nontrivial theorem relating a primed
  witness derivative to `chartFieldAmp'`. STOP if instantiating at `uniformInverseChart'` turns out to
  need global chart reachability, global old/new equality, agreement outside the bounded tube, or global
  `ContDiff` where only local regularity is mathematically justified.
- **C2 — FirstHWMConsumerPrime** (target dispatch 10–12): the earliest `hWmeas`-consuming audit theorem
  instantiated with `uniformInverseChart'_joint_measurable`. STOP if the proof needs `hWmeas` for
  anything beyond raw measurability (e.g. a hidden global reachability/geometric fact), or needs
  identifying the new witness with the old witness outside the controlled tube.
- **C3 — PrimeHEmeasAudit** (target dispatch 16–20): a complete primed `HEmeasBorelAudit`-level result
  with no raw `hWmeas` hypothesis. STOP-and-resize (not necessarily abandon) if some bundled audit field
  is definitionally tied to the old concrete roots in a way that resists genericization without a
  structural redesign of the audit type itself. **PASSED, dispatch 15 (J4-1163/1164), AHEAD of the
  target window (16–20).** `TripleHEmeasConcreteV4GenWith.tripleHEmeas_concrete_v4'` — see the dispatch
  log entry below.
- **C4 — TripleHEPrime** (target dispatch 22–28): `tripleHEmeas_concrete_v4'`, concluding about the
  primed chain, built from `uniformInverseChart'_joint_measurable`. STOP if the proof can only close by
  invoking the OLD concrete theorem and then demanding global old/new witness equality.
- **C5 — SummitPrime** (target dispatch 30–40): successful application of `gatedWitness_hEboundW_final_gen`
  to the full primed package. STOP if the final theorem's type intrinsically forces the old witness
  rather than accepting an abstract witness satisfying the summit's hypotheses.

## Dispatch log against this plan

- **J4-1156** — Phase 1 LANDED. `QIQTH/ChartFieldAmpWith.lean`
  (`chartFieldAmpWith`, `chartFieldAmpWith_uniformInverseChart` [`rfl`], `chartFieldAmp'`) and
  `QIQTH/VanVleckGatedWitnessWith.lean` (`vanVleckGatedWitnessWith`,
  `vanVleckGatedWitnessWith_uniformInverseChart` [`rfl`], `vanVleckGatedWitness'`). Canary C0 PASSED.
  Next dispatch target: Phase 2 Task A — fork `witnessFieldDeriv`/`witnessFieldDeriv2` the same way,
  reading `EngineInstantiation.lean` in full first.
- **J4-1157 (this dispatch)** — Phase 2 Task A LANDED. `QIQTH/WitnessFieldDerivWith.lean`
  (`witnessFieldDerivWith`/`witnessFieldDeriv2With`, both `..._uniformInverseChart` bridges [`rfl`],
  `witnessFieldDeriv'`/`witnessFieldDeriv2'` at `uniformInverseChart'`) — threads through Phase 1's
  `vanVleckGatedWitnessWith`/`vanVleckGatedWitness'`. Both `rfl` bridges closed cleanly (layer-analogous
  to Canary C0, one step up the derivative chain) — NOT itself Canary C1 (that needs the first genuine
  diamond theorem to `chartFieldAmp'`, still ahead). Next dispatch target: Phase 2 Task B (generic
  siblings for the theorems whose conclusions name the old roots — `witnessFieldDeriv_gate_eq`,
  `witnessFieldDeriv_gate_abs_le`, etc.) and Task C (Canary C1 — `FirstDerivativeDiamond`).
- **J4-1158 (this dispatch)** — Phase 2 Task B LANDED (6 of the 7 `EngineInstantiation.lean` consumer
  theorems: `witnessFieldDeriv2_center`, `witnessFieldDeriv2_eq_pd_witnessFieldDeriv`,
  `witnessFieldDeriv_gate_eq`, `witnessFieldDeriv_offGate_eq_zero`, `witnessFieldDeriv2_offGate_eq_zero`,
  `witnessFieldDeriv_gate_abs_le` — genericized in `QIQTH/WitnessFieldDerivConsumersWith.lean`;
  `witness_secondOrder_interchange` deliberately NOT attempted, needs a `heatConvFrozenWith`, Phase 3/4
  territory). **CANARY C1 RESULT: PASS.** `witnessFieldDeriv'_gate_eq` — the first genuine relational
  theorem connecting a PRIMED witness derivative (`witnessFieldDeriv'`) to `chartFieldAmp'` — closed
  cleanly with NO extra machinery: no global chart reachability, no global old/new chart equality, no
  bounded-tube agreement argument, no global `ContDiff` beyond the caller-supplied local `hJetV`/`hAmp1`.
  Root cause of the clean pass: `gaussComp_hasDerivAt_line`/`gaussComp_pd` (`ChartJetHessian.lean`) and
  `gatedKernel_apply_of_mem`/`gatedKernel_apply_of_notMem` (`GlobalHunifAssembly.lean`) — the two
  ingredients the old `witnessFieldDeriv_gate_eq` proof leans on — were ALREADY stated over an abstract
  chart map / already chart-independent, so the generic proof is a mechanical `W`-for-`uniformInverseChart`
  substitution of the old proof, verbatim. Also landed the on-gate domination corollary
  `witnessFieldDeriv'_gate_abs_le`. Note on Task B's true scope: a broad `grep witnessFieldDeriv` across
  all of `QIQTH/` hits ~224 files, but nearly all are downstream consumers of the 7 root theorems, not
  direct-signature consumers — genericizing that whole downstream tower was correctly read as OUT of
  Task B's scope (matches J4-1157's own worked examples, all in `EngineInstantiation.lean`) and was not
  attempted. Next dispatch target: `heatConvFrozenWith` + generic `witness_secondOrder_interchange`
  sibling (closes Task B fully), or proceed to Canary C2 per the phase table.
- **J4-1159 (Phase 3, opening dispatch)** -- `QIQTH/WitnessSecondOrderInterchangeWith.lean`
  (`witness_secondOrder_interchangeWith`/`witness_secondOrder_interchange'`) closes the Phase 2 Task B
  item J4-1158 deferred. CORRECTION of J4-1158's forward note: no `heatConvFrozenWith` was needed --
  `heatConvFrozen`/`pd_pd_heatConvFrozen_interchange` were ALREADY fully chart-generic (arbitrary
  `A/H,dH,dHH,F : ℝ → Point n → Point n → ℝ`, no chart call in their own bodies); the chart-hardwiring
  lived entirely in the concrete arguments fed in, already genericized in J4-1156/1157/1158. Pure
  mechanical substitution, mirroring the old proof exactly. Both theorems std-3, full build 0 err.
  Commit `a492ca21`. Next dispatch target: Canary **C2 -- FirstHWMConsumerPrime** -- the earliest
  `hWmeas`-consuming audit theorem (`HgateSatAudit`/`GatedRepSFix`/`HEmeasBorelAudit` import-order
  lineage) instantiated with `uniformInverseChart'_joint_measurable`.
- **J4-1160 (Phase 4, opening dispatch)** -- `QIQTH/GatedTauRepProdSWith.lean`. **CANARY C2 RESULT:
  PASS.** Identified the earliest `hWmeas`-shaped consumer as `HgateSatAudit.gatedTauRepProdS_measurable`
  (`HgateSatAudit.lean:263`, upstream of `GatedRepSFix.lean`/`HEmeasBorelAudit.lean` per actual import
  lines) -- its `hChartMeas : Measurable (fun w => uniformInverseChart g gi hC hK w.2.2 w.2.1)` hypothesis
  matches `uniformInverseChart'_joint_measurable`'s conclusion shape EXACTLY (same `w.2.2`/`w.2.1` order,
  same ambient type; the extra tube-radius `c` is just a fixed partial application, no currying/
  sigma-algebra mismatch). Re-inspection of the proof confirmed `hChartMeas` is used ONLY for raw
  measurability composition, never a hidden geometric fact, never old/new witness identification outside
  the tube -- so the crux check (canary condition) is clean. Landed `gatedTauRepProdSWith`/
  `gatedTauRepProdSWith_uniformInverseChart` (`rfl` bridge)/`gatedTauRepProdS'` (three-layer discipline
  for the def), `gatedTauRepProdSWith_measurable` (Task A: generic over `W`+`hWmeas`), and
  `gatedTauRepProdS'_measurable` (Task B: the canary deliverable, `hWmeas` fully discharged via
  `uniformInverseChart'_joint_measurable`, existential-`δ₀` shape preserved). Deliberately did NOT
  genericize `witnessTauDeriv_eq_gatedTauRepProdS`/`tauDeriv_prod_stronglyMeasurable_v4` (they consume
  `hgate`/`HasDerivAt` data about `chartFieldAmp`, not raw chart measurability -- next dispatch) or touch
  `GatedRepSFix.lean`/`HEmeasBorelAudit.lean`. std-3, full build 0 err, axiom budget 0. Commit `9f926dfe`.
  Next dispatch target: Phase 4 Task B continuation (the `hcar`-bundled siblings above), then push into
  `GatedRepSFix.lean`'s field/field² carriers toward Canary C3.
- **J4-1161 (this dispatch)** — Phase 4 Task B continuation. `QIQTH/WitnessTauDerivEqWith.lean`
  genericizes `HgateSatAudit.witnessTauDeriv_eq_gatedTauRepProdS` and
  `.tauDeriv_prod_stronglyMeasurable_v4` (the `hcar`-bundled siblings flagged as the next target above).
  **OBSTRUCTION FOUND AND ROUTED AROUND** (genuine, not routine): J4-1160's `gatedTauRepProdSWith` turned
  out to be only PARTIALLY chart-generic — its amplitude term calls the hardwired `chartFieldAmp` (OLD
  chart), not `chartFieldAmpWith … W` — harmless for J4-1160's pure-measurability goal but FATAL for a
  genuine derivative-identity theorem at abstract `W` (the product-rule identity needs the amplitude
  VALUE to match the same chart as the Gaussian argument; provably false for `W ≠` the old chart).
  Resolution: built a NEW, fully chart-generic representative `gatedTauRepProdSGenWith` in the new file
  (coincides with `gatedTauRepProdSWith`/`gatedTauRepProdS` on the old chart by `rfl`;
  `GatedTauRepProdSWith.lean` left completely untouched, matching the "never edit existing files"
  discipline). Lands the generic + primed τ-derivative identity
  (`witnessTauDeriv_eq_gatedTauRepProdSWith`/`_recovers_old`/`_'`) and the generic + primed
  strongly-measurable capstone (`tauDeriv_prod_stronglyMeasurable_v4With`/`_'`), the latter with chart
  joint-measurability fully discharged via `uniformInverseChart'_joint_measurable` — no free
  `hWmeas`/chart-measurability hypothesis remains (the genuinely amplitude-analytic `hAmpMeas`/`hgate`
  hypotheses about `chartFieldAmp'` correctly remain as caller-supplied inputs). **CANARY C3 ASSESSMENT:
  this is a STEP TOWARD C3, NOT C3 itself** — it is `HgateSatAudit`-level and τ-carrier-only, not
  `HEmeasBorelAudit`-level, and the field/field² carriers (§3 of `HgateSatAudit.lean`, prose-only, never
  even formalized for the old chart) remain untouched; `GatedRepSFix.lean`/`HEmeasBorelAudit.lean` not
  touched. std-3, full build 0 err (built clean on first attempt), axiom budget 0. Commit `87ffbc47`.
  Next dispatch target: (a) formalize the field/field² carrier honest fix (the §3 prose surgery, never
  done even for the old chart, needed before it can be genericized) or (b) push directly into
  `GatedRepSFix.lean`/`HEmeasBorelAudit.lean` if a τ-only entry point exists there.
- **J4-1162 (this dispatch)** — Phase 4 Task B continuation. `QIQTH/GatedFieldRepSGenWith.lean`.
  **STALE-PREMISE CORRECTION of J4-1161's forward note (a):** direct full read of `GatedRepSFix.lean`
  (J4-232, POSTDATES `HgateSatAudit.lean` J4-231) shows the field/field² v4 honest-fix carriers were
  ALREADY FULLY FORMALIZED for the OLD chart (§A/§B/§C, culminating in an `HEmeasBorelAudit`-level
  `tripleHEmeas_concrete_v4`) — `HgateSatAudit.lean` §3 is simply an out-of-date prose sketch relative
  to the later file. So path (a) was MOOT and path (b) reduces to "genericize `GatedRepSFix.lean`'s
  already-proven §A/§B/§C content the same way the τ carrier was genericized" — no new field/field²
  math needed. This dispatch genericizes §A (the FIRST field-`pd` carrier) only, in a NEW file, building
  its OWN fully chart-generic representative `gatedDerivRepProdSGenWith` (amplitude via
  `chartFieldAmpWith … W`, following J4-1161's own precedent for why the hardwired `chartFieldAmp` won't
  do). Lands the generic + primed field-derivative everywhere identity
  (`witnessFieldDerivWith_eq_gatedDerivRepProdSWith`/`_recovers_old`/`witnessFieldDeriv_eq_gatedDerivRepProdS'`)
  and the generic + primed strongly-measurable capstone
  (`firstFieldPd_prod_stronglyMeasurable_v4With`/`_v4'`, `hWmeas` fully discharged for the primed one).
  `GatedRepSFix.lean` left completely untouched. 2 of 3 `HEmeasBorelAudit` conjuncts (τ, first field-`pd`)
  now chart-generic + primed. **Canary C3 NOT YET REACHED** — §B (mixed second field-`pd`) and §C (triple
  assembly) remain un-genericized; assembling the primed triple once all three conjuncts are done IS
  Canary C3. std-3, full build 10429 jobs 0 err, axiom budget 0. Commit `1ddf8934`. Next dispatch target:
  genericize `GatedRepSFix.lean` §B the identical way, then assemble the primed triple (Canary C3).

- **J4-1163/1164 (dispatch 15)** — `QIQTH/GatedMixed2RepSGenWith.lean` genericizes `GatedRepSFix` §B
  (the mixed second field-`pd` v4 carrier, conjunct (3)) over an abstract chart `W`, including a missing
  prerequisite (`witnessMixedWith_gate_eq`/`_offGate_eq_zero`/`_eq_zero_of_nonpos`, a mechanical
  substitution off `ChartJetHessianMixed`'s already-generic `gaussComp_pd_pd_mixed`/
  `gaussComp_amp_pd_pd_mixed`) that had not existed before this dispatch (unlike the diagonal case,
  whose analogous prerequisite J4-1158 had already built). Built clean first attempt — no obstruction.
  Then `QIQTH/TripleHEmeasConcreteV4GenWith.lean` assembles all three now-primed conjuncts
  (`tauDeriv_prod_stronglyMeasurable_v4With` J4-1161, `firstFieldPd_prod_stronglyMeasurable_v4With`
  J4-1162, `secondFieldPd_prod_stronglyMeasurable_v4With` this dispatch) plus `hgi`/`hchr` into
  `tripleHEmeas_concrete_v4'` via `HEmeasBorelAudit.tripleHEmeas_of_surface`, sharing a SINGLE
  `uniformInverseChart'_joint_measurable`-derived `hWmeas` across all three (avoiding any cross-`δ₀`
  reconciliation). **CANARY C3 RESULT: PASS** — a complete primed `HEmeasBorelAudit`-level triple with
  no raw `hWmeas` hypothesis, reached at dispatch 15 (ahead of the target window 16–20). Both files
  std-3, full build 10428/10431 jobs 0 err, axiom budget 0. Commit `470e19bf`. Next dispatch target:
  Phase 5 — feed `tripleHEmeas_concrete_v4'` into `gatedWitness_hEboundW_final_gen` (or its analogue)
  toward the primed unconditional summit (Canary C4/C5 territory).

`a₁=R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁=R/6`.
