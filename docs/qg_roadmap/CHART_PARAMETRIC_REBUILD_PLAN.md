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
  structural redesign of the audit type itself.
- **C4 — TripleHEPrime** (target dispatch 22–28): `tripleHEmeas_concrete_v4'`, concluding about the
  primed chain, built from `uniformInverseChart'_joint_measurable`. STOP if the proof can only close by
  invoking the OLD concrete theorem and then demanding global old/new witness equality.
- **C5 — SummitPrime** (target dispatch 30–40): successful application of `gatedWitness_hEboundW_final_gen`
  to the full primed package. STOP if the final theorem's type intrinsically forces the old witness
  rather than accepting an abstract witness satisfying the summit's hypotheses.

## Dispatch log against this plan

- **J4-1156 (this dispatch)** — Phase 1 LANDED. `QIQTH/ChartFieldAmpWith.lean`
  (`chartFieldAmpWith`, `chartFieldAmpWith_uniformInverseChart` [`rfl`], `chartFieldAmp'`) and
  `QIQTH/VanVleckGatedWitnessWith.lean` (`vanVleckGatedWitnessWith`,
  `vanVleckGatedWitnessWith_uniformInverseChart` [`rfl`], `vanVleckGatedWitness'`). Canary C0 PASSED.
  Next dispatch target: Phase 2 Task A — fork `witnessFieldDeriv`/`witnessFieldDeriv2` the same way,
  reading `EngineInstantiation.lean` in full first.

`a₁=R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁=R/6`.
