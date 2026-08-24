# Witness-unification plan — connecting `tripleHEmeas_concrete_v4'` (Campaign 1) to
# `a1_R6_assembled_v3` (Campaign 2) by rebuilding the capstone against `vanVleckGatedWitness'`

Status: SCOPED (J4-1176), Phase 0 (D0) now FULLY CLOSED as of J4-1177 (grand-assembly proof-body audit
+ N=1-package chart-independence re-verification both complete, zero new fork points found).
**NOT AUTHORIZED FOR FULL CONSTRUCTION (D2 onward)** — and per J4-1177's full-repo consumer search
(NONE of the four capstone-tower theorems, root through `a1_R6_assembled_v3`, has any consumer
anywhere outside the tower's own internal plumbing) plus the 41st Sol consult's unsoftened verdict,
witness-unification is currently judged the WRONG next target entirely, not merely premature — see the
dispatch log below for Sol's recommended reallocation (creating a real consumer first), which is
itself NOT authorized by this file and requires explicit follow-up. This file is the discoverable
record so future dispatches do not re-derive it from scratch — mirrors the format of
`CHART_PARAMETRIC_REBUILD_PLAN.md` / `CAPSTONE_SIGNATURE_REDESIGN_PLAN.md`.

## Why this exists

This session landed two large, independently-successful, but ultimately DISCONNECTED sub-campaigns:

1. **Chart-parametric rebuild** (J4-1156–1166): forked the WITNESS-DEFINITION CHAIN
   (`chartFieldAmp`/`vanVleckGatedWitness`/`witnessFieldDeriv`/`witnessFieldDeriv2`/the τ- and
   field-`pd`/mixed-field-`pd` measurability carriers) into a three-layer `XWith`/`X`/`X'` discipline,
   culminating in `TripleHEmeasConcreteV4GenWith.tripleHEmeas_concrete_v4'` — a complete primed
   `HEmeasBorelAudit`-level measurability triple for `vanVleckGatedWitness'` (built on the new,
   genuinely jointly-measurable chart `uniformInverseChart'`), with NO raw `hWmeas` hypothesis
   remaining.
2. **Capstone-signature redesign** (J4-1168–1174): separately rebuilt the LIVE capstone
   `RightInverseGeneral.a1_R6_assembled_v2'` to accept a `(0,t]`-LOCAL affine-in-ceiling bound (sourced
   from the N=1 residual-discharge package `GateOpennessExport.gatedWitnessN1_package_open`) instead of
   a global `∀τ>0` bound, culminating in `CapstoneExistentialAssembly.a1_R6_assembled_v3` — but built
   verbatim against the OLD, UNPRIMED witness `vanVleckGatedWitness` throughout (mirroring
   `a1_R6_assembled_v2'` exactly), because that campaign never touched the chart layer.

J4-1175 found these do NOT connect: `tripleHEmeas_concrete_v4'`'s conclusion is about
`vanVleckGatedWitness'` (primed), while `a1_R6_assembled_v3`'s `htriple` hypothesis needs
`HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b)` (unprimed) — a genuine
type mismatch (different functions, different arity — the extra chart-radius parameter `c` — not
globally equal, only tube-agreement per `uniformInverseChart'_eqOn_uniformInverseChart`), not a proof
gap. The 39th Sol consult (J4-1175) sized the genuine fix — rebuilding the ENTIRE ~50-hypothesis
apparatus of `a1_R6_assembled_local`/`a1_R6_assembled_v3` to be about `vanVleckGatedWitness'`
throughout — at "10–30+ dispatches," a fresh sub-campaign at least comparable in size to either
completed campaign.

## Pre-check: does Campaign 1's `With`/primed infrastructure already cover the ~50 other hypotheses?

Direct grep/read (this dispatch, BEFORE the 40th Sol consult, to give Sol accurate ground truth rather
than assumed reuse) of every non-witness-chain data structure/definition the ~50 hypotheses of
`a1_R6_assembled_local`/`a1_R6_assembled_v3` depend on:

| Symbol | File | Chart/witness-hardwired in its OWN field types? | Verdict |
|---|---|---|---|
| `CConvMetricData` | `CConvFacade.lean:76` | NO — generic over `g gi` only | reusable as-is |
| `CConvSourceData` | `CConvFacade.lean:118` | NO — generic over an abstract `F : ℝ → Point n → ℝ` | reusable as-is (witness only enters via what `F` is instantiated to at the call site) |
| `CConvChartGateData` | `CConvFacade.lean:85` | **YES** — `hVmapMeas`/`hCover` call `uniformInverseChart g gi hC hK` directly | needs its own `With`/`'` fork |
| `CConvDerivativeData` | `CConvFacade.lean:130` | **YES** — `hDmeas`/`hDrep` call `witnessFieldDeriv` directly | needs re-derivation, but the ingredient `witnessFieldDeriv'` (J4-1157) already exists |
| `CConvEnvelopeData` | `CConvFacade.lean:150` | **YES** — `hC2fam`/`hGateData` call `vanVleckGatedWitness`/`uniformInverseChart`/`chartFieldAmp` directly | needs its own `With`/`'` fork, but `chartFieldAmp'` (J4-1156) already exists as an ingredient |
| `TruncatedDuhamelCore` | `TruncatedDuhamelData.lean:92` | **NO** — generic over an abstract `Wit : ℝ → Point n → Point n → ℝ` | reusable as-is |
| `EndpointData` | `TruncatedDuhamelData.lean:114` | **NO** — generic over abstract `Wit` | reusable as-is (already used exactly this way by Campaign 2's `CT`/`hEbound_t` redesign) |
| `InterchangeData` | `TruncatedDuhamelData.lean:125` | **NO** — generic over abstract `Wit` | reusable as-is |
| `MemInterchange`/`MemLapFull`/`MemAdjLo`/`MemAdjHi`/`MemECombine` | `DaLimLUWallRecon.lean:93-141` | **NO** — all five are `abbrev`s generic over abstract `H F : ℝ → Point n → Point n → ℝ` (and `g gi` for `MemLapFull`) | reusable as-is |
| `GrandAssemblyRecon.a1_R6_assembled` (the theorem `a1_R6_assembled_local`'s proof body ultimately calls) | `GrandAssemblyRecon.lean:212` | **YES at the theorem-shell level** — every hypothesis/conclusion slot literally applies `vanVleckGatedWitness g gi hChr hK S a b`, even though the DATA STRUCTURES it consumes (`EndpointData`/`TruncatedDuhamelCore`/`InterchangeData`/`CConv*Data`) are themselves generic in `Wit` | needs its own mechanical `With`/`'`-shaped copy (a shallow, Campaign-2-Layer-A-style shell fork, NOT a structural rebuild, since every ingredient it calls is either already generic or already forked) |

**Bottom line of the pre-check.** 6 of 10 audited symbols (`CConvMetricData`, `CConvSourceData`,
`TruncatedDuhamelCore`, `EndpointData`, `InterchangeData`, all five `Mem*` abbrevs) are ALREADY fully
generic and need ZERO forking — a substantially more favorable picture than the 39th consult's
unaudited "10–30+" estimate implicitly assumed. Only `CConvChartGateData`, `CConvDerivativeData`,
`CConvEnvelopeData`, and the `GrandAssemblyRecon.a1_R6_assembled` theorem shell itself need new
`With`/`'` forks — and three of those four already have their hardest ingredient
(`witnessFieldDeriv'`/`chartFieldAmp'`) pre-built by Campaign 1.

## 40th Sol consult (`gpt-5.6-sol`, high effort, 2026-08-25) — verdict given this pre-check

Given the audit table above (which Sol did NOT have at the time of the 39th consult), Sol's revised
estimate:

| Audit result at the remaining unchecked layers (this plan's Phase 0, D0) | Likely total dispatches |
|---|---:|
| Remaining layers generic or shallowly hardwired (this pre-check's actual finding, confirmed) | **9–18, mode 11–13** |
| Several additional hardwired bundles found beyond the known 4 | 14–22 |
| `GrandAssemblyRecon.a1_R6_assembled` has no usable generic seam at all (ruled out by this pre-check — its data-structure ingredients ARE generic) | 20–30+ (not applicable per this pre-check) |

Sol's explicit, unsoftened verdict on whether to proceed: **do NOT launch the full rebuild (Phases
1–5 below) right now.** There is still no named downstream consumer for `a1_R6_assembled_v3` (old OR
primed) — Campaign 2's own Phase 6 was withheld for the identical reason. Spending 9–18 dispatches
producing a second, still-unconsumed ~65-hypothesis capstone is speculative API duplication. Sol's
recommendation: run Phase 0 (the dependency-closure audit below, D0/D1) to completion, freeze the
result, and resume only when a named theorem actually requires `a1_R6_assembled_v3'` fed by
`tripleHEmeas_concrete_v4'` — or when "Campaigns 1 and 2 must connect" is itself declared an explicit
release criterion by the user.

## Campaign invariant (Sol, verbatim, adopted)

Every new public declaration in this campaign must satisfy:
- All witness-dependent hypotheses use `vanVleckGatedWitness'`; all field derivatives use the
  corresponding primed wrappers; all chart-dependent data use `uniformInverseChart'`; all
  amplitude-dependent data use `chartFieldAmp'`/`With`. `c` threaded consistently as an independent
  chart parameter (NOT packed into the N=1 package's existential `(a,b,S,C)` — the two are orthogonal).
- No proof uses global equality between the primed and unprimed witnesses (tube-`EqOn` is not a
  substitute for a congruence/localization theorem — J4-1175's own finding).
- No existing banked file is edited. New files only. No `sorry`/`admit`/new axiom/forced hypothesis.
- Generic structures (`CConvMetricData`, `CConvSourceData`, `TruncatedDuhamelCore`, `EndpointData`,
  `InterchangeData`, `Mem*`) are REUSED as-is at `Wit := vanVleckGatedWitness' ...`, never cloned.
- The final canary must literally contain an application of `tripleHEmeas_concrete_v4'` in the
  `htriple` slot — types "looking compatible" is not sufficient.

## Phased plan (Sol's, adapted to this repo's file-naming convention)

### Phase 0 — Dependency-closure audit and compiling signature skeleton (Canary C0)
- **D0 — DependencyClosureAudit.** THIS DISPATCH's pre-check table above already covers `CConvMetricData`,
  `CConvSourceData`, `CConvChartGateData`, `CConvDerivativeData`, `CConvEnvelopeData`,
  `TruncatedDuhamelCore`, `EndpointData`, `InterchangeData`, `Mem*` (all five), and
  `GrandAssemblyRecon.a1_R6_assembled`'s theorem shell. Remaining for a follow-up dispatch before D0 is
  fully closed: inspect `GrandAssemblyRecon.a1_R6_assembled`'s actual PROOF BODY (not just its
  signature) for old-witness-specific HELPER theorem calls beneath the data-structure layer (Sol's
  caution: "if its proof invokes old-witness-specific helper theorems, those helpers become the real
  fork points — restating hypothesis TYPES is cheap, reusing the theorem that CONSUMES them may not
  be"); and the N=1 residual package (`gatedWitnessN1_package_open`) for any hidden old-chart
  indexing (expected clean, since it only produces `(a,b,C,S,hbound,hmemS0,hopenS0)`, none
  chart/witness-shaped, but not yet directly re-verified against this specific question).
- **D1 — SignatureSkeleton.** A compiling `#check`/`example`-only skeleton (in a NEW audit file)
  confirming: the exact result type of `tripleHEmeas_concrete_v4'`; the intended `htriple` type for a
  primed `a1_R6_assembled_local'`; that these are definitionally the same shape modulo the `c` chart
  parameter; and a complete classification ledger for all ~50 hypotheses (unchanged / generic-at-`Wit
  := vanVleckGatedWitness'` / needs-new-primed-structure / literal-proposition-substitution /
  unresolved). **C0 gate: no unresolved entries.**

### Phase 1 — Primed CConv facade (Canary C1)
- **D2 — `CConvChartGateDataWith`/`'`.** Fork the 2 hardwired fields (`hVmapMeas`, `hCover`) over an
  abstract chart, reusing Campaign 1's shared `uniformInverseChart'_joint_measurable` ingredient (avoid
  re-deriving 3 separate `δ₀`s, mirroring `TripleHEmeasConcreteV4GenWith`'s own shared-`δ₀` discipline).
- **D3 — `CConvDerivativeDataWith`/`'`.** Fork only `hDmeas`/`hDrep` (the fields naming
  `witnessFieldDeriv`), instantiating `witnessFieldDeriv'` (already banked, J4-1157).
- **D4 — `CConvEnvelopeDataWith`/`'`.** Fork `hC2fam`/`hGateData` (naming `vanVleckGatedWitness`/
  `uniformInverseChart`/`chartFieldAmp` directly), instantiating `chartFieldAmp'` (already banked,
  J4-1156) and the D2 chart-gate fork. **C1 gate:** all three new data families compile; a negative
  grep-scan of their printed types finds no unprimed witness/chart/amplitude token.

### Phase 2 — Mid-stack structures, real consumer check (Canary C2)
- **D5 — one real application** of `TruncatedDuhamelCore`/`EndpointData`/`InterchangeData` at
  `Wit := vanVleckGatedWitness' ...` (expected trivial reuse per the pre-check — these are already
  fully generic — this dispatch's job is to CONFIRM that expectation with an actual compiling
  application, not just structural definition, and to verify `CT`/`hEbound_t` (Campaign 2's own local
  bound machinery) carries no hidden old-witness index).
- **D6 — `Mem*` reuse confirmation.** Same for all five `Mem*` abbrevs at `H := heatOp g gi
  (vanVleckGatedWitness' ...)`, `F := leviSeries (heatOp g gi (vanVleckGatedWitness' ...))`. **C2
  gate:** all six compile as direct reuse (expected outcome per the pre-check) with zero new forks
  needed at this layer.

### Phase 3 — Primed grand assembly (Canary C3)
- **D7 — `GrandAssemblyReconPrimed.a1_R6_assembled'`.** A new theorem, literal copy of
  `GrandAssemblyRecon.a1_R6_assembled`'s signature with `vanVleckGatedWitness g gi hChr hK S a b`
  replaced by `vanVleckGatedWitness' g gi hChr hK S a b c` throughout, `CConvChartGateData`/
  `CConvDerivativeData`/`CConvEnvelopeData` replaced by their D2-D4 primed forks, everything else
  (`CConvMetricData`, `CConvSourceData`, `EndpointData`, `TruncatedDuhamelCore`, `InterchangeData`,
  `Mem*`) reused unchanged. Proof adapted through the SAME generic lower-level lemmas the old proof
  uses (per the pre-check, none of those lemmas are chart/witness-hardwired below the structure layer
  — to be confirmed by actually building this, not assumed). **STOP condition:** if the proof needs a
  helper lemma D0 didn't already flag as generic, re-audit before proceeding — do not force a
  work-around mid-proof.

### Phase 4 — Capstone reconstruction (Canary C4)
- **D8 — `a1_R6_assembled_local'`** (mirrors Campaign 2 Layer A exactly, `vanVleckGatedWitness'`
  throughout, calling D7's primed grand assembly).
- **D9 — `a1_R6_assembled_v3'`** (mirrors Campaign 2 Layer C exactly: destruct the N=1 package's
  existential `(a,b,S,C)` first via the SAME `gatedWitnessN1_horizon_bound`/`package_bound_on_horizon`
  Campaign 2 already built — these are witness-independent, no forking needed — then re-expose all ~50
  other hypotheses, now stated about `vanVleckGatedWitness'`, under the existential). May still accept
  an abstract `htriple : tripleHEmeas g gi (vanVleckGatedWitness' ...)`; Phase 5 discharges it
  concretely. **C4 gate:** both compile with fully primed witness-dependent signatures.

### Phase 5 — The concrete connection (Canary C5, the campaign's actual point)
- **D10 — the bridge.** A wrapper around `a1_R6_assembled_v3'` that removes the abstract `htriple`
  input and derives it via a literal application of `tripleHEmeas_concrete_v4'`. **This is the ONLY
  dispatch in the whole campaign whose entire reason for existing is to make Campaigns 1 and 2 compose**
  — everything in Phases 0–4 is prerequisite plumbing. Final checks: clean full build; grep-scan for
  stray unprimed witness/chart/amplitude tokens in new declarations; `#print axioms` std-3 on all new
  terminal theorems; confirm every existing banked file is byte-for-byte untouched.

## Dispatch-count table (Sol's 40th consult, given the pre-check)

| Phase | Scope | Canary | Min | Target | Contingency |
|---|---|---:|---:|---:|---:|
| 0 | Dependency audit + signature skeleton | C0 | 2 | 2 | 4 |
| 1 | CConv chart/derivative/envelope forks | C1 | 2 | 3 | 6 |
| 2 | Truncated-Duhamel/`EndpointData`/`InterchangeData`/`Mem*` reuse confirmation | C2 | 1 | 2 | 5 |
| 3 | Primed grand assembly | C3 | 1 | 1 | 4 |
| 4 | Primed local + v3 capstones | C4 | 2 | 2 | 4 |
| 5 | Concrete `tripleHEmeas_concrete_v4'` bridge | C5 | 1 | 1 | 2 |
| **Total** | | | **9** | **11** | **25** |

The `25` figure is a diagnostic contingency envelope, NOT an authorized budget. **If this campaign is
ever activated, set a hard reauthorization-stop at 16 total dispatches** — matching Sol's explicit
recommendation, well below the pre-pre-check 39th-consult estimate of 10–30+.

## STOP conditions (Sol, adopted verbatim)

Phase 0 STOP (re-estimate before any construction): more than 3 additional hardwired root families
found beyond the 4 already known (`CConvChartGateData`/`CConvDerivativeData`/`CConvEnvelopeData`/the
`a1_R6_assembled` shell); `GrandAssemblyRecon.a1_R6_assembled`'s PROOF (not just signature) turns out
opaque/old-witness-locked at the helper-lemma layer; the N=1 package is secretly old-chart-indexed;
`EndpointData`/`InterchangeData` turn out to need old-witness equalities rather than abstract-`Wit`
properties (contradicts this pre-check — would be a genuine surprise); expected total exceeds 16
dispatches.

Implementation STOP (any phase): requires editing an existing banked file; requires global equality
between old and primed witnesses; uses tube-`EqOn` outside an explicitly tube-restricted theorem;
produces a hybrid structure (primed measurability + old envelope/source fields); duplicates generic
analytic machinery merely to change the witness argument; needs `sorry`/`admit`/a new axiom/an
artificial-impossible hypothesis; two failed dispatches at the same boundary without a revised
dependency map.

## Recommendation (this dispatch, following Sol's 40th-consult verdict)

**Do NOT launch Phase 1 (D2) onward right now.** The pre-check materially de-risks the campaign (6 of
10 audited symbols need zero forking; the remaining 4 have most of their hardest ingredients already
banked by Campaign 1) and lowers the realistic estimate to **9–18 dispatches, mode 11–13** — well
below the unaudited 39th consult's 10–30+ — but there is STILL no named downstream consumer for
`a1_R6_assembled_v3` (old or primed), and Campaign 2's own Phase 6 was withheld for the identical
reason. Building a second, still-unconsumed ~65-hypothesis capstone would be speculative API
duplication, not capstone progress, per the SAME discipline this session already applied twice.

**What this dispatch actually authorizes:** Phase 0 (D0/D1) only, if/when resumed — the low-cost,
high-information audit that either confirms the favorable pre-check picture at the two remaining
unchecked items (grand-assembly proof body, N=1 package chart-independence) or surfaces a genuine
surprise early. Freeze after C0. **Resume Phase 1+ only when a named downstream theorem requires BOTH
`a1_R6_assembled_v3'` AND `tripleHEmeas_concrete_v4'` as its actual measurability discharge, or when
"Campaigns 1 and 2 must connect" is itself declared an explicit release criterion.**

`a₁=R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁=R/6`.

## Dispatch log

- **J4-1176 (this dispatch) — PLAN + partial Phase-0 audit, NO NEW LEAN FILE, NOT authorized for
  construction.** Read J4-1156–1175 in full, read both prior plan files, read
  `CapstoneExistentialAssembly.lean`/`CapstoneLocalAssembly.lean`/`TripleHEmeasConcreteV4GenWith.lean`
  in full, then performed a direct-grep pre-check of the 10 non-witness-chain data structures/`abbrev`s
  the ~50 other capstone hypotheses depend on (table above) BEFORE the 40th Sol consult, finding 6 of
  10 already fully chart/witness-generic (a materially more favorable picture than the unaudited 39th
  consult assumed). Consulted `gpt-5.6-sol` (40th consult, high effort) with this pre-check; verdict:
  revised estimate 9–18 dispatches (mode 11–13, well below the prior 10–30+), but explicit
  recommendation AGAINST launching full construction absent a named downstream consumer — matching
  Campaign 2's own Phase-6-withheld precedent. This file records the full phased plan, canary table,
  and dispatch-count table for future reference; only Phase 0 (D0/D1) is authorized to resume, and
  even that was left partially open (grand-assembly proof-body audit, N=1-package chart-independence
  re-verification) rather than force-completed this dispatch. No Lean written. `a₁=R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁=R/6`.

- **J4-1177 (this dispatch) — Phase 0 CLOSED (D0 fully complete); full-repo consumer search;
  41st Sol consult; NO NEW LEAN FILE, construction still NOT authorized.**

  **Phase 0 remainder, completed by direct audit (no construction):**
  1. `GrandAssemblyRecon.a1_R6_assembled`'s PROOF BODY (not just signature) inspected line-by-line:
     it calls exactly 3 helpers — `ETailRateBound.hDaLimLU_from_data` (fully generic over abstract
     `H F`, confirmed no witness hardwiring); `HD1CLMLift.hD1_concrete_from_scalar` (hardwired via
     `witnessFieldDeriv`/`CConvDerivativeData` exactly as already flagged in the J4-1176 pre-check
     table — no NEW hardwiring found; ingredient `witnessFieldDeriv'` already banked, J4-1157);
     `CapstoneAssembly.a1_R6_of_geometry_and_frontier`, whose own proof body threads straight into
     `a1_R6_of_residue_inf_v6` with the identical uniform `vanVleckGatedWitness g gi hChr hK S a b`
     threading pattern throughout — no additional hardwired data-structure family beyond the 4 already
     known (`CConvChartGateData`/`CConvDerivativeData`/`CConvEnvelopeData`/the `a1_R6_assembled` shell
     itself). **Verdict: no surprise; confirms the J4-1176 pre-check table with zero new fork points.**
  2. `GateOpennessExport.gatedWitnessN1_package_open` re-verified directly: its existential conclusion
     `∃ a b C : ℝ, ... ∃ S : Point n → Set (Point n), ...` — the `(a,b,S,C)` tuple itself is plain
     `ℝ`/`Set`-valued, witness/chart-independent IN TYPE. The accompanying `hbound`/`hmemS0`/`hopenS0`
     proof terms DO internally mention the old unprimed `uniformInverseChart`/witness machinery
     (via `globalCutoffParametrixWitnessN`), but the plan's D9 step only proposes reusing the raw
     `(a,b,S,C)` existential via the witness-independent `gatedWitnessN1_horizon_bound`/
     `package_bound_on_horizon` bridge (confirmed present, `PackageHorizonBound.lean`/
     `LocalizedBankedData.lean`/`CapstoneExistentialAssembly.lean`), NOT `hbound` itself. **Verdict:
     matches the plan's expectation exactly; no hidden old-chart indexing that breaks D9.**
  **Phase 0 (D0) is now CLOSED with zero unresolved entries and zero new STOP-condition triggers.**

  **Full-repo consumer search (background agent, thorough grep across every `.lean` file, `verify/`,
  `docs/`, `paper_strategy/`), for the ENTIRE capstone family, not just the primed/unprimed connection
  point:**
  - `GrandAssemblyRecon.a1_R6_assembled` (root, J4-222)
  - `RightInverseGeneral.a1_R6_assembled_v2'`
  - `CapstoneLocalAssembly.a1_R6_assembled_local` (Layer A)
  - `CapstoneExistentialAssembly.a1_R6_assembled_v3` (Layer C, most recent/general, the TRUE terminal
    capstone)

  **Finding: NONE of the four has a genuine consumer anywhere in the repo outside the capstone
  tower's own internal plumbing.** Every citation found is exactly the expected chain
  root → `v2'` → `local` → `v3` (each version invoked only to build the next), plus `#print axioms`/
  `#check` bookkeeping in `AxiomAudit.lean`. Zero hits in `verify/` (`claim_card.md`, scripts), zero
  hits in `paper_strategy/`. `docs/qg_roadmap/*.md` itself already documents this in prose but is
  planning/audit narrative, not a load-bearing citation. **`a1_R6_assembled_v3`, the actual endpoint
  of two full sub-campaigns, is consumed by NOTHING outside its own construction.**

  **41st Sol consult (`gpt-5.6-sol`, high effort)**, given this finding: unsoftened verdict —
  **witness-unification is not merely premature, it is currently the WRONG next target entirely.**
  Extending an already-unconsumed tower compounds the priority inversion. Recommended reallocation
  (next 1–3 dispatches, NOT authorized by this dispatch, for explicit follow-up decision only):
  (1) create the FIRST real consumer — a dedicated, stable, publication-facing verification entry
  point (e.g. `verify/A1R6Claim.lean`) that applies `a1_R6_assembled_v3` as an actual theorem
  application (not a `#check`), with `{hDuhamel, hDConv, hCConv}` explicit and the conclusion no
  stronger than what `v3` supports — if no coherent public claim can even be written around `v3`,
  that itself is further evidence the tower is non-load-bearing; (2) wire that consumer into
  `verify/claim_card.md` and the paper draft's claim map; (3) reassess witness-unification ONLY from
  that consumer's actual blocked obligations — if `v3` already discharges the public claim, freeze the
  capstone line entirely and do NOT unify witnesses; if blocked specifically on the primed witness,
  authorize only the minimal bridge that theorem needs.

  **This dispatch authorizes NEITHER witness-unification Phase 1+ NOR the consumer-creation dispatches
  Sol recommends** — both require explicit user/follow-up authorization. No Lean written.
  `a₁=R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁=R/6`.

- **J4-1178 — LEAN: `A1R6PublicClaim.lean` — the FIRST real consumer of the capstone tower, satisfying
  Sol's 41st-consult precondition for reconsidering this file.** Full details in `JET4_TOWER_PLAN.md`.
  With a named consumer now in place, Phase 1+ of THIS plan was explicitly re-authorized (by the
  dispatcher, outside this file) for the next dispatch.

- **J4-1179 (this dispatch) — LEAN: Phase 1, D2 — `CConvChartGateDataWith.lean`.** Built
  `CConvChartGateDataWith` (generic over an abstract chart `W` AND an abstract witness-field-derivative
  `WD`), `chartGateDataWith_iff_old` (the `Iff` compatibility bridge to the existing
  `CConvChartGateData` at the old concrete values), and `CConvChartGateData'` (the primed instantiation
  at `uniformInverseChart'`/`witnessFieldDeriv'`). **Scope correction:** D2 as literally worded above
  ("2 hardwired fields") undercounts — direct re-read finds FIVE fields mention chart/witness machinery
  (`hVmapMeas`/`hCover`/`hChartB`/`hSliceData`'s `radialCutoff` leg/`hKmeas`), matching an independent
  EARLIER finding (J4-321, `ChartParamFacadeVariant.lean`/`CConvChartGateDataW`, a different chart `Wg`)
  that neither this plan's pre-check nor the 40th/41st Sol consults cross-referenced. Judged NOT a STOP
  trigger (same known fork point, more completely counted; the earlier file already proved the full
  fork closes cleanly for a different chart). **Also surfaced, unresolved:** J4-321 independently found
  the downstream consumer (`SliceInterfaceInstantiation.hjoint_instantiated`/`HenvUInstantiation`/
  `WitnessDerivMeasurability`) hardwires `uniformInverseChart` in its PROOF BODY, not just its
  statement — direct prior evidence against this plan's own Phase 3 (D7) assumption ("none of those
  lemmas are chart/witness-hardwired below the structure layer"); raises Phase 3's risk above this
  plan's stated expectation, to be re-audited when Phase 3 is reached, per Phase 3's own STOP condition.
  Build/audit clean (std-3, no sorryAx); Canary C1's "no unprimed token" grep-scan confirmed on
  `CConvChartGateData'` directly. Commit `5d4118c4`, pushed. **Canary C1 not yet fully closed** — D3
  (`CConvDerivativeDataWith`/`'`) and D4 (`CConvEnvelopeDataWith`/`'`, itself re-auditing for the SAME
  undercount risk against its own literal field list) remain. `a₁=R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁=R/6`.
