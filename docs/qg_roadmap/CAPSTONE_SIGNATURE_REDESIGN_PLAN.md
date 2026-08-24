# Capstone-signature redesign plan — reconciling the N=1 local-horizon discharge with `a1_R6_assembled_v2'`

Status: SCOPED (this dispatch, J4-1168), NOT YET AUTHORIZED FOR CONSTRUCTION. Sized per `gpt-5.6-sol`'s
38th consult (high effort), given the exact Lean signatures on both sides. This file is the discoverable
record of the plan so future dispatches do not re-derive it from scratch — mirrors the format of
`docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md`.

## Why this exists

J4-1156–1164 (the chart-parametric rebuild campaign) landed a genuine, non-vacuous discharge of `hWmeas`
for a primed triple (`TripleHEmeasConcreteV4GenWith.tripleHEmeas_concrete_v4'`) — but J4-1165/1166/1167
(three independent investigations) found this does NOT connect to the live capstone
`RightInverseGeneral.a1_R6_assembled_v2'`, and neither does the pre-existing OLD-chart N=1 discharge
`GatedGlobalWitnessN1CapstoneEbdDischarged.trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged`
(J4-774). Both discharge routes produce an EXISTENTIALLY-quantified `∃ a b S, ...` package with a
`(0,t]`-LOCAL affine-in-ceiling bound, while `a1_R6_assembled_v2'`'s `hEboundFull` binder demands a
GLOBAL `∀τ>0` bound at EXTERNALLY-FIXED `a b S C`. J4-1167 confirmed (via Sol's 37th consult) there is
no cheap (1-3 dispatch) bridge and no naive wrapper — the existential witnesses cannot be synchronized
with arbitrary external ones after the fact. This dispatch (J4-1168) obtains a concrete, ordered,
dispatch-sized plan for the "repaired path" Sol sketched at the end of J4-1167 (destruct the existential
first, then redesign).

## Exact signatures this plan is built against

**Existing discharge** (`QIQTH/GatedGlobalWitnessN1CapstoneEbdDischarged.lean`, J4-774),
`trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged`: concludes
`∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ S : Point n → Set (Point n), (let H := gatedKernel K S
(globalCutoffParametrixWitnessN 1 ...) a b (uniformInverseChart ...); <5 hyps about
StronglyMeasurable/heatConv/DifferentiableAt/ContDiff> → <a₁=R/6-shaped conclusion pair for H>)`. Inside
its proof, `gatedWitnessN1_package_open` yields `⟨a, b, C, ha, hab, hC0, S, hbound, hmemS0, hopenS0⟩`
where `hbound : ∀ t' τ p q, 0 < τ → τ ≤ t' → |heatOp g gi H τ p q| ≤ (C * (1 + t')) * baseKernelW 2 0 τ p q`
— `C` and `S` chosen INTERNALLY by the package, bound `(0,t']`-LOCAL with an AFFINE-in-ceiling constant.

**Live capstone** (`QIQTH/RightInverseGeneral.lean`), `a1_R6_assembled_v2'`: ~65 hypotheses. The two
consumers of `hEboundFull` are, verbatim from the proof body:
```
have endpoint : EndpointData g gi W t C :=
  endpointData_of_banked g gi W t C hEboundFull hEzeroE hEmeas
have inter : InterchangeData g gi W t :=
  interchangeData_of_banked g gi W t C hCnn hEboundFull hEzeroE hEmeas ht
```
(`W := vanVleckGatedWitness g gi hChr hK S a b`). Every one of the other ~50 hypotheses (`Bs/Ba/Bd/Cf/
metric/chart/source/derivData/env/hgD1/T/U/r₀/τ₀/u₀/u₁/A₀/A₁/C_L/D0/D1/E₀/E₁/...`) is stated at the same
externally-fixed `a b S`, and the large majority do NOT mention `C` at all — they are independent free
real-number bound witnesses the discharge route never supplies.

## Sol's 38th consult (`gpt-5.6-sol`, high effort, 2026-08-24) — verdict summary

Given both exact signatures, Sol's core finding: **the viable redesign is NOT "apply the existing
discharged existential to the existing fixed-`(S,a,b)` capstone"** — those witnesses cannot be
synchronized after the fact. The viable shape is a THREE-LAYER redesign (mirroring the `XWith`/`X`/`X'`
discipline of the chart-parametric campaign, but for existential-witness reconciliation rather than
chart substitution):

- **Layer A — `a1_R6_assembled_local`**: a copy of `a1_R6_assembled_v2'` with ONLY `(C, hCnn,
  hEboundFull)` replaced by `(CT, hCTnn, hEbound_t)` where `hEbound_t` is `(0,t]`-LOCAL. All ~50 other
  hypotheses are copied UNCHANGED (not generalized, not transported) — this is the real refactor.
- **Layer B — `a1_R6_assembled_v2'` preserved as a wrapper**: restrict the existing global
  `hEboundFull` to a local `hEbound_t` (`fun τ p q hτ _ => hEboundFull τ p q hτ`) and invoke
  `a1_R6_assembled_local` with `CT := C` — a regression test that Layer A didn't accidentally weaken
  anything.
- **Layer C — `a1_R6_assembled_v3`**: destructs `gatedWitnessN1_package_open`'s existential FIRST,
  sets `CT := Cpkg * (1 + t)`, derives `hEbound_t` from `hPkgBound t`, and re-exposes ALL ~50 other
  independent hypotheses as caller-supplied inputs UNDER the existential (they are NOT discharged by
  opening the package — the package never touches them).

### (a) Hypothesis classification (Sol's answer)

- **(i) Discharged/removed** as public `v3` inputs: `S`, `a`, `b`, `ha`, `hab`, external `C`, `hCnn`,
  `hEboundFull` — all replaced by the existential + internal `CT := Cpkg*(1+t)` + `hEbound_t` derived
  from `hPkgBound t`. `hK0`/`hS0` MAY discharge via `hmemS0`/`hopenS0` IF their exact types match
  (needs a fresh binder-type read — not assumed).
- **(ii) Unchanged free inputs, now at the package-selected tuple**: essentially everything else —
  `htriple, core, hCH, uu, hu_open, hu0, Bs, Ba, Bd, Cf, Dmap, metric, chart, source, derivData, env,
  hgD1, T, hT, U, hUopen, htU, hUpos, hUT, r₀, τ₀, hr₀, hτ₀, u₀, u₁, hAnear, hu₀cont, hu₀one, C₀, C₁,
  hu₀bdd, hu₁bdd, A₀, A₁, C_L, hA₀, hA₁, hC_L, hAdom, hAzero, hBdom, hBcont, hAmeas, hBmeas, hu₀meas,
  hu₁meas, hMeasFII, hUfloor, hInnerCont, nb, hnb, hFmeas, hFint, hF'meas, boundD, hbdd, hbound,
  hpardiff, L, hLnn, hCross, pdpdH, hInterchange, hLapFull, hII_lo, hII_hi, D0, D1, hD0, hD1nn, hbnd,
  E₀, E₁, hE₀, hE₁, hEdom, hEzeroE, hFzero, hIlo, hIhi, hEcomb, hEmeas`. NONE of these are supplied by
  `gatedWitnessN1_package_open` — the package fixes only `a, b, C, S` and the local bound.
- **(iii) New bridging lemmas needed**: (1) `package_bound_on_horizon` — elementary, instantiate
  `hPkgBound` at `t' := t`; (2) a LOCAL sibling of `endpointData_of_banked` accepting `(0,t]`-restricted
  input (needs auditing whether `EndpointData.hEbound`'s own stored type is already local, per J4-1167's
  finding — likely a thin adapter); (3) a LOCAL sibling of `interchangeData_of_banked` — the PRINCIPAL
  analytic risk (does `InterchangeData` genuinely need arbitrary-τ estimates internally, or only up to
  `t`?); (4) a kernel-identity bridge, `vanVleckGatedWitness g gi hChr hK S a b = gatedKernel K S
  (globalCutoffParametrixWitnessN 1 ...) a b (uniformInverseChart ...)` at the package's `a b S`
  (expected `rfl`/`simp`, unverified); (5) a `tripleHEmeas → StronglyMeasurable` projection bridge if the
  factored pointwise discharge still wants the raw `StronglyMeasurable` shape.

### (b) The `C`-vs-`CT` mismatch (Sol's answer)

Do NOT existentially quantify `C`/`Cpkg` in the public `v3` conclusion — keep it as a proof-internal
`let CT := Cpkg * (1+t)`, since none of the ~50 retained hypotheses mention the original external `C`
(confirmed by the audit above). Critically, Sol states plainly: **a single global constant `C` uniform
over ALL `τ > 0` does NOT follow from the package's bound by replumbing** — `Cpkg*(1+τ) ≤ C_external` for
all `τ>0` forces `Cpkg = 0` (degenerate). The `(0,t]`-local `CT := Cpkg*(1+t)` is the honest, valid
uniform bound on the horizon actually needed; recovering a genuinely GLOBAL bound would require a NEW,
stronger analytic residual estimate — explicitly flagged as out of scope for a replumbing campaign.

### (c) Named canary checkpoints (D0–D10, Sol's answer, adapted to this repo's convention)

- **D0 — SameKernel**: `vanVleckGatedWitness g gi hChr hK S a b = gatedKernel K S
  (globalCutoffParametrixWitnessN 1 ...) a b (uniformInverseChart ...)` at the package's tuple, by `rfl`
  or one controlled `simp`. STOP-and-resize if this needs pervasive transports through measurability/
  continuity/derivative predicates.
- **D1 — HorizonBound**: `package_bound_on_horizon` (elementary `t' := t` instantiation) compiles
  standalone.
- **D2 — CDependency**: grep-audit confirms external `C` occurs ONLY in `hCnn`, `hEboundFull`, and the
  two `_of_banked` calls in the CURRENT `a1_R6_assembled_v2'` — nowhere inside `core`/`chart`/`env`/etc.
  STOP if `C` is embedded in any retained downstream structure.
- **D3 — EndpointLocal**: `endpointData_of_banked_on_horizon` (or confirmation the existing one is
  already local) compiles with every bound-use accompanied by an explicit `τ ≤ t` proof.
- **D4 — InterchangeLocal**: same for `interchangeData_of_banked`'s local sibling — the PRINCIPAL
  early-warning checkpoint. STOP-and-reclassify-as-a-new-analysis-campaign if `InterchangeData`
  genuinely needs an estimate at times beyond `t`.
- **D5 — BackCompat**: `a1_R6_assembled_v2'` reproved as a thin wrapper around
  `a1_R6_assembled_local` (Layer B). Failure for any reason OTHER than the two changed helper calls means
  the refactor silently changed something else — investigate before proceeding.
- **D6 — SingleOpening**: the pointwise-factored discharge and `a1_R6_assembled_local` are invoked after
  EXACTLY ONE opening of `gatedWitnessN1_package_open` — no second, unrelated existential selection
  anywhere in the `v3` proof.
- **D7 — DependentTail**: a reduced `v3` truncated to the first one or two dependent-hypothesis clusters
  elaborates without `Eq.ndrec`/`cast`/manual transports (catches binder-order/`let W := ...` problems
  early, before moving all ~50 hypotheses).
- **D8 — IndependentConstants**: a real call site is asked by Lean to supply `C₀, C₁, A₀, A₁, C_L, D0,
  D1, E₀, E₁` explicitly — confirms these are NOT silently unified with `Cpkg`/`CT`.
- **D9 — NonHollowIntegration**: after opening `v3`'s existential at a real consumer, the first
  remaining goal is a genuine tuple-specific analytic hypothesis (`htriple`, `Bs`, `hAmeas`, ...), not a
  witness-equality/elaboration artifact.
- **D10 — AxiomCanary**: `#print axioms` on `a1_R6_assembled_local`/`a1_R6_assembled_v2'`/
  `a1_R6_assembled_v3` all std-3, no new axioms.

### (d) Phases and dispatch-count estimate (Sol's answer)

| Phase | Content | Dispatches |
|---|---:|---:|
| 0 | Exact-signature/dependency inventory (`hK0`/`hS0`/`hEmeas` types, all `C` occurrences, kernel-identity expansion) → D0/D2 | 2–3 |
| 1 | `package_bound_on_horizon` + kernel-identity bridge + `hK0`/`hS0` discharge decision → D0/D1 green | 3–5 |
| 2 | Localize the two `_of_banked` consumers (`endpointData_of_banked_on_horizon`, `interchangeData_of_banked_on_horizon`) → D3/D4 green. **STOP here if D4 fails genuinely** (separate math campaign, not plumbing) | 6–10 |
| 3 | Extract `a1_R6_assembled_local` (Layer A) + rebuild `v2'` as wrapper (Layer B) → D5 green | 5–8 |
| 4 | Factor the J4-774 discharge theorem into a pointwise version (concrete `a,b,Cpkg,S` + package certs, existential-opening moved to a thin corollary) → D6 green | 4–7 |
| 5 | Build the `a1_R6_assembled_v3` existential signature (Layer C), instantiate `CT` internally → D7/D8 green | 4–7 |
| 6 | Migrate a REAL consumer through all ~50 tuple-dependent hypotheses (NOT automatic — each must be constructed/reproved at the package's chosen tuple) → D9 green | 10–20+ |
| 7 | Cleanup, full build, `#print axioms` on all three layers → D10 green | 3–5 |
| **Total (API redesign through v3, no real consumer)** | | **24–40** |
| **Total (incl. one real consumer migration)** | | **34–60** |

## Honest worth-doing assessment (Sol, verbatim finding, not softened)

The `C`-vs-`CT` mismatch is a contained, tractable local-horizon API problem (Phases 0–5, ~20-30
dispatches). The `S,a,b` existential-vs-external mismatch is a genuinely separate dependent-witness
alignment problem with NO automatic transport — none of the ~50 independent hypotheses
(`Bs/Ba/Bd/Cf/A₀/A₁/C_L/D0/D1/E₀/E₁/...`) were ever discharged by the J4-774 package and remain a full
caller obligation at whatever tuple is finally chosen (Phase 6, the largest and least certain phase).
**Building Layer C (`v3`) in isolation, with no committed downstream consumer prepared to build that
tuple-specific bundle, would be mostly signature ceremony, not capstone progress.** This plan should NOT
be authorized for Phase 6 until a specific consumer (or a decision to treat `v3` itself as the new
terminal capstone target) is named.

## Recommendation

Phases 0–5 (~24-40 dispatches) are a well-defined, honestly-scoped sub-campaign that closes the `C`/`CT`
mismatch and produces a real `a1_R6_assembled_v3` existential capstone matching the N=1 package's actual
proven shape — a genuine, non-hollow improvement over the current disconnect (J4-1165/1166/1167's
finding that NOTHING wires into `a1_R6_assembled_v2'` at all). Phase 6 (the ~50-hypothesis transport,
10-20+ more dispatches) should be separately authorized only once Phase 5 lands and a concrete consumer
is named — attempting it speculatively risks exactly the "ceremony without content" failure mode Sol
flagged. D4 (Phase 2) is the single highest-risk early checkpoint: if `InterchangeData` turns out to
genuinely require unbounded-τ estimates, this entire plan pivots to a new analytic sub-campaign rather
than a plumbing one, and should be re-scoped before continuing.

`a₁=R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁=R/6`.
