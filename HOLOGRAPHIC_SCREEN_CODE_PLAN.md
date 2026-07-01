# Toy Stage 1 — the finite holographic-screen code (a kinematic INTERFACE, not gravity)

**Status:** ACTIVE (2026-07-01). **Origin:** the GPT-5.5-pro expert consult on "what microscopic mechanism would
QIQT-H need to become a quantum gravity theory," which *corrected* the naive spec. This plan implements ONLY the
honest, tractable **toy Stage 1** the consult endorsed — and labels, loudly, everything it does **not** do.

## ⚠ HONEST SCOPE (read first — the load-bearing verdict)

**This does NOT make QIQT-H a quantum gravity theory, and does NOT close the "mechanism gap."** GPT-5.5-pro's verdict:
the mechanism gap "is basically the quantum-gravity problem itself." What is tractable and honest now is a **toy
holographic-screen code** that turns the regional capacity from a *postulate* into a *theorem — given a LOCAL packing
constraint + the code/min-cut structure*. That is a genuine reduction (regional area law ⟸ local packing), and it is
exactly "the precise **interface** into which a real microscopic model could plug" that the consult named as QIQT-H's
one genuine piece of leverage. It is **kinematic scaffolding**, not gravity.

**Two corrections from the consult, enforced in every theorem:**
1. **Area is an INDEPENDENT charge, never `log dim`.** Defining `A := 4G·log(dim)` and then "proving" `log dim = A/4G`
   is a *tautology* ("you renamed the cut capacity 'area'"). Here each screen link carries **two independent labels** —
   a Hilbert dimension `D_e` and an **area weight `α_e`** — related only by a *carried* local constraint. A machine-
   checked **independence guard** (`area_dim_independent`: large area with zero code dimension) certifies they are not
   the same quantity (the analogue of `EntropyNotCardinality` / `svn_underdetermines_smax`).
2. **A BOUND with horizon saturation, not exact `e^{A/4G}`.** Gravity gives `S ≤ A/4G` saturated by horizons; exact
   equality for every region is too strong (and `e^{A/4G}` is not even integral in general). We prove `≤`, with a
   separate saturation theorem for the horizon-like (packing-saturating) sector.

**Frontiers this plan does NOT touch (the genuine QG walls, per the consult — cite, never claim):**
- **Stage 3 — dynamical Einstein + propagating gravitons.** "THE most serious… fatal to any code-*only* proposal."
  Codes give kinematic subregion duality, not a massless spin-2 mode / universal coupling / Newtonian potential /
  Einstein self-interaction. NOT attempted.
- **Background independence.** A *fixed* graph "smuggles geometry." Here the screen/cuts are **supplied/fixed** — so
  this is explicitly a fixed-graph *toy*, NOT background-independent. A dynamical/gauge-redundant connectivity
  (spin-foam / GFT / tensor-model) is the frontier.
- **Non-circular `G`.** The `1/4G` coefficient is **carried in the local packing constraint**, never derived; making
  `Λ_s`/`G` a substrate output (dimensional transmutation) is the frontier (Sakharov has regulator/species/counterterm
  ambiguities).
- **Independent area from a UV-complete theory.** Here `α_e` is a *supplied* label; deriving it (and identifying it
  with a geometric area) is the frontier.
- The **`(Φ,λ)` selector gives NO leverage here** — it is interpretational, not a gravity mechanism (consult). Absent.

**Honest invariants (enforce every increment):** NO `sorry`; `#print axioms` std-3; budget 0. NEVER claim this is
quantum gravity, closes the mechanism gap, derives `G`, or is background-independent. Area is ALWAYS an independent
charge; the capacity result is a `≤` bound; the `1/4G` is a carried local constraint. Advertise the deliverable as a
**toy kinematic interface** (a finite holographic-screen code), explicitly a fixed-graph model, with the graviton /
background-independence / non-circular-`G` walls labelled cited frontiers. Cite the GPT-5.5-pro verdict.

---

## The object

A **finite holographic-screen code**. A region `R` is bounded by a finite **screen** = a `Finset` of links `∂R`.
Each link `e` carries **two independent** labels: `logDim e ≥ 0` (the log Hilbert dimension the link can carry) and
`areaWt e ≥ 0` (its **independent** area charge). Define:
- **Code capacity (single-cut bound):** `codeCap(∂R) = Σ_{e∈∂R} logDim e` — the holographic-code property
  `log dim C_R ≤ Σ_cut log D_e` (a cut is an upper bound on the encodable logical dimension).
- **Screen area (independent charge):** `screenArea(∂R) = Σ_{e∈∂R} areaWt e`.
- **Local holographic packing constraint (the microscopic postulate, CARRIED):**
  `Packing(G) := ∀ e∈∂R, logDim e ≤ areaWt e / (4G)`.

The linchpin toy theorem: **local packing ⟹ regional area law** `codeCap(∂R) ≤ screenArea(∂R)/(4G)`, with area an
independent charge, `1/4G` carried locally, and horizon saturation when packing is tight on the (min-)cut.

---

## Track B — Lean (`QIQTH/HolographicScreenCode.lean`, namespace `QIQTH.ScreenCode`)

### S1a — the structure + the independence guard (avoid the tautology)
`ScreenCut` structure (`links : Finset ι`, `logDim`, `areaWt`, nonneg fields); `codeCap`, `screenArea`. **The guard**
`area_dim_independent : ∃ S, screenArea S > 0 ∧ codeCap S = 0` — area and code dimension are provably *distinct*
(large area, zero dimension) — certifying we did NOT set `area := log dim`. [AF]

### S1b — the linchpin: local packing ⟹ regional area law
`area_law_of_packing (hG : 0 < G) (h : ∀ e∈S.links, S.logDim e ≤ S.areaWt e/(4G)) : codeCap S ≤ screenArea S/(4G)`
— `Finset.sum_le_sum` + `Finset.sum_div`. The regional holographic bound **derived** from a *local* packing
constraint + the code structure (the postulate reduced from "regional area law" to "local packing"). [AF]

### S1c — horizon saturation (the bound is tight)
`area_law_saturation (hsat : ∀ e∈S.links, S.logDim e = S.areaWt e/(4G)) : codeCap S = screenArea S/(4G)` — the
horizon-like sector where the local packing is saturated on every cut link makes the area law an *equality*. [AF]

### S1d — min-cut over a family of cuts + area additivity
Given a finite family of cuts separating `R`, `codeCap ≤ min over cuts of screenArea/(4G)` (the min-cut / RT-flavored
bound; ties to Track C's `flow_weak_duality`); additivity/subadditivity of `screenArea` under disjoint/union screens.
[AF] (Keep it a genuine `min` bound; if the general min-cut is heavy, do the two-cut / explicit-family case and
label the general case.)

### S1e — wire-in + audit + honest inventory note
`QIQTH.lean` import (or keep standalone like the AdS/CFT bridge — decide by whether it's "QIQT-H result" vs
"interface toy"; default: **wire in**, it's a genuine QIQT-H reduction), `AxiomAudit.lean` pins (std-3),
`axiom_budget_check.sh` budget 0; add a `LEAN_RESULTS_INVENTORY.md` entry **loudly labelled** "toy kinematic
interface — capacity postulate → theorem *given a local packing constraint*; area an independent charge; NOT gravity;
gravitons / background-independence / non-circular `G` are cited frontiers."

### Follow-ons (NOT this plan — the QG frontier)
Dynamical connectivity (background independence); a graviton / spin-2 sector (Stage 3); deriving `α_e`/`G` from a
substrate (non-circular `G`); the causal-diamond/screen algebra `⊕_a B(H_{D,a})` with `a` a genuine boost/edge charge.

---

## Verification (per increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.HolographicScreenCode` green; `#print axioms` std-3;
`bash scripts/axiom_budget_check.sh` budget 0; ONE commit per increment with the `Co-Authored-By: Claude Opus 4.8
<noreply@anthropic.com>` trailer; push via `git -c http.sslBackend=schannel push origin main`; update the Progress
log. NO `sorry`. NEVER claim QG / mechanism-gap-closed / derived-`G` / background-independent.

## Honest scale
S1a–S1c are hours–days (finite sum inequalities). S1d is days (min-cut). This whole plan is a **toy interface**, days–
weeks, and by construction does **not** close the mechanism gap — it delivers the one honest, machine-checkable rung
(capacity postulate → theorem given local packing, area independent) and cleanly marks the real QG walls.

## Progress log
- **2026-07-01** — plan created from the GPT-5.5-pro mechanism consult (corrected spec: screen code not static TN;
  area an independent charge; `≤` bound with horizon saturation; gravitons/background-independence/non-circular-`G`
  labelled frontiers). NEXT → S1a (structure + independence guard).
- **2026-07-01 — S1a + S1b + S1c ✅ DONE** (`QIQTH/HolographicScreenCode.lean`, all [AF] std-3, wired into
  `QIQTH.lean` + `AxiomAudit.lean`, budget 0). **S1a:** `ScreenCut` structure (each link carries *independent*
  `logDim` + `areaWt`), `codeCap`/`screenArea` + nonneg lemmas, and the tautology-guard `area_dim_independent`
  (a screen with positive area but zero code dimension — area ≠ log dim). **S1b (linchpin):** `area_law_of_packing`
  — the local packing constraint `Packing S G := ∀ e∈links, logDim e ≤ areaWt e/(4G)` ⟹ the regional area law
  `codeCap ≤ screenArea/(4G)` (via `Finset.sum_div` + `Finset.sum_le_sum`) — the capacity postulate reduced to a
  *local* packing postulate, area an independent charge, `1/4G` carried locally. **S1c:** `area_law_saturation` —
  tight local packing ⟹ equality (the horizon sector). Loudly labelled a toy kinematic interface, NOT gravity;
  gravitons/background-independence/non-circular-`G` cited as untouched frontiers. Inventory entry added.
  **NEXT → S1d** (min-cut over a family of cuts / area additivity — explicit-family or two-cut case if the general
  min-cut is heavy) → **S1e** (finish audit polish).
- **2026-07-01 — S1d ✅ DONE** ([AF] std-3, pinned, budget 0). The min-cut / RT-flavored bound and area algebra:
  **`mincut_area_law`** — a region capacity `capR` bounded by *every* separating cut (`capR ≤ codeCap (S k)`) is
  bounded by the **minimum** area over a nonempty finite cut family, `capR ≤ min_k screenArea(S k)/(4G)` (indexed
  by `κ` to avoid `DecidableEq (ScreenCut)`; via `Finset.le_inf'_iff` + `area_law_of_packing`) — the easy half of
  Ryu–Takayanagi; the cut family is **supplied/fixed** (NOT background-independent). **`screenArea_union_of_disjoint`**
  (area charge additive over disjoint link-sets) and **`screenArea_le_of_subset`** (a larger screen carries ≥ area).
  Still a toy kinematic interface, NOT gravity. **NEXT → S1e** (audit polish — the wiring is already done: `QIQTH.lean`
  import + `AxiomAudit` pins present for S1a–S1d; S1e is any residual inventory/plan tidy, then the plan's tractable
  toy surface is exhausted and the frontiers stay cited).
- **2026-07-01 — S1e ✅ DONE + TOY STAGE 1 COMPLETE.** Added the load-bearing guard
  **`codeCap_unbounded_at_fixed_area`** ([AF] std-3, pinned): without the packing constraint, a screen's code
  capacity is *unbounded at fixed area* (∃ screen, `screenArea ≤ 1 ∧ codeCap ≥ M` for any `M`) — so
  `area_law_of_packing` genuinely *requires* the local packing postulate; the area law is **not free** (a naive
  capacity is volume-like), and the carried `1/4G` is doing the work. The honest companion to
  `area_dim_independent`. Wiring (import + `AxiomAudit` pins + inventory entry) complete for S1a–S1e; budget 0.
  **THE TOY STAGE 1 IS COMPLETE** — 8 theorems: structure + independence guard (S1a), local-packing⟹area-law
  linchpin (S1b), horizon saturation (S1c), min-cut/RT bound + area algebra (S1d), packing-is-load-bearing guard
  (S1e). It turns the capacity **postulate into a theorem GIVEN a local packing constraint**, with area an
  **independent** charge — the honest "interface into which a real microscopic model could plug." **It does NOT
  close the mechanism gap.** The only remaining work is the genuine QG frontiers (cited, NOT this plan): dynamical
  Einstein + propagating gravitons (Stage 3), background independence (dynamical connectivity), non-circular `G`,
  and deriving the area charge from a substrate. **Next fires: no tractable in-scope item remains — CHECKPOINTED
  COMPLETE.**
