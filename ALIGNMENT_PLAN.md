# Alignment plan — make every public claim match the Lean ground truth

**Status:** ACTIVE (2026-06-30). **Ground truth:** `LEAN_RESULTS_INVENTORY.md` (built from a full-coverage,
10-agent audit of all 296 `.lean` files). **Goal:** every claim in code comments, the website, and the paper is
checkable against the inventory and accurately scoped — no overclaim, no stale under-claim. The loop iterates over
the areas below, most-impactful-first; each iteration checks one area against the inventory and fixes
misalignments, one commit.

## 0. Honest invariants
- The inventory is the reference. A claim is **aligned** iff the inventory supports it with the same qualifiers
  (axiom-free? conditional-on-what? frontier? re-derivation? no-go?).
- Standing scope corrections to enforce everywhere (from the inventory):
  1. **"Finite capacity / finite quantized information" → "finite holographic ENTROPY over covariant (Type III₁)
     matter."** NOT a finite matter Hilbert space (D2/D3). Load-bearing for the gravity/area thread, NOT for the
     selection mechanism (`measure_needs_only_finiteness`).
  2. **Born is REDUCED to one premise (P5/noncontextual canonical measure), not DERIVED from unitarity.**
  3. **The 1/4 ratio is a machine-checked *re-derivation* of standard Sakharov/induced-gravity** (heat-kernel
     coefficients cited; G carried) — true & verified, but not unique to finiteness.
  4. **Single outcomes = λ + decoherence, NOT capacity** (H2 retired). Do not say capacity forbids multi-record.
  5. **The Einstein equation is conditional & free-field only.** The CPSUV "escape" is NOT established (~10–20%).
  6. **Credit what is genuinely strong:** full formal verification (296 files / ~3300 thms, budget 0); the
     Lieb-concavity/DPI/SSA tower (Mathlib-grade); the unconditional one-particle BW + the OP3b boost-invariant
     measure; the Born reduction. Don't *under*-claim these.
- Ship one area per iteration; commit + push; update §4 log.

## 1. Areas to align (the loop's work-list, most-impactful-first)

### A1 — Code-comment hygiene *(Lean docstrings + AxiomAudit; the cheapest, clearest)*
Fix stale docstrings that **under-claim** (say "axiom"/"frontier" for now-proved results), per the audit:
- `ArakiInterface.lean` header ("`IHol_le_Shannon`/`AkRelEnt` remain axioms" → both PROVED).
- `RelEntPositivity.lean:8-9` ("we axiomatize" → discharged; Gibbs proved).
- `GoldsteinStruyveFinDim.lean:21`, `GoldsteinStruyveStep1.lean:30` ("Steps 1,3 axiomatized" → fully PROVED).
- `AxiomAudit.lean:~4882-4897` (clock-energy/momentum "e.s.a. = carried frontier" → `clockEnergy_isSelfAdjoint`
  PROVED at ~5067); `AxiomAudit.lean:~216-220` (GS "standard + sub-axioms" → discharged); the `StoneProduct.lean`
  header "wiring is the follow-on" (→ `dressedModularGen_isSelfAdjoint` DONE).
Add missing `#print axioms` pins for terminal theorems: `strong_subadditivity`, `condMutualInfo_nonneg`,
`SakharovRatio.sakharov_ratio`, `ValueSelection.*`, and the GR/crossed-product capstones (~55 modules) — closes
the audit-coverage gap. PASS = no stale "axiomatized" claims; terminal theorems pinned.

### A2 — Website *(public-facing; highest external impact)*
Page by page (`website/src/pages/`: `index.astro`, `idea`, `theory`, `formalization`, `papers`,
`open-problems`, `reach`, `ladder`, `selection`, `born`, `realisations`, `about`, the `statements/` and
`browser/` pages): check each claim against the inventory. **Enforce the scope corrections (§0).** Especially:
the homepage/`idea`/`theory` "finite quantized information" headline → finite *entropy* + interpretation framing;
any "derives Born" → "reduces Born to P5"; any "finite capacity forbids two records" → retired; the 1/4 as
"derived" → note re-derivation. **Credit** the genuine breadth (the formalization scale, the DPI/Lieb tower).
PASS = every page's claims map to an inventory entry with matching qualifiers.

### A3 — Paper *(`QIQT_Foundations_Paper.md`)*
Section by section (abstract, §1.1/§1.1a, §3, §4, §7, §11.4, the formal-verification paragraph): same checks.
The Lorentz-naturalness frontier paragraph is already added; verify the abstract/§1 "finite capacity (FQ)"
framing is the entropy reading, the Born framing is "reduced to P5," and the 1/4 is a re-derivation. PASS = the
paper's claims match the inventory; the formal-verification paragraph reflects the true scope (incl. the Lieb/DPI
tower and the budget-0 / 296-file scale).

### A4 — A claims ledger + final consistency pass
Build `CLAIMS_LEDGER.md`: each headline public claim (paper + site) → the supporting inventory entry +
status. Final pass: no claim without a ledger row; the inventory, paper, and site agree. PASS = a complete,
cross-referenced ledger.

## 2. Verification (per iteration)
Code edits: rebuild the touched module(s) green; if `#print axioms` lines added, run `bash scripts/
axiom_budget_check.sh` (budget 0). Website edits: `NODE_OPTIONS=--use-system-ca npm run build` green. One commit
per area with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; update
§4. Never claim QG or the value of `G`; the `1/4` ratio is derived (a re-derivation).

## 3. Honest difficulty
A1 is days (mechanical comment/pin fixes + small rebuilds). A2/A3 are the bulk (claim-by-claim reading against
the inventory) — a few iterations each. A4 is a synthesis. The whole alignment is **weeks of iterations**, but
each iteration is a self-contained, shippable, honest increment. Expected net effect: the public framing moves
from "finite-information foundation (new physics)" to "a rigorously verified single-world interpretation + a
substantial formalized operator-algebra/entropy library + induced-gravity re-derivations," with every claim
inventory-backed.

## 4. Progress log
- **2026-06-30** — plan created; `LEAN_RESULTS_INVENTORY.md` built (full 296-file coverage); `vacuity_lint.sh`
  extended to subdirs (tree clean).
- **2026-06-30 — A1 ✅ DONE** (code-comment hygiene): fixed 4 stale docstrings that *under*-claimed now-proved
  results — `ArakiInterface.lean` ("two results remain axioms" → both PROVED, no project axioms),
  `RelEntPositivity.lean` ("we axiomatize" → discharged), `GoldsteinStruyveFinDim.lean` + `GoldsteinStruyveStep1.lean`
  ("Steps 1,3 / sub-lemmas axiomatized" → fully PROVED). Pinned the two unaudited Entropy/ capstones
  (`strong_subadditivity`, `condMutualInfo_nonneg`) in `AxiomAudit.lean` — both std-3, budget 0 (coverage gap
  closed). All touched modules green. (Remaining audit-pin gaps for other terminal theorems can be added in later
  A1 passes.)
- **2026-06-30 — A2 (website) in progress.** Survey finding: the site is **already well-aligned and honest** on
  the load-bearing scope — Born is framed as "input/reduced, not derived" (formalization/ladder/selection/
  open-problems), the H2 "capacity forbids records" reading is retired everywhere (about/born/idea/index), finite
  capacity is the conditional *entropy* chain (not finite matter), and the 1/4 is attributed to Sakharov. So A2
  is mostly the *under*-claim direction. **This pass:** added the missing **Operator-convexity → Lieb → DPI →
  strong-subadditivity** table to `formalization.md` (the Mathlib-grade entropy library, the genuine breadth the
  audit surfaced). Website builds green (66 pages). Remaining A2 (later passes): a light "re-derivation of
  standard Sakharov" note on the 1/4; a scale line (296 files / budget 0); verify the BW "cited" caveat isn't
  stale-underclaiming now that one-particle BW is unconditional.
- **2026-06-30 — A1 ✅ FULLY DONE** (closed the remaining tail items): fixed the stale *under*-claiming
  P4-WALL comments in `AxiomAudit.lean` — three "e.s.a. = the carried analytic frontier" parentheticals
  (4888/4897/4907) now read "DISCHARGED downstream: clockEnergy/momentumOp/modularGen_isSelfAdjoint" (those
  generators ARE proved self-adjoint at 5058–5075), and the "Remaining: the criterion itself (Cayley
  transform)" note (5056) now records that the self-adjointness criterion IS discharged (basic Range(A±i)=H
  form, no Cayley). Corrected the two stale `#print axioms` "expected" annotations (216–220) from "standard +
  4/5 sub-axioms + abstract Step-1 axiom" → **"standard ONLY (verified)"** — confirmed by an actual `#print
  axioms` probe: both `canonical_ic_measure_principle` and `step1_via_sub_lemmas` depend on **only** the
  standard three. Also fixed the matching stale narrative inside `GoldsteinStruyveStep1.lean` (the header /
  docstring still called `step1_schur_classification` "the single remaining interface axiom" — it was
  DISCHARGED by the proved `schur_classification_real`). `SakharovRatio.sakharov_ratio` was already pinned
  (AxiomAudit:6266). Both touched modules build green (8885 jobs); budget-check **0**, no regressions, only the
  one documented `le _ _ := True` indiscrete-preorder site. A1 PASS = no stale "axiomatized"/"frontier"
  under-claims on proved results; terminal theorems pinned & verified.
- **2026-06-30 — A2 ✅ DONE** (website remaining refinements, all 3 landed): (1) fixed a genuinely **stale**
  internal inconsistency in `formalization.md`'s GR honest-scope note — it still listed "the Bisognano–Wichmann
  package" among the *cited* inputs and called matter conservation "a physical postulate," contradicting the
  same page's body (BW is "a fully unconditional Lean theorem"; conservation is "*derived* for the KG stress
  tensor") and the inventory (§3: for the free field the BW/modular flux is **[AF]**, the genuine cited inputs
  are the **area law + localization map**). Rewrote the note so the free-field showcase's three labelled inputs
  are correctly the matter EoM (KG) + P4 capacity + localization map (Gap 2); the modular/BW/Raychaudhuri/
  conservation content is "drained into theorems"; the *algebraic* wedge-KMS package is cited **only** for the
  general interacting algebra. (2) Made the 1/4's "**re-derivation** of standard induced-gravity, not unique to
  finiteness" explicit in `theory.md` (§0 #3) — it already cited Susskind–Uglum/Solodukhin; now says so in the
  §0 words. (3) Added the **scale line** (≈296 files / ~3,300 theorems / budget 0) to the formalization intro
  (§0 #6, credit the breadth). Website builds green (66 pages). A2 PASS = pages map to inventory entries with
  matching qualifiers; the one stale GR-note under/over-claim fixed; breadth credited.
- **2026-06-30 — A3 ✅ DONE** (paper `QIQT_Foundations_Paper.md`, section by section vs inventory). Survey
  finding (as with the site): §1.1a is already heavily revised and aligned — full H2-retraction paragraph, the
  Lorentz fork frontier (~10–20%), P4-MICRO area-floor-as-theorem, the 1/4-as-Sakharov framing, (P1)–(P5) with
  λ+decoherence. So A3 was mostly mopping up **residual stale spots** the §1.1a revision didn't reach. Fixes,
  all inventory-aligned: **(1)** corrected the **stale audit numbers** in *two* places (abstract + §11.4 banner):
  "830 directives / 192 modules / ~2,010 theorems" → the verified "**2,213 directives / 256 modules**, within
  **296 files / ~3,450 theorems**" (counted directly). **(2)** Removed the **retired Macroscopic Definiteness
  Conjecture** from every place it was still listed as an *open problem / open postulate*: abstract open-problems
  list, §11.2a status table (1203), the §11.2a research-agenda sentence (1198), and noted OP2's purpose-clause
  ("feeds Open Problem 3") is void since OP3 is withdrawn. **(3)** Fixed the **uncovered "capacity forbids a
  ≥2-record state" / "finite-information restriction makes single-ness" overclaims** that lacked a retraction
  pointer — §6.4 (462, a bolded assertion), §6.8 (added a banner + fixed 541), §6.10 (592), §7.5, §10.1 (1041),
  §10.6 (1061), §11.1 summary (1138), and the final summary (1632) — each rewritten to the λ+decoherence account
  (capacity is kinematic, single-ness is λ's role), so the paper is now **internally consistent** on the
  retraction (the §7.6 body stays under its existing banner as historical record). **(4)** §1.2 → λ+decoherence
  framing + "four open problems." **(5)** Credited the **Lieb/DPI/SSA tower** in the formal-verification
  paragraph (the axiom-free operator-convexity → Lieb → DPI → strong-subadditivity tower, `QIQTH/Entropy/`, 19
  files — verified count — the Mathlib-grade breadth, §0 #6). A3 PASS = the paper's claims map to inventory
  entries with matching qualifiers; the audit numbers, the H2 retraction, the open-problem set, and the
  formal-verification scope are all consistent.
- **NEXT → A4 (build CLAIMS_LEDGER.md: each headline public claim → inventory entry + status; final consistency pass).**
