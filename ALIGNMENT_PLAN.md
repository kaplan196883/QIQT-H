# Alignment plan — make every public claim match the Lean ground truth

**Status:** A1–A4 COMPLETE (2026-06-30) → maintenance mode (re-run on inventory changes). **Ground truth:** `LEAN_RESULTS_INVENTORY.md` (built from a full-coverage,
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
- **2026-06-30 — A4 ✅ DONE; ALIGNMENT COMPLETE.** Built `CLAIMS_LEDGER.md`: ~40 headline public claims (paper +
  site) organized into 8 clusters (substrate meta · Born/λ · capacity/area-floor · gravity/1/4 · modular/BW/OP3b ·
  corner/SM/spacetime · Lieb/DPI tower · CPSUV frontier), each row mapping the public wording → the inventory
  entry (§ + theorem name) → the matching status qualifier ([AF] / [AF·cond:H] / [no-go] / [frontier] /
  [re-derivation]) → aligned ✓. Plus a **final consistency pass**: cross-source agreement table (paper ⇄ site ⇄
  inventory all agree on Born→P5, H2-retired, 1/4=re-derivation, finite=entropy-not-matter, audit scale, BW
  unconditional, the tower credited); an explicit **"claims we deliberately DO NOT make"** boundary (no QG, no
  value of G, no axiom-free area law, no finite-matter, no Born-from-unitarity, no novel-1/4, no CPSUV-escape, no
  done-frontiers); and the tracked residual completeness gap (~55 unpinned terminal theorems, low risk —
  `#print axioms` is transitive). **Verification:** spot-checked 11 cited theorem names — all exist at the cited
  modules (`finitePoincare_trivial`, `area_floor_vonNeumann`, `oneParticleBW_niceWedge_unconditional`,
  `no_covariant_selector`, `sm_free_field_in_corner`, `minCut_area_not_metric`, `positive_ray_certain_forces_born`,
  `stoneGen_isSelfAdjoint`, …) — the ledger is grounded, not phantom citations.
- **— ALL FOUR AREAS COMPLETE (A1 code-comments · A2 website · A3 paper · A4 ledger).** The recurring meta-finding
  across all four: the project was **under-claiming, not over-claiming** — proved self-adjointness/axiom-discharge
  was still labelled "frontier"/"axiom" in docstrings; genuine breadth (the Lieb/DPI tower, unconditional BW,
  budget-0/296-file scale) was uncredited on the site & in the paper; and the H2 retraction (already in §1.1a)
  **had not propagated to the paper body** (the single biggest fix, A3). Public framing is now: *a rigorously
  machine-verified single-world interpretation + a substantial formalized operator-algebra/entropy library +
  induced-gravity re-derivations*, every claim inventory-backed with matching qualifiers. **Maintenance mode:**
  re-run this loop whenever the inventory changes (new Lean results, retractions) to keep code/site/paper aligned.
- **2026-06-30 — A1/A4 follow-up: terminal-coverage pins (closed the audit-coverage gap on the ledger's headline
  capstones).** Probed then pinned 13 sorry-free-but-unaudited terminal theorems in `AxiomAudit.lean`, all verified
  **std-3**: `ValueSelection` actual-value/actual-history terminals (`actualValue_spec`, `actualValue_eq_of_mem`,
  `existsUnique_actualHistory`); the Entropy/ Lieb–DPI tower rungs (`trace_function_convex`, `star_inv_subadditive`,
  `gmean_mono`, `lieb_superadditive`, `dpi_mixed_unitary`, `partial_trace_dpi` — backing ledger G1); the Einstein
  capstones (`Curvature.jacobson_einstein_equation_of_state`, `EinsteinEOS.einstein_tensor_eq_of_state` — ledger
  D2/D3); the crossed-product terminals (`StandardSubspaceModular.covariance`, `modularAut_mul` — ledger E2/E6).
  AxiomAudit builds green (8885 jobs); budget-check **0**, no regressions, only the one documented `le _ _ := True`
  site. Updated `CLAIMS_LEDGER.md`'s residual-gap note: the headline terminal capstones are now individually pinned;
  what remains unpinned is minor, non-headline, and transitively certified.
- **2026-06-30 — maintenance drift-check (A2): homepage 1/4 sharpened.** Swept ALL site pages (incl. the not-yet-
  individually-audited `papers`/`reach`/`statements`/`browser`) for overclaim/retired patterns — all clean
  (every "forbids/derive/QG" hit resolves to a correct retraction notice or honest denial; the "830"/"932"
  matches are auto-generated theorem *numbers*, not stale audit counts). One genuine sharpening found: the
  **homepage** (`index.astro`, highest-visibility) called the 1/4 "derived (Sakharov bridge)" but — unlike
  `theory.md` — lacked the §0 #3 qualifier. Added the matching "machine-checked **re-derivation** of the standard
  induced-gravity 1/4, *not* unique to finiteness" clause to its detailed gravity section. Website builds green
  (66 pages). No other drift.
- **2026-06-30 — maintenance pass: full-paper sweep + cross-source number reconciliation.** Swept the whole
  paper for overclaim/stale patterns — clean (the two "derives Born"/"finite matter" hits are honest: a true
  remark *about Gleason's theorem* explicitly disclaimed as not QIQT-H's route, and the honest fork-dilemma
  framing). Confirmed **no Lean drift**: the only `lean/` commits since the inventory was built (`3eddca2`) are
  the alignment comment/pin commits — no new theorems or retractions, so the inventory is still current ground
  truth. Found + fixed one **cross-source number inconsistency I introduced**: the paper said "~3,450 theorems"
  (my A3 count *including* `@[…] theorem` attributed forms) while the inventory + website say "~3,300" (the
  line-start `theorem|lemma` count = 3,320). Aligned the paper (2 spots) and the ledger (2 spots) **down** to the
  reference figure "~3,300", so the inventory, website, paper, and ledger now all read identically: **296 files /
  ~3,300 theorems / 2,213 `#print axioms` directives / 256 modules / budget 0**.
- **2026-06-30 — maintenance (A2): fix the "what is postulated" conflation on the explainer pages.** Prompted by a
  live correction (the postulate is *finiteness*, NOT the holographic bound — P4-MICRO). The homepage
  (`index.astro`) was already correct (lines 53/132/165/219/311: "postulate is finiteness only; the area form
  and floor are derived"). But `idea.md`'s primary "The hypothesis" section still bundled the area form into the
  postulate ("finite capacity… $Q_R=A/4\ell_P^2$… Finite, as a postulate") — the exact pre-P4-MICRO conflation.
  Rewrote it: *finiteness* ($N_R<\infty$) is the postulate; the area **form** $Q_R=A/4\ell_P^2$ is *derived*
  (Sakharov bridge), $G$ is carried, and the area **floor** $S_{\mathrm{vN}}\le Q_R$ + the 1/4 are *theorems*.
  Also aligned `formalization.md`'s GR-showcase `hcap` row ("postulate P4, $Q_R=A/4\ell_P^2$" → "finite-capacity
  input — finiteness postulated, area form derived") and added a P4-MICRO cross-reference to the `ladder.md`
  pedagogy note. Website builds green (66 pages). (Paper abstract has the parallel issue — fixed next as A3.)
