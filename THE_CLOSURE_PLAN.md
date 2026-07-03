# THE CLOSURE (C1–C10): the von Neumann bicommutant/density theorem

**Status:** ACTIVE (2026-07-04). **FABLE-5-CONSULT-VERIFIED (self-consult, high reasoning; all API facts
verified against the pinned Mathlib)** — binding verdict below. **Goal:** the single highest-leverage
missing lemma of the continuum program — the double-commutant theorem `A″ = SOT-closure(A)` for unital
⋆-subalgebras of B(H) — the convergent blocker named FOUR times in the inventory (vN closure of the
crossed product; `DualWeightTraceExtension`; the Fock Klein-twist commutant theorem; the
`VonNeumannAlgebra` packaging of `CrossedProductCovariance`), and the gate to the ITPFI limit algebra
of THE TOWER's cornerEmbed refinement tower. A genuine Mathlib-gap contribution candidate (Mathlib's
`VonNeumannAlgebra` is topology-free; no SOT, no bicommutant theorem exists there).
Files under `lean/mathlib/QIQTH/VonNeumann/`.

## Binding verdict (from the consult — never violate)

- **D1 — SOT: concrete predicate primary; NO topology type copy.**
  `SOTApprox (A : Set (H →L[ℂ] H)) (T) : Prop := ∀ (n : ℕ) (ξ : Fin n → H), ∀ ε > 0, ∃ a ∈ A, ∀ i,
  ‖T (ξ i) - a (ξ i)‖ < ε`. LOAD-BEARING quantifier order (document): ONE `a` uniform over the whole
  tuple, ε after ξ — a per-i witness is vacuous and useless downstream. No `ContinuousLinearMapSOT`
  type copy (a PR-sized instance tower buying nothing; Mathlib's vN definition is topology-free, so
  the predicate form aligns with what we must inhabit). WOT link = exactly ONE increment (C10), last,
  pre-authorized cut.
- **D2 — Amplification: `PiLp 2 (fun _ : Fin n => H)`.** No tensor products, no induction trick.
  Do NOT prove `(diag A)' ≅ Mₙ(A')` — prove exactly TWO lemmas against a frozen six-lemma interface
  (`ι i`, `π i = adjoint (ι i)`, `diagCLM`): (entries) `S ∈ centralizer (diagCLM '' A) → π i ∘L S ∘L ι j
  ∈ centralizer A`; (assembly) `T ∈ A″ → (∀ i j entries ∈ A′-centralizer form) → Commute (diagCLM T) S`,
  via the entrywise extensionality lemma. One nontrivial star fact: `adjoint (diagCLM a) = diagCLM
  (adjoint a)` via `eq_adjoint_iff` + `PiLp.inner_apply`.
- **D3 — Hypothesis format: `A : StarSubalgebra ℂ (H →L[ℂ] H)`** — unitality and ⋆-closure ride in the
  type (document as where the load-bearing hypotheses live). State centerpiece at `Set.centralizer`
  level (plugs into `VonNeumannAlgebra.centralizer_centralizer'`). Glue already in Mathlib:
  `Set.star_mem_centralizer'`, `StarSubalgebra.centralizer`, `Set.centralizer_centralizer_centralizer`.
- **D4 — Reuse, don't re-derive:** `Submodule.starProjection` (+`range_`, `ker_`, `_eq_self_iff`,
  `isStarProjection_`), `ContinuousLinearMap.IsIdempotentElem.commute_iff`,
  `ContinuousLinearMap.orthogonal_mem_invtSubmodule`. C1 is ~30 lines, not projection-theory.
- **D5 — CUTS (final):** Kaplansky density; normal states / normality on the closure; predual /
  σ-weak / `WStarAlgebra`; the SOT type copy; DEFER the tower-GNS Hilbert space (separate campaign) —
  payoff (i) ships in the honest hypothesized-common-representation form (C9). NO claim the
  crossed-product dual-weight trace extends to the weak closure — packaging only.
- **D6 — Centerpiece names:** `mem_centralizer_centralizer_iff_sotApprox` (iff),
  `centralizer_centralizer_eq_setOf_sotApprox` (set form), alias `vonNeumann_double_commutant`.
  No theorem name says "WOT-closure" unless it literally proves it (C10:
  `wotClosure_image_eq_image_bicommutant`).
- **Counterexample comments (load-bearing hypotheses):** ⋆-closure — upper-triangular 2×2 A (unital,
  norm-closed, not ⋆): span(e₁) invariant but its projection ∉ A′ = ℂ·1, A″ = B(ℂ²) ⊋ A. Unitality —
  A = {0}: A″ = ℂ·1 ≠ {0} = SOT-closure; the ξ = Pξ step dies without 1 ∈ A. Converse needs n = 2 —
  n = 1 approximability is NOT enough (the `S x` vector is the second tuple entry).

## Increments (dependency: C1→C3→(C4→C5)→C6→C7; C2 independent; C8, C9 need C2+C7; C10 needs C7)

- [x] **C1 — `QIQTH/VonNeumann/InvariantProjection.lean`** ✅ DONE: `orbitSubmodule`/`orbitClosure` (with the
  local `HasOrthogonalProjection` instance ATTACHED AT THE DEFINITION via `IsClosed.completeSpace_coe`);
  `orbitClosure_invariant`; `starProjection_mem_centralizer` (invariance of U and Uᗮ via ⋆-closure +
  `IsIdempotentElem.commute_iff`). The ⋆-closure counterexample comment. Risk LOW.
- [x] **C2 — `QIQTH/VonNeumann/GeneratedBy.lean`** ✅ DONE: purely algebraic `VonNeumannAlgebra.generatedBy`
  (double `StarSubalgebra.centralizer`; bicommutant field from `centralizer_centralizer_centralizer` +
  star-collapse); `subset_generatedBy`, `generatedBy_le` (minimality), `generatedBy_carrier`,
  `centralizer_adjoin` (Galois, via `adjoin_induction`); the C2 bridging lemma `Set.centralizer A =
  ↑(StarSubalgebra.centralizer ℂ A)` for star-closed carriers (HOUSE RULE: theorem statements use
  `Set.centralizer`; StarSubalgebra.centralizer only inside proofs). Risk LOW.
- [x] **C3 — `QIQTH/VonNeumann/DensityOne.lean`** ✅ DONE: `bicommutant_apply_mem_orbitClosure` (P ∈ A′ → TP=PT
  → ξ = Pξ by UNITALITY → Tξ ∈ U) + ε-corollary. The unitality counterexample comment. Risk LOW.
- [ ] **C4 — `QIQTH/VonNeumann/Amplification.lean`** (THE risk lump, scheduled after C1–C3 are banked):
  the frozen six-lemma PiLp interface — `π_comp_ι_same`, `π_comp_ι_ne`, `sum_ι_π`, `adjoint_ι`,
  `π_comp_diag`, `diag_comp_ι` — plus `diag_one`, `diag_mul`, `adjoint_diag`, `clm_ext_of_entries`,
  `norm_coord_le`. NEVER unfold the synonym; route through `PiLp.continuousLinearEquiv`/`PiLp.single`/
  `PiLp.inner_apply`; later files are INTERFACE-ONLY. Fallback: define `ι i` as a hand-rolled
  `LinearIsometry`. Risk MEDIUM.
- [ ] **C5 — `QIQTH/VonNeumann/MatrixCommutant.lean`**: the two minimal matrix-commutant lemmas
  (entries + assembly); `diagAlg` (via `StarSubalgebra.copy` on the image so membership is
  definitionally `∃ a ∈ A, diagCLM a = _`); `diag_mem_bicommutant`. Risk LOW-MEDIUM.
- [ ] **C6 — `QIQTH/VonNeumann/DensityN.lean`**: `bicommutant_sotApprox` (C3 in Hⁿ on `diagAlg` +
  `diag_mem_bicommutant`; orbit element `diagCLM a v` has coordinates `a (ξ i)`; finish with
  `norm_coord_le`). Risk LOW.
- [ ] **C7 — `QIQTH/VonNeumann/Bicommutant.lean` — THE CENTERPIECE**: `SOTApprox` def +
  `mem_centralizer_centralizer_iff_sotApprox` / `centralizer_centralizer_eq_setOf_sotApprox` /
  `vonNeumann_double_commutant`. Converse via the n = 2 tuple `![x, S x]`:
  `‖(TS − ST) x‖ ≤ ‖(T−a)(S x)‖ + ‖S‖·‖(a−T) x‖`. Corollaries: `sotApprox_bicommutant_iff`
  (idempotence), `generatedBy_carrier_eq`. KEEP MATHLIB-STYLEABLE (imports only Mathlib + C1–C6,
  which themselves import only Mathlib). Risk LOW.
- [ ] **C8 — `QIQTH/VonNeumann/CrossedProductClosure.lean`** (payoff ii): `crossedProductVN :=
  generatedBy (range matterRep ∪ translations)` on the project's L²(ℝ;H); membership lemmas; scope
  banner: PACKAGING ONLY — the dual-weight trace is NOT claimed to extend to this closure. Risk LOW.
- [ ] **C9 — `QIQTH/VonNeumann/DirectedUnionVN.lean`** (payoff i, honest form): `limitVN :=
  generatedBy (⋃ i, Aᵢ)` for a directed family; `T ∈ limitVN ↔ SOTApprox (⋃ i, Aᵢ) T`
  (directed union is a ⋆-subalgebra; `sotApprox_adjoin_eq_sotApprox_self`). SCOPE BANNER (binding):
  the DiamondAlg tower has no common Hilbert-space representation yet — this packages the limit for
  ANY hypothesized common representation; instantiation awaits the deferred tower-GNS campaign.
  Risk LOW.
- [ ] **C10 — `QIQTH/VonNeumann/WOTClosure.lean`** (STRETCH; PRE-AUTHORIZED CUT):
  `wotClosure_image_eq_image_bicommutant` in `H →WOT[ℂ] H` via `precompCLM`/`postcompCLM` +
  `isClosed_eq` (T3 from `SeparatingDual`), SOTApprox beats every WOT seminorm. Every statement lives
  wholly in the WOT copy about `ofCLM '' ·`; separate continuity only. CUT LINE: one session without
  green → drop; nothing depends on it. Risk MEDIUM.
- [ ] **C11 — checkpoint**: the campaign HAVE/HAVE-NOT sentences VERBATIM (below) in a checkpoint
  module docstring + LEAN_RESULTS_INVENTORY.md; plan → COMPLETE; delete the loop; stop.

## Checkpoint sentences (verbatim at C11)

HAVE: "We have the von Neumann double-commutant theorem as an axiom-free Lean theorem over current
Mathlib — for every unital ⋆-subalgebra A of the bounded operators on a complex Hilbert space, the
double centralizer A″ equals the set of operators approximable from A in norm on every finite tuple
of vectors (and, in the shipped WOT increment, the weak-operator closure) — packaged as
`VonNeumannAlgebra.generatedBy` with membership lemmas, and instantiated to present the project's
crossed-product representation and any commonly-represented refinement tower as genuine
`VonNeumannAlgebra`s."

HAVE-NOT: "We do not have Kaplansky density, normal states, preduals or the σ-weak topology, type
classification, or the inductive-limit (tower-GNS) Hilbert space — the ITPFI tower's limit algebra is
packaged only relative to a hypothesized common representation, and the crossed-product dual-weight
trace is not claimed to extend from the algebraic core to the weak closure."

(If C10 is cut, DELETE the parenthetical WOT clause from the HAVE sentence — never ship it unproved.)

## Top-5 predicted failure modes (consult; mitigations binding)

1. **PiLp synonym friction (C4):** never unfold; interface-only downstream; LinearIsometry fallback
   for `ι i`.
2. **`HasOrthogonalProjection` not found on orbit closures:** attach the instance at the
   `orbitClosure` definition; `haveI` completeness in Hⁿ lemma scopes.
3. **`Set.centralizer` vs `StarSubalgebra.centralizer` vs `commutant` drift:** the C2 bridging lemma +
   house rule (statements = `Set.centralizer` only).
4. **`star` vs `adjoint` on B(H)/B(Hⁿ):** prove `adjoint_diag` once, derive the `star` version via
   `star_eq_adjoint`, use only the star version after; `StarSubalgebra.copy` for `diagAlg`.
5. **WOT type-copy transport (C10):** statements wholly in the copy; `precompCLM`/`postcompCLM` +
   `isClosed_eq` only; scratch-check the `SeparatingDual`/T3 instance first; invoke the cut line.

## Discipline (every increment)

`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.VonNeumann.<Mod>` green; `#print axioms` = standard 3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit on main
with trailer `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this plan's checklist + Progress log AND
LEAN_RESULTS_INVENTORY.md. NO sorry; carried inputs as hypotheses/structure fields NEVER Lean axioms;
NEVER claim the continuum done, a type classified, or a trace extended — this campaign is the GATE,
not the wall crossed; NEVER claim an increment too hard (attempt, iterate, checkpoint only after a
genuine failed attempt with the error shown); check sibling jobs (git log/status) before each
increment; explicit git paths only. Consults: Agent tool (fable) high reasoning or mcp__OpenAI__ask
gpt-5.5-pro (never expose keys).

## Progress log

- **2026-07-04** — Campaign scoped; high-reasoning self-consult complete (all API facts verified
  against pinned Mathlib: `Submodule.starProjection` kit, `IsIdempotentElem.commute_iff`,
  `orthogonal_mem_invtSubmodule`, `StarSubalgebra.centralizer` glue, `PiLp` CLM API,
  `ContinuousLinearMapWOT` + Hilbert specialization all PRESENT; SOT + bicommutant ABSENT = the gap).
  Binding verdict recorded; loop armed.

- **2026-07-04** — **C1 LANDED** (`QIQTH/VonNeumann/InvariantProjection.lean`, axiom-free std-3,
  budget 0): `orbitSubmodule`/`orbitClosure` (the cyclic subspace, `HasOrthogonalProjection`
  ATTACHED AT THE DEFINITION per the verdict — `isClosed_topologicalClosure.completeSpace_coe`);
  `self_mem_orbitSubmodule` (unitality); `orbitClosure_invariant` (`map_mem_closure`); CAPSTONE
  **`starProjection_mem_centralizer`** — the star projection onto a closed A-invariant subspace
  lies in A′ (U-invariance under `star a` ⟹ Uᗮ-invariance under `a` via
  `orthogonal_mem_invtSubmodule`; `IsIdempotentElem.commute_iff` + `range/ker_starProjection`);
  the ⋆-closure counterexample (upper-triangular 2×2) in the docstring. Lean note: the
  `invtSubmodule` membership lemmas take `f` EXPLICITLY — write
  `(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr`, never dot-`.mpr` the ∀. NEXT → C2
  (GeneratedBy).

- **2026-07-04** — **C2 LANDED** (`QIQTH/VonNeumann/GeneratedBy.lean`, axiom-free std-3, budget 0):
  **`VonNeumannAlgebra.generatedBy S := (S ∪ S*)″`** packaged as a Mathlib `VonNeumannAlgebra`
  (bicommutant field = `Set.centralizer_centralizer_centralizer`; `star_mem'` from
  centralizer-of-star-closed); `subset_generatedBy`/`star_subset_generatedBy`; MINIMALITY
  `generatedBy_le` (centralizer antitone twice + the target's bicommutant property); the
  bridging lemmas (`union_star_self_of_starClosed`, `generatedBy_starSubalgebra_coe`); the
  GALOIS lemma **`centralizer_adjoin`** — `(adjoin ℂ S)′ = (S ∪ S*)′` by the PAIR-TRICK adjoin
  induction (motive = commutation with b AND star b; the star case swaps conjuncts). The naming
  layer for the limit algebras — purely algebraic, no density claim. Lean notes: star adjoin is
  `StarAlgebra.adjoin` (not StarSubalgebra.*); `Algebra.commutes` is already `map r * x = x * map r`;
  Set-vs-SetLike membership needs an explicit `have hmem : star x ∈ M`. NEXT → C3 (DensityOne).

- **2026-07-04** — **C3 LANDED** (`QIQTH/VonNeumann/DensityOne.lean`, axiom-free std-3, budget 0,
  one trivial fix): CAPSTONE **`bicommutant_apply_mem_orbitClosure`** — `T ∈ A″ ⟹ Tξ ∈ cl(Aξ)`
  (the C1 cyclic projection P ∈ A′; T commutes with P; **Pξ = ξ by UNITALITY** — the A = {0}
  counterexample in the docstring: A″ = B(H) but cl(Aξ) = {0}, the theorem is FALSE non-unitally);
  plus the ε-form **`bicommutant_apply_approx`** (`Metric.mem_closure_iff` unfold — the form C6
  consumes). C1→C3 chain complete; the campaign now enters THE RISK LUMP (C4, PiLp). NEXT → C4
  (Amplification).
