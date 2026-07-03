# THE REPRESENTATION (R1–R9): tower-GNS — the corner tower on ONE Hilbert space

**Status:** ACTIVE (2026-07-05). **FABLE-5-CONSULT-VERIFIED (self-consult, high reasoning; every
load-bearing Mathlib name READ in the pinned sources)** — binding verdict below. **Goal:** put the
T5/T7 corner tower on one Hilbert space via the GNS of the compatible Gibbs states and instantiate
C9's `limitVN` — the genuine directed-union limit von Neumann algebra of the code tower
(`towerLimitVN`), with a cyclic vector implementing every corner Gibbs state. THE OBJECT THE
TOWER + CLOSURE CAMPAIGNS WERE BUILT FOR. Its TYPE is NOT classified (the T3 III₁ fingerprint
stays arithmetic; AW 1968/Connes 1973 stay cited). Files under `lean/mathlib/QIQTH/TowerGNS/`,
namespace `QIQTH.TowerGNS`.

## Binding verdict (from the consult — never violate)

- **DECISIVE DISCOVERY:** the pin contains `Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`
  (PreGNS → Core → seminormed → ofCore → Completion; `ContinuousLinearMap.completion` lifting;
  `induction_on` + `isClosed_eq` + `fun_prop` for laws on the completion; `eq_adjoint_iff` for
  star). NOT directly applicable (needs one C*-algebra; the tower has none) but EVERY instance
  pattern and proof incantation is to be copied from it verbatim.
- **A1 — Pre-Hilbert vehicle: the DIRECT SUM with a SEMIDEFINITE form** — no quotient, no setoid,
  no Module.DirectLimit. `TowerPre := ⨁ (C : Finset M), DiamondAlg L C` with the stabilized
  pairing `pairInner C C' a b := stateOf (gibbsDensity (C ⊔ C')) ((cornerEmbed … a)ᴴ *
  (cornerEmbed … b))` (conjugate-linear FIRST slot — Mathlib's Core convention). The form is
  DELIBERATELY degenerate (of C' (ι a) − of C a is null): the degeneracy IS the direct-limit
  gluing, and the whole chain is seminorm-tolerant — `PreInnerProductSpace.Core` (no definiteness
  field), `InnerProductSpace.Core.toSeminormedAddCommGroup`, `InnerProductSpace.ofCore`,
  `UniformSpace.Completion.innerProductSpace` + `inner_coe`, `NormedAddCommGroup (Completion E)`
  (all verified in the pin). Module.DirectLimit REJECTED (no inner product/topology; double-lift
  descent friction).
- **A2 — Index: ALL of Finset M** (the cofinal-ℕ cut REVOKED — generality is free): only
  `SemilatticeSup`, `OrderBot` (∅ for Ω), `Nonempty`, `DecidableEq (Finset M)` are used; the
  stage-collapse takes K := support-sup ⊔ …. ℕ-instantiation (the QIQT frequency tower) is a
  COROLLARY in R9.
- **A3 — Global inner product via `DirectSum.toAddMonoid` outside / `toModule` inside — NO
  DFinsupp.sum in DEFINITIONS** (decidability only in proofs, `classical`/local).
- **A4 — Positivity/estimates via STAGE COLLAPSE:** `collapseₗ K := toModule (fun C => if h :
  C ⊆ K then cornerEmbedₗ else 0)`; `inner_eq_collapse` (supports under K ⟹ towerInner =
  per-stage gnsInner of collapses); per-stage positivity via `Matrix.trace_mul_cycle` +
  `PosSemidef.mul_mul_conjTranspose_same` + `.trace_nonneg` + `RCLike.nonneg_iff` (the recipe of
  `Analysis/Matrix/Order.lean:299`).
- **A5 — Boundedness constant: the FROBENIUS bound `c a := re (trace (aᴴ a))` — NOT the C*-norm**
  (`‖π a‖ ≤ ‖a‖_op` CUT: the pin has NO bundled `CStarAlgebra (Matrix n n ℂ)` — verified absent;
  π is bounded, NOT claimed contractive/isometric). Route: (1) `(c a • 1 − aᴴa).PosSemidef` via
  `PosSemidef.of_dotProduct_mulVec_nonneg` + row Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`);
  (2) PSD transport through cornerEmbed: `open scoped MatrixOrder`, `∃ B, q = star B * B` from
  `CStarAlgebra.nonneg_iff_eq_star_mul_self` (UNBUNDLED CFC context — verified applied to matrices
  at Analysis/Matrix/Order.lean:141), then embed and `posSemidef_conjTranspose_mul_self`; FALLBACK:
  `StarOrderedRing.nonneg_iff` + `AddSubmonoid.closure_induction` (needs only scoped
  instStarOrderedRing, no CFC); (3) stage-K conjugation `PosSemidef.conjTranspose_mul_mul_same` +
  the held `trace_diagonal_mul` + `PosSemidef.diag_nonneg` + `gibbsWeight_pos`.
- **A6 — Operator recipe: `LinearMap.mkContinuous` then `ContinuousLinearMap.completion`** (NOT
  .extend — kept as documented fallback). `π_preₗ a := toModule (fun C => lof (C₀ ⊔ C) ∘ₗ
  mulLeft (cornerEmbed a) ∘ₗ cornerEmbedₗ)`; laws on the completion by the GNS-file incantation
  (`induction … using Completion.induction_on with | hp => apply isClosed_eq <;> fun_prop
  | ih => simp […]`); star via `ContinuousLinearMap.eq_adjoint_iff`.
- **A7 — THE GERM IDENTITY is the compatibility engine:** `towerGerm : ↑(of C' (cornerEmbed … a))
  = ↑(of C a)` in TowerGNS — difference has seminorm 0 (four pairInner terms all = φ_C(aᴴa) by
  state compatibility); everything downstream (π-compat, map_one, range mono) = germ + density.
- **A8 — Ω := ↑(of ∅ 1)** (no Unique (Micro ∅) needed; ⟪Ω,Ω⟫ = 1 from `sum_gibbsWeight_one`).
  Capstone: `towerLimitVN := limitVN (fun C => (towerRep C).range) (Monotone.directed_le …)`.
- **A9 — Honest naming:** TowerPre/TowerGNS/towerRep/towerCyclicVec/towerLimitVN/towerVectorState.
  FORBIDDEN in names: ITPFI, AW, Powers, III₁, "factor".
- **A10 — CUTS (final):** any type/factor classification (mandatory); Ω separating/faithfulness
  for the LIMIT algebra (needs commutant/modular theory — no cheap route; per-stage faithfulness
  may be a stage lemma only); isometry/contractivity of π; GNS uniqueness; separability;
  modular-flow transport to TowerGNS (the named FOLLOW-UP hook — one checkpoint sentence).

## Increments (deps: R1→R2→R3→R4; R5 independent after R1/R2; R6 needs R3+R5; R7 needs R4+R6; R8 needs R7; R9 needs R7+R8)

- [x] **R1 — `QIQTH/TowerGNS/EmbedTrans.lean`** ✅ DONE: tower transitivity (the ONE missing T7 lemma) —
  `restrictMicro_trans`; `sameOffSub_split` (C ⊆ C' ⊆ C'': sameOffSub factorization);
  **`cornerEmbed_trans`**; `cornerEmbedₗ` (linear bundling from held add/smul); `cornerEmbed_sub`.
  Proof style = landed cornerEmbed_one/_mul. Risk LOW.
- [x] **R2 — `QIQTH/TowerGNS/StageInner.lean`** ✅ DONE: the per-stage GNS form — `gnsInner K x y :=
  stateOf (gibbsDensity K) (xᴴ * y)`; `gnsInner_conj_symm` (trace_conjTranspose + diagonal-real
  density), `gnsInner_re_nonneg` (A4), add/smul, `stateOf_posSemidef_nonneg`; `pairInner` +
  **`pairInner_embed`** (stability under a common K — uses R1). Risk LOW-MEDIUM.
- [ ] **R3 — `QIQTH/TowerGNS/PreSpace.lean`**: THE PRE-HILBERT SPACE — `TowerPre` synonym +
  AddCommGroup/Module via `inferInstanceAs`; `towerInnerHom` (A3); `towerCore :
  PreInnerProductSpace.Core ℂ`; instances IN THE EXACT GNS-FILE ORDER
  (`toSeminormedAddCommGroup (c := towerCore …)` BEFORE `ofCore`); `abbrev TowerGNS :=
  UniformSpace.Completion (TowerPre …)`; `towerInner_of_of`; `collapseₗ` + @[simp]
  `collapse_of_le/not_le` + **`inner_eq_collapse`**; `re_inner_nonneg`. Risk MEDIUM (the
  DirectSum bookkeeping increment).
- [ ] **R4 — `QIQTH/TowerGNS/Germ.lean`**: **`towerGerm`** (A7); `towerCyclicVec` +
  `inner_cyclicVec_self` + `norm_cyclicVec`; `inner_coe_of_of` (from Completion.inner_coe).
  Risk LOW.
- [ ] **R5 — `QIQTH/TowerGNS/StageBound.lean`**: the GNS boundedness inequality — `frobBound`
  ((c a • 1 − aᴴa).PosSemidef, A5.1); `cornerEmbed_posSemidef` (A5.2, own section, scoped
  MatrixOrder/ComplexOrder; CFC fallback documented); **`gnsInner_leftMul_le`** (A5.3). Pure
  finite matrix analysis. Risk MEDIUM (the mathematical heart; fully elementary).
- [ ] **R6 — `QIQTH/TowerGNS/LeftMul.lean`**: the bounded pre-operator — `towerLeftMulₗ a` (A6);
  `collapse_leftMul`; the norm bound (R5 + inner_eq_collapse + √-conversion per GNS file
  114-116); **`towerLeftMul a := (towerLeftMulₗ a).mkContinuous …`**. Risk MEDIUM.
- [ ] **R7 — `QIQTH/TowerGNS/Representation.lean`**: **`towerRep C : DiamondAlg L C →⋆ₐ[ℂ]
  (TowerGNS →L[ℂ] TowerGNS)`** via `(towerLeftMul a).completion`; laws by the GNS-file induction
  pattern (map_one needs towerGerm); map_star via eq_adjoint_iff + the pre-level trace identity;
  **`towerRep_cornerEmbed`** (π_{C'} ∘ ι = π_C — germ + density). Risk MEDIUM.
- [ ] **R8 — `QIQTH/TowerGNS/CyclicVector.lean`**: **`towerRep_inner_cyclicVec`** (⟪Ω, π_C(a)Ω⟫ =
  φ_C(a)); `towerRep_cyclicVec_of` (π_C(a)Ω = ↑(of C a), via C ⊔ ∅ = C + cornerEmbed_one);
  **`dense_span_towerRep_cyclicVec`** (span ⊇ image of every of C x ⟹ all of TowerPre via
  sum_support_of; close with Completion.denseRange_coe). Risk LOW.
- [ ] **R9 — `QIQTH/TowerGNS/LimitVN.lean` + `Checkpoint.lean`: CAPSTONE + checkpoint** —
  `towerStageAlg C := (towerRep C).range`; `towerStageAlg_mono`; **`towerLimitVN :
  VonNeumannAlgebra (TowerGNS L ω β) := limitVN towerStageAlg (….directed_le)`**;
  `mem_towerLimitVN_iff`; the towerVectorState restriction lemma; the ℕ-instantiation (the QIQT
  frequency tower); checkpoint module with the HAVE/HAVE-NOT sentences VERBATIM + inventory;
  plan → COMPLETE; delete the loop; stop. Risk LOW.

## Checkpoint sentences (verbatim at R9)

HAVE: "One Hilbert space — the completion of the semidefinite Gibbs-GNS pre-space on the direct
sum of all finite corners — carrying compatible unital ⋆-representations of every corner algebra
(π_{C′} ∘ cornerEmbed = π_C for all C ⊆ C′), a unit cyclic vector Ω implementing every corner
Gibbs state as a vector state (⟪Ω, π_C(a)Ω⟫ = φ_C(a)), and the directed-union limit von Neumann
algebra towerLimitVN = limitVN of the representation images, with membership characterized by
SOT-approximation from the finite stages — all axiom-free."

HAVE NOT: "The type of towerLimitVN is not classified — no factor, no ITPFI identification, no
III₁ claim is made or proved (the T3 fingerprint stays arithmetic; Araki–Woods 1968 and Connes
1973 stay cited, never invoked); Ω is not shown separating, the modular theory of the limit state
on the completion is not constructed, and the representations are not shown isometric."

## Top-5 predicted failure modes (consult; mitigations binding)

1. **Instance diamonds on TowerPre:** ONE path only — copy GelfandNaimarkSegal.lean:55-86 order
   exactly (`toSeminormedAddCommGroup (c := towerCore)` before `ofCore`); towerCore passed
   explicitly, never a bare escaping instance; DirectSum has no ambient norm/topology in the pin.
2. **DFinsupp.support decidability:** definitions via toAddMonoid/toModule (decidability-free);
   support only inside proofs (`classical` local); K := support.sup id ⊔ … proof-local.
3. **Completion coercion friction:** pre-level facts through plain ↑; completion side ONLY via
   the simp kit (completion_apply_coe, inner_coe, coe_add/sub/smul, norm_coe); the literal
   GNS-file induction incantation; `UniformSpace.Completion.Continuous.inner` if fun_prop stalls;
   never unfold TowerGNS past the abbrev.
4. **The dite in collapseₗ blocking rewrites:** immediately @[simp] collapse_of_le/not_le, never
   unfold collapseₗ again; `of`-level computations, sums via map_sum; lof vs of bridged by
   lof_eq_of.
5. **CFC/order synthesis on Matrix (Micro L C) … (R5):** isolate section, exact opens of
   Analysis/Matrix/Order.lean (scoped MatrixOrder ComplexOrder); FALLBACK StarOrderedRing.nonneg_iff
   + closure_induction (no CFC); NEVER touch le_algebraMap_norm_self / star_left_conjugate (need
   bundled CStarAlgebra — absent for matrices, verified).

## Discipline (every increment)

`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.TowerGNS.<Mod>` green; `#print axioms` = standard
3; `bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit on
main with trailer `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this plan's checklist + Progress log
AND LEAN_RESULTS_INVENTORY.md. NO sorry; carried inputs as hypotheses NEVER Lean axioms; NEVER
claim a type classified, an ITPFI identification, Ω separating, or the continuum done — this
builds THE OBJECT, not its classification; NEVER claim an increment too hard (attempt, iterate,
checkpoint only after a genuine failed attempt with the error shown); check sibling jobs before
each increment; explicit git paths only. Consults: Agent tool (fable) high reasoning or
mcp__OpenAI__ask gpt-5.5-pro (never expose keys).

## Progress log

- **2026-07-05** — Campaign scoped; high-reasoning self-consult complete (all API names READ in
  the pin; decisive discovery: Mathlib's own GelfandNaimarkSegal.lean is the instance-architecture
  template — Core → seminormed → ofCore → Completion, CLM.completion, the induction incantation;
  the C*-norm contractivity CUT — no bundled CStarAlgebra (Matrix n n ℂ) in the pin, Frobenius
  bound instead; the cofinal-ℕ cut REVOKED — all of Finset M is free). Binding verdict recorded;
  loop armed.

- **2026-07-05** — **R1 LANDED** (`QIQTH/TowerGNS/EmbedTrans.lean`, axiom-free std-3/std-2,
  budget 0, one iteration — `simp only [cornerEmbed_apply]` unfolds ALL occurrences incl. the
  RHS; plain `rw` leaves the RHS untouched in the neg branch): `restrictMicro_trans` (funext
  rfl); **`sameOffSub_split`** (off-C agreement at C″ ⟺ off-C′ agreement + off-C agreement of
  the restrictions — the Subtype.ext cast bridged explicitly); CAPSTONE **`cornerEmbed_trans`**
  (the tower is a FUNCTOR on the directed corner order); `cornerEmbedₗ` (linear bundling) +
  `cornerEmbed_sub`/`_zero` (via map_sub/map_zero). NEXT → R2 (StageInner).

- **2026-07-05** — **R2 LANDED** (`QIQTH/TowerGNS/StageInner.lean`, axiom-free std-3, budget 0,
  three iterations): **`gnsInner K x y := φ_K(xᴴy)`** — conj symmetry (trace_conjTranspose +
  diagonal-real ρ + trace cycle), **POSITIVITY** `gnsInner_self_nonneg` (the A4 recipe:
  trace_mul_cycle → tr(x ρ xᴴ) → PosSemidef.mul_mul_conjTranspose_same → trace_nonneg, in
  scoped ComplexOrder), add/smul both slots, `stateOf_posSemidef_nonneg` (diagonal weights +
  diag_nonneg); **`pairInner`** + CAPSTONE **`pairInner_embed`** (stage stability via a
  self-contained `key` ∀-lemma — rw on the big goal hits the WRONG star-occurrence). Lean notes:
  `ᴴ` needs `open scoped Matrix` (again!); Finset lattice names are `Finset.subset_union_left/
  union_subset` (le_sup_* don't exist on Finset); `rw [stateOf]` fails ("equation theorems") —
  use `simp only [gnsInner, stateOf, …]`. NEXT → R3 (PreSpace — the DirectSum bookkeeping).
