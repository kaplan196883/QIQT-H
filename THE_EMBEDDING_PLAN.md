# THE EMBEDDING (EM1–EM7): the matter-side dictionary — the truncated field diamond IS a counted record corner

**Status:** ACTIVE (2026-07-03). **GPT-5.5-pro-VERIFIED** (binding verdict below). **Goal:** complete the
finite-level bridge on the matter side — give the keystone's already-counted `DiamondAlg L C` its FIELD
structure (per-mode truncated oscillators, number operators, records = occupation pointer basis) and the
mode↔link dictionary semantics, so the count READS as "the N-mode truncated free-field diamond's entropy
= area/4G", composing end-to-end with the join instance (field → corner → count → area → graviton).
KEY OBSERVATION: `Micro L C = (e : C) → Fin (D e)` IS a multi-mode truncated Fock basis — do NOT build a
new Hilbert space; add operators and semantics to the counted object. New file
`lean/mathlib/QIQTH/Embedding.lean`.

## Binding verdict (from the consult — never violate)
- **Direct-entry `modeOp`, NOT Kronecker induction:** `modeOp k A (m,n) := if (∀ j ≠ k, m j = n j) then
  A (m k) (n k) else 0`; `a_k := modeOp k (lowering (D k))`. Prove the transport package
  (`modeOp_map_one/mul/add/smul/star`, `modeOp_injective`) and NEVER unfold `lowering` for multi-mode
  commutators — transport the held single-mode theorems through the package. The Kronecker/Finset-induction
  route is CUT (brittle: tensor order, reindex, dependent Fin casts).
- **Cross-mode commutativity is ONE generic theorem** (`modeOp_commute_of_ne`, via a two-coordinate
  "same outside {k,j}" helper) — derive ladders/adjoints/number-operator cases, never reprove per case.
- **Records = occupation projectors:** `occupationProj m` (diagonal rank-one), with
  `sum_occupationProj_eq_one`, `recordProj_eq_sum_occupationProj`, trace/card — "records are occupation
  pointer-basis subsets" as a theorem.
- **No analytic spectrum API:** the number operator's "spectrum {0..D_k−1}" is the finite
  diagonal/eigenbasis pair (`numberOp_apply_diag`, `occupationProj_joint_eigen`), nothing more.
- **Corner transport:** the encoded commutator's identity is `P = VVᴴ`, NOT global 1 —
  `[encode V a_k, encode V a_k†] = P − D_k • encode V (P_top,k)`.
- **Localization is NAMED finite data** (`ModeAssignment`: mode type + cutoffs, cutoff_pos), with at most
  a SUPPLIED `LocalizedModeFrame` witness (one-particle vectors ∈ the standard subspace K) CERTIFYING
  compatibility — never constructing the modes. The continuum localization map stays the wall.
- **Capacity phrasing:** "capacity selects the admissible/saturating subtype of cutoff assignments" —
  the bound is a hypothesis (`Σ log D_k ≤ A/4G` ⟹ S ≤ A/4G), saturation gives equality for a CHOSEN
  assignment; exact integer saturation for external real area may not exist (never claimed). CAPACITY IS
  A CONSTRAINT, NOT A GENERATOR.
- **The graviton capstone is a dictionary theorem, not new dynamics** — freeze the composition
  (Micro = occupation basis; tauCount = trace; S = Σ log D_k; Σ localModeArea = 4G·Σ log D_k;
  `code_count_eq_fock_area_expect_noJoin`); keep it global (no per-mode graviton expectation).
- **CUT (permanent/non-goals):** exact finite CCR (defect theorem held); Type III₁ finite corners
  (cutoff→continuum limit is THE wall, never claimed); constructing continuum-localized modes; Kronecker
  induction; analytic spectrum; uniqueness/existence of saturating integer cutoffs for arbitrary external
  area; fermionic CAR from naive pi-fiber ladders (different-mode pi-ladders COMMUTE — CAR needs the held
  graded/FreeFieldCorner layer); interactions/renormalization/Gauss law/dynamical graviton equations.
- **Lean traps:** [Fintype C] [DecidableEq C] explicit; `zeroMicro := fun e => ⟨0, L.hD e⟩` for
  injectivity; subtype mode type internally, `Finset.attach` only at boundaries; hide dependent-update
  casts behind lemmas.

## Increments
- [x] **EM1 — the mode dictionary aliases** ✅ DONE (`QIQTH/Embedding.lean`): `ModeAssignment` (mode type + cutoffs + positivity),
  `toLinkDims`, `FieldMicro`/`TruncatedFockBasis`/`FieldDiamondAlg` aliases with the rfl/dictionary
  theorems (the keystone object IS the truncated field object).
- [x] **EM2 — the coordinate operator embedding** ✅ DONE: `sameOff`, `modeOp`, update/default lemmas,
  `modeOp_map_one/mul/add/smul/star`, `modeOp_injective` — each single-mode truncated oscillator algebra
  EMBEDS into the diamond algebra.
- [x] **EM3 — the per-mode oscillator structure** ✅ DONE: `a_k`/`a_k†`/`N_k`/`P_top,k` via `modeOp`; the same-mode
  truncation defect `[a_k, a_k†] = 1 − D_k·P_top,k` (transported, never re-proved); `numberOp_apply_diag`
  + `occupationProj_joint_eigen` (the finite spectrum reading); `[N_k, a_k] = −a_k`, `[N_k, a_k†] = a_k†`.
- [x] **EM4 — the cross-mode algebra** ✅ DONE: generic `modeOp_commute_of_ne`; derived `[a_k, a_j] = [a_k, a_j†]
  = [N_k, a_j] = 0` (j ≠ k).
- [ ] **EM5 — records and the counted corner**: `occupationProj` + `sum_occupationProj_eq_one` +
  `recordProj_eq_sum_occupationProj` + trace/card (records ARE occupation pointer subsets); the encoded
  record trace through τ₀ (keystone flatClock); corner transport `[encode V a_k, encode V a_k†] =
  P − D_k·encode V (P_top,k)`.
- [ ] **EM6 — capacity and local areas**: `capacityBound` (Σ log D_k ≤ A/4G) ⟹ `S(maxMixed) ≤ A/4G`;
  saturation ⟹ equality (chosen assignment); `localModeArea k := 4G·log D_k` + `sum_localModeArea`;
  the mode-count area-bound restatements.
- [ ] **EM7 — the localization witness + the graviton capstone (checkpoint)**: optional supplied
  `LocalizedModeFrame` (certifies, never constructs); CAPSTONE
  `truncated_field_count_eq_fock_area_expect_noJoin` — field → corner → count → area → graviton
  composed end-to-end. Then the checkpoint (the two honest sentences, VERBATIM in the module docstring +
  inventory): HAVE: "the N-mode truncated free-field diamond algebra IS a counted record corner — the
  occupation basis is Micro, the per-mode truncated oscillators embed with their honest defect
  ([a,a†] = 1 − D·P_top), records are occupation projectors, the count S = Σ log D_k = A/4G reads as the
  truncated field diamond's entropy, capacity bounds/saturates the cutoffs as a constraint, and the mode
  dictionary composes with the join instance end-to-end (field → corner → count → area → graviton
  expectation)." HAVE NOT: "no exact finite CCR (the truncation defect is permanent); no Type III₁ finite
  corner (the cutoff→continuum limit is THE wall, never claimed); no construction of continuum-localized
  modes from the standard subspace (mode membership is named finite data, at most CERTIFIED by a supplied
  localization witness); capacity is a constraint, not a generator." Delete the loop; paper/website sync
  on request.

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.Embedding` green; `#print axioms` std-3; budget 0;
AxiomAudit pins; wire `QIQTH.lean`; ONE commit + `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`;
push schannel; update this checklist + `LEAN_RESULTS_INVENTORY.md`. HONESTY: transport, not construction;
capacity is a constraint, NOT a generator; the cutoff→continuum limit is THE wall; NEVER claim QG solved
or a wall crossed. NEVER claim an increment too hard — attempt, iterate, checkpoint only after a genuine
failed attempt with the error shown. Check for sibling jobs before each increment. Consults:
`mcp__OpenAI__ask` gpt-5.5-pro (do NOT expose the key).

## Progress log
- **2026-07-03** — plan created from the GPT-5.5-pro embedding consult (direct-entry modeOp, no Kronecker
  induction; one generic cross-mode theorem; records = occupation projectors; finite spectrum reading;
  P-not-1 corner identity; ModeAssignment named data + optional certifying witness; capacity
  constraint-not-generator; the cut list; ordering EM1→EM7). NEXT → EM1.

- **2026-07-03** — **EM1 LANDED** (`QIQTH/Embedding.lean`, axiom-free std-3, budget 0): ModeAssignment
  (mode labels + per-mode truncation cutoffs — NAMED finite data); toLinkDims (the dictionary map:
  a link IS a field mode, its dimension the mode's cutoff); FieldMicro/TruncatedFockBasis/
  FieldDiamondAlg with the rfl dictionary theorems (the identification is DEFINITIONAL — the
  keystone object IS the truncated field object); card_truncatedFockBasis (= Π cutoffs); CAPSTONE
  truncated_field_diamond_entropy — S(maxMixed) = Σ_k log D_k = A_τ(C)/4G with links = modes
  (K2a verbatim through the dictionary). NEXT → EM2 (the coordinate operator embedding).

- **2026-07-03** — **EM2 LANDED** (axiom-free std-3, budget 0): sameOff (agreement off mode k, decidable)
  + refl/symm/trans; zeroMicro; updMode (the dependent-update helper — casts hidden per the trap list) +
  self/of_ne/injective + eq_updMode_of_sameOff; sum_mode_fiber (the reusable fiber-sum engine: a function
  vanishing off the sameOff-fiber sums as a sum over the k-th occupation); modeOp (direct-entry, per the
  verdict — never Kronecker); the transport package modeOp_one/add/smul/star/mul (mul via the fiber-sum
  lemma — the crux); CAPSTONE modeOp_injective — each single-mode truncated-oscillator algebra genuinely
  EMBEDS. NEXT → EM3 (the per-mode oscillator structure).

- **2026-07-03** — **EM3 LANDED** (axiom-free std-3, budget 0): modeOp_sub/neg (package completion);
  modeLowering/numberOp/topProjMode (a_k, N_k, P_top,k via modeOp); raising_mul_lowering (N_k = a_k†a_k
  transported); CAPSTONE mode_ladder_commutator — [a_k, a_k†] = 1 − D_k·P_top,k (the held single-mode
  defect transported, never re-proved); numberOp_apply_diag + occupationProj (pointer-basis projector) +
  occupationProj_joint_eigen (N_k eigenvalue n_k — the finite spectrum reading); number_comm_lowering
  (single-mode, proved once) → numberOp_comm_modeLowering ([N_k,a_k] = −a_k) +
  numberOp_comm_modeRaising ([N_k,a_k†] = a_k†, by adjoints). NEXT → EM4 (the cross-mode algebra).

- **2026-07-03** — **EM4 LANDED** (axiom-free std-3, budget 0): sameOff2 (agreement off the pair,
  decidable); modeOp_mul_apply_of_ne (the two-coordinate product entry — independent fibers, delta
  elsewhere, via the EM2 fiber-sum engine); CAPSTONE modeOp_commute_of_ne — THE one generic cross-mode
  commutativity theorem; corollaries (never re-proved): cross_lowering_commutator ([a_k,a_j] = 0),
  cross_ladder_commutator ([a_k,a_j†] = 0 — the BOSONIC sector, honest scope stated), 
  cross_number_commutator ([N_k,a_j] = 0). NEXT → EM5 (records and the counted corner).
