# THE GENERATOR (G1–G6): the self-adjoint Stone generator of the transported flow

**Status:** ACTIVE (2026-07-07). **FABLE-5-CONSULT-VERIFIED (self-consult, high reasoning; all
held APIs read).** **Goal:** `towerGen := stoneGen (towerFlow)` — the genuine self-adjoint
unbounded generator of the tower's strongly continuous modular dynamics, by instantiating the
held Stone theorem (`stoneGen_isSelfAdjoint`, Garding.lean:740) with the five Track-B facts,
PLUS the explicit dense core (the finite-stage commutator formula) and the zero-mode Ω.
File: `QIQTH/TowerGNS/Generator.lean` (pattern = `Spectral/ModularGenerator.lean`).

## Binding verdict (never violate)

- **GO — near-verbatim precedent replay.** The five hypotheses of `stoneGen_isSelfAdjoint` match
  the five Track-B facts with EXACTLY TWO adapters: (1) **`towerFlow_compL (s t) : towerFlow
  (s+t) = towerFlow s ∘L towerFlow t := (towerFlow_comp L ω β s t).symm`** — a NAMED lemma, never
  inlined (the orientation trap); (2) the inline bound `fun t y => le_of_eq (towerFlow_norm_eq
  L ω β t y)`. hU0/hUinner/hSC match exactly (towerFlow_zero, towerFlow_inner,
  continuous_towerFlow_apply). No [Nontrivial H] needed.
- **The domain workhorse:** `stoneDomain U = {x | DifferentiableAt ℝ (fun t => U t x) 0}`; action
  pinned by **`stoneGen_eq_of_hasDerivAt`** (Stone.lean:131 — takes hx explicitly + HasDerivAt at
  I•v ⟹ stoneGen ⟨x,hx⟩ = v). No density/adjoint needed for membership.
- **CUTS (binding):** PVM/spectral resolution of the unbounded towerGen (PVM_of_selfAdjoint is
  bounded-only — verified); exp-recovery U t = exp(itK) (the recovery wall, open BY DESIGN — do
  NOT wrap stoneGen_cfc_h_mul with zero tower content); any Tomita claim (towerGen is NOT log Δ
  of a limit state); Ω-separating; generator-vs-towerRep derivation identities (DEFERRED — note:
  π_{C₀}(a)·↑(of C v) is again a pure component, reachable later via G3's formula).
- **NAMING:** `towerGen`; docstring VERBATIM: "the Stone generator of the TRANSPORTED flow — not
  constructed from the limit state's Tomita operator; NOT claimed to be a modular Hamiltonian in
  the Tomita sense."
- **G3 architecture:** decompose the orbit IN TowerGNS, never in matrix norms:
  U_t ↑(of C a) = Σ_{(n,m)} e^{itκ_nm} • ↑(towerOf C (stdBasisMatrix n m (a n m))) (towerFlow_coe
  + flowRaw_of + cornerFlow_entry + linearity); one isolated lemma `hasDerivAt_expPhase (κ v) :
  HasDerivAt (fun t : ℝ => Complex.exp (I*t*κ) • v) ((I*κ) • v) 0`; sum. `cornerGenMatrix C a :=
  Matrix.of fun n m => ((log w_n − log w_m : ℝ) : ℂ) * a n m`; the commutator corollary
  cornerGenMatrix = [diagonal(log∘w), a]. R3 synonym trap: raw ⨁ for sums, synonym in application
  position only; all HasDerivAt in TowerGNS (never TowerPre — degenerate seminorm — nor matrices).
- **Subtype trap:** every domain membership a STANDALONE named theorem; all action facts through
  stoneGen_eq_of_hasDerivAt; Subtype.ext transports (the StoneExp:1765 pattern).

## Increments

- [x] **G1 — `QIQTH/TowerGNS/Generator.lean`** ✅ DONE: `towerFlow_compL` (the named adapter); `towerGen`
  def + the verbatim docstring; **`towerGen_isSelfAdjoint`** (the five-argument instantiation).
  Risk LOW (precedent replay).
- [x] **G2 — same file** ✅ DONE: `towerCyclicVec_mem_stoneDomain` (constant orbit via funext on
  towerFlow_cyclicVec + differentiableAt_const); **`towerGen_cyclicVec`** — towerGen Ω = 0
  (stoneGen_eq_of_hasDerivAt with v := 0, hasDerivAt_const). THE ZERO-MODE. Risk LOW.
- [ ] **G3 — same file — THE EXPLICIT CORE**: `hasDerivAt_expPhase` (isolated ℝ→ℂ phase
  derivative); `cornerGenMatrix` + the commutator corollary ([diagonal(log∘w), a] entrywise);
  the orbit decomposition; `towerOf_mem_stoneDomain`; **`towerGen_of`** — towerGen ↑(of C a) =
  ↑(of C (cornerGenMatrix C a)) — THE GENERATOR IS COMPUTED, NOT JUST CERTIFIED; every coerced
  pre-vector ∈ domain (finite raw support, stoneDomain submodule); **`dense_stoneDomain`**
  CONSTRUCTIVELY (denseRange_coe — independent of Gårding mollification). Risk MEDIUM (the only
  new analysis; mitigations above binding).
- [ ] **G4 — same file**: `towerGen_domain_flow_mem` (U_s maps dom to dom — stoneDomain_apply_mem
  via towerFlow_compL) + **`towerGen_comm_towerFlow`** (K U_s = U_s K — stoneGen_comm_flow
  instantiated). Risk LOW.
- [ ] **G6 — checkpoint**: the HAVE/HAVE-NOT sentences VERBATIM (below) into
  `TowerGNS/Checkpoint.lean` (Generator stanza) + inventory; AxiomAudit pins; plan → COMPLETE;
  delete the loop; stop.

## Checkpoint sentences (verbatim at G6)

HAVE: "The transported tower flow has a genuine self-adjoint unbounded generator: `towerGen :=
stoneGen (towerFlow)` is a `LinearPMap` with `IsSelfAdjoint towerGen` (K = K† in Mathlib's
adjoint sense), axiom-free, obtained by instantiating the general Stone-generator theorem with
the five held Track-B group facts." "The cyclic vector is a zero-mode: `Ω ∈ dom(towerGen)` and
`towerGen Ω = 0`, because the flow fixes Ω exactly." "The generator is explicitly computed on a
dense core: every coerced pure component `↑(of C a)` lies in `dom(towerGen)` with
`towerGen ↑(of C a) = ↑(of C ([H_C, a]))`, where `H_C = diagonal(log gibbsWeight)` — the
finite-stage phases `κ_nm = log w_n − log w_m` of the held entry formula; the domain is
therefore dense constructively, not only via Gårding mollification." "The generator commutes
with its own flow: `U_s` maps `dom(towerGen)` into itself and `towerGen (U_s ξ) = U_s
(towerGen ξ)`."

HAVE NOT: "`towerGen` is NOT constructed from, and NOT claimed equal to, a Tomita modular
Hamiltonian `log Δ` of the limit state — no Δ, J, S, separating property, KMS-at-the-limit, or
von Neumann type is claimed. No spectral resolution (PVM) of the unbounded `towerGen` is
claimed, and no exponential-recovery identity `towerFlow t = exp(it·towerGen)` is claimed — the
recovery wall is open by design and the campaign does not cross it."

## Top-4 failure modes (mitigations binding)

1. hgrp orientation slip → the NAMED towerFlow_compL adapter, never inlined.
2. R3 synonym trap in G3 → raw ⨁ sums (the tendsto_flowPre_apply pattern); HasDerivAt only in
   TowerGNS.
3. ℝ→ℂ phase derivative → the isolated hasDerivAt_expPhase lemma, proved once.
4. LinearPMap subtype mismatches → standalone named membership theorems + everything through
   stoneGen_eq_of_hasDerivAt.

## Discipline (every increment)

`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.TowerGNS.Generator` green; #print axioms std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit on
main + trailer `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this checklist + Progress log AND
LEAN_RESULTS_INVENTORY.md. NO sorry; NEVER claim log Δ/Tomita, a PVM of towerGen, exp-recovery,
Ω-separating, or a type; NEVER claim an increment too hard (attempt, iterate; checkpoint only
after a genuine failed attempt with the error shown); check sibling jobs before each increment;
explicit git paths only. Subagent authoring (fable) permitted, discipline in the main loop.
Consults: Agent tool (fable) high reasoning or mcp__OpenAI__ask gpt-5.5-pro (never expose keys).

## Progress log

- **2026-07-07** — Campaign scoped; consult verified GO (five hypotheses match with exactly two
  adapters; stoneGen_eq_of_hasDerivAt is the domain workhorse; PVM/exp-recovery/Tomita cut —
  the recovery wall open by design; G3 = the one new-analysis increment, the commutator core).
  Loop armed.

- **2026-07-07** — **G1+G2 LANDED, GREEN FIRST BUILD** (`QIQTH/TowerGNS/Generator.lean`,
  axiom-free std-3, budget 0; fable subagent, zero iterations): `towerFlow_compL` (the named
  orientation adapter); **`towerGen := stoneGen (towerFlow)`** with the verbatim not-Tomita
  docstring; **`towerGen_isSelfAdjoint`** — THE SELF-ADJOINT UNBOUNDED GENERATOR of the
  transported modular dynamics (the five-argument instantiation, ModularGenerator pattern);
  **`towerGen_cyclicVec`** — THE ZERO-MODE: Ω ∈ dom(K), KΩ = 0 (constant orbit +
  stoneGen_eq_of_hasDerivAt with v = 0). NEXT → G3 (the explicit commutator core).
