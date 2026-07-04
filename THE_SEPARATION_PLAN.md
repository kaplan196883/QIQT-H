# THE SEPARATION (S1–S8): Ω is cyclic AND separating for towerLimitVN

**Status:** COMPLETE (2026-07-07) — S1–S8 ALL LANDED, axiom-free std-3, budget 0. **FABLE-5-CONSULT-VERIFIED (self-consult, high reasoning; all
held APIs + Mathlib names verified).** **Goal:** `towerCyclicVec_separating` — T ∈ towerLimitVN,
TΩ = 0 ⟹ T = 0 — via the bounded RIGHT multiplications (in the commutant of every stage,
commuting with the limit by pure bicommutant algebra). With R8's cyclicity: THE STANDARD-FORM
HYPOTHESIS PAIR of Tomita–Takesaki theory, axiom-free. Files: `QIQTH/TowerGNS/RightMul.lean` +
extensions. Route SOUND per consult, with three cost-reducing amendments (binding below).

## Binding verdict (never violate)

- **A1 — S1 via the √ρ-CONJUGATION FACTORIZATION, not dotProduct combinatorics:**
  `sqrtGibbs K := diagonal (√gibbsWeight)` (ρ_K = S·S, Sᴴ = S — the gnsInner_conj_symm hρ
  pattern); `rightConj a := sqrtInvGibbs C₀ * a * sqrtGibbs C₀` (explicit diagonal sandwich, no
  matrix inversion); constant **c(a) := frobNormSq ((rightConj a)ᴴ)** (= Σ ‖a n m‖²·(w_m/w_n);
  nonneg free). THE ENGINE (E1, the ONE new entrywise lemma): `ι(a)·S_K = S_K·ι(rightConj a)` —
  the sameOffSub case reduces to the WEIGHT EXCHANGE `w_K(m)·w₀(n̂) = w_K(n)·w₀(m̂)`, which drops
  out of the held T7 `kappaOf_gibbsWeight_of_sameOffSub` (rearrange, Real.log_mul,
  Real.log_injOn_pos, then Real.sqrt_mul). Then the Loewner gap is a 5-step algebraic chain:
  (ιa)ρ_K(ιa)ᴴ = S·ι(â·âᴴ)·S; c•ρ_K − … = S·ι(c•1 − â·âᴴ)·S; PSD by **frobBound applied to
  (rightConj a)ᴴ** (reorient via conjTranspose_conjTranspose) + cornerEmbed_posSemidef +
  mul_mul_conjTranspose_same. Scalar capstone `gnsInner_rightMul_le` mirrors gnsInner_leftMul_le
  line-for-line (trace_mul_cycle + the A4 recipe + Complex.le_def + linarith). NO fiber sums, NO
  updOn bijections, NO marginal machinery.
- **A2 — S5 commutation: COMPLETION-ONLY via the germ at a FRESH DEEP STAGE; no pre-level
  equation, no HEq, no sup_comm casts.** towerCoe (left b (right a x)) = towerCoe (right a
  (left b x)) by DirectSum.induction_on; the of-case takes D := (C₁⊔(C₀⊔C)) ⊔ (C₀⊔(C₁⊔C)) —
  both landing stages ⊆ D by bare subset_union proofs (Props — HEq never arises); towerGerm
  glues both sides to D; at D: cornerEmbed_mul/trans collapse to ι_D b · ι_D v · ι_D a both ways
  — mul_assoc. Then CLM commutation by the held completion incantation.
- **A3 — S6 transport: PURE BICOMMUTANT ALGEBRA — the SOTApprox ε-lemma is UNNECESSARY.**
  (towerLimitVN : Set) = centralizer (centralizer (⋃ stages)) via generatedBy_coe_of_starClosed
  (the mem_limitVN_iff hstar inlined); Set.centralizer membership is DEFINITIONAL — R ∈
  centralizer (⋃ stages) (from S5, unpacking Set.mem_iUnion + range) ⟹ ∀ T ∈ towerLimitVN,
  R*T = T*R by DIRECT APPLICATION hT R hR. Ship the general 10-line lemma
  `commute_of_mem_limitVN` in DirectedUnionVN-adjacent space (file-local in the tower file is
  fine; general form preferred).
- **A4 — S7: NO new right-orbit density lemma.** towerRightMulCLM C a Ω = ↑(of C a) =
  towerRep C a Ω — the capstone vanishes T on R8's EXISTING orbit: T(RΩ) = R(TΩ) = 0; close by
  **ContinuousLinearMap.ext_on** (verified: Topology/Algebra/Module/ContinuousLinearMap/
  Basic.lean:249 — takes Dense (span s) + EqOn f g s) with s := R8's orbit set, hs :=
  dense_span_towerRep_cyclicVec (EXACT type match), g := 0.
- **A5 — S8 bonus INCLUDED:** Ω cyclic for the LIMIT (span_mono + Dense.mono over
  towerRep_mem_towerLimitVN); `towerLimitVN_eq_of_apply_cyclicVec` (TΩ = SΩ ⟹ T = S — apply
  separation to T − S, sub_mem) — the well-definedness germ of a future Tomita S₀. CUTS: S₀
  itself, Δ/J, KMS-at-limit, type, AND right ⋆-anti-representation laws (map_mul/map_star of the
  right action are NOT needed — do not build them).
- Honest naming: separation is the HYPOTHESIS for Tomita theory, not the theory. Right action
  bounded with a WEIGHTED Frobenius constant, never claimed contractive.

## Increments

- [x] **S1 — `QIQTH/TowerGNS/RightMul.lean`** ✅ DONE: the weight exchange identity (ℝ-level, standalone,
  from kappaOf_gibbsWeight_of_sameOffSub) + the √-version; `sqrtGibbs`/`sqrtInvGibbs` (product =
  ρ, ᴴ-fixed simp lemmas); `rightConj`; c(a) := frobNormSq ((rightConj a)ᴴ) + nonneg. Risk LOW.
- [x] **S2 — same file** ✅ DONE: E1 `cornerEmbed_mul_sqrtGibbs` (ι(a)·S_K = S_K·ι(rightConj a),
  entrywise); the PSD gap c•ρ_K − (ιa)ρ_K(ιa)ᴴ = S·ι(c•1 − ââᴴ)·S PSD; scalar CAPSTONE
  **`gnsInner_rightMul_le`**. Risk MEDIUM (the residual lump — one entrywise lemma).
- [x] **S3 — same file** ✅ DONE: `rightMulRaw` (LinearMap.mulRight; component of C x ↦
  of (C₀⊔C) (ι(x)·ι(a))) + `rightMulRaw_of` + `collapse_rightMul` + the norm bound +
  **`towerRightMul` via mkContinuous √c** — the R6 mirror. Risk LOW.
- [x] **S4 — same file** ✅ DONE: `towerRightMulCLM := .completion` + `_coe`;
  **`towerRightMul_cyclicVec`** (R_aΩ = ↑(of C a) — the R8-head mirror). Risk LOW.
- [x] **S5 — `QIQTH/TowerGNS/Separation.lean`** ✅ DONE: the raw left-right exchange (DEEP-STAGE double
  germ + mul_assoc — A2); CLM commutation **`towerRightMul_comm_towerRep`**. Risk MEDIUM-LOW.
- [x] **S6 — same file** ✅ DONE: **`commute_of_mem_limitVN`** (the general bicommutant application) +
  `towerRightMul_comm_limitVN`. Risk LOW.
- [x] **S7 — same file — CAPSTONE** ✅ DONE: **`towerCyclicVec_separating`** (T ∈ towerLimitVN, TΩ = 0 ⟹
  T = 0 — ext_on + R8 density). Risk LOW.
- [x] **S8 — same file + checkpoint** ✅ DONE: Ω cyclic for the limit; `towerLimitVN_eq_of_apply_
  cyclicVec`; THE STANDARD-FORM BANNER; the HAVE/HAVE-NOT sentences VERBATIM (below) into
  TowerGNS/Checkpoint.lean + inventory; AxiomAudit pins; plan → COMPLETE; delete loop; stop.

## Checkpoint sentences (verbatim at S8)

HAVE: "Ω is CYCLIC AND SEPARATING for the tower limit von Neumann algebra:
`dense_span_towerRep_cyclicVec` + `towerCyclicVec_separating` — the standard-form HYPOTHESIS
PAIR of Tomita–Takesaki theory, exhibited axiom-free on the tower Hilbert space." "Right
multiplication by a corner element is BOUNDED with the weighted Frobenius constant
`frobNormSq((rightConj a)ᴴ) = Σ_{n,m} ‖a n m‖²·(wₘ/wₙ)` and lies in the commutant of every
stage algebra — hence commutes with the whole limit algebra by the bicommutant, purely
algebraically."

HAVE NOT: "No Tomita operator S₀, no modular operator Δ, no conjugation J, no KMS condition at
the limit, and no type classification is constructed or claimed here — separation is the
HYPOTHESIS for that theory, not the theory." "The right action is bounded with a weighted
Frobenius (Hilbert–Schmidt) constant, NOT the C*-norm — never claimed contractive; and no right
⋆-anti-representation laws are stated: exactly the operators the separation argument needs,
nothing more."

## Top-4 failure modes (mitigations binding)

1. E1 cast/inverse drowning → the ℝ-level weight-exchange lemma standalone FIRST; entry case one
   field_simp/push_cast with √-positivity denominators.
2. R3 synonym lesson → copy LeftMul.lean architecture verbatim (raw ⨁; wrappers application-
   position only).
3. Set-coercion dance in S6/S7 → replicate mem_limitVN_iff's show/rw maneuver ONCE in
   commute_of_mem_limitVN; the tower file never touches coercions.
4. PSD orientation slips → frobBound applied to (rightConj a)ᴴ; c(a) DEFINED as
   frobNormSq((rightConj a)ᴴ); (sqrtGibbs K)ᴴ = sqrtGibbs K as a named simp lemma first.

## Discipline (every increment)

`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.TowerGNS.<Mod>` green; #print axioms std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit on
main + trailer `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this checklist + Progress log AND
LEAN_RESULTS_INVENTORY.md. NO sorry; NEVER claim S₀/Δ/J/KMS-at-limit/a type; NEVER claim the
right action contractive or a ⋆-anti-representation; NEVER claim an increment too hard (attempt,
iterate; checkpoint only after a genuine failed attempt with the error shown); check sibling
jobs before each increment; explicit git paths only. Subagent authoring (fable) permitted,
discipline in the main loop. Consults: Agent tool (fable) high reasoning or mcp__OpenAI__ask
gpt-5.5-pro (never expose keys).

## Progress log

- **2026-07-07** — Campaign scoped; consult verified SOUND with three cost-reducing amendments
  (the √ρ factorization replaces dotProduct combinatorics; the deep-stage germ kills the HEq
  trap; pure bicommutant algebra replaces the SOTApprox ε-argument — Set.centralizer membership
  is definitional). Loop armed.

- **2026-07-07** — **S1+S2 LANDED — THE RISK LUMP CLEARED** (`QIQTH/TowerGNS/RightMul.lean`,
  axiom-free std-3, budget 0; fable subagent, three fixes): the WEIGHT EXCHANGE
  `gibbsWeight_exchange` (from T7's kappaOf lemma via log_mul + log_injOn_pos) + √-version;
  `sqrtGibbs` (ρ = S·S, Sᴴ = S), `sqrtInvGibbs`, `rightConj`, `rightFrobBound`; THE ENGINE
  **`cornerEmbed_mul_sqrtGibbs`** (ι(a)·S_K = S_K·ι(rightConj a) — ℝ-scalar identity first via
  field_simp + linear_combination); `rightMul_gap_posSemidef` (frobBound at (rightConj a)ᴴ +
  the S·ι(·)·S sandwich); CAPSTONE **`gnsInner_rightMul_le`** — right multiplication bounded
  with the weighted Frobenius constant. Lean notes: congr 1 on big matrix subtractions blows
  whnf heartbeats — use a separate hprod equality + rw chain. NEXT → S3 (rightMulRaw, R6 mirror).

- **2026-07-07** — **S3+S4 LANDED, GREEN FIRST BUILD** (RightMul.lean extended, axiom-free
  std-3, budget 0; fable subagent): `rightMulRaw` (the R6 mirror, product reversed) +
  `collapse_rightMul` + the norm bound ≤ √(rightFrobBound) + **`towerRightMul`** (mkContinuous)
  + **`towerRightMulCLM`** (.completion); CAPSTONE **`towerRightMul_cyclicVec`** — R_aΩ =
  ↑(of C a): THE RIGHT ORBIT OF Ω IS R8'S ORBIT (no new density lemma needed, per A4).
  NEXT → S5 (Separation.lean: the deep-stage exchange).

- **2026-07-07** — **S5–S8 LANDED — CAMPAIGN COMPLETE (8/8), GREEN FIRST BUILD.**
  (`QIQTH/TowerGNS/Separation.lean`): the deep-stage double-germ exchange (no HEq, per A2);
  `towerRightMul_comm_towerRep`; `commute_of_mem_limitVN` (pure bicommutant, per A3);
  CAPSTONE **`towerCyclicVec_separating`** — T ∈ towerLimitVN, TΩ = 0 ⟹ T = 0 (ext_on over
  R8's density; the right orbit IS the left orbit, per A4); Ω cyclic for the LIMIT;
  `towerLimitVN_eq_of_apply_cyclicVec` (the Tomita-S₀ well-definedness germ). **Ω IS CYCLIC AND
  SEPARATING FOR towerLimitVN — THE STANDARD-FORM HYPOTHESIS PAIR OF TOMITA–TAKESAKI THEORY,
  AXIOM-FREE.** Checkpoint stanza verbatim in TowerGNS/Checkpoint.lean. Loop 0272b65c deleted.
  Paper/website sync on request. The next campaign on the board: the Tomita operator S₀ itself
  (TΩ ↦ T*Ω — now well-defined by towerLimitVN_eq_of_apply_cyclicVec), then Δ/J, then the type.
