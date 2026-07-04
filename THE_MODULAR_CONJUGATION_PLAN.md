# THE MODULAR CONJUGATION CAMPAIGN — J, the polar decomposition on the core, and Tomita II (inclusion)

**Status:** ACTIVE (2026-07-05). **Loop:** fe280fa3 (the continuous QG program).
**Consult:** fable high-reasoning agent abf699ea3e200897d (2026-07-05) — every claim verified
against sources; the full arithmetic + design record is in the consult.

## The verified arithmetic

- gnsInner of matrix units (StageInner.lean:31): ⟪E_{nm}c, E_{pq}d⟫_K = δ_{np}δ_{mq}·w_m·c̄d
  — the COLUMN weight; ‖↑(of C (E_{nm}c))‖² = w_m|c|².
- **THE J SCALAR**: J↑(of C (E_{nm}c)) = √(w_m/w_n) • ↑(of C (E_{mn} c̄)). Checks: isometry
  (w_m/w_n)·w_n = w_m ✓; J² = 1 ✓; JΩ = Ω free (Ω = ↑(of ∅ 1), jStage 1 = 1) ✓; polar
  sanity ‖Δ^{1/2}E‖ = ‖S̄E‖ ✓.
- **THE MATRIX CLOSED FORM**: jStage C a := sqrtGibbs · aᴴ · sqrtInvGibbs (reuse the
  RightMul.lean toolkit verbatim); deltaHalfStage C a := sqrtGibbs · a · sqrtInvGibbs. All
  identities are 3-line diagonal algebra: jStage∘deltaHalf = ᴴ (S̄-core = J∘Δ^{1/2});
  deltaHalf∘jStage = modAut ρ ∘ ᴴ (F-core = Δ^{1/2}∘J, matches towerTomitaF_of +
  rightConj_sq_conjTranspose_eq_modAut); deltaHalf² = modAut ρ; jStage² = id; jStage 1 = 1;
  anti-mult; conj-smul.
- **ORDER GUARD**: S̄ = J∘Δ^{1/2} = Δ^{−1/2}∘J; Δ^{1/2}∘J is F, NOT S̄. JΔ^{it} = Δ^{it}J
  (NOT Δ^{−it}) — antilinearity flips i, JΔJ = Δ⁻¹ flips back; verified on eigenvectors
  against towerModUnitary_of_single.

## The design (verified viable)

- **NO ℝ-reduction, NO unbounded Δ^{1/2}**: Mathlib's `ContinuousLinearMap.completion`
  (Topology/Algebra/LinearMapCompletion.lean:39) is SEMILINEAR-GENERIC, and
  `LinearMap.mkContinuous` takes E →ₛₗ[σ] F. Build exactly like towerFlow (Flow.lean:78
  pattern): jRaw (⨁ →ₛₗ[starRingEnd ℂ] ⨁, DirectSum.toAddMonoid + smul induction) →
  jPre := mkContinuous jRaw 1 → towerJ := jPre.completion.
- **Cross-stage well-definedness (the crux, pre-derisked)**: (1) no germ obligation — the
  completion kills null vectors, an isometric pre-map maps null to null (the R3
  architecture); (2) the scalar invariance is exactly `sqrt_gibbsWeight_exchange`
  (RightMul.lean:58, from kappaOf_gibbsWeight_of_sameOffSub) — new-link weights cancel in
  the ratio; better, `cornerEmbed_jStage` follows from THE ENGINE E1
  `cornerEmbed_mul_sqrtGibbs` (RightMul.lean:150) at b := jStage a, since
  rightConj (jStage a) = aᴴ; (3) single-stage anti-isometry gnsInner (jStage x)(jStage y) =
  gnsInner y x is trace-cycling with ρ = S·S.
- **Tomita II honest scope**: THE INCLUSION J M J ⊆ M′ is reachable (jconj SOT-continuous +
  towerRightMul_comm_limitVN + SOTApprox.mem_centralizer extracted from
  Bicommutant.lean:55–66); the REVERSE inclusion (full equality) is Tomita's hard half —
  NOT this campaign; named route for later: Rieffel–van Daele real-subspace argument.

## The increments

- [x] **J1 — `TowerGNS/JStage.lean`**: ✅ DONE jStage, deltaHalfStage + the lemma pack
  (jStage_single ★ the verified scalar; jStage_deltaHalfStage = ᴴ; deltaHalfStage_jStage =
  modAut∘ᴴ; deltaHalfStage_sq = modAut (invOf trick, Tomita.lean:490);
  gnsInner_jStage anti-isometry; rightConj_jStage = ᴴ; involutive/one/anti_mul/conj-smul).
  Risk LOW.
- [x] **J2 — cross-stage law**: ✅ DONE `cornerEmbed_jStage` via E1 + rightConj_jStage +
  sqrtGibbs_mul_sqrtInvGibbs + cornerEmbed_star (entrywise sqrt_gibbsWeight_exchange
  fallback); `cornerFlow_jStage` (diagonal conjugators commute). Risk LOW-MEDIUM.
- [ ] **J3 — `TowerGNS/ConjPre.lean`**: jRaw (σ-semilinear on ⨁, jRaw_of simp),
  rawInner_jRaw ★ (double induction + pairInner_embed + J2 + gnsInner_jStage), jPre
  (mkContinuous 1), towerJ := jPre.completion, towerJ_coe. Risk MEDIUM (semilinear
  plumbing — the completion API is verified σ-generic).
- [ ] **J4 — `TowerGNS/ModularConj.lean`**: the anti-unitary pack — towerJ_of,
  towerJ_of_single ★, towerJ_inner (⟪Jξ,Jη⟫ = ⟪η,ξ⟫), towerJ_norm, towerJ_involutive,
  towerJ_cyclicVec (JΩ = Ω), towerJ_smul twist guard, surjectivity. Risk LOW.
- [ ] **J5 — `TowerGNS/PolarCore.lean`**: ★ S̄↑(of C a) = towerJ↑(of C (deltaHalfStage a))
  (the polar decomposition on the core); mirror Δ^{1/2} = J∘S̄-core; F-core = Δ^{1/2}∘J;
  deltaHalf² = Δ-core; the order-guard documented. Risk LOW (harvest).
- [ ] **J6 — `TowerGNS/ConjFlow.lean`**: jRaw_flowRaw → towerJ_towerFlow →
  ★ towerJ_modUnitary (JΔ^{it} = Δ^{it}J pointwise, via towerFlow_eq_towerModUnitary).
  Risk LOW.
- [ ] **J7 — `TowerGNS/ConjImplements.lean`**: jconj (hand-bundled double-conj CLM),
  jconj_involutive, jconj_sot; ★ jconj_towerRep : jconj (towerRep C a) =
  towerRightMulCLM C (jStage C a) (stage bookkeeping mirrors towerRightMulCLM_adjoint).
  Risk MEDIUM.
- [ ] **J8 — `TowerGNS/TomitaSecondHalf.lean`**: SOTApprox.mem_centralizer (extract);
  towerRightMulCLM_mem_commutant; ★★ jconj_limitVN_mem_commutant (J M J ⊆ M′);
  M ⊆ J M′ J; Ω cyclic + separating for the commutant. Risk MEDIUM (assembly).
- [ ] **J9 — checkpoint + audit** (verbatim below); plan → COMPLETE. Risk NIL.

## The checkpoint language (J9, verbatim)

HAVE: "The modular conjugation J of the tower limit state is constructed as a global
anti-unitary on the tower GNS space — towerJ, the completion of the explicit
conjugate-linear stage map jStage a = √ρ·aᴴ·√ρ⁻¹, semilinearly extended with no
ℝ-reduction — with the full anti-unitary pack (⟪Jξ,Jη⟫ = ⟪η,ξ⟫, J² = 1, JΩ = Ω,
J(c•ξ) = conj c•Jξ) and the eigenbasis action J↑(of C E_{nm}c) = √(w_m/w_n)•↑(of C E_{mn}
conj c), all axiom-free. The polar decomposition holds exactly on the dense pure-component
core: S̄ = J∘Δ^{1/2} and F = Δ^{1/2}∘J, where the core Δ^{1/2}-action √ρ·a·√ρ⁻¹ squares to
the modular automorphism (Δ's core action); J commutes with the full modular group,
JΔ^{it} = Δ^{it}J. And the computable half of Tomita's second half: J conjugates every
represented left multiplication into the commutant-side right multiplication
(Jπ_C(a)J = R_{jStage a}), hence J·towerLimitVN·J ⊆ towerLimitVN′ — with Ω now cyclic and
separating for the commutant as well."

HAVE NOT: "The REVERSE inclusion towerLimitVN′ ⊆ J·towerLimitVN·J — the hard half of
Tomita's theorem — is not proved, so J M J = M′ as an equality stays open (the commutant of
the limit algebra is not characterized; the named route is the Rieffel–van Daele
real-subspace argument, not analytic continuation). No unbounded operator Δ^{1/2} is
constructed — the polar decomposition is a core-level identity, not an operator
factorization S̄ = J·Δ^{1/2} on the full domain of S̄; no strip-KMS of the limit state; no
von Neumann type classification; and everything remains the finite-stage Gibbs
inductive-limit state — free-field/Type-III continuum objects untouched."

## Per-increment discipline (verbatim-critical)

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` = standard 3
(propext, Classical.choice, Quot.sound); `bash scripts/axiom_budget_check.sh` budget 0;
AxiomAudit.lean pins; wire QIQTH.lean; ONE commit on main with trailer
`Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this checklist + Progress log
AND LEAN_RESULTS_INVENTORY.md; NO sorry; carried inputs as hypotheses/structure fields
NEVER Lean axioms; NEVER claim QG solved, J M J = M′ as an EQUALITY, an unbounded Δ^{1/2},
strip-KMS, a type, or any wall crossed beyond what is literally proved; NEVER claim an
increment too hard (attempt, iterate, checkpoint only after a genuine failed attempt with
the error shown); check sibling jobs (git log/status) before each increment; explicit git
paths only.

## Progress log

- **2026-07-05** — Campaign scoped (consult verified: the J scalar √(w_m/w_n) with column-
  weight inner products; the matrix closed form jStage = √ρ·aᴴ·√ρ⁻¹ reusing the RightMul
  toolkit; the σ-generic ContinuousLinearMap.completion making the extension one campaign;
  cross-stage invariance pre-derisked via E1; Tomita II scoped honestly to the inclusion).
  THE IDENTIFICATION campaign closed immediately prior (towerFlow = Δ^{it} + Tomita I,
  36th first synced at 2f30e10).

- **2026-07-05** — **J1 LANDED (green first try).** JStage.lean: jStage = √ρ·aᴴ·√ρ⁻¹ and
  deltaHalfStage = √ρ·a·√ρ⁻¹; ★ jStage_single (the verified scalar √(w_m/w_n), flipped
  indices, conjugated entry; ratio-under-one-sqrt shape); the algebraic pack (involutive,
  anti_mul, conj-smul twist, one); the polar-core trio (J∘Δ½ = ᴴ, Δ½∘J = modAut∘ᴴ,
  Δ½² = modAut); ★ gnsInner_jStage (single-stage anti-isometry, trace-cycled);
  rightConj_jStage = ᴴ (the J2 engine feed); + 5 toolkit extensions. Std-3, budget 0.
  Next: J2 (the cross-stage law).

- **2026-07-05** — **J2 LANDED (green first try).** JEmbed.lean: ★ cornerEmbed_jStage
  (THE CROSS-STAGE LAW — E1 at b := jStage a + rightConj_jStage + cornerEmbed_star, exactly
  the primary route, no fallback needed); cornerFlow_jStage (J commutes with the finite
  flow; new helpers diagPow_gibbs_conjTranspose (= −t) + S/S⁻¹–diagPow commutation — the
  ᴴ flips entries AND the sandwich, restoring +t). Std-3, budget 0. Next: J3 (jRaw/jPre/
  towerJ — the semilinear completion). NOTE: commits LOCAL ONLY per user instruction —
  do not push until told.
