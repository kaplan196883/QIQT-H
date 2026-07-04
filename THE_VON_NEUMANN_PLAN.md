# THE VON NEUMANN CAMPAIGN — Δ† = Δ (the S̄*S̄ theorem)

**Status:** ACTIVE (2026-07-05). **Loop:** fe280fa3 (the continuous QG program).
**Consult:** fable high-reasoning agent a3bf39d93364e7012 (2026-07-05) — decision (A) over the
type-negative ladder; full Mathlib-inventory verification in the consult record.

## Why this campaign

Δ = F∘S̄ (towerModularOp) is symmetric, positive, closable, computed as modAut on the core —
but not yet SELF-ADJOINT. Δ† = Δ is von Neumann's S̄*S̄ theorem, **absent from Mathlib even for
ℂ-linear T** (verified in the pin: no T*T result of any kind). It is the convergent blocker:
with Δ† = Δ, surjectivity of 1+Δ makes the resolvent (1+Δ)⁻¹ an everywhere-defined bounded
self-adjoint positive contraction — which feeds the ALREADY-BUILT `PVM_of_selfAdjoint` +
`boundedFC`/`boundedFC_mul` (QIQTH/Spectral/) via the symbol r ↦ ((1−r)/r)^{it}: the RvD
Δ = (2−R)R⁻¹ pattern already executed at the finite level. That is Δ^{1/2}, J, Δ^{it}, KMS —
the entire modular tower — waiting on one theorem.

## The architecture (from the consult — verified against the pin)

- **The kernel is field-generic**: "densely defined + IsFormalAdjoint A A + ran(1+A) = ⊤ ⟹
  A† = A" is valid over any RCLike 𝕜, applied at 𝕜 = ℂ directly to towerModularOp. In-repo
  template: the tail of `stoneGen_isSelfAdjoint` (Garding.lean).
- **The ℝ-machinery is needed for exactly ONE thing**: surjectivity of 1+Δ, via the graph
  decomposition of the closed S̄_ℝ in `WithLp 2 (E×E)` over ℝ. Decompose (h,0) = (x,S̄x) + v,
  v ⊥ graph: the orthogonality reads re⟪a, h−x⟫ = re⟪S̄a, S̄x⟫ ∀a.
- **The i-twist**: ConjHomogeneous (CC3, available) upgrades the re-pairing to the full ℂ
  pairing ⟪S̄a, S̄x⟫ = ⟪h−x, a⟫ — which is VERBATIM `mem_conjAdjointDom` for S̄x ∈ dom F with
  witness h−x. So F(S̄x) = h−x, x ∈ towerModularDom, x + Δx = h. No Mathlib ℝ-adjoint of S̄,
  no Δ_ℝ object, no ℝ→ℂ domain-comparison lift.
- **⚠ The one trap**: `InnerProductSpace.complexToReal` is a def, NOT an instance (diamond
  with PiLp). Use `letI := InnerProductSpace.rclikeToReal ℂ E` INSIDE proofs only (Mathlib
  blesses this in the docstring); its toNormedSpace is definitionally the global
  NormedSpace.complexToReal, so the ℝ-module structure under towerTomitaBar matches defeq.
  `real_inner_eq_re_inner` is rfl for this instance.
- Mathlib inventory (verified): LinearPMap adjoint file is RCLike-generic
  (IsFormalAdjoint, adjoint, adjoint_isFormalAdjoint, le_adjoint,
  mem_adjoint_domain_of_exists, instStar + isSelfAdjoint_def, Submodule.adjoint graph
  machinery, adjoint_isClosed); `Submodule.exists_add_mem_mem_orthogonal` +
  `HasOrthogonalProjection.ofCompleteSpace`; `WithLp.instProdCompleteSpace`,
  `WithLp.prodContinuousLinearEquiv`, `WithLp.prod_inner_apply`;
  `LinearPMap.eq_of_le_of_domain_eq` + PartialOrder for the antisymmetry finish.
  `LinearPMap.comp` demands the whole image in the domain — hand-roll the two-layer-domain
  composition (the towerModularOp pattern) instead.

## The increments

- [x] **VN1 — `QIQTH/VonNeumann/SelfAdjointCriterion.lean`** ✅ DONE (abstract kernel, RCLike,
  reusable): `isSelfAdjoint_of_isFormalAdjoint_of_one_add_surjective`: densely defined +
  IsFormalAdjoint A A + (∀ h, ∃ x : A.domain, ↑x + A x = h) ⟹ IsSelfAdjoint A. Route:
  le_adjoint; for z in dom A†, surject z + A†z, u := z − x has u + A†u = 0; ⟪u, y + Ay⟫ = 0
  ∀y; surjectivity ⟹ u = 0; eq_of_le_of_domain_eq. Risk LOW.
- [x] **VN2 — `QIQTH/VonNeumann/GraphDecomposition.lean`** ✅ DONE (the genuinely new content,
  RCLike-generic, consumed at 𝕜 = ℝ): `exists_pairing_of_isClosed`:
  T.IsClosed ⟹ ∀ h, ∃ x : T.domain, ∀ a : T.domain, ⟪↑a, h − ↑x⟫ = ⟪T a, T x⟫.
  Route: K := graph mapped into WithLp 2 (E×E) (closed via prodContinuousLinearEquiv);
  HasOrthogonalProjection.ofCompleteSpace; exists_add_mem_mem_orthogonal on toLp 2 (h,0);
  unpack, prod_inner_apply, rearrange. NO adjoint mentioned — deliberately. Risk MEDIUM
  (WithLp toLp/ofLp bookkeeping; Submodule.adjoint's source is the style guide).
- [x] **VN3 — `QIQTH/VonNeumann/AdjointComp.lean`** ✅ DONE (standalone von Neumann theorem,
  citable): `adjointComp T` on the two-layer domain {x ∈ dom T | Tx ∈ dom T†} (hand-rolled);
  formal self-adjointness; surjectivity corollary of VN2 via mem_adjoint_domain_of_exists;
  DENSITY of dom(T†T) (u ⊥ dom(T†T), u = x + T†Tx ⟹ ⟪u,x⟫ = ‖x‖² + ‖Tx‖² = 0 ⟹ u = 0);
  headline `vonNeumann_isSelfAdjoint`. Not on the tower's critical path (may slip after VN5)
  but IS the citable Mathlib-gap deliverable. Risk LOW-MEDIUM.
- [x] **VN4 — `QIQTH/TowerGNS/ModularSurjective.lean`** ✅ DONE (load-bearing):
  (a) abstract i-twist `conj_pairing_of_re_pairing`: ConjHomogeneous g + re-pairing ∀a ⟹
  full ℂ-pairing ∀a (evaluate at a and i•a; inner_smul, I_mul re/im arithmetic, Complex.ext).
  (b) `towerModularOp_one_add_surjective`: letI rclikeToReal inside the proof; VN2 at ℝ on
  towerTomitaBar (isClosed + Completion completeness); real_inner_eq_re_inner (rfl) +
  real_inner_comm orientation; feed (a) with towerTomitaBar_conjHomogeneous; conclude
  S̄x ∈ dom F (witness h−x) → mem_towerModularDom → Δx = h−x. Fallback if letI fights:
  restate VN2 as a ℂ-space re-pairing lemma with the letI inside its own proof. Risk MEDIUM.
- [x] **VN5 — `QIQTH/TowerGNS/ModularSelfAdjoint.lean`** ★ THE HEADLINE ★ ✅ DONE:
  `towerModularOp_isSelfAdjoint : IsSelfAdjoint (towerModularOp L ω β)` = VN1 at ℂ +
  dense_towerModularOp_domain + towerModularOp_isFormalAdjoint + VN4. Corollaries:
  isClosed, closure_eq, kernel triviality (via towerModularOp_inner_self +
  towerTomitaBar_eq_zero), the resolvent bound ‖x‖ ≤ ‖x + Δx‖. Risk LOW.
- [ ] **VN6 — checkpoint + wiring**: Checkpoint.lean stanza (verbatim HAVE/HAVE-NOT below),
  AxiomAudit sweep, inventory; state the consumer contract: towerResolvent := (1+Δ)⁻¹ as an
  everywhere-defined self-adjoint CLM contraction → PVM_of_selfAdjoint → boundedFC symbol
  ((1−r)/r)^{it} → Δ^{it} (the NEXT campaign; resolvent CLM here = stretch goal). Risk LOW.

Ordering: VN1 → VN2 → (VN3 ∥ VN4) → VN5 → VN6. VN3 may slip after VN5 without blocking.

## The checkpoint language (VN6, verbatim)

HAVE: "The modular operator Δ of the tower limit state is a genuinely self-adjoint (Mathlib
LinearPMap.adjoint-sense), positive, closed, densely defined operator with ΔΩ = Ω, acting as
the finite modular automorphism on the pure-component core, with ran(1+Δ) = ⊤; plus an
abstract, reusable, Mathlib-absent von Neumann theorem — T†T self-adjoint for closed densely
defined T over any RCLike field."

HAVE NOT: "Δ^{1/2} and the polar decomposition S̄ = JΔ^{1/2} are not constructed (so J is
still not an object); the spectral resolution of the unbounded Δ is not built
(PVM_of_selfAdjoint is for bounded operators; the resolvent bridge is stated, not built);
Δ^{it} and the KMS property of the limit state are not proved — in particular NO claim that
towerFlow/towerGen equals the modular flow of Δ (towerGen = log Δ is not established; they
are a priori different objects); Tomita's theorem (Δ^{it} M Δ^{−it} = M, JMJ = M′) is not
proved at the algebra level; no von Neumann type statement; and everything remains for the
specific finite-stage Gibbs inductive-limit state — the free-field/Type-III continuum objects
are untouched by this campaign."

## Per-increment discipline (verbatim-critical)

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` = standard 3
(propext, Classical.choice, Quot.sound); `bash scripts/axiom_budget_check.sh` budget 0;
AxiomAudit.lean pins; wire QIQTH.lean; ONE commit on main with trailer
`Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this checklist + Progress log AND
LEAN_RESULTS_INVENTORY.md; NO sorry; carried inputs as hypotheses/structure fields NEVER Lean
axioms; NEVER claim QG solved, a type classified, KMS-at-limit, or any wall crossed beyond
what is literally proved; NEVER claim an increment too hard (attempt, iterate, checkpoint
only after a genuine failed attempt with the error shown); check sibling jobs (git
log/status) before each increment; explicit git paths only.

## Progress log

- **2026-07-05** — Campaign scoped and planned (consult: fable high reasoning; decision (A);
  Mathlib inventory verified file-by-file in the pin — no T*T theorem anywhere, the kernel
  criterion, graph decomposition, and adjointComp are all new). THE MODULAR OPERATOR campaign
  (M1–M7) closed immediately prior; paper/website/inventory synced (33rd first, a47d23e).

- **2026-07-05** — **VN1 LANDED (green FIRST TRY, zero error iterations).**
  VonNeumann/SelfAdjointCriterion.lean: `isSelfAdjoint_of_isFormalAdjoint_of_one_add_surjective`
  — the abstract kernel over any RCLike field, Mathlib-only imports, genuine Star-based
  IsSelfAdjoint (instStar + isSelfAdjoint_def confirmed at the pin), structured on the
  stoneGen_isSelfAdjoint template with an abel-normalized subtraction (no ±i, field-generic);
  + corollary `adjoint_eq_...`. Std-3, budget 0. Next: VN2 (graph decomposition in WithLp 2).

- **2026-07-05** — **VN2 LANDED (green FIRST TRY again).** GraphDecomposition.lean:
  `exists_pairing_of_isClosed` — the von Neumann graph orthogonal decomposition in
  WithLp 2 (E×E), RCLike-generic, no adjoint anywhere. Route refinements that made it
  one-shot: K via `comap (WithLp.linearEquiv)` (membership Iff.rfl, closedness =
  IsClosed.preimage (prod_continuous_ofLp) — literal rfl set-equality, no map/symm
  rewriting); IsClosed.completeSpace_coe is an INSTANCE at the pin so HasOrthogonalProjection
  fires from one haveI; mem_orthogonal's orientation is already the goal's (graph element in
  slot 1) so no conjugation fix; prod_inner_apply is rfl. Std-3, budget 0.
  Next: VN4 (load-bearing i-twist + tower surjectivity); VN3 after.

- **2026-07-05** — **VN4 LANDED (green FIRST TRY — the load-bearing increment, and the letI
  trap never bit).** ModularSurjective.lean: `conj_pairing_of_re_pairing` (the abstract
  ConjHomogeneous i-twist), private `exists_re_pairing` (the ONLY letI := rclikeToReal site;
  VN2 at ℝ typechecked directly, ℝ-inner → re ⟪·,·⟫_ℂ was pure defeq — the fallback
  restatement was NOT needed), and ★ `towerModularOp_one_add_surjective`: ran(1+Δ) = ⊤ —
  the full pairing lands verbatim in mem_towerTomitaF_dom with witness h−x, Δx = h−x, abel.
  Std-3, budget 0. VN5 (Δ† = Δ) is UNBLOCKED. Next: VN5, then VN3, then VN6.

- **2026-07-05** — **VN5 LANDED — ★ Δ† = Δ IS A THEOREM ★ (green first try).**
  ModularSelfAdjoint.lean: `towerModularOp_isSelfAdjoint` (VN1 at ℂ + density + symmetry +
  the VN4 range condition — a 3-line term proof), `towerModularOp_adjoint_eq`, isClosed
  (Mathlib IsSelfAdjoint.isClosed), closure_eq (graph route — LinearPMap.IsClosed.closure_eq
  absent at pin), kernel triviality via inner_self + towerTomitaBar_eq_zero, and the
  resolvent bound ‖x‖ ≤ ‖x + Δx‖. Std-3, budget 0. Remaining: VN3 (standalone citable
  T†T), VN6 (checkpoint).

- **2026-07-05** — **VN3 LANDED (green first try — the FOURTH consecutive one-shot).**
  AdjointComp.lean: the standalone VON NEUMANN THEOREM — `vonNeumann_isSelfAdjoint`: for
  closed densely defined T over any RCLike field, T†T on the two-layer ∃-domain is densely
  defined (`vonNeumann_dense_domain`, the classical ⟪x,u⟫ = ‖x‖² + ‖Tx‖² trick) and
  self-adjoint (VN1 kernel + VN2-derived surjectivity `adjointComp_one_add_surjective`).
  Mathlib-gap file, abstract, reusable. Std-3, budget 0. Remaining: VN6 (checkpoint).
