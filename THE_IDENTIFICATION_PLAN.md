# THE IDENTIFICATION CAMPAIGN — towerFlow = Δ^{it} (crossing the exponential-recovery wall) + Tomita I

**Status:** ACTIVE (2026-07-05). **Loop:** fe280fa3 (the continuous QG program).
**Consult:** fable high-reasoning agent aa742bbcebadd4f05 (2026-07-05) — the eigenvector route
VERIFIED against sources; decision (A)+(B)-lite in one campaign.

## The discovery

The exponential-recovery wall (towerGen = log Δ) was scoped for generator-level
identification (Stone uniqueness). The eigenvector route SIDESTEPS it: two bounded operators
agreeing on a dense span are equal. Verified by the consult:

- **ρ_C is diagonal BY CONSTRUCTION**: `gibbsDensity β = Matrix.diagonal (gibbsWeight …)`
  (Dynamics.lean:260), weights strictly positive, explicit `gibbsInv` + `gibbsInvertible`
  (Dynamics.lean:351). No spectral theorem needed anywhere.
- **All three operators share the matrix-unit eigenbasis**: modAut m x = m·x·⅟m
  (FiniteModularTheory.lean:69) ⟹ modAut ρ (single n m c) = (w_n/w_m)•single n m c (the
  only genuinely NEW finite lemma); `cornerFlow_single` (Generator.lean:146) ALREADY gives
  cornerFlow t (single n m c) = exp(I·t·(log w_n − log w_m))•single n m c;
  `towerModularOp_of` (ModularOp.lean:516) transports to the GNS space.
- **towerFlow's decomposition plumbing is ALREADY BUILT**: towerFlow_coe + flowRaw_of;
  cornerFlow_eq_sum_single (Generator.lean:160), of_sum_single_smul (191),
  towerCoe_sum_raw (208), towerOf_sum_single_smul_coe (223); the horbit block in
  hasDerivAt_towerFlow_of (248–261) is verbatim the needed identity.
- **The Δ→R→U_t chain hooks all exist**: towerResolvent_one_add ⟹ eigenvector transport
  (Δx = δ•x ⟹ Rx = (1+δ)⁻¹•x, ~15 lines, subtype-smul pattern =
  towerModularOp_smul_cyclicVec); mem_spectrum_of_eigenvector + borelFC_apply_eigenvector
  (PVMEigen.lean:397, 484); usage template = towerModUnitary_cyclicVec
  (ModularUnitaryCont.lean:132). Symbol at r = (1+δ)⁻¹: (1−r)/r = δ (field_simp),
  Real.log_div — the scalar match with cornerFlow_single is EXACT, same sign convention.
  v = 0 handled by trivial case split (no faithfulness needed).
- **Density + extension precedent**: dense_span_towerRep_cyclicVec + towerRep_cyclicVec_of
  (CyclicVector.lean:94, 42) consumed via ContinuousLinearMap.ext_on (Separation.lean:144).
- **(B)-lite is nearly free**: FlowCovariance.lean already holds towerFlow_towerRep (92),
  towerFlow_conj_towerRep (111), towerLimitVN_flow_invariant (171),
  towerLimitVN_flow_conj_mem_iff (188) — after the identification, Tomita's first half
  Δ^{it} M Δ^{−it} = M is a rewrite.
- Pin API: `Matrix.single` / `Matrix.matrix_eq_sum_single` / `Matrix.smul_single` (NOT
  stdBasisMatrix).

## The increments

- [x] **ID1 — the finite modular eigenbasis** ✅ DONE (Dynamics/FiniteModular layer or a new small
  file): `invOf_gibbsDensity : ⅟(gibbsDensity L C ω β) = gibbsInv L C ω β`
  (invOf_eq_right_inv + the mul identity inside gibbsInvertible);
  `modAut_gibbs_single : modAut (gibbsDensity …) (Matrix.single n m c) =
  ((gibbsWeight n / gibbsWeight m : ℝ):ℂ) • Matrix.single n m c` (ext +
  diagonal_mul/mul_diagonal + single_apply). Optionally extract towerFlow_of_eq_sum_single
  from the horbit block for ID4 reuse. Risk LOW.
- [x] **ID2 — GNS eigenvectors of Δ and R**: ✅ DONE `towerModularOp_of_single :
  Δ⟨↑(of C (single n m c)), …⟩ = ((w_n/w_m:ℝ):ℂ) • ↑(of C (single n m c))` (from
  towerModularOp_of + ID1 + lof-smul + towerCoe_smul_raw); general
  `towerResolvent_of_eigen (0 < δ) (Δ⟨x,hx⟩ = δ•x) : R x = ((1+δ)⁻¹:ℝ) • x`; specialize
  towerResolvent_of_single. Risk LOW-MEDIUM.
- [ ] **ID3 — the modular unitary on the eigenbasis**: `towerModUnitary_of_single :
  U_t ↑(of C (single n m c)) = exp(I·t·(log w_n − log w_m)) • ↑(of C (single n m c))`.
  Case v = 0 trivial; else mem_spectrum_of_eigenvector at r = (1+δ)⁻¹,
  borelFC_apply_eigenvector, symbol evaluation ((1−(1+δ)⁻¹)/(1+δ)⁻¹ = δ; Real.log_div;
  template towerModUnitary_cyclicVec). Risk MEDIUM (the real-arithmetic step).
- [ ] **ID4 — ★ THE IDENTIFICATION ★**: `towerModUnitary_eq_towerFlow : ∀ t,
  towerModUnitary L ω β t = towerFlow L ω β t`. ContinuousLinearMap.ext_on
  (dense_span_towerRep_cyclicVec); rintro ⟨C,a,rfl⟩; towerRep_cyclicVec_of; both sides =
  Σ_{n,m} exp(…) • ↑(of C (single n m (a n m))) — flow side via cornerFlow_eq_sum_single +
  towerOf_sum_single_smul_coe, U side via matrix_eq_sum_single + map_sum + ID3. THIS
  CROSSES THE EXPONENTIAL-RECOVERY WALL. Risk MEDIUM (plumbing only).
- [ ] **ID5 — Tomita's theorem, first half, + checkpoint**: towerModUnitary_towerRep,
  towerModUnitary_conj_towerRep (Δ^{it} π_C(a) Δ^{−it} = π_C(σ_t a));
  **towerLimitVN_modUnitary_invariant + iff: Δ^{it} towerLimitVN Δ^{−it} = towerLimitVN**
  (rewrites of the FlowCovariance lemmas); bonus: towerGen = the Stone generator of Δ^{it}
  (congr under ID4 — the group-level content of towerGen = log Δ); Checkpoint stanza
  (verbatim below); AxiomAudit; plan → COMPLETE. Risk LOW.

## The checkpoint language (ID5, verbatim)

HAVE: "The transported physical flow IS the spectral modular flow of Δ — towerFlow t = Δ^{it}
as operators, axiom-free; hence the strongly continuous unitary group of Δ implements
automorphisms of towerLimitVN at every stage and preserves the limit algebra: the first half
of Tomita's theorem (Δ^{it} M Δ^{−it} = M) for the tower limit state, plus the finite-stage
KMS boundary identity now attached to the genuine modular group of Δ, plus towerGen
identified as the generator of Δ^{it} — the modular theory of the physics equals the modular
theory of the state."

HAVE NOT: "J and the polar decomposition S̄ = JΔ^{1/2} are still not constructed (so
JMJ = M′, the second half of Tomita's theorem, stays open — the natural next campaign: J on
matrix units is also explicit, so the same eigenbasis method applies); no analytic strip-KMS
of the limit state (only the boundary identity); no von Neumann type classification; and
everything remains the finite-stage Gibbs inductive-limit state — the free-field/Type-III
continuum objects are untouched."

## Per-increment discipline (verbatim-critical)

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` = standard 3
(propext, Classical.choice, Quot.sound); `bash scripts/axiom_budget_check.sh` budget 0;
AxiomAudit.lean pins; wire QIQTH.lean; ONE commit on main with trailer
`Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this checklist + Progress log AND
LEAN_RESULTS_INVENTORY.md; NO sorry; carried inputs as hypotheses/structure fields NEVER
Lean axioms; NEVER claim QG solved, a type classified, KMS-at-limit (strip form), J/polar,
or any wall crossed beyond what is literally proved; NEVER claim an increment too hard
(attempt, iterate, checkpoint only after a genuine failed attempt with the error shown);
check sibling jobs (git log/status) before each increment; explicit git paths only.

## Progress log

- **2026-07-05** — Campaign scoped (consult verified the eigenvector route file-by-file:
  ρ diagonal by construction, cornerFlow_single already computed, the decomposition
  plumbing already in Generator.lean, the borelFC eigenvector template compiled at
  towerModUnitary_cyclicVec). THE RESOLVENT campaign closed immediately prior (Δ^{it},
  35th first synced at 3f00de0).

- **2026-07-05** — **ID1 LANDED (green first try, optional item included).**
  ModularEigenbasis.lean: invOf_gibbsDensity (⅟ρ = gibbsInv); ★ modAut_gibbsDensity_single
  (modAut ρ (single n m c) = (w_n/w_m)•single n m c — the finite modular eigenbasis);
  gibbsWeight_div_pos; and towerFlow_of_eq_sum_single extracted standalone from the horbit
  block (no shape fight). Sign convention n−m matches cornerFlow_single exactly. Std-3,
  budget 0. Next: ID2 (GNS eigenvectors of Δ and R).

- **2026-07-05** — **ID2 LANDED (green first try).** ModularEigenvectors.lean:
  towerOf_smul_coe (single-scalar coercion push, new helper); ★ towerModularOp_of_single
  (Δ on a pure matrix-unit component = (w_n/w_m)•itself); ★ towerResolvent_of_eigen (the
  general transport Δx = δ•x ⟹ Rx = (1+δ)⁻¹•x, subtype-smul pattern);
  towerResolvent_of_single. Std-3, budget 0. Next: ID3 (U_t on the eigenbasis — the
  real-arithmetic step).
