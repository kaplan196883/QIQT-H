# THE RESOLVENT CAMPAIGN — (1+Δ)⁻¹ and the modular unitary group Δ^{it}

**Status:** ACTIVE (2026-07-05). **Loop:** fe280fa3 (the continuous QG program).
**Consult:** fable high-reasoning agent a64d01ffc6387c75c (2026-07-05) — decision: go THROUGH
Δ^{it}, not resolvent-only; full source-verified inventory in the consult record.

## Why and how far

THE VON NEUMANN campaign left Δ genuinely self-adjoint with ran(1+Δ) = ⊤ and the bound
‖x‖ ≤ ‖x+Δx‖. This campaign builds towerResolvent := (1+Δ)⁻¹ (an everywhere-defined
self-adjoint CLM contraction, 0 ≤ R ≤ 1) and pushes it through the project's EXISTING
spectral tower (PVM_of_selfAdjoint → borelFC/boundedFC_mul) to deliver **Δ^{it}** — a
strongly continuous one-parameter unitary group — because every analytic engine already
exists and compiles, with a line-by-line template in StandardSubspaceModularFlow.lean
(modChar/modUnitary: junk-value-1 piecewise symbol makes group laws pointwise-global;
dominated-convergence normality engines tendsto_inner_boundedFC_of_dominated present).

Key verified facts:
- PVM_of_selfAdjoint takes ANY IsSelfAdjoint CLM on a complete ℂ-inner-product space;
  carrier = subtype `spectrum ℝ T`; borelFC takes Measurable symbol + explicit bound.
- No CLM-inverse machinery needed: choice-def + ONE spec lemma + uniqueness-linearity +
  LinearMap.mkContinuous 1 (the inverse is bounded a priori by VN5's bound).
- rvdRC_spectrum_mem_Icc compiles at the pin (StarOrderedRing route) — the template for
  spec(R) ⊆ [0,1].
- MISSING (= the new-math increment R3): PVM eigenvector/atom calculus — E({0}) = 0 for
  injective T (kernel triviality does NOT kill the atom automatically; the multiplicative
  coord·1_{coord=0} = 0 argument does), eigenvector localization via the inverse-symbol
  trick + annulus decomposition, boundedFC_apply_eigenvector.
- E_compl is absent on ProjectionValuedMeasure (only PVContent) — derive from hasSum_iUnion.

## The increments

- [x] **R1 — `TowerGNS/Resolvent.lean`: the resolvent CLM.** ✅ DONE towerResolventAux h :=
  Classical.choose (towerModularOp_one_add_surjective …); ONE spec lemma (choice hygiene —
  never unfold after). Uniqueness one_add_injOn via norm_le_norm_add + map_sub; linearity
  from uniqueness; towerResolvent := LinearMap.mkContinuous _ 1. Consumer lemmas:
  towerResolvent_mem, _add_modularOp (Rh + Δ(Rh) = h), _one_add (R(x+Δx) = x),
  _injective, range = towerModularDom (dense), Δ∘R = 1−R (modularOp_towerResolvent) and
  R(Δx) = x − Rx. Risk LOW.
- [x] **R2 — `TowerGNS/ResolventOrder.lean`: self-adjointness, order, spectrum, Ω.** ✅ DONE
  isSymmetric (⟪Rh,k⟫ = ⟪h,Rk⟫ via towerModularOp_isFormalAdjoint) → isSelfAdjoint
  (isSelfAdjoint_iff_isSymmetric); nonneg (re⟪Rh,h⟫ = ‖Rh‖² + ‖S̄Rh‖²); R ≤ 1
  (re⟪h−Rh,h⟫ = ‖S̄Rh‖² + ‖ΔRh‖²); ‖R‖ ≤ 1; spectrum ⊆ Icc 0 1 (verbatim port of
  rvdRC_spectrum_mem_Icc with 1−R); towerResolvent_cyclicVec: RΩ = ½Ω. Risk LOW.
- [x] **R3 — `Spectral/PVMEigen.lean` (abstract, reusable — THE NEW MATH).** ✅ DONE (FULL, (d) included)
  (a) PVM finite additivity + E_compl from hasSum_iUnion. (b) generic eq_borelFC
  (T = ∫λ dE, de-specialize rvdRC_eq_borelFC/diagInt_specCoord). (c) KERNEL ATOM:
  Injective T ⟹ E(coe⁻¹'{0}) = 0 (coord·1_{coord=0} = 0 pointwise ⟹ T∘E({0}) =
  borelFC 0 = 0 via borelFC_mul + (b), injectivity kills it). (d) EIGENVECTOR
  LOCALIZATION: Tx = r•x ⟹ E(s)x = 0 for s ε-far from r (inverse-symbol trick:
  indicator((ω−r)⁻¹) bounded by ε⁻¹, h·(coord−r) = 1_s); annulus decomposition +
  hasSum_iUnion ⟹ x = E({r})x; capstone boundedFC_apply_eigenvector: boundedFC f x =
  f(r)•x (membership r ∈ spectrum from x ≠ 0). Risk MODERATE — the only real proof-search;
  if long, ship (a)–(c) green and split (d).
- [x] **R4 — `TowerGNS/ModularUnitary.lean` part 1: symbol + group.** ✅ DONE towerModChar t :=
  (Ioo 0 1).piecewise (r ↦ exp(I·t·log((1−r)/r))) (1) — expSymbol shape for R8; four
  pointwise laws + measurability + t-continuity (verbatim modChar ports). towerModUnitary t
  := borelFC (towerResolvent) …; _zero/add/adjoint/unitary/norm +
  inner_towerModUnitary_towerModUnitary (modUnitary ports). Risk LOW (transcription).
- [x] **R5 — part 2: strong continuity + the honesty pair.** ✅ DONE
  towerModUnitary_stronglyContinuous (port: sequential criterion +
  tendsto_inner_boundedFC_of_dominated + the 2‖ξ‖² − 2Re⟪ξ,U_{a−t}ξ⟫ identity).
  towerModUnitary_cyclicVec: U_tΩ = Ω (R3(d) at r = ½; ½ ∈ spectrum from Ω ≠ 0
  (norm_cyclicVec); towerModChar t ½ = exp(I·t·log 1) = 1).
  towerResolvent_pvm_atom_zero: E({0}) = 0 (R3(c) at towerResolvent_injective). Risk
  LOW-MODERATE (depends on R3).
- [ ] **R6 — commutation: U_t vs R and Δ.** towerResolvent_eq_borelFC (R3(b));
  towerModUnitary_commute_towerResolvent (borelFC_comm port); 1−R as FC of 1−coord; then
  algebraic: U_t maps dom Δ to dom Δ (U_t(Rh) = R(U_t h)) and Δ(U_t x) = U_t(Δx) on dom Δ
  (both = (1−R)U_t h, via Δ∘R = 1−R). Risk LOW.
- [ ] **R7 — checkpoint + audit.** Checkpoint.lean stanza (verbatim below); AxiomAudit
  pins; inventory; plan → COMPLETE.
- [ ] **R8 (OPTIONAL stretch)** — towerModLog := fcOp of the piecewise log (log Δ as
  unbounded FC operator, conditional statements only) + Stone derivative
  hasDerivAt_boundedFC_expSymbol instantiation. Do NOT attempt fcOp((1−r)/r) = Δ (missing
  scalarMeasure-density lemma; redundant given Δ∘R = 1−R). Skip freely if R1–R7 fill the
  session.

Out of scope (defer, never claim): Δ^{1/2}, J, polar; KMS-at-limit; Tomita's theorem;
towerFlow = towerModUnitary (towerGen = log Δ — the recovery wall, the NAMED next
campaign); type classification.

## The checkpoint language (R7, verbatim)

HAVE: "The resolvent of the tower modular operator is constructed as an everywhere-defined
operator: towerResolvent = (1+Δ)⁻¹, a self-adjoint contraction with 0 ≤ R ≤ 1, trivial
kernel, range equal to the (dense) domain of Δ, spectrum in [0,1], RΩ = ½Ω, and the exact
identities Δ∘R = 1−R and R∘(1+Δ) = 1 on dom Δ — so Δ is a function of a single bounded
self-adjoint operator. Through the bounded Borel functional calculus of R, the modular
unitary group of the tower limit state exists: Δ^{it} := towerModUnitary t, a strongly
continuous one-parameter unitary group (U_0 = 1, U_{s+t} = U_sU_t, U_t⋆ = U_{−t}) that
fixes the cyclic vector (U_tΩ = Ω), commutes with R and with Δ (preserving dom Δ), and
carries no spectral weight at the junk point (E({0}) = 0, forced by kernel triviality — the
group genuinely represents ((1−r)/r)^{it} = δ^{it} on the spectrum); plus a reusable
abstract supplement to the spectral tower: T = ∫λ dE at operator level, the kernel-atom
lemma E({0}) = 0 for injective self-adjoint T, and the eigenvector calculus
boundedFC f x = f(r)x — all axiom-free."

HAVE NOT: "No claim that towerModUnitary equals the transported towerFlow (equivalently
towerGen = log Δ): two strongly continuous unitary groups now coexist on the tower space
and their identification — the exponential-recovery wall — is the named next campaign, not
crossed here. No KMS condition of the limit state is proved; Tomita's theorem
(Δ^{it} towerLimitVN Δ^{−it} = towerLimitVN, JMJ = M′) is not proved — U_t is not shown to
implement automorphisms of the limit algebra; Δ^{1/2}, J, and the polar decomposition
S̄ = JΔ^{1/2} are still not constructed; no von Neumann type statement; and everything
remains for the finite-stage Gibbs inductive-limit state — the free-field/Type-III
continuum objects are untouched."

## Per-increment discipline (verbatim-critical)

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` = standard 3
(propext, Classical.choice, Quot.sound); `bash scripts/axiom_budget_check.sh` budget 0;
AxiomAudit.lean pins; wire QIQTH.lean; ONE commit on main with trailer
`Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this checklist + Progress log
AND LEAN_RESULTS_INVENTORY.md; NO sorry; carried inputs as hypotheses/structure fields
NEVER Lean axioms; NEVER claim QG solved, a type classified, KMS-at-limit, towerGen = log Δ,
or any wall crossed beyond what is literally proved; NEVER claim an increment too hard
(attempt, iterate, checkpoint only after a genuine failed attempt with the error shown);
check sibling jobs (git log/status) before each increment; explicit git paths only.

## Progress log

- **2026-07-05** — Campaign scoped and planned (consult verified the entire spectral-tower
  API against sources: PVM_of_selfAdjoint/borelFC signatures, the compiled
  StandardSubspaceModularFlow modChar/modUnitary template, dominated-convergence engines,
  the stale StarOrderedRing remark, the missing eigen/atom calculus). THE VON NEUMANN
  campaign closed immediately prior (Δ† = Δ, 34th first synced at e808695).

- **2026-07-05** — **R1 LANDED (green first try).** Resolvent.lean: towerResolvent =
  (1+Δ)⁻¹ as an everywhere-defined CLM contraction (choice-hygiene aux + ONE spec;
  uniqueness `one_add_modularOp_injOn` from the VN5 bound; linearity from uniqueness;
  mkContinuous 1). Full consumer API: Rh + Δ(Rh) = h, R(x+Δx) = x, Δ∘R = 1−R,
  R(Δx) = x − Rx, injective, range = towerModularDom (dense), ‖Rh‖ ≤ ‖h‖. Std-3,
  budget 0. Next: R2 (order/spectrum/Ω).

- **2026-07-05** — **R2 LANDED (green first try — sixth consecutive one-shot across two
  campaigns).** ResolventOrder.lean: towerResolvent is SELF-ADJOINT (symmetric via one
  IsFormalAdjoint swap), POSITIVE with 0 ≤ R and 0 ≤ 1−R in the Loewner order (both
  re-inner identities: ⟪Rh,h⟫ = ‖Rh‖² + ‖S̄Rh‖², ⟪h−Rh,h⟫ = ‖S̄Rh‖² + ‖ΔRh‖²), ‖R‖ ≤ 1,
  spectrum ⊆ [0,1] (verbatim rvdRC port), and RΩ = ½Ω. Std-3, budget 0. Next: R3 (the
  PVM eigenvector/atom calculus — the new math).

- **2026-07-05** — **R3 LANDED IN FULL — the risky increment, (d) included (3 build
  iterations).** Spectral/PVMEigen.lean: (a) E finite additivity + complement; (b) the
  generic operator-level spectral theorem T = borelFC T (coord) (rvd bridge de-specialized;
  bound ‖T‖·‖1‖ via spectrum.norm_le_norm_mul_of_mem — no caller hypothesis needed);
  (c) THE KERNEL ATOM E_zero_atom_of_injective; (d) eigenvector localization
  (inverse-symbol trick), E_eigenvector_atom via Mathlib `disjointed` annuli (needs neither
  x ≠ 0 nor r ∈ σ(T)), capstone borelFC_apply_eigenvector. Std-3, budget 0.
  Next: R4 (symbol + group — transcription).

- **2026-07-05** — **R4 LANDED (green first try).** ModularUnitary.lean: towerModChar (the
  (Ioo 0 1).piecewise junk-value-1 symbol, expSymbol shape preserved for R8) with the four
  pointwise laws; towerModUnitary := borelFC of it on towerResolvent; U0 = 1,
  U(s+t) = UsUt (mul + ∘L forms), adjoint = U(−t) (local towerBorelFC_adjoint port — no
  StandardSubspace coupling), unitary membership, isometry, and the two-vector cocycle
  ⟪Ua x, Ub y⟫ = ⟪x, U(b−a) y⟫ that R5 consumes. Std-3, budget 0. Next: R5 (strong
  continuity + U_tΩ = Ω + E({0}) = 0).

- **2026-07-05** — **R5 LANDED (green first try).** ModularUnitaryCont.lean:
  ★ towerModUnitary_stronglyContinuous (sequential criterion + dominated convergence +
  the cocycle norm-square identity; one proof-local rclikeToReal letI per project
  precedent); towerModUnitary_cyclicVec (U_tΩ = Ω via the R3 eigenvector calculus at
  RΩ = ½Ω, symbol value exp(it·log 1) = 1); towerResolvent_pvm_atom_zero (E({0}) = 0 —
  the kernel atom). Δ^{it} IS a strongly continuous one-parameter unitary group fixing Ω
  with no junk-point spectral weight. Still NO claim U = towerFlow. Std-3, budget 0.
  Next: R6 (commutation).
