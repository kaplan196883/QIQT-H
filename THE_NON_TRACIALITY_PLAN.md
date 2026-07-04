# THE NON-TRACIALITY CAMPAIGN — the tower state is a genuine non-tracial KMS state (Δ ≠ 1)

**Status:** ACTIVE (2026-07-05). **Loop:** fe280fa3 (the continuous QG program).
**Consult:** fable high-reasoning agent a67191df5dba5ebfc (2026-07-05) — arithmetic + API
verified against sources; the honest scope is the binding verdict.

## Binding verdict (READ BEFORE OVERCLAIMING)

This campaign proves **state non-traciality + modular non-triviality — and NOTHING MORE.**
It does NOT prove a type classification. Per the consult, the following are EARNED:
- ω(·) = ⟪Ω, π(·)Ω⟫ = tr(ρ_C ·) is NOT a trace: ω(π(a)π(b)) = w_n ≠ w_m = ω(π(b)π(a)) on
  matrix units a = E_{nm}, b = E_{mn} when w_n ≠ w_m.
- Δ ≠ 1 (Δv = (w_n/w_m)•v ≠ v on a nonzero eigenvector) and Δ^{it} = towerFlow is not the
  identity flow (∃ t, U_t v ≠ v).
- Ω is not a tracial vector; towerLimitVN is not in tracial standard form w.r.t. this Ω.

The following are NOT earned and MUST be stated as HAVE-NOT (the claim is false otherwise):
- NOT "towerLimitVN is not type II₁" as an ALGEBRA statement (ω non-tracial does not
  preclude some OTHER tracial state; each finite stage is a full matrix algebra = type
  I_finite and DOES carry the normalized trace — ω just isn't it).
- NOT type III / III_λ / III₁, no Connes S-invariant, no modular-spectrum closure (those
  need crossed-product / flow-of-weights machinery, absent from Mathlib and the repo, and
  depend on weight-sequence ASYMPTOTICS the finite point spectrum cannot see).
- Mathlib has NO trace/tracial-state/factor/type API at this pin — "no tracial state exists"
  is not even stateable; only the CONCRETE INEQUALITIES are proved.
- Araki–Woods, Connes, Buchholz–Wichmann (local algebras type III₁) stay CITED, never
  reproved. The tower is ITPFI, type I at every finite stage.

## The verified arithmetic

ω(a) = ⟪Ω, π_C(a)Ω⟫ = stateOf (gibbsDensity …) a = tr(ρ_C·a) (towerRep_inner_cyclicVec,
CyclicVector.lean:62); ρ_C = diagonal (gibbsWeight), weights > 0. With a = single n m 1,
b = single m n 1: a*b = single n n 1 (Matrix.single_mul_single_same) ⟹ tr(ρ·a*b) = w_n;
b*a = single m m 1 ⟹ tr = w_m. Unequal iff w_n ≠ w_m. Cross-checks: modAut ρ (single n m c)
= (w_n/w_m)•single n m c (ModularEigenbasis.lean:76); ‖↑(of C (single n m c))‖² = |c|²·w_m
> 0 for c ≠ 0 (conjTranspose_single + single_mul_single_same + trace_diagonal_mul).

## The increments

- [x] **N1 — `QIQTH/NonTracial/FiniteNonTrace.lean`: finite non-traciality.** ✅ DONE (risk LOW)
  `gibbs_stateOf_single_cycle : stateOf (gibbsDensity L C ω β) (single n m 1 * single m n 1)
  = ((gibbsWeight L C ω β n : ℝ):ℂ)` (+ swapped = w_m); `gibbs_state_not_tracial
  (h : gibbsWeight n ≠ gibbsWeight m) : stateOf ρ (single n m 1 * single m n 1) ≠
  stateOf ρ (single m n 1 * single n m 1)`. Lemmas: Matrix.single_mul_single_same,
  QIQTH.Tower.trace_diagonal_mul (CornerEmbed.lean:237), Complex.ofReal_injective.
- [x] **N2 — `NonTracial/TowerNonTrace.lean`: tower vacuum vector state non-tracial.** ✅ DONE
  (risk LOW) `towerVacuum_not_tracial (h : w_n ≠ w_m) : ⟪Ω, π_C(single n m 1)(π_C(single m n
  1)Ω)⟫ ≠ ⟪Ω, π_C(single m n 1)(π_C(single n m 1)Ω)⟫`. Route: ContinuousLinearMap.mul_apply
  + map_mul (towerRep) to collapse π(a)(π(b)Ω) = π(a*b)Ω; towerRep_inner_cyclicVec; N1.
- [ ] **N3 — `ModularNonTrivial.lean`: Δ ≠ 1 and Δ^{it} ≠ id.** (risk LOW-MEDIUM — the
  ne_zero norm computation is the only fiddly step)
  `towerOf_single_ne_zero (hc : c ≠ 0) : ↑(of C (single n m c)) ≠ 0` (inner_coe_of_of +
  pairInner_embed at K=C + trace_diagonal_mul ⟹ |c|²·w_m > 0);
  `towerModularOp_ne_id (h : w_n ≠ w_m) : towerModularOp ⟨v,_⟩ ≠ v` (v = ↑(of C (single n m
  1)); towerModularOp_of_single ⟹ ((w_n/w_m)−1)•v = 0 ⟹ smul_eq_zero + ne_zero ⟹ w_n = w_m,
  ⊥); `towerModUnitary_ne_id (h : w_n ≠ w_m) : ∃ t, towerModUnitary t v ≠ v` (κ = log w_n −
  log w_m ≠ 0; t = π/κ ⟹ phase = exp(iπ) = −1; −1•v = v ⟹ 2•v = 0 ⟹ v = 0, ⊥).
- [ ] **N3.5 — OPTIONAL non-degeneracy existence** (risk MEDIUM, CUTTABLE):
  `∃ n m, gibbsWeight n ≠ gibbsWeight m` under explicit physical hypotheses (β ≠ 0, a mode
  with ω k ≠ 0, L.D k ≥ 2), unfolding gibbsWeight = ∏ pMode — makes the conditionals
  demonstrably non-vacuous. Skip without shame; the (n,m,h)-quantified forms are already
  honest.
- [ ] **N4 — `NonTracial/Checkpoint.lean`: checkpoint** (verbatim HAVE/HAVE-NOT below);
  AxiomAudit pins; plan → COMPLETE. Risk NIL.

## The checkpoint language (N4, verbatim)

HAVE: "The tower limit state is a genuine non-tracial KMS state, machine-checked. Its
canonical vector state ω(·) = ⟪Ω, π(·)Ω⟫ = tr(ρ_C ·) is NOT a trace: on the matrix units
a = E_{nm}, b = E_{mn} at any stage where the Gibbs weights differ (w_n ≠ w_m),
ω(π(a)π(b)) = w_n ≠ w_m = ω(π(b)π(a)). Equivalently the modular data is non-trivial: the
modular operator acts non-identically, Δ↑(of C E_{nm}) = (w_n/w_m)•↑(of C E_{nm}) ≠
↑(of C E_{nm}) on a nonzero pure-component eigenvector, and the modular unitary group
Δ^{it} = towerFlow is not the identity flow (∃ t, U_t v ≠ v). So Ω is not a tracial vector
and towerLimitVN, in this state, is not in tracial standard form — the Powers
'not-the-tracial-case' separation, at the resolution the finite modular eigenbasis
delivers."

HAVE NOT: "This does NOT show towerLimitVN is 'not type II₁' as an ALGEBRA statement — ω
being non-tracial does not preclude some OTHER faithful normal tracial state (each finite
stage is a full matrix algebra, type I_finite, and DOES carry the normalized trace; ω simply
is not it). No type III / III_λ / III₁ claim, no Connes S-invariant, no
modular-spectrum-closure statement is made or proved — those need the crossed-product /
flow-of-weights machinery, which is absent from Mathlib and the repo and depends on
weight-sequence asymptotics the finite eigenbasis cannot see. Mathlib has no
trace/tracial-state/factor/type API at this pin, so 'no tracial state exists' is not even
stateable here; only the concrete inequalities are proved. Araki–Woods 1968, Connes 1973,
and Buchholz–Wichmann (local algebras type III₁) stay CITED, never invoked. Everything
remains the finite-stage Gibbs inductive-limit state; the free-field/Type-III continuum
objects are untouched."

## Per-increment discipline (verbatim-critical)

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` = standard 3
(propext, Classical.choice, Quot.sound); `bash scripts/axiom_budget_check.sh` budget 0;
AxiomAudit.lean pins; wire QIQTH.lean; ONE commit on main with trailer
`Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; **commits LOCAL ONLY — do NOT
push until the user says so (standing instruction from this session)**; update this checklist
+ Progress log AND LEAN_RESULTS_INVENTORY.md; NO sorry; carried inputs as hypotheses NEVER
Lean axioms; NEVER claim a type classified, "not type II" as an algebra statement,
KMS-at-limit (analytic strip), or any wall crossed beyond what is literally proved — the
binding verdict above is the honesty contract; NEVER claim an increment too hard (attempt,
iterate, checkpoint only after a genuine failed attempt with the error shown); check sibling
jobs (git log/status — there are unexplained website edits in the tree, LEAVE THEM) before
each increment; explicit git paths only (Lean + plan + inventory + audit ONLY, never the
website files).

## Progress log

- **2026-07-05** — Campaign scoped (consult verified: ω = tr(ρ·) non-tracial arithmetic
  w_n vs w_m; the eigenvector nonzero-ness; the Δ≠1 / Δ^{it}≠id route; and — critically —
  the HONEST BOUNDARY: this is state non-traciality, NOT a type classification, NOT "not
  type II" as an algebra statement). THE MODULAR CONJUGATION campaign closed immediately
  prior (J M J ⊆ M′; the full Tomita–Takesaki data now machine-checked for the tower).
  NOTE: J1–J9 + this plan are committed LOCAL ONLY per the user's no-push instruction; the
  paper/website sync is also on hold until push is authorized.

- **2026-07-05** — **N1 LANDED (green first try).** FiniteNonTrace.lean: stateOf ρ x =
  trace(ρ*x) (density on the left); gibbs_stateOf_single_cycle (ω(E_nm·E_mn) = w_n, the
  swapped instance = w_m — ONE lemma covers both); ★ gibbs_state_not_tracial (w_n ≠ w_m ⟹
  ω(E_nm E_mn) ≠ ω(E_mn E_nm), via Complex.ofReal_injective). Std-3, budget 0. Next: N2
  (tower vacuum vector state non-tracial).

- **2026-07-05** — **N2 LANDED (green first try, 5-line proof).** TowerNonTrace.lean:
  ★ towerVacuum_not_tracial — ⟪Ω, π(E_nm)π(E_mn)Ω⟫ = w_n ≠ w_m = ⟪Ω, π(E_mn)π(E_nm)Ω⟫;
  towerRep is a unital ⋆-algebra hom into CLMs, so the word collapses via
  ContinuousLinearMap.mul_apply + map_mul, then towerRep_inner_cyclicVec (Ω on the left,
  orientation matched) + N1. Std-3, budget 0. Next: N3 (Δ ≠ 1, Δ^{it} ≠ id).
