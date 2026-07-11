# LIMIT ALGEBRA campaign — the genuine frontier after the tower's Tomita theory

## ★★★ UPDATE (2026-07-11, same day): THE KAPLANSKY GAP IS CLOSED — J·M·J = M′ IN FULL
`94d285f7` `TowerGNS/CommutationEquality.lean` (duality campaign D2a). The gap was an ARTIFACT of
the wrong estimate: a GPT-5.5 consult identified the classical Rieffel–van Daele/Takesaki
RIGHT-BOUNDEDNESS route — the uniform bound `‖R_{b_C}‖ ≤ ‖T‖` comes from `T ∈ M′` + the bimodular
stage projection (never from the GNS norm of the symbol); the column witness cancels the Gibbs
weight exactly, giving the Loewner bound and rep contractivity with no auxiliary norm.
`tomita_commutation_equality`: rightLimitVN = M′ — with the held Tomita I and the full modular
data, **the complete both-halves Tomita commutation theorem, the first in any proof assistant**.
Remaining on this ladder: ONLY the type classification (III₁/S-invariant — no type API anywhere;
Araki–Woods/Connes cited). The LA1′ status below is superseded on the gap; its deliverables 1–3
remain the substrate the closure consumed.

## STATUS: LA1′ LANDED (2026-07-11, `15b9fb74`) — CHECKPOINT AT THE KAPLANSKY WALL, as planned
`TowerGNS/CommutationTheorem.lean` (772 lines, 47 decls, all std-3, budget 0). Deliverables 1–3
SHIPPED: the finite-stage commutation theorem; **`jconj_image_towerLimitVN` — J·M·J = rightLimitVN
as sets** (a genuine vN algebra, Ω cyclic for it, separating for it and its commutant, ⊆ M′,
M ⊆ (JMJ)′); the compression argument — every commutant element is right-multiplication-valued
POINTWISE ON THE CYCLIC ORBIT with the exact error bound, convergent along the full directed stage
filter. Deliverable 4 CHECKPOINTED with the wall now Lean-precise: the right-mult operator bound is
the RATIO-weighted Frobenius form, the compression controls only the COLUMN-weighted GNS form
(≤ ‖T‖², `commutantSymbol_gnsNorm_le`), and the two quadratic forms are inequivalent (w_m/w_n
unbounded) — **J·M·J = M′ holds up to the norm-control (Kaplansky) gap**; the Δ-smoothing escape
(bounded functions of Δ mollifying the approximants) is the named next campaign.

**Date:** 2026-07-11 (REWRITTEN same day — the first draft specced Ω-separating, which a detailed
re-read showed is ALREADY BUILT: S5–S8 `towerCyclicVec_separating`; indeed the tower's FULL modular
data is complete — S̄, Δ, Δ† = Δ, Δ^{it} = towerFlow, Tomita I, J, polar-on-core, Tomita II
INCLUSION, non-traciality, KMS-boundary; per the KMS-boundary checkpoint, "the first complete
Tomita–Takesaki modular theory in any proof assistant").

**The named HAVE-NOTs of the limit algebra (verbatim from the checkpoints):** the reverse inclusion
/ full equality **J M J = M′ (Tomita's hard half, named RvD route)**; strip-analyticity KMS; type
III (no Mathlib type API); no Kaplansky density.

## LA1′ — `TowerGNS/CommutationTheorem.lean`: the RvD corridor toward J M J = M′

Held: J8 gives `J·M·J ⊆ M′` (jconj_limitVN_mem_commutant); J7 gives `J π_C(a) J = R_{jStage a}`
with `jStage` a stage bijection; Ω cyclic AND separating for M (S8) and separating for M′ (J8);
the bounded right action with computed adjoints (S1–S4, T0_4); `mem_limitVN_iff` (SOT
approximation); the eigenbasis method. Deliverables, in rising difficulty:

1. **The finite-stage commutation theorem** (new content, finite linear algebra): on the stage GNS
   space, any operator commuting with the left action IS right multiplication by its value at the
   unit — `T ∘ L_a = L_a ∘ T (∀a) ⟹ T = R_{T(1)}` (the `T(x) = x·T(1)` argument; the stage GNS
   carrier is the full matrix algebra since the Gibbs state is faithful).
2. **`rightLimitVN = J·M·J` as a genuine von Neumann algebra**: package the right-multiplication
   limit algebra via `generatedBy`; prove `rightLimitVN = jconj '' towerLimitVN` (both inclusions:
   J7 stagewise + SOT transport through the anti-unitary homeomorphism, both directions since
   `jStage` is bijective and `J² = 1`); re-derive `rightLimitVN ⊆ M′` (J8 repackaged).
3. **Orbit-level approximation of the commutant by right multiplications** (the compression
   argument): for `T ∈ M′` and any stage `C`, the stage compression `b_C := symbol of P_{V_C}(TΩ)`
   satisfies `‖T(germ a) − R_{b_C}(germ a)‖ ≤ ‖π_C(a)‖·‖(1−P_{V_C})TΩ‖ → 0` — every commutant
   element is POINTWISE-ON-THE-ORBIT approximated by right multiplications (no operator-norm claim).
4. **THE WALL (attempt; CHECKPOINT expected here):** upgrading (3) to SOT membership
   `M′ ⊆ rightLimitVN` (equivalently `M′ ⊆ J·M·J`, i.e. the FULL Tomita equality) requires norm
   control of the approximants `R_{b_C}` — a Kaplansky-density-type statement the C11 checkpoint
   already names as absent. If a finite-tower trick closes it (everything is an inductive limit of
   finite-dimensional stages; the eigenbasis is explicit), take it; otherwise CHECKPOINT with
   (1)–(3) + the wall named precisely: "J M J = M′ up to the norm-control (Kaplansky) gap."

## ★★★ LA2 STATUS: LANDED FULL, BOTH PARTS (2026-07-12, `e3f4a757`, spectrum strategy α EXACT)
`towerLimitVN_factor` (THE TOWER LIMIT IS A FACTOR — center = ℂ·1, the central-symbol chase with
the λ-constancy trick), `spectrum_towerResolvent_eq_Icc` (σ_ℝ((1+Δ)⁻¹) = [0,1] EXACTLY),
`modular_spectrum_full` (closure of the modular point spectrum = [0,∞)), and the capstones
`operator_level_III1_signature` + the HYPOTHESIS-FREE `operator_level_III1_signature_sqrtTwo`.
The limit-algebra ladder now ends at exactly ONE item: the Connes S-invariant / type
classification proper (the infimum over ALL faithful normal states — needs a type API absent from
every proof assistant; Araki–Woods/Connes cited).

## LA2 — `TowerGNS/Factor.lean` (2026-07-12): FACTORIALITY + THE FULL MODULAR SPECTRUM
The type-III₁ rung, scoped honestly. With the commutation equality in hand:
- **Mirrored right-bimodularity**: V_C is invariant under the ⋆-closed right stage action ⟹ P_C
  commutes with the right multiplications (the C1 engine, mirrored).
- **FACTORIALITY** (`towerLimitVN_factor` / `center_trivial`): for central T ∈ M ∩ M′, the
  compressed symbol satisfies `germ(a·b_C) = germ(b_C·a)` for every stage element a (left chase via
  left-bimodularity + T ∈ M′; right chase via right-bimodularity + T ∈ M = (M′)′ commuting with the
  right multiplications) ⟹ b_C central in the stage matrix algebra ⟹ `b_C = λ_C·1` ⟹
  `P_C(TΩ) = λ_C·Ω → TΩ ∈ ℂ·Ω` ⟹ `T = λ·1` (Ω separating). **The tower limit is a FACTOR.**
- **THE FULL MODULAR SPECTRUM** (`spectrum_towerModularOp_eq_Ici` under the T3 two-frequency
  irrational-ratio hypothesis): the matrix-unit eigenvectors give Δ point spectrum = the Gibbs
  ratio set; T2/T3 Kronecker density ⟹ dense in (0,∞); spectrum closed + Δ ≥ 0 ⟹
  `spec Δ = [0,∞)`. **The operator-level III₁ signature**: a factor whose modular spectrum for the
  tower state is ALL of [0,∞).
- HONEST CEILING: the Connes S-invariant proper (the infimum over ALL faithful normal states) and
  the type classification machinery stay ABSENT/CITED (Connes 1973) — this brick upgrades the T3
  ARITHMETIC fingerprint to an OPERATOR-SPECTRUM statement on a FACTOR, the strongest honest
  III₁-adjacent claim without a type API.

## HONEST scope firewall (binding)

No strip-KMS, no type/S-invariant/ITPFI/III₁ (Araki–Woods/Connes stay cited), no claim of the full
commutation theorem unless (4) genuinely closes; the orbit-level statement (3) is pointwise on the
cyclic orbit, NOT SOT; finite-stage Gibbs inductive limit only. NOT QG.

## Discipline

Unchanged: ONE bg fable subagent (own module, NO git); independent verification (rebuild +
scratchpad `#print axioms` std-3 + no-sorry grep); wire `QIQTH.lean`; AxiomAudit pins; full budget
check (LONG ~420000ms, budget 0); commits LOCAL ONLY — DO NOT PUSH; explicit git paths; NO sorry;
hypotheses never axioms; CHECKPOINT at the named Kaplansky wall.
