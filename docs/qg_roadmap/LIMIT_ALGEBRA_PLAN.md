# LIMIT ALGEBRA campaign — the genuine frontier after the tower's Tomita theory

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

## HONEST scope firewall (binding)

No strip-KMS, no type/S-invariant/ITPFI/III₁ (Araki–Woods/Connes stay cited), no claim of the full
commutation theorem unless (4) genuinely closes; the orbit-level statement (3) is pointwise on the
cyclic orbit, NOT SOT; finite-stage Gibbs inductive limit only. NOT QG.

## Discipline

Unchanged: ONE bg fable subagent (own module, NO git); independent verification (rebuild +
scratchpad `#print axioms` std-3 + no-sorry grep); wire `QIQTH.lean`; AxiomAudit pins; full budget
check (LONG ~420000ms, budget 0); commits LOCAL ONLY — DO NOT PUSH; explicit git paths; NO sorry;
hypotheses never axioms; CHECKPOINT at the named Kaplansky wall.
