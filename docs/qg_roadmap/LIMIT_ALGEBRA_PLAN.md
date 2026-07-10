# LIMIT ALGEBRA campaign — structural facts about towerLimitVN, beyond packaging

**Date:** 2026-07-11. **Parent:** the tower-GNS campaign (R1–R9: `TowerGNS`, `towerRep`, cyclic Ω,
`towerLimitVN`) + Transport/Accounting (B1–B6: `towerFlow`, implementation, flow-invariance).
**Frontier per the R9 checkpoint (verbatim):** "Ω is not shown separating, the modular theory of the
limit state on the completion is not constructed, and the representations are not shown isometric."
**User directive:** run the limit-algebra brick in the loop.

## LA1 — `TowerGNS/Separating.lean`: Ω SEPARATING for towerLimitVN (the modular prerequisite)

The classical right-multiplication argument, mirroring the held left-multiplication machinery
(R5 `gnsInner_leftMul_le` / R6 `towerLeftMul`):
- **Per-stage faithfulness** `gibbs_faithful`: the Gibbs density is PosDef, so
  `tr(ρ·a†a) = 0 ⟹ a = 0` (via the PosDef square root / invertible factor).
- **Injectivity** `towerRep_injective`: `π_C(a)Ω` has norm² `= φ_C(a†a)` (R8), so `π_C` is
  injective — the "representations not shown isometric" gap moved to its honest half (injective
  proved; C*-isometry NOT claimed).
- **The right multiplication** `towerRightMul b` (b at a FIXED stage C₀): bounded on the tower
  pre-space. THE CRUX = the stage-uniform bound `ι(b)·ρ_K·ι(b)† ≤ c(b)·ρ_K`: the crude
  λ_max/λ_min constant is NOT stage-uniform (Gibbs eigenvalues shrink along the tower); the
  product structure rescues it — `ρ_K` factorizes across modes (DY4 `reduced_gibbsDensity_eq`),
  `ι(b) = b ⊗ 1`, so the conjugation acts only on the C₀ factor and the constant is computed at
  the FIXED stage C₀ (PSD tensor monotonicity). Fiberwise `sameOff` machinery mirrors how R5
  transported `frobBound`.
- **Commutation** `left_right_commute`: right multiplications commute with every `towerRep C a`
  (raw associativity + continuity); SOT-limits preserve commutation with a fixed bounded operator,
  so right multiplications commute with all of `towerLimitVN`.
- **Dense right orbit**: `Ω·b = germ b` — the SAME family R8 proved dense.
- **CAPSTONE `omega_separating`**: `x ∈ towerLimitVN, xΩ = 0 ⟹ x = 0` (x kills the dense right
  orbit). Corollary `towerState_faithful`: the limit vector state is faithful on towerLimitVN.

## HONEST scope firewall (binding)

Ω separating is the PREREQUISITE for the limit's modular theory, not the theory: NO modular
operator/J of the LIMIT constructed here (next campaign), NO type classification, NO factor, NO
ITPFI/III₁ identification (T3's fingerprint stays arithmetic; Araki–Woods/Connes stay cited);
representations proved INJECTIVE, not C*-isometric; the stage-uniform right bound rides the
PRODUCT Gibbs structure (an honest model property, not generality). NOT QG.

## Discipline

Unchanged: ONE bg fable subagent (own module, NO git); independent verification (rebuild +
scratchpad `#print axioms` std-3 + no-sorry grep); wire `QIQTH.lean`; AxiomAudit pins; full budget
check (LONG ~420000ms, budget 0); commits LOCAL ONLY — DO NOT PUSH; explicit git paths; NO sorry;
hypotheses never axioms; CHECKPOINT permitted at the stage-uniform right bound if it genuinely
walls (then ship faithfulness + injectivity + per-stage pieces + the exact gap).
