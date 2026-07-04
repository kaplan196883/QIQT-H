# THE FIELD-BW INCREMENT — field-level Bisognano–Wichmann, unconditional (F1, then STOP)

**Status:** COMPLETE (2026-07-05) — F1 landed, then STOP per the consult. Axiom-free std-3, budget 0. **Loop:** fe280fa3. **Commits LOCAL ONLY** (session no-push).
**Consult:** fable high-reasoning agent af34f8fd7781ed740 (2026-07-05).

## Binding verdict (READ — this is a ONE-increment plan, not a campaign)

The consult established, verified against sources, that:
- The free-field ONE-PARTICLE Bisognano–Wichmann theorem is ALREADY unconditional and
  axiom-free: `QIQTH.Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional` — the
  standard-subspace modular flow of the right-wedge one-particle subspace EQUALS the
  geometric Lorentz boost, no Reeh–Schlieder / KMS hypotheses (AxiomAudit.lean:6141).
- The QG frontier ("a Lorentzian finite-capacity substrate showing Δc²(Λ)→0") is a genuine
  RESEARCH PROBLEM, not a mechanical Lean increment. The tractable QG ladder is EXHAUSTED
  (option (c)). Do NOT frame further Lean work as "toward QG."
- There is EXACTLY ONE genuinely-new, non-thin, buildable-now Lean theorem left on this
  ladder — F1 below — and it is CONSOLIDATION (discharging a carried hypothesis), not QG
  advancement. The consult's explicit instruction: "build F1 and stop; do NOT chain
  F1→F2→… into a campaign — that would be manufacturing thin work."

After F1: STOP the modular/BW ladder and report honestly. The remaining moves are
paper-packaging (the Lean-first BW + Hardy-space KMS results deserve a write-up) or a
strategic pivot — both USER decisions.

## The increment

- [x] **F1 — `freeField_secondQuant_BW_unconditional` (field-level BW, no hypotheses).**
  In `QIQTH/Fock/OneParticleBW.lean` (or a small new `Fock/FieldBWUnconditional.lean`
  importing it + CyclicWitness). Statement: for `S = niceWedgeStandardSubspace m …`,
  `∀ t u x, secondQuantModFlowH S t (weylH u x) = weylH (boostUnitary (2π t) u)
  (secondQuantModFlowH S t x)` — no labelled hypothesis: the modular automorphism of the
  wedge field algebra acts on Weyl operators as the geometric boost. Route: a `+2π` copy of
  the existing `secondQuantModFlowH_acts_as_boost` (which currently takes `hbw` and is in
  the `−2π` convention), feeding its `hbw` from `oneParticleBW_niceWedge_unconditional hm
  (fun t => boostUnitary (2π t)) (fun _ _ => rfl)`. Lemmas in hand:
  `secondQuantModFlowH_weylH` (Tomita covariance σ_t(W(u)) = W(Δ^it u)),
  `oneParticleBW_niceWedge_unconditional`. The `+2π` sign-copy pattern is already proven in
  `FreeFieldHFlux.lean`. Risk: LOW (only the −2π vs +2π sign discipline).

## The checkpoint language (F1, verbatim)

HAVE: "The field-level (second-quantized) Bisognano–Wichmann identity is now unconditional:
the modular automorphism of the free-field right-wedge algebra acts on Weyl operators as the
geometric Lorentz boost — `secondQuantModFlowH S t (W(u)) = W(boost(2πt) u)` conjugated —
with NO carried BW hypothesis, discharged from the axiom-free one-particle
`oneParticleBW_niceWedge_unconditional`. Combined with the already-unconditional one-particle
BW, the strip-KMS condition `stripKMSrvd_boostUnitary`, and the Reeh–Schlieder cyclic +
separating witnesses, the free-field wedge modular structure is machine-checked
end-to-end — modular flow = boost, a Lean-first result. Axiom-free, std-3."

HAVE-NOT: "This is the free-field (linear, Gaussian) wedge BW for a single mass; it is NOT
the interacting theory, NOT the full Haag–Kastler net's modular covariance for arbitrary
regions, and makes NO low-energy Lorentz-violation prediction (unconditional BW = standard
induced gravity, per the QG-campaign verdict). The `hTkk` Unruh/localization stress-flux map
and the Clausius/area floor remain labelled physics inputs (never Lean axioms). The
`Δc²(Λ)→0` covariant finite-capacity substrate is a research problem, not formalized. No type
classification; the interacting / continuum-Haag-net frontier is untouched."

## Per-increment discipline

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pin; wire QIQTH.lean if a new file;
ONE commit on main with the Co-Authored-By: Claude Opus 4.8 trailer; **LOCAL ONLY — no push
until the user says so**; update this checklist + inventory; NO sorry; NEVER claim QG, a
type, interacting BW, or any wall crossed beyond what is literally proved; explicit git paths
only (Lean + plan + inventory + audit — NEVER the stray website edits in the tree); check
sibling jobs first.

## Progress log

- **2026-07-05** — Scoped (consult: free-field one-particle BW ALREADY unconditional; QG
  frontier is a research problem, ladder exhausted (option c); F1 = the single honest
  consolidation increment, discharge hbw for the field-level BW, then STOP). THE
  KMS-BOUNDARY campaign closed immediately prior (the tower modular theory complete).

- **2026-07-05** — **F1 LANDED (green first try) — and STOP.** Fock/FieldBWUnconditional.lean:
  freeField_secondQuant_BW_unconditional — the field-level (second-quantized) Bisognano–
  Wichmann identity, NO carried BW hypothesis: the wedge modular automorphism acts on Weyl
  operators as the geometric Lorentz boost (σ_t(W(u)) = W(boost(2πt)u) conjugated), the hbw
  discharged from oneParticleBW_niceWedge_unconditional (+2π convention, the FreeFieldHFlux
  sign pattern, 3-line proof). Std-3, budget 0. Per the consult's explicit instruction the
  BW ladder STOPS here — the QG frontier is a research problem, not a Lean increment.
