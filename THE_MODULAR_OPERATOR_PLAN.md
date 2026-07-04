# THE MODULAR OPERATOR (M1–M7): Δ := F∘S̄ — symmetric, positive, computed on the core

**Status:** COMPLETE (2026-07-08) — M1–M7 ALL LANDED, axiom-free std-3, budget 0. **FABLE-5-CONSULT-VERIFIED (green-light; all names verified in
the pin).** **Goal:** Tomita's F (the conjugate-linear adjoint of S̄ through the sesquilinear
pairing ⟪Fy, x⟫ = ⟪S̄x, y⟫) and **Δ := F∘S̄** — ℂ-linear, symmetric, POSITIVE, densely defined,
closable, Δ ≤ Δ†, ΔΩ = Ω, and THE HEADLINE: **Δ↑(of C a) = ↑(of C (modAut ρ_C a))** — the
modular operator acts as the finite modular automorphism on the pure-component core. Files:
abstract `QIQTH/TowerGNS/ConjAdjoint.lean` + concrete `QIQTH/TowerGNS/ModularOp.lean`.

## Binding verdict (never violate)

- **A1 — The contract's algebra CLOSES:** x ↦ ⟪S̄x, y⟫ is ℂ-LINEAR in x (conj∘conj); with
  ⟪Fy, x⟫ = ⟪S̄x, y⟫, F is CONJUGATE-linear; Δ := F∘S̄ is ℂ-linear.
- **A2 — F's VEHICLE: the ∃-RIESZ domain, bespoke** — `conjAdjointDom g := {y | ∃ w, ∀ x :
  g.domain, ⟪g x, y⟫ = ⟪w, x⟫}` (a Submodule ℂ; smul witness conj c • w); F y := the choice of
  w, UNIQUE by `Dense.eq_of_inner_left` against the dense domain (threaded as a hypothesis at
  construction). NO toDual, NO CLM extension, NO letI, NO boundedness predicate (the classical
  equivalence bounded ⟺ ∃-Riesz is NOT formalized and NOT needed — say so in the banner).
  Mirroring Mathlib's adjointDomainMkCLM REJECTED (𝕜-CLM on an ℝ-submodule doesn't typecheck);
  the ℝ-adjoint REJECTED (InnerProductSpace ℝ is a def — letI hazard, confirmed again). F
  packaged as `E →ₛₗ.[starRingEnd ℂ] E` (the towerTomita₀ precedent). CHOICE HYGIENE: one
  witness def + ONE spec lemma ⟪F y, x⟫ = ⟪S̄x, y⟫ (∀ x : dom S̄) — the tomitaFun_eq pattern.
- **A3 — Δ's packaging: bespoke composition** (LinearPMap.comp does NOT exist — verified):
  `towerModularOp : TowerGNS →ₗ.[ℂ] TowerGNS` with carrier {x | ∃ hx : x ∈ dom S̄,
  S̄⟨x,hx⟩ ∈ dom F} (smul via ConjHomogeneous.smul_mem + dom F's ℂ-closure; conjugations cancel
  in map_smul'). ℂ-id packaging = the payoff: MATHLIB'S ENTIRE id-ADJOINT THEORY APPLIES
  (adjoint_isFormalAdjoint, IsFormalAdjoint.le_adjoint, adjoint_isClosed, IsClosable.leIsClosable
  — the Spectral/Garding.lean:662–745 precedent).
- **A4 — The provable set (verified to close):** (ii) POSITIVITY ⟪Δx, x⟫ = ‖S̄x‖² ≥ 0 (ONE
  spec application at y := S̄x); (iii) symmetry as `IsFormalAdjoint Δ Δ` (two spec applications
  + inner_conj_symm); (iv) ΔΩ = Ω FREE from (v) (Ω = ↑(of ∅ 1) definitionally + modAut_one);
  (v) THE HEADLINE — F↑(of C b) = ↑(of C ((rightConj² b)ᴴ)) via the M2 core-extension +
  tomita_adjoint_pairing VERBATIM, then Δ↑(of C a) = F↑(of C aᴴ) = ↑(of C (modAut ρ (aᴴ)ᴴ)) =
  ↑(of C (modAut ρ a)) — closes exactly via rightConj_sq_conjTranspose_eq_modAut; (vi) dense
  domains (pure components ∈ dom Δ); (vii) F CLOSED (limits through the spec pairing); (viii)
  Δ ≤ Δ† + Δ† closed + Δ IsClosable (IsFormalAdjoint.le_adjoint + adjoint_isClosed +
  IsClosable.leIsClosable — symmetric-densely-defined ⟹ closable WITHOUT new theory); (ix)
  twist guards F(c•Ω) = conj c•Ω and Δ(c•Ω) = c•Ω (i-sensitive).
- **A5 — THE M2 CORE-EXTENSION LEMMA (cheaper than sequences):** the set {p : E×E | ⟪p.2, y⟫ =
  ⟪w, p.1⟫} is CLOSED (inner continuous) and contains graph(towerTomitaR) ⟹ contains its
  closure = graph(S̄) (IsClosable.graph_closure_eq_closure_graph). ~10 lines.
- **A6 — CUTS (binding):** FULL self-adjointness Δ† = Δ — von Neumann's theorem, ABSENT from
  Mathlib (no T*T machinery; named as the NEXT-campaign target via the Submodule.adjoint graph
  route); J/polar; Δ^{1/2} (no unbounded positive square roots); Δ^{it}; KMS-at-limit; type.
  Banner: "symmetric, positive, densely defined, closable, computed on the core;
  self-adjointness/J/Δ^{it}/KMS/type NOT constructed or claimed."

## Increments

- [x] **M1 — `QIQTH/TowerGNS/ConjAdjoint.lean` (ABSTRACT, Mathlib-only):** ✅ DONE `conjAdjointDom g`
  (∃-Riesz Submodule ℂ over g : E →ₗ.[ℝ] E); witness def + THE ONE SPEC LEMMA; uniqueness
  (density hypothesis); `conjAdjoint g hd : E →ₛₗ.[starRingEnd ℂ] E`; graph closedness;
  conj-homogeneity. Risk LOW (the tomitaFun pattern).
- [x] **M2 — same file:** ✅ DONE the equalizer core-extension lemma (closed set ⊇ graph ⟹ ⊇ graph of
  closure). Risk LOW.
- [x] **M3 — `QIQTH/TowerGNS/ModularOp.lean` (concrete):** ✅ DONE `towerTomitaF := conjAdjoint
  towerTomitaBar dense_…`; memberships + **F↑(of C b) = ↑(of C ((rightConj² b)ᴴ))** (M2 +
  tomita_adjoint_pairing) + FΩ = Ω; dom F dense; F twist guard. Risk MODERATE
  (orbit-presentation unpacking; route through towerTomitaBar_agrees).
- [x] **M4 — same file:** ✅ DONE `towerModularOp` (Δ) as →ₗ.[ℂ] with the two-layer ∃-domain; spec
  lemma + congr adapter (never rw under a subtype). Risk MODERATE (nested membership transport).
- [x] **M5 — same file — THE HEADLINE PACK:** ✅ DONE POSITIVITY ⟪Δx,x⟫ = ‖S̄x‖²; symmetry
  (IsFormalAdjoint Δ Δ); ΔΩ = Ω; **`towerModularOp_of` — Δ↑(of C a) = ↑(of C (modAut ρ_C a))**;
  dense domain; Δ twist guard. Risk LOW once M3/M4 land.
- [x] **M6 — same file — the Mathlib hookup:** ✅ DONE Δ ≤ Δ† (IsFormalAdjoint.le_adjoint), Δ† closed,
  **Δ IsClosable**; optional closure-symmetry/positivity via the equalizer trick. Risk LOW
  (Garding precedent).
- [x] **M7 — checkpoint:** ✅ DONE the HAVE/HAVE-NOT sentences VERBATIM (below) into
  TowerGNS/Checkpoint.lean + inventory; AxiomAudit pins; plan → COMPLETE; per the standing
  continuous-QG directive the loop CONTINUES (next consult: the von Neumann Δ† = Δ via the
  Submodule.adjoint graph route, OR the type-negative ladder — re-consult).

## Checkpoint sentences (verbatim at M7)

HAVE: "The modular operator of the tower limit state is constructed and computed: Tomita's F —
the conjugate-linear adjoint of S̄ through the sesquilinear pairing ⟪Fy, x⟫ = ⟪S̄x, y⟫, built on
the ∃-Riesz domain with no real inner product, no dual-space machinery, and no completeness
argument — and Δ := F∘S̄, a ℂ-linear densely defined partial operator that is SYMMETRIC
(IsFormalAdjoint Δ Δ), POSITIVE (⟪Δx, x⟫ = ‖S̄x‖² ≥ 0), CLOSABLE (Δ ≤ Δ† with Δ† closed), fixes
Ω, and ACTS AS THE FINITE MODULAR AUTOMORPHISM ON THE DENSE PURE-COMPONENT CORE:
Δ↑(of C a) = ↑(of C (modAut ρ_C a)) — the modular operator of the physics, computed."

HAVE NOT: "Full self-adjointness Δ† = Δ is not proved — it is von Neumann's S̄*S̄ theorem, absent
from Mathlib and named as the next target; no polar decomposition, no J, no Δ^{1/2} or Δ^{it}
(no unbounded positive square-root or spectral theory for partial operators exists in the pin),
no KMS condition of the limit state, and no von Neumann type is constructed or claimed; the
classical equivalence of the ∃-Riesz adjoint domain with the boundedness domain is not
formalized (it is not needed)."

## Top-4 failure modes (mitigations binding)

1. The ℝ/ℂ submodule seam (dom S̄ is Submodule ℝ; dom F/dom Δ are Submodule ℂ) → smoke-test
   section first; memberships through explicit intro lemmas; never coerce a submodule across
   scalars mid-proof.
2. Silent twist swap in F → the i-sensitive guards F(c•Ω) = conj c•Ω and Δ(c•Ω) = c•Ω,
   mandatory, derived only from the spec lemma.
3. Pairing-orientation drift → ONE spec lemma as the single source; the conjugated form a named
   corollary; no ad-hoc inner_conj_symm at use sites.
4. Nested membership transport in dom Δ → ∃-form carrier + a Δ-congr adapter (the
   towerTomitaBar_congr pattern); never rw under a subtype.

## Discipline (every increment)

`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.TowerGNS.<Mod>` green; #print axioms std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit on
main + trailer `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this checklist + Progress log AND
LEAN_RESULTS_INVENTORY.md. NO sorry; NEVER claim Δ† = Δ, J, Δ^{it}, KMS-at-limit, or a type;
never letI an inner product; NEVER claim an increment too hard (attempt, iterate; checkpoint
only after a genuine failed attempt with the error shown); check sibling jobs before each
increment; explicit git paths only. Subagent authoring (fable) permitted, discipline in the
main loop. Consults: Agent tool (fable) high reasoning or mcp__OpenAI__ask gpt-5.5-pro (never
expose keys).

## Progress log

- **2026-07-08** — Campaign scoped; consult green-light (the contract's algebra verified sound;
  the ∃-Riesz bespoke F — no toDual/CLM-extension/letI; Δ packaged ℂ-id riding Mathlib's
  adjoint theory; the headline Δ↑(of C a) = ↑(of C (modAut ρ a)) verified to close via
  tomita_adjoint_pairing + the modAut bridge; von Neumann Δ† = Δ cut and named). The
  continuous-QG loop carries this campaign.

- **2026-07-08** — **M1+M2 LANDED, GREEN FIRST BUILD** (`QIQTH/TowerGNS/ConjAdjoint.lean`,
  abstract, axiom-free std-3, budget 0; fable subagent): `conjAdjointDom` (the ∃-Riesz witness
  domain; the smul twist starRingEnd c • w DERIVED, not guessed); `conjAdjoint g hd` — the
  conjugate-linear adjoint as a semilinear PMap (uniqueness by Dense.eq_of_inner_left —
  orientation verified: dense in the SECOND slot, no conj-flip needed; the ONE spec lemma +
  choice-discharge + congr adapter — the tomitaFun pattern); `conjAdjoint_closed` (sequence
  form); M2 `pairing_extends_of_closure` (~12 lines, the equalizer). BONUS FINDING: the
  ConjHomogeneous hypothesis is UNNEEDED for M1 — the ∃-form closes without ℂ-linearity of the
  pairing. NEXT → M3 (towerTomitaF at TowerGNS).

- **2026-07-08** — **M3 LANDED, GREEN FIRST BUILD, ZERO ITERATIONS** (`QIQTH/TowerGNS/
  ModularOp.lean`; fable subagent): **`towerTomitaF := conjAdjoint S̄`** — the pairing
  established on the orbit core (tomita_adjoint_pairing VERBATIM through the towerTomitaR
  unpack) and EXTENDED to all of dom S̄ by the M2 equalizer (towerTomitaBar = towerTomitaR.
  closure landed DEFINITIONALLY — no bridging); **`towerTomitaF_of`** — F↑(of C b) =
  ↑(of C ((rightConj² b)ᴴ)) by pure conjAdjoint_eq term proof; **FΩ = Ω** (the modAut route,
  cheaper as predicted); dense domain; the twist guard. NEXT → M4 (Δ itself).

- **2026-07-08** — **M4+M5 LANDED — THE HEADLINE** (ModularOp.lean extended, axiom-free std-3,
  budget 0; fable subagent, one fix — explicit ⟨vector, membership⟩ mks to stop whnf
  delta-unfolding through completion defs): `towerModularDom` (the two-layer ∃-domain);
  **`towerModularOp` — Δ := F∘S̄, ℂ-LINEAR** (the twist cancellation in map_smul');
  **POSITIVITY** ⟪Δx, x⟫ = ‖S̄x‖² ≥ 0; **SYMMETRY** (IsFormalAdjoint Δ Δ); **ΔΩ = Ω**;
  ★ **`towerModularOp_of`** — Δ↑(of C a) = ↑(of C (modAut ρ_C a)): THE MODULAR OPERATOR ACTS AS
  THE FINITE MODULAR AUTOMORPHISM on the dense pure-component core ★; dense domain; the
  ℂ-linear twist guard Δ(c•Ω) = c•Ω. NEXT → M6 (the Mathlib adjoint hookup) → M7 (checkpoint).

- **2026-07-08** — **M6+M7 LANDED — CAMPAIGN COMPLETE (7/7).** M6 (green first try): Δ ≤ Δ†,
  Δ† closed, Δ IsClosable — the Mathlib id-ℂ hookup, zero new theory. M7: the HAVE/HAVE-NOT
  stanza VERBATIM in TowerGNS/Checkpoint.lean; inventory updated. THE MODULAR OPERATOR STANDS:
  Δ = F∘S̄ — ℂ-linear, symmetric, positive, densely defined, closable, ΔΩ = Ω, and COMPUTED as
  the finite modular automorphism on the pure-component core. Per the standing continuous-QG
  directive the loop CONTINUES — next consult: von Neumann Δ† = Δ (the Submodule.adjoint graph
  route) vs the type-negative ladder.
