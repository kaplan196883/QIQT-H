# THE CONJUGATE CLOSURE (CC1–CC7): S̄ — the closure of the Tomita operator, as an object

**Status:** ACTIVE (2026-07-08). **FABLE-5-CONSULT-VERIFIED (self-consult, high reasoning; all
Mathlib names verified in the pin).** **Goal:** the minimal σ-semilinear closure theory (a
genuine Mathlib gap — the σ-graph is Mathlib's own explicit TODO at LinearPMap.lean:27-29)
sufficient to construct **`towerTomitaBar` := the closure S̄ of towerTomita₀** as an object:
closed, extending S₀, agreeing on the orbit domain (S̄Ω = Ω, S̄↑(of C a) = ↑(of C aᴴ)),
conjugate-homogeneous, FULLY INVOLUTIVE on its domain (adjoint-free — the swap-graph argument),
with the orbit domain a CORE. Sets up (WITHOUT constructing) the Δ contract. Files:
`QIQTH/TowerGNS/ConjClosure.lean` (abstract) + instantiation.

## Binding verdict (never violate)

- **A1 — THE VEHICLE: the ℝ-REDUCTION (option ii), committed.** A starRingEnd-semilinear map IS
  ℝ-linear; Mathlib's ENTIRE id-closure theory (IsClosable/closure/le_closure/closure_isClosed/
  closureHasCore/…, Topology/Algebra/Module/LinearPMap.lean) applies VERBATIM at R = ℝ — the
  typeclasses are all satisfied on any ℂ-normed space by the GLOBAL priority-900 instances
  (Module.complexToReal, NormedSpace.complexToReal, IsScalarTower/SMulCommClass.complexToReal) —
  no letI, no local instances, ever. Option (i) (the σ-graph) = Mathlib's own open TODO, ~10×
  cost, zero extra payoff — REJECTED for this campaign (right shape for a future Mathlib PR).
  The earlier Tomita-plan rejection of the ℝ-route was for CONSTRUCTING S₀ and explicitly
  designated this thin path for the closure demand — that demand is this campaign; the hazard is
  confined by building ABSTRACTLY over {E F} [NormedAddCommGroup] [NormedSpace ℂ] and
  instantiating at TowerGNS exactly once.
- **A2 — New mathematical content = exactly FOUR abstract theorems:** the ℝ-restriction view
  (`LinearPMap.realRestrict` — NO Mathlib helper exists; manual 3-line map_smul' via
  IsScalarTower + Complex.conj_ofReal); the sequence-closability bridge (`isClosable_of_seq` —
  absent from Mathlib EVEN FOR id; via Submodule.topologicalClosure + mem_closure_iff_seq_limit
  (FrechetUrysohn from first-countable metric) + the Submodule.toLinearPMap graph machine —
  the same pattern Mathlib uses inside IsClosable.leIsClosable); conj-homogeneity transfer
  (`ConjHomogeneous f → ConjHomogeneous f.closure`, UNCONDITIONAL — junk branch trivial; engine:
  the twisted continuous map Φ_c = (c•·) ×ₗ (conj c•·) + image_closure_subset_closure_image);
  involution transfer (`GraphSymm` — swap-invariant graph survives closure since swap is a
  homeomorphism ⟹ FULL involution on dom S̄ + ker = ⊥ + range = dom — NO adjoint anywhere).
- **A3 — The bridge interface matches `towerTomita₀_closable'` VERBATIM** (xₙ ∈ domain,
  ↑xₙ → 0, S₀xₙ → v ⟹ v = 0).
- **A4 — CUTS (binding):** Δ/J/polar (next campaign — the Δ CONTRACT documented in a docstring:
  Tomita's F as the conjugate-linear adjoint through the ℂ-sesquilinear pairing
  ⟪Fy, x⟫ = ⟪S̄x, y⟫ — a ~40-line bespoke adjointAux mirror — then Δ := F∘S̄ is ℂ-LINEAR and
  lands back in Mathlib's id-ℂ world; recommended over Friedrichs); the σ-adjoint theory AND the
  ℝ-adjoint (InnerProductSpace ℝ is a DEF not an instance — the letI hazard; and the ℝ-adjoint
  is the wrong adjoint anyway); S̄ = S₀** (adjoint-dependent; NOT NEEDED — full involution is
  adjoint-free); KMS-at-limit; type.
- **A5 — The twist guard (binding):** derive ConjHomogeneous for realRestrict from
  towerTomita₀.map_smulₛₗ (single source of truth — a silently swapped c/conj c would
  typecheck); ship the concrete guard `S̄(c•Ω) = conj c • Ω` in CC5 (fails on c = i if wrong).
- Choice hygiene continues: every TowerGNS-level object behind a named def + one spec lemma;
  never simp-unfold towerTomitaBar; membership-proof-transport adapters.

## Increments

- [x] **CC1 — `QIQTH/TowerGNS/ConjClosure.lean` (abstract; NO TowerGNS import): the view + the
  predicate** ✅ DONE — `LinearPMap.realRestrict` (+ _apply/_domain/density transport);
  `ConjHomogeneous` def + pointwise iff + realRestrict-is-ConjHomogeneous (from map_smulₛₗ).
  Risk LOW.
- [x] **CC2 — same file: THE BRIDGE** ✅ DONE — `isClosable_of_seq` (A3 shape; topologicalClosure +
  mem_closure_iff_seq_limit + toLinearPMap_graph_eq). Risk LOW-MEDIUM (sequence/Subtype
  packaging — done once abstractly).
- [x] **CC3 — same file: the conj-homogeneity transfer** ✅ DONE — UNCONDITIONAL
  `ConjHomogeneous f.closure`; the twisted-map engine; pointwise corollaries. Risk LOW.
- [x] **CC4 — same file: the involution transfer** ✅ DONE — `GraphSymm` + survives closure +
  involution/ker/range corollaries (cross-check vs Mathlib's inverse_closure). Risk LOW.
- [x] **CC5 — instantiate at TowerGNS** ✅ DONE — instance smoke test FIRST; `towerTomitaR :=
  realRestrict towerTomita₀`; `towerTomitaR_isClosable` (CC2 + towerTomita₀_closable');
  **`towerTomitaBar := towerTomitaR.closure`**; the theorem pack: IsClosed, extends S₀
  (le_closure), S̄Ω = Ω, S̄↑(of C a) = ↑(of C aᴴ), dense domain, ConjHomogeneous + THE TWIST
  GUARD (S̄(c•Ω) = conj c•Ω), FULL INVOLUTION, closureHasCore (free). Risk MEDIUM (Completion
  elaboration — the whnf hazard; spec-lemma discipline). 
- [ ] **CC6 (STRETCH, CUTTABLE) — re-bundle S̄ semilinear** — `towerTomitaBarₛₗ` + round-trip.
  Not needed by the Δ contract; cut without shame.
- [ ] **CC7 — checkpoint** — the HAVE/HAVE-NOT sentences VERBATIM (below) into
  TowerGNS/Checkpoint.lean (ConjClosure stanza) + inventory; the Δ-contract docstring;
  AxiomAudit pins; plan → COMPLETE; delete the loop; stop.

## Checkpoint sentences (verbatim at CC7)

HAVE: "The closure S̄ of the Tomita operator is constructed as an object — towerTomitaBar, the
Mathlib closure of the ℝ-linear restriction of towerTomita₀, with the four new abstract theorems
this required (the ℝ-restriction view of a conjugate-linear partial map, the sequence-criterion
closability bridge, and the transfer theorems showing conjugate-homogeneity and the involution
survive closure): S̄ is closed, extends S₀ with the orbit domain as a core, fixes Ω, acts as
conjugate-transpose on pure components, is conjugate-homogeneous, and is FULLY involutive on its
domain with trivial kernel and range equal to domain — all axiom-free, with no real inner
product and no adjoint used anywhere."

HAVE NOT: "The modular operator Δ, the conjugation J, and the polar decomposition are not
constructed (the documented Δ contract — Tomita's F as the conjugate-linear adjoint through the
sesquilinear pairing, then Δ := F∘S̄ ℂ-linear — is the named next campaign); no σ-semilinear
graph or closure theory is contributed to Mathlib here (the ℝ-reduction sidesteps it; the
σ-graph remains Mathlib's own open TODO); no KMS condition of the limit state and no von Neumann
type is claimed."

## Top-4 failure modes (mitigations binding)

1. Module ℝ diamond at TowerGNS → both paths route through RestrictScalars (defeq); abstract
   file over [NormedSpace ℂ] only; CC5 opens with the smoke test; never letI.
2. whnf blowup of LinearPMap.domain through the Completion → named defs + one spec lemma each;
   never simp-unfold towerTomitaBar; congr-transport adapters.
3. Bridge packaging friction → proved once abstractly; TowerGNS side only feeds
   towerTomita₀_closable' (exact shape).
4. Silent wrong twist → single source of truth (map_smulₛₗ) + the c = i guard theorem.

## Discipline (every increment)

`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.TowerGNS.ConjClosure` green; #print axioms
std-3; `bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE
commit on main + trailer `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push via
`git -c http.sslBackend=schannel push origin main`; update this checklist + Progress log AND
LEAN_RESULTS_INVENTORY.md. NO sorry; NEVER claim Δ/J/polar/KMS-at-limit/a type; never letI an
inner product; NEVER claim an increment too hard (attempt, iterate; checkpoint only after a
genuine failed attempt with the error shown); check sibling jobs before each increment; explicit
git paths only. Subagent authoring (fable) permitted, discipline in the main loop. Consults:
Agent tool (fable) high reasoning or mcp__OpenAI__ask gpt-5.5-pro (never expose keys).

## Progress log

- **2026-07-08** — Campaign scoped; consult verified (the ℝ-reduction committed: Mathlib's
  id-closure theory applies verbatim at ℝ through the global complexToReal instances — no letI
  ever; the four new abstract theorems identified; the sequence-closability bridge absent from
  Mathlib even for id; FULL involution provable adjoint-free via the swap-graph; the Δ contract
  documented for the next campaign). Loop armed.

- **2026-07-08** — **CC1–CC4 LANDED — THE ABSTRACT THEORY COMPLETE** (`QIQTH/TowerGNS/
  ConjClosure.lean`, Mathlib-only imports, axiom-free std-3, budget 0; fable subagent, two
  fixes): `realRestrict` (+ rfl specs + density transport); `ConjHomogeneous` (∃-form) +
  `realRestrict_conjHomogeneous` (from map_smulₛₗ — the twist-guard source);
  **`isClosable_of_seq`** — THE BRIDGE (no choice needed: memberships from
  mem_domain_of_mem_graph, values by image_iff); **`ConjHomogeneous.closure`** (UNCONDITIONAL;
  plain Continuous twisted map — no CLM needed); **`GraphSymm.closure`** + involutive/eq_zero/
  range_eq_domain corollaries. The complexToReal path worked with NO letI, as predicted. Lean
  notes: theorems named `closure` shadow _root_.closure (qualify); ▸ on Prod-literal casts →
  rw at. NEXT → CC5 (instantiate at TowerGNS).

- **2026-07-08** — **CC5 LANDED — S̄ EXISTS AS AN OBJECT** (`QIQTH/TowerGNS/TomitaBar.lean`,
  axiom-free std-3, budget 0; fable subagent, one trivial fix — noncomputable examples in the
  smoke test): the instances resolved with NO letI (as predicted); `towerTomitaR` +
  `towerTomitaR_isClosable` (the bridge fed towerTomita₀_closable' VERBATIM, no adapters);
  **`towerTomitaBar := closure`** with the FULL theorem pack — IsClosed, extends S₀, orbit
  domain a CORE, S̄Ω = Ω, S̄↑(of C a) = ↑(of C aᴴ), dense domain, ConjHomogeneous + THE TWIST
  GUARD, FULL INVOLUTION (GraphSymm) + ker = ⊥ + range = domain. le_closure is unconditional in
  the pin. NEXT → CC6 (stretch; assess) → CC7 (checkpoint) → then per the standing directive:
  scope THE MODULAR OPERATOR.
