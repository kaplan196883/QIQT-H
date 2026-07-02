# THE JOIN INSTANCE (JI1–JI7): delete `hJoin` by construction — the bridge at the finite level

**Status:** ACTIVE (2026-07-03). **GPT-5.5-pro-VERIFIED** (binding verdict below). **Goal:** merge the code
tower (keystone THE COUNT) and the graviton tower (Q1–Q5) into ONE object at the finite level by
constructing the dictionary instance — links ↔ screen elements, weights FROM the geometry — so that the
Q5 carried hypothesis `hJoin : inducedScreenArea G links wEnt = A0 + areaVar S (classicalH pol α)` becomes
a THEOREM for the constructed instance, and the count normalization rewrites to the induced-G primitives
`(A_J/4)·N·Λs²`. New file `lean/mathlib/QIQTH/JoinInstance.lean`.

## Binding verdict (from the consult — never violate)
- **Two-level construction.** (1) `TauJoinInstance` — REAL positive trace-dimensions
  `Dτ_a := exp(A^loc_a/4G)`, `wEnt a := log Dτ_a`: deletes `hJoin` for ARBITRARY geometric data at the
  τ-dimension/count level (calibration by `Real.log_exp` — no integrality). (2) `NatRealizable` — the
  integer finite-code specialization ONLY under the named realizability datum `log n_a = wEnt a`
  (`n_a : ℕ+`): the exact old finite-code case, NOT generic.
- **Direction: geometry → code.** `Link := {a // a ∈ S.elems}`; the code weights are defined from the
  local geometric shares. The theorem says "the code instance CONSTRUCTED from this geometric data has
  the join equality" — no smuggling. Code → screen is only a designed-example constructor, never the
  main theorem.
- **`A0` apportionment is NAMED DATA** (`A0Split`: shares + `∑ share = A0`) — there is no canonical
  per-link split of a global constant; uniform/area-weighted/designed splits are optional constructors,
  never pretended-derived.
- **τ₀ realization qualifier (JI3):** arbitrary positive τ-dimensions are legitimate because the
  CLOCK-WINDOW MASS is a free positive real (`τ₀(p⊗1_W) = rank·μ(W)`) — but NOT inside one
  already-fixed matrix fiber + mass-N_C window (there only rank-multiples of a fixed real scale). The
  instance must carry/construct its clock-window witness.
- **The NΛs² capstone is algebra + shared primitives:** the content is that BOTH constructions use the
  same `A_J`, `N`, `Λs` — define `A_J := A0 + areaVar(S,h)` INTERNALLY (never a new emergence
  hypothesis); extract the per-link capacity `wEnt a = (A^loc_a/4)·N·Λs²` and the area-cost corollaries
  (one nat costs `4/(NΛs²)`; one qubit costs `4·log 2/(NΛs²)`).
- **CUT from the critical path:** generic exact integer realization for arbitrary real weights (false);
  asymptotic block-code approximation (separate campaign, stays cut); any "canonical" A0 split; rebranding
  external-weight matching as deleted calibration (it remains the old calibration problem); exact finite
  CCR/operator-level isometry (obstruction is permanent); arbitrary real subcorner dims inside ONE fixed
  window; continuum modes / full Murray–von Neumann dimension library.

## Increments
- [x] **JI1 — the local area decomposition** ✅ DONE (`QIQTH/JoinInstance.lean`): `localAreaVar` (per-element `δA_a`), `A0Split` (share +
  `sum_share`), and the algebraic core `∑_a (β_a + δA_a) = A0 + areaVar S h`.
- [x] **JI2 — the generic τ join dictionary** ✅ DONE: `wEnt a := (β_a + δA_a)/(4G)`, `Dτ_a := exp(wEnt a)`;
  `hcal_tau` (`log (Dτ a) = wEnt a` — `Real.log_exp`); **`hJoin_tau`** — the join equality as a THEOREM
  (`0 < G` required).
- [ ] **JI3 — the τ₀ corner realization**: the clock-window mass realizes any positive real —
  `exists_tau0_corner_of_posReal` (∀ r > 0, ∃ window/corner with τ₀ = r), riding the held `flatClock`
  (mass is a free positive real) + the keystone monomial trace; the finite-family/product version for
  the instance's `Dτ` family.
- [ ] **JI4 — the τ count theorem**: `dimTau J := ∏_a Dτ_a`, `S_tau J := log dimTau J`;
  `S_tau J = ∑_a wEnt a = A_J/(4G)` — **the generic exact replacement for the carried `hJoin`**.
- [ ] **JI5 — the integer finite-code specialization**: `NatRealizable` (D : Link → ℕ+, `log D_a = wEnt a`);
  the old Q5 finite-code capstone re-proved **with no `hJoin` hypothesis** (the join supplied by the
  instance).
- [ ] **JI6 — the induced-G normalization + capacity corollaries**: with `G = 1/(NΛs²)`:
  `S(J) = (A_J/4)·N·Λs²`; per-link `wEnt a = (A^loc_a/4)·N·Λs²`; the patch-capacity bound
  (`A^loc_a ≤ P_a ⟹ wEnt a ≤ (P_a/4)·N·Λs²`); the area-cost quantization (nat = `4/(NΛs²)`,
  qubit = `4 log 2/(NΛs²)`).
- [ ] **JI7 — checkpoint (the two honest sentences, verbatim in the module docstring + inventory):**
  HAVE: "after JI1–JI6, `hJoin` is no longer a hypothesis for the constructed τ join or for
  nat-realizable finite-code joins, and the count normalization rewrites to `(A_J/4)·N·Λs²` with local
  capacity corollaries." HAVE NOT: "no theorem says arbitrary external real geometry has exact natural
  link dimensions, no asymptotic approximation is included, and no canonical `A0` split is asserted
  beyond the named apportionment data/policy." Delete the loop; paper/website sync on request.

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.JoinInstance` green; `#print axioms` std-3; budget 0;
AxiomAudit pins; wire `QIQTH.lean`; ONE commit + `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`;
push schannel; update this checklist + `LEAN_RESULTS_INVENTORY.md`. HONESTY: the join is deleted for the
CONSTRUCTED instance (generic at τ level, realizable at ℕ level); external-weight matching stays the old
calibration; the CCR obstruction is permanent; NEVER claim QG solved or a wall crossed. NEVER claim an
increment too hard — attempt, iterate, checkpoint only after a genuine failed attempt with the error
shown. Check for sibling jobs before each increment. Consults: `mcp__OpenAI__ask` gpt-5.5-pro (do NOT
expose the key).

## Progress log
- **2026-07-03** — plan created from the GPT-5.5-pro join-instance consult (two-level construction;
  geometry→code; A0Split named data; the τ₀ clock-window qualifier; the cut list; ordering JI1→JI7).
  NEXT → JI1.

- **2026-07-03** — **JI1 LANDED** (`QIQTH/JoinInstance.lean`, axiom-free std-3, budget 0): localAreaVar
  (the per-element linearized share δA_a) + sum_localAreaVar (= the held areaVar); A0Split (the NAMED
  background apportionment — honest data, never canonical) + the uniform-policy constructor; CAPSTONE
  sum_localArea — ∑_a (β_a + δA_a) = A0 + areaVar S h (the carried hJoin's RHS decomposed per link).
  NEXT → JI2 (the generic τ join dictionary).

- **2026-07-03** — **JI2 LANDED** (axiom-free std-3, budget 0): tauWEnt (the geometry-defined code
  weight A^loc_a/(4G)); tauDim = exp(wEnt) — the REAL positive trace-dimension (no integrality) with
  tauDim_pos; hcal_tau — THE CALIBRATION IS A THEOREM at the τ level (Real.log_exp); CAPSTONE
  hJoin_tau — the Q5 carried hJoin equality is a THEOREM for the constructed dictionary
  (inducedScreenArea G S.elems wEnt = A0 + areaVar S (classicalH pol α); geometry → code, links =
  screen elements, 0 < G). NEXT → JI3 (the τ₀ corner realization).
