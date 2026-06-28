# Tier 1 — The semiclassical geometric-code skeleton (geometry ASSUMED)

> **Goal.** Prove, rigorously and (where possible) in Lean, the **holographic semiclassical skeleton**:
> fixed-area sectors, the JLMS / operator-algebra-QEC area identity, edge/bulk factorization,
> generalized entropy, and the finite-dimensional analogue of Type II behaviour — **all conditional
> on an assumed geometric code subspace.** This tier is honest *exactly because* it assumes geometry.
> It is the target that Tier 3 must later *derive*. Most of it is category **(b)** (a real frontier,
> but standard in AdS/CFT and plausibly formalizable conditionally); the continuum CPW pieces are
> harder **(b)**.

**The non-circularity rule (binding).** Nothing in Tier 1 may be cited as evidence that geometry
*emerges*. Tier 1 says: "*If* there is a semiclassical geometric code subspace with an area operator,
*then* the holographic entropy/modular structure follows." Whether such a subspace arises from a
finite substrate is **Tier 2 + Tier 3**. CPW/Witten crossed products, fixed-area sectors, and RT all
live here precisely because they *presuppose* the geometry — using them to "get emergent spacetime"
is the circularity this roadmap was recut to forbid.

---

## 1.1 Finite-dimensional JLMS / algebraic-QEC theorem with a central area operator  *(category (b); headline deliverable)*

**The structure to formalize.** A code subspace with a direct-sum (fixed-area-sector) decomposition
```
𝓗_code = ⊕_α 𝓗_{a_α} ⊗ 𝓗_{ā_α},     L_A = Σ_α ℓ_α P_α   (central area operator)
```
where `P_α` projects onto sector `α` and `ℓ_α` is its area eigenvalue. Prove the algebraic-QEC
entropy and modular identities:
```
S(ρ_A)   = Tr(ρ L_A) + S_bulk(ρ_a) + (center/Shannon terms)     (FLM/JLMS form)
K_A      = L_A + K_bulk            on the code subspace          (JLMS modular identity)
```
These are *known* finite-dimensional facts (Harlow's "Ryu–Takayanagi from QEC", the
operator-algebra/center treatment of edge modes). The novelty is **formalizing them in Lean** and
wiring them to the Tier-0 Gap-2 theorem: a fixed-area sector is exactly where the area term `ℓ_α` is a
constant and the edge marginal is maximally mixed — so **fixed-area sectors discharge Gap-2** at the
semiclassical level.

**Why this is the right Tier-1 first deliverable.** It is *much* more tractable than continuum CPW,
yet it captures the entire structural lesson: area is an **edge/center operator**, JLMS is an
**algebraic-QEC identity**, and the Gap-2 KMS/capacity reconciliation is the fixed-area degeneracy.
It directly upgrades Tier 0 §0.1 from "compatibility condition" to "realized in the geometric-code
model."

**Lean target.** `QIQTH/GeometricCode/JLMS.lean`:
- `code_subspace` structure (`⊕_α 𝓗_a ⊗ 𝓗_ā`, projections `P_α`, area eigenvalues `ℓ_α`),
- `areaOperator_central` (`L_A` commutes with the code algebra),
- `flm_entropy` (`S(ρ_A) = Tr(ρ L_A) + S_bulk + center`),
- `jlms_modular` (`K_A = L_A + K_bulk`),
- `fixedArea_sector_discharges_gap2` (link to `Obstructions.KmsCapacity`).
- Reuses `QuantumRelativeEntropy.lean`, `SpectralPVM.lean`, `FiniteModularTheory.lean`.

**Acceptance.** Green, axiom-free; docstring states the code subspace is **assumed**, not derived.
Ledger tag: every theorem here consumes `ASSUMED-GEOMETRIC-CODE`.

---

## 1.2 BW modular flow beyond the free scalar  *(category (b) analytic; (b)/(c) for full formalization)*

**Claim to establish.** Bisognano–Wichmann (modular flow of the wedge algebra = boost) is **not**
special to the free scalar — it holds in axiomatic relativistic QFT under Wightman/AQFT assumptions.
So "modular flow = geometric boost / Unruh temperature" extends conceptually to interacting fields.

**Honest caveat.** Rigorous *interacting* 4D QFT is not available at the level Lean formalization
would want. So:
- **Analytic deliverable (b):** a written note establishing BW-generality from the Wightman axioms +
  the existing one-particle BW results (`Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional`),
  making explicit which axioms are used.
- **Formalization (b)/(c):** keep the Lean substrate at the free field; mark interacting BW as a
  `CITED-PHYSICS` ledger entry, not a Lean theorem. Do not claim a formalized interacting result.

**This retires the "free scalar only" restriction *conceptually* for the modular/thermal slot**, while
honestly leaving the formalization at the free field.

---

## 1.3 Finite-dimensional Type II analogue (the honest stand-in for CPW)  *(category (b))*

**What CPW/Witten gives and what it assumes.** The crossed product `𝓜 ⋊_{σ^ω} ℝ` produces a Type II
algebra with a trace, a density operator, generalized entropy, and an "area-like" operator — but it
**presupposes** a semiclassical bulk background, a gravitational constraint relating boost/ADM energy
to area, a code subspace around a classical geometry, and a `G→0`/large-`N` expansion. It is a
*description of subregions in a theory that already has gravity*.

**Tier-1 honest version.** Rather than chase the continuum crossed product as if it were emergence,
formalize the **finite-dimensional Type II behaviour** that the geometric-code model already exhibits:
the central area operator `L_A` (§1.1) plays the role of the crossed-product generator; the trace is
the flat trace on each fixed-area sector. State explicitly:
- `typeII_area_operator_is_a_DESCRIPTION` — a docstring-level and ledger-level assertion that this
  structure **assumes** the geometric phase and is therefore a *target* for Tier 3, **not** a
  derivation of geometry.

**Continuum CPW (optional, frontier).** If/when the Tomita–Takesaki / Stone / Borel-FC infrastructure
lands (`STONE_THEOREM_PLAN.md`, `TOMITA_TAKESAKI_ROADMAP.md`), the genuine continuum crossed product
becomes a *conditional formal* deliverable (category (b)) — but it stays in Tier 1, tagged
`ASSUMES-SEMICLASSICAL-BACKGROUND`.

---

## 1.4 RT / first-law ⇒ linearized Einstein (conditional)  *(category (b), conditional)*

**Claim.** In the holographic (geometry-assumed) setting, the entanglement first law `δS = δ⟨K⟩`
plus RT yields the **linearized** Einstein equations in the bulk (Faulkner–Lashkari–Van Raamsdonk).

**Tier-1 status.** This is *standard in AdS/CFT* but **conditional on holography/RT** — it assumes
exactly the bulk geometry under discussion. So it belongs in Tier 1 as a conditional theorem, and its
*first-principles* version ("from finite capacity, no holography assumed") is a **Tier 3** target
(§3.4). The honest deliverable here is a written derivation + a Lean formalization of the
*linear-algebra core* (first law ⇒ linear constraint) with the geometric/holographic inputs as
labelled hypotheses.

**Ledger tag:** `ASSUMED-HOLOGRAPHY` + `ASSUMED-RT`.

---

## Tier 1 honest scale

This tier is **(b)** throughout. The finite-dimensional JLMS/QEC theorem (§1.1) is genuinely
near-to-mid-term and high-value; BW-generality (§1.2) is analytically standard but only conditionally
formalizable; the continuum CPW and RT⇒Einstein pieces (§1.3–1.4) are real frontiers but *known
physics* under their assumptions. **None of Tier 1 is quantum gravity** — it is the conditional
semiclassical skeleton. Its entire job is to be the precise, audited *target* that Tier 3 must derive
from the Tier-2 substrate.

**First concrete move:** §1.1 `QIQTH/GeometricCode/JLMS.lean` — the finite JLMS/QEC theorem with the
central area operator, linked to Tier-0 Gap-2.

**Exit criterion:** the semiclassical skeleton (fixed-area, JLMS, edge/bulk, finite Type II) is
formalized *as conditional theorems with `ASSUMES-GEOMETRY` ledger tags*, and the Gap-2 discharge is
realized in the geometric-code model. We now have a precise definition of "what emergence must
produce" — handed to Tier 3.
