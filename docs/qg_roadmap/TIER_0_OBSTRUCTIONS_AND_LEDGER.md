# Tier 0 — Obstruction theorems + the assumption ledger

> **Goal.** Before building anything, make the *boundary between what is proved and what is assumed*
> mathematically precise. Tier 0 produces (i) a set of **finite-dimensional obstruction / sufficiency
> theorems** that turn the program's hand-wavy "residuals" into exact necessary-and-sufficient
> conditions, and (ii) a **machine-readable assumption dependency graph** so every later claim traces
> to a labelled input. Tier 0 assumes *no* geometry and introduces *no* new physics. It is almost
> entirely category **(a)** — near-term Lean/analytic work — and it is the cheapest, highest-leverage
> thing to do first.

**Why Tier 0 exists.** The two errors GPT-5.5-pro caught (A2 mis-tiering; CPW circularity) were both
*assumption-tracking* failures: a conditional input was being treated as a derivation. Tier 0
institutionalizes the fix. Every later tier is allowed to *assume* things, but only against an
explicit ledger entry.

---

## 0.1 The Gap-2 KMS–capacity compatibility theorem  *(category (a); the headline deliverable)*

**The problem, made precise.** The classical GR residual ("joint reference-state identification") is:
the horizon equilibrium must be simultaneously
- the **BW/Unruh modular state** `ρ_BW ∝ e^{−2π K_boost}` (a `β>0` KMS/Gibbs state), and
- **capacity-saturating** on its record/edge sector: `ρ_rec = I_rec / dim 𝓗_rec` (maximally mixed,
  i.e. `β=0` on that sector).

These look contradictory (`β>0` vs `β=0`). The theorem pins down *exactly* when they reconcile.

**Theorem (to formalize, finite-dimensional).** Let `𝓗 = 𝓗_rec ⊗ 𝓗_rest`, `ρ = e^{−βK}/Z` with `β>0`.
Then the record marginal `Tr_rest ρ` is maximally mixed **iff** `K` restricted to the record tensor
factor is proportional to the identity (the record sector is a *modular zero-mode / fixed-area
degeneracy sector*).

**Sufficiency (the constructive half).** With a block/fixed-area decomposition
`𝓗 = ⊕_a 𝓗_{edge,a} ⊗ 𝓗_{bulk,a}` and `K_a = c_a · I_{edge,a} + I_{edge,a} ⊗ K_{bulk,a}`, the edge
marginal is maximally mixed **while** the bulk marginal is genuinely BW/KMS. This is the
finite-dimensional skeleton of the JLMS `K_∂R = A/4G + K_bulk` story: in a fixed-area sector the
area term is a *constant* `c_a`, so it contributes a flat (maximally-mixed) edge factor.

**Why this matters.** It converts "Gap-2 is the open residual" from prose into a precise statement:
*Gap-2 is dischargeable exactly to the extent that the horizon record sector is a fixed-area /
boost-zero-mode degeneracy sector.* That is a concrete, checkable physical condition — and it tells us
the *physical* discharge of Gap-2 lives in Tier 1 (edge-mode/fixed-area structure), not Tier 0.

**Lean target.** New module `QIQTH/Obstructions/KmsCapacity.lean`:
- `kms_record_maxmixed_iff_modular_trivial` (the iff),
- `edge_bulk_fixedArea_suffices` (the constructive sufficiency on `⊕_a 𝓗_{edge,a}⊗𝓗_{bulk,a}`),
- wire into `QIQTH.lean` + `AxiomAudit.lean`; budget 0.
- Reuses `FiniteModularTheory.lean` (`modAut`, `kms_condition`, `stateOf`, `sigmaDiag`).

**Acceptance.** Both theorems green, axiom-free; the docstring states plainly that the *physical*
realization of the edge⊗bulk split is deferred to Tier 1 and is not claimed here.

---

## 0.2 The "finiteness does NOT imply area" obstruction theorem  *(category (a); the anti-overclaim guardrail)*

**Statement.** Exhibit, as a Lean theorem, an explicit finite local model in which capacity is
**volume-law**: for `n` sites of on-site dimension `d`, `log dim 𝓗_R = n · log d ∝ Vol(R)`. Conclude:
the finite-capacity postulate `S_vN ≤ log N_R` is **logically independent** of the area law `log N_R ∝ A`.

**Why this is worth a theorem.** It is the formal statement of the correction that reshaped the whole
roadmap. Having it *in Lean*, cited from the paper and the assumption ledger, permanently forecloses
the "finite information ⇒ holography" overclaim. It also scopes the Sakharov bridge correctly: the
area *form* is derived **conditionally** (local QFT on a smooth background + a covariant cutoff), and
the genuine area-*capacity* law is a Tier-2/3 emergence result, not a Tier-0/A fact.

**Lean target.** `QIQTH/Obstructions/VolumeLawCounterexample.lean`:
- `tensorLattice_capacity_volume` : `log (dim (𝓗_lattice n d)) = n * log d` (volume scaling),
- `finiteness_does_not_imply_area` : a corollary packaging the independence statement
  (finiteness bound holds, area bound fails) for the tensor lattice.
- cite from `docs/SAKHAROV_KG_STAGE_B.md` and the assumption ledger.

**Acceptance.** Green, axiom-free; cross-referenced from `qiqth_one_quarter_status` and the README
non-circularity rule.

---

## 0.3 The selector / covariance obstruction (already largely in hand)  *(category (a), consolidation)*

QIQT-H already has `CovariantGluing.no_covariant_selector` (an invariant *measure* exists; an
invariant *selector* cannot) and `LorentzSelectionStrong.upvm_covariant_probability`. Tier 0 simply
**catalogues** these as the foundational-axis obstruction set and states the open frontier crisply:
a covariant *typicality measure* `μ` (OP3b) — and, critically, flags that when geometry becomes
dynamical (Tier 3), `μ` must be reinterpreted as a measure over **diffeomorphism-equivalence classes
of records/histories**, not records on a fixed slice (see Tier 3 §3.5 and the "problem of time").

No new Lean here; this section is a ledger consolidation + a forward pointer.

---

## 0.4 The machine-readable assumption dependency graph  *(category (a); the connective tissue)*

**Deliverable.** A single generated artifact — extend the existing per-target state-report tooling
(`scripts/report_*.py`, `scripts/target_probe.lean.tmpl`) — that emits, for every capstone theorem
across Born / Lorentz / GR and the new obstruction modules:
- the `#print axioms` set (confirming standard-3 / budget 0),
- every Prop-hypothesis (the typeclass/structural assumptions actually consumed),
- a **labelled tag** per hypothesis: `DERIVED` | `CONDITIONAL-BRIDGE` | `CITED-PHYSICS` | `OPEN`.

The tags are the honest contract. Examples:
- `δS=ηδA` → `DERIVED` (DifferentialAreaLaw),
- area *form* S∝A → `CONDITIONAL-BRIDGE` (Sakharov/Stage-B),
- "local QFT algebras are Type III₁" → `CITED-PHYSICS` (Buchholz–Wichmann),
- joint reference-state physical realization → `OPEN` (Gap-2, until Tier 1),
- value of G → `OPEN` (species/cutoff, until Tier 2).

**Output.** `reports/ASSUMPTION_LEDGER.md` (generated) + a stable JSON the website and paper can pull
from. The README non-circularity rule becomes *enforceable*: any later theorem that consumes a
`CITED-PHYSICS`/`OPEN` input cannot be reported as "emergent."

**Acceptance.** `python scripts/build_assumption_ledger.py` regenerates deterministically (modulo
timestamp/git-rev); a renamed/missing theorem makes the Lean probe error (self-validating).

---

## Tier 0 honest scale

Everything here is **(a) near-term**: weeks of focused Lean + tooling, no Mathlib gaps, no new
physics. Tier 0 retires *zero* of the deep open problems — but it is the single best
return-on-effort step, because it (1) makes Gap-2 a precise condition, (2) permanently scopes the
finiteness↛area claim, and (3) gives every downstream tier an audited contract to build against.

**First concrete move:** §0.1 `kms_record_maxmixed_iff_modular_trivial` + `edge_bulk_fixedArea_suffices`.

**Exit criterion:** the assumption ledger is generated and green; Gap-2 and finiteness↛area are
theorems; the boundary "proved | conditional | cited | open" is machine-checked, not editorial.
