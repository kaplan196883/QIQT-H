# Verification-status update for QIQT_Foundations_Paper.md (deliverable A)

The paper's formal-verification claims (abstract paragraph + §11.2a + §11.4a) describe a
state with **~33–37 named interface axioms**. As of 2026-06-12 the Lean development has
been driven to **zero project axioms** (CI budget 0; audit trail ends "★ THE QIQT-H FINITE
CORE IS NOW AXIOM-FREE"). The drafts below are drop-in replacements that correct this while
**preserving the paper's honesty boundary** — *axiom-free in Lean ≠ the physics is
established*. Three things must stay distinct and are kept distinct below:

1. **What is now axiom-free:** the finite/Type-I *deductive core* — the conditional
   representation theorems, the structural lemmas, and the negative audits.
2. **What remains a physics postulate:** (FQ), the Macroscopic Definiteness Conjecture, the
   Canonical IC Measure (Born) Principle, Lorentz covariance of the selector. Being
   axiom-free in Lean says nothing about whether these physical claims are *true*.
3. **What remains a formalization frontier:** the continuum Type II / Fock / modular tower
   (in active development; not complete).

---

## A.1 — Replacement for the abstract's "Formal verification." paragraph

> **Formal verification.** The deductive core of this framework is machine-checked in Lean 4
> / Mathlib and is, as of 2026-06, **axiom-free**: every audited theorem depends only on the
> three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), with **no
> `sorry`** and **no project-specific axioms** (CI-guarded by `scripts/axiom_budget_check.sh`
> at budget 0; per-theorem `#print axioms` recorded in `lean/mathlib/QIQTH/AxiomAudit.lean`,
> 795 directives over 122 modules and ~1350 theorems). This is the endpoint of a sustained
> discharge effort that retired every interface axiom the earlier drafts relied on — the
> project axiom total fell **57 → 40 → 37 → … → 0** as each named axiom was either proved in
> a concrete finite model or replaced by an explicit hypothesis. Landmarks: the entire
> `ArakiInterface` layer (11 axioms, incl. Donald's identity and the Holevo bound
> `χ ≤ H(p)`) and the `EntropyBridge` were discharged to theorems via a `CStarMatrix`
> operator-monotonicity bridge; the Goldstein–Struyve Schur classification, the
> `RelEntPositivity`/Klein, DPI, and Tsirelson-attainability axioms were each proved
> axiom-free; and a **finite no-collapse Born representation theorem** (capacity ⇒ unique
> actual value; effect-Gleason ⇒ Born weights from positivity; product preparation ⇒
> independent, Chebyshev-typical trials) is established unconditionally. The formalization
> also includes a deliberate suite of **negative audits** proving what does *not* follow:
> linear unitary decoherence does not concentrate branch weights (`NoConcentration`); the
> structural axioms do not single out Born (`NoBornFromNothing`); support preservation is
> strictly weaker than Born equivariance (`EquivarianceGap`); operational click-statistics
> underdetermine the IC measure (`OperationalNoGo`). **What machine verification does and
> does not establish must be stated plainly:** it certifies that the framework's *conditional
> and structural* mathematics is correct and rests on no hidden axiom — it does **not**
> establish the framework's *physical* postulates (the (FQ) bound, the Macroscopic
> Definiteness Conjecture, the Canonical IC Measure / Born principle, Lorentz covariance of
> the selector), which remain the open problems of §11.4. A continuum Type II / Fock /
> modular-flow tower (`QIQTH/Fock`, `QIQTH/Spectral`, `QIQTH/Entropy`) is in active
> development toward those open problems and is not complete. See `lean/mathlib/QIQTH/`.

*(Rationale: replaces the long, now-inaccurate "57→40, two remaining axioms" narrative with
the accurate axiom-free endpoint, keeps the negative audits, and — critically — keeps the
proved/postulated/frontier boundary explicit so the upgrade does not read as "the theory is
proved.")*

---

## A.2 — Replacement note for §11.2a ("The mathematical status of the framework")

Add/replace the status framing with:

> **Updated formal-verification status (2026-06).** The honest characterization in this
> section — "scaffolding + axiom + qualitative consequences, no explicit theorems for the
> central claims" — remains correct **about the physics**. What has changed is the *formal*
> status of the deductive core: the Lean development is now **axiom-free** (0 project axioms,
> no `sorry`). Concretely, three layers must be distinguished:
>
> | Layer | Formal status (2026-06) |
> |---|---|
> | Conditional/structural core (Theorems 3, 6, 7; Lemma 1; Donald's identity; no-signaling; finite Born representation; the negative audits) | **Machine-checked, axiom-free** (standard Lean axioms only) |
> | Physical postulates ((FQ); Macroscopic Definiteness Conjecture; Canonical IC/Born Principle; Lorentz covariance of $A_R[\Phi,\lambda]$) | **Open** — not theorems; axiom-free Lean does not bear on their truth |
> | Continuum realization (Type II crossed-product entropy scaling; Fock/Weyl/CCR modular flow) | **Formalization frontier** — in progress (`QIQTH/Fock`, `Spectral`, `Entropy`) |
>
> A subtlety the axiom count alone cannot see: a *vacuous* hypothesis (e.g. an interface
> axiom whose antecedent is `True`) can make a theorem trivially true without any axiom being
> declared. The project guards against this with a vacuity lint (`scripts/vacuity_lint.sh`)
> in addition to the axiom-budget check; one historical instance — a
> `set_level_locality_from_unitary_dilation (h_alg : True)` axiom that was *logically
> inconsistent* — was caught and converted to an explicit hypothesis (see §11.4.5). The
> current lint reports a single benign site (an indiscrete-preorder definition in a Lorentz
> witness), documented in `AXIOM_CONTRACTS.md`.

---

## A.3 — Refreshed preamble for the §11.4a Claim-to-Lean matrix

> The matrix below maps each major claim to its Lean theorem. **Status labels:** **U** —
> unconditional (standard Lean axioms only); **N** — negative audit / counterexample. The
> earlier **C** (conditional on a cited external theorem) and **P** (programmatic interface
> axiom) labels are now **historical**: as of 2026-06 every former C/P row has been
> discharged to **U**, so the project carries **no interface axioms** (`AxiomAudit.lean`;
> `axiom_budget_check.sh` budget 0). In particular the rows previously marked P — the
> Goldstein–Struyve Schur classification (`step1_schur_classification` →
> `schur_classification_real`), tensor multiplicativity, the Mackey–Gleason/Radon–Nikodym
> packaging, Donald's identity, and the ArakiInterface/EntropyBridge layer — are now proved
> axiom-free in their finite-dimensional realizations. The continuum versions of these
> results remain the cited/open frontier (§11.4.3, §11.4.3a, Open Problems 3/3b), and the
> *physical* postulates they would serve are unaffected by their formal discharge.

*(Then the existing table can keep its rows; flip the residual `C`/`P` status cells to `U`
with a parenthetical "(finite-dim; continuum open)" where the continuum case is still open —
chiefly the Type II / Fock rows.)*

---

## Verification of the numbers in this draft (for the author to re-check before splicing)

- `grep -rhE '^axiom ' lean/mathlib/QIQTH/ | wc -l` → **0**
- `bash lean/mathlib/scripts/axiom_budget_check.sh` → budget 0, clean
- modules: **122**; theorems+lemmas: **1347**; `#print axioms` directives: **795**
- vacuity lint: **1** benign site (`LorentzWitness.lean:180`, indiscrete preorder)
- trajectory source: audit-note comments in `scripts/axiom_budget_check.sh`
