# Plan 53 — Closing gaps 2 & 3 of the Jacobson equation-of-state derivation

The component-level derivation (plans 51/52) is complete and axiom-free: the chain
*per-null Clausius → tensor crux → contracted Bianchi → `G+Λg = a·T` with genuine constant Λ* is
machine-checked. Four honest residuals remained. The user directed us to close **gap 2** (cited
physics → formalized) and **gap 3** (single coordinate patch `Fin n → ℝ` → abstract manifold), with
the chosen routes:

- **Gap 3 → full abstract-manifold stack** (not the lighter covariance proof). Build the
  pseudo-Riemannian curvature machinery on Mathlib's 2025 `CovariantDerivative`, since Mathlib has
  **no** curvature / Ricci / Einstein / Lorentzian-metric infrastructure.
- **Gap 2 → formalize Raychaudhuri focusing.** HONEST CEILING (stated up front, not negotiable):
  **Unruh temperature is irreducibly QFT** (Bogoliubov/KMS on the Rindler wedge) and **cannot** be
  formalized without relativistic QFT in Mathlib — it stays cited as the constant `η`. The area law is
  gap 1 (excluded). So gap 2 *narrows* to "Unruh + area law" but never fully closes; we machine-check
  only the geometric focusing `R_{μν}k^μk^ν`.

This is a **multi-month, Mathlib-grade campaign**. It ships as axiom-free green increments; the budget
guard stays at 0 throughout. Pro flagged the full stack as "recertifies textbook DG, low marginal
value" — we proceed anyway per the user's explicit choice, but track honestly that the *physics*
content (what makes GR emerge) lives in the already-done component derivation; this campaign upgrades
the *rigor/generality* of the geometric substrate.

## What Mathlib HAS (verified 2026-06-19, recon)
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/{Basic,Torsion}.lean` —
`IsCovariantDerivativeOn`, `CovariantDerivative` (Koszul connection on a vector bundle; convention
`cov σ x (X x) = (∇_X σ) x`), additivity + Leibniz, torsion, affine combinations, difference one-form.
`VectorField/LieBracket.lean` — `mlieBracket I X Y` with `_swap` (antisymm), `_self`, `_add_{left,right}`,
`_smul_{left,right}`. Tangent bundle, `mfderiv`, `ContMDiff`, smooth sections. **Riemannian** metrics
(positive-definite only).

## What Mathlib LACKS (we build) — the build order
Each step = its own axiom-free file/lemma, green `lake build`, `#print axioms` clean, AxiomAudit entry.

- **P1 — Curvature of a connection** *(STARTED — `QIQTH/ManifoldCurvature.lean`)*.
  - ✅ `curvature cov X Y σ x = ∇_X∇_Yσ − ∇_Y∇_Xσ − ∇_[X,Y]σ`; ✅ `curvature_antisymm` (R(X,Y)=−R(Y,X));
    ✅ `curvature_self` (R(X,X)=0). Axiom-free.
  - ✅ **Tensoriality in `X`,`Y`** — `curvature_smul_left` (`R(fX,Y)σ=f·R(X,Y)σ`) + `curvature_smul_right`.
    The Leibniz term from `∇_{fX}=f∇_X` cancels the `−(Yf)X` term of `[fX,Y]=f[X,Y]−(Yf)X` (both the same
    `d% f x (Y x)`). Needs `[CompleteSpace E] [IsManifold I 2 M]` + section/field differentiability. Axiom-free.
  - ✅ **Additivity in `X`,`Y`** — `curvature_add_left`/`_right`. With tensoriality, `R` is now
    bilinear+tensorial in its two vector-field slots. Axiom-free.
  - ✅ **Additivity in the section slot** — `curvature_add_section` (`R(X,Y)(σ+σ')=R(X,Y)σ+R(X,Y)σ'`),
    via `funext`+`cov.add` (global differentiability of `σ,σ'` avoids germ-localisation). Curvature now
    additive in all three slots + tensorial in the two vector-field slots. **P1 structural core DONE.**
  - **WALL HIT (2026-06-19):** `C∞`-linearity in the section slot `R(X,Y)(fσ)=f·R(X,Y)σ` reduces (after
    the double-Leibniz cancellation, traced in full) to the **Lie-bracket-as-commutator on functions**:
    `(d%f)([X,Y]) = X(Yf) − Y(Xf)`. Mathlib has this ONLY at the normed-space level
    (`VectorField.fderiv_apply_lieBracket_of_isSymmSndFDerivAt`, `Analysis/Calculus/VectorField.lean`) —
    there is **no manifold (`mfderiv`/`mlieBracket`) version**. The same commutator/symmetric-second-
    derivative gap blocks **P2 first Bianchi** (Jacobi at the manifold level) and recurs in Ricci. This is
    the anticipated "Mathlib-grade" frontier. THREE honest options (see decision below): (a) build the
    manifold commutator + symmetric-second-derivative theory (multi-week Mathlib-grade); (b) accept the
    commutator as a **labeled cited hypothesis** (matches the project's per-null-Clausius/Unruh discipline)
    and finish σ-tensoriality + Bianchi modulo it; (c) pivot to **P3 (Lorentzian metric)**, which is
    wall-free but a fresh design task. P1's structural core (curvature + antisymmetry + X,Y-tensoriality +
    all-slot additivity, all axiom-free) stands as the clean checkpoint regardless.
- **P2 — Algebraic (first) Bianchi.** For a *torsion-free* connection (Mathlib `torsion`), the cyclic
  sum `∑_cyc R(X,Y)Z = 0`. Needs torsion-free + Jacobi identity of `mlieBracket` (check Mathlib has it).
- **P3 — Pseudo-Riemannian / Lorentzian metric.** Mathlib's metric is positive-definite; define a
  bundle of **nondegenerate symmetric bilinear forms** on `TM` (arbitrary signature), smooth, with the
  musical isomorphism `♭/♯` from nondegeneracy. The genuinely new foundation Mathlib lacks.
- **P4 — Levi-Civita connection.** The unique torsion-free metric-compatible `CovariantDerivative` via
  the **Koszul formula**; prove existence (it IS a covariant derivative — Leibniz/add) and uniqueness.
  Heaviest analytic step.
- **P5 — Riemann (1,3)/(0,4), Ricci, scalar, Einstein.** Lower an index with the metric; trace to Ricci
  and scalar; `G = Ric − ½R g`. Symmetries: pair antisymmetry, first Bianchi (from P2), `R_{(μν)}` Ricci
  symmetry.
- **P6 — Second Bianchi + contracted `∇^μG=0`**, abstractly (the manifold analogue of `Curvature.lean`'s
  machine-checked component result). Recovers Jacobson's conservation/Bianchi step coordinate-free.
- **P7 — Raychaudhuri focusing (gap 2).** Null geodesic congruence: expansion `θ`, shear `σ`, the
  focusing equation `dθ/dλ = −θ²/(n−2) − σ² − R_{μν}k^μk^ν`. Machine-check the **geometric** content
  (the `R_{μν}k^μk^ν` term). Unruh `T` + area law remain cited.
- **P8 — Abstract field equation.** Assemble: the per-null Clausius relation (with Unruh+area-law cited)
  + P5/P6 ⇒ `G_{μν}+Λg_{μν}=a·T_{μν}` on a genuine Lorentzian manifold. The manifold-level analogue of
  `einstein_field_equation_real_global`.

## Honest scale & stopping rule
P3 (Lorentzian metric) and P4 (Levi-Civita) are each a multi-week Mathlib-grade build; P7 (null
congruences) is the hardest geometry. If any step exceeds what Mathlib analysis supports, stop at the
last green checkpoint and cite the remainder (as with the Type-III / Araki frontier). The campaign's
*value* is rigor/generality of the geometric substrate — the physics that makes GR emerge is already
machine-checked in the component derivation (plans 51/52), and **Unruh + the area law are irreducible
and stay cited regardless of how far this goes.** No step claims to derive GR "from nothing."

## Verification
Per increment: `lake build QIQTH.ManifoldCurvature` (then the relevant module) green; `#print axioms`
= `propext, Classical.choice, Quot.sound`; `bash scripts/axiom_budget_check.sh` stays at 0; one commit
per increment. Cross-check each curvature identity against its standard statement (do Carmo / Wald).
