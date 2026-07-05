# THE LEVI-CIVITA CONNECTION — the first load-bearing brick toward curved-space G (Koszul from the metric)

**Status:** SCOPED (fable consult verified against Mathlib pin v4.30.0, 2026-07). **Track:** QG / numerical-G frontier.
**Loop:** the CONTINUOUS QG PROGRAM. **Commits LOCAL ONLY** (session no-push until the user authorizes).

## Binding verdict
This is the smallest genuinely-**LOAD-BEARING**, buildable-now brick on the curved-G path: the Levi-Civita
connection of a (pseudo-)Riemannian metric via the **Koszul formula**, turning the repo's already-built
**abstract** curvature/Ricci (`ManifoldCurvature.lean`, defined for an *arbitrary* connection) into **the metric
connection's** curvature — i.e. a genuine **metric Ricci tensor**. **HONEST HAVE-NOT (binding for all copy):** it is
a FOUNDATION STONE, **NOT** the Seeley–DeWitt `(1/6−ξ)R` coefficient, and it does **NOT** move the numerical value
of G. Never bill any increment here as "deriving κ=1/6", "sharpening G", or "curved heat kernel".

## The full gated chain (context — why the R-coefficient is NOT near-term)
metric → **Levi-Civita ∇ (THIS brick)** → geodesics / exponential map → RNC expansion
`g_{ab}(x)=δ_{ab}−⅓R_{acbd}x^cx^d`, `√det g = 1−⅙R_{cd}x^cx^d` → heat-kernel diagonal small-`t` expansion
`(4πt)^{−d/2}(a₀+a₁t+…)`, `a₁=(⅙−ξ)R−E`. The `⅙ = ½(from √) · ⅓(RNC curvature normalization)`; the `⅓` is born
ONLY from the geodesic-gauge Taylor expansion — NOT a Gaussian/contraction fact (the flat `∫G_t x^ax^b=2tδ^{ab}`
moment is already built and gives only the contraction). Every shortcut dodging the geometry leaves the `⅓` carried
= DECORATIVE. Mathlib at the pin has NO Levi-Civita, NO geodesics/expMap, NO Laplace–Beltrami, NO heat kernel, NO
sphere eigenvalues — the R-coefficient is gated on that multi-file layer (no proof-assistant precedent anywhere).

## Mathlib / repo inventory (verified at pin)
PRESENT (Mathlib): `IsCovariantDerivativeOn` / `CovariantDerivative` (`.leibniz/.add/.difference`, torsion),
`VectorField.mlieBracket`, `RiemannianMetric`/`IsRiemannianManifold` (pos-def only), integral-curve scaffolding,
flat `laplacianWithin`. ABSENT (Mathlib): Levi-Civita, Riemann tensor, geodesics/expMap, Laplace–Beltrami, heat
kernel, spherical harmonics/eigenvalues. Repo ALREADY has (axiom-free): `QIQTH/ManifoldCurvature.lean` (abstract
`curvature` endomorphism + `ricci` = trace for any connection; antisymmetry, tensoriality, torsion, Bianchi),
`QIQTH/Curvature.lean` (component-level `christoffel`/`riemann`/`ricci`/`einsteinTensor` + linearized `riemannLin`),
`QIQTH/PseudoRiemannian.lean` (`PseudoRiemannianMetric` symmetric nondegenerate + musical `lower/raise/lowerEquiv`).

## Increments
- [ ] **LC1 — the Koszul map (algebraic solve).** From a `PseudoRiemannianMetric gm`, define `covLC` by
  `2·gm(∇_X Y, Z) = X·gm(Y,Z) + Y·gm(Z,X) − Z·gm(X,Y) + gm([X,Y],Z) − gm([Y,Z],X) + gm([Z,X],Y)`, solving for
  `∇_X Y` via `gm.raise` / `lowerEquiv` injectivity. If metric-field smoothness (the derivative terms `X·gm(Y,Z)`)
  is NOT yet available (`PseudoRiemannian.lean` flags this as a later increment), land the ALGEBRAIC/pointwise
  Koszul solve FIRST — the expression as the unique solution — deferring the differential Leibniz to LC3.
- [ ] **LC2 — torsion-freeness.** `torsion covLC = 0` (repo's `torsion` def): `∇_X Y − ∇_Y X = [X,Y]` from Koszul
  antisymmetry. Pure algebra.
- [ ] **LC3 — (GATED on metric smoothness) Leibniz + metric-compatibility.** `IsCovariantDerivativeOn F covLC univ`
  + `X·gm(Y,Z) = gm(∇_XY,Z)+gm(Y,∇_XZ)`. std-4/5; land ONLY if the smoothness API cooperates, else honest checkpoint.
- [ ] **LC4 — wire to curvature.** Feed `covLC` into `ManifoldCurvature.curvature`/`ricci` → the METRIC Ricci
  `ricci_g` — the first curved geometric object built from a metric. Still NOT the R-coefficient.

## Verbatim HAVE / HAVE-NOT checkpoint sentences
- **HAVE:** "The Levi-Civita connection of a (pseudo-)Riemannian metric is constructed from the Koszul formula
  (`covLC`), torsion-free, [metric-compatible if LC3], and fed into the abstract curvature to give a genuine metric
  Ricci — the first curved geometric object derived from a metric in the repo, axiom-free std-3, closing the
  'arbitrary connection → THE metric connection' gap."
- **HAVE NOT:** "This is a FOUNDATION brick, NOT the Seeley–DeWitt `(1/6−ξ)R` coefficient, and it does NOT move the
  numerical value of G. Producing `(1/6−ξ)R` still requires geodesics/the exponential map, the RNC metric/`√g`
  curvature expansion, and a manifold heat-kernel diagonal expansion — a multi-file Riemannian layer Mathlib wholly
  lacks (no proof-assistant precedent). Numerical-G remains gated; `G=1/(N Λ_s²)` stays a relation."

## Failure modes
- Metric-smoothness API absent ⟹ LC1's differential terms don't elaborate ⟹ land the pointwise/algebraic Koszul
  solve + LC2, checkpoint LC3 with the exact missing API.
- `PseudoRiemannianMetric.raise`/`lowerEquiv` may need nondegeneracy plumbing — verify the musical iso is total.
- NEVER fake the `⅙`/`⅓` — no "carry `∂∂g=−⅓R` then derive `√g`" lemma billed as deriving κ (decorative).

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` std-3; `bash
scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire `QIQTH.lean`; ONE commit on main with the
`Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>` trailer; **LOCAL ONLY — no push**; update
this plan + `LEAN_RESULTS_INVENTORY.md`. NO `sorry`; carried inputs as hypotheses NEVER Lean axioms; NEVER claim
numerical-G moved, the R-coefficient derived, κ=1/6, or a curved heat kernel.

## Progress log
- **2026-07 (scoped):** consult (fable, high) verified the gated chain + Mathlib absence + the repo's existing
  abstract-curvature/musical-iso towers; LC1 (Koszul) identified as the smallest load-bearing buildable brick,
  honestly a foundation stone (does NOT move G).
