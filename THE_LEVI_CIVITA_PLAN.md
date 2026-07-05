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
> **2026-07-06 status.** Discovery: the *existence* half of BOTH routes was already committed —
> component (`Curvature.lean`: `christoffel`, `christoffel_symm`, `metric_compat`, `riemann`/`ricci`) and
> abstract (`LeviCivita.lean`: `koszul`, `koszul_torsion_free`, `koszul_metric_compat`, `leviCivita`,
> `leviCivita_koszul`). The genuinely-missing, load-bearing content was the **UNIQUENESS** half (the Koszul
> *solve* = the fundamental theorem). This increment adds it: `koszul_lowered` + `christoffel_unique`
> (component) and `leviCivita_unique` (abstract). All axiom-free std-3, pure algebra (no metric smoothness).
> LC1/LC2 stand CLOSED (existence + the new uniqueness); LC3 (Leibniz packaging of `leviCivita` as a global
> `IsCovariantDerivativeOn`) stays the honest gate; LC4 is realised at the COMPONENT level (uniqueness makes
> `ricci g gi` canonically the metric Ricci).

- [x] **LC1 — the Koszul map (algebraic solve).** From a `PseudoRiemannianMetric gm`, define `covLC` by
  `2·gm(∇_X Y, Z) = X·gm(Y,Z) + Y·gm(Z,X) − Z·gm(X,Y) + gm([X,Y],Z) − gm([Y,Z],X) + gm([Z,X],Y)`, solving for
  `∇_X Y` via `gm.raise` / `lowerEquiv` injectivity. If metric-field smoothness (the derivative terms `X·gm(Y,Z)`)
  is NOT yet available (`PseudoRiemannian.lean` flags this as a later increment), land the ALGEBRAIC/pointwise
  Koszul solve FIRST — the expression as the unique solution — deferring the differential Leibniz to LC3.
- [x] **LC2 — torsion-freeness.** Encoded: `koszul_torsion_free` (`koszul X Y Z − koszul Y X Z = 2g([X,Y],Z)`)
  and the component `christoffel_symm` (`Γ^i_{jk}=Γ^i_{kj}`) — both pre-existing; and torsion-freeness is now a
  HYPOTHESIS the uniqueness theorem consumes to pin the connection.
- [~] **LC3 — (GATED on metric smoothness) Leibniz + metric-compatibility.** Component `metric_compat` (`∇g=0`)
  is DONE (algebraic, no smoothness). The abstract-manifold `IsCovariantDerivativeOn` packaging of `leviCivita`
  (which needs the differential Leibniz `X·gm(Y,Z)=gm(∇_XY,Z)+gm(Y,∇_XZ)` from a smooth metric field) STAYS the
  honest gate: `PseudoRiemannianMetric` still flags metric-field smoothness as a later increment, and Mathlib's
  `IsCovariantDerivativeOn.leibniz` requires it. Not forced.
- [x] **LC4 — wire to curvature (COMPONENT level).** `christoffel_unique` makes `christoffel`/`riemann`/`ricci`
  (already built, feeding on `christoffel`) canonically the curvature of THE unique metric connection ⟹ a genuine
  **metric Ricci** `QIQTH.Curvature.ricci g gi`. The ABSTRACT `ManifoldCurvature.ricci ∘ leviCivita` wiring
  remains gated on LC3 (leviCivita as a global connection). Still NOT the R-coefficient.

## New results (2026-07-06)
- `QIQTH.Curvature.koszul_lowered` **[AF std-3]** — the lowered Koszul solve `∑σ g_{σa}Γ^σ_{bc} =
  ½(∂_b g_{ac}+∂_c g_{ab}−∂_a g_{bc})` forced for any torsion-free metric-compatible `Γ` (pure algebra).
- `QIQTH.Curvature.christoffel_unique` **[AF std-3]** — the fundamental theorem: any torsion-free,
  metric-compatible connection `= christoffel g gi`. Uniqueness of the Levi-Civita connection.
- `QIQTH.ManifoldGR.leviCivita_unique` **[AF std-3]** — abstract counterpart: a vector whose lowered covector is
  `½·koszulForm` IS `leviCivita` (musical `♯` single-valued by nondegeneracy).

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
- **2026-07-06 (built):** found the *existence* half of both routes already committed; built the missing
  **UNIQUENESS** half — `koszul_lowered` + `christoffel_unique` (component fundamental theorem, pure algebra) and
  `leviCivita_unique` (abstract musical solve). All axiom-free std-3; `lake build QIQTH.Curvature
  QIQTH.LeviCivita` green; budget check clean. LC1/LC2/LC4(component) closed; LC3 (abstract Leibniz packaging)
  stays the honest smoothness gate. FOUNDATION brick — NOT the `(1/6−ξ)R` coefficient, does NOT move numerical G.
