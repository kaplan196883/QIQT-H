# THE RNC SECOND-ORDER EXPANSION — the ⅙ conformal normalization toward curved-space G

**Status:** SCOPED (fable consult verified against pin v4.30.0 + `QIQTH/Curvature.lean`, 2026-07). **Track:** QG /
numerical-G frontier. **Loop:** CONTINUOUS QG PROGRAM. **Commits LOCAL ONLY** (session no-push).

## Binding verdict
The next load-bearing brick after the Levi-Civita connection (`christoffel_unique`, done). The Riemann-normal-
coordinate second-order metric expansion `g_{ab}(x)=δ_{ab}−⅓R_{acbd}x^cx^d`, hence `√det g = 1−⅙R_{cd}x^cx^d`, on
the component tower `QIQTH/Curvature.lean` (`pd`, `christoffel`, `riemann`, `ricci`). The `⅙ = ½(√)·⅓(RNC curvature
normalization)` **is the source of the `κ=1/6` conformal factor** that `heat_a1_of_RNC` currently CITES — so this is
genuinely load-bearing (moves κ=1/6 from cited toward derived). It is buildable NOW: the radial/normal gauge is a
**falsifiable pointwise constraint on the `christoffel` field** (like the file's `hinv`/`hmc`), NOT a geodesic/exp-map
construction. **HONEST HAVE-NOT:** this derives the ⅙ normalization; it does **NOT** give the numerical value of G
(N species-count + Λ_s scale remain), and the full `a₁=(1/6−ξ)R−E` heat-kernel coefficient still needs the E/ξ term
+ verifying the √det g → a₁ connection in `heat_a1_of_RNC` is complete. Never claim numerical-G moved or a curved
heat kernel.

## THE SHARP LOAD-BEARING TEST (binding — the implementer MUST satisfy it)
> Remove the radial/normal-gauge hypothesis: if the stated conclusion becomes **FALSE** (the totally-symmetric part
> `S_{abcd}` of `∂∂g(0)` re-enters `tr∂∂g` / breaks `∂∂g=−⅓(R+R)`), the increment is **load-bearing**; if the
> conclusion is merely an index-rearrangement of a fed-in `∂∂g(0)=−⅓(R+R)`, it is **decorative** — reject it.
The gauge MUST be a falsifiable constraint on `christoffel` (e.g. `∑_{jk} christoffel g gi i j k y · y^j · y^k = 0`,
or `∂_{(l}Γ^i_{jk)}(0)=0`), NEVER a `:= True` stub or a pre-contracted `∂∂g`-equals-answer (vacuity hole).

## Increments
- [x] **RNC1 — the `√det g` atom (CLOSED, AXIOM-FREE std-3, 2026-07-06).** `QIQTH/RNCExpansion.lean`,
  `sqrtdet_pd_pd` + `sqrtdet_taylor_coeff`. GIVEN the CARRIED, load-bearing `htr : ∑_a ∂_c∂_d g_{aa}(0) = −⅔Ric_{cd}`
  (a genuine `pd(pd g)` equation, NOT `:= True`), with `g(0)=δ`, `∂g(0)=0`: the second derivative is
  `∂_c∂_d √det g (0) = −⅓Ric_{cd}` (`sqrtdet_pd_pd`), and the quadratic Taylor COEFFICIENT (half of it) is
  `−⅙Ric_{cd}`, i.e. `√det g = 1 − ⅙R_{cd}x^cx^d` (`sqrtdet_taylor_coeff`) — the `⅙` = source of `κ=1/6`. Route
  DONE as planned: finite-product Leibniz for `pd` (`pd_prod`, mirror of `pd_sum`) on `det g=∑_σ sgnσ ∏_i g_{σi,i}`;
  `∂g(0)=0` drops the cross terms; `g(0)=δ` collapses the perm-sum to ONLY `σ=1` (`perm_moves_in_erase` +
  `Matrix.one_apply`) ⟹ `∂_c∂_d(det g)(0)=tr∂∂g(0)`; then `Real.hasDerivAt_sqrt` Taylor at `det g(0)=1,∂(det g)(0)=0`
  gives the `½` (`sqrt_pd_pd`): `½·(−⅔)=−⅓` second deriv, coeff `¼·(−⅔)=−⅙`. NB the literal `pd(pd √det g)` second
  derivative is `−⅓Ric`; the `−⅙Ric` is the TAYLOR COEFFICIENT (= ½·second derivative) — both green. `htr` is
  genuinely CARRIED + load-bearing (used via `rw [htr]`; removing it makes `−⅓Ric` false, passing the sharp test).
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`; budget 0; pinned in `AxiomAudit.lean`; wired into
  `QIQTH.lean`. HONEST: the `⅙` normalization ONLY — NOT numerical-G (N, Λ_s, E/ξ remain), NOT a curved heat kernel.
- [x] **RNC2 — R1 forward `R↔∂∂g` (CLOSED, AXIOM-FREE std-3, 2026-07-06).** `QIQTH/RNCExpansion.lean`,
  `rnc_riemann_hessian` : from `g(0)=δ` (via `gi(0)=δ`), `∂g(0)=0`, `R^ρ_{σμν}(0)=½(∂_μ∂_σg_{ρν}−∂_μ∂_ρg_{νσ}
  −∂_ν∂_σg_{ρμ}+∂_ν∂_ρg_{μσ})(0)`. Route DONE: `riemann_at_origin` (`Γ(0)=0` drops `ΓΓ`) + `pd_christoffel_origin`
  (the `∂Γ = ½(∂∂g+∂∂g−∂∂g)` atom: `(∂gi)·(∂g)` term vanishes since the `∂g` bracket is `0` at origin, `gi(0)=δ`
  collapses the inverse) + `pd_comm` Schwarz cancels the symmetric `∂_μ∂_ν g_{ρσ}` piece. Connects the tower.
- [x] **RNC3 — R2 inversion / the `−⅓`, DISCHARGES `htr` (CLOSED, AXIOM-FREE std-3→4, 2026-07-06).**
  `QIQTH/RNCExpansion.lean`, `rnc_htr_of_gauge` : carrying the FALSIFIABLE normal-coordinate gauge
  `hgauge : ∀ i a b c, ∂_aΓ^i_{bc}(0)+∂_bΓ^i_{ca}(0)+∂_cΓ^i_{ab}(0)=0` (the totally-symmetrized `∂Γ`, a genuine
  christoffel-symmetrization equation — NOT a `:=True` stub, NOT a pre-contracted `∂∂g=−⅓(R+R)`), the metric-Hessian
  trace is FORCED: `∑_a ∂_c∂_d g_{aa}(0) = −⅔ Ric_{cd}` — EXACTLY RNC1's carried `htr`, now DERIVED. **Sharp test
  PASSES:** `∑_ν ∂_cΓ^ν_{νd}` equals BOTH `½ tr∂∂g` (calculus, `sum_pd_christoffel_trace`) AND `−⅓Ric` (gauge, via
  `pd_christoffel_solve` = the finite `linarith` inversion `∂_aΓ^i_{bc}=⅓(R^i_{bac}+R^i_{cab})` + `sum_riemann_ii_zero`
  first-pair antisymmetry + `riemann_antisymm`); combining forces `tr∂∂g=−⅔Ric`. Remove `hgauge` and the `pd_christoffel_solve`
  step fails → the trace part of `∂∂g` is unconstrained → `−⅔Ric` is false. Payoff `sqrtdet_taylor_coeff_of_gauge` :
  `½∂_c∂_d √det g(0) = −⅙Ric_{cd}` GIVEN THE GAUGE (feeds `rnc_htr_of_gauge` into `sqrtdet_taylor_coeff`) — the `⅙`
  is now gauge-derived, not carried. `#print axioms` std-3; budget 0; pinned in `AxiomAudit.lean`.
  (GOLD variant: the primitive `∑Γyy=0` gauge — needs THIRD-order `pd`/Schwarz, std-5, gated; defer.)
- [ ] **RNC4 — wire to `heat_a1_of_RNC`.** Feed the derived RNC Ricci data into the existing conditional a₁ assembly,
  discharging its carried RNC input + the cited κ=1/6. Honest: still not numerical-G (N, Λ_s, E/ξ remain).

## Verbatim HAVE / HAVE-NOT
- **HAVE:** "The Riemann-normal-coordinate `√det g = 1 − ⅙R_{cd}x^cx^d` expansion is machine-checked on the component
  curvature tower, with the ⅙ DERIVED from a falsifiable radial-gauge constraint on `christoffel` (not carried) — the
  source of the κ=1/6 conformal factor, discharging what `heat_a1_of_RNC` cited. Axiom-free std-3."
- **HAVE NOT:** "This is the ⅙ normalization only. It does NOT give the numerical value of G (the species count N and
  the granularity scale Λ_s remain carried; `G=1/(N Λ_s²)` stays a relation), does NOT build a curved heat kernel, and
  the full `a₁=(1/6−ξ)R−E` still needs the E/ξ potential term. Numerical-G remains gated."

## Failure modes
- Finite-product Leibniz for `pd` harder than `pd_sum` ⟹ land RNC1 via a direct `n`-small (`Fin 2`/`Fin 3`) det if the
  general permutation-sum resists; checkpoint the general-`n` step.
- Third-order `pd`/Schwarz absent ⟹ use the `∂_{(l}Γ_{jk)}(0)=0`-as-hypothesis RNC3 (std-4), NOT the gold `∑Γyy=0`
  (std-5); do NOT build third-order `pd` speculatively.
- NEVER collapse RNC3 into carrying `∂∂g=−⅓(R+R)` directly — that FAILS the load-bearing test (decorative).

## Discipline (every increment)
`lake build QIQTH.<module>` green; `#print axioms` std-3; budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit
LOCAL ONLY (no push) with the Co-Authored-By trailer; update this plan + `LEAN_RESULTS_INVENTORY.md`. NO `sorry`;
gauge carried as a FALSIFIABLE hypothesis never an axiom/`:=True`; NEVER claim numerical-G moved or κ derived until
RNC3 lands the gauge-derived (not carried) `−⅓`.

## Progress log
- **2026-07 (scoped):** consult (fable, high) verified the RNC expansion is load-bearing + buildable on `Curvature.lean`
  (radial gauge as a christoffel constraint, no geodesics); atoms RNC1 (√det g, std-4 green-first) / RNC2 (forward,
  std-3) / RNC3 (inversion, std-4) identified with the sharp load-bearing test.
- **2026-07-06 (RNC1 CLOSED):** `QIQTH/RNCExpansion.lean` built AXIOM-FREE (std-3), `lake build` green, budget 0.
  `sqrtdet_pd_pd : ∂_c∂_d √det g (0) = −⅓Ric_{cd}` and `sqrtdet_taylor_coeff : ½·∂_c∂_d √det g (0) = −⅙Ric_{cd}`
  (the `√det g = 1 − ⅙R_{cd}x^cx^d` coefficient — source of `κ=1/6`), CONDITIONAL on the carried, load-bearing
  `htr : ∑_a ∂_c∂_d g_{aa}(0) = −⅔Ric_{cd}`. Infra proven en route: `pd_prod` (finite-product Leibniz for `pd`,
  by hand — Mathlib lacks `ContDiff.finset_prod`), `pd_congr` (germ/eventually-eq congruence), `sqrt_pd_pd` (the `½`
  √-Taylor factor), the origin permutation-sum collapse `perm_moves_in_erase`. NOT numerical-G, NOT a curved heat
  kernel.
- **2026-07-06 (RNC2 + RNC3 CLOSED — `htr` DISCHARGED FROM THE GAUGE):** `QIQTH/RNCExpansion.lean` extended
  AXIOM-FREE (std-3), `lake build QIQTH.RNCExpansion` green, `#print axioms` = `[propext, Classical.choice, Quot.sound]`
  for all four new theorems, budget 0. **RNC2** `rnc_riemann_hessian` : `R^ρ_{σμν}(0)=½(∂_μ∂_σg_{ρν}−∂_μ∂_ρg_{νσ}
  −∂_ν∂_σg_{ρμ}+∂_ν∂_ρg_{μσ})(0)`. **RNC3** `rnc_htr_of_gauge` : the normal-coordinate gauge `hgauge` (totally-
  symmetrized `∂Γ(0)=0`, a falsifiable christoffel equation) FORCES `∑_a ∂_c∂_d g_{aa}(0)=−⅔Ric_{cd}` = RNC1's `htr`,
  now DERIVED not carried. Sharp load-bearing test PASSES (gauge is not decorative; removing it breaks `−⅔Ric`).
  Payoff `sqrtdet_taylor_coeff_of_gauge` : `½∂_c∂_d √det g(0)=−⅙Ric_{cd}` GIVEN THE GAUGE — the `⅙`/`κ=1/6` is now
  gauge-derived. Infra: `christoffel_zero_at_origin`, `riemann_at_origin`, `pd_christoffel_origin` (the `∂Γ↔∂∂g`
  atom), `sum_pd_christoffel_trace`, `pd_christoffel_solve` (the finite `linarith` inversion), `sum_riemann_ii_zero`.
  HONEST: the `⅙` normalization ONLY — NOT numerical-G (N, Λ_s, E/ξ remain), NOT a curved heat kernel. NEXT: RNC4
  (wire the gauge-derived Ricci data into `heat_a1_of_RNC`, discharging its cited `κ=1/6`).
