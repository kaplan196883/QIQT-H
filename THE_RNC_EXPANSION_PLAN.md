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
- [ ] **RNC1 — the `√det g` atom (CLEAN GREEN FIRST, std-4).** GIVEN `tr∂∂g(0) = −⅔Ric` (carried honestly at this
  stage), derive `√det g` 2nd-order coefficient `= −⅙R_{cd}`. Route (dodges the det-derivative gap by evaluating at
  origin where `g(0)=δ`, `∂g(0)=0`): Leibniz permutation sum `det g=∑_σ sgnσ ∏_i g_{i,σi}` + finite-product Leibniz
  for `pd` (Mathlib `deriv_finsetProd`, mirror of the file's `pd_sum`) ⟹ `∂_c∂_d(det g)(0)=tr(∂∂g)(0)`, `det g(0)=1`,
  `∂detg(0)=0`; then `Real.hasDerivAt_sqrt` Taylor ⟹ coeff `= ¼·(−⅔R_{cd}) = −⅙R_{cd}`. Load-bearing GIVEN the input.
  Risk: LOW (only the finite-product Leibniz plumbing).
- [ ] **RNC2 — R1 forward `R↔∂∂g` (std-3, green).** From `g(0)=δ`, `∂g(0)=0`: `R_{ρσμν}(0)=½(∂_μ∂_σg_{ρν}−∂_μ∂_ρg_{νσ}
  −∂_ν∂_σg_{ρμ}+∂_ν∂_ρg_{μσ})(0)` via `riemann` def + `pd_mul` + `pd_comm` Schwarz (all present). Connects the tower.
- [ ] **RNC3 — R2 inversion / the `−⅓` (std-4).** Carry the gauge `∂_{(l}Γ^i_{jk)}(0)=0` (the load-bearing normal-
  coordinate condition), combine with `R^i_{jkl}(0)=∂_kΓ^i_{lj}−∂_lΓ^i_{kj}`, solve the finite antisymmetrize/
  symmetrize system for `∂Γ(0)=−⅓(R+R)`, push through `christoffel` to `tr∂∂g(0)=−⅔Ric` — discharging RNC1's carried
  input. (GOLD variant: the primitive `∑Γyy=0` gauge — needs THIRD-order `pd`/Schwarz, std-5, gated; defer.)
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
