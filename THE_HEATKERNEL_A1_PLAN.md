# THE HEAT-KERNEL a₁ CAMPAIGN — the derived-analysis half of the (1/6−ξ)R coefficient

**Status:** COMPLETE (2026-07-05) — A1–A4 ALL LANDED (A3 succeeded, moment matrix DERIVED for all d). Axiom-free std-3, budget 0. **Loop:** fe280fa3. **Commits LOCAL ONLY** (session no-push).
**Consult:** fable high-reasoning agent ab1397370779af8d8 (2026-07-05) — verified BUILDABLE, not
a wall; the load-bearing Gaussian second moment is reachable at the pin.

## Binding verdict (READ — the honesty boundary is the whole point)

This campaign moves the numerical-G frontier's a₁ coefficient from "fully cited" to
"cited-geometry + DERIVED-analysis" — the QIQT-H house style (carry the hard geometry as a
labelled hypothesis, prove the tractable analysis). CRITICAL honesty correction from the
consult:
- **DERIVED (the analysis):** the flat-space Gaussian second moment
  `∫ x² · G_t(x) dx = 2t` (G_t = (√(4πt))⁻¹ e^{−x²/4t}), hence the contraction
  `∑_{αβ} R_{αβ}·(2t δ^{αβ}) = 2t·R` — the machinery that turns the RNC curvature
  coefficients into the scalar-R form.
- **CARRIED / CITED (the geometry):** the RNC covariant metric/measure expansion
  (√g = 1 − (1/6)R_{αβ}x^αx^β + …) AND the assembled curvature coefficient value **κ = 1/6**.
  **The second moment does NOT produce the 1/6** — it produces only the `2t·R` contraction.
  NEVER claim the Gaussian integral yields the 1/6; that is carried, cited textbook data
  (Vassilevich/Parker–Toms/Gilkey). This keeps clear of the vacuous-hypothesis trap: every
  carried coefficient is named, cited, and visible.

Verified facts: Mathlib has NO direct `∫ x²e^{−ax²}` lemma in the Gaussian file, but
`variance_id_gaussianReal` (Var = v) + `integral_gaussianReal_eq_integral_smul` (the pdf
bridge; `gaussianPDFReal 0 (2t) x = G_t(x)` EXACTLY) + `variance_eq_integral` +
`integral_id_gaussianReal` deliver the second moment. d-dim via
`integral_fintype_prod_volume_eq_prod`. Carried geometry: abstract `Rμν : Fin d → Fin d → ℝ`
+ scalar `R = ∑ i, Rμν i i` (or the repo's `Curvature.ricci`/`scalarCurv`). Connection point:
`InducedNewtonConstant.SpeciesContent.cScalar` (the cited scalar a₁ coefficient whose R-part
this upgrades).

## The increments (new file `QIQTH/HeatKernelA1.lean`)

- [x] **A1 — the 1-D second moment (the whole load-bearing analysis).** ✅ DONE
  `gaussianSecondMoment_oneD (t) (ht : 0<t) : ∫ x:ℝ, ((√(4πt))⁻¹ * Real.exp (-x^2/(4t))) * x^2
  = 2*t`. Route: v := (2t).toNNReal, hcoe : (v:ℝ)=2t; rewrite integrand as
  gaussianPDFReal 0 v x * x² (gaussianPDFReal_def + hcoe); ← integral_gaussianReal_eq_integral_smul
  hv (smul=mul) folds to ∫ x² ∂gaussianReal 0 v; = Var[id; gaussianReal 0 v] via
  variance_eq_integral measurable_id'.aemeasurable + integral_id_gaussianReal (mean 0);
  close with variance_id_gaussianReal + hcoe. Risk LOW-MEDIUM (ℝ≥0 casts, smul/(x-0)² rewrites;
  no missing analysis).
- [x] **A2 — normalization + first moment.** ✅ DONE `gaussianZerothMoment_oneD : ∫ x, G_t x = 1`
  (gaussianReal a probability measure via the bridge) and `gaussianFirstMoment_oneD :
  ∫ x, G_t x * x = 0` (integral_id_gaussianReal, μ=0). Risk LOW.
- [x] **A3 (OPTIONAL, time-boxed) — the d-dim moment matrix.** ✅ DONE (Fubini hazard did NOT materialize) `gaussianMoment_diag (d)(t)(ht)
  (i j : Fin d) : ∫ x:(Fin d→ℝ), (∏ k, G_t (x k)) * (x i * x j) = 2t * (if i=j then 1 else 0)`.
  Route: integral_fintype_prod_volume_eq_prod split; i=j ⟹ (∫G_t)^{d−1}·(∫G_t x²) = 2t
  (A1+A2); i≠j ⟹ factor ∫G_t x = 0. Needs Fubini integrability side-goals (integrable_
  gaussianPDFReal). Risk MEDIUM (Fubini plumbing). CUTTABLE: if it stalls, carry the moment
  matrix hM as a hypothesis in A4 (still honest — A1 is the derived nugget).
- [x] **A4 — the conditional a₁ assembly (the theorem).** ✅ DONE
  `heat_a1_of_RNC (d)(t)(ht)(ξ m : ℝ) (Rμν : Fin d → Fin d → ℝ) (κ)(hκ : κ = 1/6)
  (Mmatrix)(hM : ∀ i j, Mmatrix i j = 2t*(if i=j then 1 else 0)) (Rscl)(hR : Rscl = ∑ i, Rμν i i)
  : (1/(2t)) * (κ * ∑ i, ∑ j, Rμν i j * Mmatrix i j) - ξ*Rscl - m^2 = (1/6 - ξ)*Rscl - m^2`.
  Proof: pure algebra — simp [hM, hκ, hR], Finset.sum_ite_eq collapses to 2t·Rscl,
  (1/2t)·κ·2t·Rscl = (1/6)Rscl, ring. hM DERIVED in A3 or CARRIED. Risk LOW. Corollary:
  note this is the scalar a₁ whose curvature part underlies SpeciesContent.cScalar — the
  cited→derived-analysis upgrade. **Keep the honesty label crisp: the (1/2t)·κ·(2t·R) = κR
  step shows the moment supplies 2t·R and the CARRIED κ=1/6 supplies the value.**

Order: A1 → A2 → A4 (all low-risk, delivers the honest conditional theorem) → attempt A3 to
replace hM with the derived d-dim moment; ship with hM carried + A3 labelled frontier if
Fubini stalls.

## The checkpoint language (verbatim)

HAVE: "The derived-analysis half of the a₁ Seeley–DeWitt heat-kernel coefficient is
machine-checked: the flat-space Gaussian second moment ∫ x²·(√(4πt))⁻¹e^{−x²/4t} dx = 2t
(from Mathlib's Gaussian variance), the d-dim moment matrix ∫(∏G_t)x_ix_j = 2t δ_{ij}, and
the contraction that turns the Riemann-normal-coordinate Ricci coefficients into the scalar
form ∑ R_{αβ}·2tδ^{αβ} = 2t·R — assembling, with the carried RNC coefficients, to the scalar
a₁ = (1/6 − ξ)R − m². This moves the (1/6 − ξ)R conformal-coupling coefficient underlying the
species accounting of Newton's G from FULLY CITED to CITED-GEOMETRY + DERIVED-ANALYSIS —
the Gaussian-moment analysis is now a theorem. Axiom-free, std-3."

HAVE NOT: "The GEOMETRY is carried, not derived: the RNC covariant metric/measure expansion
(√g = 1 − (1/6)R_{αβ}x^αx^β + …) and the assembled curvature coefficient VALUE κ = 1/6 are
labelled hypotheses / cited textbook data — the Gaussian second moment supplies ONLY the
2t·R contraction machinery, NOT the 1/6, which is a coincidence-limit of the covariant
heat-kernel expansion (Riemann normal coordinates / Synge world function) that Mathlib does
not have. No Riemannian heat kernel, no Seeley–DeWitt recursion, no derivation of κ; this
does NOT compute the numerical value of G (the full species-coefficient accounting with real
SM content remains the frontier). It is the honest analysis-half of one coefficient, not the
curved-space derivation."

## Per-increment discipline

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit
on main with the Co-Authored-By: Claude Opus 4.8 trailer; **LOCAL ONLY — no push until the
user says so**; update this checklist + Progress log AND LEAN_RESULTS_INVENTORY.md; NO sorry;
carried inputs as hypotheses NEVER Lean axioms; NEVER claim the Gaussian moment yields the
1/6, NEVER claim the numerical value of G, a curved-space heat kernel, or any wall crossed
beyond what is literally proved; NEVER claim an increment too hard (attempt, iterate,
checkpoint only after a genuine failed attempt with the error shown); check sibling jobs
(git log/status — stray website/.tex edits in the tree, LEAVE THEM) first; explicit git
paths only (Lean + plan + inventory + audit ONLY).

## Progress log

- **2026-07-05** — Scoped (consult: BUILDABLE, the Gaussian second moment is reachable via
  variance_id_gaussianReal + the pdf bridge; honesty correction — the moment gives 2t·R not
  the 1/6, so κ=1/6 stays carried/cited). Surfaced with the user as "option 2" after the
  numerical-G wall characterization; the user offered Vassilevich/Parker–Toms for refs/ (not
  needed for the conditional theorem, which carries the geometry).

- **2026-07-05** — **A1+A2 LANDED (green first try).** HeatKernelA1.lean: heatKernel1D +
  heatKernel1D_eq_pdf (the EXACT bridge gaussianPDFReal 0 (2t) = G_t); ★
  gaussianSecondMoment_oneD (∫ G_t x² = 2t — the load-bearing analysis, via
  variance_fun_id_gaussianReal + integral_gaussianReal_eq_integral_smul + variance_eq_integral
  + integral_id_gaussianReal); gaussianZerothMoment_oneD (= 1); gaussianFirstMoment_oneD (= 0).
  Std-3, budget 0. Next: A4 (the conditional a₁ assembly — carrying hM + κ=1/6); A3 optional.

- **2026-07-05** — **A4 LANDED (green, one field_simp fix).** heat_a1_of_RNC — given the
  carried RNC Ricci + the moment matrix M = 2t·δ + κ=1/6 (CITED), the Gaussian-averaged t¹
  coefficient = (1/6−ξ)R − m²; the sum collapses via Finset.sum_eq_single, (1/2t)·(1/6)·(2t·R)
  = (1/6)R by field_simp. Plus heat_a1_moment_from_secondMoment — for d=1 the moment matrix IS
  gaussianSecondMoment_oneD (the derived nugget genuinely feeds the assembly). Honesty label
  crisp: the moment gives 2t·R, κ=1/6 is carried. Std-3, budget 0. Next: A3 (d-dim moment,
  optional/time-boxed) then checkpoint.

- **2026-07-05** — **A3 LANDED — CAMPAIGN COMPLETE (green first try).** gaussianMoment_diag:
  ∫ (∏_k G_t(x_k)) x_i x_j = 2t·δ_ij for the product heat kernel — the Fubini hazard did NOT
  materialize (integral_fintype_prod_volume_eq_prod is UNCONDITIONAL, no per-factor
  integrability); by_cases i=j, Finset.prod_mul_distrib + Fintype.prod_ite_eq' + the three
  1-D moments. ★ heat_a1_of_RNC_derived DISCHARGES the carried hM via gaussianMoment_diag —
  so the 2t·δ contraction is DERIVED for ALL d, not just carried; only κ=1/6 + the Ricci
  datum stay carried/cited geometry. Std-3, budget 0. THE CAMPAIGN STANDS: the analysis-half
  of the a₁ coefficient is machine-checked; the numerical-G frontier's honest boundary is
  now (1/6=cited) + (contraction=derived). Per the standing directive the loop continues.
