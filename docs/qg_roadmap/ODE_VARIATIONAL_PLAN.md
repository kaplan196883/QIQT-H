# ODE-VARIATIONAL / JACOBI-EQUATION CAMPAIGN (K3), commissioned 2026-07-17

**Goal.** Build the missing primitive — **smooth dependence of the geodesic flow on initial
conditions → the Jacobi equation → the `r∂_r log J` congruence ODE** — closing K3, hence K4→K6 →
unconditional general curved `a₁=R/6` for the true kernel.

**Confirmed Mathlib gap (2026-07-17).** `Mathlib/Analysis/ODE/` has Picard–Lindelöf existence/uniqueness
(`PicardLindelof.lean`) + Grönwall (`Gronwall.lean`) + integral-curve existence/uniqueness, but **NO
smooth-dependence-on-IC / variational equation**. This is the genuine research-scale, Mathlib-PR-grade
undertaking. `a₁=R/6` (true kernel) is NOT claimed until K6; checkpoint precisely; never fake.

**What the repo already has (rides on).** First-order IC-smoothness is BUILT: `expMap_contDiffOn_one`
(exp is C¹ in the direction `v` — i.e. the geodesic flow's C¹ dependence on initial velocity),
`fderivExpMap_continuousOn` (the exp differential `D exp` = the Jacobi field at `t=1`, C¹),
`contDiffOn_fderiv_expMap_component` (C² components), `hasFDerivAt_geodesicField_fderiv` /
`geodesicField_fderiv_apply` (the field `F`'s fderiv `DF`), `expJet_linVariation_residual_deriv` (the
linear-variation residual), the Grönwall a-priori bounds. So the JACOBI FIELD exists (C¹); what's missing
is its ODE (the variational/Jacobi equation) and the DETERMINANT congruence ODE (Raychaudhuri).

## Phases (each an [AF] std-3 green checkpoint). New file(s) under `QIQTH/`.

### L1 — the geodesic VARIATIONAL EQUATION `QIQTH/GeodesicVariation.lean` (first brick)
The linear variation `V(t)` (the IC-derivative of the geodesic solution) satisfies the linearized ODE
`V'(t) = DF(γ(t))·V(t)` (first-order phase-space form), from `hasFDerivAt_geodesicField_fderiv` + the
chain rule + `expJet_linVariation_residual_deriv`. Reachable IF the repo's linVariation machinery
assembles into the clean variational ODE; else land the reachable part + checkpoint.

### L2 — the Jacobi field as the variational solution `QIQTH/JacobiField.lean`
Identify `D exp_p` (`fderivExpMap`) with the solution of L1's variational equation (the Jacobi field
`Y`), and its second-order form `Y'' = −R(Y,γ')γ'` (the Jacobi equation) — needs the SECOND-order
variational structure (`DF` differentiated). THE deep part; decompose or checkpoint.

### L3 — the Raychaudhuri / determinant ODE `QIQTH/Raychaudhuri.lean`
`θ = r∂_r log J = tr(Y⁻¹ Y')` (the congruence expansion) satisfies `θ' + …+ Ric(γ',γ') = 0`; hence at
leading order `r∂_r log J` connects to `Ric` — supplying the value `radialDeriv_log_det_split` (K2)
isolated. Closes K3's checkpoint.

### K4–K6 (as in `JACOBI_FIELD_PLAN.md`)
van-Vleck ODE (K4) → off-diagonal `O(1/t)` cancellation (K5) → unconditional `a₁=R/6` (K6).

## Discipline (unchanged)
One bg OPUS brick per phase; `#print axioms ⊆ std-3`; AxiomAudit pin (honest firewall); budget 0; commit +
push (SEPARATE fast calls); update plan + memory. This is the Mathlib-absent ODE-smooth-dependence
primitive — L2 (2nd-order variational) is the genuine wall; decompose or checkpoint honestly, NEVER fake.
`a₁=R/6` NOT claimed until K6.

### L progress (2026-07-17)
- L1 LANDED (53b5dd74) GeodesicVariation.lean — the geodesic variational equation: UNCONDITIONAL for the velocity/tangential Jacobi field (V=gamma' solves V'=DF(gamma)V, chain rule); CONDITIONAL general variation isolating the Mathlib-absent ODE-smooth-dependence-on-IC primitive as 2 named hyps (hV: IC-derivative exists, hswap: mixed-partial interchange).
- REMAINING = building ODE-smooth-dependence-on-IC unconditionally (discharge hV/hswap -> L2 2nd-order Jacobi eqn Y''=-RY -> L3 Raychaudhuri det ODE -> K4-K6). Mathlib LACKS this (Analysis/ODE = Picard-Lindelof + Gronwall only); it is a genuine multi-month Mathlib-PR-scale foundational build. The primitive is now precisely isolated. NATURAL TERMINAL CHECKPOINT of the loop-brick mode.
- L2a LANDED (f8f135f8) GeodesicSmoothDep.lean — smooth-dependence-on-IC discharged via Gronwall: geodesicVariation_exists (IC-derivative EXISTS = variational solution, discharges L1 hV) + hswap + capstone. First-order C1-dependence UNCONDITIONAL modulo the single carried hyp hNb = uniform C^2 Taylor remainder of geodesicField.
- L2b (in flight): discharge hNb = the uniform C^2 remainder ||F(a)-F(b)-DF(b)(a-b)||<=M||a-b||^2 (from the repo Christoffel 2nd-order Taylor remainders + geodesic_twopoint_gronwall) -> geodesicVariation_exists_uncond (first-order smooth-dependence fully unconditional modulo standard geometric regularity).
- L2b LANDED (7bf7ceab) — uniform C2 field remainder (geodesicField_uniform_C2_remainder) -> hNb DISCHARGED -> geodesicVariation_exists_uncond. ★ FIRST-ORDER geodesic smooth-dependence-on-IC now UNCONDITIONAL (modulo standard geometric regularity) — the primitive ExpMap.lean flagged as Mathlib-absent is CROSSED at first order.
- L2 (in flight): the 2nd-order Jacobi equation xi''=-R(xi,gamma')gamma' (geodesic deviation) — jacobiOperator + jacobiVariation_secondOrder (differentiate the 1st-order system) + jacobiOperator_eq_riemann (the curvature identification, the deep crux). Then L3 Raychaudhuri (r d_r log J), K4 van-Vleck ODE, K5 off-diagonal cancellation, K6 unconditional a1=R/6.
- L2 LANDED (33a487a7) JacobiEquation.lean — jacobiOperator + jacobiVariation_secondOrder (xi''=-jacobiOperator, UNCONDITIONAL). Honest finding: literal jacobiOperator=R(xi,v)v is FALSE in coords; true Jacobi eqn is COVARIANT D^2 xi/dtau^2 = -R(xi,v)v (agrees with xi'' only at RNC center). Covariant correction = the checkpoint.
- L2c (in flight): covariantDerivAlong + covariantSecondDeriv + covariant_jacobi_equation (D^2 xi/dtau^2 = -R(xi,v)v, from L2 xi''=-jacobiOperator + the covariant correction; Finset identity, L2 hand-verified it closes). Then L3 Raychaudhuri (r d_r log J), K4 van-Vleck ODE, K5 off-diagonal cancellation, K6 unconditional a1=R/6.
- L2c #1/#2 LANDED (468181ee) CovariantJacobi.lean — covariant-derivative machinery (covariantDerivAlong + covariantSecondDeriv + hasDerivAt_comp_curve); salvaged from an agent that died mid-#3 (partial built green). L2c-cont (in flight): #3 covariant_jacobi_equation D^2xi/dtau^2=-R(xi,v)v via the 3 Finset sub-identities (deriv sector, quad sector, eta-swap).
- L2c #3 (CENTERED) LANDED (e568d7ca) CovariantJacobi.lean — the covariant Jacobi equation AT AN RNC CENTER: covariant_jacobi_equation_centered (D^2xi/dtau^2 = -R(xi,v)v at Gamma=0), via covariantSecondDeriv_at_center (KEY INSIGHT: even where Gamma=0, D^2xi/dtau^2 = -jacobiOperator + sum(sum d_a Gamma^i_jk v^a)v^j xi^k — the SURVIVING dGamma correction from differentiating the connection term, NOT just xi'') + covariantJacobi_finset_match (dGamma-antisymmetrization via Gamma-lower-symm + v-symm). Carried hyps hgsymm/hC/hgamma/hVar/hGamma0 all genuine, none assume the conclusion. All [AF] std-3, budget 0. TWO prior agents stalled on the FULL off-center identity; the centered case CLOSED cleanly with the dGamma insight. ⚠ SCOPE: centered only — OFF-CENTER covariant Jacobi identity stays the labelled checkpoint; the DIAGONAL a1 needs only centered/diagonal structure so this is on the critical path. NEXT: L3 (Raychaudhuri / determinant ODE).
- L3 (Ricci SOURCE term) LANDED (b943e437) Raychaudhuri.lean (addendum, namespace QIQTH.ExpMap; the file ALREADY EXISTED with a divergence-route Raychaudhuri dev — raychaudhuri_geodesic etc. in namespace QIQTH.Curvature, imported by QiqtToGR/RaychaudhuriCongruence — appended WITHOUT touching it, no cycle). geodesicDeviation_trace_eq_ricci (UNCONDITIONAL pure algebra: trace over coord basis of the geodesic-deviation operator xi->R(xi,v)v = the Ricci quadratic form sum_sigma_nu ricci*v*v = Ric(v,v) — the whole "relate deviation operator to Ric" content) + covariantJacobi_trace_at_center (the traced CENTERED covariant Jacobi eqn over a basis-aligned Jacobi congruence = -Ric(v,v), the Raychaudhuri SOURCE term). All [AF] std-3, budget 0. ⚠ SCOPE: the -Ric(v,v) source term ONLY — NOT the full Raychaudhuri congruence ODE theta'+theta^2/(n-1)+Ric=0 (needs matrix Jacobi field, not traced pointwise identity), NOT the theta=r d_r log J=tr(Y^-1 Y') determinant-ODE connection to K1/K2 det g~=J^2 det(g o exp) (needs matrix Jacobi field + inverse + singular-at-center limit — the labelled checkpoint), NOT a1=R/6. NEXT ASSESSMENT: is the r d_r log J determinant connection (matrix Jacobi field Y + Y^-1 singular limit) reachable as decomposed bricks, or the genuine wall? then K4 van-Vleck ODE / K5 off-diag O(1/t) / K6 a1=R/6.
- K4-LEADING (directional van-Vleck 2-jet, OFF-diagonal) LANDED (3e36639c) VanVleckRadial.lean — radialDeriv_quadraticForm (UNCONDITIONAL Euler identity: r d_r of a quadratic form sum_ab c_ab w^a w^b = 2x the form) + sqrtdet_directional_hessian_ricci (sum_cd v^c v^d d_c d_d sqrt(det g)(0) = -(1/3) sum_cd Ric_cd v^c v^d — the LEADING OFF-DIAGONAL van-Vleck curvature coefficient in ALL directions, generalizing the diagonal TRACE used by J5-vanvleck; from RNCExpansion.sqrtdet_pd_pd's RNC metric 2-jet, carries hg/hg0/hdg0/htr). Obtained algebraically from the metric 2-jet WITHOUT any matrix Jacobi field / Y^-1. All [AF] std-3, budget 0.
- ⛔⛔ TERMINAL WALL OF THE REACHABLE CAMPAIGN (assessed 2026-07-18): the frontier has been pushed to the RNC-2-jet limit. The next genuine advance toward K6 = the UNIFORM-in-v (all-orders) van-Vleck radial ODE (r d_r) log sqrt(det g~) = the exact curvature expression that cancels the off-diagonal O(1/t) term — this needs r d_r log J ALONG RAYS (v != 0), i.e. the matrix Jacobi field Y(r) as the exp-map Jacobian + its inverse Y^-1 (singular at the center) = the documented Mathlib-absent off-radial Jacobi-field / smooth-dependence-on-IC wall (ExpMap.lean:998-1000, end of VanVleckCancellation.lean). This is NOT loop-brick-sized — a multi-month Mathlib-PR-scale foundational build. HONEST ENDPOINT: parametrix DIAGONAL a1=R/6 DERIVED (J5-vanvleck); leading OFF-DIAGONAL van-Vleck 2-jet coefficient DERIVED (K4-leading, this brick); true-kernel a1=R/6 CONDITIONAL on the uniform-in-v van-Vleck radial ODE = the off-radial Jacobi Y^-1 wall. a1=R/6 (true kernel) still carried G3. HELD for user direction (commission off-radial Jacobi as a sustained project, pursue an explicit-curved-example exact check, or redirect).
- CONSTANT-CURVATURE MODEL (exact radial ODE) LANDED (b62adc13) RaychaudhuriConstCurv.lean — proceeding with the explicit-curved-example option (user away, 4-option question unanswered; best judgment per "keep going"). jacobi_logderiv_riccati (from the scalar Jacobi ODE S''=−K·S, the geodesic-deviation log-derivative u=S'/S satisfies the EXACT Riccati u'=−K−u² — ALL ORDERS, not just the 2-jet) + raychaudhuri_constant_curvature[_theta] (θ=(n−1)u obeys θ'=(n−1)(−K−u²) division-free, and the textbook θ'=−(n−1)K−θ²/(n−1) for n≥2) + jacobiOde_sin (unit sphere K=1 realizes the hypotheses). Pure 1-var calculus, import Mathlib only, no g/gi. All [AF] std-3, budget 0. ★ SIGNIFICANCE: this CLOSES the uniform-in-r (all-orders) van-Vleck radial ODE EXACTLY for the canonical CONSTANT-curvature model — the very ODE the general variable-curvature case blocks on — WITHOUT any matrix Jacobi field / Y⁻¹; (n−1)K = Ric(∂_r,∂_r) ties to L3's covariantJacobi_trace_at_center. ⚠ SCOPE: constant-curvature model ONLY; general variable-curvature true kernel + a₁=R/6 still need the off-radial Jacobi Y⁻¹ wall. NEXT ASSESS: const-curv van-Vleck determinant Θ=(r/S)^{n-1} → Laplace-Beltrami → a₁=R/6 EXACTLY for constant curvature (partial discharge of the general wall by the canonical example), reachability via the explicit radial profile.
