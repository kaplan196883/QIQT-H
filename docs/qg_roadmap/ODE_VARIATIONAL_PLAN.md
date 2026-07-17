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
