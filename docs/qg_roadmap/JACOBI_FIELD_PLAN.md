# JACOBI-FIELD CAMPAIGN — the off-diagonal van-Vleck ODE (the last wall), commissioned 2026-07-17

**Goal.** Cross the final wall of the heat-kernel `a₁=R/6` program: the **off-diagonal `O(1/t)`
van-Vleck cancellation** (the radial-log-derivative-of-det / **Jacobi ODE** identity), which turns the
conditional capstone (C6) + the DERIVED diagonal `a₁=R/6` (J5-vanvleck) into **unconditional general
curved `a₁=R/6` for the true kernel**.

**Where we are (all axiom-free, pushed):** the entire convergence campaign (C1–C6 + C4a/C4b) + the
Jacobi/van-Vleck campaign J1–J5-vanvleck. In particular:
- the parametrix **diagonal `a₁=R/6` is DERIVED** (`VanVleckCancellation.laplaceBeltrami_detpow_diag`:
  `Δ_g((det g)^{−1/4})(0) = (∑Ric_ii)/6`);
- the off-diagonal residual is unconditionally DECOMPOSED
  (`HeatResidualBound.parametrixResidual_offdiag_absorbed`) into the radial-transport term + two named
  `O(r²)` residues, with the residue Gaussian bounds built (`ResidueBound`);
- **the SOLE remaining gap** is the off-diagonal `O(1/t)` term: the identity
  `(r∂_r) log√(det g̃)(v) = −(radial expansion of the geodesic congruence)` — the **van-Vleck / Jacobi
  ODE** — which needs the exponential-map Jacobian's radial structure (the Jacobi equation), the shared
  Riemannian-heat-kernel gap absent from every proof assistant.

**Honest scale (binding).** This is research-grade, multi-session — the geodesic-deviation / smooth-
dependence-on-IC infrastructure Mathlib lacks. `a₁=R/6` for the TRUE kernel is NOT claimed until K6.
Checkpoint precisely; never fake. What is reachable: the BRIDGE from the van-Vleck (`det g̃`) to the
exp-map Jacobian (K1), and possibly its radial structure (K2); the Jacobi equation itself (K3) is the
genuine wall.

## What is already BUILT (rides on)
- `PullbackMetric.lean`: `expPullbackMetric` `g̃ = exp_p^* g`, `expMap`, `fderiv_expMap_zero`,
  `jacobian_component_expMap`, `expPullback_radial_gauge` (2nd-jet radial gauge via `hpd2`).
- `ExpMap.lean`/`ExpMapContDiff.lean`: `geodesicSol`/`geodesicField`, `expMap_contDiffOn_one` (exp C¹),
  `fderivExpMap_continuousOn` (the exp-map differential = the Jacobi field, C¹).
- `VanVleck.lean`, `RNCExpansion.lean` (`det g̃`, `sqrtdet_taylor_coeff`).
- The whole convergence + Jacobi J1–J5-vanvleck stack.

## Phases (each an [AF] std-3 green checkpoint). New file(s) under `QIQTH/`.

### K1 — the pullback-determinant = (exp-Jacobian)² bridge `QIQTH/JacobianDet.lean` ✅ LANDED (`6c31ba66`, [AF] std-3)
`expPullbackMetric` IS definitionally the honest pullback `Jᵀ(g∘exp)J`; `expJacobianMat/Det` + `det_expPullback_eq` (det g̃ = J²·det(g∘exp)). No checkpoints.

`det g̃(v) = (det D(exp_p)_v)² · det (g ∘ exp_p)(v)` (since `g̃ = (Dexp)ᵀ (g∘exp) (Dexp)`, by
`Matrix.det_mul`). This BRIDGES the van-Vleck `Θ=(det g̃)^{−1/2}` to the exp-map Jacobian `J = det Dexp`
(whose radial ODE is the Jacobi equation). Reachable from `expPullbackMetric`'s pullback definition +
`Matrix.det_mul`/`det_transpose`.

### K2 — the exp-Jacobian radial structure `QIQTH/JacobianRadial.lean`
`J(v) = det D(exp_p)_v`'s radial derivative / its value along rays. `D(exp_p)_{tv}` is the Jacobi field;
`r∂_r log J` is the geodesic congruence expansion `θ`. Reachable pieces: `J(0)=1`, smoothness; the radial
derivative connects to `θ` (needs K3 for its ODE).

### K3 — the JACOBI EQUATION `QIQTH/JacobiEquation.lean` (THE WALL)
The Jacobi field `Y(t) = D(exp_p)_{tv}(tw)` satisfies `Y'' + R(Y,γ')γ' = 0` (geodesic deviation), and its
determinant's radial ODE (Raychaudhuri): `θ' + θ²/? + Ric(γ',γ') = 0`. This is the geodesic-deviation /
second-order smooth-dependence-on-IC infrastructure ABSENT from Mathlib — the genuine research-grade wall.
Decompose its first reachable sub-brick (the variation-field ODE from `geodesicField`'s fderiv) or
checkpoint honestly.

### K4 — the van-Vleck ODE `QIQTH/VanVleckODE.lean`
From K1+K2+K3: `(r∂_r) log√det g̃ = θ` (the congruence expansion) ⟹ the leading transport equation
`(r∂_r)Θ^{−1/2} + ½(r∂_r log det g̃)Θ^{−1/2} = 0` holds for the van-Vleck. Discharges the checkpoint of
`VanVleckCancellation`.

### K5 — the off-diagonal `O(1/t)` cancellation `QIQTH/OffDiagCancellation.lean`
Feed K4 into `HeatResidualBound.parametrixResidual_offdiag_absorbed`: the `O(1/t)` term vanishes ⟹ the
residual is `O(t^{N−d/2})·Gaussian` (via `ResidueBound`). Discharges the residual bound `hEbound`.

### K6 — unconditional `a₁=R/6` `QIQTH/HeatA1Unconditional.lean` (CAPSTONE)
Feed K5's residual bound into C5c (`leviSeries_summable`) + C6 (`trueHeatKernel_heat_eqn` unconditional) +
the diagonal expansion + the DERIVED diagonal `R/6` (J5-vanvleck) ⟹ **general `a₁=R/6` for the true
kernel**; instantiate `SeeleyDeWittData`.

## Discipline (unchanged)
One bg OPUS brick per phase; `#print axioms ⊆ std-3`; AxiomAudit pin (honest firewall); budget 0; commit +
push (SEPARATE fast calls); update this plan + memory. `a₁=R/6` (true kernel) NOT claimed until K6. K3 is
the genuine wall — decompose or checkpoint honestly; NEVER fake.

### K progress (2026-07-17)
- K1 ✅ (`6c31ba66`) pullback-det=(exp-Jacobian)² bridge (JacobianDet.lean).
- K2 ✅ (`7e0bfa75`) exp-Jacobian radial structure + radial-log split (JacobianRadial.lean) — isolates r∂_r log J as the one unknown.
- ⛔ K3 = THE TERMINAL WALL (confirmed by investigation): the r∂_r log J congruence ODE (Jacobi/Raychaudhuri for the exp-Jacobian DETERMINANT) needs the OFF-RADIAL Jacobian field / higher jets — documented as the Mathlib-absent smooth-dependence-on-IC gap in ExpMap.lean:998-1000. The repo has the radial 2-jet (⟹ diagonal R/6, DERIVED in J5-vanvleck) + the linear-variation residual, but the off-radial determinant ODE is the genuine research-grade wall. K4/K5/K6 blocked on it. HELD — no theatre brick at the wall.
