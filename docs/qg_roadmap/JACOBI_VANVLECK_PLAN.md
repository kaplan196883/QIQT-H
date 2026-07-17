# JACOBI / VAN-VLECK CAMPAIGN — the off-diagonal parametrix (C4c), commissioned 2026-07-17

**Goal.** Build the off-diagonal parametrix objects the residual bound (C4) needs — the **van-Vleck
determinant `Θ(x,y)`** and the **radial geodesic distance `r(x,y)`** as smooth functions — thereby
discharging C4c, turning the conditional capstone C6 unconditional, and yielding **general curved
`a₁ = R/6`** (conjecture input #3; the shared gate under D3-#3, D5-warp, D6-`c_i`).

**The reachable-decomposition insight.** The earlier "wall" framing (`ExpMap.lean`: off-radial Jacobi
field / Mathlib-absent smooth-dependence-on-IC) is about the FULL joint `(p,v)`-dependence of `exp_p`.
But the heat parametrix + the DIAGONAL `a₁` only need the parametrix with the **base point `y` FIXED as
the RNC center**: then `r(x,y) = |v|` (RNC radial arc-length, `v` = RNC coords of `x`) and the van-Vleck
`Θ` reduces to the **pullback metric `g̃ = exp_y^* g`** volume distortion `(det g̃)^{−1/2}` — and `det g̃`
+ its R/6 Taylor coefficient are ALREADY built (`RNCExpansion.lean`: `det`, `sqrtdet`,
`sqrtdet_taylor_coeff`). So the centered parametrix is substantially reachable; the genuinely deep parts
are the off-diagonal transport ODE (J3) and the full residual estimate (J5).

**Honest scale (binding).** Multi-session, Mathlib-grade. Reachable early phases (J1 van-Vleck, J2 radial
distance); deep risk concentrated in **J3** (off-diagonal transport recursion as functions) and **J5**
(the residual Gaussian bound). `a₁=R/6` is NOT claimed unconditionally until J6 lands; until then C6 stays
conditional and `a₁=R/6` is the carried G3 input. Checkpoint precisely at genuine walls; never fake.

## What is already BUILT (rides on)
- `RNCExpansion.lean`: `det g̃` is C∞ (`det_contDiff`), its 1st/2nd derivatives (`pd_det`, `det_pd_pd_expand`),
  `sqrtdet_pd_pd`/`sqrtdet_taylor_coeff` (the `−⅙ Ric` = R/6 source), + `_c2` finite-regularity variants.
- `PullbackMetric.lean`: `expPullbackMetric` `g̃ = exp_y^* g`, `expPullbackMetric_at_zero` (`g̃(0)=δ`),
  the christoffel/2-jet at 0, **`kappa_eq_one_sixth_expPullback`** (the κ=1/6 for g̃).
- `ExpMap.lean`/`ExpMapContDiff.lean`: `geodesicField`, `geodesicSol`, `expMap_contDiffOn_one` (exp C¹),
  `fderivExpMap_continuousOn`, the radial 2-jet `= −Γ`, Grönwall bounds.
- The convergence machinery (C1–C6) + C4a/C4b flat-Gaussian tools.

## Phases (each an [AF] std-3 green checkpoint). New file(s) under `QIQTH/`.

### J1 — the van-Vleck determinant `QIQTH/VanVleck.lean` ✅ LANDED (`3c9662e6`, [AF] std-3)
`vanVleck G v = (√det(G v))⁻¹` + `vanVleck_zero`/`_of_eq_one` (Θ(0)=1) + `vanVleck_expPullback_zero` (diagonal for
`g̃=exp_p^*g` via `expPullbackMetric_at_zero`) + `vanVleck_pos` + `vanVleck_contDiffAt`. No checkpoints.
- **`vanVleck g̃ v := (Real.sqrt (Matrix.det (g̃ v)))⁻¹`** — the van-Vleck–Morette determinant in RNC
  (volume distortion of `exp_y`), `Θ(exp_y v, y)`.
- **`vanVleck_zero`**: `vanVleck g̃ 0 = 1` (since `g̃(0)=δ`, `det = 1`, `√1⁻¹ = 1`).
- **`vanVleck_contDiff`** / smoothness from `det_contDiff` + `Real.sqrt` (on `det > 0`).
- **`vanVleck_pos`**, and the short-time link: `vanVleck = (sqrtdet)⁻¹`, so its 2-jet at 0 is `+⅙ Ric`
  (sign-flip of `sqrtdet_taylor_coeff`) — the van-Vleck side of `a₁=R/6`.

### J2 — the radial geodesic distance `QIQTH/RadialDistance.lean` ✅ LANDED (`cf938a8b`, [AF] std-3)
`rncRadialSq=∑(vⁱ)²`/`rncRadial=√` + smoothness + `pd_rncRadialSq` (∇r²=2v) + `radialDeriv` Euler field + `radialDeriv_rncRadialSq=2r²`.
(Correctly avoided the false `‖v‖²=∑(vⁱ)²` sup-norm identity.) No checkpoints. — original spec:
- **`r_y(v) = ‖v‖`** in RNC (the RNC radial arc-length property): the geodesic `t ↦ exp_y(tv)` has constant
  speed `‖v‖_{g(y)}`, so the geodesic distance `y → exp_y v` is `‖v‖`. Route: metric-compatibility of
  `geodesicField` (‖velocity‖ conserved) — check what `ExpMap.lean` gives.

### J3 — the off-diagonal transport coefficients `QIQTH/RadialTransport.lean` ✅ LANDED (`74323c99`, [AF] std-3)
`radialTransportSolve k f v = ∫₀¹ s^(k−1) f(s•v) ds` + `radialTransportSolve_transport_eq` (`(k+r∂_r)u_k = f`, k≥1,
ContDiff f, via ray chain rule + Leibniz-under-∫ + IBP — the clean no-singularity route) + `radialTransportSolve_one_const`.
No checkpoints. — original spec:
- The DeWitt transport recursion `(k + r∂_r)u_k = Θ^{1/2}Δ_g(Θ^{−1/2}u_{k−1})` solved ALONG RADIAL RAYS
  from `y` (a 1-D ODE in `r`), extending `DeWittDiagonal` (which has the diagonal `u_1=τ/6`) off-diagonal.

### J4 — the parametrix as a function `QIQTH/ParametrixFunction.lean` ✅ LANDED (`577e8116`, [AF] std-3)
`transportCoeff T` (concrete off-diagonal u_k) + `transportCoeff_succ_transport_eq` (DeWitt recursion via J3) +
`heatParametrixFn = heatParametrix (vanVleck G) (transportCoeff T)` (reused ansatz) + diagonal value/expansion/a1
(u_0(0)=1 derived; u_1(0)=R/6 the carried J6 input). Transport source T carried abstractly. No checkpoints. — spec:
- **`H_N(t,x,y) := (4πt)^{−d/2}·e^{−r_y(v)²/4t}·vanVleck(v)·Σ_{k≤N} u_k(v)·t^k`** (v = RNC coords of x).
  Assemble J1+J2+J3 into the actual parametrix kernel.

### J5 — the residual Gaussian bound `QIQTH/HeatResidualBound.lean` (DEEP — the analytic core)
**✅ J5a LANDED (`f8cfb79e`, [AF] std-3):** `parametrixResidual_telescope_N` — the FULL general-N residual telescoping
`(∂_t−Δ_g)H_N(t,0) = −G(0)·Δ_g(Θ^{−1/2}u_N)(0)·t^N` AT THE DIAGONAL (v=0, exactly what the heat-trace a₁ needs) +
`foldedCoeff`/`telescope_bracket`/`laplaceBeltrami_sum_pow`. ⚠ CHECKPOINT: diagonal only; off-diagonal blocked by the
cross-gradient ⟨∇G,∇w⟩ term. **✅ J5-offdiag LANDED (`a56021cf`):** the cross-gradient = radial-derivative identity
`∑ᵢ ∂ᵢG ∂ᵢw = (−1/2t)G·(r∂_r w)` (the Euler field absorbs it — why the off-diagonal telescoping CAN work) + the
off-diagonal telescoping, checkpointing the flat-Gaussian curvature term `(∂_t−Δ_g)G`. **J5b (todo):** the Gaussian
bound on the tail via C4a/C4b. — original spec:
- **`|E(t,x,y)| = |(∂_t−Δ_g)H_N| ≤ C·t^{N−d/2}·G_κ(t, r_y(v))`** — via C4a/C4b (Gaussian derivative +
  polynomial absorption) + the transport-recursion cancellation (the `u_k` are chosen to kill the leading
  orders). Discharges the `hEbound` hypothesis carried by C5c/C6.

### J6 — unconditional `a₁ = R/6` `QIQTH/HeatA1Unconditional.lean` (CAPSTONE)
- Feed J5's residual bound into C5c (`leviSeries_summable`) + C6 (`trueHeatKernel_heat_eqn`, now
  unconditional) + the diagonal expansion ⟹ **general `a₁ = R/6` for the true kernel**; instantiate
  `SeeleyDeWittData` (the single Phase-7 instance the DUALITY_ROADMAP ledger anticipates).

## Dependency
```
J1 (van-Vleck) ──┐
J2 (radial r) ───┼──► J4 (parametrix fn) ──► J5 (residual bound) ──► J6 (a₁=R/6)
J3 (transport) ──┘                              ↑ C4a/C4b, C5c, C6
```

## Discipline (unchanged)
One bg OPUS brick per phase; `#print axioms ⊆ std-3`; AxiomAudit pin (honest firewall); budget 0; commit
explicit paths + PUSH; update this plan + memory. `a₁=R/6` NOT claimed until J6. Checkpoint precisely at
genuine walls (esp J3/J5); NEVER fake. NOT the true kernel / a₁=R/6 until J6.

### J5 progress log (2026-07-17)
- J5a ✅ diagonal residual telescoping (`f8cfb79e`)
- J5-offdiag ✅ off-diagonal residual decomposition, 2 named O(r²) residues (`a56021cf`)
- J5-residue ✅ RNC O(r)/O(r²) decay estimates, RNCDecay.lean (`0821b184`)
- J5-resbound ✅ residue decay bounds, ResidueBound.lean (`5c481d78`)
- J5-vanvleck (in flight): the leading van-Vleck cancellation — THE crux where R/6 enters (Delta_g Theta -> Ric via sqrtdet_taylor_coeff). Expected checkpoint.
- J5b (todo): assemble |E| <= C t^(N-d/2) G_kappa. J6 (todo): unconditional a1=R/6.
- J5-vanvleck ✅ (`0748fd8f`): ★ parametrix DIAGONAL a₁=R/6 DERIVED (van-Vleck 2-jet: laplaceBeltrami_detpow_diag Δ_g((det g)^-1/4)(0)=(∑Ric_ii)/6 → u₁(0)=R/6 → heatParametrixFn_diagonal_a1_derived).
- ⛔ TERMINAL WALL: true-kernel a₁=R/6 needs the OFF-diagonal O(1/t) van-Vleck cancellation = the radial-log-det / Jacobi-field identity (geodesic smooth-dependence-on-IC, Mathlib-absent — same wall as C4c start). Diagonal R/6 closes (radialDeriv_zero=0 there); off-diagonal is the wall. J5b/J6 blocked on it.
