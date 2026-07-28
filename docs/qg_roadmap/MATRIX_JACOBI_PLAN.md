# OFF-RADIAL MATRIX JACOBI / Y⁻¹ CAMPAIGN (M-series), commissioned by the user 2026-07-18

**Decision.** User chose "Commission off-radial Jacobi Y⁻¹" — the sustained multi-session Mathlib-PR-scale
build that is the general closer for **true-kernel `a₁=R/6`** (variable curvature). This discharges the ONE
remaining wall after the ODE-variational campaign exhausted the reachable RNC-2-jet / constant-curvature
frontier (5 bricks: L2c#3 `e568d7ca`, L3 `b943e437`, K4-leading `3e36639c`, const-curv `b62adc13`,
leading-radial-ODE `6e9ec14d`).

**The wall (precise).** The off-diagonal `O(1/t)` van-Vleck cancellation (end of `VanVleckCancellation.lean`)
needs the UNIFORM-in-`v` (all-orders, variable-curvature) van-Vleck radial ODE `(r∂_r) log√det g̃ = …`, i.e.
`r∂_r log J` ALONG RAYS (`v≠0`), where `J = det(D exp_p)` is the exp-map Jacobian. `D exp_p`'s columns are
the matrix Jacobi field `Y(τ)` (`Y'' = −R(τ)Y`, `Y(0)=0`, `Y'(0)=I`), and the expansion `θ = tr(Y⁻¹Y')`.
`Y(0)=0` ⟹ `Y⁻¹` singular at the center: THE obstruction.

**The regularization key.** Factor the singularity: `Y(τ) = τ·W(τ)` with `W(0)=Y'(0)=I` invertible, `W` smooth
(Hadamard). Then `W⁻¹` is regular near `0`, `det Y = τⁿ det W`, `log det g̃ = 2 log det Y + (angular) − …`
(via K1/K2), and the finite van-Vleck content is carried by `W⁻¹W'` — computable, non-singular. This is what
makes the whole campaign formalizable rather than blocked on a genuine `1/0`.

## Phases (each an [AF] std-3 green checkpoint). New files under `QIQTH/`.

### M1 — Hadamard smooth-factorization primitive  `QIQTH/HadamardFactor.lean`  (first brick)
Mathlib LACKS it (its `Analysis/Complex/Hadamard.lean` is the three-lines theorem). For `f : ℝ → F`
(`F` a real normed space — covers vector/matrix-valued) with `f` `C¹` and `f 0 = 0`:
`f τ = τ • g τ` where `g τ := ∫ t in (0:ℝ)..1, f' (t·τ)`; `g` continuous; `g 0 = f' 0`. Route: FTC
(`d/dt f(tτ) = τ • f'(tτ)`, integrate) + parametric-integral continuity. THE regularization primitive.
Reusable, Mathlib-worthy on its own.

### M2 — the matrix Jacobi field `Y(τ)` and its regularization  `QIQTH/MatrixJacobi.lean`
The matrix Jacobi field along a geodesic ray as the solution of `Y'' = −R(τ)Y`, `Y(0)=0`, `Y'(0)=I`
(build on the L1/L2/L2a/L2b single-field variational machinery + `covariant_jacobi_equation`). Apply M1:
`Y(τ) = τ·W(τ)`, `W(0)=I`, `W` `C¹`; `W(τ) = I − (τ²/6)R(0) + O(τ³)` (the standard Jacobi 2-jet, ties to
L3 `covariantJacobi_trace_at_center`). `W(0)` invertible ⟹ `W⁻¹` regular on a `0`-nbhd.

### M3 — `det Y = τⁿ det W`; bridge to `det g̃`  `QIQTH/JacobianRegularized.lean`
`det Y = τⁿ det W`, `log det Y = n log τ + log det W`; connect to K1/K2 (`det g̃ = J²·det(g∘exp)`,
`radialDeriv_log_det_split`) so `r∂_r log det g̃` reduces to `r∂_r log det W` (finite) + explicit radial
(`n`) + angular pieces. The singular `n log τ` is isolated and explicit; the curvature lives in `log det W`.

### M4 — the uniform van-Vleck radial ODE  `QIQTH/VanVleckRadialODE.lean`  (the deep crux)
`r∂_r log det W = tr(W⁻¹ · r∂_r W)` (regular), and via the matrix Jacobi ODE for `W` this satisfies the
Raychaudhuri/van-Vleck ODE whose trace is `−Ric(v,v)` at leading order (L3) and the full expression at all
orders. Delivers the UNIFORM-in-`v` `(r∂_r) log√det g̃ = …` the checkpoint needs. Decompose or checkpoint.

### M2b ASSESSMENT (2026-07-18) — the genuine geometric wall, and the path through it
Reading `JacobiEquation.lean`: the repo's coordinate Jacobi ODE is `ξ'' = −jacobiOperator(x,v,ξ,ξ')` where
`jacobiOperator` DEPENDS ON `ξ'` (the `Γ·ξ'·v` terms), so off-center it is `ξ''+B(τ)ξ'+C(τ)ξ=0`, NOT the clean
`Y''=−A(τ)Y` that M4b consumes; and `tr(coordinate jacobiOperator) ≠ Ric` (only `tr(covariant R)=Ric`, L3). So the
physics Raychaudhuri `θ'=−Ric−tr(Θ²)` is unreachable without the OFF-CENTER covariant Jacobi eqn — the same wall that
stalled the L2c off-center agents 3×. **The clean path through (M2b, textbook):** build PARALLEL TRANSPORT along the
geodesic (frame ODE `e_i'(τ)=−Γ(γ')e_i`); in the parallel orthonormal frame the covariant derivative = ordinary
derivative, so the Jacobi field's frame-components `Ỹ` satisfy the CLEAN `Ỹ''=−R̃(τ)Ỹ` with `tr R̃ = Ric` — directly
feeding M4b. This AVOIDS the messy off-center coordinate Finset identity. Sub-phases: M2b-1 parallel transport ODE +
frame · M2b-2 covariant deriv = ordinary deriv in the frame · M2b-3 Jacobi field in the frame `Ỹ''=−R̃Ỹ` · M2b-4
`tr R̃ = Ric`. This is a fresh multi-session sub-campaign (parallel transport + frame geometry, Mathlib/repo-absent
off-center). a₁=R/6 gates on it.

**M2b progress:**
- M2b-1 ✅ (`2d5b7170`) `ParallelTransport.lean` — parallel_metricInner_const: d/dτ⟨e,f⟩_g=0 for parallel e,f (from metric_compat + parallel condition, full Γ-term Finset cancellation to 0). Parallel transport is an isometry ⟹ orthonormal frames stay orthonormal. All [AF] std-3. e,f carried as parallel.
- M2b-4 (in flight) — tr R̃=Ric in an ORTHONORMAL FRAME: ∑_i ⟨R(e_i,v)v,e_i⟩_g = Ric(v,v) for any g-orthonormal {e_i}. Generalizes L3 (center-only, coordinate basis) to a general orthonormal frame, hence holds ALONG THE RAY (coordinate-free Ricci definition). Key = completeness ∑_i e_i^a e_i^b = g^{ab} from orthonormality. Independent of parallel-transport existence.
- M2b-4 ✅ (`24f965ef`) `FrameRicci.lean` — frame_ricci_trace (∑_i⟨R(e_i,v)v,e_i⟩_g=Ric(v,v), orthonormal frame, along the ray; hcomplete carried).
- ★ HONEST M2b-3 REASSESSMENT: the parallel frame gives `D²ξ/dτ²=∑Ỹ_i''e_i` cleanly, BUT `Ỹ''=−R̃Ỹ` still needs `D²ξ/dτ²=−R(ξ,v)v` = the OFF-CENTER covariant Jacobi eqn (the same wall that stalled L2c agents 3×; off-center adds ΓΓ+Γξ'+γ''=−Γvv). The parallel frame builds surrounding infra but does NOT dissolve this core identity. M2b-3 = attempt the off-center covariant Jacobi eqn directly (with the centered `covariant_jacobi_equation_centered` as template) — the genuine crux; checkpoint honestly if it stalls.
- M2b-2 (parallel-transport EXISTENCE, frame ODE) remains; can be carried-as-hyp and discharged later.

### M5 — off-diagonal `O(1/t)` van-Vleck cancellation  (discharge `VanVleckCancellation` checkpoint)
Feed M4 into `HeatResidualBound.parametrixResidual_offdiag_absorbed` piece (II): the radial-transport term
`+(1/t)G(r∂_r P)` now cancels for ALL `v`, killing the `O(1/t)` singular term. Discharges K5.

### M6 — unconditional true-kernel `a₁=R/6`  (the capstone)
M5 + the convergence machinery (C1–C6) + `SeeleyDeWittData` instance ⟹ the true heat kernel's `a₁=R/6`
for GENERAL curvature, UNCONDITIONAL. Retires the carried G3 `a₁=R/6` input.

## Discipline (unchanged)
One bg OPUS brick per phase; `#print axioms ⊆ std-3`; AxiomAudit pin (honest firewall); budget 0; commit +
push (SEPARATE fast calls); update plan + memory. `a₁=R/6` (true kernel) NOT claimed until M6. M2/M4 are the
genuine walls; decompose or checkpoint honestly, NEVER fake. This is a multi-session foundational build.

## Progress
- (2026-07-18) Campaign commissioned; M1 (Hadamard factorization) in flight.
- M1 ✅ (`15a45483`) `HadamardFactor.lean` — hadamardFactor f' τ := ∫₀¹ f'(t·τ)dt; hadamardFactor_smul (f τ = τ • g τ for C¹ f with f 0=0, via FTC), hadamardFactor_zero (g 0 = f'(0)), hadamardFactor_continuous (parametric-integral continuity). General real Banach F. All [AF] std-3, budget 0. The regularization primitive (Mathlib-absent). NEXT: M2.
  NOTE (scope clarification): the van-Vleck radial ODE has TWO equivalent routes — (A) Cartesian `r∂_r log det g̃` (det g̃ SMOOTH, det g̃(0)=1, no singularity, but needs det g̃ to ALL orders = the exp-Jacobian along rays) and (B) polar/Raychaudhuri `θ = tr(Y⁻¹Y')` (Y = angular Jacobi fields, SINGULAR at 0, but clean Raychaudhuri ODE). M1 regularizes route B. The DEEPEST wall (both routes) is the exp map / geodesic flow solved to ALL orders along rays = ODE smooth-dependence-on-IC (partly built L1/L2a/L2b). M2 = the regularized-invertibility payoff of M1 (W(0) invertible ⟹ W invertible near 0), a clean reachable brick on route B; the geometric identification Y = D exp_p (Y''=−R Y) and the all-orders exp expansion are the deeper M2b/M4 sub-phases.
- M2 ✅ (`a5dde884`) `MatrixJacobi.lean` — the regularized-invertibility payoff: hadamardFactor_det_ne_zero_eventually (det W τ ≠ 0 near 0) + hadamardFactor_isUnit_eventually (W τ a unit near 0) + matrixJacobi_regularized (Y=τ•W ∧ W invertible near 0, for matrix Y with Y 0=0, det Y'(0)≠0). W⁻¹ regular where the polar Y⁻¹ is singular. All [AF] std-3, budget 0. Abstract structure only (Y'(0)=I carried as det Y'(0)≠0). NEXT: M3.
- M3 ✅ (`c1110123`) — det_matrixJacobi_eq (det Y = τⁿ det W via Matrix.det_smul) + log_det_matrixJacobi_split (log det Y = n log τ + log det W, isolating the singular n·log τ from the finite log det W). All [AF] std-3, budget 0. ⚠ the K1/K2 bridge to det g̃ (det g̃=J²·det(g∘exp)) requires the GEOMETRIC identification Y=D exp_p (M2b) — deferred.
- M4a ✅ (`6468ed65`) `JacobiFormula.lean` — the analytic Jacobi formula (Mathlib-ABSENT, built from scratch): matrix_det_contDiff (det is C^∞) + hasDerivAt_matrix_det (d/dτ det W = tr(adj(W)·W'), via Matrix.det_apply' + product rule + Cramer/adjugate collapse) + hasDerivAt_log_det_matrix (d/dτ log det W = tr(W⁻¹W') for IsUnit det — the regularized expansion θ=tr(W⁻¹W')). All [AF] std-3, budget 0. Self-contained analytic toolkit (no geometry).
- M4b ✅ (`5164c89f`) `MatrixRaychaudhuri.lean` — hasDerivAt_matrix_inv ((Y⁻¹)'=−Y⁻¹Y'Y⁻¹ via hasFDerivAt_ringInverse + Matrix.nonsing_inv_eq_ringInverse) + matrix_riccati (Θ:=Y'Y⁻¹, Θ'=−A−Θ² from Y''=−A·Y) + trace_raychaudhuri (θ:=tr Θ, θ'=−tr A−tr(Θ²) via traceLinearMap). All [AF] std-3, budget 0. Abstract A.
- ★ THE ABSTRACT ANALYTIC TOOLKIT (M1–M4b) IS COMPLETE (6 files: HadamardFactor, MatrixJacobi[+M3], JacobiFormula, MatrixRaychaudhuri). Everything reachable WITHOUT the geometry is landed: the regularization (Y=τW, W⁻¹ regular), the det/log split, the analytic Jacobi formula (d/dτ log det W = tr(W⁻¹W')), and the matrix Raychaudhuri (θ'=−tr A−tr Θ²).
- ⚠ M2b (GEOMETRIC identification Y=D exp_p, Y''=−R(τ)Y along rays — the off-radial Jacobi eqn, the same off-center wall that stalled the L2c off-center agents) + M4-full (feeding tr A=Ric into the Raychaudhuri ODE) remain the deep geometric walls.

## ★★★★ M2b-3 WALL CROSSED (2026-07-18)
`covariant_jacobi_equation` (`d2f9b5e6`, CovariantJacobiOffCenter.lean) — the OFF-CENTER covariant Jacobi
equation `D²ξ/dτ² = −R(ξ,v)v` ALONG THE WHOLE RAY (hyps = centered minus `hΓ0`; no vacuity), CLOSED axiom-clean
(the identity that stalled 3 prior agents). ΓΓ-group closed by an explicit involution on `Fin n⁴`. THE geometric
wall gating a₁=R/6 is removed. Remaining (now downhill): M2b-3a (covariantDerivAlong of a parallel-frame
combination = componentwise deriv) → M2b-5 (project the covariant Jacobi eqn onto the parallel orthonormal frame
⟹ Ỹ''=−R̃Ỹ) → feed M4b `trace_raychaudhuri` + M2b-4 `tr R̃=Ric` ⟹ geodesic Raychaudhuri θ'=−Ric(v,v)−tr(Θ²)
along the ray → M4-full/M5/M6 ⟹ a₁=R/6. M2b-2 (parallel-transport existence) carriable-as-hyp, discharge later.
- M2b-3a ✅ (`9cd64412`) FrameCovariantDeriv.lean — covariantDerivAlong_frame_combo + covariantSecondDeriv_frame_combo (covariant deriv = componentwise ordinary deriv in a parallel frame). NEXT: M2b-5 projection → Ỹ''=−R̃Ỹ.
- M2b-5 ✅ (`d3f933ce`) FrameJacobiEquation.lean — frame_jacobi_equation (Yt_k''=−∑_j R̃_kj Yt_j, i.e. Ỹ''=−R̃Ỹ) + riemannGeodesicDeviation_linear. The clean matrix Jacobi ODE from projecting M2b-3 onto a parallel orthonormal frame. NEXT: Raychaudhuri assembly (package columnwise Y''=−R̃Y + M4b trace_raychaudhuri + M2b-4 tr R̃=Ric ⟹ geodesic Raychaudhuri θ'=−Ric−tr Θ² along the ray).
- ★★ M4-full ✅ (`ce872a50`) GeodesicRaychaudhuri.lean — geodesic_raychaudhuri (θ'=−Ric(v,v)−tr(Θ²) along the ray, θ=tr(Y'Y⁻¹); assembles M4b + M2b-5 Y''=−R̃Y + M2b-4 tr R̃=Ric) + frameJacobi_matrix_ode (columnwise→matrix packaging). THE PHYSICS RAYCHAUDHURI EQUATION OFF-CENTER — the objective of crossing the wall. 18 [AF] bricks this session.
  REMAINING toward a₁=R/6: (A) θ↔r∂_r log J van-Vleck bridge [θ=d/dτ log det Y (M4a) + det Y=τⁿdet W (M3) + Y=D exp_p geometric id + K1/K2 ⟹ uniform-in-v van-Vleck radial ODE] · (B) M5 off-diagonal O(1/t) cancellation · (C) M6 a₁=R/6 + SeeleyDeWittData · (D) M2b-2 parallel-transport existence (linear ODE, carried as hpar/hortho/hexp, dischargeable).
