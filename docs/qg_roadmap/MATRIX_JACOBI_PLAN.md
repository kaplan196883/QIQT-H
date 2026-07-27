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
