# THE MANIFOLD HEAT-KERNEL PARAMETRIX — the top-level critical path (credit + sequence + the deep walls)

**Date 2026-07-15.** The single consolidating map for "discharge the general `a₁ = R/6`" = build the manifold
heat-kernel parametrix. It CREDITS the (large, active) existing campaign, sequences the sub-plans, and names the
genuine remaining walls. **It does not duplicate the detailed sub-plans** — it points to them. Companion to
`HEAT_KERNEL_FULL_INFRASTRUCTURE_PLAN.md` (the L0–L6 tower) and the `THE_*_PLAN.md` sub-plans.

## Honest headline
Building the parametrix (⟹ general `a₁=R/6`) is genuinely **multi-month-to-year**, even from today's advanced
state. The GEOMETRY SUBSTRATE (exp map, normal coordinates, finite jets, the RNC gauge as an algebraic identity)
is largely **built**; the immediate front is the **`ContDiff³ exp_p` finite jet-ODE tower** (makes `κ=1/6`
unconditional for the pullback metric — a scoped ~4–8-week effort); and the **heat-kernel parametrix proper**
(the Levi/Duhamel construction that PROVES the kernel exists with its short-time expansion — the thing that
actually discharges general `a₁=R/6`) is the deeper, mostly-unstarted wall beyond it. Every brick stays [AF]
std-3, budget 0; checkpoint honestly at genuine walls; NEVER claim general `a₁=R/6` / a curved heat kernel /
numerical-G until the parametrix proper lands.

## What is ALREADY BUILT (credited — grep before doubting)
**Geometry substrate (L0):**
- `Curvature.lean` (component `christoffel/riemann/ricci/scalarCurv/einstein` + all Bianchi), `ManifoldCurvature.lean`
  (coordinate-free Riemann endomorphism + tensoriality), `LeviCivita.lean` (Koszul), `PseudoRiemannian.lean`,
  `ChristoffelSmooth.lean` (C∞ regularity), `Geodesic.lean` (existence/uniqueness), `EinsteinFieldEquation.lean`.
- `CoordinateCurvature.lean` (jet-based scalar curvature) — unified to `Curvature.lean` via
  `CurvatureBridge.lean` (`scalarCurvature_bridge`, one canonical base).
- **`ExpMap.lean` (~5000 lines, the exp-map + higher-jets campaign — `THE_EXP_MAP_PLAN.md`, `THE_EXP_JETS_PLAN.md`):**
  `exp_p` strict-derivative + local C¹ diffeo (normal coordinates EXIST as a chart); the radial 2-jet
  `exp_p(t·v)''=−Γ(v,v)`; the value **2-jet and 3-jet**; the `[0,1]` operator fundamental solution `Φ_v` (`expJetFund`);
  the localized first variation `HasFDerivAt exp_p`; the **Jacobian 1-jet** `fderiv exp_p v = id − Γ_p^{sym}(v,·)+O(‖v‖²)`
  ⟹ **two of three RNC gauge conditions** `g̃(0)=δ`, `∂g̃(0)=0`. All via equilibrium two-point Grönwall (dodging the
  Mathlib-absent C¹-flow theorem).
- `RNCExpansion.lean` (`√det g = 1 − R/6·x²`, van Vleck), `RNCGauge.lean` + `RNCGaugeExp.lean`
  (**`exp_rncGaugeJet`** — the third gauge condition `∂_{(l}Γ̃_{jk)}(0)=0` DISCHARGED as a proven algebraic identity
  grounded in the exp value-3-jet, via the radial route + polarization), `Polarization.lean`.

**Flat heat kernel + coefficient (L4-flat, L6):**
- `HeatKernelOneD/DDim/A1.lean` (the Euclidean Gaussian `(4πt)^{−d/2}e^{−|x|²/4t}` + derived Gaussian moments +
  `heat_a1_of_RNC_derived` assembling `a₁=(1/6−ξ)R` from the derived moment matrix, carrying `κ=1/6`).
- `DeWittDiagonal.lean` (`u₁(x,x)=R/6` transport), `HeatCoeffDetermination.lean` (invariance),
  `HeatCoeff2/3Determination.lean` (`a₂`/`a₃` constants). `RNCExpansion.heat_a1_of_gauge` (gauge ⟹ `κ=1/6`).

**Operator/trace side (L5) — this session:** the trace-class API, compact spectral eigenbasis, `HS⟹compact`,
resolvent bridge, integral operators (`L²`-kernel⟹HS/compact), Mercer, `Spectral/HeatSemigroup` (abstract `e^{−tA}`),
`Spectral/Garding` (Gårding mollification → essential self-adjointness), `Spectral/Stone`.

**Validated on explicit geometries:** `a₁=R/6` on flat torus, `S²`, `S³`, `S²×S¹`.

## The critical path — remaining, in order

### P1 — finish the geometry substrate: `ContDiff³ exp_p` (the finite jet-ODE tower) — CURRENT FRONT
`THE_EXP_JETS_PLAN.md`'s VERDICT: the RNC gauge is discharged as an algebraic identity (`exp_rncGaugeJet`); making
`κ=1/6` **unconditional for the actual pullback metric** `g̃` needs `ContDiff³ exp_p` (derivative-loss: `g̃` uses
`D exp_p`, so `ContDiff² g̃` needs `ContDiff³ exp_p`). Reachable via the FINITE augmented jet-ODE tower (NOT the
general smooth-dependence theorem Mathlib lacks):
- **Rung 1 — `ContDiff¹ exp_p`. ✅ DONE 2026-07-15 (`ExpMapContDiff.lean`, [AF] std-3).** `expMap_contDiffOn_one`
  (`ContDiffOn ℝ 1 exp_p (ball 0 expRho)`) via `fderivExpMap_continuousOn` (continuous `v↦fderiv exp_p v`), whose
  crux `expFund_two_pt_diff` (`‖Φ_v 1 − Φ_w 1‖ ≤ C‖v−w‖`, the operator fundamental solution's Lipschitz dependence
  on the initial velocity) CLOSED via the operator two-point Grönwall on the Jet₁ system — NOT the general C¹-flow
  theorem. Strengthens the Jacobian 1-jet pointwise→continuous.
- **Rung 2 — `ContDiff² exp_p`. ✅ DONE 2026-07-15 (`ExpMapContDiff2.lean`, [AF] std-3, `expMap_contDiffOn_two`,
  NO hypothesis).** `ContDiffOn ℝ 2 (expMap …) (ball 0 expRho)` — the geodesic exp map is TWICE continuously
  differentiable near 0, via the finite Jet₂ augmented ODE tower (equilibrium-Grönwall, NOT the general smooth-
  dependence theorem Mathlib lacks). The full chain, all axiom-free: the reduction
  `expMap_contDiffOn_two_of_fderiv_contDiffOn_one`; `D²F` exists/`C^∞`/tube-bound/Lipschitz; the Jet₂ source
  `expJet2Rhs` (+regularity); the vector inhomogeneous 2nd-variation `expJet2Fund` (`Q^{hk}` on `[0,1]` via
  `IsPicardLindelof`, local→shifted→glue→capstone); the residual estimate (`expJet2_residual_bound` +
  `gronwall_vec_residual`); the quadratic remainder bound `expJet2_remainder_quadratic_bound` (combining the DF
  2nd-order Taylor `geodesicField_DF_second_order_taylor` + tube 2nd-order accuracy `expTube_second_order_accuracy`
  + `D²F` symmetry + `[0,1]` first-variation Lipschitz `expFund_two_pt_diff_Icc`); `HasFDerivAt`
  (`expMap_fderiv_hasFDerivAt`, 2nd derivative = the CLM `expJetD2`, built bilinear via ODE uniqueness
  `expJet2Fund_unique`); and the continuity `expJetD2_two_pt_diff` (`v`-Lipschitz of the 2nd derivative, from the
  parameter-Grönwall `expJet2Val_two_pt_diff`). ⚠ Does NOT yet give `κ=1/6` for the pullback metric `g̃` (needs
  `ContDiff³` = Rung 3, via the `g̃` derivative-loss), NOT the parametrix (P2), NOT general `a₁=R/6`.
- **Rung 3 — `ContDiff³ exp_p`. ✅ DONE 2026-07-15 (`ExpMapContDiff3.lean`, [AF] std-3, `expMap_contDiffOn_three`,
  NO hypothesis).** `ContDiffOn ℝ 3 (expMap …) (ball 0 expRho)` — the geodesic exp map is THREE times continuously
  differentiable near 0, via the finite Jet₃ augmented ODE tower (a clean brick-for-brick mirror of Rung 2). Full
  chain, all axiom-free: `D³F` regularity (`contDiff_fderiv3_geodesicField`, tube-bound, Lipschitz) + **D³F
  permutation-symmetry `fderiv3_geodesicField_symm_{ab,bc,cyc}` — a genuine MATHLIB-GAP FILL** (Mathlib's
  `FDeriv/Symmetric.lean` stops at the 2nd derivative); the Jet₃ source `expJet3Rhs`; the vector inhomogeneous
  3rd-variation `expJet3Fund` (`R^{hkl}` on `[0,1]` via `IsPicardLindelof`); the frontier remainder bound
  `expJet3_remainder_quadratic_bound` (the ~10-term first-order cancellation via the D³F/D²F symmetries); the
  3rd-derivative CLM `expJetD3` (trilinear via `expJet2Curve` curve-bilinearity + `expJet3Fund_unique`);
  `expMap_fderiv2_hasFDerivAt` (HasFDerivAt, 3rd deriv = `expJetD3`); the continuity `expJetD3_two_pt_diff` (from the
  14-term parameter-Grönwall `expJet3Val_v_two_pt_diff`); and the discharge
  `expMap_contDiffOn_three_of_fderiv2_contDiffOn_one`. ⚠ Does NOT by itself give `κ=1/6` — that is R3→κ next.
- **R3→κ. ✅✅ DONE 2026-07-16 — UNCONDITIONAL `κ=1/6` for the pullback metric `g̃` (`PullbackMetric.lean`, [AF] std-3,
  `87609f17`).** The full chain landed axiom-free: the exp-jet endgame (`expJetD3(0)=a₃`, twice-Leibniz `pd²g̃(0)`,
  `expPullbackMetric` + smooth inverse `expPullbackMetricInv`), the pullback-Christoffel derivative
  `pd_christoffel_expPullbackInv_zero`, the finite-regularity `heat_a1_of_gauge_c2` (weakens `ContDiff ⊤`→`ContDiffAt 2`),
  and — the crux — the pullback RNC radial identity `hpd2` proved as a pure symmetric-array identity (`2A−B=0` via the
  4-atom `S2/S3/S4/S1c` reduction + a uniform 5-index `sum5_reindex` Equiv). Cascade: `hpd2_cubic_vanish` →
  `expPullback_hpd2` → `expPullback_radial_gauge` → `gauge_pd_christoffel_expPullbackInv_zero'` → ★
  **`kappa_eq_one_sixth_expPullback`** = the heat `a₁` coefficient at `g̃` = `(1/6−ξ)R − m²`, NO gauge hypothesis, only
  the standard inputs (ambient `C^∞`, symmetry, `gi=g⁻¹`, orthonormal frame `g(p)=δ`, `κ` defined by the √det↔ricci
  relation, curvature non-degeneracy). ⚠ HONEST: this is `κ=1/6` for the EXP-PULLBACK METRIC `g̃`; it does NOT give
  the general `a₁=R/6` — that still needs the kernel = P2 (Seeley–DeWitt, labelled physical input).

### P2 — the heat-kernel parametrix PROPER (the deep wall — the actual discharge)
This is what proves the smooth kernel `K_t(x,y)` EXISTS and has the short-time diagonal expansion for an arbitrary
metric — i.e. what discharges general `a₁=R/6`. Sub-pieces (Rosenberg §3.2 / BGV Ch2 / Gilkey Ch1):

**★ P2 BUILD PROGRESS (user-directed 2026-07-16, 5 green [AF] std-3 bricks PUSHED):**
- `LaplaceBeltrami.lean` (`9f9e9a34`) — the operator `Δ_g` + RNC-center reduction to the flat Laplacian + quadratic-trace.
- `FlatHeatEquation.lean` (`91fdca0d`) — `heatKernel1D`/`gaussDdim` solve `∂_t G = Δ_flat G` (the leading term).
- `HeatParametrixError.lean` (`710a6289`) — `heatResidual = (∂_t−Δ_g)G`, `= 0` at the RNC center (flat Gaussian = leading
  parametrix), + the metric-deviation curvature form.
- `HeatParametrixAnsatz.lean` (`3ea3f478`) — P2a: `heatParametrix` `H_N` as a function + `heatParametrix_diagonal_a1`
  (`H_N(t,0) = (4πt)^{−d/2}(1 + (R/6)t + …)` — the diagonal a₁ structure).
- `HeatTransportRecursion.lean` (`e9b765d5`) — P2b: `transportOp` + `TransportRecursion` structure +
  `u1_diag_eq_tau_div_six` (u₁ diagonal = τ/6, DERIVED from the van-Vleck jet, sphere witness u₁=1/3) + DeWitt bridge.
- `HeatParametrixOrder.lean` (`86b34b40`) — P2c: `laplaceBeltrami_mul` (the Δ_g product rule) + `parametrixResidual_telescope`
  (unconditional) + `parametrixResidual_transport_identity` (first-order residual collapses to `−G·Θ^{−1/2}(Δ_g u₁)·t` at
  the diagonal — the u₁ transport cancels the t⁰ order).
- `HeatParametrixTrace.lean` (`1a4e1a5b`) + `HeatParametrixTraceDerived.lean` (`552a093a`) — P2e (parametrix level): the
  diagonal heat-trace `= (4πt)^{−d/2}(Vol + (1/6)∫R·t + …)`, i.e. the **a₁ = (1/6)∫R** coefficient, with u₁ DERIVED from
  the transport recursion (`parametrixDiagTrace_a1_derived`), sphere witness. Finite-sample sum, carried diagonal coeffs.
- ✅ **P2 REACHABLE FRONTIER COMPLETE (12 [AF] std-3 bricks, 2026-07-16/17).** The full parametrix-level local
  Seeley–DeWitt story is machine-checked: operator, flat heat solution, residual (=0 at RNC center), ansatz + diagonal
  a₁, transport recursion (u₁=τ/6 derived), first-order telescoping, parametrix trace a₁=(1/6)∫R, PLUS the **complete P2d
  ALGEBRAIC core** (`HeatDuhamel.lean`, 2026-07-17): the space-time Duhamel convolution `heatConv` + full bilinear
  algebra + the FTC-1 boundary term FULLY PROVEN, `duhamel_principle` reducing `(∂_t−Δ_g)(A*B)=B` to 4 explicit
  non-vacuous analytic hypotheses, AND associativity `(A*B)*C=A*(B*C)` (`heatConv_assoc` + the unconditional spatial
  Fubini `heatConv_spatial_fubini`) — decomposing P2d into its (proven) algebra vs its (checkpointed) convergence.
- ⚠ **THE WALL (community-scale, Mathlib lacks the infrastructure) — where the build honestly stops:** the off-diagonal
  parametrix (`udiag_rec` from the radial geodesic ODE / van-Vleck as a function), the general-N transport recursion,
  P2c-full `O(t^{N−d/2})` error estimate, **P2d Levi/Duhamel convergence + kernel existence** (true kernel = parametrix +
  iterated-convolution error), and P2e-full manifold Riemannian-volume integration (replace the finite-sample/carried
  √det g). These need geodesic-flow/exp-map function-level + parabolic-PDE + manifold-integration theory absent from
  Mathlib. **General `a₁=R/6` for the TRUE kernel stays a labelled input (G3 `PhysicalInputs`) behind P2d/P2e** — the
  entire reachable parametrix scaffolding is now built beneath it, axiom-free.

- **P2a — the parametrix ansatz** `H_N(t,x,y) = (4πt)^{−d/2} e^{−r(x,y)²/4t} · Θ(x,y)^{−1/2} · Σ_{k≤N} u_k(x,y) t^k`
  (`r`=geodesic distance, `Θ`=van Vleck — `RNCExpansion` has the diagonal `√det`; needs `r` off-diagonal).
- **P2b — the transport recursion** for `u_k` (`DeWittDiagonal` has `u_1` diagonal; extend off-diagonal + all `k`).
- **P2c — the error estimate** `(∂_t + Δ_x) H_N = O(t^{N−d/2})` (Gaussian × polynomial — hard bounds).
- **P2d — the Levi/Duhamel convergence** `K = H_N + H_N * (error) + …` → the ACTUAL kernel. **THE analytic heart**
  (iterated-convolution Gaussian-bound estimates; no proof assistant has this). ✅ **ALGEBRAIC core COMPLETE** (`HeatDuhamel.lean`,
  [AF] std-3): the convolution `*` (`heatConv`) + bilinearity + FTC-1 boundary term fully proven; Duhamel's
  principle a genuine algebraic reduction to 4 carried analytic hyps; **associativity `(A*B)*C=A*(B*C)` now UNCONDITIONAL
  modulo integrability** (`heatConv_assoc''`) — both spatial/temporal reorderings discharged (`heatConv_reorderL/_reorderR`
  via the interval↔Lebesgue Fubini + spatial `heatConv_spatial_fubini`) AND the triangular time-Fubini discharged
  (`triangular_time_fubini` via `tri_swap` = Tonelli on the masked square + the shift substitution, realizing the
  volume-preserving shear `(s,s')↦(s+s',s)`). **The entire Levi-series algebra is now axiom-free with ZERO analytic
  carries.** ⚠ **STILL the wall (the ONLY remaining gap to the true kernel):** the **Gaussian iterated-convolution
  CONVERGENCE** of the Neumann series (no proof assistant has iterated-convolution Gaussian bounds) + the under-integral
  Leibniz half of Duhamel's principle.
- **P2e — global assembly:** the Riemannian volume measure `dV` + `∫_M K_t(x,x) dV = Tr e^{−tΔ}` (ties to the L5
  trace-class/Mercer machine) ⟹ `Tr e^{−tΔ} ~ (4πt)^{−d/2}(Vol + (1/6)∫R·t + …)`.

### P3 — assemble the general discharge
P1 (`κ=1/6` gauge) + P2 (kernel + expansion) + the L5 trace machine + `HeatCoeffDetermination` invariance ⟹
`a₁=R/6` for an arbitrary closed manifold. This is the goal; it is the union of P1 and P2, both large.

## Books
**HAVE (in `refs/`):** Gilkey *Invariance Theory, the Heat Equation, and the Atiyah–Singer Index Theorem*
(`InvarianceTheory1Ed.pdf`); Berline–Getzler–Vergne *Heat Kernels and Dirac Operators* (`ruwkno3rtNaI5.djvu`);
Rosenberg *The Laplacian on a Riemannian Manifold* (djvu — §3.2 the working parametrix text); Simon *Trace Ideals*
(the L5 side). These COVER the parametrix construction (P2a–c) + the coefficient determination.
**WOULD WANT for the deep wall (P2d):** **Grigor'yan, *Heat Kernel and Analysis on Manifolds*** — the analytic
bible for heat-kernel existence, Duhamel/Levi convergence, and Gaussian bounds (not in `refs/`). Optionally
**Lee, *Introduction to Riemannian Manifolds*** or do Carmo for the exp-map/RNC-gauge textbook cross-check (the
campaign has its own equilibrium-Grönwall route, so this is a convenience, not a blocker).

## Loop scope (what is autonomously buildable now)
The loop drives **P1 rung-by-rung** (ContDiff¹ → ² → ³ exp_p via the augmented jet-ODEs, per `THE_EXP_JETS_PLAN.md`),
each an [AF] std-3 green brick, then **checkpoints at P2d** (the Levi/Duhamel convergence — the genuine wall).
P2a–c are partially reachable (ansatz + transport structure) and can be attempted; P2d and P2e are the
community-scale analytic walls where the loop stops honestly. NEVER claim general `a₁=R/6` / a curved heat kernel /
numerical-G until P2 lands.
