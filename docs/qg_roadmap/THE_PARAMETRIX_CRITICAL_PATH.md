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
- **Rung 2 — `ContDiff² exp_p`** (Jet₂: `Q'=DF Q + D²F(P,P)`, residual Grönwall ⟹ `o`). **⏳ PARTIAL / CHECKPOINT
  2026-07-15 (`ExpMapContDiff2.lean`, [AF] std-3).** TWO green results: (i) `expMap_contDiffOn_two_of_fderiv_contDiffOn_one`
  — the PROVEN Rung-2 REDUCTION: `ContDiff¹ (fderiv exp_p)` on the ball ⟹ `ContDiff² exp_p` (Rung-1 differentiability
  + `fderivWithin=fderiv` on the open ball + Mathlib `contDiffOn_succ_of_fderivWithin`), isolating the exact remaining
  obligation "`Φ_v(1)` is `C¹` in `v`"; (ii) the Jet₂ analytic ingredient `D²F = fderiv(fderiv F)` EXISTS and is `C^∞`
  (`contDiff_fderiv2_geodesicField`, `hasFDerivAt_fderiv_geodesicField`). **STILL OPEN (the multi-week bulk, NOT a
  Mathlib gap):** the `D²F` closed form + the Jet₂ fundamental solution `Q_v` on `[0,1]` (a fresh bilinear-valued PL
  tower, mirroring the `expJetFund` chain) + the parameter-residual Grönwall ⟹ `v↦Φ_v(1)` is `C¹`. `ContDiff² exp_p`
  is NOT yet produced unconditionally.
- **Rung 3 — `ContDiff³ exp_p`** (Jet₃: `R'=DF R + D²F(P,Q)+D³F(P,P,P)`). ~4–8 wk. ⟹ the bridge
  `rnc_christoffel_linearJet` (`rncDΓ = pd(christoffel g̃)(0)`) + `ContDiff g̃` ⟹ instantiate `heat_a1_of_gauge` at
  `g̃` ⟹ **`κ=1/6` unconditional given the metric.** (Does NOT yet give general `a₁=R/6` — that needs the kernel.)

### P2 — the heat-kernel parametrix PROPER (the deep wall — the actual discharge)
This is what proves the smooth kernel `K_t(x,y)` EXISTS and has the short-time diagonal expansion for an arbitrary
metric — i.e. what discharges general `a₁=R/6`. Sub-pieces (Rosenberg §3.2 / BGV Ch2 / Gilkey Ch1):
- **P2a — the parametrix ansatz** `H_N(t,x,y) = (4πt)^{−d/2} e^{−r(x,y)²/4t} · Θ(x,y)^{−1/2} · Σ_{k≤N} u_k(x,y) t^k`
  (`r`=geodesic distance, `Θ`=van Vleck — `RNCExpansion` has the diagonal `√det`; needs `r` off-diagonal).
- **P2b — the transport recursion** for `u_k` (`DeWittDiagonal` has `u_1` diagonal; extend off-diagonal + all `k`).
- **P2c — the error estimate** `(∂_t + Δ_x) H_N = O(t^{N−d/2})` (Gaussian × polynomial — hard bounds).
- **P2d — the Levi/Duhamel convergence** `K = H_N + H_N * (error) + …` → the ACTUAL kernel. **THE analytic heart**
  (iterated-convolution Gaussian-bound estimates; no proof assistant has this).
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
