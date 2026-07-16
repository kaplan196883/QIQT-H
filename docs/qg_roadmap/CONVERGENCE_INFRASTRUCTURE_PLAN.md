# CONVERGENCE INFRASTRUCTURE — the Levi/Duhamel Gaussian-bound campaign (commissioned 2026-07-17)

**Goal.** Close the last analytic gap on the heat-kernel front: the **Gaussian iterated-convolution
CONVERGENCE** of the Levi/Duhamel Neumann series, which upgrades the built parametrix
(`THE_PARAMETRIX_CRITICAL_PATH.md` §P2, 14 [AF] bricks) into the **true heat kernel** and thereby
discharges the general curved **`a₁ = R/6`** — conjecture input #3, and the shared gate under D3-#3,
D5-warp, and D6-`c_i` in `DUALITY_ROADMAP.md`. Commissioned as an explicit multi-session campaign.

**Honest scale (binding).** This is a genuine multi-session, Mathlib-grade parabolic-PDE build
(Grigor'yan-territory iterated-convolution Gaussian bounds). No proof assistant has it. Each phase is
a self-contained, axiom-free, green checkpoint; the deep risk is concentrated in **C3** (the
time-simplex Beta/factorial decay) and **C5/C6** (the Neumann-series convergence + the true-kernel
diagonal expansion). Nothing here is claimed until earned; `a₁=R/6` for the TRUE kernel stays a
labelled input (G3 `PhysicalInputs`) until C6 lands.

## What is already BUILT (the foundation this rides on)
- **The parametrix scaffolding** (`QIQTH/HeatParametrix*.lean`, `LaplaceBeltrami.lean`,
  `FlatHeatEquation.lean`): `heatKernel1D`, `gaussDdim`, the flat heat equation, the ansatz `H_N`,
  the transport recursion (`u₁=τ/6` derived), the diagonal trace `a₁=(1/6)∫R√g dV`.
- **The Levi/Duhamel ALGEBRA, complete, zero analytic carries** (`QIQTH/HeatDuhamel.lean`): the
  space-time convolution `heatConv`, bilinearity, the FTC-1 boundary term, `duhamel_principle`
  (`(∂_t−Δ_g)(A*B)=B`), and associativity `heatConv_assoc''` (unconditional modulo integrability).
  **The iterated Levi product `H_N * E * E * …` is already algebraically well-founded.**
- **Mathlib provides:** `gaussianPDFReal μ v x = (2πv)^{−1/2}e^{−(x−μ)²/2v}` (note
  `heatKernel1D t = gaussianPDFReal 0 (2t)`); `gaussianReal_conv_gaussianReal` (measure-level
  semigroup, means/variances add, via char functions); `integral_gaussian` (`∫ e^{−b x²} = √(π/b)`);
  Gaussian Fourier transforms; `Real.Gamma`, `Real.betaIntegral`.

## The phases (each an [AF] std-3 green checkpoint). New file(s) under `QIQTH/`.

### C1 — the Gaussian convolution SEMIGROUP (density level) `QIQTH/GaussianConvolution.lean` ✅ LANDED (`3ed22d38`, [AF] std-3)
The Chapman–Kolmogorov / spatial semigroup property — the foundational estimate:
**DONE** via route (a) completion-of-square: `heatKernel1D_conv` (1-D) + `gaussDdim_conv` (d-dim, Pi-Fubini)
+ `heatKernel1D_pos`/`heatKernel1D_integrable` helpers. No checkpoints.
- **`heatKernel1D_conv`** (1-D): `∫ z, heatKernel1D t (x−z) · heatKernel1D s (z−y) dz
  = heatKernel1D (t+s) (x−y)` for `t,s > 0`. Route: complete the square in `z`, then `integral_gaussian`
  (variances `2t + 2s = 2(t+s)` add); OR bridge `heatKernel1D t = gaussianPDFReal 0 (2t)` +
  `gaussianReal_conv_gaussianReal` at the density level.
- **`gaussDdim_conv`** (`d`-dim, via the product structure `gaussDdim = ∏ heatKernel1D`): the spatial
  convolution of two `d`-dim Gaussians is the Gaussian with added variances (Fubini + `heatKernel1D_conv`).
- Corollaries: Gaussian × Gaussian pointwise product completes to a Gaussian (the "Gaussian bound"
  building block); normalization/positivity/monotonicity helpers.

### C2 — the space-time Gaussian×polynomial convolution bound `QIQTH/GaussianConvBound.lean`
The key one-step estimate: convolving Gaussian-times-polynomial kernels yields Gaussian-times-(higher)-
polynomial with explicit constants.
- **`gaussPolyConv_bound`**: for `|A(t,x)| ≤ C_A t^{a} G_{κ}(t,x)` and `|B| ≤ C_B t^{b} G_{κ}(t,x)`,
  `|heatConv A B (t,x,y)| ≤ C_A C_B · Β(a+1,b+1) · t^{a+b+1} · G_{κ}(t,x−y)` (spatial part = C1's
  semigroup up to a κ-comparison; time part = the one-step Beta integral `∫₀ᵗ (t−s)^a s^b ds`).
- The κ-comparison lemma (convolution slightly widens the Gaussian; dominate by a fixed `κ`).

### C2 — the self-similar convolution identity `QIQTH/GaussianConvBound.lean` ✅ LANDED (`b22c7d58`, [AF] std-3)
`gaussTimePow_conv` (`heatConv (τ^a G_τ)(σ^b G_σ) = (∫₀ᵗ(t−s)^a s^b)·G_t`) + `betaTimeIntegral_eq`
(`= t^(a+b+1)·Γ(a+1)Γ(b+1)/Γ(a+b+2)`, ℝ↔ℂ bridged via `Complex.betaIntegral`) + `gaussTimePow_conv_beta`.
No checkpoints.

### C3 — the iterated-convolution factorial decay `QIQTH/TimeSimplexBeta.lean` (DEEP — but tractable via C2 iteration)
The source of convergence — realized NOT as a raw `k`-dim simplex Fubini but as the **iteration of C2's
`gaussTimePow_conv_beta`** (the Beta factors telescope through `Β(x,y)=Γ(x)Γ(y)/Γ(x+y)`):
- **`iterKernel α k`** (recursive): `iterKernel α 1 = τ^α G_τ`; `iterKernel α (k+1) = heatConv (τ^α G_τ)
  (iterKernel α k)` (via `heatConvK`).
- **`iterKernel_eq`**: for `α>−1`, `t>0`, `k≥1`,
  `iterKernel α k t x y = (Γ(α+1)^k / Γ(k(α+1))) · t^(k(α+1)−1) · G_t(x−y)`. Induction on `k` using
  `gaussTimePow_conv_beta` (with `a=α`, `b=k(α+1)−1`) + the Γ telescoping
  `[Γ(α+1)^k/Γ(k(α+1))]·Β(α+1,k(α+1)) = Γ(α+1)^{k+1}/Γ((k+1)(α+1))`. The `1/Γ(k(α+1))` is the
  super-exponential (Mittag-Leffler) decay driving convergence. Mathlib `Real.Gamma`, `Gamma_pos_of_pos`,
  `Gamma_ne_zero`.

### C3 — the iterated-convolution factorial decay `QIQTH/TimeSimplexBeta.lean` ✅ LANDED (`e2cf6a14`, [AF] std-3)
`iterKernel` + `iterKernel_eq` (`= (Γ(α+1)^k/Γ(k(α+1)))·t^(k(α+1)−1)·G_t`, `Nat.le_induction` on C2 + Γ
telescoping). No checkpoints. The `1/Γ(k(α+1))` is the factorial decay.

### C5a — the MODEL Neumann series is SUMMABLE `QIQTH/LeviSeries.lean` (rides on C3 + ratio test)
The convergence payoff, self-contained on C3: **`iterKernel_series_summable`** — for `α ≥ 0` (β=α+1≥1;
choose parametrix order `N ≥ d/2`), `t > 0`, `Summable (fun k => (Γ(α+1)^k/Γ((k+1)(α+1)))·t^((k+1)(α+1)−1))`
(the model coefficient series; the Gaussian `G_t(x−y)` is a k-constant factor). Route: ratio test
(`summable_of_ratio_norm_eventually_le`) — ratio `= Γ(α+1)t^β·Γ((k+1)β)/Γ((k+2)β) ≤ Γ(α+1)t^β/((k+1)β) → 0`
(via `Γ((k+2)β) = Γ((k+1)β+β) ≥ ((k+1)β)Γ((k+1)β)` for β≥1, using `Gamma_add_one` + Γ-monotonicity on [1,∞)).

### C4 — the parametrix residual bound `QIQTH/HeatResidualBound.lean`
Cast the built residual `E = (∂_t−Δ_g)H_N` (`HeatParametrixError`/`HeatParametrixOrder`) into C2 form:
- **`residual_gaussPoly_bound`**: `|E(t,x,y)| ≤ C · t^{N−d/2} · G_{κ}(t,x−y)` (Gaussian × polynomial ×
  the `t^{N−d/2}` smallness from the ansatz order). Carries the smoothness/compactness of the metric
  jets as explicit hyps (honest).

### C5a — the MODEL Neumann series is SUMMABLE `QIQTH/LeviSeries.lean` ✅ LANDED (`9892ab32`, [AF] std-3)
`modelCoeff_summable` (ratio test on the Γ decay; clean Γ-monotonicity via `Real.Gamma_strictMonoOn_Ici`) +
`iterKernel_series_summable`. No checkpoints.

### C5b — the DOMINATION lemmas `QIQTH/LeviSeries.lean` (clean integral inequalities)
The bridge from the model to the actual residual:
- **`heatConv_abs_le`**: `|heatConv A B t x y| ≤ heatConv |A| |B| t x y` (integral/interval triangle inequality).
- **`heatConv_mono`**: `0 ≤ A ≤ A'`, `0 ≤ B ≤ B'` pointwise ⟹ `heatConv A B ≤ heatConv A' B'` (integral monotonicity).
- combined `heatConv_le_of_abs_le`. Foundation for the iterated bound.

### C5b — the DOMINATION lemmas `QIQTH/LeviSeries.lean` ✅ LANDED (`1f4d12d3`, [AF] std-3)
`heatConv_abs_le` + `heatConv_mono` + `heatConv_le_of_abs_le`. No checkpoints.

### C5c — iterated-convolution bound + NEUMANN SERIES CONVERGENCE `QIQTH/LeviSeries.lean` (DEEP)
- **`iterE` / `iterConv_bound`**: `|E^{*k}(t,x,y)| ≤ C^k · iterKernel α k t x y` (induction using C5b domination
  + C3's `iterKernel` recursion + heatConv bilinearity), CARRYING the one-step residual bound
  `|E| ≤ C · baseKernel α` (`C ≥ 0`) + the requisite integrability as hypotheses.
- **`leviSeries_summable`**: `Summable (fun k => iterE E (k+1) t x y)` — absolute convergence from `iterConv_bound`
  + C5a (`iterKernel_series_summable`) via comparison (`Summable.of_nonneg_of_le` / dominated).

### C6 — TRUE KERNEL + the diagonal expansion ⟹ general `a₁ = R/6` `QIQTH/TrueHeatKernel.lean` (CAPSTONE)
- **`trueHeatKernel`** `K := H_N + heatConv H_N F` and **`trueHeatKernel_heat_eqn`**: `(∂_t−Δ_g)K = 0`
  (via the built `duhamel_principle` + the Volterra identity `F = −E + (−E)*F`) with `K_0 = δ` (the
  parametrix delta-initial-condition).
- **`trueHeatKernel_diag_expansion`**: `K(t,x,x) = H_N(t,x,x) + O(t^{N+1−d/2})` (the C5 bound on
  `H_N*F` at the diagonal is higher-order), so the true diagonal `a₁` coefficient EQUALS the parametrix
  one, `= R/6`.
- **`heat_a1_eq_R_div_6`** — the payoff: general curved **`a₁ = R/6` for the TRUE kernel**, discharging
  conjecture input #3 / the D3-#3, D5-warp, D6-`c_i` gate. Then instantiate `SeeleyDeWittData`
  (the single Phase-7 instance the `DUALITY_ROADMAP` ledger anticipates).

## Dependency / critical path
```
C1 ──► C2 ──► C3 ──► C5 ──► C6      (C4 feeds C5; C4 depends on C1/C2)
                └── C4 ──┘
```
C1 first (foundational, reachable now). C2 needs C1. C3 is independent-ish (pure Beta/Γ). C4 casts the
built residual. C5 combines C2+C3+C4 over the iterated `heatConv`. C6 is the capstone.

## Discipline (unchanged)
One bg OPUS subagent per brick; independent verification (`#print axioms ⊆ std-3`, no `sorry`);
`AxiomAudit` pin with honest firewall; full budget check (budget 0); commit explicit paths + PUSH;
update this plan + `THE_PARAMETRIX_CRITICAL_PATH.md` + memory. **Checkpoint precisely at genuine
walls; never fake.** `a₁=R/6` for the TRUE kernel is NOT claimed until C6 lands — until then it stays
the carried G3 input.

## Honest scope firewall (binding)
This plan claims nothing. The parametrix + Levi algebra are built [AF]; C1–C6 are the analytic residue.
Until C6, general curved `a₁=R/6` remains a labelled interface input, never an axiom, never derived.
NOT the true kernel, NOT QG.
