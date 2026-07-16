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

### C1 — the Gaussian convolution SEMIGROUP (density level) `QIQTH/GaussianConvolution.lean`
The Chapman–Kolmogorov / spatial semigroup property — the foundational estimate:
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

### C3 — the time-simplex Beta / factorial decay `QIQTH/TimeSimplexBeta.lean` (DEEP)
The source of convergence: iterating C2 over the `k`-fold time simplex.
- **`simplex_beta`**: `∫_{0<s₁<…<s_k<t} ∏ (s_i−s_{i−1})^{α} ds = t^{k(α+1)−1}·Γ(α+1)^k / Γ(k(α+1))`
  (Dirichlet/Beta integral). Route: induction on `k` using `Real.betaIntegral` + `Real.Gamma_add_one`;
  the `1/Γ(k(α+1))` gives the super-exponential (`~1/k!`) decay. Mathlib has `Real.betaIntegral`,
  `Real.Gamma` — this is reachable but fiddly.

### C4 — the parametrix residual bound `QIQTH/HeatResidualBound.lean`
Cast the built residual `E = (∂_t−Δ_g)H_N` (`HeatParametrixError`/`HeatParametrixOrder`) into C2 form:
- **`residual_gaussPoly_bound`**: `|E(t,x,y)| ≤ C · t^{N−d/2} · G_{κ}(t,x−y)` (Gaussian × polynomial ×
  the `t^{N−d/2}` smallness from the ansatz order). Carries the smoothness/compactness of the metric
  jets as explicit hyps (honest).

### C5 — iterated-convolution bound + NEUMANN SERIES CONVERGENCE `QIQTH/LeviSeries.lean` (DEEP)
- **`iterConv_bound`**: `|E^{*k}(t,x,y)| ≤ C^k · t^{k(N+1−d/2)−1}/Γ(k(N+1−d/2)) · G_{κ}(t,x−y)`
  (combine C2 one-step + C3 simplex, by induction on `k`; uses the built `heatConv_assoc''`).
- **`leviSeries_summable`** + **`leviSeries`** `F := Σ_{k≥1} (−E)^{*k}`: absolute convergence from the
  `Γ` decay (ratio/root test); the sum is a well-defined kernel with a Gaussian bound.

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
