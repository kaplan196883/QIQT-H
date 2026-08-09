# VACUUM AREA-LAW PLAN — closing the last carried holographic input (`S ∝ A_geom`)

**Date:** 2026-08-09. **Provenance:** GPT-5.6 (Sol) consult, grounded in a full Lean survey of the
area/induced-gravity side (`FiniteCornerValuation`, `SakharovRatio`, `ConicalSakharov`,
`BoundaryGaussianAreaLaw`, `FQBoundMicro`, `FQBoundCGP`, `RecordMincutEntropy`,
`GaussModeEntropyDerived`, `Decoupling/DecouplingShadow`). Companions: `A1_R6_RESIDUE_STATUS.md`,
`HEAT_KERNEL_GAP_PLAN.md`, `WHERE_WE_ARE.md`, `ADSCFT_GAP_ANALYSIS.md`.

**⚠ Status label (the relabel this doc installs): the geometric area-SCALING is NOT an open physics
problem. It is KNOWN free-field physics (BKLS 1986 · Srednicki 1993 · Casini–Huerta), not yet
formalized in Lean — a scoped formalization campaign.** Prior docstrings/notes calling it "M3
frontier" / "Tier-3/OPEN" should be read as "known-but-unformalized," per this plan.

---

## 0. WHY THIS IS THE LAST CARRIED PIECE

Everything on the induced-gravity/holographic side is machine-checked EXCEPT one input. Derived:
- **finiteness ⇒ cap** `S(ρ_R) ≤ log dim ℋ_R` (Jensen/Gibbs);
- **forced log-weight** — any additive + embedding-monotone valuation is uniquely `κ·log dim`
  (`finiteCorner_valuation_rigidity`, 2-adic counterexample guarding necessity);
- **per-mode entropy grounded** — `gaussModeEntropy ν = −∑ pₖ log pₖ` (thermal Shannon);
- **the ¼ ratio** — regulator- and matter-independent `4π/16π` (`sakharov_ratio`);
- **Susskind–Uglum** — `S_ent = (A/4)·δ(1/G)`, `4·G_ind·S_ent = A` (`ConicalSakharov`), given `a₁=R/6`;
- **min-cut bound** `S_vN ≤ log(min-cut capacity)`; **Williamson normal form**; **one-particle CGP
  relative entropy `≥ 0`** — all unconditional / axiom-free.

The ONE carried holographic input, named as the frontier in every file's own scope: **that the
region's entanglement entropy (equivalently its effective log-dimension) scales with the geometric
BOUNDARY AREA, not the volume — `S ∝ A_geom` — for the ACTUAL continuum vacuum.** Finiteness alone
gives only the cap, and `bulk_entropy_volume_law` PROVES the same finite modes give a *volume* law;
`S ∝ A` is proven only for the explicit boundary-local model (`BoundaryGaussianAreaLaw`), carried as
a modeling assumption.

Closing this replaces "assumed boundary-local model" with "actual-vacuum theorem." It does NOT by
itself yield the sharp regulator-independent `S = A/4G` (see §5).

---

## 1. THE TARGET THEOREM(S)

Spacetime dim `d`, spatial `D = d−1`, `d ≥ 3` (`d = 2` is the exceptional log case). `Ω ⊂ ℝ^D`
bounded with entangling surface `Σ = ∂Ω`, `A_Σ = ℋ^{d−2}(Σ)`. `H_ε` a specified UV-regulated free
scalar, `|0_ε⟩` its ground state, `ρ_{Ω,ε} = Tr_{Ω^c}|0_ε⟩⟨0_ε|`.

**Milestone M-Θ (area-order, kills the volume law):**
```
∃ 0 < c₋ ≤ c₊ < ∞,  ∀ small ε :  c₋·A_Σ/ε^{d−2} ≤ S(ρ_{Ω,ε}) ≤ c₊·A_Σ/ε^{d−2}
```
i.e. `S = Θ(A_Σ/ε^{d−2})` — proves area-order (not a unique coefficient).

**Milestone M-σ (sharp leading surface density):**
```
S(ρ_{Ω,ε}) = ε^{−(d−2)} ∫_Σ σ_reg(n_x) dA(x) + o(ε^{−(d−2)})
```
with `σ_reg` a regulator-dependent surface tension. Reduces to `c·A_Σ/ε^{d−2}` ONLY for a
rotationally-invariant regulator or an all-faces-symmetric cube (a cubic cutoff is anisotropic — do
not claim isotropy for free).

**⚠ MUST NOT be claimed:** an exact finite-ε equality `S = c·A_Σ/ε^{d−2}` (false — curvature, mass,
corners, edges, logs, finite terms), or a regulator-independent leading coefficient (false). The
honest structure is `S_ε = c_{d−2}·A/ε^{d−2} + Σ_j (subleading area invariants)/ε^{d−2−j} +
c_log·log(L/ε) + S_finite + o(1)`.

### First concrete target (smallest honest closure) — the massless lattice-aligned cube
```
S_vac(C_L) = 6·σ₀·L^{D−1} + o(L^{D−1}),   0 < σ₀ < ∞,   D ≥ 2
```
(`C_L` = cube of side `L` in lattice units, critical/massless vacuum, explicit IR prescription),
then the fixed-physical-size form with `ε = R/L`:
```
S_vac,ε(Ω) = c_lat · A_Σ/ε^{d−2} + o(ε^{−(d−2)}).
```
The general smooth-region and rotationally-invariant `cA` versions are SUBSEQUENT strengthenings —
do not bundle them into the first closure.

---

## 2. ROUTES, RANKED

### Route 1 (recommended) — refined Srednicki/BKLS harmonic-lattice
Cleanest if the theorem must literally concern `S_vN(ρ_{Ω,ε})` on a factorizing regulated Hilbert
space. Reuses the repo's Williamson + `gaussModeEntropy` machinery; stays FINITE-DIMENSIONAL at every
cutoff (dodges type-III₁); avoids replica analytic continuation. Implementation is NOT "numerically
diagonalize a ball" — it is: (i) planar half-space entropy density → (ii) finiteness+positivity of
that density → (iii) boundary localization → (iv) patchwise transfer to a cube / smooth surface →
(v) the joint thermodynamic + massless + continuum limit.

### Route 2 — replica / conical heat-kernel
Shortest if only the LEADING regulated continuum term is wanted, and it REUSES `a₁=R/6`. Needs the
replica identity `Tr ρ^n = Z(M_n)/Z(M_1)^n`, the proper-time rep `log Z = ½∫(ds/s)Tr e^{−sP}`, the
conical heat-trace variation `(1−n∂_n)Tr e^{−sP_n}|₁ = A_Σ/(6(4πs)^{(d−2)/2}) + …`, integration in
`s`, and locality/partition-of-unity transfer to smooth `Σ`. New layers: the conical-singularity
heat kernel + the replica bridge + avoiding an unjustified integer-`n` continuation + connecting the
regulated replica entropy to a literal finite-cutoff `S_vN`. (`d=4` gives `A_Σ/(48πε²)+O(log)`.)

### Route 3 — Casini modular / relative-entropy — NOT a direct route
`ΔS ≤ Δ⟨K⟩` controls entropy DIFFERENCES; the leading vacuum area divergence CANCELS in `ΔS`. Great
for Bekenstein-type bounds / first-law / monotonicity; does NOT fix the absolute leading coefficient.

### Route 4 — crossed-product Type-II dual weight — relocates, doesn't close
Supplies a semifinite trace for type-III, but identifying its normalization/effective dimension with
`A_Σ/ε^{d−2}` IS the missing theorem. Explanatory, not a proof of the coefficient.

---

## 3. THE CONCRETE LEMMA CAMPAIGN (Route 1)

**A — finite Gaussian infrastructure (MECHANICAL; repo nearly has it).** Regulated `K_ε = m²−Δ_ε`;
positivity (incl. `m>0`, finite-volume BC, massless zero mode); vacuum covariances `X=½K^{−1/2}`,
`P=½K^{1/2}`, `⟨qp+pq⟩=0`; reduced Gaussian state on a site subset; symplectic spectrum
`= spec √(X_Ω P_Ω)`; `S = Σ h(ν_j)` (already formalized).

**B — dimension-UNIFORM Gaussian-entropy estimates (WALL).** `S(ρ_Ω) ≤ F(‖X_{Ω,Ωᶜ}‖_{S_p},
‖P_{Ω,Ωᶜ}‖_{S_q})`; behaviour of `h(ν)` near `ν=½` and large `ν`; stability of Gaussian entropy under
covariance perturbations UNIFORMLY as the matrix dimension grows; a boundary-decoupling tail
estimate. ⚠ A naïve Fannes inequality has a volume-sized dimension constant that DESTROYS the scaling
— covariance-specific, dimension-uniform estimates are required.

**C — fractional lattice Green-function decay (WALL, esp. critical).** Bounds on `K_μ^{−1/2}(x,y)`
and `K_μ^{1/2}(x,y)`: massive exponential decay; the `K^{1/2}` off-diagonal cancellation; UNIFORM
estimates as `μ = mε ↓ 0` (correlation length `ξ ∼ (mε)^{−1} → ∞`, so a gapped area-law theorem does
NOT transfer); massless polynomial-decay + cross-boundary summability (`D ≥ 2`).

**D — planar surface entropy density (the coefficient source).** Tangential Fourier transform →
1-D chains at momentum `k∥`, effective mass `μ_eff² = μ² + ω∥(k∥)²`; entropy decomposition into
sectors; the half-chain entropy `s_1D(η) = O(log(1/η))` as `η↓0`; **IR integrability**
`∫_{BZ^{D−1}} s_1D(ω∥(k)) dk < ∞` (the key fact — `log(1/|k|)` is integrable in positive tangential
dim; fails at `D=1`, giving the `1+1` log law); define/finiteness of the surface tension
`σ_μ(n) = lim_L S_slab,μ(L,n)/L^{D−1}`, `0 < σ₀(n) < ∞`.

**E — localization to the geometric boundary (WALL).** Cube: split cut into face-interiors (each
`σ₀(e_i)L^{D−1}+o`), edges/corners (`o(L^{D−1})`, possibly `L^{D−2}log L`), approx additivity of
separated faces. Smooth `Σ`: cover by patches `ε ≪ ℓ ≪ R_curv`, flatten each vs a half-space,
cumulative flattening error `o(ε^{−(D−1)})`, sum local planar coefficients.

**F — geometric counting (Mathlib-grade GMT).** `#{x : dist(x,Σ) ≤ Cε} = O(A_Σ/ε^{D−1})`; lattice
boundary measures → anisotropic perimeter `ε^{D−1}#{crossing bonds ∥ e_i} → ∫_Σ |n_x·e_i| dA`;
isotropic-regulator reduction to Hausdorff area; edge/corner bounds.

**G — the noncommuting limits (HARDEST).** Specify + control the order/joint limits: finite IR box →
∞ volume; region `L → ∞`; `μ = mε → 0`; `ε → 0` at fixed physical `Ω`; optional `m → 0`. The
interchange (thermodynamic ⇄ massless ⇄ UV) is the single hardest part.

---

## 4. DIFFICULTY TIERING (vs the `a₁=R/6` campaign)

- **Gapped-lattice area UPPER bound** (M-Θ, `m>0`): ≈ or somewhat SMALLER than the a₁ campaign.
- **Replica/heat-kernel leading COEFFICIENT** (Route 2): ≈ or moderately LARGER than a₁ (reuses a₁;
  adds conical + replica).
- **Sharp lattice-vN asymptotic, critical continuum limit, smooth regions** (M-σ, general):
  SUBSTANTIALLY LARGER than a₁ (combines finite Gaussian info theory + fractional-operator estimates
  + Toeplitz/Fourier asymptotics + GMT + critical scaling + dimension-uniform entropy continuity +
  multiple noncommuting limits).

**Recommended progression:** (1) massive lattice, aligned half-space: finite positive entropy
density; (2) massive lattice, aligned cube: `S = σ_μ A + o(A)`; (3) critical limit `μ↓0` (`D ≥ 2`);
(4) physical continuum limit; (5) general smooth regions + anisotropic surface tension; (6) optional
isotropic regulator → literal `cA`.

---

## 5. THE HONEST CEILING — what closing it buys, and what it does NOT

**Buys:** removes the boundary-local toy assumption; establishes, for the actual regulated vacuum,
that the entanglement entropy has a LEADING term `∝ geometric boundary area`, i.e. the UV-entangled
dof are a SURFACE density. Combined with the held Susskind–Uglum, the strongest honest claim:

> *In the regulated free-field induced-gravity model, the actual vacuum entropy has a leading
> geometric AREA divergence; with the SAME regulator, that leading divergence renormalizes `1/G`,
> combining as `A/(4·G_ind)`.*

**Does NOT buy** the sharp standalone `S = A/4G`: the coefficient is cutoff/regulator-dependent;
there are subleading/corner/log/finite terms; the continuum algebra is type-III₁ (no standalone
finite `S`); the `1/4G` is the counterterm-MATCHING statement, not a regulator-independent standalone
entropy. Nonminimal scalars, gauge fields, edge modes, contact terms need extra care. Do NOT say
"finiteness alone derives Bekenstein," nor "the full finite-cutoff entropy equals exactly `A/4G`."

---

## 6. FIREWALL (binding)

This file plans; it claims nothing proven. The area-SCALING remains a CARRIED input until M-Θ (at
least) lands. Nothing downstream may treat `S ∝ A_geom` as discharged. NOT QG; not a claim that the
physical vacuum is holographic beyond the free-field leading-area result this campaign targets.

---

## 7. CAMPAIGN STATUS (2026-08-10) — VACAREA-1…5 landed; single-session bricks EXHAUSTED; area coefficient = the multi-session wall

An autonomous loop ground the tractable rungs of Route 1, one green `[AF]` std-3 brick per iteration
(all pushed, `#print axioms`-pinned std-3, no `sorry`, no new axiom), in
`lean/mathlib/QIQTH/VacuumAreaLaw.lean` (`namespace QIQTH.VacuumAreaLaw`):

| brick | commit | what landed |
|---|---|---|
| VACAREA-1 | `2c6cc6c9` | finite Gaussian foundation: regulated `K_ε=m²−Δ_ε`, positivity, vacuum covariances `X=½K^{−1/2}`,`P=½K^{1/2}`, pure-state CCR `X·P=¼`, reduced symplectic spectrum `= spec √(X_Ω P_Ω)`, `redEntropy = Σ gaussModeEntropy(ν_j)` |
| VACAREA-2 | `e04102fd` | the reduced **Heisenberg floor** `½ ≤ ν_j` (`redSympEig_ge_half`) via twice-Schur `(X_Ω)⁻¹ ⪯ (X⁻¹)_Ω`; `redEntropy_nonneg'` unconditional |
| VACAREA-3 | `e6efaebd` | the massive **gapped Loewner window** `m²·1 ⪯ K_ε ⪯ (m²+4/ε²)·1` (operator-norm-free cyclic-shift factorization); clean checkpoint at the CFC-sqrt-over-ℝ wall |
| VACAREA-4 | `b54c6498` | the **real-Hermitian spectral-order layer**: `loewner_of_eigenvalues_ge/le`, `eigenvalues_sqrt` (`eig(√A)=√eig A`); restored `m_le_sqrtK`,`sqrtK_le` |
| VACAREA-5 | `33e6e62e` | the **inverse Loewner bound** `loewner_inv_le` + the full cap chain → **`redEntropy_le`**: the volume-compatible upper bound `S(ρ_Ω) ≤ \|Ω\|·gaussModeEntropy(ν_max)` |

**Net:** finite Gaussian foundation + the **physicality cap** `½ ≤ ν_j ≤ ν_max` + the
**volume-compatible entropy upper bound**, all axiom-free. Reusable Mathlib-gap lemmas thrown off:
real-Hermitian Loewner ↔ eigenvalue bounds (both directions), `eig(√A)=√eig A`, and the inverse
Loewner bound over ℝ matrices.

**⚠ NOT the area law.** `redEntropy_le` bounds entropy by the *volume* (site count); no area lower
bound, no surface coefficient. `S ∝ A_geom` remains the carried input.

**Remaining wall (single-session bricks exhausted):** the area coefficient — M-Θ (the `Θ(A/ε^{d−2})`
two-sided bound) and M-σ (the surface density) — is the **multi-session wall** (Sol-confirmed):
dimension-uniform quasi-local Green-function decay `|K^{±1/2}(x,y)| ≤ C e^{−c|x−y|}`, periodic-distance
boundary summation, Schatten control of the symplectic defect, and planar surface-tension `σ₀(n)`
finiteness / IR-integrability (§3-C/§3-D). Needs an explicit scoped multi-session commission (M-Θ
upper bound first), not more single-session bricks. **Campaign checkpointed here.**
