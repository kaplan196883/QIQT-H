# A₁ = R/6 — THE FINAL-STATE CENSUS (2026-08-03)

**Provenance.** The complete, honest documentation of the `a₁ = R/6` conditional chain after the
43-brick session J4-116…J4-158 (`ConvApproximants` → `PartialsToFDeriv`), the direct continuation
of the jet-4 tower. Authoritative source = the `AxiomAudit.lean` `★` pin blocks (lines ~15707–16401)
and the theorem statements in `CapstoneStatus.lean` / `SpatialC2.lean` / `ResidueThreading.lean` /
`ConcreteDominations.lean`. This is a status document; it changes no result's labels.
**⇒ See the `## ADDENDUM 2026-08-04 (J4-154…158)` section at the foot for the newest layer;
the tables in §2–§3 have been updated in-place where those five bricks moved an item.**

**Meta (verified against the pins and `git log`).**
- All bricks `[AF]` std-3: raw axiom count **0** (`propext`, `Classical.choice`, `Quot.sound` only);
  no `sorry`; no `expRho`; no vacuous `:= True` hypotheses.
- Every J4-116…J4-158 brick was **independently build-verified** at landing.
- Pushed through commit **`c6d72971`** (`J4-158: the classical partials-to-FDeriv theorem + the
  hAssembly reduction`); the session count J4-116…J4-158 = **43 bricks**.
- ⚠ **BINDING: this is NOT unconditional `a₁ = R/6`.** It is the campaign's state of the art: a
  machine-checked *conditional* theorem whose residue is real, enumerated below, and correctly tiered.
  The honest theorem is **compact-uniform / pointwise** (base point `q ∈ K` compact), not global —
  a global `∀q` bound is mathematically false for a wild-at-∞ metric (the `Q1` finding, J4-16/17).

---

## 1. THE THEOREM CHAIN

Four theorems, each strictly reducing the hypothesis surface of the one above it. All share the same
**conclusion**: for the concrete `N = 1` gated van-Vleck witness `H_G`,

```
heatOp g gi (trueHeatKernel H_G (leviSeries (heatOp g gi H_G))) t 0 0 = 0          -- solves the heat eqn
∧ trueHeatKernel H_G (…) t 0 0
    = G_t(0)ⁿ · ( 1 + ((∑ᵢ Ricᵢᵢ)/6)·t + t²·( tail + heatConv-remainder/(G_t(0)ⁿ·t²) ) )
```

i.e. the diagonal short-time expansion with the leading coefficient **`(∑ᵢ Ricᵢᵢ)/6 = R/6`** — the
van-Vleck value derived earlier (`VanVleckCancellation`, unconditional). The `Finset.Ico 2 (1+1) = ∅`
tail collapses at `N = 1`.

| # | theorem (file) | states | what its hypothesis surface adds/removes |
|---|----------------|--------|------------------------------------------|
| 0 | `trueKernel_diagonal_a1_eq_R6_residual_restricted_C2` (`ConcreteDominations.lean:193`) | the `(0,t]`-restricted capstone for an **abstract** `H`, generic `N≥1`, `hCH`/`hCConv` weakened to `ContDiffAt ℝ 2` (the D4 verdict — a `C²`-only witness can satisfy them). | 17 hypotheses: RNC/gauge (7) + `hHdiag hEboundW_le hInt hDuhamel hInter hDH hDConv hCH hCConv`. Calls `neumann_summable_alpha0_width2_le` + `trueHeatKernel_heat_eqn_levi_C2`. |
| 1 | `a1_R6_of_residue` (`CapstoneStatus.lean:166`, J4-146) | #0 **specialized to `H := vanVleckGatedWitness …`**, with the two STRUCTURAL slots discharged. | `hHdiag` ⟸ `capstone_hHdiag_supplied` (J4-105); `hDH` ⟸ `capstone_hDH_supplied` (J4-112). Adds gate data (`hChr,hK,S,a,b,…,hHeq`). Residue = GAUGE + `{hEboundW_le,hInt,hDuhamel,hInter,hDConv,hCH,hCConv}`. |
| 2 | `a1_R6_of_residue_hCH_discharged` (`SpatialC2.lean:165`, J4-147) | #1 with `hCH` genuinely proven and `hCConv` split into two honest layers. | `hCH` ⟸ `hCH_discharge` (germ/chart-`C²` tower); `hCConv` → `(D, hConvDeriv, hConvD1)`. New carries: `hSopen`, `hu` (transport-coeff smoothness). |
| 3 | `a1_R6_of_residue_hCH_hInter_discharged` (`ResidueThreading.lean:293`, J4-151) | #2 with `hInter` gone. **The current chain endpoint.** | `hInter` ⟸ `heatConv_leviSeries_interchange`, traded for the strictly-more-basic Levi domination family `hEbound/hEzero/hEmeas` on `E := heatOp g gi H`. |

**Endpoint (#3) carried surface**, verbatim from the statement:
GATE `{hChr,hK,S,a,b,ha,hab,hK0,hS0,hSopen,H,hHeq}` · GAUGE `{hg,hg0,hgi,hΓ,hdg0,htr,hsrc,hu}` ·
Levi domination `{hEbound,hEzero,hEmeas}` · `{hEboundW_le, hInt, hDuhamel, hDConv}` ·
`hCConv` layers `{D, hConvDeriv, hConvD1}`.

Relative to the raw capstone #0, the session has removed `hHdiag, hDH, hCH, hInter` and reduced
`hCConv` to two spatial-derivative layers.

---

## 2. THE SUPPLIER MAP (per capstone input → banked supplier → status)

Legend: **DISCHARGED** = proven at the witness, slot gone from the endpoint; **REDUCED** = a proven
supplier hands off to strictly-simpler sub-carries; **CARRIED** = still an explicit hypothesis.

| capstone input | banked supplier(s) (file / brick) | status |
|----------------|-----------------------------------|--------|
| `hHdiag` | `gatedWitnessN1_diag_eval_vanVleck` (OrderOneTower, J4-105) → `capstone_hHdiag_supplied` | **DISCHARGED** at the witness (carries `0∈K, 0∈S 0, W₀ 0 = 0`). |
| `hDH` | `gatedWitnessN1_hDH` (ConcreteDominations D3, J4-112) → `capstone_hDH_supplied` | **DISCHARGED** at the witness. |
| `hEboundW_le` | `gatedWitnessN1_hEboundW_le_vanVleck_final` (CoeffU1Fix, J4-108) ← the hunif summit `gatedWitness_hEboundW_unconditional` (UniformChartRadius, J4-100) → `capstone_hEboundW_le_supplied` | **REDUCED** (LANDED existential; once `(a,b,C,S)` are chosen, no residue beyond the gauge/coefficient-smoothness it already consumes). |
| `hInt` | `gatedWitnessN1_hInt_of_kernelContinuity` (GatedWitnessEmeas, J4-110) ⊕ time-cap producer (GatedWitnessMeas, J4-109) | **REDUCED** to kernel-continuity `{Continuous H_G, Continuous ∂ⱼH_G, gi/Γ measurable}`; residue = the joint base-point `q`-regularity (see §5·F1). |
| `hInter` | `heatConv_leviSeries_interchange` (LeviInterchange, hInter ✅ 4bff8b12) | **DISCHARGED** at the endpoint; traded for `hEbound/hEzero/hEmeas`. |
| `hDConv` | `hDConv_gatedWitnessN1_of_delta_final` (ConvCarriesDischarge, J4-117) ⊕ `hDelta_gatedWitnessN1_final` (BoundaryAssembly, J4-120) | **REDUCED** to `hDaLim` (Lemma-3.14 delta-family; boundary term never evaluated). `hFII`, `hJoint`, `hTail`, `hBoundary` all discharged (J4-117/118/119/120). |
| `hDuhamel` | `hDuhamel_leviSeries_final` (DuhamelLimitWiring, J4-123) ⊕ `hDuhamel_final_of_f2carries` (F2FamilyDischarge, J4-145) ⊕ `hDuhamel_penultimate` (InterchangeThreading, J4-142) ⊕ `hDaLimLU_discharge` (DaLimLocUnif, J4-148) | **REDUCED** to the loc-unif `hDaLimLU` (analytic core `witness_sliver2_grand`/`_complete` PROVEN, J4-137) + satisfiable F2/boundary/domination families. |
| `hDH`/`hHdiag`→ see above | | |
| `hCH` | `hCH_discharge` (SpatialC2, J4-147) | **DISCHARGED** — `ContDiffAt ℝ 2` genuinely proven via the on-gate germ factorization + base-0 chart `C²` (`chartField_contDiffAt_center`). |
| `hCConv` | `hCConv_reduction` (SpatialC2, J4-147) → `hConvDeriv_linewise` + `hCConv_L1_of_partialsContinuity` (CConvLayerDischarge, J4-155) | **SUPPLIED** at the L1 layer: `hConvDeriv` = the per-coordinate first spatial derivative under `∫∫` at the singular gap-free limit (dominated engine, non-constant `(t−s)^{−1/2}` dominator, J4-155); the exact L1/`hfam` shape assembled (J4-155), its `hAssembly` slot **REDUCED-to-gcoef-continuity** by `hAssembly_reduced` (J4-158). Residue = the gcoef dominated-convergence continuity + the C4b s-domination bundle. |
| GAUGE `hg/hg0/hgi/hΓ/hdg0/htr/hsrc/hu` | — (RNC normal-coordinate data + transport-coeff smoothness) | **CARRIED by design** (geometric inputs for a metric in normal coordinates at the origin; satisfiable, never the conclusion). |
| `hInter`→ `hEmeas` | (full joint strong measurability of `heatOp g gi H`) | **CARRIED** — the C⁰ diagonal `z ↦ W z 0` is Lipschitz (`hWmeas₀_unconditional`, J4-150), but the full joint `(τ,p,q)` measurability stays carried (§5·F1). |

---

## 3. THE CURRENT RESIDUE (grouped, per-item, swept against the pins)

### GAUGE — by-design geometric inputs (CARRIED, satisfiable, never the conclusion)
`hg` (metric `C^∞`), `hg0` (`g(0)=δ`), `hgi` (`g⁻¹(0)=δ`), `hΓ` (`Γ(0)=0`), `hdg0` (`∂g(0)=0`),
`htr` (the `−⅔·Ric` Hessian-trace), `hsrc`/`hu` (transport-source / transport-coefficient smoothness).
These are the normal-coordinate specification; they are the honest physical/geometric inputs of a
Seeley–DeWitt diagonal computation, not analytic TODOs.

### GATE DATA (CARRIED, structural)
`hChr` (`Γ ∈ C^∞`), `hK` (`IsCompact K`), `S`/`a`/`b`/`ha`/`hab`, `hK0` (`0∈K`), `hS0` (`0∈S 0`),
`hSopen`, `H`/`hHeq` (pin `H = vanVleckGatedWitness …`). **The cf gate-radius floor** `hfloor`
(`∃ρ₀>0, ∀z∈K, ρ₀ ≤ cf z`) is the one genuinely-open gate item — carried at `gate_ball_floor`/T4
(J4-151): the geometry "0 lands in the gate once `‖z‖` is small" is fully derived; only a positive
floor on the `.choose`-built gate radius `cf` over `K` is assumed (§5·F2).

### ANALYTIC-STRUCTURAL

**The C² chart / diagonal-only finding.** The a₁=R/6 diagonal is a LOCAL invariant. The joint-`q`
`C¹⁺` jets that earlier plans feared are NOT needed in full: `hCH` needs only `ContDiffAt ℝ 2`
(D4 verdict, J4-112), which the `C²`-only `uniformInverseChart` supplies — and it is DISCHARGED
(J4-147). The chart-jet layer (`ChartJetBounds`, J4-132; `SliverAssembly`, J4-133) is used only at
the field-center `z = 0` (`chartField_contDiffAt_center`, `chartField_centerJet_term_vanishes_base0`,
both UNCONDITIONAL given `0∈K`); the general-base second field jet `J1b` **EXISTENCE** is now
**SUPPLIED** (`chartField_secondJet_general`/`_domain`, GeneralBaseJets J4-156, via
`ContDiffAt.fderiv_right` + the germ-at-image-point provider; `_center` unconditional at `z=0`).
Only the `‖Q z‖ ≤ C_Q` z-modulus and `D²V₀(0)=0` remain — the J3 base-point carry.

**DISCHARGED (slot gone from the endpoint / supplied by a proven lemma):**
`hCH` (J4-147) · `hInter` (J4-151, via `heatConv_leviSeries_interchange`) ·
`hWmeas₀` (J4-150 `hWmeas₀_unconditional` — `z↦W z 0` Lipschitz) ·
`hRI` (J4-151 `chartW0_rightInverse`) · `hLHSlim` (J4-151, ⟸ U2 loc-unif) ·
`hVol` (J4-151, ⟸ `leviSeries_volterra` + proven interchange) ·
`hInterchange` (J4-141 `pd_pd_heatConvFrozen_interchange`) · `hLapFull` (J4-142 `hLapFull_of_lims`) ·
`hDa`/`hLap` (J4-142 `hDa_threaded`/`hLap_threaded`) · `hDaLimLU` (J4-148 `hDaLimLU_discharge`) ·
`hDerivLU` (J4-148) · `hqLip`/`hFLocLip` (J4-144, resolvent route) · `hFII` (J4-117/145) ·
`hpar`/`htime`/`hR` (J4-145, F2 group) · `hLap`/`hLapFull` interchange group (J4-141/142).

**PROVEN this layer (J4-154…158):**
`hdetz_general` (0 < det g(W₀z) on a ball — det-continuity + RNC gauge + the DISPLACEMENT-route
continuity of `W₀` at 0, no Grönwall; J4-155) · the **m-uniform sliver constant `C_R`** — the
witness→hbnd chain CLOSED (`witness_sliver2_eventual` U1 = the i-independent eventual bound +
`hbnd_witness_final` U2 = the exact `∀m` `hbnd` slot, master-gap ε-hoisting, nothing new carried;
J4-157) · the CLASSICAL `partials_continuous_hasFDerivAt` (continuous coordinate partials on a ball
⟹ `HasFDerivAt` with `Σᵢ gᵢ(x₀)·projᵢ`, on `Fin n → ℝ`, Pi sup-norm — the reusable Mathlib gap
proven in full incl. the `n=0` case; J4-158).

**SUPPLIED this layer (interface family provided at the witness):**
- the **amplitude family** (`amp_contDiffAt`/`amp_pdiffAt`/`amp_pd_pdiffAt` center **and** general
  = the `hAmp2` slot exactly; `amp_bound`/`amp_deriv_bound` = the E2 `Ba`/`Bd` slots, ball-existential;
  the general-base `hWz` provider `chartField_contDiffAt_center_general` via germ-at-image-point +
  `chartW0_rightInverse`; `amp_hAmp1_of_globalC1`). AmplitudeFamilyDischarge J4-154.
  Sub-carries: general-base `hWz`/`hdetz` (hdetz now PROVEN, J4-155), the global-`C¹` `∀x` `hAmp1`,
  uniform-in-z constants.
- the **`J1b` second-jet existence** at general base (`chartField_secondJet_general`/`_domain`;
  `_center` unconditional). J4-156. The `‖Q z‖` modulus stays J3-carried.

**REDUCED-with-carries (proven supplier hands off to satisfiable sub-carries):**
- `hCConv` → the L1 layer SUPPLIED (`hConvDeriv_linewise` dominated first spatial derivative under
  `∫∫` + `hCConv_L1_of_partialsContinuity`, J4-155); its `hAssembly` slot **REDUCED-to-gcoef-
  continuity** (`hAssembly_reduced`, J4-158) — the new carry = the dominated-convergence continuity
  of the derivative-integral coefficients (one honest layer better). `hConvD1` (`C¹`) subsumed here.
- `hDConv` → `hDaLim` (delta-family; `hTail`/`hBoundary` proven, J4-118/119/120).
- `hDuhamel` → `hDaLimLU` (discharged J4-148; core `witness_sliver2_grand` proven J4-137) + the F2
  family `{hCross, hMeasFII, hInnerCont}` + boundary-interface + domination families.
- `hInt` → kernel continuity `{Continuous H_G, Continuous ∂ⱼH_G, gi/Γ meas}` (J4-110).

**CARRIED analytic families (satisfiable by the concrete `N=1` witness; laborious, not research-grade):**
- Levi domination `hEbound/hEzero/hEmeas` for `E := heatOp g gi H` (traded in for `hInter`); `hEmeas`
  = the full joint measurability (§5·F1).
- The **engine measurability/continuity families** — `hMeasFII`, `hInnerCont`, `hUfloor`, the C3ε
  engine interface, `hCross`, the dominated-engine z/s domination + measurability families
  (J4-141/145/152), `hBcont`, `hAmeas`/`hBmeas`, `hu₀meas`/`hu₁meas`.
- `hGateSub` (gate `⊆ K ∩ ball` side condition, J4-143); `hE1`/`hSlice` (resolvent-route interface,
  J4-144); the gcoef dominated-convergence continuity + C4b s-domination bundle behind `hCConv` L1.
- The **`hEgrad` third-jet layer** — a genuine 3–5-brick development (the field-slot chart is only
  `C²`; needs `gaussComp_pd_pd_pd` + third moments), **DEFERRED** as an honest wall (J4-156 verdict).

*Moved OUT this layer:* the amplitude family (`PdiffAt`, `M₀/M₁/M₂`, `A/E/C` constants, amplitude
Lipschitz/sup/meas) → **SUPPLIED** (J4-154); the m-uniform `C_R` eventual bound → **PROVEN**
(chain closed, J4-157); `hCConv` layers `D`/`hConvDeriv`/`hConvD1` → **REDUCED-to-gcoef-continuity**
(J4-155/158); `J1b`/`hdetz_general` → **SUPPLIED/PROVEN** (J4-156/155).

The endpoint theorem `a1_R6_of_residue_hCH_hInter_discharged` bundles exactly these; the residue is
enumerated in the S1 supply table (`CapstoneStatus.lean` header) and the J4-146/150/151/152 pins.

---

## 4. WALLS FELLED THIS SESSION (J4-116…J4-152, one line each)

*(The J4-154…158 continuation is recorded in the `## ADDENDUM 2026-08-04` section at the foot.)*

- **hDConv → hDelta** (J4-116/117): concrete ε-approximants + the two regular carries (hFII via
  Chapman–Kolmogorov `gaussDdim_conv`; hJoint via the hpar/htime/hR partial decomposition) gone.
- **the delta family / Lemma 3.14** (J4-118): `gaussDdim_integral_eq_one` + the approximate-identity
  core `tendsto_integral_gaussDdim_smul` (near/far split against mass-one).
- **the Gaussian tail** (J4-119): `hTail` UNCONDITIONAL (`gaussDdim_tail_tendsto_zero`, no √n factor)
  + the equicontinuous-family engines.
- **the moving-peak Brick 2** (J4-120): `boundary_tendstoLocallyUniformlyOn` — the full 4-way split
  (main via T2u clamped-indicator + Heine–Cantor; eps; off-ball tail; mass defect).
- **the ε-Duhamel skeleton + the ∂_t−Δ_x = E move** (J4-122): `hE_combination` at finite ε where each
  separate limit diverges 1/τ; `hDuhamel_of_daLim` reduction; `hDuhamel_leviSeries_of_daLim`.
- **the limit wiring** (J4-123): boundary/etrunc/derivConv limits + `hDuhamel_final`.
- **the cancellation library (τ^{−1/2})** (J4-124/125): `gaussian_hessian_moment_zero` (∫∂ᵢ²G=0) +
  `gaussian_hessian_cancel` (the τ^{−1/2} gain) + the gradient analogue (t-free).
- **the sliver estimates** (J4-125): `sliver2_bound` — the 3-term ∂ᵢ²(G·A) Leibniz split; `sliver_rpow`.
- **the chart-image discovery + the L¹ adapter** (J4-126/127): the honest finding that the witness
  Gaussian argument is the CHART IMAGE `W z 0`, and `chartGauss_l1_sub_plain_tendsto` reconciling it
  with all plain-z interfaces without touching them (no change of variables).
- **the inverse-chart near-isometry** (J4-129): `chartW0_displacement` (‖W₀z+z‖≤4C_D‖z‖²) +
  `chartW0_nearIsometry` — the exp-side displacement bound inverted via Mathlib `ApproximatesLinearOn`.
- **the chart-jet Hessian** (J4-130): `gaussComp_pd_pd` — the exact chart Hessian; `gaussComp_amp_pd_pd`.
- **the centerJet death** (J4-132): `chartField_centerJet_term_vanishes_base0` — the odd-parity
  centerJet term of the normal form dies UNCONDITIONALLY at the assembly point (`V₀ 0 = 0`).
- **the sliver-2 closure (both remainder halves)** (J4-135/136/137): `hRem` (E2, J4-136) and `hRemE1`
  (E1 Gaussian-replacement, degree-10 moment grind, J4-137) — `witness_sliver2_grand`, both theorems.
- **the normal-form discharge** (J4-138): `hNormalForm_concrete` — the concrete 3-term Leibniz
  identity + `witnessSecondXDeriv_offGate_eq_zero`; `witness_sliver2_concrete`.
- **the Laplacian-sliver assembly (hDaLimLU)** (J4-139): `hDuhamel_assembled` — heatOp(H*F)=F+E*F
  end-to-end, conditional on the enumerated residue.
- **the loc-unif upgrade** (J4-148): `hDaLimLU_discharge`/`hDerivLU_discharge` — the K-uniform
  LapTrunc/etrunc limits, bypassing uniform-family `.add` friction.
- **hCH** (J4-147): `ContDiffAt ℝ 2` of the witness spatial slice genuinely proven.
- **the F2 group** (J4-145): `hpar/htime/hR` + `hFII` (H*F pairing) discharged; `hR` little-o proven.
- **the INTERCHANGE group** (J4-141/142): `hInterchange` (2nd-order under `∫∫` at the finite gap),
  `hLapFull`, `hDa`, `hLap` — the honest `Δ ↔ pd∘pd` adapter, a proof not a carry.
- **the geometric moduli** (J4-143): `chartYext_hco_hYdisp` — `hco`/`hYdisp` hold globally via the
  −id off-gate extension + rnsq parity; `hbnd_from_eventual`.
- **the resolvent Lipschitz** (J4-144): `resolvent_lipschitz_pointwise` from the Volterra identity
  `F = −E − E*F` (no termwise Levi differentiation) → `hqLip_discharge`.
- **the C⁰ joint-q wall (the geodesic Grönwall)** (J4-149/150): `uniformTube_twopoint_diff_bound`
  (nonlinear two-solution Grönwall) → `chartOrigin_lipschitz_modulus` (`z↦W z 0` Lipschitz) →
  `hWmeas₀_unconditional`.
- **the threading sweeps** (J4-151): `hRI`, `hLHSlim`, `hVol`, `hInter` gone;
  `a1_R6_of_residue_hCH_hInter_discharged`.
- **the engine instantiation** (J4-152): concrete `dH`/`dHH` kernels + `witness_secondOrder_interchange`
  + ε-pinning `hbnd_witness_supplied`.

---

## 5. THE HONEST FRONTIER — what genuinely remains for UNCONDITIONAL `a₁ = R/6`

The chain endpoint `a1_R6_of_residue_hCH_hInter_discharged` is a conditional theorem. To make it
unconditional (compact-uniform), the residue below must close. Ordered by difficulty.

**F1 — the joint base-point `q`-regularity / ODE-measurability wall (HARDEST; genuinely open).**
The full joint strong measurability `hEmeas` of `(τ,p,q) ↦ heatOp g gi H τ p q`, and the analogous
joint continuity feeding `hInt`. The C⁰ **diagonal** `z ↦ W z 0` is now Lipschitz (J4-150, via the
nonlinear two-solution geodesic Grönwall on the exposed ODE), which discharges `hWmeas₀`. But the
full joint object over all `(τ,p,q)` rests on smooth/measurable dependence of the opaque
`.choose`-built `uniformFlowExp` flow map on its base point. Per the Sol consults this is a
multi-week, Mathlib-grade development (Mathlib ODE has only Picard–Lindelöf + Grönwall; no
higher/joint smooth-dependence-on-IC). **Route:** extend the J4-149/150 geodesic-Grönwall stability
from the diagonal to the joint `(τ,p,q)` object, or a bounded-geometry joint-continuity engine. This
is the "3×-surfaced" wall and the single deepest residue.

**F2 — the cf gate-radius floor (moderate; open positivity fact).**
`hfloor : ∃ρ₀>0, ∀z∈K, ρ₀ ≤ cf z` for the `.choose`-built gate radius `cf` (T4, J4-151). The geometry
(0 lands in the gate for small `‖z‖`) is derived; only the uniform positive floor over `K` is assumed.
**Route:** a compactness/`.choose`-provenance argument giving a common floor — or re-architecting the
gate radius off the opaque selector (as the J4-53/54 uniform-flow re-architecture did for `expRho`).

**F3 — the satisfiable interface families (large but not research-grade; laborious assembly).**
As of J4-154…158 the TOP of this pile is discharged: the amplitude family is **SUPPLIED** (J4-154),
the m-uniform `C_R` is **PROVEN** (J4-157), `hdetz_general` is **PROVEN** (J4-155), the `J1b`
second-jet existence is **SUPPLIED** (J4-156), and the `hCConv` L1 layer is **SUPPLIED** with its
`hAssembly` **REDUCED-to-gcoef-continuity** (J4-155/158). What REMAINS tractable: the gcoef
dominated-convergence continuity; the uniform-in-z amplitude constants (Lipschitz covering); the
engine measurability/continuity families (`hMeasFII`, `hInnerCont`, `hUfloor`, C3ε, `hCross`,
dominated-engine z/s families, `hBcont`, `u₀`/`u₁` meas); `hGateSub`; the global-`C¹` `hAmp1`; and
the `‖Q z‖ ≤ C_Q` z-modulus / `D²V₀(0)=0`. Each is satisfiable by the concrete `N=1` witness (many
verified at `z=0`, reducing to the completed toolset — moments M5–M10, `gaussDdim_replace_bound`,
the T1' Hermite bridges); none is a research wall. **Route:** mechanical plumbing/instantiation.
**⚠ The one DEFERRED WALL split off from F3:** the **`hEgrad` third-jet layer** — the field-slot
chart is only `C²`, so `hEgrad` needs a genuine 3–5-brick third-jet development
(`gaussComp_pd_pd_pd` + third moments), deferred as honest (J4-156 verdict).

**F4 — scope: compact-uniform vs global (not a wall; a labelling).**
The honest target is the **compact-uniform / pointwise** `a₁ = R/6` (`q ∈ K` compact, or fixed `q₀`).
A single global `∀q` bound is mathematically false for a general wild-at-∞ metric (the `Q1` finding,
J4-16/17); a global statement would need an explicit bounded-geometry hypothesis, with no `a₁ = R/6`
content gained. This is a firewall on the statement shape, not an obstruction to close.

**Bottom line.** The `a₁ = R/6` diagonal coefficient itself is derived and untouched
(`VanVleckCancellation`, unconditional). The van-Vleck parametrix, the Levi/Duhamel convergence, the
delta-family, the sliver cancellations, the chart-transport naturality, the hunif/hEboundW summit,
the interchange group, the resolvent Lipschitz, and the C⁰ joint-`q` diagonal are all machine-checked.
What stands between here and an unconditional (compact-uniform) `a₁ = R/6` is **F1** (the joint
base-point ODE-regularity/measurability wall — the one deep, Mathlib-scale residue), **F2** (a
positivity floor on the gate radius), the now-**thinner** **F3** interface-assembly tail (its top
supplied/proven by J4-154…158), and the one new honest sub-wall inside it — the **`hEgrad`
third-jet layer** (~3–5 bricks). Not `a₁ = R/6` yet; the residue is real, enumerated, and correctly
tiered.

---

## ADDENDUM 2026-08-04 (J4-154…158)

Five further bricks continue the session past the J4-152 endpoint, working the F3 interface-assembly
pile from the top. All `[AF]` std-3 (raw axiom 0), each independently build-verified; pushed through
`c6d72971`. Pin blocks: `AxiomAudit.lean` lines ~16336–16401.

**J4-154 — `AmplitudeFamilyDischarge` (the amplitude family SUPPLIED).** LANDED the F3 top item:
`amp_contDiffAt`/`amp_pdiffAt`/`amp_pd_pdiffAt` at **both** the center and the general base — the
`hAmp2` slot exactly — plus `amp_bound`/`amp_deriv_bound` (the E2 `Ba`/`Bd` slots, ball-existential),
the general-base `hWz` provider `chartField_contDiffAt_center_general` (via the germ at the image
point + `chartW0_rightInverse`), and `amp_hAmp1_of_globalC1` (the `∀x hAmp1` reduction).
*Carried:* the general-base `hWz`/`hdetz` (hdetz PROVEN one brick later), the global-`C¹` `hAmp1`,
uniform-in-z constants.

**J4-155 — `CConvLayerDischarge` (`hdetz` PROVEN + the `hCConv` L1 layer).** `hdetz_general`
(0 < det g(W₀z) on a ball) PROVEN by the DISPLACEMENT route (det-continuity + RNC gauge + `W₀`
continuity at 0, no Grönwall). `hConvDeriv_linewise` = the per-coordinate first spatial derivative of
the convolution under both integrals at the singular **gap-free** limit (dominated engine, non-constant
interval-integrable `(t−s)^{−1/2}` dominator). `hCConv_L1_of_partialsContinuity` = the exact
L1/`hfam` shape of `SpatialC2.hCConv_reduction`, from linewise + a labelled partials→FDeriv assembly.
*Finding:* no general `Fin n`-domain Mathlib lemma for partials→FDeriv exists — the `hAssembly` slot
is identified as the genuine Mathlib gap (discharged in J4-158). *Carried:* the C4b s-domination
bundle + `hAssembly`.

**J4-156 — `GeneralBaseJets` (general-base `J1b` second jets + the F3 assessment).** The `J1b`
second-jet EXISTENCE at general base is EXECUTED: `chartField_secondJet_of_contDiffAt` (the hJetP
existence via `ContDiffAt.fderiv_right`), `chartField_secondJet_general` (the exact shapes consumed by
`hNormalForm_concrete`), `chartField_secondJet_center` (z=0 unconditional), `chartField_secondJet_domain`
(∀z in the domain, germ-at-image-point provider). **VERDICTS recorded:** `hEgrad` is a genuine
3–5-brick third-jet layer (the field-slot chart is only `C²`; needs `gaussComp_pd_pd_pd` + third
moments) — **DEFERRED** as honest; the m-uniform `C_R` is tractable plumbing (next brick).
*Carried:* the global `∀x hJetV`, the `‖Q z‖ ≤ C_Q` z-modulus (the J3 base-point item), `D²V₀(0)=0`.

**J4-157 — `UniformCRDischarge` (the m-uniform `C_R` — chain CLOSED).** The witness→hbnd chain closed
end-to-end. The ∃-structure finding: the grand estimate is per-ε-shaped but the witnessed constant is
value-level ε-free, so the move is to extract `C_R` ONCE at a master gap ε₀ (`hRem_discharge` +
`tE1_slice_bound`), then fire the explicit-`C_R` `witness_sliver2_final` at every `ε := epsSeq m ≤ ε₀`.
LANDED `witness_sliver2_eventual` (U1, the m-uniform eventual bound with an i-independent threshold) +
`hbnd_witness_final` (U2, the exact `∀m` `hbnd` slot of `sliver_sum_bound`). **Nothing new carried.**

**J4-158 — `PartialsToFDeriv` (the classical theorem + the `hAssembly` reduction).** The reusable
Mathlib-gap theorem `partials_continuous_hasFDerivAt` PROVEN in full: continuous coordinate partials
on a ball ⟹ `HasFDerivAt` with derivative `Σᵢ gᵢ(x₀)·projᵢ`, on `Fin n → ℝ` with the Pi sup-norm —
the telescoping coordinate-path + orientation-free 1-D MVT + `isLittleO` argument, incl. the `n=0`
degenerate case. PLUS `hAssembly_reduced`: the `hCConv_L1_of_partialsContinuity` `hAssembly` slot
closed-to-continuity. The new carry is one honest layer better — the dominated-convergence continuity
of the derivative-integral (gcoef) coefficients.

**Refreshed frontier after the addendum.** REMAINING TRACTABLES: the gcoef continuity (dominated
convergence); the uniform-in-z amplitude constants (Lipschitz covering); the engine
measurability/continuity families; `hGateSub`; the global-`C¹` `hAmp1`; the `‖Q z‖` z-modulus.
DEFERRED WALLS: the `hEgrad` third-jet layer (~3–5 bricks); **F1** the joint `hEmeas` base-point
ODE-measurability (the one deep Mathlib-scale residue); **F2** the cf gate-radius floor. BY-DESIGN:
the GAUGE / RNC normal-coordinate inputs. Still NOT `a₁ = R/6` — a machine-checked conditional
(compact-uniform) theorem with a real, enumerated, correctly-tiered residue.
