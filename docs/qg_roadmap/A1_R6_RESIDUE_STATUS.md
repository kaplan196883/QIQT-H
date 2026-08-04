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

---

## Addendum (2026-08-04): the hCConv L1 branch — J4-160…175

Sixteen further bricks (`J4-160`…`J4-175`, commits `0ac1936d`…`43fba045`, ledger `f2b845b9`) drive the
`hCConv` **L1 spatial-derivative branch** — the `(D, hConvDeriv, hConvD1)` layer that the endpoint
`a1_R6_of_residue_hCH_hInter_discharged` (`ResidueThreading.lean:293`) carries. The branch supplies the
`hConvDeriv` slot (the `∃ u ∈ 𝓝 0, ∀ x∈u, HasFDerivAt (p ↦ heatConv H F t p 0) (D x) x` shape) by proving
the first spatial derivative of the heat convolution under `∫∫` (`hCConv_L1_final`, J4-160), then grinding
the resulting `gcoef`-continuity + witness-measurability + chart-geometry carries down to an honest,
satisfiable residue. All `[AF]` std-3 (raw axiom 0: `propext`/`Classical.choice`/`Quot.sound`), no `sorry`,
no `expRho`, each `#print axioms`-pinned at landing. Pin blocks `AxiomAudit.lean` ~16403–16720. **Still NOT
`a₁ = R/6`** — this hardens ONE branch of the conditional chain; the outer residue (§5, F1/F2/hEgrad, GAUGE)
is untouched. Every theorem statement below was re-read against the Lean before writing this addendum.

### The brick table (verified against the pinned statements)

| J4 | file / namespace | key theorems (verified) | what closed / reduced |
|----|------------------|--------------------------|------------------------|
| 160 | `GcoefContinuity` | `hCConv_L1_final`, `gcoef_continuity_discharge` | The L1 `∃`-shape assembled: `hCConv_L1_final` composes `PartialsToFDeriv.hAssembly_reduced` ∘ `HeatResidualBound.hCConv_L1_of_partialsContinuity` from `{hlin, hcont, hDrep}`. Reduces the `hConvDeriv` slot to a linewise-derivative family + gcoef-continuity + coordinate representation. |
| 161 | `WitnessDerivDomination` | G2 bundle: `hzcont`/`hzint` discharged, `hzbound` in shape | Three of the seven G2 slots of `gcoef_continuity_discharge` discharged at `witnessFieldDeriv`; `hzbound` reduced to a bare-kernel envelope. |
| 162 | `WitnessDerivMeasurability` | `g2_bundle_assembled` | **★★** Assembles ALL SEVEN G2 hyps at `witnessFieldDeriv` (dominators `(C₀·Cf)·G_{κ(t−s)}`, mass-one) → the `hcont` slot of `hAssembly_reduced`. Verified carries: `hC2fam, henv, hKmeas, hFmeas, hjoint, hdomS, hFbd`. |
| 163 | `G2CarryDischarge` | `gaussDdim_coercivity_envelope`, `hdomS_from_uniform`, `hKmeas_from_witness` | The x-free Gaussian envelope `G_τ(w) ≤ (√2)ⁿ·G_{2τ}(base)` under near-isometry coercivity (verified full proof, no carry); `hdomS` reordered to an x-uniform bare envelope `henvU`; `hKmeas` reduced (via a general slice-measurability lever) to `{hWmeas, hWdiff}`. |
| 164 | `HenvUInstantiation` | `henvU_assembled`, `henv_assembled`, `hdomS_assembled`, `hzbound_assembled` | The `henvU`/`henv` envelopes assembled from an x-uniform on-gate/off-gate **dichotomy carry** `hGateData`/`hGateData'`; `hdomS` and `hzbound` legs reduced to `{hGateData(′), hFbd}`. |
| 165 | `WitnessMeasDeriv` | `hWdiff_offGate` (unconditional), `hKmeas_concrete` | Off-gate field-slice derivative `= 0` proved unconditionally; `hKmeas_concrete` reduces the concrete `hKmeas` slot to four lighter carries `{hKm, hSm, hIn, hGateDiff}`. |
| 166 | `GateChartMeasurability` | `compactGate_measurableSet`, `hIn_composed_…`, `hKmeas_concrete_v2` | `hKm` **DISCHARGED** unconditionally (`MeasurableSet K` from `IsCompact K`); `hIn` reduced via a composition lever to `{hw, hVmapMeas}`. |
| 167 | `FoldedCoeffChartMeas` | `hw_discharged`, `gatedKernel_slice_…_of_restricted`, `hVmapMeasK_zero_of_geom`, `hKmeas_concrete_v3` | `hw` reduced to `{hg, hgpos, hu}`; the restricted-`K` indicator route weakens `hVmapMeas` to `volume.restrict K`; the `p=0` slice discharged from the banked near-isometry. |
| 168 | `ChartGeneralPContinuity` | `chartP_lipschitz_modulus`, `chartP_continuousOn`, `hVmapMeasK_of_geomOrMeas`, `hKmeas_concrete_v4` | General-`p` origin-chart Grönwall Lipschitz + `z`-continuity; the honest **per-`p` geometry-OR-measurability disjunction** discharge of `hVmapMeasK`. |
| 169 | `GateSetMeasurability` | `mem_flowBall_iff_chart`, `hKmeas_concrete_v5` | The flow-ball ↔ chart equivalence lever; `hSm` re-threaded to a `K`-relative `hSmK`. |
| 170 | `OnGateFieldRegularity` | `hGateDiff_hC2fam_shared_core` | **★★★** BOTH remaining field-slot carries (`hGateDiff`, `hC2fam`) produced from ONE shared geometric root (on-gate coincidence with the inner kernel + local-coincidence lever). |
| 171 | `ChartFieldC2General` | `chartField_contDiffAt_reachable_uniform`, `hGateDiff_hC2fam_from_reachableGate` | **★** Chart `C²` at EVERY reachable point (single uniform radius `δ₀`), **NO metric hyps** — reads off `uniformInverseChart_huniformChart`'s IFT clause. Full pipeline capstone for both carries. |
| 172 | `ConcreteGateAssembly` | `reachableGate_concrete`, `flowBallGate_hRI_onGate`, `hC2fam_concrete_final`, `l1_residue_status`, ~~`hKmeas_concrete_v6`~~ | Instantiates the abstract gate `S` with the concrete flow-ball gate `S z = φ_z '' ball 0 c`; openness / left-inverse / on-gate right-inverse / reachability all DERIVED. `hKmeas_concrete_v6` landed but is **SUPERSEDED** next brick (see Corrections). |
| 173 | `GeomPTransportAssess` | v6-vacuity audit, `hKmeas_concrete_v7`, `radialTransportSolve_continuous`, `hu_of_solve_smooth` | The honest **per-`p` disjunction** replacing v6's unsatisfiable `hGeomP`; the transport ray-integral continuity rung PROVEN; `hu` reduced to two operator premises `{hSolve, hT}`. |
| 174 | `TransportOpSmoothness` | `hT_discharged`, `radialTransportSolve_contDiff_one`, the `⊤=ω` finding | `hT` (transport op preserves `C^∞`) **DISCHARGED**; the `C¹` ray-integral rung proven; the finding that `(⊤:WithTop ℕ∞)=ω` is the ANALYTIC level → `hSolve` at `ω` is a genuine Mathlib gap (no parametric-analytic-integral lemma). |
| 175 | `HuInftyRebase` | generic `rayIntegral` tower, `radialTransportSolve_contDiff_infty`, `hu_infty_closed`, `hw_discharged_infty` | **`hu` CLOSED at `∞`** from `{hg, hgi, hgpos}` ALONE (`hu_infty_closed`, verified) — no longer an independent carry; the consumer `⊤↦∞` audit table shows every consumer is `∞`-safe. |

### The current honest residue of the L1 / hCConv branch (each with its exact carrier + status)

1. **The `v7` per-`p` disjunction** — carrier `GeomPTransportAssess.hKmeas_concrete_v7`. For each field point
   `p`: EITHER the geometric triple `{hball : W z p ∈ ball 0 (modulus p), hnorm : ‖W z p‖ ≤ ρ_K,
   hRI : φ_z(W z p) = p}` on `K`, OR the far-`p` pair `{MeasurableSet (K ∩ {z | p ∈ S z}),
   AEStronglyMeasurable (z ↦ W z p) |_K}`. **Satisfiable and total**: the LEFT branch is discharged for
   every reachable `p` (`reachableGate_concrete` + `flowBallGate_hRI_onGate`); the RIGHT branch carries only
   the genuine far-`p` measurability residue. Honest (never unsatisfiable).

2. **Coverage geometry `hMemNear`/`hMemPt`** — carriers `ConcreteGateAssembly.hKmeas_concrete_v6`/
   `hC2fam_concrete_final`/`l1_residue_status`. Per relevant `(x₀, z)` with `z ∈ K`, the field point lies in
   the gate: `x₀ ∈ φ_z '' ball 0 c`. This is the design intent of the gate (built to cover the reach);
   satisfiable, never the witness.

3. **Standard metric inputs `hg`/`hgi`/`hgpos`** — GAUGE by-design (metric `C^∞`, inverse `C^∞`,
   `0 < det g`). ⚠ Since J4-175, `hu` (transport-coefficient smoothness) **DERIVES from exactly these three**
   at the `C^∞` level (`hu_infty_closed`, verified) — so `hu` is no longer an independent residue item on the
   `∞` chain.

4. **`hjoint` — the last open G2 slot** — carrier `WitnessDerivMeasurability.g2_bundle_assembled`. Joint
   `(s,z)`-ae-strong-measurability of `(s,z) ↦ witnessFieldDeriv … (t−s) x p₂ · F s p₂` on the product measure.
   **Not discharged by any J4-160…175 brick** (verified: `hjoint` occurs only as the carried hyp of the bundle,
   no dedicated supplier). Satisfiable from the same gate/Gaussian/amplitude structure measured jointly; NOT
   the fibrewise-integrated conclusion. This is the genuine last-standing G2 measurability carry.

5. **`hFmeas` — source `F` measurability** — carrier `g2_bundle_assembled`. Each slice `z ↦ F s z`
   `AEStronglyMeasurable`. Instantiation-level (a property of the explicit source term `F`).

6. **`hGateData`/`hGateData'` + `hFbd` (envelope side, J4-164)** — carriers `HenvUInstantiation.hdomS_assembled`/
   `hzbound_assembled`. The x-uniform on-gate/off-gate DICHOTOMY families (off-gate: witness `≡ 0`; on-gate:
   the exact hypotheses `witnessFieldDeriv_gate_envelope_coercive` consumes, with fixed factor sup-bounds
   `Bs`/`Ba`/`Bd`), plus the scalar `F`-sup-bound `hFbd : |F| ≤ Cf`. Satisfiable.

7. **The `⊤↦∞` consumer-statement rebases** — mechanical interface edits, enumerated in the
   `HuInftyRebase.lean` Part-A audit table: `foldedCoeff_vanVleck_contDiff`, `hw_discharged`,
   `witnessInner_continuous`, `heatParametrix_contDiff_space`, `innerKernel_contDiffAt_field`,
   `gatedWitness_contDiffAt_field`, `hCH_discharge`, and the `hu` slot of `a1_R6_of_residue_hCH_discharged`.
   Each is verified `∞`-safe (interface consumers reproduce the level via `.mul`/`.sum`/`.add`; downcast
   consumers take `C⁰`/`C²` via `.continuous`/`.of_le`); only the statement TYPE reads `⊤`. Purely
   interface-level plumbing — no proof body uses `AnalyticOnNhd` or the `n = ω` branch of
   `contDiff_succ_iff_fderiv`.

8. **The chart-`P` geometry `{hball, hnorm, hRI}` for general `p` on `K`** — subsumed into item 1's LEFT
   disjunct (the on-gate instance of `hRI` is DERIVED by `flowBallGate_hRI_onGate`; the full-`K`/all-`p`
   instance rides the honest disjunction).

*(Also noted at the operator level: `hSolve` at the `ω` (analytic) level is a genuine Mathlib gap — no
parametric-analytic-integral lemma. But every consumer needs only `∞`, and `hu` closes AT `∞`, so `hSolve`
at `ω` is NOT actually required. The `ω`-level `hu` is not on the critical path.)*

### Corrections

- **`hKmeas_concrete_v6` is SUPERSEDED** (`ConcreteGateAssembly.lean:214`, struck through in the table). Its
  hypothesis `hGeomP` is a genuinely **unrestricted `∀ p : Point n`** of the chart triple, whose third clause
  `hRI : φ_z (W z p) = p` (chart right-inverse at `p`) **FAILS for far `p`** beyond the chart's uniform reach
  (for a metric with finite injectivity radius, such `p` is not the exponential image of any velocity in the
  ball). So `hGeomP` is **unsatisfiable in general** — the J4-168 far-`p` obstruction re-imported — which makes
  v6 a vacuously-true / soundness-hollow statement, not a usable reduction. J4-173's `hKmeas_concrete_v7`
  replaces it with the honest per-`p` disjunction (residue item 1). *[Precision note: the earlier framing
  called `hGeomP` "vacuous"; the exact mechanism is "unsatisfiable-in-general unrestricted `∀p`", not a literal
  `:= True` — the effect is the same (v6 unusable), and v7 is the honest form.]*

- **The `⊤ = ω` structural finding** (J4-174). In this toolchain `(⊤ : WithTop ℕ∞) = ω` is the ANALYTIC level,
  whereas `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` is `C^∞`. The van-Vleck / Laplace–Beltrami building blocks are
  real-analytic (Part A closes at `ω`), but the ray INTEGRAL of an analytic family is analytic only by a
  theorem Mathlib lacks. The finite-order differentiation-under-the-integral induction reaches every `C^N`
  (hence `C^∞`) but not `ω`. Consequence: `hu` closes at `∞` (all any consumer needs), and the `ω`-level solve
  premise is a real analytic gap that is off the critical path.

### The unchanged outer residue (endpoint `a1_R6_of_residue_hCH_hInter_discharged`, verified)

The endpoint theorem's carried surface (re-read verbatim, `ResidueThreading.lean:293`) is unchanged by this
branch: GATE `{hChr,hK,S,a,b,ha,hab,hK0,hS0,hSopen,H,hHeq}` · GAUGE `{hg,hg0,hgi,hΓ,hdg0,htr,hsrc,hu}` · Levi
domination `{hEbound,hEzero,hEmeas}` · `{hEboundW_le,hInt,hDuhamel,hDConv}` · hCConv layers
`{D,hConvDeriv,hConvD1}` (the branch this addendum hardens). The remaining outer walls, unmoved:

- **GAUGE / RNC** `{hg,hg0,hgi,hΓ,hdg0,htr,hsrc,hu}` — by-design normal-coordinate inputs. `hu` now
  additionally DERIVABLE at `∞` from `{hg,hgi,hgpos}` (J4-175), modulo the `⊤↦∞` rebase.
- **F1 — the joint base-point ODE-measurability wall** `hEmeas`
  (`StronglyMeasurable (q ↦ heatOp g gi H q.1 q.2.1 q.2.2)`) and the joint continuity feeding `hInt`. The
  single deep Mathlib-scale residue (smooth/measurable dependence of the `.choose`-built flow on its base
  point). **Untouched** — the L1 branch is orthogonal to it.
- **F2 — the `cf` gate-radius floor** (`∃ρ₀>0, ∀z∈K, ρ₀ ≤ cf z`). Moderate positivity fact. Untouched.
- **The `hEgrad` third-jet wall** — the field-slot chart is only `C²`; `hEgrad` needs a genuine 3–5-brick
  third-jet development (`gaussComp_pd_pd_pd` + third moments). **DEFERRED** (J4-156 verdict), unmoved.
- The `{hEbound,hEzero,hEboundW_le,hInt,hDuhamel,hDConv}` Levi/Duhamel/domination families (satisfiable
  interface assembly, laborious not research-grade).

### Tractability verdict

The `hCConv` L1 branch is now **substantially mechanical**. The `hKmeas` measurability chain is threaded to the
honest `v7` per-`p` disjunction (each branch satisfiable, the disjunction total); `hu` is **CLOSED at `C^∞`**
(reduces to the metric inputs); `hKm` is discharged unconditionally; the field-slot `C²` regularity is proved
at every reachable point with no metric hypotheses; and the gcoef-continuity conclusion is assembled by
`g2_bundle_assembled`. What is left on this branch is genuinely tractable plumbing: `hjoint` (the last open G2
joint-measurability slot — satisfiable), `hFmeas` (instantiation), the coverage geometry `hMemNear`/`hMemPt`
(by-design), the `hGateData` dichotomy + `hFbd`, and the mechanical `⊤↦∞` consumer-statement rebases. No new
research wall entered on this branch.

The **walls are unchanged and outside this branch**: **F1** (the joint `hEmeas` base-point ODE-measurability —
the one deep Mathlib-scale residue), **F2** (the `cf` floor), and the **`hEgrad` third-jet layer** (deferred,
~3–5 bricks). The GAUGE / RNC inputs remain by-design.

**⚠ `a₁ = R/6` remains CONDITIONAL** — a machine-checked, compact-uniform conditional theorem
(`a1_R6_of_residue_hCH_hInter_discharged`) whose residue is real, enumerated, and correctly tiered. This
addendum hardened one branch (`hConvDeriv`/`hCConv` L1); it changed no result's labels and did not touch
F1/F2/hEgrad.

---

## Addendum (2026-08-05): the Sol endgame execution — J4-182…195

Fourteen bricks landed since the L1 addendum, executing the Sol endgame plan (2026-08-04). Net effect:
the `hsrc` `⊤→∞` carry is **removed**; the F1 **factor axis** is fully discharged from geometry; the
chart is now **C⁴** (no-conjugate-points **dissolved**); the C4c off-diagonal premise is honestly
**corrected** (it is genuine curvature, not a recursion residual). Every result below is `std-3`
(`propext`, `Classical.choice`, `Quot.sound`) and `sorry`-free per its `#print axioms` block and the
`AxiomAudit` ledger. **⚠ `a₁ = R/6` remains CONDITIONAL** — this addendum moved and re-tiered the
residue; it did not close it.

### The brick table (verified against the pinned statements)

| Brick | File | Verified key result | Status |
|---|---|---|---|
| J4-182 | `InftyRebaseCapstone.lean` | `hCH_discharge_from_geometry` (spatial-`C²` witness-diag from `{hg,hgi,hgpos}`); `hsrc_from_geometry` (`hsrc` at honest `∞`) | std-3, DERIVED |
| J4-183 | `CConvFacade.lean` | five `:Prop` bundles (`Metric/ChartGate/Source/Derivative/Envelope`) + `hCConv_discharged_from_data` → the L1 `∃ w∈𝓝 0, HasFDerivAt (heatConv…)` shape | std-3 |
| J4-184 | `FlowBallInstantiation.lean` | `chartGateData_flowBall` (builds `ChartGate` from flow-ball geometry) + `facade_flowBall` (L1 `hfam` at gate `S z = φ_z '' ball 0 c`, ∀ `0<c<δ₀`) | std-3 |
| J4-185 | `GatedDInstantiation.lean` | `witnessFieldDeriv_measurable_of_gateEq` + `hDmeas_discharged` (the exact `CConvDerivativeData.hDmeas` field, per-fibre) | std-3 |
| J4-186 | `CompactTubeLemma.lean` | `compact_tube`/`compact_tube_ball` + **F2 VERDICT** `flowBall_gateRadius_floor` — the concrete gate has floor `b < c`; **F2 already discharged** (tube lemma not load-bearing) | std-3 |
| J4-187 | `ErrorKernelFactorization.lean` | `cutoffError_eq_cutoff_gauss_A_sub_annulus` — the **E normal form** `E = χ·(G_τ·A) − annulusTerms`, `A = residualCoeffA`; `residualCoeffA_measurable_of_factors` (F1 feed) | std-3 |
| J4-188 | `ErrorKernelJointMeas.lean` | `cutoffError_normalForm_measurable_from_geometry` — all factor carries from `{hg,hgi,hgpos}` (the F1 factor axis, assembled) | std-3 |
| J4-189 | `ParametrixGradientMeas.lean` | `cutoffError_normalForm_measurable_final` — the last derivative-field `hDH` **eliminated**; **F1 factor axis DONE from geometry**; W1/W2 flow `q`-regularity isolated as the residual wall | std-3 |
| J4-190 | `CompactJetBounds.lean` | `JetBoundPack` + `residualCoeffA_tau_weighted_bound`: `τ²·|residualCoeffA| ≤ C` (the τ²-cleared amplitude bound, compact-uniform) | std-3 |
| J4-191 | `GaussianGradAbsorption.lean` | the absorption family (`gaussDdim` radial/linear/quadratic power-×-Gaussian absorptions, `sqrtInv_pow`/`annulus_negPow`) | std-3 |
| J4-192 | `ChartThirdJet.lean` | `uniformFlowExp_contDiffAt_four` — **chart C⁴ DERIVED** (via `expMap↔uniformFlowExp` overlap bridge + `expMap_contDiffOn_four`); **no-conjugate-points DISSOLVED** (Neumann on uniform ball); `chartField_thirdJet_{of_contDiffAt,basePoint,reachable}` | std-3 |
| J4-193 | `ThirdJetBounds.lean` | `residualCoeffA_grad_tau_weighted_bound`; `parametrix_contDiffAt_three_field` (field-C³ parametrix); third-derivative continuity | std-3 |
| J4-194 | `GradEAssembly.lean` | `gradGA_bound`: `|∂ᵢ(G·A)| ≤ C·τ^{−5/2}·G_{2τ}`; **ALIGNMENT VERDICT** — the gap to the target `τ^{−1/2}·G_{2τ}` is the **gradient of the already-carried zeroth C4c `τ^{−2}` wall**, not an independent gap | std-3 |
| J4-195 | `OmegaHsrcC4cAudit.lean` | `a1_R6_of_residue_inf` (the `⊤`-`hsrc` carry **REMOVED**, `hsrc` now at `∞`); the **C4c honest correction**; `residualCoeffA_diag_singular_free` | std-3 |

### The definitive current residue — `a1_R6_of_residue_inf` (OmegaHsrcC4cAudit.lean:388), enumerated

The `∞`-capstone's **machine-checked hypothesis interface** (verbatim-summarised; `hHdiag`/`hDH` are now
supplied internally by `capstone_hHdiag_supplied`/`capstone_hDH_supplied`, so they are **off** the outer
surface). Grouped by honest status:

**(1) GAUGE / RNC — by-design normal-coordinate inputs** (the campaign's genuine geometric givens):
- `hg : ∀ a b, ContDiff ℝ ⊤ (g·· a b)`, `hg0 : g 0 = I`, `hgi : gi 0 = δ`, `hΓ : christoffel g gi (0)=0`,
  `hdg0 : ∂g(0)=0`, `htr : ∑ₐ ∂∂(g a a) = −(2/3)·Ric` (the RNC 2-jet identity), `hChr : ∀ a b c,
  ContDiff ℝ ⊤ (christoffel g gi a b c)`. — **satisfiable-by-design** (RNC).

**(2) Gate geometry — by-design chart data:**
- `hK : IsCompact K`, `hK0 : 0∈K`, `hS0 : 0∈S 0`, `ha : 0<a`, `hab : a<b`, `hHeq : H =
  vanVleckGatedWitness g gi hChr hK S a b` (defines the witness), `t,ht:0<t`, `C,hCnn:0≤C`. —
  **satisfiable-by-design.**

**(3) `hsrc : ContDiff ℝ ∞ (transportOp (vanVleck g) g gi (transportCoeff … 0))`** — **DISCHARGED from
geometry**: `InftyRebaseCapstone.hsrc_from_geometry` delivers exactly this `∞` form from `{hg,hgi,hgpos}`.
The `⊤` (analytic) typing is **gone** (Part A trace: `hsrc` reaches only `C¹/C⁰` atoms in
`radialTransportSolve_transport_eq_ofC1`).

**(4) `hEboundW_le : ∀ τ p q, 0<τ → τ≤t → |heatOp g gi H τ p q| ≤ C·baseKernelW 2 0 τ p q`** —
**DISCHARGEABLE from geometry**: `CoeffU1Fix.gatedWitnessN1_hEboundW_le_vanVleck_final` proves
`|heatOp…| ≤ (C·(1+t))·baseKernelW 2 0` from `{hg,hC,hgnd,hgsymm,hinvF,hframeK,hw,hdg0,hg0}` via Gaussian
**domination** into the width-2 kernel (the D1 `gaussDdim((3/2)τ)` estimate, `GateSqControl` supplied for
the flow-ball gate by `gateSqControl_of_flowBall`). Modulo the trivial `C ↦ C·(1+t)` constant reshape (`t`
fixed) this **is** the slot. **NOT** the Jacobi wall — this is domination, not cancellation-to-zero.

**(5) Levi / Duhamel interface carries** — `hInt` (`IterConvIntegrableW`), `hDuhamel`, `hInter` (Neumann
`∑'`), `hDConv` (`DifferentiableAt` of the convolution): **satisfiable interface-assembly** (laborious,
not research-grade).

**(6) `hCH : ContDiffAt ℝ 2 (fun p => H t p 0) 0`** — **DISCHARGED from geometry** by
`InftyRebaseCapstone.hCH_discharge_from_geometry` (from `{hg,hgi,hgpos}` + chart carries).

**(7) `hCConv : ContDiffAt ℝ 2 (fun p => heatConv H (leviSeries…) t p 0) 0`** — the Levi-convolution
field-`C²`. Its **L1 layer** (the `∃ w∈𝓝 0, HasFDerivAt` shape) is now delivered by the facade
(`CConvFacade.hCConv_discharged_from_data` / `FlowBallInstantiation.facade_flowBall`) from the five data
bundles. The **`C²`/L2 tail** — `hD1 : ContDiffAt ℝ 1 D 0` on the derivative representative — **remains
the reported gap** (facade docstring: "NOT the `C²` residue slot; the `hD1` tail remains the reported gap").

### The walls (final honest list)

- **(a) The off-diagonal van-Vleck cancellation — the Jacobi / exp-map radial ODE.** The identity
  `(r∂_r) log √(det g̃)(v) = −2·(Δ_flat r²/4 − d/2)` (`VanVleckCancellation` CHECKPOINT, verified) needs
  the exponential-map / Jacobi-field machinery **absent from every proof assistant** (the shared
  Riemannian-heat-kernel gap). **What it is NOT needed for:** the `τ`-free zeroth envelope `hEboundW_le`.
  Per J4-195's Part-B correction (and the `gatedWitnessN1_hEboundW_le_vanVleck_final` provider), that
  envelope is obtained by **Gaussian domination into a wider width-2 kernel, conditional on the
  `GateSqControl` near-isometry certificate — INDEPENDENT of the Jacobi cancellation**. The Jacobi ODE is
  needed only for the **genuine off-diagonal cancellation-to-zero** (the true `a₁ = R/6` value for `v≠0`,
  i.e. that `vanVleck` solves the leading transport ODE so `E` has no `O(1/τ)` head off-diagonal). It is
  **off the domination critical path**.
- **(b) W1/W2 flow `q`-regularity (F1).** Joint continuity (W1) and joint `C¹` (W2) of the gated kernel
  `H_G(τ,p,q)` in the base point `q`, which runs through the opaque `Classical.choose` geodesic flow
  `uniformFlowExp`. `ParametrixGradientMeas` closes the **factor axis** but explicitly **cannot** supply
  the `q`-continuity of the flow-dependent kernel — a distinct ODE-smooth-dependence (parameterised
  Picard / closed integral-solution + Lusin–Souslin) endeavour. **Genuine wall.**
- **(c) L2 `hD1` + the `hCConv` `C²` gap.** The `ContDiffAt ℝ 1 D 0` upgrade of the Levi-convolution
  derivative representative (the `C²` field slot). The L1 `∃`-`HasFDerivAt` shape is done via the facade;
  the `C¹`-of-the-derivative tail is the residue. **Satisfiable, non-trivial plumbing.**
- **(d) The gate-uniform third-jet constant (`expRho`).** Chart `C⁴` and third-jet **existence** land
  (J4-192), but the `z`-slot guard `‖v‖ < expRho g gi hC z` is a **per-base-point** `.choose`-fixed
  radius; a single K-uniform radius over `expRho` is **not** extracted (near-id/chart/flow radii ARE
  K-uniform). The third-jet **value** and its `τ^{−1/2}` Gaussian-moment modulus (`gaussComp_pd_pd_pd` +
  third moments) are later bricks. **Mechanical, deferred.**
- **(e) The annulus-gradient composition.** The full `∇(∂_τH − Δ_pH)` assembly aligning `gradGA_bound`'s
  honest `τ^{−5/2}·G_{2τ}` to the `hEgrad` target `τ^{−1/2}·G_{2τ}`. Per J4-194's verdict this is the
  **gradient of the already-carried zeroth C4c `τ^{−2}` wall**, not an independent gap — it aligns
  verbatim once (a)'s zeroth bound gives a genuinely bounded amplitude. **Mechanical, multi-brick.**

### Tractability verdict + recommendation

The Sol endgame narrowed the residue sharply: `hsrc` closed at `∞` (⊤ carry gone), `hCH` closed from
geometry, the **F1 factor axis** closed from geometry, chart **C⁴** derived, no-conjugate-points
**dissolved**, `hEboundW_le` shown **dischargeable-from-geometry** (domination, not cancellation), and the
C4c off-diagonal premise **honestly corrected** (genuine curvature). What remains splits cleanly:

- **Grind (mechanical / interface):** (c) the `hCConv` L2 `hD1`; (d) the K-uniform `expRho` radius +
  third-jet value/modulus; (e) the annulus-gradient `τ`-power alignment; and the `hInt/hDuhamel/hInter/
  hDConv` Levi carries. None is research-grade.
- **Sol consult (research-grade Mathlib-scale walls):** (a) the Jacobi/exp radial-ODE off-diagonal
  cancellation, and (b) the W1/W2 flow `q`-regularity of the `Classical.choose` `uniformFlowExp`. Both are
  the shared proof-assistant Riemannian-heat-kernel / ODE-smooth-dependence gaps; each is a multi-week
  endeavour, not the next increment.

**Discrepancy FLAGGED.** `GradEAssembly`'s header calls the zeroth `τ`-free envelope "CARRIED, not derived"
(citing the `1/τ²` Laurent head of the raw `residualCoeffA`), whereas J4-195 and the
`gatedWitnessN1_hEboundW_le_vanVleck_final` provider show `hEboundW_le` **is** proved from geometry via
width-2 domination. Reconciliation: "carried" there refers to the abstract `RestrictedEboundW` **hypothesis
slot** (and to cancellation-to-zero of the amplitude, which is genuinely not done), **not** to the absence
of a provider for the domination bound. The bound-on-`E` slot is therefore classed here as
**dischargeable-from-geometry**, and the Jacobi cancellation is correctly re-tiered as needed only for the
true off-diagonal **value**, off the domination path. Minor: the provider gives `(C·(1+t))·baseKernelW`
vs. the capstone's `C·baseKernelW` — a trivial `t`-fixed constant reshape.

**⚠ `a₁ = R/6` remains CONDITIONAL** — a machine-checked, compact-uniform conditional theorem
(`a1_R6_of_residue_inf`) whose residue is real, enumerated, and correctly tiered. This addendum removed the
`⊤`-`hsrc` carry, discharged the F1 factor axis and `hCH` from geometry, derived chart `C⁴`, and hardened
the `hCConv` L1 facade; the two genuine research walls (Jacobi off-diagonal cancellation, W1/W2 flow
regularity) are unchanged.
