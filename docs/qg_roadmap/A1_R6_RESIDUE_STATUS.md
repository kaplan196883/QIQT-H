# A₁ = R/6 — THE FINAL-STATE CENSUS (2026-08-03)

**Provenance.** The complete, honest documentation of the `a₁ = R/6` conditional chain after the
37-brick session J4-116…J4-152 (`ConvApproximants` → `EngineInstantiation`), the direct continuation
of the jet-4 tower. Authoritative source = the `AxiomAudit.lean` `★` pin blocks (lines ~15707–16336)
and the theorem statements in `CapstoneStatus.lean` / `SpatialC2.lean` / `ResidueThreading.lean` /
`ConcreteDominations.lean`. This is a status document; it changes no result's labels.

**Meta (verified against the pins and `git log`).**
- All bricks `[AF]` std-3: raw axiom count **0** (`propext`, `Classical.choice`, `Quot.sound` only);
  no `sorry`; no `expRho`; no vacuous `:= True` hypotheses.
- Every J4-116…J4-152 brick was **independently build-verified** at landing.
- Pushed through commit **`61263553`** (`J4-152: the engine instantiation`); HEAD `3901b487` is the
  J4-152 docs bank.
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
| `hCConv` | `hCConv_reduction` (SpatialC2, J4-147) | **REDUCED** to `(D, hConvDeriv, hConvD1)` = the first spatial derivative under `∫∫` (dominated) + `C¹` of that derivative map (the Laplacian-sliver content). |
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
both UNCONDITIONAL given `0∈K`); the general-base second field jet `J1b`/`D²V₀(0)=0` is a labelled
`C²` carry, not a wall.

**DISCHARGED (slot gone from the endpoint / supplied by a proven lemma):**
`hCH` (J4-147) · `hInter` (J4-151, via `heatConv_leviSeries_interchange`) ·
`hWmeas₀` (J4-150 `hWmeas₀_unconditional` — `z↦W z 0` Lipschitz) ·
`hRI` (J4-151 `chartW0_rightInverse`) · `hLHSlim` (J4-151, ⟸ U2 loc-unif) ·
`hVol` (J4-151, ⟸ `leviSeries_volterra` + proven interchange) ·
`hInterchange` (J4-141 `pd_pd_heatConvFrozen_interchange`) · `hLapFull` (J4-142 `hLapFull_of_lims`) ·
`hDa`/`hLap` (J4-142 `hDa_threaded`/`hLap_threaded`) · `hDaLimLU` (J4-148 `hDaLimLU_discharge`) ·
`hDerivLU` (J4-148) · `hqLip`/`hFLocLip` (J4-144, resolvent route) · `hFII` (J4-117/145) ·
`hpar`/`htime`/`hR` (J4-145, F2 group) · `hLap`/`hLapFull` interchange group (J4-141/142).

**REDUCED-with-carries (proven supplier hands off to satisfiable sub-carries):**
- `hCConv` → `hConvDeriv` (dominated first spatial derivative under `∫∫`) + `hConvD1` (`C¹` of that
  derivative map = the singular second-derivative Laplacian-sliver content). J4-147.
- `hDConv` → `hDaLim` (delta-family; `hTail`/`hBoundary` proven, J4-118/119/120).
- `hDuhamel` → `hDaLimLU` (discharged J4-148; core `witness_sliver2_grand` proven J4-137) + the F2
  family `{hCross, hMeasFII, hInnerCont}` + boundary-interface + domination families.
- `hInt` → kernel continuity `{Continuous H_G, Continuous ∂ⱼH_G, gi/Γ meas}` (J4-110).

**CARRIED analytic families (satisfiable by the concrete `N=1` witness; laborious, not research-grade):**
- Levi domination `hEbound/hEzero/hEmeas` for `E := heatOp g gi H` (traded in for `hInter`); `hEmeas`
  = the full joint measurability (§5·F1).
- The **amplitude family** — `PdiffAt`/`witnessFieldDeriv`/`witnessFieldDeriv2` (J4-152), amplitude
  bounds `{M₀,M₁,M₂}`/`{A₀,A₁,E₀,E₁,C₀,C₁,C_L}`, amplitude Lipschitz/sup/measurability.
- The **engine measurability/continuity families** — `hMeasFII`, `hInnerCont`, `hUfloor`, the C3ε
  engine interface, `hCross`, the dominated-engine z/s domination + measurability families
  (J4-141/145/152), `hBcont`, `hAmeas`/`hBmeas`, `hu₀meas`/`hu₁meas`.
- The **m-uniform sliver constant** `C_R` (eventual ε-free bound, J4-152 `hbnd_witness_supplied`);
  `hGateSub` (gate `⊆ K ∩ ball` side condition, J4-143); `hE1`/`hSlice`/`hEgrad` (resolvent-route
  interface, J4-144); `hCConv` layers `D`/`hConvDeriv`/`hConvD1`.

The endpoint theorem `a1_R6_of_residue_hCH_hInter_discharged` bundles exactly these; the residue is
enumerated in the S1 supply table (`CapstoneStatus.lean` header) and the J4-146/150/151/152 pins.

---

## 4. WALLS FELLED THIS SESSION (J4-116…J4-152, one line each)

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
The amplitude family (`PdiffAt`, bounds `M₀/M₁/M₂` and `A/E/C` constants, amplitude Lipschitz/sup/
measurability), the engine measurability/continuity families (`hMeasFII`, `hInnerCont`, `hUfloor`,
C3ε interface, `hCross`, dominated-engine z/s families, `hBcont`, amplitude/`u₀`/`u₁` measurability),
the `hCConv` layers (`hConvDeriv`/`hConvD1`), and the general-base chart second jet (`J1b`/`D²V₀(0)=0`).
Each is satisfiable by the concrete `N=1` witness (many are verified at `z=0` and reduce to the
completed toolset — moments M5–M10, `gaussDdim_replace_bound`, the T1' Hermite bridges); none is a
research wall. **Route:** mechanical plumbing/instantiation from the concrete witness, substantial in
volume.

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
positivity floor on the gate radius), and **F3** (a large but tractable interface-assembly tail).
Not `a₁ = R/6` yet; the residue is real, enumerated, and correctly tiered.
