# C4C_SCOPING — the actual state of the C4c "off-diagonal parametrix" wall

Date: 2026-08-16. Author: audit cycle following JET4_TOWER_PLAN J4-756.

## Executive finding (binding, verified)

**C4c is NOT an open community-scale wall. Its load-bearing primitive — the global
width-2 off-diagonal parametrix residual bound `hEboundW` — is ALREADY CLOSED,
std-3, fully unconditional, for the concrete gated witness.**

The terminal theorem is

```
QIQTH.HeatResidualBound.gatedWitness_hEboundW_unconditional   (QIQTH/UniformChartRadius.lean, J4-100)
```

with conclusion (exactly the shape the reduced a₁ capstone consumes):

```
∃ a b B, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∃ S : Point n → Set (Point n),
  ∀ τ p q, 0 < τ →
    |heatOp g gi (gatedKernel K S (globalCutoffParametrixWitness Θ u a b
        (uniformInverseChart g gi hC hK))) τ p q|
      ≤ B * baseKernelW 2 0 τ p q
```

Hypotheses are ONLY the genuine geometric/heat data
(`hg, hC, hK : IsCompact K, hgnd, hgsymm, hinvF, hframeK, Θ, u, hw0smooth, hw0flat`) —
no `hEboundW`-shaped carry, no `expRho`, no injectivity-radius axiom.

`#print axioms gatedWitness_hEboundW_unconditional` = `[propext, Classical.choice, Quot.sound]`
(std-3, verified this cycle). Already pinned in `QIQTH/AxiomAudit.lean` (line ~15475);
axiom budget raw 0.

## Why the "wall" framing was stale

`QIQTH/C4cDecomposition.lean` and `QIQTH/ParametrixHEboundWiring.lean` headers, and
`JET4_TOWER_PLAN.md` entries J4-750/751/756, all describe C4c as needing
"Riemannian distance, injectivity radius, smooth cutoffs, and the `Δ_g(χH)` product
rule — NONE in Mathlib — a sustained, community-scale build," split into a far-field
cutoff (1) and an off-diagonal/all-base-points (2) piece. **Every one of those pieces
was built by the separate `hunif` tower (J4-84 → J4-100), which those headers predate
and never cross-referenced** — the recurring "don't under-credit the repo" pattern.

How each named obstruction was actually discharged:

- **Smooth cutoffs / `Δ_g(χH)` product rule.** `radialCutoff a b` +
  `laplaceBeltrami_radialCutoff_bound_on_annulus_of_continuousOn` and the
  `cutoffResidual_*` engine chain (`CutoffResidualFiniteReg`, `RecenterCutoffC3`).
- **Injectivity radius / no-conjugate-points (the flagged "STILL-MISSING" `g̃`
  nondegeneracy off the diagonal).** SIDESTEPPED, never proved globally. Because `a₁`
  is a LOCAL diagonal invariant, the parametrix cutoff is supported in a small ball
  `B(0,ρ₀)` where `g̃` nondegeneracy holds by OPENNESS OF UNITS
  (`expPullbackMetric_isUnit_near_zero`, J4-9 = invertibility at 0 + continuity +
  `Units.isOpen`; NO fderiv/IFT/no-conjugate-points theorem). The within-ρ₀ continuity
  producers (J4-11, `AnnulusContinuityWithinRho`) then discharge `hgi_cont`/`hchris_cont`,
  and the radius-constraint refactor (J4-12, `RecenterCutoffLocal`) forces the cutoff
  radii `a < b < ρ₀`.
- **Off-diagonal / all base points `q`.** The arbitrary-base-point exponential map
  `uniformFlowExp g gi hC hK q` and inverse chart `uniformInverseChart` (built via
  Mathlib's quantitative IFT `ApproximatesLinearOn`, which — unlike
  `ContDiffAt.toOpenPartialHomeomorph` — EXPOSES the source ball, giving a K-UNIFORM
  radius `δ₀`, `uniformInverseChart_huniformChart`, J4-100). Uniformity in `q` over the
  compact `K` via `cutoffResidual_uniformFlow_uniform` (J4-85). For `q ∉ K` the gated
  kernel is zero and the bound holds trivially (`gaussDdim > 0`).

The reduction ladder, each rung strictly more isolated than the last:
`_uncond2` (J4-8) → `_uncond3` (J4-12) → `cutoffResidual_uniformFlow_uniform` (J4-85)
→ gated kernel / `gatedWitness_hEboundW` (J4-97/98, residue `hgood`)
→ `gatedWitness_hEboundW_final` (J4-99, residue `huniformChart`)
→ **`gatedWitness_hEboundW_unconditional` (J4-100, residue = ∅).**

## What actually remains (the real frontier — NOT C4c)

The reduced capstone `TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual`
consumes `hEboundW` as ONE of several carries for a FREE kernel `H`:

```
hInt · hInter · hDuhamel · hE · hCorrHigher · hHdiag · hEboundW
```

`gatedWitness_hEboundW_unconditional` is a drop-in for `hEboundW` with
`H := gatedKernel K S (globalCutoffParametrixWitness …)` and `E := heatOp g gi H`
(so `hE` is `rfl`). The genuinely-open work is to make the SAME witness `H` also
satisfy the other slots simultaneously:

- **`hHdiag`** — the gated witness's diagonal equals the van-Vleck parametrix diagonal
  `heatParametrixFn N …`. (Needs: the gate `S` contains a neighborhood of the diagonal
  and the recentring is identity there — plausibly reachable, but not yet threaded.)
- **`hDuhamel` / `hInter` / `hCorrHigher` / `hInt`** — the Levi/Duhamel Neumann-series
  identification of the true kernel as the limit of THIS parametrix, its integrability
  `IterConvIntegrableW` (needs joint measurability + `hEzero` of the gated witness), the
  tsum/heatConv interchange, and the ≥ t² correction-order fact.

**These are the "convergence-trio" / `slots` wall (JET4_TOWER_PLAN J4-750 item), a
SEPARATE frontier from C4c.** It is the classical-but-unformalized C^k smooth-dependence
/ Levi-parametrix-convergence theory, matching the independent deep-research verdict.

## Corrections to make (record hygiene, not code)

The following headers/entries assert or imply "C4c is the one open community-scale
wall" and should be annotated as SUPERSEDED by `gatedWitness_hEboundW_unconditional`:

- `QIQTH/C4cDecomposition.lean` header (§"NOT reachable as a loop-brick").
- `QIQTH/ParametrixHEboundWiring.lean` header (§"THE SINGLE REMAINING INPUT … the C4c wall").
- `JET4_TOWER_PLAN.md` J4-750 (wall #1 "C4c"), J4-751 (wall #4 "C4c CONFIRMED"),
  J4-756 ("Only C4c survives as a true community-scale wall").

Note: those headers describe C4c relative to the `C4cDecomposition`/`ParametrixHEboundWiring`
diagonal-chart abstract residual `E` (fixed base `q = 0`); the hunif tower closed the
GENUINE two-point/all-`q` version on a different, concrete witness object. The two are
the same mathematical primitive; the hunif tower is the one that actually landed it. The
honest single-sentence status is: **C4c (the off-diagonal parametrix width-2 residual
bound) is closed unconditionally; unconditional a₁ = R/6 is now gated solely on the
`slots` convergence-trio for the concrete gated witness.**

## No Lean banked this cycle (by design)

C4c has no remaining provable sub-piece — its primitive is already std-3 unconditional.
Manufacturing a new "C4c" theorem would be redundant/vacuous, so per the banking
protocol's non-gold-plating rule none was built. The valuable output is this correction.
