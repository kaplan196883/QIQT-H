/-
  EnvelopeCoreDischarge — J4-242: THE `core` UNBUNDLE FOR THE `a1_R6_assembled_v2'` SURFACE.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is a pure
  RE-PLUMBING / COMPOSITION brick.  It transports the J4-224 `AssemblyLadderR3` `core`-unbundle trick
  onto the `RightInverseGeneral.a1_R6_assembled_v2'` surface.

  `a1_R6_assembled_v2'` still carries the OPAQUE bundle binder
      `core : TruncatedDuhamelCore g gi Wit t`     (`Wit := vanVleckGatedWitness g gi hChr hK S a b`)
  because its line descends from `a1_R6_assembled_v2` (PRE-R3).  R3 replaced that binder — but R3 was
  built on `a1_R6_assembled_v2` (which carries the RAW-chart measurable-supplier block), NOT on the
  `htriple`-entry `v2'`.  This file supplies the SAME reduction, keyed abstractly in `Wit` (never
  materializing the ~130-binder capstone nor the concrete `vanVleckGatedWitness`, to avoid
  kernel-freeze), so it applies verbatim at the `v2'` surface.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## WHAT LANDS — `core_of_v2prime_data`.

  From the data ALREADY carried by `a1_R6_assembled_v2'` — the `hDaLimLU_from_data` pile (gauge
  `hgi`/`hΓ`; the interchange trio `hInterchange`/`hLapFull`/`hEcomb`; the strip integrabilities
  `hIlo`/`hIhi`; the adjacency integrabilities `hII_lo`/`hII_hi`; the `√ε` sliver amplitudes
  `D0`/`D1`/`hbnd`; the two Gaussian dominations `hEdom`/`hEzeroE` (residual) and `hBdom`/`hFzero`
  (source); the time window `hUfloor`/`hUT`), together with the boundary pile
  (`r₀`/`τ₀`/`hAnear`/`hu₀cont`/`hu₀one`/`hu₀bdd`/`hu₁bdd`/`hAdom`/`hBcont`/`hAmeas`/`hBmeas`/
  `hu₀meas`/`hu₁meas`) — PLUS the single carried pointwise limit `hDerivConv` — the file builds the
  `TruncatedDuhamelCore` bundle INTERNALLY, discharging TWO of its three limits FREE:

    · `hDaLim`       ← `ETailRateBound.hDaLimLU_from_data` (WALL → DATA loc-unif) composed with
                       `GrandAssemblyRecon.daLimLU_reduces_to_pointwise` (`.tendsto_at htU`);
    · `hBoundaryLim` ← `DuhamelLimitWiring`'s `HeatResidualBound.boundaryTrunc_tendsto`;
    · `hDerivConv`   ← the SINGLE carried pointwise-limit binder (SIZE-REJECTED at R3: threading via
                       `derivConv_tendsto` needs the F2 partials + `hFII`, ≥4 non-carried families).

  The composition is EXACTLY `AssemblyLadderR3.a1_R6_assembled_v3`'s internal `core` build (lines
  340–363 there), lifted out as a standalone bundle-level lemma over an abstract kernel `Wit` and the
  concrete source `F := leviSeries (heatOp g gi Wit)`.  Feeding this back into `a1_R6_assembled_v2'`'s
  `core` slot removes the last opaque `: Prop` data bundle from the `v2'` surface, leaving it bottomed
  out in the geometry + `htriple` supplier + the DATA piles + the SINGLE transparent `hDerivConv`
  limit.  Pure composition — NO new analysis.  NOT `a₁ = R/6`.

  NO `sorry`.  NO new axioms.  NO `:= True`.  NO vacuous hypotheses.
-/
import Mathlib
import QIQTH.GrandAssemblyRecon
import QIQTH.DuhamelLimitWiring
import QIQTH.TruncatedDuhamelData

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.ETailRateBound
open scoped Interval Topology BigOperators

namespace QIQTH.EnvelopeCoreDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `core_of_v2prime_data` — the `TruncatedDuhamelCore` bundle from `v2'`'s data.
    ############################################################################### -/

/-- **★★★ J4-242 — `core_of_v2prime_data`.**  The `TruncatedDuhamelCore g gi Wit t` bundle — the
    opaque `core` binder of `RightInverseGeneral.a1_R6_assembled_v2'` — built INTERNALLY from the
    data that capstone already carries plus the single carried pointwise limit `hDerivConv`.

    Two of the three truncation limits are discharged FREE:
      · `hDaLim`       via `ETailRateBound.hDaLimLU_from_data` ∘
                          `GrandAssemblyRecon.daLimLU_reduces_to_pointwise`;
      · `hBoundaryLim` via `HeatResidualBound.boundaryTrunc_tendsto`;
      · `hDerivConv`   carried (the sole size-rejected residue).

    Abstract in `Wit`; `F := leviSeries (heatOp g gi Wit)`.  Genuine composition, verbatim the R3
    internal build.  NOT `a₁ = R/6`. -/
theorem core_of_v2prime_data (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    -- gauge (RNC normalization at the centre) — defeq to `MemGaugeGi`/`MemGaugeGamma`.
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    -- the `hDaLimLU_from_data` interchange trio + integrabilities + sliver amplitudes + dominations.
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : MemInterchange Wit (leviSeries (heatOp g gi Wit)) U pdpdH)
    (hLapFull : MemLapFull g gi Wit (leviSeries (heatOp g gi Wit)) U pdpdH)
    (hII_lo : MemAdjLo (leviSeries (heatOp g gi Wit)) U pdpdH)
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi Wit)) U pdpdH)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1nn : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z
            * leviSeries (heatOp g gi Wit) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L)
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi Wit τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzeroE : ∀ τ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi Wit τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi Wit) s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, leviSeries (heatOp g gi Wit) s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi Wit (u - s) 0 z * leviSeries (heatOp g gi Wit) s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi Wit (u - s) 0 z * leviSeries (heatOp g gi Wit) s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi Wit (leviSeries (heatOp g gi Wit)))
    -- the boundary pile (near-diagonal parametrix interface for `hBoundaryLim`).
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        Wit τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |Wit τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hBcont : ContinuousOn
        (fun x : ℝ × Point n => leviSeries (heatOp g gi Wit) x.1 x.2 0)
        (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => Wit τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable
        (fun z : Point n => leviSeries (heatOp g gi Wit) s z 0) volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    -- the SINGLE carried pointwise-limit residue (size-rejected at R3).
    (hDerivConv : Filter.Tendsto
        (fun m => DaTrunc Wit (leviSeries (heatOp g gi Wit)) m t
          + BoundaryTrunc Wit (leviSeries (heatOp g gi Wit)) m t) Filter.atTop
        (𝓝 (deriv (fun u => heatConv Wit (leviSeries (heatOp g gi Wit)) u 0 0) t))) :
    TruncatedDuhamelCore g gi Wit t := by
  -- extract the uniform time floor `aT` from `hUfloor`.
  obtain ⟨aT, haT, hUlb⟩ := id hUfloor
  -- `hDaLim` (FREE): the WALL → DATA loc-unif, reduced pointwise-at-`t`.
  have hDaLimLU := QIQTH.ETailRateBound.hDaLimLU_from_data g gi
    Wit (leviSeries (heatOp g gi Wit))
    T U hUopen hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi
    D0 D1 hD0 hD1nn hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hUT
    hEdom hEzeroE hBdom hFzero hIlo hIhi hEcomb
  have hDaLim := QIQTH.GrandAssemblyRecon.daLimLU_reduces_to_pointwise g gi
    Wit (leviSeries (heatOp g gi Wit)) U t htU hDaLimLU
  -- `hBoundaryLim` (FREE): W1 pointwise-at-`t` boundary discharge.
  have hBoundaryLim := QIQTH.HeatResidualBound.boundaryTrunc_tendsto
    Wit (leviSeries (heatOp g gi Wit))
    T hT U hUopen hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ hA₀ hA₁ hAdom C_L hC_L hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas t htU
  -- build the `core` bundle from its 3-limit residue.
  exact truncatedDuhamelCore_of_daLim g gi Wit t hBoundaryLim hDaLim hDerivConv

end QIQTH.EnvelopeCoreDischarge

section AxiomChecks
open QIQTH.EnvelopeCoreDischarge
#print axioms core_of_v2prime_data
end AxiomChecks
