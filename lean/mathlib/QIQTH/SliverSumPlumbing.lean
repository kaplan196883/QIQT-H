/-
  SliverSumPlumbing — J4-140: the EASY RESIDUE DISCHARGES of the freshly-banked conditional
  `hDuhamel_assembled` (J4-139, `LapTruncAssembly`).  Threads the four proven suppliers into their
  slots and instantiates the sliver bound, producing ONE theorem — `hDuhamel_semifinal` — whose
  hypothesis list is the COMPLETE honest residue of the Duhamel-principle output, enumerated in one
  place.  One brick of the `a₁ = R/6` campaign; NOT `a₁ = R/6`, and proves NOTHING about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (all landed, ns `QIQTH.HeatResidualBound`).
    • `LapTruncAssembly.hDuhamel_assembled` — the conditional capstone with the four soft limit slots
      `hEcomb`/`hEtrunc`/`hBoundaryLim`/`hDerivConv` and the sliver slots `B`/`hSliver`/`hBlim` still
      OPEN, on top of the geometric residue `hgi`/`hΓ`/`hInterchange`/`hLapFull`/`hII_lo`/`hII_hi`.
    • `LapTruncAssembly.sliverBound_tendsto_zero` — the `√ε` rate `K₁·2√ε_m + K₂·ε_m → 0`.
    • `TruncatedDuhamel.hE_combination` — supplies `hEcomb` (`DaTrunc = LapTrunc + Etrunc`) from the
      `Da`/`Lap` integral forms and the four E-combination integrabilities.
    • `DuhamelLimitWiring.etrunc_tendsto` — supplies `hEtrunc` (`Etrunc → E*F`) from the residual
      D1-domination family + measurability.
    • `DuhamelLimitWiring.boundaryTrunc_tendsto` — supplies `hBoundaryLim` (`BoundaryTrunc → F u 0 0`)
      from the near-diagonal parametrix / domination / measurability interface.
    • `DuhamelLimitWiring.derivConv_tendsto` — supplies `hDerivConv`
      (`DaTrunc + BoundaryTrunc → deriv (heatConv H F · 0 0) u`) from the truncated `HasDerivAt` family,
      the loc-unif derivative limit, and the pointwise tail convergence.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS.
    (P1)  `sliver_sum_bound` — the SLIVER SUM PLUMBING: from the per-coordinate `√ε` sliver bounds
          `|slivInt i m| ≤ D0 i · 2√ε_m + D1 i · ε_m` (the per-`i` deliverable of
          `NormalFormDischarge.witness_sliver2_concrete`, `pdpdH i := witnessSecondXDeriv … i`), the
          sum over `i : Fin n` obeys `‖∑ i, slivInt i m‖ ≤ B(ε_m)` with `B e := ∑ i (D0 i·2√e + D1 i·e)`
          and `B(ε_m) → 0`.  Route: `norm_sum_le` + `Finset.sum_le_sum` for the bound; `tendsto_finset_sum`
          over the per-`i` `sliverBound_tendsto_zero` for the limit.  Packaged as `∃ B, hSliver ∧ hBlim`
          — exactly the two sliver slots of `hDuhamel_assembled`.
    ★★★  `hDuhamel_semifinal` — THE ONE-THEOREM MILESTONE: `hDuhamel_assembled` with the four soft slots
          FILLED (`hE_combination → hEcomb`, `etrunc_tendsto → hEtrunc`, `boundaryTrunc_tendsto →
          hBoundaryLim`, `derivConv_tendsto → hDerivConv`) and the sliver slots FILLED (P1).  The
          Duhamel-principle output
              `heatOp g gi (heatConv H F · · ·) u 0 0 = F u 0 0 + heatConv (heatOp g gi H) F u 0 0`
          conditional ONLY on the COMPLETE labelled residue below.  Pure interface threading.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FIREWALL — the COMPLETE residue of `hDuhamel_semifinal` (each a genuine fact, NONE the
  conclusion, none vacuous), GROUPED.

    GAUGE            `hgi` (`g⁻¹(0)=δ`), `hΓ` (`Γ(0)=0`) — the RNC normal-coordinate normalization at
                     the center `0`, satisfiable by an RNC chart at any point.
    INTERCHANGE      `hInterchange` (finite-gap `∂ᵢ∂ᵢ heatConvFrozen = ∫∫ pdpdH·F`), `hLapFull`
                     (untruncated `Δ_g heatConv = ∑ᵢ ∫∫ pdpdH·F`), `hDa` (τ₀-slot Leibniz
                     `DaTrunc = ∫∫ ∂_r H·F`), `hLap` (second-order `LapTrunc = ∫∫ Δ_g H·F`) — the
                     differentiation-under-∫ carries; the riskiest analytic bricks, none the conclusion.
    INTEGRABILITY    `hII_lo`/`hII_hi` (adjacency-split interval integrability of `pdpdH·F`),
                     `hLapZ`/`hEZ` (`z`-integrability of `Δ_g H·F` / `E·F`), `hLapS`/`hES` (`s`-interval
                     integrability of the same), `hmeas` (residual `s`-measurability).
    GEOMETRIC-MODULI `D0`/`D1` with `hD0`/`hD1` (the per-coordinate `√ε` sliver amplitudes = the
                     near-isometry moduli output of `witness_sliver2_concrete`) and `hbnd` (the per-`i`
                     bound), `r₀`/`τ₀` radii, `hAnear` (near-diagonal parametrix form of `H`),
                     `hu₀cont`/`hu₀one`/`hu₀bdd`/`hu₁bdd` (leading-transport normalization/bounds).
    AMPLITUDE        `A₀`/`A₁` (near-diagonal domination constants of `H`), `E₀`/`E₁` (D1-domination
                     constants of the residual `heatOp g gi H`), `C₀`/`C₁` (transport bounds),
                     `C_L` (width-2 domination constant of `F`), with the nonnegativities.
    DOMINATION       `hAdom` (`|H| ≤ …` near-diagonal), `hEdom` (`|heatOp g gi H| ≤ …`), `hEzero`
                     (residual vanishes at `τ ≤ 0`), `hBdom` (`|F| ≤ C_L·G_{2s}`).
    F2-REGULARITY    `hderiv` (the truncated diagonal `HasDerivAt` family), `D`/`hDerivLU` (the
                     loc-unif derivative limit `DaTrunc + BoundaryTrunc → D`), `hfg` (pointwise tail
                     convergence of the truncated maps to `heatConv H F · 0 0`).
    MEASURABILITY    `hBcont` (space-time continuity of `F`), `hAmeas`/`hBmeas` (`z`-measurability of
                     `H`/`F`), `hu₀meas`/`hu₁meas` (transport measurability).

    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6` — this
    is ONE brick (the easy residue discharges) of the `a₁ = R/6` campaign.
-/
import Mathlib
import QIQTH.LapTruncAssembly
import QIQTH.TruncatedDuhamel

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open scoped Interval Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### P1 — the sliver sum plumbing `hSliver`/`hBlim`.
    ############################################################################### -/

/-- **★★ P1 — `sliver_sum_bound`.**  From the per-coordinate `√ε` sliver bounds
      `|slivInt i m| ≤ D0 i · (2√ε_m) + D1 i · ε_m`   (`D0 i, D1 i ≥ 0`),
    the sum over `i : Fin n` obeys the sliver slot of `hDuhamel_assembled`:
      `‖∑ i, slivInt i m‖ ≤ B(ε_m)`   with `B e := ∑ i (D0 i·2√e + D1 i·e)`,   and   `B(ε_m) → 0`.
    Route: `norm_sum_le` + `Real.norm_eq_abs` + `Finset.sum_le_sum` (per-`i` bound) for `hSliver`;
    `tendsto_finset_sum` over the per-`i` `sliverBound_tendsto_zero` (`√ε` rate) for `hBlim`.  The
    per-coordinate bound is the deliverable of `NormalFormDischarge.witness_sliver2_concrete` at
    `pdpdH i := witnessSecondXDeriv … i` (its `(C₀ᵢ+C₁ᵢ)·2√ε + C₂ᵢ·ε` shape).  Packaged as
    `∃ B, hSliver ∧ hBlim` — the two sliver slots in one.  NOT `a₁ = R/6`. -/
theorem sliver_sum_bound (slivInt : Fin n → ℕ → ℝ) (D0 D1 : Fin n → ℝ)
    (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ),
        |slivInt i m| ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :
    ∃ B : ℝ → ℝ,
      (∀ m, ‖∑ i, slivInt i m‖ ≤ B (epsSeq m))
      ∧ Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0) := by
  refine ⟨fun e => ∑ i, (D0 i * (2 * Real.sqrt e) + D1 i * e), ?_, ?_⟩
  · intro m
    calc ‖∑ i, slivInt i m‖
        ≤ ∑ i, ‖slivInt i m‖ := norm_sum_le _ _
      _ = ∑ i, |slivInt i m| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑ i, (D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :=
          Finset.sum_le_sum (fun i _ => hbnd i m)
  · have hsum : Tendsto
        (fun m => ∑ i, (D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)) atTop
        (𝓝 (∑ _i : Fin n, (0 : ℝ))) := by
      refine tendsto_finsetSum _ (fun i _ => ?_)
      exact sliverBound_tendsto_zero (D0 i) (D1 i)
    simpa using hsum

/-! ###############################################################################
    ### ★★★ P2 — the ONE-THEOREM milestone `hDuhamel_semifinal`.
    ############################################################################### -/

/-- **★★★★ P2 — `hDuhamel_semifinal`.**  `LapTruncAssembly.hDuhamel_assembled` with the four soft
    limit slots and the two sliver slots DISCHARGED by their proven suppliers:
      • `hE_combination` (per `m`, from `hDa`/`hLap`/`hLapZ`/`hEZ`/`hLapS`/`hES`) ⟹ `hEcomb`;
      • `etrunc_tendsto` (residual D1-domination + measurability) ⟹ `hEtrunc`;
      • `boundaryTrunc_tendsto` (near-diagonal parametrix interface) ⟹ `hBoundaryLim`;
      • `derivConv_tendsto` (truncated `HasDerivAt` family + loc-unif deriv limit + tail) ⟹ `hDerivConv`;
      • `sliver_sum_bound` (P1, per-coordinate `√ε` bounds `hbnd`) ⟹ `B`/`hSliver`/`hBlim`.
    The Duhamel-principle output
        `heatOp g gi (heatConv H F · · ·) u 0 0 = F u 0 0 + heatConv (heatOp g gi H) F u 0 0`
    conditional ONLY on the complete labelled residue (see the header's grouped firewall).  Pure
    interface threading — the value is the SINGLE honest residue enumeration.  NOT `a₁ = R/6`. -/
theorem hDuhamel_semifinal (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : u ∈ U)
    (hUpos : ∀ w ∈ U, 0 < w) (hUT : ∀ w ∈ U, w ≤ T)
    -- GAUGE
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    -- INTERCHANGE
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : ∀ (m : ℕ) (i : Fin n),
        pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hLapFull : laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hDa : ∀ m, DaTrunc H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
    (hLap : ∀ m, LapTrunc g gi H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
    -- INTEGRABILITY
    (hII_lo : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m))
    (hII_hi : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume (u - epsSeq m) u)
    (hLapZ : ∀ s, Integrable
        (fun z => laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0) volume)
    (hEZ : ∀ s, Integrable (fun z => heatOp g gi H (u - s) 0 z * F s z 0) volume)
    (hLapS : ∀ m, IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ m, IntervalIntegrable
        (fun s => ∫ z, heatOp g gi H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m))
    (hmeas : AEStronglyMeasurable
        (fun s => ∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    -- GEOMETRIC-MODULI (sliver amplitudes + near-diagonal parametrix)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ),
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        H τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    -- AMPLITUDE
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (E₀ E₁ : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    -- DOMINATION
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q| ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    -- F2-REGULARITY (derivative-of-the-limit family)
    (hderiv : ∀ᶠ m in atTop, ∀ w ∈ U,
        HasDerivAt (fun v => heatConvFrozen H F v (v - epsSeq m) 0 0)
          (DaTrunc H F m w + BoundaryTrunc H F m w) w)
    (D : ℝ → ℝ)
    (hDerivLU : TendstoLocallyUniformlyOn
        (fun m w => DaTrunc H F m w + BoundaryTrunc H F m w) D atTop U)
    (hfg : ∀ w ∈ U, Tendsto (fun m => heatConvFrozen H F w (w - epsSeq m) 0 0) atTop
        (𝓝 (heatConv H F w 0 0)))
    -- MEASURABILITY
    (hBcont : ContinuousOn (fun x : ℝ × Point n => F x.1 x.2 0) (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => H τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume) :
    heatOp g gi (fun v p q => heatConv H F v p q) u 0 0
      = F u 0 0 + heatConv (heatOp g gi H) F u 0 0 := by
  -- sliver slots (P1)
  obtain ⟨B, hSliver, hBlim⟩ := sliver_sum_bound
    (fun i m => ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    D0 D1 hD0 hD1 hbnd
  -- E-combination ⟹ hEcomb
  have hEcomb : ∀ m, DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u := fun m =>
    hE_combination g gi H F m u (hDa m) (hLap m) hLapZ hEZ (hLapS m) (hES m)
  -- residual limit ⟹ hEtrunc
  have hEtrunc : Tendsto (fun m => Etrunc g gi H F m u) atTop
      (𝓝 (heatConv (heatOp g gi H) F u 0 0)) :=
    etrunc_tendsto g gi H F u T (hUpos u htU) (hUT u htU) E₀ E₁ C_L hE₀ hE₁ hC_L
      hEdom hEzero hBdom hmeas
  -- boundary limit ⟹ hBoundaryLim
  have hBoundaryLim : Tendsto (fun m => BoundaryTrunc H F m u) atTop (𝓝 (F u 0 0)) :=
    boundaryTrunc_tendsto H F T hT U hUopen hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one
      C₀ C₁ hu₀bdd hu₁bdd A₀ A₁ hA₀ hA₁ hAdom C_L hC_L hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
      u htU
  -- derivative-of-the-limit ⟹ hDerivConv
  have hDerivConv := derivConv_tendsto H F u U hUopen htU hderiv D hDerivLU hfg
  -- thread all slots into the assembled capstone
  exact hDuhamel_assembled g gi H F u hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi
    B hSliver hBlim hEcomb hEtrunc hBoundaryLim hDerivConv

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.sliver_sum_bound
#print axioms QIQTH.HeatResidualBound.hDuhamel_semifinal
