/-
  LapTruncAssembly — J4-139: THE LAPLACIAN–SLIVER CONNECTION.  Assembles the proven sliver
  machinery (the `√ε` witness-second-derivative bound) into the conditional `Da`-limit discharge
  `hDaLim`/`hDaLimLU` — the target of the entire `hDaLim` campaign — and threads it into the
  reduction capstone `hDuhamel_of_daLim` to obtain the Duhamel-principle output conditional on the
  fully-listed accumulated residue.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (all landed, ns `QIQTH.HeatResidualBound`).
    • `TruncatedDuhamel`   — `DaTrunc`/`Etrunc`/`LapTrunc`/`BoundaryTrunc` defs; `hE_combination`
      (`DaTrunc = LapTrunc + Etrunc`, its `hLap` carry = the second-order interchange); the reduction
      capstone `hDuhamel_of_daLim` (whose `hDaLim` carry is the SPECIFIC-VALUE limit
      `DaTrunc → Δ_g(H*F) + E*F` this file discharges).
    • `DuhamelLimitWiring` — `etrunc_tendsto` (`Etrunc → E*F`, PROVEN from the dominations).
    • `HeatParametrixError`/`LaplaceBeltrami` — `laplaceBeltrami_at_rnc_center` (the RNC flat reduction
      `Δ_g f 0 = ∑ᵢ ∂ᵢ∂ᵢ f 0` under the gauge `g⁻¹(0)=δ`, `Γ(0)=0`).
    • `NormalFormDischarge` — `witness_sliver2_concrete` (the terminal per-coordinate `√ε` sliver bound
      for the ACTUAL concrete van-Vleck witness second `x`-derivative).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (this file).
    (L1)  `lapTrunc_eq_sum_pdpd` / `lap_heatConv_eq_sum_pdpd` — the RNC flat reduction applied to the
          frozen (resp. genuine) convolution: `LapTrunc = ∑ᵢ ∂ᵢ∂ᵢ (heatConvFrozen …) 0`, and the same
          for `laplaceBeltrami g gi (heatConv H F u · 0) 0`.  Direct application of
          `laplaceBeltrami_at_rnc_center`.
    (rate) `sliverBound_tendsto_zero` — `K₁·(2√ε_m) + K₂·ε_m → 0` (the `√ε` sliver rate; the shape of
          `witness_sliver2_concrete`'s bound at `ε = ε_m`).
    (L3)  `lapTrunc_tendsto` — the SLIVER-DIFFERENCE LIMIT: with the finite-gap interchange
          `hInterchange` (L2, carried) at `b = u−ε_m` and the untruncated `hLapFull`, the truncated
          Laplacian differs from the target by exactly `∑ᵢ` the sliver `∫_{u−ε_m}^u ∫ pdpdH·F`
          (`integral_add_adjacent_intervals`); bounded by `B(ε_m) → 0` (`squeeze_zero_norm`) it
          converges: `LapTrunc … m u → laplaceBeltrami g gi (heatConv H F u · 0) 0`.
    (L4a) `hDaLim_discharge` — from `hEcomb` (`DaTrunc = LapTrunc + Etrunc`), L3 (`LapTrunc → Δ`), and
          `etrunc_tendsto`'s output (`Etrunc → E*F`), by `Tendsto.add` + `Tendsto.congr`, the SPECIFIC
          `Da`-limit `DaTrunc → Δ_g(H*F) + E*F`.
    (L4)  `hDaLim_full` — chains L3 into L4a (the full `Da`-limit from the sliver ingredients).
    ★★★  `hDuhamel_assembled` — THE CAPSTONE: threads `hDaLim_full` into `hDuhamel_of_daLim`, giving
          the Duhamel-principle output
          `heatOp g gi (heatConv H F · · ·) u 0 0 = F u 0 0 + heatConv (heatOp g gi H) F u 0 0`
          conditional on the FULL explicit residue below.

  ⚠ HONEST FIREWALL — the COMPLETE residue (each a genuine fact, NONE the conclusion, none vacuous).
    • `hgi`/`hΓ`       — the RNC gauge at the center `0` (`g⁻¹(0)=δ`, `Γ(0)=0`); the normal-coordinate
      normalization, satisfiable at any point by an RNC chart.
    • `hInterchange`   — (L2) the FINITE-GAP second-order differentiation under the double integral:
      `∂ᵢ∂ᵢ (heatConvFrozen H F u (u−ε_m) · 0) 0 = ∫₀^{u−ε_m} ∫ pdpdH i (u−s) z · F s z 0`.  The
      riskiest analytic brick, genuine (dominated second differentiation at the gap `u−s ≥ ε_m > 0`),
      carried; NOT the conclusion.
    • `hLapFull`       — the untruncated interchange
      `laplaceBeltrami g gi (heatConv H F u · 0) 0 = ∑ᵢ ∫₀^u ∫ pdpdH i (u−s) z · F s z 0` (the improper
      full-integral version); the same second-order interchange in the limit.
    • `hII_lo`/`hII_hi`— interval-integrability of the inner `pdpdH·F` pairing on `[0,u−ε_m]` and
      `[u−ε_m,u]` (the adjacency-splitting carries; Gaussian-domination facts).
    • `B`/`hSliver`/`hBlim` — the SLIVER BOUND `‖∑ᵢ ∫_{u−ε_m}^u ∫ pdpdH·F‖ ≤ B(ε_m)` and `B(ε_m)→0`.
      Dischargeable from `witness_sliver2_concrete` (per-coordinate `√ε` bound, `pdpdH := witness-
      SecondXDeriv`) summed over the `n` coordinates, with `hBlim` supplied by `sliverBound_tendsto_zero`
      (√ε rate).  The sum-over-coordinates plumbing is carried, not the conclusion.
    • `hEcomb`         — `DaTrunc = LapTrunc + Etrunc` (the output of `hE_combination` given its `hLap`
      + integrability carries).
    • `hEtrunc`        — `Etrunc → E*F` (the output of `etrunc_tendsto` given its dominations).
    • `hBoundaryLim`   — `BoundaryTrunc → F u 0 0` (the delta initial-condition boundary discharge).
    • `hDerivConv`     — `DaTrunc + BoundaryTrunc → deriv (heatConv H F · 0 0) u` (derivative-of-the-
      limit = limit-of-derivatives).
    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6` — this
    is ONE brick (the Laplacian–sliver connection) of the `a₁ = R/6` campaign.
-/
import Mathlib
import QIQTH.DuhamelLimitWiring
import QIQTH.NormalFormDischarge
import QIQTH.HeatParametrixError

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### L1 — the RNC flat reduction of the (frozen / genuine) convolution Laplacian.
    ############################################################################### -/

/-- **★ L1 (truncated) — `lapTrunc_eq_sum_pdpd`.**  At an RNC center (`g⁻¹(0)=δ`, `Γ(0)=0`) the
    truncated Laplacian `LapTrunc` reduces to the flat trace of second field-partials:
        `LapTrunc g gi H F m u = ∑ᵢ ∂ᵢ∂ᵢ (heatConvFrozen H F u (u−ε_m) · 0) 0`.
    Direct application of `laplaceBeltrami_at_rnc_center` to the frozen convolution `x`-slice. -/
theorem lapTrunc_eq_sum_pdpd (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) :
    LapTrunc g gi H F m u
      = ∑ i, pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0 := by
  unfold LapTrunc
  exact laplaceBeltrami_at_rnc_center g gi
    (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) 0 hgi hΓ

/-- **★ L1 (genuine) — `lap_heatConv_eq_sum_pdpd`.**  At an RNC center the Laplacian of the genuine
    convolution `x`-slice reduces to the flat trace:
        `laplaceBeltrami g gi (heatConv H F u · 0) 0 = ∑ᵢ ∂ᵢ∂ᵢ (heatConv H F u · 0) 0`.
    (The target's `Δ`-value expressed in flat-trace form, matching L2's improper interchange.) -/
theorem lap_heatConv_eq_sum_pdpd (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) :
    laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
      = ∑ i, pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0 :=
  laplaceBeltrami_at_rnc_center g gi (fun x => heatConv H F u x 0) 0 hgi hΓ

/-! ###############################################################################
    ### rate — the `√ε` sliver rate `K₁·2√ε_m + K₂·ε_m → 0`.
    ############################################################################### -/

/-- **★ rate — `sliverBound_tendsto_zero`.**  The `√ε` sliver-bound shape vanishes as `m → ∞`:
        `K₁ · (2·√ε_m) + K₂ · ε_m  →  0`.
    (`ε_m → 0` (`epsSeq_tendsto`), `√·` continuous at `0`, then `Tendsto.const_mul`/`.add`.)  This is
    exactly the `m → ∞` limit of `witness_sliver2_concrete`'s bound at `ε = ε_m`, supplying `hBlim`. -/
theorem sliverBound_tendsto_zero (K₁ K₂ : ℝ) :
    Tendsto (fun m => K₁ * (2 * Real.sqrt (epsSeq m)) + K₂ * epsSeq m) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun m => Real.sqrt (epsSeq m)) atTop (𝓝 0) := by
    have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto (0 : ℝ))
      rwa [Real.sqrt_zero] at this
    exact hc.comp epsSeq_tendsto
  have h1 : Tendsto (fun m => K₁ * (2 * Real.sqrt (epsSeq m))) atTop (𝓝 (K₁ * (2 * 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.mul hsqrt)
  have h2 : Tendsto (fun m => K₂ * epsSeq m) atTop (𝓝 (K₂ * 0)) :=
    tendsto_const_nhds.mul epsSeq_tendsto
  have := h1.add h2
  simpa using this

/-! ###############################################################################
    ### L3 — the sliver-difference limit `LapTrunc … m u → Δ_g(H*F)`.
    ############################################################################### -/

/-- **★★ L3 — `lapTrunc_tendsto`.**  THE SLIVER-DIFFERENCE LIMIT.  With
      • the RNC gauge (`hgi`/`hΓ`) at the center `0`,
      • the finite-gap interchange `hInterchange` (L2) `∂ᵢ∂ᵢ(heatConvFrozen H F u (u−ε_m) · 0) 0
        = ∫₀^{u−ε_m} ∫ pdpdH i (u−s) z · F s z 0`,
      • the untruncated interchange `hLapFull` `laplaceBeltrami g gi (heatConv H F u · 0) 0
        = ∑ᵢ ∫₀^u ∫ pdpdH i (u−s) z · F s z 0`,
      • interval-integrability on `[0,u−ε_m]` and `[u−ε_m,u]` (`hII_lo`/`hII_hi`),
      • the sliver bound `‖∑ᵢ ∫_{u−ε_m}^u ∫ pdpdH·F‖ ≤ B(ε_m)` (`hSliver`) with `B(ε_m) → 0` (`hBlim`),
    the truncated Laplacian equals the target minus exactly `∑ᵢ` the sliver (adjacency splitting), so
        `LapTrunc g gi H F m u  →  laplaceBeltrami g gi (heatConv H F u · 0) 0`.
    Route: L1 + `hInterchange` express `LapTrunc` as `∑ᵢ ∫₀^{u−ε_m}`, and
    `integral_add_adjacent_intervals` peels the sliver; `squeeze_zero_norm` + `tendsto_sub_nhds_zero_iff`
    close.  NOT `a₁ = R/6`. -/
theorem lapTrunc_tendsto (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : ∀ (m : ℕ) (i : Fin n),
        pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hLapFull : laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hII_lo : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m))
    (hII_hi : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume (u - epsSeq m) u)
    (B : ℝ → ℝ)
    (hSliver : ∀ m,
        ‖∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0‖
          ≤ B (epsSeq m))
    (hBlim : Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0)) :
    Tendsto (fun m => LapTrunc g gi H F m u) atTop
      (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0)) := by
  -- the exact sliver identity `LapTrunc = target − ∑ᵢ sliver`.
  have hL : ∀ m, LapTrunc g gi H F m u
      = laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        - ∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
    intro m
    have step1 : LapTrunc g gi H F m u
        = ∑ i, ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
      rw [lapTrunc_eq_sum_pdpd g gi H F m u hgi hΓ]
      exact Finset.sum_congr rfl (fun i _ => hInterchange m i)
    rw [step1, hLapFull, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hadj := intervalIntegral.integral_add_adjacent_intervals (hII_lo m i) (hII_hi m i)
    linarith [hadj]
  -- the norm bound feeding the squeeze.
  have hbound : ∀ m, ‖LapTrunc g gi H F m u
      - laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0‖ ≤ B (epsSeq m) := by
    intro m
    rw [hL m]
    set S := ∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 with hS
    have hring : laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0 - S
          - laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0 = -S := by ring
    rw [hring, norm_neg]
    exact hSliver m
  -- squeeze the difference to `0`, then unshift.
  have h0 : Tendsto (fun m => LapTrunc g gi H F m u
      - laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0) atTop (𝓝 0) :=
    squeeze_zero_norm hbound hBlim
  exact (tendsto_sub_nhds_zero_iff).mp h0

/-! ###############################################################################
    ### L4a — the specific `Da`-limit discharge from L3 + `Etrunc` limit.
    ############################################################################### -/

/-- **★★ L4a — `hDaLim_discharge`.**  From `hEcomb` (`DaTrunc = LapTrunc + Etrunc`, the E-combination),
    the sliver-difference limit `hLapTrunc` (`LapTrunc → Δ_g(H*F)`, L3), and the residual limit
    `hEtrunc` (`Etrunc → E*F`, `etrunc_tendsto`), the truncated `τ₀`-slot derivatives converge to the
    SPECIFIC value:
        `DaTrunc H F m u  →  laplaceBeltrami g gi (heatConv H F u · 0) 0 + heatConv (heatOp g gi H) F u 0 0`.
    `Tendsto.add` then `Tendsto.congr` along `hEcomb`.  This is exactly the `hDaLim` carry of
    `hDuhamel_of_daLim`.  NOT `a₁ = R/6`. -/
theorem hDaLim_discharge (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (hEcomb : ∀ m, DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u)
    (hLapTrunc : Tendsto (fun m => LapTrunc g gi H F m u) atTop
        (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0)))
    (hEtrunc : Tendsto (fun m => Etrunc g gi H F m u) atTop
        (𝓝 (heatConv (heatOp g gi H) F u 0 0))) :
    Tendsto (fun m => DaTrunc H F m u) atTop
      (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
            + heatConv (heatOp g gi H) F u 0 0)) :=
  (hLapTrunc.add hEtrunc).congr (fun m => (hEcomb m).symm)

/-- **★★★ L4 — `hDaLim_full`.**  The full `Da`-limit assembled directly from the L3 sliver
    ingredients: chains `lapTrunc_tendsto` (L3) into `hDaLim_discharge` (L4a).  Conclusion = the
    `hDaLim` carry of `hDuhamel_of_daLim`.  Conditional on the full residue; NOT `a₁ = R/6`. -/
theorem hDaLim_full (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : ∀ (m : ℕ) (i : Fin n),
        pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hLapFull : laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hII_lo : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m))
    (hII_hi : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume (u - epsSeq m) u)
    (B : ℝ → ℝ)
    (hSliver : ∀ m,
        ‖∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0‖
          ≤ B (epsSeq m))
    (hBlim : Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0))
    (hEcomb : ∀ m, DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u)
    (hEtrunc : Tendsto (fun m => Etrunc g gi H F m u) atTop
        (𝓝 (heatConv (heatOp g gi H) F u 0 0))) :
    Tendsto (fun m => DaTrunc H F m u) atTop
      (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
            + heatConv (heatOp g gi H) F u 0 0)) :=
  hDaLim_discharge g gi H F u hEcomb
    (lapTrunc_tendsto g gi H F u hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi B hSliver hBlim)
    hEtrunc

/-! ###############################################################################
    ### ★★★ THE CAPSTONE — `hDuhamel_assembled`.
    ############################################################################### -/

/-- **★★★★ THE hDaLimLU-ASSEMBLY CAPSTONE — `hDuhamel_assembled`.**  Threads the fully-assembled
    `Da`-limit `hDaLim_full` (L4) into the reduction capstone `hDuhamel_of_daLim`, discharging its
    `hDaLim` carry from the sliver machinery.  The Duhamel-principle output
        `heatOp g gi (heatConv H F · · ·) u 0 0 = F u 0 0 + heatConv (heatOp g gi H) F u 0 0`
    conditional ONLY on the accumulated labelled residue (the RNC gauge, the finite-gap + untruncated
    interchanges `hInterchange`/`hLapFull`, the adjacency integrabilities `hII_lo`/`hII_hi`, the sliver
    bound `B`/`hSliver`/`hBlim`, the E-combination `hEcomb`, the residual limit `hEtrunc`, the boundary
    limit `hBoundaryLim`, and the derivative-of-the-limit `hDerivConv`).  This is the campaign target =
    the conditional `hDaLim`-discharge wired to `hDuhamel`.  NOT `a₁ = R/6`. -/
theorem hDuhamel_assembled (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : ∀ (m : ℕ) (i : Fin n),
        pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hLapFull : laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hII_lo : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m))
    (hII_hi : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume (u - epsSeq m) u)
    (B : ℝ → ℝ)
    (hSliver : ∀ m,
        ‖∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0‖
          ≤ B (epsSeq m))
    (hBlim : Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0))
    (hEcomb : ∀ m, DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u)
    (hEtrunc : Tendsto (fun m => Etrunc g gi H F m u) atTop
        (𝓝 (heatConv (heatOp g gi H) F u 0 0)))
    (hBoundaryLim : Tendsto (fun m => BoundaryTrunc H F m u) atTop (𝓝 (F u 0 0)))
    (hDerivConv : Tendsto (fun m => DaTrunc H F m u + BoundaryTrunc H F m u) atTop
        (𝓝 (deriv (fun v => heatConv H F v 0 0) u))) :
    heatOp g gi (fun v p q => heatConv H F v p q) u 0 0
      = F u 0 0 + heatConv (heatOp g gi H) F u 0 0 := by
  have hDaLim := hDaLim_full g gi H F u hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi
    B hSliver hBlim hEcomb hEtrunc
  exact hDuhamel_of_daLim g gi H F u hBoundaryLim hDaLim hDerivConv

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.lapTrunc_eq_sum_pdpd
#print axioms QIQTH.HeatResidualBound.lap_heatConv_eq_sum_pdpd
#print axioms QIQTH.HeatResidualBound.sliverBound_tendsto_zero
#print axioms QIQTH.HeatResidualBound.lapTrunc_tendsto
#print axioms QIQTH.HeatResidualBound.hDaLim_discharge
#print axioms QIQTH.HeatResidualBound.hDaLim_full
#print axioms QIQTH.HeatResidualBound.hDuhamel_assembled
