/-
  DaLimLUWallRecon — J4-220: THE FINAL-WALL RECON of `hDaLimLU`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a
  census + threading brick: it (a) names every member of the `DaLimLocUnif.hDaLimLU_discharge` (U3)
  family as a build-checked `abbrev` (so the census reflects the ACTUAL Props, not prose), (b) banks
  the one genuinely-composing member — the loc-uniform (`∀ u ∈ U`) sliver bound — as NEW math, and
  (c) threads it into a capstone that isolates the sole irreducible open member of `hDaLimLU`.  No
  `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FAMILY (verbatim from `DaLimLocUnif.hDaLimLU_discharge`, U3).  The banked `hDaLimLU_discharge`
  reduces the sole genuine wall `hDaLimLU` (loc-unif `DaTrunc → Δ_g(H*F) + E*F`) to the family below.
  Each row: MEMBER — the census verdict — the provider.

    • `hgi`/`hΓ`      GAUGE (`g⁻¹(0)=δ`, `Γ(0)=0`).  DATA — the RNC normal-coordinate normalization at
                     the center `0`, satisfiable by an RNC chart.  No provider needed (input).
    • `pdpdH`        the second field-`x`-partial kernel (a FUNCTION, not a Prop).  DATA — the concrete
                     witness is `pdpdH i τ z := dHH τ 0 z` (second field-partial at `0`), whose closed
                     form is banked in `SecondOrderInterchange` / `ChartJetHessianMixed` (J4-218).
    • `hInterchange` finite-gap 2nd-order diff-under-∫∫.  BANKED (fixed `u`) —
                     `SecondOrderInterchange.hInterchange_discharge` produces the body VERBATIM at each
                     `u` (∀ m i); the `∀ u ∈ U` member re-quantifies it with `u`-uniform diff-under-∫
                     carries.  Content bottoms out in standard dominated differentiation.
    • `hLapFull`     untruncated (improper) 2nd-order interchange.  BANKED (fixed `u`) —
                     `InterchangeThreading.hLapFull_of_lims`; the reduction relocates the genuine
                     content to its carry `hLHSlim` (the C²-limit `Δ_g(frozen) → Δ_g(H*F)`, an F2 /
                     derivative-of-limit fact).
    • `hII_lo`/`hII_hi`  adjacency-split interval integrability of `pdpdH·F`.  DATA — Gaussian-domination
                     facts, routine.
    • `B`/`hSliver`/`hBlim`  the sliver bound + `√ε` rate.  BANKED — `SliverSumPlumbing.sliver_sum_bound`
                     from the per-coordinate `√ε` bounds `hbnd` (root = `NormalFormDischarge.
                     witness_sliver2_concrete`), rate = `LapTruncAssembly.sliverBound_tendsto_zero`.
                     ⚠ The existing `sliver_sum_bound` is `u`-FREE; the `hDaLimLU` member is `∀ u ∈ U`.
                     ★ `sliver_sum_bound_U` (THIS FILE) banks that loc-uniform upgrade, and
                     `hDaLimLU_of_sliverData` threads it in.
    • `Be`/`hEbnd`/`hEblim`  the residual-convolution tail bound with an EXPLICIT rate `Be(ε_m) → 0`.
                     ★★ WALL — no banked provider.  `DuhamelLimitWiring.etrunc_tendsto` gives only the
                     UN-rated pointwise limit `Etrunc → E*F` (a continuity-of-primitive argument with no
                     modulus); the loc-unif chain needs the `u`-uniform Gaussian-domination tail
                     `‖E*F − Etrunc‖ ≤ Be(ε_m)` WITH an explicit vanishing rate.  This is the genuine
                     irreducible mathematical content of `hDaLimLU` after all other members are threaded.
    • `hEcomb`       `DaTrunc = LapTrunc + Etrunc`.  BANKED — `TruncatedDuhamel.hE_combination`
                     (per `m u`, from the `Da`/`Lap` integral forms + 4 integrabilities);
                     `InterchangeThreading.hEcomb_discharged` at fixed `u`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE VERDICT.  After threading, the irreducible open content of `hDaLimLU` is EXACTLY the member
  `hEbnd` (with `Be`/`hEblim`): the `x/u`-uniform residual-convolution Gaussian tail estimate WITH AN
  EXPLICIT RATE.  Everything else is DATA (gauge, `pdpdH`, adjacency integrability) or BANKED (the
  interchange pair, the sliver bound — here upgraded to loc-uniform — and the E-combination).  The
  LADDER to close `hEbnd`:
    (E1) the pointwise tail `‖E*F u − Etrunc … m u‖ → 0` (already implicit in `etrunc_tendsto`);
    (E2) an EXPLICIT modulus: `‖E*F u − Etrunc … m u‖ ≤ Be(ε_m)` with `Be` `u`-free, from the Gaussian
         domination `|heatOp g gi H τ| ≤ (E₀+E₁τ)·√(3/2)ⁿ·G_{3τ/2}` + `|F| ≤ C_L·G_{2s}` bounding the
         truncated-tail integral `∫_{u−ε_m}^u ∫ …` by a strip-level `√ε`- or `ε`-type rate;
    (E3) `Be(ε_m) → 0` by the same `√ε`/`ε` argument as `sliverBound_tendsto_zero`.
  (E2) is the genuine remaining brick — the residual tail's explicit modulus.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DaLimLocUnif

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound
open scoped Interval Topology

namespace QIQTH.DaLimLUWallRecon

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the census: each `hDaLimLU_discharge` member as a build-checked `abbrev`.
    (The file compiling certifies each abbrev is well-typed and — via its use in the
    capstone below — is the EXACT member shape consumed by `hDaLimLU_discharge`.)
    ############################################################################### -/

/-- **GAUGE (gi).**  DATA — the RNC inverse-metric normalization `g⁻¹(0) = δ`. -/
abbrev MemGaugeGi (gi : Point n → Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0

/-- **GAUGE (Γ).**  DATA — the RNC Christoffel normalization `Γ(0) = 0`. -/
abbrev MemGaugeGamma (g gi : Point n → Fin n → Fin n → ℝ) : Prop :=
  ∀ k i j, christoffel g gi k i j (0 : Point n) = 0

/-- **INTERCHANGE (`∀ u ∈ U`).**  BANKED — `SecondOrderInterchange.hInterchange_discharge` (per `u`). -/
abbrev MemInterchange (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (pdpdH : Fin n → ℝ → Point n → ℝ) : Prop :=
  ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
    pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
      = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0

/-- **LAPFULL (`∀ u ∈ U`).**  BANKED — `InterchangeThreading.hLapFull_of_lims` (per `u`, carrying the
    C²-limit `hLHSlim`). -/
abbrev MemLapFull (g gi : Point n → Fin n → Fin n → ℝ) (H F : ℝ → Point n → Point n → ℝ)
    (U : Set ℝ) (pdpdH : Fin n → ℝ → Point n → ℝ) : Prop :=
  ∀ u ∈ U, laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
      = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0

/-- **ADJACENCY-LO (`∀ u ∈ U`).**  DATA — interval integrability of `pdpdH·F` on `[0, u−ε_m]`. -/
abbrev MemAdjLo (F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (pdpdH : Fin n → ℝ → Point n → ℝ) : Prop :=
  ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
    IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
      volume 0 (u - epsSeq m)

/-- **ADJACENCY-HI (`∀ u ∈ U`).**  DATA — interval integrability of `pdpdH·F` on `[u−ε_m, u]`. -/
abbrev MemAdjHi (F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (pdpdH : Fin n → ℝ → Point n → ℝ) : Prop :=
  ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
    IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
      volume (u - epsSeq m) u

/-- **SLIVER BOUND (`∀ u ∈ U`).**  BANKED — `sliver_sum_bound_U` (THIS FILE, the loc-uniform upgrade of
    `SliverSumPlumbing.sliver_sum_bound`). -/
abbrev MemSliver (F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (pdpdH : Fin n → ℝ → Point n → ℝ) (B : ℝ → ℝ) : Prop :=
  ∀ (m : ℕ), ∀ u ∈ U,
    ‖∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0‖
      ≤ B (epsSeq m)

/-- **RATE.**  BANKED — `LapTruncAssembly.sliverBound_tendsto_zero` / `tendsto_finsetSum`. -/
abbrev MemRateZero (B : ℝ → ℝ) : Prop :=
  Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0)

/-- **E-TAIL (`∀ u ∈ U`).**  ★★ WALL — the residual-convolution tail bound with an EXPLICIT rate.
    No banked provider; `etrunc_tendsto` gives only the un-rated pointwise limit. -/
abbrev MemETail (g gi : Point n → Fin n → Fin n → ℝ) (H F : ℝ → Point n → Point n → ℝ)
    (U : Set ℝ) (Be : ℝ → ℝ) : Prop :=
  ∀ (m : ℕ), ∀ u ∈ U,
    ‖heatConv (heatOp g gi H) F u 0 0 - Etrunc g gi H F m u‖ ≤ Be (epsSeq m)

/-- **E-COMBINATION.**  BANKED — `TruncatedDuhamel.hE_combination` (per `m u`). -/
abbrev MemECombine (g gi : Point n → Fin n → Fin n → ℝ) (H F : ℝ → Point n → Point n → ℝ) : Prop :=
  ∀ (m : ℕ) (u : ℝ), DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u

/-- **THE GOAL.**  The loc-unif `hDaLimLU` conclusion consumed by `DuhamelLimitWiring.hDuhamel_final`. -/
abbrev DaLimLUGoal (g gi : Point n → Fin n → Fin n → ℝ) (H F : ℝ → Point n → Point n → ℝ)
    (U : Set ℝ) : Prop :=
  TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
    (fun u => laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
          + heatConv (heatOp g gi H) F u 0 0) atTop U

/-! ###############################################################################
    ### §B — ★ the ONE genuinely-composing member: the loc-uniform sliver bound.
    ############################################################################### -/

/-- **★★ `sliver_sum_bound_U` — the LOC-UNIFORM (`∀ u ∈ U`) sliver bound.**  The upgrade of
    `SliverSumPlumbing.sliver_sum_bound` (which is `u`-FREE) to the `∀ u ∈ U` shape actually consumed by
    `hDaLimLU_discharge`'s `hSliver` slot.  From the per-coordinate `√ε` bounds (`u`-uniform, constants
    `D0 i, D1 i ≥ 0` strip-level)
      `|slivInt i m u| ≤ D0 i · (2√ε_m) + D1 i · ε_m`   (`∀ i m, ∀ u ∈ U`),
    the sum over `i : Fin n` obeys, WITH THE SAME `u`-FREE bound `B e := ∑ i (D0 i·2√e + D1 i·e)`,
      `‖∑ i, slivInt i m u‖ ≤ B(ε_m)`   (`∀ m, ∀ u ∈ U`),   and   `B(ε_m) → 0`.
    Route: `norm_sum_le` + `Real.norm_eq_abs` + `Finset.sum_le_sum` (the `u`-uniform per-`i` bound) for
    the bound; `tendsto_finsetSum` over the per-`i` `sliverBound_tendsto_zero` for the rate.  The `u`
    enters ONLY the `slivInt` argument — the bound `B` and the rate are `u`-free (strip-level), which is
    the whole point of the loc-uniform chain.  NOT `a₁ = R/6`. -/
theorem sliver_sum_bound_U {U : Set ℝ} (slivInt : Fin n → ℕ → ℝ → ℝ) (D0 D1 : Fin n → ℝ)
    (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |slivInt i m u| ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :
    ∃ B : ℝ → ℝ,
      (∀ (m : ℕ), ∀ u ∈ U, ‖∑ i, slivInt i m u‖ ≤ B (epsSeq m))
      ∧ Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0) := by
  refine ⟨fun e => ∑ i, (D0 i * (2 * Real.sqrt e) + D1 i * e), ?_, ?_⟩
  · intro m u hu
    calc ‖∑ i, slivInt i m u‖
        ≤ ∑ i, ‖slivInt i m u‖ := norm_sum_le _ _
      _ = ∑ i, |slivInt i m u| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑ i, (D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :=
          Finset.sum_le_sum (fun i _ => hbnd i m u hu)
  · have hsum : Tendsto
        (fun m => ∑ i, (D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)) atTop
        (𝓝 (∑ _i : Fin n, (0 : ℝ))) :=
      tendsto_finsetSum _ (fun i _ => sliverBound_tendsto_zero (D0 i) (D1 i))
    simpa using hsum

/-! ###############################################################################
    ### §C — ★★★ the capstone: thread the sliver discharge into `hDaLimLU`.
    ############################################################################### -/

/-- **★★★ `hDaLimLU_of_sliverData` — `hDaLimLU` WITH THE SLIVER SLOT INTERNALLY DISCHARGED.**  The exact
    `DaLimLocUnif.hDaLimLU_discharge` conclusion (the loc-unif `Da`-limit consumed by `hDuhamel_final`),
    with its `B`/`hSliver`/`hBlim` slots ELIMINATED — supplied internally by `sliver_sum_bound_U` from
    the per-coordinate `√ε` bounds `hbnd`.  The remaining hypotheses are EXACTLY the census residue:
      • DATA — gauge (`hgi`/`hΓ`), the kernel `pdpdH`, adjacency integrability (`hII_lo`/`hII_hi`),
        the `√ε` sliver amplitudes (`D0`/`D1`/`hD0`/`hD1`/`hbnd`);
      • BANKED (carried at their fixed-`u` builders) — `hInterchange`, `hLapFull`, `hEcomb`;
      • ★★ WALL — `hEbnd`/`hEblim` (the residual tail bound with an explicit rate — the SOLE genuinely
        open member, see the header verdict).
    This is the honest one-file threading of the only member of the `hDaLimLU` family that fully composes
    at the loc-uniform level with new math.  Pure interface threading otherwise.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_of_sliverData (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (hUopen : IsOpen U)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : MemInterchange H F U pdpdH)
    (hLapFull : MemLapFull g gi H F U pdpdH)
    (hII_lo : MemAdjLo F U pdpdH) (hII_hi : MemAdjHi F U pdpdH)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (Be : ℝ → ℝ) (hEbnd : MemETail g gi H F U Be) (hEblim : MemRateZero Be)
    (hEcomb : MemECombine g gi H F) :
    DaLimLUGoal g gi H F U := by
  obtain ⟨B, hSliver, hBlim⟩ := sliver_sum_bound_U
    (fun i m u => ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    D0 D1 hD0 hD1 hbnd
  exact hDaLimLU_discharge g gi H F U hUopen hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi
    B hSliver hBlim Be hEbnd hEblim hEcomb

end QIQTH.DaLimLUWallRecon

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimLUWallRecon.sliver_sum_bound_U
#print axioms QIQTH.DaLimLUWallRecon.hDaLimLU_of_sliverData
