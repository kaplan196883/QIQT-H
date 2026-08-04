/-
  ETailRateBound — J4-221: BRICK E2 — the last member of the last wall (`hDaLimLU`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It closes the
  SOLE genuinely-open member of the `DaLimLUWallRecon` census (J4-220): the E-tail bound `hEbnd`
  (with its rate `hEblim`) — the `u`-uniform residual-convolution Gaussian tail estimate WITH AN
  EXPLICIT VANISHING RATE.  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypotheses.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE RECIPE (the E-ladder of the `DaLimLUWallRecon` header).  Writing
      `Innr u s := ∫ z, heatOp g gi H (u−s) 0 z · F s z 0`,
  we have DEFINITIONALLY (`heatConv`, `Etrunc`)
      `heatConv (heatOp g gi H) F u 0 0 = ∫ s in 0..u,        Innr u s`,
      `Etrunc g gi H F m u           = ∫ s in 0..(u−ε_m),   Innr u s`,
  so by the adjacent-interval (Chasles) identity (`integral_add_adjacent_intervals`, from the two
  banked interval integrabilities `hIlo`/`hIhi`)
      `heatConv (heatOp g gi H) F u 0 0 − Etrunc g gi H F m u = ∫ s in (u−ε_m)..u, Innr u s`
  — EXACTLY the residual strip integral (the same peel the banked sliver bound uses).

  (E2) `inner_slice_bound` — the per-slice `u`-uniform inner bound.  From the D1 Gaussian domination
       `hEdom : |heatOp g gi H τ 0 z| ≤ (E₀+E₁τ)·√(3/2)ⁿ·G_{3τ/2}(0−z)` (residual vanishing at
       `τ ≤ 0`, `hEzero`) and the width-2 domination `hBdom : |F s z 0| ≤ C_L·G_{2s}(z−0)` (`F`
       vanishing at `s ≤ 0`, `hFzero`), on the strip `s ∈ (u−ε_m, u]` the inner `z`-pairing is
       bounded by the `s`- and `u`-FREE constant
         `‖Innr u s‖ ≤ (E₀+E₁·ε_m)·√(3/2)ⁿ·C_L·G_{aT}(0)`,
       where `aT ≤ u` is a UNIFORM time floor.  Route (mirroring `ConvCarriesDischarge`'s F1 peel):
       `‖∫ z ·‖ ≤ ∫ z |·|·|·|`, the `z`-integral of the Gaussian product collapses via Chapman–
       Kolmogorov `∫_z G_{3τ/2}(0−z)·G_{2s}(z−0) = G_{3τ/2+2s}(0)` (`gaussDdim_conv`), capped
       `s`-uniformly by `G_{aT}(0)` (width-antitone, `aT ≤ 3u/2 + s/2`), with `E₀+E₁τ ≤ E₀+E₁·ε_m`
       (`τ = u−s < ε_m`).  The `τ ≤ 0` / `s ≤ 0` excursions of the strip are killed by the vanishing
       (`hEzero`/`hFzero`), so the bound holds for ALL `m` (no `ε_m < u` restriction).

  (E2★) `hEbnd_discharge` — the RATED tail bound in the EXACT `MemETail` shape:
         `∀ m, ∀ u ∈ U, ‖heatConv (heatOp g gi H) F u 0 0 − Etrunc g gi H F m u‖ ≤ Be (ε_m)`
       with the `u`-FREE modulus `Be e := (E₀+E₁·e)·√(3/2)ⁿ·C_L·G_{aT}(0)·e`.  Route: the Chasles
       identity + `norm_integral_le_of_norm_le_const` (width `ε_m`, constant the per-slice bound).

  (E3) `Be_tendsto_zero` — the rate `Be(ε_m) → 0` (`ε_m → 0` times a bounded factor).

  (★ STRETCH) `hDaLimLU_from_data` — threading (E2★)+(E3) into
       `DaLimLUWallRecon.hDaLimLU_of_sliverData`'s `Be`/`hEbnd`/`hEblim` slots, yielding the COMPLETE
       `hDaLimLU` conclusion (`DaLimLUGoal`) from PURE DATA (gauge, `pdpdH`, the interchange/lapfull
       carries, adjacency + strip integrabilities, the `√ε` sliver amplitudes, and the two Gaussian
       dominations).  The entire `hDaLimLU` wall is thereby reduced to data.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DaLimLUWallRecon
import QIQTH.ConvCarriesDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon
open scoped Interval Topology

namespace QIQTH.ETailRateBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (E2) — the per-slice `u`-uniform inner bound.
    ############################################################################### -/

/-- **★ (E2) `inner_slice_bound`.**  On the residual strip `s ∈ (u−ε, u]`, the inner `z`-pairing of
    the parametrix residual `heatOp g gi H` against `F` is bounded by the `s`- and `u`-FREE constant
      `‖∫ z, heatOp g gi H (u−s) 0 z · F s z 0‖ ≤ (E₀+E₁·ε)·√(3/2)ⁿ·C_L·gaussDdim aT 0`,
    with `aT ≤ u` a uniform time floor.  From the D1 domination `hEdom` (residual vanishing at
    `τ ≤ 0`, `hEzero`), the width-2 domination `hFdom` (`F` vanishing at `s ≤ 0`, `hFzero`), via the
    Chapman–Kolmogorov Gaussian-product mass (`gaussDdim_conv`) capped by the diagonal peak at the
    floor (`gaussDdim_zero_antitone`).  The `τ ≤ 0` / `s ≤ 0` excursions are killed by vanishing, so
    the bound holds for ALL `ε > 0` (no `ε < u` restriction).  NOT `a₁ = R/6`. -/
theorem inner_slice_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (T E₀ E₁ C_L aT u εm : ℝ)
    (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hεm : 0 < εm) (hau : aT ≤ u) (huT : u ≤ T)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q| ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (s : ℝ) (hsmem : s ∈ Set.uIoc (u - εm) u) :
    ‖∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0‖
      ≤ (E₀ + E₁ * εm) * Real.sqrt (3 / 2) ^ n * C_L * gaussDdim aT (0 : Point n) := by
  set Sc : ℝ := Real.sqrt (3 / 2 : ℝ) ^ n with hSc
  have hSc0 : 0 ≤ Sc := by rw [hSc]; positivity
  set C : ℝ := (E₀ + E₁ * εm) * Sc * C_L * gaussDdim aT (0 : Point n) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg hE₀ (mul_nonneg hE₁ hεm.le)) hSc0) hC_L)
      (gaussDdim_nonneg _ _)
  rw [Set.uIoc_of_le (by linarith : u - εm ≤ u)] at hsmem
  rcases lt_or_ge 0 (u - s) with hτpos | hτle
  · rcases lt_or_ge 0 s with hspos | hsle
    · -- `0 < s`, `0 < τ` : full Gaussian domination.
      have hsT : s ≤ T := le_trans hsmem.2 huT
      have hτcap : u - s < εm := by linarith [hsmem.1]
      set c : ℝ := (E₀ + E₁ * (u - s)) * Sc * C_L with hc
      have hc0factor : 0 ≤ (E₀ + E₁ * (u - s)) * Sc :=
        mul_nonneg (add_nonneg hE₀ (mul_nonneg hE₁ hτpos.le)) hSc0
      have hdomg : Integrable
          (fun z : Point n =>
            c * (gaussDdim (3 / 2 * (u - s)) (0 - z) * gaussDdim (2 * s) (z - 0))) volume :=
        (gaussDdim_mul_integrable (3 / 2 * (u - s)) (2 * s) 0 0).const_mul c
      have hnn : (fun _ : Point n => (0 : ℝ)) ≤ᵐ[volume]
          (fun z : Point n => |heatOp g gi H (u - s) 0 z| * |F s z 0|) :=
        ae_of_all _ (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hle : (fun z : Point n => |heatOp g gi H (u - s) 0 z| * |F s z 0|)
          ≤ᵐ[volume]
            (fun z : Point n =>
              c * (gaussDdim (3 / 2 * (u - s)) (0 - z) * gaussDdim (2 * s) (z - 0))) := by
        refine ae_of_all _ (fun z => ?_)
        have hA' := hEdom (u - s) hτpos 0 z
        have hB' := hFdom s hspos hsT z 0
        calc |heatOp g gi H (u - s) 0 z| * |F s z 0|
            ≤ ((E₀ + E₁ * (u - s)) * Sc * gaussDdim (3 / 2 * (u - s)) (0 - z))
                * (C_L * gaussDdim (2 * s) (z - 0)) :=
              mul_le_mul hA' hB' (abs_nonneg _) (mul_nonneg hc0factor (gaussDdim_nonneg _ _))
          _ = c * (gaussDdim (3 / 2 * (u - s)) (0 - z) * gaussDdim (2 * s) (z - 0)) := by
              rw [hc]; ring
      calc ‖∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0‖
          ≤ ∫ (z : Point n), ‖heatOp g gi H (u - s) 0 z * F s z 0‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ (z : Point n), |heatOp g gi H (u - s) 0 z| * |F s z 0| := by
            simp only [Real.norm_eq_abs, abs_mul]
        _ ≤ ∫ z, c * (gaussDdim (3 / 2 * (u - s)) (0 - z) * gaussDdim (2 * s) (z - 0)) :=
            integral_mono_of_nonneg hnn hdomg hle
        _ = c * gaussDdim (3 / 2 * (u - s) + 2 * s) (0 : Point n) := by
            rw [integral_const_mul,
                gaussDdim_conv (3 / 2 * (u - s)) (2 * s) (by linarith) (by linarith) 0 0, sub_zero]
        _ ≤ C := by
            rw [hCdef]
            have hcle : c ≤ (E₀ + E₁ * εm) * Sc * C_L := by
              rw [hc]
              have hstep : E₀ + E₁ * (u - s) ≤ E₀ + E₁ * εm := by
                have := mul_le_mul_of_nonneg_left hτcap.le hE₁
                linarith
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep hSc0) hC_L
            have hgle : gaussDdim (3 / 2 * (u - s) + 2 * s) (0 : Point n)
                ≤ gaussDdim aT (0 : Point n) :=
              gaussDdim_zero_antitone haT (by linarith)
            calc c * gaussDdim (3 / 2 * (u - s) + 2 * s) (0 : Point n)
                ≤ ((E₀ + E₁ * εm) * Sc * C_L) * gaussDdim aT (0 : Point n) :=
                  mul_le_mul hcle hgle (gaussDdim_nonneg _ _)
                    (mul_nonneg (mul_nonneg (add_nonneg hE₀ (mul_nonneg hE₁ hεm.le)) hSc0) hC_L)
              _ = (E₀ + E₁ * εm) * Sc * C_L * gaussDdim aT (0 : Point n) := by ring
    · -- `s ≤ 0` : `F` vanishes.
      have hz : (fun z : Point n => heatOp g gi H (u - s) 0 z * F s z 0) = fun _ => (0 : ℝ) := by
        funext z; rw [hFzero s hsle z 0, mul_zero]
      rw [hz]; simp only [integral_zero, norm_zero]; exact hC0
  · -- `τ = u − s ≤ 0` : the residual vanishes.
    have hz : (fun z : Point n => heatOp g gi H (u - s) 0 z * F s z 0) = fun _ => (0 : ℝ) := by
      funext z; rw [hEzero (u - s) hτle 0 z, zero_mul]
    rw [hz]; simp only [integral_zero, norm_zero]; exact hC0

/-! ###############################################################################
    ### (E2★) — the RATED E-tail bound in the EXACT `MemETail` shape.
    ############################################################################### -/

/-- **★★ (E2★) `hEbnd_discharge`.**  The `x/u`-uniform residual-convolution tail bound WITH an
    explicit `u`-free rate, hitting `DaLimLUWallRecon.MemETail` VERBATIM:
      `∀ m, ∀ u ∈ U, ‖heatConv (heatOp g gi H) F u 0 0 − Etrunc g gi H F m u‖ ≤ Be (ε_m)`,
    with `Be e := (E₀+E₁·e)·√(3/2)ⁿ·C_L·gaussDdim aT 0 · e`.  Route: the strip-difference identity
    `heatConv − Etrunc = ∫ s in (u−ε_m)..u, Innr u s` (Chasles, from `hIlo`/`hIhi`) +
    `norm_integral_le_of_norm_le_const` (width `ε_m`, per-slice constant `inner_slice_bound`).

    Carried DATA (each genuine, none the conclusion, none vacuous):
      • `aT` a UNIFORM time floor `hUlb : ∀ u ∈ U, aT ≤ u` and ceiling `hUT : ∀ u ∈ U, u ≤ T`
        (satisfiable e.g. `U = Ioo aT T`);
      • the D1 domination `hEdom` + residual vanishing `hEzero`;
      • the width-2 domination `hFdom` + source vanishing `hFzero` (`F = leviSeries E` vanishes at
        `s ≤ 0`);
      • the two strip interval integrabilities `hIlo`/`hIhi` of the inner `s`-pairing (the census
        INTEGRABILITY pile).
    NOT `a₁ = R/6`. -/
theorem hEbnd_discharge (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (T : ℝ) (U : Set ℝ)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u) (hUT : ∀ u ∈ U, u ≤ T)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q| ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0)
          volume (u - epsSeq m) u) :
    MemETail g gi H F U
      (fun e => (E₀ + E₁ * e) * Real.sqrt (3 / 2) ^ n * C_L * gaussDdim aT (0 : Point n) * e) := by
  intro m u hu
  have hεm : 0 < epsSeq m := epsSeq_pos m
  -- the two convolutions as `s`-integrals of the common inner pairing.
  have hHC : heatConv (heatOp g gi H) F u 0 0
      = ∫ s in (0)..u, ∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0 := rfl
  have hET : Etrunc g gi H F m u
      = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0 := rfl
  -- Chasles: the difference is exactly the residual strip integral.
  have hadj := intervalIntegral.integral_add_adjacent_intervals (hIlo m u hu) (hIhi m u hu)
  have hdiff : heatConv (heatOp g gi H) F u 0 0 - Etrunc g gi H F m u
      = ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0 := by
    rw [hHC, hET]; linarith [hadj]
  rw [hdiff]
  -- the strip estimate (width `ε_m` × the per-slice constant).
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun s (hs : s ∈ Set.uIoc (u - epsSeq m) u) =>
      inner_slice_bound g gi H F T E₀ E₁ C_L aT u (epsSeq m) hE₀ hE₁ hC_L haT hεm
        (hUlb u hu) (hUT u hu) hEdom hEzero hFdom hFzero s hs)
  rw [show |u - (u - epsSeq m)| = epsSeq m from by rw [sub_sub_cancel]; exact abs_of_pos hεm] at hbnd
  exact hbnd

/-! ###############################################################################
    ### (E3) — the rate `Be(ε_m) → 0`.
    ############################################################################### -/

/-- **★ (E3) `Be_tendsto_zero`.**  The explicit modulus of `hEbnd_discharge` vanishes:
      `Be(ε_m) = (E₀+E₁·ε_m)·√(3/2)ⁿ·C_L·gaussDdim aT 0 · ε_m  →  0`,
    since `ε_m → 0` and the leading factor `(E₀+E₁·ε_m)·√(3/2)ⁿ·C_L·gaussDdim aT 0` converges to a
    finite limit.  Hits `DaLimLUWallRecon.MemRateZero` for the same `Be`.  NOT `a₁ = R/6`. -/
theorem Be_tendsto_zero (E₀ E₁ C_L aT : ℝ) :
    MemRateZero
      (fun e => (E₀ + E₁ * e) * Real.sqrt (3 / 2) ^ n * C_L * gaussDdim aT (0 : Point n) * e) := by
  show Tendsto (fun m => (E₀ + E₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * C_L
      * gaussDdim aT (0 : Point n) * epsSeq m) atTop (𝓝 0)
  have h1 : Tendsto (fun m => E₀ + E₁ * epsSeq m) atTop (𝓝 (E₀ + E₁ * 0)) :=
    (epsSeq_tendsto.const_mul E₁).const_add E₀
  have h2 := (((h1.mul_const (Real.sqrt (3 / 2) ^ n)).mul_const C_L).mul_const
    (gaussDdim aT (0 : Point n))).mul epsSeq_tendsto
  simpa using h2

/-! ###############################################################################
    ### ★ THE STRETCH — the full `hDaLimLU` wall reduced entirely to DATA.
    ############################################################################### -/

/-- **★★★ THE STRETCH — `hDaLimLU_from_data`.**  The COMPLETE `hDaLimLU` conclusion (`DaLimLUGoal`,
    the loc-unif `Da`-limit consumed by `DuhamelLimitWiring.hDuhamel_final`) from PURE DATA — the last
    wall of the `a₁ = R/6` Duhamel-principle reduction reduced entirely to data.  Threads
    `hEbnd_discharge` (E2★) and `Be_tendsto_zero` (E3) into the `Be`/`hEbnd`/`hEblim` slots of
    `DaLimLUWallRecon.hDaLimLU_of_sliverData` (which already discharges the sliver slot internally).

    The remaining hypotheses are EXACTLY the census residue, now ALL DATA:
      • GAUGE — `hgi`/`hΓ` (RNC normalization at the center);
      • INTERCHANGE (BANKED at their fixed-`u` builders) — `hInterchange`/`hLapFull`/`hEcomb`;
      • INTEGRABILITY — adjacency `hII_lo`/`hII_hi` (`pdpdH·F`) and the residual strip
        `hIlo`/`hIhi` (the E-tail's inner pairing);
      • GEOMETRIC-MODULI — the `√ε` sliver amplitudes `D0`/`D1`/`hD0`/`hD1`/`hbnd`;
      • DOMINATION — the two Gaussian dominations `hEdom`/`hEzero` (residual) and `hFdom`/`hFzero`
        (source `F`), with the uniform time floor `aT` (`hUlb`) / ceiling (`hUT`) and the amplitude
        nonnegativities.
    The SOLE previously-open member `hEbnd`/`hEblim` is now DISCHARGED from these dominations.  Pure
    interface threading otherwise.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_from_data (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : MemInterchange H F U pdpdH)
    (hLapFull : MemLapFull g gi H F U pdpdH)
    (hII_lo : MemAdjLo F U pdpdH) (hII_hi : MemAdjHi F U pdpdH)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u) (hUT : ∀ u ∈ U, u ≤ T)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q| ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi H F) :
    DaLimLUGoal g gi H F U :=
  hDaLimLU_of_sliverData g gi H F U hUopen hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi
    D0 D1 hD0 hD1 hbnd
    (fun e => (E₀ + E₁ * e) * Real.sqrt (3 / 2) ^ n * C_L * gaussDdim aT (0 : Point n) * e)
    (hEbnd_discharge g gi H F T U E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hUT
      hEdom hEzero hFdom hFzero hIlo hIhi)
    (Be_tendsto_zero E₀ E₁ C_L aT)
    hEcomb

end QIQTH.ETailRateBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.ETailRateBound.inner_slice_bound
#print axioms QIQTH.ETailRateBound.hEbnd_discharge
#print axioms QIQTH.ETailRateBound.Be_tendsto_zero
#print axioms QIQTH.ETailRateBound.hDaLimLU_from_data
