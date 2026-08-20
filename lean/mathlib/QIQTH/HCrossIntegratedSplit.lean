/-
  HCrossIntegratedSplit — the INTEGRATED (diagonal-split) reduction of the live `hCross` census
  binder, replacing J4-926's FALSE pointwise `hdiff` premise with a TRUE integrated one.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick.  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis,
  none equal to the conclusion, no existing file edited.

  ## THE PRIOR TRAP (J4-926 / cp794, documented + confirmed).  J4-926 collapsed the mixed
  second-difference of `heatConvFrozen A B` to a SINGLE sliver integral
      `Δ² = ∫ s in b..(b+k), (Φ(a+h,s) − Φ(a,s))`,   `Φ(c,s) := ∫ z, A(c−s) x z · B s z y`,
  and then bounded it by a POINTWISE premise `hdiff : |Φ(a+h,s)−Φ(a,s)| ≤ L·|h|`.  With `a = u`,
  `b = u−ε`, that premise is GENUINELY FALSE: the sliver reaches the causal diagonal `s = u`
  (whenever `k ≥ ε`), where `Φ(u,u) = ∫ W(0)·F = 0` (`W(0)=0`) but `Φ(u+h,u) → F(u,0,0) ≠ 0` as
  `h→0⁺`, so `|Φ(u+h,u)−Φ(u,u)|/|h| ~ 1/h` diverges.  The naive integrated salvage using the `τ⁻¹`
  time-derivative envelope LOSES A LOG (`h·∫ dτ/τ = h·log(ε/h)`); a bounded+continuous `F` is
  insufficient.

  ## THE INTEGRATED SPLIT (this file; sympy + gpt-5.6-sol GO).  Write `D(s) := Φ(u+h,s) − Φ(u,s)`.
  Split the sliver integral in `s` at the diagonals `s = u` and `s = u+h`, using THREE hypotheses:
    • (H_far)  for `s < u`:            `|D(s)| ≤ C_far·h·(u−s)^{−1/2}`   — the `F`-Lipschitz
      CANCELLATION envelope (subtract `F(s,0)`, `∫∂_σW = 0` mass conservation, Gaussian moments
      upgrade the `τ⁻¹` rate to the INTEGRABLE `τ^{−1/2}` — this is what KILLS the log);
    • (H_near) for `u ≤ s ≤ u+h`:      `|D(s)| ≤ 2M`   (`M = sup|Φ|`, from `|W|,|F|` bounded);
    • (H_zero) for `s > u+h`:          `D(s) = 0`   (both time args of `W` negative — finite
      propagation).
  The three pieces assemble to (NO LOG, `L` depending only on `ε = ε_m`):
      `|Δ²|  ≤  (2·C_far/√ε + 2·M/ε) · (h·k)`.

  ⚠  WHAT THIS DOES — AND DOES NOT — DO.  This is the maximal honest INTEGRATED reduction the cp794
  next-session menu asked for: it REPLACES J4-926's impossible pointwise `hdiff` with the TRUE
  integrated split, reducing `hCross` (for `h,k > 0`) to exactly `{H_far, H_near, H_zero}`.  `H_near`
  (boundedness) and `H_zero` (finite propagation, `W(≤0)=0`) are cheap and true for the concrete
  witness; `H_far` (the `F`-Lipschitz `τ^{−1/2}` cancellation envelope for the chart-composed
  concrete witness) remains the OPEN chart-CoV moment wall (J4-919/920 core, not yet assembled).  So
  this file does NOT close `hCross`, and (per gpt-5.6-sol) it covers only the `h > 0, k > 0` quadrant
  (negative `k` is a mirror; negative `h` moves the diagonal to `u+h` and needs a separate route).
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
-/
import Mathlib
import QIQTH.HeatDuhamel
import QIQTH.SliverEstimates

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatDuhamel
open scoped Interval

namespace QIQTH.HeatResidualBound

/-! ###############################################################################
    ### §A — the two real/analytic helpers (no measure theory).
    ############################################################################### -/

/-- **`far_sqrt_bound`.**  The far-part square-root increment is `O(k/√ε)` uniformly: for `0 < ε`,
    `0 ≤ δ ≤ ε`, and `ε − δ ≤ k`,
        `2·√ε − 2·√δ ≤ (2/√ε)·k`.
    This is the single inequality that converts the reflected-sliver value `2(√ε − √δ)` into the
    `hCross`-shaped `k`-linear bound (with `δ = (ε−k)₊`).  NOT `a₁ = R/6`. -/
theorem far_sqrt_bound (ε δ k : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (hk : ε - δ ≤ k) :
    2 * Real.sqrt ε - 2 * Real.sqrt δ ≤ 2 / Real.sqrt ε * k := by
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  rw [div_mul_eq_mul_div, le_div_iff₀ hsε]
  have h1 : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
  have h2 : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ
  have h3 : Real.sqrt δ ≤ Real.sqrt ε := Real.sqrt_le_sqrt hδε
  nlinarith [Real.sqrt_nonneg δ, Real.sqrt_nonneg ε, h1, h2, h3, hk]

/-- **`reflected_sliver_partial`.**  The reflected sliver weight integrated to an interior endpoint:
        `∫ s in (u−ε)..c, (u−s)^{−1/2} = 2·√ε − 2·√(u−c)`   (for `u−ε ≤ c ≤ u`, `0 ≤ ε`).
    Route: oriented additivity `∫_{u−ε}^c + ∫_c^u = ∫_{u−ε}^u`, each closed by the banked
    `sliver_rpow_sub`.  NOT `a₁ = R/6`. -/
theorem reflected_sliver_partial (u ε c : ℝ) (hbc : u - ε ≤ c) (hcu : c ≤ u) (hε : 0 ≤ ε) :
    ∫ s in (u - ε)..c, (u - s) ^ (-(1 : ℝ) / 2) = 2 * Real.sqrt ε - 2 * Real.sqrt (u - c) := by
  have hfull := sliver_rpow_sub u ε hε
  have hupper := sliver_rpow_sub u (u - c) (by linarith)
  have hc : u - (u - c) = c := by ring
  rw [hc] at hupper
  have hII1 : IntervalIntegrable (fun s => (u - s) ^ (-(1 : ℝ) / 2)) volume (u - ε) c :=
    (rpow_sub_intervalIntegrable u ε hε).mono_set (by
      rw [Set.uIcc_of_le hbc, Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc le_rfl hcu)
  have hII2 : IntervalIntegrable (fun s => (u - s) ^ (-(1 : ℝ) / 2)) volume c u :=
    (rpow_sub_intervalIntegrable u ε hε).mono_set (by
      rw [Set.uIcc_of_le hcu, Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc hbc le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hII1 hII2
  rw [hfull] at hadd
  rw [hupper] at hadd
  linarith [hadd]

/-! ###############################################################################
    ### §B — the far-part sub-integral bound.
    ############################################################################### -/

/-- **`far_part_bound`.**  On a sub-interval `[u−ε, c]` with `c ≤ u`, the `(u−s)^{−1/2}` cancellation
    envelope integrates to the reflected-sliver value:
        `|∫ s in (u−ε)..c, D s|  ≤  C_far·h·(2·√ε − 2·√(u−c))`.
    The singular endpoint `s = u` is excluded a.e. (`ae_ne_point`); the majorant is interval-integrable
    (`rpow_sub_intervalIntegrable`) and evaluated by `reflected_sliver_partial`.  NOT `a₁ = R/6`. -/
theorem far_part_bound (D : ℝ → ℝ) (u ε h C_far c : ℝ)
    (hε : 0 < ε) (hh : 0 ≤ h) (hCf : 0 ≤ C_far) (hbc : u - ε ≤ c) (hcu : c ≤ u)
    (hII : IntervalIntegrable D volume (u - ε) c)
    (H_far : ∀ s ∈ Set.Ioo (u - ε) u, |D s| ≤ C_far * h * (u - s) ^ (-(1 : ℝ) / 2)) :
    |∫ s in (u - ε)..c, D s| ≤ C_far * h * (2 * Real.sqrt ε - 2 * Real.sqrt (u - c)) := by
  have hmajII : IntervalIntegrable
      (fun s => C_far * h * (u - s) ^ (-(1 : ℝ) / 2)) volume (u - ε) c := by
    have h1 : IntervalIntegrable (fun s => (u - s) ^ (-(1 : ℝ) / 2)) volume (u - ε) c :=
      (rpow_sub_intervalIntegrable u ε hε.le).mono_set (by
        rw [Set.uIcc_of_le hbc, Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc le_rfl hcu)
    exact h1.const_mul _
  rw [← Real.norm_eq_abs]
  have hstep : ‖∫ s in (u - ε)..c, D s‖
      ≤ ∫ s in (u - ε)..c, C_far * h * (u - s) ^ (-(1 : ℝ) / 2) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hbc ?_ hmajII
    filter_upwards [ae_ne_point u] with t ht htmem
    have htmem' : t ∈ Set.Ioo (u - ε) u :=
      ⟨htmem.1, lt_of_le_of_ne (le_trans htmem.2 hcu) ht⟩
    rw [Real.norm_eq_abs]; exact H_far t htmem'
  refine le_trans hstep ?_
  rw [intervalIntegral.integral_const_mul, reflected_sliver_partial u ε c hbc hcu hε.le]

/-! ###############################################################################
    ### §C — the integrated diagonal-split sliver bound (THE analytic core).
    ############################################################################### -/

set_option maxHeartbeats 800000 in
/-- **★★ `integrated_split_sliver_bound` — THE INTEGRATED DIAGONAL SPLIT.**  For ANY `D : ℝ → ℝ`,
    given `0 < ε, h, k`, constants `0 ≤ C_far, M`, interval-integrability of `D` on the sliver, and
      • (H_far)  `|D s| ≤ C_far·h·(u−s)^{−1/2}`  for `s ∈ Ioo (u−ε) u`,
      • (H_near) `|D s| ≤ 2·M`                    for `s ∈ Icc u (u+h)`,
      • (H_zero) `D s = 0`                         for `s ∈ Ioi (u+h)`,
    the sliver integral is bounded WITHOUT any log:
        `|∫ s in (u−ε)..(u−ε+k), D s|  ≤  (2·C_far/√ε + 2·M/ε)·(h·k)`.
    Route: split at `min(b+k,u)` and `min(b+k,u+h)` into three cases (`k ≤ ε`, `ε < k ≤ ε+h`,
    `ε+h < k`); far part via `far_part_bound`+`far_sqrt_bound`, near part via
    `norm_integral_le_of_norm_le_const`, zero part vanishes.  NOT `a₁ = R/6`. -/
theorem integrated_split_sliver_bound (D : ℝ → ℝ) (u ε h k C_far M : ℝ)
    (hε : 0 < ε) (hh : 0 < h) (hk : 0 < k) (hCf : 0 ≤ C_far) (hM : 0 ≤ M)
    (hII : IntervalIntegrable D volume (u - ε) (u - ε + k))
    (H_far : ∀ s ∈ Set.Ioo (u - ε) u, |D s| ≤ C_far * h * (u - s) ^ (-(1 : ℝ) / 2))
    (H_near : ∀ s ∈ Set.Icc u (u + h), |D s| ≤ 2 * M)
    (H_zero : ∀ s ∈ Set.Ioi (u + h), D s = 0) :
    |∫ s in (u - ε)..(u - ε + k), D s| ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (h * k) := by
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hCterm : 0 ≤ 2 * C_far / Real.sqrt ε := by positivity
  have hMterm : 0 ≤ 2 * M / ε := by positivity
  have hhk : 0 ≤ h * k := by positivity
  -- the far-part → L·h·k inequality, reused in all three cases (δ = u − c).
  have far_to_L : ∀ c : ℝ, u - ε ≤ c → c ≤ u → ε - (u - c) ≤ k →
      C_far * h * (2 * Real.sqrt ε - 2 * Real.sqrt (u - c)) ≤ (2 * C_far / Real.sqrt ε) * (h * k) := by
    intro c hc1 hc2 hc3
    have hsq := far_sqrt_bound ε (u - c) k hε (by linarith) (by linarith) hc3
    calc C_far * h * (2 * Real.sqrt ε - 2 * Real.sqrt (u - c))
        ≤ C_far * h * (2 / Real.sqrt ε * k) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (2 * C_far / Real.sqrt ε) * (h * k) := by ring
  -- the near-part constant bound helper.
  have near_bound : ∀ p q : ℝ, p ≤ q → q ≤ u + h → u ≤ p →
      IntervalIntegrable D volume p q → |∫ s in p..q, D s| ≤ 2 * M * (q - p) := by
    intro p q hpq hqu hup _
    rw [← Real.norm_eq_abs]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := p) (b := q) (C := 2 * M) (f := D) (fun s hs => by
        rw [Set.uIoc_of_le hpq] at hs
        rw [Real.norm_eq_abs]
        exact H_near s ⟨le_trans hup (le_of_lt hs.1), le_trans hs.2 hqu⟩)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ q - p)] at hb
    exact hb
  rcases le_or_gt (u - ε + k) u with hA | hA
  · -- Case A: k ≤ ε (whole sliver is far).
    have hfar := far_part_bound D u ε h C_far (u - ε + k) hε hh.le hCf (by linarith) hA hII H_far
    refine le_trans hfar ?_
    have := far_to_L (u - ε + k) (by linarith) hA (by
      have : u - (u - ε + k) = ε - k := by ring
      rw [this]; linarith)
    refine le_trans this ?_
    have : (2 * C_far / Real.sqrt ε) * (h * k)
        ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (h * k) := by
      apply mul_le_mul_of_nonneg_right (by linarith) hhk
    exact this
  · -- Cases B/C: u < u−ε+k, split at u.
    have hIIbu : IntervalIntegrable D volume (u - ε) u :=
      hII.mono_set (by
        rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc le_rfl (by linarith))
    have hIIu : IntervalIntegrable D volume u (u - ε + k) :=
      hII.mono_set (by
        rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc (by linarith) le_rfl)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hIIbu hIIu
    -- far part on [u−ε, u]
    have hfar := far_part_bound D u ε h C_far u hε hh.le hCf (by linarith) le_rfl hIIbu H_far
    simp only [sub_self, Real.sqrt_zero, mul_zero, sub_zero] at hfar
    have hfarL : C_far * h * (2 * Real.sqrt ε) ≤ (2 * C_far / Real.sqrt ε) * (h * k) := by
      have := far_to_L u (by linarith) le_rfl (by simp; linarith)
      simpa only [sub_self, Real.sqrt_zero, mul_zero, sub_zero] using this
    rcases le_or_gt (u - ε + k) (u + h) with hB | hC
    · -- Case B: ε < k ≤ ε+h.
      have hnear := near_bound u (u - ε + k) (by linarith) hB le_rfl hIIu
      have hnearval : 2 * M * ((u - ε + k) - u) ≤ (2 * M / ε) * (h * k) := by
        have hkmε : (u - ε + k) - u = k - ε := by ring
        rw [hkmε]
        have hkeh : k - ε ≤ h := by linarith
        have hle : k - ε ≤ h * k / ε := by
          rw [le_div_iff₀ hε]; nlinarith [hh.le]
        calc 2 * M * (k - ε) ≤ 2 * M * (h * k / ε) :=
              mul_le_mul_of_nonneg_left hle (by linarith)
          _ = (2 * M / ε) * (h * k) := by ring
      calc |∫ s in (u - ε)..(u - ε + k), D s|
          = |(∫ s in (u - ε)..u, D s) + ∫ s in u..(u - ε + k), D s| := by rw [hadd]
        _ ≤ |∫ s in (u - ε)..u, D s| + |∫ s in u..(u - ε + k), D s| := abs_add_le _ _
        _ ≤ C_far * h * (2 * Real.sqrt ε) + 2 * M * ((u - ε + k) - u) := add_le_add hfar hnear
        _ ≤ (2 * C_far / Real.sqrt ε) * (h * k) + (2 * M / ε) * (h * k) :=
              add_le_add hfarL hnearval
        _ = (2 * C_far / Real.sqrt ε + 2 * M / ε) * (h * k) := by ring
    · -- Case C: ε+h < k.  Split further at u+h.
      have hIInear : IntervalIntegrable D volume u (u + h) :=
        hII.mono_set (by
          rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
          exact Set.Icc_subset_Icc (by linarith) (by linarith))
      have hIIzero : IntervalIntegrable D volume (u + h) (u - ε + k) :=
        hII.mono_set (by
          rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
          exact Set.Icc_subset_Icc (by linarith) le_rfl)
      have hadd2 := intervalIntegral.integral_add_adjacent_intervals hIInear hIIzero
      -- ∫_u^{b+k} = ∫_u^{u+h} + ∫_{u+h}^{b+k}
      have hnear := near_bound u (u + h) (by linarith) le_rfl le_rfl hIInear
      have hnearval : 2 * M * ((u + h) - u) ≤ (2 * M / ε) * (h * k) := by
        have huh : (u + h) - u = h := by ring
        rw [huh]
        have hle : h ≤ h * k / ε := by
          rw [le_div_iff₀ hε]; nlinarith [hh.le]
        calc 2 * M * h ≤ 2 * M * (h * k / ε) := mul_le_mul_of_nonneg_left hle (by linarith)
          _ = (2 * M / ε) * (h * k) := by ring
      -- zero part vanishes
      have hzeroval : |∫ s in (u + h)..(u - ε + k), D s| ≤ 0 := by
        rw [← Real.norm_eq_abs]
        have hb := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := u + h) (b := u - ε + k) (C := 0) (f := D) (fun s hs => by
            rw [Set.uIoc_of_le (by linarith)] at hs
            rw [Real.norm_eq_abs, H_zero s (Set.mem_Ioi.mpr hs.1), abs_zero])
        simpa using hb
      calc |∫ s in (u - ε)..(u - ε + k), D s|
          = |(∫ s in (u - ε)..u, D s) + ∫ s in u..(u - ε + k), D s| := by rw [hadd]
        _ = |(∫ s in (u - ε)..u, D s)
              + ((∫ s in u..(u + h), D s) + ∫ s in (u + h)..(u - ε + k), D s)| := by rw [hadd2]
        _ ≤ |∫ s in (u - ε)..u, D s|
              + |(∫ s in u..(u + h), D s) + ∫ s in (u + h)..(u - ε + k), D s| := abs_add_le _ _
        _ ≤ |∫ s in (u - ε)..u, D s|
              + (|∫ s in u..(u + h), D s| + |∫ s in (u + h)..(u - ε + k), D s|) :=
              add_le_add le_rfl (abs_add_le _ _)
        _ ≤ C_far * h * (2 * Real.sqrt ε) + (2 * M * ((u + h) - u) + 0) :=
              add_le_add hfar (add_le_add hnear hzeroval)
        _ ≤ (2 * C_far / Real.sqrt ε) * (h * k) + ((2 * M / ε) * (h * k) + 0) :=
              add_le_add hfarL (add_le_add hnearval le_rfl)
        _ = (2 * C_far / Real.sqrt ε + 2 * M / ε) * (h * k) := by ring

/-! ###############################################################################
    ### §D — the collapse wrapper: mixed 2nd difference ⟶ integrated sliver bound.
    ############################################################################### -/

/-- **★ `mixed_second_diff_frozen_reduction_integrated`.**  The INTEGRATED sibling of J4-926's
    `mixed_second_diff_frozen_reduction`: the same oriented-additivity collapse of the mixed second
    difference to the single sliver integral, but bounded by an ARBITRARY integrated bound `Bnd`
    (rather than J4-926's FALSE pointwise `hdiff`).  GIVEN the four interval-integrabilities of the
    inner convolution and
        `hInt : |∫ s in b..(b+k), (Φ(a+h,s) − Φ(a,s))| ≤ Bnd`,
    the mixed second difference obeys `|Δ²| ≤ Bnd`.  Pure algebra (the J4-926 collapse) + `hInt`.
    NOT `a₁ = R/6`. -/
theorem mixed_second_diff_frozen_reduction_integrated {n : ℕ}
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (a b h k Bnd : ℝ)
    (hah_hi : IntervalIntegrable (fun s => ∫ z, A (a + h - s) x z * B s z y) volume b (b + k))
    (ha_hi : IntervalIntegrable (fun s => ∫ z, A (a - s) x z * B s z y) volume b (b + k))
    (hah_lo : IntervalIntegrable (fun s => ∫ z, A (a + h - s) x z * B s z y) volume 0 b)
    (ha_lo : IntervalIntegrable (fun s => ∫ z, A (a - s) x z * B s z y) volume 0 b)
    (hInt : |∫ s in b..(b + k),
        ((∫ z, A (a + h - s) x z * B s z y) - (∫ z, A (a - s) x z * B s z y))| ≤ Bnd) :
    |heatConvFrozen A B (a + h) (b + k) x y - heatConvFrozen A B (a + h) b x y
        - heatConvFrozen A B a (b + k) x y + heatConvFrozen A B a b x y| ≤ Bnd := by
  simp only [heatConvFrozen]
  have hah : (∫ s in (0 : ℝ)..(b + k), ∫ z, A (a + h - s) x z * B s z y)
      - (∫ s in (0 : ℝ)..b, ∫ z, A (a + h - s) x z * B s z y)
      = ∫ s in b..(b + k), ∫ z, A (a + h - s) x z * B s z y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hah_lo hah_hi]; ring
  have ha : (∫ s in (0 : ℝ)..(b + k), ∫ z, A (a - s) x z * B s z y)
      - (∫ s in (0 : ℝ)..b, ∫ z, A (a - s) x z * B s z y)
      = ∫ s in b..(b + k), ∫ z, A (a - s) x z * B s z y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals ha_lo ha_hi]; ring
  have hrew : (∫ s in (0 : ℝ)..(b + k), ∫ z, A (a + h - s) x z * B s z y)
        - (∫ s in (0 : ℝ)..b, ∫ z, A (a + h - s) x z * B s z y)
        - (∫ s in (0 : ℝ)..(b + k), ∫ z, A (a - s) x z * B s z y)
        + (∫ s in (0 : ℝ)..b, ∫ z, A (a - s) x z * B s z y)
      = ∫ s in b..(b + k),
          ((∫ z, A (a + h - s) x z * B s z y) - (∫ z, A (a - s) x z * B s z y)) := by
    have e1 : (∫ s in (0 : ℝ)..(b + k), ∫ z, A (a + h - s) x z * B s z y)
          - (∫ s in (0 : ℝ)..b, ∫ z, A (a + h - s) x z * B s z y)
          - (∫ s in (0 : ℝ)..(b + k), ∫ z, A (a - s) x z * B s z y)
          + (∫ s in (0 : ℝ)..b, ∫ z, A (a - s) x z * B s z y)
        = ((∫ s in (0 : ℝ)..(b + k), ∫ z, A (a + h - s) x z * B s z y)
            - (∫ s in (0 : ℝ)..b, ∫ z, A (a + h - s) x z * B s z y))
          - ((∫ s in (0 : ℝ)..(b + k), ∫ z, A (a - s) x z * B s z y)
            - (∫ s in (0 : ℝ)..b, ∫ z, A (a - s) x z * B s z y)) := by ring
    rw [e1, hah, ha]
    exact (intervalIntegral.integral_sub hah_hi ha_hi).symm
  rw [hrew]; exact hInt

/-! ###############################################################################
    ### §E — the CAPSTONE: the exact live `hCross` binder shape from the split.
    ############################################################################### -/

set_option maxHeartbeats 800000 in
/-- **★★★ `hcross_mixed_second_diff_split_bound` — the exact `hCross` binder from the integrated split.**
    For the frozen convolution of ANY `A B`, base times `a = u`, `b = u − ε`, shifts `h, k > 0`,
    GIVEN the four interval-integrabilities AND the diagonal-split hypotheses
    `{H_far, H_near, H_zero}` on the inner τ-shift difference, the MIXED SECOND DIFFERENCE obeys the
    exact live `hCross` binder shape
        `|Δ²|  ≤  (2·C_far/√ε + 2·M/ε) · (|h|·|k|)`.
    Route: `integrated_split_sliver_bound` bounds the sliver integral of the difference,
    `mixed_second_diff_frozen_reduction_integrated` collapses the second difference onto it, and
    `|h|·|k| = h·k` for `h,k > 0`.  This REPLACES J4-926's impossible pointwise `hdiff` with the TRUE
    integrated split.  Covers only `h,k > 0`; still open on the concrete `H_far` cancellation
    envelope.  NOT `a₁ = R/6`. -/
theorem hcross_mixed_second_diff_split_bound {n : ℕ}
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (u ε h k C_far M : ℝ)
    (hε : 0 < ε) (hh : 0 < h) (hk : 0 < k) (hCf : 0 ≤ C_far) (hM : 0 ≤ M)
    (hah_hi : IntervalIntegrable
      (fun s => ∫ z, A (u + h - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (ha_hi : IntervalIntegrable
      (fun s => ∫ z, A (u - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (hah_lo : IntervalIntegrable (fun s => ∫ z, A (u + h - s) x z * B s z y) volume 0 (u - ε))
    (ha_lo : IntervalIntegrable (fun s => ∫ z, A (u - s) x z * B s z y) volume 0 (u - ε))
    (H_far : ∀ s ∈ Set.Ioo (u - ε) u,
        |(∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y)|
          ≤ C_far * h * (u - s) ^ (-(1 : ℝ) / 2))
    (H_near : ∀ s ∈ Set.Icc u (u + h),
        |(∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y)| ≤ 2 * M)
    (H_zero : ∀ s ∈ Set.Ioi (u + h),
        (∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y) = 0) :
    |heatConvFrozen A B (u + h) (u - ε + k) x y - heatConvFrozen A B (u + h) (u - ε) x y
        - heatConvFrozen A B u (u - ε + k) x y + heatConvFrozen A B u (u - ε) x y|
      ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (|h| * |k|) := by
  -- the sliver integrand.
  set D : ℝ → ℝ :=
    fun s => (∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y) with hDdef
  have hIID : IntervalIntegrable D volume (u - ε) (u - ε + k) := hah_hi.sub ha_hi
  have hslive := integrated_split_sliver_bound D u ε h k C_far M hε hh hk hCf hM hIID
    H_far H_near H_zero
  -- feed to the collapse wrapper (a = u, b = u − ε).
  have hcollapse := mixed_second_diff_frozen_reduction_integrated A B x y u (u - ε) h k
    ((2 * C_far / Real.sqrt ε + 2 * M / ε) * (h * k))
    (by simpa using hah_hi) (by simpa using ha_hi) hah_lo ha_lo (by
      simpa only [hDdef] using hslive)
  -- rewrite |h|·|k| = h·k.
  rw [abs_of_pos hh, abs_of_pos hk]
  simpa using hcollapse

/-! ###############################################################################
    ### §F — NON-VACUITY of the analytic core (teeth-bearing, finite-support witness).
    ############################################################################### -/

/-- **Non-vacuity of `integrated_split_sliver_bound`, with TEETH.**  The full hypothesis bundle is
    jointly satisfiable at the CONTINUOUS finite-support witness
        `D(s) := max 0 (u+h−s) − max 0 (u−s)`   (`u = 0, ε = h = 1, k = 3`, case `ε+h < k`):
      • far: on `Ioo (−1) 0` the two ramps are both active so `D ≡ 1 = h`, and `1 ≤ 1·(−s)^{−1/2}`
        (`C_far = 1`) since `√(−s) ≤ 1` — the `(u−s)^{−1/2}` envelope machinery is genuinely exercised
        (NOT `0 ≤ 0`);
      • near: on `Icc 0 1`, `D = 1 − s ∈ [0,1] ≤ 1 = 2M` (`M = 1/2`), tight at `s = 0`;
      • zero: on `Ioi 1`, both ramps vanish so `D = 0`.
    `D` is continuous (difference of two `max 0 (affine)`), hence interval-integrable.  NOT `a₁ = R/6`. -/
theorem integrated_split_sliver_bound_hyp_satisfiable :
    ∃ (D : ℝ → ℝ) (u ε h k C_far M : ℝ),
      0 < ε ∧ 0 < h ∧ 0 < k ∧ 0 ≤ C_far ∧ 0 ≤ M ∧
      IntervalIntegrable D volume (u - ε) (u - ε + k) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, |D s| ≤ C_far * h * (u - s) ^ (-(1 : ℝ) / 2)) ∧
      (∀ s ∈ Set.Icc u (u + h), |D s| ≤ 2 * M) ∧
      (∀ s ∈ Set.Ioi (u + h), D s = 0) := by
  refine ⟨fun s => max 0 (0 + 1 - s) - max 0 (0 - s), 0, 1, 1, 3, 1, 1 / 2,
    one_pos, one_pos, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · -- integrability from continuity.
    apply Continuous.intervalIntegrable
    exact (continuous_const.max (by fun_prop)).sub (continuous_const.max (by fun_prop))
  · -- H_far on Ioo (0−1) 0 = Ioo (−1) 0.
    intro s hs
    simp only [Set.mem_Ioo] at hs
    dsimp only
    have hpos : (0 : ℝ) < 0 - s := by linarith
    have hval : max 0 (0 + 1 - s) - max 0 (0 - s) = 1 := by
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ 0 + 1 - s),
          max_eq_right (by linarith : (0 : ℝ) ≤ 0 - s)]; ring
    have hle1 : Real.sqrt (0 - s) ≤ 1 := by
      calc Real.sqrt (0 - s) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    have hrw : (0 - s) ^ (-(1 : ℝ) / 2) = (Real.sqrt (0 - s))⁻¹ :=
      (inv_sqrt_eq_rpow (0 - s) hpos).symm
    rw [hval, hrw, one_mul, one_mul, abs_one]
    exact (one_le_inv₀ (Real.sqrt_pos.mpr hpos)).mpr hle1
  · -- H_near on Icc 0 1.
    intro s hs
    simp only [Set.mem_Icc] at hs
    dsimp only
    have hval : max 0 (0 + 1 - s) - max 0 (0 - s) = 1 - s := by
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ 0 + 1 - s),
          max_eq_left (by linarith : (0 - s : ℝ) ≤ 0)]; ring
    rw [hval, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s)]; linarith
  · -- H_zero on Ioi 1.
    intro s hs
    simp only [Set.mem_Ioi] at hs
    dsimp only
    rw [max_eq_left (by linarith : (0 + 1 - s : ℝ) ≤ 0),
        max_eq_left (by linarith : (0 - s : ℝ) ≤ 0)]; ring

end QIQTH.HeatResidualBound
