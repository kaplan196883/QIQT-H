/-
  HCrossNegativeQuadrants — the THREE negative-sign quadrants of the integrated `hCross`
  mixed-second-difference estimate, completing J4-927's `h,k > 0`-only construction to ALL four
  sign quadrants (the degenerate `h=0`/`k=0` axes are trivial by `subst;simp`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE brick completing the sign-quadrant coverage of the hCross sliver estimate.  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypothesis,
  no existing banked file edited.

  ## WHAT J4-927 LEFT OPEN.  `HCrossIntegratedSplit.lean` (J4-927) proved the live `hCross` binder shape
  ONLY for `h > 0, k > 0` — the census/differentiation layer only ever instantiates that quadrant.  The
  three negative-sign quadrants `(h>0,k<0)`, `(h<0,k>0)`, `(h<0,k<0)` had NO banked lemma even stating
  them.  This file supplies all three, as a genuine mathematical completion of the estimate's own
  infrastructure (gpt-5.6-sol high scope check 2026-08-21: both constructions SOUND; k<0 genuinely EASY
  = pure orientation + far-only; h<0 reduces to J4-927 by an EXACT antisymmetry relabel with NO new
  analysis).

  ## THE TWO CONSTRUCTIONS.
    • **k < 0 (far-only).**  For `k < 0` the sliver interval `[u−ε+k, u−ε]` lies ENTIRELY LEFT of `u−ε`,
      i.e. every `s ≤ u−ε < u`, so `u−s ≥ ε > 0`: NO diagonal singularity.  Reversing orientation
      (`integral_symm`) and majorizing `(u−s)^{−1/2} ≤ ε^{−1/2}` (`Real.rpow_le_rpow_of_nonpos`, base
      `u−s ≥ ε`, exponent `≤ 0`) gives `|∫| ≤ (C_far/√ε)·(h·|k|)` with a CONSTANT bound — no near/zero
      pieces, no sqrt-sliver integration, no cancellation.  Needs only the FAR envelope, on the
      leftward-extended domain `Ioo (u−ε+k) u`.  → `far_only_sliver_bound`.
    • **h < 0 (antisymmetry relabel).**  The mixed second difference is ANTISYMMETRIC under swapping the
      two h-points: `|Δ²(u,ε,h,k)| = |Δ²(u+h,ε+h,−h,k)|`.  For `−ε < h < 0` (⟺ `u+h > u−ε`, the moved
      diagonal `u+h` stays right of the lower anchor `u−ε`), the `h<0` sliver is EXACTLY the banked
      `h>0` sliver core `integrated_split_sliver_bound` re-centred at `ũ := u+h` (`ε̃ := ε+h`, `h̃ := −h`),
      with the far envelope re-anchored at `u+h` (`(u+h−s)^{−1/2}`) — no new estimate, degraded constant
      `√(ε+h) < √ε`.  → `hcross_split_bound_hneg_kpos` (k>0), `hcross_split_bound_hneg_kneg` (k<0).

  The sign-agnostic collapse `mixed_second_diff_frozen_reduction_integrated` (J4-927; no positivity on
  `h,k`) assembles all three onto the exact live `hCross` binder shape.

  ⚠  STILL NOT `a₁ = R/6`, and does NOT change the top-level conditional status.  Each quadrant is
  carrier-conditional on the SAME per-`s` far/near/zero data as the `h,k>0` branch (whose concrete
  `H_far` cancellation envelope stays the OPEN chart wall), so this closes real gaps in the campaign's
  own hCross infrastructure without discharging any of `{hDuhamel, hDConv, hCConv}`.  `a₁ = R/6` remains
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import Mathlib
import QIQTH.HeatDuhamel
import QIQTH.HCrossIntegratedSplit

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatDuhamel
open scoped Interval

namespace QIQTH.HeatResidualBound

/-! ###############################################################################
    ### §A — the k < 0 far-only sliver bound (constant majorant, no singularity).
    ############################################################################### -/

/-- **★★ `far_only_sliver_bound` — the `k < 0` sliver bound (far-only, no diagonal).**  For ANY
    `D : ℝ → ℝ`, `0 < ε`, `0 < h`, `k < 0`, `0 ≤ C_far, M`, interval-integrability of `D` on the
    (reversed) sliver, and the FAR envelope on the leftward-extended domain
      • (H_far)  `|D s| ≤ C_far·h·(u−s)^{−1/2}`   for `s ∈ Ioo (u−ε+k) u`,
    the sliver integral is bounded WITHOUT any near/zero pieces:
        `|∫ s in (u−ε)..(u−ε+k), D s|  ≤  (2·C_far/√ε + 2·M/ε)·(h·|k|)`.
    Route: since `k < 0` the whole interval sits at `s ≤ u−ε < u`, so `u−s ≥ ε > 0` and there is NO
    diagonal singularity; reverse orientation (`integral_symm`) and majorize `(u−s)^{−1/2} ≤ ε^{−1/2}`
    (`Real.rpow_le_rpow_of_nonpos`) by a CONSTANT, then `norm_integral_le_of_norm_le_const`.
    NOT `a₁ = R/6`. -/
theorem far_only_sliver_bound (D : ℝ → ℝ) (u ε h k C_far M : ℝ)
    (hε : 0 < ε) (hh : 0 < h) (hk : k < 0) (hCf : 0 ≤ C_far) (hM : 0 ≤ M)
    (hII : IntervalIntegrable D volume (u - ε) (u - ε + k))
    (H_far : ∀ s ∈ Set.Ioo (u - ε + k) u, |D s| ≤ C_far * h * (u - s) ^ (-(1 : ℝ) / 2)) :
    |∫ s in (u - ε)..(u - ε + k), D s| ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (h * |k|) := by
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hℓb : u - ε + k ≤ u - ε := by linarith
  -- reverse to forward orientation.
  rw [intervalIntegral.integral_symm (u - ε + k) (u - ε), abs_neg]
  -- goal: |∫ s in (u−ε+k)..(u−ε), D s| ≤ ...
  have hconst := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := u - ε + k) (b := u - ε) (C := C_far * h * (Real.sqrt ε)⁻¹) (f := D)
      (fun s hs => by
        rw [Set.uIoc_of_le hℓb] at hs
        rw [Real.norm_eq_abs]
        have hsmem : s ∈ Set.Ioo (u - ε + k) u := ⟨hs.1, by have := hs.2; linarith⟩
        have hfar := H_far s hsmem
        have hus : ε ≤ u - s := by have := hs.2; linarith
        have hmono : (u - s) ^ (-(1 : ℝ) / 2) ≤ ε ^ (-(1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_nonpos hε hus (by norm_num)
        have hεrw : ε ^ (-(1 : ℝ) / 2) = (Real.sqrt ε)⁻¹ := (inv_sqrt_eq_rpow ε hε).symm
        calc |D s| ≤ C_far * h * (u - s) ^ (-(1 : ℝ) / 2) := hfar
          _ ≤ C_far * h * ε ^ (-(1 : ℝ) / 2) :=
                mul_le_mul_of_nonneg_left hmono (mul_nonneg hCf hh.le)
          _ = C_far * h * (Real.sqrt ε)⁻¹ := by rw [hεrw])
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (u - ε) - (u - ε + k))] at hconst
  have hlen : (u - ε) - (u - ε + k) = |k| := by rw [abs_of_neg hk]; ring
  rw [hlen] at hconst
  refine le_trans hconst ?_
  have heq : C_far * h * (Real.sqrt ε)⁻¹ * |k| = (C_far / Real.sqrt ε) * (h * |k|) := by
    rw [div_eq_mul_inv]; ring
  rw [heq]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hh.le (abs_nonneg k))
  have h1 : (0 : ℝ) ≤ C_far / Real.sqrt ε := div_nonneg hCf hsε.le
  have h2 : (0 : ℝ) ≤ 2 * M / ε := div_nonneg (by linarith) hε.le
  have e : 2 * C_far / Real.sqrt ε = 2 * (C_far / Real.sqrt ε) := by ring
  rw [e]; linarith

/-- **Non-vacuity of `far_only_sliver_bound`, with TEETH.**  The full bundle is jointly satisfiable at
    the constant witness `D ≡ 2^{−1/2}` (`u=0, ε=h=1, k=−1, C_far=1, M=1/2`): the far domain is
    `Ioo (−2) 0`, and the envelope `(0−s)^{−1/2}` genuinely DOMINATES the nonzero constant `2^{−1/2}`
    (`2^{−1/2} ≤ (0−s)^{−1/2}` since `0−s ≤ 2`, via `Real.rpow_le_rpow_of_nonpos`), NOT `0 ≤ 0` — the
    `(u−s)^{−1/2}` envelope is genuinely exercised.  `D` constant ⟹ interval-integrable.  NOT `a₁=R/6`. -/
theorem far_only_sliver_bound_hyp_satisfiable :
    ∃ (D : ℝ → ℝ) (u ε h k C_far M : ℝ),
      0 < ε ∧ 0 < h ∧ k < 0 ∧ 0 ≤ C_far ∧ 0 ≤ M ∧
      IntervalIntegrable D volume (u - ε) (u - ε + k) ∧
      (∀ s ∈ Set.Ioo (u - ε + k) u, |D s| ≤ C_far * h * (u - s) ^ (-(1 : ℝ) / 2)) := by
  refine ⟨fun _ => (2 : ℝ) ^ (-(1 : ℝ) / 2), 0, 1, 1, -1, 1, 1 / 2,
    one_pos, one_pos, by norm_num, one_pos.le, by norm_num, ?_, ?_⟩
  · exact (continuous_const).intervalIntegrable _ _
  · intro s hs
    simp only [Set.mem_Ioo] at hs
    have hpos : (0 : ℝ) < 0 - s := by linarith [hs.2]
    have hle2 : (0 : ℝ) - s ≤ 2 := by linarith [hs.1]
    have hmono : (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ (0 - s) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hpos hle2 (by norm_num)
    show |(2 : ℝ) ^ (-(1 : ℝ) / 2)| ≤ (1 : ℝ) * 1 * ((0 : ℝ) - s) ^ (-(1 : ℝ) / 2)
    rw [one_mul, one_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact hmono

/-! ###############################################################################
    ### §B — the frozen `hCross` binder, quadrant `h > 0, k < 0`.
    ############################################################################### -/

set_option maxHeartbeats 800000 in
/-- **★★★ `hcross_split_bound_hpos_kneg` — the live `hCross` binder for `h > 0, k < 0`.**  Same shape as
    J4-927's `hcross_mixed_second_diff_split_bound` but for `k < 0`: needs ONLY the FAR envelope (on the
    leftward-extended domain `Ioo (u−ε+k) u`), NO near/zero carries.  Route: `far_only_sliver_bound`
    bounds the sliver of the inner τ-shift difference; `mixed_second_diff_frozen_reduction_integrated`
    (sign-agnostic in `k`) collapses the mixed second difference; `|h| = h`, `|k|` kept.  NOT `a₁=R/6`. -/
theorem hcross_split_bound_hpos_kneg {n : ℕ}
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (u ε h k C_far M : ℝ)
    (hε : 0 < ε) (hh : 0 < h) (hk : k < 0) (hCf : 0 ≤ C_far) (hM : 0 ≤ M)
    (hah_hi : IntervalIntegrable
      (fun s => ∫ z, A (u + h - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (ha_hi : IntervalIntegrable
      (fun s => ∫ z, A (u - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (hah_lo : IntervalIntegrable (fun s => ∫ z, A (u + h - s) x z * B s z y) volume 0 (u - ε))
    (ha_lo : IntervalIntegrable (fun s => ∫ z, A (u - s) x z * B s z y) volume 0 (u - ε))
    (H_far : ∀ s ∈ Set.Ioo (u - ε + k) u,
        |(∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y)|
          ≤ C_far * h * (u - s) ^ (-(1 : ℝ) / 2)) :
    |heatConvFrozen A B (u + h) (u - ε + k) x y - heatConvFrozen A B (u + h) (u - ε) x y
        - heatConvFrozen A B u (u - ε + k) x y + heatConvFrozen A B u (u - ε) x y|
      ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (|h| * |k|) := by
  set D : ℝ → ℝ :=
    fun s => (∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y) with hDdef
  have hIID : IntervalIntegrable D volume (u - ε) (u - ε + k) := hah_hi.sub ha_hi
  have hslive := far_only_sliver_bound D u ε h k C_far M hε hh hk hCf hM hIID H_far
  have hcollapse := mixed_second_diff_frozen_reduction_integrated A B x y u (u - ε) h k
    ((2 * C_far / Real.sqrt ε + 2 * M / ε) * (h * |k|))
    (by simpa using hah_hi) (by simpa using ha_hi) hah_lo ha_lo
    (by simpa only [hDdef] using hslive)
  rw [abs_of_pos hh]
  exact hcollapse

/-! ###############################################################################
    ### §C — the frozen `hCross` binder, quadrant `h < 0, k > 0` (antisymmetry relabel).
    ############################################################################### -/

set_option maxHeartbeats 800000 in
/-- **★★★ `hcross_split_bound_hneg_kpos` — the live `hCross` binder for `−ε < h < 0, k > 0`.**  The
    `h<0` sliver IS the banked `h>0` core `integrated_split_sliver_bound` re-centred at `ũ := u+h`
    (`ε̃ := ε+h > 0`, `h̃ := −h > 0`), with the far envelope re-anchored at `u+h`, the near strip
    `[u+h,u]`, and the zero region `(u,∞)`.  No new estimate; degraded constant `√(ε+h)`.  Collapse via
    the sign-agnostic `mixed_second_diff_frozen_reduction_integrated`.  NOT `a₁=R/6`. -/
theorem hcross_split_bound_hneg_kpos {n : ℕ}
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (u ε h k C_far M : ℝ)
    (hε : 0 < ε) (hh : h < 0) (hhε : -ε < h) (hk : 0 < k) (hCf : 0 ≤ C_far) (hM : 0 ≤ M)
    (hah_hi : IntervalIntegrable
      (fun s => ∫ z, A (u + h - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (ha_hi : IntervalIntegrable
      (fun s => ∫ z, A (u - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (hah_lo : IntervalIntegrable (fun s => ∫ z, A (u + h - s) x z * B s z y) volume 0 (u - ε))
    (ha_lo : IntervalIntegrable (fun s => ∫ z, A (u - s) x z * B s z y) volume 0 (u - ε))
    (H_far : ∀ s ∈ Set.Ioo (u - ε) (u + h),
        |(∫ z, A (u - s) x z * B s z y) - (∫ z, A (u + h - s) x z * B s z y)|
          ≤ C_far * (-h) * (u + h - s) ^ (-(1 : ℝ) / 2))
    (H_near : ∀ s ∈ Set.Icc (u + h) u,
        |(∫ z, A (u - s) x z * B s z y) - (∫ z, A (u + h - s) x z * B s z y)| ≤ 2 * M)
    (H_zero : ∀ s ∈ Set.Ioi u,
        (∫ z, A (u - s) x z * B s z y) - (∫ z, A (u + h - s) x z * B s z y) = 0) :
    |heatConvFrozen A B (u + h) (u - ε + k) x y - heatConvFrozen A B (u + h) (u - ε) x y
        - heatConvFrozen A B u (u - ε + k) x y + heatConvFrozen A B u (u - ε) x y|
      ≤ (2 * C_far / Real.sqrt (ε + h) + 2 * M / (ε + h)) * (|h| * |k|) := by
  set D' : ℝ → ℝ :=
    fun s => (∫ z, A (u - s) x z * B s z y) - (∫ z, A (u + h - s) x z * B s z y) with hD'
  have hε' : 0 < ε + h := by linarith
  have hh' : 0 < -h := by linarith
  have hIID : IntervalIntegrable D' volume ((u + h) - (ε + h)) ((u + h) - (ε + h) + k) := by
    rw [show (u + h) - (ε + h) = u - ε from by ring]
    exact ha_hi.sub hah_hi
  have hslive := integrated_split_sliver_bound D' (u + h) (ε + h) (-h) k C_far M
      hε' hh' hk hCf hM hIID
      (by
        intro s hs
        rw [show (u + h) - (ε + h) = u - ε from by ring] at hs
        exact H_far s hs)
      (by
        intro s hs
        rw [show (u + h) + (-h) = u from by ring] at hs
        exact H_near s hs)
      (by
        intro s hs
        rw [show (u + h) + (-h) = u from by ring] at hs
        exact H_zero s hs)
  rw [show (u + h) - (ε + h) = u - ε from by ring] at hslive
  have hfun : (fun s => (∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y))
            = fun s => -D' s := by funext s; simp only [hD']; ring
  have key : |∫ s in (u - ε)..(u - ε + k),
        ((∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y))|
      = |∫ s in (u - ε)..(u - ε + k), D' s| := by
    rw [hfun, intervalIntegral.integral_neg, abs_neg]
  have hInt : |∫ s in (u - ε)..(u - ε + k),
        ((∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y))|
      ≤ (2 * C_far / Real.sqrt (ε + h) + 2 * M / (ε + h)) * ((-h) * k) := by
    rw [key]; exact hslive
  have hcollapse := mixed_second_diff_frozen_reduction_integrated A B x y u (u - ε) h k
    ((2 * C_far / Real.sqrt (ε + h) + 2 * M / (ε + h)) * ((-h) * k))
    (by simpa using hah_hi) (by simpa using ha_hi) hah_lo ha_lo (by simpa using hInt)
  rw [abs_of_neg hh, abs_of_pos hk]
  exact hcollapse

/-! ###############################################################################
    ### §D — the frozen `hCross` binder, quadrant `h < 0, k < 0`.
    ############################################################################### -/

set_option maxHeartbeats 800000 in
/-- **★★★ `hcross_split_bound_hneg_kneg` — the live `hCross` binder for `−ε < h < 0, k < 0`.**  Combines
    both constructions: the far-only `k<0` sliver bound `far_only_sliver_bound` re-centred at `ũ := u+h`
    (`ε̃ := ε+h`, `h̃ := −h`), collapsed by the sign-agnostic reduction.  NOT `a₁=R/6`. -/
theorem hcross_split_bound_hneg_kneg {n : ℕ}
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (u ε h k C_far M : ℝ)
    (hε : 0 < ε) (hh : h < 0) (hhε : -ε < h) (hk : k < 0) (hCf : 0 ≤ C_far) (hM : 0 ≤ M)
    (hah_hi : IntervalIntegrable
      (fun s => ∫ z, A (u + h - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (ha_hi : IntervalIntegrable
      (fun s => ∫ z, A (u - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (hah_lo : IntervalIntegrable (fun s => ∫ z, A (u + h - s) x z * B s z y) volume 0 (u - ε))
    (ha_lo : IntervalIntegrable (fun s => ∫ z, A (u - s) x z * B s z y) volume 0 (u - ε))
    (H_far : ∀ s ∈ Set.Ioo (u - ε + k) (u + h),
        |(∫ z, A (u - s) x z * B s z y) - (∫ z, A (u + h - s) x z * B s z y)|
          ≤ C_far * (-h) * (u + h - s) ^ (-(1 : ℝ) / 2)) :
    |heatConvFrozen A B (u + h) (u - ε + k) x y - heatConvFrozen A B (u + h) (u - ε) x y
        - heatConvFrozen A B u (u - ε + k) x y + heatConvFrozen A B u (u - ε) x y|
      ≤ (2 * C_far / Real.sqrt (ε + h) + 2 * M / (ε + h)) * (|h| * |k|) := by
  set D' : ℝ → ℝ :=
    fun s => (∫ z, A (u - s) x z * B s z y) - (∫ z, A (u + h - s) x z * B s z y) with hD'
  have hε' : 0 < ε + h := by linarith
  have hh' : 0 < -h := by linarith
  have hIID : IntervalIntegrable D' volume ((u + h) - (ε + h)) ((u + h) - (ε + h) + k) := by
    rw [show (u + h) - (ε + h) = u - ε from by ring]
    exact ha_hi.sub hah_hi
  have hslive := far_only_sliver_bound D' (u + h) (ε + h) (-h) k C_far M hε' hh' hk hCf hM hIID
      (by
        intro s hs
        rw [show (u + h) - (ε + h) = u - ε from by ring] at hs
        exact H_far s hs)
  rw [show (u + h) - (ε + h) = u - ε from by ring] at hslive
  have hfun : (fun s => (∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y))
            = fun s => -D' s := by funext s; simp only [hD']; ring
  have key : |∫ s in (u - ε)..(u - ε + k),
        ((∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y))|
      = |∫ s in (u - ε)..(u - ε + k), D' s| := by
    rw [hfun, intervalIntegral.integral_neg, abs_neg]
  have hInt : |∫ s in (u - ε)..(u - ε + k),
        ((∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y))|
      ≤ (2 * C_far / Real.sqrt (ε + h) + 2 * M / (ε + h)) * ((-h) * |k|) := by
    rw [key]; exact hslive
  have hcollapse := mixed_second_diff_frozen_reduction_integrated A B x y u (u - ε) h k
    ((2 * C_far / Real.sqrt (ε + h) + 2 * M / (ε + h)) * ((-h) * |k|))
    (by simpa using hah_hi) (by simpa using ha_hi) hah_lo ha_lo (by simpa using hInt)
  rw [abs_of_neg hh]
  exact hcollapse

end QIQTH.HeatResidualBound

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms far_only_sliver_bound
#print axioms far_only_sliver_bound_hyp_satisfiable
#print axioms hcross_split_bound_hpos_kneg
#print axioms hcross_split_bound_hneg_kpos
#print axioms hcross_split_bound_hneg_kneg
end AxiomChecks
