/-
  HCrossLargeShiftRegime — the degenerate `|h| ≥ ε` regime of the integrated `hCross` mixed-second-
  difference estimate, completing the FULL `h ∈ ℝ` coverage left open by J4-965.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE brick completing the shift-magnitude coverage of the hCross sliver estimate.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise
  hypothesis, no existing banked file edited.

  ## WHAT J4-965 LEFT OPEN.  `HCrossNegativeQuadrants.lean` (J4-965) completed all four SIGN quadrants
  of the live `hCross` binder EXCEPT the degenerate regime `|h| ≥ ε`: for `h ≤ −ε` the moved diagonal
  `u+h` sits at or LEFT of the lower window anchor `u−ε`, so the far/near/zero sliver split (used in
  every completed quadrant, all of which need `−ε < h`) no longer applies — the far envelope
  `(u+h−s)^{−1/2}` is anchored at `u+h ≤ u−ε ≤ s`, a nonpositive base.  This file supplies the missing
  regime, generalized to ALL `|h| ≥ ε` (both signs), and thereby closes the live binder's `h`-quantifier
  for every `h ∈ ℝ` (gpt-5.6-sol high scope check 2026-08-21: SOUND; the case split
  {`|h|≥ε`, `h>0`, `−ε<h<0`, `h=0`} is exhaustive; the uniform bound is the abstract cheap input).

  ## THE CONSTRUCTION (uniform bound — no diagonal analysis at all).  The banked sign-AND-magnitude-
  agnostic collapse `mixed_second_diff_frozen_reduction_integrated` (J4-927) reduces the mixed second
  difference to a SINGLE sliver integral of `D(s) := Φ(u+h,s) − Φ(u,s)`, `Φ(c,s) := ∫ z, A(c−s) x z·B s z y`,
  WITHOUT any positivity or magnitude bound on `h,k`.  The diagonal "singularity" of J4-926 lived only in
  the DIVIDED difference `D/h ~ 1/h`; `D` ITSELF is uniformly bounded (`|Φ| ≤ M` ⟹ `|D| ≤ 2M`) — no
  cancellation envelope needed.  Hence
      `|∫ s in (u−ε)..(u−ε+k), D s|  ≤  2M·|k|`   (`norm_integral_le_of_norm_le_const`),
  and since `ε ≤ |h|` the coefficient `2M` is absorbed by the RHS's `|h|`:
      `2M·|k| ≤ (2M/ε)·(|h|·|k|) ≤ (2·C_far/√ε + 2·M/ε)·(|h|·|k|)`,
  landing the EXACT same constant `L = 2·C_far/√ε + 2·M/ε` used in every other regime.  → `uniform_sliver_bound`.
  The far-envelope constant `C_far` is carried inert (`≥ 0`) purely to keep `L` identical across regimes.

  ⚠  STILL NOT `a₁ = R/6`, and does NOT change the top-level conditional status.  The regime is
  carrier-conditional on the SAME sup-boundedness `|Φ| ≤ M` (cheap, true for the concrete witness — the
  `H_near`-style datum, here on the whole sliver) as the other branches; the concrete `H_far` cancellation
  envelope of the `|h| < ε` branches stays the OPEN chart wall.  So this closes the last shift-magnitude
  gap in the campaign's own hCross infrastructure without discharging any of `{hDuhamel, hDConv, hCConv}`.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import Mathlib
import QIQTH.HeatDuhamel
import QIQTH.HCrossIntegratedSplit

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatDuhamel
open scoped Interval

namespace QIQTH.HeatResidualBound

/-! ###############################################################################
    ### §A — the `|h| ≥ ε` uniform sliver bound (no diagonal, no envelope).
    ############################################################################### -/

/-- **★★ `uniform_sliver_bound` — the `|h| ≥ ε` sliver bound (uniform, no diagonal).**  For ANY
    `D : ℝ → ℝ`, `0 < ε`, `ε ≤ |h|`, `0 ≤ C_far, M`, interval-integrability of `D` on the sliver, and
    the UNIFORM bound
      • (H_bnd)  `|D s| ≤ 2·M`   for `s ∈ Ι (u−ε) (u−ε+k)`  (`Set.uIoc`),
    the sliver integral is bounded WITHOUT any far/near/zero pieces and WITHOUT any sign assumption on
    `h, k`:
        `|∫ s in (u−ε)..(u−ε+k), D s|  ≤  (2·C_far/√ε + 2·M/ε)·(|h|·|k|)`.
    Route: `norm_integral_le_of_norm_le_const` gives `|∫| ≤ 2M·|k|` (interval length `= |k|`); then
    `ε ≤ |h|` absorbs the `1/ε`: `2M ≤ (2M/ε)·|h|`, and the inert `2·C_far/√ε ≥ 0` term only enlarges
    the RHS.  NOT `a₁ = R/6`. -/
theorem uniform_sliver_bound (D : ℝ → ℝ) (u ε h k C_far M : ℝ)
    (hε : 0 < ε) (hhε : ε ≤ |h|) (hCf : 0 ≤ C_far) (hM : 0 ≤ M)
    (hII : IntervalIntegrable D volume (u - ε) (u - ε + k))
    (H_bnd : ∀ s ∈ Set.uIoc (u - ε) (u - ε + k), |D s| ≤ 2 * M) :
    |∫ s in (u - ε)..(u - ε + k), D s| ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (|h| * |k|) := by
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  -- crude uniform-constant bound on the sliver integral.
  rw [← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u - ε) (b := u - ε + k) (C := 2 * M) (f := D)
    (fun s hs => by rw [Real.norm_eq_abs]; exact H_bnd s hs)
  have hlen : (u - ε + k) - (u - ε) = k := by ring
  rw [hlen] at hb
  -- hb : ‖∫ s in (u−ε)..(u−ε+k), D s‖ ≤ 2 * M * |k|
  refine le_trans hb ?_
  have hk0 : (0 : ℝ) ≤ |k| := abs_nonneg k
  -- absorb 2M into (2M/ε)·|h| using ε ≤ |h|.
  have step1 : 2 * M * |k| ≤ (2 * M / ε) * (|h| * |k|) := by
    have hcoef : 2 * M ≤ (2 * M / ε) * |h| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]
      nlinarith [hM, hhε]
    calc 2 * M * |k| ≤ ((2 * M / ε) * |h|) * |k| := mul_le_mul_of_nonneg_right hcoef hk0
      _ = (2 * M / ε) * (|h| * |k|) := by ring
  have step2 : (2 * M / ε) * (|h| * |k|)
      ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (|h| * |k|) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (abs_nonneg h) (abs_nonneg k))
    have : (0 : ℝ) ≤ 2 * C_far / Real.sqrt ε := div_nonneg (by linarith) hsε.le
    linarith
  linarith [step1, step2]

/-- **Non-vacuity of `uniform_sliver_bound`, with TEETH.**  The full bundle is jointly satisfiable at the
    NONZERO constant witness `D ≡ 2^{−1/2}` (`u=0, ε=1, h=−2, k=−2, C_far=1, M=1/2`): `ε = 1 ≤ 2 = |−2|`,
    and the uniform bound is genuinely EXERCISED — `|2^{−1/2}| = 2^{−1/2} ≈ 0.707 ≤ 1 = 2·M`, a nonzero
    value strictly below the bound, NOT `0 ≤ 0`.  `D` constant ⟹ interval-integrable.  NOT `a₁ = R/6`. -/
theorem uniform_sliver_bound_hyp_satisfiable :
    ∃ (D : ℝ → ℝ) (u ε h k C_far M : ℝ),
      0 < ε ∧ ε ≤ |h| ∧ 0 ≤ C_far ∧ 0 ≤ M ∧
      IntervalIntegrable D volume (u - ε) (u - ε + k) ∧
      (∀ s ∈ Set.uIoc (u - ε) (u - ε + k), |D s| ≤ 2 * M) := by
  refine ⟨fun _ => (2 : ℝ) ^ (-(1 : ℝ) / 2), 0, 1, -2, -2, 1, 1 / 2,
    one_pos, ?_, one_pos.le, by norm_num, ?_, ?_⟩
  · rw [show |(-2 : ℝ)| = 2 from by norm_num]; norm_num
  · exact (continuous_const).intervalIntegrable _ _
  · intro s _
    show |(2 : ℝ) ^ (-(1 : ℝ) / 2)| ≤ 2 * (1 / 2)
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    have h1 : (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    linarith

/-! ###############################################################################
    ### §B — the frozen `hCross` binder, regime `ε ≤ |h|` (any `k`).
    ############################################################################### -/

set_option maxHeartbeats 800000 in
/-- **★★★ `hcross_split_bound_habs_ge_eps` — the live `hCross` binder for `ε ≤ |h|` (any `k`).**  The
    degenerate regime uncovered by J4-965's four sign quadrants (all of which need `−ε < h`): for
    `ε ≤ |h|` the sliver needs NO far/near/zero split — only the UNIFORM sup-bound `|D| ≤ 2M` on the
    sliver (the `H_near`-style datum, here on the whole window), which the large-`|h|` RHS absorbs.
    Route: `uniform_sliver_bound` bounds the sliver of the inner τ-shift difference;
    `mixed_second_diff_frozen_reduction_integrated` (sign/magnitude-agnostic) collapses the mixed second
    difference onto it.  The RHS carries `|h|·|k|` directly — no sign rewriting.  NOT `a₁ = R/6`. -/
theorem hcross_split_bound_habs_ge_eps {n : ℕ}
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (u ε h k C_far M : ℝ)
    (hε : 0 < ε) (hhε : ε ≤ |h|) (hCf : 0 ≤ C_far) (hM : 0 ≤ M)
    (hah_hi : IntervalIntegrable
      (fun s => ∫ z, A (u + h - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (ha_hi : IntervalIntegrable
      (fun s => ∫ z, A (u - s) x z * B s z y) volume (u - ε) (u - ε + k))
    (hah_lo : IntervalIntegrable (fun s => ∫ z, A (u + h - s) x z * B s z y) volume 0 (u - ε))
    (ha_lo : IntervalIntegrable (fun s => ∫ z, A (u - s) x z * B s z y) volume 0 (u - ε))
    (H_bnd : ∀ s ∈ Set.uIoc (u - ε) (u - ε + k),
        |(∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y)| ≤ 2 * M) :
    |heatConvFrozen A B (u + h) (u - ε + k) x y - heatConvFrozen A B (u + h) (u - ε) x y
        - heatConvFrozen A B u (u - ε + k) x y + heatConvFrozen A B u (u - ε) x y|
      ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (|h| * |k|) := by
  set D : ℝ → ℝ :=
    fun s => (∫ z, A (u + h - s) x z * B s z y) - (∫ z, A (u - s) x z * B s z y) with hDdef
  have hIID : IntervalIntegrable D volume (u - ε) (u - ε + k) := hah_hi.sub ha_hi
  have hslive := uniform_sliver_bound D u ε h k C_far M hε hhε hCf hM hIID
    (by simpa only [hDdef] using H_bnd)
  have hcollapse := mixed_second_diff_frozen_reduction_integrated A B x y u (u - ε) h k
    ((2 * C_far / Real.sqrt ε + 2 * M / ε) * (|h| * |k|))
    (by simpa using hah_hi) (by simpa using ha_hi) hah_lo ha_lo
    (by simpa only [hDdef] using hslive)
  exact hcollapse

end QIQTH.HeatResidualBound

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms uniform_sliver_bound
#print axioms uniform_sliver_bound_hyp_satisfiable
#print axioms hcross_split_bound_habs_ge_eps
end AxiomChecks
