/-
  WidthFree — J4-633: the `hlam8` AUDIT — the frozen-side `G_{8s}` landing pin of the
  `FrozenTransportBridge` triangle is a SPURIOUS pin, and is DELETED here by width-parametrizing
  the bridge Prop.  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`;
  proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★ THE AUDIT VERDICT (all three questions answered YES / SPURIOUS / GOES THROUGH):

  (1) `gaussDdim_le_of_width_le` — the CLEAN widening `c ≤ d ⟹ G_{cτ}(v) ≤ √(d/c)ⁿ·G_{dτ}(v)`
      IS true in the repo's normalization (`heatKernel1D t x = (4πt)^{−1/2}·e^{−x²/(4t)}`,
      `gaussDdim = ∏ₖ heatKernel1D`), with NO upper-ratio restriction: it is EXACTLY the banked
      normalized chart comparison `gaussDdim_le_gaussDdim_chart` at `w = v` (prefactor ratio
      `√(d/c)ⁿ`; the exponential factor `e^{−|v|²(d−c)/(4cd)} ≤ 1` is what the chart lemma's
      `hnorm` trivializes to at `w = v`).  ⚠ DIRECTION: narrow ≤ const·wide ONLY — the reverse
      (`wide ≤ const·narrow`) is FALSE at large `|v|` and is nowhere used.
  (2) The banked `gaussDdim_widen_le`'s `d ≤ 4c` restriction was itself a SPURIOUS pin — it only
      bought the clean constant `2ⁿ`; `gaussDdim_widen_le_ratio` recovers it at ANY ratio bound
      `d ≤ ρ·c` with constant `√ρⁿ`.
  (3) The sufficiency chain (`tail_slice_of_pointwise` → `smoke_bridge_verdict`) does NOT
      genuinely pin `8`: the C–K composition `G_{2(t−s)} ∗ G_{ws} = G_{2t+(w−2)s}` is exact at
      any width; the final widening `G_{2t+(w−2)s} ≤ √(w/2)ⁿ·G_{wt}` needs only `w ≥ 2` (ratio
      `wt/(2t+(w−2)s) ≤ w/2` since `2t+(w−2)s ≥ 2t`); the `H`-side width `2` is the MODEL
      (parametrix) side, independent of the tail width.  Every `8` in the chain is a
      `w`-dependent CONSTANT, not a structural constraint.

  ★★ THE DELETION.  `FrozenTransportBridgeW w` (the bridge Prop landing at `G_{ws}`) at
  `w := max 8 lam`:
    ▸ the WHITENED tail (`white_tail_O_s`, width `lam = whiteLam`, opaque `C₀`) widens INTO
      `G_{ws}` (`lam ≤ w`, clean lemma, constant `√(w/lam)ⁿ`);
    ▸ the FROZEN tail (`frozenColumn_tail_O_s`, width `8`) widens INTO `G_{ws}` (`8 ≤ w`,
      constant `√(w/8)ⁿ`);
    ▸ triangle ⟹ `frozenTransportBridgeW_of_tails` — the bridge Prop at `max 8 lam` with NO
      `lam ≤ 8` hypothesis;
    ▸ the width-general sufficiency `smoke_bridge_verdict_w` (slice + corrHigher consumption at
      any `w ≥ 8`) re-runs the certified J4-616 transfer landing at `G_{wt}`;
    ▸ ★ `white_transport_bridge_unconditional` — the J4-632 feeder with hEmeas discharged
      (banked `WhiteS1C.white_tail_O_s_unconditional`) AND `hlam8` DELETED: for every `κ ≤ 0`,
      compact `K ⊆ B̄(0,R)` (`n > 0`) and frozen data there ARE a fat gate + radii +
      `lam = whiteLam ≥ 2` with `FrozenTransportBridgeW (max 8 lam)` holding OUTRIGHT;
    ▸ ★ `white_corrHigher_unconditional` — the capstone-shaped bounded-cRem O(t²) API at the
      whitened defect, at landing width `max 8 lam`, with NO width residue and NO measurability
      residue.

  ⚠ HONEST FRAMING.  `a₁ = R/6` remains CONDITIONAL: the flat tower is closed and non-vacuous;
  the curved side still owes `K1TransportBudget` (the k = 1 thread — a SEPARATE owed Prop), the
  fat-K carrier piles, the capstone co-instantiation at the WHITENED witness (the capstone is
  pinned at `vanVleckGatedWitness`, and its corrHigher slot consumes a FIXED-width landing —
  the width-`(max 8 lam)` API here is the supplier shape, the capstone-side re-thread is a
  follow-on), and the prior piles.  Nothing here proves anything about the coefficient.
  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.WhiteS1C

open Finset Filter Topology MeasureTheory
open scoped Interval
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.AlphaLevi QIQTH.FrozenWire QIQTH.FrozenColumn
open QIQTH.FrozenK2 QIQTH.FrozenK2Sharp QIQTH.CoInstSmoke QIQTH.BridgeDefect QIQTH.BridgeWidth
open QIQTH.WhiteGated QIQTH.WhiteAnnulus QIQTH.WhiteBridge QIQTH.WhiteS1C

namespace QIQTH.WidthFree

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. ★ The CLEAN widening — no ratio restriction (audit answer (1)/(2)). -/

/-- **★ `gaussDdim_le_of_width_le` — the clean width widening, scaled form.**  For `0 < c ≤ d`
    and any `τ > 0`: `G_{cτ}(v) ≤ √(d/c)ⁿ·G_{dτ}(v)` — NO upper-ratio restriction.  Direction
    checked: NARROW ≤ const·WIDE (the reverse is false at large `|v|`).  This is the banked
    normalized chart comparison `gaussDdim_le_gaussDdim_chart` at `w = v` (where `hnorm`
    trivializes); the banked `gaussDdim_widen_le`'s `d ≤ 4c` restriction was spurious. -/
theorem gaussDdim_le_of_width_le (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    gaussDdim (c * τ) v ≤ Real.sqrt (d / c) ^ n * gaussDdim (d * τ) v :=
  QIQTH.HeatResidualBound.gaussDdim_le_gaussDdim_chart hc (lt_of_lt_of_le hc hcd) hτ
    (mul_le_mul_of_nonneg_right hcd (rncRadialSq_nonneg v))

/-- **The clean widening, unscaled form**: `c ≤ d ⟹ G_c(v) ≤ √(d/c)ⁿ·G_d(v)`. -/
theorem gaussDdim_le_of_width_le' (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) (v : Point n) :
    gaussDdim c v ≤ Real.sqrt (d / c) ^ n * gaussDdim d v := by
  have h := gaussDdim_le_of_width_le c d hc hcd (τ := 1) one_pos v
  rwa [mul_one, mul_one] at h

/-- **`gaussDdim_widen_le_ratio` — the ratio-bounded widening at ANY ratio `ρ`.**
    `c ≤ d ≤ ρ·c ⟹ G_c(v) ≤ √ρⁿ·G_d(v)` — the banked `gaussDdim_widen_le` is the `ρ = 4`
    (`√ρⁿ = 2ⁿ`) special case; the restriction to ratio ≤ 4 bought only the clean constant. -/
theorem gaussDdim_widen_le_ratio (c d ρ : ℝ) (hc : 0 < c) (hcd : c ≤ d) (hρ : d ≤ ρ * c)
    (v : Point n) :
    gaussDdim c v ≤ Real.sqrt ρ ^ n * gaussDdim d v := by
  refine (gaussDdim_le_of_width_le' c d hc hcd v).trans
    (mul_le_mul_of_nonneg_right ?_ (QIQTH.ResidueBound.gaussDdim_nonneg _ _))
  have hdc : d / c ≤ ρ := (div_le_iff₀ hc).mpr hρ
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hdc) n

/-! ### 2. ★ The width-parametric bridge Prop. -/

/-- **★ `FrozenTransportBridgeW` — the width-parametric frozen-vs-transport bridge Prop.**
    The k ≥ 2 Levi tails of the transport defect `E` and the frozen defect `F` differ by
    `O(s)·G_{ws}` on the center column, `s ∈ (0,1]`.  `FrozenTransportBridge = FrozenTransportBridgeW 8`
    (definitional, gate below); the width slot is what deletes the `hlam8` residue: both tails
    widen INTO `G_{(max 8 lam)·s}` with NO alignment condition. -/
def FrozenTransportBridgeW (w : ℝ) (E F : ℝ → Point n → Point n → ℝ) : Prop :=
  ∃ C_B : ℝ, 0 ≤ C_B ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
    |(leviSeries E s p 0 + E s p 0) - (leviSeries F s p 0 + F s p 0)|
      ≤ C_B * (s * gaussDdim (w * s) (p - 0))

/-- **Gate: the width-parametric Prop at `w = 8` IS the banked bridge Prop** (definitional
    equality of the two `Prop`s — nothing is re-scoped). -/
theorem frozenTransportBridgeW_eight_iff (E F : ℝ → Point n → Point n → ℝ) :
    FrozenTransportBridgeW 8 E F ↔ FrozenTransportBridge E F := Iff.rfl

/-- **Width monotonicity of the bridge Prop**: `0 < w ≤ w' ⟹ (W w ⟹ W w')` — one clean
    widening, cost `√(w'/w)ⁿ` folded into the constant. -/
theorem frozenTransportBridgeW_mono {w w' : ℝ} (hw : 0 < w) (hww : w ≤ w')
    (E F : ℝ → Point n → Point n → ℝ) (h : FrozenTransportBridgeW w E F) :
    FrozenTransportBridgeW w' E F := by
  obtain ⟨C_B, hCB, hb⟩ := h
  refine ⟨C_B * Real.sqrt (w' / w) ^ n, mul_nonneg hCB (by positivity),
    fun s p hs hs1 => ?_⟩
  have hwide : gaussDdim (w * s) (p - 0)
      ≤ Real.sqrt (w' / w) ^ n * gaussDdim (w' * s) (p - 0) :=
    gaussDdim_le_of_width_le w w' hw hww hs (p - 0)
  calc |(leviSeries E s p 0 + E s p 0) - (leviSeries F s p 0 + F s p 0)|
      ≤ C_B * (s * gaussDdim (w * s) (p - 0)) := hb s p hs hs1
    _ ≤ C_B * (s * (Real.sqrt (w' / w) ^ n * gaussDdim (w' * s) (p - 0))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwide hs.le) hCB
    _ = (C_B * Real.sqrt (w' / w) ^ n) * (s * gaussDdim (w' * s) (p - 0)) := by ring

/-! ### 3. ★★ The max-width bridge from the two tails — `hlam8` deleted. -/

/-- **★★ `frozenTransportBridgeW_of_tails` — BOTH tails widen into `G_{(max 8 lam)·s}`.**
    Given the whitened k ≥ 2 tail at ANY width `lam > 0` (`O(s)·G_{lam·s}`), the bridge Prop
    holds against the frozen defect at landing width `w = max 8 lam` — the whitened side
    widens by `lam ≤ w`, the frozen side (banked `frozenColumn_tail_O_s`, width 8) by
    `8 ≤ w`, each via the clean no-ratio-restriction lemma.  NO `lam ≤ 8` hypothesis. -/
theorem frozenTransportBridgeW_of_tails (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r)
    (E : ℝ → Point n → Point n → ℝ) (lam C_os : ℝ) (hlam : 0 < lam) (hCos : 0 ≤ C_os)
    (htail : ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |leviSeries E s p 0 + E s p 0| ≤ C_os * (s * gaussDdim (lam * s) (p - 0))) :
    FrozenTransportBridgeW (max 8 lam) E (frozenDefectKernel K r) := by
  obtain ⟨C_f, hCf, hf⟩ := frozenColumn_tail_O_s (n := n) K r hK hr
  set w : ℝ := max 8 lam with hwdef
  have hw8 : (8 : ℝ) ≤ w := le_max_left _ _
  have hwlam : lam ≤ w := le_max_right _ _
  refine ⟨C_os * Real.sqrt (w / lam) ^ n + C_f * Real.sqrt (w / 8) ^ n,
    add_nonneg (mul_nonneg hCos (by positivity)) (mul_nonneg hCf (by positivity)),
    fun s p hs hs1 => ?_⟩
  have hwideE : gaussDdim (lam * s) (p - 0)
      ≤ Real.sqrt (w / lam) ^ n * gaussDdim (w * s) (p - 0) :=
    gaussDdim_le_of_width_le lam w hlam hwlam hs (p - 0)
  have hwideF : gaussDdim (8 * s) (p - 0)
      ≤ Real.sqrt (w / 8) ^ n * gaussDdim (w * s) (p - 0) :=
    gaussDdim_le_of_width_le 8 w (by norm_num) hw8 hs (p - 0)
  calc |(leviSeries E s p 0 + E s p 0)
          - (leviSeries (frozenDefectKernel K r) s p 0 + frozenDefectKernel K r s p 0)|
      ≤ |leviSeries E s p 0 + E s p 0|
          + |leviSeries (frozenDefectKernel K r) s p 0 + frozenDefectKernel K r s p 0| := by
        rw [sub_eq_add_neg]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_neg]
    _ ≤ C_os * (s * gaussDdim (lam * s) (p - 0)) + C_f * (s * gaussDdim (8 * s) (p - 0)) :=
        add_le_add (htail s p hs hs1) (hf s p hs hs1)
    _ ≤ C_os * (s * (Real.sqrt (w / lam) ^ n * gaussDdim (w * s) (p - 0)))
          + C_f * (s * (Real.sqrt (w / 8) ^ n * gaussDdim (w * s) (p - 0))) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwideE hs.le) hCos)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwideF hs.le) hCf)
    _ = (C_os * Real.sqrt (w / lam) ^ n + C_f * Real.sqrt (w / 8) ^ n)
          * (s * gaussDdim (w * s) (p - 0)) := by ring

/-! ### 4. ★ The width-general sufficiency — the J4-616 consumer chain at width `w` (audit
    answer (3): no genuine 8-pin; every step is a `w`-dependent constant). -/

/-- **`tail_slice_of_pointwise_w` — the banked slice budget at general tail width `w ≥ 2`.**
    ANY center-column kernel `Φ` with `|Φ(s,p)| ≤ C_os·s·G_{ws}(p)` feeds the linear slice
    budget against every width-2-Gaussian-dominated slice kernel `H`: the C–K composition
    `G_{2(t−s)} ∗ G_{ws} = G_{2t+(w−2)s}` is exact, and the widening to `G_{wt}` needs only
    `2t+(w−2)s ≤ wt` (from `w ≥ 2`, `s < t`) at ratio `≤ w/2` (since `2t+(w−2)s ≥ 2t`) —
    constant `√(w/2)ⁿ`.  The `H`-side width 2 is the MODEL side, independent of `w`. -/
theorem tail_slice_of_pointwise_w (w : ℝ) (hw2 : 2 ≤ w)
    (Φ : ℝ → Point n → ℝ) (C_os : ℝ) (hCos : 0 ≤ C_os)
    (hΦ : ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |Φ s p| ≤ C_os * (s * gaussDdim (w * s) (p - 0)))
    (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ) (hCH : 0 ≤ C_H)
    (hH : ∀ (a : ℝ) (ζ : Point n), 0 < a →
      |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) :
    ∀ (t s : ℝ), 0 < s → s < t → s ≤ 1 →
      ‖∫ ζ, H (t - s) 0 ζ * Φ s ζ‖
        ≤ (C_H * (Real.sqrt (w / 2) ^ n * C_os)) * (s * gaussDdim (w * t) (0 : Point n)) := by
  intro t s hs hst hs1
  have hw0 : (0 : ℝ) < w := lt_of_lt_of_le two_pos hw2
  have hts : 0 < t - s := by linarith
  have hws : 0 < w * s := mul_pos hw0 hs
  have hg_int : Integrable (fun ζ : Point n =>
      (C_H * C_os * s)
        * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
            * gaussDdim (w * s) (ζ - (0 : Point n)))) volume :=
    (gaussDdim_mul_integrable (2 * (t - s)) (w * s) (0 : Point n) (0 : Point n)).const_mul _
  have hpt : ∀ ζ : Point n,
      ‖H (t - s) 0 ζ * Φ s ζ‖
        ≤ (C_H * C_os * s)
            * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
                * gaussDdim (w * s) (ζ - (0 : Point n))) := by
    intro ζ
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hH (t - s) ζ hts
    have h2 := hΦ s ζ hs hs1
    have hGnn : (0 : ℝ) ≤ gaussDdim (2 * (t - s)) ((0 : Point n) - ζ) :=
      QIQTH.ResidueBound.gaussDdim_nonneg _ _
    calc |H (t - s) 0 ζ| * |Φ s ζ|
        ≤ (C_H * gaussDdim (2 * (t - s)) ((0 : Point n) - ζ))
            * (C_os * (s * gaussDdim (w * s) (ζ - (0 : Point n)))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCH hGnn)
      _ = (C_H * C_os * s)
            * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
                * gaussDdim (w * s) (ζ - (0 : Point n))) := by ring
  have hwide : gaussDdim (2 * (t - s) + w * s) ((0 : Point n) - 0)
      ≤ Real.sqrt (w / 2) ^ n * gaussDdim (w * t) ((0 : Point n) - 0) :=
    gaussDdim_widen_le_ratio (2 * (t - s) + w * s) (w * t) (w / 2)
      (by linarith)
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hw2) hts.le])
      (by nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hw2) hw0.le) hs.le]) _
  calc ‖∫ ζ, H (t - s) 0 ζ * Φ s ζ‖
      ≤ ∫ ζ, (C_H * C_os * s)
          * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
              * gaussDdim (w * s) (ζ - (0 : Point n))) :=
        MeasureTheory.norm_integral_le_of_norm_le hg_int (ae_of_all _ hpt)
    _ = (C_H * C_os * s)
          * ∫ ζ, gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
              * gaussDdim (w * s) (ζ - (0 : Point n)) :=
        integral_const_mul _ _
    _ = (C_H * C_os * s) * gaussDdim (2 * (t - s) + w * s) ((0 : Point n) - 0) := by
        rw [QIQTH.GaussianConvolution.gaussDdim_conv (2 * (t - s)) (w * s)
          (by linarith) hws (0 : Point n) (0 : Point n)]
    _ ≤ (C_H * C_os * s) * (Real.sqrt (w / 2) ^ n * gaussDdim (w * t) ((0 : Point n) - 0)) :=
        mul_le_mul_of_nonneg_left hwide (by positivity)
    _ = (C_H * (Real.sqrt (w / 2) ^ n * C_os)) * (s * gaussDdim (w * t) (0 : Point n)) := by
        rw [sub_zero]
        ring

/-- **`bridged_tail_pointwise_w` — width-`w` bridge ⟹ the transport tail has the width-`w`
    pointwise shape** (`w ≥ 8`: the frozen tail widens `8 → w`, then triangle). -/
theorem bridged_tail_pointwise_w (P : FatFrozenPackage n) (E : ℝ → Point n → Point n → ℝ)
    {w : ℝ} (hw8 : 8 ≤ w)
    (hB : FrozenTransportBridgeW w E (frozenDefectKernel P.κ P.rS)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |leviSeries E s p 0 + E s p 0| ≤ C * (s * gaussDdim (w * s) (p - 0)) := by
  obtain ⟨C_B, hCB, hb⟩ := hB
  obtain ⟨C_os, hCos, htail⟩ := frozenColumn_tail_O_s (n := n) P.κ P.rS P.hκ.le P.hrS.le
  refine ⟨C_B + C_os * Real.sqrt (w / 8) ^ n,
    add_nonneg hCB (mul_nonneg hCos (by positivity)), fun s p hs hs1 => ?_⟩
  have hwideF : gaussDdim (8 * s) (p - 0)
      ≤ Real.sqrt (w / 8) ^ n * gaussDdim (w * s) (p - 0) :=
    gaussDdim_le_of_width_le 8 w (by norm_num) hw8 hs (p - 0)
  calc |leviSeries E s p 0 + E s p 0|
      = |((leviSeries E s p 0 + E s p 0)
            - (leviSeries (frozenDefectKernel P.κ P.rS) s p 0
                + frozenDefectKernel P.κ P.rS s p 0))
          + (leviSeries (frozenDefectKernel P.κ P.rS) s p 0
              + frozenDefectKernel P.κ P.rS s p 0)| := by congr 1; ring
    _ ≤ |(leviSeries E s p 0 + E s p 0)
            - (leviSeries (frozenDefectKernel P.κ P.rS) s p 0
                + frozenDefectKernel P.κ P.rS s p 0)|
          + |leviSeries (frozenDefectKernel P.κ P.rS) s p 0
              + frozenDefectKernel P.κ P.rS s p 0| := abs_add_le _ _
    _ ≤ C_B * (s * gaussDdim (w * s) (p - 0))
          + C_os * (s * gaussDdim (8 * s) (p - 0)) :=
        add_le_add (hb s p hs hs1) (htail s p hs hs1)
    _ ≤ C_B * (s * gaussDdim (w * s) (p - 0))
          + C_os * (s * (Real.sqrt (w / 8) ^ n * gaussDdim (w * s) (p - 0))) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwideF hs.le) hCos)
    _ = (C_B + C_os * Real.sqrt (w / 8) ^ n) * (s * gaussDdim (w * s) (p - 0)) := by ring

/-- **★★ `smoke_bridge_verdict_w` — THE CERTIFIED TRANSFER AT GENERAL WIDTH `w ≥ 8`**: the
    width-`w` bridge Prop ⟹ the capstone-shaped bounded-cRem O(t²) API for the transport
    k ≥ 2 tail, landing at `G_{wt}`.  Width-general replay of the J4-616 `smoke_bridge_verdict`
    — the equality shape, the O(t²) assembly and BOUNDED `cRem` all go through with
    `w`-dependent constants only.  ⚠ NOT `a₁ = R/6`; `K1TransportBudget` stays owed. -/
theorem smoke_bridge_verdict_w (P : FatFrozenPackage n) (E : ℝ → Point n → Point n → ℝ)
    {w : ℝ} (hw8 : 8 ≤ w)
    (hB : FrozenTransportBridgeW w E (frozenDefectKernel P.κ P.rS)) :
    ∃ C_t : ℝ, 0 ≤ C_t ∧
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (ζ : Point n), 0 < a →
          |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        ∀ (pref t : ℝ), 0 < t → t ≤ 1 → pref ≠ 0 →
          (heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0
            = pref * (t ^ 2
                * (heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0
                    / (pref * t ^ 2))))
          ∧ |heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0|
            ≤ (C_H * C_t * gaussDdim (w * t) (0 : Point n)) * t ^ 2
          ∧ |heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0 / (pref * t ^ 2)|
            ≤ (C_H * C_t * gaussDdim (w * t) (0 : Point n)) / |pref| := by
  have hw2 : (2 : ℝ) ≤ w := le_trans (by norm_num) hw8
  obtain ⟨C, hC, hpt⟩ := bridged_tail_pointwise_w P E hw8 hB
  refine ⟨Real.sqrt (w / 2) ^ n * C, mul_nonneg (by positivity) hC,
    fun H C_H hCH hH hH0 pref t ht ht1 hpref => ?_⟩
  have hsl := tail_slice_of_pointwise_w w hw2 (fun s p => leviSeries E s p 0 + E s p 0)
    C hC hpt H C_H hCH hH
  set Kt : ℝ := C_H * (Real.sqrt (w / 2) ^ n * C) * gaussDdim (w * t) (0 : Point n)
    with hKtdef
  have hKt0 : 0 ≤ Kt := by
    rw [hKtdef]
    exact mul_nonneg (mul_nonneg hCH (mul_nonneg (by positivity) hC))
      (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  -- the LINEAR slice budget, at EVERY s ∈ Ι 0 t (endpoint s = t via H(0,0,·) = 0)
  have hslice : ∀ s ∈ Ι (0 : ℝ) t,
      ‖∫ ζ, H (t - s) 0 ζ
          * (fun σ p q => leviSeries E σ p q + E σ p q) s ζ 0‖
        ≤ Kt * ((t - s) + s) + 0 * Real.sqrt s := by
    intro s hs
    have hs' : s ∈ Set.Ioc (0 : ℝ) t := by rwa [Set.uIoc_of_le ht.le] at hs
    rcases lt_or_eq_of_le hs'.2 with hst | hseq
    · have hb := hsl t s hs'.1 hst (le_trans hs'.2 ht1)
      calc ‖∫ ζ, H (t - s) 0 ζ * (fun σ p q => leviSeries E σ p q + E σ p q) s ζ 0‖
          = ‖∫ ζ, H (t - s) 0 ζ * (leviSeries E s ζ 0 + E s ζ 0)‖ := rfl
        _ ≤ (C_H * (Real.sqrt (w / 2) ^ n * C))
              * (s * gaussDdim (w * t) (0 : Point n)) := hb
        _ = Kt * s := by rw [hKtdef]; ring
        _ ≤ Kt * ((t - s) + s) + 0 * Real.sqrt s := by
            have : Kt * s ≤ Kt * ((t - s) + s) :=
              mul_le_mul_of_nonneg_left (by linarith) hKt0
            linarith
    · have hzero : (fun ζ => H (t - s) 0 ζ
          * (fun σ p q => leviSeries E σ p q + E σ p q) s ζ 0) = fun _ => (0 : ℝ) := by
        funext ζ
        rw [hseq, sub_self, hH0 ζ, zero_mul]
      rw [hzero, integral_zero, norm_zero]
      have h1 : Kt * ((t - s) + s) + 0 * Real.sqrt s = Kt * t := by ring
      rw [h1]
      exact mul_nonneg hKt0 ht.le
  obtain ⟨heq, hbd, hrem⟩ := corrHigher_bounded_of_slice_sqrt H
    (fun σ p q => leviSeries E σ p q + E σ p q) pref Kt 0 t ht hpref le_rfl hslice
  refine ⟨heq, ?_, ?_⟩
  · calc |heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0|
        ≤ Kt * t ^ 2 + 0 * (t * Real.sqrt t) := hbd
      _ = (C_H * (Real.sqrt (w / 2) ^ n * C) * gaussDdim (w * t) (0 : Point n)) * t ^ 2 := by
          rw [hKtdef]; ring
  · calc |heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0 / (pref * t ^ 2)|
        ≤ (Kt + 0 / Real.sqrt t) / |pref| := hrem
      _ = (C_H * (Real.sqrt (w / 2) ^ n * C) * gaussDdim (w * t) (0 : Point n)) / |pref| := by
          rw [zero_div, add_zero, hKtdef]

/-! ### 5. ★★ The whitened feeders — `hlam8` DELETED. -/

/-- **★ `white_transport_bridgeW` — the width-parametric bridge at the whitened defect,
    NO `hlam8`.**  Same hypotheses as `WhiteBridge.white_transport_bridge` MINUS `hlam8`:
    the landing width is `max 8 lam` instead of the frozen chain's pinned `8`. -/
theorem white_transport_bridgeW (K₀ r : ℝ) (hK₀ : K₀ ≤ 0) (hr : 0 ≤ r)
    (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    FrozenTransportBridgeW (max 8 lam) (whiteDefectKernel κ hκ hKc S a b)
      (frozenDefectKernel K₀ r) := by
  obtain ⟨C_os, hCos, htail⟩ := white_tail_O_s κ hκ hKc S a b C lam hC hlam2 hpkg hEmeas
  exact frozenTransportBridgeW_of_tails K₀ r hK₀ hr _ lam C_os
    (lt_of_lt_of_le two_pos hlam2) hCos htail

/-- **★★ `white_transport_bridge_unconditional` — THE PAYOFF: the whitened transport bridge
    with the S1/`hEmeas` residue discharged (J4-632) AND the `hlam8` width residue DELETED.**
    For every `κ ≤ 0`, compact `K ⊆ B̄(0,R)` (`n > 0`) and frozen data `(K₀, r)` there ARE a
    fat open gate `S`, radii `0 < a < b`, and the width `lam = whiteLam ≥ 2` such that
    `FrozenTransportBridgeW (max 8 lam) (whiteDefectKernel …) (frozenDefectKernel K₀ r)` holds
    OUTRIGHT — no measurability antecedent, no width antecedent.  The former `hlam8` carried
    input (`lam ≤ 8 ↔ n·C₀² ≤ 3`, opaque `C₀`) is gone: the bridge Prop's landing width is
    now the honest `max 8 lam`.  ⚠ NOT `a₁ = R/6` (see the header framing). -/
theorem white_transport_bridge_unconditional (K₀ r : ℝ) (hK₀ : K₀ ≤ 0) (hr : 0 ≤ r)
    (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)} (hKc : IsCompact Kset)
    (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        FrozenTransportBridgeW (max 8 lam) (whiteDefectKernel κ hκ hKc S a b)
          (frozenDefectKernel K₀ r) := by
  obtain ⟨S, a, b, ha, hab, hfat, lam, hlam2, C_os, hCos, htail⟩ :=
    white_tail_O_s_unconditional hn κ hκ hKc R hKb
  exact ⟨S, a, b, ha, hab, hfat, lam, hlam2,
    frozenTransportBridgeW_of_tails K₀ r hK₀ hr _ lam C_os
      (lt_of_lt_of_le two_pos hlam2) hCos htail⟩

/-- **★★ `white_corrHigher_unconditional` — the capstone-shaped bounded-cRem O(t²) API at the
    whitened defect with NO width and NO measurability residue**: chained through the certified
    width-`w` transfer at `w = max 8 lam ≥ 8`.  The landing Gaussian is `G_{(max 8 lam)·t}` —
    the honest width the whitened chain actually produces.  Residual owed inputs are the
    SEPARATE threads only: `K1TransportBudget`, fat-K carriers, capstone co-instantiation at
    the whitened witness.  ⚠ NOT `a₁ = R/6`. -/
theorem white_corrHigher_unconditional (P : FatFrozenPackage n)
    (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)} (hKc : IsCompact Kset)
    (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        ∃ C_t : ℝ, 0 ≤ C_t ∧
          ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
            (∀ (a' : ℝ) (ζ : Point n), 0 < a' →
              |H a' 0 ζ| ≤ C_H * gaussDdim (2 * a') ((0 : Point n) - ζ)) →
            (∀ ζ : Point n, H 0 0 ζ = 0) →
            ∀ (pref t : ℝ), 0 < t → t ≤ 1 → pref ≠ 0 →
              (heatConv H (fun σ p q => leviSeries (whiteDefectKernel κ hκ hKc S a b) σ p q
                    + whiteDefectKernel κ hκ hKc S a b σ p q) t 0 0
                = pref * (t ^ 2
                    * (heatConv H
                          (fun σ p q => leviSeries (whiteDefectKernel κ hκ hKc S a b) σ p q
                            + whiteDefectKernel κ hκ hKc S a b σ p q) t 0 0
                        / (pref * t ^ 2))))
              ∧ |heatConv H (fun σ p q => leviSeries (whiteDefectKernel κ hκ hKc S a b) σ p q
                    + whiteDefectKernel κ hκ hKc S a b σ p q) t 0 0|
                ≤ (C_H * C_t * gaussDdim (max 8 lam * t) (0 : Point n)) * t ^ 2
              ∧ |heatConv H (fun σ p q => leviSeries (whiteDefectKernel κ hκ hKc S a b) σ p q
                    + whiteDefectKernel κ hκ hKc S a b σ p q) t 0 0 / (pref * t ^ 2)|
                ≤ (C_H * C_t * gaussDdim (max 8 lam * t) (0 : Point n)) / |pref| := by
  obtain ⟨S, a, b, ha, hab, hfat, lam, hlam2, hB⟩ :=
    white_transport_bridge_unconditional P.κ P.rS P.hκ.le P.hrS.le hn κ hκ hKc R hKb
  exact ⟨S, a, b, ha, hab, hfat, lam, hlam2,
    smoke_bridge_verdict_w P _ (le_max_left _ _) hB⟩

/-! ### 6. Non-vacuity / adversarial gates (cp466 discipline). -/

/-- **Gate 1 — the width-parametric bridge Prop is INHABITED at `w = 8`** at the banked
    genuinely-nonzero `bridgeWitnessKernel` against genuinely curved frozen data
    (`κ = −1`, `r = 1/2`) — via the definitional equivalence with the banked Prop. -/
theorem bridgeW_witness_w8 :
    FrozenTransportBridgeW 8 (bridgeWitnessKernel (n := n))
      (frozenDefectKernel (-1) (1 / 2)) :=
  (frozenTransportBridgeW_eight_iff _ _).mpr (bridgeWidth_witness_w2 (n := n))

/-- **Gate 2 — the `w > 8` regime is inhabited** (the regime the `hlam8` deletion exists for):
    the same nonzero witness satisfies the bridge Prop at `w = 12` via one clean widening. -/
theorem bridgeW_witness_wide :
    FrozenTransportBridgeW 12 (bridgeWitnessKernel (n := n))
      (frozenDefectKernel (-1) (1 / 2)) :=
  frozenTransportBridgeW_mono (by norm_num) (by norm_num) _ _ bridgeW_witness_w8

/-- **Gate 3 — the unconditional whitened bridge FIRES at genuinely curved fat data**
    (`n = 2`, `κ = −1`, `K = B̄(0,2)`, frozen `(−1, 1/2)`): a fat gate (`0 ∈ S 0`, open),
    radii `0 < a < b`, and `lam ≥ 2` with the bridge Prop holding OUTRIGHT — the deleted-residue
    feeder is not `∅`-degenerate. -/
theorem white_bridgeW_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        FrozenTransportBridgeW (max 8 lam)
          (whiteDefectKernel (-1 : ℝ) (by norm_num)
            (isCompact_closedBall (0 : Point 2) 2) S a b)
          (frozenDefectKernel (-1) (1 / 2)) := by
  obtain ⟨S, a, b, ha, hab, hfat, lam, hlam2, hB⟩ :=
    white_transport_bridge_unconditional (n := 2) (-1 : ℝ) (1 / 2) (by norm_num)
      (by norm_num) (by norm_num) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
  exact ⟨S, a, b, ha, hab, hfat 0 (Metric.mem_closedBall_self (by norm_num)),
    lam, hlam2, hB⟩

end QIQTH.WidthFree

-- std-3 verification (chk): READ these outputs — no sorryAx, no extra axioms.
#print axioms QIQTH.WidthFree.gaussDdim_le_of_width_le
#print axioms QIQTH.WidthFree.gaussDdim_le_of_width_le'
#print axioms QIQTH.WidthFree.gaussDdim_widen_le_ratio
#print axioms QIQTH.WidthFree.frozenTransportBridgeW_eight_iff
#print axioms QIQTH.WidthFree.frozenTransportBridgeW_mono
#print axioms QIQTH.WidthFree.frozenTransportBridgeW_of_tails
#print axioms QIQTH.WidthFree.tail_slice_of_pointwise_w
#print axioms QIQTH.WidthFree.bridged_tail_pointwise_w
#print axioms QIQTH.WidthFree.smoke_bridge_verdict_w
#print axioms QIQTH.WidthFree.white_transport_bridgeW
#print axioms QIQTH.WidthFree.white_transport_bridge_unconditional
#print axioms QIQTH.WidthFree.white_corrHigher_unconditional
#print axioms QIQTH.WidthFree.bridgeW_witness_w8
#print axioms QIQTH.WidthFree.bridgeW_witness_wide
#print axioms QIQTH.WidthFree.white_bridgeW_witness_gate
