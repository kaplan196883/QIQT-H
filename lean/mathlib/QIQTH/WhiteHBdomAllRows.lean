/-
  WhiteHBdomAllRows — J4-687: THE ALL-ROWS WHITENED↔hBdom RE-BASE, downstream item (i) of the
  J4-686 reconciliation.  Extends the width-`w` full signed Levi-series COLUMN engine
  (`WhiteHBdomReconcile.leviSeries_full_col_of_tail`, `y = 0`) to ALL ROWS (`∀ z y`), then feeds
  the whitened all-`τ` fat-`K` supply through it to land the FULL-MATRIX whitened `hBdom`
  (`∀ (z, y)`), the exact `∀ z y` SHAPE that `CurvedA1HContDom.curved_hInnerCont_of_dominations`
  consumes.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; nothing here touches the coefficient value.  `a₁ = R/6`
  remains CONDITIONAL — this brick is a WIDTH-w SHAPE reconciliation at the `hBdom` consumer
  interface, ALL-ROWS form, at the WHITENED witness.

  ── THE ROW-GENERALIZABILITY VERDICT (the finding).  The column restriction to the right node
  `y = 0` in the banked tail engine (`BridgeWidth.bridgeGeneric_tail_O_s_w` and its supports
  `iterE_column_bound_w` / `leviSeries_column_k3_bound_w` / `bridgeGenericK2_O_s_w`) is COSMETIC,
  NOT structural: the whitened defect's Chapman–Kolmogorov did NOT run at `y = 0`.  Every
  convolution / integrability helper the engine consumes
  (`GaussianConvolution.gaussDdim_conv`, `GaussianWidthTolerant.gaussTimePow_conv_beta_scaled`,
  `BridgeWidth.mixedColZW_integrable`, `BridgeWidth.mixedColSW_intervalIntegrable`,
  `BridgeWidth.heatConv_le_of_abs_le_pos_right_capped`) is ALREADY stated at general endpoints
  `x y`; and the whitened one-step supplies (`WhiteBridge.white_hEuni`,
  `WhiteBridge.white_hEbound_negHalf`) are ALREADY FULL-MATRIX (`∀ p q`).  So the tail engine's
  `y = 0` conclusion is a mere instantiation of a general-`y` fact — re-proved here at general
  right node `y` by verbatim replay of the column proofs with `0 ↦ y`.

  ── WHAT LANDS HERE (all proved, std-3; NO sorry, NO `:= True`, NO new axioms).
    • `iterE_row_bound_w`, `leviSeries_row_k3_bound_w`, `bridgeGenericK2_O_s_w_row`,
      `bridgeGeneric_tail_O_s_w_row` — ★ the row-generalized (`∀ p y`) tail-engine ladder: the
      width-`w` mixed ladder, the k ≥ 3 sub-tail, the k = 2 O(s) bound, and the FULL k ≥ 2 tail
      `O(s)·G_{w s}(p − y)`, at ANY width `w > 0`, general right node `y`.  Same all-matrix
      hypothesis pile as the column engine (which already carried `∀ p q` bounds).
    • `leviSeries_full_row_of_tail` — ★ THE REUSABLE WIDTH-`w` FULL-ROW ENGINE: the all-rows
      analogue of `WhiteHBdomReconcile.leviSeries_full_col_of_tail`; from {the k ≥ 2 tail row
      bound, the O(1) full-matrix bound} the FULL signed series obeys
      `|leviSeries E s p y| ≤ (C_os + C_U)·G_{w s}(p − y)` on `(0,1]`, `∀ p y`.
    • `white_tail_O_s_row` / `white_leviSeries_full_row` — ★ the whitened all-rows instantiations,
      fed by `white_hEbound_negHalf` (tail α = −1/2) and `white_hEuni` (O(1)), both full-matrix.
      CONDITIONAL on the pkg bound `+` the carried S1 measurability, exactly as `white_tail_O_s`.
    • `white_hBdom_discharged` — ★★ THE ALL-ROWS FEED: for EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)`,
      there ARE a fat open gate `S`, radii `0 < a < b`, and a width `lam ≥ 2` such that, MODULO
      exactly ONE labelled input (the whitened-defect S1 joint measurability), the FULL whitened
      signed Levi-series obeys `|leviSeries (whiteDefectKernel …) s z y| ≤ C_L·G_{lam·s}(z − y)`
      on `(0,1]`, for ALL `z y` — the `∀ (z,y)` `hBdom` SHAPE.  All Gaussian/integrability slots
      UNCONDITIONALLY discharged from J4-626's `white_hpkgBound_discharged`.  ⚠ HONEST WIDTH
      `lam = whiteLam` (opaque `C₀`); NO `lam ≤ 8` used.
    • `white_hBdom_allrows_witness_gate` — non-vacuity (cp466) at `n = 2`, `κ = −1`,
      `K = closedBall 0 2`.

  ── HONEST RESIDUAL.  This is the FULL-MATRIX `∀ (z,y)` `hBdom` at the WHITENED witness, width
  `lam = whiteLam`; the general-`K` `curved_hInnerCont_of_dominations` builder is still pinned at
  `vanVleckGatedWitness` and width `2`.  Feeding THIS all-rows bound into that builder still owes
  (a) the whitened-witness re-base of the builder (or a width-`lam` variant), (b) the single S1
  measurability of the whitened defect, (c) the prior `K1TransportBudget` / capstone
  co-instantiation piles.  `a₁ = R/6` established non-vacuously ONLY for the FLAT tower.

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedent posing as discharge, no
  existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.WhiteHBdomReconcile

open Finset Filter Topology MeasureTheory
open scoped Interval
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.AlphaLevi QIQTH.FrozenColumn QIQTH.BridgeDefect QIQTH.BridgeWidth
open QIQTH.WhiteGated QIQTH.WhiteAnnulus QIQTH.WhiteBridge QIQTH.CurvedA1CenterAmp

namespace QIQTH.WhiteHBdomAllRows

variable {n : ℕ}

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! ###############################################################################
    ### 1. ★ The ROW-GENERALIZED tail-engine ladder (`∀ p y`) — verbatim replay of the
    ###    `BridgeWidth` column lemmas with the right node `0 ↦ y`.
    ############################################################################### -/

/-- **★ `iterE_row_bound_w` — the width-`w` τ-capped mixed ladder at GENERAL right node `y`.**
    The all-rows analogue of `BridgeWidth.iterE_column_bound_w`; the right-column bound is taken
    full-matrix (`∀ p q`, i.e. `hEuni`).  NOT `a₁ = R/6`. -/
theorem iterE_row_bound_w (E : ℝ → Point n → Point n → ℝ) (w C C₀ : ℝ)
    (hw : 0 < w) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ 1 → |E τ p q| ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C₀ * gaussDdim (w * τ) (p - q))
    (hInt : IterConvIntegrableW E w (-(1 / 2) : ℝ) C) :
    ∀ (m : ℕ) (s : ℝ), 0 < s → s ≤ 1 → ∀ p y : Point n,
      |iterE E (m + 1) s p y|
        ≤ colC C C₀ m * s ^ ((m : ℝ) / 2) * gaussDdim (w * s) (p - y) := by
  intro m
  induction m with
  | zero =>
      intro s hs hs1 p y
      rw [show (0 : ℕ) + 1 = 1 from rfl, iterE_one, colC_zero,
          show ((0 : ℕ) : ℝ) / 2 = (0 : ℝ) from by norm_num, Real.rpow_zero, mul_one]
      exact hEuni s p y hs hs1
  | succ m ih =>
      intro s hs hs1 p y
      have hm1 : 1 ≤ m + 1 := by omega
      obtain ⟨hI1, hI2, hIf, -, -⟩ := hInt (m + 1) hm1 s hs p y
      have hB : ∀ (τ : ℝ) (z : Point n), 0 < τ → τ < s →
          |iterE E (m + 1) τ z y|
            ≤ colC C C₀ m * baseKernelW w ((m : ℝ) / 2) τ z y := by
        intro τ z hτ hτs
        have hτ1 : τ ≤ 1 := le_of_lt (lt_of_lt_of_le hτs hs1)
        calc |iterE E (m + 1) τ z y|
            ≤ colC C C₀ m * τ ^ ((m : ℝ) / 2) * gaussDdim (w * τ) (z - y) :=
              ih τ hτ hτ1 z y
          _ = colC C C₀ m * baseKernelW w ((m : ℝ) / 2) τ z y := by
              simp only [baseKernelW]; ring
      have hA : ∀ (τ : ℝ) (p' q' : Point n), 0 < τ → τ < s →
          |E τ p' q'| ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p' q' := by
        intro τ p' q' hτ hτs
        exact hEbound τ p' q' hτ (le_of_lt (lt_of_lt_of_le hτs hs1))
      have hIg : ∀ σ, Integrable
          (fun z => C * baseKernelW w (-(1 / 2) : ℝ) (s - σ) p z
            * (colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z y)) :=
        fun σ => mixedColZW_integrable w (-(1 / 2)) ((m : ℝ) / 2) C (colC C C₀ m) hw s σ p y
      have hbge : (-1 : ℝ) < (m : ℝ) / 2 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hIsg : IntervalIntegrable
          (fun σ => ∫ z, C * baseKernelW w (-(1 / 2) : ℝ) (s - σ) p z
            * (colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z y)) volume 0 s :=
        mixedColSW_intervalIntegrable w (-(1 / 2)) ((m : ℝ) / 2) C (colC C C₀ m) hw
          (by norm_num) hbge s hs p y
      rw [iterE_succ E hm1]
      simp only [heatConvK_apply]
      have hdom := heatConv_le_of_abs_le_pos_right_capped E (iterE E (m + 1))
        (fun τ p' q' => C * baseKernelW w (-(1 / 2) : ℝ) τ p' q')
        (fun σ z' q' => colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z' q')
        s p y hs hA hB hI1 hI2 hIf hIg hIsg
      have hRHS : heatConv
            (fun τ p' q' => C * baseKernelW w (-(1 / 2) : ℝ) τ p' q')
            (fun σ z' q' => colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z' q') s p y
          = C * colC C C₀ m
              * (s ^ (((m : ℝ) + 1) / 2)
                * (Real.Gamma (1 / 2) * Real.Gamma ((m : ℝ) / 2 + 1)
                    / Real.Gamma ((m : ℝ) / 2 + 3 / 2))
                * gaussDdim (w * s) (p - y)) := by
        rw [heatConv_smul_left C (baseKernelW w (-(1 / 2)))
              (fun σ z' q' => colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z' q') s p y,
            heatConv_smul_right (colC C C₀ m) (baseKernelW w (-(1 / 2)))
              (baseKernelW w ((m : ℝ) / 2)) s p y]
        unfold baseKernelW
        rw [gaussTimePow_conv_beta_scaled w (-(1 / 2)) ((m : ℝ) / 2) hw
              (by norm_num) hbge s hs p y,
            show (-(1 / 2 : ℝ) + (m : ℝ) / 2 + 1) = ((m : ℝ) + 1) / 2 from by ring,
            show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) from by norm_num,
            show (-(1 / 2 : ℝ) + (m : ℝ) / 2 + 2) = (m : ℝ) / 2 + 3 / 2 from by ring]
        ring
      calc |heatConv E (iterE E (m + 1)) s p y|
          ≤ heatConv
              (fun τ p' q' => C * baseKernelW w (-(1 / 2) : ℝ) τ p' q')
              (fun σ z' q' => colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z' q')
              s p y := hdom
        _ = C * colC C C₀ m
              * (s ^ (((m : ℝ) + 1) / 2)
                * (Real.Gamma (1 / 2) * Real.Gamma ((m : ℝ) / 2 + 1)
                    / Real.Gamma ((m : ℝ) / 2 + 3 / 2))
                * gaussDdim (w * s) (p - y)) := hRHS
        _ = colC C C₀ (m + 1) * s ^ (((m + 1 : ℕ) : ℝ) / 2) * gaussDdim (w * s) (p - y) := by
            rw [show (((m + 1 : ℕ) : ℝ) / 2) = ((m : ℝ) + 1) / 2 from by push_cast; ring,
                ← colC_succ C C₀ m]
            ring

/-- **★ `leviSeries_row_k3_bound_w` — the width-`w` k ≥ 3 sub-tail is O(s) at general right node
    `y`.**  The all-rows analogue of `BridgeWidth.leviSeries_column_k3_bound_w`.  NOT `a₁ = R/6`. -/
theorem leviSeries_row_k3_bound_w (E : ℝ → Point n → Point n → ℝ) (w C C₀ : ℝ)
    (hw : 0 < w) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ 1 → |E τ p q| ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C₀ * gaussDdim (w * τ) (p - q))
    (hInt : IterConvIntegrableW E w (-(1 / 2) : ℝ) C) :
    ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ p y : Point n,
      |leviSeries E s p y + E s p y - iterE E 2 s p y|
        ≤ (∑' m : ℕ, colC C C₀ (m + 2)) * (s * gaussDdim (w * s) (p - y)) := by
  intro s hs hs1 p y
  have hG0 : 0 ≤ gaussDdim (w * s) (p - y) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hterm := iterE_row_bound_w E w C C₀ hw hC hC₀ hEbound hEuni hInt
  have hterm4 : ∀ m : ℕ, |iterE E (m + 1 + 1 + 1) s p y|
      ≤ colC C C₀ (m + 2) * (s * gaussDdim (w * s) (p - y)) := by
    intro m
    have hD0 := colC_nonneg C C₀ hC hC₀ (m + 2)
    have hpow : s ^ (((m + 2 : ℕ) : ℝ) / 2) ≤ s := by
      have hexp : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) / 2 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        push_cast
        linarith
      calc s ^ (((m + 2 : ℕ) : ℝ) / 2) ≤ s ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hs hs1 hexp
        _ = s := Real.rpow_one s
    calc |iterE E (m + 1 + 1 + 1) s p y|
        ≤ colC C C₀ (m + 2) * s ^ (((m + 2 : ℕ) : ℝ) / 2) * gaussDdim (w * s) (p - y) :=
          hterm (m + 2) s hs hs1 p y
      _ ≤ colC C C₀ (m + 2) * s * gaussDdim (w * s) (p - y) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hD0) hG0
      _ = colC C C₀ (m + 2) * (s * gaussDdim (w * s) (p - y)) := by ring
  have hterm2 : ∀ m : ℕ, |iterE E (m + 1) s p y|
      ≤ colC C C₀ m * gaussDdim (w * s) (p - y) := by
    intro m
    have hpow : s ^ ((m : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one hs.le hs1 (by positivity)
    calc |iterE E (m + 1) s p y|
        ≤ colC C C₀ m * s ^ ((m : ℝ) / 2) * gaussDdim (w * s) (p - y) :=
          hterm m s hs hs1 p y
      _ ≤ colC C C₀ m * 1 * gaussDdim (w * s) (p - y) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (colC_nonneg C C₀ hC hC₀ m)) hG0
      _ = colC C C₀ m * gaussDdim (w * s) (p - y) := by ring
  have hSumCG : Summable (fun m : ℕ => colC C C₀ m * gaussDdim (w * s) (p - y)) :=
    (colC_summable C C₀ hC hC₀).mul_right _
  have hAbsSum : Summable (fun m : ℕ => |iterE E (m + 1) s p y|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hterm2 hSumCG
  have hnormeq : (fun m : ℕ => ‖(-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p y‖)
      = fun m : ℕ => |iterE E (m + 1) s p y| := by
    funext m
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  have hfSum : Summable (fun m : ℕ => (-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p y) :=
    Summable.of_norm (by rw [hnormeq]; exact hAbsSum)
  have hsplit1 : leviSeries E s p y
      = (-1 : ℝ) ^ (0 + 1) * iterE E (0 + 1) s p y
        + ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p y := by
    simp only [leviSeries]
    exact hfSum.tsum_eq_zero_add
  have hfSum1 : Summable
      (fun m : ℕ => (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p y) :=
    (summable_nat_add_iff 1).mpr hfSum
  have hsplit2 : (∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p y)
      = (-1 : ℝ) ^ (0 + 1 + 1) * iterE E (0 + 1 + 1) s p y
        + ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p y :=
    hfSum1.tsum_eq_zero_add
  have hf0 : (-1 : ℝ) ^ (0 + 1) * iterE E (0 + 1) s p y = -(E s p y) := by
    rw [show (0 : ℕ) + 1 = 1 from rfl, iterE_one]
    ring
  have hf1 : (-1 : ℝ) ^ (0 + 1 + 1) * iterE E (0 + 1 + 1) s p y = iterE E 2 s p y := by
    norm_num
  have htaileq : leviSeries E s p y + E s p y - iterE E 2 s p y
      = ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p y := by
    rw [hsplit1, hsplit2, hf0, hf1]; ring
  have hAbsSum3 : Summable (fun m : ℕ => |iterE E (m + 1 + 1 + 1) s p y|) := by
    have := (summable_nat_add_iff 2).mpr hAbsSum
    exact this.congr (fun m => by norm_num)
  have hColSum2 : Summable (fun m : ℕ => colC C C₀ (m + 2)) := by
    have := (summable_nat_add_iff 2).mpr (colC_summable C C₀ hC hC₀)
    exact this.congr (fun m => by norm_num)
  have hSumK3 : Summable
      (fun m : ℕ => colC C C₀ (m + 2) * (s * gaussDdim (w * s) (p - y))) :=
    hColSum2.mul_right _
  have hnormeq3 : (fun m : ℕ => ‖(-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p y‖)
      = fun m : ℕ => |iterE E (m + 1 + 1 + 1) s p y| := by
    funext m
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  calc |leviSeries E s p y + E s p y - iterE E 2 s p y|
      = |∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p y| := by
        rw [htaileq]
    _ ≤ ∑' m : ℕ, |iterE E (m + 1 + 1 + 1) s p y| := by
        rw [← Real.norm_eq_abs]
        calc ‖∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p y‖
            ≤ ∑' m : ℕ, ‖(-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p y‖ :=
              norm_tsum_le_tsum_norm (by rw [hnormeq3]; exact hAbsSum3)
          _ = ∑' m : ℕ, |iterE E (m + 1 + 1 + 1) s p y| := by rw [hnormeq3]
    _ ≤ ∑' m : ℕ, colC C C₀ (m + 2) * (s * gaussDdim (w * s) (p - y)) :=
        hAbsSum3.tsum_le_tsum hterm4 hSumK3
    _ = (∑' m : ℕ, colC C C₀ (m + 2)) * (s * gaussDdim (w * s) (p - y)) := tsum_mul_right

/-- **★ `bridgeGenericK2_O_s_w_row` — k = 2 is O(s)·G_{ws}(p − y) at general right node `y`.**
    The all-rows analogue of `BridgeWidth.bridgeGenericK2_O_s_w`.  NOT `a₁ = R/6`. -/
theorem bridgeGenericK2_O_s_w_row (E : ℝ → Point n → Point n → ℝ) (w C C_U : ℝ) (hw : 0 < w)
    (hEuni : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C_U * gaussDdim (w * τ) (p - q))
    (hInt : IterConvIntegrableW E w (-(1 / 2) : ℝ) C) :
    ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ p y : Point n,
      |iterE E 2 s p y| ≤ C_U ^ 2 * (s * gaussDdim (w * s) (p - y)) := by
  intro s hs hs1 p y
  obtain ⟨hI1, hI2, hIf, -, -⟩ := hInt 1 le_rfl s hs p y
  have huniW : ∀ τ (p' q' : Point n), 0 < τ → τ < s →
      |E τ p' q'| ≤ C_U * baseKernelW w (0 : ℝ) τ p' q' := by
    intro τ p' q' hτ hτs
    have hbw : baseKernelW w (0 : ℝ) τ p' q' = gaussDdim (w * τ) (p' - q') := by
      simp only [baseKernelW, Real.rpow_zero, one_mul]
    rw [hbw]
    exact hEuni τ p' q' hτ (le_of_lt (lt_of_lt_of_le hτs hs1))
  have hB : ∀ (τ : ℝ) (z : Point n), 0 < τ → τ < s →
      |iterE E 1 τ z y| ≤ C_U * baseKernelW w (0 : ℝ) τ z y := by
    intro τ z hτ hτs
    rw [iterE_one]
    exact huniW τ z y hτ hτs
  have hIg : ∀ σ, Integrable (fun z => C_U * baseKernelW w (0 : ℝ) (s - σ) p z
      * (C_U * baseKernelW w (0 : ℝ) σ z y)) :=
    fun σ => mixedColZW_integrable w (0 : ℝ) (0 : ℝ) C_U C_U hw s σ p y
  have hIsg : IntervalIntegrable (fun σ => ∫ z, C_U * baseKernelW w (0 : ℝ) (s - σ) p z
      * (C_U * baseKernelW w (0 : ℝ) σ z y)) volume 0 s :=
    mixedColSW_intervalIntegrable w (0 : ℝ) (0 : ℝ) C_U C_U hw (by norm_num) (by norm_num)
      s hs p y
  rw [show (2 : ℕ) = 1 + 1 from rfl, iterE_succ E le_rfl]
  simp only [heatConvK_apply]
  have hdom := heatConv_le_of_abs_le_pos_right_capped E (iterE E 1)
    (fun τ p' q' => C_U * baseKernelW w (0 : ℝ) τ p' q')
    (fun σ z' q' => C_U * baseKernelW w (0 : ℝ) σ z' q')
    s p y hs huniW hB hI1 hI2 hIf hIg hIsg
  have hRHS : heatConv (fun τ p' q' => C_U * baseKernelW w (0 : ℝ) τ p' q')
      (fun σ z' q' => C_U * baseKernelW w (0 : ℝ) σ z' q') s p y
      = C_U ^ 2 * (s * gaussDdim (w * s) (p - y)) := by
    rw [heatConv_smul_left C_U (baseKernelW w (0 : ℝ))
          (fun σ z' q' => C_U * baseKernelW w (0 : ℝ) σ z' q') s p y,
        heatConv_smul_right C_U (baseKernelW w (0 : ℝ))
          (baseKernelW w (0 : ℝ)) s p y]
    unfold baseKernelW
    rw [gaussTimePow_conv_beta_scaled w 0 0 hw (by norm_num) (by norm_num) s hs p y,
        show ((0 : ℝ) + 0 + 1) = (1 : ℝ) from by norm_num,
        show ((0 : ℝ) + 0 + 2) = (2 : ℝ) from by norm_num,
        show ((0 : ℝ) + 1) = (1 : ℝ) from by norm_num,
        Real.rpow_one, Real.Gamma_one, Real.Gamma_two]
    ring
  calc |heatConv E (iterE E 1) s p y|
      ≤ heatConv (fun τ p' q' => C_U * baseKernelW w (0 : ℝ) τ p' q')
          (fun σ z' q' => C_U * baseKernelW w (0 : ℝ) σ z' q') s p y := hdom
    _ = C_U ^ 2 * (s * gaussDdim (w * s) (p - y)) := hRHS

/-- **★ `bridgeGeneric_tail_O_s_w_row` — the FULL k ≥ 2 tail is O(s)·G_{ws}(p − y) at ANY width
    `w > 0`, general right node `y`.**  The all-rows analogue of
    `BridgeWidth.bridgeGeneric_tail_O_s_w`; SAME hypothesis pile (already all-matrix), general-`y`
    conclusion.  NOT `a₁ = R/6`. -/
theorem bridgeGeneric_tail_O_s_w_row (E : ℝ → Point n → Point n → ℝ) (w C C_U : ℝ)
    (hw : 0 < w) (hC : 0 ≤ C) (hCU : 0 ≤ C_U)
    (hEbound : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C_U * gaussDdim (w * τ) (p - q))
    (hInt : IterConvIntegrableW E w (-(1 / 2) : ℝ) C) :
    ∃ C_os : ℝ, 0 ≤ C_os ∧ ∀ (s : ℝ) (p y : Point n), 0 < s → s ≤ 1 →
      |leviSeries E s p y + E s p y| ≤ C_os * (s * gaussDdim (w * s) (p - y)) := by
  have hk3 := leviSeries_row_k3_bound_w E w C C_U hw hC hCU hEbound hEuni hInt
  have hk2 := bridgeGenericK2_O_s_w_row E w C C_U hw hEuni hInt
  have hsum_nn : 0 ≤ (∑' m : ℕ, colC C C_U (m + 2)) :=
    tsum_nonneg (fun m => colC_nonneg C C_U hC hCU (m + 2))
  refine ⟨(∑' m : ℕ, colC C C_U (m + 2)) + C_U ^ 2,
    add_nonneg hsum_nn (by positivity), fun s p y hs hs1 => ?_⟩
  calc |leviSeries E s p y + E s p y|
      = |(leviSeries E s p y + E s p y - iterE E 2 s p y) + iterE E 2 s p y| := by ring_nf
    _ ≤ |leviSeries E s p y + E s p y - iterE E 2 s p y| + |iterE E 2 s p y| := abs_add_le _ _
    _ ≤ (∑' m : ℕ, colC C C_U (m + 2)) * (s * gaussDdim (w * s) (p - y))
          + C_U ^ 2 * (s * gaussDdim (w * s) (p - y)) :=
        add_le_add (hk3 s hs hs1 p y) (hk2 s hs hs1 p y)
    _ = ((∑' m : ℕ, colC C C_U (m + 2)) + C_U ^ 2) * (s * gaussDdim (w * s) (p - y)) := by
        ring

/-! ###############################################################################
    ### 2. ★ The reusable width-`w` FULL-ROW engine (tail + k = 1 term), all rows.
    ############################################################################### -/

/-- **★ `leviSeries_full_row_of_tail` — the width-`w` full signed Levi-series bound, ALL ROWS.**
    The all-rows analogue of `WhiteHBdomReconcile.leviSeries_full_col_of_tail`: the triangle split
    `leviSeries E = (leviSeries E + E) − E` combines the k ≥ 2 tail row bound with the k = 1 term
    `E`, giving `|leviSeries E s p y| ≤ (C_os + C_U)·G_{ws}(p − y)` on `(0,1]`, `∀ p y`.
    Width-generic, witness-generic.  NOT `a₁ = R/6`. -/
theorem leviSeries_full_row_of_tail (E : ℝ → Point n → Point n → ℝ) (w C_os C_U : ℝ)
    (hCos : 0 ≤ C_os) (hCU : 0 ≤ C_U)
    (htail : ∀ (s : ℝ) (p y : Point n), 0 < s → s ≤ 1 →
      |leviSeries E s p y + E s p y| ≤ C_os * (s * gaussDdim (w * s) (p - y)))
    (hEuni : ∀ (s : ℝ) (p y : Point n), 0 < s → s ≤ 1 →
      |E s p y| ≤ C_U * gaussDdim (w * s) (p - y)) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ (s : ℝ) (p y : Point n), 0 < s → s ≤ 1 →
      |leviSeries E s p y| ≤ C_L * gaussDdim (w * s) (p - y) := by
  refine ⟨C_os + C_U, add_nonneg hCos hCU, fun s p y hs hs1 => ?_⟩
  have hG : 0 ≤ gaussDdim (w * s) (p - y) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have htl := htail s p y hs hs1
  have hE := hEuni s p y hs hs1
  have hsplit : |leviSeries E s p y| ≤ |leviSeries E s p y + E s p y| + |E s p y| := by
    calc |leviSeries E s p y|
        = |(leviSeries E s p y + E s p y) + (-(E s p y))| := by
          rw [show (leviSeries E s p y + E s p y) + (-(E s p y)) = leviSeries E s p y from by ring]
      _ ≤ |leviSeries E s p y + E s p y| + |(-(E s p y))| := abs_add_le _ _
      _ = |leviSeries E s p y + E s p y| + |E s p y| := by rw [abs_neg]
  have hos : C_os * (s * gaussDdim (w * s) (p - y)) ≤ C_os * gaussDdim (w * s) (p - y) := by
    refine mul_le_mul_of_nonneg_left ?_ hCos
    calc s * gaussDdim (w * s) (p - y) ≤ 1 * gaussDdim (w * s) (p - y) :=
          mul_le_mul_of_nonneg_right hs1 hG
      _ = gaussDdim (w * s) (p - y) := one_mul _
  calc |leviSeries E s p y|
      ≤ |leviSeries E s p y + E s p y| + |E s p y| := hsplit
    _ ≤ C_os * (s * gaussDdim (w * s) (p - y)) + C_U * gaussDdim (w * s) (p - y) :=
        add_le_add htl hE
    _ ≤ C_os * gaussDdim (w * s) (p - y) + C_U * gaussDdim (w * s) (p - y) :=
        add_le_add hos (le_refl _)
    _ = (C_os + C_U) * gaussDdim (w * s) (p - y) := by ring

/-! ###############################################################################
    ### 3. ★ The whitened all-rows instantiation — the full Levi-series at width `lam`, all rows.
    ############################################################################### -/

/-- **★ `white_tail_O_s_row` — the whitened k ≥ 2 tail is `O(s)·G_{lam·s}(p − y)`, ALL ROWS.**
    `bridgeGeneric_tail_O_s_w_row` at the τ-gated whitened defect, all slots supplied from
    {the pkg bound (via `white_hEbound_negHalf`, `white_hEuni`, both full-matrix), the S1 input}.
    Width-PARAMETRIC (no `lam ≤ 8`).  NOT `a₁ = R/6`. -/
theorem white_tail_O_s_row (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    ∃ C_os : ℝ, 0 ≤ C_os ∧ ∀ (s : ℝ) (p y : Point n), 0 < s → s ≤ 1 →
      |leviSeries (whiteDefectKernel κ hκ hKc S a b) s p y
          + whiteDefectKernel κ hκ hKc S a b s p y|
        ≤ C_os * (s * gaussDdim (lam * s) (p - y)) := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  exact bridgeGeneric_tail_O_s_w_row (whiteDefectKernel κ hκ hKc S a b) lam (2 * C) (2 * C)
    hlam0 (by linarith) (by linarith)
    (fun τ p q hτ _hτ1 => white_hEbound_negHalf κ hκ hKc S a b C lam hC hpkg τ p q hτ)
    (white_hEuni κ hκ hKc S a b C lam hpkg)
    (white_hInt κ hκ hKc S a b C lam hC hlam0 hpkg hEmeas)

/-- **★ `white_leviSeries_full_row` — the full whitened Levi-series at width `lam`, ALL ROWS.**
    `white_tail_O_s_row` (tail) `+` `white_hEuni` (k = 1, full-matrix) fed into
    `leviSeries_full_row_of_tail`.  CONDITIONAL on the pkg bound `+` the carried S1 measurability,
    exactly as `white_tail_O_s_row`.  Width `lam`, NO `lam ≤ 8`.  NOT `a₁ = R/6`. -/
theorem white_leviSeries_full_row (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ (s : ℝ) (p y : Point n), 0 < s → s ≤ 1 →
      |leviSeries (whiteDefectKernel κ hκ hKc S a b) s p y|
        ≤ C_L * gaussDdim (lam * s) (p - y) := by
  obtain ⟨C_os, hCos, htail⟩ :=
    white_tail_O_s_row κ hκ hKc S a b C lam hC hlam2 hpkg hEmeas
  refine leviSeries_full_row_of_tail (whiteDefectKernel κ hκ hKc S a b) lam C_os (2 * C)
    hCos (by linarith) htail ?_
  intro s p y hs hs1
  exact white_hEuni κ hκ hKc S a b C lam hpkg s p y hs hs1

/-- **★★ `white_hBdom_discharged` — THE ALL-ROWS FEED.**  For EVERY `κ ≤ 0` and compact
    `K ⊆ B̄(0,R)` there ARE a fat open gate `S`, radii `0 < a < b`, and a width `lam ≥ 2` such
    that, MODULO exactly ONE labelled input — the S1 joint measurability of the whitened defect —
    the FULL whitened signed Levi-series obeys
    `|leviSeries (whiteDefectKernel …) s z y| ≤ C_L·G_{lam·s}(z − y)` on `(0,1]`, for ALL `z y`
    — the `∀ (z,y)` `hBdom` SHAPE that `CurvedA1HContDom.curved_hInnerCont_of_dominations`
    consumes.  Every Gaussian-domination / integrability slot is UNCONDITIONALLY discharged from
    J4-626's `white_hpkgBound_discharged`.  ⚠ HONEST WIDTH `lam = whiteLam` (opaque `C₀`); the
    conclusion is at `G_{lam·s}` — NO `lam ≤ 8` used.  This is the full-matrix analogue of the
    `hBdom` of `CurvedA1ReBaseHBdom.gated_hBdom_of_defect_bound`, at the WHITENED witness.
    NOT `a₁ = R/6`. -/
theorem white_hBdom_discharged (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        (QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
            (whiteGatedWitness κ hκ hKc S a b) →
          ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ (s : ℝ) (z y : Point n), 0 < s → s ≤ 1 →
            |leviSeries (whiteDefectKernel κ hκ hKc S a b) s z y|
              ≤ C_L * gaussDdim (lam * s) (z - y)) := by
  obtain ⟨S, a, b, ha, hab, hgate, C, hC0, lam, hlam2, hpkg⟩ :=
    white_hpkgBound_discharged κ hκ hKc R hKb
  exact ⟨S, a, b, ha, hab, hgate, lam, hlam2,
    fun hEmeas => white_leviSeries_full_row κ hκ hKc S a b C lam hC0 hlam2 hpkg hEmeas⟩

/-! ###############################################################################
    ### 4. Non-vacuity / adversarial gate (cp466 discipline).
    ############################################################################### -/

/-- **Non-vacuity gate** — at genuinely curved data (`n = 2`, `κ = −1`, `K = closedBall 0 2`): the
    ∃-package of `white_hBdom_discharged` produces a FAT gate (`q ∈ S q`, open, at `q ∈ K ≠ ∅`)
    with `0 < a < b` and `lam ≥ 2` — the antecedent chain up to the single S1 input is genuinely
    satisfiable, not `∅`-degenerate.  NOT `a₁ = R/6`. -/
theorem white_hBdom_allrows_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0))
      ∧ ∃ lam : ℝ, 2 ≤ lam := by
  obtain ⟨S, a, b, ha, hab, hgate, lam, hlam2, -⟩ :=
    white_hBdom_discharged (n := 2) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
  exact ⟨S, a, b, ha, hab,
    hgate 0 (Metric.mem_closedBall_self (by norm_num)), lam, hlam2⟩

end QIQTH.WhiteHBdomAllRows

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.WhiteHBdomAllRows

#print axioms iterE_row_bound_w
#print axioms leviSeries_row_k3_bound_w
#print axioms bridgeGenericK2_O_s_w_row
#print axioms bridgeGeneric_tail_O_s_w_row
#print axioms leviSeries_full_row_of_tail
#print axioms white_tail_O_s_row
#print axioms white_leviSeries_full_row
#print axioms white_hBdom_discharged
#print axioms white_hBdom_allrows_witness_gate

end AxiomChecks
