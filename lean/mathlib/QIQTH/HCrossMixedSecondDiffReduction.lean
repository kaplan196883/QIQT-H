/-
  HCrossMixedSecondDiffReduction — the DOUBLE-DIFFERENCE DECOMPOSITION of the live `hCross`
  census binder: the mixed second difference of a frozen convolution collapses to a single
  sliver-integral of the FIRST-ORDER τ-shift difference of the inner convolution.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick — the genuine assembly of the chart-CoV moment-cancellation
  sub-campaign (J4-919..J4-925) against the ACTUAL binder shape of the live `hCross` hypothesis
  (`HDuhamelLiveGateWired.hDuhamel_live_gate_wired`, the mixed second-difference bilinear Lipschitz
  wall shared by hDuhamel/hDConv).

  ## THE OBJECT.  For the frozen convolution
      `heatConvFrozen A B c d x y = ∫ s in 0..d, (∫ z, A (c − s) x z · B s z y)`
  (`c` = the FIRST time argument / τ-shift direction; `d` = the second / upper integration limit),
  `hCross` demands, with `W` = a witness, `F` = a field, base point `a := u`, `b := u − ε_m`:
      `|heatConvFrozen W F (u+h) (u−ε+k) 0 0 − heatConvFrozen W F (u+h) (u−ε) 0 0
          − heatConvFrozen W F u (u−ε+k) 0 0 + heatConvFrozen W F u (u−ε) 0 0|  ≤  L m u · (|h|·|k|)` .

  ## THE DECOMPOSITION (gpt-5.6-sol audited GO).  Write `Φ(c,s) := ∫ z, A (c−s) x z · B s z y`, so
  `K(c,d) = ∫ s in 0..d, Φ(c,s)`.  Oriented interval additivity (NOT a derivative — pure
  `integral_add_adjacent_intervals`) in the `d`-direction gives, for each fixed `c`,
      `K(c,b+k) − K(c,b) = ∫ s in b..(b+k), Φ(c,s)` ,
  so the whole mixed second difference collapses to a SINGLE sliver integral of the FIRST-order
  τ-shift difference:
      `Δ² = ∫ s in b..(b+k), (Φ(a+h,s) − Φ(a,s))` .
  Then `|Δ²| ≤ (L·|h|)·|k|` by `norm_integral_le_of_norm_le_const`, GIVEN the SINGLE-DIFFERENCE bound
      `hdiff : ∀ s ∈ uIoc b (b+k), |Φ(a+h,s) − Φ(a,s)| ≤ L·|h|` .

  ## WHAT THIS DOES — AND DOES NOT — UNBLOCK (gpt-5.6-sol audit, verbatim honest).
  This is a GENUINE, NON-CIRCULAR reduction of the mixed bilinear 2nd-difference to a cleaner
  LOWER-ORDER analytic sub-obligation `hdiff` (the τ-shift Lipschitz of the inner convolution,
  pointwise in `s`) + four interval-integrabilities of `Φ(c,·)`.  ⚠  `hdiff` is NOT logically WEAKER
  than `hCross` — it is a STRONGER POINTWISE SUFFICIENT condition (a pointwise bound implies the
  integrated one, not conversely).  It IS a strictly lower-ORDER, single-DIRECTION object: a first
  difference in ONE variable (the τ-shift) versus the integrated bilinear second difference.  The
  `k`-direction (an integration-LIMIT displacement, NOT an argument shift) is genuinely FREE — its
  `|k|` factor is pure interval length, no differentiability/continuity in `d` required (only
  measurability/integrability in `s`).  So `hdiff` IS the honest remaining wall: the τ-shift Lipschitz
  of `c ↦ ∫ z W(c−s)0z·F s z 0`, uniform over `s`.  This file does NOT close `hCross`; it REDUCES it
  to `hdiff` (still unbuilt for the concrete curved witness).

  ⚠  STILL NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, none equal
  to the conclusion, no existing file edited.
-/
import Mathlib
import QIQTH.HeatDuhamel

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatDuhamel

namespace QIQTH.HeatResidualBound

/-! ###############################################################################
    ### §A — the DOUBLE-DIFFERENCE DECOMPOSITION reduction of `hCross`'s binder.
    ############################################################################### -/

/-- **★★ `mixed_second_diff_frozen_reduction` — the DOUBLE-DIFFERENCE DECOMPOSITION.**
    For ANY `A B : ℝ → Point n → Point n → ℝ`, base point `x y`, base times `a b`, shifts `h k`, and
    constant `L ≥ 0`: GIVEN
      (i)  the inner convolution `Φ(c,·) := ∫ z, A (c−·) x z · B · z y` is `IntervalIntegrable` on
           `0..b` and `b..(b+k)`, for BOTH `c = a+h` and `c = a` (four hyps), and
      (ii) the SINGLE-DIFFERENCE τ-shift bound `|Φ(a+h,s) − Φ(a,s)| ≤ L·|h|` for all `s ∈ uIoc b (b+k)`,
    the MIXED SECOND DIFFERENCE of `heatConvFrozen A B` is bounded by `L·(|h|·|k|)` — EXACTLY the live
    `hCross` binder shape.  Route: oriented interval additivity collapses the `d`-direction to the
    sliver `∫ b..(b+k) (Φ(a+h,·) − Φ(a,·))`; `norm_integral_le_of_norm_le_const` closes with
    `|(b+k)−b| = |k|`.  NOT `a₁ = R/6`. -/
theorem mixed_second_diff_frozen_reduction {n : ℕ}
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n)
    (a b L h k : ℝ) (hL : 0 ≤ L)
    (hah_lo : IntervalIntegrable (fun s => ∫ z, A (a + h - s) x z * B s z y) volume 0 b)
    (hah_hi : IntervalIntegrable (fun s => ∫ z, A (a + h - s) x z * B s z y) volume b (b + k))
    (ha_lo : IntervalIntegrable (fun s => ∫ z, A (a - s) x z * B s z y) volume 0 b)
    (ha_hi : IntervalIntegrable (fun s => ∫ z, A (a - s) x z * B s z y) volume b (b + k))
    (hdiff : ∀ s ∈ Set.uIoc b (b + k),
        |(∫ z, A (a + h - s) x z * B s z y) - (∫ z, A (a - s) x z * B s z y)| ≤ L * |h|) :
    |heatConvFrozen A B (a + h) (b + k) x y - heatConvFrozen A B (a + h) b x y
        - heatConvFrozen A B a (b + k) x y + heatConvFrozen A B a b x y|
      ≤ L * (|h| * |k|) := by
  -- unfold the four frozen convolutions to their `s`-integrals
  simp only [heatConvFrozen]
  -- collapse each upper-limit difference to a sliver integral (oriented additivity)
  have hah : (∫ s in (0 : ℝ)..(b + k), ∫ z, A (a + h - s) x z * B s z y)
      - (∫ s in (0 : ℝ)..b, ∫ z, A (a + h - s) x z * B s z y)
      = ∫ s in b..(b + k), ∫ z, A (a + h - s) x z * B s z y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hah_lo hah_hi]; ring
  have ha : (∫ s in (0 : ℝ)..(b + k), ∫ z, A (a - s) x z * B s z y)
      - (∫ s in (0 : ℝ)..b, ∫ z, A (a - s) x z * B s z y)
      = ∫ s in b..(b + k), ∫ z, A (a - s) x z * B s z y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals ha_lo ha_hi]; ring
  -- rearrange the four terms into a single sliver integral of the difference
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
  rw [hrew]
  -- the interval norm bound
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := b) (b := b + k) (C := L * |h|)
    (f := fun s => (∫ z, A (a + h - s) x z * B s z y) - (∫ z, A (a - s) x z * B s z y))
    (fun s hs => by simpa only [Real.norm_eq_abs] using hdiff s hs)
  simp only [Real.norm_eq_abs] at hbound
  have hbk : (b + k) - b = k := by ring
  rw [hbk, mul_assoc] at hbound
  exact hbound

/-! ###############################################################################
    ### §B — non-vacuity (the hypothesis bundle is jointly satisfiable, with TEETH).
    ############################################################################### -/

/-- Factorization helper: the constant-in-`z` cosine amplitude pulls out of the `z`-integral. -/
private theorem cosGaussFactor {n : ℕ} (w : ℝ) :
    (∫ z : Point n, (Real.cos w * Real.exp (-‖z‖ ^ 2)) * Real.exp (-‖z‖ ^ 2))
      = Real.cos w * ∫ z : Point n, Real.exp (-‖z‖ ^ 2) * Real.exp (-‖z‖ ^ 2) := by
  simp_rw [mul_assoc]
  rw [integral_const_mul]

/-- **Non-vacuity of `mixed_second_diff_frozen_reduction`.**  Exhibited at the genuinely nonconstant,
    genuinely `c`-varying witness `A τ x z := cos τ · e^{−‖z‖²}`, `B s z y := e^{−‖z‖²}`, giving
    `Φ(c,s) = cos(c−s)·C` with `C = ∫ e^{−2‖z‖²}` a fixed real.  The single-difference bound holds
    with `L = |C|` via the 1-Lipschitz `cos` (`Real.lipschitzWith_cos`), the four interval
    integrabilities via continuity of `s ↦ cos(c−s)·C`; the τ-shift difference is generically
    nonzero, so the reduction's Lipschitz machinery is genuinely exercised (NOT the degenerate
    `0 ≤ 0`).  NOT `a₁ = R/6`. -/
theorem mixed_second_diff_frozen_reduction_hyp_satisfiable {n : ℕ} :
    ∃ (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (a b L h k : ℝ),
      0 ≤ L ∧
      IntervalIntegrable (fun s => ∫ z, A (a + h - s) x z * B s z y) volume 0 b ∧
      IntervalIntegrable (fun s => ∫ z, A (a + h - s) x z * B s z y) volume b (b + k) ∧
      IntervalIntegrable (fun s => ∫ z, A (a - s) x z * B s z y) volume 0 b ∧
      IntervalIntegrable (fun s => ∫ z, A (a - s) x z * B s z y) volume b (b + k) ∧
      (∀ s ∈ Set.uIoc b (b + k),
        |(∫ z, A (a + h - s) x z * B s z y) - (∫ z, A (a - s) x z * B s z y)| ≤ L * |h|) := by
  classical
  set C : ℝ := ∫ z : Point n, Real.exp (-‖z‖ ^ 2) * Real.exp (-‖z‖ ^ 2) with hC
  -- the four `Φ(c,·)` functions all equal `s ↦ cos(c−s)·C`, continuous hence interval-integrable
  have hInt : ∀ w a' b' : ℝ,
      IntervalIntegrable
        (fun s => ∫ z : Point n,
          (Real.cos (w - s) * Real.exp (-‖z‖ ^ 2)) * Real.exp (-‖z‖ ^ 2)) volume a' b' := by
    intro w a' b'
    have hfun : (fun s => ∫ z : Point n,
          (Real.cos (w - s) * Real.exp (-‖z‖ ^ 2)) * Real.exp (-‖z‖ ^ 2))
        = fun s => Real.cos (w - s) * C := by
      funext s; rw [cosGaussFactor (w - s), ← hC]
    rw [hfun]
    exact (((Real.continuous_cos.comp (continuous_const.sub continuous_id)).mul
      continuous_const).intervalIntegrable a' b')
  refine ⟨fun τ _ z => Real.cos τ * Real.exp (-‖z‖ ^ 2), fun _ z _ => Real.exp (-‖z‖ ^ 2),
    (0 : Point n), (0 : Point n), 0, 1, |C|, 1, 1, abs_nonneg _, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hInt (0 + 1) 0 1
  · simpa using hInt (0 + 1) 1 (1 + 1)
  · simpa using hInt 0 0 1
  · simpa using hInt 0 1 (1 + 1)
  · intro s _
    have e1 : (∫ z : Point n,
        (fun τ (_ : Point n) z => Real.cos τ * Real.exp (-‖z‖ ^ 2)) (0 + 1 - s) (0 : Point n) z
          * (fun (_ : ℝ) z (_ : Point n) => Real.exp (-‖z‖ ^ 2)) s z (0 : Point n))
        = Real.cos (0 + 1 - s) * C := by
      simp only []; rw [cosGaussFactor (0 + 1 - s), ← hC]
    have e2 : (∫ z : Point n,
        (fun τ (_ : Point n) z => Real.cos τ * Real.exp (-‖z‖ ^ 2)) (0 - s) (0 : Point n) z
          * (fun (_ : ℝ) z (_ : Point n) => Real.exp (-‖z‖ ^ 2)) s z (0 : Point n))
        = Real.cos (0 - s) * C := by
      simp only []; rw [cosGaussFactor (0 - s), ← hC]
    rw [e1, e2]
    have hcos : |Real.cos (0 + 1 - s) - Real.cos (0 - s)| ≤ (1 : ℝ) := by
      have hlip := Real.lipschitzWith_cos.dist_le_mul (0 + 1 - s) (0 - s)
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hlip
      have harg : |(0 + 1 - s) - (0 - s)| = (1 : ℝ) := by
        rw [show (0 + 1 - s) - (0 - s) = (1 : ℝ) by ring]; norm_num
      rw [harg] at hlip; exact hlip
    calc |Real.cos (0 + 1 - s) * C - Real.cos (0 - s) * C|
        = |Real.cos (0 + 1 - s) - Real.cos (0 - s)| * |C| := by rw [← sub_mul, abs_mul]
      _ ≤ (1 : ℝ) * |C| := by exact mul_le_mul_of_nonneg_right hcos (abs_nonneg _)
      _ = |C| * |(1 : ℝ)| := by rw [one_mul, abs_one, mul_one]

end QIQTH.HeatResidualBound
