/-
  WhiteCapstoneWire — J4-634: the CAPSTONE-SIDE WIDTH RE-THREAD + the K1 scope.  ONE brick of
  the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING new about the coefficient.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★ PART 1 — THE CAPSTONE WIRE (mechanical, as predicted by the J4-614/617 reads):
  The flat capstone's `hCorrHigher` binder (`TrueKernelA1.trueKernel_diagonal_a1_eq_R6`) is the
  PURE fixed-`t` equality
        `heatConv H (leviSeries E) t 0 0 = (heatKernel1D t 0)^n · (t² · cRem)`
  with `cRem` a free real — consumed by `rw + ring` only, WIDTH-AGNOSTIC.  The genuine content is
  the t-UNIFORM boundedness of `cRem` (else `t²·cRem` is not `O(t²)`).  The J4-633 supplier
  (`WidthFree.white_corrHigher_unconditional`) lands the k ≥ 2 tail at width `max 8 lam` with
        `|cRem_tail| ≤ C_H·C_t·G_{(max 8 lam)t}(0) / pref`.
  The normalization ratio is CONSTANT:  `G_{wt}(0) = (4πwt)^{−n/2}`, `pref = (4πt)^{−n/2}`, so
        `G_{wt}(0)/pref = w^{−n/2} = (√w)⁻ⁿ`  —  t-FREE (`gaussDdim_zero_scale`, proved here).
  ★★ `white_corrHigher_capstone_shaped` packages the FULL `leviSeries E` slot in the EXACT
  capstone binder shape (equality with `cRem := heatConv/(pref·t²)` — the spurious-pin
  normalization one level up — PLUS the t-uniform bound with the explicit `(√(max 8 lam))⁻ⁿ`
  constant folded), from TWO owed inputs on the specific whitened data:
    (i)  the k = 1 budget `|heatConv H E_white| ≤ C₁·G_{(max 8 lam)t}(0)·t²` (K1TransportBudgetW —
         the sole bridge-thread residue), and
    (ii) the Duhamel additivity split `heatConv H (leviSeries E) = −(heatConv H E) + heatConv H
         (leviSeries E + E)` (an integrability carry — DERIVED from the natural integrability
         hypotheses in `heatConv_leviSeries_split`, via `heatConv_add_right` + `heatConv_neg_right`).

  ★ PART 2 — THE K1 SCOPE (the k = 1 thread made precise + two reduction rungs PROVED):
    • `K1TransportBudgetW w` — the width-parametric k = 1 Prop (defeq to the banked
      `CoInstSmoke.K1TransportBudget` at `w = 8`; monotone in `w`).
    • ★ `k1BudgetW_of_pointwise_linear_gain` — the k = 1 budget FALLS from the LINEAR-GAIN
      pointwise column bound `|E(s,p,0)| ≤ C_E·s·G_{ws}(p)`: the width-`w` slice engine
      (`tail_slice_of_pointwise_w`, generic in Φ) + the Duhamel simplex assembly give
      `|heatConv H E| ≤ C_H·√(w/2)ⁿ·C_E·G_{wt}(0)·t²` — same mechanism as the k ≥ 2 tail.
    • ★ `gaussDdim_quadratic_absorb` — the GAUSSIAN MOMENT ABSORPTION `r²·G_τ ≤ 8τ·√2ⁿ·G_{2τ}`
      (from `u·e^{−u} ≤ 1`): a QUADRATIC spatial coefficient converts into a LINEAR time gain.
    • ★ `k1BudgetW_of_quadratic_coeff` / `white_k1_of_quadratic_coeff` — hence the k = 1 budget
      REDUCES to the quadratic-coefficient column bound on the whitened defect
          `|E_white(s,p,0)| ≤ C_E·r(p)²·G_{ws}(p)`   (the J4-635 target Prop),
      which is exactly the shape the whitened center gauge makes plausible: the whitened chart
      diagonal defect is EXACTLY 0 (`whiteChart_heatOp_diag_clean`, J4-622) and the whitened
      value jet is exactly `δ` with `O(‖w‖²)` deviation (`whitePullbackMetricInv_dev_uniform`) —
      the CenterZero mechanism at the whitened row.  ⚠ NOT proved here: whether `E_white`
      SATISFIES the quadratic-coefficient bound (its far/off-diagonal part is the labelled
      producer residue) — that is the genuinely owed analytic content of the k = 1 wall.

  ⚠ HONEST FRAMING.  `a₁ = R/6` remains CONDITIONAL: the flat tower is closed and non-vacuous;
  the curved side still owes the K1TransportBudget content (here REDUCED to the whitened
  quadratic-coefficient column bound — reduced, NOT discharged), the Duhamel split integrability
  carry, the fat-K carrier piles, the capstone co-instantiation at the whitened witness, and the
  prior piles.  Nothing here proves anything about the coefficient.  No axioms, no `sorry`,
  no `:= True`.
-/
import Mathlib
import QIQTH.WidthFree
import QIQTH.DuhamelSimplexAssembly

open Finset Filter Topology MeasureTheory
open scoped Interval
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.AlphaLevi QIQTH.FrozenWire QIQTH.FrozenColumn
open QIQTH.FrozenK2 QIQTH.FrozenK2Sharp QIQTH.CoInstSmoke QIQTH.BridgeDefect QIQTH.BridgeWidth
open QIQTH.WhiteGated QIQTH.WhiteAnnulus QIQTH.WhiteBridge QIQTH.WhiteS1C QIQTH.WidthFree

namespace QIQTH.WhiteCapstoneWire

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. The `w^{−n/2}` normalization arithmetic (the constant of the re-thread). -/

/-- **The 1-D diagonal width scaling** `heatKernel1D (w·t) 0 = (√w)⁻¹ · heatKernel1D t 0`:
    the diagonal value carries the width only through the prefactor `(4πwt)^{−1/2}`. -/
theorem heatKernel1D_zero_scale (w t : ℝ) (hw : 0 ≤ w) :
    heatKernel1D (w * t) 0 = (Real.sqrt w)⁻¹ * heatKernel1D t 0 := by
  unfold heatKernel1D
  rw [show (4 : ℝ) * Real.pi * (w * t) = w * (4 * Real.pi * t) by ring,
    Real.sqrt_mul hw (4 * Real.pi * t), mul_inv]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
    Real.exp_zero, mul_one]

/-- **★ The diagonal-peak width ratio is a CONSTANT** — the `w^{−n/2}` arithmetic of the
    capstone re-thread:  `G_{wt}(0) = (√w)⁻ⁿ · (heatKernel1D t 0)ⁿ`, i.e. the J4-633 landing
    `G_{(max 8 lam)t}(0)` divided by the capstone prefactor `pref = (heatKernel1D t 0)ⁿ` is the
    t-FREE constant `(√(max 8 lam))⁻ⁿ`.  This is what makes the bounded-`cRem` layer t-uniform
    at ANY landing width. -/
theorem gaussDdim_zero_scale (w t : ℝ) (hw : 0 ≤ w) :
    gaussDdim (w * t) (0 : Point n)
      = (Real.sqrt w)⁻¹ ^ n * (heatKernel1D t 0) ^ n := by
  unfold gaussDdim
  have hconst : ∀ k : Fin n, heatKernel1D (w * t) ((0 : Point n) k)
      = (Real.sqrt w)⁻¹ * heatKernel1D t 0 := fun _ => heatKernel1D_zero_scale w t hw
  rw [Finset.prod_congr rfl (fun k _ => hconst k), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_pow]

/-! ### 2. `heatConv` negation + the k = 1 / tail SPLIT of the capstone slot. -/

/-- **Right negation** `A * (−B) = −(A * B)` — pure scalar pull-out, no integrability needed. -/
theorem heatConv_neg_right (A B : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n) :
    heatConv A (fun τ p q => -(B τ p q)) t x y = -(heatConv A B t x y) := by
  have h := heatConv_smul_right (-1) A B t x y
  simpa [neg_one_mul] using h

/-- **★ `heatConv_leviSeries_split` — the k = 1 isolation at the VALUE level.**  The pointwise
    accounting `leviSeries E = −E + (leviSeries E + E)` (`CoInstSmoke.leviSeries_split`) pushed
    through the Duhamel convolution:
        `heatConv H (leviSeries E) = −(heatConv H E) + heatConv H (leviSeries E + E)`,
    under the natural integrability carries (inner `z`-integrand + outer `s`-integrand of each
    summand — genuine, labelled; `heatConv_add_right` + `heatConv_neg_right`).  This is the
    (ii)-input of the capstone wire, DERIVED from integrability. -/
theorem heatConv_leviSeries_split (H E : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (hIntE : ∀ s, Integrable (fun z => H (t - s) x z * E s z y))
    (hIntTail : ∀ s, Integrable (fun z => H (t - s) x z * (leviSeries E s z y + E s z y)))
    (hIIE : IntervalIntegrable (fun s => ∫ z, H (t - s) x z * E s z y) volume 0 t)
    (hIITail : IntervalIntegrable
      (fun s => ∫ z, H (t - s) x z * (leviSeries E s z y + E s z y)) volume 0 t) :
    heatConv H (leviSeries E) t x y
      = -(heatConv H E t x y)
        + heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t x y := by
  have hIntNeg : ∀ s, Integrable (fun z => H (t - s) x z * -(E s z y)) := by
    intro s
    simpa [mul_neg] using (hIntE s).neg
  have hIINeg : IntervalIntegrable (fun s => ∫ z, H (t - s) x z * -(E s z y)) volume 0 t := by
    have hfun : (fun s => ∫ z, H (t - s) x z * -(E s z y))
        = fun s => -(∫ z, H (t - s) x z * E s z y) := by
      funext s
      rw [← MeasureTheory.integral_neg]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    rw [hfun]
    exact hIIE.neg
  have hBeq : leviSeries E = fun σ p q => -(E σ p q) + (leviSeries E σ p q + E σ p q) := by
    funext σ p q; ring
  calc heatConv H (leviSeries E) t x y
      = heatConv H (fun σ p q => -(E σ p q) + (leviSeries E σ p q + E σ p q)) t x y :=
        congrArg (fun B => heatConv H B t x y) hBeq
    _ = heatConv H (fun σ p q => -(E σ p q)) t x y
          + heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t x y :=
        heatConv_add_right H (fun σ p q => -(E σ p q))
          (fun σ p q => leviSeries E σ p q + E σ p q) t x y hIntNeg hIntTail hIINeg hIITail
    _ = -(heatConv H E t x y)
          + heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t x y := by
        rw [heatConv_neg_right]

/-! ### 3. ★ The width-parametric k = 1 Prop. -/

/-- **★ `K1TransportBudgetW` — the width-parametric k = 1 owed Prop** (the transport-cancellation
    thread): the leading Duhamel correction `H ∗ E` is `O(t²)` on the diagonal, landing at
    `G_{wt}(0)`.  `K1TransportBudget = K1TransportBudgetW 8` (definitional, gate below). -/
def K1TransportBudgetW (w : ℝ) (H E : ℝ → Point n → Point n → ℝ) : Prop :=
  ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
    |heatConv H E t 0 0| ≤ C₁ * gaussDdim (w * t) (0 : Point n) * t ^ 2

/-- **Gate: the width-parametric k = 1 Prop at `w = 8` IS the banked Prop** (definitional). -/
theorem k1TransportBudgetW_eight_iff (H E : ℝ → Point n → Point n → ℝ) :
    K1TransportBudgetW 8 H E ↔ K1TransportBudget H E := Iff.rfl

/-- **Width monotonicity of the k = 1 Prop**: `0 < w ≤ w'` widens the landing at cost
    `√(w'/w)ⁿ` folded into the constant. -/
theorem k1TransportBudgetW_mono {w w' : ℝ} (hw : 0 < w) (hww : w ≤ w')
    (H E : ℝ → Point n → Point n → ℝ) (h : K1TransportBudgetW w H E) :
    K1TransportBudgetW w' H E := by
  obtain ⟨C₁, hC₁, hb⟩ := h
  refine ⟨C₁ * Real.sqrt (w' / w) ^ n, mul_nonneg hC₁ (by positivity), fun t ht ht1 => ?_⟩
  have hwide : gaussDdim (w * t) (0 : Point n)
      ≤ Real.sqrt (w' / w) ^ n * gaussDdim (w' * t) (0 : Point n) :=
    gaussDdim_le_of_width_le w w' hw hww ht (0 : Point n)
  calc |heatConv H E t 0 0|
      ≤ C₁ * gaussDdim (w * t) (0 : Point n) * t ^ 2 := hb t ht ht1
    _ ≤ C₁ * (Real.sqrt (w' / w) ^ n * gaussDdim (w' * t) (0 : Point n)) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwide hC₁) (by positivity)
    _ = C₁ * Real.sqrt (w' / w) ^ n * gaussDdim (w' * t) (0 : Point n) * t ^ 2 := by ring

/-! ### 4. ★★ THE CAPSTONE WIRE — the full `leviSeries E` slot in the EXACT binder shape. -/

/-- **★★ `white_corrHigher_capstone_shaped` — the capstone-side width re-thread (J4-634).**
    From the J4-633 supplier alone, for every fat compact whitened datum there are a gate
    `S`, radii `0 < a < b`, a width `lam ≥ 2` and a tail constant `C_t ≥ 0` such that for EVERY
    Gaussian-dominated slice kernel `H` (with `H(0,0,·) = 0`) and every carried
      (i)  k = 1 budget `|heatConv H E_white| ≤ C₁·G_{(max 8 lam)t}(0)·t²` (the sole
           bridge-thread residue, `K1TransportBudgetW (max 8 lam)` unfolded), and
      (ii) Duhamel split `heatConv H (leviSeries E) = −(heatConv H E) + heatConv H (tail)`
           (the integrability carry, derivable via `heatConv_leviSeries_split`),
    the FULL capstone `hCorrHigher` slot holds in the EXACT binder shape of
    `trueKernel_diagonal_a1_eq_R6` at `cRem := heatConv/(pref·t²)`:
        `heatConv H (leviSeries E_white) t 0 0 = (heatKernel1D t 0)ⁿ · (t² · cRem)`
    WITH the t-UNIFORM bound
        `|cRem| ≤ (C_H·C_t + C₁) · (√(max 8 lam))⁻ⁿ`
    — the landing-width Gaussian is absorbed into the T-FREE constant `w^{−n/2}` (the
    normalization ratio `G_{wt}(0)/pref`), so the width re-thread is MECHANICAL, exactly the
    spurious-pin pattern one level up.  ⚠ NOT `a₁ = R/6`: (i) and (ii) are genuinely owed
    (see Part 2 for the reduction of (i)), plus fat-K carriers + capstone co-instantiation. -/
theorem white_corrHigher_capstone_shaped (P : FatFrozenPackage n)
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
            ∀ C₁ : ℝ, 0 ≤ C₁ →
            (∀ t : ℝ, 0 < t → t ≤ 1 →
              |heatConv H (whiteDefectKernel κ hκ hKc S a b) t 0 0|
                ≤ C₁ * gaussDdim (max 8 lam * t) (0 : Point n) * t ^ 2) →
            (∀ t : ℝ, 0 < t → t ≤ 1 →
              heatConv H (leviSeries (whiteDefectKernel κ hκ hKc S a b)) t 0 0
                = -(heatConv H (whiteDefectKernel κ hκ hKc S a b) t 0 0)
                  + heatConv H (fun σ p q =>
                      leviSeries (whiteDefectKernel κ hκ hKc S a b) σ p q
                        + whiteDefectKernel κ hκ hKc S a b σ p q) t 0 0) →
            ∀ t : ℝ, 0 < t → t ≤ 1 →
              (heatConv H (leviSeries (whiteDefectKernel κ hκ hKc S a b)) t 0 0
                = (heatKernel1D t 0) ^ n
                  * (t ^ 2
                      * (heatConv H (leviSeries (whiteDefectKernel κ hκ hKc S a b)) t 0 0
                          / ((heatKernel1D t 0) ^ n * t ^ 2))))
              ∧ |heatConv H (leviSeries (whiteDefectKernel κ hκ hKc S a b)) t 0 0
                    / ((heatKernel1D t 0) ^ n * t ^ 2)|
                  ≤ (C_H * C_t + C₁) * (Real.sqrt (max 8 lam))⁻¹ ^ n := by
  obtain ⟨S, a, b, ha, hab, hfat, lam, hlam2, C_t, hCt, hall⟩ :=
    white_corrHigher_unconditional P hn κ hκ hKc R hKb
  refine ⟨S, a, b, ha, hab, hfat, lam, hlam2, C_t, hCt, ?_⟩
  intro H C_H hCH hHdom hH0 C₁ hC₁ hK1 hsplit t ht ht1
  set E := whiteDefectKernel κ hκ hKc S a b with hEdef
  have hk : 0 < heatKernel1D t 0 := by
    unfold heatKernel1D
    positivity
  have hprefpos : 0 < (heatKernel1D t 0) ^ n := pow_pos hk n
  have hpref : (heatKernel1D t 0) ^ n ≠ 0 := ne_of_gt hprefpos
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hptpos : 0 < (heatKernel1D t 0) ^ n * t ^ 2 := mul_pos hprefpos ht2
  have hpt2 : (heatKernel1D t 0) ^ n * t ^ 2 ≠ 0 := ne_of_gt hptpos
  obtain ⟨heqT, hbdT, hremT⟩ :=
    hall H C_H hCH hHdom hH0 ((heatKernel1D t 0) ^ n) t ht ht1 hpref
  have hw0 : (0 : ℝ) ≤ max 8 lam := le_trans (by norm_num) (le_max_left _ _)
  have hG : gaussDdim (max 8 lam * t) (0 : Point n)
      = (Real.sqrt (max 8 lam))⁻¹ ^ n * (heatKernel1D t 0) ^ n :=
    gaussDdim_zero_scale (max 8 lam) t hw0
  -- the t-uniform O(t²) bound on the FULL slot value, via the split + the two budgets
  have habs : |heatConv H (leviSeries E) t 0 0|
      ≤ (C_H * C_t + C₁) * gaussDdim (max 8 lam * t) (0 : Point n) * t ^ 2 := by
    rw [hsplit t ht ht1]
    calc |(-(heatConv H E t 0 0))
            + heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0|
        ≤ |(-(heatConv H E t 0 0))|
            + |heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0| :=
          abs_add_le _ _
      _ = |heatConv H E t 0 0|
            + |heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0| := by
          rw [abs_neg]
      _ ≤ C₁ * gaussDdim (max 8 lam * t) (0 : Point n) * t ^ 2
            + (C_H * C_t * gaussDdim (max 8 lam * t) (0 : Point n)) * t ^ 2 :=
          add_le_add (hK1 t ht ht1) hbdT
      _ = (C_H * C_t + C₁) * gaussDdim (max 8 lam * t) (0 : Point n) * t ^ 2 := by ring
  refine ⟨?_, ?_⟩
  · -- the EXACT capstone binder equality at `cRem := heatConv/(pref·t²)`
    field_simp
  · -- the t-UNIFORM bound: the landing Gaussian folds into the constant `(√(max 8 lam))⁻ⁿ`
    rw [abs_div, abs_of_pos hptpos, div_le_iff₀ hptpos]
    calc |heatConv H (leviSeries E) t 0 0|
        ≤ (C_H * C_t + C₁) * gaussDdim (max 8 lam * t) (0 : Point n) * t ^ 2 := habs
      _ = ((C_H * C_t + C₁) * (Real.sqrt (max 8 lam))⁻¹ ^ n)
            * ((heatKernel1D t 0) ^ n * t ^ 2) := by
          rw [hG]; ring

/-! ### 5. ★ The K1 reduction ladder (the k = 1 scope, theorem-level pieces). -/

/-- **★ `k1BudgetW_of_pointwise_linear_gain` — RUNG 1: the k = 1 budget from the LINEAR time
    gain.**  If the defect's center column obeys `|E(s,p,0)| ≤ C_E·s·G_{ws}(p)` (ONE extra
    power of `s` over the raw `O(1)·G` pkg bound), the k = 1 budget holds at width `w` with
    `C₁ = C_H·√(w/2)ⁿ·C_E` — the SAME slice + simplex mechanism as the banked k ≥ 2 tail
    (`tail_slice_of_pointwise_w`, generic in the column, + `duhamel_simplex_quadratic_bound`). -/
theorem k1BudgetW_of_pointwise_linear_gain (w : ℝ) (hw2 : 2 ≤ w)
    (E : ℝ → Point n → Point n → ℝ) (C_E : ℝ) (hCE : 0 ≤ C_E)
    (hE : ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |E s p 0| ≤ C_E * (s * gaussDdim (w * s) (p - 0)))
    (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ) (hCH : 0 ≤ C_H)
    (hH : ∀ (a : ℝ) (ζ : Point n), 0 < a →
      |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ))
    (hH0 : ∀ ζ : Point n, H 0 0 ζ = 0) :
    K1TransportBudgetW w H E := by
  refine ⟨C_H * (Real.sqrt (w / 2) ^ n * C_E),
    mul_nonneg hCH (mul_nonneg (by positivity) hCE), fun t ht ht1 => ?_⟩
  have hsl := tail_slice_of_pointwise_w w hw2 (fun s p => E s p 0) C_E hCE hE H C_H hCH hH
  set Kt : ℝ := C_H * (Real.sqrt (w / 2) ^ n * C_E) * gaussDdim (w * t) (0 : Point n)
    with hKtdef
  have hKt0 : 0 ≤ Kt := by
    rw [hKtdef]
    exact mul_nonneg (mul_nonneg hCH (mul_nonneg (by positivity) hCE))
      (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  have hslice : ∀ s ∈ Ι (0 : ℝ) t,
      ‖∫ z, H (t - s) 0 z * E s z 0‖ ≤ Kt * ((t - s) + s) := by
    intro s hs
    have hs' : s ∈ Set.Ioc (0 : ℝ) t := by rwa [Set.uIoc_of_le ht.le] at hs
    rcases lt_or_eq_of_le hs'.2 with hst | hseq
    · calc ‖∫ z, H (t - s) 0 z * E s z 0‖
          ≤ (C_H * (Real.sqrt (w / 2) ^ n * C_E))
              * (s * gaussDdim (w * t) (0 : Point n)) :=
            hsl t s hs'.1 hst (le_trans hs'.2 ht1)
        _ = Kt * s := by rw [hKtdef]; ring
        _ ≤ Kt * ((t - s) + s) :=
            mul_le_mul_of_nonneg_left (by linarith) hKt0
    · have hzero : (fun z => H (t - s) 0 z * E s z 0) = fun _ => (0 : ℝ) := by
        funext z
        rw [hseq, sub_self, hH0 z, zero_mul]
      rw [hzero, MeasureTheory.integral_zero, norm_zero]
      have hts : (t - s) + s = t := by ring
      rw [hts]
      exact mul_nonneg hKt0 ht.le
  have hbound : ‖heatConv H E t 0 0‖ ≤ Kt * t ^ 2 :=
    QIQTH.DuhamelAssembly.duhamel_simplex_quadratic_bound
      (fun a s' => ∫ z, H a 0 z * E s' z 0) Kt t ht.le hslice
  rw [Real.norm_eq_abs] at hbound
  exact hbound

/-- **★ `gaussDdim_quadratic_absorb` — RUNG 2: the Gaussian MOMENT ABSORPTION.**  A quadratic
    spatial factor is absorbed into a linear time factor at one width doubling:
        `r(p)² · G_τ(p) ≤ 8τ · √2ⁿ · G_{2τ}(p)`
    (from `u·e^{−u} ≤ 1` at `u = r²/(8τ)`; prefactor bridge `(√(4πτ))⁻ⁿ = √2ⁿ·(√(8πτ))⁻ⁿ`).
    This is the mechanism by which the whitened CENTER-ZERO structure (quadratic coefficient)
    would produce the linear gain of RUNG 1. -/
theorem gaussDdim_quadratic_absorb (τ : ℝ) (hτ : 0 < τ) (p : Point n) :
    rncRadialSq p * gaussDdim τ p
      ≤ (8 * τ) * (Real.sqrt 2 ^ n * gaussDdim (2 * τ) p) := by
  have hr2 : 0 ≤ rncRadialSq p := rncRadialSq_nonneg p
  rw [QIQTH.GaussianWidthTransfer.gaussDdim_closed τ p,
    QIQTH.GaussianWidthTransfer.gaussDdim_closed (2 * τ) p]
  simp only [neg_div]
  set r2 := rncRadialSq p with hr2def
  have harg : (4 : ℝ) * (2 * τ) = 8 * τ := by ring
  rw [harg]
  -- prefactor bridge
  have hpref : Real.sqrt 2 ^ n * ((Real.sqrt (4 * Real.pi * (2 * τ)))⁻¹) ^ n
      = ((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n := by
    rw [← mul_pow]
    congr 1
    rw [show (4 : ℝ) * Real.pi * (2 * τ) = 2 * (4 * Real.pi * τ) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv]
    have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  -- exponent split
  have hsplit : Real.exp (-(r2 / (4 * τ)))
      = Real.exp (-(r2 / (8 * τ))) * Real.exp (-(r2 / (8 * τ))) := by
    rw [← Real.exp_add]
    congr 1
    have h4 : (4 : ℝ) * τ ≠ 0 := by positivity
    have h8 : (8 : ℝ) * τ ≠ 0 := by positivity
    field_simp
    ring
  -- the moment bound `r² · e^{−r²/(8τ)} ≤ 8τ` from `u·e^{−u} ≤ 1`
  have hmom : r2 * Real.exp (-(r2 / (8 * τ))) ≤ 8 * τ := by
    have h8 : (0 : ℝ) < 8 * τ := by positivity
    have hexp_pos : 0 < Real.exp (r2 / (8 * τ)) := Real.exp_pos _
    have hu : r2 / (8 * τ) ≤ Real.exp (r2 / (8 * τ)) := by
      have := Real.add_one_le_exp (r2 / (8 * τ))
      linarith
    have h1 : r2 / (8 * τ) * Real.exp (-(r2 / (8 * τ))) ≤ 1 := by
      rw [Real.exp_neg, mul_inv_le_iff₀ hexp_pos, one_mul]
      exact hu
    have h2 : r2 * Real.exp (-(r2 / (8 * τ)))
        = (8 * τ) * (r2 / (8 * τ) * Real.exp (-(r2 / (8 * τ)))) := by
      field_simp
    rw [h2]
    calc (8 * τ) * (r2 / (8 * τ) * Real.exp (-(r2 / (8 * τ))))
        ≤ (8 * τ) * 1 := mul_le_mul_of_nonneg_left h1 h8.le
      _ = 8 * τ := mul_one _
  rw [hsplit]
  calc r2 * (((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n
        * (Real.exp (-(r2 / (8 * τ))) * Real.exp (-(r2 / (8 * τ)))))
      = (((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n * Real.exp (-(r2 / (8 * τ))))
          * (r2 * Real.exp (-(r2 / (8 * τ)))) := by ring
    _ ≤ (((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n * Real.exp (-(r2 / (8 * τ))))
          * (8 * τ) := mul_le_mul_of_nonneg_left hmom (by positivity)
    _ = (8 * τ) * (Real.sqrt 2 ^ n
          * (((Real.sqrt (4 * Real.pi * (2 * τ)))⁻¹) ^ n * Real.exp (-(r2 / (8 * τ))))) := by
        rw [show Real.sqrt 2 ^ n
              * (((Real.sqrt (4 * Real.pi * (2 * τ)))⁻¹) ^ n * Real.exp (-(r2 / (8 * τ))))
            = (Real.sqrt 2 ^ n * ((Real.sqrt (4 * Real.pi * (2 * τ)))⁻¹) ^ n)
              * Real.exp (-(r2 / (8 * τ))) from by ring, hpref]
        ring

/-- **★ `k1BudgetW_of_quadratic_coeff` — RUNG 1 ∘ RUNG 2: the k = 1 budget from the QUADRATIC
    spatial coefficient.**  If `|E(s,p,0)| ≤ C_E·r(p)²·G_{ws}(p)` (the CenterZero-shaped column
    bound), the k = 1 budget holds at width `2w` with `C₁ = C_H·√w ⁿ·(C_E·8w·√2ⁿ)`:
    absorption converts `r²·G_{ws}` into `(8ws·√2ⁿ)·G_{2ws}` — the linear gain — and RUNG 1
    finishes.  The k = 1 wall is thereby REDUCED to the quadratic-coefficient bound. -/
theorem k1BudgetW_of_quadratic_coeff (w : ℝ) (hw2 : 2 ≤ w)
    (E : ℝ → Point n → Point n → ℝ) (C_E : ℝ) (hCE : 0 ≤ C_E)
    (hE : ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |E s p 0| ≤ C_E * (rncRadialSq (p - 0) * gaussDdim (w * s) (p - 0)))
    (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ) (hCH : 0 ≤ C_H)
    (hH : ∀ (a : ℝ) (ζ : Point n), 0 < a →
      |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ))
    (hH0 : ∀ ζ : Point n, H 0 0 ζ = 0) :
    K1TransportBudgetW (2 * w) H E := by
  have hw0 : (0 : ℝ) < w := lt_of_lt_of_le two_pos hw2
  refine k1BudgetW_of_pointwise_linear_gain (2 * w) (by linarith) E
    (C_E * (8 * w * Real.sqrt 2 ^ n))
    (mul_nonneg hCE (by positivity)) ?_ H C_H hCH hH hH0
  intro s p hs hs1
  calc |E s p 0|
      ≤ C_E * (rncRadialSq (p - 0) * gaussDdim (w * s) (p - 0)) := hE s p hs hs1
    _ ≤ C_E * ((8 * (w * s)) * (Real.sqrt 2 ^ n * gaussDdim (2 * (w * s)) (p - 0))) :=
        mul_le_mul_of_nonneg_left
          (gaussDdim_quadratic_absorb (w * s) (mul_pos hw0 hs) (p - 0)) hCE
    _ = (C_E * (8 * w * Real.sqrt 2 ^ n)) * (s * gaussDdim (2 * w * s) (p - 0)) := by
        rw [show (2 : ℝ) * (w * s) = 2 * w * s from (mul_assoc 2 w s).symm]
        ring

/-- **★ `white_k1_of_quadratic_coeff` — THE PRECISE K1 Prop AT THE WHITENED WITNESS.**  The sole
    remaining k = 1 antecedent is the quadratic-coefficient column bound on the whitened defect
        `|E_white(s,p,0)| ≤ C_E · r(p)² · G_{ws}(p)`   on `(0,1]`
    — the J4-635 target.  Motivation (NOT proof): the whitened chart diagonal defect is EXACTLY
    zero (`whiteChart_heatOp_diag_clean`) and the whitened value jet deviates from `δ` only at
    `O(‖p‖²)` (`whitePullbackMetricInv_dev_uniform`), so the defect's amplitude coefficient
    plausibly vanishes quadratically at the chart origin; the far/off-diagonal `O(1)·G` part
    must ALSO be re-expressed through the `r²` factor (it dominates `G` off a ball) — the
    genuinely owed analytic content.  Given it, the k = 1 budget lands at width `2w`. -/
theorem white_k1_of_quadratic_coeff (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (w : ℝ) (hw2 : 2 ≤ w) (C_E : ℝ) (hCE : 0 ≤ C_E)
    (hE : ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |whiteDefectKernel κ hκ hKc S a b s p 0|
        ≤ C_E * (rncRadialSq (p - 0) * gaussDdim (w * s) (p - 0)))
    (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ) (hCH : 0 ≤ C_H)
    (hH : ∀ (a' : ℝ) (ζ : Point n), 0 < a' →
      |H a' 0 ζ| ≤ C_H * gaussDdim (2 * a') ((0 : Point n) - ζ))
    (hH0 : ∀ ζ : Point n, H 0 0 ζ = 0) :
    K1TransportBudgetW (2 * w) H (whiteDefectKernel κ hκ hKc S a b) :=
  k1BudgetW_of_quadratic_coeff w hw2 _ C_E hCE hE H C_H hCH hH hH0

/-! ### 6. Non-vacuity / adversarial gates (cp466 discipline). -/

/-- **The linear-gain probe kernel** — a genuinely NONZERO kernel satisfying the RUNG-1
    antecedent with `C_E = 1` (window-gated `s·G_{ws}`). -/
noncomputable def k1ProbeKernel (w : ℝ) : ℝ → Point n → Point n → ℝ :=
  fun s p _ => if 0 < s ∧ s ≤ 1 then s * gaussDdim (w * s) (p - 0) else 0

/-- The probe satisfies the linear-gain column bound with `C_E = 1`. -/
theorem k1Probe_linear_gain (w : ℝ) :
    ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |k1ProbeKernel w s p 0| ≤ 1 * (s * gaussDdim (w * s) (p - 0)) := by
  intro s p hs hs1
  simp only [k1ProbeKernel]
  rw [if_pos ⟨hs, hs1⟩, one_mul,
    abs_of_nonneg (mul_nonneg hs.le (QIQTH.ResidueBound.gaussDdim_nonneg _ _))]

/-- The probe is genuinely nonzero (at `s = 1`, `p = 0`). -/
theorem k1Probe_ne_zero (w : ℝ) (hw : 0 < w) :
    k1ProbeKernel (n := n) w 1 0 0 ≠ 0 := by
  have hpos : 0 < gaussDdim (w * 1) ((0 : Point n) - (0 : Point n)) := by
    rw [sub_zero]
    unfold gaussDdim
    refine Finset.prod_pos fun k _ => ?_
    show 0 < heatKernel1D (w * 1) 0
    unfold heatKernel1D
    positivity
  simp only [k1ProbeKernel]
  rw [if_pos ⟨one_pos, le_refl (1 : ℝ)⟩, one_mul]
  exact ne_of_gt hpos

/-- **Gate 1 — RUNG 1 FIRES at a genuinely nonzero column and a genuinely nonzero slice
    kernel** (`n = 2`, `w = 8`, the banked Gaussian witness `H`): the K1 reduction is not
    `∅`-degenerate on either side. -/
theorem white_k1_reduction_gate :
    K1TransportBudgetW (n := 2) 8
      (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ)) (k1ProbeKernel 8)
    ∧ k1ProbeKernel (n := 2) 8 1 0 0 ≠ 0 := by
  refine ⟨?_, k1Probe_ne_zero 8 (by norm_num)⟩
  have hW := frozenK2Sharp_H_witness (n := 2) (by norm_num)
  exact k1BudgetW_of_pointwise_linear_gain 8 (by norm_num) (k1ProbeKernel 8) 1 zero_le_one
    (k1Probe_linear_gain 8) (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ)) 1
    zero_le_one (fun a ζ ha => hW.1 a ζ ha) (fun ζ => hW.2.1 ζ)

/-- **Gate 2 — the absorption input is non-degenerate**: at `n = 2`, `p = (1,1)` the quadratic
    moment `r(p)²·G₁(p)` is strictly positive — `gaussDdim_quadratic_absorb` bounds a genuinely
    nonzero quantity, it does not close on `0 ≤ 0`. -/
theorem absorb_gate :
    0 < rncRadialSq ((fun _ => (1 : ℝ)) : Point 2)
        * gaussDdim 1 ((fun _ => (1 : ℝ)) : Point 2) := by
  have h2 : 0 < gaussDdim 1 ((fun _ => (1 : ℝ)) : Point 2) := by
    unfold gaussDdim
    refine Finset.prod_pos fun k _ => ?_
    show 0 < heatKernel1D 1 1
    unfold heatKernel1D
    positivity
  have h1 : 0 < rncRadialSq ((fun _ => (1 : ℝ)) : Point 2) := by
    norm_num [rncRadialSq, Fin.sum_univ_two]
  exact mul_pos h1 h2

/-- **Gate 3 — the capstone wire FIRES end-to-end at genuinely curved fat data** (`n = 2`,
    `κ = −1`, `K = B̄(0,2)`), with ALL antecedents discharged at the DEGENERATE slice kernel
    `H = 0` (⚠ honest label: this certifies joint SATISFIABILITY / non-contradiction of the
    antecedent stack and inhabitation of the capstone-shaped conclusion; the nonzero-`H`
    instantiation additionally owes exactly (i) the K1 budget and (ii) the split carry). -/
theorem white_capstone_wire_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b lam C_c : ℝ, 0 ≤ C_c ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
        ∃ cRem : ℝ,
          heatConv (fun _ _ _ => (0 : ℝ))
              (leviSeries (whiteDefectKernel (-1 : ℝ) (by norm_num)
                (isCompact_closedBall (0 : Point 2) 2) S a b)) t 0 0
            = (heatKernel1D t 0) ^ 2 * (t ^ 2 * cRem)
          ∧ |cRem| ≤ C_c := by
  obtain ⟨P⟩ := fatFrozenPackage_inhabited 2 le_rfl
  obtain ⟨S, a, b, ha, hab, hfat, lam, hlam2, C_t, hCt, hall⟩ :=
    white_corrHigher_capstone_shaped P (by norm_num) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
  refine ⟨S, a, b, lam, (0 * C_t + 0) * (Real.sqrt (max 8 lam))⁻¹ ^ 2,
    mul_nonneg (by norm_num) (by positivity), fun t ht ht1 => ?_⟩
  have hout := hall (fun _ _ _ => (0 : ℝ)) 0 le_rfl
    (fun a' ζ _ => by
      simp only [abs_zero, zero_mul]
      exact le_refl (0 : ℝ))
    (fun ζ => rfl) 0 le_rfl
    (fun t' ht' ht1' => by
      rw [heatConv_zero_left]
      simp)
    (fun t' ht' ht1' => by
      simp only [heatConv_zero_left]
      norm_num) t ht ht1
  exact ⟨_, hout.1, hout.2⟩

/-- **Gate 4 — the folded constant is the honest `w^{−n/2}`**: at `w = 8`, `n = 2` the fold is
    exactly `1/8` — a concrete nonzero value (the normalization ratio does not collapse). -/
theorem width8_fold_value : ((Real.sqrt 8)⁻¹ : ℝ) ^ 2 = 1 / 8 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  norm_num

end QIQTH.WhiteCapstoneWire

-- std-3 verification (chk): READ these outputs — no sorryAx, no extra axioms.
#print axioms QIQTH.WhiteCapstoneWire.heatKernel1D_zero_scale
#print axioms QIQTH.WhiteCapstoneWire.gaussDdim_zero_scale
#print axioms QIQTH.WhiteCapstoneWire.heatConv_neg_right
#print axioms QIQTH.WhiteCapstoneWire.heatConv_leviSeries_split
#print axioms QIQTH.WhiteCapstoneWire.k1TransportBudgetW_eight_iff
#print axioms QIQTH.WhiteCapstoneWire.k1TransportBudgetW_mono
#print axioms QIQTH.WhiteCapstoneWire.white_corrHigher_capstone_shaped
#print axioms QIQTH.WhiteCapstoneWire.k1BudgetW_of_pointwise_linear_gain
#print axioms QIQTH.WhiteCapstoneWire.gaussDdim_quadratic_absorb
#print axioms QIQTH.WhiteCapstoneWire.k1BudgetW_of_quadratic_coeff
#print axioms QIQTH.WhiteCapstoneWire.white_k1_of_quadratic_coeff
#print axioms QIQTH.WhiteCapstoneWire.k1Probe_linear_gain
#print axioms QIQTH.WhiteCapstoneWire.k1Probe_ne_zero
#print axioms QIQTH.WhiteCapstoneWire.white_k1_reduction_gate
#print axioms QIQTH.WhiteCapstoneWire.absorb_gate
#print axioms QIQTH.WhiteCapstoneWire.white_capstone_wire_gate
#print axioms QIQTH.WhiteCapstoneWire.width8_fold_value
