/-
  FrozenK2Sharp — J4-616: the refined E∗E center-column composition — THE `O(√s) → O(s)`
  UPGRADE.  |（E∗E)(s, z, 0)| ≤ C·s·G_{8s}(z), restoring the bounded-`cRem` `O(t²)` API.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE MATHEMATICS (Sol route-(a), J4-614/615 verdicts; all suppliers banked J4-609→615).

  (E∗E)(s,z,0) = ∫₀ˢ ∫_w E(s−σ, z, w)·E(σ, w, 0) dw dσ.  The banked mixed ladder (J4-613)
  bounded the OUTER factor by the generic α = −1/2 bound `(C/√a)·G_{2a}` and got only `O(√s)`.
  The genuine `O(s)` needs the STRUCTURED outer bound: with the J4-615 zero-constant-term
  coefficient supplier `|gⁱʲ(z) − gⁱʲ(w)| ≤ L·‖z−w‖·(‖z‖+‖w‖)` (L = 2(−K)/3) and the split
  `‖z‖ ≤ ‖z−w‖ + ‖w‖` (so `‖z‖+‖w‖ ≤ ‖v‖ + 2‖w‖`, v := z−w — NO free unbounded `‖z‖`
  survives), the frozen defect kernel obeys the SHARP two-term bound (§2)

      |E(a, z, w)| ≤ C_A·G_{2a}(z−w) + C_B·‖w‖·a^{−1/2}·G_{2a}(z−w)     (all a > 0):

    ▸ the `‖v‖²` part folds CLEANLY (`‖v‖²·(M/(2a) + n²M²‖v‖²/(4a²)) = (M/2)x + (n²M²/4)x²`,
      x = ‖v‖²/a — a PURE polynomial in x, NO negative power of a; absorbed by the banked
      k = 1, 2 width-2 levers) — the same mechanism as the J4-612 center-zero bound;
    ▸ the `‖v‖·‖w‖` part pays HALF a moment (`‖v‖·(…) ≤ (cB/√a)·√x(1+x)`, absorbed by the
      J4-614 half-cubic lever) and keeps the factor `‖w‖` IN RESERVE.

  In the composition the reserved `‖w‖` is paid against the INNER center-column Gaussian
  (J4-612: `|E(σ,w,0)| ≤ C₀·G_{2σ}(w)`) via the J4-614 moment lever
  `‖w‖·G_{2σ}(w) ≤ C_m·√(2σ)·G_{8σ}(w)` — the `√σ` exactly cancels the outer `a^{−1/2}`'s
  time singularity under the Beta integral:

      TIME LEDGER:  A-term ∫₀ˢ dσ = s;   B-term ∫₀ˢ (s−σ)^{−1/2}·σ^{1/2} dσ ≤ 2s.   BOTH O(s).

  WIDTH LEDGER (every widening accounted):  A-term C-K composition `G_{2(s−σ)} ∗ G_{2σ} = G_{2s}`
  (EXACT, banked semigroup); B-term `G_{2(s−σ)} ∗ G_{8σ} = G_{2s+6σ}`; both widened ONCE to the
  final `G_{8s}` by the banked normalized chart comparison (`c ≤ 8s ≤ 4c` ⟹ factor `≤ 2ⁿ`).
  MOMENT LEDGER: ‖v‖² (outer) → 2 absorbs at width 2 (NO time cost); ‖v‖ (outer) → half-cubic
  absorb at width 2, cost `a^{−1/2}`; ‖w‖ (outer, reserved) → moment vs INNER `G_{2σ}`, width
  `2σ → 8σ`, GAIN `√(2σ)`.  Net: `O(s)` with final width `8s`.

  WHAT LANDS.
    ▸ `sharp_fold_A` / `sharp_fold_B` — the two scalar folds (exact polynomial identity; the
      half-moment scalar inequality).
    ▸ `gaussDdim_widen_le` — the bounded-ratio width widening `G_c ≤ 2ⁿ·G_d` (c ≤ d ≤ 4c).
    ▸ ★ `frozenDefect_outer_sharp` — the SHARPENED outer bound (two-term, all a > 0).
    ▸ `betaHalf_integral_le` — the time integral `∫₀ˢ (s−σ)^{−1/2}·σ^{1/2} dσ ≤ 2s`.
    ▸ ★★ `frozenK2_sharp` — THE COMPOSITION: |iterE E_frozen 2 (s,z,0)| ≤ C·s·G_{8s}(z−0),
      ALL s > 0 (no s ≤ 1 needed!) — the k = 2 term is `O(s)`, upgrading J4-613's `O(√s)`.
    ▸ ★ `frozenColumn_tail_O_s` — the FULL k ≥ 2 tail is `O(s)`:
      |leviSeries E + E| ≤ C·s·G_{8s} on (0,1] (k = 2 sharp + banked k ≥ 3 `O(s)`).
    ▸ ★ `frozenK2_tail_slice_O_s` / `frozenK2_tail_corr_O_t2` — the tail feeds the consumer's
      LINEAR slice budget `K·((t−s)+s)` and assembles to `K·t²` (K carries the diagonal mass
      `G_{8t}(0)` explicitly — t-uniform RELATIVE to the capstone's `pref = (4πt)^{−n/2}`:
      `G_{8t}(0)/pref → 8^{−n/2}`, a genuine constant).
    ▸ ★★ `corrHigher_O_t2_restored` — THE RESTORED BOUNDED-cRem O(t²) API: the hCorrHigher
      equality shape + `|heatConv| ≤ K·t²` + `|cRem| ≤ K/|pref|` — BOUNDED (vs the J4-614
      route-(b) `O(t^{−1/2})`), for the k ≥ 2 tail of the frozen Levi series.
    ▸ NON-VACUITY: `frozenK2Sharp_H_witness` (the Gaussian slice-kernel hypothesis class is
      inhabited by a genuinely nonzero H) + the banked `frozenColumn_witness_ne_zero` (the
      composed column's k = 1 factor is nonzero at curved data K < 0, n ≥ 2).

  ⚠ HONEST SCOPE.  `a₁ = R/6` remains CONDITIONAL: the flat tower is non-vacuous and closed;
  the curved side still owes the k = 1 `SliceBoundO1`/transport-cancellation thread (the `−E`
  term of `leviSeries = −E + tail` is NOT covered by this brick), the per-q producer
  re-assembly, the fat-K hEmeas/hAdom/hcont piles, the capstone co-instantiation, and the
  prior piles.  This brick closes the k = 2 composition: the k ≥ 2 tail now fits the ORIGINAL
  `O((t−s)+s)` slice budget with bounded cRem.  No axioms, no sorry.
-/
import Mathlib
import QIQTH.FrozenK2
import QIQTH.AffineDiff

open Finset Filter Topology MeasureTheory
open scoped Interval
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianWidthTransfer QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.CurvedRNCGaugeBundle QIQTH.FrozenGauss QIQTH.FrozenDefect
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.AlphaLevi QIQTH.FrozenWire QIQTH.FrozenColumn
open QIQTH.FrozenK2 QIQTH.AffineDiff

namespace QIQTH.FrozenK2Sharp

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. The scalar folds and the bounded-ratio width widening. -/

/-- **Scalar fold A** — the `‖v‖²`-part of the structured coefficient folds to a PURE polynomial
    in `x = Q/τ`, with NO negative power of `τ`:
    `Q·(M/(2τ) + c·Q/(4τ²)) = (M/2)·(Q/τ) + (c/4)·(Q/τ)²`.  (Exact identity.) -/
theorem sharp_fold_A (M c τ Q : ℝ) (hτ : 0 < τ) :
    Q * (M / (2 * τ) + c * Q / (4 * τ ^ 2))
      = M / 2 * (Q / τ) + c / 4 * (Q / τ) ^ 2 := by
  field_simp

/-- **Scalar fold B** — the `‖v‖`-part pays exactly HALF a time power:
    `√Q·(M/(2τ) + c·Q/(4τ²)) ≤ ((M/2 + c/4)/√τ)·(√(Q/τ)·(1 + Q/τ))` — the right side is the
    exact half-cubic absorb shape of the banked `gaussDdim_absorb_half_cubic`. -/
theorem sharp_fold_B (M c τ Q : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c) (hτ : 0 < τ) (hQ : 0 ≤ Q) :
    Real.sqrt Q * (M / (2 * τ) + c * Q / (4 * τ ^ 2))
      ≤ (M / 2 + c / 4) / Real.sqrt τ * (Real.sqrt (Q / τ) * (1 + Q / τ)) := by
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hτs : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ.le
  set u := Real.sqrt (Q / τ) with hudef
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u * u = Q / τ := Real.mul_self_sqrt (div_nonneg hQ hτ.le)
  have hsq : Real.sqrt Q = Real.sqrt τ * u := by
    rw [hudef, ← Real.sqrt_mul hτ.le, mul_comm τ (Q / τ), div_mul_cancel₀ Q hτ.ne']
  have hQeq : Q = τ * (u * u) := by
    rw [hu2, mul_comm τ (Q / τ), div_mul_cancel₀ Q hτ.ne']
  rw [hsq, div_mul_eq_mul_div, le_div_iff₀ hst]
  calc Real.sqrt τ * u * (M / (2 * τ) + c * Q / (4 * τ ^ 2)) * Real.sqrt τ
      = (Real.sqrt τ * Real.sqrt τ) * (u * (M / (2 * τ) + c * Q / (4 * τ ^ 2))) := by ring
    _ = τ * (u * (M / (2 * τ) + c * Q / (4 * τ ^ 2))) := by rw [hτs]
    _ = M / 2 * u + c / 4 * (u * (Q / τ)) := by
        field_simp
    _ = M / 2 * u + c / 4 * (u * (u * u)) := by rw [← hu2]
    _ ≤ (M / 2 + c / 4) * (u * (1 + u * u)) := by nlinarith [mul_nonneg hu0 (mul_nonneg hu0 hu0)]
    _ = (M / 2 + c / 4) * (u * (1 + Q / τ)) := by rw [hu2]

/-- **Bounded-ratio width widening** — `G_c(v) ≤ 2ⁿ·G_d(v)` whenever `c ≤ d ≤ 4c` (the banked
    normalized chart comparison at `τ = 1`, `w = v`; ratio `d/c ≤ 4` so the factor is `≤ 2ⁿ`). -/
theorem gaussDdim_widen_le (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) (hd4 : d ≤ 4 * c)
    (v : Point n) :
    gaussDdim c v ≤ 2 ^ n * gaussDdim d v := by
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  have h := QIQTH.HeatResidualBound.gaussDdim_le_gaussDdim_chart (n := n) hc hd
    (τ := 1) one_pos (v := v) (w := v)
    (mul_le_mul_of_nonneg_right hcd (rncRadialSq_nonneg v))
  rw [mul_one, mul_one] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (QIQTH.ResidueBound.gaussDdim_nonneg _ _))
  have hratio : Real.sqrt (d / c) ≤ 2 := by
    have h4 : d / c ≤ 4 := (div_le_iff₀ hc).mpr (by linarith)
    calc Real.sqrt (d / c) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h4
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hratio n

/-! ### 2. ★ The SHARPENED outer bound — the structured coefficient through the frozen Hessian. -/

/-- **★ `frozenDefect_outer_sharp` — the sharpened two-term outer bound.**  For `K ≤ 0`, `r ≥ 0`
    there are `C_A, C_B ≥ 0` with, for ALL `τ > 0` and ALL `z, w`:
        `|E_frozen(τ, z, w)| ≤ C_A·G_{2τ}(z−w) + C_B·‖w‖·τ^{−1/2}·G_{2τ}(z−w)`.
    The J4-615 structured coefficient `L·‖v‖·(‖z‖+‖w‖)` (v = z−w) is split by the triangle
    `‖z‖ ≤ ‖w‖ + ‖v‖` into `L·(‖v‖² + 2‖v‖·‖w‖)`; the quadratic part folds with NO time cost
    (`sharp_fold_A` + k = 1,2 absorbs), the linear part pays `τ^{−1/2}` (`sharp_fold_B` +
    half-cubic absorb) and keeps `‖w‖ = √(rncRadialSq w)` IN RESERVE for the composition's
    inner-Gaussian moment payment.  Off the gate the kernel is `0` and the RHS is nonnegative. -/
theorem frozenDefect_outer_sharp (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r) :
    ∃ C_A C_B : ℝ, 0 ≤ C_A ∧ 0 ≤ C_B ∧ ∀ (τ : ℝ) (z w : Point n), 0 < τ →
      |frozenDefectKernel K r τ z w|
        ≤ C_A * gaussDdim (2 * τ) (z - w)
          + C_B * Real.sqrt (rncRadialSq w) / Real.sqrt τ * gaussDdim (2 * τ) (z - w) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := gaussDdim_absorb_one (n := n) (η := 0) (lam := 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂, hb₂⟩ := gaussDdim_absorb_two (n := n) (η := 0) (lam := 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Ch, hCh, hbh⟩ := gaussDdim_absorb_half_cubic (n := n) (η := 0) (lam := 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hk0 : (0 : ℝ) ≤ -K / 3 := by linarith
  set M : ℝ := 1 + -K / 3 * r ^ 2 with hMdef
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; nlinarith [sq_nonneg r]
  set D : ℝ := Real.sqrt ((Nat.factorial n : ℝ) * M ^ n) with hDdef
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  set L : ℝ := 2 * (-K) / 3 with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; linarith
  set cH : ℝ := (n : ℝ) ^ 2 * M ^ 2 with hcHdef
  have hcH0 : 0 ≤ cH := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  set cB : ℝ := M / 2 + cH / 4 with hcBdef
  have hcB0 : 0 ≤ cB := by rw [hcBdef]; positivity
  refine ⟨(n : ℝ) ^ 2 * (D * L * (M / 2 * C₁ + cH / 4 * C₂)),
    (n : ℝ) ^ 2 * (D * L * (2 * cB * Ch)), by positivity, by positivity,
    fun τ z w hτ => ?_⟩
  have hG20 : 0 ≤ gaussDdim (2 * τ) (z - w) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  by_cases hgate : τ ≤ 1 ∧ rncRadialSq w ≤ r ^ 2
  swap
  · -- off the gate: kernel is 0, RHS ≥ 0
    unfold frozenDefectKernel
    rw [if_neg (fun h => hgate ⟨h.2.1, h.2.2⟩), abs_zero]
    have h1 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (D * L * (M / 2 * C₁ + cH / 4 * C₂))
        * gaussDdim (2 * τ) (z - w) := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (D * L * (2 * cB * Ch))
        * Real.sqrt (rncRadialSq w) / Real.sqrt τ * gaussDdim (2 * τ) (z - w) := by positivity
    linarith
  obtain ⟨hτ1, hqw⟩ := hgate
  rw [frozenDefectKernel_eq_pd K r τ z w hτ hτ1 hqw]
  set v : Point n := fun b => z b - w b with hvdef
  set sv : ℝ := Real.sqrt (rncRadialSq v) with hsvdef
  set sw : ℝ := Real.sqrt (rncRadialSq w) with hswdef
  have hsv0 : 0 ≤ sv := Real.sqrt_nonneg _
  have hsw0 : 0 ≤ sw := Real.sqrt_nonneg _
  have hQv0 : 0 ≤ rncRadialSq v := rncRadialSq_nonneg v
  have hsv2 : sv * sv = rncRadialSq v := Real.mul_self_sqrt hQv0
  have hGτ0 : 0 ≤ gaussDdim τ v := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hG2v0 : 0 ≤ gaussDdim (2 * τ) v := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hgatev : (1 - 0) * rncRadialSq v ≤ rncRadialSq v := by norm_num
  -- the structured coefficient, triangle-split
  have hcoef : ∀ i j : Fin n,
      |curvedRNCInv K z i j - curvedRNCInv K w i j|
        ≤ L * (rncRadialSq v + 2 * sv * sw) := by
    intro i j
    have h := curvedRNCInv_diff_structured K hK z w i j
    have htri : Real.sqrt (rncRadialSq z) ≤ sw + sv := by
      have h2 := radial_sqrt_add_le w v
      have hz : (fun b => w b + v b) = z := by
        funext b
        simp [hvdef]
      rwa [hz] at h2
    have hstep : Real.sqrt (rncRadialSq (fun b => z b - w b))
        * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w))
        ≤ sv * (sv + 2 * sw) := by
      have hv' : Real.sqrt (rncRadialSq (fun b => z b - w b)) = sv := by
        rw [hsvdef, hvdef]
      rw [hv']
      have hin : Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w) ≤ sv + 2 * sw := by
        rw [← hswdef]; linarith
      exact mul_le_mul_of_nonneg_left hin hsv0
    calc |curvedRNCInv K z i j - curvedRNCInv K w i j|
        ≤ 2 * (-K) / 3 * (Real.sqrt (rncRadialSq (fun b => z b - w b))
            * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w))) := h
      _ ≤ 2 * (-K) / 3 * (sv * (sv + 2 * sw)) := by
          apply mul_le_mul_of_nonneg_left hstep (by linarith)
      _ = L * (rncRadialSq v + 2 * sv * sw) := by
          rw [hLdef, ← hsv2]; ring
  -- the frozen Hessian entry bound, det-transported
  have hpd : ∀ i j : Fin n,
      |pd (fun y => pd (fun x => frozenGauss (curvedRNCMetric K w) τ x) j y) i v|
        ≤ (M / (2 * τ) + cH * rncRadialSq v / (4 * τ ^ 2)) * (D * gaussDdim τ v) := by
    intro i j
    have hcoefH0 : 0 ≤ M / (2 * τ) + cH * rncRadialSq v / (4 * τ ^ 2) := by positivity
    calc |pd (fun y => pd (fun x => frozenGauss (curvedRNCMetric K w) τ x) j y) i v|
        ≤ (M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2))
            * frozenGauss (curvedRNCMetric K w) τ v :=
          frozenGauss_pd_pd_abs_le K hK r w hqw τ hτ v i j
      _ = (M / (2 * τ) + cH * rncRadialSq v / (4 * τ ^ 2))
            * frozenGauss (curvedRNCMetric K w) τ v := by rw [hcHdef]
      _ ≤ (M / (2 * τ) + cH * rncRadialSq v / (4 * τ ^ 2)) * (D * gaussDdim τ v) := by
          apply mul_le_mul_of_nonneg_left _ hcoefH0
          rw [hDdef]
          exact frozenGauss_le_detBound_mul_gauss K hK r w hqw τ hτ v
  -- sub-claim A: the quadratic part absorbs with NO time cost
  have hclaimA : rncRadialSq v * (M / (2 * τ) + cH * rncRadialSq v / (4 * τ ^ 2))
        * gaussDdim τ v
      ≤ (M / 2 * C₁ + cH / 4 * C₂) * gaussDdim (2 * τ) v := by
    rw [sharp_fold_A M cH τ (rncRadialSq v) hτ]
    have h1 := hb₁ τ hτ v v hgatev
    have h2 := hb₂ τ hτ v v hgatev
    calc (M / 2 * (rncRadialSq v / τ) + cH / 4 * (rncRadialSq v / τ) ^ 2) * gaussDdim τ v
        = M / 2 * ((rncRadialSq v / τ) * gaussDdim τ v)
            + cH / 4 * ((rncRadialSq v / τ) ^ 2 * gaussDdim τ v) := by ring
      _ ≤ M / 2 * (C₁ * gaussDdim (2 * τ) v) + cH / 4 * (C₂ * gaussDdim (2 * τ) v) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith))
            (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = (M / 2 * C₁ + cH / 4 * C₂) * gaussDdim (2 * τ) v := by ring
  -- sub-claim B: the linear part pays τ^{−1/2} via the half-cubic absorb
  have hclaimB : sv * (M / (2 * τ) + cH * rncRadialSq v / (4 * τ ^ 2)) * gaussDdim τ v
      ≤ cB * Ch / Real.sqrt τ * gaussDdim (2 * τ) v := by
    have hs := sharp_fold_B M cH τ (rncRadialSq v) hM0 hcH0 hτ hQv0
    rw [← hsvdef, ← hcBdef] at hs
    have hh := hbh τ hτ v v hgatev
    calc sv * (M / (2 * τ) + cH * rncRadialSq v / (4 * τ ^ 2)) * gaussDdim τ v
        ≤ (cB / Real.sqrt τ * (Real.sqrt (rncRadialSq v / τ) * (1 + rncRadialSq v / τ)))
            * gaussDdim τ v := mul_le_mul_of_nonneg_right hs hGτ0
      _ = cB / Real.sqrt τ
            * (Real.sqrt (rncRadialSq v / τ) * (1 + rncRadialSq v / τ) * gaussDdim τ v) := by
          ring
      _ ≤ cB / Real.sqrt τ * (Ch * gaussDdim (2 * τ) v) := by
          apply mul_le_mul_of_nonneg_left hh (by positivity)
      _ = cB * Ch / Real.sqrt τ * gaussDdim (2 * τ) v := by ring
  -- per-entry bound
  have hterm : ∀ i j : Fin n,
      |(curvedRNCInv K z i j - curvedRNCInv K w i j)
        * pd (fun y => pd (fun x => frozenGauss (curvedRNCMetric K w) τ x) j y) i v|
      ≤ D * L * (M / 2 * C₁ + cH / 4 * C₂) * gaussDdim (2 * τ) v
        + D * L * (2 * cB * Ch) * sw / Real.sqrt τ * gaussDdim (2 * τ) v := by
    intro i j
    have hB0 : 0 ≤ L * (rncRadialSq v + 2 * sv * sw) := by
      apply mul_nonneg hL0
      have := mul_nonneg (mul_nonneg hsv0 hsw0) (by norm_num : (0:ℝ) ≤ 2)
      nlinarith
    rw [abs_mul]
    calc |curvedRNCInv K z i j - curvedRNCInv K w i j|
          * |pd (fun y => pd (fun x => frozenGauss (curvedRNCMetric K w) τ x) j y) i v|
        ≤ (L * (rncRadialSq v + 2 * sv * sw))
            * ((M / (2 * τ) + cH * rncRadialSq v / (4 * τ ^ 2)) * (D * gaussDdim τ v)) :=
          mul_le_mul (hcoef i j) (hpd i j) (abs_nonneg _) hB0
      _ = D * L * (rncRadialSq v * (M / (2 * τ) + cH * rncRadialSq v / (4 * τ ^ 2))
              * gaussDdim τ v)
          + D * L * 2 * sw
              * (sv * (M / (2 * τ) + cH * rncRadialSq v / (4 * τ ^ 2)) * gaussDdim τ v) := by
          ring
      _ ≤ D * L * ((M / 2 * C₁ + cH / 4 * C₂) * gaussDdim (2 * τ) v)
          + D * L * 2 * sw * (cB * Ch / Real.sqrt τ * gaussDdim (2 * τ) v) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hclaimA (mul_nonneg hD0 hL0)
          · exact mul_le_mul_of_nonneg_left hclaimB
              (by positivity)
      _ = D * L * (M / 2 * C₁ + cH / 4 * C₂) * gaussDdim (2 * τ) v
          + D * L * (2 * cB * Ch) * sw / Real.sqrt τ * gaussDdim (2 * τ) v := by
          ring
  -- sum the n² entries
  have hsum : |∑ i, ∑ j, (curvedRNCInv K z i j - curvedRNCInv K w i j)
        * pd (fun y => pd (fun x => frozenGauss (curvedRNCMetric K w) τ x) j y) i v|
      ≤ (n : ℝ) ^ 2 * (D * L * (M / 2 * C₁ + cH / 4 * C₂) * gaussDdim (2 * τ) v
          + D * L * (2 * cB * Ch) * sw / Real.sqrt τ * gaussDdim (2 * τ) v) := by
    calc |∑ i, ∑ j, (curvedRNCInv K z i j - curvedRNCInv K w i j)
          * pd (fun y => pd (fun x => frozenGauss (curvedRNCMetric K w) τ x) j y) i v|
        ≤ ∑ i, |∑ j, (curvedRNCInv K z i j - curvedRNCInv K w i j)
            * pd (fun y => pd (fun x => frozenGauss (curvedRNCMetric K w) τ x) j y) i v| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |(curvedRNCInv K z i j - curvedRNCInv K w i j)
            * pd (fun y => pd (fun x => frozenGauss (curvedRNCMetric K w) τ x) j y) i v| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n,
            (D * L * (M / 2 * C₁ + cH / 4 * C₂) * gaussDdim (2 * τ) v
              + D * L * (2 * cB * Ch) * sw / Real.sqrt τ * gaussDdim (2 * τ) v) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = (n : ℝ) ^ 2 * (D * L * (M / 2 * C₁ + cH / 4 * C₂) * gaussDdim (2 * τ) v
            + D * L * (2 * cB * Ch) * sw / Real.sqrt τ * gaussDdim (2 * τ) v) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  -- rewrite `v = z − w` and reshape
  have hvzw : v = z - w := by
    funext b
    rw [hvdef]
    exact (Pi.sub_apply z w b).symm
  calc |∑ i, ∑ j, (curvedRNCInv K z i j - curvedRNCInv K w i j)
        * pd (fun y => pd (fun x => frozenGauss (curvedRNCMetric K w) τ x) j y) i v|
      ≤ (n : ℝ) ^ 2 * (D * L * (M / 2 * C₁ + cH / 4 * C₂) * gaussDdim (2 * τ) v
          + D * L * (2 * cB * Ch) * sw / Real.sqrt τ * gaussDdim (2 * τ) v) := hsum
    _ = (n : ℝ) ^ 2 * (D * L * (M / 2 * C₁ + cH / 4 * C₂)) * gaussDdim (2 * τ) (z - w)
        + (n : ℝ) ^ 2 * (D * L * (2 * cB * Ch)) * sw / Real.sqrt τ
            * gaussDdim (2 * τ) (z - w) := by
        rw [hvzw]
        ring
    _ = (n : ℝ) ^ 2 * (D * L * (M / 2 * C₁ + cH / 4 * C₂)) * gaussDdim (2 * τ) (z - w)
        + (n : ℝ) ^ 2 * (D * L * (2 * cB * Ch)) * Real.sqrt (rncRadialSq w) / Real.sqrt τ
            * gaussDdim (2 * τ) (z - w) := by rw [← hswdef]

/-! ### 3. The Beta(1/2, 3/2) time integral. -/

/-- **The B-term time integral is `O(s)`**: `∫₀ˢ (s−σ)^{−1/2}·σ^{1/2} dσ ≤ 2s`
    (crude-but-honest: `σ^{1/2} ≤ √s` on the path and `∫₀ˢ (s−σ)^{−1/2} = 2√s`;
    the exact value would be `B(1/2,3/2)·s = (π/2)s`). -/
theorem betaHalf_integral_le (s : ℝ) (hs : 0 < s) :
    ∫ σ in (0 : ℝ)..s, (s - σ) ^ (-(1 / 2) : ℝ) * σ ^ ((1 / 2) : ℝ) ≤ 2 * s := by
  have hI : IntervalIntegrable
      (fun σ => (s - σ) ^ (-(1 / 2) : ℝ) * σ ^ ((1 / 2) : ℝ)) volume 0 s :=
    rpow_mul_rpow_intervalIntegrable (-(1 / 2)) (1 / 2) s (by norm_num) (by norm_num) hs
  have hII2 : IntervalIntegrable (fun σ : ℝ => (s - σ) ^ (-(1 / 2) : ℝ)) volume 0 s := by
    have h0 : IntervalIntegrable (fun u : ℝ => u ^ (-(1 / 2) : ℝ)) volume 0 s :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h1 := h0.comp_sub_left s
    rw [sub_self, sub_zero] at h1
    exact h1.symm
  have hIc : IntervalIntegrable
      (fun σ : ℝ => (s - σ) ^ (-(1 / 2) : ℝ) * Real.sqrt s) volume 0 s :=
    hII2.mul_const _
  calc ∫ σ in (0 : ℝ)..s, (s - σ) ^ (-(1 / 2) : ℝ) * σ ^ ((1 / 2) : ℝ)
      ≤ ∫ σ in (0 : ℝ)..s, (s - σ) ^ (-(1 / 2) : ℝ) * Real.sqrt s := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo hs.le hI hIc (fun σ hσ => ?_)
        obtain ⟨hσ0, hσs⟩ := hσ
        have hts : 0 < s - σ := by linarith
        have hp : σ ^ ((1 / 2) : ℝ) ≤ Real.sqrt s := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_sqrt hσs.le
        exact mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hts.le _)
    _ = (∫ σ in (0 : ℝ)..s, (s - σ) ^ (-(1 / 2) : ℝ)) * Real.sqrt s :=
        intervalIntegral.integral_mul_const _ _
    _ = (2 * Real.sqrt s) * Real.sqrt s := by
        rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-(1 / 2) : ℝ)) s,
            sub_self, sub_zero,
            show (-(1 / 2) : ℝ) = -(1 : ℝ) / 2 from by norm_num,
            integral_rpow (Or.inl (show (-1 : ℝ) < -(1 : ℝ) / 2 by norm_num)),
            Real.zero_rpow (show -(1 : ℝ) / 2 + 1 ≠ 0 by norm_num), sub_zero,
            Real.sqrt_eq_rpow,
            show -(1 : ℝ) / 2 + 1 = 1 / (2 : ℝ) from by norm_num]
        ring
    _ = 2 * s := by
        rw [mul_assoc, Real.mul_self_sqrt hs.le]

/-! ### 4. ★★ THE COMPOSITION — `|E∗E(s, z, 0)| ≤ C·s·G_{8s}(z)`. -/

/-- **★★ J4-616 — `frozenK2_sharp`: the refined E∗E center-column bound, `O(s)`.**  For `K ≤ 0`,
    `r ≥ 0` there is `C ≥ 0` with, for ALL `s > 0` (no `s ≤ 1` cap needed) and all `z`:
        `|iterE E_frozen 2 (s, z, 0)| ≤ C·s·G_{8s}(z−0)`.
    The sharpened outer bound (`frozenDefect_outer_sharp`) composes with the banked
    center-column bound (`frozenColumnKernel_bound`): the A-term is the clean C-K product
    (time `∫₀ˢ dσ = s`), the B-term pays the reserved `‖w‖` as a `√σ` moment against the inner
    Gaussian (`gaussDdim_moment_half_self`) so the time integral is the Beta `≤ 2s`.  Every
    width is widened ONCE to `8s` (ratio ≤ 4 ⟹ factor ≤ 2ⁿ).  This upgrades J4-613's k = 2
    `O(√s)` — the SOLE obstruction isolated by `frozenColumn_k2_isolation` — to `O(s)`.
    ⚠ NOT `a₁ = R/6`. -/
theorem frozenK2_sharp (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ), 0 < s → ∀ z : Point n,
      |iterE (frozenDefectKernel K r) 2 s z 0|
        ≤ C * (s * gaussDdim (8 * s) (z - 0)) := by
  set E := frozenDefectKernel (n := n) K r with hEdef
  obtain ⟨Cg, hCgpos, hbd⟩ := frozenDefectKernel_bound (n := n) K r hK hr
  have hEboundW : ∀ (τ : ℝ) (p q : Point n), 0 < τ →
      |E τ p q| ≤ Cg * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q := by
    intro τ p q hτ
    rw [baseKernelW_negHalf_apply τ hτ]
    calc |E τ p q| ≤ Cg / Real.sqrt τ * gaussDdim (2 * τ) (p - q) := hbd τ p q hτ
      _ = Cg * (gaussDdim (2 * τ) (p - q) / Real.sqrt τ) := by ring
  have hInt : IterConvIntegrableW E (2 : ℝ) (-(1 / 2) : ℝ) Cg :=
    iterConvIntegrableW_of_bound_baseMeas_alpha E (-(1 / 2)) Cg
      (by norm_num) hEboundW
      (fun τ hτ p q => frozenDefectKernel_zero K r τ hτ p q)
      (frozenDefectKernel_stronglyMeasurable K r)
  obtain ⟨C₀, hC₀pos, hcol⟩ := frozenColumnKernel_bound (n := n) K r hK
  obtain ⟨CA, CB, hCA, hCB, houter⟩ := frozenDefect_outer_sharp (n := n) K r hK hr
  obtain ⟨Cm, hCmpos, hmom⟩ := gaussDdim_moment_half_self (n := n)
  refine ⟨2 ^ n * C₀ * (CA + 2 * (Real.sqrt 2 * (CB * Cm))), by positivity,
    fun s hs z => ?_⟩
  -- unfold `iterE E 2 = heatConv E E`
  have hiter2 : iterE E 2 s z 0 = heatConv E E s z 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iterE_succ E le_rfl, iterE_one, heatConvK_apply]
  -- the actual-kernel integrabilities at column 0 (from the banked producer, k = 1)
  obtain ⟨hI1, hI2, hIf, -, -⟩ := hInt 1 le_rfl s hs z 0
  simp only [iterE_one] at hI1 hI2 hIf
  -- notation
  set Gz : ℝ := gaussDdim (8 * s) (z - 0) with hGzdef
  have hGz0 : 0 ≤ Gz := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  set c₁ : ℝ := 2 ^ n * C₀ * CA * Gz with hc₁def
  set c₂ : ℝ := 2 ^ n * C₀ * (Real.sqrt 2 * (CB * Cm)) * Gz with hc₂def
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁def]; positivity
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂def]; positivity
  set g : ℝ → ℝ := fun σ =>
    c₁ + c₂ * ((s - σ) ^ (-(1 / 2) : ℝ) * σ ^ ((1 / 2) : ℝ)) with hgdef
  have hg_ii : IntervalIntegrable g volume 0 s := by
    simp only [hgdef]
    exact IntervalIntegrable.add intervalIntegrable_const
      ((rpow_mul_rpow_intervalIntegrable (-(1 / 2)) (1 / 2) s
        (by norm_num) (by norm_num) hs).const_mul c₂)
  -- the per-slice comparison on the open interval
  have hcomp : ∀ σ ∈ Set.Ioo (0 : ℝ) s,
      (∫ w, |E (s - σ) z w| * |E σ w 0|) ≤ g σ := by
    intro σ hσ
    obtain ⟨hσ0, hσs⟩ := hσ
    have hts : 0 < s - σ := by linarith
    have hst2 : 0 < Real.sqrt (s - σ) := Real.sqrt_pos.mpr hts
    -- the dominating w-integrand (moment ALREADY paid on the B-term)
    set c₂w : ℝ := CB * C₀ * Cm * Real.sqrt 2 * (Real.sqrt σ / Real.sqrt (s - σ)) with hc₂wdef
    have hc₂w0 : 0 ≤ c₂w := by
      rw [hc₂wdef]
      positivity
    set hdom : Point n → ℝ := fun w =>
      CA * C₀ * (gaussDdim (2 * (s - σ)) (z - w) * gaussDdim (2 * σ) (w - 0))
        + c₂w * (gaussDdim (2 * (s - σ)) (z - w) * gaussDdim (8 * σ) (w - 0)) with hdomdef
    have hdomInt : Integrable hdom := by
      rw [hdomdef]
      exact ((gaussDdim_mul_integrable (2 * (s - σ)) (2 * σ) z 0).const_mul (CA * C₀)).add
        ((gaussDdim_mul_integrable (2 * (s - σ)) (8 * σ) z 0).const_mul c₂w)
    -- the pointwise product bound
    have hptw : ∀ w : Point n, |E (s - σ) z w| * |E σ w 0| ≤ hdom w := by
      intro w
      have h1 := houter (s - σ) z w hts
      have h2 := hcol σ w hσ0
      have hG2a0 : 0 ≤ gaussDdim (2 * (s - σ)) (z - w) :=
        QIQTH.ResidueBound.gaussDdim_nonneg _ _
      have hRHS1_0 : 0 ≤ CA * gaussDdim (2 * (s - σ)) (z - w)
          + CB * Real.sqrt (rncRadialSq w) / Real.sqrt (s - σ)
            * gaussDdim (2 * (s - σ)) (z - w) := by positivity
      -- the moment payment on `‖w‖·G_{2σ}(w−0)`
      have hmoment : Real.sqrt (rncRadialSq w) * gaussDdim (2 * σ) (w - 0)
          ≤ Cm * (Real.sqrt 2 * Real.sqrt σ) * gaussDdim (8 * σ) (w - 0) := by
        rw [sub_zero]
        have h := hmom (2 * σ) (by positivity) w
        rw [show (4 : ℝ) * (2 * σ) = 8 * σ from by ring,
            Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) σ] at h
        exact h
      calc |E (s - σ) z w| * |E σ w 0|
          ≤ (CA * gaussDdim (2 * (s - σ)) (z - w)
              + CB * Real.sqrt (rncRadialSq w) / Real.sqrt (s - σ)
                * gaussDdim (2 * (s - σ)) (z - w))
            * (C₀ * gaussDdim (2 * σ) (w - 0)) :=
            mul_le_mul h1 h2 (abs_nonneg _) hRHS1_0
        _ = CA * C₀ * (gaussDdim (2 * (s - σ)) (z - w) * gaussDdim (2 * σ) (w - 0))
            + CB * C₀ / Real.sqrt (s - σ) * gaussDdim (2 * (s - σ)) (z - w)
              * (Real.sqrt (rncRadialSq w) * gaussDdim (2 * σ) (w - 0)) := by ring
        _ ≤ CA * C₀ * (gaussDdim (2 * (s - σ)) (z - w) * gaussDdim (2 * σ) (w - 0))
            + CB * C₀ / Real.sqrt (s - σ) * gaussDdim (2 * (s - σ)) (z - w)
              * (Cm * (Real.sqrt 2 * Real.sqrt σ) * gaussDdim (8 * σ) (w - 0)) := by
            have hpos : 0 ≤ CB * C₀ / Real.sqrt (s - σ)
                * gaussDdim (2 * (s - σ)) (z - w) := by positivity
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hmoment hpos)
        _ = hdom w := by
            rw [hdomdef, hc₂wdef]
            field_simp
    -- integrate in w: C-K composition + width widening
    have hval : (∫ w, hdom w)
        = CA * C₀ * gaussDdim (2 * s) (z - 0)
          + c₂w * gaussDdim (2 * s + 6 * σ) (z - 0) := by
      rw [hdomdef]
      rw [integral_add
        ((gaussDdim_mul_integrable (2 * (s - σ)) (2 * σ) z 0).const_mul (CA * C₀))
        ((gaussDdim_mul_integrable (2 * (s - σ)) (8 * σ) z 0).const_mul c₂w),
        integral_const_mul, integral_const_mul,
        QIQTH.GaussianConvolution.gaussDdim_conv (2 * (s - σ)) (2 * σ)
          (by linarith) (by linarith) z 0,
        QIQTH.GaussianConvolution.gaussDdim_conv (2 * (s - σ)) (8 * σ)
          (by linarith) (by linarith) z 0,
        show 2 * (s - σ) + 2 * σ = 2 * s from by ring,
        show 2 * (s - σ) + 8 * σ = 2 * s + 6 * σ from by ring]
    have hwide1 : gaussDdim (2 * s) (z - 0) ≤ 2 ^ n * Gz := by
      rw [hGzdef]
      exact gaussDdim_widen_le (2 * s) (8 * s) (by linarith) (by linarith) (by linarith) _
    have hwide2 : gaussDdim (2 * s + 6 * σ) (z - 0) ≤ 2 ^ n * Gz := by
      rw [hGzdef]
      exact gaussDdim_widen_le (2 * s + 6 * σ) (8 * s)
        (by linarith) (by linarith) (by linarith) _
    have hrpow : (s - σ) ^ (-(1 / 2) : ℝ) * σ ^ ((1 / 2) : ℝ)
        = Real.sqrt σ / Real.sqrt (s - σ) := by
      rw [Real.rpow_neg hts.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
          inv_mul_eq_div]
    calc (∫ w, |E (s - σ) z w| * |E σ w 0|)
        ≤ ∫ w, hdom w := integral_mono (hIf σ) hdomInt hptw
      _ = CA * C₀ * gaussDdim (2 * s) (z - 0) + c₂w * gaussDdim (2 * s + 6 * σ) (z - 0) :=
          hval
      _ ≤ CA * C₀ * (2 ^ n * Gz) + c₂w * (2 ^ n * Gz) :=
          add_le_add (mul_le_mul_of_nonneg_left hwide1 (by positivity))
            (mul_le_mul_of_nonneg_left hwide2 hc₂w0)
      _ = g σ := by
          simp only [hgdef]
          rw [hrpow, hc₁def, hc₂def, hc₂wdef]
          ring
  -- assemble the time integral
  have hbeta := betaHalf_integral_le s hs
  calc |iterE E 2 s z 0|
      = |heatConv E E s z 0| := by rw [hiter2]
    _ ≤ heatConv (fun τ p q => |E τ p q|) (fun τ p q => |E τ p q|) s z 0 :=
        heatConv_abs_le E E s z 0 hs.le hI1 hI2
    _ = ∫ σ in (0 : ℝ)..s, (∫ w, |E (s - σ) z w| * |E σ w 0|) := rfl
    _ ≤ ∫ σ in (0 : ℝ)..s, g σ :=
        intervalIntegral.integral_mono_on_of_le_Ioo hs.le hI2 hg_ii hcomp
    _ = c₁ * s + c₂ * ∫ σ in (0 : ℝ)..s,
          ((s - σ) ^ (-(1 / 2) : ℝ) * σ ^ ((1 / 2) : ℝ)) := by
        simp only [hgdef]
        rw [intervalIntegral.integral_add intervalIntegrable_const
          ((rpow_mul_rpow_intervalIntegrable (-(1 / 2)) (1 / 2) s
            (by norm_num) (by norm_num) hs).const_mul c₂),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        simp only [smul_eq_mul, sub_zero]
        ring
    _ ≤ c₁ * s + c₂ * (2 * s) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hbeta hc₂0)
    _ = 2 ^ n * C₀ * (CA + 2 * (Real.sqrt 2 * (CB * Cm))) * (s * Gz) := by
        rw [hc₁def, hc₂def]
        ring

/-! ### 5. ★ The FULL k ≥ 2 tail is `O(s)`. -/

/-- **★ `frozenColumn_tail_O_s` — the FULL k ≥ 2 column tail is `O(s)`.**  For `K ≤ 0`, `r ≥ 0`
    there is `C ≥ 0` with, on `0 < s ≤ 1` and all `p`:
        `|leviSeries E_frozen (s, p, 0) + E_frozen (s, p, 0)| ≤ C·s·G_{8s}(p−0)`
    — the sharp k = 2 bound (`frozenK2_sharp`) + the banked k ≥ 3 `O(s)` sub-tail
    (`frozenColumn_k2_isolation`), the latter widened `G_{2s} → 2ⁿ·G_{8s}`.  This UPGRADES the
    J4-613 honest tail `O(√s)·G_{2s}` to the consumer's linear shape.  ⚠ NOT `a₁ = R/6` (the
    k = 1 term `−E` is the separate transport-cancellation thread). -/
theorem frozenColumn_tail_O_s (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |leviSeries (frozenDefectKernel K r) s p 0 + frozenDefectKernel K r s p 0|
        ≤ C * (s * gaussDdim (8 * s) (p - 0)) := by
  obtain ⟨Ck2, hCk2, hsharp⟩ := frozenK2_sharp (n := n) K r hK hr
  obtain ⟨Ck3, hCk3, hk3⟩ := frozenColumn_k2_isolation (n := n) K r hK hr
  refine ⟨Ck3 * 2 ^ n + Ck2, by positivity, fun s p hs hs1 => ?_⟩
  have hG8 : 0 ≤ gaussDdim (8 * s) (p - 0) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hwide : gaussDdim (2 * s) (p - 0) ≤ 2 ^ n * gaussDdim (8 * s) (p - 0) :=
    gaussDdim_widen_le (2 * s) (8 * s) (by linarith) (by linarith) (by linarith) _
  calc |leviSeries (frozenDefectKernel K r) s p 0 + frozenDefectKernel K r s p 0|
      = |(leviSeries (frozenDefectKernel K r) s p 0 + frozenDefectKernel K r s p 0
          - iterE (frozenDefectKernel K r) 2 s p 0)
          + iterE (frozenDefectKernel K r) 2 s p 0| := by ring_nf
    _ ≤ |leviSeries (frozenDefectKernel K r) s p 0 + frozenDefectKernel K r s p 0
          - iterE (frozenDefectKernel K r) 2 s p 0|
        + |iterE (frozenDefectKernel K r) 2 s p 0| := abs_add_le _ _
    _ ≤ Ck3 * (s * gaussDdim (2 * s) (p - 0)) + Ck2 * (s * gaussDdim (8 * s) (p - 0)) :=
        add_le_add (hk3 s p hs hs1) (hsharp s hs p)
    _ ≤ Ck3 * (s * (2 ^ n * gaussDdim (8 * s) (p - 0)))
        + Ck2 * (s * gaussDdim (8 * s) (p - 0)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hwide hs.le) hCk3) le_rfl
    _ = (Ck3 * 2 ^ n + Ck2) * (s * gaussDdim (8 * s) (p - 0)) := by ring

/-! ### 6. ★ The consumer wiring — the tail fits the LINEAR slice budget; `O(t²)` restored. -/

/-- **★ `frozenK2_tail_slice_O_s` — the k ≥ 2 tail feeds the slice LINEARLY.**  For `K ≤ 0`,
    `r ≥ 0` there is `C_t ≥ 0` such that for every Gaussian-dominated slice kernel
    (`|H(a,0,ζ)| ≤ C_H·G_{2a}(0−ζ)`, `a > 0`) and all `0 < s < t`, `s ≤ 1`:
        `‖∫ ζ, H(t−s,0,ζ)·(leviSeries E_frozen + E_frozen)(s,ζ,0)‖
             ≤ (C_H·C_t)·(s·G_{8t}(0))`.
    C-K composition `G_{2(t−s)} ∗ G_{8s} = G_{2t+6s}`, widened once to `G_{8t}` (ratio ≤ 4).
    ⚠ NORMALIZATION: the diagonal mass `G_{8t}(0)` is carried EXPLICITLY — `t`-uniformity is
    RELATIVE to the capstone prefactor `pref = (4πt)^{−n/2}` (`G_{8t}(0)/pref = 8^{−n/2}`). -/
theorem frozenK2_tail_slice_O_s (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r) :
    ∃ C_t : ℝ, 0 ≤ C_t ∧
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (ζ : Point n), 0 < a →
          |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
        ∀ (t s : ℝ), 0 < s → s < t → s ≤ 1 →
          ‖∫ ζ, H (t - s) 0 ζ
              * (leviSeries (frozenDefectKernel K r) s ζ 0 + frozenDefectKernel K r s ζ 0)‖
            ≤ (C_H * C_t) * (s * gaussDdim (8 * t) (0 : Point n)) := by
  obtain ⟨C_os, hCos, htail⟩ := frozenColumn_tail_O_s (n := n) K r hK hr
  refine ⟨2 ^ n * C_os, by positivity, fun H C_H hCH hH t s hs hst hs1 => ?_⟩
  have hts : 0 < t - s := by linarith
  have hg_int : Integrable (fun ζ : Point n =>
      (C_H * C_os * s)
        * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
            * gaussDdim (8 * s) (ζ - (0 : Point n)))) volume :=
    (gaussDdim_mul_integrable (2 * (t - s)) (8 * s) (0 : Point n) (0 : Point n)).const_mul _
  have hpt : ∀ ζ : Point n,
      ‖H (t - s) 0 ζ
          * (leviSeries (frozenDefectKernel K r) s ζ 0 + frozenDefectKernel K r s ζ 0)‖
        ≤ (C_H * C_os * s)
            * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
                * gaussDdim (8 * s) (ζ - (0 : Point n))) := by
    intro ζ
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hH (t - s) ζ hts
    have h2 := htail s ζ hs hs1
    have hGnn : (0 : ℝ) ≤ gaussDdim (2 * (t - s)) ((0 : Point n) - ζ) :=
      QIQTH.ResidueBound.gaussDdim_nonneg _ _
    calc |H (t - s) 0 ζ|
          * |leviSeries (frozenDefectKernel K r) s ζ 0 + frozenDefectKernel K r s ζ 0|
        ≤ (C_H * gaussDdim (2 * (t - s)) ((0 : Point n) - ζ))
            * (C_os * (s * gaussDdim (8 * s) (ζ - (0 : Point n)))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCH hGnn)
      _ = (C_H * C_os * s)
            * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
                * gaussDdim (8 * s) (ζ - (0 : Point n))) := by ring
  have hwide : gaussDdim (2 * (t - s) + 8 * s) ((0 : Point n) - 0)
      ≤ 2 ^ n * gaussDdim (8 * t) ((0 : Point n) - 0) :=
    gaussDdim_widen_le (2 * (t - s) + 8 * s) (8 * t)
      (by linarith) (by linarith) (by linarith) _
  calc ‖∫ ζ, H (t - s) 0 ζ
          * (leviSeries (frozenDefectKernel K r) s ζ 0 + frozenDefectKernel K r s ζ 0)‖
      ≤ ∫ ζ, (C_H * C_os * s)
          * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
              * gaussDdim (8 * s) (ζ - (0 : Point n))) :=
        MeasureTheory.norm_integral_le_of_norm_le hg_int (ae_of_all _ hpt)
    _ = (C_H * C_os * s)
          * ∫ ζ, gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
              * gaussDdim (8 * s) (ζ - (0 : Point n)) :=
        integral_const_mul _ _
    _ = (C_H * C_os * s) * gaussDdim (2 * (t - s) + 8 * s) ((0 : Point n) - 0) := by
        rw [QIQTH.GaussianConvolution.gaussDdim_conv (2 * (t - s)) (8 * s)
          (by linarith) (by linarith) (0 : Point n) (0 : Point n)]
    _ ≤ (C_H * C_os * s) * (2 ^ n * gaussDdim (8 * t) ((0 : Point n) - 0)) :=
        mul_le_mul_of_nonneg_left hwide (by positivity)
    _ = (C_H * (2 ^ n * C_os)) * (s * gaussDdim (8 * t) (0 : Point n)) := by
        rw [sub_zero]
        ring

/-- **★★ `corrHigher_O_t2_restored` — THE BOUNDED-cRem `O(t²)` API, RESTORED.**  For `K ≤ 0`,
    `r ≥ 0` there is `C_t ≥ 0` such that for every Gaussian-dominated slice kernel `H`
    (`|H(a,0,ζ)| ≤ C_H·G_{2a}(0−ζ)` for `a > 0`, and `H(0,0,·) = 0` — true of the parametrix,
    which vanishes at time 0), every `pref ≠ 0` and `0 < t ≤ 1`, with
    `F := leviSeries E_frozen + E_frozen` (the k ≥ 2 tail) and `K_t := C_H·C_t·G_{8t}(0)`:
      (i)   the `hCorrHigher` EQUALITY shape `heatConv H F t 0 0 = pref·(t²·cRem)` with the
            concrete witness `cRem = heatConv H F t 0 0/(pref·t²)`;
      (ii)  `|heatConv H F t 0 0| ≤ K_t·t²`  — the GENUINE `O(t²)` assembly;
      (iii) `|cRem| ≤ K_t/|pref|` — **BOUNDED** (vs the J4-614 route-(b) `O(t^{−1/2})`):
            `K_t/|pref|` carries only the ratio `G_{8t}(0)/pref → 8^{−n/2}` of diagonal masses,
            a genuine constant relative to the capstone's `pref = (4πt)^{−n/2}` normalization.
    This restores the bounded-`cRem` `O(t²)` API of `corrHigher_bounded_of_slice` for the k ≥ 2
    tail.  ⚠ NOT `a₁ = R/6` (the k = 1 transport term is NOT in `F`). -/
theorem corrHigher_O_t2_restored (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r) :
    ∃ C_t : ℝ, 0 ≤ C_t ∧
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (ζ : Point n), 0 < a →
          |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        ∀ (pref t : ℝ), 0 < t → t ≤ 1 → pref ≠ 0 →
          (heatConv H (fun σ p q => leviSeries (frozenDefectKernel K r) σ p q
              + frozenDefectKernel K r σ p q) t 0 0
            = pref * (t ^ 2
                * (heatConv H (fun σ p q => leviSeries (frozenDefectKernel K r) σ p q
                    + frozenDefectKernel K r σ p q) t 0 0 / (pref * t ^ 2))))
          ∧ |heatConv H (fun σ p q => leviSeries (frozenDefectKernel K r) σ p q
              + frozenDefectKernel K r σ p q) t 0 0|
            ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) * t ^ 2
          ∧ |heatConv H (fun σ p q => leviSeries (frozenDefectKernel K r) σ p q
              + frozenDefectKernel K r σ p q) t 0 0 / (pref * t ^ 2)|
            ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) / |pref| := by
  obtain ⟨C_t, hCt, hsl⟩ := frozenK2_tail_slice_O_s (n := n) K r hK hr
  refine ⟨C_t, hCt, fun H C_H hCH hH hH0 pref t ht ht1 hpref => ?_⟩
  set Kt : ℝ := C_H * C_t * gaussDdim (8 * t) (0 : Point n) with hKtdef
  have hKt0 : 0 ≤ Kt := by
    rw [hKtdef]
    exact mul_nonneg (mul_nonneg hCH hCt) (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  -- the LINEAR slice budget, at EVERY s ∈ Ι 0 t (endpoint s = t via H(0,0,·) = 0)
  have hslice : ∀ s ∈ Ι (0 : ℝ) t,
      ‖∫ ζ, H (t - s) 0 ζ
          * (fun σ p q => leviSeries (frozenDefectKernel K r) σ p q
              + frozenDefectKernel K r σ p q) s ζ 0‖
        ≤ Kt * ((t - s) + s) + 0 * Real.sqrt s := by
    intro s hs
    have hs' : s ∈ Set.Ioc (0 : ℝ) t := by rwa [Set.uIoc_of_le ht.le] at hs
    rcases lt_or_eq_of_le hs'.2 with hst | hseq
    · -- interior: the sharp slice bound, then `Kt·s ≤ Kt·t`
      have hb := hsl H C_H hCH hH t s hs'.1 hst (le_trans hs'.2 ht1)
      calc ‖∫ ζ, H (t - s) 0 ζ
              * (fun σ p q => leviSeries (frozenDefectKernel K r) σ p q
                  + frozenDefectKernel K r σ p q) s ζ 0‖
          = ‖∫ ζ, H (t - s) 0 ζ
              * (leviSeries (frozenDefectKernel K r) s ζ 0 + frozenDefectKernel K r s ζ 0)‖ :=
            rfl
        _ ≤ (C_H * C_t) * (s * gaussDdim (8 * t) (0 : Point n)) := hb
        _ = Kt * s := by rw [hKtdef]; ring
        _ ≤ Kt * ((t - s) + s) + 0 * Real.sqrt s := by
            have : Kt * s ≤ Kt * ((t - s) + s) :=
              mul_le_mul_of_nonneg_left (by linarith) hKt0
            linarith
    · -- endpoint s = t: the parametrix age is 0 and H(0,0,·) = 0
      have hzero : (fun ζ => H (t - s) 0 ζ
          * (fun σ p q => leviSeries (frozenDefectKernel K r) σ p q
              + frozenDefectKernel K r σ p q) s ζ 0) = fun _ => (0 : ℝ) := by
        funext ζ
        rw [hseq, sub_self, hH0 ζ, zero_mul]
      rw [hzero, integral_zero, norm_zero]
      have h1 : Kt * ((t - s) + s) + 0 * Real.sqrt s = Kt * t := by ring
      rw [h1]
      exact mul_nonneg hKt0 ht.le
  -- feed the banked consumer at K' = 0: bounded cRem
  obtain ⟨heq, hbd, hrem⟩ := corrHigher_bounded_of_slice_sqrt H
    (fun σ p q => leviSeries (frozenDefectKernel K r) σ p q + frozenDefectKernel K r σ p q)
    pref Kt 0 t ht hpref le_rfl hslice
  refine ⟨heq, ?_, ?_⟩
  · calc |heatConv H (fun σ p q => leviSeries (frozenDefectKernel K r) σ p q
          + frozenDefectKernel K r σ p q) t 0 0|
        ≤ Kt * t ^ 2 + 0 * (t * Real.sqrt t) := hbd
      _ = (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) * t ^ 2 := by
          rw [hKtdef]; ring
  · calc |heatConv H (fun σ p q => leviSeries (frozenDefectKernel K r) σ p q
          + frozenDefectKernel K r σ p q) t 0 0 / (pref * t ^ 2)|
        ≤ (Kt + 0 / Real.sqrt t) / |pref| := hrem
      _ = (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) / |pref| := by
          rw [zero_div, add_zero, hKtdef]

/-! ### 7. Non-vacuity gates. -/

/-- **NON-VACUITY (consumer side).**  The Gaussian-dominated slice-kernel hypothesis class of
    `frozenK2_tail_slice_O_s`/`corrHigher_O_t2_restored` is inhabited by the GENUINELY NONZERO
    kernel `H := (a,p,q) ↦ G_{2a}(p−q)` (with `C_H = 1` and `H(0,0,·) = 0` for `n ≥ 1`, and
    `H(a,0,0) > 0` at `a > 0`) — the restored `O(t²)` consumer is not certified on the zero
    kernel only.  (The SUBJECT side is the banked `frozenColumn_witness_ne_zero`: at `K < 0`,
    `n ≥ 2` the center column being composed is genuinely nonzero.) -/
theorem frozenK2Sharp_H_witness (hn : 1 ≤ n) :
    (∀ (a : ℝ) (ζ : Point n), 0 < a →
      |gaussDdim (2 * a) ((0 : Point n) - ζ)|
        ≤ 1 * gaussDdim (2 * a) ((0 : Point n) - ζ))
    ∧ (∀ ζ : Point n, gaussDdim (2 * (0 : ℝ)) ((0 : Point n) - ζ) = 0)
    ∧ ∀ a : ℝ, 0 < a → 0 < gaussDdim (2 * a) ((0 : Point n) - (0 : Point n)) := by
  refine ⟨fun a ζ _ => ?_, fun ζ => ?_, fun a ha => ?_⟩
  · rw [one_mul, abs_of_nonneg (QIQTH.ResidueBound.gaussDdim_nonneg _ _)]
  · rw [mul_zero]
    exact gaussDdim_eq_zero_of_nonpos hn le_rfl _
  · rw [gaussDdim_closed]
    positivity

end QIQTH.FrozenK2Sharp

section AxiomChecks
open QIQTH.FrozenK2Sharp
#print axioms sharp_fold_A
#print axioms sharp_fold_B
#print axioms gaussDdim_widen_le
#print axioms frozenDefect_outer_sharp
#print axioms betaHalf_integral_le
#print axioms frozenK2_sharp
#print axioms frozenColumn_tail_O_s
#print axioms frozenK2_tail_slice_O_s
#print axioms corrHigher_O_t2_restored
#print axioms frozenK2Sharp_H_witness
end AxiomChecks
