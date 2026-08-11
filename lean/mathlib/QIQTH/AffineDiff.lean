/-
  AffineDiff — J4-615: the ZERO-CONSTANT-TERM affine-difference supplier for the curved
  inverse metric — route-(a) brick (ii) of the genuine `E∗E : O(√s) → O(s)` upgrade
  (Sol route verdict, FrozenK2 header, 2026-08-11).

  THE MATHEMATICS.  The banked coefficient bound `curvedRNCInv_diff_bound` is affine in
  `(‖v‖, ‖v‖²)` with an `r`-dependent LINEAR term — a plain Lipschitz shape.  Sol (J4-614):
  a mere Lipschitz bound `L·‖z−w‖` leaves an `a^{−1/2}` in the E∗E composition and only
  reproduces `O(√s)`; the `O(s)` upgrade needs the STRUCTURED bound

      |gⁱʲ(z) − gⁱʲ(w)| ≤ L · ‖z−w‖ · (‖z‖ + ‖w‖)

  whose right side vanishes QUADRATICALLY at the origin pair — then in the E∗E composition
  BOTH `‖·‖`-type factors pay `√time` moments via the banked `gaussDdim_moment_half`
  (`√(r²(z))·G_τ ≤ C·√τ·G_{λτ}`) and the total is `O(s)`.

  THE ROUTE (chosen after reading the definition).  `curvedRNCInv` is the CLOSED
  Sherman–Morrison rational form `gi^K(x) = (δ − (K/3)x⊗x)/α(x)`, `α(x) = 1 − (K/3)‖x‖² ≥ 1`
  for `K ≤ 0` — NOT an opaque matrix inverse.  So we do NOT need the resolvent identity with
  entry-sup bounds: the banked exact rational-difference identity `curvedRNCInv_sub_eq`
  (q := w, v := z − w) splits `gi(z) − gi(w)` into

      T₁ = (−K/3)·(zᵢzⱼ − wᵢwⱼ)/α(z)
      T₂ = (δᵢⱼ − (K/3)wᵢwⱼ) · (K/3)(‖z‖² − ‖w‖²) / (α(z)·α(w)),

  and the KEY cancellation is that the E-factor obeys `|δᵢⱼ − (K/3)wᵢwⱼ| ≤ α(w)` — the
  numerator's `w`-growth is EXACTLY eaten by the `α(w)` denominator.  With the two elementary
  factorizations `zᵢzⱼ − wᵢwⱼ = zᵢ(zⱼ−wⱼ) + (zᵢ−wᵢ)wⱼ` and
  `‖z‖² − ‖w‖² = ⟨z−w, z+w⟩ ≤ ‖z−w‖(‖z‖+‖w‖)` (Cauchy–Schwarz + triangle), each of
  `|T₁|, |T₂| ≤ (−K/3)·‖z−w‖·(‖z‖+‖w‖)` after dropping `α(z) ≥ 1`.  Hence the supplier is

      ★ GLOBAL (UNGATED, all of `Point n`, no ball, no `r`), with L = 2(−K)/3 —
        the SAME honest constant as the polynomial metric itself.

  WHAT LANDS (all proved, no sorry; `‖x‖ := √(rncRadialSq x)` throughout, matching the
  `Real.sqrt (rncRadialSq ·)` shape the moment lever `gaussDdim_moment_half` absorbs):
    • `radial_sqrt_add_le` / `radialSq_diff_structured` / `entry_prod_diff_structured` —
      the elementary structured factorizations (triangle, `‖z‖²−‖w‖²`, `zᵢzⱼ−wᵢwⱼ`).
    • `curvedRNCMetric_diff_structured` — |g(z)ᵢⱼ − g(w)ᵢⱼ| ≤ (2(−K)/3)·‖z−w‖·(‖z‖+‖w‖),
      global, from the polynomial closed form.
    • ★ `curvedRNCInv_diff_structured` — THE SUPPLIER:
          |gⁱʲ(z) − gⁱʲ(w)| ≤ (2(−K)/3)·‖z−w‖·(‖z‖+‖w‖)   (K ≤ 0, GLOBAL).
    • `curvedRNCInv_diff_structured'` — the (q, v)-shape corollary
      |gⁱʲ(q+v) − gⁱʲ(q)| ≤ (2(−K)/3)·‖v‖·(‖q+v‖+‖q‖), the exact Levi-defect coefficient
      shape the refined E∗E composition (J4-616) consumes.
    • `curvedRNCInv_diff_structured_sum` — the summed compatibility form
      ∑ᵢⱼ |gⁱʲ(z) − gⁱʲ(w)| ≤ n²·(2(−K)/3)·‖z−w‖·(‖z‖+‖w‖).
    • NON-VACUITY: `curvedRNCInv_diff_structured_nonvacuous` — for `K < 0`, `n ≥ 2` there are
      `z, w, i, j` with `gⁱʲ(z) − gⁱʲ(w) ≠ 0` (evaluates to `(K/3)/(1−K/3) < 0` at
      z = e₀, w = 0, i = j = 1) AND the structured right side strictly positive there:
      the bound is exercised on a genuinely nonzero difference, not vacuously about `0`.

  ⚠ HONEST SCOPE.  `a₁ = R/6` remains CONDITIONAL: the flat tower is non-vacuous and closed;
  the curved side still owes the refined `E∗E ≤ C·s·G_{Ms}` center-column theorem (J4-616,
  which THIS brick supplies), the k = 1 transport thread, the per-q producer re-assembly,
  the fat-K hEmeas/hAdom/hcont piles, the capstone co-instantiation, and the prior piles.
  This brick is the structured affine-difference supplier ONLY.  No axioms, no sorry.
-/
import Mathlib
import QIQTH.FrozenDefect

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianWidthTransfer QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.CurvedRNCGaugeBundle QIQTH.FrozenGauss QIQTH.FrozenDefect

namespace QIQTH.AffineDiff

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### 1. Elementary structured factorizations. -/

/-- Triangle inequality for the radial norm: `‖x+y‖ ≤ ‖x‖ + ‖y‖`
    (`‖·‖ = √(rncRadialSq ·)`), via the radial-square expansion + Cauchy–Schwarz. -/
theorem radial_sqrt_add_le (x y : Point n) :
    Real.sqrt (rncRadialSq (fun a => x a + y a))
      ≤ Real.sqrt (rncRadialSq x) + Real.sqrt (rncRadialSq y) := by
  have hx0 : (0 : ℝ) ≤ Real.sqrt (rncRadialSq x) := Real.sqrt_nonneg _
  have hy0 : (0 : ℝ) ≤ Real.sqrt (rncRadialSq y) := Real.sqrt_nonneg _
  have hsq : rncRadialSq (fun a => x a + y a)
      ≤ (Real.sqrt (rncRadialSq x) + Real.sqrt (rncRadialSq y)) ^ 2 := by
    rw [rncRadialSq_add]
    have hin := le_of_abs_le (abs_inner_le_sqrt x y)
    have h1 : Real.sqrt (rncRadialSq x) ^ 2 = rncRadialSq x :=
      Real.sq_sqrt (rncRadialSq_nonneg x)
    have h2 : Real.sqrt (rncRadialSq y) ^ 2 = rncRadialSq y :=
      Real.sq_sqrt (rncRadialSq_nonneg y)
    nlinarith [hin, h1, h2]
  calc Real.sqrt (rncRadialSq (fun a => x a + y a))
      ≤ Real.sqrt ((Real.sqrt (rncRadialSq x) + Real.sqrt (rncRadialSq y)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (rncRadialSq x) + Real.sqrt (rncRadialSq y) :=
        Real.sqrt_sq (by linarith)

/-- **The structured radial-square difference**: `|‖z‖² − ‖w‖²| ≤ ‖z−w‖·(‖z‖+‖w‖)` —
    both factors on the right vanish at the origin pair (zero constant term). -/
theorem radialSq_diff_structured (z w : Point n) :
    |rncRadialSq z - rncRadialSq w|
      ≤ Real.sqrt (rncRadialSq (fun a => z a - w a))
        * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w)) := by
  have hexp : rncRadialSq z - rncRadialSq w
      = ∑ a, (z a - w a) * (z a + w a) := by
    simp only [rncRadialSq]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hexp]
  calc |∑ a, (z a - w a) * (z a + w a)|
      ≤ Real.sqrt (rncRadialSq (fun a => z a - w a))
          * Real.sqrt (rncRadialSq (fun a => z a + w a)) := by
        simpa using abs_inner_le_sqrt (fun a => z a - w a) (fun a => z a + w a)
    _ ≤ Real.sqrt (rncRadialSq (fun a => z a - w a))
          * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w)) :=
        mul_le_mul_of_nonneg_left (radial_sqrt_add_le z w) (Real.sqrt_nonneg _)

/-- **The structured entry-product difference**: `|zᵢzⱼ − wᵢwⱼ| ≤ ‖z−w‖·(‖z‖+‖w‖)`
    via the split `zᵢzⱼ − wᵢwⱼ = zᵢ(zⱼ−wⱼ) + (zᵢ−wᵢ)wⱼ`. -/
theorem entry_prod_diff_structured (z w : Point n) (i j : Fin n) :
    |z i * z j - w i * w j|
      ≤ Real.sqrt (rncRadialSq (fun a => z a - w a))
        * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w)) := by
  have hD0 : (0 : ℝ) ≤ Real.sqrt (rncRadialSq (fun a => z a - w a)) := Real.sqrt_nonneg _
  have hSz0 : (0 : ℝ) ≤ Real.sqrt (rncRadialSq z) := Real.sqrt_nonneg _
  have h1 : |z i| ≤ Real.sqrt (rncRadialSq z) := abs_apply_le_sqrt_radialSq z i
  have h2 : |w j| ≤ Real.sqrt (rncRadialSq w) := abs_apply_le_sqrt_radialSq w j
  have hdi : |z i - w i| ≤ Real.sqrt (rncRadialSq (fun a => z a - w a)) := by
    simpa using abs_apply_le_sqrt_radialSq (fun a => z a - w a) i
  have hdj : |z j - w j| ≤ Real.sqrt (rncRadialSq (fun a => z a - w a)) := by
    simpa using abs_apply_le_sqrt_radialSq (fun a => z a - w a) j
  have hexp : z i * z j - w i * w j = z i * (z j - w j) + (z i - w i) * w j := by ring
  rw [hexp]
  calc |z i * (z j - w j) + (z i - w i) * w j|
      ≤ |z i * (z j - w j)| + |(z i - w i) * w j| := abs_add_le _ _
    _ = |z i| * |z j - w j| + |z i - w i| * |w j| := by rw [abs_mul, abs_mul]
    _ ≤ Real.sqrt (rncRadialSq z) * Real.sqrt (rncRadialSq (fun a => z a - w a))
          + Real.sqrt (rncRadialSq (fun a => z a - w a)) * Real.sqrt (rncRadialSq w) :=
        add_le_add (mul_le_mul h1 hdj (abs_nonneg _) hSz0)
          (mul_le_mul hdi h2 (abs_nonneg _) hD0)
    _ = Real.sqrt (rncRadialSq (fun a => z a - w a))
          * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w)) := by ring

/-! ### 2. The structured metric difference (polynomial closed form). -/

/-- **The structured METRIC difference** — global, zero constant term:
    `|g^K(z)ᵢⱼ − g^K(w)ᵢⱼ| ≤ (2(−K)/3)·‖z−w‖·(‖z‖+‖w‖)` for `K ≤ 0`, ALL `z, w`. -/
theorem curvedRNCMetric_diff_structured (K : ℝ) (hK : K ≤ 0) (z w : Point n) (i j : Fin n) :
    |curvedRNCMetric K z i j - curvedRNCMetric K w i j|
      ≤ 2 * (-K) / 3 *
        (Real.sqrt (rncRadialSq (fun a => z a - w a))
          * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w))) := by
  have hk0 : (0 : ℝ) ≤ -(K / 3) := by linarith
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    calc |a - b| = |a + -b| := by ring_nf
      _ ≤ |a| + |-b| := abs_add_le _ _
      _ = |a| + |b| := by rw [abs_neg]
  have hexp : curvedRNCMetric K z i j - curvedRNCMetric K w i j
      = -(K / 3) * ((rncRadialSq z - rncRadialSq w) * (if i = j then (1 : ℝ) else 0)
          - (z i * z j - w i * w j)) := by
    simp only [curvedRNCMetric]; ring
  have hδ : |(rncRadialSq z - rncRadialSq w) * (if i = j then (1 : ℝ) else 0)|
      ≤ |rncRadialSq z - rncRadialSq w| := by
    by_cases h : i = j <;> simp [h, abs_nonneg]
  have hA := radialSq_diff_structured z w
  have hB := entry_prod_diff_structured z w i j
  rw [hexp, abs_mul, abs_of_nonneg hk0]
  calc -(K / 3) * |(rncRadialSq z - rncRadialSq w) * (if i = j then (1 : ℝ) else 0)
        - (z i * z j - w i * w j)|
      ≤ -(K / 3) * (|(rncRadialSq z - rncRadialSq w) * (if i = j then (1 : ℝ) else 0)|
          + |z i * z j - w i * w j|) :=
        mul_le_mul_of_nonneg_left (htri _ _) hk0
    _ ≤ -(K / 3) * (2 * (Real.sqrt (rncRadialSq (fun a => z a - w a))
          * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w)))) := by
        apply mul_le_mul_of_nonneg_left _ hk0
        have := le_trans hδ hA
        linarith
    _ = 2 * (-K) / 3 *
        (Real.sqrt (rncRadialSq (fun a => z a - w a))
          * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w))) := by ring

/-! ### 3. ★ THE SUPPLIER: the structured INVERSE-metric difference (global, ungated). -/

/-- **★ J4-615 — the zero-constant-term affine-difference supplier, GLOBAL.**  For `K ≤ 0`
    and ALL `z, w ∈ Point n` (no ball, no `r`-gate — the closed rational form has
    denominator `α ≥ 1` everywhere and the E-factor's `w`-growth is exactly eaten by the
    `α(w)` denominator):
        `|gⁱʲ(z) − gⁱʲ(w)| ≤ (2(−K)/3)·‖z−w‖·(‖z‖+‖w‖)`,
    the SAME honest constant `L = 2(−K)/3` as the polynomial metric itself.  Both norm
    factors on the right are `√(rncRadialSq ·)` — the exact shape the banked moment lever
    `gaussDdim_moment_half` converts into `√time` in the E∗E composition (J4-616). -/
theorem curvedRNCInv_diff_structured (K : ℝ) (hK : K ≤ 0) (z w : Point n) (i j : Fin n) :
    |curvedRNCInv K z i j - curvedRNCInv K w i j|
      ≤ 2 * (-K) / 3 *
        (Real.sqrt (rncRadialSq (fun a => z a - w a))
          * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w))) := by
  set X : ℝ := Real.sqrt (rncRadialSq (fun a => z a - w a))
    * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w)) with hXdef
  have hX0 : 0 ≤ X := mul_nonneg (Real.sqrt_nonneg _)
    (by positivity)
  have hk0 : (0 : ℝ) ≤ -(K / 3) := by linarith
  -- denominators ≥ 1
  have haz1 : 1 ≤ 1 - K / 3 * rncRadialSq z := one_sub_K3_radial_ge_one K hK z
  have haw1 : 1 ≤ 1 - K / 3 * rncRadialSq w := one_sub_K3_radial_ge_one K hK w
  have haz0 : (0 : ℝ) < 1 - K / 3 * rncRadialSq z := lt_of_lt_of_le one_pos haz1
  have haw0 : (0 : ℝ) < 1 - K / 3 * rncRadialSq w := lt_of_lt_of_le one_pos haw1
  -- the exact rational-difference identity at q := w, v := z − w
  have hzw : (fun a => w a + (z a - w a)) = z := by funext a; ring
  have hco : ∀ a : Fin n, w a + (z a - w a) = z a := fun a => by ring
  have hsub := curvedRNCInv_sub_eq K hK w (fun a => z a - w a) i j
  rw [hzw] at hsub
  simp only [hco] at hsub
  rw [hsub]
  -- Term 1: the product-modulus term over α(z)
  have ht1 : |(-(K / 3)) * (z i * z j - w i * w j) / (1 - K / 3 * rncRadialSq z)|
      ≤ -(K / 3) * X := by
    rw [abs_div, abs_of_pos haz0, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ -(K / 3))]
    calc -(K / 3) * |z i * z j - w i * w j| / (1 - K / 3 * rncRadialSq z)
        ≤ -(K / 3) * |z i * z j - w i * w j| :=
          div_le_self (mul_nonneg hk0 (abs_nonneg _)) haz1
      _ ≤ -(K / 3) * X :=
          mul_le_mul_of_nonneg_left (entry_prod_diff_structured z w i j) hk0
  -- Term 2: the radial-modulus term — the α(w) cancellation
  have hww : |w i * w j| ≤ rncRadialSq w := by
    calc |w i * w j| = |w i| * |w j| := abs_mul _ _
      _ ≤ Real.sqrt (rncRadialSq w) * Real.sqrt (rncRadialSq w) :=
          mul_le_mul (abs_apply_le_sqrt_radialSq w i) (abs_apply_le_sqrt_radialSq w j)
            (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = rncRadialSq w := Real.mul_self_sqrt (rncRadialSq_nonneg w)
  have hE : |(if i = j then (1 : ℝ) else 0) - K / 3 * (w i * w j)|
      ≤ 1 - K / 3 * rncRadialSq w := by
    have hd1 : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by
      by_cases h : i = j <;> simp [h]
    have htri : |(if i = j then (1 : ℝ) else 0) - K / 3 * (w i * w j)|
        ≤ |(if i = j then (1 : ℝ) else 0)| + |K / 3 * (w i * w j)| := by
      have h := abs_add_le (if i = j then (1 : ℝ) else 0) (-(K / 3 * (w i * w j)))
      simpa [sub_eq_add_neg] using h
    have habs : |K / 3 * (w i * w j)| = -(K / 3) * |w i * w j| := by
      rw [abs_mul, abs_of_nonpos (by linarith : K / 3 ≤ 0)]
    have hmul : -(K / 3) * |w i * w j| ≤ -(K / 3) * rncRadialSq w :=
      mul_le_mul_of_nonneg_left hww hk0
    calc |(if i = j then (1 : ℝ) else 0) - K / 3 * (w i * w j)|
        ≤ |(if i = j then (1 : ℝ) else 0)| + |K / 3 * (w i * w j)| := htri
      _ ≤ 1 + -(K / 3) * rncRadialSq w := by rw [habs]; linarith
      _ = 1 - K / 3 * rncRadialSq w := by ring
  have ht2 : |((if i = j then (1 : ℝ) else 0) - K / 3 * (w i * w j))
        * (K / 3 * (rncRadialSq z - rncRadialSq w))
        / ((1 - K / 3 * rncRadialSq z) * (1 - K / 3 * rncRadialSq w))|
      ≤ -(K / 3) * X := by
    rw [abs_div, abs_of_pos (mul_pos haz0 haw0), abs_mul]
    have habsK : |K / 3 * (rncRadialSq z - rncRadialSq w)|
        = -(K / 3) * |rncRadialSq z - rncRadialSq w| := by
      rw [abs_mul, abs_of_nonpos (by linarith : K / 3 ≤ 0)]
    rw [habsK]
    have hnum : |(if i = j then (1 : ℝ) else 0) - K / 3 * (w i * w j)|
          * (-(K / 3) * |rncRadialSq z - rncRadialSq w|)
        ≤ (1 - K / 3 * rncRadialSq w) * (-(K / 3) * X) :=
      mul_le_mul hE
        (mul_le_mul_of_nonneg_left (radialSq_diff_structured z w) hk0)
        (mul_nonneg hk0 (abs_nonneg _)) (by linarith)
    calc |(if i = j then (1 : ℝ) else 0) - K / 3 * (w i * w j)|
            * (-(K / 3) * |rncRadialSq z - rncRadialSq w|)
          / ((1 - K / 3 * rncRadialSq z) * (1 - K / 3 * rncRadialSq w))
        ≤ (1 - K / 3 * rncRadialSq w) * (-(K / 3) * X)
          / ((1 - K / 3 * rncRadialSq z) * (1 - K / 3 * rncRadialSq w)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hnum
            (inv_nonneg.mpr (mul_pos haz0 haw0).le)
      _ = -(K / 3) * X / (1 - K / 3 * rncRadialSq z) := by
          rw [mul_comm (1 - K / 3 * rncRadialSq z) (1 - K / 3 * rncRadialSq w),
              mul_div_mul_left _ _ haw0.ne']
      _ ≤ -(K / 3) * X := div_le_self (mul_nonneg hk0 hX0) haz1
  calc |(-(K / 3)) * (z i * z j - w i * w j) / (1 - K / 3 * rncRadialSq z)
        + ((if i = j then (1 : ℝ) else 0) - K / 3 * (w i * w j))
          * (K / 3 * (rncRadialSq z - rncRadialSq w))
          / ((1 - K / 3 * rncRadialSq z) * (1 - K / 3 * rncRadialSq w))|
      ≤ |(-(K / 3)) * (z i * z j - w i * w j) / (1 - K / 3 * rncRadialSq z)|
        + |((if i = j then (1 : ℝ) else 0) - K / 3 * (w i * w j))
          * (K / 3 * (rncRadialSq z - rncRadialSq w))
          / ((1 - K / 3 * rncRadialSq z) * (1 - K / 3 * rncRadialSq w))| := abs_add_le _ _
    _ ≤ -(K / 3) * X + -(K / 3) * X := add_le_add ht1 ht2
    _ = 2 * (-K) / 3 * X := by ring

/-- **The (q, v)-shape corollary** — the exact Levi-defect coefficient shape J4-616's
    refined E∗E composition consumes: `|gⁱʲ(q+v) − gⁱʲ(q)| ≤ (2(−K)/3)·‖v‖·(‖q+v‖+‖q‖)`. -/
theorem curvedRNCInv_diff_structured' (K : ℝ) (hK : K ≤ 0) (q v : Point n) (i j : Fin n) :
    |curvedRNCInv K (fun a => q a + v a) i j - curvedRNCInv K q i j|
      ≤ 2 * (-K) / 3 *
        (Real.sqrt (rncRadialSq v)
          * (Real.sqrt (rncRadialSq (fun a => q a + v a)) + Real.sqrt (rncRadialSq q))) := by
  have h := curvedRNCInv_diff_structured K hK (fun a => q a + v a) q i j
  have hv : (fun a => q a + v a - q a) = v := by funext a; ring
  simpa only [hv] using h

/-- **The summed compatibility form** for the E∗E composition:
    `∑ᵢⱼ |gⁱʲ(z) − gⁱʲ(w)| ≤ n²·(2(−K)/3)·‖z−w‖·(‖z‖+‖w‖)`. -/
theorem curvedRNCInv_diff_structured_sum (K : ℝ) (hK : K ≤ 0) (z w : Point n) :
    (∑ i, ∑ j, |curvedRNCInv K z i j - curvedRNCInv K w i j|)
      ≤ (n : ℝ) ^ 2 * (2 * (-K) / 3 *
        (Real.sqrt (rncRadialSq (fun a => z a - w a))
          * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w)))) := by
  calc (∑ i, ∑ j, |curvedRNCInv K z i j - curvedRNCInv K w i j|)
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, 2 * (-K) / 3 *
          (Real.sqrt (rncRadialSq (fun a => z a - w a))
            * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w))) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          curvedRNCInv_diff_structured K hK z w i j
    _ = (n : ℝ) ^ 2 * (2 * (-K) / 3 *
          (Real.sqrt (rncRadialSq (fun a => z a - w a))
            * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w)))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### 4. Non-vacuity gate. -/

/-- **NON-VACUITY.**  For `K < 0`, `n ≥ 2` there are `z, w, i, j` at which the bounded
    difference is GENUINELY NONZERO (z = e₀, w = 0, i = j = 1 gives
    `gⁱʲ(z) − gⁱʲ(w) = 1/(1−K/3) − 1 = (K/3)/(1−K/3) < 0`) and the structured right side
    is strictly positive — the supplier is exercised, not vacuously about `0 ≤ 0`. -/
theorem curvedRNCInv_diff_structured_nonvacuous (K : ℝ) (hK : K < 0) (hn : 2 ≤ n) :
    ∃ (z w : Point n) (i j : Fin n),
      curvedRNCInv K z i j - curvedRNCInv K w i j ≠ 0 ∧
      0 < 2 * (-K) / 3 *
        (Real.sqrt (rncRadialSq (fun a => z a - w a))
          * (Real.sqrt (rncRadialSq z) + Real.sqrt (rncRadialSq w))) := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  set i0 : Fin n := ⟨0, h0⟩ with hi0
  set i1 : Fin n := ⟨1, h1⟩ with hi1
  set z : Point n := fun a => if a = i0 then (1 : ℝ) else 0 with hzdef
  have hne : i1 ≠ i0 := by
    rw [hi0, hi1]
    simp [Fin.ext_iff]
  have hz1 : z i1 = 0 := by simp [hzdef, hne]
  have hzsq : rncRadialSq z = 1 := by
    have h : ∀ a : Fin n, (z a) ^ 2 = if a = i0 then (1 : ℝ) else 0 := fun a => by
      by_cases hh : a = i0 <;> simp [hzdef, hh]
    simp [rncRadialSq, h]
  have hden : (1 : ℝ) < 1 - K / 3 := by linarith
  have hzi : curvedRNCInv K z i1 i1 = 1 / (1 - K / 3) := by
    simp only [curvedRNCInv, hzsq, hz1]
    norm_num
  have hwi : curvedRNCInv K (0 : Point n) i1 i1 = 1 := by
    simp [curvedRNCInv_zero]
  refine ⟨z, 0, i1, i1, ?_, ?_⟩
  · rw [hzi, hwi]
    have hlt : 1 / (1 - K / 3) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    exact ne_of_lt (by linarith)
  · have hz0 : (fun a => z a - (0 : Point n) a) = z := by
      funext a; simp
    have h00 : rncRadialSq (0 : Point n) = 0 := by simp [rncRadialSq]
    rw [hz0, hzsq, h00, Real.sqrt_one, Real.sqrt_zero]
    have hKpos : (0 : ℝ) < -K := by linarith
    nlinarith

/-! ### 5. std-3 audit pins. -/

#print axioms curvedRNCMetric_diff_structured
#print axioms curvedRNCInv_diff_structured
#print axioms curvedRNCInv_diff_structured'
#print axioms curvedRNCInv_diff_structured_sum
#print axioms curvedRNCInv_diff_structured_nonvacuous

end QIQTH.AffineDiff
