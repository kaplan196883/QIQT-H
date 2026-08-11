/-
  FrozenColumn — J4-613: the center-column α = 0 SERIES SPLICE — the mixed-weight domination of
  the Levi series' q = 0 column, |leviSeries E_frozen (s,·,0)| ≤ C·G_{2s} (CLEAN, no τ^{−1/2}),
  from the column α = 0 defect bound (J4-612's `frozenDefectCenterZero_spaceForm`) + the uniform
  α = −1/2 bound on the outer factors (J4-610/612), + the HONEST k ≥ 2 tail exponent.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE MIXED LADDER (the honest exponents — the s^{1/2}-vs-s discrepancy RESOLVED).

  The recursion is `iterE E (k+1) = heatConvK E (iterE E k)` (LeviSeries): the OUTER factor is a
  fresh `E`, the INNER factor is the iterate.  Evaluated at target column `q = 0`,
      iterE (k+1) (s, p, 0) = ∫₀^s ∫_z E(s−σ, p, z) · iterE k (σ, z, 0) dz dσ,
  the INNER column stays `0` at every level, so INDUCTIVELY the inner factor carries the CLEAN
  α = 0 center-column bound while the ONE outer `E(s−σ, p, z)` factor per level has generic
  column `z` and can only carry the α = −1/2 bound `(C/√τ)·G_{2τ}`.  The exponent ladder is
      L_1 = 0  (the center-column bound itself),
      L_{k+1} = L_k + 1/2   (Beta step `∫₀^s (s−σ)^{−1/2}·σ^{L_k} dσ = B(1/2, L_k+1)·s^{L_k+1/2}`),
  i.e. **L_k = (k−1)/2**:  |iterE k (s,·,0)| ≤ D_k · s^{(k−1)/2} · G_{2s}, with
      D_k = C₀·(C·Γ(1/2))^{k−1} / Γ((k+1)/2)
  (the Γ-telescoped Beta product — factorially small, so ∑ D_k < ∞ and the series bound is CLEAN
  on (0,1]).  ⚠ RESOLUTION OF THE J4-612 AUDIT'S O(s) CLAIM: the audit's "k ≥ 2 tail is
  O(s^{2(α+1)−1}) = O(s) at α = 0" implicitly assumed EVERY factor carries the α = 0 bound.  The
  actual mixed chain has ONE α = −1/2 outer factor per level whose column `z` is generic, so the
  k-th term is s^{(k−1)/2}·G — the k = 2 term is **O(s^{1/2})·G, NOT O(s)·G**.  The honest tail is
      |leviSeries E (s,·,0) + E(s,·,0)| ≤ C_tail · √s · G_{2s}   on (0,1]
  (`leviSeries = −E + (k≥2 tail)`; the k = 1 term is `−E` itself, the transport-cancellation
  thread's object).

  ★ BUDGET COMPATIBILITY (vs `CorrHigherReduction.corrHigher_bounded_of_slice`).  The consumer's
  per-slice requirement is `‖∫_z H(t−s) 0 z · F s z 0‖ ≤ K·((t−s)+s) = K·t` with a `t`-UNIFORM
  `K` (that uniformity is the genuine `O(t²)`/bounded-`cRem` content).  The k ≥ 2 tail feeds the
  slice a `C_tail·√s`-weighted Gaussian mass, and `√s ≤ K·s`-type absorption FAILS as `s → 0`
  (`sqrt_exceeds_linear_budget` below): **the √s tail does NOT fit the literal `O((t−s)+s)`
  slice budget**.  Integrated it yields `∫₀^t √s ds ≤ t^{3/2}` (`integral_sqrt_le_linear` below),
  i.e. a `pref·O(t^{3/2})` correction: `o(t)` (so the `t¹` coefficient `a₁` is NOT shifted by the
  tail) but NOT the `O(t²)` the bounded-`cRem` reduction demands — `cRem ~ t^{−1/2}`.  The precise
  residual gap is the single factor `√s → s`, and the fix routes are (i) a `t^{3/2}`-exponent
  variant of `corrHigher_bounded_of_slice` (sufficient for `a₁` if the capstone consumes only the
  `o(t)` statement), or (ii) sharpening the k = 2 term using that the CONSUMER's outer column is
  ALSO localized at 0 (the slice integrates `z` against `H(t−s) 0 z`, a Gaussian centered at 0 —
  a two-sided center-column/moment analysis, not available to this brick's one-sided ladder).

  WHAT LANDS HERE.
    ▸ `colC` — the mixed-ladder constants `D_{m+1} = C₀·(C·Γ(1/2))^m / Γ(m/2+1)` (index m = k−1);
      `colC_summable` — ∑ D < ∞ (even indices are `C₀·(x²)^j/j!`, odd are Γ-dominated by them).
    ▸ `heatConv_le_of_abs_le_pos_right` — the `heatConv` domination step needing the B-bound only
      at the FIXED right column `y` (the LeviSeries lemma demands `∀ q`; the column argument has
      the clean bound only at `q = 0`).
    ▸ `mixedColZ_integrable` / `mixedColS_intervalIntegrable` — the mixed-model `(a, b)`
      integrability pair (outer exponent `a = −1/2`, inner `b = m/2`), mirroring the J4-612
      model conjuncts.
    ▸ ★ `iterE_column_bound` — THE MIXED LADDER: |iterE E (m+1) (s,·,0)| ≤ D_{m+1}·s^{m/2}·G_{2s},
      all s > 0 (induction; per-step `gaussTimePow_conv_beta_scaled` at `(−1/2, m/2)`).
    ▸ ★ `leviSeries_column_bound` — THE CLEAN COLUMN SERIES BOUND:
          |leviSeries E (s,·,0)| ≤ (∑ D)·G_{2s}   on 0 < s ≤ 1  (NO negative power of s).
    ▸ ★ `leviSeries_column_tail_bound` — THE HONEST k ≥ 2 TAIL:
          |leviSeries E (s,·,0) + E(s,·,0)| ≤ (∑_{k≥2} D)·√s·G_{2s}   on 0 < s ≤ 1.
    ▸ ★ `frozenColumn_leviSeries_bound` — the instantiation at the WIRED frozen kernel
      (`frozenDefectKernel`, all suppliers PROVED: J4-610 bound, J4-612 center-zero + IterConv).
    ▸ NON-VACUITY: `frozenColumn_witness_ne_zero` — at curved data (K < 0, n ≥ 2) the CENTER
      COLUMN itself is nonzero at some `p` (the J4-610 witness has base `q = 0`), so the column
      bounds are about a genuinely nonzero column.
    ▸ BUDGET CERTIFICATES: `sqrt_exceeds_linear_budget` (no t-uniform `K` absorbs `√t ≤ K·t`) and
      `integral_sqrt_le_linear` (`∫₀^t √s ≤ t^{3/2}` — the tail's integrated `o(t)` rate).

  ⚠ HONEST SCOPE.  `a₁ = R/6` remains CONDITIONAL: the flat tower is non-vacuous and closed; the
  curved side still owes this column splice's consumer wiring (the √s-vs-s budget gap above), the
  k = 1 `SliceBoundO1`/transport-cancellation thread, the per-q producer re-assembly, the fat-K
  hEmeas/hAdom/hcont piles, the capstone co-instantiation, and the prior piles.  This brick is
  the column SERIES splice + the honest tail-rate verdict.  No axioms, no sorry.
-/
import Mathlib
import QIQTH.FrozenWire

open Finset Filter Topology MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianWidthTransfer QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.CurvedRNCGaugeBundle QIQTH.FrozenGauss QIQTH.FrozenDefect
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.AlphaLevi QIQTH.FrozenWire

namespace QIQTH.FrozenColumn

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. The mixed-ladder constants `colC` and their summability. -/

/-- **The mixed-ladder constant** `colC C C₀ m = C₀·(C·Γ(1/2))^m / Γ(m/2 + 1)` — the coefficient
    of the `k = m+1` column iterate (`D_{m+1}`): one α = 0 seed (`C₀`) and `m` outer α = −1/2
    factors, Beta-telescoped (`∏ B(1/2, (j+1)/2) = Γ(1/2)^m·Γ(1)/Γ((m+2)/2)` shape). -/
noncomputable def colC (C C₀ : ℝ) (m : ℕ) : ℝ :=
  C₀ * (C * Real.Gamma (1 / 2)) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)

theorem colC_nonneg (C C₀ : ℝ) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (m : ℕ) : 0 ≤ colC C C₀ m := by
  unfold colC
  have hx : (0 : ℝ) ≤ C * Real.Gamma (1 / 2) :=
    mul_nonneg hC (Real.Gamma_pos_of_pos (by norm_num)).le
  have hΓ : (0 : ℝ) < Real.Gamma ((m : ℝ) / 2 + 1) :=
    Real.Gamma_pos_of_pos (by positivity)
  exact div_nonneg (mul_nonneg hC₀ (pow_nonneg hx m)) hΓ.le

theorem colC_zero (C C₀ : ℝ) : colC C C₀ 0 = C₀ := by
  unfold colC
  norm_num [Real.Gamma_one]

/-- The one-step ladder recursion `C·D_m·B(1/2, m/2+1) = D_{m+1}` in the exact Γ shape the
    per-step Beta identity produces. -/
theorem colC_succ (C C₀ : ℝ) (m : ℕ) :
    C * colC C C₀ m
        * (Real.Gamma (1 / 2) * Real.Gamma ((m : ℝ) / 2 + 1) / Real.Gamma ((m : ℝ) / 2 + 3 / 2))
      = colC C C₀ (m + 1) := by
  unfold colC
  have h1 : Real.Gamma ((m : ℝ) / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have h2 : Real.Gamma ((m : ℝ) / 2 + 3 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have h3 : ((m + 1 : ℕ) : ℝ) / 2 + 1 = (m : ℝ) / 2 + 3 / 2 := by push_cast; ring
  rw [h3, pow_succ]
  field_simp

/-- **The ladder constants are summable** — the Γ (factorial) decay beats the geometric factor.
    Even indices are EXACTLY `C₀·(x²)^j/j!` (`Γ(j+1) = j!`); odd indices are dominated by
    `2·C₀·x·(x²)^j/j!` (`j! ≤ 2·Γ(j+3/2)`: Γ-monotonicity on `[2,∞)` for `j ≥ 1`, and
    `2·Γ(3/2) = √π ≥ 1` at `j = 0`); both compare to the exponential series. -/
theorem colC_summable (C C₀ : ℝ) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) :
    Summable (colC C C₀) := by
  set x : ℝ := C * Real.Gamma (1 / 2) with hxdef
  have hx : 0 ≤ x := mul_nonneg hC (Real.Gamma_pos_of_pos (by norm_num)).le
  apply Summable.even_add_odd
  · -- even indices: colC (2j) = C₀·(x²)^j/j!
    have heq : (fun j : ℕ => colC C C₀ (2 * j))
        = fun j : ℕ => C₀ * ((x ^ 2) ^ j / (Nat.factorial j : ℝ)) := by
      funext j
      unfold colC
      rw [← hxdef]
      have hc : ((2 * j : ℕ) : ℝ) / 2 + 1 = (j : ℝ) + 1 := by push_cast; ring
      rw [hc, Real.Gamma_nat_eq_factorial j, pow_mul]
      ring
    rw [heq]
    exact (Real.summable_pow_div_factorial (x ^ 2)).mul_left C₀
  · -- odd indices: colC (2j+1) ≤ 2·C₀·x·(x²)^j/j!
    have hbound : ∀ j : ℕ, colC C C₀ (2 * j + 1) ≤ 2 * C₀ * x * (x ^ 2) ^ j / (Nat.factorial j : ℝ) := by
      intro j
      have hc : ((2 * j + 1 : ℕ) : ℝ) / 2 + 1 = (j : ℝ) + 3 / 2 := by push_cast; ring
      have hΓpos : (0 : ℝ) < Real.Gamma ((j : ℝ) + 3 / 2) :=
        Real.Gamma_pos_of_pos (by positivity)
      have hfacpos : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast j.factorial_pos
      have hfac : (Nat.factorial j : ℝ) ≤ 2 * Real.Gamma ((j : ℝ) + 3 / 2) := by
        rcases Nat.eq_zero_or_pos j with h0 | h1
        · subst h0
          have h32 : Real.Gamma ((0 : ℕ) + (3 : ℝ) / 2) = 1 / 2 * Real.Gamma (1 / 2) := by
            rw [show ((0 : ℕ) + (3 : ℝ) / 2) = 1 / 2 + 1 from by norm_num,
                Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
          rw [h32, Real.Gamma_one_half_eq]
          have hπ : (1 : ℝ) ≤ Real.sqrt Real.pi := by
            rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
            exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
          simp only [Nat.factorial_zero, Nat.cast_one]
          linarith
        · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h1
          have hmono : Real.Gamma ((j : ℝ) + 1) ≤ Real.Gamma ((j : ℝ) + 3 / 2) :=
            Real.Gamma_strictMonoOn_Ici.monotoneOn
              (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith)
          rw [Real.Gamma_nat_eq_factorial j] at hmono
          linarith [hΓpos]
      unfold colC
      rw [← hxdef, hc]
      have hxp : x ^ (2 * j + 1) = x * (x ^ 2) ^ j := by
        rw [pow_succ, pow_mul]; ring
      rw [hxp, div_le_div_iff₀ hΓpos hfacpos]
      have hA0 : (0 : ℝ) ≤ C₀ * (x * (x ^ 2) ^ j) :=
        mul_nonneg hC₀ (mul_nonneg hx (pow_nonneg (sq_nonneg x) j))
      have hkey := mul_le_mul_of_nonneg_left hfac hA0
      nlinarith [hkey]
    refine Summable.of_nonneg_of_le (fun j => colC_nonneg C C₀ hC hC₀ _) hbound ?_
    have heq2 : (fun j : ℕ => 2 * C₀ * x * (x ^ 2) ^ j / (Nat.factorial j : ℝ))
        = fun j : ℕ => (2 * C₀ * x) * ((x ^ 2) ^ j / (Nat.factorial j : ℝ)) := by
      funext j; ring
    rw [heq2]
    exact (Real.summable_pow_div_factorial (x ^ 2)).mul_left _

/-! ### 2. The fixed-right-column `heatConv` domination step. -/

/-- **The positive-time `heatConv` domination step with the RIGHT bound only at the FIXED column
    `y`** — the LeviSeries lemma `heatConv_le_of_abs_le_pos` demands `hB` at ALL `q`; the column
    argument has the clean bound only at `q = 0`.  The proof is verbatim: the pointwise step only
    ever evaluates `B` at the fixed outer `y`. -/
theorem heatConv_le_of_abs_le_pos_right (A B A' B' : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (x y : Point n) (ht : 0 < t)
    (hA : ∀ τ p q, 0 < τ → |A τ p q| ≤ A' τ p q)
    (hB : ∀ τ p, 0 < τ → |B τ p y| ≤ B' τ p y)
    (hI1 : IntervalIntegrable (fun s => ‖∫ z, A (t - s) x z * B s z y‖) volume 0 t)
    (hI2 : IntervalIntegrable (fun s => ∫ z, |A (t - s) x z| * |B s z y|) volume 0 t)
    (hIf : ∀ s, Integrable (fun z => |A (t - s) x z| * |B s z y|))
    (hIg : ∀ s, Integrable (fun z => A' (t - s) x z * B' s z y))
    (hIsg : IntervalIntegrable (fun s => ∫ z, A' (t - s) x z * B' s z y) volume 0 t) :
    |heatConv A B t x y| ≤ heatConv A' B' t x y := by
  refine le_trans (heatConv_abs_le A B t x y ht.le hI1 hI2) ?_
  simp only [heatConv]
  refine intervalIntegral.integral_mono_on_of_le_Ioo ht.le hI2 hIsg (fun s hs => ?_)
  obtain ⟨hs0, hst⟩ := hs
  have hts : 0 < t - s := by linarith
  refine integral_mono (hIf s) (hIg s) (fun z => ?_)
  have hAz := hA (t - s) x z hts
  have hBz := hB s z hs0
  exact mul_le_mul hAz hBz (abs_nonneg _) (le_trans (abs_nonneg _) hAz)

/-! ### 3. The mixed-model `(a, b)` integrability pair. -/

/-- **Mixed-model `z`-integrability**: the product of two width-2 base kernels at DIFFERENT time
    exponents `(a, b)` (outer/inner) is `z`-integrable for every `s` — the closed Gaussian form on
    `0 < s < t`, `0` off it (`n ≥ 1`), finiteness at `n = 0`. -/
theorem mixedColZ_integrable (a b C₁ C₂ : ℝ) (t s : ℝ) (x y : Point n) :
    Integrable
      (fun z => C₁ * baseKernelW (2 : ℝ) a (t - s) x z
        * (C₂ * baseKernelW (2 : ℝ) b s z y)) volume := by
  by_cases hs : 0 < s ∧ s < t
  · obtain ⟨hs0, hst⟩ := hs
    have hform : (fun z => C₁ * baseKernelW (2 : ℝ) a (t - s) x z
          * (C₂ * baseKernelW (2 : ℝ) b s z y))
        = fun z => (C₁ * C₂ * ((t - s) ^ a * s ^ b))
            * (gaussDdim (2 * (t - s)) (x - z) * gaussDdim (2 * s) (z - y)) := by
      funext z
      simp only [baseKernelW]
      ring
    rw [hform]
    exact (gaussDdim_mul_integrable (2 * (t - s)) (2 * s) x y).const_mul _
  · rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      exact Integrable.of_finite
    · have hzero : (fun z => C₁ * baseKernelW (2 : ℝ) a (t - s) x z
            * (C₂ * baseKernelW (2 : ℝ) b s z y))
          = fun _ => (0 : ℝ) := by
        funext z
        rcases not_and_or.mp hs with h | h
        · push_neg at h
          simp only [baseKernelW]
          rw [gaussDdim_eq_zero_of_nonpos hn1 (by linarith : 2 * s ≤ 0) (z - y)]
          ring
        · push_neg at h
          simp only [baseKernelW]
          rw [gaussDdim_eq_zero_of_nonpos hn1 (by linarith : 2 * (t - s) ≤ 0) (x - z)]
          ring
      rw [hzero]
      exact integrable_zero _ _ _

/-- **Mixed-model `s`-interval-integrability** (`a, b > −1`): the `z`-integral of the mixed pair
    is a.e. the Beta integrand `const·(t−s)^a·s^b` (Gaussian semigroup), interval-integrable by
    the J4-612 `rpow_mul_rpow_intervalIntegrable`. -/
theorem mixedColS_intervalIntegrable (a b C₁ C₂ : ℝ) (ha : -1 < a) (hb : -1 < b)
    (t : ℝ) (ht : 0 < t) (x y : Point n) :
    IntervalIntegrable
      (fun s => ∫ z, C₁ * baseKernelW (2 : ℝ) a (t - s) x z
        * (C₂ * baseKernelW (2 : ℝ) b s z y)) volume 0 t := by
  have hg_ii : IntervalIntegrable
      (fun s => (C₁ * C₂ * gaussDdim (2 * t) (x - y)) * ((t - s) ^ a * s ^ b)) volume 0 t :=
    (rpow_mul_rpow_intervalIntegrable a b t ha hb ht).const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  have hg : IntegrableOn
      (fun s => (C₁ * C₂ * gaussDdim (2 * t) (x - y)) * ((t - s) ^ a * s ^ b))
      (Set.Ioc 0 t) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]; exact hg_ii
  refine hg.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
  intro hmem
  obtain ⟨hs0, hsle⟩ := hmem
  have hsne : s ≠ t := by simpa using hst
  have hst2 : s < t := lt_of_le_of_ne hsle hsne
  have hts : 0 < t - s := by linarith
  have hform : (fun z => C₁ * baseKernelW (2 : ℝ) a (t - s) x z
        * (C₂ * baseKernelW (2 : ℝ) b s z y))
      = fun z => (C₁ * C₂ * ((t - s) ^ a * s ^ b))
          * (gaussDdim (2 * (t - s)) (x - z) * gaussDdim (2 * s) (z - y)) := by
    funext z
    simp only [baseKernelW]
    ring
  show (C₁ * C₂ * gaussDdim (2 * t) (x - y)) * ((t - s) ^ a * s ^ b)
      = ∫ z, C₁ * baseKernelW (2 : ℝ) a (t - s) x z * (C₂ * baseKernelW (2 : ℝ) b s z y)
  rw [hform, integral_const_mul,
      QIQTH.GaussianConvolution.gaussDdim_conv (2 * (t - s)) (2 * s)
        (by linarith) (by linarith) x y,
      show 2 * (t - s) + 2 * s = 2 * t from by ring]
  ring

/-! ### 4. ★ THE MIXED LADDER — the column iterate bound. -/

/-- **★ `iterE_column_bound` — the mixed center-column ladder.**  From the generic α = −1/2
    one-step bound (`hEbound`, outer factors), the CLEAN α = 0 center-column bound (`hEcol`,
    inner seed), and the α = −1/2 per-step integrability family, the `(m+1)`-st column iterate
    obeys
        `|iterE E (m+1) (s, p, 0)| ≤ D_{m+1} · s^{m/2} · G_{2s}(p)`,   all `s > 0`,
    with the Γ-telescoped `D_{m+1} = colC C C₀ m`.  Induction on `m`; the step is the width-2
    self-similar Beta identity `gaussTimePow_conv_beta_scaled` at exponents `(−1/2, m/2)` — the
    HONEST exponent ladder `L_{m+1} = m/2` (ONE `τ^{−1/2}` outer factor per level; the audit's
    all-α = 0 `O(s)` shape is NOT available since the outer column is generic). -/
theorem iterE_column_bound (E : ℝ → Point n → Point n → ℝ) (C C₀ : ℝ)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q)
    (hEcol : ∀ (τ : ℝ) (p : Point n), 0 < τ →
      |E τ p 0| ≤ C₀ * gaussDdim (2 * τ) (p - 0))
    (hInt : IterConvIntegrableW E (2 : ℝ) (-(1 / 2) : ℝ) C) :
    ∀ (m : ℕ) (s : ℝ), 0 < s → ∀ p : Point n,
      |iterE E (m + 1) s p 0|
        ≤ colC C C₀ m * s ^ ((m : ℝ) / 2) * gaussDdim (2 * s) (p - 0) := by
  intro m
  induction m with
  | zero =>
      intro s hs p
      rw [show (0 : ℕ) + 1 = 1 from rfl, iterE_one, colC_zero,
          show ((0 : ℕ) : ℝ) / 2 = (0 : ℝ) from by norm_num, Real.rpow_zero, mul_one]
      exact hEcol s p hs
  | succ m ih =>
      intro s hs p
      have hm1 : 1 ≤ m + 1 := by omega
      -- the five actual-kernel integrabilities at column 0
      obtain ⟨hI1, hI2, hIf, -, -⟩ := hInt (m + 1) hm1 s hs p 0
      -- the right-column bound for the inner iterate, in `baseKernelW` shape
      have hB : ∀ (τ : ℝ) (z : Point n), 0 < τ →
          |iterE E (m + 1) τ z 0|
            ≤ colC C C₀ m * baseKernelW (2 : ℝ) ((m : ℝ) / 2) τ z 0 := by
        intro τ z hτ
        calc |iterE E (m + 1) τ z 0|
            ≤ colC C C₀ m * τ ^ ((m : ℝ) / 2) * gaussDdim (2 * τ) (z - 0) := ih τ hτ z
          _ = colC C C₀ m * baseKernelW (2 : ℝ) ((m : ℝ) / 2) τ z 0 := by
              simp only [baseKernelW]; ring
      -- the mixed-model integrabilities
      have hIg : ∀ σ, Integrable
          (fun z => C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) (s - σ) p z
            * (colC C C₀ m * baseKernelW (2 : ℝ) ((m : ℝ) / 2) σ z 0)) :=
        fun σ => mixedColZ_integrable (-(1 / 2)) ((m : ℝ) / 2) C (colC C C₀ m) s σ p 0
      have hIsg : IntervalIntegrable
          (fun σ => ∫ z, C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) (s - σ) p z
            * (colC C C₀ m * baseKernelW (2 : ℝ) ((m : ℝ) / 2) σ z 0)) volume 0 s := by
        have hbge : (-1 : ℝ) < (m : ℝ) / 2 := by
          have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          linarith
        exact mixedColS_intervalIntegrable (-(1 / 2)) ((m : ℝ) / 2) C (colC C C₀ m)
          (by norm_num) hbge s hs p 0
      -- unfold one iteration and dominate
      rw [iterE_succ E hm1]
      simp only [heatConvK_apply]
      have hdom := heatConv_le_of_abs_le_pos_right E (iterE E (m + 1))
        (fun τ p' q' => C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p' q')
        (fun σ z' q' => colC C C₀ m * baseKernelW (2 : ℝ) ((m : ℝ) / 2) σ z' q')
        s p 0 hs
        (fun τ p' q' hτ => hEbound τ p' q' hτ)
        (fun τ z' hτ => hB τ z' hτ)
        hI1 hI2 hIf hIg hIsg
      -- evaluate the dominating pair exactly (width-2 Beta identity at (−1/2, m/2))
      have hbge : (-1 : ℝ) < (m : ℝ) / 2 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hRHS : heatConv
            (fun τ p' q' => C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p' q')
            (fun σ z' q' => colC C C₀ m * baseKernelW (2 : ℝ) ((m : ℝ) / 2) σ z' q') s p 0
          = C * colC C C₀ m
              * (s ^ (((m : ℝ) + 1) / 2)
                * (Real.Gamma (1 / 2) * Real.Gamma ((m : ℝ) / 2 + 1)
                    / Real.Gamma ((m : ℝ) / 2 + 3 / 2))
                * gaussDdim (2 * s) (p - 0)) := by
        rw [heatConv_smul_left C (baseKernelW (2 : ℝ) (-(1 / 2)))
              (fun σ z' q' => colC C C₀ m * baseKernelW (2 : ℝ) ((m : ℝ) / 2) σ z' q') s p 0,
            heatConv_smul_right (colC C C₀ m) (baseKernelW (2 : ℝ) (-(1 / 2)))
              (baseKernelW (2 : ℝ) ((m : ℝ) / 2)) s p 0]
        unfold baseKernelW
        rw [gaussTimePow_conv_beta_scaled 2 (-(1 / 2)) ((m : ℝ) / 2) (by norm_num)
              (by norm_num) hbge s hs p 0,
            show (-(1 / 2 : ℝ) + (m : ℝ) / 2 + 1) = ((m : ℝ) + 1) / 2 from by ring,
            show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) from by norm_num,
            show (-(1 / 2 : ℝ) + (m : ℝ) / 2 + 2) = (m : ℝ) / 2 + 3 / 2 from by ring]
        ring
      calc |heatConv E (iterE E (m + 1)) s p 0|
          ≤ heatConv
              (fun τ p' q' => C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p' q')
              (fun σ z' q' => colC C C₀ m * baseKernelW (2 : ℝ) ((m : ℝ) / 2) σ z' q')
              s p 0 := hdom
        _ = C * colC C C₀ m
              * (s ^ (((m : ℝ) + 1) / 2)
                * (Real.Gamma (1 / 2) * Real.Gamma ((m : ℝ) / 2 + 1)
                    / Real.Gamma ((m : ℝ) / 2 + 3 / 2))
                * gaussDdim (2 * s) (p - 0)) := hRHS
        _ = colC C C₀ (m + 1) * s ^ (((m + 1 : ℕ) : ℝ) / 2) * gaussDdim (2 * s) (p - 0) := by
            rw [show (((m + 1 : ℕ) : ℝ) / 2) = ((m : ℝ) + 1) / 2 from by push_cast; ring,
                ← colC_succ C C₀ m]
            ring

/-! ### 5. ★ THE CLEAN COLUMN SERIES BOUND AND THE HONEST k ≥ 2 TAIL. -/

/-- **★ `leviSeries_column_bound` — the CLEAN center-column series bound.**  On `0 < s ≤ 1`,
        `|leviSeries E (s, p, 0)| ≤ (∑ D)·G_{2s}(p)`   — NO negative power of `s`:
    the `k = 1` term already carries the clean α = 0 column bound and the ladder only ADDS
    positive half-powers.  (The α = −1/2 GENERIC-column series bound irreducibly carries
    `τ^{−1/2}`, `AlphaLevi.negHalf_weight_unbounded`; the column is strictly better.) -/
theorem leviSeries_column_bound (E : ℝ → Point n → Point n → ℝ) (C C₀ : ℝ)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q)
    (hEcol : ∀ (τ : ℝ) (p : Point n), 0 < τ →
      |E τ p 0| ≤ C₀ * gaussDdim (2 * τ) (p - 0))
    (hInt : IterConvIntegrableW E (2 : ℝ) (-(1 / 2) : ℝ) C) :
    ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ p : Point n,
      |leviSeries E s p 0| ≤ (∑' m : ℕ, colC C C₀ m) * gaussDdim (2 * s) (p - 0) := by
  intro s hs hs1 p
  have hG0 : 0 ≤ gaussDdim (2 * s) (p - 0) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hterm := iterE_column_bound E C C₀ hC hC₀ hEbound hEcol hInt
  -- termwise clean domination on (0,1]
  have hterm2 : ∀ m : ℕ, |iterE E (m + 1) s p 0|
      ≤ colC C C₀ m * gaussDdim (2 * s) (p - 0) := by
    intro m
    have hpow : s ^ ((m : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one hs.le hs1 (by positivity)
    calc |iterE E (m + 1) s p 0|
        ≤ colC C C₀ m * s ^ ((m : ℝ) / 2) * gaussDdim (2 * s) (p - 0) := hterm m s hs p
      _ ≤ colC C C₀ m * 1 * gaussDdim (2 * s) (p - 0) := by
          have := colC_nonneg C C₀ hC hC₀ m
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow this) hG0
      _ = colC C C₀ m * gaussDdim (2 * s) (p - 0) := by ring
  have hSumCG : Summable (fun m : ℕ => colC C C₀ m * gaussDdim (2 * s) (p - 0)) :=
    (colC_summable C C₀ hC hC₀).mul_right _
  have hAbsSum : Summable (fun m : ℕ => |iterE E (m + 1) s p 0|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hterm2 hSumCG
  have hnormeq : (fun m : ℕ => ‖(-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p 0‖)
      = fun m : ℕ => |iterE E (m + 1) s p 0| := by
    funext m
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  calc |leviSeries E s p 0|
      ≤ ∑' m : ℕ, |iterE E (m + 1) s p 0| := by
        simp only [leviSeries, ← Real.norm_eq_abs]
        calc ‖∑' m : ℕ, (-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p 0‖
            ≤ ∑' m : ℕ, ‖(-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p 0‖ :=
              norm_tsum_le_tsum_norm (by rw [hnormeq]; exact hAbsSum)
          _ = ∑' m : ℕ, |iterE E (m + 1) s p 0| := by rw [hnormeq]
    _ ≤ ∑' m : ℕ, colC C C₀ m * gaussDdim (2 * s) (p - 0) :=
        hAbsSum.tsum_le_tsum hterm2 hSumCG
    _ = (∑' m : ℕ, colC C C₀ m) * gaussDdim (2 * s) (p - 0) := tsum_mul_right

/-- **★ `leviSeries_column_tail_bound` — the HONEST k ≥ 2 column tail.**  On `0 < s ≤ 1`,
        `|leviSeries E (s, p, 0) + E (s, p, 0)| ≤ (∑_{m} D_{m+2})·√s·G_{2s}(p)`.
    `leviSeries = −E + (k ≥ 2 tail)`, and each `k = m+2` term carries `s^{(m+1)/2} ≤ √s`.
    ⚠ HONEST EXPONENT: the tail is `O(√s)·G`, NOT `O(s)·G` — the mixed ladder's `k = 2` term has
    exactly ONE outer `τ^{−1/2}` factor giving `B(1/2,1)·s^{1/2}`.  See the header for the budget
    verdict against `corrHigher_bounded_of_slice`. -/
theorem leviSeries_column_tail_bound (E : ℝ → Point n → Point n → ℝ) (C C₀ : ℝ)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q)
    (hEcol : ∀ (τ : ℝ) (p : Point n), 0 < τ →
      |E τ p 0| ≤ C₀ * gaussDdim (2 * τ) (p - 0))
    (hInt : IterConvIntegrableW E (2 : ℝ) (-(1 / 2) : ℝ) C) :
    ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ p : Point n,
      |leviSeries E s p 0 + E s p 0|
        ≤ (∑' m : ℕ, colC C C₀ (m + 1))
            * (Real.sqrt s * gaussDdim (2 * s) (p - 0)) := by
  intro s hs hs1 p
  have hG0 : 0 ≤ gaussDdim (2 * s) (p - 0) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hsqrt0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hterm := iterE_column_bound E C C₀ hC hC₀ hEbound hEcol hInt
  -- the k = m+2 term carries √s
  have hterm3 : ∀ m : ℕ, |iterE E (m + 1 + 1) s p 0|
      ≤ colC C C₀ (m + 1) * (Real.sqrt s * gaussDdim (2 * s) (p - 0)) := by
    intro m
    have hD0 := colC_nonneg C C₀ hC hC₀ (m + 1)
    have hpow : s ^ (((m + 1 : ℕ) : ℝ) / 2) ≤ Real.sqrt s := by
      have hsplit : (((m + 1 : ℕ) : ℝ) / 2) = 1 / 2 + (m : ℝ) / 2 := by push_cast; ring
      have hle1 : s ^ ((m : ℝ) / 2) ≤ 1 :=
        Real.rpow_le_one hs.le hs1 (by positivity)
      calc s ^ (((m + 1 : ℕ) : ℝ) / 2)
          = s ^ ((1 : ℝ) / 2) * s ^ ((m : ℝ) / 2) := by
            rw [hsplit, Real.rpow_add hs]
        _ ≤ s ^ ((1 : ℝ) / 2) * 1 :=
            mul_le_mul_of_nonneg_left hle1 (Real.rpow_nonneg hs.le _)
        _ = Real.sqrt s := by rw [mul_one, ← Real.sqrt_eq_rpow]
    calc |iterE E (m + 1 + 1) s p 0|
        ≤ colC C C₀ (m + 1) * s ^ (((m + 1 : ℕ) : ℝ) / 2) * gaussDdim (2 * s) (p - 0) :=
          hterm (m + 1) s hs p
      _ ≤ colC C C₀ (m + 1) * Real.sqrt s * gaussDdim (2 * s) (p - 0) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hD0) hG0
      _ = colC C C₀ (m + 1) * (Real.sqrt s * gaussDdim (2 * s) (p - 0)) := by ring
  -- summabilities
  have hColSum1 : Summable (fun m : ℕ => colC C C₀ (m + 1)) :=
    (summable_nat_add_iff 1).mpr (colC_summable C C₀ hC hC₀)
  have hSumTail : Summable
      (fun m : ℕ => colC C C₀ (m + 1) * (Real.sqrt s * gaussDdim (2 * s) (p - 0))) :=
    hColSum1.mul_right _
  have hAbsSum2 : Summable (fun m : ℕ => |iterE E (m + 1 + 1) s p 0|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hterm3 hSumTail
  -- clean-domination summability for the FULL signed series (to split off k = 1)
  have hterm2 : ∀ m : ℕ, |iterE E (m + 1) s p 0|
      ≤ colC C C₀ m * gaussDdim (2 * s) (p - 0) := by
    intro m
    have hpow : s ^ ((m : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one hs.le hs1 (by positivity)
    calc |iterE E (m + 1) s p 0|
        ≤ colC C C₀ m * s ^ ((m : ℝ) / 2) * gaussDdim (2 * s) (p - 0) := hterm m s hs p
      _ ≤ colC C C₀ m * 1 * gaussDdim (2 * s) (p - 0) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (colC_nonneg C C₀ hC hC₀ m)) hG0
      _ = colC C C₀ m * gaussDdim (2 * s) (p - 0) := by ring
  have hSumCG : Summable (fun m : ℕ => colC C C₀ m * gaussDdim (2 * s) (p - 0)) :=
    (colC_summable C C₀ hC hC₀).mul_right _
  have hAbsSum : Summable (fun m : ℕ => |iterE E (m + 1) s p 0|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hterm2 hSumCG
  have hnormeq : (fun m : ℕ => ‖(-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p 0‖)
      = fun m : ℕ => |iterE E (m + 1) s p 0| := by
    funext m
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  have hfSum : Summable (fun m : ℕ => (-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p 0) :=
    Summable.of_norm (by rw [hnormeq]; exact hAbsSum)
  -- split off the k = 1 term: leviSeries = −E + tail
  have hsplit : leviSeries E s p 0
      = (-1 : ℝ) ^ (0 + 1) * iterE E (0 + 1) s p 0
        + ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0 := by
    simp only [leviSeries]
    exact hfSum.tsum_eq_zero_add
  have hf0 : (-1 : ℝ) ^ (0 + 1) * iterE E (0 + 1) s p 0 = -(E s p 0) := by
    rw [show (0 : ℕ) + 1 = 1 from rfl, iterE_one]
    ring
  have htaileq : leviSeries E s p 0 + E s p 0
      = ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0 := by
    rw [hsplit, hf0]; ring
  -- bound the tail tsum
  have hnormeq2 : (fun m : ℕ => ‖(-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0‖)
      = fun m : ℕ => |iterE E (m + 1 + 1) s p 0| := by
    funext m
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  calc |leviSeries E s p 0 + E s p 0|
      = |∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0| := by rw [htaileq]
    _ ≤ ∑' m : ℕ, |iterE E (m + 1 + 1) s p 0| := by
        rw [← Real.norm_eq_abs]
        calc ‖∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0‖
            ≤ ∑' m : ℕ, ‖(-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0‖ :=
              norm_tsum_le_tsum_norm (by rw [hnormeq2]; exact hAbsSum2)
          _ = ∑' m : ℕ, |iterE E (m + 1 + 1) s p 0| := by rw [hnormeq2]
    _ ≤ ∑' m : ℕ, colC C C₀ (m + 1) * (Real.sqrt s * gaussDdim (2 * s) (p - 0)) :=
        hAbsSum2.tsum_le_tsum hterm3 hSumTail
    _ = (∑' m : ℕ, colC C C₀ (m + 1))
          * (Real.sqrt s * gaussDdim (2 * s) (p - 0)) := tsum_mul_right

/-- **★ `leviSeries_column_k3_bound` — the k ≥ 3 sub-tail is ALREADY `O(s)` (Sol-audit
    sharpening).**  On `0 < s ≤ 1`,
        `|leviSeries E (s, p, 0) + E (s, p, 0) − iterE E 2 (s, p, 0)| ≤ (∑ D_{k≥3})·s·G_{2s}(p)`:
    for `k = m+3` the ladder exponent is `(m+2)/2 ≥ 1`, so every k ≥ 3 term is `≤ D_k·s·G` on
    `(0,1]`.  **This isolates the k = 2 term `iterE E 2` as the SOLE obstruction** between the
    `O(√s)` tail and the consumer's `O(s)` slice budget — the J4-614 target. -/
theorem leviSeries_column_k3_bound (E : ℝ → Point n → Point n → ℝ) (C C₀ : ℝ)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q)
    (hEcol : ∀ (τ : ℝ) (p : Point n), 0 < τ →
      |E τ p 0| ≤ C₀ * gaussDdim (2 * τ) (p - 0))
    (hInt : IterConvIntegrableW E (2 : ℝ) (-(1 / 2) : ℝ) C) :
    ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ p : Point n,
      |leviSeries E s p 0 + E s p 0 - iterE E 2 s p 0|
        ≤ (∑' m : ℕ, colC C C₀ (m + 2)) * (s * gaussDdim (2 * s) (p - 0)) := by
  intro s hs hs1 p
  have hG0 : 0 ≤ gaussDdim (2 * s) (p - 0) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hterm := iterE_column_bound E C C₀ hC hC₀ hEbound hEcol hInt
  -- the k = m+3 term carries s^{(m+2)/2} ≤ s on (0,1]
  have hterm4 : ∀ m : ℕ, |iterE E (m + 1 + 1 + 1) s p 0|
      ≤ colC C C₀ (m + 2) * (s * gaussDdim (2 * s) (p - 0)) := by
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
    calc |iterE E (m + 1 + 1 + 1) s p 0|
        ≤ colC C C₀ (m + 2) * s ^ (((m + 2 : ℕ) : ℝ) / 2) * gaussDdim (2 * s) (p - 0) :=
          hterm (m + 2) s hs p
      _ ≤ colC C C₀ (m + 2) * s * gaussDdim (2 * s) (p - 0) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hD0) hG0
      _ = colC C C₀ (m + 2) * (s * gaussDdim (2 * s) (p - 0)) := by ring
  -- summabilities (as in the tail bound, shifted once more)
  have hterm2 : ∀ m : ℕ, |iterE E (m + 1) s p 0|
      ≤ colC C C₀ m * gaussDdim (2 * s) (p - 0) := by
    intro m
    have hpow : s ^ ((m : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one hs.le hs1 (by positivity)
    calc |iterE E (m + 1) s p 0|
        ≤ colC C C₀ m * s ^ ((m : ℝ) / 2) * gaussDdim (2 * s) (p - 0) := hterm m s hs p
      _ ≤ colC C C₀ m * 1 * gaussDdim (2 * s) (p - 0) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (colC_nonneg C C₀ hC hC₀ m)) hG0
      _ = colC C C₀ m * gaussDdim (2 * s) (p - 0) := by ring
  have hSumCG : Summable (fun m : ℕ => colC C C₀ m * gaussDdim (2 * s) (p - 0)) :=
    (colC_summable C C₀ hC hC₀).mul_right _
  have hAbsSum : Summable (fun m : ℕ => |iterE E (m + 1) s p 0|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hterm2 hSumCG
  have hnormeq : (fun m : ℕ => ‖(-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p 0‖)
      = fun m : ℕ => |iterE E (m + 1) s p 0| := by
    funext m
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  have hfSum : Summable (fun m : ℕ => (-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p 0) :=
    Summable.of_norm (by rw [hnormeq]; exact hAbsSum)
  -- two splits: leviSeries = −E + iterE 2 + Σ_{k≥3}
  have hsplit1 : leviSeries E s p 0
      = (-1 : ℝ) ^ (0 + 1) * iterE E (0 + 1) s p 0
        + ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0 := by
    simp only [leviSeries]
    exact hfSum.tsum_eq_zero_add
  have hfSum1 : Summable
      (fun m : ℕ => (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0) :=
    (summable_nat_add_iff 1).mpr hfSum
  have hsplit2 : (∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0)
      = (-1 : ℝ) ^ (0 + 1 + 1) * iterE E (0 + 1 + 1) s p 0
        + ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0 :=
    hfSum1.tsum_eq_zero_add
  have hf0 : (-1 : ℝ) ^ (0 + 1) * iterE E (0 + 1) s p 0 = -(E s p 0) := by
    rw [show (0 : ℕ) + 1 = 1 from rfl, iterE_one]
    ring
  have hf1 : (-1 : ℝ) ^ (0 + 1 + 1) * iterE E (0 + 1 + 1) s p 0 = iterE E 2 s p 0 := by
    norm_num
  have htaileq : leviSeries E s p 0 + E s p 0 - iterE E 2 s p 0
      = ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0 := by
    rw [hsplit1, hsplit2, hf0, hf1]; ring
  have hAbsSum3 : Summable (fun m : ℕ => |iterE E (m + 1 + 1 + 1) s p 0|) := by
    have := (summable_nat_add_iff 2).mpr hAbsSum
    exact this.congr (fun m => by norm_num)
  have hColSum2 : Summable (fun m : ℕ => colC C C₀ (m + 2)) := by
    have := (summable_nat_add_iff 2).mpr (colC_summable C C₀ hC hC₀)
    exact this.congr (fun m => by norm_num)
  have hSumK3 : Summable
      (fun m : ℕ => colC C C₀ (m + 2) * (s * gaussDdim (2 * s) (p - 0))) :=
    hColSum2.mul_right _
  have hnormeq3 : (fun m : ℕ => ‖(-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0‖)
      = fun m : ℕ => |iterE E (m + 1 + 1 + 1) s p 0| := by
    funext m
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  calc |leviSeries E s p 0 + E s p 0 - iterE E 2 s p 0|
      = |∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0| := by
        rw [htaileq]
    _ ≤ ∑' m : ℕ, |iterE E (m + 1 + 1 + 1) s p 0| := by
        rw [← Real.norm_eq_abs]
        calc ‖∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0‖
            ≤ ∑' m : ℕ, ‖(-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0‖ :=
              norm_tsum_le_tsum_norm (by rw [hnormeq3]; exact hAbsSum3)
          _ = ∑' m : ℕ, |iterE E (m + 1 + 1 + 1) s p 0| := by rw [hnormeq3]
    _ ≤ ∑' m : ℕ, colC C C₀ (m + 2) * (s * gaussDdim (2 * s) (p - 0)) :=
        hAbsSum3.tsum_le_tsum hterm4 hSumK3
    _ = (∑' m : ℕ, colC C C₀ (m + 2)) * (s * gaussDdim (2 * s) (p - 0)) := tsum_mul_right

/-! ### 6. ★ THE FROZEN INSTANTIATION — all suppliers proved. -/

/-- **The frozen kernel's center-column α = 0 bound, transported to the KERNEL** (from the J4-612
    pd-form `frozenDefectCenterZero_spaceForm`): `|E_frozen(τ, p, 0)| ≤ C₀·G_{2τ}(p)`, ALL `τ > 0`
    (above the τ-gate the kernel is `0`; the center `q = 0` is inside every `r`-ball). -/
theorem frozenColumnKernel_bound (K r : ℝ) (hK : K ≤ 0) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (τ : ℝ) (p : Point n), 0 < τ →
      |frozenDefectKernel K r τ p 0| ≤ C₀ * gaussDdim (2 * τ) (p - 0) := by
  obtain ⟨C₀, hC₀, hcol⟩ := frozenDefectCenterZero_spaceForm (n := n) K hK
  refine ⟨C₀, hC₀, fun τ p hτ => ?_⟩
  have hG0 : 0 ≤ gaussDdim (2 * τ) (p - 0) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  by_cases hτ1 : τ ≤ 1
  · have hq0 : rncRadialSq (0 : Point n) ≤ r ^ 2 := by
      rw [rncRadialSq_zero]; positivity
    rw [frozenDefectKernel_eq_pd K r τ p 0 hτ hτ1 hq0]
    have h := hcol τ hτ p
    simp only [Pi.zero_apply, sub_zero]
    simpa using h
  · push_neg at hτ1
    unfold frozenDefectKernel
    rw [if_neg (fun h => absurd h.2.1 (not_le.mpr hτ1)), abs_zero]
    exact mul_nonneg hC₀.le hG0

/-- **★★ J4-613 — THE FROZEN CENTER-COLUMN SERIES SPLICE.**  For every `K ≤ 0`, `r ≥ 0` there are
    `C_col, C_tail ≥ 0` with, on `0 < s ≤ 1` and all `p`:
      (i)  **the CLEAN column series bound**  `|leviSeries E_frozen (s, p, 0)| ≤ C_col·G_{2s}(p)`
           (NO `s^{−1/2}` — versus the generic-column `(C_L/√s)·G_{2s}` of J4-612), and
      (ii) **the honest k ≥ 2 tail**
           `|leviSeries E_frozen (s, p, 0) + E_frozen (s, p, 0)| ≤ C_tail·√s·G_{2s}(p)`
           (`leviSeries = −E + O(√s)·G`: the series splice isolates the k = 1 term for the
           transport-cancellation thread with an EXPLICIT √s-tail — honest exponent, NOT O(s)).
    All suppliers are PROVED, none carried: the α = −1/2 one-step bound (J4-610 via J4-612's
    kernel transport), the center-column α = 0 bound (J4-612 `frozenDefectCenterZero_spaceForm`),
    and the per-step integrability (J4-612 producer).  ⚠ NOT `a₁ = R/6`. -/
theorem frozenColumn_leviSeries_bound (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r) :
    ∃ C_col C_tail : ℝ, 0 ≤ C_col ∧ 0 ≤ C_tail ∧
      ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
        |leviSeries (frozenDefectKernel K r) s p 0| ≤ C_col * gaussDdim (2 * s) (p - 0) ∧
        |leviSeries (frozenDefectKernel K r) s p 0 + frozenDefectKernel K r s p 0|
          ≤ C_tail * (Real.sqrt s * gaussDdim (2 * s) (p - 0)) := by
  obtain ⟨C, hCpos, hbd⟩ := frozenDefectKernel_bound (n := n) K r hK hr
  obtain ⟨C₀, hC₀pos, hcolK⟩ := frozenColumnKernel_bound (n := n) K r hK
  -- the one-step bound in the engine's `baseKernelW` shape (as in J4-612's wire)
  have hEboundW : ∀ (τ : ℝ) (p q : Point n), 0 < τ →
      |frozenDefectKernel K r τ p q| ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q := by
    intro τ p q hτ
    rw [baseKernelW_negHalf_apply τ hτ]
    calc |frozenDefectKernel K r τ p q|
        ≤ C / Real.sqrt τ * gaussDdim (2 * τ) (p - q) := hbd τ p q hτ
      _ = C * (gaussDdim (2 * τ) (p - q) / Real.sqrt τ) := by ring
  -- the α = −1/2 per-step integrability, discharged (J4-612 producer)
  have hInt : IterConvIntegrableW (frozenDefectKernel K r) (2 : ℝ) (-(1 / 2) : ℝ) C :=
    iterConvIntegrableW_of_bound_baseMeas_alpha (frozenDefectKernel K r) (-(1 / 2)) C
      (by norm_num) hEboundW
      (fun τ hτ p q => frozenDefectKernel_zero K r τ hτ p q)
      (frozenDefectKernel_stronglyMeasurable K r)
  refine ⟨∑' m : ℕ, colC C C₀ m, ∑' m : ℕ, colC C C₀ (m + 1),
    tsum_nonneg (fun m => colC_nonneg C C₀ hCpos.le hC₀pos.le m),
    tsum_nonneg (fun m => colC_nonneg C C₀ hCpos.le hC₀pos.le (m + 1)),
    fun s p hs hs1 => ⟨?_, ?_⟩⟩
  · exact leviSeries_column_bound (frozenDefectKernel K r) C C₀ hCpos.le hC₀pos.le
      hEboundW (fun τ p' hτ => hcolK τ p' hτ) hInt s hs hs1 p
  · exact leviSeries_column_tail_bound (frozenDefectKernel K r) C C₀ hCpos.le hC₀pos.le
      hEboundW (fun τ p' hτ => hcolK τ p' hτ) hInt s hs hs1 p

/-- **★ `frozenColumn_k2_isolation` — the k = 2 term is the SOLE obstruction (frozen).**  For
    `K ≤ 0`, `r ≥ 0` there is `C_k3 ≥ 0` with, on `0 < s ≤ 1`,
        `|leviSeries E_frozen (s,p,0) + E_frozen (s,p,0) − (E∗E)(s,p,0)| ≤ C_k3·s·G_{2s}(p)`:
    the k ≥ 3 sub-tail ALREADY fits the `O(s)` slice shape; only the single convolution square
    `iterE E_frozen 2 = E ∗ E` stands between the column splice and the consumer's linear
    budget — the pinned J4-614 target (Gaussian-bridge/moment estimate on `E∗E` at both end
    columns 0). -/
theorem frozenColumn_k2_isolation (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r) :
    ∃ C_k3 : ℝ, 0 ≤ C_k3 ∧
      ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
        |leviSeries (frozenDefectKernel K r) s p 0 + frozenDefectKernel K r s p 0
            - iterE (frozenDefectKernel K r) 2 s p 0|
          ≤ C_k3 * (s * gaussDdim (2 * s) (p - 0)) := by
  obtain ⟨C, hCpos, hbd⟩ := frozenDefectKernel_bound (n := n) K r hK hr
  obtain ⟨C₀, hC₀pos, hcolK⟩ := frozenColumnKernel_bound (n := n) K r hK
  have hEboundW : ∀ (τ : ℝ) (p q : Point n), 0 < τ →
      |frozenDefectKernel K r τ p q| ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q := by
    intro τ p q hτ
    rw [baseKernelW_negHalf_apply τ hτ]
    calc |frozenDefectKernel K r τ p q|
        ≤ C / Real.sqrt τ * gaussDdim (2 * τ) (p - q) := hbd τ p q hτ
      _ = C * (gaussDdim (2 * τ) (p - q) / Real.sqrt τ) := by ring
  have hInt : IterConvIntegrableW (frozenDefectKernel K r) (2 : ℝ) (-(1 / 2) : ℝ) C :=
    iterConvIntegrableW_of_bound_baseMeas_alpha (frozenDefectKernel K r) (-(1 / 2)) C
      (by norm_num) hEboundW
      (fun τ hτ p q => frozenDefectKernel_zero K r τ hτ p q)
      (frozenDefectKernel_stronglyMeasurable K r)
  exact ⟨∑' m : ℕ, colC C C₀ (m + 2),
    tsum_nonneg (fun m => colC_nonneg C C₀ hCpos.le hC₀pos.le (m + 2)),
    fun s p hs hs1 => leviSeries_column_k3_bound (frozenDefectKernel K r) C C₀
      hCpos.le hC₀pos.le hEboundW (fun τ p' hτ => hcolK τ p' hτ) hInt s hs hs1 p⟩

/-! ### 7. Non-vacuity: the CENTER COLUMN itself is nonzero at curved data. -/

/-- **NON-VACUITY (adversarial, column-specific).**  For `K < 0`, `n ≥ 2`, ANY `r`, and ANY
    `0 < τ ≤ 1`, the CENTER COLUMN `E_frozen(τ, ·, 0)` is nonzero at some `p`: the J4-610 witness
    at ball radius `0` forces its base point `q = 0` (radial-square `≤ 0` on a sum of squares),
    so the witness IS a center-column witness.  Hence the column bounds of
    `frozenColumn_leviSeries_bound` are about a GENUINELY nonzero column, not `0 ≤ bound`. -/
theorem frozenColumn_witness_ne_zero (K r : ℝ) (hKlt : K < 0) (hn : 2 ≤ n)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ p : Point n, frozenDefectKernel K r τ p 0 ≠ 0 := by
  obtain ⟨q, v, hq, hne⟩ := frozenDefect_witness_ne_zero K hKlt hn 0 τ hτ
  -- the radius-0 gate forces q = 0
  have hq0 : q = (0 : Point n) := by
    have hr0 : rncRadialSq q ≤ 0 := by simpa using hq
    have hsum0 : rncRadialSq q = 0 := le_antisymm hr0 (rncRadialSq_nonneg q)
    funext a
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (q i))).mp (by simpa [rncRadialSq] using hsum0) a (Finset.mem_univ a)
    have : q a = 0 := sq_eq_zero_iff.mp h
    simpa using this
  rw [hq0] at hne
  refine ⟨fun a => (0 : Point n) a + v a, ?_⟩
  have hq0gate : rncRadialSq (0 : Point n) ≤ r ^ 2 := by
    rw [rncRadialSq_zero]; positivity
  rw [frozenDefectKernel_eq_pd K r τ (fun a => (0 : Point n) a + v a) 0 hτ hτ1 hq0gate]
  simp only [Pi.zero_apply, zero_add, sub_zero]
  simpa using hne

/-! ### 8. BUDGET CERTIFICATES — the √s tail vs the `O((t−s)+s)` slice budget. -/

/-- **The √-weight EXCEEDS every t-uniform linear budget** (the negative half of the budget
    verdict): for NO constant `K` does `√t ≤ K·t` hold down to `t → 0⁺` — witnessed by an explicit
    `t ∈ (0,1]` with `K·t < √t`.  Hence the k ≥ 2 column tail `C_tail·√s·G` does NOT fit the
    per-slice `K·((t−s)+s)` requirement of `CorrHigherReduction.corrHigher_bounded_of_slice`
    with a t-uniform `K` — the bounded-`cRem` (`O(t²)`) reduction is NOT reached by this brick;
    the residual gap is the factor `√s → s`. -/
theorem sqrt_exceeds_linear_budget (K : ℝ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ K * t < Real.sqrt t := by
  set M : ℝ := max K 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right K 0
  have hM1 : 0 < M + 1 := by linarith
  refine ⟨((M + 1) ^ 2)⁻¹, by positivity, ?_, ?_⟩
  · rw [inv_le_one_iff₀]
    right
    nlinarith
  · have hsq : Real.sqrt (((M + 1) ^ 2)⁻¹) = (M + 1)⁻¹ := by
      rw [Real.sqrt_inv, Real.sqrt_sq hM1.le]
    rw [hsq]
    have hKM : K ≤ M := le_max_left K 0
    have hstep : M * ((M + 1) ^ 2)⁻¹ < (M + 1)⁻¹ := by
      have h2 : (0 : ℝ) < (M + 1) ^ 2 := by positivity
      have hdiv : M / (M + 1) ^ 2 < 1 / (M + 1) := by
        rw [div_lt_div_iff₀ h2 hM1]
        nlinarith
      simpa [div_eq_mul_inv] using hdiv
    calc K * ((M + 1) ^ 2)⁻¹ ≤ M * ((M + 1) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hKM (by positivity)
      _ < (M + 1)⁻¹ := hstep

/-- **The tail's integrated rate** (the positive half of the budget verdict):
    `∫₀^t √s ds ≤ t·√t = t^{3/2}` — the `O(√s)` per-slice tail folds under the Duhamel `∫₀^t ds`
    to a `pref·O(t^{3/2})` correction: `o(t)` (the `a₁` coefficient of `t¹` is NOT shifted by the
    k ≥ 2 tail) but NOT the `O(t²)` that bounded-`cRem` demands. -/
theorem integral_sqrt_le_linear (t : ℝ) (ht : 0 ≤ t) :
    ∫ s in (0)..t, Real.sqrt s ≤ t * Real.sqrt t := by
  have h1 : IntervalIntegrable (fun s => Real.sqrt s) volume 0 t :=
    Real.continuous_sqrt.intervalIntegrable 0 t
  have h2 : IntervalIntegrable (fun _ : ℝ => Real.sqrt t) volume 0 t :=
    intervalIntegrable_const
  calc ∫ s in (0)..t, Real.sqrt s
      ≤ ∫ _ in (0)..t, Real.sqrt t :=
        intervalIntegral.integral_mono_on ht h1 h2
          (fun s hs => Real.sqrt_le_sqrt hs.2)
    _ = (t - 0) • Real.sqrt t := intervalIntegral.integral_const _
    _ = t * Real.sqrt t := by simp

end QIQTH.FrozenColumn

section AxiomChecks
open QIQTH.FrozenColumn
#print axioms colC_summable
#print axioms heatConv_le_of_abs_le_pos_right
#print axioms mixedColZ_integrable
#print axioms mixedColS_intervalIntegrable
#print axioms iterE_column_bound
#print axioms leviSeries_column_bound
#print axioms leviSeries_column_tail_bound
#print axioms leviSeries_column_k3_bound
#print axioms frozenColumnKernel_bound
#print axioms frozenColumn_k2_isolation
#print axioms frozenColumn_leviSeries_bound
#print axioms frozenColumn_witness_ne_zero
#print axioms sqrt_exceeds_linear_budget
#print axioms integral_sqrt_le_linear
end AxiomChecks
