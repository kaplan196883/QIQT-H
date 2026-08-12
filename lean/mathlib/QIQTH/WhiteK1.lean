/-
  WhiteK1 — J4-635: the k = 1 WALL — the SHAPE VERDICT + the honest ceiling.  ONE brick of the
  `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING new about the coefficient.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★★ THE SHAPE VERDICT (the J4-635 finding; Sol-confirmed, gpt-5.5-pro high).
  The J4-634 reduction offered the k = 1 budget from the QUADRATIC-COEFFICIENT column bound
      `|E_white(s,p,0)| ≤ C_E·r(p)²·G_{ws}(p)`      (the "J4-635 target Prop").
  THAT INTERFACE IS THE WRONG SHAPE for the as-built whitened witness.  The exact chart-side
  normal form (banked `flatCurvatureResidue_leading`) of the defect of the ORDER-ZERO-amplitude
  whitened witness (`whiteAmbientKernel = √det g^κ(q)·G_τ∘chart` — NO `τ·u₁` transport layer) is
      `E = (1/τ)·G_τ·[½tr(ĝ⁻¹−δ) − ½Σ ĝ⁻¹Γ̂x] + (1/τ²)·G_τ·[−¼Σ(ĝ⁻¹−δ)xx]`,
  and with the banked quadratic dev `|ĝ⁻¹−δ| ≤ M·r²` and linear Christoffel `|Γ̂| ≤ C_Γ·‖x‖`
  the TRUE column shape is
      `|E(s,x,0)| ≤ C·[ (r²/s) + (r²/s)² ]·G_s(x)`      (★ the INVERSE-LINEAR shape),
  proved at the actual whitened chart data in §2 (`whiteChart_heatOp_invtau_bound`).
  The two shapes are INEQUIVALENT and the gap is real:
    • §4 `invtauProbe_not_quadratic_coeff` — a kernel satisfying the inverse-linear shape with
      `C_E = 1` satisfies the quadratic-coefficient bound for NO constant (the `1/s` is real);
    • §4 `far_O1_le_invtau` — conversely the O(1)·G far/annulus bound (banked `hpkgBound`) IS
      subsumed by the inverse-linear shape on `r ≥ a`, `s ≤ 1` — so inverse-linear is the honest
      GLOBAL interface shape for the order-0 witness;
    • §3 ★ `k1CeilingW_of_invtau_shape` — what the true shape DELIVERS: the O(t) CEILING
          `|heatConv H E t 0 0| ≤ C₁·G_{wt}(0)·t`      on `(0,1]`
      (absorption `(r²/τ)^k·G_τ ≤ C·G_{2τ}` + the banked Chapman–Kolmogorov pairing
      `∫G_a·G_b = G_{a+b}(0)` + the antitone peak) — ONE FULL POWER OF `t` SHORT of the
      `K1TransportBudgetW` `t²` demand.
  WHY THE BUDGET IS OUT OF REACH (not merely unproved) FOR THIS WITNESS: for the order-0
  parametrix the k = 1 Duhamel correction on the diagonal is exactly where the `a₁·t·pref` mass
  lives (`trueKernel − W₀ = pref·(R/6·t + O(t²))` at the diagonal); a `t²` bound would contradict
  `R ≠ 0`.  Consistently, the consuming capstone (`trueKernel_diagonal_a1_eq_R6`) pins `H`'s
  diagonal to `heatParametrixFn N` with `N ≥ 1` — the amplitude ALREADY carries `τ·u₁`
  (`u₁(0) = R/6`), and only for such an ORDER-ONE witness is the defect `O(τ)·G` (the J4-634
  RUNG-1 linear-gain shape) and the `t²` budget true.  A `q`-only first-order layer
  `√det g(q)·(1+τ·c₁(q))` does NOT suffice (its defect keeps the `(1/τ)` transport layer AND adds
  `c₁·W₀ = O(1)·G`); the genuine fix is the `p`-dependent transported `u₁` (the banked
  `transportCoeff` machinery) — the recommended J4-636.

  ── WHAT IS PROVED HERE (all axiom-free):
    §1  `normalform_abs_bound_raw` — the lever-free `(1/τ)+(1/τ²)` normal-form assembly.
    §2  ★ `whiteChart_heatOp_invtau_bound` — the TRUE near-diagonal column shape at the actual
        whitened chart data (every row `q ∈ K`, uniform gate), un-absorbed:
            `|heatOp ĝ_q ĝ⁻¹_q (flat phase) τ x 0| ≤ cA·(r²/τ)·G_τ(x) + cB·(r²/τ)²·G_τ(x)`;
        + `whiteChart_invtau_implies_offdiag` — consistency: the banked absorbed `O(1)·G_{2τ}`
        bound (J4-623 shape) RE-DERIVES from it (the raw bound is at least as strong).
    §3  ★ `K1LinearCeilingW` + `k1CeilingW_of_invtau_shape` — the honest O(t) ceiling the
        inverse-linear shape delivers (the k = 1 slice consumption via pairing/second-moment).
    §4  ★ the interface gap (`invtauProbe_not_quadratic_coeff`) + the far subsumption
        (`far_O1_le_invtau`).
    §5  non-vacuity gates (probe nonzero; ceiling fires at a nonzero column and the banked
        nonzero Gaussian slice kernel).

  ⚠ HONEST FRAMING.  `a₁ = R/6` remains CONDITIONAL: the flat tower is closed and non-vacuous;
  the curved side still owes the K1 content — NOW RE-SCOPED: not the J4-634 quadratic-coefficient
  bound (shown here to be the wrong interface for the order-0 witness) but the ORDER-ONE
  (`τ·u₁`-amplitude) whitened witness whose defect has the linear gain (J4-636) — plus the
  Duhamel-split integrability carry, the fat-K carrier piles, the capstone co-instantiation at
  the whitened witness, and the prior piles.  Nothing here proves anything about the coefficient
  value.  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.WhiteCapstoneWire
import QIQTH.WhiteOffDiag
import QIQTH.CConvV2GaussianPairing

open Finset Filter Topology MeasureTheory Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.RNCDecay QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.PullbackMetric QIQTH.ExpMap
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp
open QIQTH.GaussianWidthTransfer QIQTH.WhiteWitness QIQTH.WhiteReplay QIQTH.WhiteOffDiag
open QIQTH.WidthFree QIQTH.WhiteCapstoneWire QIQTH.CConvV2GaussianPairing
open QIQTH.GaussianConvolution
open scoped Interval

namespace QIQTH.WhiteK1

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §1. The lever-free normal-form assembly (the un-absorbed variant of J4-623 §0). -/

/-- **The pure-arithmetic assembly, un-absorbed**: if the two normal-form coefficients satisfy
    `|S₁| ≤ cA·r²` and `|S₂| ≤ cB·(r²)²`, then
        `|(1/τ)·G·S₁ + (1/τ²)·G·S₂| ≤ cA·(r²/τ)·G + cB·(r²/τ)²·G`
    — the `(1/τ)` powers kept EXPLICIT (no width lever, no `G₂` landing).  This is the honest
    shape layer: the inverse powers of `τ` are REAL, not absorbable into `r²` alone. -/
theorem normalform_abs_bound_raw (τ G S1 S2 r2 cA cB : ℝ)
    (hτ : 0 < τ) (hG : 0 ≤ G)
    (hS1 : |S1| ≤ cA * r2) (hS2 : |S2| ≤ cB * r2 ^ 2) :
    |1 / τ * G * S1 + 1 / τ ^ 2 * G * S2|
      ≤ cA * (r2 / τ * G) + cB * ((r2 / τ) ^ 2 * G) := by
  have hτG : 0 ≤ 1 / τ * G := by positivity
  have hτG2 : 0 ≤ 1 / τ ^ 2 * G := by positivity
  have ha : |1 / τ * G * S1| ≤ cA * (r2 / τ * G) := by
    rw [abs_mul, abs_of_nonneg hτG]
    calc 1 / τ * G * |S1| ≤ 1 / τ * G * (cA * r2) := mul_le_mul_of_nonneg_left hS1 hτG
      _ = cA * (r2 / τ * G) := by ring
  have hb : |1 / τ ^ 2 * G * S2| ≤ cB * ((r2 / τ) ^ 2 * G) := by
    rw [abs_mul, abs_of_nonneg hτG2]
    calc 1 / τ ^ 2 * G * |S2| ≤ 1 / τ ^ 2 * G * (cB * r2 ^ 2) :=
          mul_le_mul_of_nonneg_left hS2 hτG2
      _ = cB * ((r2 / τ) ^ 2 * G) := by ring
  calc |1 / τ * G * S1 + 1 / τ ^ 2 * G * S2|
      ≤ |1 / τ * G * S1| + |1 / τ ^ 2 * G * S2| := abs_add_le _ _
    _ ≤ cA * (r2 / τ * G) + cB * ((r2 / τ) ^ 2 * G) := add_le_add ha hb

/-! ### §2. ★ The TRUE near-diagonal column shape at the actual whitened chart data. -/

/-- **★ `whiteChart_heatOp_invtau_bound` — the un-absorbed whitened chart defect bound (the
    TRUE k = 1 column shape).**  For the whitened chart metric pair there are ONE radius
    `r₀ > 0` and constants `cA, cB ≥ 0` with
        `|heatOp ĝ_q ĝ⁻¹_q (flat phase G) τ x 0|
           ≤ cA·(r²(x)/τ)·G_τ(x) + cB·(r²(x)/τ)²·G_τ(x)`
    for EVERY row `q ∈ K`, EVERY `τ > 0` and every `‖x‖ < r₀`.  Same mechanism as the banked
    J4-623 absorbed bound (normal form + quadratic dev + linear Christoffel), but the inverse
    `τ`-powers are kept EXPLICIT — this is the honest near-diagonal structure: the defect of the
    ORDER-ZERO-amplitude witness is `O(1)·G` at `r² ~ τ` (parabolic scale), NOT `O(r²)·G` and
    NOT `O(τ)·G`.  NOT `a₁ = R/6`. -/
theorem whiteChart_heatOp_invtau_bound (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∃ cA cB : ℝ, 0 ≤ cA ∧ 0 ≤ cB
      ∧ ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ x : Point n, ‖x‖ < r₀ →
      |heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w)
        (fun t x y => flatPhaseModel t x y) τ x (0 : Point n)|
      ≤ cA * (rncRadialSq x / τ * gaussDdim τ x)
        + cB * ((rncRadialSq x / τ) ^ 2 * gaussDdim τ x) := by
  classical
  obtain ⟨r₁, hr₁0, M₁, hM₁0, hdev⟩ := whitePullbackMetricInv_dev_uniform κ hκ hKc
  obtain ⟨rΓ, hrΓ0, CΓ, hCΓ0, hΓ⟩ := whiteChart_christoffel_linear_uniform κ hκ hKc
  set r₀ : ℝ := min r₁ rΓ with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hr₁0 hrΓ0
  set Gb : ℝ := 1 + M₁ * ((n : ℝ) * r₀ ^ 2) with hGbdef
  have hGb0 : 0 ≤ Gb := add_nonneg zero_le_one (mul_nonneg hM₁0 (by positivity))
  set cA : ℝ := 1 / 2 * ((n : ℝ) * M₁) + 1 / 2 * ((n : ℝ) ^ 3 * (Gb * CΓ)) with hcAdef
  set cB : ℝ := 1 / 4 * ((n : ℝ) ^ 2 * M₁) with hcBdef
  have hcA0 : 0 ≤ cA :=
    add_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg n) hM₁0))
      (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (mul_nonneg hGb0 hCΓ0)))
  have hcB0 : 0 ≤ cB := mul_nonneg (by norm_num) (mul_nonneg (by positivity) hM₁0)
  refine ⟨r₀, hr₀0, cA, cB, hcA0, hcB0, ?_⟩
  intro q hq τ hτ x hx
  have hx1 : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxΓ : ‖x‖ < rΓ := lt_of_lt_of_le hx (min_le_right _ _)
  have hG : 0 < gaussDdim τ x := gaussDdim_pos τ hτ x
  -- rewrite the heat operator into the flat-Gaussian normal form
  have hK1 : (fun u => flatPhaseModel u x (0 : Point n)) = (fun u => gaussDdim u x) := by
    funext u
    simp only [flatPhaseModel]
    congr 1
    funext i
    simp
  have hK2 : (fun p => flatPhaseModel τ p (0 : Point n)) = gaussDdim τ := by
    funext p
    simp only [flatPhaseModel]
    congr 1
    funext i
    simp
  have hexpr : heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
      (fun w => whitePullbackMetricInv κ hκ hKc q w)
      (fun t x y => flatPhaseModel t x y) τ x (0 : Point n)
      = deriv (fun s => gaussDdim s x) τ
        - laplaceBeltrami (fun w => whitePullbackMetric κ hκ hKc q w)
            (fun w => whitePullbackMetricInv κ hκ hKc q w) (gaussDdim τ) x := by
    simp only [heatOp]
    rw [hK1, hK2]
  have hlead := flatCurvatureResidue_leading τ hτ
    (fun w => whitePullbackMetric κ hκ hKc q w)
    (fun w => whitePullbackMetricInv κ hκ hKc q w) x
  rw [hexpr, hlead]
  -- the geometric radial data
  have hr2b : rncRadialSq x ≤ (n : ℝ) * r₀ ^ 2 := by
    refine rncRadialSq_le_of_mem_closedBall (q := x) (r := r₀) ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx.le
  have hdev' : ∀ i j : Fin n,
      |whitePullbackMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)|
        ≤ M₁ * rncRadialSq x := fun i j => hdev q hq x hx1 i j
  have hxk : ∀ k : Fin n, |x k| ≤ Real.sqrt (rncRadialSq x) :=
    fun k => QIQTH.FrozenDefect.abs_apply_le_sqrt_radialSq x k
  have hxn : ‖x‖ ≤ Real.sqrt (rncRadialSq x) := by
    have h := norm_le_rncRadial x
    simpa only [rncRadial] using h
  have hxk_prod : ∀ k : Fin n, ‖x‖ * |x k| ≤ rncRadialSq x := by
    intro k
    calc ‖x‖ * |x k| ≤ Real.sqrt (rncRadialSq x) * Real.sqrt (rncRadialSq x) :=
          mul_le_mul hxn (hxk k) (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = rncRadialSq x := Real.mul_self_sqrt (rncRadialSq_nonneg x)
  have hxij : ∀ i j : Fin n, |x i * x j| ≤ rncRadialSq x := by
    intro i j
    rw [abs_mul]
    calc |x i| * |x j| ≤ Real.sqrt (rncRadialSq x) * Real.sqrt (rncRadialSq x) :=
          mul_le_mul (hxk i) (hxk j) (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = rncRadialSq x := Real.mul_self_sqrt (rncRadialSq_nonneg x)
  -- bounded whitened inverse entries
  have hgib : ∀ a b : Fin n, |whitePullbackMetricInv κ hκ hKc q x a b| ≤ Gb := by
    intro a b
    have hd := hdev' a b
    have hδ : |(if a = b then (1 : ℝ) else 0)| ≤ 1 := by
      by_cases h : a = b <;> simp [h]
    have htri : |whitePullbackMetricInv κ hκ hKc q x a b|
        ≤ |whitePullbackMetricInv κ hκ hKc q x a b - (if a = b then (1 : ℝ) else 0)|
          + |(if a = b then (1 : ℝ) else 0)| := by
      calc |whitePullbackMetricInv κ hκ hKc q x a b|
          = |(whitePullbackMetricInv κ hκ hKc q x a b - (if a = b then (1 : ℝ) else 0))
              + (if a = b then (1 : ℝ) else 0)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hmono : M₁ * rncRadialSq x ≤ M₁ * ((n : ℝ) * r₀ ^ 2) :=
      mul_le_mul_of_nonneg_left hr2b hM₁0
    calc |whitePullbackMetricInv κ hκ hKc q x a b| ≤ M₁ * rncRadialSq x + 1 := by
          linarith [htri, hd, hδ]
      _ ≤ Gb := by rw [hGbdef]; linarith
  -- T1: the trace deviation
  have hT1 : |∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1)|
      ≤ (n : ℝ) * (M₁ * rncRadialSq x) := by
    calc |∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1)|
        ≤ ∑ i, |whitePullbackMetricInv κ hκ hKc q x i i - 1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, M₁ * rncRadialSq x := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hdev' i i
          rw [if_pos rfl] at h
          exact h
      _ = (n : ℝ) * (M₁ * rncRadialSq x) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- T2: the Christoffel contraction
  have hΓ' : ∀ k i j : Fin n,
      |christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| ≤ CΓ * ‖x‖ :=
    fun k i j => hΓ q hq x hxΓ k i j
  have hT2term : ∀ i j k : Fin n,
      |whitePullbackMetricInv κ hκ hKc q x i j
        * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
            (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
        * x k| ≤ Gb * (CΓ * rncRadialSq x) := by
    intro i j k
    rw [abs_mul, abs_mul]
    have hbc : |christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| * |x k|
        ≤ CΓ * rncRadialSq x := by
      calc |christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
            (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| * |x k|
          ≤ (CΓ * ‖x‖) * |x k| :=
            mul_le_mul_of_nonneg_right (hΓ' k i j) (abs_nonneg _)
        _ = CΓ * (‖x‖ * |x k|) := by ring
        _ ≤ CΓ * rncRadialSq x := mul_le_mul_of_nonneg_left (hxk_prod k) hCΓ0
    calc |whitePullbackMetricInv κ hκ hKc q x i j|
          * |christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
              (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| * |x k|
        = |whitePullbackMetricInv κ hκ hKc q x i j|
          * (|christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
              (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| * |x k|) := by ring
      _ ≤ Gb * (CΓ * rncRadialSq x) :=
          mul_le_mul (hgib i j) hbc
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hGb0
  have hT2 : |∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
      * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
          (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
      * x k| ≤ (n : ℝ) ^ 3 * (Gb * (CΓ * rncRadialSq x)) := by
    calc |∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
          * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
              (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
          * x k|
        ≤ ∑ i, |∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
            * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
            * x k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ((n : ℝ) ^ 2 * (Gb * (CΓ * rncRadialSq x))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc |∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
                * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                    (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
                * x k|
              ≤ ∑ j, |∑ k, whitePullbackMetricInv κ hκ hKc q x i j
                  * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                      (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
                  * x k| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _j : Fin n, ((n : ℝ) * (Gb * (CΓ * rncRadialSq x))) := by
                refine Finset.sum_le_sum fun j _ => ?_
                calc |∑ k, whitePullbackMetricInv κ hκ hKc q x i j
                      * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                          (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
                      * x k|
                    ≤ ∑ k, |whitePullbackMetricInv κ hκ hKc q x i j
                        * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                            (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
                        * x k| := Finset.abs_sum_le_sum_abs _ _
                  _ ≤ ∑ _k : Fin n, (Gb * (CΓ * rncRadialSq x)) :=
                      Finset.sum_le_sum fun k _ => hT2term i j k
                  _ = (n : ℝ) * (Gb * (CΓ * rncRadialSq x)) := by
                      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                        nsmul_eq_mul]
            _ = (n : ℝ) ^ 2 * (Gb * (CΓ * rncRadialSq x)) := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                ring
      _ = (n : ℝ) ^ 3 * (Gb * (CΓ * rncRadialSq x)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- S1: the 1/τ coefficient
  have hS1 : |1 / 2 * (∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1))
      - 1 / 2 * (∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
          * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
              (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
          * x k)| ≤ cA * rncRadialSq x := by
    have hsplit : |1 / 2 * (∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1))
        - 1 / 2 * (∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
            * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
            * x k)|
        ≤ 1 / 2 * |∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1)|
          + 1 / 2 * |∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
              * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                  (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
              * x k| := by
      rw [sub_eq_add_neg]
      calc _ ≤ |1 / 2 * (∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1))|
            + |-(1 / 2 * (∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
                * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                    (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
                * x k))| := abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_mul, abs_mul]; norm_num
    calc _ ≤ _ := hsplit
      _ ≤ 1 / 2 * ((n : ℝ) * (M₁ * rncRadialSq x))
          + 1 / 2 * ((n : ℝ) ^ 3 * (Gb * (CΓ * rncRadialSq x))) := by
          have h1 := mul_le_mul_of_nonneg_left hT1 (by norm_num : (0:ℝ) ≤ 1 / 2)
          have h2 := mul_le_mul_of_nonneg_left hT2 (by norm_num : (0:ℝ) ≤ 1 / 2)
          linarith
      _ = cA * rncRadialSq x := by rw [hcAdef]; ring
  -- S2: the 1/τ² coefficient
  have hS2 : |(-1) / 4 * (∑ i, ∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
      - (if i = j then (1 : ℝ) else 0)) * (x i * x j))| ≤ cB * rncRadialSq x ^ 2 := by
    rw [abs_mul]
    have hq14 : |(-1 : ℝ) / 4| = 1 / 4 := by norm_num
    rw [hq14]
    have hD : |∑ i, ∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
        - (if i = j then (1 : ℝ) else 0)) * (x i * x j)|
        ≤ (n : ℝ) ^ 2 * (M₁ * rncRadialSq x * rncRadialSq x) := by
      calc |∑ i, ∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
            - (if i = j then (1 : ℝ) else 0)) * (x i * x j)|
          ≤ ∑ i, |∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
              - (if i = j then (1 : ℝ) else 0)) * (x i * x j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, ((n : ℝ) * (M₁ * rncRadialSq x * rncRadialSq x)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc |∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
                  - (if i = j then (1 : ℝ) else 0)) * (x i * x j)|
                ≤ ∑ j, |(whitePullbackMetricInv κ hκ hKc q x i j
                    - (if i = j then (1 : ℝ) else 0)) * (x i * x j)| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _j : Fin n, (M₁ * rncRadialSq x * rncRadialSq x) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  rw [abs_mul]
                  exact mul_le_mul (hdev' i j) (hxij i j) (abs_nonneg _)
                    (mul_nonneg hM₁0 (rncRadialSq_nonneg x))
              _ = (n : ℝ) * (M₁ * rncRadialSq x * rncRadialSq x) := by
                  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (n : ℝ) ^ 2 * (M₁ * rncRadialSq x * rncRadialSq x) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc (1 : ℝ) / 4 * |∑ i, ∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
          - (if i = j then (1 : ℝ) else 0)) * (x i * x j)|
        ≤ 1 / 4 * ((n : ℝ) ^ 2 * (M₁ * rncRadialSq x * rncRadialSq x)) :=
          mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = cB * rncRadialSq x ^ 2 := by rw [hcBdef]; ring
  -- assemble, un-absorbed
  exact normalform_abs_bound_raw τ (gaussDdim τ x) _ _ (rncRadialSq x)
    cA cB hτ hG.le hS1 hS2

/-- **Consistency gate — the banked absorbed shape RE-DERIVES from the raw shape**: applying
    the banked width levers to `whiteChart_heatOp_invtau_bound` recovers an `O(1)·G_{2τ}` bound
    of exactly the J4-623 landing shape.  (The raw bound is at least as strong; the two bricks
    agree.)  NOT `a₁ = R/6`. -/
theorem whiteChart_invtau_implies_offdiag (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ x : Point n, ‖x‖ < r₀ →
      |heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w)
        (fun t x y => flatPhaseModel t x y) τ x (0 : Point n)|
      ≤ C * gaussDdim (2 * τ) x := by
  obtain ⟨r₀, hr₀0, cA, cB, hcA0, hcB0, hbd⟩ := whiteChart_heatOp_invtau_bound κ hκ hKc
  obtain ⟨CL1, hCL1, hlev1⟩ :=
    gaussDdim_absorb_one (n := n) (η := 0) (lam := 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CL2, hCL2, hlev2⟩ :=
    gaussDdim_absorb_two (n := n) (η := 0) (lam := 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨r₀, hr₀0, cA * CL1 + cB * CL2,
    add_nonneg (mul_nonneg hcA0 hCL1.le) (mul_nonneg hcB0 hCL2.le), ?_⟩
  intro q hq τ hτ x hx
  have h1 : rncRadialSq x / τ * gaussDdim τ x ≤ CL1 * gaussDdim (2 * τ) x :=
    hlev1 τ hτ x x (by norm_num)
  have h2 : (rncRadialSq x / τ) ^ 2 * gaussDdim τ x ≤ CL2 * gaussDdim (2 * τ) x :=
    hlev2 τ hτ x x (by norm_num)
  calc |heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w)
        (fun t x y => flatPhaseModel t x y) τ x (0 : Point n)|
      ≤ cA * (rncRadialSq x / τ * gaussDdim τ x)
        + cB * ((rncRadialSq x / τ) ^ 2 * gaussDdim τ x) := hbd q hq τ hτ x hx
    _ ≤ cA * (CL1 * gaussDdim (2 * τ) x) + cB * (CL2 * gaussDdim (2 * τ) x) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hcA0) (mul_le_mul_of_nonneg_left h2 hcB0)
    _ = (cA * CL1 + cB * CL2) * gaussDdim (2 * τ) x := by ring

/-! ### §3. ★ The honest O(t) ceiling the inverse-linear shape delivers. -/

/-- **`K1LinearCeilingW` — the O(t) ceiling Prop** (mirror of `K1TransportBudgetW` with `t¹` in
    place of `t²`): the k = 1 Duhamel correction is `O(t)·G_{wt}(0)` on the diagonal.  This is
    what the TRUE (inverse-linear) column shape of the order-0 witness delivers — ONE power of
    `t` short of the budget; the missing power is exactly the `a₁·t` mass. -/
def K1LinearCeilingW (w : ℝ) (H E : ℝ → Point n → Point n → ℝ) : Prop :=
  ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
    |heatConv H E t 0 0| ≤ C₁ * gaussDdim (w * t) (0 : Point n) * t

/-- **★ `k1CeilingW_of_invtau_shape` — the k = 1 slice consumption of the TRUE column shape.**
    If the defect's center column obeys the inverse-linear shape
        `|E(s,p,0)| ≤ C_E·[(r²/s) + (r²/s)²]·G_{ws}(p)`   on `(0,1]`,
    and `H` is Gaussian-dominated with `H(0,0,·) = 0`, then
        `|heatConv H E t 0 0| ≤ C₁·G_{wt}(0)·t`   on `(0,1]`
    — the O(t) CEILING.  Mechanism: absorption `(r²/(ws))^k·G_{ws} ≤ CL_k·G_{2ws}` converts the
    column into `O(1)·G_{2ws}`; the banked Chapman–Kolmogorov pairing
    `∫ G_{2(t−s)}·G_{2ws} = G_{2(t−s)+2ws}(0)` and the antitone peak
    (`2(t−s)+2ws ≥ 2t`, `w ≥ 2`) make each slice `s`-uniformly `≤ C·G_{wt}(0)`; the outer
    `s`-integral then pays exactly ONE power of `t`.  ⚠ NO `t²`: the slice bound is `O(1)`, not
    `O(s)` — this is the honest ceiling of the order-0 witness, not a lossy estimate. -/
theorem k1CeilingW_of_invtau_shape (w : ℝ) (hw2 : 2 ≤ w)
    (E : ℝ → Point n → Point n → ℝ) (C_E : ℝ) (hCE : 0 ≤ C_E)
    (hE : ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |E s p 0| ≤ C_E * (rncRadialSq (p - 0) / s * gaussDdim (w * s) (p - 0)
        + (rncRadialSq (p - 0) / s) ^ 2 * gaussDdim (w * s) (p - 0)))
    (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ) (hCH : 0 ≤ C_H)
    (hH : ∀ (a : ℝ) (ζ : Point n), 0 < a →
      |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ))
    (hH0 : ∀ ζ : Point n, H 0 0 ζ = 0) :
    K1LinearCeilingW w H E := by
  have hw0 : (0 : ℝ) < w := lt_of_lt_of_le two_pos hw2
  obtain ⟨CL1, hCL1, hlev1⟩ :=
    gaussDdim_absorb_one (n := n) (η := 0) (lam := 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CL2, hCL2, hlev2⟩ :=
    gaussDdim_absorb_two (n := n) (η := 0) (lam := 2) (by norm_num) (by norm_num) (by norm_num)
  set Cc : ℝ := C_E * (w * CL1 + w ^ 2 * CL2) with hCcdef
  have hCc0 : 0 ≤ Cc :=
    mul_nonneg hCE (add_nonneg (mul_nonneg hw0.le hCL1.le)
      (mul_nonneg (by positivity) hCL2.le))
  -- the absorbed O(1) column bound
  have hcol : ∀ (s : ℝ) (z : Point n), 0 < s → s ≤ 1 →
      |E s z 0| ≤ Cc * gaussDdim (2 * (w * s)) z := by
    intro s z hs hs1
    have hws : 0 < w * s := mul_pos hw0 hs
    have h1 : rncRadialSq z / (w * s) * gaussDdim (w * s) z
        ≤ CL1 * gaussDdim (2 * (w * s)) z := hlev1 (w * s) hws z z (by norm_num)
    have h2 : (rncRadialSq z / (w * s)) ^ 2 * gaussDdim (w * s) z
        ≤ CL2 * gaussDdim (2 * (w * s)) z := hlev2 (w * s) hws z z (by norm_num)
    have hr1 : rncRadialSq z / s * gaussDdim (w * s) z
        = w * (rncRadialSq z / (w * s) * gaussDdim (w * s) z) := by
      field_simp
    have hr2 : (rncRadialSq z / s) ^ 2 * gaussDdim (w * s) z
        = w ^ 2 * ((rncRadialSq z / (w * s)) ^ 2 * gaussDdim (w * s) z) := by
      field_simp
      try ring
    calc |E s z 0|
        ≤ C_E * (rncRadialSq (z - 0) / s * gaussDdim (w * s) (z - 0)
            + (rncRadialSq (z - 0) / s) ^ 2 * gaussDdim (w * s) (z - 0)) := hE s z hs hs1
      _ = C_E * (w * (rncRadialSq z / (w * s) * gaussDdim (w * s) z)
            + w ^ 2 * ((rncRadialSq z / (w * s)) ^ 2 * gaussDdim (w * s) z)) := by
          rw [sub_zero, hr1, hr2]
      _ ≤ C_E * (w * (CL1 * gaussDdim (2 * (w * s)) z)
            + w ^ 2 * (CL2 * gaussDdim (2 * (w * s)) z)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hCE
          · exact mul_le_mul_of_nonneg_left h1 hw0.le
          · exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cc * gaussDdim (2 * (w * s)) z := by rw [hCcdef]; ring
  refine ⟨C_H * Cc * Real.sqrt (w / 2) ^ n,
    mul_nonneg (mul_nonneg hCH hCc0) (by positivity), fun t ht ht1 => ?_⟩
  set K : ℝ := C_H * Cc * Real.sqrt (w / 2) ^ n * gaussDdim (w * t) (0 : Point n) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCH hCc0) (by positivity))
      (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  -- the s-UNIFORM slice bound (this is where the t² budget is lost: the slice is O(1), not O(s))
  have hslice : ∀ s ∈ Ι (0 : ℝ) t, ‖∫ z, H (t - s) 0 z * E s z 0‖ ≤ K := by
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rcases lt_or_eq_of_le hs.2 with hst | hseq
    · -- 0 < s < t: pairing + antitone peak
      have hts : 0 < t - s := by linarith
      have hs1 : s ≤ 1 := le_trans hs.2 ht1
      have hdom : ∀ z : Point n, ‖H (t - s) 0 z * E s z 0‖
          ≤ C_H * Cc * (gaussDdim (2 * (t - s)) z * gaussDdim (2 * (w * s)) z) := by
        intro z
        rw [Real.norm_eq_abs, abs_mul]
        have hHz := hH (t - s) z hts
        rw [gaussDdim_zero_sub] at hHz
        have hEz := hcol s z hs.1 hs1
        calc |H (t - s) 0 z| * |E s z 0|
            ≤ (C_H * gaussDdim (2 * (t - s)) z) * (Cc * gaussDdim (2 * (w * s)) z) :=
              mul_le_mul hHz hEz (abs_nonneg _)
                (mul_nonneg hCH (QIQTH.ResidueBound.gaussDdim_nonneg _ _))
          _ = C_H * Cc * (gaussDdim (2 * (t - s)) z * gaussDdim (2 * (w * s)) z) := by ring
      have hgint : Integrable (fun z : Point n =>
          C_H * Cc * (gaussDdim (2 * (t - s)) z * gaussDdim (2 * (w * s)) z)) volume :=
        (gaussDdim_pair_integrable _ _).const_mul _
      calc ‖∫ z, H (t - s) 0 z * E s z 0‖
          ≤ ∫ z, ‖H (t - s) 0 z * E s z 0‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ z, C_H * Cc * (gaussDdim (2 * (t - s)) z * gaussDdim (2 * (w * s)) z) :=
            integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _)
              hgint (Eventually.of_forall hdom)
        _ = C_H * Cc * ∫ z, gaussDdim (2 * (t - s)) z * gaussDdim (2 * (w * s)) z :=
            integral_const_mul _ _
        _ = C_H * Cc * gaussDdim (2 * (t - s) + 2 * (w * s)) (0 : Point n) := by
            rw [gaussDdim_pairing_integral _ _ (by linarith) (mul_pos two_pos (mul_pos hw0 hs.1))]
        _ ≤ C_H * Cc * (Real.sqrt (w / 2) ^ n * gaussDdim (w * t) (0 : Point n)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCH hCc0)
            calc gaussDdim (2 * (t - s) + 2 * (w * s)) (0 : Point n)
                ≤ gaussDdim (2 * t) (0 : Point n) :=
                  gaussDdim_zero_antitone (2 * t) _ (by linarith) (by nlinarith [hs.1])
              _ ≤ Real.sqrt (w / 2) ^ n * gaussDdim (w * t) (0 : Point n) :=
                  gaussDdim_le_of_width_le 2 w two_pos hw2 ht (0 : Point n)
        _ = K := by rw [hKdef]; ring
    · -- s = t: the slice integrand vanishes (H(0,0,·) = 0)
      have hzero : (fun z => H (t - s) 0 z * E s z 0) = fun _ => (0 : ℝ) := by
        funext z
        rw [hseq, sub_self, hH0 z, zero_mul]
      rw [hzero, MeasureTheory.integral_zero, norm_zero]
      exact hK0
  -- the outer s-integral pays exactly ONE power of t
  have hval : heatConv H E t 0 0
      = ∫ s in (0 : ℝ)..t, ∫ z, H (t - s) 0 z * E s z 0 := rfl
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const hslice
  rw [← hval] at houter
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos ht] at houter
  exact houter

/-! ### §4. ★ The interface gap + the far subsumption (the shape verdict, pinned). -/

/-- **The inverse-linear probe kernel** — a genuinely nonzero kernel realizing the TRUE column
    shape with `C_E = 1` (window-gated `(r²/s)·G_{ws}`, the leading normal-form term). -/
noncomputable def invtauProbe (w : ℝ) : ℝ → Point n → Point n → ℝ :=
  fun s p _ => if 0 < s ∧ s ≤ 1 then rncRadialSq p / s * gaussDdim (w * s) p else 0

/-- The probe satisfies the inverse-linear column shape with `C_E = 1`. -/
theorem invtauProbe_shape (w : ℝ) :
    ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |invtauProbe w s p 0| ≤ 1 * (rncRadialSq (p - 0) / s * gaussDdim (w * s) (p - 0)
        + (rncRadialSq (p - 0) / s) ^ 2 * gaussDdim (w * s) (p - 0)) := by
  intro s p hs hs1
  simp only [invtauProbe, if_pos (And.intro hs hs1), sub_zero, one_mul]
  rw [abs_of_nonneg (mul_nonneg (div_nonneg (rncRadialSq_nonneg p) hs.le)
    (QIQTH.ResidueBound.gaussDdim_nonneg _ _))]
  have h2 : 0 ≤ (rncRadialSq p / s) ^ 2 * gaussDdim (w * s) p :=
    mul_nonneg (sq_nonneg _) (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  linarith

/-- The probe is genuinely nonzero (at `s = 1`, `p = (1,1)`, `n = 2`). -/
theorem invtauProbe_ne_zero (w : ℝ) (hw : 0 < w) :
    invtauProbe (n := 2) w 1 (fun _ => (1 : ℝ)) 0 ≠ 0 := by
  have hr : rncRadialSq ((fun _ => (1 : ℝ)) : Point 2) = 2 := by
    norm_num [rncRadialSq, Fin.sum_univ_two]
  have hG : 0 < gaussDdim (w * 1) ((fun _ => (1 : ℝ)) : Point 2) :=
    gaussDdim_pos _ (by linarith) _
  simp only [invtauProbe, if_pos (And.intro one_pos (le_refl (1 : ℝ))), hr]
  positivity

/-- **★★ THE INTERFACE GAP — the J4-634 quadratic-coefficient target is the WRONG shape.**
    The inverse-linear probe (which realizes the TRUE near-diagonal column structure of the
    order-0 whitened witness with `C_E = 1`) satisfies the J4-635 quadratic-coefficient bound
        `|E(s,p,0)| ≤ C_E·r(p)²·G_{ws}(p)`
    for NO constant `C_E`: the `1/s` in the true shape is REAL (take `s → 0` at fixed `p ≠ 0`;
    the Gaussian factors cancel exactly, leaving `1/s ≤ C_E`).  Hence
    `white_k1_of_quadratic_coeff`'s antecedent is NOT satisfiable by the true defect structure —
    the k = 1 budget cannot be fed through that interface for the order-0 witness. -/
theorem invtauProbe_not_quadratic_coeff (w : ℝ) (hw : 0 < w) :
    ∀ C_E : ℝ, ¬ (∀ (s : ℝ) (p : Point 2), 0 < s → s ≤ 1 →
      |invtauProbe w s p 0|
        ≤ C_E * (rncRadialSq (p - 0) * gaussDdim (w * s) (p - 0))) := by
  intro C_E hcon
  set D : ℝ := max C_E 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  have hDC : C_E ≤ D := le_max_left _ _
  set s₀ : ℝ := 1 / (D + 2) with hs₀def
  have hs₀ : 0 < s₀ := by positivity
  have hs₁ : s₀ ≤ 1 := by
    rw [hs₀def, div_le_one (by linarith)]
    linarith
  set p₁ : Point 2 := (fun _ => (1 : ℝ)) with hp₁def
  have hr : rncRadialSq p₁ = 2 := by
    norm_num [hp₁def, rncRadialSq, Fin.sum_univ_two]
  have hG : 0 < gaussDdim (w * s₀) p₁ := gaussDdim_pos _ (by positivity) _
  have h := hcon s₀ p₁ hs₀ hs₁
  rw [sub_zero] at h
  simp only [invtauProbe, if_pos (And.intro hs₀ hs₁)] at h
  rw [abs_of_nonneg (mul_nonneg (div_nonneg (rncRadialSq_nonneg p₁) hs₀.le) hG.le), hr] at h
  -- h : 2 / s₀ * G ≤ C_E * (2 * G) with 2/s₀ = 2(D+2); Gaussian cancels: 2(D+2) ≤ 2C_E ≤ 2D — absurd
  have hinv : 2 / s₀ = 2 * (D + 2) := by
    rw [hs₀def]
    field_simp
  rw [hinv] at h
  nlinarith [hG, mul_le_mul_of_nonneg_right hDC (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hG.le)]

/-- **The far/annulus O(1) bound is SUBSUMED by the inverse-linear shape**: on `r(p)² ≥ a²`
    (`a > 0`) and `s ≤ 1`, any `C·G` bound implies the `(C/a²)·(r²/s)·G` bound.  Together with
    §2 this makes the inverse-linear shape the honest GLOBAL column interface for the order-0
    witness (near-diagonal: §2; far: banked `hpkgBound` + this).  NOT `a₁ = R/6`. -/
theorem far_O1_le_invtau (C a s : ℝ) (hC : 0 ≤ C) (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1)
    (p : Point n) (hfar : a ^ 2 ≤ rncRadialSq p) (G : ℝ) (hG : 0 ≤ G) :
    C * G ≤ C / a ^ 2 * (rncRadialSq p / s * G) := by
  have h1 : 1 ≤ rncRadialSq p / (a ^ 2 * s) := by
    rw [le_div_iff₀ (by positivity), one_mul]
    nlinarith
  have key : C * G * 1 ≤ C * G * (rncRadialSq p / (a ^ 2 * s)) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hC hG)
  calc C * G = C * G * 1 := (mul_one _).symm
    _ ≤ C * G * (rncRadialSq p / (a ^ 2 * s)) := key
    _ = C / a ^ 2 * (rncRadialSq p / s * G) := by
        field_simp
        try ring

/-! ### §5. Non-vacuity gates (cp466 discipline). -/

/-- **Gate — the O(t) ceiling FIRES at a genuinely nonzero column and a genuinely nonzero
    Gaussian slice kernel** (`n = 2`, `w = 8`, the banked witness `H`): the ceiling theorem is
    not `∅`-degenerate on either side, and the SAME probe pins the interface gap — the two
    verdict halves (ceiling reachable, budget interface not) hold at ONE witness. -/
theorem white_k1_ceiling_gate :
    K1LinearCeilingW (n := 2) 8
      (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ)) (invtauProbe 8)
    ∧ invtauProbe (n := 2) 8 1 (fun _ => (1 : ℝ)) 0 ≠ 0
    ∧ ∀ C_E : ℝ, ¬ (∀ (s : ℝ) (p : Point 2), 0 < s → s ≤ 1 →
        |invtauProbe 8 s p 0|
          ≤ C_E * (rncRadialSq (p - 0) * gaussDdim (8 * s) (p - 0))) := by
  refine ⟨?_, invtauProbe_ne_zero 8 (by norm_num),
    invtauProbe_not_quadratic_coeff 8 (by norm_num)⟩
  have hW := QIQTH.FrozenK2Sharp.frozenK2Sharp_H_witness (n := 2) (by norm_num)
  exact k1CeilingW_of_invtau_shape 8 (by norm_num) (invtauProbe 8) 1 zero_le_one
    (invtauProbe_shape 8) (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ)) 1
    zero_le_one (fun a ζ ha => hW.1 a ζ ha) (fun ζ => hW.2.1 ζ)

/-- **Gate — the raw chart bound fires at genuinely curved fat data** (`n = 2`, `κ = −1`,
    `K = B̄(0,2)`): the ∃-package of §2 is inhabited with a genuinely positive gate radius. -/
theorem whiteChart_invtau_witness_gate :
    ∃ r₀ > (0 : ℝ), ∃ cA cB : ℝ, 0 ≤ cA ∧ 0 ≤ cB
      ∧ ∀ q ∈ Metric.closedBall (0 : Point 2) 2, ∀ τ : ℝ, 0 < τ →
        ∀ x : Point 2, ‖x‖ < r₀ →
        |heatOp (fun w => whitePullbackMetric (-1 : ℝ) (by norm_num)
            (isCompact_closedBall (0 : Point 2) 2) q w)
          (fun w => whitePullbackMetricInv (-1 : ℝ) (by norm_num)
            (isCompact_closedBall (0 : Point 2) 2) q w)
          (fun t x y => flatPhaseModel t x y) τ x (0 : Point 2)|
        ≤ cA * (rncRadialSq x / τ * gaussDdim τ x)
          + cB * ((rncRadialSq x / τ) ^ 2 * gaussDdim τ x) :=
  whiteChart_heatOp_invtau_bound (-1 : ℝ) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2)

end QIQTH.WhiteK1

-- std-3 verification (chk): READ these outputs — no sorryAx, no extra axioms.
#print axioms QIQTH.WhiteK1.normalform_abs_bound_raw
#print axioms QIQTH.WhiteK1.whiteChart_heatOp_invtau_bound
#print axioms QIQTH.WhiteK1.whiteChart_invtau_implies_offdiag
#print axioms QIQTH.WhiteK1.k1CeilingW_of_invtau_shape
#print axioms QIQTH.WhiteK1.invtauProbe_shape
#print axioms QIQTH.WhiteK1.invtauProbe_ne_zero
#print axioms QIQTH.WhiteK1.invtauProbe_not_quadratic_coeff
#print axioms QIQTH.WhiteK1.far_O1_le_invtau
#print axioms QIQTH.WhiteK1.white_k1_ceiling_gate
#print axioms QIQTH.WhiteK1.whiteChart_invtau_witness_gate
