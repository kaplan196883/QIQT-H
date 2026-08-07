/-
  AffineRawResidual — J4-369: the RAW GRADED (pre-absorption) residual slice for the concrete `N = 1`
  van-Vleck gated witness (Sol consult #15, brick 2 — the heavy one).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  RESIDUAL-DECOMPOSITION brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It extracts
  the RAW, PRE-WIDTH-ABSORPTION graded estimate for the `N = 0` parametrix residual (and, via the affine
  N=1 fold, the shape feeding `HgateAffineRepair.AffineGateBound`).  The point (Sol #15 A1 verdict) is
  that the banked capstone `CoeffU1Fix.gatedWitnessN1_hEboundW_le_lin` outputs at WIDTH 2
  (`baseKernelW 2 …`), which can NEVER be narrowed to `4/3` by polynomial factors; the honest narrow
  route must be re-derived from the raw residual terms at the PRE-ABSORPTION width (here `w₀ = 1`, the
  literal Gaussian width `gaussDdim τ` produced by `parametrixResidual_N0_O1_isolated_C2`).  Everything
  here stays at width `≤ 4/3` and reuses ONLY the P-independent pointwise machinery.  NO `sorry` (header
  prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to (or
  trivially yielding) the conclusion, NO existing file edited, nothing committed.  `a₁ = R/6` stays
  CONDITIONAL on the whole convergence / geometric-wiring stack AND on the surviving LABELLED inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE RAW `N = 0` RESIDUAL DECOMPOSITION (banked `parametrixResidual_N0_O1_isolated_C2`).  For
  `τ > 0` and `w₀ = foldedCoeff Θ u 0` of class `C²` at `v`,
      `parametrixResidualN 0 g gi Θ u τ v`
        =  (1/τ)·G_τ·(totalRadialO1_coeff g gi Θ u v)                                     -- T1
         + (1/τ²)·G_τ·((-1/4)·Σᵢⱼ(g̃⁻¹−δ)ᵢⱼ vᵢvⱼ)·w₀(v)                                   -- T2
         − G_τ·(Δ_{g̃} w₀)(v)                                                              -- T3
  ALL THREE terms carry the LITERAL Gaussian width `G_τ = gaussDdim τ v` (pre-absorption width `w₀ = 1`).

  ## THE PER-TERM GRADE (with `x := rncRadialSq v / τ`).
  •  T1 with an `O(r²)` coefficient bound `|coeff| ≤ Cc·r²` gives `|T1| ≤ Cc·x·G_τ`         — monomial `x`.
  •  T2 with `|g̃⁻¹−δ| ≤ Md·r²` and `|w₀| ≤ W` gives `|T2| ≤ (n²·Md·W/4)·x²·G_τ`            — monomial `x²`.
  •  T3 with `|Δ w₀| ≤ L` gives `|T3| ≤ L·G_τ`                                              — monomial `1`.
  Folded: `|R₀| ≤ (L + Cc + n²MdW/4)·((x²+x+1)·G_τ)` — the raw QUADRATIC grade at width `1`.

  ## DELIVERABLES.
  •  `rawResidualN0_graded_quadPoly_width1` — the raw `N = 0` graded quadratic bound at width `1`
     (`w₀ = 1 < 4/3`), from the three per-term graded bounds.  THE promoted residual slice.
  •  `rawResidualN0_graded_quadPoly_width43` — the NORMALIZED width comparison `1 → 4/3` (Sol brick 3):
     `G_τ ≤ √(4/3)ⁿ·G_{(4/3)τ}` via `gaussDdim_le_gaussDdim_chart` (never a bare `G_{w₀} ≤ G_{4/3}`),
     folding the width-`1` quadratic bound to the width-`4/3` quadratic bound in the SAME frame.
  •  `rawResidualN1_affine_graded_quadPoly_width1` — the affine `N = 1` graded quadratic bound at width
     `1` with a GENUINE `P₁ ≠ 0` (`R₁ = R₀[u] + H₀[u'] + τ·R₀[u']`; the `τ·R₀[u']` branch, via an `O(r)`
     shifted coefficient, deposits the `√x` monomial folded by `√τ ≤ 1+τ`).  This is the raw graded
     estimate the full `AffineGateBound` derivation consumes (before chart transfer + transport wiring).

  ## HONESTY / SATISFIABILITY.  Every coefficient hypothesis (`hcoeff`/`hcoeffLin`/`hdev`/`hwbd`/`hlap`)
  is a POINTWISE instance of a banked UNIFORM bound (`hCoeffU0_vanVleck`, `uniformCoeffLinear_bound`,
  `uniformFlowPullbackMetricInv_dev_uniform`, sup-on-compact, `uniformFlowLaplaceBeltrami_w0_near_uniform`)
  — all satisfiable for the concrete van-Vleck witness; none equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WidthMarginEngine
import QIQTH.ResidualN0FiniteReg
import QIQTH.ResidualN1GaussianBound

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.ResidueBound QIQTH.HeatResidualBound QIQTH.HeatParametrixAnsatz
open scoped BigOperators

namespace QIQTH.AffineRawResidual

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (B) — the raw `N = 0` graded quadratic bound at width `1`.
    ############################################################################### -/

/-- **★ (B) — `rawResidualN0_graded_quadPoly_width1`.**  THE PROMOTED RAW RESIDUAL SLICE.  From the
    banked three-term identity `parametrixResidual_N0_O1_isolated_C2` and the per-term coefficient
    carries (`O(r²)` coefficient `hcoeff`, deviation `hdev`, amplitude `hwbd`, Laplacian `hlap`), the
    `N = 0` residual is bounded by the RAW QUADRATIC grade at the PRE-ABSORPTION width `1`:
        `|parametrixResidualN 0 g gi Θ u τ v|
           ≤ (L + Cc + n²·Md·W/4)·(((r²/τ)² + r²/τ + 1)·gaussDdim τ v)`.
    T1 ↦ `Cc·x`, T2 ↦ `(n²MdW/4)·x²`, T3 ↦ `L`, with `x = rncRadialSq v / τ`.  All carries are pointwise
    instances of banked uniform bounds (satisfiable).  Width `1 < 4/3`, so this is REUSABLE for the
    narrow route.  NOT `a₁ = R/6`. -/
theorem rawResidualN0_graded_quadPoly_width1
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v)
    (Cc Md W L : ℝ) (hCc : 0 ≤ Cc) (hMd : 0 ≤ Md) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hcoeff : |totalRadialO1_coeff g gi Θ u v| ≤ Cc * rncRadialSq v)
    (hdev : ∀ i j : Fin n, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ Md * rncRadialSq v)
    (hwbd : |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L) :
    |parametrixResidualN 0 g gi Θ u τ v|
      ≤ (L + Cc + (1 / 4) * (n : ℝ) ^ 2 * Md * W)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
  rw [parametrixResidual_N0_O1_isolated_C2 g gi Θ u τ hτ v hw0]
  set G : ℝ := gaussDdim τ v with hGdef
  have hG0 : 0 ≤ G := gaussDdim_nonneg τ v
  set r2 : ℝ := rncRadialSq v with hr2def
  have hr20 : 0 ≤ r2 := rncRadialSq_nonneg v
  have hx0 : 0 ≤ r2 / τ := div_nonneg hr20 hτ.le
  have hq20 : 0 ≤ (1 / 4) * (n : ℝ) ^ 2 * Md * W := by positivity
  set S : ℝ := ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j) with hSdef
  set w0 : ℝ := foldedCoeff Θ u 0 v with hw0valdef
  set Lap : ℝ := laplaceBeltrami g gi (foldedCoeff Θ u 0) v with hLapdef
  -- (T1) coefficient branch: monomial `x`.
  have hT1 : |(1 / τ) * G * totalRadialO1_coeff g gi Θ u v| ≤ Cc * (r2 / τ) * G := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hG0)]
    calc (1 / τ) * G * |totalRadialO1_coeff g gi Θ u v|
        ≤ (1 / τ) * G * (Cc * r2) :=
          mul_le_mul_of_nonneg_left hcoeff (mul_nonneg (one_div_nonneg.mpr hτ.le) hG0)
      _ = Cc * (r2 / τ) * G := by rw [hr2def]; ring
  -- (T2) deviation-quadratic branch: monomial `x²`.
  have hvv : ∀ i j : Fin n, |v i * v j| ≤ r2 := by
    intro i j
    rw [abs_mul, hr2def, ← rncRadial_sq, pow_two]
    exact mul_le_mul (abs_coord_le_rncRadial v i) (abs_coord_le_rncRadial v j)
      (abs_nonneg _) (rncRadial_nonneg v)
  have hS : |S| ≤ (n : ℝ) ^ 2 * Md * r2 ^ 2 := by
    rw [hSdef]
    calc |∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)|
        ≤ ∑ i, ∑ j, |(gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (Md * r2) * r2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hdev i j) (hvv i j) (abs_nonneg _) (mul_nonneg hMd hr20)
      _ = (n : ℝ) ^ 2 * Md * r2 ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hpf : (0 : ℝ) ≤ (1 / τ ^ 2) * G * (1 / 4) :=
    mul_nonneg (mul_nonneg (one_div_nonneg.mpr (pow_pos hτ 2).le) hG0) (by norm_num)
  have hT2 : |(1 / τ ^ 2) * G * ((-1 / 4) * S) * w0|
      ≤ (1 / 4) * (n : ℝ) ^ 2 * Md * W * (r2 / τ) ^ 2 * G := by
    have hrw : |(1 / τ ^ 2) * G * ((-1 / 4) * S) * w0|
        = ((1 / τ ^ 2) * G * (1 / 4)) * (|S| * |w0|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (one_div_nonneg.mpr (pow_pos hτ 2).le), abs_of_nonneg hG0,
          show |(-1 / 4 : ℝ)| = 1 / 4 from by norm_num]
      ring
    rw [hrw]
    calc ((1 / τ ^ 2) * G * (1 / 4)) * (|S| * |w0|)
        ≤ ((1 / τ ^ 2) * G * (1 / 4)) * (((n : ℝ) ^ 2 * Md * r2 ^ 2) * W) := by
          apply mul_le_mul_of_nonneg_left _ hpf
          exact mul_le_mul hS hwbd (abs_nonneg _)
            (mul_nonneg (mul_nonneg (by positivity) hMd) (sq_nonneg r2))
      _ = (1 / 4) * (n : ℝ) ^ 2 * Md * W * (r2 / τ) ^ 2 * G := by rw [hr2def]; ring
  -- (T3) Laplacian branch: monomial `1`.
  have hT3 : |G * Lap| ≤ L * G := by
    rw [abs_mul, abs_of_nonneg hG0]
    calc G * |Lap| ≤ G * L := mul_le_mul_of_nonneg_left hlap hG0
      _ = L * G := by ring
  -- assemble `|T1 + T2 - T3| ≤ |T1| + |T2| + |T3|` then fold to the quadratic grade.
  have hscalar : Cc * (r2 / τ) + (1 / 4) * (n : ℝ) ^ 2 * Md * W * (r2 / τ) ^ 2 + L
      ≤ (L + Cc + (1 / 4) * (n : ℝ) ^ 2 * Md * W)
          * ((r2 / τ) ^ 2 + r2 / τ + 1) := by
    nlinarith [mul_nonneg hL hx0, mul_nonneg hL (mul_nonneg hx0 hx0),
      mul_nonneg hCc (mul_nonneg hx0 hx0), mul_nonneg hq20 hx0, hx0, hL, hCc, hq20]
  calc |(1 / τ) * G * totalRadialO1_coeff g gi Θ u v
          + (1 / τ ^ 2) * G * ((-1 / 4) * S) * w0 - G * Lap|
      ≤ |(1 / τ) * G * totalRadialO1_coeff g gi Θ u v
          + (1 / τ ^ 2) * G * ((-1 / 4) * S) * w0| + |G * Lap| := by
        have h := abs_add_le ((1 / τ) * G * totalRadialO1_coeff g gi Θ u v
          + (1 / τ ^ 2) * G * ((-1 / 4) * S) * w0) (-(G * Lap))
        rwa [← sub_eq_add_neg, abs_neg] at h
    _ ≤ (|(1 / τ) * G * totalRadialO1_coeff g gi Θ u v|
          + |(1 / τ ^ 2) * G * ((-1 / 4) * S) * w0|) + |G * Lap| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (Cc * (r2 / τ) * G + (1 / 4) * (n : ℝ) ^ 2 * Md * W * (r2 / τ) ^ 2 * G) + L * G :=
        add_le_add (add_le_add hT1 hT2) hT3
    _ = (Cc * (r2 / τ) + (1 / 4) * (n : ℝ) ^ 2 * Md * W * (r2 / τ) ^ 2 + L) * G := by ring
    _ ≤ ((L + Cc + (1 / 4) * (n : ℝ) ^ 2 * Md * W)
          * ((r2 / τ) ^ 2 + r2 / τ + 1)) * G := mul_le_mul_of_nonneg_right hscalar hG0
    _ = (L + Cc + (1 / 4) * (n : ℝ) ^ 2 * Md * W)
          * (((r2 / τ) ^ 2 + r2 / τ + 1) * G) := by ring

/-! ###############################################################################
    ### (S3) — the normalized width `1 → 4/3` comparison (Sol brick 3, `N = 0`).
    ############################################################################### -/

/-- **★ (S3) — `rawResidualN0_graded_quadPoly_width43`.**  THE NORMALIZED WIDTH COMPARISON `1 → 4/3`.
    Folds the raw width-`1` quadratic bound (B) to the width-`4/3` quadratic bound in the SAME frame,
    via the P-INDEPENDENT normalized comparison `gaussDdim τ v ≤ √(4/3)ⁿ·gaussDdim ((4/3)·τ) v`
    (`gaussDdim_le_gaussDdim_chart`, `c = 1 < d = 4/3`, `w = v`) — NEVER a bare `G_{1} ≤ G_{4/3}`.  The
    normalizing constant `√(4/3)ⁿ` is absorbed into the outer factor.  This is the `4/3`-target inner
    shape of `HgateAffineRepair.AffineGateBound` (with `P₁ = 0` for the `N = 0` case).  NOT `a₁ = R/6`. -/
theorem rawResidualN0_graded_quadPoly_width43
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v)
    (Cc Md W L : ℝ) (hCc : 0 ≤ Cc) (hMd : 0 ≤ Md) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hcoeff : |totalRadialO1_coeff g gi Θ u v| ≤ Cc * rncRadialSq v)
    (hdev : ∀ i j : Fin n, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ Md * rncRadialSq v)
    (hwbd : |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L) :
    |parametrixResidualN 0 g gi Θ u τ v|
      ≤ (Real.sqrt (4 / 3) ^ n * (L + Cc + (1 / 4) * (n : ℝ) ^ 2 * Md * W))
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (4 / 3 * τ) v) := by
  have hbase := rawResidualN0_graded_quadPoly_width1 g gi Θ u hτ v hw0 Cc Md W L
    hCc hMd hW hL hcoeff hdev hwbd hlap
  set Kq : ℝ := L + Cc + (1 / 4) * (n : ℝ) ^ 2 * Md * W with hKqdef
  have hKq0 : 0 ≤ Kq := by rw [hKqdef]; positivity
  have hxr : 0 ≤ rncRadialSq v / τ := div_nonneg (rncRadialSq_nonneg v) hτ.le
  have hpoly0 : 0 ≤ (rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1 :=
    add_nonneg (add_nonneg (sq_nonneg _) hxr) zero_le_one
  have hwidth : gaussDdim τ v ≤ Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) v := by
    have h := gaussDdim_le_gaussDdim_chart (n := n) (c := 1) (d := 4 / 3)
      (by norm_num) (by norm_num) hτ (v := v) (w := v)
      (by have := rncRadialSq_nonneg v; linarith)
    simpa using h
  calc |parametrixResidualN 0 g gi Θ u τ v|
      ≤ Kq * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := hbase
    _ ≤ Kq * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1)
          * (Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) v)) := by
        apply mul_le_mul_of_nonneg_left _ hKq0
        exact mul_le_mul_of_nonneg_left hwidth hpoly0
    _ = (Real.sqrt (4 / 3) ^ n * Kq)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (4 / 3 * τ) v) := by
        ring

/-! ###############################################################################
    ### (C-helper) — the `τ·R₀[u']` branch with an `O(r)` coefficient (the `√x` monomial).
    ############################################################################### -/

/-- **★ (C-helper) — `tauResidualN0_Or_graded_quadPoly_width1`.**  The `τ·R₀` branch bound for an
    `O(r)` (LINEAR, shifted-profile) coefficient.  T1 now carries `|coeff| ≤ Cc·r`, so `τ·|T1|` deposits
    the `√x` monomial `Cc·(1+τ)·√x·G_τ` (via `rncRadial v = √x·√τ` and `√τ ≤ 1+τ`); `√x ≤ x²+x+1`,
    `x² ≤ x²+x+1`, `1 ≤ x²+x+1` fold every monomial into the quadratic grade.  Result is AFFINE in `τ`
    with a GENUINE `τ`-linear part:
        `τ·|parametrixResidualN 0 g gi Θ u τ v|
           ≤ (Cc + (Cc + n²MdW/4 + L)·τ)·((x²+x+1)·gaussDdim τ v)`,   `x = rncRadialSq v/τ`.
    This is the `E₁ ≠ 0` source of the affine repair.  NOT `a₁ = R/6`. -/
theorem tauResidualN0_Or_graded_quadPoly_width1
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v)
    (Cc Md W L : ℝ) (hCc : 0 ≤ Cc) (hMd : 0 ≤ Md) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hcoeff : |totalRadialO1_coeff g gi Θ u v| ≤ Cc * rncRadial v)
    (hdev : ∀ i j : Fin n, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ Md * rncRadialSq v)
    (hwbd : |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L) :
    τ * |parametrixResidualN 0 g gi Θ u τ v|
      ≤ (Cc + (Cc + (1 / 4) * (n : ℝ) ^ 2 * Md * W + L) * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
  have hτ0 : τ ≠ 0 := hτ.ne'
  rw [parametrixResidual_N0_O1_isolated_C2 g gi Θ u τ hτ v hw0]
  set G : ℝ := gaussDdim τ v with hGdef
  have hG0 : 0 ≤ G := gaussDdim_nonneg τ v
  set r2 : ℝ := rncRadialSq v with hr2def
  have hr20 : 0 ≤ r2 := rncRadialSq_nonneg v
  have hx0 : 0 ≤ r2 / τ := div_nonneg hr20 hτ.le
  set Q : ℝ := (r2 / τ) ^ 2 + r2 / τ + 1 with hQdef
  have hQ1 : (1 : ℝ) ≤ Q := by rw [hQdef]; nlinarith [sq_nonneg (r2 / τ), hx0]
  have hx2Q : (r2 / τ) ^ 2 ≤ Q := by rw [hQdef]; nlinarith [sq_nonneg (r2 / τ), hx0]
  set S : ℝ := ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j) with hSdef
  set w0 : ℝ := foldedCoeff Θ u 0 v with hw0valdef
  set Lap : ℝ := laplaceBeltrami g gi (foldedCoeff Θ u 0) v with hLapdef
  -- reusable scalar facts.
  have hττ : τ * (1 / τ) = 1 := by rw [mul_one_div, div_self hτ0]
  have hsqrtτ : Real.sqrt τ ≤ 1 + τ := by
    have h := Real.sqrt_le_sqrt (show τ ≤ (1 + τ) ^ 2 by nlinarith [hτ.le])
    rwa [Real.sqrt_sq (by linarith [hτ.le] : (0 : ℝ) ≤ 1 + τ)] at h
  have hsx_le : Real.sqrt (r2 / τ) ≤ Q := by
    have h1x : (0 : ℝ) ≤ 1 + r2 / τ := by linarith [hx0]
    have h := Real.sqrt_le_sqrt (show r2 / τ ≤ (1 + r2 / τ) ^ 2 by nlinarith [hx0])
    rw [Real.sqrt_sq h1x] at h
    rw [hQdef]; nlinarith [h, sq_nonneg (r2 / τ), hx0]
  have hr_sx : rncRadial v = Real.sqrt (r2 / τ) * Real.sqrt τ := by
    have heq : Real.sqrt (r2 / τ) * Real.sqrt τ = Real.sqrt r2 := by
      rw [← Real.sqrt_mul (div_nonneg hr20 hτ.le) τ]; congr 1; field_simp
    rw [heq]; simp only [rncRadial, hr2def]
  -- (T1') `O(r)` branch: the `√x` monomial folded into `Q`.
  have hT1' : τ * |(1 / τ) * G * totalRadialO1_coeff g gi Θ u v| ≤ Cc * (1 + τ) * Q * G := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hG0)]
    calc τ * ((1 / τ) * G * |totalRadialO1_coeff g gi Θ u v|)
        = G * |totalRadialO1_coeff g gi Θ u v| := by
          rw [show τ * ((1 / τ) * G * |totalRadialO1_coeff g gi Θ u v|)
            = (τ * (1 / τ)) * (G * |totalRadialO1_coeff g gi Θ u v|) from by ring, hττ, one_mul]
      _ ≤ G * (Cc * rncRadial v) := mul_le_mul_of_nonneg_left hcoeff hG0
      _ = Cc * rncRadial v * G := by ring
      _ = Cc * (Real.sqrt (r2 / τ) * Real.sqrt τ) * G := by rw [hr_sx]
      _ ≤ Cc * (Real.sqrt (r2 / τ) * (1 + τ)) * G := by
          apply mul_le_mul_of_nonneg_right _ hG0
          apply mul_le_mul_of_nonneg_left _ hCc
          exact mul_le_mul_of_nonneg_left hsqrtτ (Real.sqrt_nonneg _)
      _ ≤ Cc * (Q * (1 + τ)) * G := by
          apply mul_le_mul_of_nonneg_right _ hG0
          apply mul_le_mul_of_nonneg_left _ hCc
          exact mul_le_mul_of_nonneg_right hsx_le (by linarith [hτ.le])
      _ = Cc * (1 + τ) * Q * G := by ring
  -- (T2') deviation-quadratic branch × τ: monomial `x²`.
  have hvv : ∀ i j : Fin n, |v i * v j| ≤ r2 := by
    intro i j
    rw [abs_mul, hr2def, ← rncRadial_sq, pow_two]
    exact mul_le_mul (abs_coord_le_rncRadial v i) (abs_coord_le_rncRadial v j)
      (abs_nonneg _) (rncRadial_nonneg v)
  have hS : |S| ≤ (n : ℝ) ^ 2 * Md * r2 ^ 2 := by
    rw [hSdef]
    calc |∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)|
        ≤ ∑ i, ∑ j, |(gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (Md * r2) * r2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hdev i j) (hvv i j) (abs_nonneg _) (mul_nonneg hMd hr20)
      _ = (n : ℝ) ^ 2 * Md * r2 ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hpf : (0 : ℝ) ≤ (1 / τ ^ 2) * G * (1 / 4) :=
    mul_nonneg (mul_nonneg (one_div_nonneg.mpr (pow_pos hτ 2).le) hG0) (by norm_num)
  have hq2τ : (0 : ℝ) ≤ (1 / 4) * (n : ℝ) ^ 2 * Md * W * τ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hMd) hW) hτ.le
  have hT2' : τ * |(1 / τ ^ 2) * G * ((-1 / 4) * S) * w0|
      ≤ ((1 / 4) * (n : ℝ) ^ 2 * Md * W * τ) * Q * G := by
    have hrw : |(1 / τ ^ 2) * G * ((-1 / 4) * S) * w0|
        = ((1 / τ ^ 2) * G * (1 / 4)) * (|S| * |w0|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (one_div_nonneg.mpr (pow_pos hτ 2).le), abs_of_nonneg hG0,
          show |(-1 / 4 : ℝ)| = 1 / 4 from by norm_num]
      ring
    rw [hrw]
    have hbase2 : ((1 / τ ^ 2) * G * (1 / 4)) * (|S| * |w0|)
        ≤ (1 / 4) * (n : ℝ) ^ 2 * Md * W * (r2 / τ) ^ 2 * G := by
      calc ((1 / τ ^ 2) * G * (1 / 4)) * (|S| * |w0|)
          ≤ ((1 / τ ^ 2) * G * (1 / 4)) * (((n : ℝ) ^ 2 * Md * r2 ^ 2) * W) := by
            apply mul_le_mul_of_nonneg_left _ hpf
            exact mul_le_mul hS hwbd (abs_nonneg _)
              (mul_nonneg (mul_nonneg (by positivity) hMd) (sq_nonneg r2))
        _ = (1 / 4) * (n : ℝ) ^ 2 * Md * W * (r2 / τ) ^ 2 * G := by rw [hr2def]; ring
    calc τ * (((1 / τ ^ 2) * G * (1 / 4)) * (|S| * |w0|))
        ≤ τ * ((1 / 4) * (n : ℝ) ^ 2 * Md * W * (r2 / τ) ^ 2 * G) :=
          mul_le_mul_of_nonneg_left hbase2 hτ.le
      _ = ((1 / 4) * (n : ℝ) ^ 2 * Md * W * τ) * ((r2 / τ) ^ 2 * G) := by ring
      _ ≤ ((1 / 4) * (n : ℝ) ^ 2 * Md * W * τ) * (Q * G) := by
          apply mul_le_mul_of_nonneg_left _ hq2τ
          exact mul_le_mul_of_nonneg_right hx2Q hG0
      _ = ((1 / 4) * (n : ℝ) ^ 2 * Md * W * τ) * Q * G := by ring
  -- (T3') Laplacian branch × τ: monomial `1`.
  have hT3' : τ * |G * Lap| ≤ (L * τ) * Q * G := by
    rw [abs_mul, abs_of_nonneg hG0]
    calc τ * (G * |Lap|)
        ≤ τ * (G * L) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlap hG0) hτ.le
      _ = (L * τ) * (1 * G) := by ring
      _ ≤ (L * τ) * (Q * G) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL hτ.le)
          exact mul_le_mul_of_nonneg_right hQ1 hG0
      _ = (L * τ) * Q * G := by ring
  -- assemble `τ·|T1'+T2'−T3'| ≤ τ|T1'| + τ|T2'| + τ|T3'|`.
  have htri : |(1 / τ) * G * totalRadialO1_coeff g gi Θ u v
        + (1 / τ ^ 2) * G * ((-1 / 4) * S) * w0 - G * Lap|
      ≤ |(1 / τ) * G * totalRadialO1_coeff g gi Θ u v|
        + |(1 / τ ^ 2) * G * ((-1 / 4) * S) * w0| + |G * Lap| := by
    calc |(1 / τ) * G * totalRadialO1_coeff g gi Θ u v
            + (1 / τ ^ 2) * G * ((-1 / 4) * S) * w0 - G * Lap|
        ≤ |(1 / τ) * G * totalRadialO1_coeff g gi Θ u v
            + (1 / τ ^ 2) * G * ((-1 / 4) * S) * w0| + |G * Lap| := by
          have h := abs_add_le ((1 / τ) * G * totalRadialO1_coeff g gi Θ u v
            + (1 / τ ^ 2) * G * ((-1 / 4) * S) * w0) (-(G * Lap))
          rwa [← sub_eq_add_neg, abs_neg] at h
      _ ≤ (|(1 / τ) * G * totalRadialO1_coeff g gi Θ u v|
            + |(1 / τ ^ 2) * G * ((-1 / 4) * S) * w0|) + |G * Lap| :=
          add_le_add (abs_add_le _ _) le_rfl
  calc τ * |(1 / τ) * G * totalRadialO1_coeff g gi Θ u v
          + (1 / τ ^ 2) * G * ((-1 / 4) * S) * w0 - G * Lap|
      ≤ τ * (|(1 / τ) * G * totalRadialO1_coeff g gi Θ u v|
          + |(1 / τ ^ 2) * G * ((-1 / 4) * S) * w0| + |G * Lap|) :=
        mul_le_mul_of_nonneg_left htri hτ.le
    _ = τ * |(1 / τ) * G * totalRadialO1_coeff g gi Θ u v|
          + τ * |(1 / τ ^ 2) * G * ((-1 / 4) * S) * w0| + τ * |G * Lap| := by ring
    _ ≤ Cc * (1 + τ) * Q * G
          + ((1 / 4) * (n : ℝ) ^ 2 * Md * W * τ) * Q * G + (L * τ) * Q * G :=
        add_le_add (add_le_add hT1' hT2') hT3'
    _ = (Cc + (Cc + (1 / 4) * (n : ℝ) ^ 2 * Md * W + L) * τ) * (Q * G) := by ring

/-! ###############################################################################
    ### (C) — the affine `N = 1` graded quadratic bound at width `1`.
    ############################################################################### -/

/-- **★★ (C) — `rawResidualN1_affine_graded_quadPoly_width1`.**  THE RAW AFFINE GRADED ESTIMATE at the
    pre-absorption width `1`.  Via the banked `N = 1` split `R₁ = R₀[u] + H₀[u'] + τ·R₀[u']`
    (`parametrixResidual_one_split`): `R₀[u]` by the width-`1` quadratic bound (B); `H₀[u'] = G_τ·w₁`
    by the amplitude carry; `τ·R₀[u']` by the `O(r)` helper (`√x` monomial).  Summed into the honest
    AFFINE quadratic shape with a GENUINE `P₁ ≠ 0`:
        `∃ P₀ P₁ ≥ 0, |parametrixResidualN 1 g gi Θ u τ v|
           ≤ (P₀ + P₁·τ)·((x²+x+1)·gaussDdim τ v)`,   `x = rncRadialSq v/τ`.
    This is EXACTLY the inner shape of `HgateAffineRepair.AffineGateBound` at width `w₀ = 1`; the
    remaining bricks to the full `AffineGateBound` are the chart transfer `1 → 4/3` (as in (S3)) plus the
    transport / cutoff-annulus wiring `heatOp (gatedKernel …) = R₁∘chart`.  The `u`-profile carries are
    `O(r²)`; the `u'`-profile carries are `O(r)` (satisfiable via `uniformCoeffLinear_bound`).  NOT
    `a₁ = R/6`. -/
theorem rawResidualN1_affine_graded_quadPoly_width1
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (v : Point n)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (Md : ℝ) (hMd : 0 ≤ Md)
    (hdev : ∀ i j : Fin n, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ Md * rncRadialSq v)
    -- profile `u` (`O(r²)`) carries:
    (Cc0 W0 L0 : ℝ) (hCc0 : 0 ≤ Cc0) (hW0 : 0 ≤ W0) (hL0 : 0 ≤ L0)
    (hcoeff0 : |totalRadialO1_coeff g gi Θ u v| ≤ Cc0 * rncRadialSq v)
    (hw0bd : |foldedCoeff Θ u 0 v| ≤ W0)
    (hlap0 : |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L0)
    -- shifted profile `u' = fun j => u (j+1)` (`O(r)`) carries:
    (Cc1 W1 L1 : ℝ) (hCc1 : 0 ≤ Cc1) (hW1 : 0 ≤ W1) (hL1 : 0 ≤ L1)
    (hcoeff1 : |totalRadialO1_coeff g gi Θ (fun j => u (j + 1)) v| ≤ Cc1 * rncRadial v)
    (hw1bd : |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W1)
    (hlap1 : |laplaceBeltrami g gi (foldedCoeff Θ (fun j => u (j + 1)) 0) v| ≤ L1) :
    ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
      |parametrixResidualN 1 g gi Θ u τ v|
        ≤ (P₀ + P₁ * τ)
            * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
  have hcd0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := (hw 0).contDiffAt.of_le le_top
  have hcd1 : ContDiffAt ℝ 2 (foldedCoeff Θ (fun j => u (j + 1)) 0) v := by
    rw [foldedCoeff_shift]; exact (hw 1).contDiffAt.of_le le_top
  have hq0 : (0 : ℝ) ≤ (1 / 4) * (n : ℝ) ^ 2 * Md * W0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hMd) hW0
  have hq1 : (0 : ℝ) ≤ (1 / 4) * (n : ℝ) ^ 2 * Md * W1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hMd) hW1
  -- the three per-piece width-`1` quadratic bounds.
  have hA := rawResidualN0_graded_quadPoly_width1 g gi Θ u hτ v hcd0 Cc0 Md W0 L0
    hCc0 hMd hW0 hL0 hcoeff0 hdev hw0bd hlap0
  have hmideq : heatParametrix 0 Θ (fun j => u (j + 1)) τ v
      = gaussDdim τ v * foldedCoeff Θ (fun j => u (j + 1)) 0 v := by
    rw [heatParametrix_folded, Finset.sum_range_one, pow_zero, mul_one]
  have hq1poly : (1 : ℝ) ≤ (rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1 := by
    nlinarith [sq_nonneg (rncRadialSq v / τ), div_nonneg (rncRadialSq_nonneg v) hτ.le]
  have hB : |heatParametrix 0 Θ (fun j => u (j + 1)) τ v|
      ≤ W1 * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
    rw [hmideq, abs_mul, abs_of_nonneg (gaussDdim_nonneg τ v)]
    calc gaussDdim τ v * |foldedCoeff Θ (fun j => u (j + 1)) 0 v|
        ≤ gaussDdim τ v * W1 := mul_le_mul_of_nonneg_left hw1bd (gaussDdim_nonneg τ v)
      _ = W1 * (1 * gaussDdim τ v) := by ring
      _ ≤ W1 * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
          apply mul_le_mul_of_nonneg_left _ hW1
          exact mul_le_mul_of_nonneg_right hq1poly (gaussDdim_nonneg τ v)
  have hC : |τ * parametrixResidualN 0 g gi Θ (fun j => u (j + 1)) τ v|
      ≤ (Cc1 + (Cc1 + (1 / 4) * (n : ℝ) ^ 2 * Md * W1 + L1) * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
    rw [abs_mul, abs_of_pos hτ]
    exact tauResidualN0_Or_graded_quadPoly_width1 g gi Θ (fun j => u (j + 1)) hτ v hcd1
      Cc1 Md W1 L1 hCc1 hMd hW1 hL1 hcoeff1 hdev hw1bd hlap1
  refine ⟨(L0 + Cc0 + (1 / 4) * (n : ℝ) ^ 2 * Md * W0) + W1 + Cc1,
    Cc1 + (1 / 4) * (n : ℝ) ^ 2 * Md * W1 + L1,
    add_nonneg (add_nonneg (add_nonneg (add_nonneg hL0 hCc0) hq0) hW1) hCc1,
    add_nonneg (add_nonneg hCc1 hq1) hL1, ?_⟩
  rw [parametrixResidual_one_split g gi Θ u τ hτ v hw]
  calc |parametrixResidualN 0 g gi Θ u τ v
          + heatParametrix 0 Θ (fun j => u (j + 1)) τ v
          + τ * parametrixResidualN 0 g gi Θ (fun j => u (j + 1)) τ v|
      ≤ |parametrixResidualN 0 g gi Θ u τ v
          + heatParametrix 0 Θ (fun j => u (j + 1)) τ v|
          + |τ * parametrixResidualN 0 g gi Θ (fun j => u (j + 1)) τ v| :=
        abs_add_le _ _
    _ ≤ (|parametrixResidualN 0 g gi Θ u τ v|
          + |heatParametrix 0 Θ (fun j => u (j + 1)) τ v|)
          + |τ * parametrixResidualN 0 g gi Θ (fun j => u (j + 1)) τ v| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((L0 + Cc0 + (1 / 4) * (n : ℝ) ^ 2 * Md * W0)
              * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v)
            + W1 * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v))
          + (Cc1 + (Cc1 + (1 / 4) * (n : ℝ) ^ 2 * Md * W1 + L1) * τ)
              * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) :=
        add_le_add (add_le_add hA hB) hC
    _ = ((L0 + Cc0 + (1 / 4) * (n : ℝ) ^ 2 * Md * W0) + W1 + Cc1
            + (Cc1 + (1 / 4) * (n : ℝ) ^ 2 * Md * W1 + L1) * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by ring

end QIQTH.AffineRawResidual

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AffineRawResidual.rawResidualN0_graded_quadPoly_width1
#print axioms QIQTH.AffineRawResidual.rawResidualN0_graded_quadPoly_width43
#print axioms QIQTH.AffineRawResidual.tauResidualN0_Or_graded_quadPoly_width1
#print axioms QIQTH.AffineRawResidual.rawResidualN1_affine_graded_quadPoly_width1
