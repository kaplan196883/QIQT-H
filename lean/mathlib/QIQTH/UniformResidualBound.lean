/-
  UniformResidualBound — J4-86: discharging the F-res firewall of J4-84/J4-85.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## The firewall this file addresses (F-res).

  J4-85 (`UniformCutoffEngine.lean`) reduced the whole uniform cutoff-residual bound over the compact base
  set `K` to the SINGLE conditional input `hResU` (F-res):
      `∃ ρ_u > 0, ∃ C ≥ 0, ∀ q ∈ K, ∀ v, ‖v‖ < ρ_u →
         |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u t v| ≤ C·gaussDdimWide t v`.

  J4-84's census split the per-`q` residual (`residualN0_gaussian_bound_C3`,
  `parametrixResidual_N0_O1_isolated_C2`) into THREE terms:
    (1) the leading off-diagonal term `(1/t)·G·totalRadialO1_coeff g̃ g̃⁻¹ Θ u v` — bounded per `q` by a
        LITTLE-`o` of `totalRadialO1_coeff` (`totalRadialO1_coeff_isLittleO_C3`), whose radius is the
        C³ Taylor-remainder wall (NON-explicit; per-`q`);
    (2) the quadratic deviation `(1/t²)·G·((-1/4)·∑(g̃⁻¹−δ)v_iv_j)·w₀` — already uniform: the deviation
        `M` is uniform over `K` (`uniformFlowPullbackMetricInv_dev_uniform`, ONE `M`/`r₀`) and
        `W = |w₀|` is `q`-independent;
    (3) the Laplacian term `G·Δ_g̃ w₀` — needs a uniform Laplacian bound `L = |Δ_g̃ w₀|` near `0`.

  ## Landed here (green; NO `sorry`, NO new axioms, NO `expRho` in statements, NO vacuous hypotheses).

  * `uniformFlowLaplaceBeltrami_w0_near_uniform` (R2) — TERM (3) MADE UNIFORM.  For the `q`-INDEPENDENT
    smooth coefficient `w₀ = foldedCoeff Θ u 0`, there is a SINGLE radius `r > 0` and constant `L ≥ 0`
    with `|Δ_g̃_q w₀ v| ≤ L` for EVERY `q ∈ K` and `‖v‖ < r`.  Assembled DIRECTLY (bounds-bypass-continuity,
    same style as `uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound` but NEAR `0` instead of an
    annulus) from the uniform inverse-metric entry bound (D4), the uniform Christoffel bound (D5), and
    the `q`-independent gradient/Hessian sup-bounds of the FIXED smooth `w₀` on a closed ball (EVT via
    `IsCompact.exists_bound_of_continuousOn`).  Hypotheses ONLY `hg`+`hC`+`IsCompact K`+`hgnd`+`hw0smooth`,
    all genuine (satisfiable by `g = gi = δ`).  NOT `a₁ = R/6`.

  ## FIREWALLED (exact open statement — the ONE genuine per-`q` ingredient).

  (F-res-1) THE UNIFORM QUANTITATIVE `O(r²)` COEFFICIENT BOUND — term (1)'s residue:
      `∃ ρ_c > 0, ∃ C_c ≥ 0, ∀ q ∈ K, ∀ v, ‖v‖ < ρ_c →
         |totalRadialO1_coeff g̃_q g̃⁻¹_q Θ u v| ≤ C_c · rncRadialSq v`.
  The per-`q` little-`o` `totalRadialO1_coeff_isLittleO_C3` gives NO explicit radius; a uniform explicit
  `O(r²)` bound over `K` needs a uniform bound on `∂Γ̃` (equivalently a uniform `C³` bound on `g̃`), one
  derivative above the available `uniformFlowPullbackMetric_c2_uniform_full`.  This is the residual
  C³ Taylor-remainder wall, carried as the `hCoeffU` hypothesis of the assembly below.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.UniformCutoffEngine
import QIQTH.UniformFlowJetZero
import QIQTH.ResidualN0FiniteReg
import QIQTH.ParametrixResidualN0Bound

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.GaussianWidthTolerant QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### R2 — the uniform Laplacian bound `|Δ_g̃ w₀|` near `0` (term (3)). -/

/-- **★ J4-86 (R2) — THE UNIFORM `|Δ_g̃ w₀|` BOUND near `0`.**  For the `q`-independent smooth
    coefficient `w₀ = foldedCoeff Θ u 0`, there is a SINGLE radius `r > 0` and constant `L ≥ 0` with
    `|Δ_g̃_q w₀ v| ≤ L` for every `q ∈ K` and `‖v‖ < r`, where
    `g̃_q = uniformFlowPullbackMetric g gi hC hK q`.  The Laplace–Beltrami of a FIXED smooth function has
    uniformly bounded value once the metric data is uniformly bounded:
    `|Δ_g̃ w₀| ≤ ∑_{ij} |g̃⁻¹_{ij}|·(|∂_i∂_j w₀| + ∑_k |Γ̃^k_{ij}|·|∂_k w₀|)
              ≤ n²·Kg·(Kw₂ + n·KΓ·Kw₁)`
    with `Kg` the uniform inverse-metric entry bound (D4), `KΓ` the uniform Christoffel bound (D5), and
    `Kw₁`,`Kw₂` the gradient/Hessian sup-bounds of the `q`-independent `w₀` on the closed ball
    `closedBall 0 r` (EVT: `w₀ ∈ C^∞ ⟹ ∂w₀,∂∂w₀` continuous ⟹ bounded on the compact ball).  Same
    bounds-bypass-continuity assembly as `uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound`, but
    NEAR `0` rather than on an annulus.  Hypotheses ONLY `hg`+`hC`+`IsCompact K`+`hgnd`+`hw0smooth`, all
    genuine (satisfiable by `g = gi = δ`).  NOT `a₁ = R/6`. -/
theorem uniformFlowLaplaceBeltrami_w0_near_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0)) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r →
      |laplaceBeltrami (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
          (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d)
          (foldedCoeff Θ u 0) v| ≤ L := by
  classical
  obtain ⟨r₁, hr₁0, Kg, hKg0, hGIb⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound g gi hg hC hK hgnd
  obtain ⟨r₂, hr₂0, KΓ, hKΓ0, hChb⟩ := uniformFlowChristoffel_uniform_bound g gi hg hC hK hgnd
  set w0 : Point n → ℝ := foldedCoeff Θ u 0 with hw0def
  set r : ℝ := min r₁ r₂ with hr_def
  have hr0 : 0 < r := lt_min hr₁0 hr₂0
  -- continuity of the gradient / Hessian entries of the fixed smooth `w₀`.
  have hpd1cont : ∀ k : Fin n, Continuous (fun v => pd w0 k v) :=
    fun k => (contDiff_pd w0 hw0smooth k).continuous
  have hpd2cont : ∀ i j : Fin n, Continuous (fun v => pd (fun y => pd w0 j y) i v) :=
    fun i j => (contDiff_pd (fun y => pd w0 j y) (contDiff_pd w0 hw0smooth j) i).continuous
  -- `Kw₁` bounds `∑_k |∂_k w₀|` on `closedBall 0 r`.
  obtain ⟨Kw1, hKw10, hw1sum⟩ : ∃ Kw1 : ℝ, 0 ≤ Kw1 ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) r, (∑ k, |pd w0 k v|) ≤ Kw1 := by
    have hcont : Continuous (fun v => ∑ k, |pd w0 k v|) :=
      continuous_finsetSum _ (fun k _ => (hpd1cont k).abs)
    obtain ⟨C, hC'⟩ :=
      (isCompact_closedBall (0 : Point n) r).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hC' v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  -- `Kw₂` bounds `∑_i ∑_j |∂_i∂_j w₀|` on `closedBall 0 r`.
  obtain ⟨Kw2, hKw20, hw2sum⟩ : ∃ Kw2 : ℝ, 0 ≤ Kw2 ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) r,
        (∑ i, ∑ j, |pd (fun y => pd w0 j y) i v|) ≤ Kw2 := by
    have hcont : Continuous (fun v => ∑ i, ∑ j, |pd (fun y => pd w0 j y) i v|) :=
      continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => (hpd2cont i j).abs))
    obtain ⟨C, hC'⟩ :=
      (isCompact_closedBall (0 : Point n) r).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hC' v hv
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  refine ⟨r, hr0, (n : ℝ) * (n : ℝ) * (Kg * (Kw2 + (n : ℝ) * KΓ * Kw1)), by positivity, ?_⟩
  intro q hq v hv
  have hv1 : ‖v‖ < r₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v‖ < r₂ := lt_of_lt_of_le hv (min_le_right _ _)
  have hvball : v ∈ Metric.closedBall (0 : Point n) r := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  -- entrywise uniform bounds at the near point `v`.
  have hGI : ∀ i j : Fin n, |uniformFlowPullbackMetricInv g gi hC hK q v i j| ≤ Kg := hGIb q hq v hv1
  have hCh : ∀ k i j : Fin n,
      |christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
          (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v| ≤ KΓ :=
    hChb q hq v hv2
  -- per-`k` gradient bound and per-`(i,j)` Hessian bound of the fixed `w₀`.
  have hDw : ∀ k : Fin n, |pd w0 k v| ≤ Kw1 := by
    intro k
    exact le_trans (Finset.single_le_sum (f := fun k' => |pd w0 k' v|)
      (fun k' _ => abs_nonneg _) (Finset.mem_univ k)) (hw1sum v hvball)
  have hDDw : ∀ i j : Fin n, |pd (fun y => pd w0 j y) i v| ≤ Kw2 := by
    intro i j
    refine le_trans ?_ (hw2sum v hvball)
    calc |pd (fun y => pd w0 j y) i v|
        ≤ ∑ j', |pd (fun y => pd w0 j' y) i v| :=
          Finset.single_le_sum (f := fun j' => |pd (fun y => pd w0 j' y) i v|)
            (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', |pd (fun y => pd w0 j' y) i' v| :=
          Finset.single_le_sum (f := fun i' => ∑ j', |pd (fun y => pd w0 j' y) i' v|)
            (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i)
  -- `|x - y| ≤ |x| + |y|`.
  have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    have h := abs_add_le x (-y); rwa [← sub_eq_add_neg, abs_neg] at h
  -- inner-expression bound: `|∂_i∂_j w₀ − ∑_k Γ̃^k_{ij} ∂_k w₀| ≤ Kw₂ + n·KΓ·Kw₁`.
  have hE : ∀ i j : Fin n,
      |pd (fun y => pd w0 j y) i v
          - ∑ k, christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
              (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v
              * pd w0 k v|
        ≤ Kw2 + (n : ℝ) * KΓ * Kw1 := by
    intro i j
    refine le_trans (habs_sub _ _) ?_
    refine add_le_add (hDDw i j) ?_
    calc |∑ k, christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
            (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v * pd w0 k v|
        ≤ ∑ k, |christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
            (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v * pd w0 k v| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, KΓ * Kw1 := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul]
            exact mul_le_mul (hCh k i j) (hDw k) (abs_nonneg _) hKΓ0
      _ = (n : ℝ) * KΓ * Kw1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- assemble the double sum.
  simp only [laplaceBeltrami]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _) ?_
  have hInner : ∀ i j : Fin n,
      |uniformFlowPullbackMetricInv g gi hC hK q v i j
          * (pd (fun y => pd w0 j y) i v
            - ∑ k, christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
                (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v
                * pd w0 k v)|
        ≤ Kg * (Kw2 + (n : ℝ) * KΓ * Kw1) := by
    intro i j
    rw [abs_mul]
    exact mul_le_mul (hGI i j) (hE i j) (abs_nonneg _) hKg0
  calc ∑ i, ∑ j, |uniformFlowPullbackMetricInv g gi hC hK q v i j
          * (pd (fun y => pd w0 j y) i v
            - ∑ k, christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
                (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v
                * pd w0 k v)|
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, Kg * (Kw2 + (n : ℝ) * KΓ * Kw1) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hInner i j
    _ = (n : ℝ) * (n : ℝ) * (Kg * (Kw2 + (n : ℝ) * KΓ * Kw1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### The pointwise (explicit-`v`) quadratic-deviation bound (term (2)). -/

/-- **Pointwise quadratic-deviation bound.**  The single-`v` core of `residualQuadratic_gaussian_bound`
    (the `filter_upwards` body extracted verbatim): for any `v` with `|gi v i j − δ_{ij}| ≤ M·rncRadialSq v`
    (all `i,j`) and `|w₀ v| ≤ W`,
        `|(1/t²)·G·((−¼)·∑(gi−δ)v_iv_j)·w₀ v| ≤ 32·n²·M·W·gaussDdimWide t v` .
    This is the explicit-radius replacement of the `∀ᶠ` `residualQuadratic_gaussian_bound`, so a uniform
    `M`/`W` over `K` yields a uniform term-(2) bound on an explicit ball. -/
theorem residualQuadratic_pointwise (gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) {t : ℝ} (ht : 0 < t) (M W : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (v : Point n)
    (hdev_v : ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw_v : |foldedCoeff Θ u 0 v| ≤ W) :
    |(1 / t ^ 2) * gaussDdim t v
        * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
        * foldedCoeff Θ u 0 v|
      ≤ 32 * (n : ℝ) ^ 2 * M * W * gaussDdimWide t v := by
  have htne : t ≠ 0 := ht.ne'
  set S : ℝ := ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j) with hSdef
  set w : ℝ := foldedCoeff Θ u 0 v with hwdef
  have hSabs : |S| ≤ (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 := by
    calc |S| ≤ ∑ i, ∑ j, |(gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, M * rncRadialSq v ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            have h1 : |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v := hdev_v i j
            have h2 : |v i * v j| ≤ rncRadialSq v := by
              rw [abs_mul]
              calc |v i| * |v j|
                  ≤ rncRadial v * rncRadial v :=
                    mul_le_mul (abs_coord_le_rncRadial v i) (abs_coord_le_rncRadial v j)
                      (abs_nonneg _) (rncRadial_nonneg v)
                _ = rncRadialSq v := by rw [← rncRadial_sq]; ring
            calc |gi v i j - (if i = j then (1 : ℝ) else 0)| * |v i * v j|
                ≤ (M * rncRadialSq v) * rncRadialSq v :=
                  mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hM (rncRadialSq_nonneg v))
              _ = M * rncRadialSq v ^ 2 := by ring
      _ = (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
  have hrr2G : rncRadialSq v ^ 2 * gaussDdim t v ≤ 128 * t ^ 2 * gaussDdimWide t v := by
    have h := rncRadialSq_pow_mul_gaussDdim_le 2 ht v
    have hc : (8 : ℝ) ^ 2 * ((2 : ℕ).factorial : ℝ) = 128 := by norm_num [Nat.factorial]
    rwa [hc] at h
  have hG : 0 ≤ gaussDdim t v := gaussDdim_nonneg t v
  have hn2Mrr : 0 ≤ (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hM) (sq_nonneg _)
  have hC0 : 0 ≤ (1 / t ^ 2) * (1 / 4) := by positivity
  have hK2 : 0 ≤ (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2) := by
    apply mul_nonneg
    · apply div_nonneg _ (by norm_num)
      exact mul_nonneg (mul_nonneg (sq_nonneg _) hM) hW
    · positivity
  have habs2 : |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * gaussDdim t v * (1 / 4) * |S| * |w| := by
    simp only [abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / t ^ 2 by positivity),
        abs_of_nonneg hG, show |(-1 / 4 : ℝ)| = 1 / 4 by norm_num]
    ring
  calc |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * (1 / 4) * gaussDdim t v * (|S| * |w|) := by rw [habs2]; ring
    _ ≤ (1 / t ^ 2) * (1 / 4) * gaussDdim t v
          * (((n : ℝ) ^ 2 * M * rncRadialSq v ^ 2) * W) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hSabs hw_v (abs_nonneg _) hn2Mrr)
            (mul_nonneg hC0 hG)
    _ = (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2) * (rncRadialSq v ^ 2 * gaussDdim t v) := by ring
    _ ≤ (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2) * (128 * t ^ 2 * gaussDdimWide t v) :=
          mul_le_mul_of_nonneg_left hrr2G hK2
    _ = 32 * (n : ℝ) ^ 2 * M * W * gaussDdimWide t v := by field_simp; ring

/-! ### R3 — the assembly: F-res from the ONE firewalled coefficient input. -/

/-- **★ J4-86 (R3) — F-res ASSEMBLED, conditional ONLY on the term-(1) coefficient bound.**  From the
    ONE firewalled input `hCoeffU` (the UNIFORM quantitative `O(r²)` bound on `totalRadialO1_coeff` over
    `K`), together with the genuine geometric data (`hg`/`hC`/`hK`/`hgnd`/`hgsymm`/`hinvF`/`hframeK`) and
    the heat-side data (`Θ`/`u`/`hw0smooth`/`ht`), there is a SINGLE radius `ρ_u > 0` and constant
    `C ≥ 0` such that the `N=0` uniform-flow parametrix residual is dominated by `C·gaussDdimWide t v`
    for EVERY `q ∈ K`, `‖v‖ < ρ_u` — exactly the F-res (`hResU`) shape J4-85 consumes.

    Assembly (per `q`, on the SINGLE ball `ρ_u = min(r_dev, r_L, ρ_c)`):  the residual is split by
    `parametrixResidual_N0_O1_isolated_C2` into its three terms, each dominated on the explicit ball:
      • term (1) `(1/t)·G·totalRadialO1_coeff` ≤ `8·C_c·G_wide`  — from `hCoeffU` and the `m=1`
        absorption `rncRadialSq·G ≤ 8t·G_wide` (`rncRadialSq_mul_gaussDdim_le`);
      • term (2) `(1/t²)·G·[−¼∑(g̃⁻¹−δ)v_iv_j]·w₀` ≤ `32·n²·M·W·G_wide`  — via `residualQuadratic_pointwise`
        fed the UNIFORM deviation `M` (`uniformFlowPullbackMetricInv_dev_uniform`) and the `q`-independent
        `W = sup|w₀|` (EVT on the closed ball);
      • term (3) `G·Δ_g̃ w₀` ≤ `L·G_wide`  — via the uniform `L` of R2
        (`uniformFlowLaplaceBeltrami_w0_near_uniform`) and `G ≤ G_wide`.
    Summed by the triangle inequality: `C = 8·C_c + 32·n²·M·W + L`.  All non-firewalled hypotheses are
    genuine (satisfiable by `g = gi = δ`, `hframeK` the RNC-gauge family), none the conclusion; NO
    `expRho` in the statement.  Conditional ONLY on `hCoeffU` (the residual C³ Taylor-remainder wall).
    NOT `a₁ = R/6`. -/
theorem uniformResidual_gaussian_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    {t : ℝ} (ht : 0 < t)
    (ρ_c C_c : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c)
    (hCoeffU : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c * rncRadialSq v) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
      |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u t v|
        ≤ C * gaussDdimWide t v := by
  classical
  have htne : t ≠ 0 := ht.ne'
  -- term (2) uniform deviation `M`.
  obtain ⟨rM, hrM0, M, hM0, hdevU⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform g gi hC hK hg hgnd hgsymm hinvF hframeK
  -- term (3) uniform Laplacian `L` (R2).
  obtain ⟨rL, hrL0, L, hL0, hLapU⟩ :=
    uniformFlowLaplaceBeltrami_w0_near_uniform g gi hg hC hK hgnd Θ u hw0smooth
  -- the SINGLE ball radius.
  set ρ_u : ℝ := min rM (min rL ρ_c) with hρ_u_def
  have hρ_u0 : 0 < ρ_u := lt_min hrM0 (lt_min hrL0 hρ_c)
  -- term (2) `q`-independent `W = sup|w₀|` on the closed ball of radius `ρ_u`.
  obtain ⟨W, hW0, hWbd⟩ : ∃ W : ℝ, 0 ≤ W ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_u, |foldedCoeff Θ u 0 v| ≤ W := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_u).exists_bound_of_continuousOn
        hw0smooth.continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  refine ⟨ρ_u, hρ_u0, 8 * C_c + 32 * (n : ℝ) ^ 2 * M * W + L, by positivity, ?_⟩
  intro q hq v hv
  -- the three strict sub-radius conditions and the closed-ball membership.
  have hvM : ‖v‖ < rM := lt_of_lt_of_le hv (min_le_left _ _)
  have hvL : ‖v‖ < rL := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvc : ‖v‖ < ρ_c := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  -- w₀ ∈ C² at `v` (from `C^∞`), to split the residual.
  have hw0at : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := hw0smooth.contDiffAt.of_le le_top
  rw [parametrixResidual_N0_O1_isolated_C2 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u t ht v hw0at]
  set Gw : ℝ := gaussDdimWide t v with hGwdef
  have hGwnn : 0 ≤ Gw := gaussDdimWide_nonneg t v
  have hGnn : 0 ≤ gaussDdim t v := gaussDdim_nonneg t v
  set T1 : ℝ := (1 / t) * gaussDdim t v
      * totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v with hT1def
  set T2 : ℝ := (1 / t ^ 2) * gaussDdim t v
      * ((-1 / 4) * (∑ i, ∑ j, (uniformFlowPullbackMetricInv g gi hC hK q v i j
          - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
      * foldedCoeff Θ u 0 v with hT2def
  set T3 : ℝ := gaussDdim t v * laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v with hT3def
  -- term (1): `|T1| ≤ 8·C_c·Gw`.
  have hT1bd : |T1| ≤ 8 * C_c * Gw := by
    rw [hT1def, abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr ht.le) hGnn)]
    calc (1 / t) * gaussDdim t v
            * |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ (1 / t) * gaussDdim t v * (C_c * rncRadialSq v) :=
          mul_le_mul_of_nonneg_left (hCoeffU q hq v hvc)
            (mul_nonneg (one_div_nonneg.mpr ht.le) hGnn)
      _ = C_c * (1 / t) * (rncRadialSq v * gaussDdim t v) := by ring
      _ ≤ C_c * (1 / t) * (8 * t * Gw) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_c0 (one_div_nonneg.mpr ht.le))
          rw [hGwdef, ← rncRadial_sq]; exact rncRadialSq_mul_gaussDdim_le ht v
      _ = 8 * C_c * Gw := by field_simp
  -- term (2): `|T2| ≤ 32·n²·M·W·Gw`.
  have hT2bd : |T2| ≤ 32 * (n : ℝ) ^ 2 * M * W * Gw := by
    rw [hT2def, hGwdef]
    exact residualQuadratic_pointwise (uniformFlowPullbackMetricInv g gi hC hK q) Θ u ht M W hM0 hW0 v
      (hdevU q hq v hvM) (hWbd v hvball)
  -- term (3): `|T3| ≤ L·Gw`.
  have hT3bd : |T3| ≤ L * Gw := by
    rw [hT3def, abs_mul, abs_of_nonneg hGnn]
    calc gaussDdim t v * |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v|
        ≤ gaussDdim t v * L := mul_le_mul_of_nonneg_left (hLapU q hq v hvL) hGnn
      _ ≤ Gw * L := by rw [hGwdef]; exact mul_le_mul_of_nonneg_right (gaussDdim_le_gaussDdimWide ht v) hL0
      _ = L * Gw := by ring
  -- assemble via the triangle inequality.
  have htri : |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 + T2 - T3| ≤ |T1 + T2| + |T3| := by
      have h := abs_add_le (T1 + T2) (-T3); rwa [← sub_eq_add_neg, abs_neg] at h
    have h2 : |T1 + T2| ≤ |T1| + |T2| := abs_add_le _ _
    linarith
  calc |T1 + T2 - T3|
      ≤ |T1| + |T2| + |T3| := htri
    _ ≤ 8 * C_c * Gw + 32 * (n : ℝ) ^ 2 * M * W * Gw + L * Gw :=
        add_le_add (add_le_add hT1bd hT2bd) hT3bd
    _ = (8 * C_c + 32 * (n : ℝ) ^ 2 * M * W + L) * Gw := by ring

/-! ### R4 — the uniform cutoff engine, conditional ONLY on the term-(1) coefficient bound. -/

/-- **★ J4-86 (R4) — THE CUTOFF ENGINE UNIFORM OVER `K`, conditional only on `hCoeffU`.**  Feeds the
    assembled F-res (`uniformResidual_gaussian_bound`, R3) into J4-85's `cutoffResidual_uniformFlow_uniform`,
    discharging its `hResU`.  So the uniform-over-`K` single-`(a,b,B)` cutoff-parametrix residual bound
    holds under ONLY the geometric/heat-side data plus the ONE firewalled term-(1) coefficient input
    `hCoeffU`.  This is the F-res wall reduced to exactly the residual C³ Taylor-remainder of the
    off-diagonal cancellation, uniform over `K`.  NOT `a₁ = R/6`. -/
theorem cutoffResidual_uniformFlow_of_coeffBound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    {t : ℝ} (ht : 0 < t)
    (ρ_c C_c : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c)
    (hCoeffU : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c * rncRadialSq v) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∀ q ∈ K, ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) t
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u t y) v|
        ≤ B * gaussDdimWide t v := by
  obtain ⟨ρ_u, hρ_u0, C, hC0, hResU⟩ :=
    uniformResidual_gaussian_bound g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw0smooth ht
      ρ_c C_c hρ_c hC_c0 hCoeffU
  exact cutoffResidual_uniformFlow_uniform g gi hg hC hK hgnd hgsymm Θ u hw0smooth ht
    C ρ_u hC0 hρ_u0 hResU

end QIQTH.HeatResidualBound
