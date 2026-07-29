/-
  ParametrixHAnnulusBounds — the concrete heat-parametrix annulus derivative bounds
  `hHann` / `hDHann` for `H = gaussDdim · cofactor`, discharging the `H`-carries of the C4c
  cutoff-residual global bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE DELIVERS (honest FLOOR = F1).

  The just-landed `cutoffResidual_global_gaussianWide_bound` (in `CutoffResidualGlobalBound`)
  carries two annulus derivative bounds on the concrete parametrix `H = gaussDdim · cofactor`
  (the heat parametrix `H = G_t · Θ^{-1/2} · Σ_k u_k t^k`, with a smooth, bounded geometric
  `cofactor = Θ^{-1/2} Σ_k u_k t^k` on the injectivity ball):

    • `hHann`  : `∀ w, a² ≤ rncRadialSq w → rncRadialSq w ≤ b² → |H w| ≤ M · gaussDdim t w` ,
    • `hDHann` : `∀ w j, … → |∂ⱼ H w| ≤ M · (1/t) · gaussDdim t w` .

  THE MECHANISM.  `H = G · cofactor` with `G = gaussDdim t`.
    • `hHann`  : `|G w · cofactor w| = G w · |cofactor w| ≤ G w · K_cof` (cofactor bounded by
      `K_cof` on the compact annulus, `exists_bound_on_annulus`), take `M ≥ K_cof`.
    • `hDHann` : by the Leibniz rule `pd_mul` and the EXACT Gaussian gradient
      `∂ⱼG = (−wʲ/(2t))·G` (`gaussDdim_pd_eq`),
        `∂ⱼ(G·cofactor) w = (−wʲ/(2t))·G w·cofactor w + G w·∂ⱼcofactor w` .
      On the annulus `|wʲ| ≤ b` (from `(wʲ)² ≤ ∑ = rncRadialSq ≤ b²`), `|cofactor| ≤ K_cof`,
      `|∂ⱼcofactor| ≤ K_dcof`, so
        `|∂ⱼ(G·cofactor) w| ≤ (b/(2t))·G w·K_cof + G w·K_dcof
                            = (1/t)·G w·(b·K_cof/2 + t·K_dcof) ≤ M·(1/t)·G w` ,
      taking `M := max K_cof (b·K_cof/2 + t·K_dcof)` (secures both `M ≥ K_cof` and
      `M ≥ b·K_cof/2 + t·K_dcof`).  `M` depends on the FIXED cutoff-time parameter `t` — fine.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CARRIED COFACTOR REGULARITY (all GENUINE, load-bearing, NONE vacuous).  These are honest
  regularity facts about the geometric cofactor `Θ^{-1/2} Σ_k u_k t^k`, which is `C∞` on the
  injectivity ball (smooth `Θ`, `u_k`), hence continuous with continuous partials and partially
  differentiable in every coordinate:
    • `hcof_cont  : Continuous cofactor`                              (bounds `|cofactor|`);
    • `hcof_pdiff : ∀ i x, PdiffAt cofactor i x`                      (feeds the Leibniz rule);
    • `hdcof_cont : ∀ j, Continuous (fun w => pd cofactor j w)`       (bounds `|∂ⱼcofactor|`).
  NONE is vacuous: each is a true `C¹` fact for the concrete cofactor.  The Gaussian factor's own
  smoothness (`gaussDdim_contDiff`) and gradient (`gaussDdim_pd_eq`) are NOT carried — proved.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  FLOOR STATUS = F1 (the full lemma: both `hHann` and `hDHann`).  `parametrixH_annulus_bounds`
  produces `∃ M ≥ 0, hHann ∧ hDHann` from cofactor continuity / `C¹`.  This discharges the
  `hHann` / `hDHann` carries of `cutoffResidual_global_gaussianWide_bound`, reducing them to
  cofactor regularity, toward the far-field / unconditional `a₁ = R/6`.  It is NOT itself
  `a₁ = R/6`.  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.HeatResidualBound
import QIQTH.ResidueBound
import QIQTH.HeatParametrixOrder
import QIQTH.CutoffAnnulusBounds
import QIQTH.CutoffResidualGlobalBound

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.HeatParametrixOrder
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **The concrete-parametrix annulus derivative bounds `hHann` / `hDHann`** for
    `H = gaussDdim t · cofactor`.  On the compact annulus `{a² ≤ rncRadialSq ≤ b²}`,
      `|H w| ≤ M · gaussDdim t w`   and   `|∂ⱼ H w| ≤ M · (1/t) · gaussDdim t w` ,
    with a single `M ≥ 0` (depending on the fixed cutoff-time `t`).  The value bound comes from
    boundedness of the smooth cofactor on the compact annulus (`exists_bound_on_annulus`); the
    derivative bound comes from the Leibniz rule (`pd_mul`) together with the EXACT flat Gaussian
    gradient `∂ⱼ(gaussDdim t) = (−wʲ/(2t))·gaussDdim t` (`gaussDdim_pd_eq`) and the annulus radial
    bound `|wʲ| ≤ b`.  Carries genuine cofactor continuity / `C¹` (see the file docstring); none
    vacuous.  Discharges the `H`-carries of `cutoffResidual_global_gaussianWide_bound`. -/
theorem parametrixH_annulus_bounds (t : ℝ) (ht : 0 < t) (a b : ℝ) (hb : 0 < b)
    (cofactor : Point n → ℝ) (hcof_cont : Continuous cofactor)
    (hcof_pdiff : ∀ (i : Fin n) (x : Point n), PdiffAt cofactor i x)
    (hdcof_cont : ∀ j, Continuous (fun w => pd cofactor j w)) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |(fun y => gaussDdim t y * cofactor y) w| ≤ M * gaussDdim t w) ∧
      (∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd (fun y => gaussDdim t y * cofactor y) j w| ≤ M * (1 / t) * gaussDdim t w) := by
  classical
  -- cofactor value bound on the annulus
  obtain ⟨Kcof, hKcof0, hKcof⟩ := exists_bound_on_annulus cofactor hcof_cont a b
  -- uniform cofactor-gradient bound on the annulus (sum over the finite index set `Fin n`)
  have hbd : ∀ j : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |pd cofactor j w| ≤ K :=
    fun j => exists_bound_on_annulus (fun w => pd cofactor j w) (hdcof_cont j) a b
  choose Kd hKd0 hKdbd using hbd
  set Kdcof : ℝ := ∑ j, Kd j with hKdcof_def
  have hKdcof0 : 0 ≤ Kdcof := Finset.sum_nonneg fun j _ => hKd0 j
  have hKdcof : ∀ (w : Point n) (j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |pd cofactor j w| ≤ Kdcof := by
    intro w j h1 h2
    refine (hKdbd j w h1 h2).trans ?_
    exact Finset.single_le_sum (f := fun j' => Kd j') (fun j' _ => hKd0 j') (Finset.mem_univ j)
  -- the common constant
  set M : ℝ := max Kcof (b * Kcof / 2 + t * Kdcof) with hM_def
  have hMKcof : Kcof ≤ M := le_max_left _ _
  have hMsum : b * Kcof / 2 + t * Kdcof ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := le_trans hKcof0 hMKcof
  refine ⟨M, hM0, ?_, ?_⟩
  · -- `hHann` : the value bound
    intro w h1 h2
    have hG0 : 0 ≤ gaussDdim t w := gaussDdim_nonneg t w
    show |gaussDdim t w * cofactor w| ≤ M * gaussDdim t w
    rw [abs_mul, abs_of_nonneg hG0]
    calc gaussDdim t w * |cofactor w|
        ≤ gaussDdim t w * Kcof := mul_le_mul_of_nonneg_left (hKcof w h1 h2) hG0
      _ ≤ gaussDdim t w * M := mul_le_mul_of_nonneg_left hMKcof hG0
      _ = M * gaussDdim t w := by ring
  · -- `hDHann` : the derivative bound
    intro w j h1 h2
    have hG0 : 0 ≤ gaussDdim t w := gaussDdim_nonneg t w
    have h2tpos : (0 : ℝ) < 2 * t := by linarith
    -- `|wʲ| ≤ b` on the annulus
    have hwj : |w j| ≤ b := by
      have hle : (w j) ^ 2 ≤ b ^ 2 :=
        calc (w j) ^ 2 ≤ ∑ i, (w i) ^ 2 :=
              Finset.single_le_sum (f := fun i => (w i) ^ 2)
                (fun i _ => sq_nonneg _) (Finset.mem_univ j)
          _ = rncRadialSq w := rfl
          _ ≤ b ^ 2 := h2
      calc |w j| = Real.sqrt ((w j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hle
        _ = |b| := Real.sqrt_sq_eq_abs _
        _ = b := abs_of_pos hb
    -- Leibniz + exact Gaussian gradient
    have hpg : PdiffAt (fun y => gaussDdim t y) j w :=
      PdiffAt_of_contDiff (fun y => gaussDdim t y) (gaussDdim_contDiff t) j w
    have hpc : PdiffAt cofactor j w := hcof_pdiff j w
    rw [pd_mul (fun y => gaussDdim t y) cofactor j w hpg hpc, gaussDdim_pd_eq t ht w j]
    -- bound the two Leibniz terms
    have hT1 : |(-(w j) / (2 * t)) * gaussDdim t w * cofactor w|
        ≤ b / (2 * t) * gaussDdim t w * Kcof := by
      rw [abs_mul, abs_mul, abs_of_nonneg hG0, abs_div, abs_neg, abs_of_pos h2tpos]
      have hGA : 0 ≤ |w j| / (2 * t) * gaussDdim t w :=
        mul_nonneg (div_nonneg (abs_nonneg _) (le_of_lt h2tpos)) hG0
      calc |w j| / (2 * t) * gaussDdim t w * |cofactor w|
          ≤ |w j| / (2 * t) * gaussDdim t w * Kcof :=
            mul_le_mul_of_nonneg_left (hKcof w h1 h2) hGA
        _ ≤ b / (2 * t) * gaussDdim t w * Kcof :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right h2tpos).mpr hwj) hG0)
              hKcof0
    have hT2 : |gaussDdim t w * pd cofactor j w| ≤ gaussDdim t w * Kdcof := by
      rw [abs_mul, abs_of_nonneg hG0]
      exact mul_le_mul_of_nonneg_left (hKdcof w j h1 h2) hG0
    -- scalar closing inequality
    have hscalar : b / (2 * t) * Kcof + Kdcof ≤ M * (1 / t) := by
      have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
      rw [mul_one_div, le_div_iff₀ ht]
      have heq : (b / (2 * t) * Kcof + Kdcof) * t = b * Kcof / 2 + t * Kdcof := by
        field_simp
      rw [heq]
      exact hMsum
    calc |(-(w j) / (2 * t)) * gaussDdim t w * cofactor w + gaussDdim t w * pd cofactor j w|
        ≤ |(-(w j) / (2 * t)) * gaussDdim t w * cofactor w| + |gaussDdim t w * pd cofactor j w| :=
          abs_add_le _ _
      _ ≤ b / (2 * t) * gaussDdim t w * Kcof + gaussDdim t w * Kdcof := add_le_add hT1 hT2
      _ = gaussDdim t w * (b / (2 * t) * Kcof + Kdcof) := by ring
      _ ≤ gaussDdim t w * (M * (1 / t)) := mul_le_mul_of_nonneg_left hscalar hG0
      _ = M * (1 / t) * gaussDdim t w := by ring

end QIQTH.HeatResidualBound
