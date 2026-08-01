/-
  UniformCutoffEngine — J4-85: making the CUTOFF ENGINE uniform over the compact base set `K`,
  discharging the F-cut firewall left open by J4-84 (`UniformNearEngine.lean`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## The firewall this file addresses (F-cut).

  J4-84 made the NEAR engine uniform (`near_uncutResidual_uniform`), reducing the full uniform `hEnear`
  over `K` to the single firewalled residual input `hResU` (F-res).  The remaining obstruction to a
  UNIFORM cutoff-residual bound over `K` was purely PACKAGING: the finite-regularity cutoff engine
  `cutoffResidual_global_gaussianWide_bound_C2` (`CutoffResidualFiniteReg.lean:73`) returns its dominating
  constant `B` EXISTENTIALLY, hiding the actual formula
      `B = C + Mann·Kc2 + 2·n²·Kg·Kc1·Mann·(8/a²)` ,
  so a single-over-`K` `B` cannot be assembled even though every ingredient has a uniform (or
  `q`-independent) supplier:

    • `C`    (near constant)              — uniform via J4-84 `near_uncutResidual_uniform` (from `hResU`);
    • `Mann` (`|H|`,`|∂H|` annulus)       — `q`-INDEPENDENT via `parametrixH_annulus_bounds` on the
                                            `q`-independent `heatParametrix 0 Θ u t`;
    • `Kg`   (`|g̃⁻¹|` annulus)            — uniform via `uniformFlowPullbackMetricInv_entry_uniform_bound_annulus`;
    • `Kc1`  (cutoff-derivative)          — `q`-INDEPENDENT via `pd_radialCutoff_bound_on_annulus`;
    • `Kc2`  (`|Δ_g̃χ|` annulus)           — uniform via `uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound`.

  ## Landed here (green; NO `sorry`, NO new axioms, NO `expRho` in statements, NO vacuous hypotheses).

  * `cutoffResidual_global_gaussianWide_bound_explicitB` (C1) — the EXPLICIT-`B` variant of the finite
    cutoff engine: same hypotheses, conclusion with the constant given by its actual formula
    `C + M·Kc2 + 2·n²·Kg·Kc1·M·(8/a²)` (a conjunction `0 ≤ B_expl ∧ ∀ v, |…| ≤ B_expl·gaussDdimWide`).
    This is `cutoffResidual_global_gaussianWide_bound_C2`'s proof verbatim, with only the final
    existential packaging replaced by the transparent constant.

  * `uniformFlowPullbackMetricInv_symm_global` — GLOBAL symmetry of the uniform-flow inverse metric
    (all `w`, unconditionally on unit-ness): where `g̃(w)` is a unit use `uniformFlowPullbackMetricInv_symm`;
    where it is not, `Ring.inverse = 0` so both entries vanish.  Discharges the cutoff engine's global
    `hgisymm` from the genuine metric symmetry `hgsymm`.

  * `cutoffResidual_uniformFlow_uniform` (C2) — THE CUTOFF ENGINE MADE UNIFORM OVER `K`: from the single
    firewalled uniform residual input `hResU` (F-res) plus the genuine geometric/heat-side data
    (`hg`/`hC`/`hK`/`hgnd`/`hgsymm` + `Θ`/`u`/`t`/`hw0smooth`), a SINGLE annulus `(a,b)` and SINGLE
    constant `B ≥ 0` dominate the cutoff-parametrix residual for EVERY `q ∈ K`.  Assembled from C1
    (per `q`, same explicit `B`) + `near_uncutResidual_uniform` (uniform `hEnear`) + the uniform annulus
    suppliers, with the radius bookkeeping `a := b/2`, `b := min(b_near, r₀/2)`.

  ## FIREWALLED (exact open statement).

  (F-res) THE UNIFORM RESIDUAL GAUSSIAN BOUND over `K` — carried verbatim as `hResU`, exactly as J4-84's
  `near_uncutResidual_uniform` consumes it.  Its open residue is the uniform C³ Taylor-remainder wall of
  the off-diagonal cancellation over `K`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CutoffResidualFiniteReg
import QIQTH.UniformNearEngine
import QIQTH.ParametrixHAnnulusBounds
import QIQTH.UniformFlowMetricInvProps

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.GaussianWidthTolerant QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### C1 — the EXPLICIT-`B` cutoff engine (transparent dominating constant). -/

/-- **★ J4-85 (C1) — THE FINITE-REGULARITY GLOBAL CUTOFF RESIDUAL BOUND WITH EXPLICIT `B`.**  Same
    hypotheses as `cutoffResidual_global_gaussianWide_bound_C2`, but the dominating constant is exposed
    by its ACTUAL formula
        `B = C + M·Kc2 + 2·n²·Kg·Kc1·M·(8/a²)` .
    The conclusion is the conjunction `0 ≤ B ∧ ∀ v, |χ·∂ₜH − Δ_g(χ·H)| ≤ B·gaussDdimWide t v` with this
    transparent `B`, so a caller assembling a UNIFORM bound over a base set can read off `B` from uniform
    suppliers of `C`,`M`,`Kg`,`Kc1`,`Kc2`,`a`.  This is the `…_C2` proof VERBATIM (the region split with
    the `C²` Leibniz rule), with only the final existential packaging replaced by the explicit constant.
    All carried hypotheses are genuine and load-bearing exactly as in `…_C2`.  NOT `a₁ = R/6`. -/
theorem cutoffResidual_global_gaussianWide_bound_explicitB
    (g gi : Point n → Fin n → Fin n → ℝ) (H dtH : Point n → ℝ)
    (a b t : ℝ) (ha : 0 < a) (hab : a < b) (ht : 0 < t)
    (hH2 : ∀ w : Point n, ContDiffAt ℝ 2 H w)
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (C : ℝ) (hCnn : 0 ≤ C)
    (hEnear : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |dtH w - laplaceBeltrami g gi H w| ≤ C * gaussDdimWide t w)
    (M : ℝ) (hM : 0 ≤ M)
    (hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |H w| ≤ M * gaussDdim t w)
    (hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd H j w| ≤ M * (1 / t) * gaussDdim t w)
    (Kg Kc1 Kc2 : ℝ) (hKg : 0 ≤ Kg) (hKc1 : 0 ≤ Kc1) (hKc2 : 0 ≤ Kc2)
    (hgibd : ∀ (w : Point n) (i j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |gi w i j| ≤ Kg)
    (hDchi : ∀ (w : Point n) (i : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd (radialCutoff a b) i w| ≤ Kc1)
    (hLapChi : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |laplaceBeltrami g gi (radialCutoff a b) w| ≤ Kc2) :
    0 ≤ C + M * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2) ∧ ∀ v : Point n,
      |radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v|
        ≤ (C + M * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v := by
  -- the three pieces of the constant `B` (unchanged from the `…_C2` version)
  have hb2 : 0 ≤ M * Kc2 := mul_nonneg hM hKc2
  have hcoef : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M := by positivity
  have hb3 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2) := by positivity
  refine ⟨by linarith, ?_⟩
  intro v
  -- the `C²` regularity of the (still smooth) cutoff at the point `v`
  have hχC2 : ContDiffAt ℝ 2 (radialCutoff a b) v :=
    (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgd : gaussDdim t v ≤ gaussDdimWide t v := gaussDdim_le_gaussDdimWide ht v
  have hWnn : 0 ≤ gaussDdimWide t v := gaussDdimWide_nonneg t v
  have ha2b2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  rcases lt_or_ge (rncRadialSq v) (a ^ 2) with hnear | ha2
  · -- (a) NEAR: rncRadialSq v < a²
    have hb : rncRadialSq v ≤ b ^ 2 := le_trans (le_of_lt hnear) ha2b2
    have hχ1 : radialCutoff a b v = 1 := radialCutoff_eq_one ha hab (le_of_lt hnear)
    have hlbmul := laplaceBeltrami_mul_C2 g gi (radialCutoff a b) H v hχC2 (hH2 v) (hgisymm v)
    have hlapχ : laplaceBeltrami g gi (radialCutoff a b) v = 0 :=
      laplaceBeltrami_radialCutoff_zero_near g gi ha hab hnear
    have hpdχ : ∀ i, pd (radialCutoff a b) i v = 0 :=
      fun i => pd_radialCutoff_eq_zero_of_near ha hab hnear i
    have hRcut : radialCutoff a b v * dtH v
        - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v
          = dtH v - laplaceBeltrami g gi H v := by
      rw [hlbmul, hχ1, hlapχ]
      simp [hpdχ]
    rw [hRcut]
    calc |dtH v - laplaceBeltrami g gi H v| ≤ C * gaussDdimWide t v := hEnear v hb
      _ ≤ (C + M * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v := by
          apply mul_le_mul_of_nonneg_right _ hWnn; linarith
  · rcases le_or_gt (rncRadialSq v) (b ^ 2) with hb | hfar
    · -- (b) ANNULUS: a² ≤ rncRadialSq v ≤ b²
      have hlbmul := laplaceBeltrami_mul_C2 g gi (radialCutoff a b) H v hχC2 (hH2 v) (hgisymm v)
      have hRcut : radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v
            = radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v)
              - H v * laplaceBeltrami g gi (radialCutoff a b) v
              - 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v := by
        rw [hlbmul]; ring
      rw [hRcut]
      -- triangle inequality `|A - B' - Cc| ≤ |A| + |B'| + |Cc|`
      have hsub2 : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
        rw [sub_eq_add_neg]; exact (abs_add_le x (-y)).trans_eq (by rw [abs_neg])
      set A := radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v) with hA
      set B' := H v * laplaceBeltrami g gi (radialCutoff a b) v with hB'
      set Cc := 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v with hCc
      have htri : |A - B' - Cc| ≤ |A| + |B'| + |Cc| :=
        (hsub2 (A - B') Cc).trans (by have := hsub2 A B'; linarith)
      -- |A| = |χ·E| ≤ C·W
      have hAbd : |A| ≤ C * gaussDdimWide t v := by
        rw [hA, abs_mul]
        have hχle : |radialCutoff a b v| ≤ 1 := by
          rw [abs_of_nonneg (radialCutoff_nonneg a b v)]; exact radialCutoff_le_one a b v
        calc |radialCutoff a b v| * |dtH v - laplaceBeltrami g gi H v|
            ≤ 1 * (C * gaussDdimWide t v) :=
              mul_le_mul hχle (hEnear v hb) (abs_nonneg _) (by norm_num)
          _ = C * gaussDdimWide t v := by ring
      -- |B'| = |H·Δ_gχ| ≤ (M·Kc2)·W
      have hBbd : |B'| ≤ (M * Kc2) * gaussDdimWide t v := by
        rw [hB', abs_mul]
        calc |H v| * |laplaceBeltrami g gi (radialCutoff a b) v|
            ≤ (M * gaussDdim t v) * Kc2 :=
              mul_le_mul (hHann v ha2 hb) (hLapChi v ha2 hb) (abs_nonneg _)
                (mul_nonneg hM (gaussDdim_nonneg t v))
          _ = (M * Kc2) * gaussDdim t v := by ring
          _ ≤ (M * Kc2) * gaussDdimWide t v := mul_le_mul_of_nonneg_left hgd hb2
      -- |Cc| = |2·∑∑ gⁱʲ ∂ᵢχ ∂ⱼH| ≤ (2 n² Kg Kc1 M (8/a²))·W
      have hSabs : |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      have hterm : ∀ i j : Fin n, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ Kg * Kc1 * (M * (1 / t) * gaussDdim t v) := by
        intro i j
        rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (hgibd v i j ha2 hb) (hDchi v i ha2 hb) (abs_nonneg _) hKg)
          (hDHann v j ha2 hb) (abs_nonneg _) (mul_nonneg hKg hKc1)
      have hsum2 : ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ ∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (M * (1 / t) * gaussDdim t v)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      have hconst : (∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (M * (1 / t) * gaussDdim t v)))
          = (n : ℝ) ^ 2 * (Kg * Kc1 * (M * (1 / t) * gaussDdim t v)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      have hinvT : (1 / t) * gaussDdim t v ≤ (8 / a ^ 2) * gaussDdimWide t v := by
        have h := invTpow_gaussDdim_le_gaussDdimWide 1 a ha ht ha2
        simpa [pow_one, Nat.factorial_one, Nat.cast_one] using h
      have h2pos : (0 : ℝ) < 2 := by norm_num
      have hCcbd : |Cc| ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v := by
        rw [hCc]
        calc |2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
            = 2 * |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v| := by
              rw [abs_mul, abs_of_pos h2pos]
          _ ≤ 2 * ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
              mul_le_mul_of_nonneg_left hSabs (by norm_num)
          _ ≤ 2 * ((n : ℝ) ^ 2 * (Kg * Kc1 * (M * (1 / t) * gaussDdim t v))) :=
              mul_le_mul_of_nonneg_left (hsum2.trans hconst.le) (by norm_num)
          _ = (2 * (n : ℝ) ^ 2 * Kg * Kc1 * M) * ((1 / t) * gaussDdim t v) := by ring
          _ ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * M) * ((8 / a ^ 2) * gaussDdimWide t v) :=
              mul_le_mul_of_nonneg_left hinvT hcoef
          _ = (2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v := by ring
      calc |A - B' - Cc|
          ≤ C * gaussDdimWide t v + (M * Kc2) * gaussDdimWide t v
              + (2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v :=
            htri.trans (add_le_add (add_le_add hAbd hBbd) hCcbd)
        _ = (C + M * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v := by
            ring
    · -- (c) FAR: b² < rncRadialSq v
      have hχ0 : radialCutoff a b v = 0 := radialCutoff_eq_zero ha hab (le_of_lt hfar)
      have hlbmul := laplaceBeltrami_mul_C2 g gi (radialCutoff a b) H v hχC2 (hH2 v) (hgisymm v)
      have hlapχ : laplaceBeltrami g gi (radialCutoff a b) v = 0 :=
        laplaceBeltrami_radialCutoff_zero_far g gi ha hab hfar
      have hpdχ : ∀ i, pd (radialCutoff a b) i v = 0 :=
        fun i => pd_radialCutoff_eq_zero_of_far ha hab hfar i
      have hRcut : radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v = 0 := by
        rw [hlbmul, hχ0, hlapχ]
        simp [hpdχ]
      rw [hRcut, abs_zero]
      have : (0 : ℝ) ≤ C + M * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2) := by linarith
      exact mul_nonneg this hWnn

/-! ### Global symmetry of the uniform-flow inverse metric (discharges the engine's `hgisymm`). -/

/-- **Global symmetry of the uniform-flow inverse metric.**  For EVERY `w` (unconditionally on
    unit-ness), `g̃⁻¹_q(w) i j = g̃⁻¹_q(w) j i`, from the genuine metric symmetry `hgsymm`.  Where the
    matrix `g̃_q(w)` is a unit, this is `uniformFlowPullbackMetricInv_symm`; where it is not,
    `Ring.inverse = 0`, so both entries vanish.  This discharges the cutoff engine's GLOBAL `hgisymm`
    hypothesis (needed on all of `Point n`, off the injectivity ball) from `hgsymm` alone. -/
theorem uniformFlowPullbackMetricInv_symm_global (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hgsymm : ∀ y a b, g y a b = g y b a)
    (q w : Point n) (i j : Fin n) :
    uniformFlowPullbackMetricInv g gi hC hK q w i j
      = uniformFlowPullbackMetricInv g gi hC hK q w j i := by
  by_cases hU : IsUnit (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q w a b))
  · exact uniformFlowPullbackMetricInv_symm g gi hC hK hgsymm q w hU i j
  · simp only [uniformFlowPullbackMetricInv, Ring.inverse_non_unit _ hU,
      ContinuousLinearMap.zero_apply, Pi.zero_apply]

/-! ### C2 — the cutoff engine MADE UNIFORM over `K`. -/

/-- **★ J4-85 (C2) — THE CUTOFF ENGINE, UNIFORM OVER `K`.**  Discharges the F-cut firewall.  From the
    SINGLE firewalled uniform residual input `hResU` (F-res, ONE `ρ_u`, ONE `C`, `∀ q ∈ K`) plus the
    genuine geometric data (`hg` metric `C∞`, `hC` Christoffel `C∞`, `hK` compact, `hgnd` global
    nondegeneracy, `hgsymm` metric symmetry) and the heat-side data (`Θ`/`u`, `ht`, `hw0smooth`), there
    is a SINGLE annulus `(a,b)` and a SINGLE constant `B ≥ 0` such that for EVERY `q ∈ K` the
    cutoff-parametrix residual on `g̃_q = uniformFlowPullbackMetric g gi hC hK q` is dominated by
    `B · gaussDdimWide t v`:
        `∃ a b B, 0<a ∧ a<b ∧ 0≤B ∧ ∀ q∈K, ∀ v,
           |χ(v)·∂ₜH v − Δ_g̃_q(χ·H) v| ≤ B·gaussDdimWide t v`   (χ = radialCutoff a b).
    Assembly: the explicit-`B` engine `cutoffResidual_global_gaussianWide_bound_explicitB` (C1) applied
    per `q` with the SAME `B = C + Mann·Kc2 + 2·n²·Kg·Kc1·Mann·(8/a²)`, fed the uniform near `hEnear`
    (`near_uncutResidual_uniform`, J4-84), the `q`-independent `Mann`
    (`parametrixH_annulus_bounds` on `heatParametrix 0 Θ u t`) and `Kc1`
    (`pd_radialCutoff_bound_on_annulus`), and the UNIFORM annulus `Kg`
    (`uniformFlowPullbackMetricInv_entry_uniform_bound_annulus`) / `Kc2`
    (`uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound`).  Radius bookkeeping: `b := min(b_near,
    r₀/2)` sits below both the near radius `b_near = ρ_u/2` and the annulus-supplier radius `r₀`, and
    `a := b/2` makes the annulus nonempty.  `hgisymm` is discharged globally by
    `uniformFlowPullbackMetricInv_symm_global`.  All hypotheses genuine (satisfiable by `g = δ`), none
    the conclusion; NO `expRho` in the statement.  Conditional ONLY on `hResU` (F-res).  NOT
    `a₁ = R/6`. -/
theorem cutoffResidual_uniformFlow_uniform
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    {t : ℝ} (ht : 0 < t)
    (C ρ_u : ℝ) (hCnn : 0 ≤ C) (hρ_u : 0 < ρ_u)
    (hResU : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
      |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u t v|
        ≤ C * gaussDdimWide t v) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∀ q ∈ K, ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) t
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u t y) v|
        ≤ B * gaussDdimWide t v := by
  classical
  -- (1) the uniform near `hEnear`; FIXES the near radius `b_near = ρ_u/2`.
  obtain ⟨bN, hbN0, hEnearU⟩ :=
    near_uncutResidual_uniform g gi hC hK Θ u C ρ_u hρ_u hResU
  -- (2) uniform annulus suppliers: `Kg` (inverse metric) and the `Kc2` radius (`Δ_g̃χ`).
  obtain ⟨rKg, hrKg0, Kg, hKg0, hGIann⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound_annulus g gi hg hC hK hgnd
  obtain ⟨rKc2, hrKc20, hLapAnn⟩ :=
    uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound g gi hg hC hK hgnd
  -- (3) choose the SINGLE annulus `(a,b)`: `b := min(b_near, r₀/2)`, `a := b/2`.
  set rmin : ℝ := min rKg rKc2 with hrmin_def
  have hrmin0 : 0 < rmin := lt_min hrKg0 hrKc20
  set b : ℝ := min bN (rmin / 2) with hb_def
  have hb0 : 0 < b := lt_min hbN0 (by linarith)
  have hb_nonneg : (0 : ℝ) ≤ b := le_of_lt hb0
  set a : ℝ := b / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  have hb_le_bN : b ≤ bN := min_le_left _ _
  have hb_lt_rmin : b < rmin := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hb_lt_rKg : b < rKg := lt_of_lt_of_le hb_lt_rmin (min_le_left _ _)
  have hb_lt_rKc2 : b < rKc2 := lt_of_lt_of_le hb_lt_rmin (min_le_right _ _)
  -- (4) instantiate the uniform annulus bounds at this `(a,b)`.
  have hGIannK := hGIann a b hb_nonneg hb_lt_rKg
  obtain ⟨Kc2, hKc20, hLapChiU⟩ := hLapAnn a b hb_nonneg hb_lt_rKc2
  -- (5) `q`-independent `Mann` (heat parametrix annulus bounds) and `Kc1` (cutoff derivative).
  obtain ⟨Mann, hMann0, hHann', hDHann'⟩ :=
    parametrixH_annulus_bounds t ht a b hb0 (foldedCoeff Θ u 0)
      hw0smooth.continuous
      (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) hw0smooth i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) hw0smooth j).continuous)
  obtain ⟨Kc1, hKc10, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  -- (6) the concrete parametrix `H = gaussDdim t · foldedCoeff` and its regularity / annulus bounds.
  have hHeq : (heatParametrix 0 Θ u t : Point n → ℝ)
      = fun y => gaussDdim t y * foldedCoeff Θ u 0 y := by
    funext x; rw [heatParametrix_folded]; simp
  have hHeqw : ∀ w : Point n,
      heatParametrix 0 Θ u t w = gaussDdim t w * foldedCoeff Θ u 0 w := fun w => congrFun hHeq w
  have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u t) := by
    rw [hHeq]; exact (gaussDdim_contDiff t).mul hw0smooth
  have hH2 : ∀ w : Point n, ContDiffAt ℝ 2 (heatParametrix 0 Θ u t) w :=
    fun w => hH.contDiffAt.of_le le_top
  have hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |heatParametrix 0 Θ u t w| ≤ Mann * gaussDdim t w := by
    intro w h1 h2; rw [hHeqw w]; exact hHann' w h1 h2
  have hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (heatParametrix 0 Θ u t) j w| ≤ Mann * (1 / t) * gaussDdim t w := by
    intro w j h1 h2; rw [hHeq]; exact hDHann' w j h1 h2
  -- (7) the SINGLE constant `B` and its nonnegativity.
  have hBnn : 0 ≤ C + Mann * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Mann * (8 / a ^ 2) := by
    have h1 : 0 ≤ Mann * Kc2 := mul_nonneg hMann0 hKc20
    have h2 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Mann * (8 / a ^ 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hKg0) hKc10) hMann0)
        (by positivity)
    linarith
  refine ⟨a, b, C + Mann * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Mann * (8 / a ^ 2),
    ha0, hab, hBnn, ?_⟩
  intro q hq v
  -- (8) per-`q`: the uniform near bound restricted to the sub-ball `rncRadialSq ≤ b² (≤ b_near²)`.
  have hb2_le : b ^ 2 ≤ bN ^ 2 := by nlinarith [hb_le_bN, hb0, hbN0]
  have hEnear_q : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
      |deriv (fun s => heatParametrix 0 Θ u s w) t
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 0 Θ u t) w|
        ≤ C * gaussDdimWide t w :=
    fun w hw => hEnearU q hq w (le_trans hw hb2_le)
  -- (9) per-`q` inverse-metric symmetry (global) and annulus bounds.
  have hgisymm_q : ∀ w i j, uniformFlowPullbackMetricInv g gi hC hK q w i j
      = uniformFlowPullbackMetricInv g gi hC hK q w j i :=
    fun w i j => uniformFlowPullbackMetricInv_symm_global g gi hC hK hgsymm q w i j
  have hgibd_q : ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |uniformFlowPullbackMetricInv g gi hC hK q w i j| ≤ Kg :=
    fun w i j h1 h2 => hGIannK q hq w h1 h2 i j
  -- (10) fire the explicit-`B` engine per `q` (same `B`), extract the bound at `v`.
  exact (cutoffResidual_global_gaussianWide_bound_explicitB
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
    (heatParametrix 0 Θ u t) (fun x => deriv (fun s => heatParametrix 0 Θ u s x) t)
    a b t ha0 hab ht hH2 hgisymm_q
    C hCnn hEnear_q Mann hMann0 hHann hDHann
    Kg Kc1 Kc2 hKg0 hKc10 hKc20 hgibd_q hDchi (hLapChiU q hq)).2 v

/-! ### C3 — the per-base-point width-2 Gaussian shape (as close to `hEboundW` as reachable). -/

/-- **★ J4-85 (C3) — THE UNIFORM CUTOFF BOUND IN `gaussDdim (2t)` (per-base-point width-2 shape).**
    The faithful restatement of C2 in the width-2 (doubled-time) Gaussian, absorbing the `(√2)ⁿ`
    prefactor of `gaussDdimWide_eq_scaled_gaussDdim` (`gaussDdimWide t v = (√2)ⁿ·gaussDdim (2t) v`) into
    the constant.  For a SINGLE annulus `(a,b)` and constant `B ≥ 0`, for every `q ∈ K`:
        `|χ(v)·∂ₜH v − Δ_g̃_q(χ·H) v| ≤ B · gaussDdim (2·t) v` .
    This is the per-base-point (over `K`) width-2 Gaussian in the RECENTERED coordinate `v` (centered at
    `0`) — exactly the SHAPE `gaussDdim (2τ)(p−q)` of the target
    `RecenterReduction.UniformPerBasePointGaussian`, with `τ = t` and `v` playing the role of `p − q`.

    HONEST FIREWALL (why this does NOT directly instantiate `hEboundW_of_uniform_perBasePoint`).  Three
    genuine gaps remain between this bound and the capstone's `E τ p q` shape:
      (i)   TIME — this is a single FIXED time `t`; the target quantifies `∀ τ > 0`;
      (ii)  BASE SET — this holds `∀ q ∈ K` (a compact set); the target is `∀ q : Point n`;
      (iii) THE `E`-IDENTIFICATION (Vmap) — the target's residual `E τ p q` lives in the ORIGINAL chart
            in `(p, q)`, whereas this bound is in the `q`-RECENTERED coordinate `v`; identifying
            `E t p q` with the cutoff residual evaluated at `v = p − q` (the base-point coordinate map
            `Vmap`) is a separate transport, not proved here.
    So this corollary is "as close as the current `E`-definition allows"; it is NOT a proof of
    `hEboundW`, and NOT `a₁ = R/6`. -/
theorem cutoffResidual_uniformFlow_uniform_gaussDdim
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    {t : ℝ} (ht : 0 < t)
    (C ρ_u : ℝ) (hCnn : 0 ≤ C) (hρ_u : 0 < ρ_u)
    (hResU : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
      |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u t v|
        ≤ C * gaussDdimWide t v) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∀ q ∈ K, ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) t
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u t y) v|
        ≤ B * gaussDdim (2 * t) v := by
  obtain ⟨a, b, B, ha0, hab, hBnn, hbd⟩ :=
    cutoffResidual_uniformFlow_uniform g gi hg hC hK hgnd hgsymm Θ u hw0smooth ht
      C ρ_u hCnn hρ_u hResU
  refine ⟨a, b, B * Real.sqrt 2 ^ n, ha0, hab, mul_nonneg hBnn (by positivity), ?_⟩
  intro q hq v
  refine le_trans (hbd q hq v) (le_of_eq ?_)
  rw [gaussDdimWide_eq_scaled_gaussDdim ht v]; ring

end QIQTH.HeatResidualBound
