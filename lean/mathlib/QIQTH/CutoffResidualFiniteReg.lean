/-
  CutoffResidualFiniteReg — the FINITE-REGULARITY (`ContDiffAt ℝ 2`) global cutoff-parametrix
  residual bound.

  Brick R2 of the RECENTER campaign (docs/qg_roadmap/RECENTER_CAMPAIGN_PLAN.md) toward the
  unconditional `a₁ = R/6` heat-kernel coefficient.  The existing global cutoff-residual bound
  `QIQTH.HeatResidualBound.cutoffResidual_global_gaussianWide_bound`
  (`QIQTH/CutoffResidualGlobalBound.lean`) demands the parametrix profile `H` to be `ContDiff ℝ ∞`.
  The q-centered pullback-metric parametrix (`expPullbackMetric`) is only `ContDiffOn ℝ 2` on the
  injectivity ball, so the global bound must be re-provable at finite (`C²`) regularity.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHY THE PORT IS MECHANICAL.  The only place `ContDiff ℝ ∞ H` enters the ∞ proof is through the
  Laplace–Beltrami Leibniz split `laplaceBeltrami_mul_inf` (three call sites: near / annulus / far).
  R1 (`QIQTH.LaplaceBeltrami.laplaceBeltrami_mul_C2`, `QIQTH/LaplaceBeltramiFiniteReg.lean`) supplies
  the identical conclusion from `ContDiffAt ℝ 2 f x` + `ContDiffAt ℝ 2 h x` — no metric-regularity
  hypothesis — so we simply swap the three calls, feeding `hH2 v : ContDiffAt ℝ 2 H v` for `H` and
  `(radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)` for the (still smooth)
  cutoff.

  The region-vanishing facts `laplaceBeltrami_radialCutoff_zero_near`/`_far` and the cutoff derivative
  identities `pd_radialCutoff_eq_zero_of_near`/`_far` never used `H` smoothness, so they are reused
  verbatim from the imported ∞ file.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  We also supply the reusable bridge `contDiffAt_two_of_contDiffOn_two`
  (`ContDiffOn ℝ 2 f s → IsOpen s → x ∈ s → ContDiffAt ℝ 2 f x`), which later R-bricks use to feed the
  q-centered `expPullbackMetric` (`ContDiffOn ℝ 2` on the open exp-ball) into this pointwise-`ContDiffAt 2`
  residual chain.

  The weakened hypothesis is `hH2 : ∀ w, ContDiffAt ℝ 2 H w` (pointwise `C²`).  All carried
  hypotheses are genuine and load-bearing exactly as in the ∞ version.  No `sorry`, no new axioms,
  no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CutoffResidualGlobalBound
import QIQTH.LaplaceBeltramiFiniteReg

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### Reusable bridge: open-set `ContDiffOn ℝ 2` ⟹ pointwise `ContDiffAt ℝ 2`. -/

/-- **Bridge lemma.**  On an OPEN set, `ContDiffOn ℝ 2` at every point yields the pointwise
    `ContDiffAt ℝ 2` fact.  This feeds a `ContDiffOn ℝ 2` parametrix (e.g. `expPullbackMetric` on the
    open exp-ball) into the pointwise-`ContDiffAt 2` residual chain below. -/
theorem contDiffAt_two_of_contDiffOn_two {f : Point n → ℝ} {s : Set (Point n)}
    (hf : ContDiffOn ℝ 2 f s) (hs : IsOpen s) {x : Point n} (hx : x ∈ s) :
    ContDiffAt ℝ 2 f x :=
  hf.contDiffAt (hs.mem_nhds hx)

/-! ### ★ The global cutoff-parametrix residual bound at `C²` (F1, diagonal chart). -/

/-- **★ THE GLOBAL CUTOFF-PARAMETRIX RESIDUAL BOUND AT `C²` (F1, diagonal chart).**  The
    finite-regularity analogue of `cutoffResidual_global_gaussianWide_bound`: the `ContDiff ℝ ∞ H`
    hypothesis is weakened to the pointwise `hH2 : ∀ w, ContDiffAt ℝ 2 H w`.  Same conclusion — the
    heat-operator residual of the cutoff parametrix `χ·H` is GLOBALLY dominated by a constant times
    the width-2 Gaussian:

      `∃ B ≥ 0, ∀ v, |χ(v)·dtH v − Δ_g(χ·H) v| ≤ B · gaussDdimWide t v` .

    The proof is the ∞ region split with the three `laplaceBeltrami_mul_inf` calls swapped for the
    `C²` Leibniz rule `laplaceBeltrami_mul_C2` (R1), fed `hH2 v` and the still-smooth cutoff.  All
    carried hypotheses are genuine and load-bearing exactly as in the ∞ version. -/
theorem cutoffResidual_global_gaussianWide_bound_C2
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
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Point n,
      |radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v|
        ≤ B * gaussDdimWide t v := by
  -- the three pieces of the constant `B` (unchanged from the ∞ version)
  have hb2 : 0 ≤ M * Kc2 := mul_nonneg hM hKc2
  have hcoef : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M := by positivity
  have hb3 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2) := by positivity
  refine ⟨C + M * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2), by linarith, ?_⟩
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

/-- **The base-kernel form at `C²` (width-2 `hEboundW` shape).**  Finite-regularity analogue of
    `cutoffResidual_global_baseKernelW_bound`: rewrites the `C²` global cutoff residual bound through
    `gaussDdimWide t v = √2ⁿ · baseKernelW 2 0 t v 0`. -/
theorem cutoffResidual_global_baseKernelW_bound_C2
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
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Point n,
      |radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v|
        ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by
  obtain ⟨B, hBnn, hBd⟩ := cutoffResidual_global_gaussianWide_bound_C2 g gi H dtH a b t ha hab ht hH2
    hgisymm C hCnn hEnear M hM hHann hDHann Kg Kc1 Kc2 hKg hKc1 hKc2 hgibd hDchi hLapChi
  refine ⟨B * Real.sqrt 2 ^ n, by positivity, fun v => ?_⟩
  calc |radialCutoff a b v * dtH v
        - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v|
      ≤ B * gaussDdimWide t v := hBd v
    _ = B * (Real.sqrt 2 ^ n * baseKernelW (2 : ℝ) (0 : ℝ) t v 0) := by
        rw [gaussDdimWide_eq_scaled_baseKernelW ht v]
    _ = (B * Real.sqrt 2 ^ n) * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by ring

end QIQTH.HeatResidualBound
