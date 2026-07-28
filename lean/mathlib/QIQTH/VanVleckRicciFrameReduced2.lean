/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# VanVleckRicciFrameReduced2 — the van-Vleck `−Ric` radial ODE with `hu_ev` and `hYev` discharged,
  reducing the interior conditional to the single deep primitive `hY2` (frame `C²`) plus `hLY2`.

`vanVleck_ricci_frame_reduced` (VanVleckRicciFrameReduced.lean) proves the interior van-Vleck `−Ric`
radial ODE at each `s₀ ∈ (0, δ)` for a concrete exposed frame `(e, V)`, CONDITIONAL on four carried
frame-side arrows: `hY2` (`C²`-regularity of the frame Jacobi components), `hu_ev` (the frame Jacobi
matrix `Y` is a unit near `s₀`), `hYev` (differentiability of `log det Y` near `s₀`), and `hLY2`
(the second-derivative germ of `log det Y`).

This file DISCHARGES TWO of those four — `hu_ev` and `hYev` — from the concrete exposed frame data,
reducing the interior conditional to just `{hY2, hLY2}`:

* `hu_ev` — invertibility of the frame Jacobi matrix `Y_{kj} = ⟨V_j, e_k⟩_g`.  With `B := s·D exp`,
  `G := g∘exp`, `E := (e_i^a)`, one has `Y = (Bᵀ G E)ᵀ`, so `det Y = det B · det G · det E`.
  `g`-orthonormality of `e` gives `(det E)²·det G = 1` (`gorthonormal_det_sq`), hence `det E ≠ 0` and
  `det G ≠ 0`; `det B = sⁿ·det(D exp) > 0` (`det_smul` + `expJacobianDet_pos_nhds`, `s > 0`).  So
  `det Y ≠ 0`, i.e. `IsUnit Y` (`Matrix.isUnit_iff_isUnit_det`), on a neighbourhood of `s₀`.

* `hYev` — differentiability of `log det Y`.  The frame Jacobi matrix is `C¹` near `s₀`
  (`frameComponentMatrix_hasDerivAt`, fed the entrywise `C¹` of `g∘γ` (chain rule from `hg`), of `V`
  (the exp differential flow `Φ`), and of `e` (the exposed frame regularity `he`)); combined with
  `hu_ev`, the log-determinant potential has a derivative at each nearby `s`
  (`raychaudhuri_logdet_firstderiv`), hence is differentiable there.

The remaining carried arrows are `hY2` (the genuine 2nd-order `C²`-regularity of the frame Jacobi
components) and `hLY2` (the second-derivative germ of `log det Y`, which folds from `hY2` + `hu_ev`
by the same log-det matrix calculus).  The frame orthonormality `hortho` and `C¹` regularity `he` are
surfaced by the (now enriched) `vanVleck_ricci_reduced` existential; the radial-Jacobi link `hBV` is
discharged here from the exp-flow `Φ`-data (as in `vanVleck_ricci_frame_reduced`).

⚠ This is NOT the heat-kernel `a₁ = R/6` coefficient.  Axiom-free (`propext`, `Classical.choice`,
`Quot.sound` only).
-/
import Mathlib
import QIQTH.VanVleckRicciReduced
import QIQTH.TransverseVariationDischarge
import QIQTH.FrameComponentsDeriv
import QIQTH.RaychaudhuriLogDet
import QIQTH.OrthonormalFrameDet
import QIQTH.ExpJacobianRescale
import QIQTH.JacobianRadial
import QIQTH.JacobianDet

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric QIQTH.JacobianDet
open QIQTH.JacobianRegularity QIQTH.JacobianRadial Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **The interior van-Vleck determinant `−Ric` radial ODE with `hu_ev` and `hYev` discharged.**

    Same conclusion and `∃ δ, ∀ s₀ ∈ (0,δ), ∃ e V` prefix as `vanVleck_ricci_frame_reduced`, but the
    frame-Jacobi invertibility `hu_ev` and the log-det differentiability `hYev` are now DISCHARGED
    from the concrete frame data (`hortho`/`he`, surfaced by the enriched `vanVleck_ricci_reduced`),
    the exp-Jacobian positivity bricks, and `raychaudhuri_logdet_firstderiv`.  Only the two genuine
    regularity arrows remain carried:

    * `hY2`  — `C²`-regularity of the frame Jacobi components;
    * `hLY2` — the second-derivative germ of `log det Y` at `s₀` (folds from `hY2` + `hu_ev`).

    NOT `a₁ = R/6`. -/
theorem vanVleck_ricci_frame_reduced2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgisymm : ∀ y μ ν, gi y μ ν = gi y ν μ)
    (hginv : ∀ y a μ, (∑ b, g y a b * gi y μ b) = if a = μ then (1 : ℝ) else 0)
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    (hgpd : Matrix.PosDef (g p : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ s₀ ∈ Set.Ioo (0 : ℝ) δ,
      ∃ (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n),
        -- carried FRAME-side arrows (`hu_ev`/`hYev` are now discharged, alongside `hBV`/`hortho`/`hEdet`):
        (∀ j i, ∀ᶠ τ in nhds s₀,
            HasDerivAt (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i))
              (deriv (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i)) τ) τ) →
        (HasDerivAt (deriv (fun s : ℝ => Real.log ((Matrix.of (fun k j =>
            frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
              : Matrix (Fin n) (Fin n) ℝ).det)))
          (deriv (deriv (fun s : ℝ => Real.log ((Matrix.of (fun k j =>
            frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
              : Matrix (Fin n) (Fin n) ℝ).det))) s₀) s₀) →
          deriv (deriv (fun s : ℝ =>
              Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))) s₀
            = - 2 * (∑ σ, ∑ ν, ricci g gi σ ν (expTube g gi hC p v s₀).1
                    * (expTube g gi hC p v s₀).2 σ * (expTube g gi hC p v s₀).2 ν)
              - 2 * (((Matrix.of (fun k j =>
                      deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k) s₀))
                    * (Matrix.of (fun k j =>
                      frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s₀))⁻¹)
                  * ((Matrix.of (fun k j =>
                      deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k) s₀))
                    * (Matrix.of (fun k j =>
                      frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s₀))⁻¹)).trace
              + 2 * (n : ℝ) / s₀ ^ 2 := by
  -- the frame-reduced engine (now surfacing the frame data `hortho`/`he` and the exp-flow `Φ`-data)
  obtain ⟨δ, hδ, hbody⟩ := vanVleck_ricci_reduced g gi hC hg hgsymm hgisymm hginv p v hv hgpd
  -- a positivity radius in the ray parameter `s` for `J = det (D exp) > 0`
  have hray_tendsto : Filter.Tendsto (fun s : ℝ => s • v) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun s : ℝ => s • v) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hcont.tendsto 0
  have hJ0 : ∀ᶠ s in nhds (0 : ℝ), 0 < expJacobianDet g gi hC p (s • v) :=
    hray_tendsto.eventually (expJacobianDet_pos_nhds g gi hC p)
  obtain ⟨a, ha, haball⟩ := Metric.mem_nhds_iff.mp hJ0
  -- the reduced radius, confined into `(0,1)` and the positivity ball
  refine ⟨min δ (min a 1), lt_min hδ (lt_min ha one_pos), fun s₀ hs₀ => ?_⟩
  have hs₀δ : s₀ ∈ Set.Ioo (0 : ℝ) δ :=
    ⟨hs₀.1, lt_of_lt_of_le hs₀.2 (min_le_left _ _)⟩
  have hs₀lt1 : s₀ < 1 :=
    lt_of_lt_of_le hs₀.2 (le_trans (min_le_right δ (min a 1)) (min_le_right a 1))
  have hs₀balla : s₀ < a :=
    lt_of_lt_of_le hs₀.2 (le_trans (min_le_right δ (min a 1)) (min_le_left a 1))
  have hs₀abs1 : |s₀| < 1 := abs_lt.mpr ⟨by linarith [hs₀.1], hs₀lt1⟩
  -- the exposed frame data + exp-flow `Φ`-data + carried chain
  obtain ⟨e, V, hortho_ev, he, hΦdata, hchain⟩ := hbody s₀ hs₀δ
  obtain ⟨Φ, hΦ0, hflow, hVeq⟩ := hΦdata
  -- ===== near-`s₀` coordinate germs (`hpos`, `hγ`, `hBdet`) =====
  have hmemball : s₀ ∈ Metric.ball (0 : ℝ) a := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs₀.1]; exact hs₀balla
  have hpos : ∀ᶠ s in nhds s₀, 0 < expJacobianDet g gi hC p (s • v) :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hmemball) (fun s hs => haball hs)
  have hlt1 : ∀ᶠ s in nhds s₀, |s| < 1 :=
    Filter.eventually_of_mem ((isOpen_lt continuous_abs continuous_const).mem_nhds hs₀abs1)
      (fun s hs => hs)
  have hγ : ∀ᶠ s in nhds s₀, (expTube g gi hC p v s).1 = expMap g gi hC p (s • v) := by
    filter_upwards [hlt1] with s hs
    exact (expMap_smul_eq_expTube g gi hC p v hv.le hs.le).symm
  have hspos : ∀ᶠ s in nhds s₀, (0 : ℝ) < s :=
    Filter.eventually_of_mem (Ioi_mem_nhds hs₀.1) (fun s hs => hs)
  have hBdet : ∀ᶠ s in nhds s₀,
      0 < ((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det := by
    filter_upwards [hpos, hspos] with s hp hs0
    show 0 < (s • expJacobianMat g gi hC p (s • v)).det
    rw [Matrix.det_smul, Fintype.card_fin]
    have hp' : 0 < (expJacobianMat g gi hC p (s • v)).det := hp
    exact mul_pos (pow_pos hs0 n) hp'
  -- ===== the radial-Jacobi link `hBV` from the surfaced `Φ`-data =====
  have hBV : ∀ᶠ s in nhds s₀, ∀ a j,
      (V j s).1 a = (s • expJacobianMat g gi hC p (s • v)) a j := by
    have hlink := radialJacobiLink_of_tubeTransverseVariation g gi hC p v hv hs₀abs1 Φ
      (by
        filter_upwards [Ioo_mem_nhds hs₀.1 hs₀lt1] with s hs_ioo w
        have hs_icc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs_ioo.1.le, hs_ioo.2.le⟩
        have hphase := tubeTransverse_hasDerivAt_phase g gi hC p v hv Φ hΦ0 hflow hs_icc w
        have hc := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt 0 hphase
        simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', Prod.fst] using hc)
    filter_upwards [hlink] with s hs a j
    rw [hVeq j s]; exact hs a j
  -- ===== discharge `hu_ev` : `IsUnit Y` near `s₀` from `det Y = det B · det G · det E ≠ 0` =====
  have hu_ev : ∀ᶠ s in nhds s₀,
      IsUnit (Matrix.of (fun k j =>
          frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
        : Matrix (Fin n) (Fin n) ℝ) := by
    filter_upwards [hγ, hBV, hortho_ev, hBdet] with s hγs hBVs horthos hBdets
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    set Bmat : Matrix (Fin n) (Fin n) ℝ := s • expJacobianMat g gi hC p (s • v) with hBmat
    set Gmat : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.of (fun a b => g (expMap g gi hC p (s • v)) a b) with hGmat
    set Emat : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun a i => e i s a) with hEmat
    set Ymat : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.of (fun k j => frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
      with hYmat
    -- (1) orthonormality in matrix form: `Eᵀ G E = 1`
    have hE1 : Ematᵀ * Gmat * Emat = 1 := by
      ext i k
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hEmat, hGmat, Matrix.of_apply,
        Matrix.one_apply]
      rw [← horthos i k]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    -- (2) `Y = (Bᵀ G E)ᵀ`
    have hYM : Ymat = (Bmatᵀ * Gmat * Emat)ᵀ := by
      ext k j
      rw [Matrix.transpose_apply, Matrix.mul_apply]
      simp only [hYmat, Matrix.of_apply, frameComponent, Matrix.mul_apply, Matrix.transpose_apply,
        hGmat, hEmat]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hγs, hBVs b j]
      ring
    -- (3) `det Y = det B · det G · det E`
    have hdetY : Ymat.det = Bmat.det * Gmat.det * Emat.det := by
      rw [hYM, Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    -- (4) the metric factor `(det E)² · det G = 1` ⟹ `det E ≠ 0`, `det G ≠ 0`
    have hsq : (Emat.det) ^ 2 * Gmat.det = 1 := gorthonormal_det_sq Gmat Emat hE1
    have hGne : Gmat.det ≠ 0 := by
      intro h; rw [h, mul_zero] at hsq; exact one_ne_zero hsq.symm
    have hEne : Emat.det ≠ 0 := by
      intro h; rw [h] at hsq; simp at hsq
    have hBne : Bmat.det ≠ 0 := hBdets.ne'
    -- (5) assemble
    rw [hdetY]
    exact mul_ne_zero (mul_ne_zero hBne hGne) hEne
  -- ===== eventual entrywise `C¹` of `g∘γ`, `V`, `e` → matrix `C¹` of `Y` (`hYmat_ev`) =====
  have he_ev : ∀ᶠ τ in nhds s₀, ∀ (i b : Fin n),
      HasDerivAt (fun s => e i s b) (deriv (fun s => e i s b) τ) τ :=
    Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun b => he i b))
  have hV_ev : ∀ᶠ τ in nhds s₀, ∀ (j a : Fin n),
      HasDerivAt (fun s => (V j s).1 a) (deriv (fun s => (V j s).1 a) τ) τ := by
    filter_upwards [Ioo_mem_nhds hs₀.1 hs₀lt1] with τ hτ j a
    have hΦτ : HasDerivAt (fun s => (Φ s) ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)))
        (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v τ)
          ((Φ τ) ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)))) τ :=
      (hflow ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)) τ
        (Set.mem_Icc.mpr ⟨hτ.1.le, hτ.2.le⟩)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
    have hproj := ((ContinuousLinearMap.proj a).comp
        (ContinuousLinearMap.fst ℝ (Point n) (Point n))).hasFDerivAt.comp_hasDerivAt τ hΦτ
    have hVrw : (fun s => (V j s).1 a)
        = (fun s => ((ContinuousLinearMap.proj a).comp
            (ContinuousLinearMap.fst ℝ (Point n) (Point n)))
            ((Φ s) ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)))) := by
      funext s
      simp only [hVeq j s, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.proj_apply]
    have hkey : HasDerivAt (fun s => (V j s).1 a)
        (((ContinuousLinearMap.proj a).comp (ContinuousLinearMap.fst ℝ (Point n) (Point n)))
          (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v τ)
            ((Φ τ) ((0 : Point n), (Pi.single j (1 : ℝ) : Point n))))) τ := by
      rw [hVrw]
      simpa only [Function.comp_def] using hproj
    rw [hkey.deriv]; exact hkey
  have hg_ev : ∀ᶠ τ in nhds s₀, ∀ (a b : Fin n),
      HasDerivAt (fun s => g ((expTube g gi hC p v s).1) a b)
        (deriv (fun s => g ((expTube g gi hC p v s).1) a b) τ) τ := by
    filter_upwards [Ioo_mem_nhds (show (-2 : ℝ) < s₀ by linarith [hs₀.1])
        (show s₀ < (2 : ℝ) by linarith [hs₀lt1])] with τ hτ a b
    have hposd : HasDerivAt (fun u => (expTube g gi hC p v u).1)
        ((expTube g gi hC p v τ).2) τ := by
      have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ
        ((expTube_spec g gi hC p v hv.le).2.1 τ hτ)
      simpa [geodesicField] using this
    have hgf : HasFDerivAt (fun y => g y a b)
        (fderiv ℝ (fun y => g y a b) (expTube g gi hC p v τ).1) (expTube g gi hC p v τ).1 :=
      ((hg a b).differentiable (by simp)).differentiableAt.hasFDerivAt
    have hcomp := hgf.comp_hasDerivAt τ hposd
    have hkey : HasDerivAt (fun s => g ((expTube g gi hC p v s).1) a b)
        (fderiv ℝ (fun y => g y a b) (expTube g gi hC p v τ).1
          ((expTube g gi hC p v τ).2)) τ := by
      simpa only [Function.comp_def] using hcomp
    rw [hkey.deriv]; exact hkey
  have hYmat_ev : ∀ᶠ s in nhds s₀,
      HasDerivAt
        (fun u => (Matrix.of (fun k j =>
            frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k u)
          : Matrix (Fin n) (Fin n) ℝ))
        (Matrix.of (fun k j =>
          deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k) s)) s := by
    filter_upwards [hg_ev, hV_ev, he_ev] with s h1 h2 h3
    exact frameComponentMatrix_hasDerivAt g (fun u => (expTube g gi hC p v u).1) e V h1 h2 h3
  -- ===== discharge `hYev` : `log det Y` differentiable near `s₀` (`raychaudhuri_logdet_firstderiv`) =====
  have hYev : ∀ᶠ s in nhds s₀, DifferentiableAt ℝ (fun u => Real.log ((Matrix.of (fun k j =>
      frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k u)
        : Matrix (Fin n) (Fin n) ℝ).det)) s := by
    filter_upwards [hYmat_ev, hu_ev] with s hd hu
    exact (raychaudhuri_logdet_firstderiv
      (fun u => (Matrix.of (fun k j =>
          frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k u)
        : Matrix (Fin n) (Fin n) ℝ))
      (fun u => (Matrix.of (fun k j =>
          deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k) u)
        : Matrix (Fin n) (Fin n) ℝ))
      hd hu).differentiableAt
  -- ===== assemble: feed the discharged `hu_ev`, `hBV`, `hYev`; carry only `hY2`/`hLY2` =====
  exact ⟨e, V, fun hY2 hLY2 => hchain hY2 hu_ev hBV hYev hLY2⟩

end QIQTH.ExpMap
