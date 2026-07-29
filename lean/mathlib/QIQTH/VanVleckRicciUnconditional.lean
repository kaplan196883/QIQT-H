/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# VanVleckRicciUnconditional — ★ THE (b)-CLOSER: the van-Vleck `−Ric` radial ODE, FULLY UNCONDITIONAL

★ **The (b)-closer.**  The van-Vleck / Raychaudhuri `−Ric` radial ODE on the real coordinate
exp-Jacobian,

  `deriv²[log det g̃(s•v)]|_{s₀} = −2·Ric(u,u) − 2·tr((Y'Y⁻¹)²) + 2n/s₀²`,

is now proven **fully unconditional** at every interior ray parameter `s₀ ∈ (0,δ)`: all frame
construction data, all regularity germs, and the no-conjugate invertibility are discharged, and the
theorem carries NO hypothesis arrows beyond the top-level metric hypotheses
(`g`, `gi`, smoothness `hC`/`hg`, symmetry, inverse relation, `‖v‖ < expRho`, `g p` positive
definite).

## What this file discharges — the last arrow `hLY2`

`vanVleck_ricci_frame_reduced3` (VanVleckRicciFrameReduced3.lean) reduced the interior conditional to
the SINGLE carried arrow

* `hLY2` — the second-derivative germ of `log det Y` at `s₀`
  (`HasDerivAt (deriv (log det Y)) (deriv² (log det Y) s₀) s₀`).

This file folds `hLY2` from the frame `C²` regularity plus the frame-Jacobi invertibility.  Because
the frame Jacobi components are only known to be **twice-differentiable germs** (`C2germ`) — the
variation factor `V.1` comes from the coordinate Jacobi ODE and the frame factor `e` from the
parallel-transport ODE, both established through `HasDerivAt` facts rather than continuity of the
second derivative — the discharge goes through the `C2germ` calculus of `FrameComponentsSecondDeriv`,
NOT through `ContDiffAt ℝ 2`:

* a small `C2germ` product/determinant/log calculus (`c2germ_prod`, `c2germ_matrixDet`,
  `c2germ_log`) lifts the entrywise frame `C2germ` to a `C2germ` of `log det Y` (given `det Y ≠ 0`);
* `det Y s₀ ≠ 0` comes from the no-conjugate invertibility `hu_ev`
  (`det Y = det B · det G · det E ≠ 0`, orthonormality + `J > 0`);
* the `hLY2`-shaped `HasDerivAt` is the pointwise value of that `C2germ` at `s₀`.

Because `vanVleck_ricci_frame_reduced3` hides the frame data (`Φ`/`he`/`hpar`) and the orthonormality
(`hortho`) needed to build both ingredients, the discharge is done at the level of
`vanVleck_ricci_reduced`, which surfaces all of it; the intermediate arrows `hY2` (frame `C²`,
`frameComponent_hY2_of_frameData`), `hu_ev`/`hYev`/`hBV` (as in `vanVleck_ricci_frame_reduced2`) are
re-discharged inline, and the final `hLY2` closes the chain.

This closes the **(b)-side of `a₁ = R/6` duality wall #1** (the van-Vleck `−Ric` radial ODE).

⚠ This is NOT yet `a₁ = R/6` itself: that additionally needs the `(c)`-side M5 `O(1/t)` and M6
curvature-expansion layers.  Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.VanVleckRicciFrameReduced3
import QIQTH.FrameComponentsSecondDeriv
import QIQTH.VanVleckRicciReduced

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric QIQTH.JacobianDet
open QIQTH.JacobianRegularity QIQTH.JacobianRadial Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ### A small `C2germ` product / determinant / log calculus

`FrameComponentsSecondDeriv.lean` supplies `C2germ` (twice-differentiable germ: differentiable near
`s₀` with a differentiable derivative near `s₀`) closed under `+`, `·`, and finite `∑`.  Here we add
the closures needed to push a `C2germ` through `Matrix.det` and `Real.log`. -/

/-- The constant function has a `C²` germ. -/
theorem c2germ_const {c : ℝ} {s₀ : ℝ} : C2germ (fun _ : ℝ => c) s₀ :=
  c2germ_of_contDiffAt contDiffAt_const

/-- `C²` germs are closed under left multiplication by a constant. -/
theorem C2germ.const_mul {c : ℝ} {f : ℝ → ℝ} {s₀ : ℝ} (hf : C2germ f s₀) :
    C2germ (fun s => c * f s) s₀ :=
  C2germ.mul c2germ_const hf

/-- `C²` germs are closed under finite products. -/
theorem c2germ_prod {ι : Type*} {f : ι → ℝ → ℝ} {s₀ : ℝ} (s : Finset ι)
    (h : ∀ i, C2germ (f i) s₀) : C2germ (fun x => ∏ i ∈ s, f i x) s₀ := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.prod_empty] using (c2germ_const (c := (1 : ℝ)) (s₀ := s₀))
  | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h a).mul ih

/-- **`C²` of a matrix determinant along a real curve from entrywise `C²` germs.**  The determinant
    is a finite sum (`Matrix.det_apply'`) of constant-scaled finite products of the entries; the
    `C2germ` calculus lifts entrywise `C²` germs to a `C²` germ of `det`. -/
theorem c2germ_matrixDet {m : ℕ} {M : ℝ → Matrix (Fin m) (Fin m) ℝ} {s₀ : ℝ}
    (h : ∀ i j, C2germ (fun s => M s i j) s₀) :
    C2germ (fun s => (M s).det) s₀ := by
  simp_rw [Matrix.det_apply']
  refine C2germ.sum Finset.univ (fun σ => ?_)
  exact (c2germ_prod Finset.univ (fun i => h (σ i) i)).const_mul

/-- **`C²` germs are closed under `Real.log` at a nonvanishing point.**  If `h` is a `C²` germ at
    `s₀` and `h s₀ ≠ 0`, then `Real.log ∘ h` is a `C²` germ at `s₀`.  Part 1 uses `DifferentiableAt.log`
    (with `h ≠ 0` near `s₀` from continuity); part 2 rewrites `deriv (log ∘ h) = (deriv h)/h` near
    `s₀` (from `HasDerivAt.log`) and uses `DifferentiableAt.div` on `deriv h / h`. -/
theorem c2germ_log {h : ℝ → ℝ} {s₀ : ℝ} (hh : C2germ h s₀) (hne : h s₀ ≠ 0) :
    C2germ (fun s => Real.log (h s)) s₀ := by
  have hcont : ContinuousAt h s₀ := hh.1.self_of_nhds.continuousAt
  have hne_ev : ∀ᶠ τ in nhds s₀, h τ ≠ 0 := hcont.eventually_ne hne
  refine ⟨?_, ?_⟩
  · filter_upwards [hh.1, hne_ev] with τ hdτ hnτ using hdτ.log hnτ
  · have hpt : ∀ᶠ σ in nhds s₀, deriv (fun s => Real.log (h s)) σ = deriv h σ / h σ := by
      filter_upwards [hh.1, hne_ev] with σ hdσ hnσ
      exact (hdσ.hasDerivAt.log hnσ).deriv
    filter_upwards [eventually_eventually_nhds.2 hpt, hh.1, hh.2, hne_ev]
      with τ heqτ hdτ hd2τ hnτ
    exact (hd2τ.div hdτ hnτ).congr_of_eventuallyEq heqτ

/-! ### ★ The fully unconditional van-Vleck `−Ric` radial ODE -/

/-- **★ THE (b)-CLOSER — the van-Vleck `−Ric` radial ODE, FULLY UNCONDITIONAL.**

    At every interior ray parameter `s₀ ∈ (0,δ)` there is an exposed frame `(e, V)` for which the
    coordinate exp-Jacobian log-determinant satisfies the van-Vleck / Raychaudhuri `−Ric` radial ODE

      `deriv²[log det g̃(s•v)]|_{s₀}
         = −2·Ric(u,u) − 2·tr((Y'Y⁻¹)²) + 2n/s₀²`,

    with `Y` the frame Jacobi matrix.  The statement carries NO hypothesis arrows beyond the
    top-level metric hypotheses.  Every frame-side arrow — `hY2` (frame `C²`), `hu_ev`
    (no-conjugate invertibility), `hBV` (radial-Jacobi link), `hYev` (log-det differentiability),
    and the last arrow `hLY2` (the second-derivative germ of `log det Y`) — is discharged inline.

    This closes the `(b)`-side of `a₁ = R/6` duality wall #1.  NOT `a₁ = R/6` itself. -/
theorem vanVleck_ricci_unconditional (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgisymm : ∀ y μ ν, gi y μ ν = gi y ν μ)
    (hginv : ∀ y a μ, (∑ b, g y a b * gi y μ b) = if a = μ then (1 : ℝ) else 0)
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    (hgpd : Matrix.PosDef (g p : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ s₀ ∈ Set.Ioo (0 : ℝ) δ,
      ∃ (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n),
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
  -- the reduced engine (surfaces `hortho`, `he`, `hpar`, exp-flow `Φ`-data; carries the 5-arrow chain)
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
  have hs₀ioo : s₀ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs₀.1, hs₀lt1⟩
  -- the exposed frame data + exp-flow `Φ`-data + carried chain
  obtain ⟨e, V, hortho_ev, he, hpar, hΦdata, hchain⟩ := hbody s₀ hs₀δ
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
  -- ===== discharge `hYev` : `log det Y` differentiable near `s₀` =====
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
  -- ===== discharge `hY2` : the frame Jacobi components are `C²` (frame construction data) =====
  have hY2 : ∀ j i, ∀ᶠ τ in nhds s₀,
      HasDerivAt (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i))
        (deriv (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i)) τ) τ :=
    frameComponent_hY2_of_frameData g gi hC hg p v hv hs₀ioo e V Φ hflow hVeq he hpar
  -- ===== discharge the LAST arrow `hLY2` : the 2nd-derivative germ of `log det Y` =====
  -- entrywise frame `C²` germs (the `C2germ` underlying `hY2`)
  have hentryC2 : ∀ j i,
      C2germ (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i) s₀ := by
    intro j i
    refine frameComponent_c2germ g (fun u => (expTube g gi hC p v u).1) e V j i ?_ ?_ ?_
    · exact fun a b => gComp_expTube_c2germ g gi hC hg p v hv hs₀abs1 a b
    · exact fun a => frameVarComp_c2germ g gi hC p v hs₀ioo Φ hflow V hVeq j a
    · exact fun b => parallelFrameComp_c2germ g gi hC p v hv hs₀abs1 e he hpar i b
  -- `det Y` is a `C²` germ at `s₀`
  have hdetC2 : C2germ (fun s : ℝ => ((Matrix.of (fun k j =>
      frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
        : Matrix (Fin n) (Fin n) ℝ).det)) s₀ := by
    refine c2germ_matrixDet (fun i j => ?_)
    simp only [Matrix.of_apply]
    exact hentryC2 j i
  -- `det Y s₀ ≠ 0` from the no-conjugate invertibility `hu_ev`
  have hdet_ne : ((Matrix.of (fun k j =>
      frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s₀)
        : Matrix (Fin n) (Fin n) ℝ).det) ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu_ev.self_of_nhds)
  -- `log det Y` is a `C²` germ at `s₀`
  have hlogC2 : C2germ (fun s : ℝ => Real.log ((Matrix.of (fun k j =>
      frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
        : Matrix (Fin n) (Fin n) ℝ).det)) s₀ :=
    c2germ_log hdetC2 hdet_ne
  -- `hLY2` = the pointwise `HasDerivAt` value of that `C²` germ at `s₀`
  have hLY2 : HasDerivAt (deriv (fun s : ℝ => Real.log ((Matrix.of (fun k j =>
        frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
          : Matrix (Fin n) (Fin n) ℝ).det)))
      (deriv (deriv (fun s : ℝ => Real.log ((Matrix.of (fun k j =>
        frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
          : Matrix (Fin n) (Fin n) ℝ).det))) s₀) s₀ :=
    hlogC2.2.self_of_nhds.hasDerivAt
  -- ===== assemble the fully-applied chain: NO carried arrows remain =====
  exact ⟨e, V, hchain hY2 hu_ev hBV hYev hLY2⟩

end QIQTH.ExpMap
