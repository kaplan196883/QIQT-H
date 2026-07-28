/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# VanVleckRicciReduced — the van-Vleck `−Ric` radial ODE with the COORDINATE-side germs discharged

This file reduces `QIQTH.ExpMap.vanVleck_ricci_assembled` (VanVleckRicciAssembled.lean) toward
unconditional by **discharging inline every COORDINATE-side hypothesis arrow** from the repo's
exp-Jacobian smoothness/positivity bricks, leaving ONLY the FRAME-side arrows carried.

`vanVleck_ricci_assembled` exposes, at each interior ray parameter `s₀ ∈ (0, δ)`, a chain of ~17
hypothesis arrows.  Of these, the following COORDINATE-side germs (about `J = expJacobianDet`, the
ray metric `g∘exp`, and the scaled Jacobi matrix `B = s • D exp_p|_{s•v}`) are discharged HERE:

* `hγ`    ← `expMap_smul_eq_expTube` (the ray/tube identity `(expTube …)₁ = exp_p(s•v)`);
* `hGdet` ← metric determinant positivity `det(g∘exp) > 0` near the centre (from `g p` positive
  definite, `Matrix.PosDef.det_pos`, propagated by continuity of `s ↦ det(g∘exp(s•v))`);
* `hBdet` ← `det(s • D exp)= sⁿ · J > 0` (`Matrix.det_smul` + `J > 0`);
* `hpos`  ← `expJacobianDet_pos_nhds` (`J > 0` near the centre);
* `hsplit`← `logdet_gtilde_split` (pointwise `log det g̃ = 2 log J + log det(g∘exp)`);
* `hLJev`/`hLJ2` ← `log_expJacobianDet_contDiffOn_two` (`log J` is `C²`) → the ray-composition germs;
* `hLmev`/`hLm2` ← `expMap_contDiffOn_two` + `hg` (metric log-det is `C²` along the ray);
* `hLBev`/`hLB2` ← `hresc_of_pos_at` (`log det B = log J + n log s` near `s₀`) → `C²` along the ray.

The remaining CARRIED arrows are the FRAME-side ones — `hortho`, `hEdet`, `hYev`, `hLY2`, `hY2`,
`hu_ev` — plus, honestly, the radial-Jacobi link `hBV`.

## Why `hBV` is still carried (alignment note)

`radialJacobiLink_uncond` (TransverseVariationDischarge.lean) now proves `hBV` UNCONDITIONALLY for the
exp-flow columns `V j s = Φ s (0, e_j)` of `expDiff_flow_isGeodesicVariation`.  `vanVleck_h4_assembled`
(hence `vanVleck_ricci_assembled`) builds its `V` from the SAME construction, but returns it only
through an existential — the equation `V j s = Φ s (0, e_j)` is not exposed to the caller.  Without a
refactor of `vanVleck_h4_assembled` to surface that equation (or to accept `V` as data), the uncond
`hBV` cannot be aligned with the opaque `V` obtained here.  So `hBV` is dischargeable-in-principle but
is CARRIED in this reduction; discharging it needs the `(e,V)`-exposure refactor.

## What remains carried

`hY2` (C²-regularity of the frame Jacobi components), `hu_ev` (no-conjugate invertibility of the
frame Jacobi matrix), `hortho` (`g`-orthonormality of the frame), `hEdet` (`det E > 0`),
`hYev`/`hLY2` (differentiability/second-derivative of `log det Y`), and `hBV` (alignment).  All are
genuine, non-vacuous.  A reduction of `vanVleck_ricci_assembled` from ~17 arrows to 7 carried.

⚠ This is NOT the heat-kernel `a₁ = R/6` coefficient.  Axiom-free (`propext`, `Classical.choice`,
`Quot.sound` only).
-/
import Mathlib
import QIQTH.VanVleckRicciAssembled
import QIQTH.TransverseVariationDischarge
import QIQTH.ExpJacobianRegularity
import QIQTH.LogJacobianRegularity
import QIQTH.VanVleckGenericPoint
import QIQTH.VanVleckLogDetSplit
import QIQTH.ExpJacobianRescale
import QIQTH.JacobianRadial
import QIQTH.ExpMapContDiff2

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric QIQTH.JacobianDet
open QIQTH.JacobianRegularity QIQTH.JacobianRadial Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **From `C²` at a point to the two ray-derivative germs.**  If `f : ℝ → ℝ` is `C²` at `s₀`, then
    `f` is differentiable on a neighbourhood of `s₀` (`hLJev`-shape) and `deriv f` is itself
    differentiable at `s₀`, i.e. `HasDerivAt (deriv f) (deriv² f s₀) s₀` (`hLJ2`-shape).  Pure
    regularity plumbing; NONE vacuous. -/
theorem contDiffAt_two_deriv_germs {f : ℝ → ℝ} {s₀ : ℝ} (hf : ContDiffAt ℝ 2 f s₀) :
    (∀ᶠ s in nhds s₀, DifferentiableAt ℝ f s) ∧
      HasDerivAt (deriv f) (deriv (deriv f) s₀) s₀ := by
  obtain ⟨u, hUopen, hs₀u, hcd⟩ := hf.contDiffOn' (le_refl (2 : WithTop ℕ∞)) (by simp)
  rw [Set.insert_eq_of_mem (Set.mem_univ s₀), Set.univ_inter] at hcd
  have hUnhds : u ∈ nhds s₀ := hUopen.mem_nhds hs₀u
  refine ⟨?_, ?_⟩
  · have hd : DifferentiableOn ℝ f u := hcd.differentiableOn (by norm_num)
    filter_upwards [hUnhds] with s hs using (hd s hs).differentiableAt (hUopen.mem_nhds hs)
  · have hderiv_cdo : ContDiffOn ℝ 1 (deriv f) u := hcd.deriv_of_isOpen hUopen (by norm_num)
    exact ((hderiv_cdo.differentiableOn (by norm_num)).differentiableAt hUnhds).hasDerivAt

/-- **`C²` of a matrix determinant along a real curve from entrywise `C²`.**  If every entry
    `s ↦ M(s)_{ij}` is `C²` at `s₀`, then `s ↦ det (M s)` is `C²` at `s₀` (`Matrix.det_apply'` as a
    finite sum of finite products of the entries). -/
theorem contDiffAt_matrixDet {m : ℕ} {M : ℝ → Matrix (Fin m) (Fin m) ℝ} {s₀ : ℝ}
    (h : ∀ i j, ContDiffAt ℝ 2 (fun s => M s i j) s₀) :
    ContDiffAt ℝ 2 (fun s => (M s).det) s₀ := by
  simp_rw [Matrix.det_apply']
  refine ContDiffAt.sum (fun σ _ => ?_)
  refine ContDiffAt.mul contDiffAt_const ?_
  exact contDiffAt_prod (fun i _ => h (σ i) i)

/-- **The interior van-Vleck determinant `−Ric` equation with the COORDINATE-side germs discharged.**

    Same conclusion, same top-level hypotheses, and same `∃ δ, ∀ s₀ ∈ (0,δ), ∃ e V` prefix as
    `vanVleck_ricci_assembled`, but the eleven COORDINATE-side hypothesis arrows
    (`hγ`, `hGdet`, `hBdet`, `hsplit`, `hLJev`, `hLmev`, `hpos`, `hLBev`, `hLJ2`, `hLm2`, `hLB2`) are
    now discharged INLINE from the exp-Jacobian smoothness/positivity bricks.  Only the FRAME-side
    arrows (`hY2`, `hu_ev`, `hortho`, `hEdet`, `hYev`, `hLY2`) plus the radial-Jacobi link `hBV`
    (carried for the `(e,V)`-alignment reason documented above) remain.  NOT `a₁ = R/6`. -/
theorem vanVleck_ricci_reduced (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgisymm : ∀ y μ ν, gi y μ ν = gi y ν μ)
    (hginv : ∀ y a μ, (∑ b, g y a b * gi y μ b) = if a = μ then (1 : ℝ) else 0)
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    (hgpd : Matrix.PosDef (g p : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ s₀ ∈ Set.Ioo (0 : ℝ) δ,
      ∃ (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n),
        -- exposed exp-flow data `Φ` (threaded) for the downstream `hBV` discharge (`V = Φ(0,e_j)`):
        (∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
            Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
            (∀ (z : Point n × Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
                HasDerivWithinAt (fun s => Φ s z)
                  (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (Φ t z))
                  (Set.Icc (0 : ℝ) 1) t) ∧
            (∀ j s, V j s = Φ s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)))) ∧
        -- carried FRAME-side arrows (`hortho`/`hEdet` now discharged inside the engine):
        ((∀ j i, ∀ᶠ τ in nhds s₀,
            HasDerivAt (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i))
              (deriv (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i)) τ) τ) →
        (∀ᶠ s in nhds s₀,
            IsUnit (Matrix.of (fun k j =>
                frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
              : Matrix (Fin n) (Fin n) ℝ)) →
        -- carried radial-Jacobi link (discharged downstream from the Φ-data):
        (∀ᶠ s in nhds s₀, ∀ a j,
            (V j s).1 a = (s • expJacobianMat g gi hC p (s • v)) a j) →
        (∀ᶠ s in nhds s₀, DifferentiableAt ℝ (fun u => Real.log ((Matrix.of (fun k j =>
            frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k u)
              : Matrix (Fin n) (Fin n) ℝ).det)) s) →
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
              + 2 * (n : ℝ) / s₀ ^ 2) := by
  -- the assembled engine
  obtain ⟨δ, hδ, hbody⟩ := vanVleck_ricci_assembled g gi hC hg hgsymm hgisymm hginv p v hv hgpd
  -- the `C²` radius for `log J` (a metric ball around the centre in `x`-space)
  obtain ⟨rJ, hrJ, hlogJ_cdo⟩ := log_expJacobianDet_contDiffOn_two g gi hC p
  -- the ray `s ↦ s • v` is `C^∞` (pin the scalar/module types once)
  have hray_cdf : ContDiff ℝ (2 : WithTop ℕ∞) (fun s : ℝ => s • v) :=
    contDiff_id.smul contDiff_const
  -- ===== near-centre (in the ray parameter `s`) coordinate facts =====
  have hray_tendsto : Filter.Tendsto (fun s : ℝ => s • v) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun s : ℝ => s • v) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hcont.tendsto 0
  have hJ0 : ∀ᶠ s in nhds (0 : ℝ), 0 < expJacobianDet g gi hC p (s • v) :=
    hray_tendsto.eventually (expJacobianDet_pos_nhds g gi hC p)
  -- metric determinant positivity near `s = 0` (via `C²` continuity + `g p` positive definite)
  have hG0 : ∀ᶠ s in nhds (0 : ℝ),
      0 < (Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det := by
    have hcda0 : ContDiffAt ℝ 2
        (fun s : ℝ => (Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det) (0 : ℝ) := by
      have hat : ContDiffAt ℝ 2 (expMap g gi hC p) ((0 : ℝ) • v) := by
        refine (expMap_contDiffOn_two g gi hC p).contDiffAt (Metric.isOpen_ball.mem_nhds ?_)
        rw [zero_smul]; exact Metric.mem_ball_self (expRho_pos g gi hC p)
      have hexp0 : ContDiffAt ℝ 2 (fun s : ℝ => expMap g gi hC p (s • v)) (0 : ℝ) := by
        simpa only [Function.comp_def] using hat.comp (0 : ℝ) hray_cdf.contDiffAt
      refine contDiffAt_matrixDet (fun i j => ?_)
      have hij : ContDiffAt ℝ 2 (fun s : ℝ => g (expMap g gi hC p (s • v)) i j) (0 : ℝ) :=
        ((hg i j).contDiffAt.of_le le_top).comp (0 : ℝ) hexp0
      simpa only [Matrix.of_apply] using hij
    have hval : 0 < (Matrix.of fun a b => g (expMap g gi hC p ((0 : ℝ) • v)) a b).det := by
      rw [zero_smul, expMap_apply_zero]
      exact hgpd.det_pos
    exact Filter.Tendsto.eventually hcda0.continuousAt (Ioi_mem_nhds hval)
  have hrJ0 : ∀ᶠ s in nhds (0 : ℝ), (s • v) ∈ Metric.ball (0 : Point n) rJ :=
    hray_tendsto.eventually (Metric.ball_mem_nhds 0 hrJ)
  have hRho0 : ∀ᶠ s in nhds (0 : ℝ), (s • v) ∈ Metric.ball (0 : Point n) (expRho g gi hC p) :=
    hray_tendsto.eventually (Metric.ball_mem_nhds 0 (expRho_pos g gi hC p))
  have hlt1_0 : ∀ᶠ s in nhds (0 : ℝ), |s| < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with s hs
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
  have hQ0 : ∀ᶠ s in nhds (0 : ℝ),
      0 < expJacobianDet g gi hC p (s • v)
      ∧ 0 < (Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det
      ∧ (s • v) ∈ Metric.ball (0 : Point n) rJ
      ∧ (s • v) ∈ Metric.ball (0 : Point n) (expRho g gi hC p)
      ∧ |s| < 1 :=
    hJ0.and (hG0.and (hrJ0.and (hRho0.and hlt1_0)))
  obtain ⟨a, ha, haball⟩ := Metric.mem_nhds_iff.mp hQ0
  -- ===== the reduced radius and the interior point =====
  refine ⟨min δ a, lt_min hδ ha, fun s₀ hs₀ => ?_⟩
  have hmemball : s₀ ∈ Metric.ball (0 : ℝ) a := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs₀.1]
    exact lt_of_lt_of_le hs₀.2 (min_le_right δ a)
  have hQs₀ := haball hmemball
  have hballnhds : Metric.ball (0 : ℝ) a ∈ nhds s₀ := Metric.isOpen_ball.mem_nhds hmemball
  have hQnear : ∀ᶠ s in nhds s₀,
      0 < expJacobianDet g gi hC p (s • v)
      ∧ 0 < (Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det
      ∧ (s • v) ∈ Metric.ball (0 : Point n) rJ
      ∧ (s • v) ∈ Metric.ball (0 : Point n) (expRho g gi hC p)
      ∧ |s| < 1 :=
    Filter.eventually_of_mem hballnhds (fun s hs => haball hs)
  have hs₀mem : s₀ ∈ Set.Ioo (0 : ℝ) δ :=
    ⟨hs₀.1, lt_of_lt_of_le hs₀.2 (min_le_left δ a)⟩
  obtain ⟨e, V, hΦdata, hchain⟩ := hbody s₀ hs₀mem
  refine ⟨e, V, hΦdata, fun hY2 hu_ev hBV hYev hLY2 => ?_⟩
  -- ===== discharge the coordinate germs =====
  -- positivity arrows
  have hpos : ∀ᶠ s in nhds s₀, 0 < expJacobianDet g gi hC p (s • v) :=
    hQnear.mono (fun s h => h.1)
  have hGdet : ∀ᶠ s in nhds s₀,
      0 < (Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det :=
    hQnear.mono (fun s h => h.2.1)
  have hspos : ∀ᶠ s in nhds s₀, (0 : ℝ) < s :=
    Filter.eventually_of_mem (Ioi_mem_nhds hs₀.1) (fun s hs => hs)
  -- `hγ` : the ray/tube identity
  have hγ : ∀ᶠ s in nhds s₀, (expTube g gi hC p v s).1 = expMap g gi hC p (s • v) := by
    filter_upwards [hQnear] with s hs
    exact (expMap_smul_eq_expTube g gi hC p v hv.le (le_of_lt hs.2.2.2.2)).symm
  -- `hBdet` : `det (s • D exp) = sⁿ · J > 0`
  have hBdet : ∀ᶠ s in nhds s₀,
      0 < ((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det := by
    filter_upwards [hQnear, hspos] with s hs hs0
    show 0 < (s • expJacobianMat g gi hC p (s • v)).det
    rw [Matrix.det_smul, Fintype.card_fin]
    have hJ' : 0 < (expJacobianMat g gi hC p (s • v)).det := hs.1
    exact mul_pos (pow_pos hs0 n) hJ'
  -- `hsplit` : the additive log-determinant split
  have hsplit : (fun s : ℝ =>
        Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))
      =ᶠ[nhds s₀] (fun s => 2 * Real.log (expJacobianDet g gi hC p (s • v))
        + Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det)) := by
    filter_upwards [hQnear] with s hs
    exact logdet_gtilde_split g gi hC p (s • v) hs.1 hs.2.1
  -- `log J` along the ray is `C²` at `s₀`
  have hLJ_cda : ContDiffAt ℝ 2
      (fun s : ℝ => Real.log (expJacobianDet g gi hC p (s • v))) s₀ := by
    have hat : ContDiffAt ℝ 2 (fun x => Real.log (expJacobianDet g gi hC p x)) (s₀ • v) :=
      hlogJ_cdo.contDiffAt (Metric.isOpen_ball.mem_nhds hQs₀.2.2.1)
    simpa only [Function.comp_def] using hat.comp s₀ hray_cdf.contDiffAt
  -- the metric log-det along the ray is `C²` at `s₀`
  have hexp_ray : ContDiffAt ℝ 2 (fun s : ℝ => expMap g gi hC p (s • v)) s₀ := by
    have hat : ContDiffAt ℝ 2 (expMap g gi hC p) (s₀ • v) :=
      (expMap_contDiffOn_two g gi hC p).contDiffAt
        (Metric.isOpen_ball.mem_nhds hQs₀.2.2.2.1)
    simpa only [Function.comp_def] using hat.comp s₀ hray_cdf.contDiffAt
  have hLm_cda : ContDiffAt ℝ 2
      (fun s : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det)) s₀ := by
    have hdet : ContDiffAt ℝ 2
        (fun s : ℝ => (Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det) s₀ := by
      refine contDiffAt_matrixDet (fun i j => ?_)
      have hij : ContDiffAt ℝ 2 (fun s : ℝ => g (expMap g gi hC p (s • v)) i j) s₀ :=
        ((hg i j).contDiffAt.of_le le_top).comp s₀ hexp_ray
      simpa only [Matrix.of_apply] using hij
    exact hdet.log hQs₀.2.1.ne'
  -- `log det B` along the ray is `C²` at `s₀` (via the rescaling germ `log J = log det B − n log s`)
  have hresc : (fun s => Real.log (expJacobianDet g gi hC p (s • v)))
        =ᶠ[nhds s₀]
      (fun s => Real.log (((fun r => (r : ℝ) • expJacobianMat g gi hC p (r • v)) s).det)
                 - (n : ℝ) * Real.log s) :=
    hresc_of_pos_at g gi hC p v hs₀.1 hpos
  have hLB_eq : (fun s => Real.log (((fun r => (r : ℝ) • expJacobianMat g gi hC p (r • v)) s).det))
        =ᶠ[nhds s₀]
      (fun s => Real.log (expJacobianDet g gi hC p (s • v)) + (n : ℝ) * Real.log s) := by
    filter_upwards [hresc] with s hs
    linarith [hs]
  have hLB_cda : ContDiffAt ℝ 2
      (fun s => Real.log (((fun r => (r : ℝ) • expJacobianMat g gi hC p (r • v)) s).det)) s₀ := by
    have hlogs : ContDiffAt ℝ 2 (fun s : ℝ => (n : ℝ) * Real.log s) s₀ :=
      contDiffAt_const.mul (Real.contDiffAt_log.2 hs₀.1.ne')
    have hsum : ContDiffAt ℝ 2
        (fun s => Real.log (expJacobianDet g gi hC p (s • v)) + (n : ℝ) * Real.log s) s₀ :=
      hLJ_cda.add hlogs
    exact hsum.congr_of_eventuallyEq hLB_eq
  -- the six differentiability / second-derivative germs from the three `C²` facts
  obtain ⟨hLJev, hLJ2⟩ := contDiffAt_two_deriv_germs hLJ_cda
  obtain ⟨hLmev, hLm2⟩ := contDiffAt_two_deriv_germs hLm_cda
  obtain ⟨hLBev, hLB2⟩ := contDiffAt_two_deriv_germs hLB_cda
  -- ===== assemble =====
  exact hchain hY2 hu_ev hγ hBV hGdet hBdet hsplit hLJev hLmev hpos hLBev hYev
    hLJ2 hLm2 hLB2 hLY2

end QIQTH.ExpMap
