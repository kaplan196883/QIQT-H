/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The van-Vleck `h4` with the FRAME DATA discharged: `d²(log det Y) s₀ = −Ric − Sh`.

This is the CULMINATING `h4` assembly.  It instantiates the general `h4`-producer
`expFlow_frame_h4` (ExpFlowFrameH4.lean) at an interior parameter `s₀ ∈ (0, δ)` and DISCHARGES,
from already-landed bricks, all of the frame data and first-order regularity that `expFlow_frame_h4`
carries as hypotheses:

* the parallel orthonormal frame `e` and its data (`he`, `hpar`, `hortho`, `hcomplete`, `hinv`)
  come from `parallelFrame_expTube_exists` (ParallelFrameExpTube.lean);
* the Jacobi variation `V` (columns of the exp differential flow `Φ`) and its variational property
  `hVar` come from `expDiff_flow_isGeodesicVariation` (ExpDiffVariation.lean), upgraded from the
  within-`[0,1]` derivative to a genuine `HasDerivAt` germ at the interior `s₀`;
* the frame Jacobi components `Yt := frameComponent g γ e V` and their first-order regularity
  (`hY`, `hYmat`, `hYmat_ev`) come from `frameComponent_hasDerivAt` / `frameComponentMatrix_hasDerivAt`
  (FrameComponentsDeriv.lean), fed the entrywise `HasDerivAt` facts of `g∘γ` (chain rule from `hg` +
  `expTube_spec`), of `V` (the exp flow, projected to a component), and of `e` (frame regularity);
* the frame-reconstruction identity `hexp` comes from `frameComponents_hexp` (FrameComponentsHexp.lean).

What remains CARRIED are exactly the genuine 2nd-order regularity `hY2` (each component has a second
derivative near `s₀`) and the no-conjugate invertibility `hu_ev` (the frame Jacobi matrix is a unit
near `s₀`).  From these the point-level `hu`, `hYmat` and the 2nd-derivative matrix `hY'mat` are
assembled internally.  Both carried hypotheses are honest math facts (C² regularity and
invertibility of the Jacobi matrix), NOT the conclusion; neither is vacuous.

## Honest scope

The output
```
  d²/ds² (log det Y) s₀ = −Ric(γ',γ') − tr(Θ²)
```
holds with the FRAME DATA no longer assumed (frame existence + Jacobi variation + frame components +
first-order regularity all provided).  This is the penultimate step to unconditional van-Vleck `−Ric`.
It is NOT yet the coordinate van-Vleck determinant feed (`vanVleck_ray_secondDeriv_ricci_at`), and it
is NOT `a₁ = R/6`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.ExpFlowFrameH4
import QIQTH.ParallelFrameExpTube
import QIQTH.FrameComponentsHexp
import QIQTH.FrameComponentsDeriv
import QIQTH.ExpDiffVariation
import QIQTH.ExpJacobianRescale
import QIQTH.OrthonormalFrameDet
import QIQTH.JacobianDet

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.JacobianDet Finset Matrix
open scoped Topology Matrix.Norms.Elementwise

set_option maxHeartbeats 2000000

variable {n : ℕ}

/-- **The van-Vleck `h4` with the frame data discharged.**

    For a smooth symmetric metric `g` with symmetric inverse `gi` (a genuine matrix inverse), a base
    point `p`, and `‖v‖ < expRho`, there is a radius `δ > 0` such that at every interior parameter
    `s₀ ∈ (0, δ)` there are a parallel orthonormal frame `e` and an exp-flow Jacobi variation `V`
    (the columns of the exponential differential flow) for which, given ONLY

    * `hY2` — each frame Jacobi component has a second derivative near `s₀` (genuine C² regularity), and
    * `hu_ev` — the frame Jacobi matrix `Yt = frameComponent g γ e V` is invertible near `s₀`
      (the no-conjugate-point condition),

    the second derivative of the log-determinant potential equals `−Ric − Sh`:
    ```
      d²/ds² (log det Y) s₀
        = −∑_{σν} Ric_{σν}(γ s₀) γ'^σ γ'^ν
          − tr( (Y' Y⁻¹) (Y' Y⁻¹) )   (s₀).
    ```

    All frame data (`he`/`hpar`/`hortho`/`hcomplete`/`hinv`), the Jacobi variation (`hVar`), the frame
    components (`hexp`), and first-order regularity (`hY`/`hYmat`) are DISCHARGED internally from
    `parallelFrame_expTube_exists`, `expDiff_flow_isGeodesicVariation`, `frameComponents_hexp`,
    `frameComponent_hasDerivAt` / `frameComponentMatrix_hasDerivAt`.  Penultimate step to
    unconditional van-Vleck `−Ric`; NOT the coordinate van-Vleck feed, NOT `a₁ = R/6`. -/
theorem vanVleck_h4_assembled (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgisymm : ∀ y μ ν, gi y μ ν = gi y ν μ)
    (hginv : ∀ y a μ, (∑ b, g y a b * gi y μ b) = if a = μ then (1 : ℝ) else 0)
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    (hgpd : Matrix.PosDef (g p : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ s₀ ∈ Set.Ioo (0 : ℝ) δ,
      ∃ (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n),
        -- exposed FRAME-side facts, discharged internally (orthonormality, frame det ≠ 0):
        (∀ᶠ s in nhds s₀, ∀ i k,
            (∑ a, ∑ b, g (expMap g gi hC p (s • v)) a b * e i s a * e k s b)
              = if i = k then (1 : ℝ) else 0) ∧
        (∀ᶠ s in nhds s₀,
            (Matrix.of (fun a i => e i s a) : Matrix (Fin n) (Fin n) ℝ).det ≠ 0) ∧
        -- exposed frame `C¹` data (`e` is `C¹` along the ray) for a downstream `hu_ev`/`hYev` discharge:
        (∀ i a, ∀ᶠ τ in nhds s₀,
            HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ) ∧
        -- exposed frame PARALLELISM `hpar` (`covariantDerivAlong g gi γ (e i) = 0` near `s₀`), for a
        -- downstream `hY2` (frame `C²`) discharge via `frameComponent_hY2_of_frameData`:
        (∀ i, ∀ᶠ τ in nhds s₀,
            covariantDerivAlong g gi (fun τ => (expTube g gi hC p v τ).1) (e i) τ = 0) ∧
        -- exposed exp-flow data `Φ` (with `Φ 0 = id`, the `[0,1]` Jacobi law, and `V = Φ(0,e_j)`):
        -- this surfaces enough to discharge the radial-Jacobi link `hBV` in a downstream file
        -- (`radialJacobiLink_of_tubeTransverseVariation`), which cannot be imported here (cycle).
        (∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
            Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
            (∀ (z : Point n × Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
                HasDerivWithinAt (fun s => Φ s z)
                  (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (Φ t z))
                  (Set.Icc (0 : ℝ) 1) t) ∧
            (∀ j s, V j s = Φ s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)))) ∧
        ((∀ j i, ∀ᶠ τ in nhds s₀,
            HasDerivAt (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i))
              (deriv (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i)) τ) τ) →
        (∀ᶠ s in nhds s₀,
            IsUnit (Matrix.of (fun k j =>
                frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
              : Matrix (Fin n) (Fin n) ℝ)) →
          deriv (deriv (fun s => Real.log
              ((Matrix.of (fun k j =>
                  frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
                : Matrix (Fin n) (Fin n) ℝ).det))) s₀
            = -(∑ σ, ∑ ν, ricci g gi σ ν (expTube g gi hC p v s₀).1
                    * (expTube g gi hC p v s₀).2 σ * (expTube g gi hC p v s₀).2 ν)
              - (((Matrix.of (fun k j =>
                      deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k) s₀))
                    * (Matrix.of (fun k j =>
                      frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s₀))⁻¹)
                  * ((Matrix.of (fun k j =>
                      deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k) s₀))
                    * (Matrix.of (fun k j =>
                      frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s₀))⁻¹)).trace) := by
  classical
  -- (1) the parallel orthonormal frame + full frame data along the exp geodesic
  obtain ⟨δ, e, hδpos, hdata⟩ :=
    parallelFrame_expTube_exists g gi hC hg hgsymm hgisymm hginv p v (le_of_lt hv) hgpd
  -- (2) the exp differential flow `Φ` and its geodesic-variation column law on `[0,1]`
  obtain ⟨Φ, hΦ0, hFD, hflow⟩ := expDiff_flow_isGeodesicVariation g gi hC p v hv
  -- the exp-flow Jacobi variation columns and the geodesic base curve
  set V : Fin n → ℝ → Point n × Point n :=
    fun j s => (Φ s) ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)) with hVdef
  set γ : ℝ → Point n := fun u => (expTube g gi hC p v u).1 with hγdef
  -- the component-`a`-of-`.1` projection continuous-linear map
  set projFst : Fin n → ((Point n × Point n) →L[ℝ] ℝ) :=
    fun a => (ContinuousLinearMap.proj a).comp (ContinuousLinearMap.fst ℝ (Point n) (Point n))
    with hprojFst
  refine ⟨min δ 1, lt_min hδpos one_pos, ?_⟩
  intro s₀ hs₀
  -- `s₀` lies both in the transport window `(-δ, δ)` and the geodesic-interior window `(0,1)`
  have hs₀δ : s₀ ∈ Set.Ioo (-δ) δ :=
    ⟨by have := hs₀.1; linarith [hδpos], lt_of_lt_of_le hs₀.2 (min_le_left δ 1)⟩
  have hs₀1 : s₀ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hs₀.1, lt_of_lt_of_le hs₀.2 (min_le_right δ 1)⟩
  have hs₀2 : s₀ ∈ Set.Ioo (-2 : ℝ) 2 :=
    ⟨by linarith [hs₀1.1], by linarith [hs₀1.2]⟩
  -- the frame data at `s₀`
  obtain ⟨he, hpar, hortho, hcomplete, hinv⟩ := hdata s₀ hs₀δ
  -- ===== discharge the exposed frame-side facts (orthonormality, det E ≠ 0) + surface Φ-data =====
  -- `hortho_ev` : `g`-orthonormality of the frame in the `expMap` form, near `s₀`
  have hortho_ev : ∀ᶠ s in nhds s₀, ∀ i k,
      (∑ a, ∑ b, g (expMap g gi hC p (s • v)) a b * e i s a * e k s b)
        = if i = k then (1 : ℝ) else 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hs₀δ, Ioo_mem_nhds hs₀1.1 hs₀1.2] with s hsδ hs01 i k
    have hs1 : |s| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hs01.1], by linarith [hs01.2]⟩
    rw [expMap_smul_eq_expTube g gi hC p v hv.le hs1]
    exact (hdata s hsδ).2.2.1 i k
  -- `hEdet` : `det E ≠ 0`, from `Eᵀ G E = 1` (`gorthonormal_det_sq`)
  have hEdet : ∀ᶠ s in nhds s₀,
      (Matrix.of (fun a i => e i s a) : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 := by
    filter_upwards [hortho_ev] with s hs
    set Emat : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun a i => e i s a) with hEmatd
    set Gmat : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.of (fun a b => g (expMap g gi hC p (s • v)) a b) with hGmatd
    have hE1 : Ematᵀ * Gmat * Emat = 1 := by
      ext i k
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hEmatd, hGmatd, Matrix.of_apply,
        Matrix.one_apply]
      rw [← hs i k]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hsq := gorthonormal_det_sq Gmat Emat hE1
    intro hzero
    rw [hzero] at hsq
    simp at hsq
  -- `Φ-data` : the exp-flow, with `V = Φ(0,e_j)` (surfaced for the downstream `hBV` discharge)
  have hΦdata : ∃ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      (∀ (z : Point n × Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivWithinAt (fun s => Φ' s z)
            (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (Φ' t z))
            (Set.Icc (0 : ℝ) 1) t) ∧
      (∀ j s, V j s = Φ' s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n))) :=
    ⟨Φ, hΦ0, hflow, fun j s => by simp only [hVdef]⟩
  refine ⟨e, V, hortho_ev, hEdet, he, hpar, hΦdata, fun hY2 hu_ev => ?_⟩
  -- ===== the Jacobi variation property `hVar` (interior upgrade of the exp-flow column law) =====
  have hVar : ∀ j, ∀ᶠ τ in nhds s₀,
      IsGeodesicVariationAt g gi (expTube g gi hC p v) (V j) τ := by
    intro j
    refine Filter.eventually_of_mem (Ioo_mem_nhds hs₀1.1 hs₀1.2) (fun τ hτ => ?_)
    have hwithin := hflow ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)) τ
      (Set.mem_Icc.mpr ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩)
    exact hwithin.hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
  -- ===== eventual entrywise `HasDerivAt` of `g∘γ`, `V`, `e` near `s₀` =====
  -- `e` regularity: swap `∀ (finite)` past `∀ᶠ`
  have he_ev : ∀ᶠ τ in nhds s₀, ∀ (i b : Fin n),
      HasDerivAt (fun s => e i s b) (deriv (fun s => e i s b) τ) τ :=
    Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun b => he i b))
  -- `V` regularity: interior upgrade of the exp flow, projected to a coordinate of `.1`
  have hV_ev : ∀ᶠ τ in nhds s₀, ∀ (j a : Fin n),
      HasDerivAt (fun s => (V j s).1 a) (deriv (fun s => (V j s).1 a) τ) τ := by
    filter_upwards [Ioo_mem_nhds hs₀1.1 hs₀1.2] with τ hτ j a
    have hΦτ : HasDerivAt (fun s => (Φ s) ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)))
        (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v τ)
          ((Φ τ) ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)))) τ :=
      (hflow ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)) τ
        (Set.mem_Icc.mpr ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
    have hproj := (projFst a).hasFDerivAt.comp_hasDerivAt τ hΦτ
    have hkey : HasDerivAt (fun s => (V j s).1 a)
        ((projFst a) (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v τ)
          ((Φ τ) ((0 : Point n), (Pi.single j (1 : ℝ) : Point n))))) τ := by
      simpa only [hVdef, hprojFst, Function.comp_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply] using hproj
    rw [hkey.deriv]; exact hkey
  -- `g∘γ` regularity: chain rule from `hg` and the position part of the geodesic ODE
  have hg_ev : ∀ᶠ τ in nhds s₀, ∀ (a b : Fin n),
      HasDerivAt (fun s => g (γ s) a b) (deriv (fun s => g (γ s) a b) τ) τ := by
    filter_upwards [Ioo_mem_nhds hs₀2.1 hs₀2.2] with τ hτ a b
    have hpos : HasDerivAt (fun u => (expTube g gi hC p v u).1)
        ((expTube g gi hC p v τ).2) τ := by
      have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ
        ((expTube_spec g gi hC p v (le_of_lt hv)).2.1 τ hτ)
      simpa [geodesicField] using this
    have hgf : HasFDerivAt (fun y => g y a b)
        (fderiv ℝ (fun y => g y a b) (expTube g gi hC p v τ).1) (expTube g gi hC p v τ).1 :=
      ((hg a b).differentiable (by simp)).differentiableAt.hasFDerivAt
    have hcomp := hgf.comp_hasDerivAt τ hpos
    have hkey : HasDerivAt (fun s => g (γ s) a b)
        (fderiv ℝ (fun y => g y a b) (expTube g gi hC p v τ).1 ((expTube g gi hC p v τ).2)) τ := by
      simpa only [hγdef, Function.comp_def] using hcomp
    rw [hkey.deriv]; exact hkey
  -- combined eventual regularity bundle near `s₀`
  have hreg : ∀ᶠ τ in nhds s₀,
      (∀ a b, HasDerivAt (fun s => g (γ s) a b) (deriv (fun s => g (γ s) a b) τ) τ)
      ∧ (∀ j a, HasDerivAt (fun s => (V j s).1 a) (deriv (fun s => (V j s).1 a) τ) τ)
      ∧ (∀ i b, HasDerivAt (fun s => e i s b) (deriv (fun s => e i s b) τ) τ) := by
    filter_upwards [hg_ev, hV_ev, he_ev] with τ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- ===== first-order component regularity `hY`, matrix regularity `hYmat`(`_ev`) =====
  have hY : ∀ j i, ∀ᶠ τ in nhds s₀,
      HasDerivAt (frameComponent g γ e V j i)
        (deriv (frameComponent g γ e V j i) τ) τ := by
    intro j i
    filter_upwards [hreg] with τ hτ
    exact frameComponent_hasDerivAt_deriv g γ e V hτ.1 hτ.2.1 hτ.2.2 j i
  have hYmat_ev : ∀ᶠ s in nhds s₀,
      HasDerivAt
        (fun u => (Matrix.of (fun k j => frameComponent g γ e V j k u) : Matrix (Fin n) (Fin n) ℝ))
        (Matrix.of (fun k j => deriv (frameComponent g γ e V j k) s)) s := by
    filter_upwards [hreg] with s hs
    exact frameComponentMatrix_hasDerivAt g γ e V hs.1 hs.2.1 hs.2.2
  have hYmat := hYmat_ev.self_of_nhds
  -- ===== the 2nd-derivative matrix `hY'mat`, assembled from the carried entrywise `hY2` =====
  have hY'mat : HasDerivAt
      (fun s => (Matrix.of (fun k j => deriv (frameComponent g γ e V j k) s)
        : Matrix (Fin n) (Fin n) ℝ))
      (Matrix.of (fun k j => deriv (deriv (frameComponent g γ e V j k)) s₀)) s₀ := by
    refine hasDerivAt_pi.mpr (fun k => hasDerivAt_pi.mpr (fun j => ?_))
    exact (hY2 j k).self_of_nhds
  -- ===== the frame-reconstruction identity `hexp` =====
  have hIoo : Set.Ioo (-δ) δ ∈ nhds s₀ := isOpen_Ioo.mem_nhds hs₀δ
  have hcomplete_ev : ∀ᶠ s in nhds s₀, ∀ μ ν, (∑ i, e i s μ * e i s ν) = gi (γ s) μ ν := by
    filter_upwards [hIoo] with s hs μ ν
    exact (hdata s hs).2.2.2.1 μ ν
  have hinv_ev : ∀ᶠ s in nhds s₀, ∀ a μ,
      (∑ b, g (γ s) a b * gi (γ s) μ b) = if a = μ then (1 : ℝ) else 0 := by
    filter_upwards [hIoo] with s hs a μ
    exact (hdata s hs).2.2.2.2 a μ
  have hgisymm_ev : ∀ᶠ s in nhds s₀, ∀ p' q, gi (γ s) p' q = gi (γ s) q p' := by
    filter_upwards with s p' q using hgisymm (γ s) p' q
  have hexp : ∀ j,
      (fun s => fun a => ∑ i, frameComponent g γ e V j i s * e i s a)
        =ᶠ[nhds s₀] (fun s => (V j s).1) :=
    fun j => frameComponents_hexp g gi γ e V hcomplete_ev hinv_ev hgisymm_ev j
  -- ===== assemble via the general `h4`-producer =====
  exact expFlow_frame_h4 g gi hC hgsymm p v hv hs₀1 V hVar e
    (fun j i => frameComponent g γ e V j i) hY hY2 he hpar hortho hcomplete hinv hexp
    hYmat hY'mat hu_ev.self_of_nhds hYmat_ev hu_ev

end QIQTH.ExpMap
