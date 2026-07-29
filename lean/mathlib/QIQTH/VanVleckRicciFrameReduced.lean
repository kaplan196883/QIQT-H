/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# VanVleckRicciFrameReduced — the van-Vleck `−Ric` radial ODE with a CONCRETE exposed frame `(e,V)`,
  discharging the frame-side arrows `hBV`/`hortho`/`hEdet` and reducing to `{hY2, hu_ev, hYev, hLY2}`.

`vanVleck_ricci_reduced` (VanVleckRicciReduced.lean) proves the interior van-Vleck `−Ric` radial ODE
at each `s₀ ∈ (0, δ)` for a frame `(e, V)` returned through an existential, CONDITIONAL on the
frame-side arrows `hY2`, `hu_ev`, `hBV`, `hYev`, `hLY2` (with the COORDINATE-side germs already
discharged there, and `hortho`/`hEdet` discharged inside `vanVleck_h4_assembled`).

The one frame-side arrow that could not be discharged inside the engine chain is the radial-Jacobi
link `hBV` (`(V j s)₁_a = (s • D exp_p|_{s•v})_{aj}`): the machinery that proves it unconditionally
(`radialJacobiLink_of_tubeTransverseVariation`, via `RadialJacobiLink`) sits DOWNSTREAM of
`VanVleckRicciAssembled` in the import DAG, so it cannot be invoked inside the engine (an import
cycle).  To bridge this, `vanVleck_h4_assembled` now SURFACES the exp-flow data `Φ` — with
`Φ 0 = id`, the `[0,1]` Jacobi law, and the column identity `V j s = Φ s (0, e_j)` — threaded
through `vanVleck_ricci_assembled` and `vanVleck_ricci_reduced`.

This file, living downstream of BOTH the engine and the radial-Jacobi machinery, consumes that
`Φ`-data and DISCHARGES `hBV` outright (`tubeTransverse_hasDerivAt_phase` +
`radialJacobiLink_of_tubeTransverseVariation`, aligned to the engine's own `V` via `V = Φ(0,e_j)`).

## What remains carried

After this file, the interior van-Vleck `−Ric` radial ODE is CONDITIONAL only on the two deep
frame-Jacobi primitives plus the two log-det regularity germs:

* `hY2`   — each frame Jacobi component has a second derivative near `s₀` (`C²`-regularity);
* `hu_ev` — the frame Jacobi matrix is a unit near `s₀` (no conjugate point);
* `hYev`  — `log det Y` is differentiable near `s₀`;
* `hLY2`  — `deriv (log det Y)` is differentiable at `s₀` (its second-derivative germ).

`hYev`/`hLY2` are ordinary log-det regularity of the frame Jacobi matrix (derivable in principle
from `hY2`+`hu_ev`, but carried here — the genuine 2nd-order matrix-calculus of `log det` is not yet
in this chain); `hY2`/`hu_ev` are the two deep smooth-dependence / no-conjugate primitives.  The
three frame-side arrows `hBV`, `hortho`, `hEdet` are now ALL discharged (`hortho`/`hEdet` inside the
engine, `hBV` here).

⚠ This is NOT the heat-kernel `a₁ = R/6` coefficient.  Axiom-free (`propext`, `Classical.choice`,
`Quot.sound` only).
-/
import Mathlib
import QIQTH.VanVleckRicciReduced
import QIQTH.TransverseVariationDischarge

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric QIQTH.JacobianDet Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-- **The interior van-Vleck determinant `−Ric` radial ODE with a concrete exposed frame `(e,V)` and
    the radial-Jacobi link `hBV` discharged.**

    Same conclusion and `∃ δ, ∀ s₀ ∈ (0,δ), ∃ e V` prefix as `vanVleck_ricci_reduced`, but the
    frame-side radial-Jacobi link `hBV` is now DISCHARGED (from the exp-flow `Φ`-data surfaced by
    `vanVleck_h4_assembled`, via `radialJacobiLink_of_tubeTransverseVariation`), in addition to the
    orthonormality `hortho` and frame-determinant `hEdet` arrows already discharged inside the
    engine.  Only the four genuine frame-side regularity arrows remain carried:

    * `hY2`   — `C²`-regularity of the frame Jacobi components;
    * `hu_ev` — no-conjugate invertibility of the frame Jacobi matrix;
    * `hYev`  — differentiability of `log det Y` near `s₀`;
    * `hLY2`  — the second-derivative germ of `log det Y` at `s₀`.

    NOT `a₁ = R/6`. -/
theorem vanVleck_ricci_frame_reduced (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgisymm : ∀ y μ ν, gi y μ ν = gi y ν μ)
    (hginv : ∀ y a μ, (∑ b, g y a b * gi y μ b) = if a = μ then (1 : ℝ) else 0)
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    (hgpd : Matrix.PosDef (g p : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ s₀ ∈ Set.Ioo (0 : ℝ) δ,
      ∃ (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n),
        -- carried FRAME-side arrows (`hBV`/`hortho`/`hEdet` are now all discharged):
        (∀ j i, ∀ᶠ τ in nhds s₀,
            HasDerivAt (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i))
              (deriv (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i)) τ) τ) →
        (∀ᶠ s in nhds s₀,
            IsUnit (Matrix.of (fun k j =>
                frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
              : Matrix (Fin n) (Fin n) ℝ)) →
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
              + 2 * (n : ℝ) / s₀ ^ 2 := by
  -- the reduced engine (COORDINATE germs + `hortho`/`hEdet` already discharged; `hBV` still carried,
  -- but the exp-flow `Φ`-data is surfaced)
  obtain ⟨δ, hδ, hbody⟩ := vanVleck_ricci_reduced g gi hC hg hgsymm hgisymm hginv p v hv hgpd
  -- restrict to the geodesic interior `(0,1)` so the radial-Jacobi link applies
  refine ⟨min δ 1, lt_min hδ one_pos, fun s₀ hs₀ => ?_⟩
  have hs₀δ : s₀ ∈ Set.Ioo (0 : ℝ) δ :=
    ⟨hs₀.1, lt_of_lt_of_le hs₀.2 (min_le_left δ 1)⟩
  have hs₀1 : s₀ < 1 := lt_of_lt_of_le hs₀.2 (min_le_right δ 1)
  obtain ⟨e, V, _hortho, _he, _hpar, hΦdata, hchain⟩ := hbody s₀ hs₀δ
  obtain ⟨Φ, hΦ0, hflow, hVeq⟩ := hΦdata
  -- ===== discharge the radial-Jacobi link `hBV` from the surfaced `Φ`-data =====
  have hBV : ∀ᶠ s in nhds s₀, ∀ a j,
      (V j s).1 a = (s • expJacobianMat g gi hC p (s • v)) a j := by
    have hlink := radialJacobiLink_of_tubeTransverseVariation g gi hC p v hv
      (show |s₀| < 1 from abs_lt.mpr ⟨by linarith [hs₀.1], hs₀1⟩) Φ
      (by
        filter_upwards [Ioo_mem_nhds hs₀.1 hs₀1] with s hs_ioo w
        have hs_icc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs_ioo.1.le, hs_ioo.2.le⟩
        have hphase := tubeTransverse_hasDerivAt_phase g gi hC p v hv Φ hΦ0 hflow hs_icc w
        have hc := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt 0 hphase
        simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', Prod.fst] using hc)
    filter_upwards [hlink] with s hs a j
    rw [hVeq j s]; exact hs a j
  -- ===== assemble: feed `hBV` (discharged) alongside the carried `hY2`/`hu_ev`/`hYev`/`hLY2` =====
  exact ⟨e, V, fun hY2 hu_ev hYev hLY2 => hchain hY2 hu_ev hBV hYev hLY2⟩

end QIQTH.ExpMap
