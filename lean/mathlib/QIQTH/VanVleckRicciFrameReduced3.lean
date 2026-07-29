/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# VanVleckRicciFrameReduced3 — the van-Vleck `−Ric` radial ODE with `hY2` discharged, carrying ONLY `hLY2`

`vanVleck_ricci_frame_reduced2` (VanVleckRicciFrameReduced2.lean) proves the interior van-Vleck `−Ric`
radial ODE at each `s₀ ∈ (0, δ)` for an exposed frame `(e, V)`, carrying the two genuine frame-side
regularity arrows `(hY2)→(hLY2)→⟨van-Vleck −Ric⟩`, where

* `hY2`  — the frame Jacobi components are `C²` near `s₀` (each named first derivative has a derivative);
* `hLY2` — the second-derivative germ of `log det Y` at `s₀` (folds from `hY2` + `hu_ev`).

This file DISCHARGES `hY2` outright, reducing the carried conditional to just `{hLY2}`.

## Mechanism

The engine chain (`vanVleck_h4_assembled` → `vanVleck_ricci_assembled` → `vanVleck_ricci_reduced` →
`vanVleck_ricci_frame_reduced2`) was enriched (Option A threading, mirroring the earlier `he`
threading) to SURFACE, through each `∃ e V` existential, the frame construction data needed to build
`hY2` from the just-landed `C²` capstone `frameComponent_hY2_of_frameData`
(FrameComponentsSecondDeriv.lean):

* `he`   — frame `C¹` regularity (already surfaced);
* `Φ`-data (`Φ 0 = id`, the `[0,1]` Jacobi law, `V = Φ(0,e_j)`) — already surfaced for `hBV`;
* `hpar` — frame parallelism `covariantDerivAlong g gi γ (e i) = 0` near `s₀` — NEWLY surfaced here,
  from `parallelFrame_expTube_exists` in the assembly.

Feeding `(g, gi, hC, hg, p, v, hv, s₀∈(0,1), e, V, Φ, hflow, hVeq, he, hpar)` into
`frameComponent_hY2_of_frameData` produces exactly the `hY2` germ carried by
`vanVleck_ricci_frame_reduced2`.  Discharging it leaves the single carried arrow `hLY2`.

This is the penultimate step to `(b)`-closure (van-Vleck `−Ric` unconditional): only `hLY2` — the
second-derivative germ of `log det Y`, which folds from `hY2` + `hu_ev` by the log-det matrix
calculus — remains.

⚠ This is NOT the heat-kernel `a₁ = R/6` coefficient.  Axiom-free (`propext`, `Classical.choice`,
`Quot.sound` only).
-/
import Mathlib
import QIQTH.VanVleckRicciFrameReduced2
import QIQTH.FrameComponentsSecondDeriv

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-- **The interior van-Vleck determinant `−Ric` radial ODE with `hY2` discharged, carrying ONLY
    `hLY2`.**

    Same conclusion and `∃ δ, ∀ s₀ ∈ (0,δ), ∃ e V` prefix as `vanVleck_ricci_frame_reduced2`, but the
    frame-`C²` arrow `hY2` is now DISCHARGED from the frame construction data surfaced by the enriched
    engine chain (frame `C¹` `he`, exp-flow `Φ`-data, frame parallelism `hpar`) via the `C²` capstone
    `frameComponent_hY2_of_frameData`.  Only the second-derivative germ of `log det Y` remains carried:

    * `hLY2` — `HasDerivAt (deriv (log det Y)) (deriv² (log det Y) s₀) s₀`, which folds from
      `hY2` + `hu_ev` by the log-det matrix calculus.

    Penultimate step to unconditional van-Vleck `−Ric`; NOT `a₁ = R/6`. -/
theorem vanVleck_ricci_frame_reduced3 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgisymm : ∀ y μ ν, gi y μ ν = gi y ν μ)
    (hginv : ∀ y a μ, (∑ b, g y a b * gi y μ b) = if a = μ then (1 : ℝ) else 0)
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    (hgpd : Matrix.PosDef (g p : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ s₀ ∈ Set.Ioo (0 : ℝ) δ,
      ∃ (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n),
        -- carried FRAME-side arrow (`hY2` is now discharged): only `hLY2` remains:
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
  -- the frame-reduced2 engine (now surfacing `he` / `Φ`-data / `hpar`)
  obtain ⟨δ, hδ, hbody⟩ :=
    vanVleck_ricci_frame_reduced2 g gi hC hg hgsymm hgisymm hginv p v hv hgpd
  -- confine into the geodesic interior `(0,1)` so the `C²` capstone applies
  refine ⟨min δ 1, lt_min hδ one_pos, fun s₀ hs₀ => ?_⟩
  have hs₀δ : s₀ ∈ Set.Ioo (0 : ℝ) δ :=
    ⟨hs₀.1, lt_of_lt_of_le hs₀.2 (min_le_left δ 1)⟩
  have hs₀1 : s₀ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hs₀.1, lt_of_lt_of_le hs₀.2 (min_le_right δ 1)⟩
  -- the surfaced frame data + the carried `(hY2)→(hLY2)→⟨van-Vleck −Ric⟩` arrow
  obtain ⟨e, V, he, hΦdata, hpar, hchain⟩ := hbody s₀ hs₀δ
  obtain ⟨Φ, hΦ0, hflow, hVeq⟩ := hΦdata
  -- build `hY2` from the frame construction data via the `C²` capstone
  have hY2 : ∀ j i, ∀ᶠ τ in nhds s₀,
      HasDerivAt (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i))
        (deriv (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i)) τ) τ :=
    frameComponent_hY2_of_frameData g gi hC hg p v hv hs₀1 e V Φ hflow hVeq he hpar
  -- feed `hY2`; carry only `hLY2`
  exact ⟨e, V, fun hLY2 => hchain hY2 hLY2⟩

end QIQTH.ExpMap
