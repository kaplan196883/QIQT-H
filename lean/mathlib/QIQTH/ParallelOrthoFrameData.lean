/-
  ParallelOrthoFrameData — PACKAGE the parallel orthonormal frame data
  (`he`, `hpar`, `hortho`, `hcomplete`) from a frame-transport curve.

  Step b3d-3 of the a₁=R/6 endgame.  Given the geodesic + WHOLE-FRAME parallel-transport integral
  curve `Γc : ℝ → Point n × Point n × (Fin n → Point n)` on an interval `Ioo lo hi`
  (`HasDerivAt Γc (geodesicFrameTransportField g gi (Γc s)) s`, from
  `parallelFrameTransport_local_existence`), whose components are `Γc.1` = position,
  `Γc.2.1` = velocity and `Γc.2.2 : Fin n → Point n` = the transported FRAME `{e_i}`, this file
  EXTRACTS the frame `e i := fun s => (Γc s).2.2 i` and PROVES the four pieces of frame data
  consumed by `expFlow_frame_raychaudhuri` / `frame_raychaudhuri_ricci_nhds`:

    • **he** (frame regularity): each frame component `(Γc·).2.2 i a` is differentiable at every
      interior point (its own `deriv` is a valid `HasDerivAt` value) — by projecting the frame-curve
      `HasDerivAt` through the phase-space projections.
    • **hpar** (parallelism): each frame column `(Γc·).2.2 i` has vanishing covariant derivative
      along the geodesic — DIRECT from `frameTransport_covariantDeriv_zero`.
    • **hortho** (orthonormality preserved): if the initial frame `(Γc t₀).2.2` is g-orthonormal at
      `(Γc t₀).1` (`hIC`), then `∑ₚ∑_q g(Γc s) (e_i)ₚ (e_k)_q = δ_{ik}` for every `s ∈ Ioo lo hi` —
      via `parallelPair_metricInner_eq_on_Ioo` (metric inner product constant along parallel
      transport) followed by the orthonormal initial condition.
    • **hcomplete**: `∑_i (e_i)^μ (e_i)^ν = gi(Γc s)^{μν}` pointwise on `Ioo lo hi` — by
      `gorthonormal_frame_complete` from `hortho` and the metric-inverse identity.

  All four land.  Every carried hypothesis is a GENUINE mathematical statement: the frame-curve
  `HasDerivAt` data `hΓcd`, the base-time membership `ht₀`, the metric smoothness/symmetry `hg`/
  `hgsymm`, the metric-inverse identity `hinv`, inverse-metric symmetry `hGisymm`, and the initial
  orthonormality `hIC` (a real constraint on the initial frame — not vacuous, not the conclusion).

  HONEST CAPTION (binding): this file packages the frame data ALONG `(Γc ·).1` directly.  It does
  NOT align the frame data with `expTube` (that is `frameTransport_geodesic_eq_expTube`, a separate
  lemma the caller uses to rewrite), does NOT construct the exp-flow Jacobi components `Yt`, does NOT
  discharge the van-Vleck frame data, and does NOT establish `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FrameTransportField
import QIQTH.FrameTransportParallel
import QIQTH.ParallelInnerInterval
import QIQTH.OrthonormalFrameComplete
import QIQTH.CovariantJacobi

namespace QIQTH.Geodesic

open QIQTH.Curvature QIQTH.ExpMap QIQTH.ParallelTransport
open Finset Set

set_option maxHeartbeats 1200000

variable {n : ℕ}

/-- **Package the parallel orthonormal frame data from a frame-transport curve.**

    For the geodesic + whole-frame parallel-transport integral curve `Γc` on `Ioo lo hi`
    (`hΓcd : ∀ s ∈ Ioo lo hi, HasDerivAt Γc (geodesicFrameTransportField g gi (Γc s)) s`), with
    `Γc.1` position, `Γc.2.1` velocity and `Γc.2.2 : Fin n → Point n` the transported FRAME `{e_i}`,
    and given the initial orthonormality `hIC` of `(Γc t₀).2.2` at `(Γc t₀).1`, this returns the FOUR
    frame-data pieces consumed by `frame_raychaudhuri_ricci_nhds`, all along `(Γc ·).1`:

    * `he`   — frame regularity: `HasDerivAt (fun u => (Γc u).2.2 i a) (deriv … s) s` on `Ioo lo hi`;
    * `hpar` — parallelism: `covariantDerivAlong g gi (fun u => (Γc u).1) (fun u => (Γc u).2.2 i) s = 0`;
    * `hortho` — orthonormality preserved: `∑ₚ∑_q g(Γc s) (e_i)ₚ (e_k)_q = δ_{ik}` on `Ioo lo hi`;
    * `hcomplete` — completeness: `∑_i (e_i)^μ (e_i)^ν = gi(Γc s)^{μν}` on `Ioo lo hi`.

    Does NOT align with `expTube` (separate lemma), does NOT build the exp-flow Jacobi components,
    does NOT discharge the van-Vleck frame data, and is unrelated to `a₁ = R/6`. -/
theorem parallelOrthoFrame_data (g gi : Point n → Fin n → Fin n → ℝ)
    (Γc : ℝ → Point n × Point n × (Fin n → Point n)) {lo hi t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo lo hi)
    (hΓcd : ∀ s ∈ Set.Ioo lo hi,
      HasDerivAt Γc (geodesicFrameTransportField g gi (Γc s)) s)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ s ∈ Set.Ioo lo hi, ∀ a μ,
      (∑ b, g (Γc s).1 a b * gi (Γc s).1 μ b) = if a = μ then (1 : ℝ) else 0)
    (hGisymm : ∀ s ∈ Set.Ioo lo hi, ∀ μ ν, gi (Γc s).1 μ ν = gi (Γc s).1 ν μ)
    (hIC : ∀ i k,
      (∑ p, ∑ q, g (Γc t₀).1 p q * (Γc t₀).2.2 i p * (Γc t₀).2.2 k q)
        = if i = k then (1 : ℝ) else 0) :
    -- he
    (∀ (i a : Fin n), ∀ s ∈ Set.Ioo lo hi,
        HasDerivAt (fun u => (Γc u).2.2 i a) (deriv (fun u => (Γc u).2.2 i a) s) s)
    -- hpar
    ∧ (∀ (i : Fin n), ∀ s ∈ Set.Ioo lo hi,
        covariantDerivAlong g gi (fun u => (Γc u).1) (fun u => (Γc u).2.2 i) s = 0)
    -- hortho
    ∧ (∀ (i k : Fin n), ∀ s ∈ Set.Ioo lo hi,
        (∑ p, ∑ q, g (Γc s).1 p q * (Γc s).2.2 i p * (Γc s).2.2 k q)
          = if i = k then (1 : ℝ) else 0)
    -- hcomplete
    ∧ (∀ s ∈ Set.Ioo lo hi, ∀ μ ν,
        (∑ i, (Γc s).2.2 i μ * (Γc s).2.2 i ν) = gi (Γc s).1 μ ν) := by
  -- frame-component derivative via the phase-space projections
  have hcol : ∀ (i a : Fin n), ∀ s ∈ Set.Ioo lo hi,
      HasDerivAt (fun u => (Γc u).2.2 i a)
        ((geodesicFrameTransportField g gi (Γc s)).2.2 i a) s := by
    intro i a s hs
    have hΓc := hΓcd s hs
    have he2 : HasDerivAt (fun u => (Γc u).2.2)
        ((geodesicFrameTransportField g gi (Γc s)).2.2) s := by
      have h1 := (ContinuousLinearMap.snd ℝ (Point n)
        (Point n × (Fin n → Point n))).hasFDerivAt.comp_hasDerivAt s hΓc
      have h2 := (ContinuousLinearMap.snd ℝ (Point n)
        (Fin n → Point n)).hasFDerivAt.comp_hasDerivAt s h1
      simpa using h2
    have hem : HasDerivAt (fun u => (Γc u).2.2 i)
        ((geodesicFrameTransportField g gi (Γc s)).2.2 i) s := by
      have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Point n)
        i).hasFDerivAt.comp_hasDerivAt s he2
      simpa using this
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ)
      a).hasFDerivAt.comp_hasDerivAt s hem
    simpa using this
  -- position-component derivative (value = velocity `Γc.2.1`)
  have hxP : ∀ s ∈ Set.Ioo lo hi,
      HasDerivAt (fun u => (Γc u).1) ((Γc s).2.1) s := by
    intro s hs
    have := (ContinuousLinearMap.fst ℝ (Point n)
      (Point n × (Fin n → Point n))).hasFDerivAt.comp_hasDerivAt s (hΓcd s hs)
    simpa [geodesicFrameTransportField] using this
  -- (he) frame regularity: the component is differentiable, so its own `deriv` is a valid value
  have he : ∀ (i a : Fin n), ∀ s ∈ Set.Ioo lo hi,
      HasDerivAt (fun u => (Γc u).2.2 i a) (deriv (fun u => (Γc u).2.2 i a) s) s := by
    intro i a s hs
    exact (hcol i a s hs).differentiableAt.hasDerivAt
  -- (hpar) parallelism, per column, direct from the per-column theorem
  have hpar : ∀ (i : Fin n), ∀ s ∈ Set.Ioo lo hi,
      covariantDerivAlong g gi (fun u => (Γc u).1) (fun u => (Γc u).2.2 i) s = 0 := by
    intro i s hs
    exact frameTransport_covariantDeriv_zero g gi Γc (hΓcd s hs) i
  -- metric-inverse identity in the shape `parallelPair_metricInner_eq_on_Ioo` expects
  have hinv_pp : ∀ s ∈ Set.Ioo lo hi, ∀ p q,
      (∑ σ, g (Γc s).1 p σ * gi (Γc s).1 σ q) = if p = q then (1 : ℝ) else 0 := by
    intro s hs p q
    rw [← hinv s hs p q]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [hGisymm s hs σ q]
  -- (hortho) orthonormality preserved along the interval, then the orthonormal IC at `t₀`
  have hortho : ∀ (i k : Fin n), ∀ s ∈ Set.Ioo lo hi,
      (∑ p, ∑ q, g (Γc s).1 p q * (Γc s).2.2 i p * (Γc s).2.2 k q)
        = if i = k then (1 : ℝ) else 0 := by
    intro i k s hs
    have hconst :
        (∑ p, ∑ q, g (Γc s).1 p q * (Γc s).2.2 i p * (Γc s).2.2 k q)
          = (∑ p, ∑ q, g (Γc t₀).1 p q * (Γc t₀).2.2 i p * (Γc t₀).2.2 k q) :=
      parallelPair_metricInner_eq_on_Ioo g gi hg hgsymm
        (fun u => (Γc u).1) (fun u => (Γc u).2.1)
        (fun u => (Γc u).2.2 i) (fun u => (geodesicFrameTransportField g gi (Γc u)).2.2 i)
        (fun u => (Γc u).2.2 k) (fun u => (geodesicFrameTransportField g gi (Γc u)).2.2 k)
        ht₀ hinv_pp hxP
        (fun s hs a => hcol i a s hs) (fun s hs a => hcol k a s hs)
        (fun s _ a => rfl) (fun s _ a => rfl) s hs
    rw [hconst, hIC i k]
  -- (hcomplete) completeness from orthonormality, pointwise on the interval
  have hcomplete : ∀ s ∈ Set.Ioo lo hi, ∀ μ ν,
      (∑ i, (Γc s).2.2 i μ * (Γc s).2.2 i ν) = gi (Γc s).1 μ ν := by
    intro s hs
    exact QIQTH.Curvature.gorthonormal_frame_complete (g (Γc s).1) (gi (Γc s).1)
      (fun i => (Γc s).2.2 i) (fun i k => hortho i k s hs) (hinv s hs) (hGisymm s hs)
  exact ⟨he, hpar, hortho, hcomplete⟩

end QIQTH.Geodesic
