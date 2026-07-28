/-
  # A parallel orthonormal frame exists along the exp geodesic `expTube` (step M2b-2)

  This file DISCHARGES the "frame existence" input that `FrameRaychaudhuri.lean`
  (`frame_raychaudhuri_ricci_nhds`) currently CARRIES as hypotheses: it constructs an explicit
  frame `e : Fin n → ℝ → Point n` and proves, on a neighbourhood of `0`, the FULL frame data in
  exactly the shapes that consumer needs, all evaluated along the exponential geodesic
  `expTube g gi hC p v`:

    * `he`        — frame regularity (`HasDerivAt` of each component, eventually near the point);
    * `hpar`      — parallelism `covariantDerivAlong g gi (fun τ => (expTube … τ).1) (e i) τ = 0`
                    (eventually near the point);
    * `hortho`    — orthonormality `∑ₐ∑_b g(expTube…).1 · e_i · e_k = δ_{ik}`;
    * `hcomplete` — completeness `∑_i (e_i)^μ (e_i)^ν = gi(expTube…).1^{μν}`;
    * `hinv`      — metric/inverse-metric identity at the geodesic point.

  MECHANISM.  Parallel-transport existence (`parallelFrameTransport_local_existence`) builds the
  whole-frame transport curve `Γc` through the initial state `(p, v, e₀)`, where `e₀` is the
  `g p`-orthonormal frame produced by `exists_gorthonormal_frame`; `parallelOrthoFrame_data`
  packages the four frame-data pieces ALONG `(Γc ·).1`; the geodesic alignment
  `frameTransport_geodesic_eq_expTube` identifies `(Γc s).1 = (expTube … s).1` on the transport
  interval; and the curve-germ congruence `covariantDerivAlong_curve_congr` transports the
  parallelism statement from `Γc.1` onto `expTube.1`.  The metric/inverse identities are genuine
  inputs (`g`,`gi` inverse metrics), instantiated at the geodesic point.

  HONEST CAPTION (binding): this establishes the parallel ORTHONORMAL FRAME along `expTube` with
  full frame data, on the (locally existent) transport neighbourhood of `0`.  It does NOT yet
  assemble the van-Vleck `−Ric` second-derivative (the final feed to
  `vanVleck_ray_secondDeriv_ricci_at`), and is NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FrameTransportField
import QIQTH.ParallelOrthoFrameData
import QIQTH.FrameGeodesicAlign
import QIQTH.CovariantDerivCurveCongr
import QIQTH.OrthonormalFrameExists
import QIQTH.ExpMap

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- **A parallel orthonormal frame exists along the exp geodesic `expTube`, with full frame data.**

    Given a metric `g` (smooth, symmetric, positive-definite at `p`) with inverse `gi` (symmetric,
    a genuine matrix inverse of `g`), and `‖v‖ ≤ expRho`, there is a radius `δ > 0` and a frame
    `e : Fin n → ℝ → Point n` such that at every point `t` of the transport neighbourhood
    `Ioo (-δ) δ` the five frame-data pieces consumed by `frame_raychaudhuri_ricci_nhds` hold,
    all along the geodesic `expTube g gi hC p v`:

    * `he`        — `∀ i a, ∀ᶠ τ in 𝓝 t, HasDerivAt (fun s => e i s a) (deriv … τ) τ`;
    * `hpar`      — `∀ i, ∀ᶠ τ in 𝓝 t, covariantDerivAlong g gi (fun τ => (expTube … τ).1) (e i) τ = 0`;
    * `hortho`    — `∑ₐ∑_b g (expTube … t).1 a b · e i t a · e k t b = δ_{ik}`;
    * `hcomplete` — `∑_i e i t μ · e i t b = gi (expTube … t).1 μ b`;
    * `hinv`      — `∑_b g (expTube … t).1 a b · gi (expTube … t).1 μ b = δ_{aμ}`.

    Proof: parallel-transport existence + orthonormal-frame data along the transport curve `Γc`
    + geodesic alignment `(Γc s).1 = (expTube … s).1` + curve-germ congruence for `covariantDerivAlong`.

    HONEST: discharges the M2b-2 frame-existence input carried by `FrameRaychaudhuri.lean`.  Does NOT
    assemble the van-Vleck `−Ric` second derivative, and is NOT `a₁ = R/6`. -/
theorem parallelFrame_expTube_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgisymm : ∀ y μ ν, gi y μ ν = gi y ν μ)
    (hginv : ∀ y a μ, (∑ b, g y a b * gi y μ b) = if a = μ then (1 : ℝ) else 0)
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p)
    (hgpd : Matrix.PosDef (g p : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ (δ : ℝ) (e : Fin n → ℝ → Point n), 0 < δ ∧
      ∀ t ∈ Set.Ioo (-δ) δ,
        (∀ i a, ∀ᶠ τ in nhds t,
            HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
        ∧ (∀ i, ∀ᶠ τ in nhds t,
            covariantDerivAlong g gi (fun τ => (expTube g gi hC p v τ).1) (e i) τ = 0)
        ∧ (∀ i k, (∑ a, ∑ b, g (expTube g gi hC p v t).1 a b * e i t a * e k t b)
            = if i = k then (1 : ℝ) else 0)
        ∧ (∀ μ b, (∑ i, e i t μ * e i t b) = gi (expTube g gi hC p v t).1 μ b)
        ∧ (∀ a μ, (∑ b, g (expTube g gi hC p v t).1 a b * gi (expTube g gi hC p v t).1 μ b)
            = if a = μ then (1 : ℝ) else 0) := by
  classical
  -- (1) an orthonormal IC frame at `p` from positive-definiteness of the metric
  obtain ⟨e₀, he₀⟩ := exists_gorthonormal_frame (g p) hgpd
  -- (2) the whole-frame parallel-transport curve through `(p, v, e₀)` at `t₀ = 0`
  obtain ⟨Γc, hz0, ε, hεpos, hΓcd0⟩ :=
    parallelFrameTransport_local_existence g gi hC (p, v, e₀) 0
  -- confine the transport neighbourhood into `Ioo (-2) 2` as well
  set δ : ℝ := min ε 2 with hδdef
  have hδpos : 0 < δ := lt_min hεpos (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ2 : δ ≤ 2 := min_le_right _ _
  have ht₀ : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδpos⟩
  -- the frame ODE holds on `Ioo (-δ) δ`
  have hΓcd : ∀ s ∈ Set.Ioo (-δ) δ,
      HasDerivAt Γc (geodesicFrameTransportField g gi (Γc s)) s := by
    intro s hs
    exact hΓcd0 s ⟨by linarith [hs.1, hδε], by linarith [hs.2, hδε]⟩
  -- alignment prerequisites
  have hab : Set.Ioo (-δ) δ ⊆ Set.Ioo (-2 : ℝ) 2 :=
    fun s hs => ⟨by linarith [hs.1, hδ2], by linarith [hs.2, hδ2]⟩
  have hΓc0 : ((Γc 0).1, (Γc 0).2.1) = (p, v) := by rw [hz0]
  -- (3) geodesic alignment: `((Γc s).1, (Γc s).2.1) = expTube … s` on `Ioo (-δ) δ`
  have halign := frameTransport_geodesic_eq_expTube g gi hC p v hv Γc hab ht₀ hΓc0 hΓcd
  have halign1 : ∀ s ∈ Set.Ioo (-δ) δ, (Γc s).1 = (expTube g gi hC p v s).1 := by
    intro s hs
    exact congrArg Prod.fst (halign hs)
  -- inputs to the orthonormal-frame packaging, instantiated along `Γc.1`
  have hginv_c : ∀ s ∈ Set.Ioo (-δ) δ, ∀ a μ,
      (∑ b, g (Γc s).1 a b * gi (Γc s).1 μ b) = if a = μ then (1 : ℝ) else 0 :=
    fun s _ a μ => hginv (Γc s).1 a μ
  have hGisymm_c : ∀ s ∈ Set.Ioo (-δ) δ, ∀ μ ν, gi (Γc s).1 μ ν = gi (Γc s).1 ν μ :=
    fun s _ μ ν => hgisymm (Γc s).1 μ ν
  have hIC : ∀ i k,
      (∑ p', ∑ q, g (Γc 0).1 p' q * (Γc 0).2.2 i p' * (Γc 0).2.2 k q)
        = if i = k then (1 : ℝ) else 0 := by
    intro i k; rw [hz0]; exact he₀ i k
  -- (4) the four frame-data pieces along `Γc.1`
  obtain ⟨he, hpar_c, hortho_c, hcomplete_c⟩ :=
    parallelOrthoFrame_data g gi Γc ht₀ hΓcd hg hgsymm hginv_c hGisymm_c hIC
  -- assemble, transporting each piece onto `expTube`
  refine ⟨δ, fun i => fun s => (Γc s).2.2 i, hδpos, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- he : frame regularity, eventually near `t`
    intro i a
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact he i a τ hτ
  · -- hpar : parallelism along `expTube.1`, eventually near `t`
    intro i
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    have hcurve : (fun u => (Γc u).1) =ᶠ[nhds τ] (fun u => (expTube g gi hC p v u).1) := by
      filter_upwards [isOpen_Ioo.mem_nhds hτ] with s hs using halign1 s hs
    have hcongr := covariantDerivAlong_curve_congr g gi (fun u => (Γc u).2.2 i) hcurve
    have h0 := hpar_c i τ hτ
    rw [hcongr] at h0
    exact h0
  · -- hortho : orthonormality at the geodesic point
    intro i k
    have h := hortho_c i k t ht
    rw [halign1 t ht] at h
    exact h
  · -- hcomplete : completeness at the geodesic point
    intro μ b
    have h := hcomplete_c t ht μ b
    rw [halign1 t ht] at h
    exact h
  · -- hinv : metric/inverse identity at the geodesic point
    intro a μ
    exact hginv (expTube g gi hC p v t).1 a μ

end QIQTH.ExpMap
