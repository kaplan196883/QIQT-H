/-
  FrameJacobiEquationNhds — LOCALIZING the FRAME Jacobi equation `Yt'' = −R̃ Yt` from `∀τ`
  to a NEIGHBORHOOD of `t` (assembly step of the frame-route sub-campaign toward `B''=−R̃B`).

  CONTENT.  `QIQTH.FrameJacobiEquation.frame_jacobi_equation` proved the clean matrix Jacobi ODE
      `Yt_k''(t) = − ∑ j, R̃_{kj}(t) · Yt_j(t)`     (`Yt'' = −R̃ Yt`)
  under GLOBAL `∀τ` regularity/parallelism/variation hypotheses.  The exp-flow only supplies those
  facts on a NEIGHBORHOOD of the interior evaluation point `t`.  This file weakens every non-`t`
  hypothesis to a genuine `∀ᶠ … in nhds t` fact, bringing the localized covariant pieces
  (`covariant_jacobi_equation_nhds`, `covariantSecondDeriv_frame_combo_nhds`) together so the frame
  equation applies to the exp-flow.

  WHAT LANDS HERE:

    * `covariantSecondDeriv_congr_nhds` — the covariant SECOND derivative depends only on the GERM of
      the field at `t`: if `f =ᶠ[nhds t] h` then `D²f(t) = D²h(t)`.  Proved by lifting the germ
      equality one level (`Filter.Eventually.eventually_nhds`) so the inner covariant-deriv fields
      agree EVENTUALLY, then applying germ-congruence `covariantDerivAlong_congr_nhds` twice.

    * `frame_jacobi_equation_nhds` — identical statement and conclusion to `frame_jacobi_equation`,
      but with `hγ`, `hVar`, `hY`, `hY2`, `he`, `hpar` weakened to `∀ᶠ … in nhds t` and the frame
      expansion `hexp` weakened to an `EventuallyEq`.  The two `hexp` uses are re-routed: the global
      field rewrite goes through `covariantSecondDeriv_congr_nhds`, and the AT-`t` value uses
      `hexp.self_of_nhds`.  Everything else (`key`, `proj`, `hL`, `hR`, `hRV`, `hlin`, `contracted`,
      orthonormal projection) is verbatim.

  HONEST SCOPE.  This is a pure LOCALIZATION/assembly of the existing frame Jacobi identity.  It does
  NOT construct the parallel orthonormal frame, prove the trace identity `tr R̃ = Ric`, prove
  `B'' = −R̃ B`, or the heat-kernel coefficient `a₁ = R/6`.  The parallel orthonormal frame (`hpar`,
  `hortho`, `hexp`) is CARRIED, not constructed; no hypothesis assumes the conclusion.
-/
import Mathlib
import QIQTH.FrameJacobiEquation
import QIQTH.CovariantJacobiNhds
import QIQTH.FrameCovariantDerivNhds
import QIQTH.CovariantJacobi

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic Finset

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ### helper — the covariant second derivative depends only on the germ at `t` -/

/-- **Germ-congruence of `covariantSecondDeriv`.**  If two fields agree on a neighborhood of `t`
    (`f =ᶠ[nhds t] h`), their covariant SECOND derivatives along `γ` at `t` coincide.  Lifting the
    germ equality one level (`Filter.Eventually.eventually_nhds`) makes the two inner
    covariant-derivative fields agree EVENTUALLY near `t`; then `covariantDerivAlong_congr_nhds`
    (germ-congruence of the covariant first derivative) applied twice closes it. -/
theorem covariantSecondDeriv_congr_nhds
    (g gi : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n) {t : ℝ}
    {f h : ℝ → Point n} (hfh : f =ᶠ[nhds t] h) :
    covariantSecondDeriv g gi γ f t = covariantSecondDeriv g gi γ h t := by
  unfold covariantSecondDeriv
  -- the two inner covariant-derivative fields agree on a neighborhood of `t`.
  have hinner : covariantDerivAlong g gi γ f =ᶠ[nhds t] covariantDerivAlong g gi γ h := by
    filter_upwards [hfh.eventually_nhds] with τ hτ
    exact covariantDerivAlong_congr_nhds g gi γ hτ
  -- germ-congruence of the OUTER covariant derivative at `t`.
  exact covariantDerivAlong_congr_nhds g gi γ hinner

/-! ### the frame Jacobi equation `Yt'' = −R̃ Yt`, localized to a neighborhood of `t` -/

/-- **The frame Jacobi equation (`Yt'' = −R̃ Yt`), localized (`∀ᶠ … in 𝓝 t`).**  Identical statement
    and conclusion to `frame_jacobi_equation`, but the geodesic ODE (`hγ`), Jacobi-variation ODE
    (`hVar`), all regularity (`hY`, `hY2`, `he`), and parallelism (`hpar`) are only assumed on a
    NEIGHBORHOOD of `t`, and the frame expansion (`hexp`) is only an `EventuallyEq` near `t` — the
    form the exp-flow supplies.  Proved by swapping in `covariant_jacobi_equation_nhds` and
    `covariantSecondDeriv_frame_combo_nhds`, re-routing the frame-field rewrite through
    `covariantSecondDeriv_congr_nhds hexp` and the AT-`t` value through `hexp.self_of_nhds`; the
    orthonormal projection is verbatim from `frame_jacobi_equation`. -/
theorem frame_jacobi_equation_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hγ : ∀ᶠ τ in nhds t, HasDerivAt γ (geodesicField g gi (γ τ)) τ)
    (hVar : ∀ᶠ τ in nhds t, IsGeodesicVariationAt g gi γ V τ)
    (e : Fin n → ℝ → Point n) (Yt : Fin n → ℝ → ℝ)
    (hY : ∀ i, ∀ᶠ τ in nhds t, HasDerivAt (Yt i) (deriv (Yt i) τ) τ)
    (hY2 : ∀ i, ∀ᶠ τ in nhds t, HasDerivAt (deriv (Yt i)) (deriv (deriv (Yt i)) τ) τ)
    (he : ∀ i a, ∀ᶠ τ in nhds t, HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, ∀ᶠ τ in nhds t, covariantDerivAlong g gi (fun τ => (γ τ).1) (e i) τ = 0)
    (hortho : ∀ i k, (∑ a, ∑ b, g (γ t).1 a b * e i t a * e k t b) = if i = k then 1 else 0)
    (hexp : (fun s => fun a => ∑ j, Yt j s * e j s a) =ᶠ[nhds t] (fun s => (V s).1))
    (k : Fin n) :
    deriv (deriv (Yt k)) t
      = - ∑ j, (∑ a, ∑ b, g (γ t).1 a b
            * (riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (e j t)) a * e k t b) * Yt j t := by
  -- the off-center covariant Jacobi equation (vector form), localized.
  have hcj := covariant_jacobi_equation_nhds (t := t) g gi hC hgsymm hγ hVar
  -- the parallel-frame second covariant derivative, localized, rewritten through the frame expansion.
  have hfc := covariantSecondDeriv_frame_combo_nhds g gi (fun τ => (γ τ).1) e Yt t hY hY2 he hpar
  rw [covariantSecondDeriv_congr_nhds g gi (fun τ => (γ τ).1) hexp] at hfc
  -- the VECTOR identity `∑_i Yt_i'' e_i = − R(ξ,v)v`.
  have key : (fun a => ∑ i, deriv (deriv (Yt i)) t * e i t a)
      = - riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (V t).1 := by
    rw [← hfc]; exact hcj
  -- the bilinear projection `∑_{a,b} g_{ab}(∑_i c_i w_i^a) e_k^b = ∑_i c_i (∑_{a,b} g_{ab} w_i^a e_k^b)`.
  have proj : ∀ (c : Fin n → ℝ) (w : Fin n → Point n),
      (∑ a, ∑ b, g (γ t).1 a b * (∑ i, c i * w i a) * e k t b)
        = ∑ i, c i * (∑ a, ∑ b, g (γ t).1 a b * w i a * e k t b) := by
    intro c w
    rw [show (∑ a, ∑ b, g (γ t).1 a b * (∑ i, c i * w i a) * e k t b)
          = ∑ a, ∑ b, ∑ i, c i * (g (γ t).1 a b * w i a * e k t b) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)))]
    rw [show (∑ a, ∑ b, ∑ i, c i * (g (γ t).1 a b * w i a * e k t b))
          = ∑ a, ∑ i, ∑ b, c i * (g (γ t).1 a b * w i a * e k t b) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
  -- linearity of `R(·,v)v` applied to the frame-expanded Jacobi field.
  have hRV : riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (V t).1
      = fun a => ∑ i, Yt i t * (riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (e i t)) a := by
    have hVt : (V t).1 = fun μ => ∑ j, Yt j t * e j t μ := hexp.self_of_nhds.symm
    rw [hVt]
    exact riemannGeodesicDeviation_linear g gi (γ t).1 (γ t).2 (fun j => Yt j t) (fun j => e j t)
  -- the negated deviation, as a frame combination with components `−Yt_i`.
  have hlin : (- riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (V t).1)
      = fun a => ∑ i, (- Yt i t) * (riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (e i t)) a := by
    rw [hRV]
    funext a
    simp only [Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- LHS projection: orthonormality collapses `∑_i Yt_i'' ⟨e_i,e_k⟩` to `Yt_k''`.
  have hL : (∑ a, ∑ b, g (γ t).1 a b * (∑ i, deriv (deriv (Yt i)) t * e i t a) * e k t b)
      = deriv (deriv (Yt k)) t := by
    rw [proj (fun i => deriv (deriv (Yt i)) t) (fun i => e i t)]
    simp only [hortho, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- RHS projection: linearity + `proj` yield the frame curvature matrix `R̃`.
  have hR : (∑ a, ∑ b, g (γ t).1 a b
        * (- riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (V t).1) a * e k t b)
      = - ∑ j, (∑ a, ∑ b, g (γ t).1 a b
            * (riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (e j t)) a * e k t b) * Yt j t := by
    rw [hlin]
    simp only []
    rw [proj (fun i => - Yt i t) (fun i => riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (e i t))]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- contract the vector identity `key` with `⟨·, e_k⟩_g` and combine.
  have contracted := congrArg
    (fun f : Point n => ∑ a, ∑ b, g (γ t).1 a b * f a * e k t b) key
  simp only [] at contracted
  rw [hL, hR] at contracted
  exact contracted

end QIQTH.ExpMap
