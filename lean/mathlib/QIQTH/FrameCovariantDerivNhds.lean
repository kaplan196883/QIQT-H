/-
  FrameCovariantDerivNhds — LOCALIZING the FRAME covariant second-derivative combo from
  `∀τ` to a NEIGHBORHOOD of `t` (frame-route sub-campaign toward `B''=−R̃B`).

  CONTENT.  The originals in `QIQTH.FrameCovariantDeriv` (`covariantDerivAlong_frame_combo` `#1`,
  `covariantSecondDeriv_frame_combo` `#2`) carry their regularity/parallelism hypotheses as GLOBAL
  `∀τ` facts.  This file weakens those to genuine NEIGHBORHOOD (`∀ᶠ … in nhds t`) hypotheses:

    * `covariantDerivAlong_frame_combo_at` (`A`) — a pointwise variant of `#1` taking the hypotheses
      only AT the single point `τ` (its proof never used any other `τ'`, so this is a verbatim copy).
    * `covariantDerivAlong_congr_nhds` (`B`) — `covariantDerivAlong g gi γ · τ` depends only on the
      GERM of the field at `τ` (via `Filter.EventuallyEq.deriv_eq` for the ordinary-`deriv` part and
      `hfh.self_of_nhds` for the pointwise connection part).
    * `covariantSecondDeriv_frame_combo_nhds` (`C`) — the payoff: `#2` with every hypothesis a
      neighborhood fact.  The inner covariant derivative agrees with its explicit frame form on a
      neighborhood of `t` (`filter_upwards` + `A`); germ-congruence `B` rewrites the inner field
      inside the OUTER `covariantDerivAlong` at `t`; then `A` at `t` (via `.self_of_nhds`) finishes.

  HONEST SCOPE.  This is a pure LOCALIZATION of the existing frame identity.  It does NOT prove the
  frame Jacobi equation `B''=−R̃B`, the trace identity `tr R̃ = Ric`, or the heat-kernel coefficient
  `a₁=R/6`.  The parallelism of the frame `hpar` and all regularity of `Y_i`, `e_i^a` are carried as
  genuine, labelled hypotheses; none assume the conclusion.
-/
import Mathlib
import QIQTH.CovariantJacobi
import QIQTH.FrameCovariantDeriv

namespace QIQTH.ExpMap

open QIQTH.Curvature
open Finset Topology

set_option maxHeartbeats 1200000

variable {n : ℕ}

/-- **Reorder a triple `Finset.univ` sum** from nesting order `j,k,i` to `i,j,k`.  Pure finite
    reindexing (local copy of the `private` helper in `QIQTH.FrameCovariantDeriv`). -/
private lemma sum_reorder_jki_to_ijk (F : Fin n → Fin n → Fin n → ℝ) :
    (∑ j, ∑ k, ∑ i, F i j k) = ∑ i, ∑ j, ∑ k, F i j k := by
  rw [show (∑ j, ∑ k, ∑ i, F i j k) = ∑ j, ∑ i, ∑ k, F i j k from
    Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

/-! ### (A) — pointwise (at-`τ`) frame covariant derivative -/

/-- **Frame covariant derivative, pointwise (`A`).**  A variant of `covariantDerivAlong_frame_combo`
    (`#1`) taking the regularity (`hY`, `he`) and parallelism (`hpar`) hypotheses only AT the single
    point `τ`.  The original's proof used those hypotheses solely at its `τ` argument, so this is a
    near-verbatim copy. -/
theorem covariantDerivAlong_frame_combo_at
    (g gi : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (Y : Fin n → ℝ → ℝ) (τ : ℝ)
    (hY : ∀ i, HasDerivAt (Y i) (deriv (Y i) τ) τ)
    (he : ∀ i a, HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, covariantDerivAlong g gi γ (e i) τ = 0) :
    covariantDerivAlong g gi γ (fun s => fun a => ∑ i, Y i s * e i s a) τ
      = fun a => ∑ i, deriv (Y i) τ * e i τ a := by
  funext a
  rw [covariantDerivAlong_apply]
  show deriv (fun s => ∑ i, Y i s * e i s a) τ
        + ∑ j, ∑ k, christoffel g gi a j k (γ τ) * deriv (fun s => γ s j) τ
            * ∑ i, Y i τ * e i τ k
      = ∑ i, deriv (Y i) τ * e i τ a
  -- Leibniz derivative of the field component `a`.
  have hΞ : HasDerivAt (fun s => ∑ i, Y i s * e i s a)
      (∑ i, (deriv (Y i) τ * e i τ a + Y i τ * deriv (fun s => e i s a) τ)) τ := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hY i).mul (he i a)
  rw [hΞ.deriv]
  -- regroup the connection double-sum by pulling out the frame index `i`.
  have hcomm :
      (∑ j, ∑ k, christoffel g gi a j k (γ τ) * deriv (fun s => γ s j) τ * ∑ i, Y i τ * e i τ k)
      = ∑ i, Y i τ *
          ∑ j, ∑ k, christoffel g gi a j k (γ τ) * deriv (fun s => γ s j) τ * e i τ k := by
    simp only [Finset.mul_sum]
    rw [sum_reorder_jki_to_ijk]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => by ring)))
  rw [hcomm]
  -- parallelism: `deriv e_i^a + (connection sum)_i = (covariantDerivAlong (e_i))_a = 0`.
  have hp : ∀ i, deriv (fun s => e i s a) τ
      + ∑ j, ∑ k, christoffel g gi a j k (γ τ) * deriv (fun s => γ s j) τ * e i τ k = 0 := by
    intro i
    have h := congrFun (hpar i) a
    rwa [covariantDerivAlong_apply, Pi.zero_apply] at h
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hpi := hp i
  linear_combination (Y i τ) * hpi

/-! ### (B) — `covariantDerivAlong` depends only on the germ at `τ` -/

/-- **Germ-congruence of `covariantDerivAlong` (`B`).**  If two fields agree on a neighborhood of `τ`
    (`f =ᶠ[nhds τ] h`), their covariant derivatives along `γ` at `τ` coincide.  The ordinary-`deriv`
    part uses `Filter.EventuallyEq.deriv_eq`; the pointwise connection part uses `hfh.self_of_nhds`. -/
theorem covariantDerivAlong_congr_nhds
    (g gi : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n) {τ : ℝ}
    {f h : ℝ → Point n} (hfh : f =ᶠ[nhds τ] h) :
    covariantDerivAlong g gi γ f τ = covariantDerivAlong g gi γ h τ := by
  funext a
  rw [covariantDerivAlong_apply g gi γ f τ a, covariantDerivAlong_apply g gi γ h τ a]
  have hev : (fun s => f s a) =ᶠ[nhds τ] (fun s => h s a) :=
    hfh.mono (fun s hs => congrFun hs a)
  have hderiv : deriv (fun s => f s a) τ = deriv (fun s => h s a) τ := hev.deriv_eq
  rw [hderiv, hfh.self_of_nhds]

/-! ### (C) — the frame covariant SECOND derivative, localized to a neighborhood of `t` -/

/-- **Frame covariant second derivative, localized (`C`).**  The neighborhood version of
    `covariantSecondDeriv_frame_combo` (`#2`): every regularity/parallelism hypothesis is only a
    genuine `∀ᶠ … in nhds t` fact.  The inner covariant derivative equals its explicit frame form on
    a neighborhood of `t` (`filter_upwards` + `A`); germ-congruence `B` transports that equality
    inside the OUTER covariant derivative at `t`; then `A` at `t` (via `.self_of_nhds`) closes it. -/
theorem covariantSecondDeriv_frame_combo_nhds
    (g gi : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (Y : Fin n → ℝ → ℝ) (t : ℝ)
    (hY : ∀ i, ∀ᶠ τ in nhds t, HasDerivAt (Y i) (deriv (Y i) τ) τ)
    (hY2 : ∀ i, ∀ᶠ τ in nhds t, HasDerivAt (deriv (Y i)) (deriv (deriv (Y i)) τ) τ)
    (he : ∀ i a, ∀ᶠ τ in nhds t, HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, ∀ᶠ τ in nhds t, covariantDerivAlong g gi γ (e i) τ = 0) :
    covariantSecondDeriv g gi γ (fun s => fun a => ∑ i, Y i s * e i s a) t
      = fun a => ∑ i, deriv (deriv (Y i)) t * e i t a := by
  -- assemble the per-index neighborhood hypotheses into single `∀ᶠ` facts (`Fin n` is finite).
  have hYev : ∀ᶠ τ in nhds t, ∀ i, HasDerivAt (Y i) (deriv (Y i) τ) τ :=
    Filter.eventually_all.2 hY
  have heev : ∀ᶠ τ in nhds t, ∀ i a, HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ :=
    Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (he i))
  have hparev : ∀ᶠ τ in nhds t, ∀ i, covariantDerivAlong g gi γ (e i) τ = 0 :=
    Filter.eventually_all.2 hpar
  -- the inner covariant-derivative field agrees with its explicit frame form on a neighborhood of `t`.
  have hinner_ev : covariantDerivAlong g gi γ (fun s => fun a => ∑ i, Y i s * e i s a)
      =ᶠ[nhds t] (fun s => fun a => ∑ i, deriv (Y i) s * e i s a) := by
    filter_upwards [hYev, heev, hparev] with s hYs hes hpars
    exact covariantDerivAlong_frame_combo_at g gi γ e Y s hYs hes hpars
  -- iterate: outer covariant derivative, germ-congruence at `t`, then `A` at `t`.
  unfold covariantSecondDeriv
  rw [covariantDerivAlong_congr_nhds g gi γ hinner_ev]
  exact covariantDerivAlong_frame_combo_at g gi γ e (fun i => deriv (Y i)) t
    (fun i => (hY2 i).self_of_nhds) (fun i a => (he i a).self_of_nhds)
    (fun i => (hpar i).self_of_nhds)

end QIQTH.ExpMap
