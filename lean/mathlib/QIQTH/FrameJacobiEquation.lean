/-
  FrameJacobiEquation — the FRAME Jacobi equation `Yt'' = −R̃ Yt` (M2b-5 of the off-radial
  matrix-Jacobi campaign, `docs/qg_roadmap/MATRIX_JACOBI_PLAN.md`).

  CONTENT.  Projecting the (now-proven, OFF-CENTER) covariant Jacobi equation
  (`covariant_jacobi_equation`, M2b-3) onto a PARALLEL ORTHONORMAL frame `{e_i}` gives the clean
  matrix Jacobi ODE
      `Yt_k''(t) = − ∑ j, R̃_{kj}(t) · Yt_j(t)`     (`Yt'' = −R̃ Yt`),
  where the Jacobi field is expanded in the frame, `ξ(s) = fun a => ∑ j, Yt j s · e j s a`
  (hypothesis `hexp`), and the frame curvature matrix is
      `R̃_{kj} := ∑_{a,b} g_{ab}(x) · (R(e_j, v) v)^a · (e_k)^b`
                (`= ∑ a, ∑ b, g x a b · (riemannGeodesicDeviation g gi x v (e j))^a · (e k)^b`).
  Its trace (`k = j` summed) is `Ric(v,v)` by `QIQTH.FrameRicci.frame_ricci_trace` (M2b-4); this R̃ is
  the `A(τ)` matrix that feeds M4b's matrix Raychaudhuri
  `θ' = −tr R̃ − tr(Θ²) = −Ric(v,v) − tr(Θ²)`.

  HOW IT LANDS.
  * `covariant_jacobi_equation` (M2b-3): `D²ξ/dτ² = − R(ξ,γ')γ'` (`= − riemannGeodesicDeviation …`).
  * `covariantSecondDeriv_frame_combo` (M2b-3a): in a parallel frame,
    `D²ξ/dτ² = fun a => ∑ i, Yt_i''(t) · e_i(t)^a`.
    Equating these (via `hexp`) gives the VECTOR identity `∑_i Yt_i'' e_i = − R(ξ,v)v`.
  * `riemannGeodesicDeviation_linear` (below): `R(·,v)v` is LINEAR in the deviation vector, so
    `R(ξ,v)v = ∑_j Yt_j R(e_j,v)v`.
  * Contracting the vector identity with `⟨·, e_k⟩_g = ∑_{a,b} g_{ab}(·)^a (e_k)^b` and using
    orthonormality `∑_{a,b} g_{ab} e_i^a e_k^b = δ_{ik}` (`hortho`) collapses the LHS to `Yt_k''` and the
    RHS to `−∑_j R̃_{kj} Yt_j`.

  HONEST SCOPE.  This file assumes — as genuine, clearly-labelled hypotheses — the EXISTENCE of the
  parallel orthonormal frame: parallelism (`hpar`), orthonormality (`hortho`), and the frame expansion
  of the Jacobi field (`hexp`) are CARRIED, not constructed (construction is M2b-2).  It does NOT
  assemble the Raychaudhuri equation (M4b, next brick), and it is unrelated to the heat-kernel
  coefficient `a₁ = R/6` (M6).  None of the hypotheses assume the conclusion; all regularity inputs
  (`hY`, `hY2`, `he`) are exactly those of `covariantSecondDeriv_frame_combo`.
-/
import Mathlib
import QIQTH.CovariantJacobiOffCenter
import QIQTH.FrameCovariantDeriv
import QIQTH.JacobiEquation

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic Finset

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **Reorder a 4-fold `Finset.univ` sum** moving the INNERMOST index out to the front:
    `∑ σ ∑ μ ∑ ν ∑ j F = ∑ j ∑ σ ∑ μ ∑ ν F`.  Pure finite reindexing (three `Finset.sum_comm`),
    no analysis. -/
private lemma sum4_reorder_last_to_first (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ σ, ∑ μ, ∑ ν, ∑ j, F σ μ ν j) = ∑ j, ∑ σ, ∑ μ, ∑ ν, F σ μ ν j := by
  rw [show (∑ σ, ∑ μ, ∑ ν, ∑ j, F σ μ ν j) = ∑ σ, ∑ μ, ∑ j, ∑ ν, F σ μ ν j from
      Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun μ _ => Finset.sum_comm))]
  rw [show (∑ σ, ∑ μ, ∑ j, ∑ ν, F σ μ ν j) = ∑ σ, ∑ j, ∑ μ, ∑ ν, F σ μ ν j from
      Finset.sum_congr rfl (fun σ _ => Finset.sum_comm)]
  rw [Finset.sum_comm]

/-! ### #1 — the geodesic-deviation contraction is LINEAR in the deviation vector -/

/-- **`R(·,v)v` is linear in the deviation vector.**  Expanding the deviation vector in a frame,
    `ξ = fun μ => ∑ j, Y j · e j μ`, the Riemann geodesic-deviation contraction distributes:
      `riemannGeodesicDeviation g gi x v (∑ j Y_j e_j) = fun a => ∑ j, Y_j · (R(e_j, v)v)^a`.
    Pure finite index algebra (the `ξ μ` factor of `riemannGeodesicDeviation` carries the linearity). -/
theorem riemannGeodesicDeviation_linear (g gi : Point n → Fin n → Fin n → ℝ)
    (x v : Point n) (Y : Fin n → ℝ) (e : Fin n → Point n) :
    riemannGeodesicDeviation g gi x v (fun μ => ∑ j, Y j * e j μ)
      = fun a => ∑ j, Y j * (riemannGeodesicDeviation g gi x v (e j)) a := by
  funext a
  simp only [riemannGeodesicDeviation]
  rw [show (∑ σ, ∑ μ, ∑ ν, riemann g gi a σ μ ν x * v σ * (∑ j, Y j * e j μ) * v ν)
        = ∑ σ, ∑ μ, ∑ ν, ∑ j, Y j * (riemann g gi a σ μ ν x * v σ * e j μ * v ν) from
      Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun μ _ =>
        Finset.sum_congr rfl (fun ν _ => by
          rw [show riemann g gi a σ μ ν x * v σ * (∑ j, Y j * e j μ) * v ν
                = (∑ j, Y j * e j μ) * (riemann g gi a σ μ ν x * v σ * v ν) from by ring,
              Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by ring))))]
  rw [sum4_reorder_last_to_first
        (fun σ μ ν j => Y j * (riemann g gi a σ μ ν x * v σ * e j μ * v ν))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Finset.mul_sum]

/-! ### #2 — the frame Jacobi equation `Yt'' = −R̃ Yt` -/

/-- **The frame Jacobi equation (`Yt'' = −R̃ Yt`).**  For a geodesic `γ=(x,v)` (`hγ`) and Jacobi field
    `V=(ξ,η)` (`hVar`), with the position variation `ξ = (V·).1` expanded in a PARALLEL (`hpar`)
    ORTHONORMAL (`hortho`) frame `{e_i}` (`hexp`), projecting the off-center covariant Jacobi equation
    onto `e_k` (metric inner product) gives, for each `k`, the CLEAN matrix Jacobi ODE
      `Yt_k''(t) = − ∑ j, R̃_{kj}(t) · Yt_j(t)`,
    where `R̃_{kj} := ∑_{a,b} g_{ab}(x) · (R(e_j,v)v)^a · (e_k)^b` is the frame curvature matrix (whose
    trace is `Ric(v,v)`, `QIQTH.FrameRicci.frame_ricci_trace`).  Combines `covariant_jacobi_equation`
    (M2b-3), `covariantSecondDeriv_frame_combo` (M2b-3a), `riemannGeodesicDeviation_linear`, and
    orthonormal projection.  The parallel orthonormal frame is CARRIED (existence = M2b-2). -/
theorem frame_jacobi_equation (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hγ : ∀ τ, HasDerivAt γ (geodesicField g gi (γ τ)) τ)
    (hVar : ∀ τ, IsGeodesicVariationAt g gi γ V τ)
    (e : Fin n → ℝ → Point n) (Yt : Fin n → ℝ → ℝ)
    (hY : ∀ i, ∀ τ, HasDerivAt (Yt i) (deriv (Yt i) τ) τ)
    (hY2 : ∀ i, ∀ τ, HasDerivAt (deriv (Yt i)) (deriv (deriv (Yt i)) τ) τ)
    (he : ∀ i a, ∀ τ, HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, ∀ τ, covariantDerivAlong g gi (fun τ => (γ τ).1) (e i) τ = 0)
    (hortho : ∀ i k, (∑ a, ∑ b, g (γ t).1 a b * e i t a * e k t b) = if i = k then 1 else 0)
    (hexp : (fun s => fun a => ∑ j, Yt j s * e j s a) = (fun s => (V s).1))
    (k : Fin n) :
    deriv (deriv (Yt k)) t
      = - ∑ j, (∑ a, ∑ b, g (γ t).1 a b
            * (riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (e j t)) a * e k t b) * Yt j t := by
  -- the off-center covariant Jacobi equation (vector form).
  have hcj := covariant_jacobi_equation (t := t) g gi hC hgsymm hγ hVar
  -- the parallel-frame second covariant derivative, rewritten through the frame expansion `hexp`.
  have hfc := covariantSecondDeriv_frame_combo g gi (fun τ => (γ τ).1) e Yt hY hY2 he hpar t
  rw [hexp] at hfc
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
    have hVt : (V t).1 = fun μ => ∑ j, Yt j t * e j t μ := (congrFun hexp t).symm
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
