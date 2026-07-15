/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapContDiff3

/-!
# Closed-form values of `D²F` and `D³F` of the geodesic field AT the equilibrium `(p,0)`

The R3→κ chain (`QIQTH/PullbackMetric.lean`) reduced the closed third-jet `expJetD3(0) = a₃`
to evaluating `expJet3Rhs … 0 …`, whose only remaining unknowns are the CONSTANT closed-form
VALUES of the second and third Fréchet derivatives of the geodesic field `F = geodesicField g gi`
at the equilibrium `(p,0)`:
* `D²F(p,0) = fderiv ℝ (fderiv ℝ F) (p,0)`, and
* `D³F(p,0) = fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (p,0)`.

This file builds those closed-form `apply` lemmas — the direct one/two-order extension of
`geodesicField_fderiv_apply` (the order-1 closed form).  The key simplification is the equilibrium
velocity `u = 0`: at `(x,u) = (p,0)` every ACCELERATION term of `DF` carries a factor `u`, so
`DF(p,0)(ξ,η) = (η,0)` and differentiating the acceleration block and evaluating at `u = 0` kills
every term except the `u`-linear ones, whose one surviving derivative regroups into a CLEAN
bilinear (resp. trilinear) form in `Γ(p)` (resp. `Γ(p)`, `∂Γ(p)`).

The reduction to a `Point n`-valued (not nested-CLM) derivative is via `fderiv_clm_apply`:
`(fderiv (fderiv F) x) v w = fderiv (fun y => fderiv F y w) x v` (the constant-second-slot
specialisation), so `D²F(x)(v)(w)` is the ordinary Fréchet derivative in direction `v` of the
CLOSED map `y ↦ DF(y)(w)` (`geodesicField_fderiv_apply`), which we differentiate by the product/pd
layer exactly as `geodesicField_fderiv_apply` differentiated `F` itself.

HONEST: these are the pointwise closed-form second/third Jacobi-coefficient values at the
equilibrium; they do NOT by themselves give the `a₃` match (still needs the polynomial-in-`s`
integral evaluation + `a3rawArr` symmetrization), NOT the pullback metric, NOT numerical-`G`. -/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **The nested `D²F`-to-directional reduction.**  For the (`C^∞`) geodesic field, the second
    Fréchet derivative applied `D²F(x)(v)(w)` equals the ordinary directional derivative in `v` of
    the closed map `y ↦ DF(y)(w)` (constant second slot `w`), via `fderiv_clm_apply` with a constant
    inner function (`fderiv (fun _ => w) = 0`). -/
theorem fderiv2_geodesicField_reduce (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x v w : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x) v w
      = fderiv ℝ (fun y => fderiv ℝ (geodesicField g gi) y w) x v := by
  have hc : DifferentiableAt ℝ (fderiv ℝ (geodesicField g gi)) x :=
    ((contDiff_fderiv_geodesicField g gi hC).differentiable (by simp)).differentiableAt
  rw [fderiv_clm_apply hc (differentiableAt_const _)]
  simp [ContinuousLinearMap.flip_apply]

set_option maxHeartbeats 1600000 in
/-- **The closed-form VALUE of `D²F` at the equilibrium `(p,0)`.**  Bilinear in `Γ(p)` only (NO
    `∂Γ`): the `u = 0` kill removes both the quadratic-in-`u` `∂Γ` term and the `x`-derivatives of the
    two `u`-linear `Γ` terms, leaving only the derivative of the surviving `u`-factor.  With the first
    applied argument `(Δx,Δu)` the differentiation direction and the second `(ξ,η)` the `DF`-slot:
    `D²F(p,0)(Δx,Δu)(ξ,η) = (0, a ↦ −∑_{jk} Γ^a_{jk}(p)·(η_j Δu_k + Δu_j η_k))`. -/
theorem fderiv2_geodesicField_apply_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p Δx Δu ξ η : Point n) :
    (fderiv ℝ (fderiv ℝ (geodesicField g gi)) ((p, 0) : Point n × Point n))
        ((Δx, Δu) : Point n × Point n) ((ξ, η) : Point n × Point n)
      = ((0 : Point n), fun a => -∑ j, ∑ k,
          christoffel g gi a j k p * (η j * Δu k + Δu j * η k)) := by
  rw [fderiv2_geodesicField_reduce g gi hC]
  -- differentiability of the `Γ` and `∂Γ` scalar layers at `p`.
  have hΓd : ∀ a j k, DifferentiableAt ℝ (fun z : Point n => christoffel g gi a j k z) p :=
    fun a j k => ((hC a j k).differentiable (by simp)).differentiableAt
  have hpdd : ∀ a j k l,
      DifferentiableAt ℝ (fun z : Point n => pd (fun z => christoffel g gi a j k z) l z) p :=
    fun a j k l => ((christoffel_pd_contDiff g gi hC a j k l).differentiable (by simp)).differentiableAt
  -- `y ↦ Γ^a_{jk}(y.1)` and `y ↦ (∑ₗ ∂ₗΓ·ξₗ)(y.1)` HasFDerivAt at `(p,0)`.
  have hΓf := fun a j k =>
    HasFDerivAt.comp (f := Prod.fst) ((p, 0) : Point n × Point n)
      (hΓd a j k).hasFDerivAt hasFDerivAt_fst
  -- velocity projection `y ↦ y.2 j` HasFDerivAt at `(p,0)` (a CLM, self-derivative).
  have hu := fun j => ((ContinuousLinearMap.proj (R := ℝ) j).comp
      (ContinuousLinearMap.snd ℝ (Point n) (Point n))).hasFDerivAt (x := ((p, 0) : Point n × Point n))
  have hS := fun a j k => HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n))) (fun l _ =>
    (HasFDerivAt.comp (f := Prod.fst) ((p, 0) : Point n × Point n)
      (hpdd a j k l).hasFDerivAt hasFDerivAt_fst).mul_const (ξ l))
  -- per-`(a,j,k)` summand HasFDerivAt (the three product families).
  have hterm := fun a j k =>
    ((((hS a j k).mul (hu j)).mul (hu k)).add
      (((hΓf a j k).mul_const (η j)).mul (hu k))).add
      (((hΓf a j k).mul (hu j)).mul_const (η k))
  -- assemble the acceleration Pi and the constant velocity slot into `y ↦ DF(y)(ξ,η)`.
  have hExpl := (hasFDerivAt_const (η : Point n) ((p, 0) : Point n × Point n)).prodMk
    (hasFDerivAt_pi.2 (fun a =>
      (HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n))) (fun j _ =>
        HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n))) (fun k _ => hterm a j k))).neg))
  -- transport to the closed map `y ↦ fderiv F y (ξ,η)` (pointwise = via `geodesicField_fderiv_apply`).
  have hpt : ∀ y : Point n × Point n,
      fderiv ℝ (geodesicField g gi) y ((ξ, η) : Point n × Point n)
        = ((η : Point n), fun a => -∑ j, ∑ k,
            ((∑ l, pd (fun z => christoffel g gi a j k z) l y.1 * ξ l) * y.2 j * y.2 k
              + christoffel g gi a j k y.1 * η j * y.2 k
              + christoffel g gi a j k y.1 * y.2 j * η k)) :=
    fun y => by obtain ⟨x, u⟩ := y; exact geodesicField_fderiv_apply g gi hC x u ξ η
  have hHFD : HasFDerivAt (fun y => fderiv ℝ (geodesicField g gi) y ((ξ, η) : Point n × Point n))
      _ ((p, 0) : Point n × Point n) :=
    hExpl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => hpt y)
  rw [hHFD.fderiv]
  -- evaluate the built derivative CLM at `(Δx,Δu)` and simplify with the equilibrium `u = 0`.
  refine Prod.ext ?_ ?_
  · simp
  · funext a
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply, smul_eq_mul,
      Function.comp_apply, Pi.mul_apply, Pi.zero_apply]
    rw [neg_inj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring

/-- **General `D²`-to-directional reduction (for any twice-differentiable `f` on the phase space).**
    `(fderiv (fderiv f) x) v w = fderiv (fun y => fderiv f y w) x v`, via `fderiv_clm_apply` with a
    constant inner slot.  The `f = geodesicField` specialisation is `fderiv2_geodesicField_reduce`;
    this general form is what the `D³F` reduction applies to the CLOSED order-1 map
    `Q z = DF(z)(ξ,η)`. -/
theorem fderiv2_reduce_general (f : (Point n × Point n) → (Point n × Point n))
    (x v w : Point n × Point n) (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    (fderiv ℝ (fderiv ℝ f) x) v w = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [fderiv_clm_apply hf (differentiableAt_const _)]
  simp [ContinuousLinearMap.flip_apply]

/-- **The `D³F`-to-`D²Q` reduction: the third Fréchet derivative of the geodesic field, applied,
    equals a SECOND derivative of the CLOSED order-1 map `Q z = DF(z)(v₃)`.**
      `D³F(x)(v₁)(v₂)(v₃) = (fderiv (fderiv (fun z => DF(z)(v₃))) x)(v₁)(v₂)`.
    Proof (three `fderiv_clm_apply`/const reductions):
    (1) `D³F(x)(v₁)(v₂)(v₃) = fderiv (fun y => D²F(y)(v₂)(v₃)) x v₁` (peel the two constant outer slots
        `v₂, v₃` off the nested `fderiv (fderiv (fderiv F))`);
    (2) pointwise `D²F(y)(v₂)(v₃) = fderiv (fun z => DF(z)(v₃)) y v₂` (`fderiv2_geodesicField_reduce`
        at the running point `y`), so the inner function is `y ↦ fderiv Q y v₂`;
    (3) `fderiv (fun y => fderiv Q y v₂) x v₁ = (fderiv (fderiv Q) x)(v₁)(v₂)`
        (`fderiv2_reduce_general` for the `C^∞` map `Q`).
    This reduces the closed `D³F(p,0)` VALUE to the second derivative at `(p,0)` of the fully explicit
    `Q` (whose closed form is `geodesicField_fderiv_apply`): the remaining wall is the closed VALUE of
    `(fderiv (fderiv Q) (p,0))(v₁)(v₂)`, i.e. the trilinear-in-`∂Γ(p)` form
    `−∑_{jk}[ (∑_l ∂_lΓ^i_{jk}(p)·ξ_l)(b₁_j b₂_k + b₂_j b₁_k)
             + (∑_m ∂_mΓ^i_{jk}(p)·a₁_m)(η_j b₂_k + b₂_j η_k)
             + (∑_m ∂_mΓ^i_{jk}(p)·a₂_m)(η_j b₁_k + b₁_j η_k) ]`
    (with `v₁ = (a₁,b₁)`, `v₂ = (a₂,b₂)`, `v₃ = (ξ,η)`), obtained by the general-point first derivative
    of `Q` (carrying the vanishing `∂²Γ·u²` terms) followed by a second product-rule build + the `u = 0`
    kill — the direct `D³F` analogue of `fderiv2_geodesicField_apply_zero`. -/
theorem fderiv3_geodesicField_reduce (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x v1 v2 v3 : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x) v1 v2 v3
      = (fderiv ℝ (fderiv ℝ (fun z => fderiv ℝ (geodesicField g gi) z v3)) x) v1 v2 := by
  set F := geodesicField g gi with hF
  -- abbreviations: `H = D²F`, `Q z = DF(z)(v3)`.
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((contDiff_fderiv_geodesicField g gi hC).differentiable (by simp)).differentiableAt
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ F)) x :=
    ((contDiff_fderiv2_geodesicField g gi hC).differentiable (by simp)).differentiableAt
  -- (1) peel the two constant outer slots.
  have hstep1 : (fderiv ℝ (fderiv ℝ (fderiv ℝ F)) x) v1 v2 v3
      = fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ F) y) v2 v3) x v1 := by
    -- `fun y => H y v2 v3 = fun y => (H y v2) v3`; differentiate peeling `v3` then `v2`.
    have hc : DifferentiableAt ℝ (fun y => (fderiv ℝ (fderiv ℝ F) y) v2) x :=
      hH.clm_apply (differentiableAt_const _)
    rw [fderiv_clm_apply hc (differentiableAt_const _)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    rw [fderiv_clm_apply hH (differentiableAt_const _)]
    simp [ContinuousLinearMap.flip_apply]
  rw [hstep1]
  -- (2) pointwise middle-slot reduction `H y v2 v3 = fderiv Q y v2`.
  have hstep2 : (fun y => (fderiv ℝ (fderiv ℝ F) y) v2 v3)
      = (fun y => fderiv ℝ (fun z => fderiv ℝ F z v3) y v2) :=
    funext fun y => fderiv2_reduce_general F y v2 v3
      (((contDiff_fderiv_geodesicField g gi hC).differentiable (by simp)).differentiableAt)
  rw [hstep2]
  -- (3) general reduce for the closed map `Q`.
  have hQdiff : DifferentiableAt ℝ (fderiv ℝ (fun z => fderiv ℝ F z v3)) x := by
    have hQC : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z => fderiv ℝ F z v3) :=
      (contDiff_fderiv_geodesicField g gi hC).clm_apply contDiff_const
    exact ((hQC.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).differentiable (by simp)).differentiableAt
  rw [fderiv2_reduce_general (fun z => fderiv ℝ F z v3) x v1 v2 hQdiff]

end QIQTH.ExpMap
