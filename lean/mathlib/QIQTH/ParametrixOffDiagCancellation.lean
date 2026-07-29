/-
  ParametrixOffDiagCancellation — the (c)-side M5 off-diagonal `O(1/t)` cancellation, ONE ORDER
  BEYOND the diagonal face:  the **GRADIENT (first-derivative) face** of `totalRadialO1_coeff = 0`
  at the RNC centre.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHICH ROUTE (read this — it is the honest scope).

  The assembled leading `O(1/t)` coefficient (landed in `ParametrixResidualO1Total`) is
      totalRadialO1_coeff g gi Θ u v
        = [½Σ(gⁱⁱ−1) − ½Σ gⁱʲΓᵏᵢⱼvᵏ]·w₀(v)  +  (r∂_r w₀)(v)  +  ½Σᵢⱼ(gⁱʲ−δ)(vⁱ∂ⱼw₀+vʲ∂ᵢw₀)(v),
  with `w₀ = foldedCoeff Θ u 0`.  Its full OFF-diagonal vanishing (`= 0` for all `v` near the centre)
  is the `k=0` DeWitt/van-Vleck transport equation in radial-Raychaudhuri form.

  • ROUTE (b) — the EXACT general-`v` transport identity — is NOT available in the repo, and this file
    does NOT use it.  The radial term `(r∂_r)w₀` is connected to Ricci ONLY through the
    `expMap`/`expPullbackMetric` representation (`ExpMap.vanVleck_radialDeriv_ricci_form`:
    `radialDeriv(log det g̃) = 2(θ_B − n) + radialDeriv(log det(g∘exp))`, a *first-derivative* `θ_B`
    identity), whereas the `A = [½Σ(gⁱⁱ−1) − …]` and deviation `(gⁱʲ−δ)` terms are carried
    SYMBOLICALLY in the `(gⁱʲ, Γ)` representation.  The two representations coincide only through the
    point-`0` RNC 2-jets — there is NO general-`v` algebraic transport equation, and no general-`v`
    Taylor-`o(r²)` framework, in the library (the RNC bricks state pointwise-at-`0` derivatives
    `∂∂f(0)=…`, e.g. `rnc_gInv_hessian`, `pd_christoffel_solve`, `sqrtdet_pd_pd`, NOT a function-level
    `f(v) = jet + o(r²)`).  So the full `= 0` stays CHECKPOINTED.

  • ROUTE (a) — the pointwise-at-`0` jet face — is what this file advances.  The DIAGONAL (`v=0`)
    face `totalRadialO1_coeff(0) = 0` was landed at c5 (`totalRadialO1_coeff_center_vanishes`).  This
    file lands the NEXT ORDER: the **GRADIENT at the centre**
        `∂_e totalRadialO1_coeff g gi Θ u (0) = ∂_e w₀(0)`   (`totalRadialO1_coeff_center_grad`),
    i.e. under the RNC-centre data (`gⁱʲ(0)=δ`, `∂gⁱʲ(0)=0`, `Γ(0)=0`) EVERY curvature-carrying term
    (the metric-trace `A`-term, the deviation term) contributes `0` to the gradient, and the whole
    gradient collapses to the gradient of the leading folded coefficient `w₀`.  Hence
        `∂_e totalRadialO1_coeff g gi Θ u (0) = 0`   (`totalRadialO1_coeff_center_grad_vanishes`)
    given the van-Vleck flatness datum `∂_e w₀(0) = 0` — the standard `w₀ = (det g̃)^{1/4} = 1+O(r²)`
    fact (the leading coefficient is flat at the centre), a genuine load-bearing input (for ARBITRARY
    `Θ, u` the gradient is `∂_e w₀(0) ≠ 0`).

  WHAT THIS LOCALIZES.  The gradient face shows the off-diagonal cancellation holds to FIRST order at
  the centre with NO curvature input beyond RNC flatness — curvature (Ricci) enters the off-diagonal
  cancellation ONLY at the HESSIAN (second-derivative) order.  That is the precise content of "the
  off-diagonal `O(1/t)` cancellation to leading van-Vleck order": the value (c5) and the gradient
  (here) are curvature-free consequences of the RNC gauge; the Ricci cancellation is the Hessian.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  [CHECKPOINT — the Hessian (curvature-order) face, the genuine next brick].  The remaining reachable
  order is `∂_a∂_b totalRadialO1_coeff(0) = 0`.  Its structure (derived, not yet formalized here):
      ∂_a∂_b totalRadialO1_coeff(0)
        = ∂_a∂_b A(0)·w₀(0)                              -- term (I): Ricci via `rnc_gInv_hessian`
                                                          --           (trace) + `pd_christoffel_solve`
          + [∂_a∂_b w₀(0) + ∂_b∂_a w₀(0)]                -- term (II): 2·Hess(w₀) at the centre
          + 0 ,                                          -- term (IV): deviation, `∂gⁱʲ(0)=0` kills it
  where `∂_a∂_b A(0) = ⅓ Ric_{ab} + (Christoffel-derivative contraction)` is a genuine Ricci
  contraction.  The `= 0` then needs the van-Vleck coefficient HESSIAN `∂_a∂_b w₀(0)` (the datum
  `w₀ = (det g̃)^{1/4}`, `Hess(w₀)(0) = compensating Ricci`) supplied so that term (I) + term (II)
  cancel — the SAME class of input (`sqrtdet_pd_pd`-style) as the transport equation, at Hessian order.
  The deviation term (IV) vanishing IS unconditional (`∂gⁱʲ(0)=0`).  This is the checkpointed brick.

  This is NOT `a₁ = R/6` (M6 parametrix convergence remains).  No axioms, no `sorry`, no vacuous hyps.
  The carried RNC-centre data (`hgi0`, `hdgi0`, `hΓ0`) is the SAME normal-coordinate gauge the √det
  chain carries; `hw0flat` is the standard van-Vleck-leading-coefficient flatness — all load-bearing.
  Grounded in Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.1.
-/
import Mathlib
import QIQTH.ParametrixResidualO1Total
import QIQTH.RNCInverseMetricJet
import QIQTH.VanVleckCancellation

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.RNCExpansion
open QIQTH.HeatResidualBound

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### Two reusable primitives -/

/-- **Coordinate-projection derivative at the centre.**  `∂_e (v ↦ vⁱ) (0) = δⁱ_e`. -/
private theorem pd_coord_at_zero (i e : Fin n) :
    pd (fun v : Point n => v i) e (0 : Point n) = if i = e then (1 : ℝ) else 0 := by
  simp only [pd]
  have hfun : (fun t => (Function.update (0 : Point n) e t) i)
      = fun t => if i = e then t else (0 : ℝ) := by
    funext t
    rw [Function.update_apply]
    by_cases h : i = e <;> simp [h]
  rw [hfun]
  by_cases h : i = e
  · subst h; simp
  · simp [h]

/-- **Gradient of the Euler radial derivative at the centre.**  For any smooth `w`,
    `∂_e (v ↦ (r∂_r w)(v)) (0) = ∂_e w (0)`.  The Euler field `r∂_r w = Σᵢ vⁱ ∂ᵢw` has, at `v=0`,
    only the `∂_e`-hitting-the-`vⁱ`-factor contribution survive (the `Σᵢ vⁱ ∂_e∂ᵢw` part carries a
    `vⁱ(0)=0`), leaving exactly `∂_e w(0)`. -/
private theorem pd_radialDeriv_at_zero (w : Point n → ℝ) (hw : ContDiff ℝ ⊤ w) (e : Fin n) :
    pd (fun v => radialDeriv w v) e (0 : Point n) = pd w e (0 : Point n) := by
  have hgoal : pd (fun v => ∑ i, v i * pd w i v) e (0 : Point n) = pd w e (0 : Point n) := by
    rw [pd_sum univ (fun i v => v i * pd w i v) e 0
          (fun i _ => (PdiffAt_of_contDiff (fun v => v i) (coord_contDiff i) e 0).mul
            (PdiffAt_pd w hw i e 0))]
    have hsummand : ∀ i, pd (fun v => v i * pd w i v) e (0 : Point n)
        = if i = e then pd w i (0 : Point n) else 0 := by
      intro i
      rw [pd_mul (fun v => v i) (fun v => pd w i v) e 0
            (PdiffAt_of_contDiff (fun v => v i) (coord_contDiff i) e 0)
            (PdiffAt_pd w hw i e 0),
          pd_coord_at_zero i e]
      by_cases h : i = e <;> simp [h]
    rw [Finset.sum_congr rfl (fun i _ => hsummand i),
        Finset.sum_ite_eq' univ e (fun i => pd w i (0 : Point n))]
    simp
  -- `radialDeriv w` is definitionally `fun v => ∑ i, v i * pd w i v`
  have hrw : (fun v : Point n => radialDeriv w v) = (fun v => ∑ i, v i * pd w i v) := rfl
  rw [hrw]; exact hgoal

/-! ### The gradient face of the off-diagonal `O(1/t)` cancellation -/

/-- **★ THE GRADIENT (first-derivative) FACE of the off-diagonal `O(1/t)` cancellation.**  At the RNC
    centre, with the normal-coordinate data `gⁱʲ(0)=δ` (`hgi0`), `∂gⁱʲ(0)=0` (`hdgi0`), `Γ(0)=0`
    (`hΓ0`), the gradient of the assembled leading `O(1/t)` coefficient collapses to the gradient of
    the leading folded coefficient `w₀ = foldedCoeff Θ u 0`:
        `∂_e totalRadialO1_coeff g gi Θ u (0) = ∂_e w₀(0)` .
    Every curvature-carrying summand — the metric-trace `A`-term `[½Σ(gⁱⁱ−1) − ½ΣgⁱʲΓv]·w₀` and the
    deviation term `½Σ(gⁱʲ−δ)(v∂w₀)` — contributes `0` to the gradient at the centre (`A(0)=0` and
    `∂_e A(0)=0`; the deviation is a product of two RNC-vanishing factors with `∂gⁱʲ(0)=0`), so the
    Euler radial term `(r∂_r w₀)` is the ONLY first-order survivor.  This extends the DIAGONAL value
    face `totalRadialO1_coeff_center_vanishes` by one order and shows the off-diagonal cancellation is
    curvature-free through first order — curvature enters only at the Hessian (see header CHECKPOINT).
    The carried RNC data is the same gauge the √det chain uses; all hypotheses load-bearing. -/
theorem totalRadialO1_coeff_center_grad
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw0 : ContDiff ℝ ⊤ (foldedCoeff Θ u 0))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (e : Fin n) :
    pd (fun v => totalRadialO1_coeff g gi Θ u v) e (0 : Point n)
      = pd (foldedCoeff Θ u 0) e (0 : Point n) := by
  -- abbreviations
  set W : Point n → ℝ := foldedCoeff Θ u 0 with hWdef
  -- PdiffAt of the atomic pieces at the centre
  have hPDgi : ∀ i j, PdiffAt (fun y => gi y i j) e (0 : Point n) :=
    fun i j => PdiffAt_of_contDiff _ (hgiC i j) e 0
  have hPDcoord : ∀ i, PdiffAt (fun v : Point n => v i) e (0 : Point n) :=
    fun i => PdiffAt_of_contDiff _ (coord_contDiff i) e 0
  have hPDW : PdiffAt W e (0 : Point n) := PdiffAt_of_contDiff _ hw0 e 0
  have hPDpdW : ∀ i, PdiffAt (fun v => pd W i v) e (0 : Point n) :=
    fun i => PdiffAt_pd W hw0 i e 0
  -- ══ TERM (I): the `A·w₀` term contributes 0 to the gradient. ══
  -- `A(0) = 0`
  have hAf0 : (1 / 2) * (∑ i, (gi (0 : Point n) i i - 1))
        - (1 / 2) * (∑ i, ∑ j, ∑ k, gi (0 : Point n) i j * christoffel g gi k i j (0 : Point n)
            * (0 : Point n) k) = 0 := by
    have h1 : (∑ i, (gi (0 : Point n) i i - 1)) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hgi0 i i]; simp
    have h2 : (∑ i, ∑ j, ∑ k, gi (0 : Point n) i j * christoffel g gi k i j (0 : Point n)
          * (0 : Point n) k) = 0 := by
      refine Finset.sum_eq_zero (fun i _ =>
        Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun k _ => ?_)))
      simp
    rw [h1, h2]; ring
  -- `∂_e A(0) = 0`
  -- first sum's gradient
  have hpd_s1 : pd (fun v => ∑ i, (gi v i i - 1)) e (0 : Point n) = 0 := by
    rw [pd_sum univ (fun i v => gi v i i - 1) e 0
          (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0))]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [pd_sub (fun v => gi v i i) (fun _ => (1 : ℝ)) e 0 (hPDgi i i)
          (PdiffAt_of_contDiff _ contDiff_const e 0), hdgi0 i i e, pd_const]
    ring
  -- second sum's gradient (the `ΣgⁱʲΓv` term)
  have hPDF : ∀ i j k, PdiffAt (fun v => gi v i j * christoffel g gi k i j v * v k) e (0 : Point n) :=
    fun i j k => ((hPDgi i j).mul (PdiffAt_of_contDiff _ (hC k i j) e 0)).mul (hPDcoord k)
  have hPDinner_k : ∀ i j, PdiffAt (fun v => ∑ k, gi v i j * christoffel g gi k i j v * v k)
      e (0 : Point n) := fun i j => PdiffAt_sum univ _ e 0 (fun k _ => hPDF i j k)
  have hPDinner_jk : ∀ i, PdiffAt (fun v => ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)
      e (0 : Point n) := fun i => PdiffAt_sum univ _ e 0 (fun j _ => hPDinner_k i j)
  have hpd_s2 : pd (fun v => ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)
      e (0 : Point n) = 0 := by
    rw [pd_sum univ _ e 0 (fun i _ => hPDinner_jk i)]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [pd_sum univ _ e 0 (fun j _ => hPDinner_k i j)]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [pd_sum univ _ e 0 (fun k _ => hPDF i j k)]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    -- `(gⁱʲ·Γ)·vᵏ`: both `Γ(0)=0` and `vᵏ(0)=0`, so the gradient is 0
    rw [pd_mul (fun v => gi v i j * christoffel g gi k i j v) (fun v => v k) e 0
          ((hPDgi i j).mul (PdiffAt_of_contDiff _ (hC k i j) e 0)) (hPDcoord k)]
    have hf0 : gi (0 : Point n) i j * christoffel g gi k i j (0 : Point n) = 0 := by
      rw [hΓ0 k i j]; ring
    rw [hf0]
    simp
  have hpdAf : pd (fun v => (1 / 2) * (∑ i, (gi v i i - 1))
        - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)) e (0 : Point n) = 0 := by
    rw [pd_sub _ _ e 0
          (PdiffAt_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0
            (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0))))
          (PdiffAt_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0 (fun i _ => hPDinner_jk i))),
        pd_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0
          (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0))),
        pd_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0 (fun i _ => hPDinner_jk i)),
        hpd_s1, hpd_s2]
    ring
  -- PdiffAt of the `A`-field
  have hPDA : PdiffAt (fun v => (1 / 2) * (∑ i, (gi v i i - 1))
        - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)) e (0 : Point n) :=
    (PdiffAt_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0
        (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0)))).sub
      (PdiffAt_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0 (fun i _ => hPDinner_jk i)))
  have hT1 : pd (fun v => ((1 / 2) * (∑ i, (gi v i i - 1))
        - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)) * W v)
      e (0 : Point n) = 0 := by
    rw [pd_mul _ W e 0 hPDA hPDW, hpdAf, hAf0]
    ring
  -- ══ TERM (II): the Euler radial term contributes `∂_e w₀(0)`. ══
  have hT2 : pd (fun v => radialDeriv W v) e (0 : Point n) = pd W e (0 : Point n) :=
    pd_radialDeriv_at_zero W hw0 e
  -- ══ TERM (IV): the deviation term contributes 0 (two RNC-vanishing factors, `∂gⁱʲ(0)=0`). ══
  have hPDR : ∀ i j, PdiffAt (fun v => v i * pd W j v + v j * pd W i v) e (0 : Point n) :=
    fun i j => ((hPDcoord i).mul (hPDpdW j)).add ((hPDcoord j).mul (hPDpdW i))
  have hPDD : ∀ i j, PdiffAt (fun v => gi v i j - (if i = j then (1 : ℝ) else 0)) e (0 : Point n) :=
    fun i j => (hPDgi i j).sub (PdiffAt_of_contDiff _ contDiff_const e 0)
  have hPDdev_j : ∀ i, PdiffAt (fun v => ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
      * (v i * pd W j v + v j * pd W i v)) e (0 : Point n) :=
    fun i => PdiffAt_sum univ _ e 0 (fun j _ => (hPDD i j).mul (hPDR i j))
  have hpd_dev : pd (fun v => ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd W j v + v j * pd W i v)) e (0 : Point n) = 0 := by
    rw [pd_sum univ _ e 0 (fun i _ => hPDdev_j i)]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [pd_sum univ _ e 0 (fun j _ => (hPDD i j).mul (hPDR i j))]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [pd_mul (fun v => gi v i j - (if i = j then (1 : ℝ) else 0))
          (fun v => v i * pd W j v + v j * pd W i v) e 0 (hPDD i j) (hPDR i j)]
    have hD0 : gi (0 : Point n) i j - (if i = j then (1 : ℝ) else 0) = 0 := by
      rw [hgi0 i j]; ring
    rw [hD0]
    simp
  have hT3 : pd (fun v => (1 / 2) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd W j v + v j * pd W i v))) e (0 : Point n) = 0 := by
    rw [pd_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0 (fun i _ => hPDdev_j i)), hpd_dev]
    ring
  -- ══ ASSEMBLE:  gradient = 0 + ∂_e w₀(0) + 0 = ∂_e w₀(0). ══
  have hPD1 : PdiffAt (fun v => ((1 / 2) * (∑ i, (gi v i i - 1))
        - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)) * W v)
      e (0 : Point n) := hPDA.mul hPDW
  have hPD2 : PdiffAt (fun v => radialDeriv W v) e (0 : Point n) := by
    have hrw : (fun v : Point n => radialDeriv W v) = (fun v => ∑ i, v i * pd W i v) := rfl
    rw [hrw]
    exact PdiffAt_sum univ (fun i v => v i * pd W i v) e 0
      (fun i _ => (hPDcoord i).mul (hPDpdW i))
  have hPD3 : PdiffAt (fun v => (1 / 2) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd W j v + v j * pd W i v))) e (0 : Point n) :=
    PdiffAt_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0 (fun i _ => hPDdev_j i))
  unfold totalRadialO1_coeff
  rw [pd_add _ _ e 0 (hPD1.add hPD2) hPD3, pd_add _ _ e 0 hPD1 hPD2, hT1, hT2, hT3]
  ring

/-- **★ THE OFF-DIAGONAL `O(1/t)` GRADIENT CANCELLATION at the centre.**  Composing the gradient face
    `totalRadialO1_coeff_center_grad` with the van-Vleck flatness datum `∂_e w₀(0) = 0` (the standard
    `w₀ = (det g̃)^{1/4} = 1 + O(r²)` — the leading folded coefficient is flat at the RNC centre):
        `∂_e totalRadialO1_coeff g gi Θ u (0) = 0` .
    This is the first-derivative extension of the diagonal value cancellation
    `totalRadialO1_coeff_center_vanishes`; together they establish the off-diagonal cancellation to
    FIRST order at the centre.  `hw0flat` is genuine and load-bearing (for arbitrary `Θ, u` the
    gradient is `∂_e w₀(0) ≠ 0`).  NOT the full general-`v` `= 0` (ROUTE (b), no exact transport
    identity), NOT the Hessian/curvature order (header CHECKPOINT), NOT `a₁ = R/6`. -/
theorem totalRadialO1_coeff_center_grad_vanishes
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw0 : ContDiff ℝ ⊤ (foldedCoeff Θ u 0))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (e : Fin n) :
    pd (fun v => totalRadialO1_coeff g gi Θ u v) e (0 : Point n) = 0 := by
  rw [totalRadialO1_coeff_center_grad g gi Θ u hgiC hC hw0 hgi0 hdgi0 hΓ0 e]
  exact hw0flat e

end QIQTH.HeatResidualBound
