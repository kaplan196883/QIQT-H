/-
  OffDiagLittleOFiniteReg — brick R3c-2 of the RECENTER campaign: the FINITE-REGULARITY
  (`ContDiffAt`) version of the off-diagonal leading-term little-`o` capstone
  `totalRadialO1_coeff_isLittleO`.

  The `⊤`-version (`ParametrixOffDiagLittleO`) proves, near the RNC centre,
      `totalRadialO1_coeff g gi Θ u  =o[𝓝 0]  (fun v => ‖v‖²)`
  from the value (c5) / gradient (c6) / Hessian (c7) cancellations fed into the general-`v` second-order
  Peano Taylor expansion (`RNCExpansion.pd_taylor_two_peano`, already stated at `ContDiffAt ℝ 2`).
  It carries `ContDiff ℝ ⊤` on the metric `g`, inverse metric `gi`, Christoffel `Γ`, and the folded
  coefficient `w₀`.

  This file re-derives the SAME conclusion with those hypotheses weakened to their TRUE MINIMAL finite
  order at the single base point `0` (exactly what the q-centered pullback metric `g̃` supplies):
    • `g`  : `ContDiffAt ℝ 2` at `0`  (used only by the term-(I) Ricci converter),
    • `gi` : `ContDiffAt ℝ 2` at `0`,
    • `Γ`  : `ContDiffAt ℝ 2` at `0`,
    • `w₀` : `ContDiffAt ℝ 3` at `0`  (the coefficient contains `Γ = ∂g` and the radial `r∂_r w₀`, whose
             Hessian needs the SECOND derivative of `∂w₀`, i.e. `w₀ ∈ C³`).

  All of the ⊤ proof skeletons (c5/c6/c7 + the inverse-metric sign flip + the `A`-Hessian Ricci
  converter) are ported here, swapping the `ContDiff ⊤ → PdiffAt` extractors for R1's finite-regularity
  `PdiffAt_of_contDiffAt` / `PdiffAt_pd_of_contDiffAt` (plus a local `ContDiffAt ℝ 3 → ContDiffAt ℝ 2`
  third-partial extractor), and localising the two funext-over-all-`y` steps (`pd_pd_sum`,
  `pd_pd_radialDeriv`, `pd_pd_gInv`) to germ-at-`0` `EventuallyEq`s (the metric is only `C²` near `0`).

  No `sorry`, no new axioms, no vacuous hypotheses — every regularity hypothesis is genuinely used.
  NOT `a₁ = R/6` (M6 parametrix convergence remains); NOT the exact general-`v` transport identity.
-/
import Mathlib
import QIQTH.ParametrixOffDiagLittleO
import QIQTH.RNCTaylorPeano
import QIQTH.LaplaceBeltramiFiniteReg
import QIQTH.RNCExpansionFiniteReg
import QIQTH.RNCInverseMetricJet
import QIQTH.PullbackMetric

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.RNCExpansion QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### Finite-regularity extractors and second-derivative primitives -/

/-- `ContDiffAt ℝ 2` of a coordinate projection at `0`. -/
private theorem coordCDA2 (i : Fin n) : ContDiffAt ℝ 2 (fun v : Point n => v i) 0 :=
  (coord_contDiff i).contDiffAt.of_le le_top

/-- **Third-partial extractor.**  `ContDiffAt ℝ 3 f x → ContDiffAt ℝ 2 (fun y => pd f m y) x` — one
    order above R1's `PdiffAt_pd_of_contDiffAt`.  `fderiv f` is `C²` at `x`, applying it to the constant
    basis covector `eₘ` is `C²`, and this equals `pd f m` on the differentiable germ at `x`. -/
private theorem contDiffAt_pd_of_contDiffAt3 (f : Point n → ℝ) (m : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 3 f x) : ContDiffAt ℝ 2 (fun y => pd f m y) x := by
  have hfd2 : ContDiffAt ℝ 2 (fun y => fderiv ℝ f y) x := hf.fderiv_right (m := 2) (by norm_num)
  have happ : ContDiffAt ℝ 2 (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) x :=
    hfd2.clm_apply contDiffAt_const
  have hdf_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have e1 : (fun y => pd f m y) =ᶠ[nhds x] (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f m y hy
  exact happ.congr_of_eventuallyEq e1

/-- Second-derivative additivity at `0`, `C²` version (germ-localised). -/
private theorem pd_pd_add_C2 (f h : Point n → ℝ) (a b : Fin n)
    (hf : ContDiffAt ℝ 2 f 0) (hh : ContDiffAt ℝ 2 h 0) :
    pd (fun y => pd (fun w => f w + h w) b y) a (0 : Point n)
      = pd (fun y => pd f b y) a 0 + pd (fun y => pd h b y) a 0 := by
  have hev : ∀ᶠ y in nhds (0 : Point n), DifferentiableAt ℝ f y ∧ DifferentiableAt ℝ h y := by
    filter_upwards [hf.eventually (by norm_num), hh.eventually (by norm_num)] with y hyf hyh
      using ⟨hyf.differentiableAt (by norm_num), hyh.differentiableAt (by norm_num)⟩
  have hgerm : (fun y => pd (fun w => f w + h w) b y)
      =ᶠ[nhds (0 : Point n)] (fun y => pd f b y + pd h b y) := by
    filter_upwards [hev] with y hy
    exact pd_add f h b y (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt f b y hy.1) (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt h b y hy.2)
  rw [pd_congr a 0 hgerm, pd_add (fun y => pd f b y) (fun y => pd h b y) a 0
        (PdiffAt_pd_of_contDiffAt f b a 0 hf) (PdiffAt_pd_of_contDiffAt h b a 0 hh)]

/-- Second-derivative subtractivity at `0`, `C²` version. -/
private theorem pd_pd_sub_C2 (f h : Point n → ℝ) (a b : Fin n)
    (hf : ContDiffAt ℝ 2 f 0) (hh : ContDiffAt ℝ 2 h 0) :
    pd (fun y => pd (fun w => f w - h w) b y) a (0 : Point n)
      = pd (fun y => pd f b y) a 0 - pd (fun y => pd h b y) a 0 := by
  have hev : ∀ᶠ y in nhds (0 : Point n), DifferentiableAt ℝ f y ∧ DifferentiableAt ℝ h y := by
    filter_upwards [hf.eventually (by norm_num), hh.eventually (by norm_num)] with y hyf hyh
      using ⟨hyf.differentiableAt (by norm_num), hyh.differentiableAt (by norm_num)⟩
  have hgerm : (fun y => pd (fun w => f w - h w) b y)
      =ᶠ[nhds (0 : Point n)] (fun y => pd f b y - pd h b y) := by
    filter_upwards [hev] with y hy
    exact pd_sub f h b y (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt f b y hy.1) (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt h b y hy.2)
  rw [pd_congr a 0 hgerm, pd_sub (fun y => pd f b y) (fun y => pd h b y) a 0
        (PdiffAt_pd_of_contDiffAt f b a 0 hf) (PdiffAt_pd_of_contDiffAt h b a 0 hh)]

/-- Second-derivative scalar-multiplicativity at `0`, `C²` version. -/
private theorem pd_pd_const_mul_C2 (c : ℝ) (f : Point n → ℝ) (a b : Fin n) (hf : ContDiffAt ℝ 2 f 0) :
    pd (fun y => pd (fun w => c * f w) b y) a (0 : Point n) = c * pd (fun y => pd f b y) a 0 := by
  have hev : ∀ᶠ y in nhds (0 : Point n), DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have hgerm : (fun y => pd (fun w => c * f w) b y)
      =ᶠ[nhds (0 : Point n)] (fun y => c * pd f b y) := by
    filter_upwards [hev] with y hy
    exact pd_const_mul c f b y (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt f b y hy)
  rw [pd_congr a 0 hgerm, pd_const_mul c (fun y => pd f b y) a 0 (PdiffAt_pd_of_contDiffAt f b a 0 hf)]

/-- Second-derivative commutes with a finite sum at `0`, `C²` version (germ-localised). -/
private theorem pd_pd_sum_C2 {ι : Type*} (s : Finset ι) (F : ι → Point n → ℝ) (a b : Fin n)
    (hF : ∀ k ∈ s, ContDiffAt ℝ 2 (F k) 0) :
    pd (fun y => pd (fun v => ∑ k ∈ s, F k v) b y) a (0 : Point n)
      = ∑ k ∈ s, pd (fun y => pd (F k) b y) a 0 := by
  have hev : ∀ᶠ y in nhds (0 : Point n), ∀ k ∈ s, DifferentiableAt ℝ (F k) y := by
    rw [Filter.eventually_all_finset]
    intro k hk
    filter_upwards [(hF k hk).eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have hgerm : (fun y => pd (fun v => ∑ k ∈ s, F k v) b y)
      =ᶠ[nhds (0 : Point n)] (fun y => ∑ k ∈ s, pd (F k) b y) := by
    filter_upwards [hev] with y hy
    exact pd_sum s F b y (fun k hk => QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt (F k) b y (hy k hk))
  rw [pd_congr a 0 hgerm,
      pd_sum s (fun k y => pd (F k) b y) a 0 (fun k hk => PdiffAt_pd_of_contDiffAt (F k) b a 0 (hF k hk))]

/-- Second derivative of a constant vanishes. -/
private theorem pd_pd_const_zero' (c : ℝ) (a b : Fin n) :
    pd (fun y => pd (fun _ : Point n => c) b y) a (0 : Point n) = 0 := by
  have h : (fun y => pd (fun _ : Point n => c) b y) = (fun _ : Point n => (0 : ℝ)) :=
    funext (fun y => pd_const c b y)
  rw [h]; exact pd_const 0 a 0

/-- Second derivative of a coordinate function vanishes. -/
private theorem pd_pd_coord_zero' (i a b : Fin n) :
    pd (fun y => pd (fun v : Point n => v i) b y) a (0 : Point n) = 0 := by
  have h : (fun y => pd (fun v : Point n => v i) b y)
      = (fun _ : Point n => (if i = b then (1 : ℝ) else 0)) :=
    funext (fun y => QIQTH.LaplaceBeltrami.pd_coord i b y)
  rw [h]; exact pd_const _ a 0

/-! ### The gradient (c6) face at finite regularity -/

/-- Gradient of the Euler radial derivative at the centre, `C²` version. -/
private theorem pd_radialDeriv_at_zero_C2 (w : Point n → ℝ) (hw : ContDiffAt ℝ 2 w 0) (e : Fin n) :
    pd (fun v => radialDeriv w v) e (0 : Point n) = pd w e (0 : Point n) := by
  have hgoal : pd (fun v => ∑ i, v i * pd w i v) e (0 : Point n) = pd w e (0 : Point n) := by
    rw [pd_sum univ (fun i v => v i * pd w i v) e 0
          (fun i _ => (PdiffAt_of_contDiff (fun v => v i) (coord_contDiff i) e 0).mul
            (PdiffAt_pd_of_contDiffAt w i e 0 hw))]
    have hsummand : ∀ i, pd (fun v => v i * pd w i v) e (0 : Point n)
        = if i = e then pd w i (0 : Point n) else 0 := by
      intro i
      rw [pd_mul (fun v => v i) (fun v => pd w i v) e 0
            (PdiffAt_of_contDiff (fun v => v i) (coord_contDiff i) e 0)
            (PdiffAt_pd_of_contDiffAt w i e 0 hw),
          QIQTH.LaplaceBeltrami.pd_coord i e 0]
      by_cases h : i = e <;> simp [h]
    rw [Finset.sum_congr rfl (fun i _ => hsummand i),
        Finset.sum_ite_eq' univ e (fun i => pd w i (0 : Point n))]
    simp
  have hrw : (fun v : Point n => radialDeriv w v) = (fun v => ∑ i, v i * pd w i v) := rfl
  rw [hrw]; exact hgoal

/-- **The gradient face of the off-diagonal `O(1/t)` cancellation, `C²`.**  Verbatim port of
    `totalRadialO1_coeff_center_grad` with the ⊤ extractors swapped for R1's finite-regularity ones
    (`gi, Γ ∈ C¹`, `w₀ ∈ C²`, all at `0`). -/
theorem totalRadialO1_coeff_center_grad_C2
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hgi1 : ∀ i j, ContDiffAt ℝ 1 (fun y => gi y i j) 0)
    (hC1 : ∀ a b c, ContDiffAt ℝ 1 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) 0)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (e : Fin n) :
    pd (fun v => totalRadialO1_coeff g gi Θ u v) e (0 : Point n)
      = pd (foldedCoeff Θ u 0) e (0 : Point n) := by
  set W : Point n → ℝ := foldedCoeff Θ u 0 with hWdef
  have hPDgi : ∀ i j, PdiffAt (fun y => gi y i j) e (0 : Point n) :=
    fun i j => PdiffAt_of_contDiffAt _ e 0 (hgi1 i j)
  have hPDcoord : ∀ i, PdiffAt (fun v : Point n => v i) e (0 : Point n) :=
    fun i => PdiffAt_of_contDiff _ (coord_contDiff i) e 0
  have hPDW : PdiffAt W e (0 : Point n) := PdiffAt_of_contDiffAt _ e 0 (hw0.of_le (by norm_num))
  have hPDpdW : ∀ i, PdiffAt (fun v => pd W i v) e (0 : Point n) :=
    fun i => PdiffAt_pd_of_contDiffAt W i e 0 hw0
  -- TERM (I): the `A·w₀` term contributes 0 to the gradient.
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
  have hpd_s1 : pd (fun v => ∑ i, (gi v i i - 1)) e (0 : Point n) = 0 := by
    rw [pd_sum univ (fun i v => gi v i i - 1) e 0
          (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0))]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [pd_sub (fun v => gi v i i) (fun _ => (1 : ℝ)) e 0 (hPDgi i i)
          (PdiffAt_of_contDiff _ contDiff_const e 0), hdgi0 i i e, pd_const]
    ring
  have hPDF : ∀ i j k, PdiffAt (fun v => gi v i j * christoffel g gi k i j v * v k) e (0 : Point n) :=
    fun i j k => ((hPDgi i j).mul (PdiffAt_of_contDiffAt _ e 0 (hC1 k i j))).mul (hPDcoord k)
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
    rw [pd_mul (fun v => gi v i j * christoffel g gi k i j v) (fun v => v k) e 0
          ((hPDgi i j).mul (PdiffAt_of_contDiffAt _ e 0 (hC1 k i j))) (hPDcoord k)]
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
  have hT2 : pd (fun v => radialDeriv W v) e (0 : Point n) = pd W e (0 : Point n) :=
    pd_radialDeriv_at_zero_C2 W hw0 e
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

/-- **The off-diagonal `O(1/t)` gradient cancellation at the centre, `C²`.** -/
theorem totalRadialO1_coeff_center_grad_vanishes_C2
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hgi1 : ∀ i j, ContDiffAt ℝ 1 (fun y => gi y i j) 0)
    (hC1 : ∀ a b c, ContDiffAt ℝ 1 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) 0)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (e : Fin n) :
    pd (fun v => totalRadialO1_coeff g gi Θ u v) e (0 : Point n) = 0 := by
  rw [totalRadialO1_coeff_center_grad_C2 g gi Θ u hgi1 hC1 hw0 hgi0 hdgi0 hΓ0 e]
  exact hw0flat e

/-! ### The Hessian (c7) face at finite regularity -/

/-- The metric-trace / connection field `A`. -/
private noncomputable def coeffAF (g gi : Point n → Fin n → Fin n → ℝ) (v : Point n) : ℝ :=
  (1 / 2) * (∑ i, (gi v i i - 1))
    - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)

/-- The deviation field `Dev`. -/
private noncomputable def coeffDevF (gi : Point n → Fin n → Fin n → ℝ) (W : Point n → ℝ)
    (v : Point n) : ℝ :=
  (1 / 2) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
      * (v i * pd W j v + v j * pd W i v))

private theorem coeff_split_F (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) :
    (fun v => totalRadialO1_coeff g gi Θ u v)
      = (fun v => coeffAF g gi v * foldedCoeff Θ u 0 v + radialDeriv (foldedCoeff Θ u 0) v
          + coeffDevF gi (foldedCoeff Θ u 0) v) := by
  funext v; unfold totalRadialO1_coeff coeffAF coeffDevF; ring

private theorem coeffAF_contDiffAt2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hgi2 : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hC2 : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0) :
    ContDiffAt ℝ 2 (fun v => coeffAF g gi v) 0 := by
  unfold coeffAF
  refine (contDiffAt_const.mul (ContDiffAt.sum fun i _ => (hgi2 i i).sub contDiffAt_const)).sub
    (contDiffAt_const.mul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ContDiffAt.sum fun k _ => ?_))
  exact ((hgi2 i j).mul (hC2 k i j)).mul (coordCDA2 k)

private theorem radialDeriv_contDiffAt2 (W : Point n → ℝ) (hW : ContDiffAt ℝ 3 W 0) :
    ContDiffAt ℝ 2 (fun v => radialDeriv W v) 0 := by
  have hrw : (fun v : Point n => radialDeriv W v) = (fun v => ∑ i, v i * pd W i v) := rfl
  rw [hrw]
  exact ContDiffAt.sum fun i _ => (coordCDA2 i).mul (contDiffAt_pd_of_contDiffAt3 W i 0 hW)

private theorem coeffDevF_contDiffAt2 (gi : Point n → Fin n → Fin n → ℝ) (W : Point n → ℝ)
    (hgi2 : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0) (hW : ContDiffAt ℝ 3 W 0) :
    ContDiffAt ℝ 2 (fun v => coeffDevF gi W v) 0 := by
  unfold coeffDevF
  refine contDiffAt_const.mul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ?_)
  exact ((hgi2 i j).sub contDiffAt_const).mul
    (((coordCDA2 i).mul (contDiffAt_pd_of_contDiffAt3 W j 0 hW)).add
      ((coordCDA2 j).mul (contDiffAt_pd_of_contDiffAt3 W i 0 hW)))

private theorem coeffAF_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0) :
    coeffAF g gi (0 : Point n) = 0 := by
  unfold coeffAF
  have h1 : (∑ i, (gi (0 : Point n) i i - 1)) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hgi0 i i]; simp
  have h2 : (∑ i, ∑ j, ∑ k, gi (0 : Point n) i j * christoffel g gi k i j 0 * (0 : Point n) k) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => by simp
  rw [h1, h2]; ring

private theorem pd_coeffAF_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hgi1 : ∀ i j, ContDiffAt ℝ 1 (fun y => gi y i j) 0)
    (hC1 : ∀ a b c, ContDiffAt ℝ 1 (fun y => christoffel g gi a b c y) 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) (e : Fin n) :
    pd (coeffAF g gi) e (0 : Point n) = 0 := by
  have hPDgi : ∀ i j, PdiffAt (fun y => gi y i j) e (0 : Point n) :=
    fun i j => PdiffAt_of_contDiffAt _ e 0 (hgi1 i j)
  have hPDcoord : ∀ i, PdiffAt (fun v : Point n => v i) e (0 : Point n) :=
    fun i => PdiffAt_of_contDiff _ (coord_contDiff i) e 0
  have hpd_s1 : pd (fun v => ∑ i, (gi v i i - 1)) e (0 : Point n) = 0 := by
    rw [pd_sum univ (fun i v => gi v i i - 1) e 0
          (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0))]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [pd_sub (fun v => gi v i i) (fun _ => (1 : ℝ)) e 0 (hPDgi i i)
          (PdiffAt_of_contDiff _ contDiff_const e 0), hdgi0 i i e, pd_const]
    ring
  have hPDF : ∀ i j k,
      PdiffAt (fun v => gi v i j * christoffel g gi k i j v * v k) e (0 : Point n) :=
    fun i j k => ((hPDgi i j).mul (PdiffAt_of_contDiffAt _ e 0 (hC1 k i j))).mul (hPDcoord k)
  have hPDinner_k : ∀ i j,
      PdiffAt (fun v => ∑ k, gi v i j * christoffel g gi k i j v * v k) e (0 : Point n) :=
    fun i j => PdiffAt_sum univ _ e 0 (fun k _ => hPDF i j k)
  have hPDinner_jk : ∀ i,
      PdiffAt (fun v => ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) e (0 : Point n) :=
    fun i => PdiffAt_sum univ _ e 0 (fun j _ => hPDinner_k i j)
  have hpd_s2 : pd (fun v => ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)
      e (0 : Point n) = 0 := by
    rw [pd_sum univ _ e 0 (fun i _ => hPDinner_jk i)]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [pd_sum univ _ e 0 (fun j _ => hPDinner_k i j)]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [pd_sum univ _ e 0 (fun k _ => hPDF i j k)]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [pd_mul (fun v => gi v i j * christoffel g gi k i j v) (fun v => v k) e 0
          ((hPDgi i j).mul (PdiffAt_of_contDiffAt _ e 0 (hC1 k i j))) (hPDcoord k)]
    have hf0 : gi (0 : Point n) i j * christoffel g gi k i j (0 : Point n) = 0 := by
      rw [hΓ0 k i j]; ring
    rw [hf0]; simp
  unfold coeffAF
  rw [pd_sub _ _ e 0
        (PdiffAt_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0
          (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0))))
        (PdiffAt_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0 (fun i _ => hPDinner_jk i))),
      pd_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0
        (fun i _ => (hPDgi i i).sub (PdiffAt_of_contDiff _ contDiff_const e 0))),
      pd_const_mul _ _ e 0 (PdiffAt_sum univ _ e 0 (fun i _ => hPDinner_jk i)),
      hpd_s1, hpd_s2]
  ring

/-- Term (II) — the Euler radial Hessian at the centre, `C³` version. -/
private theorem pd_pd_radialDeriv_C2 (W : Point n → ℝ) (hW : ContDiffAt ℝ 3 W 0) (a b : Fin n) :
    pd (fun y => pd (fun v => radialDeriv W v) b y) a (0 : Point n)
      = pd (fun y => pd W b y) a 0 + pd (fun y => pd W a y) b 0 := by
  have hrw : (fun v : Point n => radialDeriv W v) = (fun v => ∑ i, v i * pd W i v) := rfl
  rw [hrw]
  have hW2ev : ∀ᶠ y in nhds (0 : Point n), ContDiffAt ℝ 2 W y :=
    (hW.of_le (by norm_num)).eventually (by norm_num)
  have hinner : (fun y => pd (fun v => ∑ i, v i * pd W i v) b y)
      =ᶠ[nhds (0 : Point n)] (fun y => ∑ i, pd (fun v => v i * pd W i v) b y) := by
    filter_upwards [hW2ev] with y hy
    exact pd_sum univ (fun i v => v i * pd W i v) b y
      (fun i _ => (PdiffAt_of_contDiff (fun v => v i) (coord_contDiff i) b y).mul
        (PdiffAt_pd_of_contDiffAt W i b y hy))
  rw [pd_congr a 0 hinner,
      pd_sum univ (fun i y => pd (fun v => v i * pd W i v) b y) a 0
        (fun i _ => PdiffAt_pd_of_contDiffAt (fun v => v i * pd W i v) b a 0
          ((coordCDA2 i).mul (contDiffAt_pd_of_contDiffAt3 W i 0 hW)))]
  have hsummand : ∀ i, pd (fun y => pd (fun v => v i * pd W i v) b y) a (0 : Point n)
      = (if i = b then (1 : ℝ) else 0) * pd (fun y => pd W i y) a 0
        + (if i = a then (1 : ℝ) else 0) * pd (fun y => pd W i y) b 0 := by
    intro i
    rw [QIQTH.LaplaceBeltrami.pd_pd_mul_C2 (fun v => v i) (fun v => pd W i v) a b 0
          (coordCDA2 i) (contDiffAt_pd_of_contDiffAt3 W i 0 hW),
        pd_pd_coord_zero' i a b, QIQTH.LaplaceBeltrami.pd_coord i b 0,
        QIQTH.LaplaceBeltrami.pd_coord i a 0]
    have hc0 : (0 : Point n) i = 0 := rfl
    rw [hc0]; ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i), Finset.sum_add_distrib]
  congr 1
  · rw [show (∑ i, (if i = b then (1 : ℝ) else 0) * pd (fun y => pd W i y) a 0)
          = ∑ i, (if i = b then pd (fun y => pd W i y) a 0 else 0) from
        Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring),
      Finset.sum_ite_eq' univ b (fun i => pd (fun y => pd W i y) a 0)]
    simp
  · rw [show (∑ i, (if i = a then (1 : ℝ) else 0) * pd (fun y => pd W i y) b 0)
          = ∑ i, (if i = a then pd (fun y => pd W i y) b 0 else 0) from
        Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring),
      Finset.sum_ite_eq' univ a (fun i => pd (fun y => pd W i y) b 0)]
    simp

/-- Term (I) — the `A·w₀` Hessian at the centre collapses to `∂_a∂_b A(0)·w₀(0)`, `C²` version. -/
private theorem pd_pd_coeffA_mul_C2 (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ)
    (hgi2 : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hC2 : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) 0)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) (a b : Fin n) :
    pd (fun y => pd (fun v => coeffAF g gi v * foldedCoeff Θ u 0 v) b y) a (0 : Point n)
      = pd (fun y => pd (coeffAF g gi) b y) a 0 * foldedCoeff Θ u 0 0 := by
  have hgi1 : ∀ i j, ContDiffAt ℝ 1 (fun y => gi y i j) 0 := fun i j => (hgi2 i j).of_le (by norm_num)
  have hC1 : ∀ a b c, ContDiffAt ℝ 1 (fun y => christoffel g gi a b c y) 0 :=
    fun a b c => (hC2 a b c).of_le (by norm_num)
  have hA0 : coeffAF g gi (0 : Point n) = 0 := coeffAF_zero g gi hgi0
  have hpdAa : pd (coeffAF g gi) a (0 : Point n) = 0 := pd_coeffAF_zero g gi hgi1 hC1 hdgi0 hΓ0 a
  have hpdAb : pd (coeffAF g gi) b (0 : Point n) = 0 := pd_coeffAF_zero g gi hgi1 hC1 hdgi0 hΓ0 b
  rw [QIQTH.LaplaceBeltrami.pd_pd_mul_C2 (coeffAF g gi) (foldedCoeff Θ u 0) a b 0
        (coeffAF_contDiffAt2 g gi hgi2 hC2) hw0, hpdAa, hpdAb, hA0]
  ring

/-- Term (IV) — the deviation Hessian at the centre vanishes unconditionally, `C³` version. -/
private theorem pd_pd_coeffDev_C2 (gi : Point n → Fin n → Fin n → ℝ) (W : Point n → ℝ)
    (hgi2 : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0) (hW : ContDiffAt ℝ 3 W 0)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0) (a b : Fin n) :
    pd (fun y => pd (fun v => coeffDevF gi W v) b y) a (0 : Point n) = 0 := by
  unfold coeffDevF
  have hgiev : ∀ᶠ y in nhds (0 : Point n), ∀ i j, DifferentiableAt ℝ (fun v => gi v i j) y := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    filter_upwards [(hgi2 i j).eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have hWev : ∀ᶠ y in nhds (0 : Point n), ∀ i, DifferentiableAt ℝ (fun v => pd W i v) y := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [hW.eventually (by norm_num)] with y hy
      using (contDiffAt_pd_of_contDiffAt3 W i y hy).differentiableAt (by norm_num)
  have hSPd : ∀ y, (∀ i j, DifferentiableAt ℝ (fun v => gi v i j) y)
      → (∀ i, DifferentiableAt ℝ (fun v => pd W i v) y)
      → PdiffAt (fun v => ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
          * (v i * pd W j v + v j * pd W i v)) b y := by
    intro y hgiy hWy
    refine PdiffAt_sum univ _ b y (fun i _ => PdiffAt_sum univ _ b y (fun j _ => ?_))
    exact ((QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt (fun v => gi v i j) b y (hgiy i j)).sub
        (PdiffAt_of_contDiff _ contDiff_const b y)).mul
      (((PdiffAt_of_contDiff (fun v => v i) (coord_contDiff i) b y).mul
          (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt (fun v => pd W j v) b y (hWy j))).add
       ((PdiffAt_of_contDiff (fun v => v j) (coord_contDiff j) b y).mul
          (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt (fun v => pd W i v) b y (hWy i))))
  have hSc2 : ContDiffAt ℝ 2 (fun v => ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
      * (v i * pd W j v + v j * pd W i v)) 0 :=
    ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
      ((hgi2 i j).sub contDiffAt_const).mul
        (((coordCDA2 i).mul (contDiffAt_pd_of_contDiffAt3 W j 0 hW)).add
          ((coordCDA2 j).mul (contDiffAt_pd_of_contDiffAt3 W i 0 hW)))
  have hinner : (fun y => pd (fun v => (1 / 2 : ℝ) * ∑ i, ∑ j,
        (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * pd W j v + v j * pd W i v)) b y)
      =ᶠ[nhds (0 : Point n)] (fun y => (1 / 2 : ℝ) * pd (fun v => ∑ i, ∑ j,
        (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * pd W j v + v j * pd W i v)) b y) := by
    filter_upwards [hgiev, hWev] with y hgiy hWy
    exact pd_const_mul _ _ b y (hSPd y hgiy hWy)
  rw [pd_congr a 0 hinner, pd_const_mul _ _ a 0 (PdiffAt_pd_of_contDiffAt _ b a 0 hSc2)]
  rw [show (fun v => ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd W j v + v j * pd W i v))
      = (fun v => ∑ i, (fun v' => ∑ j, (gi v' i j - (if i = j then (1 : ℝ) else 0))
        * (v' i * pd W j v' + v' j * pd W i v')) v) from rfl]
  rw [pd_pd_sum_C2 univ (fun i v => ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd W j v + v j * pd W i v)) a b
        (fun i _ => ContDiffAt.sum fun j _ =>
          ((hgi2 i j).sub contDiffAt_const).mul
            (((coordCDA2 i).mul (contDiffAt_pd_of_contDiffAt3 W j 0 hW)).add
              ((coordCDA2 j).mul (contDiffAt_pd_of_contDiffAt3 W i 0 hW))))]
  rw [Finset.sum_eq_zero (fun i _ => ?_), mul_zero]
  rw [pd_pd_sum_C2 univ (fun j v => (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd W j v + v j * pd W i v)) a b
        (fun j _ => ((hgi2 i j).sub contDiffAt_const).mul
          (((coordCDA2 i).mul (contDiffAt_pd_of_contDiffAt3 W j 0 hW)).add
            ((coordCDA2 j).mul (contDiffAt_pd_of_contDiffAt3 W i 0 hW))))]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [QIQTH.LaplaceBeltrami.pd_pd_mul_C2 (fun v => gi v i j - (if i = j then (1 : ℝ) else 0))
        (fun v => v i * pd W j v + v j * pd W i v) a b 0
        ((hgi2 i j).sub contDiffAt_const)
        (((coordCDA2 i).mul (contDiffAt_pd_of_contDiffAt3 W j 0 hW)).add
          ((coordCDA2 j).mul (contDiffAt_pd_of_contDiffAt3 W i 0 hW)))]
  have hD0 : gi (0 : Point n) i j - (if i = j then (1 : ℝ) else 0) = 0 := by rw [hgi0 i j]; ring
  have hpdD : ∀ e, pd (fun v => gi v i j - (if i = j then (1 : ℝ) else 0)) e (0 : Point n) = 0 := by
    intro e
    rw [pd_sub (fun v => gi v i j) (fun _ => (if i = j then (1 : ℝ) else 0)) e 0
          (PdiffAt_of_contDiffAt _ e 0 ((hgi2 i j).of_le (by norm_num)))
          (PdiffAt_of_contDiff _ contDiff_const e 0),
        hdgi0 i j e, pd_const]
    ring
  have hR0 : (0 : Point n) i * pd W j (0 : Point n) + (0 : Point n) j * pd W i (0 : Point n) = 0 := by
    simp
  rw [hpdD a, hpdD b, hD0, hR0]
  ring

/-- **The Hessian decomposition of the off-diagonal `O(1/t)` coefficient, `C³` version.** -/
private theorem totalRadialO1_coeff_center_hessian_C3
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hgi2 : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hC2 : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (a b : Fin n) :
    pd (fun y => pd (fun v => totalRadialO1_coeff g gi Θ u v) b y) a (0 : Point n)
      = pd (fun y => pd (coeffAF g gi) b y) a 0 * foldedCoeff Θ u 0 0
        + (pd (fun y => pd (foldedCoeff Θ u 0) b y) a 0
           + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0) := by
  rw [coeff_split_F g gi Θ u]
  have hw02 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) 0 := hw0.of_le (by norm_num)
  have hT1 : ContDiffAt ℝ 2 (fun v => coeffAF g gi v * foldedCoeff Θ u 0 v) 0 :=
    (coeffAF_contDiffAt2 g gi hgi2 hC2).mul hw02
  have hT2 : ContDiffAt ℝ 2 (fun v => radialDeriv (foldedCoeff Θ u 0) v) 0 :=
    radialDeriv_contDiffAt2 (foldedCoeff Θ u 0) hw0
  have hT3 : ContDiffAt ℝ 2 (fun v => coeffDevF gi (foldedCoeff Θ u 0) v) 0 :=
    coeffDevF_contDiffAt2 gi (foldedCoeff Θ u 0) hgi2 hw0
  rw [pd_pd_add_C2 (fun v => coeffAF g gi v * foldedCoeff Θ u 0 v + radialDeriv (foldedCoeff Θ u 0) v)
        (fun v => coeffDevF gi (foldedCoeff Θ u 0) v) a b (hT1.add hT2) hT3,
      pd_pd_add_C2 (fun v => coeffAF g gi v * foldedCoeff Θ u 0 v)
        (fun v => radialDeriv (foldedCoeff Θ u 0) v) a b hT1 hT2,
      pd_pd_coeffA_mul_C2 g gi Θ u hgi2 hC2 hw02 hgi0 hdgi0 hΓ0 a b,
      pd_pd_radialDeriv_C2 (foldedCoeff Θ u 0) hw0 a b,
      pd_pd_coeffDev_C2 gi (foldedCoeff Θ u 0) hgi2 hw0 hgi0 hdgi0 a b]
  ring

/-! ### The inverse-metric Hessian sign flip at finite regularity -/

/-- First derivative of the inverse metric vanishes at an RNC centre, `C¹` version. -/
private theorem pd_gInv_first_zero_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg1 : ∀ a b, ContDiffAt ℝ 1 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (i j e : Fin n) :
    pd (fun y => gi y i j) e (0 : Point n) = 0 := by
  have hzero : pd (fun y => ∑ σ, gi y i σ * g y σ j) e (0 : Point n) = 0 := by
    rw [show (fun y => ∑ σ, gi y i σ * g y σ j) = (fun _ => (if i = j then (1 : ℝ) else 0))
          from funext (fun y => hinv y i j)]
    exact pd_const _ e 0
  have hexp : pd (fun y => ∑ σ, gi y i σ * g y σ j) e (0 : Point n)
      = ∑ σ, (pd (fun y => gi y i σ) e 0 * g 0 σ j + gi 0 i σ * pd (fun y => g y σ j) e 0) := by
    rw [pd_sum univ _ e 0 (fun σ _ => (PdiffAt_of_contDiffAt _ e 0 (hgi1 i σ)).mul
          (PdiffAt_of_contDiffAt _ e 0 (hg1 σ j)))]
    exact Finset.sum_congr rfl (fun σ _ => pd_mul _ _ e 0
      (PdiffAt_of_contDiffAt _ e 0 (hgi1 i σ)) (PdiffAt_of_contDiffAt _ e 0 (hg1 σ j)))
  rw [hexp] at hzero
  simp only [hdg0, mul_zero, add_zero, hg0, Matrix.one_apply, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hzero
  exact hzero

/-- The inverse-metric Hessian is minus the metric Hessian at an RNC centre, `C²` version. -/
private theorem pd_pd_gInv_eq_neg_metric_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi2 : ∀ a b, ContDiffAt ℝ 2 (fun y => gi y a b) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (a b i j : Fin n) :
    pd (fun y => pd (fun w => gi w i j) b y) a (0 : Point n)
      = - pd (fun y => pd (fun w => g w i j) b y) a 0 := by
  have hg1 : ∀ p q, ContDiffAt ℝ 1 (fun y => g y p q) 0 := fun p q => (hg2 p q).of_le (by norm_num)
  have hgi1 : ∀ p q, ContDiffAt ℝ 1 (fun y => gi y p q) 0 := fun p q => (hgi2 p q).of_le (by norm_num)
  have hgi0 : ∀ p q, gi 0 p q = (1 : Matrix (Fin n) (Fin n) ℝ) p q := by
    intro p q
    have h := hinv 0 p q
    rw [show (∑ σ, gi 0 p σ * g 0 σ q) = gi 0 p q from by
          rw [Finset.sum_eq_single q (fun σ _ hσ => by
                rw [hg0 σ q, Matrix.one_apply_ne hσ, mul_zero])
              (fun hq => absurd (Finset.mem_univ q) hq)]
          rw [hg0 q q, Matrix.one_apply_eq, mul_one]] at h
    rw [Matrix.one_apply]; exact h
  have hdgi0 : ∀ p q e, pd (fun y => gi y p q) e 0 = 0 := fun p q e =>
    pd_gInv_first_zero_c2 g gi hg1 hgi1 hg0 hdg0 hinv p q e
  have hgev : ∀ᶠ y in nhds (0 : Point n), (∀ p q, DifferentiableAt ℝ (fun w => g w p q) y)
      ∧ (∀ p q, DifferentiableAt ℝ (fun w => gi w p q) y) := by
    have hg' : ∀ᶠ y in nhds (0 : Point n), ∀ p q, DifferentiableAt ℝ (fun w => g w p q) y := by
      rw [Filter.eventually_all]; intro p; rw [Filter.eventually_all]; intro q
      filter_upwards [(hg2 p q).eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
    have hgi' : ∀ᶠ y in nhds (0 : Point n), ∀ p q, DifferentiableAt ℝ (fun w => gi w p q) y := by
      rw [Filter.eventually_all]; intro p; rw [Filter.eventually_all]; intro q
      filter_upwards [(hgi2 p q).eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
    filter_upwards [hg', hgi'] with y h1 h2 using ⟨h1, h2⟩
  have hΨeq : (fun y => pd (fun w => ∑ σ, gi w i σ * g w σ j) b y)
      =ᶠ[nhds (0 : Point n)] (fun y => ∑ σ, (pd (fun w => gi w i σ) b y * g y σ j
                        + gi y i σ * pd (fun w => g w σ j) b y)) := by
    filter_upwards [hgev] with y hy
    rw [pd_sum univ _ b y (fun σ _ =>
          (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ b y (hy.2 i σ)).mul
            (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ b y (hy.1 σ j)))]
    exact Finset.sum_congr rfl (fun σ _ => pd_mul _ _ b y
      (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ b y (hy.2 i σ))
      (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ b y (hy.1 σ j)))
  have hconst2 : pd (fun y => pd (fun w => ∑ σ, gi w i σ * g w σ j) b y) a (0 : Point n) = 0 := by
    rw [show (fun y => pd (fun w => ∑ σ, gi w i σ * g w σ j) b y) = (fun _ => (0 : ℝ)) from
          funext (fun y => by
            rw [show (fun w => ∑ σ, gi w i σ * g w σ j)
                  = (fun _ => (if i = j then (1 : ℝ) else 0)) from funext (fun w => hinv w i j)]
            exact pd_const _ b y)]
    exact pd_const 0 a 0
  rw [pd_congr a 0 hΨeq] at hconst2
  have hσ : ∀ σ : Fin n,
      pd (fun y => pd (fun w => gi w i σ) b y * g y σ j + gi y i σ * pd (fun w => g w σ j) b y) a 0
        = pd (fun y => pd (fun w => gi w i σ) b y) a 0 * g 0 σ j
          + gi 0 i σ * pd (fun y => pd (fun w => g w σ j) b y) a 0 := by
    intro σ
    rw [pd_add _ _ a 0
          ((PdiffAt_pd_of_contDiffAt (fun w => gi w i σ) b a 0 (hgi2 i σ)).mul
            (PdiffAt_of_contDiffAt _ a 0 (hg1 σ j)))
          ((PdiffAt_of_contDiffAt _ a 0 (hgi1 i σ)).mul
            (PdiffAt_pd_of_contDiffAt (fun w => g w σ j) b a 0 (hg2 σ j))),
        pd_mul (fun y => pd (fun w => gi w i σ) b y) (fun y => g y σ j) a 0
          (PdiffAt_pd_of_contDiffAt (fun w => gi w i σ) b a 0 (hgi2 i σ))
          (PdiffAt_of_contDiffAt _ a 0 (hg1 σ j)),
        pd_mul (fun y => gi y i σ) (fun y => pd (fun w => g w σ j) b y) a 0
          (PdiffAt_of_contDiffAt _ a 0 (hgi1 i σ))
          (PdiffAt_pd_of_contDiffAt (fun w => g w σ j) b a 0 (hg2 σ j)),
        hdgi0 i σ b, hdgi0 i σ a, hdg0 σ j b]
    ring
  rw [pd_sum univ _ a 0 (fun σ _ =>
        ((PdiffAt_pd_of_contDiffAt (fun w => gi w i σ) b a 0 (hgi2 i σ)).mul
          (PdiffAt_of_contDiffAt _ a 0 (hg1 σ j))).add
        ((PdiffAt_of_contDiffAt _ a 0 (hgi1 i σ)).mul
          (PdiffAt_pd_of_contDiffAt (fun w => g w σ j) b a 0 (hg2 σ j)))),
      Finset.sum_congr rfl (fun σ _ => hσ σ)] at hconst2
  simp only [hg0, hgi0, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    at hconst2
  linarith [hconst2]

/-! ### The term-(I) Ricci value of the `A`-Hessian at finite regularity -/

private theorem coeffA1_hessian_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi2 : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0mat : ∀ i j, gi (0 : Point n) i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (a b : Fin n) :
    pd (fun y => pd (fun v => ∑ i, (gi v i i - 1)) b y) a (0 : Point n)
      = (2 / 3) * ricci g gi a b 0 := by
  rw [pd_pd_sum_C2 univ (fun i v => gi v i i - 1) a b (fun i _ => (hgi2 i i).sub contDiffAt_const)]
  have hi : ∀ i, pd (fun y => pd (fun v => gi v i i - 1) b y) a (0 : Point n)
      = - pd (fun y => pd (fun w => g w i i) b y) a 0 := by
    intro i
    rw [pd_pd_sub_C2 (fun v => gi v i i) (fun _ => (1 : ℝ)) a b (hgi2 i i) contDiffAt_const,
        pd_pd_const_zero' (1 : ℝ) a b, sub_zero,
        pd_pd_gInv_eq_neg_metric_c2 g gi hg2 hgi2 hg0 hdg0 hinv a b i i]
  have key : (∑ i, pd (fun y => pd (fun w => g w i i) b y) a 0) = -(2 / 3) * ricci g gi a b 0 :=
    rnc_htr_of_gauge_c2 g gi hg2 (fun p q => (hgi2 p q).of_le (by norm_num)) hgi0mat hdg0 hsymm hgauge a b
  rw [Finset.sum_congr rfl (fun i _ => hi i),
      show (∑ i, - pd (fun y => pd (fun w => g w i i) b y) a 0)
         = (-1 : ℝ) * ∑ i, pd (fun y => pd (fun w => g w i i) b y) a 0 from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring),
      key]
  ring

private theorem coeffA2_hessian_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hgi2 : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hC2 : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) (a b : Fin n) :
    pd (fun y => pd (fun v => ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) b y)
        a (0 : Point n)
      = (∑ i, pd (fun y => christoffel g gi a i i y) b 0)
        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0) := by
  rw [pd_pd_sum_C2 univ (fun i v => ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) a b
        (fun i _ => ContDiffAt.sum fun j _ => ContDiffAt.sum fun k _ =>
          ((hgi2 i j).mul (hC2 k i j)).mul (coordCDA2 k))]
  have hi : ∀ i,
      pd (fun y => pd (fun v => ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) b y) a 0
      = pd (fun y => christoffel g gi a i i y) b 0 + pd (fun y => christoffel g gi b i i y) a 0 := by
    intro i
    rw [pd_pd_sum_C2 univ (fun j v => ∑ k, gi v i j * christoffel g gi k i j v * v k) a b
          (fun j _ => ContDiffAt.sum fun k _ => ((hgi2 i j).mul (hC2 k i j)).mul (coordCDA2 k))]
    have hj : ∀ j,
        pd (fun y => pd (fun v => ∑ k, gi v i j * christoffel g gi k i j v * v k) b y) a 0
        = (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi a i j y) b 0
          + (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi b i j y) a 0 := by
      intro j
      rw [pd_pd_sum_C2 univ (fun k v => gi v i j * christoffel g gi k i j v * v k) a b
            (fun k _ => ((hgi2 i j).mul (hC2 k i j)).mul (coordCDA2 k))]
      have hk : ∀ k,
          pd (fun y => pd (fun v => gi v i j * christoffel g gi k i j v * v k) b y) a 0
          = (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) b 0
              * (if k = a then (1 : ℝ) else 0)
            + (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) a 0
              * (if k = b then (1 : ℝ) else 0) := by
        intro k
        rw [QIQTH.PullbackMetric.pd_pd_mul3_zero (fun v => gi v i j) (fun v => christoffel g gi k i j v) (fun v => v k)
              a b (hgi2 i j) (hC2 k i j) (coordCDA2 k),
            hgi0 i j, hΓ0 k i j, hdgi0 i j a, hdgi0 i j b, pd_pd_coord_zero' k a b,
            QIQTH.LaplaceBeltrami.pd_coord k a 0, QIQTH.LaplaceBeltrami.pd_coord k b 0]
        have hck : (0 : Point n) k = 0 := rfl
        rw [hck]; ring
      rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_add_distrib]
      congr 1
      · rw [show (∑ k, (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) b 0
                * (if k = a then (1 : ℝ) else 0))
              = ∑ k, (if k = a then (if i = j then (1 : ℝ) else 0)
                  * pd (fun y => christoffel g gi k i j y) b 0 else 0) from
            Finset.sum_congr rfl (fun k _ => by split_ifs <;> ring),
          Finset.sum_ite_eq' univ a
            (fun k => (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) b 0)]
        simp
      · rw [show (∑ k, (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) a 0
                * (if k = b then (1 : ℝ) else 0))
              = ∑ k, (if k = b then (if i = j then (1 : ℝ) else 0)
                  * pd (fun y => christoffel g gi k i j y) a 0 else 0) from
            Finset.sum_congr rfl (fun k _ => by split_ifs <;> ring),
          Finset.sum_ite_eq' univ b
            (fun k => (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi k i j y) a 0)]
        simp
    rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_add_distrib]
    congr 1
    · rw [show (∑ j, (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi a i j y) b 0)
            = ∑ j, (if i = j then pd (fun y => christoffel g gi a i j y) b 0 else 0) from
          Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring),
        Finset.sum_ite_eq univ i (fun j => pd (fun y => christoffel g gi a i j y) b 0)]
      simp
    · rw [show (∑ j, (if i = j then (1 : ℝ) else 0) * pd (fun y => christoffel g gi b i j y) a 0)
            = ∑ j, (if i = j then pd (fun y => christoffel g gi b i j y) a 0 else 0) from
          Finset.sum_congr rfl (fun j _ => by split_ifs <;> ring),
        Finset.sum_ite_eq univ i (fun j => pd (fun y => christoffel g gi b i j y) a 0)]
      simp
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib]

private theorem coeffAF_center_hessian_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi2 : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hC2 : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (a b : Fin n) :
    pd (fun y => pd (coeffAF g gi) b y) a (0 : Point n)
      = (1 / 3) * ricci g gi a b 0
        - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                   + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)) := by
  have hgi0mat : ∀ i j, gi (0 : Point n) i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hgi0 i j, Matrix.one_apply]
  have hCS1 : ContDiffAt ℝ 2 (fun v : Point n => ∑ i, (gi v i i - 1)) 0 :=
    ContDiffAt.sum fun i _ => (hgi2 i i).sub contDiffAt_const
  have hCS2 : ContDiffAt ℝ 2
      (fun v : Point n => ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) 0 :=
    ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ContDiffAt.sum fun k _ =>
      ((hgi2 i j).mul (hC2 k i j)).mul (coordCDA2 k)
  unfold coeffAF
  rw [pd_pd_sub_C2 (fun v => (1 / 2 : ℝ) * ∑ i, (gi v i i - 1))
        (fun v => (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) a b
        (contDiffAt_const.mul hCS1) (contDiffAt_const.mul hCS2),
      pd_pd_const_mul_C2 (1 / 2) (fun v => ∑ i, (gi v i i - 1)) a b hCS1,
      pd_pd_const_mul_C2 (1 / 2)
        (fun v => ∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k) a b hCS2,
      coeffA1_hessian_C2 g gi hg2 hgi2 hg0 hgi0mat hdg0 hsymm hinv hgauge a b,
      coeffA2_hessian_C2 g gi hgi2 hC2 hgi0 hdgi0 hΓ0 a b]
  ring

/-- **The Hessian of the off-diagonal `O(1/t)` coefficient in explicit Ricci form, `C³`.** -/
private theorem totalRadialO1_coeff_center_hessian_ricci_C3
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi2 : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hC2 : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (a b : Fin n) :
    pd (fun y => pd (fun v => totalRadialO1_coeff g gi Θ u v) b y) a (0 : Point n)
      = ((1 / 3) * ricci g gi a b 0
           - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                      + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
          * foldedCoeff Θ u 0 0
        + (pd (fun y => pd (foldedCoeff Θ u 0) b y) a 0
           + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0) := by
  rw [totalRadialO1_coeff_center_hessian_C3 g gi Θ u hgi2 hC2 hw0 hgi0 hdgi0 hΓ0 a b,
      coeffAF_center_hessian_C2 g gi hg2 hgi2 hC2 hg0 hgi0 hdg0 hdgi0 hΓ0 hsymm hinv hgauge a b]

/-! ### ★ The finite-regularity capstone -/

/-- **★ THE FINITE-REGULARITY OFF-DIAGONAL `O(1/t)` CANCELLATION (R3c-2).**  The `ContDiff ℝ ⊤`
    hypotheses of `totalRadialO1_coeff_isLittleO` are weakened to their true minimal finite order at
    the RNC centre (`g, gi, Γ ∈ ContDiffAt ℝ 2`, `w₀ ∈ ContDiffAt ℝ 3`, all at `0`).  Same conclusion:
        `totalRadialO1_coeff g gi Θ u  =o[𝓝 0]  (fun v => ‖v‖²)` .
    The value (c5) / gradient (c6) / Hessian (c7) jets all vanish, so the second-order Peano Taylor
    polynomial of the coefficient at `0` is identically `0`.  Inherits the van-Vleck 2-jet
    (`hw0flat`, `hw0hessRicci`) + the RNC gauge.  NOT the exact transport identity, NOT `a₁ = R/6`. -/
theorem totalRadialO1_coeff_isLittleO_C3
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgiC : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hC : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 0 0) :
    (fun v => totalRadialO1_coeff g gi Θ u v) =o[nhds (0 : Point n)] (fun v => ‖v‖ ^ 2) := by
  have hw02 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) 0 := hw0.of_le (by norm_num)
  have hgi1 : ∀ i j, ContDiffAt ℝ 1 (fun y => gi y i j) 0 := fun i j => (hgiC i j).of_le (by norm_num)
  have hC1 : ∀ a b c, ContDiffAt ℝ 1 (fun y => christoffel g gi a b c y) 0 :=
    fun a b c => (hC a b c).of_le (by norm_num)
  -- VALUE face (c5).
  have hval : totalRadialO1_coeff g gi Θ u (0 : Point n) = 0 :=
    totalRadialO1_coeff_center_vanishes g gi Θ u (fun i => by rw [hgi0 i i]; simp)
  -- GRADIENT face (c6).
  have hgrad : ∀ e, pd (fun v => totalRadialO1_coeff g gi Θ u v) e (0 : Point n) = 0 :=
    fun e => totalRadialO1_coeff_center_grad_vanishes_C2 g gi Θ u hgi1 hC1 hw02 hgi0 hdgi0 hΓ0 hw0flat e
  -- HESSIAN face (c7), in explicit Ricci form.
  have hhess : ∀ a b, pd (fun y => pd (fun v => totalRadialO1_coeff g gi Θ u v) b y) a (0 : Point n)
      = 0 := by
    intro a b
    rw [totalRadialO1_coeff_center_hessian_ricci_C3 g gi Θ u hg hgiC hC hw0 hg0 hgi0 hdg0 hdgi0 hΓ0
          hsymm hinv hgauge a b]
    linear_combination hw0hessRicci a b
  -- ContDiffAt 2 of the assembled coefficient.
  have hf : ContDiffAt ℝ 2 (fun v => totalRadialO1_coeff g gi Θ u v) 0 := by
    rw [coeff_split_F g gi Θ u]
    exact (((coeffAF_contDiffAt2 g gi hgiC hC).mul hw02).add
      (radialDeriv_contDiffAt2 (foldedCoeff Θ u 0) hw0)).add
      (coeffDevF_contDiffAt2 gi (foldedCoeff Θ u 0) hgiC hw0)
  -- Feed the general-`v` second-order Peano Taylor; the polynomial is identically 0.
  have hpeano := QIQTH.RNCExpansion.pd_taylor_two_peano
    (fun v => totalRadialO1_coeff g gi Θ u v) hf
  refine hpeano.congr_left (fun x => ?_)
  have h1 : (∑ i, pd (fun v => totalRadialO1_coeff g gi Θ u v) i 0 * x i) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hgrad i]; ring
  have h2 : (∑ i, ∑ j, pd (fun y => pd (fun v => totalRadialO1_coeff g gi Θ u v) j y) i 0
      * x i * x j) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [hhess i j]; ring
  show totalRadialO1_coeff g gi Θ u x - totalRadialO1_coeff g gi Θ u 0
      - (∑ i, pd (fun v => totalRadialO1_coeff g gi Θ u v) i 0 * x i)
      - (1 / 2) * ∑ i, ∑ j, pd (fun y => pd (fun v => totalRadialO1_coeff g gi Θ u v) j y) i 0
          * x i * x j
      = totalRadialO1_coeff g gi Θ u x
  rw [hval, h1, h2]; ring

end QIQTH.HeatResidualBound
