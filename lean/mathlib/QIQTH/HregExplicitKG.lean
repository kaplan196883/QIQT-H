/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The `hreg` regularity input, discharged for the explicit Klein–Gordon field

Tier A4 of `QIQT_GR_DISCHARGEABLE_PLAN.md`.  The QIQT→GR capstone takes a regularity hypothesis `hreg`: for any
focusing scalar `f` with `a·T = Ric + f·g`, `f` is differentiable and `f + ½R` is differentiable.  For the explicit
KG stress tensor `T = kgStress`, `f` is *uniquely determined* by taking the `gi`-trace of the defining relation
(`f = (a·tr(kgStress) − R)/4`, using `∑ gi·g = 4` from `metric_contraction_trace`), and that explicit `f` is `C^∞`
(via the curvature `C^∞` chain `scalarCurv_contDiff` + `kgStress` smoothness).  So `hreg` is a THEOREM here.

Axiom-free.
-/
import QIQTH.KGStressConservation
import QIQTH.ChristoffelSmooth
import QIQTH.EinsteinFieldEquation

namespace QIQTH.Curvature

variable {n : ℕ}

/-- The KG Lagrangian scalar is `C^∞`. -/
theorem kgLagr_contDiff (m : ℝ) (φ : Point n → ℝ) (gi : Point n → Fin n → Fin n → ℝ)
    (hφ : ContDiff ℝ ⊤ φ) (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b)) :
    ContDiff ℝ ⊤ (kgLagr m φ gi) := by
  have he : (kgLagr m φ gi)
      = fun y => (∑ α, ∑ β, gi y α β * (pd φ α y * pd φ β y)) + m ^ 2 * (φ y) ^ 2 := by
    funext y; rfl
  rw [he]
  refine (ContDiff.sum (fun α _ => ContDiff.sum (fun β _ =>
    (hCgi α β).mul ((contDiff_pd φ hφ α).mul (contDiff_pd φ hφ β))))).add ?_
  exact contDiff_const.mul (hφ.pow 2)

/-- The KG stress tensor component `y ↦ kgStress m φ g gi y a b` is `C^∞`. -/
theorem kgStress_contDiff (m : ℝ) (φ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (hφ : ContDiff ℝ ⊤ φ) (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b)) (a b : Fin n) :
    ContDiff ℝ ⊤ (fun y => kgStress m φ g gi y a b) := by
  have he : (fun y => kgStress m φ g gi y a b)
      = fun y => pd φ a y * pd φ b y - (1 / 2 : ℝ) * g y a b * kgLagr m φ gi y := by
    funext y; rfl
  rw [he]
  exact ((contDiff_pd φ hφ a).mul (contDiff_pd φ hφ b)).sub
    ((contDiff_const.mul (hCg a b)).mul (kgLagr_contDiff m φ gi hφ hCgi))

/-- **★ The `hreg` input, DISCHARGED for the explicit free Klein–Gordon field (Tier A4).**  For any focusing
    scalar `f` satisfying `a·kgStress = Ric + f·g`, the `gi`-trace fixes `f = (a·tr(kgStress) − R)/4` (using
    `∑ gi·g = 4`), which is `C^∞`; hence `f` is differentiable everywhere and `f + ½R` is differentiable. -/
theorem hreg_kg (m : ℝ) (φ : Point 4 → ℝ) (g gi : Point 4 → Fin 4 → Fin 4 → ℝ) (a : ℝ)
    (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hφ : ContDiff ℝ ⊤ φ) (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (f : Point 4 → ℝ)
    (hrel : ∀ y a' b, a * kgStress m φ g gi y a' b = ricci g gi a' b y + f y * g y a' b) :
    (∀ x ρ, PdiffAt f ρ x) ∧
      Differentiable ℝ (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y) := by
  -- the explicit smooth focusing scalar `f₀ y = (a·tr(kgStress) − R)/4`
  have htrKG : ContDiff ℝ ⊤ (fun y => ∑ a', ∑ b, gi y a' b * kgStress m φ g gi y a' b) :=
    ContDiff.sum (fun a' _ => ContDiff.sum (fun b _ =>
      (hCgi a' b).mul (kgStress_contDiff m φ g gi hφ hCg hCgi a' b)))
  have hf0diff : ContDiff ℝ ⊤
      (fun y => (a * (∑ a', ∑ b, gi y a' b * kgStress m φ g gi y a' b) - scalarCurv g gi y) / 4) :=
    ((contDiff_const.mul htrKG).sub (scalarCurv_contDiff g gi hCg hCgi)).div_const 4
  -- `f = f₀` from the `gi`-trace of the defining relation
  have hfeq : f = fun y =>
      (a * (∑ a', ∑ b, gi y a' b * kgStress m φ g gi y a' b) - scalarCurv g gi y) / 4 := by
    funext y
    -- trace-contract `hrel`: `∑ gi·(a·kgStress) = ∑ gi·ricci + ∑ gi·(f·g)`
    have hsum : (∑ a', ∑ b, gi y a' b * (a * kgStress m φ g gi y a' b))
        = (∑ a', ∑ b, gi y a' b * ricci g gi a' b y)
          + (∑ a', ∑ b, gi y a' b * (f y * g y a' b)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by rw [hrel y a' b]; ring)
    have hLHS : (∑ a', ∑ b, gi y a' b * (a * kgStress m φ g gi y a' b))
        = a * (∑ a', ∑ b, gi y a' b * kgStress m φ g gi y a' b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a' _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring))
    have hfg : (∑ a', ∑ b, gi y a' b * (f y * g y a' b))
        = f y * (∑ a', ∑ b, gi y a' b * g y a' b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a' _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring))
    have hR : (∑ a', ∑ b, gi y a' b * ricci g gi a' b y) = scalarCurv g gi y := rfl
    have htrace : (∑ a', ∑ b, gi y a' b * g y a' b) = (4 : ℝ) := by
      simpa using metric_contraction_trace g gi hsymm_gi hinv y
    rw [hLHS, hR, hfg, htrace] at hsum
    -- `a·trKG = R + f·4` ⟹ `f = (a·trKG − R)/4`
    rw [eq_div_iff (by norm_num : (4 : ℝ) ≠ 0)]; linarith [hsum]
  rw [hfeq]
  exact ⟨fun x ρ => PdiffAt_of_contDiff _ hf0diff ρ x,
    (hf0diff.differentiable (by simp)).add
      ((contDiff_const.mul (scalarCurv_contDiff g gi hCg hCgi)).differentiable (by simp))⟩

end QIQTH.Curvature
