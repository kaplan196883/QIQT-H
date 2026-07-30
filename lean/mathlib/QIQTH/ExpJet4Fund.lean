/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4Rhs
import QIQTH.ExpMapContDiff3
import Mathlib

/-!
# The Jet₄ fourth-variation fundamental solution — local existence `expJet4Fund_local`

This file lands the **J4-2a brick** of the JET-4 TOWER campaign
(`docs/qg_roadmap/JET4_TOWER_PLAN.md`) toward the truly-unconditional `a₁ = R/6`: the **local
Picard–Lindelöf existence** for the fourth-variation fundamental-solution ODE, a FAITHFUL MIRROR one
Fréchet-derivative order higher of the landed `expJet3Fund_local` (`ExpMapContDiff3.lean`).

The fourth variation `R^{hklm}(t)` (VECTOR-valued in `Point n × Point n`) solves the INHOMOGENEOUS
linear ODE `R'(t) = DF(Y_v t)(R t) + Θ₄^{hklm}(t)`, `R(0) = 0`, with `Θ₄ = expJet4Rhs …` the
fourteen-term J4-source term (`ExpJet4Rhs.lean`).  The affine field
`F₄ t R := DF(Y_v t)(R) + Θ₄^{hklm}(t)` has EXACTLY the same structure as `F₃`: the homogeneous
linear part `DF(Y_v t)(R)` is IDENTICAL (only the inhomogeneity `Θ₃ → Θ₄` changes order), the source
is GLOBAL (constant in `R`, not propagator-scaled), so the `IsPicardLindelof` instantiation is a
verbatim one-order-higher mirror — the source symbol / continuity witness are the only change.

`Φ` is the abstract first-variation propagator; `Qhk … Qklm` are the abstract second/third-variation
solutions (parametrized, exactly as in `expJet4Rhs`); all carry `ContinuousOn (Icc 0 1)` hypotheses
(needed for `expJet4Rhs_continuousOn`).

## Honest firewall (binding)

**What is proven here:** the LOCAL (short-time `[0, T]`) Picard–Lindelöf existence of the Jet₄
fourth-variation fundamental solution `R^{hklm}` for the affine field `F₄`, a mechanical
one-order-higher mirror of `expJet3Fund_local`.

**What is NOT closed:** this does NOT build the `[0,1]` GLOBAL Jet₄ solution (the next brick J4-2b:
`expJet4Fund_shifted`/`_glue`/`expJet4Fund`), does NOT establish `exp_p ∈ C⁴`, does NOT reach
`κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`, and is NOT numerical-`G` / the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- **R4-fund LOCAL — the LOCAL Jet₄ fourth-variation solution `R^{hklm}`.**  For `‖v‖ ≤ expRho` and
    `Φ`/`Qhk … Qklm` continuous on `[0,1]`, there is a short time `T > 0` and a VECTOR-valued curve
    `R : ℝ → Point n × Point n` with `R 0 = 0` solving the INHOMOGENEOUS linear Jet₄ ODE
    `R'(t) = DF(Y_v t)(R t) + Θ₄^{hklm}(t)` on `[0, T]`, where `DF = fderiv (geodesicField g gi)`,
    `Y_v t = expTube p v t`, and `Θ₄^{hklm} = expJet4Rhs …` is the J4-source term.  Verbatim mirror of
    `expJet3Fund_local`: the affine vector-normed `IsPicardLindelof` instantiation of
    `F₄ t R := DF(Y_v t)(R) + Θ₄^{hklm}(t)` on `closedBall(0,1)`, centred at `R₀ = 0` (source constant
    in `R` ⟹ `KdF`-Lipschitz; source continuous on compact `[0,1]` ⟹ `Cθ`-bounded).  The linear part
    is IDENTICAL to `expJet3Fund_local`; only the inhomogeneity `Θ₃ → Θ₄` (order 4) changes. -/
theorem expJet4Fund_local (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1)) (h k l m : Point n) :
    ∃ T > (0 : ℝ), ∃ R : ℝ → (Point n × Point n),
      R 0 = 0 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt R
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          (Set.Icc (0 : ℝ) T) t := by
  obtain ⟨KdF, hKdF0, hKdF⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  -- `Θ₄^{hklm}` is continuous on the compact `[0,1]`, hence uniformly bounded by some `Cθ ≥ 0`.
  have hΘcont : ContinuousOn
      (fun t => expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
      (Set.Icc (0 : ℝ) 1) :=
    expJet4Rhs_continuousOn g gi hC p v hv Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm
      hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m
  obtain ⟨Cθ0, hCθ0⟩ := isCompact_Icc.exists_bound_of_continuousOn hΘcont
  set Cθ : ℝ := max Cθ0 0 with hCθdef
  have hCθnn : 0 ≤ Cθ := le_max_right _ _
  have hCθ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t‖ ≤ Cθ :=
    fun t ht => (hCθ0 t ht).trans (le_max_left _ _)
  -- the affine vector field `F₄ t R = DF(Y_v t)(R) + Θ₄^{hklm}(t)`.
  set F₄ : ℝ → (Point n × Point n) → (Point n × Point n) :=
    fun t R => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) R
      + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t with hF₄
  set T : ℝ := min 1 (1 / (KdF + Cθ + 1)) with hTdef
  have hL0 : 0 ≤ KdF + Cθ := add_nonneg hKdF0 hCθnn
  have hden : (0 : ℝ) < KdF + Cθ + 1 := by linarith
  have hT0 : 0 < T := lt_min one_pos (by positivity)
  have hTle1 : T ≤ 1 := min_le_left _ _
  have hTle2 : T ≤ 1 / (KdF + Cθ + 1) := min_le_right _ _
  set Lnn : NNReal := ⟨KdF + Cθ, hL0⟩ with hLnn
  set Knn : NNReal := ⟨KdF, hKdF0⟩ with hKnn
  have hIccsub : Set.Icc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc_right hTle1
  -- `DF(Y_v ·)` continuous on `[0,1]` (tube continuity ∘ `DF` C^∞).
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hDFtube : ContinuousOn
      (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Set.Icc (0 : ℝ) 1) :=
    hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)
  -- assemble `IsPicardLindelof` for the affine field on `[0, T]`, centred at `0`.
  have hpl : IsPicardLindelof F₄
      (tmin := (0 : ℝ)) (tmax := T) ⟨0, ⟨le_refl 0, hT0.le⟩⟩
      (0 : Point n × Point n) 1 0 Lnn Knn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in `R` on `closedBall(0,1)` with constant `KdF` (source drops out).
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro M _ N _
      simp only [dist_eq_norm, hKnn]
      have hsub : F₄ t M - F₄ t N
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (M - N) := by
        simp only [hF₄, map_sub]; abel
      rw [hsub]
      calc ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (M - N)‖
          ≤ ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ * ‖M - N‖ :=
            (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).le_opNorm _
        _ ≤ KdF * ‖M - N‖ := mul_le_mul_of_nonneg_right (hKdF t htIcc) (norm_nonneg _)
    · -- continuity in `t` for fixed `R`.
      intro x _
      have h1 : ContinuousOn
          (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x)
          (Set.Icc (0 : ℝ) 1) := hDFtube.clm_apply continuousOn_const
      exact ((h1.add hΘcont).mono hIccsub)
    · -- uniform bound `‖F₄ t R‖ ≤ KdF + Cθ` on `closedBall(0,1)`.
      intro t ht x hx
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      have hxnorm : ‖x‖ ≤ 1 := by
        have hd := Metric.mem_closedBall.mp hx
        rw [dist_zero_right] at hd
        simpa using hd
      show ‖F₄ t x‖ ≤ KdF + Cθ
      calc ‖F₄ t x‖
          = ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t‖ := by
            rw [hF₄]
        _ ≤ ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x‖
              + ‖expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t‖ :=
            norm_add_le _ _
        _ ≤ KdF * ‖x‖ + Cθ :=
            add_le_add
              (le_trans
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).le_opNorm x)
                (mul_le_mul_of_nonneg_right (hKdF t htIcc) (norm_nonneg _)))
              (hCθ t htIcc)
        _ ≤ KdF + Cθ := by
            have : KdF * ‖x‖ ≤ KdF * 1 := mul_le_mul_of_nonneg_left hxnorm hKdF0
            linarith
    · -- the interval constraint `(KdF + Cθ)·T ≤ 1`.
      show (Lnn : ℝ) * max (T - ((⟨0, ⟨le_refl 0, hT0.le⟩⟩ : Set.Icc (0 : ℝ) T) : ℝ))
          (((⟨0, ⟨le_refl 0, hT0.le⟩⟩ : Set.Icc (0 : ℝ) T) : ℝ) - 0) ≤ (1 : NNReal) - (0 : NNReal)
      simp only [hLnn, NNReal.coe_one, NNReal.coe_zero, sub_zero, sub_self, max_eq_left hT0.le]
      calc (KdF + Cθ) * T ≤ (KdF + Cθ) * (1 / (KdF + Cθ + 1)) :=
            mul_le_mul_of_nonneg_left hTle2 hL0
        _ ≤ 1 := by rw [mul_one_div, div_le_one hden]; linarith
  obtain ⟨R, hR0, hRd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨T, hT0, R, hR0, fun t ht => ?_⟩
  have hd := hRd t ht
  simpa only [hF₄] using hd

end QIQTH.ExpMap
