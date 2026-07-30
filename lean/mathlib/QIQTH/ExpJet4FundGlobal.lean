/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4Fund
import QIQTH.ExpJet4Rhs
import QIQTH.ExpMapContDiff3
import Mathlib

/-!
# The Jet₄ fourth-variation fundamental solution — `[0,1]` global existence `expJet4Fund`

This file lands the **J4-2b brick** of the JET-4 TOWER campaign
(`docs/qg_roadmap/JET4_TOWER_PLAN.md`) toward the truly-unconditional `a₁ = R/6`: the **`[0,1]`
global** fourth-variation fundamental solution obtained by gluing the local Picard–Lindelöf solutions,
a FAITHFUL MIRROR one Fréchet-derivative order higher of the landed `expJet3Fund` glue chain
(`ExpMapContDiff3.lean`, ~lines 578–1047).

The fourth variation `R^{hklm}(t)` (VECTOR-valued in `Point n × Point n`) solves the INHOMOGENEOUS
linear ODE `R'(t) = DF(Y_v t)(R t) + Θ₄^{hklm}(t)`, `R(0) = 0`, with `Θ₄ = expJet4Rhs …` the
fourteen-term J4-source term (`ExpJet4Rhs.lean`).  The affine field
`F₄ t R := DF(Y_v t)(R) + Θ₄^{hklm}(t)` has EXACTLY the same structure as `F₃`: the homogeneous
linear part `DF(Y_v t)(R)` is IDENTICAL (only the inhomogeneity `Θ₃ → Θ₄` changes order), the source
is GLOBAL (constant in `R`), so the whole existence-glue chain is a verbatim one-order-higher mirror
— the source symbol / continuity witness are the only change.  The chain is:

* `expJet4Field_continuousOn` — continuity of the affine field on any `A ⊆ [0,1]`;
* `expJet4Fund_shifted` — the local Picard–Lindelöf solver centred at an arbitrary `x₀`;
* `expJet4Fund_shifted_integral` — its integral form (the gluing brick);
* `expJet4Fund_glue` (private) — the endpoint-matching concatenation across `[0,1]`;
* `expJet4Fund` — the `[0,1]` global capstone existence.

`Φ` is the abstract first-variation propagator; `Qhk … Qklm` are the abstract second/third-variation
solutions (parametrized, exactly as in `expJet4Rhs`); all carry `ContinuousOn (Icc 0 1)` hypotheses
(needed for `expJet4Rhs_continuousOn`).

## Honest firewall (binding)

**What is proven here:** the `[0,1]` GLOBAL existence of the Jet₄ fourth-variation fundamental
solution `R^{hklm}` (continuous, obeying the global integral equation and the inhomogeneous derivative
law), a mechanical one-order-higher mirror of the `expJet3Fund` glue chain.

**What is NOT closed:** this does NOT instantiate `Φ`/`Q` with the lower-jet fundamental-solution
witnesses (a later rung), does NOT establish `exp_p ∈ C⁴`, does NOT reach `κ = 1/6`, the heat-kernel
parametrix, or `a₁ = R/6`, and is NOT numerical-`G` / the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **Continuity of the Jet₄ inhomogeneous field** `s ↦ DF(Y_v s)(R s) + Θ₄^{hklm}(s)` on any
    `A ⊆ [0,1]` where `R` is continuous.  Direct mirror of `expJet3Field_continuousOn`, source
    continuity via `expJet4Rhs_continuousOn`. -/
theorem expJet4Field_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
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
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1)) (h k l m : Point n)
    {A : Set ℝ} (hA : A ⊆ Set.Icc (0 : ℝ) 1)
    {R : ℝ → (Point n × Point n)} (hR : ContinuousOn R A) :
    ContinuousOn (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
      + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s) A := by
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hDFtube : ContinuousOn
      (fun s => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) A :=
    (hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)).mono hA
  have h1 : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)) A :=
    hDFtube.clm_apply hR
  have h2 : ContinuousOn
      (fun s => expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s) A :=
    (expJet4Rhs_continuousOn g gi hC p v hv Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm
      hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).mono hA
  exact h1.add h2

set_option maxHeartbeats 1000000 in
/-- **R4-fund SHIFTED — the shifted Jet₄ fourth-variation solver from arbitrary vector IC `x₀`.**
    Direct mirror of `expJet3Fund_shifted`: the vector-normed `IsPicardLindelof` instantiation of
    `F₄ t R := DF(Y_v t)(R) + Θ₄^{hklm}(t)` centred at `x₀` on `closedBall(x₀, a)` with the same
    linear-in-`x₀` radius `a := 2·(KdF·‖x₀‖·T + Cθ·T) + 1`.  The reusable brick of the `[0,1]`
    concatenation. -/
theorem expJet4Fund_shifted (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1)) (h k l m : Point n)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (t₀ T : ℝ) (ht₀ : 0 ≤ t₀) (hT : 0 < T) (hsum : t₀ + T ≤ 1) (hstep : 2 * KdF * T ≤ 1)
    (x₀ : Point n × Point n) :
    ∃ R : ℝ → (Point n × Point n),
      R t₀ = x₀ ∧
      ∀ t ∈ Set.Icc t₀ (t₀ + T),
        HasDerivWithinAt R
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          (Set.Icc t₀ (t₀ + T)) t := by
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
  have hTnn : 0 ≤ T := hT.le
  -- ball radius (linear in `x₀`, chosen so the affine a-priori bound closes for ANY `x₀`).
  set aval : ℝ := 2 * (KdF * ‖x₀‖ * T + Cθ * T) + 1 with haval
  have haval0 : 0 ≤ aval := by
    rw [haval]
    have h1 : 0 ≤ KdF * ‖x₀‖ * T := mul_nonneg (mul_nonneg hKdF0 (norm_nonneg _)) hTnn
    have h2 : 0 ≤ Cθ * T := mul_nonneg hCθnn hTnn
    linarith
  set Lval : ℝ := KdF * (‖x₀‖ + aval) + Cθ with hLval
  have hLval0 : 0 ≤ Lval := by
    rw [hLval]
    have hm : 0 ≤ KdF * (‖x₀‖ + aval) :=
      mul_nonneg hKdF0 (add_nonneg (norm_nonneg _) haval0)
    linarith
  set Ann : NNReal := ⟨aval, haval0⟩ with hAnndef
  set Lnn : NNReal := ⟨Lval, hLval0⟩ with hLnndef
  set Knn : NNReal := ⟨KdF, hKdF0⟩ with hKnn
  have hIccsub : Set.Icc t₀ (t₀ + T) ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc ht₀ hsum
  -- the interval constraint `L·T ≤ a`.
  have hKT : KdF * T ≤ 1 / 2 := by linarith
  have hstepPL : Lval * T ≤ aval := by
    have key : aval * (KdF * T) ≤ aval * (1 / 2) := mul_le_mul_of_nonneg_left hKT haval0
    have hLvalT : Lval * T = KdF * ‖x₀‖ * T + KdF * aval * T + Cθ * T := by rw [hLval]; ring
    rw [hLvalT]
    nlinarith [key, haval, haval0]
  -- `DF(Y_v ·)` continuous on `[0,1]`.
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hDFtube : ContinuousOn
      (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Set.Icc (0 : ℝ) 1) :=
    hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)
  -- assemble `IsPicardLindelof` for the affine field on `[t₀, t₀+T]`, centred at `x₀`.
  have hpl : IsPicardLindelof F₄
      (tmin := t₀) (tmax := t₀ + T) ⟨t₀, ⟨le_refl t₀, by linarith⟩⟩
      x₀ Ann 0 Lnn Knn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in `R` with constant `KdF` (source drops out).
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
    · -- uniform bound `‖F₄ t x‖ ≤ L` on `closedBall(x₀, a)`.
      intro t ht x hx
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      have hd : ‖x - x₀‖ ≤ aval := by
        have h' := Metric.mem_closedBall.mp hx
        rw [dist_eq_norm] at h'
        exact h'
      have hxx : (x - x₀) + x₀ = x := by abel
      have hxnorm : ‖x‖ ≤ ‖x₀‖ + aval := by
        calc ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [hxx]
          _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
          _ ≤ aval + ‖x₀‖ := by linarith
          _ = ‖x₀‖ + aval := by ring
      show ‖F₄ t x‖ ≤ Lval
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
        _ ≤ Lval := by
            rw [hLval]
            have hmul : KdF * ‖x‖ ≤ KdF * (‖x₀‖ + aval) :=
              mul_le_mul_of_nonneg_left hxnorm hKdF0
            linarith
    · -- the interval constraint `L · max(T, 0) ≤ a`.
      show (Lnn : ℝ) * max ((t₀ + T) - ((⟨t₀, ⟨le_refl t₀, by linarith⟩⟩ :
              Set.Icc t₀ (t₀ + T)) : ℝ))
          (((⟨t₀, ⟨le_refl t₀, by linarith⟩⟩ : Set.Icc t₀ (t₀ + T)) : ℝ) - t₀)
            ≤ (Ann : ℝ) - ((0 : NNReal) : ℝ)
      rw [NNReal.coe_zero, sub_zero]
      show Lval * max ((t₀ + T) - t₀) (t₀ - t₀) ≤ aval
      rw [sub_self, show (t₀ + T) - t₀ = T from by ring, max_eq_left hT.le]
      exact hstepPL
  obtain ⟨R, hR0, hRd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨R, hR0, fun t ht => ?_⟩
  have hd := hRd t ht
  simpa only [hF₄] using hd

set_option maxHeartbeats 1000000 in
/-- **R4-fund SHIFTED-INTEGRAL — the shifted Jet₄ solver in INTEGRAL form (the gluing brick).**
    Direct mirror of `expJet3Fund_shifted_integral`: additionally packages the LOCAL INTEGRAL
    EQUATION `R(t) = x₀ + ∫_{t₀}^t (DF(Y_v s)(R s) + Θ₄^{hklm}(s)) ds` via FTC-2.  Since the source is
    GLOBAL, the `[0,1]` concatenation glues these directly by ENDPOINT VALUE — no right-composition. -/
theorem expJet4Fund_shifted_integral (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1)) (h k l m : Point n)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (t₀ T : ℝ) (ht₀ : 0 ≤ t₀) (hT : 0 < T) (hsum : t₀ + T ≤ 1) (hstep : 2 * KdF * T ≤ 1)
    (x₀ : Point n × Point n) :
    ∃ R : ℝ → (Point n × Point n),
      R t₀ = x₀ ∧
      ContinuousOn R (Set.Icc t₀ (t₀ + T)) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + T),
        HasDerivWithinAt R
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          (Set.Icc t₀ (t₀ + T)) t) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + T),
        R t = x₀ + ∫ s in t₀..t,
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
             + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s)) := by
  obtain ⟨R, hR0, hRd⟩ :=
    expJet4Fund_shifted g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m
      KdF hKdF0 hKdF t₀ T ht₀ hT hsum hstep x₀
  have hIccsub : Set.Icc t₀ (t₀ + T) ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc ht₀ hsum
  have hRcont : ContinuousOn R (Set.Icc t₀ (t₀ + T)) := fun s hs => (hRd s hs).continuousWithinAt
  have hintegrand : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s)
      (Set.Icc t₀ (t₀ + T)) :=
    expJet4Field_continuousOn g gi hC p v hv Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm
      hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m hIccsub hRcont
  refine ⟨R, hR0, hRcont, hRd, fun t ht => ?_⟩
  have hab : t₀ ≤ t := ht.1
  have hsubt : Set.Icc t₀ t ⊆ Set.Icc t₀ (t₀ + T) := Set.Icc_subset_Icc_right ht.2
  have hcont : ContinuousOn R (Set.Icc t₀ t) := hRcont.mono hsubt
  have hderiv : ∀ x ∈ Set.Ioo t₀ t,
      HasDerivWithinAt R
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x)) (R x)
           + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m x)
        (Set.Ioi x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc t₀ (t₀ + T) := hsubt ⟨hx.1.le, hx.2.le⟩
    have hnhds : Set.Icc t₀ (t₀ + T) ∈ nhds x :=
      Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 ht.2)
    exact ((hRd x hxIcc).hasDerivAt hnhds).hasDerivWithinAt
  have hint : IntervalIntegrable
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s)
      MeasureTheory.volume t₀ t :=
    (hintegrand.mono hsubt).intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint
  rw [hR0] at hftc
  rw [hftc]; abel

set_option maxHeartbeats 2000000 in
/-- **The partition induction (endpoint-matching concatenation) for the Jet₄ solver.**  Direct mirror
    of `expJet3Fund_glue`: for every `j ≤ N` builds a curve `R` on `[0, j/N]` with `R 0 = 0`,
    continuous, obeying the GLOBAL integral equation
    `R t = 0 + ∫₀ᵗ (DF(Y_v s)(R s) + Θ₄^{hklm}(s)) ds`, by induction gluing `R_j` and the shifted
    solver `U` at the endpoint value `R_j(j/N)`; the global source pastes directly. -/
private theorem expJet4Fund_glue (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1)) (h k l m : Point n)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (N : ℕ) (hN0 : 0 < N) (hstep : 2 * KdF * (1 / (N : ℝ)) ≤ 1) :
    ∀ j : ℕ, j ≤ N →
      ∃ R : ℝ → (Point n × Point n),
        R 0 = 0 ∧
        ContinuousOn R (Set.Icc (0 : ℝ) ((j : ℝ) / (N : ℝ))) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) ((j : ℝ) / (N : ℝ)),
          R t = (0 : Point n × Point n) + ∫ s in (0 : ℝ)..t,
            ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
               + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun _ => (0 : Point n × Point n), rfl, continuousOn_const, ?_⟩
    intro t ht
    have h0 : ((0 : ℕ) : ℝ) / (N : ℝ) = 0 := by rw [Nat.cast_zero, zero_div]
    rw [h0] at ht
    have htz : t = 0 := le_antisymm ht.2 ht.1
    subst htz
    simp only [intervalIntegral.integral_same, add_zero]
  | succ M ih =>
    intro hk
    obtain ⟨Rj, hRj0, hRjcont, hRjint⟩ := ih (Nat.le_of_succ_le hk)
    have hτnn : 0 ≤ (M : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg M) hNpos.le
    have hInpos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hsucc : ((M + 1 : ℕ) : ℝ) / (N : ℝ) = (M : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
      push_cast; ring
    have hτm1le1 : (M : ℝ) / (N : ℝ) + 1 / (N : ℝ) ≤ 1 :=
      hsucc ▸ (by rw [div_le_one hNpos]; exact_mod_cast hk)
    obtain ⟨U, hU0, hUcont, hUderiv, hUint⟩ :=
      expJet4Fund_shifted_integral g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv
        hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m
        KdF hKdF0 hKdF
        ((M : ℝ) / (N : ℝ)) (1 / (N : ℝ)) hτnn hInpos hτm1le1 hstep (Rj ((M : ℝ) / (N : ℝ)))
    set R' : ℝ → (Point n × Point n) :=
      fun t => if t ≤ (M : ℝ) / (N : ℝ) then Rj t else U t with hR'def
    have hR'_lo : ∀ s, s ≤ (M : ℝ) / (N : ℝ) → R' s = Rj s := by
      intro s hs; rw [hR'def]; exact if_pos hs
    have hR'_hi : ∀ s, ¬ (s ≤ (M : ℝ) / (N : ℝ)) → R' s = U s := by
      intro s hs; rw [hR'def]; exact if_neg hs
    -- EqOn on the two closed pieces (junction value matches: `Rj(τ_M) = x₀ = U(τ_M)`).
    have hEqLo : Set.EqOn R' Rj (Set.Icc (0 : ℝ) ((M : ℝ) / (N : ℝ))) :=
      fun s hs => hR'_lo s hs.2
    have hEqHi : Set.EqOn R' U
        (Set.Icc ((M : ℝ) / (N : ℝ)) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ))) := by
      intro s hs
      by_cases hsle : s ≤ (M : ℝ) / (N : ℝ)
      · have hseq : s = (M : ℝ) / (N : ℝ) := le_antisymm hsle hs.1
        rw [hR'_lo s hsle, hseq, hU0]
      · rw [hR'_hi s hsle]
    -- continuity of the glued curve on [0, (M+1)/N].
    have hR'cont : ContinuousOn R' (Set.Icc (0 : ℝ) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ))) := by
      have hunion : Set.Icc (0 : ℝ) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ))
          = Set.Icc (0 : ℝ) ((M : ℝ) / (N : ℝ))
            ∪ Set.Icc ((M : ℝ) / (N : ℝ)) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
        (Set.Icc_union_Icc_eq_Icc hτnn (by linarith)).symm
      rw [hunion]
      exact (hRjcont.congr hEqLo).union_of_isClosed (hUcont.congr hEqHi)
        isClosed_Icc isClosed_Icc
    -- integrand continuity for interval integrability.
    have hcontψ' : ContinuousOn
        (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
          + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s)
        (Set.Icc (0 : ℝ) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ))) :=
      expJet4Field_continuousOn g gi hC p v hv Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm
        hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m
        (Set.Icc_subset_Icc_right hτm1le1) hR'cont
    rw [hsucc]
    refine ⟨R', ?_, hR'cont, ?_⟩
    · rw [hR'_lo 0 hτnn]; exact hRj0
    · intro t ht
      by_cases htle : t ≤ (M : ℝ) / (N : ℝ)
      · -- t in [0, τM]: the curve is Rj there.
        rw [hR'_lo t htle]
        have hcong : (∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s))
            = ∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
                 + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le ht.1] at hs
          show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s
            = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s
          rw [hR'_lo s (le_trans hs.2 htle)]
        rw [hcong]
        exact hRjint t ⟨ht.1, htle⟩
      · -- t in (τM, τM + 1/N]: the curve is U there.
        have htlt : (M : ℝ) / (N : ℝ) < t := not_le.mp htle
        have htmem : t ∈ Set.Icc ((M : ℝ) / (N : ℝ)) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
          ⟨htlt.le, ht.2⟩
        rw [hR'_hi t htle]
        have hII1 : IntervalIntegrable
            (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s)
            MeasureTheory.volume 0 ((M : ℝ) / (N : ℝ)) :=
          (hcontψ'.mono (Set.Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hτnn
        have hII2 : IntervalIntegrable
            (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s)
            MeasureTheory.volume ((M : ℝ) / (N : ℝ)) t :=
          (hcontψ'.mono (Set.Icc_subset_Icc hτnn ht.2)).intervalIntegrable_of_Icc htlt.le
        have hsplit : (∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s))
            = (∫ s in (0 : ℝ)..((M : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s))
              + ∫ s in ((M : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s) :=
          (intervalIntegral.integral_add_adjacent_intervals hII1 hII2).symm
        -- first piece = Rj(τM) - 0.
        have hI1 : (∫ s in (0 : ℝ)..((M : ℝ) / (N : ℝ)),
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s))
            = Rj ((M : ℝ) / (N : ℝ)) - (0 : Point n × Point n) := by
          have hc : (∫ s in (0 : ℝ)..((M : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s))
              = ∫ s in (0 : ℝ)..((M : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
                   + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le hτnn] at hs
            show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s
              = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
                + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s
            rw [hR'_lo s hs.2]
          rw [hc, hRjint ((M : ℝ) / (N : ℝ)) ⟨hτnn, le_refl _⟩]; abel
        -- second piece = U(t) - Rj(τM).
        have hI2 : (∫ s in ((M : ℝ) / (N : ℝ))..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s))
            = U t - Rj ((M : ℝ) / (N : ℝ)) := by
          have hc : (∫ s in ((M : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s))
              = ∫ s in ((M : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (U s)
                   + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le htlt.le] at hs
            have hsmem : s ∈ Set.Icc ((M : ℝ) / (N : ℝ)) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
              ⟨hs.1, le_trans hs.2 ht.2⟩
            show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s
              = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (U s)
                + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s
            rw [hEqHi hsmem]
          rw [hc, hUint t htmem]; abel
        rw [hsplit, hI1, hI2]; abel

set_option maxHeartbeats 2000000 in
/-- **R4-fund CAPSTONE — the `[0,1]` Jet₄ fourth-variation fundamental solution `R^{hklm}`.**  Direct
    mirror of `expJet3Fund`: for `‖v‖ ≤ expRho` and `Φ`/`Qhk … Qklm` continuous on `[0,1]`, there is a
    vector-valued curve `R : ℝ → Point n × Point n` with `R 0 = 0`, continuous on `[0,1]`, obeying the
    GLOBAL integral equation `R t = 0 + ∫₀ᵗ (DF(Y_v s)(R s) + Θ₄^{hklm}(s)) ds`, and — by FTC-1 — the
    inhomogeneous Jet₄ derivative law `HasDerivWithinAt R (DF(Y_v t)(R t) + Θ₄^{hklm}(t)) (Icc 0 1) t`
    for every `t ∈ [0,1]`.  Built by concatenating `N ≥ 2(KdF+1)` shifted solvers
    (`expJet4Fund_glue`).

    HONEST: the `[0,1]` inhomogeneous Jet₄ fourth-variation solution `R^{hklm}` (the fourth-variation
    transport of `h, k, l, m` through `D⁴F`/`D³F`/`D²F`).  It does NOT instantiate `Φ`/`Q`, NOT close
    `ContDiff⁴ exp_p`, NOT the parameter-residual identity, NOT `κ = 1/6`, NOT numerical-`G`. -/
theorem expJet4Fund (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ R : ℝ → (Point n × Point n),
      R 0 = 0 ∧
      ContinuousOn R (Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        R t = (0 : Point n × Point n) + ∫ s in (0 : ℝ)..t,
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
             + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt R
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          (Set.Icc (0 : ℝ) 1) t) := by
  obtain ⟨KdF, hKdF0, hKdF⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (KdF + 1))
  have hpos : (0 : ℝ) < 2 * (KdF + 1) := by linarith
  have hNRpos : (0 : ℝ) < (N : ℝ) := hpos.trans_le hN
  have hN0 : 0 < N := by exact_mod_cast hNRpos
  have hstep : 2 * KdF * (1 / (N : ℝ)) ≤ 1 := by
    have h2 : 2 * KdF * (1 / (N : ℝ)) = (2 * KdF) / (N : ℝ) := by ring
    rw [h2, div_le_one hNRpos]; linarith [hN]
  obtain ⟨R, hR0, hRcont, hRint⟩ :=
    expJet4Fund_glue g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m
      KdF hKdF0 hKdF N hN0 hstep N le_rfl
  have hNN : (N : ℝ) / (N : ℝ) = 1 := div_self hNRpos.ne'
  rw [hNN] at hRcont hRint
  refine ⟨R, hR0, hRcont, hRint, ?_⟩
  have hψcont : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s)
      (Set.Icc (0 : ℝ) 1) :=
    expJet4Field_continuousOn g gi hC p v hv Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm
      hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m (subset_refl _) hRcont
  intro t ht
  have hII : IntervalIntegrable
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m s)
      MeasureTheory.volume 0 t :=
    (hψcont.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  haveI : Fact (t ∈ Set.Icc (0 : ℝ) 1) := ⟨ht⟩
  have hmeas := hψcont.stronglyMeasurableAtFilter_nhdsWithin (μ := MeasureTheory.volume)
    measurableSet_Icc t
  have hFTC := intervalIntegral.integral_hasDerivWithinAt_right (s := Set.Icc (0 : ℝ) 1)
    hII hmeas (hψcont t ht)
  have hconst := hFTC.const_add (0 : Point n × Point n)
  exact hconst.congr (fun s hs => hRint s hs) (hRint t ht)

end QIQTH.ExpMap
