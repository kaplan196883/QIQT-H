/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4FundGlobal
import QIQTH.ExpJet4Fund
import QIQTH.ExpJet4Rhs
import QIQTH.ExpMapContDiff3
import Mathlib

/-!
# The Jet₄ fourth-variation fundamental solution — uniqueness and value bounds

This file lands the **J4-2c brick** of the JET-4 TOWER campaign
(`docs/qg_roadmap/JET4_TOWER_PLAN.md`) toward the truly-unconditional `a₁ = R/6`: the **uniqueness**
and **a-priori value bounds** for the `[0,1]` fourth-variation fundamental solution — a FAITHFUL
MIRROR one Fréchet-derivative order higher of the jet-3 versions (`ExpMapContDiff3.lean`:
`expJet3Fund_unique`, `expJet3Fund_value_bound`, `expJet3Fund_value_bound_Icc`).

The fourth variation `R^{hklm}(t)` (VECTOR-valued in `Point n × Point n`) solves the INHOMOGENEOUS
linear ODE `R'(t) = DF(Y_v t)(R t) + Θ₄^{hklm}(t)`, `R(0) = 0`, with `Θ₄ = expJet4Rhs …` the
fourteen-term J4-source term (`ExpJet4Rhs.lean`).  Because the affine field
`F₄ t R := DF(Y_v t)(R) + Θ₄^{hklm}(t)` has EXACTLY the same homogeneous linear part `DF(Y_v t)(R)`
as `F₃` (only the inhomogeneity `Θ₃ → Θ₄` changes order, and it is CONSTANT in `R`), the Grönwall
uniqueness / a-priori bound machinery is a verbatim one-order-higher mirror — only the source
symbol and its norm bound (`expJet4Rhs_norm_le`, fourteen terms) change.

* `expJet4Fund_unique` — uniqueness of the `[0,1]` IVP (difference solves the homogeneous Jacobi
  equation with `S 0 = 0`, `gronwall_vec_residual_Icc` with residual `0`);
* `expJet4Fund_value_bound` — the `t = 1` a-priori value bound `‖R 1‖ ≤ ρ₄·e^{Kstar}`;
* `expJet4Fund_value_bound_Icc` — the `[0,1]`-uniform version `∀ t, ‖R t‖ ≤ ρ₄·e^{Kstar}`.

`Φ` is the abstract first-variation propagator; `Qhk … Qklm` are the abstract second/third-variation
solutions, kept ABSTRACT throughout (exactly as jet-3).

## Honest firewall (binding)

**What is proven here:** uniqueness and a-priori value bounds for the `[0,1]` fourth-variation
fundamental solution `R^{hklm}`, a mechanical one-order-higher mirror of the jet-3 versions.

**What is NOT closed:** this does NOT instantiate `Φ`/`Q` with the lower-jet fundamental-solution
witnesses, does NOT establish `exp_p ∈ C⁴`, does NOT reach `κ = 1/6`, the heat-kernel parametrix, or
`a₁ = R/6`, and is NOT numerical-`G` / the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 4

variable {n : ℕ}

/-- **Uniqueness of the Jet₄ fourth-variation IVP on `[0,1]`.**  Mirror of `expJet3Fund_unique`: the
    inhomogeneous source `Θ₄^{hklm}` is CONSTANT in `R`, so two solutions `R₁,R₂` with the same IC
    agree — the difference `S := R₁ - R₂` solves the HOMOGENEOUS Jacobi equation
    `S' = DF(Y_v)(S)` (the sources cancel) with `S 0 = 0`, and `gronwall_vec_residual_Icc` with
    residual `ρ = 0` forces `‖S t‖ ≤ 0` on `[0,1]`. -/
theorem expJet4Fund_unique (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (h k l m : Point n)
    (R₁ R₂ : ℝ → (Point n × Point n)) (hR₁0 : R₁ 0 = 0) (hR₂0 : R₂ 0 = 0)
    (hderiv₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R₁
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₁ t)
        + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
        (Set.Icc (0 : ℝ) 1) t)
    (hderiv₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R₂
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₂ t)
        + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
        (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, R₁ t = R₂ t := by
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  have hgron := gronwall_vec_residual_Icc
    (fun t => R₁ t - R₂ t) (fun _ => (0 : Point n × Point n))
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar 0 hKstar0 le_rfl
    (by simp only [hR₁0, hR₂0, sub_zero])
    (fun t ht => by
      have hd := (hderiv₁ t ht).sub (hderiv₂ t ht)
      have hval : ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₁ t)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
            - ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₂ t)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₁ t - R₂ t) + 0 := by
        rw [map_sub, add_zero]; abel
      rwa [hval] at hd)
    (fun t ht => hKstar t ht)
    (fun _ _ => by simp)
  intro t ht
  have h0 : ‖R₁ t - R₂ t‖ ≤ 0 := by simpa using hgron t ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

/-- **`R^{hklm}(1)` value bound.**  For the inhomogeneous Jet₄ solution `R` (`R 0 = 0`,
    `R' = DF(Y_v)(R) + Θ₄^{hklm}`), with a `[0,1]` Jacobi bound `Kstar` on `‖DF(Y_v t)‖`, the
    `D⁴F`/`D³F`/`D²F` tube bounds `Kstar4`/`Kstar3`/`Kstar2`, a `[0,1]`-bound `Cphi` on `‖Φ t‖`, and
    `[0,1]`-bounds on the ten `Q··`/`Q···`, the fourteen-term source bound (`expJet4Rhs_norm_le`) is
    fed as the residual `ρ` into `gronwall_vec_residual` ⟹ `‖R 1‖ ≤ ρ₄·e^{Kstar}`. -/
theorem expJet4Fund_value_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n)) (h k l m : Point n)
    (Kstar Kstar4 Kstar3 Kstar2 Cphi : ℝ)
    (Cq_hk Cq_hl Cq_hm Cq_kl Cq_km Cq_lm : ℝ)
    (Cq_hkl Cq_hkm Cq_hlm Cq_klm : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar40 : 0 ≤ Kstar4) (hKstar30 : 0 ≤ Kstar3) (hKstar20 : 0 ≤ Kstar2)
    (hCphi0 : 0 ≤ Cphi)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hKstar4 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)‖
        ≤ Kstar4)
    (hKstar3 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3)
    (hKstar2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2)
    (hCphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi)
    (hCqhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhk t‖ ≤ Cq_hk)
    (hCqhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhl t‖ ≤ Cq_hl)
    (hCqhm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhm t‖ ≤ Cq_hm)
    (hCqkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq_kl)
    (hCqkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkm t‖ ≤ Cq_km)
    (hCqlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlm t‖ ≤ Cq_lm)
    (hCqhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkl t‖ ≤ Cq_hkl)
    (hCqhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkm t‖ ≤ Cq_hkm)
    (hCqhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlm t‖ ≤ Cq_hlm)
    (hCqklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklm t‖ ≤ Cq_klm)
    (R : ℝ → (Point n × Point n)) (hR0 : R 0 = 0)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
        + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
        (Set.Icc (0 : ℝ) 1) t) :
    ‖R 1‖ ≤ (Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖)
        + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hk
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hl
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hm
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_kl
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_km
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lm
        + Kstar2 * Cq_hk * Cq_lm
        + Kstar2 * Cq_hl * Cq_km
        + Kstar2 * Cq_hm * Cq_kl
        + Kstar2 * (Cphi * ‖h‖) * Cq_klm
        + Kstar2 * (Cphi * ‖k‖) * Cq_hlm
        + Kstar2 * (Cphi * ‖l‖) * Cq_hkm
        + Kstar2 * (Cphi * ‖m‖) * Cq_hkl) * Real.exp Kstar := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num [Set.mem_Icc]
  have hCqhk0 : 0 ≤ Cq_hk := (norm_nonneg _).trans (hCqhk 0 hmem0)
  have hCqhl0 : 0 ≤ Cq_hl := (norm_nonneg _).trans (hCqhl 0 hmem0)
  have hCqhm0 : 0 ≤ Cq_hm := (norm_nonneg _).trans (hCqhm 0 hmem0)
  have hCqkl0 : 0 ≤ Cq_kl := (norm_nonneg _).trans (hCqkl 0 hmem0)
  have hCqkm0 : 0 ≤ Cq_km := (norm_nonneg _).trans (hCqkm 0 hmem0)
  have hCqlm0 : 0 ≤ Cq_lm := (norm_nonneg _).trans (hCqlm 0 hmem0)
  have hCqhkl0 : 0 ≤ Cq_hkl := (norm_nonneg _).trans (hCqhkl 0 hmem0)
  have hCqhkm0 : 0 ≤ Cq_hkm := (norm_nonneg _).trans (hCqhkm 0 hmem0)
  have hCqhlm0 : 0 ≤ Cq_hlm := (norm_nonneg _).trans (hCqhlm 0 hmem0)
  have hCqklm0 : 0 ≤ Cq_klm := (norm_nonneg _).trans (hCqklm 0 hmem0)
  have hρ0 : (0 : ℝ) ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖)
      + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hk
      + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hl
      + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hm
      + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_kl
      + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_km
      + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lm
      + Kstar2 * Cq_hk * Cq_lm
      + Kstar2 * Cq_hl * Cq_km
      + Kstar2 * Cq_hm * Cq_kl
      + Kstar2 * (Cphi * ‖h‖) * Cq_klm
      + Kstar2 * (Cphi * ‖k‖) * Cq_hlm
      + Kstar2 * (Cphi * ‖l‖) * Cq_hkm
      + Kstar2 * (Cphi * ‖m‖) * Cq_hkl := by positivity
  have hΘbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t‖
        ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖)
          + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hk
          + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hl
          + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hm
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_kl
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_km
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lm
          + Kstar2 * Cq_hk * Cq_lm
          + Kstar2 * Cq_hl * Cq_km
          + Kstar2 * Cq_hm * Cq_kl
          + Kstar2 * (Cphi * ‖h‖) * Cq_klm
          + Kstar2 * (Cphi * ‖k‖) * Cq_hlm
          + Kstar2 * (Cphi * ‖l‖) * Cq_hkm
          + Kstar2 * (Cphi * ‖m‖) * Cq_hkl :=
    fun t ht => expJet4Rhs_norm_le g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm
      h k l m Kstar4 Kstar3 Kstar2 Cphi Cq_hk Cq_hl Cq_hm Cq_kl Cq_km Cq_lm
      Cq_hkl Cq_hkm Cq_hlm Cq_klm hKstar40 hKstar30 hKstar20 hCphi0
      hKstar4 hKstar3 hKstar2 hCphi hCqhk hCqhl hCqhm hCqkl hCqkm hCqlm
      hCqhkl hCqhkm hCqhlm hCqklm t ht
  exact gronwall_vec_residual R
    (fun t => expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar _ hKstar0 hρ0 hR0 hderiv hKstar hΘbd

/-- **The `[0,1]`-uniform value bound for the fourth variation `R^{hklm}`.**  The `∀ t ∈ [0,1]`
    mirror of `expJet4Fund_value_bound` (its `t = 1` endpoint): with the fourteen-term `Θ₄^{hklm}`
    source bound (`expJet4Rhs_norm_le`) fed into the `[0,1]`-uniform vector Grönwall
    (`gronwall_vec_residual_Icc`), `‖R t‖ ≤ ρ₄·e^{Kstar}` for every `t`. -/
theorem expJet4Fund_value_bound_Icc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n)) (h k l m : Point n)
    (Kstar Kstar4 Kstar3 Kstar2 Cphi : ℝ)
    (Cq_hk Cq_hl Cq_hm Cq_kl Cq_km Cq_lm : ℝ)
    (Cq_hkl Cq_hkm Cq_hlm Cq_klm : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar40 : 0 ≤ Kstar4) (hKstar30 : 0 ≤ Kstar3) (hKstar20 : 0 ≤ Kstar2)
    (hCphi0 : 0 ≤ Cphi)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hKstar4 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)‖
        ≤ Kstar4)
    (hKstar3 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3)
    (hKstar2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2)
    (hCphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi)
    (hCqhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhk t‖ ≤ Cq_hk)
    (hCqhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhl t‖ ≤ Cq_hl)
    (hCqhm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhm t‖ ≤ Cq_hm)
    (hCqkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq_kl)
    (hCqkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkm t‖ ≤ Cq_km)
    (hCqlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlm t‖ ≤ Cq_lm)
    (hCqhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkl t‖ ≤ Cq_hkl)
    (hCqhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkm t‖ ≤ Cq_hkm)
    (hCqhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlm t‖ ≤ Cq_hlm)
    (hCqklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklm t‖ ≤ Cq_klm)
    (R : ℝ → (Point n × Point n)) (hR0 : R 0 = 0)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
        + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
        (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖R t‖ ≤ (Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖)
        + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hk
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hl
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hm
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_kl
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_km
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lm
        + Kstar2 * Cq_hk * Cq_lm
        + Kstar2 * Cq_hl * Cq_km
        + Kstar2 * Cq_hm * Cq_kl
        + Kstar2 * (Cphi * ‖h‖) * Cq_klm
        + Kstar2 * (Cphi * ‖k‖) * Cq_hlm
        + Kstar2 * (Cphi * ‖l‖) * Cq_hkm
        + Kstar2 * (Cphi * ‖m‖) * Cq_hkl) * Real.exp Kstar := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num [Set.mem_Icc]
  have hCqhk0 : 0 ≤ Cq_hk := (norm_nonneg _).trans (hCqhk 0 hmem0)
  have hCqhl0 : 0 ≤ Cq_hl := (norm_nonneg _).trans (hCqhl 0 hmem0)
  have hCqhm0 : 0 ≤ Cq_hm := (norm_nonneg _).trans (hCqhm 0 hmem0)
  have hCqkl0 : 0 ≤ Cq_kl := (norm_nonneg _).trans (hCqkl 0 hmem0)
  have hCqkm0 : 0 ≤ Cq_km := (norm_nonneg _).trans (hCqkm 0 hmem0)
  have hCqlm0 : 0 ≤ Cq_lm := (norm_nonneg _).trans (hCqlm 0 hmem0)
  have hCqhkl0 : 0 ≤ Cq_hkl := (norm_nonneg _).trans (hCqhkl 0 hmem0)
  have hCqhkm0 : 0 ≤ Cq_hkm := (norm_nonneg _).trans (hCqhkm 0 hmem0)
  have hCqhlm0 : 0 ≤ Cq_hlm := (norm_nonneg _).trans (hCqhlm 0 hmem0)
  have hCqklm0 : 0 ≤ Cq_klm := (norm_nonneg _).trans (hCqklm 0 hmem0)
  have hρ0 : (0 : ℝ) ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖)
      + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hk
      + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hl
      + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hm
      + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_kl
      + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_km
      + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lm
      + Kstar2 * Cq_hk * Cq_lm
      + Kstar2 * Cq_hl * Cq_km
      + Kstar2 * Cq_hm * Cq_kl
      + Kstar2 * (Cphi * ‖h‖) * Cq_klm
      + Kstar2 * (Cphi * ‖k‖) * Cq_hlm
      + Kstar2 * (Cphi * ‖l‖) * Cq_hkm
      + Kstar2 * (Cphi * ‖m‖) * Cq_hkl := by positivity
  have hΘbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t‖
        ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖)
          + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hk
          + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hl
          + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hm
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_kl
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_km
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lm
          + Kstar2 * Cq_hk * Cq_lm
          + Kstar2 * Cq_hl * Cq_km
          + Kstar2 * Cq_hm * Cq_kl
          + Kstar2 * (Cphi * ‖h‖) * Cq_klm
          + Kstar2 * (Cphi * ‖k‖) * Cq_hlm
          + Kstar2 * (Cphi * ‖l‖) * Cq_hkm
          + Kstar2 * (Cphi * ‖m‖) * Cq_hkl :=
    fun t ht => expJet4Rhs_norm_le g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm
      h k l m Kstar4 Kstar3 Kstar2 Cphi Cq_hk Cq_hl Cq_hm Cq_kl Cq_km Cq_lm
      Cq_hkl Cq_hkm Cq_hlm Cq_klm hKstar40 hKstar30 hKstar20 hCphi0
      hKstar4 hKstar3 hKstar2 hCphi hCqhk hCqhl hCqhm hCqkl hCqkm hCqlm
      hCqhkl hCqhkm hCqhlm hCqklm t ht
  exact gronwall_vec_residual_Icc R
    (fun t => expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar _ hKstar0 hρ0 hR0 hderiv hKstar hΘbd

end QIQTH.ExpMap
