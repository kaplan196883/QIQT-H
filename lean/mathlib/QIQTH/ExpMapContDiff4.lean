/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapContDiff3

/-!
# Toward `ContDiff⁴ exp_p` — Rung 4 of the exponential-map smooth-dependence tower

This file lands the **Rung-4 reduction** for the `q`-centered exponential map, one Fréchet-derivative
order above the Rung-3 capstone `expMap_contDiffOn_three` in `ExpMapContDiff3.lean`.

* `contDiff_fderiv4_geodesicField` — the geodesic field's **fourth Fréchet derivative**
  `D⁴F := fderiv (fderiv (fderiv (fderiv F)))` is `C^∞` (a one-line extension of
  `contDiff_fderiv3_geodesicField`; the field is `C^∞`, so every Fréchet derivative is `C^∞`).

* `expMap_contDiffOn_four_of_fderiv3_contDiffOn_one` — the **proven Rung-4 reduction**: IF the third
  derivative map `v ↦ fderiv³ exp_p v` is `ContDiffOn ℝ 1` on the exp-ball, THEN `exp_p` is
  `ContDiffOn ℝ 4` there.  This is the clean mirror of the Rung-3 reduction
  (`expMap_contDiffOn_three_of_fderiv2_contDiffOn_one`), one order higher: it bootstraps off the
  UNCONDITIONAL `expMap_contDiffOn_three` (which already yields `fderiv exp_p ∈ ContDiff²` and
  `fderiv² exp_p ∈ ContDiff¹`), and chains `contDiffOn_succ_of_fderivWithin` three times on the open
  ball.

## Honest firewall (binding)

**What is proven here:** the reduction — the genuine remaining obligation `hfd3` (the Jet₄ third-jet
map is `C¹`, equivalently `fderiv⁴ exp_p` exists and is continuous on the ball) is carried as an
EXPLICIT hypothesis and is genuinely used.  `contDiff_fderiv4_geodesicField` gives the *field*'s
fourth-derivative regularity for free, but that alone does NOT discharge `hfd3`: `exp_p` solves the
geodesic ODE, so its fourth-jet `C¹` regularity requires the Jet₄ fundamental-solution / Grönwall
machinery (the `expJetD4_two_pt_diff` analog of `expJetD3_two_pt_diff`), which is NOT built here.

**What is NOT closed:** this does NOT build the Jet₄ fourth-variation fundamental solution, does NOT
discharge `hfd3` unconditionally, does NOT reach `κ = 1/6`, the heat-kernel parametrix, or
`a₁ = R/6`, and is NOT numerical-`G` / the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

-- The codomain of `D⁴F` is a QUADRUPLY-nested continuous-linear-map space; its normed-group instance
-- chains one level deeper than the `D³F` case, so we raise the pending-instance synthesis depth.
set_option maxSynthPendingDepth 4

variable {n : ℕ}

/-! ### The geodesic field's fourth Fréchet derivative `D⁴F` is `C^∞` -/

/-- The geodesic field's **fourth Fréchet derivative** `D⁴F = fderiv (fderiv (fderiv (fderiv F)))` is
    `C^∞`.  (`D³F = fderiv (fderiv (fderiv F))` is `C^∞` by `contDiff_fderiv3_geodesicField`;
    differentiate once more.) -/
theorem contDiff_fderiv4_geodesicField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) :=
  (contDiff_fderiv3_geodesicField g gi hC).fderiv_right le_top

/-! ### The Rung-4 reduction to the crux `ContDiff¹ (fderiv³ exp_p)` -/

/-- **The Rung-4 reduction (proven).**  If the third-derivative map
    `v ↦ fderiv (fun z => fderiv (fun w => fderiv exp_p w) z) v` is `ContDiffOn ℝ 1` on the ball
    `‖v‖ < expRho`, then `exp_p` is `ContDiffOn ℝ 4` there.  A clean mirror of the Rung-3 reduction
    (`expMap_contDiffOn_three_of_fderiv2_contDiffOn_one`), one Fréchet-derivative order higher.

    Route (bootstrap off the unconditional Rung-3 capstone, then chain
    `contDiffOn_succ_of_fderivWithin` three times on the open ball, where `fderivWithin = fderiv` via
    `fderivWithin_of_isOpen`):
    * `F₁ := fderiv exp_p` is `ContDiffOn ℝ 2` on the ball (from Rung 3, `expMap_contDiffOn_three`
      through `ContDiffOn.fderiv_of_isOpen`); hence `F₂ := fderiv F₁` is `ContDiffOn ℝ 1` and
      `DifferentiableOn`.  With the crux `hfd3` (which is exactly `ContDiff¹ (fderivWithin F₂ s)`
      after `fderivWithin = fderiv`), `contDiffOn_succ_of_fderivWithin` gives `ContDiffOn ℝ 2 F₂`.
    * `F₁` is `DifferentiableOn` with `fderivWithin F₁ s = F₂`; `contDiffOn_succ_of_fderivWithin`
      gives `ContDiffOn ℝ 3 F₁`.
    * `exp_p` is `DifferentiableOn` (Rung 1, `expMap_contDiffOn_one`) with `fderivWithin exp_p s = F₁`;
      `contDiffOn_succ_of_fderivWithin` gives `ContDiffOn ℝ (3+1) exp_p`, and `(3+1 : WithTop ℕ∞) = 4`.

    HONEST: this ISOLATES the remaining Rung-4 obligation (`ContDiff¹ (fderiv³ exp_p)`, the Jet₃
    fundamental solution is `C¹` in the base parameter — equivalently the fourth jet exists and is
    continuous); it does NOT discharge it (that is the Jet₄ sub-campaign, the `D⁴F`-level analog of
    the `expJetD3_two_pt_diff` Lipschitz machinery, not built here). -/
theorem expMap_contDiffOn_four_of_fderiv3_contDiffOn_one
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hfd3 : ContDiffOn ℝ 1
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) v)
      (Metric.ball (0 : Point n) (expRho g gi hC p))) :
    ContDiffOn ℝ 4 (expMap g gi hC p) (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  set s : Set (Point n) := Metric.ball (0 : Point n) (expRho g gi hC p) with hsdef
  -- `F₁ := fderiv exp_p` is `ContDiffOn ℝ 2` on the open ball (Rung 3, `ContDiffOn.fderiv_of_isOpen`).
  have hF1cd2 : ContDiffOn ℝ 2 (fun v => fderiv ℝ (expMap g gi hC p) v) s :=
    (expMap_contDiffOn_three g gi hC p).fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  -- `F₂ := fderiv F₁` is `ContDiffOn ℝ 1`, hence `DifferentiableOn`.
  have hF2cd1 : ContDiffOn ℝ 1
      (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) s :=
    hF1cd2.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hF2diff : DifferentiableOn ℝ
      (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) s :=
    hF2cd1.differentiableOn (by norm_num)
  -- Step 1: `ContDiffOn ℝ 2 F₂ s`, using the crux `hfd3` (`= ContDiff¹ (fderivWithin F₂ s)`).
  have hfw_F3 : ContDiffOn ℝ 1
      (fun v => fderivWithin ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) s v) s :=
    hfd3.congr (fun v hv => fderivWithin_of_isOpen Metric.isOpen_ball hv)
  have hF2cd2 : ContDiffOn ℝ (1 + 1)
      (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) s :=
    contDiffOn_succ_of_fderivWithin hF2diff (by simp) hfw_F3
  have e2 : (1 : WithTop ℕ∞) + 1 = 2 := by norm_num
  rw [e2] at hF2cd2
  -- Step 2: `ContDiffOn ℝ 3 F₁ s`.
  have hF1diff : DifferentiableOn ℝ (fun v => fderiv ℝ (expMap g gi hC p) v) s :=
    hF1cd2.differentiableOn (by norm_num)
  have hfw_F2 : ContDiffOn ℝ 2
      (fun v => fderivWithin ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) s v) s :=
    hF2cd2.congr (fun v hv => fderivWithin_of_isOpen Metric.isOpen_ball hv)
  have hF1cd3 : ContDiffOn ℝ (2 + 1) (fun v => fderiv ℝ (expMap g gi hC p) v) s :=
    contDiffOn_succ_of_fderivWithin hF1diff (by simp) hfw_F2
  have e3 : (2 : WithTop ℕ∞) + 1 = 3 := by norm_num
  rw [e3] at hF1cd3
  -- Step 3: `ContDiffOn ℝ 4 exp_p s`.
  have hexpdiff : DifferentiableOn ℝ (expMap g gi hC p) s :=
    (expMap_contDiffOn_one g gi hC p).differentiableOn (by norm_num)
  have hfw_F1 : ContDiffOn ℝ 3 (fun v => fderivWithin ℝ (expMap g gi hC p) s v) s :=
    hF1cd3.congr (fun v hv => fderivWithin_of_isOpen Metric.isOpen_ball hv)
  have hres : ContDiffOn ℝ (3 + 1) (expMap g gi hC p) s :=
    contDiffOn_succ_of_fderivWithin hexpdiff (by simp) hfw_F1
  have e4 : (3 : WithTop ℕ∞) + 1 = 4 := by norm_num
  rwa [e4] at hres

end QIQTH.ExpMap
