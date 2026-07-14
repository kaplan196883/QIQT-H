/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapContDiff

/-!
# Toward `ContDiff² exp_p` — Rung 2 of the `ContDiff³ exp_p` tower

`ContDiff² exp_p` (the geodesic exp map is twice continuously differentiable near `0`), via the
parameter-`C¹` dependence of the operator fundamental solution `Φ_v` (the Jet₂ augmented ODE,
equilibrium-Grönwall — NOT the general C²-flow theorem Mathlib lacks).  **Rung 2 of the
`ContDiff³ exp_p` tower** (`THE_EXP_JETS_PLAN.md`).

The route (per the plan): `ContDiff² = ContDiff¹` (Rung 1, `expMap_contDiffOn_one`) `+` the first
derivative map `v ↦ fderiv exp_p v = π ∘ (Φ_v 1) ∘ ι` is itself `ContDiff¹`.  Via Mathlib's
`contDiffOn_succ_of_fderivWithin` (and `fderivWithin = fderiv` on the open ball,
`fderivWithin_of_isOpen`), this reduces **cleanly and unconditionally** to the single obligation

  `ContDiffOn ℝ 1 (fun v => fderiv exp_p v) (ball 0 expRho)`   -- the crux `Φ_v(1)` is `C¹` in `v`.

This file lands (all `[AF]`, no `sorry`):
* `expMap_contDiffOn_two_of_fderiv_contDiffOn_one` — the **proven reduction**: the crux
  `ContDiffOn ℝ 1 (fderiv exp_p) ball` implies `ContDiff² exp_p` on the ball.  (Isolates the exact
  remaining Rung-2 obligation in the project's own terms — the whole route in one theorem.)
* `contDiff_fderiv_geodesicField` — the geodesic field's Fréchet derivative `DF` is `C^∞`; hence the
  **second Fréchet derivative `D²F = fderiv (fderiv F)` exists and is `C^∞`**
  (`hasFDerivAt_fderiv_geodesicField`, `contDiff_fderiv2_geodesicField`).  This is the Jet₂ analytic
  ingredient (`∂_v Ψ_v`) at the level of *existence + smoothness* — the coefficient of the
  inhomogeneous term of the Jet₂ fundamental-solution ODE `Q' = Ψ_v Q + (∂_v Ψ_v) Φ_v`.

## Honest firewall (binding) — CHECKPOINT

**What is proven here:** the reduction of `ContDiff² exp_p` to the crux `ContDiff¹ (fderiv exp_p)`
(equivalently, `v ↦ Φ_v(1)` is `C¹`), and the `D²F` analytic ingredient at the level of existence
and `C^∞`-smoothness.

**What is NOT yet closed (the exact obstruction, honest):** the crux hypothesis
`ContDiffOn ℝ 1 (fderiv exp_p) ball` is **NOT discharged**.  Discharging it needs, in order:
1. the **closed form of `D²F`** (in application form `D²F(x,u)(a,b)(ξ,η)`, an explicit `Γ/∂Γ/∂²Γ`
   expression — reachable by extending `geodesicField_fderiv_apply` one order via the `pd`/second-
   partial infrastructure `christoffel_pd_contDiff`, `fderiv_apply_eq_sum_pd`, `pd_pd_eq`; a large
   but self-contained scalar-level `HasFDerivAt` computation — NOT a Mathlib gap, pure assembly);
2. the **Jet₂ fundamental solution `Q_v = ∂_v Φ_v`** — the operator-bilinear-valued solution of
   `Q'(t) = Ψ_v(t)∘Q(t) + (∂_vΨ_v)(t)∘Φ_v(t)`, `Q(0) = 0`, built on `[0,1]` by the SAME
   Picard–Lindelöf concatenation machinery (`expJetFund_local` → `_shifted` → `_glue` → `expJetFund`)
   that built `Φ_v`;
3. the **parameter-residual Grönwall** `S_h = Φ_{v+h} − Φ_v − Q_v(h) = o(‖h‖)` ⟹
   `HasFDerivAt (v ↦ Φ_v 1) (Q_v 1) v`, plus a second parameter-Grönwall (as in Rung 1's
   `expFund_two_pt_diff`) for continuity of `v ↦ Q_v 1`, giving `C¹`.

Building `Q_v` on `[0,1]` (a fresh bilinear-valued PL tower) is the multi-week bulk of Rung 2 and is
**not** attempted here.  It is pure assembly + the (also unwritten) `D²F` closed form, NOT a Mathlib
gap.

⚠ This does NOT reach `ContDiff³` (Rung 3, needed for `κ = 1/6` via the `g̃` derivative-loss), does
NOT build the heat-kernel parametrix, does NOT discharge general `a₁ = R/6`, is NOT numerical-`G`,
and is NOT the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-! ### The reduction to the crux `ContDiff¹ (fderiv exp_p)` -/

/-- **The Rung-2 reduction (proven).**  If the first-derivative map `v ↦ fderiv exp_p v` is
    `ContDiffOn ℝ 1` on the ball `‖v‖ < expRho`, then `exp_p` is `ContDiffOn ℝ 2` there.

    Route: `exp_p` is differentiable on the ball (from Rung 1, `expMap_contDiffOn_one`); the open ball
    has unique derivatives, so `fderivWithin = fderiv` there (`fderivWithin_of_isOpen`); Mathlib's
    `contDiffOn_succ_of_fderivWithin` upgrades `C¹`-of-the-derivative to `C²` of the function.

    HONEST: this ISOLATES the remaining Rung-2 obligation (`ContDiff¹ (fderiv exp_p)`, i.e. the
    fundamental solution `Φ_v(1)` is `C¹` in `v`); it does NOT discharge it (that needs the Jet₂
    solution `Q_v`, see the module firewall). -/
theorem expMap_contDiffOn_two_of_fderiv_contDiffOn_one
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hfd : ContDiffOn ℝ 1 (fun v => fderiv ℝ (expMap g gi hC p) v)
      (Metric.ball (0 : Point n) (expRho g gi hC p))) :
    ContDiffOn ℝ 2 (expMap g gi hC p) (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  set s : Set (Point n) := Metric.ball (0 : Point n) (expRho g gi hC p) with hsdef
  have hdiff : DifferentiableOn ℝ (expMap g gi hC p) s :=
    (expMap_contDiffOn_one g gi hC p).differentiableOn (by norm_num)
  have hfw : ContDiffOn ℝ 1 (fun v => fderivWithin ℝ (expMap g gi hC p) s v) s :=
    hfd.congr (fun v hv => fderivWithin_of_isOpen Metric.isOpen_ball hv)
  have hres : ContDiffOn ℝ (1 + 1) (expMap g gi hC p) s :=
    contDiffOn_succ_of_fderivWithin hdiff (by simp) hfw
  have h2 : (1 : WithTop ℕ∞) + 1 = 2 := by norm_num
  rwa [h2] at hres

/-! ### The Jet₂ analytic ingredient `D²F` — existence and `C^∞`-smoothness -/

/-- The geodesic field's Fréchet derivative `DF = fderiv F` is `C^∞`.  (`geodesicField` is `C^∞` by
    `contDiff_geodesicField`; differentiate once.) -/
theorem contDiff_fderiv_geodesicField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (geodesicField g gi)) :=
  (contDiff_geodesicField g gi hC).fderiv_right le_top

/-- The geodesic field's **second Fréchet derivative** `D²F = fderiv (fderiv F)` is `C^∞`. -/
theorem contDiff_fderiv2_geodesicField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fderiv ℝ (fderiv ℝ (geodesicField g gi))) :=
  (contDiff_fderiv_geodesicField g gi hC).fderiv_right le_top

/-- `D²F` exists at every point as an honest Fréchet derivative:
    `HasFDerivAt (fderiv F) (D²F q) q` with `D²F q = fderiv (fderiv F) q`. -/
theorem hasFDerivAt_fderiv_geodesicField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q : Point n × Point n) :
    HasFDerivAt (fderiv ℝ (geodesicField g gi))
      (fderiv ℝ (fderiv ℝ (geodesicField g gi)) q) q :=
  ((contDiff_fderiv_geodesicField g gi hC).differentiable (by simp)).differentiableAt.hasFDerivAt

/-- **Uniform operator-norm bound of `D²F` over the `[0,1]` confined tube.**  The direct `D²F`
    analog of `expJet_fderiv_tube_bddAbove_unif` (which bounds the first derivative `DF`).
    Confinement (`expTube_spec`) puts every tube point `expTube p v t` (for `‖v‖ ≤ expRho`,
    `t ∈ [0,1]`) in a FIXED closed ball around `(p, 0)`; `D²F = fderiv (fderiv F)` is continuous
    (`contDiff_fderiv2_geodesicField`), so a continuous function on that compact ball is bounded,
    yielding a uniform `Kstar`. -/
theorem expJet_fderiv2_tube_bddAbove_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ Kstar : ℝ, 0 ≤ Kstar ∧ ∀ v : Point n, ‖v‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar := by
  have hC₀ := expConst_nonneg g gi hC p
  have hρ0 : 0 ≤ expRho g gi hC p := (expRho_pos g gi hC p).le
  set Rb : ℝ := expConst g gi hC p * expRho g gi hC p with hRbdef
  -- Route through the ℝ-valued norm function `q ↦ ‖D²F q‖` to avoid the nested-CLM topology
  -- diamond that `exists_bound_of_continuousOn` hits on the codomain `E →L[ℝ] E →L[ℝ] E`.
  have hdFcont : Continuous (fun q => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) q‖) :=
    ((contDiff_fderiv_geodesicField g gi hC).continuous_fderiv (by simp)).norm
  obtain ⟨C, hC'⟩ :=
    (isCompact_closedBall ((p, 0) : Point n × Point n) Rb).exists_bound_of_continuousOn
      hdFcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun v hv t ht => ?_⟩
  have hmem : expTube g gi hC p v t ∈ Metric.closedBall ((p, 0) : Point n × Point n) Rb := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    obtain ⟨_, _, hconf⟩ := expTube_spec g gi hC p v hv
    calc ‖expTube g gi hC p v t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖v‖ := hconf t ht
      _ ≤ Rb := by rw [hRbdef]; exact mul_le_mul_of_nonneg_left hv hC₀
  have hbnd := hC' _ hmem
  calc ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖
      ≤ C := le_trans (le_abs_self _) (by simpa using hbnd)
    _ ≤ max C 0 := le_max_left _ _

/-- **`D²F` is Lipschitz on the confined tube ball.**  The direct `D²F` analog of the `hLipDF`
    hypothesis (`LipschitzOnWith Ldf (fderiv F) ball`) that `expFund_two_pt_diff` consumes for `DF`.
    `D²F = fderiv (fderiv F)` is `C^∞` (`contDiff_fderiv2_geodesicField`), hence `C¹`, and the tube
    ball `Metric.closedBall (p,0) (expConst · expRho)` is compact and convex; a `C¹` map is Lipschitz
    on a compact convex set (`ContDiffOn.exists_lipschitzOnWith`).  Mirrors verbatim the DF-Lipschitz
    discharge (`hLipDF`) inside `fderivExpMap_continuousOn`. -/
theorem expJet_fderiv2_lipschitzOnWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ Ld2f : NNReal, LipschitzOnWith Ld2f (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) :=
  ((contDiff_fderiv2_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)

end QIQTH.ExpMap
