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

/-! ### Sub-brick 3a — the inhomogeneous source `Θ^{hk}` of the Jet₂ second-variation ODE

The second variation `Q^{hk}(t)` of the flow (vector-valued in `Point n × Point n`) solves the
INHOMOGENEOUS linear ODE `Q'(t) = DF(Y_v t)·Q(t) + Θ^{hk}(t)`, `Q(0) = 0`, whose homogeneous part is
propagated by the built fundamental solution `Φ_v` (`expJetFund`, coefficient `expJetPsi`).  The
inhomogeneous SOURCE is
`Θ^{hk}(t) = D²F(Y_v t)( Φ_v(t)(ι h) )( Φ_v(t)(ι k) )`, `ι = expJetIota` (`h ↦ (0,h)`),
`D²F = fderiv (fderiv F)` (`contDiff_fderiv2_geodesicField`).

Because `Φ_v` is the ∃-object of `expJetFund` (not a global def), we PARAMETRIZE by an abstract `Φ`,
exactly as `expFund_two_pt_diff` does.  This sub-brick delivers the source `def` plus its `[0,1]`
regularity (continuity + a uniform norm bound), the well-posedness data the (next) `Q^{hk}`
construction consumes.  It does NOT build `Q^{hk}` (the multi-week bilinear-valued PL tower). -/

/-- **The inhomogeneous source term `Θ^{hk}(t)` of the Jet₂ second-variation ODE.**
    `Θ^{hk}(t) = D²F(Y_v t)( Φ(t)(ι h) )( Φ(t)(ι k) )`, where `D²F = fderiv (fderiv F)` (the second
    Fréchet derivative of the geodesic field, `contDiff_fderiv2_geodesicField`), `Y_v t = expTube p v t`
    is the confined geodesic tube, `ι = expJetIota` (`h ↦ (0,h)`), and `Φ` is the operator-valued
    fundamental solution (abstract argument, instantiated at `expJetFund`'s witness downstream).
    `fderiv (fderiv F) x : E →L[ℝ] E →L[ℝ] E`, applied to the two vectors gives an element of `E`. -/
noncomputable def expJet2Rhs (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))) (h k : Point n) (t : ℝ) :
    Point n × Point n :=
  (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
    (Φ t (expJetIota h)) (Φ t (expJetIota k))

@[simp] theorem expJet2Rhs_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))) (h k : Point n) (t : ℝ) :
    expJet2Rhs g gi hC p v Φ h k t
      = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota k)) := rfl

/-- **`Θ^{hk}` is continuous on `[0,1]`.**  For `‖v‖ ≤ expRho` and `Φ` continuous on `[0,1]`:
    `D²F` is continuous (`contDiff_fderiv2_geodesicField`), `t ↦ Y_v t` is continuous on `[0,1]`
    (`expTube_continuousOn`), so `t ↦ D²F(Y_v t)` is continuous there; `t ↦ Φ t (ι h)` and
    `t ↦ Φ t (ι k)` are continuous (`ContinuousOn.clm_apply` against the fixed vectors `ι h`, `ι k`);
    the bilinear CLM application `(A, a, b) ↦ A a b` is continuous, applied via `ContinuousOn.clm_apply`
    twice. -/
theorem expJet2Rhs_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦ : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (h k : Point n) :
    ContinuousOn (fun t => expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) := by
  -- `t ↦ D²F(Y_v t)` continuous on `[0,1]`.
  have hD2cont : Continuous (fderiv ℝ (fderiv ℝ (geodesicField g gi))) :=
    (contDiff_fderiv2_geodesicField g gi hC).continuous
  have hA : ContinuousOn
      (fun t => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Set.Icc (0 : ℝ) 1) :=
    hD2cont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)
  -- `t ↦ Φ t (ι h)` and `t ↦ Φ t (ι k)` continuous on `[0,1]`.
  have ha : ContinuousOn (fun t => Φ t (expJetIota h)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  have hb : ContinuousOn (fun t => Φ t (expJetIota k)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  -- assemble via the bilinear CLM application (`ContinuousOn.clm_apply` twice).
  simpa only [expJet2Rhs_apply] using (hA.clm_apply ha).clm_apply hb

/-- **Uniform `[0,1]` norm bound of `Θ^{hk}`.**  For `‖v‖ ≤ expRho`, `t ∈ [0,1]`, given a `D²F`
    tube bound `Kstar` (`expJet_fderiv2_tube_bddAbove_unif`) and a `[0,1]`-bound `Cphi` on `‖Φ t‖`,
    `‖Θ^{hk}(t)‖ ≤ Kstar · (Cphi·‖h‖) · (Cphi·‖k‖)`.  Two applications of `ContinuousLinearMap.le_opNorm`
    for the bilinear `D²F`, and `‖ι h‖ ≤ ‖h‖` (`expJetIota` is a norm-`≤ 1` CLM).  This is the ODE
    well-posedness bound the (next) `Q^{hk}` construction consumes. -/
theorem expJet2Rhs_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))) (h k : Point n)
    (Kstar Cphi : ℝ) (hKstar0 : 0 ≤ Kstar) (hCphi0 : 0 ≤ Cphi)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hCphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖expJet2Rhs g gi hC p v Φ h k t‖ ≤ Kstar * (Cphi * ‖h‖) * (Cphi * ‖k‖) := by
  set D2 := fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t) with hD2
  set a := Φ t (expJetIota h) with ha
  set b := Φ t (expJetIota k) with hb
  -- `‖ι h‖ ≤ ‖h‖`, `‖ι k‖ ≤ ‖k‖`.
  have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ := by
    refine ((expJetIota (n := n)).le_opNorm h).trans ?_
    simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h)
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ := by
    refine ((expJetIota (n := n)).le_opNorm k).trans ?_
    simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k)
  -- `‖a‖ ≤ Cphi·‖h‖`, `‖b‖ ≤ Cphi·‖k‖`.
  have hanorm : ‖a‖ ≤ Cphi * ‖h‖ := by
    calc ‖a‖ ≤ ‖Φ t‖ * ‖expJetIota (n := n) h‖ := (Φ t).le_opNorm _
      _ ≤ Cphi * ‖h‖ :=
        mul_le_mul (hCphi t ht) hιh (norm_nonneg _) hCphi0
  have hbnorm : ‖b‖ ≤ Cphi * ‖k‖ := by
    calc ‖b‖ ≤ ‖Φ t‖ * ‖expJetIota (n := n) k‖ := (Φ t).le_opNorm _
      _ ≤ Cphi * ‖k‖ :=
        mul_le_mul (hCphi t ht) hιk (norm_nonneg _) hCphi0
  -- bilinear opNorm: `‖D2 a b‖ ≤ ‖D2‖·‖a‖·‖b‖ ≤ Kstar·(Cphi‖h‖)·(Cphi‖k‖)`.
  have hCh0 : 0 ≤ Cphi * ‖h‖ := mul_nonneg hCphi0 (norm_nonneg _)
  have hbil : ‖D2 a b‖ ≤ ‖D2‖ * ‖a‖ * ‖b‖ := by
    calc ‖D2 a b‖ ≤ ‖D2 a‖ * ‖b‖ := (D2 a).le_opNorm b
      _ ≤ (‖D2‖ * ‖a‖) * ‖b‖ :=
        mul_le_mul_of_nonneg_right (D2.le_opNorm a) (norm_nonneg b)
  refine le_trans (by simpa only [expJet2Rhs_apply, ← hD2, ← ha, ← hb] using hbil) ?_
  refine mul_le_mul (mul_le_mul (hKstar t ht) hanorm (norm_nonneg _) hKstar0) hbnorm
    (norm_nonneg _) (mul_nonneg hKstar0 hCh0)

/-! ### Sub-brick 3b — the LOCAL Jet₂ second-variation solution `Q^{hk}` -/

set_option maxHeartbeats 1000000 in
/-- **EXP-JET3b — the LOCAL second-variation fundamental solution `Q^{hk}`.**  For `‖v‖ ≤ expRho`
    and `Φ` continuous on `[0,1]`, there is a short time `T > 0` and a VECTOR-valued curve
    `Q : ℝ → Point n × Point n` with `Q 0 = 0` solving the INHOMOGENEOUS linear Jet₂ ODE
    `Q'(t) = DF(Y_v t)(Q t) + Θ^{hk}(t)` on `[0, T]`, where `DF = fderiv (geodesicField g gi)`,
    `Y_v t = expTube p v t`, and `Θ^{hk} = expJet2Rhs …` is the 3a source term.

    Built by the FULL vector-normed `IsPicardLindelof` instantiation of the AFFINE field
    `F₂ t Q := DF(Y_v t)(Q) + Θ^{hk}(t)` on `closedBall(0, 1)`, centred at `Q₀ = 0`:
    the source `Θ` is CONSTANT in `Q`, so it drops out of the difference and `F₂` is `KdF`-Lipschitz
    in `Q` (`KdF` = the `DF` tube bound `expJet_fderiv_tube_bddAbove`); it is continuous in `t`
    (`DF(Y_v ·)` continuous ∘ `expJet2Rhs_continuousOn`); bounded by `KdF + Cθ` on the ball
    (`Cθ` = a `[0,1]`-bound on `‖Θ‖`, obtained since `Θ` is continuous on the compact `Icc`); and the
    interval constraint `(KdF + Cθ)·T ≤ 1` is met by `T = min 1 (1/(KdF + Cθ + 1))`.
    The Mathlib extraction is `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` (`r = 0`).

    HONEST: this is the LOCAL (short-interval) Jet₂ solution — the affine vector-normed PL
    instantiation.  It does NOT reach `Q^{hk}(1)` (that needs the inhomogeneous concatenation with
    varying initial data past the `mul_max_le` interval bound), NOT the parameter-residual Grönwall
    `∂_v Φ_v = Q`, NOT `ContDiff¹ (fderiv exp_p)`, NOT numerical-G. -/
theorem expJet2Fund_local (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (h k : Point n) :
    ∃ T > (0 : ℝ), ∃ Q : ℝ → (Point n × Point n),
      Q 0 = 0 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt Q
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q t)
             + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) T) t := by
  obtain ⟨KdF, hKdF0, hKdF⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  -- `Θ^{hk}` is continuous on the compact `[0,1]`, hence uniformly bounded by some `Cθ ≥ 0`.
  have hΘcont : ContinuousOn (fun t => expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) :=
    expJet2Rhs_continuousOn g gi hC p v hv Φ hΦcont h k
  obtain ⟨Cθ0, hCθ0⟩ := isCompact_Icc.exists_bound_of_continuousOn hΘcont
  set Cθ : ℝ := max Cθ0 0 with hCθdef
  have hCθnn : 0 ≤ Cθ := le_max_right _ _
  have hCθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖expJet2Rhs g gi hC p v Φ h k t‖ ≤ Cθ :=
    fun t ht => (hCθ0 t ht).trans (le_max_left _ _)
  -- the affine vector field `F₂ t Q = DF(Y_v t)(Q) + Θ^{hk}(t)`.
  set F₂ : ℝ → (Point n × Point n) → (Point n × Point n) :=
    fun t Q => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) Q
      + expJet2Rhs g gi hC p v Φ h k t with hF₂
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
  have hpl : IsPicardLindelof F₂
      (tmin := (0 : ℝ)) (tmax := T) ⟨0, ⟨le_refl 0, hT0.le⟩⟩
      (0 : Point n × Point n) 1 0 Lnn Knn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in `Q` on `closedBall(0,1)` with constant `KdF` (source drops out).
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro M _ N _
      simp only [dist_eq_norm, hKnn]
      have hsub : F₂ t M - F₂ t N
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (M - N) := by
        simp only [hF₂, map_sub]; abel
      rw [hsub]
      calc ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (M - N)‖
          ≤ ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ * ‖M - N‖ :=
            (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).le_opNorm _
        _ ≤ KdF * ‖M - N‖ := mul_le_mul_of_nonneg_right (hKdF t htIcc) (norm_nonneg _)
    · -- continuity in `t` for fixed `Q`.
      intro x _
      have h1 : ContinuousOn
          (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x)
          (Set.Icc (0 : ℝ) 1) := hDFtube.clm_apply continuousOn_const
      exact ((h1.add hΘcont).mono hIccsub)
    · -- uniform bound `‖F₂ t Q‖ ≤ KdF + Cθ` on `closedBall(0,1)`.
      intro t ht x hx
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      have hxnorm : ‖x‖ ≤ 1 := by
        have hd := Metric.mem_closedBall.mp hx
        rw [dist_zero_right] at hd
        simpa using hd
      show ‖F₂ t x‖ ≤ KdF + Cθ
      calc ‖F₂ t x‖
          = ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x
              + expJet2Rhs g gi hC p v Φ h k t‖ := by rw [hF₂]
        _ ≤ ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x‖
              + ‖expJet2Rhs g gi hC p v Φ h k t‖ := norm_add_le _ _
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
  obtain ⟨Q, hQ0, hQd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨T, hT0, Q, hQ0, fun t ht => ?_⟩
  have hd := hQd t ht
  simpa only [hF₂] using hd

set_option maxHeartbeats 1000000 in
/-- **EXP-JET3b-[0,1] (concatenation building block) — the SHIFTED Jet₂ second-variation solver.**
    For a `[0,1]`-uniform Jacobi bound `KdF` (threaded externally so one `N` fixes the step) and any
    subinterval `[t₀, t₀+T] ⊆ [0,1]` with `2·KdF·T ≤ 1`, and ANY vector initial datum `x₀`, there is
    a VECTOR-valued curve `Q : ℝ → Point n × Point n` with `Q t₀ = x₀` solving the INHOMOGENEOUS
    linear Jet₂ ODE `Q'(t) = DF(Y_v t)(Q t) + Θ^{hk}(t)` on `[t₀, t₀+T]`, where `DF = fderiv (geodesicField g gi)`,
    `Y_v t = expTube p v t`, and `Θ^{hk} = expJet2Rhs …` is the 3a source term.

    Built by the vector-normed `IsPicardLindelof` instantiation of the AFFINE field
    `F₂ t Q := DF(Y_v t)(Q) + Θ^{hk}(t)`, centred at `x₀` on `closedBall(x₀, a)` with the ball radius
    `a := 2·(KdF·‖x₀‖·T + Cθ·T) + 1` (`Cθ` a `[0,1]`-bound on `‖Θ‖`, from compactness of `Icc`):
    the source is constant in `Q`, so `F₂` is `KdF`-Lipschitz; on the ball `‖F₂ t x‖ ≤ KdF·(‖x₀‖+a)+Cθ =: L`;
    and the interval constraint `L·T ≤ a` closes because `KdF·T ≤ 1/2` forces `KdF·a·T ≤ a/2` (affine
    fields have a global-in-`a` bound, so the linear-in-`a` radius above works for ANY `x₀`).
    Extraction is `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` (`r = 0`).

    HONEST: the shifted local Jet₂ solver from arbitrary vector IC — the reusable brick of the `[0,1]`
    concatenation (matching each piece's ENDPOINT VALUE); it does NOT yet reach `Q^{hk}(1)`, NOT the
    parameter-residual Grönwall `∂_v Φ_v = Q`, NOT `ContDiff¹ (fderiv exp_p)`, NOT numerical-G. -/
theorem expJet2Fund_shifted (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (h k : Point n)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (t₀ T : ℝ) (ht₀ : 0 ≤ t₀) (hT : 0 < T) (hsum : t₀ + T ≤ 1) (hstep : 2 * KdF * T ≤ 1)
    (x₀ : Point n × Point n) :
    ∃ Q : ℝ → (Point n × Point n),
      Q t₀ = x₀ ∧
      ∀ t ∈ Set.Icc t₀ (t₀ + T),
        HasDerivWithinAt Q
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q t)
             + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc t₀ (t₀ + T)) t := by
  -- `Θ^{hk}` is continuous on the compact `[0,1]`, hence uniformly bounded by some `Cθ ≥ 0`.
  have hΘcont : ContinuousOn (fun t => expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) :=
    expJet2Rhs_continuousOn g gi hC p v hv Φ hΦcont h k
  obtain ⟨Cθ0, hCθ0⟩ := isCompact_Icc.exists_bound_of_continuousOn hΘcont
  set Cθ : ℝ := max Cθ0 0 with hCθdef
  have hCθnn : 0 ≤ Cθ := le_max_right _ _
  have hCθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖expJet2Rhs g gi hC p v Φ h k t‖ ≤ Cθ :=
    fun t ht => (hCθ0 t ht).trans (le_max_left _ _)
  -- the affine vector field `F₂ t Q = DF(Y_v t)(Q) + Θ^{hk}(t)`.
  set F₂ : ℝ → (Point n × Point n) → (Point n × Point n) :=
    fun t Q => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) Q
      + expJet2Rhs g gi hC p v Φ h k t with hF₂
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
  have hpl : IsPicardLindelof F₂
      (tmin := t₀) (tmax := t₀ + T) ⟨t₀, ⟨le_refl t₀, by linarith⟩⟩
      x₀ Ann 0 Lnn Knn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in `Q` with constant `KdF` (source drops out).
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro M _ N _
      simp only [dist_eq_norm, hKnn]
      have hsub : F₂ t M - F₂ t N
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (M - N) := by
        simp only [hF₂, map_sub]; abel
      rw [hsub]
      calc ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (M - N)‖
          ≤ ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ * ‖M - N‖ :=
            (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).le_opNorm _
        _ ≤ KdF * ‖M - N‖ := mul_le_mul_of_nonneg_right (hKdF t htIcc) (norm_nonneg _)
    · -- continuity in `t` for fixed `Q`.
      intro x _
      have h1 : ContinuousOn
          (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x)
          (Set.Icc (0 : ℝ) 1) := hDFtube.clm_apply continuousOn_const
      exact ((h1.add hΘcont).mono hIccsub)
    · -- uniform bound `‖F₂ t x‖ ≤ L` on `closedBall(x₀, a)`.
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
      show ‖F₂ t x‖ ≤ Lval
      calc ‖F₂ t x‖
          = ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x
              + expJet2Rhs g gi hC p v Φ h k t‖ := by rw [hF₂]
        _ ≤ ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x‖
              + ‖expJet2Rhs g gi hC p v Φ h k t‖ := norm_add_le _ _
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
  obtain ⟨Q, hQ0, hQd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨Q, hQ0, fun t ht => ?_⟩
  have hd := hQd t ht
  simpa only [hF₂] using hd

/-- **Continuity of the Jet₂ inhomogeneous field** `s ↦ DF(Y_v s)(Q s) + Θ^{hk}(s)` on any
    `A ⊆ [0,1]` where `Q` is continuous: `DF(Y_v ·)` is continuous on `[0,1]` (tube continuity ∘
    `DF` C^∞), `Q` continuous, so `DF(Y_v ·)(Q ·)` continuous (`ContinuousOn.clm_apply`), and the
    source `Θ^{hk}` is continuous (`expJet2Rhs_continuousOn`). -/
theorem expJet2Field_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (h k : Point n)
    {A : Set ℝ} (hA : A ⊆ Set.Icc (0 : ℝ) 1)
    {Q : ℝ → (Point n × Point n)} (hQ : ContinuousOn Q A) :
    ContinuousOn (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q s)
      + expJet2Rhs g gi hC p v Φ h k s) A := by
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hDFtube : ContinuousOn
      (fun s => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) A :=
    (hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)).mono hA
  have h1 : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q s)) A :=
    hDFtube.clm_apply hQ
  have h2 : ContinuousOn (fun s => expJet2Rhs g gi hC p v Φ h k s) A :=
    (expJet2Rhs_continuousOn g gi hC p v hv Φ hΦcont h k).mono hA
  exact h1.add h2

set_option maxHeartbeats 1000000 in
/-- **EXP-JET3b-[0,1] — the shifted Jet₂ solver in INTEGRAL form (the gluing brick).**
    Same hypotheses as `expJet2Fund_shifted`, additionally packaging (i) `Q t₀ = x₀`, (ii) continuity
    on `[t₀, t₀+T]`, (iii) the differential law, and — the piece the `[0,1]` concatenation consumes —
    (iv) the LOCAL INTEGRAL EQUATION `Q(t) = x₀ + ∫_{t₀}^t (DF(Y_v s)(Q s) + Θ^{hk}(s)) ds`, from
    (iii) by FTC-2 (`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, integrand continuous
    by `expJet2Field_continuousOn`).

    Because the source `Θ^{hk}` is GLOBAL (not scaled by a propagator), the `[0,1]` concatenation glues
    these directly by ENDPOINT VALUE (`x₀ := Q_j(τ_j)`) — no right-composition needed, unlike the
    operator fundamental solution.

    HONEST: still ONE subinterval; it does NOT yet reach `Q^{hk}(1)`, NOT `∂_v Φ_v = Q`, NOT
    `ContDiff¹ (fderiv exp_p)`, NOT numerical-G. -/
theorem expJet2Fund_shifted_integral (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (h k : Point n)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (t₀ T : ℝ) (ht₀ : 0 ≤ t₀) (hT : 0 < T) (hsum : t₀ + T ≤ 1) (hstep : 2 * KdF * T ≤ 1)
    (x₀ : Point n × Point n) :
    ∃ Q : ℝ → (Point n × Point n),
      Q t₀ = x₀ ∧
      ContinuousOn Q (Set.Icc t₀ (t₀ + T)) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + T),
        HasDerivWithinAt Q
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q t)
             + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc t₀ (t₀ + T)) t) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + T),
        Q t = x₀ + ∫ s in t₀..t,
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q s)
             + expJet2Rhs g gi hC p v Φ h k s)) := by
  obtain ⟨Q, hQ0, hQd⟩ :=
    expJet2Fund_shifted g gi hC p v Φ hv hΦcont h k KdF hKdF0 hKdF t₀ T ht₀ hT hsum hstep x₀
  have hIccsub : Set.Icc t₀ (t₀ + T) ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc ht₀ hsum
  have hQcont : ContinuousOn Q (Set.Icc t₀ (t₀ + T)) := fun s hs => (hQd s hs).continuousWithinAt
  have hintegrand : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q s)
        + expJet2Rhs g gi hC p v Φ h k s) (Set.Icc t₀ (t₀ + T)) :=
    expJet2Field_continuousOn g gi hC p v hv Φ hΦcont h k hIccsub hQcont
  refine ⟨Q, hQ0, hQcont, hQd, fun t ht => ?_⟩
  have hab : t₀ ≤ t := ht.1
  have hsubt : Set.Icc t₀ t ⊆ Set.Icc t₀ (t₀ + T) := Set.Icc_subset_Icc_right ht.2
  have hcont : ContinuousOn Q (Set.Icc t₀ t) := hQcont.mono hsubt
  have hderiv : ∀ x ∈ Set.Ioo t₀ t,
      HasDerivWithinAt Q
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x)) (Q x)
           + expJet2Rhs g gi hC p v Φ h k x) (Set.Ioi x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc t₀ (t₀ + T) := hsubt ⟨hx.1.le, hx.2.le⟩
    have hnhds : Set.Icc t₀ (t₀ + T) ∈ nhds x :=
      Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 ht.2)
    exact ((hQd x hxIcc).hasDerivAt hnhds).hasDerivWithinAt
  have hint : IntervalIntegrable
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q s)
        + expJet2Rhs g gi hC p v Φ h k s) MeasureTheory.volume t₀ t :=
    (hintegrand.mono hsubt).intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint
  rw [hQ0] at hftc
  rw [hftc]; abel

set_option maxHeartbeats 2000000 in
/-- **The partition induction (endpoint-matching concatenation).**  For a `[0,1]`-uniform Jacobi bound
    `KdF` and a step count `N` with `2·KdF·(1/N) ≤ 1`, there is, for every `j ≤ N`, a vector-valued
    curve `Q` on `[0, j/N]` with `Q 0 = 0`, continuous, obeying the GLOBAL integral equation
    `Q t = 0 + ∫₀ᵗ (DF(Y_v s)(Q s) + Θ^{hk}(s)) ds`.  Proved by induction on `j`: the `[0,(j+1)/N]`
    curve glues `Q_j` and the shifted solver `U` on `[j/N,(j+1)/N]` started at the ENDPOINT VALUE
    `Q_j(j/N)`.  Since the source is global, the global integral equation pastes directly
    (`integral_add_adjacent_intervals` + `integral_congr`), with no right-composition. -/
private theorem expJet2Fund_glue (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (h k : Point n)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (N : ℕ) (hN0 : 0 < N) (hstep : 2 * KdF * (1 / (N : ℝ)) ≤ 1) :
    ∀ j : ℕ, j ≤ N →
      ∃ Q : ℝ → (Point n × Point n),
        Q 0 = 0 ∧
        ContinuousOn Q (Set.Icc (0 : ℝ) ((j : ℝ) / (N : ℝ))) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) ((j : ℝ) / (N : ℝ)),
          Q t = (0 : Point n × Point n) + ∫ s in (0 : ℝ)..t,
            ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q s)
               + expJet2Rhs g gi hC p v Φ h k s)) := by
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
  | succ m ih =>
    intro hk
    obtain ⟨Qj, hQj0, hQjcont, hQjint⟩ := ih (Nat.le_of_succ_le hk)
    have hτnn : 0 ≤ (m : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg m) hNpos.le
    have hInpos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hsucc : ((m + 1 : ℕ) : ℝ) / (N : ℝ) = (m : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
      push_cast; ring
    have hτm1le1 : (m : ℝ) / (N : ℝ) + 1 / (N : ℝ) ≤ 1 :=
      hsucc ▸ (by rw [div_le_one hNpos]; exact_mod_cast hk)
    obtain ⟨U, hU0, hUcont, hUderiv, hUint⟩ :=
      expJet2Fund_shifted_integral g gi hC p v Φ hv hΦcont h k KdF hKdF0 hKdF
        ((m : ℝ) / (N : ℝ)) (1 / (N : ℝ)) hτnn hInpos hτm1le1 hstep (Qj ((m : ℝ) / (N : ℝ)))
    set Q' : ℝ → (Point n × Point n) :=
      fun t => if t ≤ (m : ℝ) / (N : ℝ) then Qj t else U t with hQ'def
    have hQ'_lo : ∀ s, s ≤ (m : ℝ) / (N : ℝ) → Q' s = Qj s := by
      intro s hs; rw [hQ'def]; exact if_pos hs
    have hQ'_hi : ∀ s, ¬ (s ≤ (m : ℝ) / (N : ℝ)) → Q' s = U s := by
      intro s hs; rw [hQ'def]; exact if_neg hs
    -- EqOn on the two closed pieces (junction value matches: `Qj(τ_m) = x₀ = U(τ_m)`).
    have hEqLo : Set.EqOn Q' Qj (Set.Icc (0 : ℝ) ((m : ℝ) / (N : ℝ))) :=
      fun s hs => hQ'_lo s hs.2
    have hEqHi : Set.EqOn Q' U
        (Set.Icc ((m : ℝ) / (N : ℝ)) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ))) := by
      intro s hs
      by_cases hsle : s ≤ (m : ℝ) / (N : ℝ)
      · have hseq : s = (m : ℝ) / (N : ℝ) := le_antisymm hsle hs.1
        rw [hQ'_lo s hsle, hseq, hU0]
      · rw [hQ'_hi s hsle]
    -- continuity of the glued curve on [0, (m+1)/N].
    have hΦ'cont : ContinuousOn Q' (Set.Icc (0 : ℝ) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ))) := by
      have hunion : Set.Icc (0 : ℝ) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ))
          = Set.Icc (0 : ℝ) ((m : ℝ) / (N : ℝ))
            ∪ Set.Icc ((m : ℝ) / (N : ℝ)) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
        (Set.Icc_union_Icc_eq_Icc hτnn (by linarith)).symm
      rw [hunion]
      exact (hQjcont.congr hEqLo).union_of_isClosed (hUcont.congr hEqHi)
        isClosed_Icc isClosed_Icc
    -- integrand continuity for interval integrability.
    have hcontψ' : ContinuousOn
        (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
          + expJet2Rhs g gi hC p v Φ h k s)
        (Set.Icc (0 : ℝ) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ))) :=
      expJet2Field_continuousOn g gi hC p v hv Φ hΦcont h k
        (Set.Icc_subset_Icc_right hτm1le1) hΦ'cont
    rw [hsucc]
    refine ⟨Q', ?_, hΦ'cont, ?_⟩
    · rw [hQ'_lo 0 hτnn]; exact hQj0
    · intro t ht
      by_cases htle : t ≤ (m : ℝ) / (N : ℝ)
      · -- t in [0, τm]: the curve is Qj there.
        rw [hQ'_lo t htle]
        have hcong : (∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
                 + expJet2Rhs g gi hC p v Φ h k s))
            = ∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Qj s)
                 + expJet2Rhs g gi hC p v Φ h k s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le ht.1] at hs
          show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
              + expJet2Rhs g gi hC p v Φ h k s
            = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Qj s)
              + expJet2Rhs g gi hC p v Φ h k s
          rw [hQ'_lo s (le_trans hs.2 htle)]
        rw [hcong]
        exact hQjint t ⟨ht.1, htle⟩
      · -- t in (τm, τm + 1/N]: the curve is U there.
        have htlt : (m : ℝ) / (N : ℝ) < t := not_le.mp htle
        have htmem : t ∈ Set.Icc ((m : ℝ) / (N : ℝ)) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
          ⟨htlt.le, ht.2⟩
        rw [hQ'_hi t htle]
        have hII1 : IntervalIntegrable
            (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
              + expJet2Rhs g gi hC p v Φ h k s) MeasureTheory.volume 0 ((m : ℝ) / (N : ℝ)) :=
          (hcontψ'.mono (Set.Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hτnn
        have hII2 : IntervalIntegrable
            (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
              + expJet2Rhs g gi hC p v Φ h k s) MeasureTheory.volume ((m : ℝ) / (N : ℝ)) t :=
          (hcontψ'.mono (Set.Icc_subset_Icc hτnn ht.2)).intervalIntegrable_of_Icc htlt.le
        have hsplit : (∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
                 + expJet2Rhs g gi hC p v Φ h k s))
            = (∫ s in (0 : ℝ)..((m : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
                   + expJet2Rhs g gi hC p v Φ h k s))
              + ∫ s in ((m : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
                   + expJet2Rhs g gi hC p v Φ h k s) :=
          (intervalIntegral.integral_add_adjacent_intervals hII1 hII2).symm
        -- first piece = Qj(τm) - 0.
        have hI1 : (∫ s in (0 : ℝ)..((m : ℝ) / (N : ℝ)),
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
                 + expJet2Rhs g gi hC p v Φ h k s))
            = Qj ((m : ℝ) / (N : ℝ)) - (0 : Point n × Point n) := by
          have hc : (∫ s in (0 : ℝ)..((m : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
                   + expJet2Rhs g gi hC p v Φ h k s))
              = ∫ s in (0 : ℝ)..((m : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Qj s)
                   + expJet2Rhs g gi hC p v Φ h k s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le hτnn] at hs
            show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
                + expJet2Rhs g gi hC p v Φ h k s
              = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Qj s)
                + expJet2Rhs g gi hC p v Φ h k s
            rw [hQ'_lo s hs.2]
          rw [hc, hQjint ((m : ℝ) / (N : ℝ)) ⟨hτnn, le_refl _⟩]; abel
        -- second piece = U(t) - Qj(τm).
        have hI2 : (∫ s in ((m : ℝ) / (N : ℝ))..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
                 + expJet2Rhs g gi hC p v Φ h k s))
            = U t - Qj ((m : ℝ) / (N : ℝ)) := by
          have hc : (∫ s in ((m : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
                   + expJet2Rhs g gi hC p v Φ h k s))
              = ∫ s in ((m : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (U s)
                   + expJet2Rhs g gi hC p v Φ h k s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le htlt.le] at hs
            have hsmem : s ∈ Set.Icc ((m : ℝ) / (N : ℝ)) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
              ⟨hs.1, le_trans hs.2 ht.2⟩
            show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q' s)
                + expJet2Rhs g gi hC p v Φ h k s
              = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (U s)
                + expJet2Rhs g gi hC p v Φ h k s
            rw [hEqHi hsmem]
          rw [hc, hUint t htmem]; abel
        rw [hsplit, hI1, hI2]; abel

set_option maxHeartbeats 2000000 in
/-- **EXP-JET3b-[0,1] (capstone) — the `[0,1]` Jet₂ second-variation fundamental solution `Q^{hk}`.**
    For `‖v‖ ≤ expRho` and `Φ` continuous on `[0,1]`, there is a vector-valued curve
    `Q : ℝ → Point n × Point n` with `Q 0 = 0`, continuous on `[0,1]`, obeying the GLOBAL integral
    equation `Q t = 0 + ∫₀ᵗ (DF(Y_v s)(Q s) + Θ^{hk}(s)) ds`, and — by FTC-1 — the inhomogeneous
    Jet₂ derivative law `HasDerivWithinAt Q (DF(Y_v t)(Q t) + Θ^{hk}(t)) (Icc 0 1) t` for every
    `t ∈ [0,1]`.  Built by concatenating `N ≥ 2(KdF+1)` shifted solvers (`expJet2Fund_glue`).

    HONEST: the `[0,1]` inhomogeneous Jet₂ solution `Q^{hk}` (the second-variation transport of the
    fixed vectors `h, k` through `D²F`) — the multi-week PL-tower analog of `expJetFund` for Rung 2.
    It does NOT yet give the parameter-residual Grönwall `∂_v Φ_v = Q`, NOT `ContDiff¹ (fderiv exp_p)`,
    NOT `ContDiff² exp_p`, NOT the pullback metric, NOT numerical-G. -/
theorem expJet2Fund (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (h k : Point n) :
    ∃ Q : ℝ → (Point n × Point n),
      Q 0 = 0 ∧
      ContinuousOn Q (Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Q t = (0 : Point n × Point n) + ∫ s in (0 : ℝ)..t,
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q s)
             + expJet2Rhs g gi hC p v Φ h k s)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt Q
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q t)
             + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) t) := by
  obtain ⟨KdF, hKdF0, hKdF⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (KdF + 1))
  have hpos : (0 : ℝ) < 2 * (KdF + 1) := by linarith
  have hNRpos : (0 : ℝ) < (N : ℝ) := hpos.trans_le hN
  have hN0 : 0 < N := by exact_mod_cast hNRpos
  have hstep : 2 * KdF * (1 / (N : ℝ)) ≤ 1 := by
    have h2 : 2 * KdF * (1 / (N : ℝ)) = (2 * KdF) / (N : ℝ) := by ring
    rw [h2, div_le_one hNRpos]; linarith [hN]
  obtain ⟨Q, hQ0, hQcont, hQint⟩ :=
    expJet2Fund_glue g gi hC p v Φ hv hΦcont h k KdF hKdF0 hKdF N hN0 hstep N le_rfl
  have hNN : (N : ℝ) / (N : ℝ) = 1 := div_self hNRpos.ne'
  rw [hNN] at hQcont hQint
  refine ⟨Q, hQ0, hQcont, hQint, ?_⟩
  have hψcont : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q s)
        + expJet2Rhs g gi hC p v Φ h k s) (Set.Icc (0 : ℝ) 1) :=
    expJet2Field_continuousOn g gi hC p v hv Φ hΦcont h k (subset_refl _) hQcont
  intro t ht
  have hII : IntervalIntegrable
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Q s)
        + expJet2Rhs g gi hC p v Φ h k s) MeasureTheory.volume 0 t :=
    (hψcont.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  haveI : Fact (t ∈ Set.Icc (0 : ℝ) 1) := ⟨ht⟩
  have hmeas := hψcont.stronglyMeasurableAtFilter_nhdsWithin (μ := MeasureTheory.volume)
    measurableSet_Icc t
  have hFTC := intervalIntegral.integral_hasDerivWithinAt_right (s := Set.Icc (0 : ℝ) 1)
    hII hmeas (hψcont t ht)
  have hconst := hFTC.const_add (0 : Point n × Point n)
  exact hconst.congr (fun s hs => hQint s hs) (hQint t ht)

/-! ### Sub-brick 3c — the parameter-residual estimate (the analytic heart of Rung 2)

The map `v ↦ fderiv exp_p v = π ∘ Φ_v(1) ∘ ι` is differentiated in `v`.  For fixed direction `h`
the first variation is `P^h_v(t) = Φ_v(t)(ι h)`; its parameter-derivative in direction `k` is the
second variation `Q^{hk}_v(t)` built in `expJet2Fund`.  The Fréchet-derivative little-o reduces to
the **parameter residual** `S(t) := Φ_{v+k}(t)(ι h) − Φ_v(t)(ι h) − Q^{hk}_v(t)` being `o(‖k‖)`.

This sub-brick lands, `[AF]` and unconditionally green:
* `expJet2_residual_hasDerivWithinAt` — the **residual ODE** (the Jet₂ analog of Rung 1's residual
  identity): `S(0) = 0` and `S'(t) = DF(Y_v t)(S t) + r(t)` on `[0,1]`, where the inhomogeneous
  remainder is `r(t) = [DF(Y_{v+k} t) − DF(Y_v t)](Φ_{v+k}(t)(ι h)) − Θ^{hk}(t)` with
  `Θ^{hk} = expJet2Rhs …` the 3a source.
* `gronwall_vec_residual` — a small-context **inhomogeneous vector Grönwall** on `[0,1]`:
  `S(0) = 0`, `S' = A(S) + r`, `‖A‖ ≤ K`, `‖r‖ ≤ ρ` ⟹ `‖S(1)‖ ≤ ρ·e^{K}`.
* `expJet2_residual_bound` — the two combined: **`‖S(1)‖ ≤ ρ·e^{Kstar}`** for any `[0,1]`-bound
  `ρ` on `‖r(t)‖` and Jacobi bound `Kstar` on `‖DF(Y_v t)‖`.  This is the residual estimate (A) of
  the plan **reduced to the single obligation `‖r(t)‖ ≤ ρ`** — with `ρ = C·‖k‖²` it would close the
  Fréchet little-o.

## Honest firewall — the exact remaining obstruction

`expJet2_residual_bound` gives the full residual estimate `‖S(1)‖ ≤ ρ·e^{Kstar}` CONDITIONAL on the
**quadratic remainder bound** `‖r(t)‖ ≤ C·‖k‖²` on `[0,1]`.  That bound is **NOT discharged here** and
is the wall.  Its leading terms cancel (by symmetry of `D²F`, `Θ^{hk}` equals the linear-in-`k` part
of the `DF`-difference), leaving a genuine `O(‖k‖²)` remainder, but proving it needs three ingredients
not yet in the codebase:
1. a **second-order Taylor remainder for `DF`**, `‖(DF(Y_{v+k}) − DF(Y_v)) − D²F(Y_v)(ΔY)‖ ≤ C‖ΔY‖²`;
2. **second-order tube accuracy** `‖ (Y_{v+k}−Y_v)(t) − Φ_v(t)(ι k) ‖ ≤ C‖k‖²` (a nested inhomogeneous
   Grönwall requiring the geodesic field's own `C²` Taylor remainder);
3. the **`[0,1]`-uniform first-variation Lipschitz** `‖Φ_{v+k}(t)(ι h) − Φ_v(t)(ι h)‖ ≤ C‖k‖`
   (`expFund_two_pt_diff` currently concludes only at `t = 1`) and **symmetry of `D²F`**
   (`second_derivative_symmetric`).

These are the multi-week analytic bulk; with them, `‖r‖ ≤ C‖k‖²` feeds `expJet2_residual_bound` to
give `HasFDerivAt (v ↦ Φ_v(1)(ι h)) (k ↦ Q^{hk}_v(1)) v` (plan step (B)); a second parameter-Grönwall
for `v ↦ Q^{hk}_v(1)` gives continuity (C); and (B)+(C) feed
`expMap_contDiffOn_two_of_fderiv_contDiffOn_one` to give `ContDiff² exp_p` unconditionally (D).

⚠ This does NOT reach `ContDiff²` (the remainder bound above is open), NOT `ContDiff³`, NOT `κ = 1/6`,
NOT a heat-kernel parametrix, NOT `a₁ = R/6`, NOT numerical-`G`, and NOT the conjecture / QG. -/

/-- **Small-context inhomogeneous vector Grönwall on `[0,1]`.**  If `S : ℝ → E` has `S 0 = 0` and
    right derivative `A t (S t) + r t` within `[0,1]` at each `t ∈ [0,1]`, with `‖A t‖ ≤ K` and
    `‖r t‖ ≤ ρ` there, then `‖S 1‖ ≤ ρ · e^{K}`.  Wraps `gronwall_Icc01_all` (the norm bound
    `‖A t (S t) + r t‖ ≤ K·‖S t‖ + ρ` via `ContinuousLinearMap.le_opNorm`) and closes with
    `gronwallBound_zero_le_exp`.  Abstract in `E` (tiny context) — the Jet₂ analog of the operator
    Grönwall inside `expFund_two_pt_diff`. -/
theorem gronwall_vec_residual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S r : ℝ → E) (A : ℝ → (E →L[ℝ] E)) (K ρ : ℝ) (hK0 : 0 ≤ K) (hρ0 : 0 ≤ ρ)
    (hS0 : S 0 = 0)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt S (A t (S t) + r t) (Set.Icc (0 : ℝ) 1) t)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A t‖ ≤ K)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖r t‖ ≤ ρ) :
    ‖S 1‖ ≤ ρ * Real.exp K := by
  have hall := gronwall_Icc01_all S (fun t => A t (S t) + r t) 0 K ρ hderiv
    (by rw [hS0]; simp)
    (fun t ht => by
      calc ‖A t (S t) + r t‖ ≤ ‖A t (S t)‖ + ‖r t‖ := norm_add_le _ _
        _ ≤ K * ‖S t‖ + ρ := by
            refine add_le_add ?_ (hr t ht)
            calc ‖A t (S t)‖ ≤ ‖A t‖ * ‖S t‖ := (A t).le_opNorm _
              _ ≤ K * ‖S t‖ := mul_le_mul_of_nonneg_right (hA t ht) (norm_nonneg _))
  have h1 : ‖S 1‖ ≤ gronwallBound 0 K ρ 1 := hall 1 (by norm_num [Set.mem_Icc])
  exact h1.trans (gronwallBound_zero_le_exp K ρ 1 hK0 hρ0 (by norm_num) le_rfl)

set_option maxHeartbeats 1000000 in
/-- **The Jet₂ residual ODE (residual identity).**  With `Φ` the fundamental solution for parameter
    `v` and `Φ'` for the perturbed parameter `w` (`= v + k`), and `Q` the second-variation witness of
    `expJet2Fund` (whose derivative law is `Q'(t) = DF(Y_v t)(Q t) + Θ^{hk}(t)`), the parameter
    residual `S(t) = Φ'(t)(ι h) − Φ(t)(ι h) − Q(t)` obeys, on `[0,1]`,
    `S'(t) = DF(Y_v t)(S t) + ([DF(Y_w t) − DF(Y_v t)](Φ'(t)(ι h)) − Θ^{hk}(t))`.

    Proof: `P^h_·(t) = Φ_·(t)(ι h)` solves `(P^h_·)' = DF(Y_· t)(P^h_·)` (differentiate the operator
    ODE `Φ_·' = Ψ_·(Φ_·)` applied at the fixed vector `ι h`, `HasDerivWithinAt.clm_apply` against a
    constant); subtracting the three curves and using linearity of `DF(Y_v t)` (`map_sub`) plus
    `ContinuousLinearMap.sub_apply` rearranges the difference into the `DF(Y_v t)(S) + r` form. -/
theorem expJet2_residual_hasDerivWithinAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Q : ℝ → (Point n × Point n)) (h k : Point n)
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p w t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
    (hQd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Q
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q t)
           + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) t)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => Φ' s (expJetIota h) - Φ s (expJetIota h) - Q s)
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
          (Φ' t (expJetIota h) - Φ t (expJetIota h) - Q t)
        + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
             - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ' t (expJetIota h))
           - expJet2Rhs g gi hC p v Φ h k t))
      (Set.Icc (0 : ℝ) 1) t := by
  -- first variation `P^h_w(t) = Φ'(t)(ι h)` solves `(P^h_w)' = DF(Y_w t)(P^h_w)`.
  have hP' : HasDerivWithinAt (fun s => Φ' s (expJetIota h))
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Φ' t (expJetIota h)))
      (Set.Icc (0 : ℝ) 1) t := by
    have hcl := (hΦ'd t ht).clm_apply
      (hasDerivWithinAt_const (x := t) (s := Set.Icc (0 : ℝ) 1) (c := expJetIota (n := n) h))
    simpa only [expJetPsi_apply, ContinuousLinearMap.comp_apply, map_zero, add_zero] using hcl
  -- first variation `P^h_v(t) = Φ(t)(ι h)` solves `(P^h_v)' = DF(Y_v t)(P^h_v)`.
  have hP : HasDerivWithinAt (fun s => Φ s (expJetIota h))
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ t (expJetIota h)))
      (Set.Icc (0 : ℝ) 1) t := by
    have hcl := (hΦd t ht).clm_apply
      (hasDerivWithinAt_const (x := t) (s := Set.Icc (0 : ℝ) 1) (c := expJetIota (n := n) h))
    simpa only [expJetPsi_apply, ContinuousLinearMap.comp_apply, map_zero, add_zero] using hcl
  -- the natural difference derivative.
  have hcomb := (hP'.sub hP).sub (hQd t ht)
  -- rearrange the target derivative into the natural one via linearity.
  have heq :
      (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
          (Φ' t (expJetIota h) - Φ t (expJetIota h) - Q t)
        + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
             - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ' t (expJetIota h))
           - expJet2Rhs g gi hC p v Φ h k t)
      = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Φ' t (expJetIota h))
          - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ t (expJetIota h))
          - ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q t)
             + expJet2Rhs g gi hC p v Φ h k t) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  exact hcomb

set_option maxHeartbeats 1000000 in
/-- **The Jet₂ parameter-residual estimate (A), reduced to the remainder bound.**  With the
    fundamental-solution and second-variation data of `expJet2_residual_hasDerivWithinAt` and the
    initial conditions `Φ 0 = Φ' 0 = 1`, `Q 0 = 0`, given a `[0,1]`-bound `Kstar` on `‖DF(Y_v t)‖`
    (`expJet_fderiv_tube_bddAbove`) and a `[0,1]`-bound `ρ` on the remainder
    `‖[DF(Y_w t) − DF(Y_v t)](Φ'(t)(ι h)) − Θ^{hk}(t)‖`, one has
    `‖Φ'(1)(ι h) − Φ(1)(ι h) − Q(1)‖ ≤ ρ · e^{Kstar}`.

    Feeds the residual ODE (`expJet2_residual_hasDerivWithinAt`) into the vector Grönwall
    (`gronwall_vec_residual`).  This is the residual estimate (A) of the Rung-2 plan **reduced to the
    single obligation `‖r(t)‖ ≤ ρ`**; with `ρ = C·‖k‖²` (the OPEN quadratic remainder bound — see the
    module firewall) it closes the Fréchet little-o for `v ↦ Φ_v(1)(ι h)`. -/
theorem expJet2_residual_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Q : ℝ → (Point n × Point n)) (h k : Point n)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hQ0 : Q 0 = 0)
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p w t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
    (hQd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Q
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q t)
           + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) t)
    (Kstar ρ : ℝ) (hKstar0 : 0 ≤ Kstar) (hρ0 : 0 ≤ ρ)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ' t (expJetIota h))
         - expJet2Rhs g gi hC p v Φ h k t‖ ≤ ρ) :
    ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Q 1‖ ≤ ρ * Real.exp Kstar := by
  refine gronwall_vec_residual (fun s => Φ' s (expJetIota h) - Φ s (expJetIota h) - Q s)
    (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
        - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ' t (expJetIota h))
      - expJet2Rhs g gi hC p v Φ h k t)
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) Kstar ρ hKstar0 hρ0
    ?_ ?_ hKstar hr
  · -- initial condition `S 0 = 0`.
    simp only [hΦ0, hΦ'0, ContinuousLinearMap.id_apply, hQ0, sub_self]
  · -- the residual ODE.
    intro t ht
    exact expJet2_residual_hasDerivWithinAt g gi hC p v w Φ Φ' Q h k hΦd hΦ'd hQd t ht

/-! ### Rung-2 remainder-bound ingredient (iii): `D²F` symmetry and the `[0,1]`-uniform Lipschitz -/

/-- **The second Fréchet derivative `D²F = fderiv (fderiv F)` of the geodesic field is symmetric.**
    `geodesicField g gi` is `C^∞` (`contDiff_geodesicField`), hence `C²`, so by Mathlib's
    `ContDiffAt.isSymmSndFDerivAt` its second derivative is a symmetric bilinear map:
    `D²F(x)(a)(b) = D²F(x)(b)(a)`.  A supporting ingredient of the Rung-2 quadratic remainder bound
    `‖r(t)‖ ≤ C‖k‖²` (`THE_EXP_JETS_PLAN.md`); the mixed second partials of `F` commute. -/
theorem fderiv2_geodesicField_symm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x) a b
      = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x) b a :=
  ((contDiff_geodesicField g gi hC).contDiffAt.isSymmSndFDerivAt le_top) a b

set_option maxHeartbeats 2000000 in
/-- **The `[0,1]`-UNIFORM first-variation Lipschitz bound.**  Same hypotheses as
    `expFund_two_pt_diff` (which concludes only at `t = 1`), but the Lipschitz-in-`v` bound holds
    UNIFORMLY for every `t ∈ [0,1]` with the SAME constant.  Its proof runs the identical difference
    Grönwall (`gronwall_Icc01_all`) giving `‖Φv t − Φw t‖ ≤ gronwallBound 0 Kstar b t` on all of
    `[0,1]`, then bounds `gronwallBound 0 Kstar b t ≤ b·e^{Kstar}` uniformly in `t ≤ 1`
    (`gronwallBound_zero_le_exp`) — the `t = 1` constant is an upper bound for every `t ≤ 1`.

    Supporting ingredient of the Rung-2 remainder bound `‖r(t)‖ ≤ C‖k‖²` (`THE_EXP_JETS_PLAN.md`):
    callers need the first-variation Lipschitz control on the whole time interval, not just the
    endpoint. -/
theorem expFund_two_pt_diff_Icc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n) (Kf Ldf : NNReal) (Kstar : ℝ) (hKstar0 : 0 ≤ Kstar)
    (hLipF : LipschitzOnWith Kf (geodesicField g gi)
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipDF : LipschitzOnWith Ldf (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)‖ ≤ Kstar)
    (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Φv Φw : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦv0 : Φv 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦw0 : Φw 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φv (expJetPsi g gi hC p v t (Φv t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φw (expJetPsi g gi hC p w t (Φw t)) (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φv t - Φw t‖
      ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ := by
  have hC₀ := expConst_nonneg g gi hC p
  set Rb : ℝ := expConst g gi hC p * expRho g gi hC p with hRbdef
  set S : Set (Point n × Point n) := Metric.closedBall ((p, 0) : Point n × Point n) Rb with hSdef
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  obtain ⟨hY0w, hYdw, hconfw⟩ := expTube_spec g gi hC p w hw
  have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- both tubes lie in the ball `S` on `[0,1]`.
  have hSv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈ S := by
    intro t ht; rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖expTube g gi hC p v t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖v‖ := hconfv t ht
      _ ≤ Rb := by rw [hRbdef]; exact mul_le_mul_of_nonneg_left hv hC₀
  have hSw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p w t ∈ S := by
    intro t ht; rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖expTube g gi hC p w t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖w‖ := hconfw t ht
      _ ≤ Rb := by rw [hRbdef]; exact mul_le_mul_of_nonneg_left hw hC₀
  -- single-solution norm bound `‖Φw t‖ ≤ e^{Kstar}`.
  have hΦwbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φw t‖ ≤ Real.exp Kstar := by
    have hall := gronwall_Icc01_all Φw (fun t => expJetPsi g gi hC p w t (Φw t)) 1 Kstar 0
      hΦwd (by rw [hΦw0]; exact ContinuousLinearMap.norm_id_le)
      (fun t ht => by
        rw [add_zero]
        exact (expJetPsi_norm_le g gi hC p w t (Φw t)).trans
          (mul_le_mul_of_nonneg_right (hKstarw t ht) (norm_nonneg _)))
    intro t ht
    have h := hall t ht
    rw [gronwallBound_ε0, one_mul] at h
    refine h.trans (Real.exp_le_exp.mpr ?_)
    calc Kstar * t ≤ Kstar * 1 := mul_le_mul_of_nonneg_left ht.2 hKstar0
      _ = Kstar := mul_one _
  -- two-point tube separation `‖Y_v t − Y_w t‖ ≤ ‖v−w‖·e^{Kf}`.
  have hdist0 : dist (expTube g gi hC p v 0) (expTube g gi hC p w 0) = ‖v - w‖ := by
    rw [hY0v, hY0w, dist_eq_norm, Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg _)]
  have htwopoint := geodesic_twopoint_gronwall g gi (S := S) (K := Kf) hLipF
    (fun t ht => hYdv t (hIcc_Ioo t ht)) (fun t ht => hYdw t (hIcc_Ioo t ht)) hSv hSw
  have hYvw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p v t - expTube g gi hC p w t‖ ≤ ‖v - w‖ * Real.exp (Kf : ℝ) := by
    intro t ht
    have h := htwopoint t ht
    rw [hdist0, dist_eq_norm] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  -- Lipschitz of `DF` in the space variable ⟹ two-point `DF`-difference bound.
  have hDFvw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)‖
        ≤ (Ldf : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipDF.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  -- the inhomogeneous constant `b` and the difference Grönwall.
  set b : ℝ := (Ldf : ℝ) * ‖v - w‖ * Real.exp (Kf : ℝ) * Real.exp Kstar with hbdef
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hEall := gronwall_Icc01_all (fun t => Φv t - Φw t)
    (fun t => expJetPsi g gi hC p v t (Φv t) - expJetPsi g gi hC p w t (Φw t))
    0 Kstar b
    (fun t ht => (hΦvd t ht).sub (hΦwd t ht))
    (by simp [hΦv0, hΦw0])
    (fun t ht => by
      show ‖expJetPsi g gi hC p v t (Φv t) - expJetPsi g gi hC p w t (Φw t)‖
          ≤ Kstar * ‖Φv t - Φw t‖ + b
      rw [expJetPsi_apply, expJetPsi_apply]
      refine opFieldDiff_bound (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
        (fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) _ _ (hKstarv t ht) ?_
      rw [hbdef]
      refine (mul_le_mul (hDFvw t ht) (hΦwbound t ht) (norm_nonneg _) (by positivity)).trans ?_
      exact le_of_eq (by ring))
  -- lift the per-`t` Grönwall bound to the uniform constant (monotone in `t ≤ 1`).
  intro t ht
  refine (hEall t ht).trans
    ((gronwallBound_zero_le_exp Kstar b t hKstar0 hb0 ht.1 ht.2).trans ?_)
  rw [hbdef]; exact le_of_eq (by ring)

/-! ### Sub-brick (i) — the `DF` second-order Taylor remainder is quadratic

Rung-2-capstone ingredient (i): on the confined tube ball, the first-order Taylor remainder of
`DF = fderiv F` about `x` is `O(‖y − x‖²)`.  Since `DF` is `C^∞` (`contDiff_fderiv_geodesicField`),
its Fréchet derivative is `D²F = fderiv (fderiv F)` (`hasFDerivAt_fderiv_geodesicField`), which is
Lipschitz on the (convex, compact) ball (`expJet_fderiv2_lipschitzOnWith`).  Applying the
fixed-linear-map mean-value inequality `Convex.norm_image_sub_le_of_norm_fderiv_le'` to `DF` on the
SEGMENT `[x, y]` (convex, `⊆ ball`), with the derivative-difference bound
`‖D²F z − D²F x‖ ≤ L·‖z − x‖ ≤ L·‖y − x‖` (Lipschitz `+` `norm_sub_le_of_mem_segment`), gives the
remainder estimate with constant `L·‖y − x‖`, i.e. the quadratic bound `L·‖y − x‖²`. -/

/-- **`DF` second-order Taylor remainder is quadratic on the confined tube ball.**
    With `L` a Lipschitz constant of `D²F = fderiv (fderiv F)` on the tube ball
    `closedBall (p,0) (expConst·expRho)` (from `expJet_fderiv2_lipschitzOnWith`), the first-order
    Taylor remainder of `DF = fderiv (geodesicField g gi)` about `x` is bounded by `L·‖y − x‖²`
    for `x, y` in that ball.  Ingredient (i) of the Rung-2 capstone quadratic remainder bound. -/
theorem geodesicField_DF_second_order_taylor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (L : ℝ) (hL0 : 0 ≤ L)
    (hLip : LipschitzOnWith L.toNNReal (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p,0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (x y : Point n × Point n)
    (hx : x ∈ Metric.closedBall ((p,0) : Point n × Point n)
      (expConst g gi hC p * expRho g gi hC p))
    (hy : y ∈ Metric.closedBall ((p,0) : Point n × Point n)
      (expConst g gi hC p * expRho g gi hC p)) :
    ‖fderiv ℝ (geodesicField g gi) y - fderiv ℝ (geodesicField g gi) x
        - (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x) (y - x)‖
      ≤ L * ‖y - x‖ ^ 2 := by
  -- The segment `[x, y]` is convex and sits inside the (convex) ball.
  have hseg : segment ℝ x y ⊆
      Metric.closedBall ((p,0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) :=
    (convex_closedBall _ _).segment_subset hx hy
  -- `DF` is differentiable everywhere (it is `C^∞`).
  have hdiff : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ (fderiv ℝ (geodesicField g gi)) z :=
    fun z _ => (hasFDerivAt_fderiv_geodesicField g gi hC z).differentiableAt
  -- Uniform bound on the derivative-difference over the segment: `‖D²F z − D²F x‖ ≤ L·‖y − x‖`.
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ L * ‖y - x‖ := by
    intro z hz
    have hd := hLip.dist_le_mul z (hseg hz) x hx
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal L hL0] at hd
    calc ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z
              - fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖
        ≤ L * ‖z - x‖ := hd
      _ ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hL0
  -- Mean-value inequality on the segment, fixed-linear-map (`φ = D²F x`) version.
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (f := fderiv ℝ (geodesicField g gi))
    (φ := fderiv ℝ (fderiv ℝ (geodesicField g gi)) x)
    (C := L * ‖y - x‖) hdiff hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  calc ‖fderiv ℝ (geodesicField g gi) y - fderiv ℝ (geodesicField g gi) x
          - (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x) (y - x)‖
      ≤ L * ‖y - x‖ * ‖y - x‖ := hmv
    _ = L * ‖y - x‖ ^ 2 := by ring

/-! ### Rung-2 remainder-bound ingredient (ii): 2nd-order tube accuracy

Two floor lemmas, direct mirrors one order down of the `D²F`/`DF` bricks above:
* `expJet_fderiv_lipschitzOnWith` — `DF = fderiv F` is Lipschitz on the confined tube ball (mirror
  of `expJet_fderiv2_lipschitzOnWith` with `contDiff_fderiv_geodesicField` in place of
  `contDiff_fderiv2_geodesicField`);
* `geodesicField_F_second_order_taylor` — `F = geodesicField`'s first-order Taylor remainder about
  `x` is `O(‖y − x‖²)` on the tube ball (mirror of `geodesicField_DF_second_order_taylor` with
  `F`/`DF` in place of `DF`/`D²F`). -/

/-- **`DF` is Lipschitz on the confined tube ball.**  The direct `DF` analog of
    `expJet_fderiv2_lipschitzOnWith` one order down.  `DF = fderiv (geodesicField g gi)` is `C^∞`
    (`contDiff_fderiv_geodesicField`), hence `C¹`, and the tube ball
    `Metric.closedBall (p,0) (expConst · expRho)` is compact and convex; a `C¹` map is Lipschitz on a
    compact convex set (`ContDiffOn.exists_lipschitzOnWith`).  Ingredient (ii) of the Rung-2 capstone:
    the `DF`-Lipschitz constant `M` that `geodesicField_F_second_order_taylor` consumes. -/
theorem expJet_fderiv_lipschitzOnWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ Ldf : NNReal, LipschitzOnWith Ldf (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) :=
  ((contDiff_fderiv_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)

/-- **`F` second-order Taylor remainder is quadratic on the confined tube ball.**
    With `M` a Lipschitz constant of `DF = fderiv (geodesicField g gi)` on the tube ball
    `closedBall (p,0) (expConst·expRho)` (from `expJet_fderiv_lipschitzOnWith`), the first-order
    Taylor remainder of `F = geodesicField g gi` about `x` is bounded by `M·‖y − x‖²` for `x, y` in
    that ball.  Ingredient (ii) of the Rung-2 capstone quadratic remainder bound — the direct `F`/`DF`
    mirror of `geodesicField_DF_second_order_taylor`.  `F` is `C^∞` (`contDiff_geodesicField`), hence
    differentiable everywhere; `DF` is `M`-Lipschitz on the (convex, compact) ball, and the
    fixed-linear-map mean-value inequality `Convex.norm_image_sub_le_of_norm_fderiv_le'` on the segment
    `[x, y]` (with `‖DF z − DF x‖ ≤ M·‖z − x‖ ≤ M·‖y − x‖`) yields the remainder constant `M·‖y − x‖`,
    i.e. the quadratic bound `M·‖y − x‖²`. -/
theorem geodesicField_F_second_order_taylor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hLip : LipschitzOnWith M.toNNReal (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p,0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (x y : Point n × Point n)
    (hx : x ∈ Metric.closedBall ((p,0) : Point n × Point n)
      (expConst g gi hC p * expRho g gi hC p))
    (hy : y ∈ Metric.closedBall ((p,0) : Point n × Point n)
      (expConst g gi hC p * expRho g gi hC p)) :
    ‖geodesicField g gi y - geodesicField g gi x
        - (fderiv ℝ (geodesicField g gi) x) (y - x)‖
      ≤ M * ‖y - x‖ ^ 2 := by
  -- The segment `[x, y]` is convex and sits inside the (convex) ball.
  have hseg : segment ℝ x y ⊆
      Metric.closedBall ((p,0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) :=
    (convex_closedBall _ _).segment_subset hx hy
  -- `F` is differentiable everywhere (it is `C^∞`).
  have hdiff : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ (geodesicField g gi) z :=
    fun z _ => ((contDiff_geodesicField g gi hC).differentiable (by simp)).differentiableAt
  -- Uniform bound on the derivative-difference over the segment: `‖DF z − DF x‖ ≤ M·‖y − x‖`.
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ (geodesicField g gi) z
          - fderiv ℝ (geodesicField g gi) x‖ ≤ M * ‖y - x‖ := by
    intro z hz
    have hd := hLip.dist_le_mul z (hseg hz) x hx
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal M hM0] at hd
    calc ‖fderiv ℝ (geodesicField g gi) z - fderiv ℝ (geodesicField g gi) x‖
        ≤ M * ‖z - x‖ := hd
      _ ≤ M * ‖y - x‖ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hM0
  -- Mean-value inequality on the segment, fixed-linear-map (`φ = DF x`) version.
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (f := geodesicField g gi)
    (φ := fderiv ℝ (geodesicField g gi) x)
    (C := M * ‖y - x‖) hdiff hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  calc ‖geodesicField g gi y - geodesicField g gi x
          - (fderiv ℝ (geodesicField g gi) x) (y - x)‖
      ≤ M * ‖y - x‖ * ‖y - x‖ := hmv
    _ = M * ‖y - x‖ ^ 2 := by ring

/-! ### Rung-2 remainder-bound ingredient (ii), assembly — the 2nd-order tube accuracy

The residual `W(t) := Y_{v+k}(t) − Y_v(t) − Φ_v(t)(ι k)` (with `Y_v = expTube p v`, `ι = expJetIota`,
and `Φ_v` the abstract first-variation propagator of `expJetFund` for `v`) satisfies `W(0) = 0` and, on
`[0,1]`, the inhomogeneous linear ODE `W'(t) = DF(Y_v t)(W t) + rF t`, where the source
`rF t = F(Y_{v+k} t) − F(Y_v t) − DF(Y_v t)(Y_{v+k} t − Y_v t)` is `F`'s own first-order Taylor
remainder.  Bounding `rF` by (ii-a) (`geodesicField_F_second_order_taylor`) and the two-point tube
separation `‖Y_{v+k} t − Y_v t‖ ≤ ‖k‖·e^{Kf}` (`geodesic_twopoint_gronwall`), a `[0,1]`-uniform vector
Grönwall (`gronwall_vec_residual_Icc`) yields the quadratic tube accuracy
`‖W t‖ ≤ (M·(e^{Kf})²·e^{Kstar})·‖k‖²`. -/

set_option maxHeartbeats 1000000 in
/-- **The 2nd-order tube-accuracy residual ODE.**  With `Φ` the first-variation propagator for
    parameter `v` (`expJetFund` witness, derivative law `Φ' = Ψ_v(Φ)`), the tube residual
    `W(t) = Y_{v+k}(t) − Y_v(t) − Φ(t)(ι k)` obeys, on `[0,1]`,
    `W'(t) = DF(Y_v t)(W t) + (F(Y_{v+k} t) − F(Y_v t) − DF(Y_v t)(Y_{v+k} t − Y_v t))`.

    Proof: the tubes solve `Y_·' = F(Y_·)` (`expTube_spec`) and the first variation solves
    `(Φ(ι k))' = DF(Y_v t)(Φ(ι k))` (differentiate `Φ' = Ψ_v(Φ)` applied at the fixed vector `ι k`,
    `HasDerivWithinAt.clm_apply` against a constant); subtracting the three curves and using linearity
    of `DF(Y_v t)` (`map_sub`) rearranges into the `DF(Y_v t)(W) + rF` form.  The `F`-analog of
    `expJet2_residual_hasDerivWithinAt`, one order down. -/
theorem expTube_second_order_residual_hasDerivWithinAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v k : Point n) (hvk : ‖v + k‖ ≤ expRho g gi hC p) (hv : ‖v‖ ≤ expRho g gi hC p)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun s => expTube g gi hC p (v + k) s - expTube g gi hC p v s - Φ s (expJetIota k))
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
          (expTube g gi hC p (v + k) t - expTube g gi hC p v t - Φ t (expJetIota k))
        + (geodesicField g gi (expTube g gi hC p (v + k) t)
             - geodesicField g gi (expTube g gi hC p v t)
             - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                 (expTube g gi hC p (v + k) t - expTube g gi hC p v t)))
      (Set.Icc (0 : ℝ) 1) t := by
  have hIcc_Ioo : t ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨_, hYdvk, _⟩ := expTube_spec g gi hC p (v + k) hvk
  obtain ⟨_, hYdv, _⟩ := expTube_spec g gi hC p v hv
  -- the two tubes' derivatives (within `[0,1]`).
  have hYvk : HasDerivWithinAt (expTube g gi hC p (v + k))
      (geodesicField g gi (expTube g gi hC p (v + k) t)) (Set.Icc (0 : ℝ) 1) t :=
    (hYdvk t hIcc_Ioo).hasDerivWithinAt
  have hYv : HasDerivWithinAt (expTube g gi hC p v)
      (geodesicField g gi (expTube g gi hC p v t)) (Set.Icc (0 : ℝ) 1) t :=
    (hYdv t hIcc_Ioo).hasDerivWithinAt
  -- first variation `P^k_v(t) = Φ(t)(ι k)` solves `(P^k_v)' = DF(Y_v t)(P^k_v)`.
  have hP : HasDerivWithinAt (fun s => Φ s (expJetIota k))
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ t (expJetIota k)))
      (Set.Icc (0 : ℝ) 1) t := by
    have hcl := (hΦd t ht).clm_apply
      (hasDerivWithinAt_const (x := t) (s := Set.Icc (0 : ℝ) 1) (c := expJetIota (n := n) k))
    simpa only [expJetPsi_apply, ContinuousLinearMap.comp_apply, map_zero, add_zero] using hcl
  -- the natural difference derivative.
  have hcomb := (hYvk.sub hYv).sub hP
  -- rearrange the target derivative into the natural one via linearity of `DF(Y_v t)`.
  have heq :
      (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
          (expTube g gi hC p (v + k) t - expTube g gi hC p v t - Φ t (expJetIota k))
        + (geodesicField g gi (expTube g gi hC p (v + k) t)
             - geodesicField g gi (expTube g gi hC p v t)
             - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                 (expTube g gi hC p (v + k) t - expTube g gi hC p v t))
      = geodesicField g gi (expTube g gi hC p (v + k) t)
          - geodesicField g gi (expTube g gi hC p v t)
          - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ t (expJetIota k)) := by
    simp only [map_sub]
    abel
  rw [heq]
  exact hcomb

/-- **`[0,1]`-uniform inhomogeneous vector Grönwall.**  The `∀ t ∈ [0,1]` version of
    `gronwall_vec_residual`: under the same hypotheses (`S 0 = 0`, `S' = A(S) + r`, `‖A‖ ≤ K`,
    `‖r‖ ≤ ρ`), `‖S t‖ ≤ ρ·e^{K}` uniformly for every `t ∈ [0,1]`.  Same `gronwall_Icc01_all` lift
    as the tail of `expFund_two_pt_diff_Icc`: the per-`t` bound `‖S t‖ ≤ gronwallBound 0 K ρ t` is
    monotone-dominated by the endpoint constant `ρ·e^{K}` (`gronwallBound_zero_le_exp`). -/
theorem gronwall_vec_residual_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S r : ℝ → E) (A : ℝ → (E →L[ℝ] E)) (K ρ : ℝ) (hK0 : 0 ≤ K) (hρ0 : 0 ≤ ρ)
    (hS0 : S 0 = 0)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt S (A t (S t) + r t) (Set.Icc (0 : ℝ) 1) t)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A t‖ ≤ K)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖r t‖ ≤ ρ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖S t‖ ≤ ρ * Real.exp K := by
  have hall := gronwall_Icc01_all S (fun t => A t (S t) + r t) 0 K ρ hderiv
    (by rw [hS0]; simp)
    (fun t ht => by
      calc ‖A t (S t) + r t‖ ≤ ‖A t (S t)‖ + ‖r t‖ := norm_add_le _ _
        _ ≤ K * ‖S t‖ + ρ := by
            refine add_le_add ?_ (hr t ht)
            calc ‖A t (S t)‖ ≤ ‖A t‖ * ‖S t‖ := (A t).le_opNorm _
              _ ≤ K * ‖S t‖ := mul_le_mul_of_nonneg_right (hA t ht) (norm_nonneg _))
  intro t ht
  exact (hall t ht).trans (gronwallBound_zero_le_exp K ρ t hK0 hρ0 ht.1 ht.2)

set_option maxHeartbeats 2000000 in
/-- **EXP-JET (ii) — the 2nd-order tube accuracy.**  For `‖v + k‖ ≤ expRho`, `‖v‖ ≤ expRho`, with `M`
    a `DF`-Lipschitz constant on the tube ball (`expJet_fderiv_lipschitzOnWith`), `Kf` an `F`-Lipschitz
    constant on the same ball, `Kstar` a `[0,1]`-bound on `‖DF(Y_v t)‖`, and `Φ` the first-variation
    propagator for `v` (`expJetFund` witness, `Φ 0 = 1`, derivative law `Φ' = Ψ_v(Φ)`), the tube
    residual `W(t) = Y_{v+k}(t) − Y_v(t) − Φ(t)(ι k)` is `O(‖k‖²)` uniformly on `[0,1]`:
    `‖W t‖ ≤ (M·(e^{Kf})²·e^{Kstar})·‖k‖²`.

    Assembly: the residual ODE `W' = DF(Y_v)(W) + rF` (`expTube_second_order_residual_hasDerivWithinAt`)
    with initial `W 0 = 0`; the source `‖rF t‖ ≤ M·‖Y_{v+k} t − Y_v t‖²` (`geodesicField_F_second_order_taylor`,
    (ii-a)); the two-point tube separation `‖Y_{v+k} t − Y_v t‖ ≤ ‖k‖·e^{Kf}`
    (`geodesic_twopoint_gronwall`), giving `‖rF t‖ ≤ M·(e^{Kf})²·‖k‖²`; then the `[0,1]`-uniform vector
    Grönwall (`gronwall_vec_residual_Icc`).  Ingredient (ii) of the Rung-2 quadratic remainder bound. -/
theorem expTube_second_order_accuracy (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v k : Point n) (hvk : ‖v + k‖ ≤ expRho g gi hC p) (hv : ‖v‖ ≤ expRho g gi hC p)
    (M : ℝ) (hM0 : 0 ≤ M) (Kf : NNReal) (Kstar : ℝ) (hKstar0 : 0 ≤ Kstar)
    (hLipF : LipschitzOnWith Kf (geodesicField g gi)
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipDF : LipschitzOnWith M.toNNReal (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t - Φ t (expJetIota k)‖
        ≤ (M * (Real.exp (Kf : ℝ)) ^ 2 * Real.exp Kstar) * ‖k‖ ^ 2 := by
  have hC₀ := expConst_nonneg g gi hC p
  set Rb : ℝ := expConst g gi hC p * expRho g gi hC p with hRbdef
  set S : Set (Point n × Point n) := Metric.closedBall ((p, 0) : Point n × Point n) Rb with hSdef
  obtain ⟨hY0vk, hYdvk, hconfvk⟩ := expTube_spec g gi hC p (v + k) hvk
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- both tubes lie in the ball `S` on `[0,1]`.
  have hSvk : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + k) t ∈ S := by
    intro t ht; rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖expTube g gi hC p (v + k) t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖v + k‖ := hconfvk t ht
      _ ≤ Rb := by rw [hRbdef]; exact mul_le_mul_of_nonneg_left hvk hC₀
  have hSv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈ S := by
    intro t ht; rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖expTube g gi hC p v t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖v‖ := hconfv t ht
      _ ≤ Rb := by rw [hRbdef]; exact mul_le_mul_of_nonneg_left hv hC₀
  -- two-point tube separation `‖Y_{v+k} t − Y_v t‖ ≤ ‖k‖·e^{Kf}`.
  have hdist0 : dist (expTube g gi hC p (v + k) 0) (expTube g gi hC p v 0) = ‖k‖ := by
    rw [hY0vk, hY0v, dist_eq_norm, Prod.mk_sub_mk, add_sub_cancel_left, sub_self, Prod.norm_def,
      norm_zero, max_eq_right (norm_nonneg _)]
  have htwopoint := geodesic_twopoint_gronwall g gi (S := S) (K := Kf) hLipF
    (fun t ht => hYdvk t (hIcc_Ioo t ht)) (fun t ht => hYdv t (hIcc_Ioo t ht)) hSvk hSv
  have hYvw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t‖ ≤ ‖k‖ * Real.exp (Kf : ℝ) := by
    intro t ht
    have h := htwopoint t ht
    rw [hdist0, dist_eq_norm] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  -- the Taylor-remainder source bound `‖rF t‖ ≤ M·(e^{Kf})²·‖k‖²`.
  set ρ : ℝ := M * (‖k‖ * Real.exp (Kf : ℝ)) ^ 2 with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (expTube g gi hC p (v + k) t)
          - geodesicField g gi (expTube g gi hC p v t)
          - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (expTube g gi hC p (v + k) t - expTube g gi hC p v t)‖ ≤ ρ := by
    intro t ht
    have htaylor := geodesicField_F_second_order_taylor g gi hC p M hM0 hLipDF
      (expTube g gi hC p v t) (expTube g gi hC p (v + k) t) (hSv t ht) (hSvk t ht)
    refine htaylor.trans ?_
    rw [hρdef]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hYvw t ht) 2) hM0
  -- initial condition `W 0 = 0`.
  have hW0 : expTube g gi hC p (v + k) 0 - expTube g gi hC p v 0 - Φ 0 (expJetIota k) = 0 := by
    rw [hY0vk, hY0v, hΦ0, ContinuousLinearMap.id_apply, expJetIota_apply]
    ext <;> simp
  -- apply the `[0,1]`-uniform vector Grönwall.
  have hgron := gronwall_vec_residual_Icc
    (fun s => expTube g gi hC p (v + k) s - expTube g gi hC p v s - Φ s (expJetIota k))
    (fun t => geodesicField g gi (expTube g gi hC p (v + k) t)
        - geodesicField g gi (expTube g gi hC p v t)
        - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
            (expTube g gi hC p (v + k) t - expTube g gi hC p v t))
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) Kstar ρ hKstar0 hρ0 hW0
    (fun t ht => expTube_second_order_residual_hasDerivWithinAt g gi hC p v k hvk hv Φ hΦd t ht)
    hKstarv hr
  intro t ht
  refine (hgron t ht).trans (le_of_eq ?_)
  rw [hρdef]; ring

/-! ### Rung-2 capstone — the quadratic remainder bound `‖r(t)‖ ≤ C·‖k‖²`

Two small `F`-generic CLM-application norm helpers (abstract normed spaces — no giant tube atoms
inside, so no `whnf` blow-up), then the assembly `expJet2_remainder_quadratic_bound`. -/

/-- **Generic CLM-application norm bound.**  `‖C a‖ ≤ KC · Ka` from `‖C‖ ≤ KC` and `‖a‖ ≤ Ka`. -/
private theorem clmApply_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : E →L[ℝ] F) (a : E) {KC Ka : ℝ} (hKC : 0 ≤ KC)
    (hC : ‖C‖ ≤ KC) (ha : ‖a‖ ≤ Ka) : ‖C a‖ ≤ KC * Ka :=
  (C.le_opNorm a).trans (mul_le_mul hC ha (norm_nonneg _) hKC)

/-- **Generic bilinear CLM-application norm bound.**  `‖B a b‖ ≤ KB · Ka · Kb`. -/
private theorem clmApply2_norm_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (a : E) (b : F) {KB Ka Kb : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) : ‖B a b‖ ≤ KB * Ka * Kb :=
  (B.le_opNorm₂ a b).trans
    (mul_le_mul (mul_le_mul hB ha (norm_nonneg _) hKB) hb (norm_nonneg _) (mul_nonneg hKB hKa))

set_option maxHeartbeats 2400000 in
/-- **The Jet₂ quadratic remainder bound (the Rung-2 capstone glue).**  With `Φ` the first-variation
    propagator for `v` and `Φ'` for `w = v + k` (`expJetFund` witnesses: `Φ 0 = Φ' 0 = 1`, derivative
    laws `Φ' = Ψ_v(Φ)`, `Φ'' = Ψ_{v+k}(Φ')`, continuous on `[0,1]`), the residual of
    `expJet2_residual_hasDerivWithinAt`
    `r(t) = [DF(Y_{v+k} t) − DF(Y_v t)](Φ'(t)(ι h)) − D²F(Y_v t)(Φ(t)(ι h))(Φ(t)(ι k))`
    is `O(‖k‖²)` uniformly on `[0,1]`: there is a `C ≥ 0` with `‖r(t)‖ ≤ C·‖k‖²`.

    Assembly of the three landed ingredients: (i) the `DF` second-order Taylor remainder is quadratic
    (`geodesicField_DF_second_order_taylor`), (ii) the 2nd-order tube accuracy
    `‖ΔY(t) − Φ(t)(ι k)‖ ≤ C₂‖k‖²` (`expTube_second_order_accuracy`) plus the tube separation
    `‖ΔY(t)‖ ≤ ‖k‖·e^{Kf}` (`geodesic_twopoint_gronwall`), (iii-a) the first-variation Lipschitz
    `‖Φ' t − Φ t‖ ≤ C₃‖k‖` (`expFund_two_pt_diff_Icc`) and (iii-b) the `D²F` symmetry
    (`fderiv2_geodesicField_symm`).  Feeds `expJet2_residual_bound` with `ρ = C·‖k‖²` to close the
    Fréchet little-o for `v ↦ Φ_v(1)(ι h)`. -/
theorem expJet2_remainder_quadratic_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v k h : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hvk : ‖v + k‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + k) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ' t (expJetIota h))
        - expJet2Rhs g gi hC p v Φ h k t‖ ≤ C * ‖k‖ ^ 2 := by
  have hC₀ := expConst_nonneg g gi hC p
  -- ── constants ──────────────────────────────────────────────────────────────────────────────
  -- `F`-Lipschitz const `Kf` on the confined tube ball.
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  -- `DF`-Lipschitz const `Ldf` and `D²F`-Lipschitz const `Ld2f`.
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  -- `DF` tube bounds for `v` and `v+k`; `D²F` tube bound (uniform).
  obtain ⟨Kv, hKv0, hKvbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨Kw, _hKw0, hKwbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p (v + k) hvk
  obtain ⟨Kstar2, hKstar20, hD2bd⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  -- `Φ`, `Φ'` op-norm bounds on `[0,1]` (compact + continuous).
  obtain ⟨Cv, hCvbd⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦcont
  obtain ⟨Cw, hCwbd⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦ'cont
  -- real-valued constants.
  set eKf : ℝ := Real.exp (Kf : ℝ) with heKf
  have heKf0 : 0 ≤ eKf := by rw [heKf]; exact (Real.exp_pos _).le
  set Kstar : ℝ := max Kv Kw with hKstardef
  have hKstar0 : 0 ≤ Kstar := le_max_of_le_left hKv0
  set eKs : ℝ := Real.exp Kstar with heKs
  have heKs0 : 0 ≤ eKs := by rw [heKs]; exact (Real.exp_pos _).le
  set Cphi : ℝ := max (max Cv Cw) 0 with hCphidef
  have hCphi0 : 0 ≤ Cphi := le_max_right _ _
  set L : ℝ := (Ld2f : ℝ) with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Ld2f.coe_nonneg
  set M : ℝ := (Ldf : ℝ) with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact Ldf.coe_nonneg
  set C2 : ℝ := M * eKf ^ 2 * eKs with hC2def
  have hC2_0 : 0 ≤ C2 := by
    rw [hC2def]; exact mul_nonneg (mul_nonneg hM0 (pow_nonneg heKf0 2)) heKs0
  set C3 : ℝ := M * eKf * eKs * eKs with hC3def
  have hC3_0 : 0 ≤ C3 := by
    rw [hC3def]; exact mul_nonneg (mul_nonneg (mul_nonneg hM0 heKf0) heKs0) heKs0
  -- Lipschitz constants recast to the `.toNNReal` shape the Taylor/accuracy lemmas consume.
  have hLipD2R : LipschitzOnWith L.toNNReal (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hLdef, Real.toNNReal_coe]; exact hLipD2
  have hLipDF_M : LipschitzOnWith M.toNNReal (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hMdef, Real.toNNReal_coe]; exact hLipDF
  -- uniform `[0,1]` bounds.
  have hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar :=
    fun t ht => (hKvbd t ht).trans (le_max_left Kv Kw)
  have hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t)‖ ≤ Kstar :=
    fun t ht => (hKwbd t ht).trans (le_max_right Kv Kw)
  have hΦbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi :=
    fun t ht => (hCvbd t ht).trans ((le_max_left Cv Cw).trans (le_max_left _ 0))
  have hΦ'bd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t‖ ≤ Cphi :=
    fun t ht => (hCwbd t ht).trans ((le_max_right Cv Cw).trans (le_max_left _ 0))
  -- ── tube-ball membership and separation ────────────────────────────────────────────────────
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  obtain ⟨hY0vk, hYdvk, hconfvk⟩ := expTube_spec g gi hC p (v + k) hvk
  have hmemv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfv t ht).trans (mul_le_mul_of_nonneg_left hv hC₀)
  have hmemw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + k) t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfvk t ht).trans (mul_le_mul_of_nonneg_left hvk hC₀)
  have hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t‖ ≤ ‖k‖ * eKf := by
    have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdist0 : dist (expTube g gi hC p (v + k) 0) (expTube g gi hC p v 0) = ‖k‖ := by
      rw [hY0vk, hY0v, dist_eq_norm, Prod.mk_sub_mk, add_sub_cancel_left, sub_self, Prod.norm_def,
        norm_zero, max_eq_right (norm_nonneg _)]
    have htwo := geodesic_twopoint_gronwall g gi
      (S := Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p))
      (K := Kf) hLipF
      (fun t ht => hYdvk t (hIcc_Ioo t ht)) (fun t ht => hYdv t (hIcc_Ioo t ht)) hmemw hmemv
    intro t ht
    have hh := htwo t ht
    rw [hdist0, dist_eq_norm] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  -- ── the three landed ingredient bounds, at each `t` ────────────────────────────────────────
  have htay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
              (expTube g gi hC p (v + k) t - expTube g gi hC p v t)‖
        ≤ L * ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_DF_second_order_taylor g gi hC p L hL0 hLipD2R
      (expTube g gi hC p v t) (expTube g gi hC p (v + k) t) (hmemv t ht) (hmemw t ht)
  have hacc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t - Φ t (expJetIota k)‖ ≤ C2 * ‖k‖ ^ 2 :=
    fun t ht => expTube_second_order_accuracy g gi hC p v k hvk hv M hM0 Kf Kstar hKstar0
      hLipF hLipDF_M hKstarv Φ hΦ0 hΦd t ht
  have htwopt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t - Φ' t‖ ≤ C3 * ‖k‖ := by
    have hbase := expFund_two_pt_diff_Icc g gi hC p v (v + k) Kf Ldf Kstar hKstar0
      hLipF hLipDF hKstarv hKstarw hv hvk Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    intro t ht
    have hb := hbase t ht
    rw [show v - (v + k) = -k by abel, norm_neg] at hb
    exact hb
  -- iota norm bounds.
  have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ :=
    ((expJetIota (n := n)).le_opNorm h).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h))
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ :=
    ((expJetIota (n := n)).le_opNorm k).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k))
  -- ── the witness constant and the per-`t` chain ─────────────────────────────────────────────
  refine ⟨L * eKf ^ 2 * Cphi * ‖h‖ + Kstar2 * C2 * Cphi * ‖h‖ + Kstar2 * Cphi * C3 * ‖h‖, ?_, ?_⟩
  · have hnh := norm_nonneg h
    exact add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hL0 (pow_nonneg heKf0 2)) hCphi0) hnh)
      (mul_nonneg (mul_nonneg (mul_nonneg hKstar20 hC2_0) hCphi0) hnh))
      (mul_nonneg (mul_nonneg (mul_nonneg hKstar20 hCphi0) hC3_0) hnh)
  · intro t ht
    rw [expJet2Rhs_apply]
    set dv := fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) with hdvE
    set dw := fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t) with hdwE
    set d2 := fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t) with hd2E
    set yv := expTube g gi hC p v t with hyvE
    set yw := expTube g gi hC p (v + k) t with hywE
    set ph := Φ t (expJetIota h) with hphE
    set ph' := Φ' t (expJetIota h) with hph'E
    set pk := Φ t (expJetIota k) with hpkE
    -- the four error-term inputs, in `set`-abbreviated form.
    have hE1 : ‖dw - dv - d2 (yw - yv)‖ ≤ L * ‖yw - yv‖ ^ 2 := htay t ht
    have hW : ‖yw - yv - pk‖ ≤ C2 * ‖k‖ ^ 2 := hacc t ht
    have hsepT : ‖yw - yv‖ ≤ ‖k‖ * eKf := hsep t ht
    have hd2n : ‖d2‖ ≤ Kstar2 := hD2bd v hv t ht
    have hph'n : ‖ph'‖ ≤ Cphi * ‖h‖ :=
      clmApply_norm_le (Φ' t) (expJetIota h) hCphi0 (hΦ'bd t ht) hιh
    have hpkn : ‖pk‖ ≤ Cphi * ‖k‖ :=
      clmApply_norm_le (Φ t) (expJetIota k) hCphi0 (hΦbd t ht) hιk
    have hdiffn : ‖ph' - ph‖ ≤ C3 * ‖k‖ * ‖h‖ := by
      have hsub : ph' - ph = (Φ' t - Φ t) (expJetIota h) := by
        rw [hph'E, hphE, ContinuousLinearMap.sub_apply]
      rw [hsub]
      calc ‖(Φ' t - Φ t) (expJetIota h)‖
          ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) h‖ := (Φ' t - Φ t).le_opNorm _
        _ ≤ C3 * ‖k‖ * ‖h‖ :=
            mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιh (norm_nonneg _)
              (mul_nonneg hC3_0 (norm_nonneg k))
    -- `D²F` symmetry cancels the leading term against `expJet2Rhs`.
    have hsymm : d2 pk ph = d2 ph pk := fderiv2_geodesicField_symm g gi hC yv pk ph
    have heq : (dw - dv) ph' - d2 ph pk
        = (dw - dv - d2 (yw - yv)) ph'
          + (d2 (yw - yv - pk)) ph'
          + (d2 pk) (ph' - ph) := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      rw [← hsymm]; abel
    rw [heq]
    -- bound each of the three `O(‖k‖²)` error terms.
    have hT1 : ‖(dw - dv - d2 (yw - yv)) ph'‖ ≤ (L * eKf ^ 2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by
      calc ‖(dw - dv - d2 (yw - yv)) ph'‖
          ≤ (L * ‖yw - yv‖ ^ 2) * (Cphi * ‖h‖) :=
            clmApply_norm_le _ ph' (mul_nonneg hL0 (pow_nonneg (norm_nonneg _) 2)) hE1 hph'n
        _ ≤ (L * (‖k‖ * eKf) ^ 2) * (Cphi * ‖h‖) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsepT 2) hL0)
              (mul_nonneg hCphi0 (norm_nonneg h))
        _ = (L * eKf ^ 2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by ring
    have hT2 : ‖(d2 (yw - yv - pk)) ph'‖ ≤ (Kstar2 * C2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by
      calc ‖(d2 (yw - yv - pk)) ph'‖
          ≤ Kstar2 * (C2 * ‖k‖ ^ 2) * (Cphi * ‖h‖) :=
            clmApply2_norm_le d2 (yw - yv - pk) ph' hKstar20
              (mul_nonneg hC2_0 (pow_nonneg (norm_nonneg k) 2)) hd2n hW hph'n
        _ = (Kstar2 * C2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by ring
    have hT3 : ‖(d2 pk) (ph' - ph)‖ ≤ (Kstar2 * Cphi * C3 * ‖h‖) * ‖k‖ ^ 2 := by
      calc ‖(d2 pk) (ph' - ph)‖
          ≤ Kstar2 * (Cphi * ‖k‖) * (C3 * ‖k‖ * ‖h‖) :=
            clmApply2_norm_le d2 pk (ph' - ph) hKstar20
              (mul_nonneg hCphi0 (norm_nonneg k)) hd2n hpkn hdiffn
        _ = (Kstar2 * Cphi * C3 * ‖h‖) * ‖k‖ ^ 2 := by ring
    calc ‖(dw - dv - d2 (yw - yv)) ph' + (d2 (yw - yv - pk)) ph' + (d2 pk) (ph' - ph)‖
        ≤ ‖(dw - dv - d2 (yw - yv)) ph' + (d2 (yw - yv - pk)) ph'‖ + ‖(d2 pk) (ph' - ph)‖ :=
          norm_add_le _ _
      _ ≤ (‖(dw - dv - d2 (yw - yv)) ph'‖ + ‖(d2 (yw - yv - pk)) ph'‖) + ‖(d2 pk) (ph' - ph)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((L * eKf ^ 2 * Cphi * ‖h‖) * ‖k‖ ^ 2 + (Kstar2 * C2 * Cphi * ‖h‖) * ‖k‖ ^ 2)
            + (Kstar2 * Cphi * C3 * ‖h‖) * ‖k‖ ^ 2 := add_le_add (add_le_add hT1 hT2) hT3
      _ = (L * eKf ^ 2 * Cphi * ‖h‖ + Kstar2 * C2 * Cphi * ‖h‖ + Kstar2 * Cphi * C3 * ‖h‖)
            * ‖k‖ ^ 2 := by ring

set_option maxHeartbeats 2400000 in
/-- **The `‖h‖`-separated Jet₂ quadratic remainder bound (the guaranteed floor).**  Identical to
    `expJet2_remainder_quadratic_bound` except the probe direction `h` is universally quantified and
    the constant `C₀` is INDEPENDENT of `h` — the `‖h‖` factor is pulled out explicitly:
    `∃ C₀ ≥ 0, ∀ h t, t ∈ [0,1] → ‖r_h(t)‖ ≤ C₀·‖h‖·‖k‖²`.  Every remainder term already carries a
    single `‖Φ' t (ι h)‖ ≤ Cφ‖h‖` or `‖ι h‖ ≤ ‖h‖` factor, so the constant without it is `C₀`.  This
    is exactly the form the operator-norm little-o (`expMap_fderiv_hasFDerivAt`) consumes: bounding the
    CLM `A_k := fderiv exp_p(v+k) − fderiv exp_p v − D²_v k` by `‖A_k h‖ ≤ C₀'·‖k‖²·‖h‖` uniformly. -/
theorem expJet2_remainder_quadratic_bound' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v k : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hvk : ‖v + k‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + k) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (h : Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ' t (expJetIota h))
        - expJet2Rhs g gi hC p v Φ h k t‖ ≤ C₀ * ‖h‖ * ‖k‖ ^ 2 := by
  have hC₀ := expConst_nonneg g gi hC p
  -- ── constants (identical to `expJet2_remainder_quadratic_bound`) ────────────────────────────
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Kv, hKv0, hKvbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨Kw, _hKw0, hKwbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p (v + k) hvk
  obtain ⟨Kstar2, hKstar20, hD2bd⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Cv, hCvbd⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦcont
  obtain ⟨Cw, hCwbd⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦ'cont
  set eKf : ℝ := Real.exp (Kf : ℝ) with heKf
  have heKf0 : 0 ≤ eKf := by rw [heKf]; exact (Real.exp_pos _).le
  set Kstar : ℝ := max Kv Kw with hKstardef
  have hKstar0 : 0 ≤ Kstar := le_max_of_le_left hKv0
  set eKs : ℝ := Real.exp Kstar with heKs
  have heKs0 : 0 ≤ eKs := by rw [heKs]; exact (Real.exp_pos _).le
  set Cphi : ℝ := max (max Cv Cw) 0 with hCphidef
  have hCphi0 : 0 ≤ Cphi := le_max_right _ _
  set L : ℝ := (Ld2f : ℝ) with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Ld2f.coe_nonneg
  set M : ℝ := (Ldf : ℝ) with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact Ldf.coe_nonneg
  set C2 : ℝ := M * eKf ^ 2 * eKs with hC2def
  have hC2_0 : 0 ≤ C2 := by
    rw [hC2def]; exact mul_nonneg (mul_nonneg hM0 (pow_nonneg heKf0 2)) heKs0
  set C3 : ℝ := M * eKf * eKs * eKs with hC3def
  have hC3_0 : 0 ≤ C3 := by
    rw [hC3def]; exact mul_nonneg (mul_nonneg (mul_nonneg hM0 heKf0) heKs0) heKs0
  have hLipD2R : LipschitzOnWith L.toNNReal (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hLdef, Real.toNNReal_coe]; exact hLipD2
  have hLipDF_M : LipschitzOnWith M.toNNReal (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hMdef, Real.toNNReal_coe]; exact hLipDF
  have hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar :=
    fun t ht => (hKvbd t ht).trans (le_max_left Kv Kw)
  have hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t)‖ ≤ Kstar :=
    fun t ht => (hKwbd t ht).trans (le_max_right Kv Kw)
  have hΦbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi :=
    fun t ht => (hCvbd t ht).trans ((le_max_left Cv Cw).trans (le_max_left _ 0))
  have hΦ'bd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t‖ ≤ Cphi :=
    fun t ht => (hCwbd t ht).trans ((le_max_right Cv Cw).trans (le_max_left _ 0))
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  obtain ⟨hY0vk, hYdvk, hconfvk⟩ := expTube_spec g gi hC p (v + k) hvk
  have hmemv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfv t ht).trans (mul_le_mul_of_nonneg_left hv hC₀)
  have hmemw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + k) t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfvk t ht).trans (mul_le_mul_of_nonneg_left hvk hC₀)
  have hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t‖ ≤ ‖k‖ * eKf := by
    have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdist0 : dist (expTube g gi hC p (v + k) 0) (expTube g gi hC p v 0) = ‖k‖ := by
      rw [hY0vk, hY0v, dist_eq_norm, Prod.mk_sub_mk, add_sub_cancel_left, sub_self, Prod.norm_def,
        norm_zero, max_eq_right (norm_nonneg _)]
    have htwo := geodesic_twopoint_gronwall g gi
      (S := Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p))
      (K := Kf) hLipF
      (fun t ht => hYdvk t (hIcc_Ioo t ht)) (fun t ht => hYdv t (hIcc_Ioo t ht)) hmemw hmemv
    intro t ht
    have hh := htwo t ht
    rw [hdist0, dist_eq_norm] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  have htay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
              (expTube g gi hC p (v + k) t - expTube g gi hC p v t)‖
        ≤ L * ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_DF_second_order_taylor g gi hC p L hL0 hLipD2R
      (expTube g gi hC p v t) (expTube g gi hC p (v + k) t) (hmemv t ht) (hmemw t ht)
  have hacc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t - Φ t (expJetIota k)‖ ≤ C2 * ‖k‖ ^ 2 :=
    fun t ht => expTube_second_order_accuracy g gi hC p v k hvk hv M hM0 Kf Kstar hKstar0
      hLipF hLipDF_M hKstarv Φ hΦ0 hΦd t ht
  have htwopt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t - Φ' t‖ ≤ C3 * ‖k‖ := by
    have hbase := expFund_two_pt_diff_Icc g gi hC p v (v + k) Kf Ldf Kstar hKstar0
      hLipF hLipDF hKstarv hKstarw hv hvk Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    intro t ht
    have hb := hbase t ht
    rw [show v - (v + k) = -k by abel, norm_neg] at hb
    exact hb
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ :=
    ((expJetIota (n := n)).le_opNorm k).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k))
  -- ── the `h`-INDEPENDENT witness constant ───────────────────────────────────────────────────
  refine ⟨L * eKf ^ 2 * Cphi + Kstar2 * C2 * Cphi + Kstar2 * Cphi * C3, ?_, ?_⟩
  · exact add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg hL0 (pow_nonneg heKf0 2)) hCphi0)
      (mul_nonneg (mul_nonneg hKstar20 hC2_0) hCphi0))
      (mul_nonneg (mul_nonneg hKstar20 hCphi0) hC3_0)
  · intro h t ht
    -- the `h`-dependent `ι` bound.
    have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ :=
      ((expJetIota (n := n)).le_opNorm h).trans (by
        simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h))
    rw [expJet2Rhs_apply]
    set dv := fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) with hdvE
    set dw := fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t) with hdwE
    set d2 := fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t) with hd2E
    set yv := expTube g gi hC p v t with hyvE
    set yw := expTube g gi hC p (v + k) t with hywE
    set ph := Φ t (expJetIota h) with hphE
    set ph' := Φ' t (expJetIota h) with hph'E
    set pk := Φ t (expJetIota k) with hpkE
    have hE1 : ‖dw - dv - d2 (yw - yv)‖ ≤ L * ‖yw - yv‖ ^ 2 := htay t ht
    have hW : ‖yw - yv - pk‖ ≤ C2 * ‖k‖ ^ 2 := hacc t ht
    have hsepT : ‖yw - yv‖ ≤ ‖k‖ * eKf := hsep t ht
    have hd2n : ‖d2‖ ≤ Kstar2 := hD2bd v hv t ht
    have hph'n : ‖ph'‖ ≤ Cphi * ‖h‖ :=
      clmApply_norm_le (Φ' t) (expJetIota h) hCphi0 (hΦ'bd t ht) hιh
    have hpkn : ‖pk‖ ≤ Cphi * ‖k‖ :=
      clmApply_norm_le (Φ t) (expJetIota k) hCphi0 (hΦbd t ht) hιk
    have hdiffn : ‖ph' - ph‖ ≤ C3 * ‖k‖ * ‖h‖ := by
      have hsub : ph' - ph = (Φ' t - Φ t) (expJetIota h) := by
        rw [hph'E, hphE, ContinuousLinearMap.sub_apply]
      rw [hsub]
      calc ‖(Φ' t - Φ t) (expJetIota h)‖
          ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) h‖ := (Φ' t - Φ t).le_opNorm _
        _ ≤ C3 * ‖k‖ * ‖h‖ :=
            mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιh (norm_nonneg _)
              (mul_nonneg hC3_0 (norm_nonneg k))
    have hsymm : d2 pk ph = d2 ph pk := fderiv2_geodesicField_symm g gi hC yv pk ph
    have heq : (dw - dv) ph' - d2 ph pk
        = (dw - dv - d2 (yw - yv)) ph'
          + (d2 (yw - yv - pk)) ph'
          + (d2 pk) (ph' - ph) := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      rw [← hsymm]; abel
    rw [heq]
    have hT1 : ‖(dw - dv - d2 (yw - yv)) ph'‖ ≤ (L * eKf ^ 2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by
      calc ‖(dw - dv - d2 (yw - yv)) ph'‖
          ≤ (L * ‖yw - yv‖ ^ 2) * (Cphi * ‖h‖) :=
            clmApply_norm_le _ ph' (mul_nonneg hL0 (pow_nonneg (norm_nonneg _) 2)) hE1 hph'n
        _ ≤ (L * (‖k‖ * eKf) ^ 2) * (Cphi * ‖h‖) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsepT 2) hL0)
              (mul_nonneg hCphi0 (norm_nonneg h))
        _ = (L * eKf ^ 2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by ring
    have hT2 : ‖(d2 (yw - yv - pk)) ph'‖ ≤ (Kstar2 * C2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by
      calc ‖(d2 (yw - yv - pk)) ph'‖
          ≤ Kstar2 * (C2 * ‖k‖ ^ 2) * (Cphi * ‖h‖) :=
            clmApply2_norm_le d2 (yw - yv - pk) ph' hKstar20
              (mul_nonneg hC2_0 (pow_nonneg (norm_nonneg k) 2)) hd2n hW hph'n
        _ = (Kstar2 * C2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by ring
    have hT3 : ‖(d2 pk) (ph' - ph)‖ ≤ (Kstar2 * Cphi * C3 * ‖h‖) * ‖k‖ ^ 2 := by
      calc ‖(d2 pk) (ph' - ph)‖
          ≤ Kstar2 * (Cphi * ‖k‖) * (C3 * ‖k‖ * ‖h‖) :=
            clmApply2_norm_le d2 pk (ph' - ph) hKstar20
              (mul_nonneg hCphi0 (norm_nonneg k)) hd2n hpkn hdiffn
        _ = (Kstar2 * Cphi * C3 * ‖h‖) * ‖k‖ ^ 2 := by ring
    calc ‖(dw - dv - d2 (yw - yv)) ph' + (d2 (yw - yv - pk)) ph' + (d2 pk) (ph' - ph)‖
        ≤ ‖(dw - dv - d2 (yw - yv)) ph' + (d2 (yw - yv - pk)) ph'‖ + ‖(d2 pk) (ph' - ph)‖ :=
          norm_add_le _ _
      _ ≤ (‖(dw - dv - d2 (yw - yv)) ph'‖ + ‖(d2 (yw - yv - pk)) ph'‖) + ‖(d2 pk) (ph' - ph)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((L * eKf ^ 2 * Cphi * ‖h‖) * ‖k‖ ^ 2 + (Kstar2 * C2 * Cphi * ‖h‖) * ‖k‖ ^ 2)
            + (Kstar2 * Cphi * C3 * ‖h‖) * ‖k‖ ^ 2 := add_le_add (add_le_add hT1 hT2) hT3
      _ = (L * eKf ^ 2 * Cphi + Kstar2 * C2 * Cphi + Kstar2 * Cphi * C3) * ‖h‖ * ‖k‖ ^ 2 := by ring

/-! ### Rung-2 capstone step (B) — the pointwise little-o of `fderiv exp_p`

This is the payoff of the quadratic remainder bound.  Fixing a probe direction `h`, the difference of
first derivatives `fderiv exp_p (v+k) h − fderiv exp_p v h` is approximated by the second-variation
value `π(Q^{hk}_v(1))` up to a genuinely **quadratic-in-`k`** error:

`‖ fderiv exp_p (v+k) h − fderiv exp_p v h − π(Q^{hk}_v(1)) ‖ ≤ C·‖k‖²`.

This is the `o(‖k‖)` little-o of `v ↦ fderiv exp_p v` (pointwise in `h`), the differentiability datum
of the second jet.  Threading:

* two `hasFDerivAt_expMap` witnesses `Φ` (at `v`) and `Φ'` (at `v+k`) — each simultaneously an
  ODE-spec propagator *and*, via `HasFDerivAt.fderiv`, the identity `fderiv exp_p · = π∘(·)(1)∘ι`;
* the vector second variation `Q^{hk}_v` from `expJet2Fund`;
* the Jacobi bound `Kstar` from `expJet_fderiv_tube_bddAbove` at `v`;
* the quadratic remainder bound `‖r(t)‖ ≤ C‖k‖²` from `expJet2_remainder_quadratic_bound`, fed as the
  `ρ` of `expJet2_residual_bound` ⟹ `‖Φ'(1)(ι h) − Φ(1)(ι h) − Q(1)‖ ≤ C‖k‖²·e^{Kstar}`;
* applying `π` (`‖π‖ ≤ 1`) and rewriting `fderiv exp_p · h = π(·(1)(ι h))`.

`Q^{hk}_v(1)` is exposed as `expJetPi (Q 1)` for the `expJet2Fund` witness `Q`.  The CLM-level
`HasFDerivAt (fun v => fderiv exp_p v) D²_v v` is **not** built here — it needs `Q^{hk}` linear in
`(h,k)` (ODE uniqueness + source linearity), a separate sub-brick; see the report/checkpoint. -/
theorem expMap_fderiv_sub_quadratic (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v k h : Point n)
    (hv : ‖v‖ < expRho g gi hC p) (hvk : ‖v + k‖ < expRho g gi hC p) :
    ∃ (Qhk1 : Point n) (C : ℝ), 0 ≤ C ∧
      ‖(fderiv ℝ (expMap g gi hC p) (v + k)) h
          - (fderiv ℝ (expMap g gi hC p) v) h - Qhk1‖ ≤ C * ‖k‖ ^ 2 := by
  -- the two propagators, each an ODE spec + a `fderiv` identity (via `HasFDerivAt.fderiv`).
  obtain ⟨Φ, hΦ0, hΦderiv, hfdv⟩ := hasFDerivAt_expMap g gi hC p v hv
  obtain ⟨Φ', hΦ'0, hΦ'deriv, hfdvk⟩ := hasFDerivAt_expMap g gi hC p (v + k) hvk
  have hfd_v : fderiv ℝ (expMap g gi hC p) v
      = expJetPi.comp ((Φ 1).comp (expJetIota (n := n))) := hfdv.fderiv
  have hfd_vk : fderiv ℝ (expMap g gi hC p) (v + k)
      = expJetPi.comp ((Φ' 1).comp (expJetIota (n := n))) := hfdvk.fderiv
  -- continuity of the propagators from their ODE derivatives.
  have hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hΦderiv t ht).continuousWithinAt
  have hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hΦ'deriv t ht).continuousWithinAt
  -- the vector second variation `Q^{hk}_v`.
  obtain ⟨Q, hQ0, _hQcont, _hQint, hQderiv⟩ :=
    expJet2Fund g gi hC p v Φ hv.le hΦcont h k
  -- the Jacobi bound `Kstar` on `‖DF(Y_v t)‖`.
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv.le
  -- the quadratic remainder bound `‖r(t)‖ ≤ C‖k‖²`.
  obtain ⟨C, hC0, hrbd⟩ := expJet2_remainder_quadratic_bound g gi hC p v k h Φ Φ'
    hv.le hvk.le hΦ0 hΦ'0 hΦcont hΦ'cont hΦderiv hΦ'deriv
  -- fed as `ρ = C‖k‖²` into the residual/Grönwall estimate.
  have hρ0 : (0 : ℝ) ≤ C * ‖k‖ ^ 2 := mul_nonneg hC0 (sq_nonneg _)
  have hresidual : ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Q 1‖
      ≤ (C * ‖k‖ ^ 2) * Real.exp Kstar :=
    expJet2_residual_bound g gi hC p v (v + k) Φ Φ' Q h k hΦ0 hΦ'0 hQ0
      hΦderiv hΦ'deriv hQderiv Kstar (C * ‖k‖ ^ 2) hKstar0 hρ0 hKstar hrbd
  -- project by `π` (`‖π‖ ≤ 1`), which is the `.1` coordinate.
  refine ⟨expJetPi (Q 1), C * Real.exp Kstar, mul_nonneg hC0 (Real.exp_pos _).le, ?_⟩
  rw [hfd_vk, hfd_v]
  simp only [ContinuousLinearMap.comp_apply]
  have hπsub : expJetPi (Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Q 1)
      = expJetPi (Φ' 1 (expJetIota h)) - expJetPi (Φ 1 (expJetIota h)) - expJetPi (Q 1) := by
    rw [map_sub, map_sub]
  calc ‖expJetPi (Φ' 1 (expJetIota h)) - expJetPi (Φ 1 (expJetIota h)) - expJetPi (Q 1)‖
      = ‖expJetPi (Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Q 1)‖ := by rw [hπsub]
    _ ≤ ‖expJetPi (n := n)‖ * ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Q 1‖ :=
        (expJetPi (n := n)).le_opNorm _
    _ ≤ 1 * ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Q 1‖ :=
        mul_le_mul_of_nonneg_right expJetPi_opNorm_le (norm_nonneg _)
    _ = ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Q 1‖ := one_mul _
    _ ≤ (C * ‖k‖ ^ 2) * Real.exp Kstar := hresidual
    _ = C * Real.exp Kstar * ‖k‖ ^ 2 := by ring

/-! ### Rung-2 capstone step (B-CLM) — `Q^{hk}(1)` is a BOUNDED BILINEAR function of `(h,k)`

The vector second variation `Q^{hk}` (the `expJet2Fund` witness) solves the inhomogeneous linear
Jet₂ IVP `Q'(t) = DF(Y_v t)(Q t) + Θ^{hk}(t)`, `Q(0) = 0`, with source
`Θ^{hk}(t) = D²F(Y_v t)(Φ t (ι h))(Φ t (ι k))` (`expJet2Rhs`).  This block establishes that the
value `Q^{hk}(1)` is well-defined (independent of the ODE witness) and a **bounded bilinear** function
of `(h,k)` — the datum a continuous linear map `D²_v : Point n →L[ℝ] Point n →L[ℝ] Point n` consumes
(via `mkContinuous₂`), the enabler for the CLM-level second derivative of `fderiv exp_p`.

Everything is `[AF]` (no `sorry`), a clean `gronwall_vec_residual`/`_Icc` + superposition-via-
uniqueness argument.  It does NOT build the parameter-residual `HasFDerivAt (v ↦ fderiv exp_p v) D²_v`
(the little-o step still needs `expMap_fderiv_sub_quadratic` fed the LINEAR `Q^{hk}(1)`), NOT
`ContDiff² exp_p`, NOT `ContDiff³`, NOT `κ = 1/6`, NOT the heat kernel / `a₁ = R/6`, NOT QG. -/

/-- **Source additivity in the `h`-slot.**  `Θ^{h₁+h₂,k} = Θ^{h₁,k} + Θ^{h₂,k}`, because `ι`, `Φ t`,
    and the bilinear `D²F(Y_v t)` are all additive in their (first) argument. -/
theorem expJet2Rhs_add_left (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))) (h₁ h₂ k : Point n) (t : ℝ) :
    expJet2Rhs g gi hC p v Φ (h₁ + h₂) k t
      = expJet2Rhs g gi hC p v Φ h₁ k t + expJet2Rhs g gi hC p v Φ h₂ k t := by
  simp only [expJet2Rhs_apply, map_add, ContinuousLinearMap.add_apply]

/-- **Source ℝ-homogeneity in the `h`-slot.**  `Θ^{c•h,k} = c • Θ^{h,k}`. -/
theorem expJet2Rhs_smul_left (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))) (c : ℝ) (h k : Point n) (t : ℝ) :
    expJet2Rhs g gi hC p v Φ (c • h) k t = c • expJet2Rhs g gi hC p v Φ h k t := by
  simp only [expJet2Rhs_apply, map_smul, ContinuousLinearMap.smul_apply]

/-- **Source additivity in the `k`-slot.**  `Θ^{h,k₁+k₂} = Θ^{h,k₁} + Θ^{h,k₂}`. -/
theorem expJet2Rhs_add_right (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))) (h k₁ k₂ : Point n) (t : ℝ) :
    expJet2Rhs g gi hC p v Φ h (k₁ + k₂) t
      = expJet2Rhs g gi hC p v Φ h k₁ t + expJet2Rhs g gi hC p v Φ h k₂ t := by
  simp only [expJet2Rhs_apply, map_add]

/-- **Source ℝ-homogeneity in the `k`-slot.**  `Θ^{h,c•k} = c • Θ^{h,k}`. -/
theorem expJet2Rhs_smul_right (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))) (c : ℝ) (h k : Point n) (t : ℝ) :
    expJet2Rhs g gi hC p v Φ h (c • k) t = c • expJet2Rhs g gi hC p v Φ h k t := by
  simp only [expJet2Rhs_apply, map_smul]

/-- **(1) `Q^{hk}` uniqueness — the second variation is well-defined.**  Any two solutions `Q₁, Q₂`
    of the inhomogeneous linear Jet₂ IVP (`Qᵢ 0 = 0`, `Qᵢ' = DF(Y_v)(Qᵢ) + Θ^{hk}`) agree on `[0,1]`
    (in particular at `t = 1`).  The difference `S = Q₁ − Q₂` has `S 0 = 0` and solves the
    HOMOGENEOUS equation `S' = DF(Y_v)(S)` (the sources cancel), so the residual vector Grönwall
    (`gronwall_vec_residual_Icc`, `r := 0`, `ρ := 0`, Jacobi bound `Kstar` from
    `expJet_fderiv_tube_bddAbove`) forces `‖S t‖ ≤ 0`, hence `S t = 0`. -/
theorem expJet2Fund_unique (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (h k : Point n)
    (Q₁ Q₂ : ℝ → (Point n × Point n)) (hQ₁0 : Q₁ 0 = 0) (hQ₂0 : Q₂ 0 = 0)
    (hderiv₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Q₁
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q₁ t)
        + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) t)
    (hderiv₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Q₂
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q₂ t)
        + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Q₁ t = Q₂ t := by
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  have hgron := gronwall_vec_residual_Icc
    (fun t => Q₁ t - Q₂ t) (fun _ => (0 : Point n × Point n))
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar 0 hKstar0 le_rfl
    (by simp only [hQ₁0, hQ₂0, sub_zero])
    (fun t ht => by
      have hd := (hderiv₁ t ht).sub (hderiv₂ t ht)
      have hval : ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q₁ t)
              + expJet2Rhs g gi hC p v Φ h k t)
            - ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q₂ t)
              + expJet2Rhs g gi hC p v Φ h k t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q₁ t - Q₂ t) + 0 := by
        rw [map_sub, add_zero]; abel
      rwa [hval] at hd)
    (fun t ht => hKstar t ht)
    (fun _ _ => by simp)
  intro t ht
  have h0 : ‖Q₁ t - Q₂ t‖ ≤ 0 := by simpa using hgron t ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

/-- **(2) `Q^{hk}(1)` value bound — bilinear-in-`(h,k)` magnitude.**  For the inhomogeneous Jet₂
    solution `Q` (`Q 0 = 0`, `Q' = DF(Y_v)(Q) + Θ^{hk}`), with a `[0,1]` Jacobi bound `Kstar` on
    `‖DF(Y_v t)‖` (`expJet_fderiv_tube_bddAbove`), a `[0,1]` `D²F`-bound `Kstar₂`
    (`expJet_fderiv2_tube_bddAbove_unif`), and a `[0,1]`-bound `Cphi` on `‖Φ t‖`,
    `‖Q 1‖ ≤ (Kstar₂·Cphi²·e^{Kstar})·‖h‖·‖k‖`.  The constant `M := Kstar₂·Cphi²·e^{Kstar}` is
    manifestly UNIFORM in `(h,k)`.  Proof: `‖Θ^{hk} t‖ ≤ Kstar₂·(Cphi‖h‖)·(Cphi‖k‖)`
    (`expJet2Rhs_norm_le`) fed as `ρ` into `gronwall_vec_residual` ⟹ `‖Q 1‖ ≤ ρ·e^{Kstar}`. -/
theorem expJet2Fund_value_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))) (h k : Point n)
    (Kstar Kstar₂ Cphi : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar₂0 : 0 ≤ Kstar₂) (hCphi0 : 0 ≤ Cphi)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hKstar₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar₂)
    (hCphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi)
    (Q : ℝ → (Point n × Point n)) (hQ0 : Q 0 = 0)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Q
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q t)
        + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) t) :
    ‖Q 1‖ ≤ (Kstar₂ * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖ := by
  have hρ0 : (0 : ℝ) ≤ Kstar₂ * (Cphi * ‖h‖) * (Cphi * ‖k‖) :=
    mul_nonneg (mul_nonneg hKstar₂0 (mul_nonneg hCphi0 (norm_nonneg _)))
      (mul_nonneg hCphi0 (norm_nonneg _))
  have hΘbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet2Rhs g gi hC p v Φ h k t‖ ≤ Kstar₂ * (Cphi * ‖h‖) * (Cphi * ‖k‖) :=
    fun t ht =>
      expJet2Rhs_norm_le g gi hC p v Φ h k Kstar₂ Cphi hKstar₂0 hCphi0 hKstar₂ hCphi t ht
  have hgron := gronwall_vec_residual Q (fun t => expJet2Rhs g gi hC p v Φ h k t)
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar (Kstar₂ * (Cphi * ‖h‖) * (Cphi * ‖k‖)) hKstar0 hρ0 hQ0 hderiv hKstar hΘbd
  calc ‖Q 1‖ ≤ (Kstar₂ * (Cphi * ‖h‖) * (Cphi * ‖k‖)) * Real.exp Kstar := hgron
    _ = (Kstar₂ * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖ := by ring

/-- **The chosen second-variation value** `Q^{hk}_v(1) : Point n × Point n`.  A canonical
    representative of the (uniqueness-`expJet2Fund_unique`-well-defined) value at `t = 1` of the
    `expJet2Fund` witness for direction pair `(h,k)`; used to STATE the bilinearity/boundedness. -/
noncomputable def expJet2Val (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k : Point n) : Point n × Point n :=
  (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose 1

/-- **(3a) Additivity of `Q^{hk}(1)` in the `h`-slot.**  Superposition via uniqueness: for chosen
    witnesses `Q^{h₁,k}, Q^{h₂,k}`, the sum `Q^{h₁,k}+Q^{h₂,k}` solves the `(h₁+h₂,k)` IVP (its
    derivative is `DF(Q₁+Q₂) + (Θ^{h₁}+Θ^{h₂}) = DF(Q₁+Q₂) + Θ^{h₁+h₂}` by `expJet2Rhs_add_left`),
    so by `expJet2Fund_unique` the `(h₁+h₂,k)` value equals `Q^{h₁,k}(1)+Q^{h₂,k}(1)`. -/
theorem expJet2Val_add_left (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h₁ h₂ k : Point n) :
    expJet2Val g gi hC p v Φ hv hΦcont (h₁ + h₂) k
      = expJet2Val g gi hC p v Φ hv hΦcont h₁ k + expJet2Val g gi hC p v Φ hv hΦcont h₂ k := by
  obtain ⟨hQ₁0, -, -, hQ₁deriv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h₁ k).choose_spec
  obtain ⟨hQ₂0, -, -, hQ₂deriv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h₂ k).choose_spec
  obtain ⟨hQ₃0, -, -, hQ₃deriv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont (h₁ + h₂) k).choose_spec
  have huniq := expJet2Fund_unique g gi hC p v Φ hv (h₁ + h₂) k
    (expJet2Fund g gi hC p v Φ hv hΦcont (h₁ + h₂) k).choose
    (fun t => (expJet2Fund g gi hC p v Φ hv hΦcont h₁ k).choose t
      + (expJet2Fund g gi hC p v Φ hv hΦcont h₂ k).choose t)
    hQ₃0 (by simp only [hQ₁0, hQ₂0, add_zero]) hQ₃deriv
    (fun t ht => by
      have hd := (hQ₁deriv t ht).add (hQ₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet2Fund g gi hC p v Φ hv hΦcont h₁ k).choose t)
            + expJet2Rhs g gi hC p v Φ h₁ k t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet2Fund g gi hC p v Φ hv hΦcont h₂ k).choose t)
            + expJet2Rhs g gi hC p v Φ h₂ k t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet2Fund g gi hC p v Φ hv hΦcont h₁ k).choose t
                + (expJet2Fund g gi hC p v Φ hv hΦcont h₂ k).choose t)
            + expJet2Rhs g gi hC p v Φ (h₁ + h₂) k t := by
        rw [map_add, expJet2Rhs_add_left]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet2Val] using h1

/-- **(3b) ℝ-homogeneity of `Q^{hk}(1)` in the `h`-slot.**  `Q^{c•h,k}(1) = c·Q^{h,k}(1)` (chosen
    witness `c•Q^{h,k}` solves the `(c•h,k)` IVP by `expJet2Rhs_smul_left` + uniqueness). -/
theorem expJet2Val_smul_left (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k : Point n) :
    expJet2Val g gi hC p v Φ hv hΦcont (c • h) k
      = c • expJet2Val g gi hC p v Φ hv hΦcont h k := by
  obtain ⟨hQ0, -, -, hQderiv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec
  obtain ⟨hQc0, -, -, hQcderiv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont (c • h) k).choose_spec
  have huniq := expJet2Fund_unique g gi hC p v Φ hv (c • h) k
    (expJet2Fund g gi hC p v Φ hv hΦcont (c • h) k).choose
    (fun t => c • (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose t)
    hQc0 (by simp only [hQ0, smul_zero]) hQcderiv
    (fun t ht => by
      have hd := (hQderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet2Fund g gi hC p v Φ hv hΦcont h k).choose t)
              + expJet2Rhs g gi hC p v Φ h k t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose t)
            + expJet2Rhs g gi hC p v Φ (c • h) k t := by
        rw [smul_add, map_smul, expJet2Rhs_smul_left]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet2Val] using h1

/-- **(3c) Additivity of `Q^{hk}(1)` in the `k`-slot.**  `Q^{h,k₁+k₂}(1) = Q^{h,k₁}(1)+Q^{h,k₂}(1)`
    (`expJet2Rhs_add_right` + uniqueness). -/
theorem expJet2Val_add_right (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k₁ k₂ : Point n) :
    expJet2Val g gi hC p v Φ hv hΦcont h (k₁ + k₂)
      = expJet2Val g gi hC p v Φ hv hΦcont h k₁ + expJet2Val g gi hC p v Φ hv hΦcont h k₂ := by
  obtain ⟨hQ₁0, -, -, hQ₁deriv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k₁).choose_spec
  obtain ⟨hQ₂0, -, -, hQ₂deriv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k₂).choose_spec
  obtain ⟨hQ₃0, -, -, hQ₃deriv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h (k₁ + k₂)).choose_spec
  have huniq := expJet2Fund_unique g gi hC p v Φ hv h (k₁ + k₂)
    (expJet2Fund g gi hC p v Φ hv hΦcont h (k₁ + k₂)).choose
    (fun t => (expJet2Fund g gi hC p v Φ hv hΦcont h k₁).choose t
      + (expJet2Fund g gi hC p v Φ hv hΦcont h k₂).choose t)
    hQ₃0 (by simp only [hQ₁0, hQ₂0, add_zero]) hQ₃deriv
    (fun t ht => by
      have hd := (hQ₁deriv t ht).add (hQ₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet2Fund g gi hC p v Φ hv hΦcont h k₁).choose t)
            + expJet2Rhs g gi hC p v Φ h k₁ t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet2Fund g gi hC p v Φ hv hΦcont h k₂).choose t)
            + expJet2Rhs g gi hC p v Φ h k₂ t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet2Fund g gi hC p v Φ hv hΦcont h k₁).choose t
                + (expJet2Fund g gi hC p v Φ hv hΦcont h k₂).choose t)
            + expJet2Rhs g gi hC p v Φ h (k₁ + k₂) t := by
        rw [map_add, expJet2Rhs_add_right]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet2Val] using h1

/-- **(3d) ℝ-homogeneity of `Q^{hk}(1)` in the `k`-slot.**  `Q^{h,c•k}(1) = c·Q^{h,k}(1)`
    (`expJet2Rhs_smul_right` + uniqueness). -/
theorem expJet2Val_smul_right (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k : Point n) :
    expJet2Val g gi hC p v Φ hv hΦcont h (c • k)
      = c • expJet2Val g gi hC p v Φ hv hΦcont h k := by
  obtain ⟨hQ0, -, -, hQderiv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec
  obtain ⟨hQc0, -, -, hQcderiv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h (c • k)).choose_spec
  have huniq := expJet2Fund_unique g gi hC p v Φ hv h (c • k)
    (expJet2Fund g gi hC p v Φ hv hΦcont h (c • k)).choose
    (fun t => c • (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose t)
    hQc0 (by simp only [hQ0, smul_zero]) hQcderiv
    (fun t ht => by
      have hd := (hQderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet2Fund g gi hC p v Φ hv hΦcont h k).choose t)
              + expJet2Rhs g gi hC p v Φ h k t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose t)
            + expJet2Rhs g gi hC p v Φ h (c • k) t := by
        rw [smul_add, map_smul, expJet2Rhs_smul_right]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet2Val] using h1

/-- **(2′) Uniform value bound for `expJet2Val`.**  A single `M ≥ 0` (from the `[0,1]` Jacobi/`D²F`
    tube bounds and a compactness bound `Cphi := ⨆ ‖Φ‖` on `[0,1]`) with
    `‖Q^{hk}_v(1)‖ ≤ M·‖h‖·‖k‖` for ALL `(h,k)`.  Feeds the `mkContinuous₂` packaging. -/
theorem expJet2Val_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h k : Point n,
      ‖expJet2Val g gi hC p v Φ hv hΦcont h k‖ ≤ M * ‖h‖ * ‖k‖ := by
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨Kstar₂, hKstar₂0, hKstar₂u⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  have hKstar₂ := hKstar₂u v hv
  obtain ⟨Cb, hCb⟩ := (isCompact_Icc).exists_bound_of_continuousOn hΦcont
  refine ⟨Kstar₂ * (max Cb 0) ^ 2 * Real.exp Kstar,
    mul_nonneg (mul_nonneg hKstar₂0 (sq_nonneg _)) (Real.exp_pos _).le, fun h k => ?_⟩
  obtain ⟨hQ0, -, -, hQderiv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec
  have hbd := expJet2Fund_value_bound g gi hC p v Φ h k Kstar Kstar₂ (max Cb 0)
    hKstar0 hKstar₂0 (le_max_right _ _) hKstar hKstar₂
    (fun t ht => (hCb t ht).trans (le_max_left _ _))
    (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose hQ0 hQderiv
  simpa only [expJet2Val] using hbd

/-- **(4) The packaged second-derivative operator `D²_v : Point n →L[ℝ] Point n →L[ℝ] Point n`.**
    `D²_v(k)(h) = π(Q^{hk}_v(1))` (slot order matching the eventual `D²_v(k)(h)`), a genuine
    CONTINUOUS BILINEAR map assembled from the four `expJet2Val` bilinearity facts
    (`expJet2Val_add_left/smul_left/add_right/smul_right`, transported through the linear projection
    `π = expJetPi`) via `LinearMap.mk₂`, with continuity/norm bound from `expJet2Val_norm_le`
    (`‖π‖ ≤ 1`) via `LinearMap.mkContinuous₂`.  This is the CLM datum the (downstream)
    `HasFDerivAt (v ↦ fderiv exp_p v) D²_v` little-o step consumes. -/
noncomputable def expJetD2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) :
    Point n →L[ℝ] Point n →L[ℝ] Point n :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun k h => expJetPi (expJet2Val g gi hC p v Φ hv hΦcont h k))
      (fun k₁ k₂ h => by
        simp only [expJet2Val_add_right g gi hC p v Φ hv hΦcont h k₁ k₂, map_add])
      (fun c k h => by
        simp only [expJet2Val_smul_right g gi hC p v Φ hv hΦcont c h k, map_smul])
      (fun k h₁ h₂ => by
        simp only [expJet2Val_add_left g gi hC p v Φ hv hΦcont h₁ h₂ k, map_add])
      (fun c k h => by
        simp only [expJet2Val_smul_left g gi hC p v Φ hv hΦcont c h k, map_smul]))
    (expJet2Val_norm_le g gi hC p v Φ hv hΦcont).choose
    (fun k h => by
      have hb := (expJet2Val_norm_le g gi hC p v Φ hv hΦcont).choose_spec.2 h k
      simp only [LinearMap.mk₂_apply]
      calc ‖expJetPi (expJet2Val g gi hC p v Φ hv hΦcont h k)‖
          ≤ ‖expJetPi (n := n)‖ * ‖expJet2Val g gi hC p v Φ hv hΦcont h k‖ :=
            (expJetPi (n := n)).le_opNorm _
        _ ≤ 1 * ‖expJet2Val g gi hC p v Φ hv hΦcont h k‖ :=
            mul_le_mul_of_nonneg_right expJetPi_opNorm_le (norm_nonneg _)
        _ = ‖expJet2Val g gi hC p v Φ hv hΦcont h k‖ := one_mul _
        _ ≤ (expJet2Val_norm_le g gi hC p v Φ hv hΦcont).choose * ‖h‖ * ‖k‖ := hb
        _ = (expJet2Val_norm_le g gi hC p v Φ hv hΦcont).choose * ‖k‖ * ‖h‖ := by ring)

/-- **`expJetD2` application form.**  `D²_v(k)(h) = π(Q^{hk}_v(1))`. -/
@[simp] theorem expJetD2_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (k h : Point n) :
    expJetD2 g gi hC p v Φ hv hΦcont k h = expJetPi (expJet2Val g gi hC p v Φ hv hΦcont h k) := rfl

/-! ### Rung-2 capstone step (B-asm) — the CLM operator-norm quadratic bound

The `‖h‖`-separated remainder (`expJet2_remainder_quadratic_bound'`) upgrades the pointwise-in-`h`
little-o (`expMap_fderiv_sub_quadratic`) to an OPERATOR-NORM bound on the CLM difference
`A_k := fderiv exp_p (v+k) − fderiv exp_p v − D²_v k`.  Reading off `‖A_k h‖ ≤ C·‖k‖²·‖h‖` for every
`h` (via the `‖h‖`-separated remainder fed to the residual Grönwall + `π`-projection), the operator
norm `‖A_k‖ ≤ C·‖k‖²` follows by `ContinuousLinearMap.opNorm_le_bound`.  This is the CLM datum the
`HasFDerivAt` little-o consumes (per fixed `k`; the constant `C` here still depends on `k` through the
`v+k` propagator `Φ'` — the UNIFORM-in-`k` version is `expMap_fderiv_hasFDerivAt`'s internal step). -/

set_option maxHeartbeats 1600000 in
/-- **CLM operator-norm quadratic bound for `fderiv exp_p` (fixed `k`).**  With `Φ` the first-variation
    propagator witness at `v` (an `hasFDerivAt_expMap` witness: `Φ 0 = 1`, ODE law, and the `fderiv`
    identity `fderiv exp_p v = π∘(Φ 1)∘ι`), for `k` with `‖v+k‖ < expRho` the continuous-linear-map
    difference `A_k := fderiv exp_p (v+k) − fderiv exp_p v − D²_v k` (`D²_v = expJetD2 … v Φ`) obeys
    `‖A_k‖ ≤ C·‖k‖²` for some `C ≥ 0`.  Proof: `‖A_k h‖ ≤ C·‖k‖²·‖h‖` for every `h` — the `‖h‖`-separated
    remainder `expJet2_remainder_quadratic_bound'` fed as `ρ = C₀‖h‖‖k‖²` into `expJet2_residual_bound`,
    projected by `π` (`‖π‖ ≤ 1`), identifying `D²_v k h = π(Q^{hk}(1))` (`expJetD2_apply`, `.choose`
    for `expJet2Val`) — then `ContinuousLinearMap.opNorm_le_bound`. -/
theorem expMap_fderiv_sub_quadratic_opNorm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v k : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ < expRho g gi hC p) (hvk : ‖v + k‖ < expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hfdv : fderiv ℝ (expMap g gi hC p) v
      = expJetPi.comp ((Φ 1).comp (expJetIota (n := n)))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖fderiv ℝ (expMap g gi hC p) (v + k) - fderiv ℝ (expMap g gi hC p) v
          - expJetD2 g gi hC p v Φ hv.le hΦcont k‖ ≤ C * ‖k‖ ^ 2 := by
  -- the `v+k` propagator + its `fderiv` identity.
  obtain ⟨Φ', hΦ'0, hΦ'deriv, hfdvk'⟩ := hasFDerivAt_expMap g gi hC p (v + k) hvk
  have hfd_vk : fderiv ℝ (expMap g gi hC p) (v + k)
      = expJetPi.comp ((Φ' 1).comp (expJetIota (n := n))) := hfdvk'.fderiv
  have hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hΦ'deriv t ht).continuousWithinAt
  -- the Jacobi bound at `v` and the `‖h‖`-separated quadratic remainder.
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv.le
  obtain ⟨C₀, hC₀0, hrbd⟩ := expJet2_remainder_quadratic_bound' g gi hC p v k Φ Φ'
    hv.le hvk.le hΦ0 hΦ'0 hΦcont hΦ'cont hΦderiv hΦ'deriv
  refine ⟨C₀ * Real.exp Kstar, mul_nonneg hC₀0 (Real.exp_pos _).le, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hC₀0 (Real.exp_pos _).le) (sq_nonneg _)) (fun h => ?_)
  -- reduce `A_k h` to `π(Φ' 1 (ι h) − Φ 1 (ι h) − Q^{hk}(1))`.
  set Qc := (expJet2Fund g gi hC p v Φ hv.le hΦcont h k).choose with hQcE
  obtain ⟨hQc0, -, -, hQcderiv⟩ :=
    (expJet2Fund g gi hC p v Φ hv.le hΦcont h k).choose_spec
  have hval : expJet2Val g gi hC p v Φ hv.le hΦcont h k = Qc 1 := rfl
  -- the residual Grönwall with `ρ = C₀·‖h‖·‖k‖²`.
  have hρ0 : (0 : ℝ) ≤ C₀ * ‖h‖ * ‖k‖ ^ 2 :=
    mul_nonneg (mul_nonneg hC₀0 (norm_nonneg _)) (sq_nonneg _)
  have hresidual : ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1‖
      ≤ (C₀ * ‖h‖ * ‖k‖ ^ 2) * Real.exp Kstar :=
    expJet2_residual_bound g gi hC p v (v + k) Φ Φ' Qc h k hΦ0 hΦ'0 hQc0
      hΦderiv hΦ'deriv hQcderiv Kstar (C₀ * ‖h‖ * ‖k‖ ^ 2) hKstar0 hρ0 hKstar
      (fun t ht => hrbd h t ht)
  -- unfold the CLM application and project by `π`.
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, hfd_vk, hfdv,
    expJetD2_apply, hval]
  simp only [ContinuousLinearMap.comp_apply]
  have hπsub : expJetPi (Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1)
      = expJetPi (Φ' 1 (expJetIota h)) - expJetPi (Φ 1 (expJetIota h)) - expJetPi (Qc 1) := by
    rw [map_sub, map_sub]
  calc ‖expJetPi (Φ' 1 (expJetIota h)) - expJetPi (Φ 1 (expJetIota h)) - expJetPi (Qc 1)‖
      = ‖expJetPi (Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1)‖ := by rw [hπsub]
    _ ≤ ‖expJetPi (n := n)‖ * ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1‖ :=
        (expJetPi (n := n)).le_opNorm _
    _ ≤ 1 * ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1‖ :=
        mul_le_mul_of_nonneg_right expJetPi_opNorm_le (norm_nonneg _)
    _ = ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1‖ := one_mul _
    _ ≤ (C₀ * ‖h‖ * ‖k‖ ^ 2) * Real.exp Kstar := hresidual
    _ = C₀ * Real.exp Kstar * ‖k‖ ^ 2 * ‖h‖ := by ring

/-! ### Rung-2 capstone step (B-asm-2) — the CLM `HasFDerivAt` of `fderiv exp_p`

The per-`k` operator-norm bound has a `k`-dependent constant (the `v+k` propagator `Φ'`).  For the
genuine `HasFDerivAt (v ↦ fderiv exp_p v) D²_v v` little-o, the constant must be UNIFORM over a
neighbourhood of `k = 0`.  The `k`-dependence of `expJet2_remainder_quadratic_bound'`'s constant
enters ONLY through (i) the `v+k`-tube Jacobi bound and (ii) the `‖Φ' t‖` bound.  Both are killed by
the UNIFORM devices: `expJet_fderiv_tube_bddAbove_unif` bounds `‖DF(Y_w t)‖` by one `Kstar` for ALL
`‖w‖ ≤ expRho`, and the linear-propagator Grönwall (`expJetFund_norm_le_exp`) bounds `‖Φ' t‖ ≤ e^{Kstar}`
with the SAME `Kstar` — independent of which propagator witness.  This yields a `k`-uniform quadratic
remainder, hence a `k`-uniform `‖A_k‖ ≤ M·‖k‖²`, hence the little-o via `‖k‖² = o(‖k‖)`. -/

/-- **Uniform propagator norm bound `‖Φ t‖ ≤ e^{Kstar}`.**  Any solution `Ψ` of the linear
    Jacobi propagator ODE `Ψ' = Ψ_w(Ψ)`, `Ψ 0 = 1`, with `‖DF(Y_w t)‖ ≤ Kstar` on `[0,1]`, obeys
    `‖Ψ t‖ ≤ e^{Kstar}` for all `t ∈ [0,1]` (Grönwall `gronwall_Icc01_all` with `ε = 0`,
    `δ = 1` from `‖Ψ 0‖ = ‖id‖ ≤ 1`, generator bound `‖Ψ_w M‖ ≤ Kstar·‖M‖` via `expJetPsi_norm_le`).
    The bound is UNIFORM in the witness `Ψ` and in `w` given the `Kstar` — the enabler of the
    `k`-uniform quadratic remainder. -/
theorem expJetFund_norm_le_exp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p w : Point n)
    (Ψ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Kstar : ℝ) (hKstar0 : 0 ≤ Kstar)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)‖ ≤ Kstar)
    (hΨ0 : Ψ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΨd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Ψ (expJetPsi g gi hC p w t (Ψ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Ψ t‖ ≤ Real.exp Kstar := by
  have hall := gronwall_Icc01_all Ψ (fun t => expJetPsi g gi hC p w t (Ψ t)) 1 Kstar 0
    hΨd (by rw [hΨ0]; exact ContinuousLinearMap.norm_id_le)
    (fun t ht => by
      rw [add_zero]
      exact (expJetPsi_norm_le g gi hC p w t (Ψ t)).trans
        (mul_le_mul_of_nonneg_right (hKstar t ht) (norm_nonneg _)))
  intro t ht
  have h := hall t ht
  rw [gronwallBound_ε0, one_mul] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  calc Kstar * t ≤ Kstar * 1 := mul_le_mul_of_nonneg_left ht.2 hKstar0
    _ = Kstar := mul_one _

set_option maxHeartbeats 2400000 in
/-- **The `k`-UNIFORM `‖h‖`-separated quadratic remainder bound.**  Like
    `expJet2_remainder_quadratic_bound'`, but the constant `C₀` is INDEPENDENT of `k` (and of the
    `v+k`-propagator witness `Φ'`): a single `C₀ ≥ 0` works for EVERY `k` with `‖v+k‖ ≤ expRho` and
    every propagator `Φ'` for `v+k`.  The `k`-uniformity comes from replacing the compactness bounds
    of `expJet2_remainder_quadratic_bound'` by the uniform devices: `Kstar` from
    `expJet_fderiv_tube_bddAbove_unif` (bounds `DF` at both `v` and `v+k`) and `Cphi = e^{Kstar}` from
    `expJetFund_norm_le_exp` (bounds both `‖Φ t‖` and `‖Φ' t‖`).  Feeds the residual Grönwall in
    `expMap_fderiv_hasFDerivAt` with a fixed proportionality constant. -/
theorem expJet2_remainder_quadratic_bound_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (_hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (k : Point n), ‖v + k‖ ≤ expRho g gi hC p →
      ∀ (Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))),
        Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n) →
        ContinuousOn Φ' (Set.Icc (0 : ℝ) 1) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + k) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t) →
        ∀ (h : Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t)
              - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Φ' t (expJetIota h))
            - expJet2Rhs g gi hC p v Φ h k t‖ ≤ C₀ * ‖h‖ * ‖k‖ ^ 2 := by
  have hC₀ := expConst_nonneg g gi hC p
  -- ── UNIFORM (k-independent) constants ──────────────────────────────────────────────────────
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Kstar2, hKstar20, hD2bd⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar, hKstar0, hKstaru⟩ := expJet_fderiv_tube_bddAbove_unif g gi hC p
  set eKf : ℝ := Real.exp (Kf : ℝ) with heKf
  have heKf0 : 0 ≤ eKf := by rw [heKf]; exact (Real.exp_pos _).le
  set Cphi : ℝ := Real.exp Kstar with hCphidef
  have hCphi0 : 0 ≤ Cphi := by rw [hCphidef]; exact (Real.exp_pos _).le
  set L : ℝ := (Ld2f : ℝ) with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Ld2f.coe_nonneg
  set M : ℝ := (Ldf : ℝ) with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact Ldf.coe_nonneg
  set C2 : ℝ := M * eKf ^ 2 * Cphi with hC2def
  have hC2_0 : 0 ≤ C2 := by
    rw [hC2def]; exact mul_nonneg (mul_nonneg hM0 (pow_nonneg heKf0 2)) hCphi0
  set C3 : ℝ := M * eKf * Cphi * Cphi with hC3def
  have hC3_0 : 0 ≤ C3 := by
    rw [hC3def]; exact mul_nonneg (mul_nonneg (mul_nonneg hM0 heKf0) hCphi0) hCphi0
  have hLipD2R : LipschitzOnWith L.toNNReal (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hLdef, Real.toNNReal_coe]; exact hLipD2
  have hLipDF_M : LipschitzOnWith M.toNNReal (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hMdef, Real.toNNReal_coe]; exact hLipDF
  -- v-side uniform bounds (k-independent): Jacobi bound, propagator norm, tube membership.
  have hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar := hKstaru v hv
  have hΦbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi :=
    expJetFund_norm_le_exp g gi hC p v Φ Kstar hKstar0 hKstarv hΦ0 hΦd
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  have hmemv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfv t ht).trans (mul_le_mul_of_nonneg_left hv hC₀)
  have hιk_gen : ∀ x : Point n, ‖expJetIota (n := n) x‖ ≤ ‖x‖ :=
    fun x => ((expJetIota (n := n)).le_opNorm x).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg x))
  -- ── the k-INDEPENDENT witness constant ─────────────────────────────────────────────────────
  refine ⟨L * eKf ^ 2 * Cphi + Kstar2 * C2 * Cphi + Kstar2 * Cphi * C3, ?_, ?_⟩
  · exact add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg hL0 (pow_nonneg heKf0 2)) hCphi0)
      (mul_nonneg (mul_nonneg hKstar20 hC2_0) hCphi0))
      (mul_nonneg (mul_nonneg hKstar20 hCphi0) hC3_0)
  · intro k hvk Φ' hΦ'0 hΦ'cont hΦ'd
    -- k-side uniform bounds (same uniform constants).
    have hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t)‖ ≤ Kstar :=
      hKstaru (v + k) hvk
    have hΦ'bd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t‖ ≤ Cphi :=
      expJetFund_norm_le_exp g gi hC p (v + k) Φ' Kstar hKstar0 hKstarw hΦ'0 hΦ'd
    obtain ⟨hY0vk, hYdvk, hconfvk⟩ := expTube_spec g gi hC p (v + k) hvk
    have hmemw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + k) t ∈
        Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
      intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
      exact (hconfvk t ht).trans (mul_le_mul_of_nonneg_left hvk hC₀)
    have hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t‖ ≤ ‖k‖ * eKf := by
      have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
        fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hdist0 : dist (expTube g gi hC p (v + k) 0) (expTube g gi hC p v 0) = ‖k‖ := by
        rw [hY0vk, hY0v, dist_eq_norm, Prod.mk_sub_mk, add_sub_cancel_left, sub_self, Prod.norm_def,
          norm_zero, max_eq_right (norm_nonneg _)]
      have htwo := geodesic_twopoint_gronwall g gi
        (S := Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p))
        (K := Kf) hLipF
        (fun t ht => hYdvk t (hIcc_Ioo t ht)) (fun t ht => hYdv t (hIcc_Ioo t ht)) hmemw hmemv
      intro t ht
      have hh := htwo t ht
      rw [hdist0, dist_eq_norm] at hh
      refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
      calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
        _ = (Kf : ℝ) := mul_one _
    have htay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t)
            - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
            - (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
                (expTube g gi hC p (v + k) t - expTube g gi hC p v t)‖
          ≤ L * ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t‖ ^ 2 :=
      fun t ht => geodesicField_DF_second_order_taylor g gi hC p L hL0 hLipD2R
        (expTube g gi hC p v t) (expTube g gi hC p (v + k) t) (hmemv t ht) (hmemw t ht)
    have hacc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t - Φ t (expJetIota k)‖ ≤ C2 * ‖k‖ ^ 2 :=
      fun t ht => expTube_second_order_accuracy g gi hC p v k hvk hv M hM0 Kf Kstar hKstar0
        hLipF hLipDF_M hKstarv Φ hΦ0 hΦd t ht
    have htwopt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t - Φ' t‖ ≤ C3 * ‖k‖ := by
      have hbase := expFund_two_pt_diff_Icc g gi hC p v (v + k) Kf Ldf Kstar hKstar0
        hLipF hLipDF hKstarv hKstarw hv hvk Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
      intro t ht
      have hb := hbase t ht
      rw [show v - (v + k) = -k by abel, norm_neg] at hb
      exact hb
    intro h t ht
    have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ := hιk_gen h
    have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ := hιk_gen k
    rw [expJet2Rhs_apply]
    set dv := fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) with hdvE
    set dw := fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + k) t) with hdwE
    set d2 := fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t) with hd2E
    set yv := expTube g gi hC p v t with hyvE
    set yw := expTube g gi hC p (v + k) t with hywE
    set ph := Φ t (expJetIota h) with hphE
    set ph' := Φ' t (expJetIota h) with hph'E
    set pk := Φ t (expJetIota k) with hpkE
    have hE1 : ‖dw - dv - d2 (yw - yv)‖ ≤ L * ‖yw - yv‖ ^ 2 := htay t ht
    have hW : ‖yw - yv - pk‖ ≤ C2 * ‖k‖ ^ 2 := hacc t ht
    have hsepT : ‖yw - yv‖ ≤ ‖k‖ * eKf := hsep t ht
    have hd2n : ‖d2‖ ≤ Kstar2 := hD2bd v hv t ht
    have hph'n : ‖ph'‖ ≤ Cphi * ‖h‖ :=
      clmApply_norm_le (Φ' t) (expJetIota h) hCphi0 (hΦ'bd t ht) hιh
    have hpkn : ‖pk‖ ≤ Cphi * ‖k‖ :=
      clmApply_norm_le (Φ t) (expJetIota k) hCphi0 (hΦbd t ht) hιk
    have hdiffn : ‖ph' - ph‖ ≤ C3 * ‖k‖ * ‖h‖ := by
      have hsub : ph' - ph = (Φ' t - Φ t) (expJetIota h) := by
        rw [hph'E, hphE, ContinuousLinearMap.sub_apply]
      rw [hsub]
      calc ‖(Φ' t - Φ t) (expJetIota h)‖
          ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) h‖ := (Φ' t - Φ t).le_opNorm _
        _ ≤ C3 * ‖k‖ * ‖h‖ :=
            mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιh (norm_nonneg _)
              (mul_nonneg hC3_0 (norm_nonneg k))
    have hsymm : d2 pk ph = d2 ph pk := fderiv2_geodesicField_symm g gi hC yv pk ph
    have heq : (dw - dv) ph' - d2 ph pk
        = (dw - dv - d2 (yw - yv)) ph'
          + (d2 (yw - yv - pk)) ph'
          + (d2 pk) (ph' - ph) := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      rw [← hsymm]; abel
    rw [heq]
    have hT1 : ‖(dw - dv - d2 (yw - yv)) ph'‖ ≤ (L * eKf ^ 2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by
      calc ‖(dw - dv - d2 (yw - yv)) ph'‖
          ≤ (L * ‖yw - yv‖ ^ 2) * (Cphi * ‖h‖) :=
            clmApply_norm_le _ ph' (mul_nonneg hL0 (pow_nonneg (norm_nonneg _) 2)) hE1 hph'n
        _ ≤ (L * (‖k‖ * eKf) ^ 2) * (Cphi * ‖h‖) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsepT 2) hL0)
              (mul_nonneg hCphi0 (norm_nonneg h))
        _ = (L * eKf ^ 2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by ring
    have hT2 : ‖(d2 (yw - yv - pk)) ph'‖ ≤ (Kstar2 * C2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by
      calc ‖(d2 (yw - yv - pk)) ph'‖
          ≤ Kstar2 * (C2 * ‖k‖ ^ 2) * (Cphi * ‖h‖) :=
            clmApply2_norm_le d2 (yw - yv - pk) ph' hKstar20
              (mul_nonneg hC2_0 (pow_nonneg (norm_nonneg k) 2)) hd2n hW hph'n
        _ = (Kstar2 * C2 * Cphi * ‖h‖) * ‖k‖ ^ 2 := by ring
    have hT3 : ‖(d2 pk) (ph' - ph)‖ ≤ (Kstar2 * Cphi * C3 * ‖h‖) * ‖k‖ ^ 2 := by
      calc ‖(d2 pk) (ph' - ph)‖
          ≤ Kstar2 * (Cphi * ‖k‖) * (C3 * ‖k‖ * ‖h‖) :=
            clmApply2_norm_le d2 pk (ph' - ph) hKstar20
              (mul_nonneg hCphi0 (norm_nonneg k)) hd2n hpkn hdiffn
        _ = (Kstar2 * Cphi * C3 * ‖h‖) * ‖k‖ ^ 2 := by ring
    calc ‖(dw - dv - d2 (yw - yv)) ph' + (d2 (yw - yv - pk)) ph' + (d2 pk) (ph' - ph)‖
        ≤ ‖(dw - dv - d2 (yw - yv)) ph' + (d2 (yw - yv - pk)) ph'‖ + ‖(d2 pk) (ph' - ph)‖ :=
          norm_add_le _ _
      _ ≤ (‖(dw - dv - d2 (yw - yv)) ph'‖ + ‖(d2 (yw - yv - pk)) ph'‖) + ‖(d2 pk) (ph' - ph)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((L * eKf ^ 2 * Cphi * ‖h‖) * ‖k‖ ^ 2 + (Kstar2 * C2 * Cphi * ‖h‖) * ‖k‖ ^ 2)
            + (Kstar2 * Cphi * C3 * ‖h‖) * ‖k‖ ^ 2 := add_le_add (add_le_add hT1 hT2) hT3
      _ = (L * eKf ^ 2 * Cphi + Kstar2 * C2 * Cphi + Kstar2 * Cphi * C3) * ‖h‖ * ‖k‖ ^ 2 := by ring

set_option maxHeartbeats 1600000 in
/-- **Rung-2 capstone (B-asm-2): `fderiv exp_p` is Fréchet-differentiable with derivative `D²_v`.**
    For `‖v‖ < expRho` and the first-variation propagator witness `Φ` at `v` (an `hasFDerivAt_expMap`
    witness: `Φ 0 = 1`, ODE law, and the `fderiv` identity `fderiv exp_p v = π∘(Φ 1)∘ι`),
    `HasFDerivAt (w ↦ fderiv exp_p w) (D²_v) v` with `D²_v = expJetD2 … v Φ`.  Proof: the
    `k`-UNIFORM quadratic remainder (`expJet2_remainder_quadratic_bound_unif`) + residual Grönwall +
    `π`-projection give `‖A_k h‖ ≤ (C₀·e^{Kstar})·‖k‖²·‖h‖` for every `h`, hence
    `‖A_k‖ ≤ M·‖k‖²` (`M = C₀·e^{Kstar}`, `ContinuousLinearMap.opNorm_le_bound`) where
    `A_k = fderiv exp_p(v+k) − fderiv exp_p v − D²_v k`; then `M·‖k‖² = o(‖k‖)` as `k → 0`
    (`hasFDerivAt_iff_isLittleO_nhds_zero`, radius `min (expRho−‖v‖) (c/(M+1))`).  This is the
    second-derivative differentiability datum of `exp_p`; it does NOT by itself give `ContDiff²`
    (continuity of `v ↦ D²_v` is the next step), NOT `ContDiff³`, NOT `κ = 1/6`, NOT the heat
    kernel / `a₁ = R/6`, NOT QG. -/
theorem expMap_fderiv_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ < expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hfdv : fderiv ℝ (expMap g gi hC p) v
      = expJetPi.comp ((Φ 1).comp (expJetIota (n := n)))) :
    HasFDerivAt (fun w => fderiv ℝ (expMap g gi hC p) w)
      (expJetD2 g gi hC p v Φ hv.le hΦcont) v := by
  obtain ⟨C₀, hC₀0, hrbdU⟩ :=
    expJet2_remainder_quadratic_bound_unif g gi hC p v Φ hv.le hΦ0 hΦcont hΦderiv
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv.le
  set Mc : ℝ := C₀ * Real.exp Kstar with hMcdef
  have hMc0 : 0 ≤ Mc := mul_nonneg hC₀0 (Real.exp_pos _).le
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min (expRho g gi hC p - ‖v‖) (c / (Mc + 1)),
    lt_min (by linarith [hv]) (div_pos hc (by linarith)), fun k hk => ?_⟩
  rw [dist_eq_norm, sub_zero] at hk
  have hk1 : ‖k‖ < expRho g gi hC p - ‖v‖ := lt_of_lt_of_le hk (min_le_left _ _)
  have hkM : ‖k‖ ≤ c / (Mc + 1) := (lt_of_lt_of_le hk (min_le_right _ _)).le
  have hvk_lt : ‖v + k‖ < expRho g gi hC p :=
    lt_of_le_of_lt (norm_add_le v k) (by linarith)
  have hvk_le : ‖v + k‖ ≤ expRho g gi hC p := hvk_lt.le
  -- the `v+k` propagator witness + its `fderiv` identity.
  obtain ⟨Φ', hΦ'0, hΦ'deriv, hfdvk'⟩ := hasFDerivAt_expMap g gi hC p (v + k) hvk_lt
  have hfd_vk : fderiv ℝ (expMap g gi hC p) (v + k)
      = expJetPi.comp ((Φ' 1).comp (expJetIota (n := n))) := hfdvk'.fderiv
  have hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hΦ'deriv t ht).continuousWithinAt
  -- the k-UNIFORM operator-norm bound `‖A_k‖ ≤ Mc·‖k‖²`.
  have hAk : ‖fderiv ℝ (expMap g gi hC p) (v + k) - fderiv ℝ (expMap g gi hC p) v
      - expJetD2 g gi hC p v Φ hv.le hΦcont k‖ ≤ Mc * ‖k‖ ^ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hMc0 (sq_nonneg _)) (fun h => ?_)
    set Qc := (expJet2Fund g gi hC p v Φ hv.le hΦcont h k).choose with hQcE
    obtain ⟨hQc0, -, -, hQcderiv⟩ :=
      (expJet2Fund g gi hC p v Φ hv.le hΦcont h k).choose_spec
    have hval : expJet2Val g gi hC p v Φ hv.le hΦcont h k = Qc 1 := rfl
    have hρ0 : (0 : ℝ) ≤ C₀ * ‖h‖ * ‖k‖ ^ 2 :=
      mul_nonneg (mul_nonneg hC₀0 (norm_nonneg _)) (sq_nonneg _)
    have hresidual : ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1‖
        ≤ (C₀ * ‖h‖ * ‖k‖ ^ 2) * Real.exp Kstar :=
      expJet2_residual_bound g gi hC p v (v + k) Φ Φ' Qc h k hΦ0 hΦ'0 hQc0
        hΦderiv hΦ'deriv hQcderiv Kstar (C₀ * ‖h‖ * ‖k‖ ^ 2) hKstar0 hρ0 hKstar
        (fun t ht => hrbdU k hvk_le Φ' hΦ'0 hΦ'cont hΦ'deriv h t ht)
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, hfd_vk, hfdv,
      expJetD2_apply, hval]
    simp only [ContinuousLinearMap.comp_apply]
    have hπsub : expJetPi (Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1)
        = expJetPi (Φ' 1 (expJetIota h)) - expJetPi (Φ 1 (expJetIota h)) - expJetPi (Qc 1) := by
      rw [map_sub, map_sub]
    calc ‖expJetPi (Φ' 1 (expJetIota h)) - expJetPi (Φ 1 (expJetIota h)) - expJetPi (Qc 1)‖
        = ‖expJetPi (Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1)‖ := by rw [hπsub]
      _ ≤ ‖expJetPi (n := n)‖ * ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1‖ :=
          (expJetPi (n := n)).le_opNorm _
      _ ≤ 1 * ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1‖ :=
          mul_le_mul_of_nonneg_right expJetPi_opNorm_le (norm_nonneg _)
      _ = ‖Φ' 1 (expJetIota h) - Φ 1 (expJetIota h) - Qc 1‖ := one_mul _
      _ ≤ (C₀ * ‖h‖ * ‖k‖ ^ 2) * Real.exp Kstar := hresidual
      _ = Mc * ‖k‖ ^ 2 * ‖h‖ := by rw [hMcdef]; ring
  -- the little-o: `Mc·‖k‖² ≤ c·‖k‖` on the chosen radius.
  have hMc : Mc * ‖k‖ ≤ c := by
    have h1 : Mc * ‖k‖ ≤ Mc * (c / (Mc + 1)) := mul_le_mul_of_nonneg_left hkM hMc0
    have h2 : Mc * (c / (Mc + 1)) ≤ c := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0 : ℝ) < Mc + 1)]
      nlinarith [hc, hMc0]
    linarith
  show ‖fderiv ℝ (expMap g gi hC p) (v + k) - fderiv ℝ (expMap g gi hC p) v
      - expJetD2 g gi hC p v Φ hv.le hΦcont k‖ ≤ c * ‖k‖
  calc ‖fderiv ℝ (expMap g gi hC p) (v + k) - fderiv ℝ (expMap g gi hC p) v
          - expJetD2 g gi hC p v Φ hv.le hΦcont k‖
      ≤ Mc * ‖k‖ ^ 2 := hAk
    _ = (Mc * ‖k‖) * ‖k‖ := by ring
    _ ≤ c * ‖k‖ := mul_le_mul_of_nonneg_right hMc (norm_nonneg _)

end QIQTH.ExpMap
