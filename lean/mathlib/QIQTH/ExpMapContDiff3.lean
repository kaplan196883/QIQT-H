/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapContDiff2

/-!
# Toward `ContDiff³ exp_p` — Rung 3 of the `ContDiff³ exp_p` tower

The **D³F regularity layer** — a clean mirror of the landed D²F regularity bricks in
`ExpMapContDiff2.lean` (`contDiff_fderiv2_geodesicField`, `expJet_fderiv2_tube_bddAbove_unif`,
`expJet_fderiv2_lipschitzOnWith`), one Fréchet-derivative order higher.

`D³F := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))` is the third Fréchet derivative of the
geodesic field.  This file lands (all `[AF]`, no `sorry`):
* `contDiff_fderiv3_geodesicField` — `D³F` is `C^∞`.
* `expJet_fderiv3_tube_bddAbove_unif` — a uniform operator-norm bound of `D³F` over the confined
  `[0,1]` geodesic tube.
* `expJet_fderiv3_lipschitzOnWith` — `D³F` is Lipschitz on the confined tube ball.

These are the Jet₃ analytic ingredients at the level of existence + smoothness (the coefficients of
the third-variation ODE), the exact `D³F` analogs of the Jet₂ (`D²F`) regularity bricks.

## Honest firewall (binding)

**What is proven here:** the `C^∞`-smoothness of `D³F`, plus its uniform bound and Lipschitz
regularity on the confined `[0,1]` tube — the Jet₃ well-posedness data.

**What is NOT closed:** this does NOT build the Jet₃ third-variation fundamental solution, does NOT
discharge `ContDiff² (fderiv exp_p)` / `ContDiff³ exp_p`, does NOT reach `κ = 1/6`, the heat-kernel
parametrix, or `a₁ = R/6`, and is NOT numerical-`G` / the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

-- The codomain of `D³F` is a TRIPLY-nested continuous-linear-map space
-- `E →L E →L E →L E`; its normed-group instance chains one level deeper than the D² case, so we
-- raise the pending-instance synthesis depth to let it resolve.
set_option maxSynthPendingDepth 3

variable {n : ℕ}

/-! ### The Jet₃ analytic ingredient `D³F` — existence and `C^∞`-smoothness -/

/-- The geodesic field's **third Fréchet derivative** `D³F = fderiv (fderiv (fderiv F))` is `C^∞`.
    (`D²F = fderiv (fderiv F)` is `C^∞` by `contDiff_fderiv2_geodesicField`; differentiate once
    more.) -/
theorem contDiff_fderiv3_geodesicField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) :=
  (contDiff_fderiv2_geodesicField g gi hC).fderiv_right le_top

/-- **Uniform operator-norm bound of `D³F` over the `[0,1]` confined tube.**  The direct `D³F`
    analog of `expJet_fderiv2_tube_bddAbove_unif` (which bounds the second derivative `D²F`).
    Confinement (`expTube_spec`) puts every tube point `expTube p v t` (for `‖v‖ ≤ expRho`,
    `t ∈ [0,1]`) in a FIXED closed ball around `(p, 0)`; `D³F = fderiv (fderiv (fderiv F))` is
    continuous (`contDiff_fderiv3_geodesicField`), so a continuous function on that compact ball is
    bounded, yielding a uniform `Kstar`.

    As in the D² version, the bound is routed through the ℝ-valued norm function `q ↦ ‖D³F q‖` to
    avoid the (now TRIPLY-)nested-CLM topology diamond on the codomain
    `E →L[ℝ] E →L[ℝ] E →L[ℝ] E`. -/
theorem expJet_fderiv3_tube_bddAbove_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ Kstar : ℝ, 0 ≤ Kstar ∧ ∀ v : Point n, ‖v‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar := by
  have hC₀ := expConst_nonneg g gi hC p
  have hρ0 : 0 ≤ expRho g gi hC p := (expRho_pos g gi hC p).le
  set Rb : ℝ := expConst g gi hC p * expRho g gi hC p with hRbdef
  -- Route through the ℝ-valued norm function `q ↦ ‖D³F q‖` to avoid the nested-CLM topology
  -- diamond that `exists_bound_of_continuousOn` hits on the codomain `E →L[ℝ] E →L[ℝ] E →L[ℝ] E`.
  have hdFcont : Continuous (fun q => ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) q‖) :=
    ((contDiff_fderiv2_geodesicField g gi hC).continuous_fderiv (by simp)).norm
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
  calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖
      ≤ C := le_trans (le_abs_self _) (by simpa using hbnd)
    _ ≤ max C 0 := le_max_left _ _

/-- **`D³F` is Lipschitz on the confined tube ball.**  The direct `D³F` analog of
    `expJet_fderiv2_lipschitzOnWith`.  `D³F = fderiv (fderiv (fderiv F))` is `C^∞`
    (`contDiff_fderiv3_geodesicField`), hence `C¹`, and the tube ball
    `Metric.closedBall (p,0) (expConst · expRho)` is compact and convex; a `C¹` map is Lipschitz on
    a compact convex set (`ContDiffOn.exists_lipschitzOnWith`). -/
theorem expJet_fderiv3_lipschitzOnWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ Ld3f : NNReal, LipschitzOnWith Ld3f
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) :=
  ((contDiff_fderiv3_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)

/-! ### Sub-brick R3-source — the inhomogeneous source `Θ₃^{hkl}` of the Jet₃ third-variation ODE

The third variation `R^{hkl}(t)` of the flow (vector-valued in `Point n × Point n`) solves the
INHOMOGENEOUS linear ODE `R'(t) = DF(Y_v t)·R(t) + Θ₃^{hkl}(t)`, `R(0) = 0`, whose homogeneous part
is propagated by the built first-variation fundamental solution `Φ_v` (`expJetFund`).  The
inhomogeneous SOURCE is the FOUR-term third-variation inhomogeneity (the `t`-derivative of the Jet₂
source, product/chain rule): one pure `D³F` term contracting three first variations, plus the three
`D²F` cross-terms pairing one first variation `P^h = Φ(ι·)` against the appropriate second variation
`Q^{··}`:
`Θ₃^{hkl}(t) = D³F(Y_v t)( P^h(t) )( P^k(t) )( P^l(t) )`
`            + D²F(Y_v t)( P^h(t) )( Q^{kl}(t) )`
`            + D²F(Y_v t)( P^k(t) )( Q^{hl}(t) )`
`            + D²F(Y_v t)( P^l(t) )( Q^{hk}(t) )`,
with `D³F = fderiv (fderiv (fderiv F))` (`contDiff_fderiv3_geodesicField`),
`D²F = fderiv (fderiv F)` (`contDiff_fderiv2_geodesicField`), `Y_v t = expTube p v t`,
`ι = expJetIota` (`h ↦ (0,h)`), `Φ` the abstract first-variation propagator and `Q^{kl},Q^{hl},Q^{hk}`
the abstract second-variation solutions (parametrized, exactly as `Φ`/`Q` are in the Jet₂ source
`expJet2Rhs`, since they are `∃`-objects of `expJetFund`/`expJet2Fund`, not global defs).

This sub-brick delivers the source `def` plus its `[0,1]` regularity (continuity + a uniform norm
bound) — the well-posedness data the (next) `R^{hkl}` construction consumes.  It does NOT build
`R^{hkl}` (the multi-week vector-valued PL tower). -/

/-- **Generic CLM-application norm bound.**  `‖C a‖ ≤ KC · Ka` (local copy of the private
    `ExpMapContDiff2` helper). -/
private theorem clmApply_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : E →L[ℝ] F) (a : E) {KC Ka : ℝ} (hKC : 0 ≤ KC)
    (hC : ‖C‖ ≤ KC) (ha : ‖a‖ ≤ Ka) : ‖C a‖ ≤ KC * Ka :=
  (C.le_opNorm a).trans (mul_le_mul hC ha (norm_nonneg _) hKC)

/-- **Generic bilinear CLM-application norm bound.**  `‖B a b‖ ≤ KB · Ka · Kb` (local copy of the
    private `ExpMapContDiff2` helper). -/
private theorem clmApply2_norm_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (a : E) (b : F) {KB Ka Kb : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) : ‖B a b‖ ≤ KB * Ka * Kb :=
  (B.le_opNorm₂ a b).trans
    (mul_le_mul (mul_le_mul hB ha (norm_nonneg _) hKB) hb (norm_nonneg _) (mul_nonneg hKB hKa))

/-- **Generic trilinear CLM-application norm bound.**  `‖B a b c‖ ≤ KB · Ka · Kb · Kc`.  The direct
    one-order-higher analog of `clmApply2_norm_le`: apply the outer `B` to `a` (`clmApply_norm_le`),
    then the resulting bilinear CLM `B a` to `b, c` (`clmApply2_norm_le`).  Kept `F`-generic (abstract
    normed spaces, no giant tube atoms) so the triply-nested-CLM `whnf` never fires here. -/
private theorem clmApply3_norm_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] H) (a : E) (b : F) (c : G) {KB Ka Kb Kc : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) (hc : ‖c‖ ≤ Kc) :
    ‖B a b c‖ ≤ KB * Ka * Kb * Kc :=
  clmApply2_norm_le (B a) b c (mul_nonneg hKB hKa) hKb (clmApply_norm_le B a hKB hB ha) hb hc

/-- **The inhomogeneous source term `Θ₃^{hkl}(t)` of the Jet₃ third-variation ODE.**  The four-term
    third-variation inhomogeneity (one pure `D³F` contraction of three first variations `Φ(ι·)`, plus
    three `D²F` cross-terms pairing a first variation against a second variation `Qkl/Qhl/Qhk`), the
    one-order-higher analog of `expJet2Rhs`.  `D³F x : E →L E →L E →L E` applied to three vectors and
    `D²F x : E →L E →L E` applied to two vectors both land in `E = Point n × Point n`. -/
noncomputable def expJet3Rhs (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n)) (h k l : Point n) (t : ℝ) :
    Point n × Point n :=
  (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l))
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Qkl t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Qhl t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Φ t (expJetIota l)) (Qhk t)

@[simp] theorem expJet3Rhs_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n)) (h k l : Point n) (t : ℝ) :
    expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l))
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Qkl t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Qhl t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota l)) (Qhk t) := rfl

/-- **`Θ₃^{hkl}` is continuous on `[0,1]`.**  For `‖v‖ ≤ expRho`, `Φ`/`Qkl`/`Qhl`/`Qhk` all continuous
    on `[0,1]`: `D³F`/`D²F` are continuous (`contDiff_fderiv3/2_geodesicField`), `t ↦ Y_v t` is
    continuous on `[0,1]` (`expTube_continuousOn`), so `t ↦ D³F(Y_v t)`, `t ↦ D²F(Y_v t)` are
    continuous there; each first variation `t ↦ Φ t (ι·)` is continuous (`ContinuousOn.clm_apply`
    against a fixed vector); the multi-CLM applications assemble via `ContinuousOn.clm_apply` (thrice
    for the `D³F` term, twice for each `D²F` cross-term); `ContinuousOn.add` combines the 4 terms. -/
theorem expJet3Rhs_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hΦ : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n) :
    ContinuousOn (fun t => expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) (Set.Icc (0 : ℝ) 1) := by
  -- `t ↦ D³F(Y_v t)` and `t ↦ D²F(Y_v t)` continuous on `[0,1]`.
  have hD3cont : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) :=
    (contDiff_fderiv3_geodesicField g gi hC).continuous
  have hD2cont : Continuous (fderiv ℝ (fderiv ℝ (geodesicField g gi))) :=
    (contDiff_fderiv2_geodesicField g gi hC).continuous
  have hYcont := expTube_continuousOn g gi hC p v hv
  have hA3 : ContinuousOn
      (fun t => fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Set.Icc (0 : ℝ) 1) := hD3cont.comp_continuousOn hYcont
  have hA2 : ContinuousOn
      (fun t => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Set.Icc (0 : ℝ) 1) := hD2cont.comp_continuousOn hYcont
  -- first variations `t ↦ Φ t (ι·)`.
  have hPh : ContinuousOn (fun t => Φ t (expJetIota h)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  have hPk : ContinuousOn (fun t => Φ t (expJetIota k)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  have hPl : ContinuousOn (fun t => Φ t (expJetIota l)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  -- assemble the four terms.
  have ht1 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l))) (Set.Icc (0 : ℝ) 1) :=
    ((hA3.clm_apply hPh).clm_apply hPk).clm_apply hPl
  have ht2 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Qkl t)) (Set.Icc (0 : ℝ) 1) :=
    (hA2.clm_apply hPh).clm_apply hQkl
  have ht3 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Qhl t)) (Set.Icc (0 : ℝ) 1) :=
    (hA2.clm_apply hPk).clm_apply hQhl
  have ht4 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota l)) (Qhk t)) (Set.Icc (0 : ℝ) 1) :=
    (hA2.clm_apply hPl).clm_apply hQhk
  simpa only [expJet3Rhs_apply] using ((ht1.add ht2).add ht3).add ht4

/-- **Uniform `[0,1]` norm bound of `Θ₃^{hkl}`.**  For `‖v‖ ≤ expRho`, `t ∈ [0,1]`, given the `D³F`
    tube bound `Kstar3` (`expJet_fderiv3_tube_bddAbove_unif`), the `D²F` tube bound `Kstar2`
    (`expJet_fderiv2_tube_bddAbove_unif`), a `[0,1]`-bound `Cphi` on `‖Φ t‖`, and `[0,1]`-bounds
    `Cq_kl`/`Cq_hl`/`Cq_hk` on `‖Qkl t‖`/`‖Qhl t‖`/`‖Qhk t‖`:
    `‖Θ₃^{hkl}(t)‖ ≤ Kstar3·(Cφ‖h‖)(Cφ‖k‖)(Cφ‖l‖) + Kstar2·(Cφ‖h‖)·Cq_kl + Kstar2·(Cφ‖k‖)·Cq_hl
                    + Kstar2·(Cφ‖l‖)·Cq_hk`.
    Triple `le_opNorm` via `clmApply3_norm_le` for the `D³F` term, double `le_opNorm` via
    `clmApply2_norm_le` for each `D²F` cross-term, and `‖ι m‖ ≤ ‖m‖` (`expJetIota` norm-`≤ 1`).  The
    ODE well-posedness bound the (next) `R^{hkl}` construction consumes. -/
theorem expJet3Rhs_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n)) (h k l : Point n)
    (Kstar3 Kstar2 Cphi Cq_kl Cq_hl Cq_hk : ℝ)
    (hKstar30 : 0 ≤ Kstar3) (hKstar20 : 0 ≤ Kstar2) (hCphi0 : 0 ≤ Cphi)
    (hKstar3 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3)
    (hKstar2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2)
    (hCphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi)
    (hCqkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq_kl)
    (hCqhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhl t‖ ≤ Cq_hl)
    (hCqhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhk t‖ ≤ Cq_hk)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t‖
      ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖)
        + Kstar2 * (Cphi * ‖h‖) * Cq_kl
        + Kstar2 * (Cphi * ‖k‖) * Cq_hl
        + Kstar2 * (Cphi * ‖l‖) * Cq_hk := by
  set D3 := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t) with hD3
  set D2 := fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t) with hD2
  -- first-variation vector bounds `‖Φ t (ι m)‖ ≤ Cphi·‖m‖`.
  have hP : ∀ m : Point n, ‖Φ t (expJetIota m)‖ ≤ Cphi * ‖m‖ := by
    intro m
    have hιm : ‖expJetIota (n := n) m‖ ≤ ‖m‖ := by
      refine ((expJetIota (n := n)).le_opNorm m).trans ?_
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg m)
    calc ‖Φ t (expJetIota m)‖ ≤ ‖Φ t‖ * ‖expJetIota (n := n) m‖ := (Φ t).le_opNorm _
      _ ≤ Cphi * ‖m‖ := mul_le_mul (hCphi t ht) hιm (norm_nonneg _) hCphi0
  have hnn : ∀ m : Point n, 0 ≤ Cphi * ‖m‖ := fun m => mul_nonneg hCphi0 (norm_nonneg _)
  -- the four term-wise bounds.
  have hb1 : ‖D3 (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l))‖
      ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) (hnn k) (hKstar3 t ht) (hP h) (hP k) (hP l)
  have hb2 : ‖D2 (Φ t (expJetIota h)) (Qkl t)‖ ≤ Kstar2 * (Cphi * ‖h‖) * Cq_kl :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn h) (hKstar2 t ht) (hP h) (hCqkl t ht)
  have hb3 : ‖D2 (Φ t (expJetIota k)) (Qhl t)‖ ≤ Kstar2 * (Cphi * ‖k‖) * Cq_hl :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn k) (hKstar2 t ht) (hP k) (hCqhl t ht)
  have hb4 : ‖D2 (Φ t (expJetIota l)) (Qhk t)‖ ≤ Kstar2 * (Cphi * ‖l‖) * Cq_hk :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn l) (hKstar2 t ht) (hP l) (hCqhk t ht)
  -- combine via triangle inequality (`Θ₃ = t₁ + t₂ + t₃ + t₄`).
  rw [expJet3Rhs_apply, ← hD3, ← hD2]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hb3)) hb4)

end QIQTH.ExpMap
