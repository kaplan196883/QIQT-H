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

/-! ### D³F symmetry — the third derivative is a symmetric trilinear map

Mathlib supplies second-derivative symmetry only (`ContDiffAt.isSymmSndFDerivAt`); it has **no**
general "iterated Fréchet derivative is symmetric under all argument permutations" API.  We bridge
this gap for `D³F` of the (`C^∞`) geodesic field by proving the two adjacent transpositions that
generate the full symmetric group `S₃`:
* `fderiv3_geodesicField_symm_ab` — swap the FIRST two arguments, obtained by applying the
  second-derivative-symmetry theorem to the (`C^∞`) function `DF = fderiv F` (`D³F = D²(DF)` is
  symmetric in its two `D²`-slots);
* `fderiv3_geodesicField_symm_bc` — swap the LAST two arguments, obtained by differentiating the
  pointwise `D²F`-symmetry `D²F y = (D²F y).flip`: the flip is a linear isometry, so it commutes with
  `fderiv` (`LinearIsometryEquiv.comp_fderiv`), giving `D³F x a = (D³F x a).flip`.
Composing the two yields every permutation (e.g. the cyclic `l h k ↦ h k l` needed by the Rung-3
cancellation).  This is the D³F-symmetry prerequisite of the quadratic residual bound. -/

/-- **`D³F` is symmetric in its first two arguments.**  `D³F(x) a b c = D³F(x) b a c`.
    `D³F = D²(DF)` where `DF = fderiv F` is `C^∞` (`contDiff_fderiv_geodesicField`); its second
    derivative is a symmetric bilinear map (`ContDiffAt.isSymmSndFDerivAt`), i.e. `D³F(x) a b = D³F(x)
    b a` as elements of `E →L F`; apply that CLM equality at `c`. -/
theorem fderiv3_geodesicField_symm_ab (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x) a b c
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x) b a c :=
  DFunLike.congr_fun
    (((contDiff_fderiv_geodesicField g gi hC).contDiffAt.isSymmSndFDerivAt le_top) a b) c

/-- **`D³F` is symmetric in its last two arguments.**  `D³F(x) a b c = D³F(x) a c b`.
    For each `y`, `D²F(y)` is a symmetric bilinear map (`fderiv2_geodesicField_symm`), i.e. `D²F(y) =
    (D²F(y)).flip`; hence `D²F = flipₗᵢ ∘ D²F` as functions.  `flipₗᵢ` is a linear isometry, so it
    commutes with the outer `fderiv` (`LinearIsometryEquiv.comp_fderiv`): `D³F(x) = (flipₗᵢ).comp
    (D³F(x))`, giving `D³F(x) a = (D³F(x) a).flip` and thus the swap of `b,c`. -/
theorem fderiv3_geodesicField_symm_bc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x) a b c
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x) a c b := by
  set iso := ContinuousLinearMap.flipₗᵢ ℝ (Point n × Point n) (Point n × Point n)
    (Point n × Point n) with hiso
  -- `D²F = ⇑iso ∘ D²F` (pointwise flip-invariance of the symmetric bilinear `D²F y`).
  have hcomp : (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      = ⇑iso ∘ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) := by
    funext y
    simp only [Function.comp_apply, hiso, ContinuousLinearMap.coe_flipₗᵢ]
    refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.flip_apply]
    exact (fderiv2_geodesicField_symm g gi hC y w u).symm
  -- differentiate: `D³F x = (↑iso).comp (D³F x)` since `iso` (a linear isometry) commutes with fderiv.
  have key : fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x
      = (iso : ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n))
            →L[ℝ] ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n))).comp
          (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x) := by
    conv_lhs => rw [hcomp]
    exact iso.comp_fderiv
  -- read off the (b,c)-swap.
  have h1 := DFunLike.congr_fun key a
  rw [ContinuousLinearMap.comp_apply] at h1
  conv_lhs => rw [h1]
  simp only [hiso, LinearIsometryEquiv.coe_coe'', ContinuousLinearMap.coe_flipₗᵢ,
    ContinuousLinearMap.flip_apply]

/-- **`D³F` is fully symmetric: the cyclic permutation `(a,b,c) ↦ (b,c,a)`.**  `D³F(x) a b c = D³F(x)
    b c a`, obtained by composing the two adjacent transpositions
    (`fderiv3_geodesicField_symm_ab` then `_bc`).  This is the permutation the Rung-3 cancellation
    uses to identify the pure `D³F` contraction of the three first variations with its
    `expJet3Rhs` counterpart. -/
theorem fderiv3_geodesicField_symm_cyc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x) a b c
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x) b c a := by
  rw [fderiv3_geodesicField_symm_ab g gi hC x a b c,
    fderiv3_geodesicField_symm_bc g gi hC x b a c]

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

/-! ### Sub-brick R3-fund — the Jet₃ third-variation fundamental solution `R^{hkl}`

The third variation `R^{hkl}(t)` (VECTOR-valued in `Point n × Point n`) solves the INHOMOGENEOUS
linear ODE `R'(t) = DF(Y_v t)(R t) + Θ₃^{hkl}(t)`, `R(0) = 0`, with `Θ₃ = expJet3Rhs …` the R3-source
term.  This is a CLOSE MIRROR of the landed Jet₂ chain (`expJet2Fund*` in `ExpMapContDiff2.lean`):
the affine field `F₃ t R := DF(Y_v t)(R) + Θ₃^{hkl}(t)` has the SAME structure as `F₂` — the source is
GLOBAL (constant in `R`, not propagator-scaled), so the `IsPicardLindelof` instantiation, the shifted
solver, and the endpoint-matching glue are identical to the Jet₂ version, only the source symbol
changes.  Delivered in order: `expJet3Fund_local` → `expJet3Field_continuousOn` → `expJet3Fund_shifted`
→ `expJet3Fund_shifted_integral` → `expJet3Fund_glue` (private) → `expJet3Fund` (the `[0,1]` capstone).

`Φ` is the abstract first-variation propagator and `Qkl,Qhl,Qhk` the abstract second-variation
solutions (parametrized, as in `expJet3Rhs`); all carry `ContinuousOn (Icc 0 1)` hypotheses (needed
for `expJet3Rhs_continuousOn`). -/

set_option maxHeartbeats 1000000 in
/-- **R3-fund LOCAL — the LOCAL Jet₃ third-variation solution `R^{hkl}`.**  For `‖v‖ ≤ expRho` and
    `Φ`/`Qkl`/`Qhl`/`Qhk` continuous on `[0,1]`, there is a short time `T > 0` and a VECTOR-valued
    curve `R : ℝ → Point n × Point n` with `R 0 = 0` solving the INHOMOGENEOUS linear Jet₃ ODE
    `R'(t) = DF(Y_v t)(R t) + Θ₃^{hkl}(t)` on `[0, T]`, where `DF = fderiv (geodesicField g gi)`,
    `Y_v t = expTube p v t`, and `Θ₃^{hkl} = expJet3Rhs …` is the R3-source term.  Verbatim mirror of
    `expJet2Fund_local`: the affine vector-normed `IsPicardLindelof` instantiation of
    `F₃ t R := DF(Y_v t)(R) + Θ₃^{hkl}(t)` on `closedBall(0,1)`, centred at `R₀ = 0` (source constant
    in `R` ⟹ `KdF`-Lipschitz; source continuous on compact `[0,1]` ⟹ `Cθ`-bounded). -/
theorem expJet3Fund_local (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n) :
    ∃ T > (0 : ℝ), ∃ R : ℝ → (Point n × Point n),
      R 0 = 0 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt R
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) (Set.Icc (0 : ℝ) T) t := by
  obtain ⟨KdF, hKdF0, hKdF⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  -- `Θ₃^{hkl}` is continuous on the compact `[0,1]`, hence uniformly bounded by some `Cθ ≥ 0`.
  have hΘcont : ContinuousOn (fun t => expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
      (Set.Icc (0 : ℝ) 1) :=
    expJet3Rhs_continuousOn g gi hC p v hv Φ Qkl Qhl Qhk hΦcont hQkl hQhl hQhk h k l
  obtain ⟨Cθ0, hCθ0⟩ := isCompact_Icc.exists_bound_of_continuousOn hΘcont
  set Cθ : ℝ := max Cθ0 0 with hCθdef
  have hCθnn : 0 ≤ Cθ := le_max_right _ _
  have hCθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t‖ ≤ Cθ :=
    fun t ht => (hCθ0 t ht).trans (le_max_left _ _)
  -- the affine vector field `F₃ t R = DF(Y_v t)(R) + Θ₃^{hkl}(t)`.
  set F₃ : ℝ → (Point n × Point n) → (Point n × Point n) :=
    fun t R => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) R
      + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t with hF₃
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
  have hpl : IsPicardLindelof F₃
      (tmin := (0 : ℝ)) (tmax := T) ⟨0, ⟨le_refl 0, hT0.le⟩⟩
      (0 : Point n × Point n) 1 0 Lnn Knn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in `R` on `closedBall(0,1)` with constant `KdF` (source drops out).
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro M _ N _
      simp only [dist_eq_norm, hKnn]
      have hsub : F₃ t M - F₃ t N
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (M - N) := by
        simp only [hF₃, map_sub]; abel
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
    · -- uniform bound `‖F₃ t R‖ ≤ KdF + Cθ` on `closedBall(0,1)`.
      intro t ht x hx
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      have hxnorm : ‖x‖ ≤ 1 := by
        have hd := Metric.mem_closedBall.mp hx
        rw [dist_zero_right] at hd
        simpa using hd
      show ‖F₃ t x‖ ≤ KdF + Cθ
      calc ‖F₃ t x‖
          = ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t‖ := by rw [hF₃]
        _ ≤ ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x‖
              + ‖expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t‖ := norm_add_le _ _
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
  simpa only [hF₃] using hd

/-- **Continuity of the Jet₃ inhomogeneous field** `s ↦ DF(Y_v s)(R s) + Θ₃^{hkl}(s)` on any
    `A ⊆ [0,1]` where `R` is continuous.  Direct mirror of `expJet2Field_continuousOn`, source
    continuity via `expJet3Rhs_continuousOn`. -/
theorem expJet3Field_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n)
    {A : Set ℝ} (hA : A ⊆ Set.Icc (0 : ℝ) 1)
    {R : ℝ → (Point n × Point n)} (hR : ContinuousOn R A) :
    ContinuousOn (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
      + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) A := by
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hDFtube : ContinuousOn
      (fun s => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) A :=
    (hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)).mono hA
  have h1 : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)) A :=
    hDFtube.clm_apply hR
  have h2 : ContinuousOn (fun s => expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) A :=
    (expJet3Rhs_continuousOn g gi hC p v hv Φ Qkl Qhl Qhk hΦcont hQkl hQhl hQhk h k l).mono hA
  exact h1.add h2

set_option maxHeartbeats 1000000 in
/-- **R3-fund SHIFTED — the shifted Jet₃ third-variation solver from arbitrary vector IC `x₀`.**
    Direct mirror of `expJet2Fund_shifted`: the vector-normed `IsPicardLindelof` instantiation of
    `F₃ t R := DF(Y_v t)(R) + Θ₃^{hkl}(t)` centred at `x₀` on `closedBall(x₀, a)` with the same
    linear-in-`x₀` radius `a := 2·(KdF·‖x₀‖·T + Cθ·T) + 1`.  The reusable brick of the `[0,1]`
    concatenation. -/
theorem expJet3Fund_shifted (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n)
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
             + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) (Set.Icc t₀ (t₀ + T)) t := by
  -- `Θ₃^{hkl}` is continuous on the compact `[0,1]`, hence uniformly bounded by some `Cθ ≥ 0`.
  have hΘcont : ContinuousOn (fun t => expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
      (Set.Icc (0 : ℝ) 1) :=
    expJet3Rhs_continuousOn g gi hC p v hv Φ Qkl Qhl Qhk hΦcont hQkl hQhl hQhk h k l
  obtain ⟨Cθ0, hCθ0⟩ := isCompact_Icc.exists_bound_of_continuousOn hΘcont
  set Cθ : ℝ := max Cθ0 0 with hCθdef
  have hCθnn : 0 ≤ Cθ := le_max_right _ _
  have hCθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t‖ ≤ Cθ :=
    fun t ht => (hCθ0 t ht).trans (le_max_left _ _)
  -- the affine vector field `F₃ t R = DF(Y_v t)(R) + Θ₃^{hkl}(t)`.
  set F₃ : ℝ → (Point n × Point n) → (Point n × Point n) :=
    fun t R => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) R
      + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t with hF₃
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
  have hpl : IsPicardLindelof F₃
      (tmin := t₀) (tmax := t₀ + T) ⟨t₀, ⟨le_refl t₀, by linarith⟩⟩
      x₀ Ann 0 Lnn Knn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in `R` with constant `KdF` (source drops out).
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro M _ N _
      simp only [dist_eq_norm, hKnn]
      have hsub : F₃ t M - F₃ t N
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (M - N) := by
        simp only [hF₃, map_sub]; abel
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
    · -- uniform bound `‖F₃ t x‖ ≤ L` on `closedBall(x₀, a)`.
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
      show ‖F₃ t x‖ ≤ Lval
      calc ‖F₃ t x‖
          = ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t‖ := by rw [hF₃]
        _ ≤ ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x‖
              + ‖expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t‖ := norm_add_le _ _
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
  simpa only [hF₃] using hd

set_option maxHeartbeats 1000000 in
/-- **R3-fund SHIFTED-INTEGRAL — the shifted Jet₃ solver in INTEGRAL form (the gluing brick).**
    Direct mirror of `expJet2Fund_shifted_integral`: additionally packages the LOCAL INTEGRAL
    EQUATION `R(t) = x₀ + ∫_{t₀}^t (DF(Y_v s)(R s) + Θ₃^{hkl}(s)) ds` via FTC-2.  Since the source is
    GLOBAL, the `[0,1]` concatenation glues these directly by ENDPOINT VALUE — no right-composition. -/
theorem expJet3Fund_shifted_integral (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n)
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
             + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) (Set.Icc t₀ (t₀ + T)) t) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + T),
        R t = x₀ + ∫ s in t₀..t,
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
             + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s)) := by
  obtain ⟨R, hR0, hRd⟩ :=
    expJet3Fund_shifted g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l
      KdF hKdF0 hKdF t₀ T ht₀ hT hsum hstep x₀
  have hIccsub : Set.Icc t₀ (t₀ + T) ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc ht₀ hsum
  have hRcont : ContinuousOn R (Set.Icc t₀ (t₀ + T)) := fun s hs => (hRd s hs).continuousWithinAt
  have hintegrand : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) (Set.Icc t₀ (t₀ + T)) :=
    expJet3Field_continuousOn g gi hC p v hv Φ Qkl Qhl Qhk hΦcont hQkl hQhl hQhk h k l
      hIccsub hRcont
  refine ⟨R, hR0, hRcont, hRd, fun t ht => ?_⟩
  have hab : t₀ ≤ t := ht.1
  have hsubt : Set.Icc t₀ t ⊆ Set.Icc t₀ (t₀ + T) := Set.Icc_subset_Icc_right ht.2
  have hcont : ContinuousOn R (Set.Icc t₀ t) := hRcont.mono hsubt
  have hderiv : ∀ x ∈ Set.Ioo t₀ t,
      HasDerivWithinAt R
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x)) (R x)
           + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l x) (Set.Ioi x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc t₀ (t₀ + T) := hsubt ⟨hx.1.le, hx.2.le⟩
    have hnhds : Set.Icc t₀ (t₀ + T) ∈ nhds x :=
      Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 ht.2)
    exact ((hRd x hxIcc).hasDerivAt hnhds).hasDerivWithinAt
  have hint : IntervalIntegrable
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) MeasureTheory.volume t₀ t :=
    (hintegrand.mono hsubt).intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint
  rw [hR0] at hftc
  rw [hftc]; abel

set_option maxHeartbeats 2000000 in
/-- **The partition induction (endpoint-matching concatenation) for the Jet₃ solver.**  Direct mirror
    of `expJet2Fund_glue`: for every `j ≤ N` builds a curve `R` on `[0, j/N]` with `R 0 = 0`,
    continuous, obeying the GLOBAL integral equation `R t = 0 + ∫₀ᵗ (DF(Y_v s)(R s) + Θ₃^{hkl}(s)) ds`,
    by induction gluing `R_j` and the shifted solver `U` at the endpoint value `R_j(j/N)`; the global
    source pastes directly. -/
private theorem expJet3Fund_glue (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n)
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
               + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s)) := by
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
    obtain ⟨Rj, hRj0, hRjcont, hRjint⟩ := ih (Nat.le_of_succ_le hk)
    have hτnn : 0 ≤ (m : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg m) hNpos.le
    have hInpos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hsucc : ((m + 1 : ℕ) : ℝ) / (N : ℝ) = (m : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
      push_cast; ring
    have hτm1le1 : (m : ℝ) / (N : ℝ) + 1 / (N : ℝ) ≤ 1 :=
      hsucc ▸ (by rw [div_le_one hNpos]; exact_mod_cast hk)
    obtain ⟨U, hU0, hUcont, hUderiv, hUint⟩ :=
      expJet3Fund_shifted_integral g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l
        KdF hKdF0 hKdF
        ((m : ℝ) / (N : ℝ)) (1 / (N : ℝ)) hτnn hInpos hτm1le1 hstep (Rj ((m : ℝ) / (N : ℝ)))
    set R' : ℝ → (Point n × Point n) :=
      fun t => if t ≤ (m : ℝ) / (N : ℝ) then Rj t else U t with hR'def
    have hR'_lo : ∀ s, s ≤ (m : ℝ) / (N : ℝ) → R' s = Rj s := by
      intro s hs; rw [hR'def]; exact if_pos hs
    have hR'_hi : ∀ s, ¬ (s ≤ (m : ℝ) / (N : ℝ)) → R' s = U s := by
      intro s hs; rw [hR'def]; exact if_neg hs
    -- EqOn on the two closed pieces (junction value matches: `Rj(τ_m) = x₀ = U(τ_m)`).
    have hEqLo : Set.EqOn R' Rj (Set.Icc (0 : ℝ) ((m : ℝ) / (N : ℝ))) :=
      fun s hs => hR'_lo s hs.2
    have hEqHi : Set.EqOn R' U
        (Set.Icc ((m : ℝ) / (N : ℝ)) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ))) := by
      intro s hs
      by_cases hsle : s ≤ (m : ℝ) / (N : ℝ)
      · have hseq : s = (m : ℝ) / (N : ℝ) := le_antisymm hsle hs.1
        rw [hR'_lo s hsle, hseq, hU0]
      · rw [hR'_hi s hsle]
    -- continuity of the glued curve on [0, (m+1)/N].
    have hR'cont : ContinuousOn R' (Set.Icc (0 : ℝ) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ))) := by
      have hunion : Set.Icc (0 : ℝ) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ))
          = Set.Icc (0 : ℝ) ((m : ℝ) / (N : ℝ))
            ∪ Set.Icc ((m : ℝ) / (N : ℝ)) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
        (Set.Icc_union_Icc_eq_Icc hτnn (by linarith)).symm
      rw [hunion]
      exact (hRjcont.congr hEqLo).union_of_isClosed (hUcont.congr hEqHi)
        isClosed_Icc isClosed_Icc
    -- integrand continuity for interval integrability.
    have hcontψ' : ContinuousOn
        (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
          + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s)
        (Set.Icc (0 : ℝ) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ))) :=
      expJet3Field_continuousOn g gi hC p v hv Φ Qkl Qhl Qhk hΦcont hQkl hQhl hQhk h k l
        (Set.Icc_subset_Icc_right hτm1le1) hR'cont
    rw [hsucc]
    refine ⟨R', ?_, hR'cont, ?_⟩
    · rw [hR'_lo 0 hτnn]; exact hRj0
    · intro t ht
      by_cases htle : t ≤ (m : ℝ) / (N : ℝ)
      · -- t in [0, τm]: the curve is Rj there.
        rw [hR'_lo t htle]
        have hcong : (∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s))
            = ∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
                 + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le ht.1] at hs
          show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s
            = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s
          rw [hR'_lo s (le_trans hs.2 htle)]
        rw [hcong]
        exact hRjint t ⟨ht.1, htle⟩
      · -- t in (τm, τm + 1/N]: the curve is U there.
        have htlt : (m : ℝ) / (N : ℝ) < t := not_le.mp htle
        have htmem : t ∈ Set.Icc ((m : ℝ) / (N : ℝ)) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
          ⟨htlt.le, ht.2⟩
        rw [hR'_hi t htle]
        have hII1 : IntervalIntegrable
            (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) MeasureTheory.volume 0 ((m : ℝ) / (N : ℝ)) :=
          (hcontψ'.mono (Set.Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hτnn
        have hII2 : IntervalIntegrable
            (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) MeasureTheory.volume ((m : ℝ) / (N : ℝ)) t :=
          (hcontψ'.mono (Set.Icc_subset_Icc hτnn ht.2)).intervalIntegrable_of_Icc htlt.le
        have hsplit : (∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s))
            = (∫ s in (0 : ℝ)..((m : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s))
              + ∫ s in ((m : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) :=
          (intervalIntegral.integral_add_adjacent_intervals hII1 hII2).symm
        -- first piece = Rj(τm) - 0.
        have hI1 : (∫ s in (0 : ℝ)..((m : ℝ) / (N : ℝ)),
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s))
            = Rj ((m : ℝ) / (N : ℝ)) - (0 : Point n × Point n) := by
          have hc : (∫ s in (0 : ℝ)..((m : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s))
              = ∫ s in (0 : ℝ)..((m : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
                   + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le hτnn] at hs
            show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s
              = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
                + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s
            rw [hR'_lo s hs.2]
          rw [hc, hRjint ((m : ℝ) / (N : ℝ)) ⟨hτnn, le_refl _⟩]; abel
        -- second piece = U(t) - Rj(τm).
        have hI2 : (∫ s in ((m : ℝ) / (N : ℝ))..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s))
            = U t - Rj ((m : ℝ) / (N : ℝ)) := by
          have hc : (∫ s in ((m : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s))
              = ∫ s in ((m : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (U s)
                   + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le htlt.le] at hs
            have hsmem : s ∈ Set.Icc ((m : ℝ) / (N : ℝ)) ((m : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
              ⟨hs.1, le_trans hs.2 ht.2⟩
            show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s
              = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (U s)
                + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s
            rw [hEqHi hsmem]
          rw [hc, hUint t htmem]; abel
        rw [hsplit, hI1, hI2]; abel

set_option maxHeartbeats 2000000 in
/-- **R3-fund CAPSTONE — the `[0,1]` Jet₃ third-variation fundamental solution `R^{hkl}`.**  Direct
    mirror of `expJet2Fund`: for `‖v‖ ≤ expRho` and `Φ`/`Qkl`/`Qhl`/`Qhk` continuous on `[0,1]`, there
    is a vector-valued curve `R : ℝ → Point n × Point n` with `R 0 = 0`, continuous on `[0,1]`, obeying
    the GLOBAL integral equation `R t = 0 + ∫₀ᵗ (DF(Y_v s)(R s) + Θ₃^{hkl}(s)) ds`, and — by FTC-1 — the
    inhomogeneous Jet₃ derivative law `HasDerivWithinAt R (DF(Y_v t)(R t) + Θ₃^{hkl}(t)) (Icc 0 1) t`
    for every `t ∈ [0,1]`.  Built by concatenating `N ≥ 2(KdF+1)` shifted solvers
    (`expJet3Fund_glue`).

    HONEST: the `[0,1]` inhomogeneous Jet₃ third-variation solution `R^{hkl}` (the third-variation
    transport of `h, k, l` through `D³F`/`D²F`).  It does NOT close `ContDiff² (fderiv exp_p)` /
    `ContDiff³ exp_p`, NOT the parameter-residual identity `∂_v Q = R`, NOT `κ = 1/6`, NOT
    numerical-`G`. -/
theorem expJet3Fund (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n) :
    ∃ R : ℝ → (Point n × Point n),
      R 0 = 0 ∧
      ContinuousOn R (Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        R t = (0 : Point n × Point n) + ∫ s in (0 : ℝ)..t,
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
             + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt R
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) (Set.Icc (0 : ℝ) 1) t) := by
  obtain ⟨KdF, hKdF0, hKdF⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (KdF + 1))
  have hpos : (0 : ℝ) < 2 * (KdF + 1) := by linarith
  have hNRpos : (0 : ℝ) < (N : ℝ) := hpos.trans_le hN
  have hN0 : 0 < N := by exact_mod_cast hNRpos
  have hstep : 2 * KdF * (1 / (N : ℝ)) ≤ 1 := by
    have h2 : 2 * KdF * (1 / (N : ℝ)) = (2 * KdF) / (N : ℝ) := by ring
    rw [h2, div_le_one hNRpos]; linarith [hN]
  obtain ⟨R, hR0, hRcont, hRint⟩ :=
    expJet3Fund_glue g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l
      KdF hKdF0 hKdF N hN0 hstep N le_rfl
  have hNN : (N : ℝ) / (N : ℝ) = 1 := div_self hNRpos.ne'
  rw [hNN] at hRcont hRint
  refine ⟨R, hR0, hRcont, hRint, ?_⟩
  have hψcont : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) (Set.Icc (0 : ℝ) 1) :=
    expJet3Field_continuousOn g gi hC p v hv Φ Qkl Qhl Qhk hΦcont hQkl hQhl hQhk h k l
      (subset_refl _) hRcont
  intro t ht
  have hII : IntervalIntegrable
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l s) MeasureTheory.volume 0 t :=
    (hψcont.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  haveI : Fact (t ∈ Set.Icc (0 : ℝ) 1) := ⟨ht⟩
  have hmeas := hψcont.stronglyMeasurableAtFilter_nhdsWithin (μ := MeasureTheory.volume)
    measurableSet_Icc t
  have hFTC := intervalIntegral.integral_hasDerivWithinAt_right (s := Set.Icc (0 : ℝ) 1)
    hII hmeas (hψcont t ht)
  have hconst := hFTC.const_add (0 : Point n × Point n)
  exact hconst.congr (fun s hs => hRint s hs) (hRint t ht)

/-! ### The Rung-3 reduction to the crux `ContDiff¹ (fderiv² exp_p)` -/

/-- **The Rung-3 reduction (proven).**  If the second-derivative map
    `v ↦ fderiv (fun w => fderiv exp_p w) v` is `ContDiffOn ℝ 1` on the ball `‖v‖ < expRho`, then
    `exp_p` is `ContDiffOn ℝ 3` there.  A clean mirror of the Rung-2 reduction
    (`expMap_contDiffOn_two_of_fderiv_contDiffOn_one`), one Fréchet-derivative order higher.

    Route (chain `contDiffOn_succ_of_fderivWithin` twice on the open ball, where
    `fderivWithin = fderiv` via `fderivWithin_of_isOpen`):
    * `F₁ := fderiv exp_p` is `ContDiffOn ℝ 1` on the ball (from Rung 2, `expMap_contDiffOn_two`
      through `ContDiffOn.fderiv_of_isOpen`), hence `DifferentiableOn`; with the crux `hfd2` (which is
      exactly `ContDiff¹ (fderivWithin F₁ s)` after `fderivWithin = fderiv`),
      `contDiffOn_succ_of_fderivWithin` gives `ContDiffOn ℝ 2 F₁`.
    * `exp_p` is `DifferentiableOn` (Rung 1, `expMap_contDiffOn_one`) with `fderivWithin exp_p s = F₁`;
      `contDiffOn_succ_of_fderivWithin` on the `ContDiffOn ℝ 2 F₁` gives `ContDiffOn ℝ (2+1) exp_p`,
      and `(2+1 : WithTop ℕ∞) = 3`.

    HONEST: this ISOLATES the remaining Rung-3 obligation (`ContDiff¹ (fderiv² exp_p)`, the Jet₂
    fundamental solution `Q_v` is `C¹` in `v`); it does NOT discharge it (that is the residual
    sub-campaign built on `expJet3Fund`). -/
theorem expMap_contDiffOn_three_of_fderiv2_contDiffOn_one
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hfd2 : ContDiffOn ℝ 1 (fun v => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) v)
      (Metric.ball (0 : Point n) (expRho g gi hC p))) :
    ContDiffOn ℝ 3 (expMap g gi hC p) (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  set s : Set (Point n) := Metric.ball (0 : Point n) (expRho g gi hC p) with hsdef
  -- `F₁ := fderiv exp_p` is `ContDiffOn ℝ 1` on the open ball (Rung 2), hence `DifferentiableOn`.
  have hF1cd1 : ContDiffOn ℝ 1 (fun v => fderiv ℝ (expMap g gi hC p) v) s :=
    (expMap_contDiffOn_two g gi hC p).fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hF1diff : DifferentiableOn ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) s :=
    hF1cd1.differentiableOn (by norm_num)
  -- Step 2: `ContDiffOn ℝ 2 F₁ s`.
  have hfw2 : ContDiffOn ℝ 1
      (fun v => fderivWithin ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) s v) s :=
    hfd2.congr (fun v hv => fderivWithin_of_isOpen Metric.isOpen_ball hv)
  have hF1cd2 : ContDiffOn ℝ (1 + 1) (fun w => fderiv ℝ (expMap g gi hC p) w) s :=
    contDiffOn_succ_of_fderivWithin hF1diff (by simp) hfw2
  have e2 : (1 : WithTop ℕ∞) + 1 = 2 := by norm_num
  rw [e2] at hF1cd2
  -- Step 3: `ContDiffOn ℝ 3 exp_p s`.
  have hdiff : DifferentiableOn ℝ (expMap g gi hC p) s :=
    (expMap_contDiffOn_one g gi hC p).differentiableOn (by norm_num)
  have hfw3 : ContDiffOn ℝ 2 (fun v => fderivWithin ℝ (expMap g gi hC p) s v) s :=
    hF1cd2.congr (fun v hv => fderivWithin_of_isOpen Metric.isOpen_ball hv)
  have hres : ContDiffOn ℝ (2 + 1) (expMap g gi hC p) s :=
    contDiffOn_succ_of_fderivWithin hdiff (by simp) hfw3
  have e3 : (2 : WithTop ℕ∞) + 1 = 3 := by norm_num
  rwa [e3] at hres

/-! ### Sub-brick R3-residual — the Jet₃ third-variation residual ODE identity (+ value bound)

Mirrors the Rung-2 `expJet2_residual_hasDerivWithinAt`/`expJet2_residual_bound`, one Fréchet order up.
Rung 2's residual was the first-variation difference vs the second variation
(`Φ'(ιh) − Φ(ιh) − Q`); Rung 3's residual is the second-variation difference vs the third variation
`S(t) = Q^{hk}_w(t) − Q^{hk}_v(t) − R^{hkl}_v(t)` (with `w := v + l`).  It obeys, on `[0,1]`,
`S'(t) = DF(Y_v t)(S t) + ρ(t)` with
`ρ(t) = [DF(Y_w t) − DF(Y_v t)](Q^{hk}_w t) + (Θ₂^{hk}_w(t) − Θ₂^{hk}_v(t) − Θ₃^{hkl}_v(t))`,
where `Θ₂ = expJet2Rhs …`, `Θ₃ = expJet3Rhs …`.  With `‖DF(Y_v)‖ ≤ Kstar` and `‖ρ‖ ≤ ρ₀` on `[0,1]`,
the vector Grönwall (`gronwall_vec_residual`) yields `‖S(1)‖ ≤ ρ₀·e^{Kstar}`.

`Qv`,`Qw` are the abstract Jet₂ second-variation solutions (carrying their `expJet2Fund` derivative
specs; `Φ`,`Φ'` are the first-variation propagators for `v`,`w`), `R` the abstract Jet₃ witness
(carrying its `expJet3Fund` derivative spec), and `Qkl`,`Qhl`,`Qhk` the second-variation inputs
feeding `R`'s source.  This is the LEVEL-UP mirror of the Rung-2 residual and — unlike Rung 2 — needs
no `clm_apply`, since `Qv`/`Qw`/`R` are already vector curves. -/

set_option maxHeartbeats 1000000 in
/-- **The Jet₃ residual ODE (residual identity).**  With `Qv`,`Qw` the Jet₂ second-variation witnesses
    for base parameters `v`,`w` (`Q'_· = DF(Y_· t)(Q_·) + Θ₂^{hk}_·(t)`) and `R` the Jet₃
    third-variation witness for `v` (`R' = DF(Y_v t)(R) + Θ₃^{hkl}_v(t)`), the parameter residual
    `S(t) = Qw(t) − Qv(t) − R(t)` obeys, on `[0,1]`,
    `S'(t) = DF(Y_v t)(S t) + ([DF(Y_w t) − DF(Y_v t)](Qw t) + (Θ₂^{hk}_w(t) − Θ₂^{hk}_v(t) − Θ₃^{hkl}_v(t)))`.

    Proof (mirror of `expJet2_residual_hasDerivWithinAt`, one order up): `Qw`,`Qv`,`R` solve their ODEs
    (`hQwd`,`hQvd`,`hRd`); `HasDerivWithinAt.sub` twice gives the natural difference derivative;
    `map_sub` (linearity of `DF(Y_v t)`) + `ContinuousLinearMap.sub_apply` + `abel` regroup it into the
    `DF(Y_v t)(S) + ρ` form (the extra `−Θ₃` and `−R` terms vs the Jet₂ algebra). -/
theorem expJet3_residual_hasDerivWithinAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qv Qw Qkl Qhl Qhk R : ℝ → (Point n × Point n)) (h k l : Point n)
    (hQvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qv
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qv t)
           + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) t)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qw
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
           + expJet2Rhs g gi hC p w Φ' h k t) (Set.Icc (0 : ℝ) 1) t)
    (hRd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt R
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
           + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) (Set.Icc (0 : ℝ) 1) t)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => Qw s - Qv s - R s)
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t - Qv t - R t)
        + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
             - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
           + (expJet2Rhs g gi hC p w Φ' h k t
              - expJet2Rhs g gi hC p v Φ h k t
              - expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)))
      (Set.Icc (0 : ℝ) 1) t := by
  -- the natural difference derivative from the three ODEs.
  have hcomb := ((hQwd t ht).sub (hQvd t ht)).sub (hRd t ht)
  -- rearrange the target derivative into the natural one via linearity.
  have heq :
      (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t - Qv t - R t)
        + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
             - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
           + (expJet2Rhs g gi hC p w Φ' h k t
              - expJet2Rhs g gi hC p v Φ h k t
              - expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t))
      = ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
            + expJet2Rhs g gi hC p w Φ' h k t)
          - ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qv t)
             + expJet2Rhs g gi hC p v Φ h k t)
          - ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  exact hcomb

set_option maxHeartbeats 1000000 in
/-- **The Jet₃ parameter-residual estimate, reduced to the remainder bound.**  With the Jet₂/Jet₃
    second/third-variation data of `expJet3_residual_hasDerivWithinAt` and the initial conditions
    `Qv 0 = Qw 0 = R 0 = 0`, given a `[0,1]`-bound `Kstar` on `‖DF(Y_v t)‖`
    (`expJet_fderiv_tube_bddAbove`) and a `[0,1]`-bound `ρ` on the remainder
    `‖[DF(Y_w t) − DF(Y_v t)](Qw t) + (Θ₂^{hk}_w(t) − Θ₂^{hk}_v(t) − Θ₃^{hkl}_v(t))‖`, one has
    `‖Qw 1 − Qv 1 − R 1‖ ≤ ρ · e^{Kstar}`.

    Feeds the residual ODE (`expJet3_residual_hasDerivWithinAt`) into the vector Grönwall
    (`gronwall_vec_residual`).  This is the residual estimate reduced to the single obligation
    `‖ρ(t)‖ ≤ ρ`; the quadratic bound `ρ = C·‖l‖²` (which closes the Fréchet little-o for
    `v ↦ Q^{hk}_v(1)`, discharging `ContDiff¹ (fderiv² exp_p)`) is the NEXT brick, the Rung-3
    assembly — NOT proven here. -/
theorem expJet3_residual_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qv Qw Qkl Qhl Qhk R : ℝ → (Point n × Point n)) (h k l : Point n)
    (hQv0 : Qv 0 = 0) (hQw0 : Qw 0 = 0) (hR0 : R 0 = 0)
    (hQvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qv
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qv t)
           + expJet2Rhs g gi hC p v Φ h k t) (Set.Icc (0 : ℝ) 1) t)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qw
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
           + expJet2Rhs g gi hC p w Φ' h k t) (Set.Icc (0 : ℝ) 1) t)
    (hRd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt R
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
           + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) (Set.Icc (0 : ℝ) 1) t)
    (Kstar ρ : ℝ) (hKstar0 : 0 ≤ Kstar) (hρ0 : 0 ≤ ρ)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
         + (expJet2Rhs g gi hC p w Φ' h k t
            - expJet2Rhs g gi hC p v Φ h k t
            - expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)‖ ≤ ρ) :
    ‖Qw 1 - Qv 1 - R 1‖ ≤ ρ * Real.exp Kstar := by
  refine gronwall_vec_residual (fun s => Qw s - Qv s - R s)
    (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
        - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
      + (expJet2Rhs g gi hC p w Φ' h k t
         - expJet2Rhs g gi hC p v Φ h k t
         - expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t))
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) Kstar ρ hKstar0 hρ0
    ?_ ?_ hKstar hr
  · -- initial condition `S 0 = 0`.
    simp only [hQv0, hQw0, hR0, sub_self]
  · -- the residual ODE.
    intro t ht
    exact expJet3_residual_hasDerivWithinAt g gi hC p v w Φ Φ' Qv Qw Qkl Qhl Qhk R h k l
      hQvd hQwd hRd t ht

/-! ### Sub-brick R3-firstvar — the `[0,1]`-uniform first-variation residual (quadratic)

The Rung-3 cancellation needs, as an input, that each first-variation difference in the varied
direction `l` agrees with the corresponding second variation up to `O(‖l‖²)`, UNIFORMLY on `[0,1]`
(not just at the endpoint `t = 1`).  This is the LEVEL-UP, `[0,1]`-uniform sharpening of the Rung-2
residual estimate `expJet2_residual_bound` (whose conclusion is only at `t = 1`); it is a pure
assembly of already-landed Rung-2 pieces — NOT a new Mathlib gap.  It supplies the
`‖Φ_{v+l}(t)(ιh) − Φ_v(t)(ιh) − Q^{hl}_v(t)‖ ≤ C‖l‖²` control (prerequisite 2 of the Rung-3
`ρ ≤ C‖l‖²` remainder bound). -/

set_option maxHeartbeats 1000000 in
/-- **The `[0,1]`-uniform first-variation residual, quadratic in `l`.**  With `Φ` the first-variation
    propagator for base point `v`, `Φ'` for `w = v + l`, and `Q` the `(h,l)` second-variation solution
    for `v` (`Q' = DF(Y_v)(Q) + D²F(Y_v)(Φ(ιh))(Φ(ιl))`, `Q 0 = 0`), the first-variation residual
    `S(t) = Φ'(t)(ιh) − Φ(t)(ιh) − Q(t)` is `O(‖l‖²)` uniformly on `[0,1]`:
    `∃ C ≥ 0, ∀ t ∈ [0,1], ‖S(t)‖ ≤ C·‖l‖²`.

    Assembly (mirror of `expJet2_residual_bound`, but at the `[0,1]`-uniform Grönwall):
    (i) the Rung-2 quadratic remainder bound `expJet2_remainder_quadratic_bound` (with the varied
    direction `k := l`) gives the `[0,1]` source estimate `‖r(t)‖ ≤ Cr·‖l‖²`; (ii) a `[0,1]` Jacobi
    bound `Kstar` on `‖DF(Y_v t)‖` (`expJet_fderiv_tube_bddAbove`); (iii) the residual ODE
    (`expJet2_residual_hasDerivWithinAt`) fed into the `[0,1]`-uniform vector Grönwall
    (`gronwall_vec_residual_Icc`) yields `‖S(t)‖ ≤ (Cr·‖l‖²)·e^{Kstar}` for every `t ∈ [0,1]`. -/
theorem expJet2FirstVar_residual_Icc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Q : ℝ → (Point n × Point n)) (h l : Point n)
    (hv : ‖v‖ ≤ expRho g gi hC p) (hvl : ‖v + l‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hQ0 : Q 0 = 0)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + l) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
    (hQd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Q
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Q t)
           + expJet2Rhs g gi hC p v Φ h l t) (Set.Icc (0 : ℝ) 1) t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota h) - Φ t (expJetIota h) - Q t‖ ≤ C * ‖l‖ ^ 2 := by
  -- (i) the Rung-2 quadratic remainder of the residual ODE source (varied direction `k := l`).
  obtain ⟨Cr, hCr0, hrbd⟩ := expJet2_remainder_quadratic_bound g gi hC p v l h Φ Φ'
    hv hvl hΦ0 hΦ'0 hΦcont hΦ'cont hΦd hΦ'd
  -- (ii) the `[0,1]` Jacobi bound on `‖DF(Y_v t)‖`.
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  refine ⟨Cr * Real.exp Kstar, mul_nonneg hCr0 (Real.exp_pos _).le, fun t ht => ?_⟩
  -- (iii) residual ODE + `[0,1]`-uniform vector Grönwall.
  have hgron := gronwall_vec_residual_Icc
    (fun s => Φ' s (expJetIota h) - Φ s (expJetIota h) - Q s)
    (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + l) s)
        - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Φ' s (expJetIota h))
      - expJet2Rhs g gi hC p v Φ h l s)
    (fun s => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) Kstar (Cr * ‖l‖ ^ 2)
    hKstar0 (mul_nonneg hCr0 (pow_nonneg (norm_nonneg _) 2))
    (by simp only [hΦ0, hΦ'0, ContinuousLinearMap.id_apply, hQ0, sub_self])
    (fun s hs => expJet2_residual_hasDerivWithinAt g gi hC p v (v + l) Φ Φ' Q h l
      hΦd hΦ'd hQd s hs)
    hKstar hrbd t ht
  calc ‖Φ' t (expJetIota h) - Φ t (expJetIota h) - Q t‖
      ≤ (Cr * ‖l‖ ^ 2) * Real.exp Kstar := hgron
    _ = Cr * Real.exp Kstar * ‖l‖ ^ 2 := by ring

/-! ### Sub-brick R3-(e) — the `[0,1]`-uniform second-variation two-point Lipschitz in the base point

The Rung-3 quadratic remainder bound `‖ρ‖ ≤ C‖l‖²` needs, as its last prerequisite (e), that the
Jet₂ second-variation curve `Q^{hk}_v(t)` is Lipschitz in the base point `v`, UNIFORMLY on `[0,1]`
(not just at the endpoint `t = 1`, which is `expJet2Val_two_pt_diff`).  This is the LEVEL-UP,
`[0,1]`-uniform sharpening of `expJet2Val_two_pt_diff`; it is a pure assembly of already-landed
Rung-2 pieces — NOT a new Mathlib gap.  The proof body is EXACTLY that of `expJet2Val_two_pt_diff`
with the `t = 1` vector Grönwall (`gronwall_vec_residual`) replaced by the `[0,1]`-uniform
`gronwall_vec_residual_Icc`; the residual-ODE identity (`expJet2_v_residual_hasDerivWithinAt`) and the
`ρ` two-point bound (`expJet2_v_residual_norm_le`) are reused verbatim. -/

set_option maxHeartbeats 3200000 in
/-- **The (e) core — the `[0,1]`-uniform `v`-two-point Lipschitz of the second-variation curve.**
    For `v, w` in the exp-ball, two first-variation propagators `Φv, Φw` (`Φ 0 = 1`, `Φ' = Ψ(Φ)`) and
    two second-variation solutions `Qv, Qw` (`Q 0 = 0`, `Q' = DF(Y_·)(Q) + Θ^{hk}_·`),
    `∀ t ∈ [0,1], ‖Qv t − Qw t‖ ≤ expJet2VtpConst·‖v−w‖·‖h‖·‖k‖`.  The `[0,1]`-uniform mirror of
    `expJet2Val_two_pt_diff`: the difference `D = Qv − Qw` solves `D' = DF(Y_v)(D) + ρ`
    (`expJet2_v_residual_hasDerivWithinAt`), the residual is `‖ρ‖ ≤ B1B2 + …`
    (`expJet2_v_residual_norm_le`) with the eight uniform bounds supplied by the tube two-point
    separation (`geodesic_twopoint_gronwall`), the `DF`/`D²F` Lipschitz constants, the `Φ` two-point
    Lipschitz (`expFund_two_pt_diff_Icc`), the `Φ`-norm bound (`expJetFund_norm_le_exp`) and the `Q`
    value bound (`expJet2Fund_value_bound_Icc`); then `gronwall_vec_residual_Icc`. -/
theorem expJet2_v_two_pt_Icc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Kf Ldf Ld2f : NNReal) (Kstar Kstar₂ : ℝ) (hKstar0 : 0 ≤ Kstar) (hKstar₂0 : 0 ≤ Kstar₂)
    (hLipF : LipschitzOnWith Kf (geodesicField g gi)
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipDF : LipschitzOnWith Ldf (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD2F : LipschitzOnWith Ld2f (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hKstar : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p u t)‖ ≤ Kstar)
    (hKstar₂ : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p u t)‖ ≤ Kstar₂)
    (Φv Φw : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦv0 : Φv 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦw0 : Φw 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φv (expJetPsi g gi hC p v t (Φv t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φw (expJetPsi g gi hC p w t (Φw t)) (Set.Icc (0 : ℝ) 1) t)
    (Qv Qw : ℝ → (Point n × Point n)) (h k : Point n)
    (hQv0 : Qv 0 = 0) (hQw0 : Qw 0 = 0)
    (hQvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qv t)
        + expJet2Rhs g gi hC p v Φv h k t) (Set.Icc (0 : ℝ) 1) t)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
        + expJet2Rhs g gi hC p w Φw h k t) (Set.Icc (0 : ℝ) 1) t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qv t - Qw t‖
        ≤ C * ‖v - w‖ * ‖h‖ * ‖k‖ := by
  have hC₀ := expConst_nonneg g gi hC p
  set Rb : ℝ := expConst g gi hC p * expRho g gi hC p with hRbdef
  set S : Set (Point n × Point n) := Metric.closedBall ((p, 0) : Point n × Point n) Rb with hSdef
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  obtain ⟨hY0w, hYdw, hconfw⟩ := expTube_spec g gi hC p w hw
  have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- tubes lie in the ball on `[0,1]`.
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
  -- uniform tube DF/D²F bounds specialised.
  have hKstarv := hKstar v hv
  have hKstarw := hKstar w hw
  have hK2v := hKstar₂ v hv
  have hK2w := hKstar₂ w hw
  -- `‖ι·‖ ≤ ‖·‖`.
  have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ :=
    ((expJetIota (n := n)).le_opNorm h).trans
      (by simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h))
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ :=
    ((expJetIota (n := n)).le_opNorm k).trans
      (by simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k))
  -- Φ-norm bounds `‖Φ t‖ ≤ e^{Kstar}`.
  have hΦvnorm := expJetFund_norm_le_exp g gi hC p v Φv Kstar hKstar0 hKstarv hΦv0 hΦvd
  have hΦwnorm := expJetFund_norm_le_exp g gi hC p w Φw Kstar hKstar0 hKstarw hΦw0 hΦwd
  -- tube two-point separation `‖Y_v t − Y_w t‖ ≤ ‖v−w‖·e^{Kf}`.
  have hdist0 : dist (expTube g gi hC p v 0) (expTube g gi hC p w 0) = ‖v - w‖ := by
    rw [hY0v, hY0w, dist_eq_norm, Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg _)]
  have htwopoint := geodesic_twopoint_gronwall g gi (S := S) (K := Kf) hLipF
    (fun t ht => hYdv t (hIcc_Ioo t ht)) (fun t ht => hYdw t (hIcc_Ioo t ht)) hSv hSw
  have hYvw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p v t - expTube g gi hC p w t‖ ≤ ‖v - w‖ * Real.exp (Kf : ℝ) := by
    intro t ht
    have hh := htwopoint t ht
    rw [hdist0, dist_eq_norm] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  -- `DF` and `D²F` two-point differences (Lipschitz ∘ tube two-point).
  have hDFdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)‖
        ≤ (Ldf : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipDF.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hD2diff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p w t)‖
        ≤ (Ld2f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipD2F.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  -- `Φ` two-point Lipschitz.
  have hΦdiff := expFund_two_pt_diff_Icc g gi hC p v w Kf Ldf Kstar hKstar0 hLipF hLipDF
    hKstarv hKstarw hv hw Φv Φw hΦv0 hΦw0 hΦvd hΦwd
  -- the `Q_w` value bound (all `t`).
  have hQwbd := expJet2Fund_value_bound_Icc g gi hC p w Φw h k Kstar Kstar₂ (Real.exp Kstar)
    hKstar0 hKstar₂0 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qw hQw0 hQwd
  -- the eight uniform bounds `B1..B8`.
  have hB5v : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φv t (expJetIota h)‖ ≤ Real.exp Kstar * ‖h‖ :=
    fun t ht => ((Φv t).le_opNorm _).trans
      (mul_le_mul (hΦvnorm t ht) hιh (norm_nonneg _) (Real.exp_pos _).le)
  have hB6v : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φv t (expJetIota k)‖ ≤ Real.exp Kstar * ‖k‖ :=
    fun t ht => ((Φv t).le_opNorm _).trans
      (mul_le_mul (hΦvnorm t ht) hιk (norm_nonneg _) (Real.exp_pos _).le)
  have hB5w : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φw t (expJetIota h)‖ ≤ Real.exp Kstar * ‖h‖ :=
    fun t ht => ((Φw t).le_opNorm _).trans
      (mul_le_mul (hΦwnorm t ht) hιh (norm_nonneg _) (Real.exp_pos _).le)
  have hB7 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φv t (expJetIota h) - Φw t (expJetIota h)‖
        ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖h‖ := by
    intro t ht
    rw [← ContinuousLinearMap.sub_apply]
    exact ((Φv t - Φw t).le_opNorm _).trans
      (mul_le_mul (hΦdiff t ht) hιh (norm_nonneg _)
        (by positivity))
  have hB8 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φv t (expJetIota k) - Φw t (expJetIota k)‖
        ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖k‖ := by
    intro t ht
    rw [← ContinuousLinearMap.sub_apply]
    exact ((Φv t - Φw t).le_opNorm _).trans
      (mul_le_mul (hΦdiff t ht) hιk (norm_nonneg _)
        (by positivity))
  -- the residual `ρ`-bound.
  set B1 : ℝ := (Ldf : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) with hB1def
  set B2 : ℝ := (Kstar₂ * (Real.exp Kstar) ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖ with hB2def
  set B3 : ℝ := (Ld2f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) with hB3def
  set B5 : ℝ := Real.exp Kstar * ‖h‖ with hB5def
  set B6 : ℝ := Real.exp Kstar * ‖k‖ with hB6def
  set B7 : ℝ := ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖h‖
    with hB7def
  set B8 : ℝ := ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖k‖
    with hB8def
  have hB1nn : 0 ≤ B1 := by rw [hB1def]; positivity
  have hB2nn : 0 ≤ B2 := by rw [hB2def]; positivity
  have hB3nn : 0 ≤ B3 := by rw [hB3def]; positivity
  have hB5nn : 0 ≤ B5 := by rw [hB5def]; positivity
  have hB6nn : 0 ≤ B6 := by rw [hB6def]; positivity
  have hB7nn : 0 ≤ B7 := by rw [hB7def]; positivity
  have hB8nn : 0 ≤ B8 := by rw [hB8def]; positivity
  set ρval : ℝ := B1 * B2 + (B3 * B5 * B6 + Kstar₂ * B7 * B6 + Kstar₂ * B5 * B8) with hρvaldef
  have hρval0 : 0 ≤ ρval := by
    rw [hρvaldef]; positivity
  have hrbound := expJet2_v_residual_norm_le g gi hC p v w Φv Φw Qw h k
    B1 B2 B3 Kstar₂ B5 B6 B7 B8 hB1nn hB2nn hB3nn hKstar₂0 hB5nn hB6nn hB7nn hB8nn
    (fun t ht => hDFdiff t ht) (fun t ht => hQwbd t ht) (fun t ht => hD2diff t ht)
    (fun t ht => hK2w t ht) (fun t ht => hB5v t ht) (fun t ht => hB6v t ht)
    (fun t ht => hB5w t ht) (fun t ht => hB7 t ht) (fun t ht => hB8 t ht)
  -- the difference Grönwall — `[0,1]`-uniform version.
  have hgron := gronwall_vec_residual_Icc (fun s => Qv s - Qw s)
    (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
        - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
      + (expJet2Rhs g gi hC p v Φv h k t - expJet2Rhs g gi hC p w Φw h k t))
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar ρval hKstar0 hρval0
    (by simp only [hQv0, hQw0, sub_zero])
    (fun t ht => expJet2_v_residual_hasDerivWithinAt g gi hC p v w Φv Φw Qv Qw h k hQvd hQwd t ht)
    (fun t ht => hKstarv t ht)
    (fun t ht => hrbound t ht)
  -- read off the constant and package the existential.
  refine ⟨expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar₂,
    expJet2VtpConst_nonneg _ _ _ _ _ Ldf.2 Ld2f.2 hKstar₂0, fun t ht => ?_⟩
  refine (hgron t ht).trans (le_of_eq ?_)
  rw [hρvaldef, hB1def, hB2def, hB3def, hB5def, hB6def, hB7def, hB8def, expJet2VtpConst]
  ring

end QIQTH.ExpMap
