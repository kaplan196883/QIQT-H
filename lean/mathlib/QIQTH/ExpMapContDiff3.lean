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

/-! ### R3-source multilinearity — the matched-`Q` source-linearity helpers

`expJet3Rhs` is multilinear in `(h,k,l)` jointly with its second-variation inputs, but ONLY when each
`Q··` input varies in exactly the two directions it names (the third stays fixed).  These six helpers
(scale/split in each of `l`, `h`, `k`) are the algebraic engine of the `expJet3Val` value facts, the
Rung-3 analogs of `expJet2Rhs_{add,smul}_{left,right}`. -/

/-- **Source `ℝ`-homogeneity in the `l`-slot.**  Scaling `l` by `c` (and the two `l`-carrying inputs
    `Qkl,Qhl` by `c`, `Qhk` fixed) scales `Θ₃` by `c`. -/
theorem expJet3Rhs_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n)) (c : ℝ) (h k l : Point n) (t : ℝ) :
    expJet3Rhs g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk h k (c • l) t
      = c • expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t := by
  simp only [expJet3Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

/-- **Source additivity in the `l`-slot.**  Splitting `l` (and the two `l`-carrying inputs
    `Qkl,Qhl`, `Qhk` shared) splits `Θ₃`. -/
theorem expJet3Rhs_add_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl₁ Qkl₂ Qhl₁ Qhl₂ Qhk : ℝ → (Point n × Point n)) (h k l₁ l₂ : Point n) (t : ℝ) :
    expJet3Rhs g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s) Qhk h k (l₁ + l₂) t
      = expJet3Rhs g gi hC p v Φ Qkl₁ Qhl₁ Qhk h k l₁ t
        + expJet3Rhs g gi hC p v Φ Qkl₂ Qhl₂ Qhk h k l₂ t := by
  simp only [expJet3Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

/-- **Source `ℝ`-homogeneity in the `h`-slot.**  Scaling `h` by `c` (and the two `h`-carrying inputs
    `Qhl,Qhk` by `c`, `Qkl` fixed) scales `Θ₃` by `c`. -/
theorem expJet3Rhs_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n)) (c : ℝ) (h k l : Point n) (t : ℝ) :
    expJet3Rhs g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) (c • h) k l t
      = c • expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t := by
  simp only [expJet3Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

/-- **Source additivity in the `h`-slot.**  Splitting `h` (and the two `h`-carrying inputs
    `Qhl,Qhk`, `Qkl` shared) splits `Θ₃`. -/
theorem expJet3Rhs_add_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl₁ Qhl₂ Qhk₁ Qhk₂ : ℝ → (Point n × Point n)) (h₁ h₂ k l : Point n) (t : ℝ) :
    expJet3Rhs g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhk₁ s + Qhk₂ s) (h₁ + h₂) k l t
      = expJet3Rhs g gi hC p v Φ Qkl Qhl₁ Qhk₁ h₁ k l t
        + expJet3Rhs g gi hC p v Φ Qkl Qhl₂ Qhk₂ h₂ k l t := by
  simp only [expJet3Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

/-- **Source `ℝ`-homogeneity in the `k`-slot.**  Scaling `k` by `c` (and the two `k`-carrying inputs
    `Qkl,Qhk` by `c`, `Qhl` fixed) scales `Θ₃` by `c`. -/
theorem expJet3Rhs_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n)) (c : ℝ) (h k l : Point n) (t : ℝ) :
    expJet3Rhs g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) h (c • k) l t
      = c • expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t := by
  simp only [expJet3Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

/-- **Source additivity in the `k`-slot.**  Splitting `k` (and the two `k`-carrying inputs
    `Qkl,Qhk`, `Qhl` shared) splits `Θ₃`. -/
theorem expJet3Rhs_add_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl₁ Qkl₂ Qhl Qhk₁ Qhk₂ : ℝ → (Point n × Point n)) (h k₁ k₂ l : Point n) (t : ℝ) :
    expJet3Rhs g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl (fun s => Qhk₁ s + Qhk₂ s) h (k₁ + k₂) l t
      = expJet3Rhs g gi hC p v Φ Qkl₁ Qhl Qhk₁ h k₁ l t
        + expJet3Rhs g gi hC p v Φ Qkl₂ Qhl Qhk₂ h k₂ l t := by
  simp only [expJet3Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

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

/-! ### Sub-brick R3-(c′) — the `D²F` second-order Taylor remainder is quadratic

The Rung-3 cancellation expands `D²F(Y_w) − D²F(Y_v)` to first order in the tube separation, with a
quadratic remainder.  This is the direct `D²F`/`D³F` analog, one Fréchet order up, of the landed
`geodesicField_DF_second_order_taylor` (which uses the `D²F`-Lipschitz constant): here the derivative
of `D²F = fderiv (fderiv F)` is `D³F = fderiv (fderiv (fderiv F))`, Lipschitz on the confined tube
ball (`expJet_fderiv3_lipschitzOnWith`), and the fixed-linear-map mean-value inequality
`Convex.norm_image_sub_le_of_norm_fderiv_le'` on the segment `[x,y]` yields the quadratic remainder
`‖D²F y − D²F x − D³F x (y − x)‖ ≤ L·‖y − x‖²`. -/

/-- **`D²F` second-order Taylor remainder is quadratic on the confined tube ball.**  With `L` a
    Lipschitz constant of `D³F = fderiv (fderiv (fderiv F))` on the tube ball
    `closedBall (p,0) (expConst·expRho)` (from `expJet_fderiv3_lipschitzOnWith`), the first-order
    Taylor remainder of `D²F = fderiv (fderiv (geodesicField g gi))` about `x` is bounded by
    `L·‖y − x‖²` for `x, y` in that ball.  The `D²F`/`D³F` mirror of
    `geodesicField_DF_second_order_taylor`. -/
theorem geodesicField_D2F_second_order_taylor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (L : ℝ) (hL0 : 0 ≤ L)
    (hLip : LipschitzOnWith L.toNNReal (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      (Metric.closedBall ((p,0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (x y : Point n × Point n)
    (hx : x ∈ Metric.closedBall ((p,0) : Point n × Point n)
      (expConst g gi hC p * expRho g gi hC p))
    (hy : y ∈ Metric.closedBall ((p,0) : Point n × Point n)
      (expConst g gi hC p * expRho g gi hC p)) :
    ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) y - fderiv ℝ (fderiv ℝ (geodesicField g gi)) x
        - (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x) (y - x)‖
      ≤ L * ‖y - x‖ ^ 2 := by
  have hseg : segment ℝ x y ⊆
      Metric.closedBall ((p,0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) :=
    (convex_closedBall _ _).segment_subset hx hy
  have hdiff : ∀ z ∈ segment ℝ x y,
      DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) z :=
    fun z _ => ((contDiff_fderiv2_geodesicField g gi hC).differentiable (by simp)).differentiableAt
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) z
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x‖ ≤ L * ‖y - x‖ := by
    intro z hz
    have hd := hLip.dist_le_mul z (hseg hz) x hx
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal L hL0] at hd
    calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) z
              - fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x‖
        ≤ L * ‖z - x‖ := hd
      _ ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hL0
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (f := fderiv ℝ (fderiv ℝ (geodesicField g gi)))
    (φ := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x)
    (C := L * ‖y - x‖) hdiff hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  calc ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) y - fderiv ℝ (fderiv ℝ (geodesicField g gi)) x
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x) (y - x)‖
      ≤ L * ‖y - x‖ * ‖y - x‖ := hmv
    _ = L * ‖y - x‖ ^ 2 := by ring

/-! ### Rung-3 capstone — the quadratic remainder bound `‖ρ(t)‖ ≤ C·‖l‖²`

The heavy cancellation-identity + per-term-bound assembly closing the `ρ` hypothesis of
`expJet3_residual_bound`.  The residual (from `expJet3_residual_hasDerivWithinAt`, `w := v + l`) is
`ρ(t) = (DF(Y_w) − DF(Y_v))(Q^{hk}_w) + (Θ₂^{hk}_w − Θ₂^{hk}_v − Θ₃^{hkl}_v)`.  Expanding to first
order in `l`, the first-order parts cancel EXACTLY (D³F cyclic symmetry `_cyc`, the D²F symmetry
`fderiv2_geodesicField_symm`, and the identity `Q^{hk} = Qv`), leaving ten explicit `O(‖l‖²)` error
terms bounded by the landed Taylor/accuracy/two-point ingredients. -/

set_option maxHeartbeats 4000000 in
/-- **The Jet₃ quadratic remainder bound (the Rung-3 capstone).**  With `Φ`/`Φ'` the first-variation
    propagators for `v`/`w = v + l`, `Qv`/`Qw` the `(h,k)` second variations for `v`/`w`,
    `Qkl`/`Qhl` the `(k,l)`/`(h,l)` second variations for `v`, and `Qhk = Qv`, the Jet₃ residual `ρ`
    of `expJet3_residual_hasDerivWithinAt` is `O(‖l‖²)` uniformly on `[0,1]`.  Consumes the
    first-variation residuals `hFVh`/`hFVk` (`= O(‖l‖²)`, from `expJet2FirstVar_residual_Icc`) and the
    second-variation two-point Lipschitz `hQlip` (`= O(‖l‖)`, from `expJet2_v_two_pt_Icc`).  The
    first-order-in-`l` cancellation is exact; the ten residual error terms are bounded by the
    `DF`/`D²F` second-order Taylor remainders (`geodesicField_DF/D2F_second_order_taylor`), the tube
    accuracy (`expTube_second_order_accuracy`), the first-variation two-point Lipschitz
    (`expFund_two_pt_diff_Icc`), and the tube/`Φ`/`Q` `[0,1]` bounds. -/
theorem expJet3_remainder_quadratic_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w l : Point n) (hwl : w = v + l)
    (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qv Qw Qkl Qhl Qhk : ℝ → (Point n × Point n)) (h k : Point n)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p w t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
    (hQw0 : Qw 0 = 0)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qw
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
           + expJet2Rhs g gi hC p w Φ' h k t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkv : Qhk = Qv)
    (Cd Ce : ℝ) (hCd0 : 0 ≤ Cd) (hCe0 : 0 ≤ Ce)
    (hFVh : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota h) - Φ t (expJetIota h) - Qhl t‖ ≤ Cd * ‖l‖ ^ 2)
    (hFVk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota k) - Φ t (expJetIota k) - Qkl t‖ ≤ Cd * ‖l‖ ^ 2)
    (hQlip : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qw t - Qv t‖ ≤ Ce * ‖l‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
         + (expJet2Rhs g gi hC p w Φ' h k t
            - expJet2Rhs g gi hC p v Φ h k t
            - expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)‖ ≤ C * ‖l‖ ^ 2 := by
  subst hwl
  have hC₀ := expConst_nonneg g gi hC p
  -- ── Lipschitz constants on the confined tube ball ──────────────────────────────────────────
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Ld3f, hLipD3⟩ := expJet_fderiv3_lipschitzOnWith g gi hC p
  -- ── tube bounds ────────────────────────────────────────────────────────────────────────────
  obtain ⟨Kvb, hKvb0, hKvbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨Kwb, _hKwb0, hKwbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p (v + l) hw
  obtain ⟨Kstar2, hKstar20, hD2bd⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hD3bd⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  -- ── real constants ─────────────────────────────────────────────────────────────────────────
  set eKf : ℝ := Real.exp (Kf : ℝ) with heKf
  have heKf0 : 0 ≤ eKf := (Real.exp_pos _).le
  set Kstar : ℝ := max Kvb Kwb with hKstardef
  have hKstar0 : 0 ≤ Kstar := le_max_of_le_left hKvb0
  set eKs : ℝ := Real.exp Kstar with heKs
  have heKs0 : 0 ≤ eKs := (Real.exp_pos _).le
  set M : ℝ := (Ldf : ℝ) with hMdef
  have hM0 : 0 ≤ M := Ldf.coe_nonneg
  set L2 : ℝ := (Ld2f : ℝ) with hL2def
  have hL2_0 : 0 ≤ L2 := Ld2f.coe_nonneg
  set L3 : ℝ := (Ld3f : ℝ) with hL3def
  have hL3_0 : 0 ≤ L3 := Ld3f.coe_nonneg
  set C2 : ℝ := M * eKf ^ 2 * eKs with hC2def
  have hC2_0 : 0 ≤ C2 := by rw [hC2def]; positivity
  set C3 : ℝ := M * eKf * eKs * eKs with hC3def
  have hC3_0 : 0 ≤ C3 := by rw [hC3def]; positivity
  set CQ : ℝ := Kstar2 * eKs ^ 2 * eKs with hCQdef
  have hCQ0 : 0 ≤ CQ := by rw [hCQdef]; positivity
  -- Lipschitz constants in `.toNNReal` shape.
  have hLipDF_M : LipschitzOnWith M.toNNReal (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hMdef, Real.toNNReal_coe]; exact hLipDF
  have hLipD2R : LipschitzOnWith L2.toNNReal (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL2def, Real.toNNReal_coe]; exact hLipD2
  have hLipD3R : LipschitzOnWith L3.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL3def, Real.toNNReal_coe]; exact hLipD3
  -- ── uniform `[0,1]` DF/D²F/D³F bounds ──────────────────────────────────────────────────────
  have hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar :=
    fun t ht => (hKvbd t ht).trans (le_max_left Kvb Kwb)
  have hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + l) t)‖ ≤ Kstar :=
    fun t ht => (hKwbd t ht).trans (le_max_right Kvb Kwb)
  have hK2v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2 :=
    fun t ht => hD2bd v hv t ht
  have hK2w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + l) t)‖ ≤ Kstar2 :=
    fun t ht => hD2bd (v + l) hw t ht
  have hK3v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3 :=
    fun t ht => hD3bd v hv t ht
  -- ── `Φ`, `Φ'` op-norm bounds on `[0,1]` ────────────────────────────────────────────────────
  have hΦnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p v Φ Kstar hKstar0 hKstarv hΦ0 hΦd
  have hΦ'norm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p (v + l) Φ' Kstar hKstar0 hKstarw hΦ'0 hΦ'd
  -- ── tube-ball memberships and separation ───────────────────────────────────────────────────
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  obtain ⟨hY0w, hYdw, hconfw⟩ := expTube_spec g gi hC p (v + l) hw
  have hmemv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfv t ht).trans (mul_le_mul_of_nonneg_left hv hC₀)
  have hmemw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + l) t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfw t ht).trans (mul_le_mul_of_nonneg_left hw hC₀)
  have hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + l) t - expTube g gi hC p v t‖ ≤ ‖l‖ * eKf := by
    have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdist0 : dist (expTube g gi hC p (v + l) 0) (expTube g gi hC p v 0) = ‖l‖ := by
      rw [hY0w, hY0v, dist_eq_norm, Prod.mk_sub_mk, add_sub_cancel_left, sub_self, Prod.norm_def,
        norm_zero, max_eq_right (norm_nonneg _)]
    have htwo := geodesic_twopoint_gronwall g gi
      (S := Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p))
      (K := Kf) hLipF
      (fun t ht => hYdw t (hIcc_Ioo t ht)) (fun t ht => hYdv t (hIcc_Ioo t ht)) hmemw hmemv
    intro t ht
    have hh := htwo t ht
    rw [hdist0, dist_eq_norm] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  -- ── the landed ingredient bounds (as `∀ t ∈ [0,1]` families) ───────────────────────────────
  have htay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + l) t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
              (expTube g gi hC p (v + l) t - expTube g gi hC p v t)‖
        ≤ L2 * ‖expTube g gi hC p (v + l) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_DF_second_order_taylor g gi hC p L2 hL2_0 hLipD2R
      (expTube g gi hC p v t) (expTube g gi hC p (v + l) t) (hmemv t ht) (hmemw t ht)
  have hD2tay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + l) t)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
              (expTube g gi hC p (v + l) t - expTube g gi hC p v t)‖
        ≤ L3 * ‖expTube g gi hC p (v + l) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_D2F_second_order_taylor g gi hC p L3 hL3_0 hLipD3R
      (expTube g gi hC p v t) (expTube g gi hC p (v + l) t) (hmemv t ht) (hmemw t ht)
  have hacc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + l) t - expTube g gi hC p v t - Φ t (expJetIota l)‖ ≤ C2 * ‖l‖ ^ 2 :=
    fun t ht => expTube_second_order_accuracy g gi hC p v l hw hv M hM0 Kf Kstar hKstar0
      hLipF hLipDF_M hKstarv Φ hΦ0 hΦd t ht
  have hQwval : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qw t‖ ≤ CQ * ‖h‖ * ‖k‖ :=
    expJet2Fund_value_bound_Icc g gi hC p (v + l) Φ' h k Kstar Kstar2 eKs
      hKstar0 hKstar20 heKs0 hKstarw hK2w hΦ'norm Qw hQw0 hQwd
  have htwopt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t - Φ' t‖ ≤ C3 * ‖l‖ := by
    have hbase := expFund_two_pt_diff_Icc g gi hC p v (v + l) Kf Ldf Kstar hKstar0
      hLipF hLipDF hKstarv hKstarw hv hw Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    intro t ht
    have hb := hbase t ht
    rw [show v - (v + l) = -l by abel, norm_neg] at hb
    exact hb
  -- ── iota norm bounds ───────────────────────────────────────────────────────────────────────
  have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ :=
    ((expJetIota (n := n)).le_opNorm h).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h))
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ :=
    ((expJetIota (n := n)).le_opNorm k).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k))
  have hιl : ‖expJetIota (n := n) l‖ ≤ ‖l‖ :=
    ((expJetIota (n := n)).le_opNorm l).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg l))
  -- ── the witness constant and the per-`t` chain ─────────────────────────────────────────────
  refine ⟨L2 * eKf ^ 2 * CQ * ‖h‖ * ‖k‖ + Kstar2 * C2 * CQ * ‖h‖ * ‖k‖ + Kstar2 * eKs * Ce
      + L3 * eKf ^ 2 * eKs ^ 2 * ‖h‖ * ‖k‖ + Kstar3 * C2 * eKs ^ 2 * ‖h‖ * ‖k‖
      + Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖ + Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖
      + Kstar2 * C3 ^ 2 * ‖h‖ * ‖k‖ + Kstar2 * Cd * eKs * ‖k‖ + Kstar2 * eKs * Cd * ‖h‖, ?_, ?_⟩
  · positivity
  · intro t ht
    rw [hQhkv]
    simp only [expJet2Rhs_apply, expJet3Rhs_apply]
    set yv := expTube g gi hC p v t with hyvE
    set yw := expTube g gi hC p (v + l) t with hywE
    set dv := fderiv ℝ (geodesicField g gi) yv with hdvE
    set dw := fderiv ℝ (geodesicField g gi) yw with hdwE
    set d2v := fderiv ℝ (fderiv ℝ (geodesicField g gi)) yv with hd2vE
    set d2w := fderiv ℝ (fderiv ℝ (geodesicField g gi)) yw with hd2wE
    set d3v := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) yv with hd3vE
    set ph := Φ t (expJetIota h) with hphE
    set pk := Φ t (expJetIota k) with hpkE
    set pl := Φ t (expJetIota l) with hplE
    set ph' := Φ' t (expJetIota h) with hph'E
    set pk' := Φ' t (expJetIota k) with hpk'E
    set qv := Qv t with hqvE
    set qw := Qw t with hqwE
    set qkl := Qkl t with hqklE
    set qhl := Qhl t with hqhlE
    -- derived vector/CLM bounds at this `t`.
    have hph : ‖ph‖ ≤ eKs * ‖h‖ := clmApply_norm_le (Φ t) (expJetIota h) heKs0 (hΦnorm t ht) hιh
    have hpk : ‖pk‖ ≤ eKs * ‖k‖ := clmApply_norm_le (Φ t) (expJetIota k) heKs0 (hΦnorm t ht) hιk
    have hpl : ‖pl‖ ≤ eKs * ‖l‖ := clmApply_norm_le (Φ t) (expJetIota l) heKs0 (hΦnorm t ht) hιl
    have hph' : ‖ph'‖ ≤ eKs * ‖h‖ :=
      clmApply_norm_le (Φ' t) (expJetIota h) heKs0 (hΦ'norm t ht) hιh
    have hpk' : ‖pk'‖ ≤ eKs * ‖k‖ :=
      clmApply_norm_le (Φ' t) (expJetIota k) heKs0 (hΦ'norm t ht) hιk
    have hd2n : ‖d2v‖ ≤ Kstar2 := hK2v t ht
    have hd3n : ‖d3v‖ ≤ Kstar3 := hK3v t ht
    have hph'ph : ‖ph' - ph‖ ≤ C3 * ‖l‖ * ‖h‖ := by
      have hsub : ph' - ph = (Φ' t - Φ t) (expJetIota h) := by
        rw [ContinuousLinearMap.sub_apply]
      rw [hsub]
      calc ‖(Φ' t - Φ t) (expJetIota h)‖
          ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) h‖ := (Φ' t - Φ t).le_opNorm _
        _ ≤ (C3 * ‖l‖) * ‖h‖ :=
            mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιh (norm_nonneg _) (by positivity)
        _ = C3 * ‖l‖ * ‖h‖ := by ring
    have hpk'pk : ‖pk' - pk‖ ≤ C3 * ‖l‖ * ‖k‖ := by
      have hsub : pk' - pk = (Φ' t - Φ t) (expJetIota k) := by
        rw [ContinuousLinearMap.sub_apply]
      rw [hsub]
      calc ‖(Φ' t - Φ t) (expJetIota k)‖
          ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) k‖ := (Φ' t - Φ t).le_opNorm _
        _ ≤ (C3 * ‖l‖) * ‖k‖ :=
            mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιk (norm_nonneg _) (by positivity)
        _ = C3 * ‖l‖ * ‖k‖ := by ring
    -- ── the cancellation identity ──────────────────────────────────────────────────────────
    have heq :
        (dw - dv) qw
          + (d2w ph' pk' - d2v ph pk
             - (d3v ph pk pl + d2v ph qkl + d2v pk qhl + d2v pl qv))
        = (dw - dv - d2v (yw - yv)) qw
          + (d2v (yw - yv - pl)) qw
          + (d2v pl) (qw - qv)
          + (d2w - d2v - d3v (yw - yv)) ph' pk'
          + d3v (yw - yv - pl) ph' pk'
          + d3v pl (ph' - ph) pk'
          + d3v pl ph (pk' - pk)
          + d2v (ph' - ph) (pk' - pk)
          + d2v (ph' - ph - qhl) pk
          + d2v ph (pk' - pk - qkl) := by
      have hcyc : d3v pl ph pk = d3v ph pk pl :=
        fderiv3_geodesicField_symm_cyc g gi hC yv pl ph pk
      have hsym : d2v qhl pk = d2v pk qhl :=
        fderiv2_geodesicField_symm g gi hC yv qhl pk
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      rw [hcyc, hsym]
      abel
    rw [heq]
    -- ── the ten `O(‖l‖²)` per-term bounds ───────────────────────────────────────────────────
    have hbA : ‖(dw - dv - d2v (yw - yv)) qw‖ ≤ (L2 * eKf ^ 2 * CQ * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 := by
      calc ‖(dw - dv - d2v (yw - yv)) qw‖
          ≤ ‖dw - dv - d2v (yw - yv)‖ * ‖qw‖ := (dw - dv - d2v (yw - yv)).le_opNorm _
        _ ≤ (L2 * ‖yw - yv‖ ^ 2) * (CQ * ‖h‖ * ‖k‖) :=
            mul_le_mul (htay t ht) (hQwval t ht) (norm_nonneg _) (by positivity)
        _ ≤ (L2 * (‖l‖ * eKf) ^ 2) * (CQ * ‖h‖ * ‖k‖) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hsep t ht) 2) hL2_0)
              (by positivity)
        _ = (L2 * eKf ^ 2 * CQ * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 := by ring
    have hbB : ‖(d2v (yw - yv - pl)) qw‖ ≤ (Kstar2 * C2 * CQ * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply2_norm_le d2v (yw - yv - pl) qw hKstar20 (by positivity) hd2n
        (hacc t ht) (hQwval t ht)).trans (le_of_eq (by ring))
    have hbC : ‖(d2v pl) (qw - qv)‖ ≤ (Kstar2 * eKs * Ce) * ‖l‖ ^ 2 :=
      (clmApply2_norm_le d2v pl (qw - qv) hKstar20 (by positivity) hd2n hpl
        (hQlip t ht)).trans (le_of_eq (by ring))
    have hbE1 : ‖(d2w - d2v - d3v (yw - yv)) ph' pk'‖
        ≤ (L3 * eKf ^ 2 * eKs ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 := by
      calc ‖(d2w - d2v - d3v (yw - yv)) ph' pk'‖
          ≤ (L3 * ‖yw - yv‖ ^ 2) * (eKs * ‖h‖) * (eKs * ‖k‖) :=
            clmApply2_norm_le _ ph' pk' (by positivity) (by positivity) (hD2tay t ht) hph' hpk'
        _ ≤ (L3 * (‖l‖ * eKf) ^ 2) * (eKs * ‖h‖) * (eKs * ‖k‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hsep t ht) 2) hL3_0)
              (by positivity)) (by positivity)
        _ = (L3 * eKf ^ 2 * eKs ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 := by ring
    have hbE2 : ‖d3v (yw - yv - pl) ph' pk'‖
        ≤ (Kstar3 * C2 * eKs ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply3_norm_le d3v (yw - yv - pl) ph' pk' hKstar30 (by positivity) (by positivity)
        hd3n (hacc t ht) hph' hpk').trans (le_of_eq (by ring))
    have hbE3 : ‖d3v pl (ph' - ph) pk'‖ ≤ (Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply3_norm_le d3v pl (ph' - ph) pk' hKstar30 (by positivity) (by positivity)
        hd3n hpl hph'ph hpk').trans (le_of_eq (by ring))
    have hbE4 : ‖d3v pl ph (pk' - pk)‖ ≤ (Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply3_norm_le d3v pl ph (pk' - pk) hKstar30 (by positivity) (by positivity)
        hd3n hpl hph hpk'pk).trans (le_of_eq (by ring))
    have hbE5 : ‖d2v (ph' - ph) (pk' - pk)‖ ≤ (Kstar2 * C3 ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply2_norm_le d2v (ph' - ph) (pk' - pk) hKstar20 (by positivity) hd2n
        hph'ph hpk'pk).trans (le_of_eq (by ring))
    have hbE6 : ‖d2v (ph' - ph - qhl) pk‖ ≤ (Kstar2 * Cd * eKs * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply2_norm_le d2v (ph' - ph - qhl) pk hKstar20 (by positivity) hd2n
        (hFVh t ht) hpk).trans (le_of_eq (by ring))
    have hbE7 : ‖d2v ph (pk' - pk - qkl)‖ ≤ (Kstar2 * eKs * Cd * ‖h‖) * ‖l‖ ^ 2 :=
      (clmApply2_norm_le d2v ph (pk' - pk - qkl) hKstar20 (by positivity) hd2n
        hph (hFVk t ht)).trans (le_of_eq (by ring))
    -- ── combine via the triangle inequality ──────────────────────────────────────────────────
    rw [show (L2 * eKf ^ 2 * CQ * ‖h‖ * ‖k‖ + Kstar2 * C2 * CQ * ‖h‖ * ‖k‖ + Kstar2 * eKs * Ce
          + L3 * eKf ^ 2 * eKs ^ 2 * ‖h‖ * ‖k‖ + Kstar3 * C2 * eKs ^ 2 * ‖h‖ * ‖k‖
          + Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖ + Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖
          + Kstar2 * C3 ^ 2 * ‖h‖ * ‖k‖ + Kstar2 * Cd * eKs * ‖k‖ + Kstar2 * eKs * Cd * ‖h‖)
          * ‖l‖ ^ 2
        = (L2 * eKf ^ 2 * CQ * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 + (Kstar2 * C2 * CQ * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar2 * eKs * Ce) * ‖l‖ ^ 2 + (L3 * eKf ^ 2 * eKs ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar3 * C2 * eKs ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 + (Kstar2 * C3 ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar2 * Cd * eKs * ‖k‖) * ‖l‖ ^ 2 + (Kstar2 * eKs * Cd * ‖h‖) * ‖l‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE7)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE6)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE5)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE4)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE3)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE2)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE1)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbC)
    refine (norm_add_le _ _).trans (add_le_add hbA hbB)

/-! ### B-CLM(3) — uniqueness, value bound, and (matched-`Q`) trilinearity of the Jet₃ third variation

The Rung-3 mirror of the landed Rung-2 B-CLM chain (`expJet2Fund_unique` → `expJet2Fund_value_bound`
→ `expJet2Val` → the four `expJet2Val_{add,smul}_{left,right}` bilinearity facts → `expJetD2`).

**Honest scope note on the linearity layer.**  Unlike the Jet₂ source `expJet2Rhs` — which is
`D²F(Φ(ι h))(Φ(ι k))`, manifestly bilinear in `(h,k)` through the two EXPLICIT `Φ(ι·)` slots — the
Jet₃ source `expJet3Rhs` carries three `D²F` CROSS-terms `D²F(Φ(ι·))(Q··)` whose second factors
`Qkl/Qhl/Qhk` are ABSTRACT second-variation inputs that themselves depend on the two directions they
name.  Consequently `R^{hkl}(1)` is NOT trilinear in `(h,k,l)` for FIXED abstract `Qkl,Qhl,Qhk`; it is
multilinear only when the `Q··` inputs vary in the matched way (scale/split in exactly the directions
they carry, while the third stays fixed).  We therefore land the honest **matched-`Q`** multilinearity:
source-linearity helpers `expJet3Rhs_{smul,add}_{l,h,k}` and the six `expJet3Val_{smul,add}_{l,h,k}`
value facts, each with the `Q··` inputs varied in the correct slots.  The full CLM packaging `expJetD3`
would require instantiating `Qkl/Qhl/Qhk` as the genuine bilinear 2nd variations (`expJet2Val`-derived)
so the composite is trilinear in three plain vectors; that wiring is a separate layer — see the closing
checkpoint. -/

/-- **Uniqueness of the Jet₃ third-variation IVP on `[0,1]`.**  Mirror of `expJet2Fund_unique`: the
    inhomogeneous source `Θ₃^{hkl}` is CONSTANT in `R`, so two solutions `R₁,R₂` with the same IC agree
    — the difference `S := R₁ - R₂` solves the HOMOGENEOUS Jacobi equation `S' = DF(Y_v)(S)` (the
    sources cancel) with `S 0 = 0`, and `gronwall_vec_residual_Icc` with residual `ρ = 0` forces
    `‖S t‖ ≤ 0` on `[0,1]`. -/
theorem expJet3Fund_unique (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (h k l : Point n)
    (R₁ R₂ : ℝ → (Point n × Point n)) (hR₁0 : R₁ 0 = 0) (hR₂0 : R₂ 0 = 0)
    (hderiv₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R₁
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₁ t)
        + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) (Set.Icc (0 : ℝ) 1) t)
    (hderiv₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R₂
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₂ t)
        + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) (Set.Icc (0 : ℝ) 1) t) :
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
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
            - ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₂ t)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₁ t - R₂ t) + 0 := by
        rw [map_sub, add_zero]; abel
      rwa [hval] at hd)
    (fun t ht => hKstar t ht)
    (fun _ _ => by simp)
  intro t ht
  have h0 : ‖R₁ t - R₂ t‖ ≤ 0 := by simpa using hgron t ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

/-- **(2) `R^{hkl}(1)` value bound.**  For the inhomogeneous Jet₃ solution `R` (`R 0 = 0`,
    `R' = DF(Y_v)(R) + Θ₃^{hkl}`), with a `[0,1]` Jacobi bound `Kstar` on `‖DF(Y_v t)‖`, the `D³F`/`D²F`
    tube bounds `Kstar3`/`Kstar2`, a `[0,1]`-bound `Cphi` on `‖Φ t‖`, and `[0,1]`-bounds
    `Cq_kl/Cq_hl/Cq_hk` on `‖Qkl/Qhl/Qhk‖`,
    `‖R 1‖ ≤ (Kstar3·(Cφ‖h‖)(Cφ‖k‖)(Cφ‖l‖) + Kstar2·(Cφ‖h‖)·Cq_kl + Kstar2·(Cφ‖k‖)·Cq_hl
             + Kstar2·(Cφ‖l‖)·Cq_hk)·e^{Kstar}`.  Proof: the four-term source bound
    (`expJet3Rhs_norm_le`) is fed as the residual `ρ` into `gronwall_vec_residual` ⟹
    `‖R 1‖ ≤ ρ·e^{Kstar}`. -/
theorem expJet3Fund_value_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n)) (h k l : Point n)
    (Kstar Kstar3 Kstar2 Cphi Cq_kl Cq_hl Cq_hk : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar30 : 0 ≤ Kstar3) (hKstar20 : 0 ≤ Kstar2) (hCphi0 : 0 ≤ Cphi)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hKstar3 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3)
    (hKstar2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2)
    (hCphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi)
    (hCqkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq_kl)
    (hCqhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhl t‖ ≤ Cq_hl)
    (hCqhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhk t‖ ≤ Cq_hk)
    (R : ℝ → (Point n × Point n)) (hR0 : R 0 = 0)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
        + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t) (Set.Icc (0 : ℝ) 1) t) :
    ‖R 1‖ ≤ (Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖)
        + Kstar2 * (Cphi * ‖h‖) * Cq_kl
        + Kstar2 * (Cphi * ‖k‖) * Cq_hl
        + Kstar2 * (Cphi * ‖l‖) * Cq_hk) * Real.exp Kstar := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num [Set.mem_Icc]
  have hCqkl0 : 0 ≤ Cq_kl := (norm_nonneg _).trans (hCqkl 0 hmem0)
  have hCqhl0 : 0 ≤ Cq_hl := (norm_nonneg _).trans (hCqhl 0 hmem0)
  have hCqhk0 : 0 ≤ Cq_hk := (norm_nonneg _).trans (hCqhk 0 hmem0)
  have hρ0 : (0 : ℝ) ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖)
      + Kstar2 * (Cphi * ‖h‖) * Cq_kl
      + Kstar2 * (Cphi * ‖k‖) * Cq_hl
      + Kstar2 * (Cphi * ‖l‖) * Cq_hk := by positivity
  have hΘbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t‖
        ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖)
          + Kstar2 * (Cphi * ‖h‖) * Cq_kl
          + Kstar2 * (Cphi * ‖k‖) * Cq_hl
          + Kstar2 * (Cphi * ‖l‖) * Cq_hk :=
    fun t ht => expJet3Rhs_norm_le g gi hC p v Φ Qkl Qhl Qhk h k l
      Kstar3 Kstar2 Cphi Cq_kl Cq_hl Cq_hk hKstar30 hKstar20 hCphi0
      hKstar3 hKstar2 hCphi hCqkl hCqhl hCqhk t ht
  exact gronwall_vec_residual R (fun t => expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar _ hKstar0 hρ0 hR0 hderiv hKstar hΘbd

/-- **The chosen third-variation value** `R^{hkl}_v(1) : Point n × Point n`.  The canonical
    representative of the (uniqueness-`expJet3Fund_unique`-well-defined) value at `t = 1` of the
    `expJet3Fund` witness for direction triple `(h,k,l)` and second-variation inputs `Qkl,Qhl,Qhk`;
    used to STATE the matched-`Q` multilinearity. -/
noncomputable def expJet3Val (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n) : Point n × Point n :=
  (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose 1

/-- **Matched-`Q` `ℝ`-homogeneity of `R^{hkl}(1)` in the `l`-slot.**  `R^{h,k,c•l}(1) = c·R^{h,k,l}(1)`
    when the two `l`-carrying inputs `Qkl,Qhl` scale by `c` (`Qhk` fixed): the chosen witness
    `c•R^{h,k,l}` solves the `(c•l)` IVP by `expJet3Rhs_smul_l` + `expJet3Fund_unique`. -/
theorem expJet3Val_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (c : ℝ) (h k l : Point n) :
    expJet3Val g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk hv hΦcont
        (hQkl.const_smul c) (hQhl.const_smul c) hQhk h k (c • l)
      = c • expJet3Val g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet3Fund g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk hv hΦcont
      (hQkl.const_smul c) (hQhl.const_smul c) hQhk h k (c • l)).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk hv
    h k (c • l)
    (expJet3Fund g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk hv hΦcont
      (hQkl.const_smul c) (hQhl.const_smul c) hQhk h k (c • l)).choose
    (fun t => c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
            + expJet3Rhs g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk h k (c • l) t := by
        rw [smul_add, map_smul, expJet3Rhs_smul_l]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet3Val] using h1

/-- **Matched-`Q` additivity of `R^{hkl}(1)` in the `l`-slot.**  `R^{h,k,l₁+l₂}(1) =
    R^{h,k,l₁}(1)+R^{h,k,l₂}(1)` when the two `l`-carrying inputs `Qkl,Qhl` split (`Qhk` shared)
    (`expJet3Rhs_add_l` + `expJet3Fund_unique`). -/
theorem expJet3Val_add_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl₁ Qkl₂ Qhl₁ Qhl₂ Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl₁ : ContinuousOn Qkl₁ (Set.Icc (0 : ℝ) 1)) (hQkl₂ : ContinuousOn Qkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhl₁ : ContinuousOn Qhl₁ (Set.Icc (0 : ℝ) 1)) (hQhl₂ : ContinuousOn Qhl₂ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l₁ l₂ : Point n) :
    expJet3Val g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s) Qhk hv hΦcont
        (hQkl₁.add hQkl₂) (hQhl₁.add hQhl₂) hQhk h k (l₁ + l₂)
      = expJet3Val g gi hC p v Φ Qkl₁ Qhl₁ Qhk hv hΦcont hQkl₁ hQhl₁ hQhk h k l₁
        + expJet3Val g gi hC p v Φ Qkl₂ Qhl₂ Qhk hv hΦcont hQkl₂ hQhl₂ hQhk h k l₂ := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl₁ Qhl₁ Qhk hv hΦcont hQkl₁ hQhl₁ hQhk h k l₁).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl₂ Qhl₂ Qhk hv hΦcont hQkl₂ hQhl₂ hQhk h k l₂).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet3Fund g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s) Qhk hv hΦcont
      (hQkl₁.add hQkl₂) (hQhl₁.add hQhl₂) hQhk h k (l₁ + l₂)).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s)
    Qhk hv h k (l₁ + l₂)
    (expJet3Fund g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s) Qhk hv hΦcont
      (hQkl₁.add hQkl₂) (hQhl₁.add hQhl₂) hQhk h k (l₁ + l₂)).choose
    (fun t => (expJet3Fund g gi hC p v Φ Qkl₁ Qhl₁ Qhk hv hΦcont hQkl₁ hQhl₁ hQhk h k l₁).choose t
      + (expJet3Fund g gi hC p v Φ Qkl₂ Qhl₂ Qhk hv hΦcont hQkl₂ hQhl₂ hQhk h k l₂).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₁ Qhl₁ Qhk hv hΦcont hQkl₁ hQhl₁ hQhk h k l₁).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl₁ Qhl₁ Qhk h k l₁ t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₂ Qhl₂ Qhk hv hΦcont hQkl₂ hQhl₂ hQhk h k l₂).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl₂ Qhl₂ Qhk h k l₂ t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₁ Qhl₁ Qhk hv hΦcont hQkl₁ hQhl₁ hQhk h k l₁).choose t
                + (expJet3Fund g gi hC p v Φ Qkl₂ Qhl₂ Qhk hv hΦcont hQkl₂ hQhl₂ hQhk h k l₂).choose t)
            + expJet3Rhs g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s) Qhk
                h k (l₁ + l₂) t := by
        rw [map_add, expJet3Rhs_add_l]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet3Val] using h1

/-- **Matched-`Q` `ℝ`-homogeneity of `R^{hkl}(1)` in the `h`-slot.**  `R^{c•h,k,l}(1) = c·R^{h,k,l}(1)`
    when the two `h`-carrying inputs `Qhl,Qhk` scale by `c` (`Qkl` fixed) (`expJet3Rhs_smul_h` +
    `expJet3Fund_unique`). -/
theorem expJet3Val_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (c : ℝ) (h k l : Point n) :
    expJet3Val g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) hv hΦcont
        hQkl (hQhl.const_smul c) (hQhk.const_smul c) (c • h) k l
      = c • expJet3Val g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) hv hΦcont
      hQkl (hQhl.const_smul c) (hQhk.const_smul c) (c • h) k l).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) hv
    (c • h) k l
    (expJet3Fund g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) hv hΦcont
      hQkl (hQhl.const_smul c) (hQhk.const_smul c) (c • h) k l).choose
    (fun t => c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) (c • h) k l t := by
        rw [smul_add, map_smul, expJet3Rhs_smul_h]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet3Val] using h1

/-- **Matched-`Q` additivity of `R^{hkl}(1)` in the `h`-slot.**  `R^{h₁+h₂,k,l}(1) =
    R^{h₁,k,l}(1)+R^{h₂,k,l}(1)` when the two `h`-carrying inputs `Qhl,Qhk` split (`Qkl` shared)
    (`expJet3Rhs_add_h` + `expJet3Fund_unique`). -/
theorem expJet3Val_add_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl₁ Qhl₂ Qhk₁ Qhk₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl₁ : ContinuousOn Qhl₁ (Set.Icc (0 : ℝ) 1)) (hQhl₂ : ContinuousOn Qhl₂ (Set.Icc (0 : ℝ) 1))
    (hQhk₁ : ContinuousOn Qhk₁ (Set.Icc (0 : ℝ) 1)) (hQhk₂ : ContinuousOn Qhk₂ (Set.Icc (0 : ℝ) 1))
    (h₁ h₂ k l : Point n) :
    expJet3Val g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
        hQkl (hQhl₁.add hQhl₂) (hQhk₁.add hQhk₂) (h₁ + h₂) k l
      = expJet3Val g gi hC p v Φ Qkl Qhl₁ Qhk₁ hv hΦcont hQkl hQhl₁ hQhk₁ h₁ k l
        + expJet3Val g gi hC p v Φ Qkl Qhl₂ Qhk₂ hv hΦcont hQkl hQhl₂ hQhk₂ h₂ k l := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl₁ Qhk₁ hv hΦcont hQkl hQhl₁ hQhk₁ h₁ k l).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl₂ Qhk₂ hv hΦcont hQkl hQhl₂ hQhk₂ h₂ k l).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
      hQkl (hQhl₁.add hQhl₂) (hQhk₁.add hQhk₂) (h₁ + h₂) k l).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s)
    (fun s => Qhk₁ s + Qhk₂ s) hv (h₁ + h₂) k l
    (expJet3Fund g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
      hQkl (hQhl₁.add hQhl₂) (hQhk₁.add hQhk₂) (h₁ + h₂) k l).choose
    (fun t => (expJet3Fund g gi hC p v Φ Qkl Qhl₁ Qhk₁ hv hΦcont hQkl hQhl₁ hQhk₁ h₁ k l).choose t
      + (expJet3Fund g gi hC p v Φ Qkl Qhl₂ Qhk₂ hv hΦcont hQkl hQhl₂ hQhk₂ h₂ k l).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl Qhl₁ Qhk₁ hv hΦcont hQkl hQhl₁ hQhk₁ h₁ k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl Qhl₁ Qhk₁ h₁ k l t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl Qhl₂ Qhk₂ hv hΦcont hQkl hQhl₂ hQhk₂ h₂ k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl Qhl₂ Qhk₂ h₂ k l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl Qhl₁ Qhk₁ hv hΦcont hQkl hQhl₁ hQhk₁ h₁ k l).choose t
                + (expJet3Fund g gi hC p v Φ Qkl Qhl₂ Qhk₂ hv hΦcont hQkl hQhl₂ hQhk₂ h₂ k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhk₁ s + Qhk₂ s)
                (h₁ + h₂) k l t := by
        rw [map_add, expJet3Rhs_add_h]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet3Val] using h1

/-- **Matched-`Q` `ℝ`-homogeneity of `R^{hkl}(1)` in the `k`-slot.**  `R^{h,c•k,l}(1) = c·R^{h,k,l}(1)`
    when the two `k`-carrying inputs `Qkl,Qhk` scale by `c` (`Qhl` fixed) (`expJet3Rhs_smul_k` +
    `expJet3Fund_unique`). -/
theorem expJet3Val_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (c : ℝ) (h k l : Point n) :
    expJet3Val g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) hv hΦcont
        (hQkl.const_smul c) hQhl (hQhk.const_smul c) h (c • k) l
      = c • expJet3Val g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet3Fund g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) hv hΦcont
      (hQkl.const_smul c) hQhl (hQhk.const_smul c) h (c • k) l).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) hv
    h (c • k) l
    (expJet3Fund g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) hv hΦcont
      (hQkl.const_smul c) hQhl (hQhk.const_smul c) h (c • k) l).choose
    (fun t => c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
            + expJet3Rhs g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) h (c • k) l t := by
        rw [smul_add, map_smul, expJet3Rhs_smul_k]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet3Val] using h1

/-- **Matched-`Q` additivity of `R^{hkl}(1)` in the `k`-slot.**  `R^{h,k₁+k₂,l}(1) =
    R^{h,k₁,l}(1)+R^{h,k₂,l}(1)` when the two `k`-carrying inputs `Qkl,Qhk` split (`Qhl` shared)
    (`expJet3Rhs_add_k` + `expJet3Fund_unique`). -/
theorem expJet3Val_add_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl₁ Qkl₂ Qhl Qhk₁ Qhk₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl₁ : ContinuousOn Qkl₁ (Set.Icc (0 : ℝ) 1)) (hQkl₂ : ContinuousOn Qkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk₁ : ContinuousOn Qhk₁ (Set.Icc (0 : ℝ) 1)) (hQhk₂ : ContinuousOn Qhk₂ (Set.Icc (0 : ℝ) 1))
    (h k₁ k₂ l : Point n) :
    expJet3Val g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
        (hQkl₁.add hQkl₂) hQhl (hQhk₁.add hQhk₂) h (k₁ + k₂) l
      = expJet3Val g gi hC p v Φ Qkl₁ Qhl Qhk₁ hv hΦcont hQkl₁ hQhl hQhk₁ h k₁ l
        + expJet3Val g gi hC p v Φ Qkl₂ Qhl Qhk₂ hv hΦcont hQkl₂ hQhl hQhk₂ h k₂ l := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl₁ Qhl Qhk₁ hv hΦcont hQkl₁ hQhl hQhk₁ h k₁ l).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl₂ Qhl Qhk₂ hv hΦcont hQkl₂ hQhl hQhk₂ h k₂ l).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet3Fund g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
      (hQkl₁.add hQkl₂) hQhl (hQhk₁.add hQhk₂) h (k₁ + k₂) l).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl
    (fun s => Qhk₁ s + Qhk₂ s) hv h (k₁ + k₂) l
    (expJet3Fund g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
      (hQkl₁.add hQkl₂) hQhl (hQhk₁.add hQhk₂) h (k₁ + k₂) l).choose
    (fun t => (expJet3Fund g gi hC p v Φ Qkl₁ Qhl Qhk₁ hv hΦcont hQkl₁ hQhl hQhk₁ h k₁ l).choose t
      + (expJet3Fund g gi hC p v Φ Qkl₂ Qhl Qhk₂ hv hΦcont hQkl₂ hQhl hQhk₂ h k₂ l).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₁ Qhl Qhk₁ hv hΦcont hQkl₁ hQhl hQhk₁ h k₁ l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl₁ Qhl Qhk₁ h k₁ l t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₂ Qhl Qhk₂ hv hΦcont hQkl₂ hQhl hQhk₂ h k₂ l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl₂ Qhl Qhk₂ h k₂ l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₁ Qhl Qhk₁ hv hΦcont hQkl₁ hQhl hQhk₁ h k₁ l).choose t
                + (expJet3Fund g gi hC p v Φ Qkl₂ Qhl Qhk₂ hv hΦcont hQkl₂ hQhl hQhk₂ h k₂ l).choose t)
            + expJet3Rhs g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl (fun s => Qhk₁ s + Qhk₂ s)
                h (k₁ + k₂) l t := by
        rw [map_add, expJet3Rhs_add_k]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet3Val] using h1

/-! ### The genuine second-variation CURVE and its curve-level bilinearity on `[0,1]`

The B-CLM(3) checkpoint identified the wall: `expJetD3` needs PLAIN trilinearity for FIXED inputs,
but the matched-`Q` value facts split only when the abstract `Q··` inputs are varied in tandem.  The
fix is to instantiate `Qkl/Qhl/Qhk` with the GENUINE second-variation curves `t ↦ Q^{··}(t)` — the
`expJet2Fund` witnesses — which ARE bilinear in their two directions, so the matched-`Q` splitting is
automatic.  Here we build that curve `expJet2Curve` and prove its curve-level (∀ `t ∈ [0,1]`)
bilinearity by the SAME superposition-via-uniqueness argument as `expJet2Val_{add,smul}_{left,right}`,
concluding at every `t` (not just `t = 1`).  This is the curve-vs-value upgrade the wiring needs. -/

/-- The **genuine second-variation curve** `t ↦ Q^{hk}_v(t)`: the chosen `expJet2Fund` witness for the
    direction pair `(h,k)`.  Its value at `t = 1` is `expJet2Val`; here we keep the whole curve, since
    the Jet₃ source `expJet3Rhs` feeds the curve pointwise. -/
noncomputable def expJet2Curve (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k : Point n) : ℝ → (Point n × Point n) :=
  (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose

/-- `expJet2Curve` is continuous on `[0,1]` (the `expJet2Fund` witness spec). -/
theorem expJet2Curve_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k : Point n) :
    ContinuousOn (expJet2Curve g gi hC p v Φ hv hΦcont h k) (Set.Icc (0 : ℝ) 1) :=
  (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec.2.1

/-- **Curve-level additivity of `Q^{hk}` in the first (`h`) slot, on `[0,1]`.**  The `∀ t`-upgrade of
    `expJet2Val_add_left`: same superposition (`expJet2Rhs_add_left` + `expJet2Fund_unique`), but
    keeping the whole-interval uniqueness conclusion. -/
theorem expJet2Curve_add_left (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h₁ h₂ k : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet2Curve g gi hC p v Φ hv hΦcont (h₁ + h₂) k t
      = expJet2Curve g gi hC p v Φ hv hΦcont h₁ k t
        + expJet2Curve g gi hC p v Φ hv hΦcont h₂ k t := by
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
  intro t ht
  simpa only [expJet2Curve] using huniq t ht

/-- **Curve-level ℝ-homogeneity of `Q^{hk}` in the first (`h`) slot, on `[0,1]`.** -/
theorem expJet2Curve_smul_left (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet2Curve g gi hC p v Φ hv hΦcont (c • h) k t
      = c • expJet2Curve g gi hC p v Φ hv hΦcont h k t := by
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
  intro t ht
  simpa only [expJet2Curve] using huniq t ht

/-- **Curve-level additivity of `Q^{hk}` in the second (`k`) slot, on `[0,1]`.** -/
theorem expJet2Curve_add_right (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k₁ k₂ : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet2Curve g gi hC p v Φ hv hΦcont h (k₁ + k₂) t
      = expJet2Curve g gi hC p v Φ hv hΦcont h k₁ t
        + expJet2Curve g gi hC p v Φ hv hΦcont h k₂ t := by
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
  intro t ht
  simpa only [expJet2Curve] using huniq t ht

/-- **Curve-level ℝ-homogeneity of `Q^{hk}` in the second (`k`) slot, on `[0,1]`.** -/
theorem expJet2Curve_smul_right (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet2Curve g gi hC p v Φ hv hΦcont h (c • k) t
      = c • expJet2Curve g gi hC p v Φ hv hΦcont h k t := by
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
  intro t ht
  simpa only [expJet2Curve] using huniq t ht

/-! ### Packaging `expJetD3` — genuine trilinearity via the second-variation curves

With the genuine curves in hand, `expJet3Val` becomes plain-trilinear in `(h,k,l)`.  The bridge is a
`Q`-congruence lemma (`expJet3Val_congr`: the value depends on the `Q··` inputs only through their
values on `[0,1]`, by `expJet3Fund_unique`) that lets us swap the combined genuine curve
`expJet2Curve k (l₁+l₂)` for the sum `s ↦ expJet2Curve k l₁ s + expJet2Curve k l₂ s` (they agree on
`[0,1]` by the curve bilinearity), after which the already-landed matched-`Q` value facts
(`expJet3Val_{add,smul}_{l,h,k}`) discharge each slot.  Then a uniform value bound
(`expJet3ValG_norm_le`, from `expJet3Fund_value_bound` + `expJet2Fund_value_bound_Icc`) and iterated
`mkContinuous₂`/`mkContinuous` assemble the third-derivative CLM `expJetD3`. -/

/-- **`Q`-congruence of `R^{hkl}(1)`.**  If the second-variation inputs `Qkl,Qhl,Qhk` agree on `[0,1]`
    with `Qkl',Qhl',Qhk'`, then `expJet3Val` is unchanged: both chosen witnesses solve the same IVP on
    `[0,1]` (the source `expJet3Rhs` at `t` depends on the `Q··` only through their value at `t`), so
    `expJet3Fund_unique` forces the endpoint values to coincide.  This is the value-only interface that
    lets us feed the genuine bilinear curves, whose combined/sum forms agree on `[0,1]` but not
    globally. -/
theorem expJet3Val_congr (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk Qkl' Qhl' Qhk' : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQkl' : ContinuousOn Qkl' (Set.Icc (0 : ℝ) 1)) (hQhl' : ContinuousOn Qhl' (Set.Icc (0 : ℝ) 1))
    (hQhk' : ContinuousOn Qhk' (Set.Icc (0 : ℝ) 1)) (h k l : Point n)
    (eKl : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qkl t = Qkl' t)
    (eHl : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qhl t = Qhl' t)
    (eHk : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qhk t = Qhk' t) :
    expJet3Val g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l
      = expJet3Val g gi hC p v Φ Qkl' Qhl' Qhk' hv hΦcont hQkl' hQhl' hQhk' h k l := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl' Qhl' Qhk' hv hΦcont hQkl' hQhl' hQhk' h k l).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ Qkl Qhl Qhk hv h k l
    (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose
    (expJet3Fund g gi hC p v Φ Qkl' Qhl' Qhk' hv hΦcont hQkl' hQhl' hQhk' h k l).choose
    hR₁0 hR₂0 hR₁deriv
    (fun t ht => by
      have he : (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl' Qhl' Qhk' hv hΦcont hQkl' hQhl' hQhk' h k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl' Qhl' Qhk' h k l t
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl' Qhl' Qhk' hv hΦcont hQkl' hQhl' hQhk' h k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t := by
        congr 1
        rw [expJet3Rhs_apply, expJet3Rhs_apply, eKl t ht, eHl t ht, eHk t ht]
      rw [← he]; exact hR₂deriv t ht)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet3Val] using h1

/-- **The genuine third-variation value** `R^{hkl}_v(1)` with the `Q··` slots instantiated by the
    genuine second-variation curves `expJet2Curve k l`, `expJet2Curve h l`, `expJet2Curve h k`.  This
    is plain-trilinear in `(h,k,l)` (below), the datum packaged into `expJetD3`. -/
noncomputable def expJet3ValG (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l : Point n) : Point n × Point n :=
  expJet3Val g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    h k l

/-- **Additivity of `expJet3ValG` in the `l`-slot.**  Bridge the combined genuine curves to their sums
    on `[0,1]` (`expJet2Curve_add_right`, `Qhk` fixed) via `expJet3Val_congr`, then apply the
    matched-`Q` fact `expJet3Val_add_l`. -/
theorem expJet3ValG_add_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l₁ l₂ : Point n) :
    expJet3ValG g gi hC p v Φ hv hΦcont h k (l₁ + l₂)
      = expJet3ValG g gi hC p v Φ hv hΦcont h k l₁ + expJet3ValG g gi hC p v Φ hv hΦcont h k l₂ := by
  have hbridge := expJet3Val_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k (l₁ + l₂))
      (expJet2Curve g gi hC p v Φ hv hΦcont h (l₁ + l₂))
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont k l₁ s
        + expJet2Curve g gi hC p v Φ hv hΦcont k l₂ s)
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h l₁ s
        + expJet2Curve g gi hC p v Φ hv hΦcont h l₂ s)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k (l₁ + l₂))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (l₁ + l₂))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₁).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₂))
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₁).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₂))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      h k (l₁ + l₂)
      (expJet2Curve_add_right g gi hC p v Φ hv hΦcont k l₁ l₂)
      (expJet2Curve_add_right g gi hC p v Φ hv hΦcont h l₁ l₂)
      (fun _ _ => rfl)
  simp only [expJet3ValG]
  rw [hbridge]
  exact expJet3Val_add_l g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l₁) (expJet2Curve g gi hC p v Φ hv hΦcont k l₂)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l₁) (expJet2Curve g gi hC p v Φ hv hΦcont h l₂)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₂)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₂)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l₁ l₂

/-- **ℝ-homogeneity of `expJet3ValG` in the `l`-slot** (`expJet2Curve_smul_right` + `expJet3Val_smul_l`). -/
theorem expJet3ValG_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l : Point n) :
    expJet3ValG g gi hC p v Φ hv hΦcont h k (c • l)
      = c • expJet3ValG g gi hC p v Φ hv hΦcont h k l := by
  have hbridge := expJet3Val_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k (c • l))
      (expJet2Curve g gi hC p v Φ hv hΦcont h (c • l))
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont k l s)
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h l s)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k (c • l))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (c • l))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l).const_smul c)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l).const_smul c)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      h k (c • l)
      (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c k l)
      (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c h l)
      (fun _ _ => rfl)
  simp only [expJet3ValG]
  rw [hbridge]
  exact expJet3Val_smul_l g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) c h k l

/-- **Additivity of `expJet3ValG` in the `h`-slot** (`expJet2Curve_add_left` on the two `h`-carrying
    curves `Qhl,Qhk`; `Qkl` fixed) + `expJet3Val_add_h`. -/
theorem expJet3ValG_add_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h₁ h₂ k l : Point n) :
    expJet3ValG g gi hC p v Φ hv hΦcont (h₁ + h₂) k l
      = expJet3ValG g gi hC p v Φ hv hΦcont h₁ k l + expJet3ValG g gi hC p v Φ hv hΦcont h₂ k l := by
  have hbridge := expJet3Val_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont (h₁ + h₂) l)
      (expJet2Curve g gi hC p v Φ hv hΦcont (h₁ + h₂) k)
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h₁ l s
        + expJet2Curve g gi hC p v Φ hv hΦcont h₂ l s)
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h₁ k s
        + expJet2Curve g gi hC p v Φ hv hΦcont h₂ k s)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (h₁ + h₂) l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (h₁ + h₂) k)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ l).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ l))
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ k).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ k))
      (h₁ + h₂) k l
      (fun _ _ => rfl)
      (expJet2Curve_add_left g gi hC p v Φ hv hΦcont h₁ h₂ l)
      (expJet2Curve_add_left g gi hC p v Φ hv hΦcont h₁ h₂ k)
  simp only [expJet3ValG]
  rw [hbridge]
  exact expJet3Val_add_h g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h₁ l) (expJet2Curve g gi hC p v Φ hv hΦcont h₂ l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h₁ k) (expJet2Curve g gi hC p v Φ hv hΦcont h₂ k)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ k) h₁ h₂ k l

/-- **ℝ-homogeneity of `expJet3ValG` in the `h`-slot** (`expJet2Curve_smul_left` + `expJet3Val_smul_h`). -/
theorem expJet3ValG_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l : Point n) :
    expJet3ValG g gi hC p v Φ hv hΦcont (c • h) k l
      = c • expJet3ValG g gi hC p v Φ hv hΦcont h k l := by
  have hbridge := expJet3Val_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont (c • h) l)
      (expJet2Curve g gi hC p v Φ hv hΦcont (c • h) k)
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h l s)
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h k s)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • h) l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • h) k)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l).const_smul c)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k).const_smul c)
      (c • h) k l
      (fun _ _ => rfl)
      (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c h l)
      (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c h k)
  simp only [expJet3ValG]
  rw [hbridge]
  exact expJet3Val_smul_h g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) c h k l

/-- **Additivity of `expJet3ValG` in the `k`-slot** (`expJet2Curve_add_left` on `Qkl` — `k` first —
    and `expJet2Curve_add_right` on `Qhk` — `k` second; `Qhl` fixed) + `expJet3Val_add_k`. -/
theorem expJet3ValG_add_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k₁ k₂ l : Point n) :
    expJet3ValG g gi hC p v Φ hv hΦcont h (k₁ + k₂) l
      = expJet3ValG g gi hC p v Φ hv hΦcont h k₁ l + expJet3ValG g gi hC p v Φ hv hΦcont h k₂ l := by
  have hbridge := expJet3Val_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont (k₁ + k₂) l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h (k₁ + k₂))
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont k₁ l s
        + expJet2Curve g gi hC p v Φ hv hΦcont k₂ l s)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h k₁ s
        + expJet2Curve g gi hC p v Φ hv hΦcont h k₂ s)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (k₁ + k₂) l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (k₁ + k₂))
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₁ l).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₂ l))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₁).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₂))
      h (k₁ + k₂) l
      (expJet2Curve_add_left g gi hC p v Φ hv hΦcont k₁ k₂ l)
      (fun _ _ => rfl)
      (expJet2Curve_add_right g gi hC p v Φ hv hΦcont h k₁ k₂)
  simp only [expJet3ValG]
  rw [hbridge]
  exact expJet3Val_add_k g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k₁ l) (expJet2Curve g gi hC p v Φ hv hΦcont k₂ l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k₁) (expJet2Curve g gi hC p v Φ hv hΦcont h k₂)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₁ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₂ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₂) h k₁ k₂ l

/-- **ℝ-homogeneity of `expJet3ValG` in the `k`-slot** (`expJet2Curve_smul_left` on `Qkl`,
    `expJet2Curve_smul_right` on `Qhk`) + `expJet3Val_smul_k`. -/
theorem expJet3ValG_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l : Point n) :
    expJet3ValG g gi hC p v Φ hv hΦcont h (c • k) l
      = c • expJet3ValG g gi hC p v Φ hv hΦcont h k l := by
  have hbridge := expJet3Val_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont (c • k) l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h (c • k))
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont k l s)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h k s)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • k) l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (c • k))
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l).const_smul c)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k).const_smul c)
      h (c • k) l
      (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c k l)
      (fun _ _ => rfl)
      (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c h k)
  simp only [expJet3ValG]
  rw [hbridge]
  exact expJet3Val_smul_k g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) c h k l

/-- **Uniform trilinear value bound for `expJet3ValG`.**  A single `M ≥ 0` (from the `[0,1]`
    Jacobi/`D³F`/`D²F` tube bounds `Kstar/Kstar3/Kstar2`, a compactness bound `Cphi = ⨆‖Φ‖`, and the
    curve value bound `‖Q^{··} t‖ ≤ M₂‖·‖‖·‖` from `expJet2Fund_value_bound_Icc`) with
    `‖expJet3ValG h k l‖ ≤ M·‖h‖·‖k‖·‖l‖` for ALL `(h,k,l)`.  Fed into the CLM packaging. -/
theorem expJet3ValG_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h k l : Point n,
      ‖expJet3ValG g gi hC p v Φ hv hΦcont h k l‖ ≤ M * ‖h‖ * ‖k‖ * ‖l‖ := by
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨Kstar3, hKstar30, hKstar3u⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar2, hKstar20, hKstar2u⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  have hKstar3 := hKstar3u v hv
  have hKstar2 := hKstar2u v hv
  obtain ⟨Cb, hCb⟩ := (isCompact_Icc).exists_bound_of_continuousOn hΦcont
  set Cphi : ℝ := max Cb 0 with hCphidef
  have hCphi0 : 0 ≤ Cphi := le_max_right _ _
  have hCphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi :=
    fun t ht => (hCb t ht).trans (le_max_left _ _)
  have hM₂0 : 0 ≤ Kstar2 * Cphi ^ 2 * Real.exp Kstar :=
    mul_nonneg (mul_nonneg hKstar20 (sq_nonneg _)) (Real.exp_pos _).le
  refine ⟨(Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi))
      * Real.exp Kstar,
    by positivity, fun h k l => ?_⟩
  -- curve value bounds on `[0,1]`
  obtain ⟨-, -, -, hQklderiv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont k l).choose_spec
  obtain ⟨-, -, -, hQhlderiv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h l).choose_spec
  obtain ⟨-, -, -, hQhkderiv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec
  have hQkl0 := ((expJet2Fund g gi hC p v Φ hv hΦcont k l).choose_spec).1
  have hQhl0 := ((expJet2Fund g gi hC p v Φ hv hΦcont h l).choose_spec).1
  have hQhk0 := ((expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec).1
  have hCqkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet2Curve g gi hC p v Φ hv hΦcont k l t‖ ≤ (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φ k l Kstar Kstar2 Cphi hKstar0 hKstar20 hCphi0
      hKstar hKstar2 hCphi (expJet2Curve g gi hC p v Φ hv hΦcont k l) hQkl0 hQklderiv
  have hCqhl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet2Curve g gi hC p v Φ hv hΦcont h l t‖ ≤ (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φ h l Kstar Kstar2 Cphi hKstar0 hKstar20 hCphi0
      hKstar hKstar2 hCphi (expJet2Curve g gi hC p v Φ hv hΦcont h l) hQhl0 hQhlderiv
  have hCqhk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet2Curve g gi hC p v Φ hv hΦcont h k t‖ ≤ (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φ h k Kstar Kstar2 Cphi hKstar0 hKstar20 hCphi0
      hKstar hKstar2 hCphi (expJet2Curve g gi hC p v Φ hv hΦcont h k) hQhk0 hQhkderiv
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet3Fund g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l).choose_spec
  have hbd := expJet3Fund_value_bound g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) h k l
    Kstar Kstar3 Kstar2 Cphi
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
    hKstar0 hKstar30 hKstar20 hCphi0 hKstar hKstar3 hKstar2 hCphi hCqkl hCqhl hCqhk
    _ hR0 hRderiv
  calc ‖expJet3ValG g gi hC p v Φ hv hΦcont h k l‖
      ≤ (Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖)
          + Kstar2 * (Cphi * ‖h‖) * ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
          + Kstar2 * (Cphi * ‖k‖) * ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
          + Kstar2 * (Cphi * ‖l‖) * ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖))
          * Real.exp Kstar := hbd
    _ = (Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi))
          * Real.exp Kstar * ‖h‖ * ‖k‖ * ‖l‖ := by ring

/-- **The inner (`k,h`)-bilinear slice `D³_v(l)` for a fixed `l`.**  `π(R^{hkl}_v(1))` as a genuine
    continuous BILINEAR map in `(k,h)`, from the `expJet3ValG` `k`/`h` linearity facts (`mk₂`) and the
    uniform bound `expJet3ValG_norm_le` (`‖π‖ ≤ 1`), via `LinearMap.mkContinuous₂`.  The bound constant
    is `M·‖l‖` with `M = expJet3ValG_norm_le.choose`. -/
noncomputable def expJetD3Inner (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (l : Point n) :
    Point n →L[ℝ] Point n →L[ℝ] Point n :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun k h => expJetPi (expJet3ValG g gi hC p v Φ hv hΦcont h k l))
      (fun k₁ k₂ h => by
        simp only [expJet3ValG_add_k g gi hC p v Φ hv hΦcont h k₁ k₂ l, map_add])
      (fun c k h => by
        simp only [expJet3ValG_smul_k g gi hC p v Φ hv hΦcont c h k l, map_smul])
      (fun k h₁ h₂ => by
        simp only [expJet3ValG_add_h g gi hC p v Φ hv hΦcont h₁ h₂ k l, map_add])
      (fun c k h => by
        simp only [expJet3ValG_smul_h g gi hC p v Φ hv hΦcont c h k l, map_smul]))
    ((expJet3ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖l‖)
    (fun k h => by
      have hb := (expJet3ValG_norm_le g gi hC p v Φ hv hΦcont).choose_spec.2 h k l
      simp only [LinearMap.mk₂_apply]
      calc ‖expJetPi (expJet3ValG g gi hC p v Φ hv hΦcont h k l)‖
          ≤ ‖expJetPi (n := n)‖ * ‖expJet3ValG g gi hC p v Φ hv hΦcont h k l‖ :=
            (expJetPi (n := n)).le_opNorm _
        _ ≤ 1 * ‖expJet3ValG g gi hC p v Φ hv hΦcont h k l‖ :=
            mul_le_mul_of_nonneg_right expJetPi_opNorm_le (norm_nonneg _)
        _ = ‖expJet3ValG g gi hC p v Φ hv hΦcont h k l‖ := one_mul _
        _ ≤ (expJet3ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖h‖ * ‖k‖ * ‖l‖ := hb
        _ = (expJet3ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖l‖ * ‖k‖ * ‖h‖ := by ring)

@[simp] theorem expJetD3Inner_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (l k h : Point n) :
    expJetD3Inner g gi hC p v Φ hv hΦcont l k h
      = expJetPi (expJet3ValG g gi hC p v Φ hv hΦcont h k l) := rfl

/-- Operator-norm bound for the inner slice: `‖D³_v(l)‖ ≤ M·‖l‖`. -/
theorem expJetD3Inner_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (l : Point n) :
    ‖expJetD3Inner g gi hC p v Φ hv hΦcont l‖
      ≤ (expJet3ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖l‖ := by
  unfold expJetD3Inner
  exact LinearMap.mkContinuous₂_norm_le _
    (mul_nonneg (expJet3ValG_norm_le g gi hC p v Φ hv hΦcont).choose_spec.1 (norm_nonneg _)) _

/-- **(4) The packaged third-derivative operator**
    `D³_v : Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n`, `D³_v(l)(k)(h) = π(R^{hkl}_v(1))` with
    the genuine second-variation curves in the `Q··` slots.  A genuine CONTINUOUS TRILINEAR map: the
    inner two slots `(k,h)` are `expJetD3Inner` (`mk₂` + `mkContinuous₂`), and the outer `l`-slot is
    assembled via `LinearMap.mkContinuous` (Mathlib has no `mkContinuous₃`), with `l`-linearity from
    `expJet3ValG_add_l/smul_l` and the bound `expJetD3Inner_norm_le`.  This is the CLM datum the
    (downstream) third-order Fréchet layer consumes. -/
noncomputable def expJetD3 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) :
    Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n :=
  LinearMap.mkContinuous
    { toFun := fun l => expJetD3Inner g gi hC p v Φ hv hΦcont l
      map_add' := fun l₁ l₂ => by
        refine ContinuousLinearMap.ext fun k => ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.add_apply, expJetD3Inner_apply,
          expJet3ValG_add_l g gi hC p v Φ hv hΦcont h k l₁ l₂, map_add]
      map_smul' := fun c l => by
        refine ContinuousLinearMap.ext fun k => ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply, expJetD3Inner_apply,
          expJet3ValG_smul_l g gi hC p v Φ hv hΦcont c h k l, map_smul] }
    (expJet3ValG_norm_le g gi hC p v Φ hv hΦcont).choose
    (fun l => expJetD3Inner_norm_le g gi hC p v Φ hv hΦcont l)

/-- **`expJetD3` application form.**  `D³_v(l)(k)(h) = π(R^{hkl}_v(1))` (genuine curves). -/
@[simp] theorem expJetD3_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (l k h : Point n) :
    expJetD3 g gi hC p v Φ hv hΦcont l k h
      = expJetPi (expJet3ValG g gi hC p v Φ hv hΦcont h k l) := by
  simp only [expJetD3, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    expJetD3Inner_apply]

/-! ### B-asm(3), pointwise stage — the per-`(h,k)` little-o of `fderiv² exp_p`

The Rung-3 mirror of the Rung-2 pointwise split `expMap_fderiv_sub_quadratic`, one Fréchet order up.
For fixed direction pair `(h,k)` and the first-variation propagators `Φ` (at `v`), `Φ'` (at `v+l`),
the second-derivative value `expJetD2_· k h = π(Q^{hk}_·(1))` obeys the quadratic-in-`l` little-o
`‖expJetD2_{v+l} k h − expJetD2_v k h − expJetD3_v(l) k h‖ ≤ C·‖l‖²`, i.e. the third derivative
`expJetD3_v(l)(k)(h) = π(R^{hkl}_v(1))` is the genuine directional Fréchet increment of
`v ↦ expJetD2_v k h` at `v` in direction `l`.

Assembly (mirror of `expMap_fderiv_sub_quadratic`): instantiate the abstract second-variation slots
`Qkl,Qhl,Qhk` of the Jet₃ third-variation ODE by the GENUINE second-variation curves
`expJet2Curve · l`, `expJet2Curve h ·`, `expJet2Curve h k` (so the third-variation witness `R`
coincides with the `expJet3ValG`/`expJetD3` datum); feed the `[0,1]`-uniform first-variation residuals
`expJet2FirstVar_residual_Icc` (⟹ `hFVh,hFVk`) and the `[0,1]`-uniform second-variation two-point
Lipschitz `expJet2_v_two_pt_Icc` (⟹ `hQlip`) into the Jet₃ quadratic remainder bound
`expJet3_remainder_quadratic_bound` (ρ = C·‖l‖²), then into the Jet₃ residual/Grönwall estimate
`expJet3_residual_bound`, giving `‖Q^{hk}_{v+l}(1) − Q^{hk}_v(1) − R^{hkl}_v(1)‖ ≤ C·‖l‖²·e^{Kstar}`;
finally project by `π` (`‖π‖ ≤ 1`), identifying `π(Q^{hk}(1)) = expJetD2 k h` (`expJetD2_apply`) and
`π(R^{hkl}(1)) = expJetD3(l) k h` (`expJetD3_apply`).

HONEST SCOPE: this is the per-`(h,k)` pointwise little-o; the constant `C` depends on `(h,k)` (through
the abstract Rung-2/Rung-3 remainder constants).  Promoting to the operator-norm CLM `HasFDerivAt`
(uniform over `‖h‖,‖k‖ ≤ 1`) — the analog of `expMap_fderiv_hasFDerivAt` — needs the `‖h‖·‖k‖`-separated
remainder, which is NOT available symbolically here (the `expJet2FirstVar_residual_Icc` constant is an
abstract `∃ C`, not `_·‖h‖`); that CLM packaging is the checkpointed next step.  This does NOT give
`ContDiff² (fderiv exp_p)` / `ContDiff³ exp_p`, NOT `κ = 1/6`, NOT the heat kernel / `a₁ = R/6`,
NOT QG. -/
set_option maxHeartbeats 3200000 in
/-- **Pointwise little-o of `fderiv² exp_p` (per direction pair `(h,k)`).**  For `Φ` the first-variation
    propagator witness at `v` and `Φ'` at `v+l` (both `Φ 0 = 1`, ODE law `Φ' = Ψ(Φ)`), and any `h,k`,
    `∃ C ≥ 0, ‖expJetD2_{v+l} Φ' k h − expJetD2_v Φ k h − expJetD3_v Φ (l) k h‖ ≤ C·‖l‖²`. -/
theorem expMap_fderiv2_sub_quadratic (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v l : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hvl : ‖v + l‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + l) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
    (h k : Point n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖expJetD2 g gi hC p (v + l) Φ' hvl hΦ'cont k h
          - expJetD2 g gi hC p v Φ hv hΦcont k h
          - expJetD3 g gi hC p v Φ hv hΦcont l k h‖ ≤ C * ‖l‖ ^ 2 := by
  -- IC/ODE specs of the second- and third-variation curves (via `choose_spec`; `expJet2Curve`,
  -- `expJet2Val`, `expJet3ValG` are all definitionally the corresponding `choose`).
  obtain ⟨hQv0, -, -, hQvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec
  obtain ⟨hQw0, -, -, hQwd⟩ := (expJet2Fund g gi hC p (v + l) Φ' hvl hΦ'cont h k).choose_spec
  obtain ⟨hQkl0, -, -, hQkld⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont k l).choose_spec
  obtain ⟨hQhl0, -, -, hQhld⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h l).choose_spec
  obtain ⟨hR0, -, -, hRd⟩ :=
    (expJet3Fund g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l).choose_spec
  -- Lipschitz constants + uniform tube bounds (for the two-point Lipschitz `(e)`).
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Kstar, hKstar0, hKstaru⟩ := expJet_fderiv_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar₂, hKstar₂0, hK2u⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  -- (e) `[0,1]`-uniform two-point Lipschitz of `Q^{hk}_v, Q^{hk}_{v+l}` ⟹ `hQlip`.
  obtain ⟨Ctp, hCtp0, htp⟩ := expJet2_v_two_pt_Icc g gi hC p v (v + l) hv hvl
    Kf Ldf Ld2f Kstar Kstar₂ hKstar0 hKstar₂0 hLipF hLipDF hLipD2 hKstaru hK2u
    Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k) h k hQv0 hQw0 hQvd hQwd
  have hQlip : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k t
          - expJet2Curve g gi hC p v Φ hv hΦcont h k t‖ ≤ (Ctp * ‖h‖ * ‖k‖) * ‖l‖ := by
    intro t ht
    rw [norm_sub_rev]
    have hh := htp t ht
    rw [show v - (v + l) = -l by abel, norm_neg] at hh
    calc ‖expJet2Curve g gi hC p v Φ hv hΦcont h k t
            - expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k t‖
        ≤ Ctp * ‖l‖ * ‖h‖ * ‖k‖ := hh
      _ = (Ctp * ‖h‖ * ‖k‖) * ‖l‖ := by ring
  -- `[0,1]`-uniform first-variation residuals ⟹ `hFVh, hFVk`.
  obtain ⟨Cdh, hCdh0, hFVh0⟩ := expJet2FirstVar_residual_Icc g gi hC p v Φ Φ'
    (expJet2Curve g gi hC p v Φ hv hΦcont h l) h l hv hvl hΦ0 hΦ'0 hQhl0 hΦcont hΦ'cont
    hΦd hΦ'd hQhld
  obtain ⟨Cdk, hCdk0, hFVk0⟩ := expJet2FirstVar_residual_Icc g gi hC p v Φ Φ'
    (expJet2Curve g gi hC p v Φ hv hΦcont k l) k l hv hvl hΦ0 hΦ'0 hQkl0 hΦcont hΦ'cont
    hΦd hΦ'd hQkld
  -- the Jet₃ quadratic remainder bound `‖source(t)‖ ≤ Crem·‖l‖²`.
  obtain ⟨Crem, hCrem0, hrem⟩ := expJet3_remainder_quadratic_bound g gi hC p v (v + l) l rfl
    hv hvl Φ Φ'
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) h k hΦ0 hΦ'0 hΦd hΦ'd hQw0 hQwd rfl
    (max Cdh Cdk) (Ctp * ‖h‖ * ‖k‖)
    (le_trans hCdh0 (le_max_left _ _))
    (mul_nonneg (mul_nonneg hCtp0 (norm_nonneg _)) (norm_nonneg _))
    (fun t ht => (hFVh0 t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
    (fun t ht => (hFVk0 t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)))
    hQlip
  -- the `[0,1]` Jacobi bound at `v` and the Jet₃ residual/Grönwall estimate.
  obtain ⟨Kv, hKv0, hKv⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  have hres := expJet3_residual_bound g gi hC p v (v + l) Φ Φ'
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet3Fund g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l).choose
    h k l hQv0 hQw0 hR0 hQvd hQwd hRd Kv (Crem * ‖l‖ ^ 2) hKv0
    (mul_nonneg hCrem0 (sq_nonneg _)) hKv (fun t ht => hrem t ht)
  -- project by `π`, identify the value forms.
  refine ⟨Crem * Real.exp Kv, mul_nonneg hCrem0 (Real.exp_pos _).le, ?_⟩
  rw [expJetD2_apply, expJetD2_apply, expJetD3_apply]
  calc ‖expJetPi (expJet2Val g gi hC p (v + l) Φ' hvl hΦ'cont h k)
          - expJetPi (expJet2Val g gi hC p v Φ hv hΦcont h k)
          - expJetPi (expJet3ValG g gi hC p v Φ hv hΦcont h k l)‖
      = ‖expJetPi (expJet2Val g gi hC p (v + l) Φ' hvl hΦ'cont h k
            - expJet2Val g gi hC p v Φ hv hΦcont h k
            - expJet3ValG g gi hC p v Φ hv hΦcont h k l)‖ := by rw [map_sub, map_sub]
    _ ≤ ‖expJetPi (n := n)‖ * ‖expJet2Val g gi hC p (v + l) Φ' hvl hΦ'cont h k
            - expJet2Val g gi hC p v Φ hv hΦcont h k
            - expJet3ValG g gi hC p v Φ hv hΦcont h k l‖ :=
        (expJetPi (n := n)).le_opNorm _
    _ ≤ 1 * ‖expJet2Val g gi hC p (v + l) Φ' hvl hΦ'cont h k
            - expJet2Val g gi hC p v Φ hv hΦcont h k
            - expJet3ValG g gi hC p v Φ hv hΦcont h k l‖ :=
        mul_le_mul_of_nonneg_right expJetPi_opNorm_le (norm_nonneg _)
    _ = ‖expJet2Val g gi hC p (v + l) Φ' hvl hΦ'cont h k
            - expJet2Val g gi hC p v Φ hv hΦcont h k
            - expJet3ValG g gi hC p v Φ hv hΦcont h k l‖ := one_mul _
    _ ≤ (Crem * ‖l‖ ^ 2) * Real.exp Kv := hres
    _ = Crem * Real.exp Kv * ‖l‖ ^ 2 := by ring

/-! ### Rung-3 sub-brick — the `‖h‖`/`‖k‖`-SEPARATED primed remainder bounds

The 3rd-derivative CLM `HasFDerivAt` needs the pointwise little-o `‖A_l k h‖ ≤ C‖l‖²` with the
constant SEPARATED as `C₀·‖h‖·‖k‖` (`C₀` independent of `h,k`), so that
`ContinuousLinearMap.opNorm_le_bound₂` yields `‖A_l‖_op ≤ C₀‖l‖²`.  The two abstract-`∃C` residual
bounds `expJet2FirstVar_residual_Icc` / `expJet3_remainder_quadratic_bound` are NOT yet
`‖h‖`/`‖k‖`-separated.  Here we land their primed (separated) mirrors, keeping the direction norms
explicit throughout instead of folding them into the constant. -/

set_option maxHeartbeats 3200000 in
/-- **The `‖h‖`-separated first-variation residual bound.**  The `‖h‖`-out mirror of
    `expJet2FirstVar_residual_Icc`: the probe `h` is universally quantified and the constant `C₀` is
    INDEPENDENT of `h` — the residual is measured against the GENUINE `(h,l)` second-variation curve
    `expJet2Curve … h l` (so its `h`-linearity stays available downstream), and the `‖h‖` factor is
    pulled out explicitly.  Copies `expJet2FirstVar_residual_Icc`'s proof, feeding the `‖h‖`-separated
    Rung-2 remainder bound `expJet2_remainder_quadratic_bound'` and threading `‖h‖` through the vector
    Grönwall. -/
theorem expJet2FirstVar_residual_Icc' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (l : Point n)
    (hv : ‖v‖ ≤ expRho g gi hC p) (hvl : ‖v + l‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + l) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (h : Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota h) - Φ t (expJetIota h)
          - expJet2Curve g gi hC p v Φ hv hΦcont h l t‖ ≤ C₀ * ‖h‖ * ‖l‖ ^ 2 := by
  -- (i) the `‖h‖`-separated Rung-2 quadratic remainder of the residual ODE source (direction `k := l`).
  obtain ⟨Cr, hCr0, hrbd⟩ := expJet2_remainder_quadratic_bound' g gi hC p v l Φ Φ'
    hv hvl hΦ0 hΦ'0 hΦcont hΦ'cont hΦd hΦ'd
  -- (ii) the `[0,1]` Jacobi bound on `‖DF(Y_v t)‖`.
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  refine ⟨Cr * Real.exp Kstar, mul_nonneg hCr0 (Real.exp_pos _).le, fun h t ht => ?_⟩
  -- (iii) the genuine `(h,l)` second-variation curve's IC/ODE spec (`expJet2Curve = choose`).
  obtain ⟨hQ0, -, -, hQd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h l).choose_spec
  -- (iv) residual ODE + `[0,1]`-uniform vector Grönwall, source `ρ = Cr·‖h‖·‖l‖²`.
  have hgron := gronwall_vec_residual_Icc
    (fun s => Φ' s (expJetIota h) - Φ s (expJetIota h)
      - expJet2Curve g gi hC p v Φ hv hΦcont h l s)
    (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + l) s)
        - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Φ' s (expJetIota h))
      - expJet2Rhs g gi hC p v Φ h l s)
    (fun s => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) Kstar (Cr * ‖h‖ * ‖l‖ ^ 2)
    hKstar0 (mul_nonneg (mul_nonneg hCr0 (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 2))
    (by simp only [expJet2Curve, hΦ0, hΦ'0, ContinuousLinearMap.id_apply, hQ0, sub_self])
    (fun s hs => expJet2_residual_hasDerivWithinAt g gi hC p v (v + l) Φ Φ'
      (expJet2Curve g gi hC p v Φ hv hΦcont h l) h l hΦd hΦ'd hQd s hs)
    hKstar (fun s hs => hrbd h s hs) t ht
  calc ‖Φ' t (expJetIota h) - Φ t (expJetIota h)
          - expJet2Curve g gi hC p v Φ hv hΦcont h l t‖
      ≤ (Cr * ‖h‖ * ‖l‖ ^ 2) * Real.exp Kstar := hgron
    _ = Cr * Real.exp Kstar * ‖h‖ * ‖l‖ ^ 2 := by ring

set_option maxHeartbeats 4000000 in
/-- **The `‖h‖‖k‖`-separated Jet₃ quadratic remainder bound.**  The `‖h‖‖k‖`-out mirror of
    `expJet3_remainder_quadratic_bound`: the constant `C₀` is INDEPENDENT of `h,k`, the `‖h‖·‖k‖`
    factor being pulled out explicitly.  The proof is `expJet3_remainder_quadratic_bound`'s verbatim,
    fed the `‖h‖`-separated first-variation residuals (`hFVh = Cd·‖h‖·‖l‖²`, `hFVk = Cd·‖k‖·‖l‖²`) and
    the already-`‖h‖‖k‖`-carrying two-point Lipschitz (`hQlip = Ce·‖h‖·‖k‖·‖l‖`, from
    `expJet2_v_two_pt_Icc`); every per-term bound already carries `‖h‖`, `‖k‖` as single factors, so
    they are pulled out of the witness constant. -/
theorem expJet3_remainder_quadratic_bound' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w l : Point n) (hwl : w = v + l)
    (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qv Qw Qkl Qhl Qhk : ℝ → (Point n × Point n)) (h k : Point n)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p w t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
    (hQw0 : Qw 0 = 0)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qw
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
           + expJet2Rhs g gi hC p w Φ' h k t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkv : Qhk = Qv)
    (Cd Ce : ℝ) (hCd0 : 0 ≤ Cd) (hCe0 : 0 ≤ Ce)
    (hFVh : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota h) - Φ t (expJetIota h) - Qhl t‖ ≤ Cd * ‖h‖ * ‖l‖ ^ 2)
    (hFVk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota k) - Φ t (expJetIota k) - Qkl t‖ ≤ Cd * ‖k‖ * ‖l‖ ^ 2)
    (hQlip : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qw t - Qv t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖l‖) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
         + (expJet2Rhs g gi hC p w Φ' h k t
            - expJet2Rhs g gi hC p v Φ h k t
            - expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)‖ ≤ C₀ * ‖h‖ * ‖k‖ * ‖l‖ ^ 2 := by
  subst hwl
  have hC₀ := expConst_nonneg g gi hC p
  -- ── Lipschitz constants on the confined tube ball ──────────────────────────────────────────
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Ld3f, hLipD3⟩ := expJet_fderiv3_lipschitzOnWith g gi hC p
  -- ── tube bounds ────────────────────────────────────────────────────────────────────────────
  obtain ⟨Kvb, hKvb0, hKvbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨Kwb, _hKwb0, hKwbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p (v + l) hw
  obtain ⟨Kstar2, hKstar20, hD2bd⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hD3bd⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  -- ── real constants ─────────────────────────────────────────────────────────────────────────
  set eKf : ℝ := Real.exp (Kf : ℝ) with heKf
  have heKf0 : 0 ≤ eKf := (Real.exp_pos _).le
  set Kstar : ℝ := max Kvb Kwb with hKstardef
  have hKstar0 : 0 ≤ Kstar := le_max_of_le_left hKvb0
  set eKs : ℝ := Real.exp Kstar with heKs
  have heKs0 : 0 ≤ eKs := (Real.exp_pos _).le
  set M : ℝ := (Ldf : ℝ) with hMdef
  have hM0 : 0 ≤ M := Ldf.coe_nonneg
  set L2 : ℝ := (Ld2f : ℝ) with hL2def
  have hL2_0 : 0 ≤ L2 := Ld2f.coe_nonneg
  set L3 : ℝ := (Ld3f : ℝ) with hL3def
  have hL3_0 : 0 ≤ L3 := Ld3f.coe_nonneg
  set C2 : ℝ := M * eKf ^ 2 * eKs with hC2def
  have hC2_0 : 0 ≤ C2 := by rw [hC2def]; positivity
  set C3 : ℝ := M * eKf * eKs * eKs with hC3def
  have hC3_0 : 0 ≤ C3 := by rw [hC3def]; positivity
  set CQ : ℝ := Kstar2 * eKs ^ 2 * eKs with hCQdef
  have hCQ0 : 0 ≤ CQ := by rw [hCQdef]; positivity
  -- Lipschitz constants in `.toNNReal` shape.
  have hLipDF_M : LipschitzOnWith M.toNNReal (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hMdef, Real.toNNReal_coe]; exact hLipDF
  have hLipD2R : LipschitzOnWith L2.toNNReal (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL2def, Real.toNNReal_coe]; exact hLipD2
  have hLipD3R : LipschitzOnWith L3.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL3def, Real.toNNReal_coe]; exact hLipD3
  -- ── uniform `[0,1]` DF/D²F/D³F bounds ──────────────────────────────────────────────────────
  have hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar :=
    fun t ht => (hKvbd t ht).trans (le_max_left Kvb Kwb)
  have hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + l) t)‖ ≤ Kstar :=
    fun t ht => (hKwbd t ht).trans (le_max_right Kvb Kwb)
  have hK2v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2 :=
    fun t ht => hD2bd v hv t ht
  have hK2w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + l) t)‖ ≤ Kstar2 :=
    fun t ht => hD2bd (v + l) hw t ht
  have hK3v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3 :=
    fun t ht => hD3bd v hv t ht
  -- ── `Φ`, `Φ'` op-norm bounds on `[0,1]` ────────────────────────────────────────────────────
  have hΦnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p v Φ Kstar hKstar0 hKstarv hΦ0 hΦd
  have hΦ'norm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p (v + l) Φ' Kstar hKstar0 hKstarw hΦ'0 hΦ'd
  -- ── tube-ball memberships and separation ───────────────────────────────────────────────────
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  obtain ⟨hY0w, hYdw, hconfw⟩ := expTube_spec g gi hC p (v + l) hw
  have hmemv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfv t ht).trans (mul_le_mul_of_nonneg_left hv hC₀)
  have hmemw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + l) t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfw t ht).trans (mul_le_mul_of_nonneg_left hw hC₀)
  have hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + l) t - expTube g gi hC p v t‖ ≤ ‖l‖ * eKf := by
    have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdist0 : dist (expTube g gi hC p (v + l) 0) (expTube g gi hC p v 0) = ‖l‖ := by
      rw [hY0w, hY0v, dist_eq_norm, Prod.mk_sub_mk, add_sub_cancel_left, sub_self, Prod.norm_def,
        norm_zero, max_eq_right (norm_nonneg _)]
    have htwo := geodesic_twopoint_gronwall g gi
      (S := Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p))
      (K := Kf) hLipF
      (fun t ht => hYdw t (hIcc_Ioo t ht)) (fun t ht => hYdv t (hIcc_Ioo t ht)) hmemw hmemv
    intro t ht
    have hh := htwo t ht
    rw [hdist0, dist_eq_norm] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  -- ── the landed ingredient bounds (as `∀ t ∈ [0,1]` families) ───────────────────────────────
  have htay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + l) t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
              (expTube g gi hC p (v + l) t - expTube g gi hC p v t)‖
        ≤ L2 * ‖expTube g gi hC p (v + l) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_DF_second_order_taylor g gi hC p L2 hL2_0 hLipD2R
      (expTube g gi hC p v t) (expTube g gi hC p (v + l) t) (hmemv t ht) (hmemw t ht)
  have hD2tay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + l) t)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
              (expTube g gi hC p (v + l) t - expTube g gi hC p v t)‖
        ≤ L3 * ‖expTube g gi hC p (v + l) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_D2F_second_order_taylor g gi hC p L3 hL3_0 hLipD3R
      (expTube g gi hC p v t) (expTube g gi hC p (v + l) t) (hmemv t ht) (hmemw t ht)
  have hacc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + l) t - expTube g gi hC p v t - Φ t (expJetIota l)‖ ≤ C2 * ‖l‖ ^ 2 :=
    fun t ht => expTube_second_order_accuracy g gi hC p v l hw hv M hM0 Kf Kstar hKstar0
      hLipF hLipDF_M hKstarv Φ hΦ0 hΦd t ht
  have hQwval : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qw t‖ ≤ CQ * ‖h‖ * ‖k‖ :=
    expJet2Fund_value_bound_Icc g gi hC p (v + l) Φ' h k Kstar Kstar2 eKs
      hKstar0 hKstar20 heKs0 hKstarw hK2w hΦ'norm Qw hQw0 hQwd
  have htwopt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t - Φ' t‖ ≤ C3 * ‖l‖ := by
    have hbase := expFund_two_pt_diff_Icc g gi hC p v (v + l) Kf Ldf Kstar hKstar0
      hLipF hLipDF hKstarv hKstarw hv hw Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    intro t ht
    have hb := hbase t ht
    rw [show v - (v + l) = -l by abel, norm_neg] at hb
    exact hb
  -- ── iota norm bounds ───────────────────────────────────────────────────────────────────────
  have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ :=
    ((expJetIota (n := n)).le_opNorm h).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h))
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ :=
    ((expJetIota (n := n)).le_opNorm k).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k))
  have hιl : ‖expJetIota (n := n) l‖ ≤ ‖l‖ :=
    ((expJetIota (n := n)).le_opNorm l).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg l))
  -- ── the `h,k`-independent witness constant and the per-`t` chain ────────────────────────────
  refine ⟨L2 * eKf ^ 2 * CQ + Kstar2 * C2 * CQ + Kstar2 * eKs * Ce
      + L3 * eKf ^ 2 * eKs ^ 2 + Kstar3 * C2 * eKs ^ 2
      + Kstar3 * eKs ^ 2 * C3 + Kstar3 * eKs ^ 2 * C3
      + Kstar2 * C3 ^ 2 + Kstar2 * Cd * eKs + Kstar2 * eKs * Cd, ?_, ?_⟩
  · positivity
  · intro t ht
    rw [hQhkv]
    simp only [expJet2Rhs_apply, expJet3Rhs_apply]
    set yv := expTube g gi hC p v t with hyvE
    set yw := expTube g gi hC p (v + l) t with hywE
    set dv := fderiv ℝ (geodesicField g gi) yv with hdvE
    set dw := fderiv ℝ (geodesicField g gi) yw with hdwE
    set d2v := fderiv ℝ (fderiv ℝ (geodesicField g gi)) yv with hd2vE
    set d2w := fderiv ℝ (fderiv ℝ (geodesicField g gi)) yw with hd2wE
    set d3v := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) yv with hd3vE
    set ph := Φ t (expJetIota h) with hphE
    set pk := Φ t (expJetIota k) with hpkE
    set pl := Φ t (expJetIota l) with hplE
    set ph' := Φ' t (expJetIota h) with hph'E
    set pk' := Φ' t (expJetIota k) with hpk'E
    set qv := Qv t with hqvE
    set qw := Qw t with hqwE
    set qkl := Qkl t with hqklE
    set qhl := Qhl t with hqhlE
    -- derived vector/CLM bounds at this `t`.
    have hph : ‖ph‖ ≤ eKs * ‖h‖ := clmApply_norm_le (Φ t) (expJetIota h) heKs0 (hΦnorm t ht) hιh
    have hpk : ‖pk‖ ≤ eKs * ‖k‖ := clmApply_norm_le (Φ t) (expJetIota k) heKs0 (hΦnorm t ht) hιk
    have hpl : ‖pl‖ ≤ eKs * ‖l‖ := clmApply_norm_le (Φ t) (expJetIota l) heKs0 (hΦnorm t ht) hιl
    have hph' : ‖ph'‖ ≤ eKs * ‖h‖ :=
      clmApply_norm_le (Φ' t) (expJetIota h) heKs0 (hΦ'norm t ht) hιh
    have hpk' : ‖pk'‖ ≤ eKs * ‖k‖ :=
      clmApply_norm_le (Φ' t) (expJetIota k) heKs0 (hΦ'norm t ht) hιk
    have hd2n : ‖d2v‖ ≤ Kstar2 := hK2v t ht
    have hd3n : ‖d3v‖ ≤ Kstar3 := hK3v t ht
    have hph'ph : ‖ph' - ph‖ ≤ C3 * ‖l‖ * ‖h‖ := by
      have hsub : ph' - ph = (Φ' t - Φ t) (expJetIota h) := by
        rw [ContinuousLinearMap.sub_apply]
      rw [hsub]
      calc ‖(Φ' t - Φ t) (expJetIota h)‖
          ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) h‖ := (Φ' t - Φ t).le_opNorm _
        _ ≤ (C3 * ‖l‖) * ‖h‖ :=
            mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιh (norm_nonneg _) (by positivity)
        _ = C3 * ‖l‖ * ‖h‖ := by ring
    have hpk'pk : ‖pk' - pk‖ ≤ C3 * ‖l‖ * ‖k‖ := by
      have hsub : pk' - pk = (Φ' t - Φ t) (expJetIota k) := by
        rw [ContinuousLinearMap.sub_apply]
      rw [hsub]
      calc ‖(Φ' t - Φ t) (expJetIota k)‖
          ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) k‖ := (Φ' t - Φ t).le_opNorm _
        _ ≤ (C3 * ‖l‖) * ‖k‖ :=
            mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιk (norm_nonneg _) (by positivity)
        _ = C3 * ‖l‖ * ‖k‖ := by ring
    -- ── the cancellation identity ──────────────────────────────────────────────────────────
    have heq :
        (dw - dv) qw
          + (d2w ph' pk' - d2v ph pk
             - (d3v ph pk pl + d2v ph qkl + d2v pk qhl + d2v pl qv))
        = (dw - dv - d2v (yw - yv)) qw
          + (d2v (yw - yv - pl)) qw
          + (d2v pl) (qw - qv)
          + (d2w - d2v - d3v (yw - yv)) ph' pk'
          + d3v (yw - yv - pl) ph' pk'
          + d3v pl (ph' - ph) pk'
          + d3v pl ph (pk' - pk)
          + d2v (ph' - ph) (pk' - pk)
          + d2v (ph' - ph - qhl) pk
          + d2v ph (pk' - pk - qkl) := by
      have hcyc : d3v pl ph pk = d3v ph pk pl :=
        fderiv3_geodesicField_symm_cyc g gi hC yv pl ph pk
      have hsym : d2v qhl pk = d2v pk qhl :=
        fderiv2_geodesicField_symm g gi hC yv qhl pk
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      rw [hcyc, hsym]
      abel
    rw [heq]
    -- ── the ten `O(‖l‖²)` per-term bounds (each carries `‖h‖·‖k‖`) ────────────────────────────
    have hbA : ‖(dw - dv - d2v (yw - yv)) qw‖ ≤ (L2 * eKf ^ 2 * CQ * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 := by
      calc ‖(dw - dv - d2v (yw - yv)) qw‖
          ≤ ‖dw - dv - d2v (yw - yv)‖ * ‖qw‖ := (dw - dv - d2v (yw - yv)).le_opNorm _
        _ ≤ (L2 * ‖yw - yv‖ ^ 2) * (CQ * ‖h‖ * ‖k‖) :=
            mul_le_mul (htay t ht) (hQwval t ht) (norm_nonneg _) (by positivity)
        _ ≤ (L2 * (‖l‖ * eKf) ^ 2) * (CQ * ‖h‖ * ‖k‖) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hsep t ht) 2) hL2_0)
              (by positivity)
        _ = (L2 * eKf ^ 2 * CQ * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 := by ring
    have hbB : ‖(d2v (yw - yv - pl)) qw‖ ≤ (Kstar2 * C2 * CQ * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply2_norm_le d2v (yw - yv - pl) qw hKstar20 (by positivity) hd2n
        (hacc t ht) (hQwval t ht)).trans (le_of_eq (by ring))
    have hbC : ‖(d2v pl) (qw - qv)‖ ≤ (Kstar2 * eKs * Ce * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply2_norm_le d2v pl (qw - qv) hKstar20 (by positivity) hd2n hpl
        (hQlip t ht)).trans (le_of_eq (by ring))
    have hbE1 : ‖(d2w - d2v - d3v (yw - yv)) ph' pk'‖
        ≤ (L3 * eKf ^ 2 * eKs ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 := by
      calc ‖(d2w - d2v - d3v (yw - yv)) ph' pk'‖
          ≤ (L3 * ‖yw - yv‖ ^ 2) * (eKs * ‖h‖) * (eKs * ‖k‖) :=
            clmApply2_norm_le _ ph' pk' (by positivity) (by positivity) (hD2tay t ht) hph' hpk'
        _ ≤ (L3 * (‖l‖ * eKf) ^ 2) * (eKs * ‖h‖) * (eKs * ‖k‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hsep t ht) 2) hL3_0)
              (by positivity)) (by positivity)
        _ = (L3 * eKf ^ 2 * eKs ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 := by ring
    have hbE2 : ‖d3v (yw - yv - pl) ph' pk'‖
        ≤ (Kstar3 * C2 * eKs ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply3_norm_le d3v (yw - yv - pl) ph' pk' hKstar30 (by positivity) (by positivity)
        hd3n (hacc t ht) hph' hpk').trans (le_of_eq (by ring))
    have hbE3 : ‖d3v pl (ph' - ph) pk'‖ ≤ (Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply3_norm_le d3v pl (ph' - ph) pk' hKstar30 (by positivity) (by positivity)
        hd3n hpl hph'ph hpk').trans (le_of_eq (by ring))
    have hbE4 : ‖d3v pl ph (pk' - pk)‖ ≤ (Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply3_norm_le d3v pl ph (pk' - pk) hKstar30 (by positivity) (by positivity)
        hd3n hpl hph hpk'pk).trans (le_of_eq (by ring))
    have hbE5 : ‖d2v (ph' - ph) (pk' - pk)‖ ≤ (Kstar2 * C3 ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply2_norm_le d2v (ph' - ph) (pk' - pk) hKstar20 (by positivity) hd2n
        hph'ph hpk'pk).trans (le_of_eq (by ring))
    have hbE6 : ‖d2v (ph' - ph - qhl) pk‖ ≤ (Kstar2 * Cd * eKs * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply2_norm_le d2v (ph' - ph - qhl) pk hKstar20 (by positivity) hd2n
        (hFVh t ht) hpk).trans (le_of_eq (by ring))
    have hbE7 : ‖d2v ph (pk' - pk - qkl)‖ ≤ (Kstar2 * eKs * Cd * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 :=
      (clmApply2_norm_le d2v ph (pk' - pk - qkl) hKstar20 (by positivity) hd2n
        hph (hFVk t ht)).trans (le_of_eq (by ring))
    -- ── combine via the triangle inequality ──────────────────────────────────────────────────
    rw [show (L2 * eKf ^ 2 * CQ + Kstar2 * C2 * CQ + Kstar2 * eKs * Ce
          + L3 * eKf ^ 2 * eKs ^ 2 + Kstar3 * C2 * eKs ^ 2
          + Kstar3 * eKs ^ 2 * C3 + Kstar3 * eKs ^ 2 * C3
          + Kstar2 * C3 ^ 2 + Kstar2 * Cd * eKs + Kstar2 * eKs * Cd)
          * ‖h‖ * ‖k‖ * ‖l‖ ^ 2
        = (L2 * eKf ^ 2 * CQ * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 + (Kstar2 * C2 * CQ * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar2 * eKs * Ce * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (L3 * eKf ^ 2 * eKs ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar3 * C2 * eKs ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar3 * eKs ^ 2 * C3 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 + (Kstar2 * C3 ^ 2 * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar2 * Cd * eKs * ‖h‖ * ‖k‖) * ‖l‖ ^ 2
          + (Kstar2 * eKs * Cd * ‖h‖ * ‖k‖) * ‖l‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE7)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE6)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE5)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE4)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE3)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE2)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbE1)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbC)
    refine (norm_add_le _ _).trans (add_le_add hbA hbB)

end QIQTH.ExpMap
