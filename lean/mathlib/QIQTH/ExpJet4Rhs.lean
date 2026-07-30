/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapContDiff3
import QIQTH.ExpMapContDiff4
import QIQTH.GeodesicFieldJets
import Mathlib

/-!
# The Jet₄ fourth-variation ODE right-hand-side field `expJet4Rhs`

This file lands the **J4-1 brick** of the JET-4 TOWER campaign (`docs/qg_roadmap/JET4_TOWER_PLAN.md`)
toward the truly-unconditional `a₁ = R/6`: the fourth-variation ODE inhomogeneous source
`expJet4Rhs`, a FAITHFUL MIRROR one Fréchet-derivative order higher of the landed `expJet3Rhs`
(`ExpMapContDiff3.lean`).

The fourth variation `R^{hklm}(t)` of the confined geodesic flow solves the INHOMOGENEOUS linear ODE
`R'(t) = DF(Y_v t)·R(t) + Θ₄^{hklm}(t)`, `R(0) = 0`, whose homogeneous part is propagated by the
built first-variation fundamental solution `Φ_v`.  The inhomogeneous SOURCE `Θ₄^{hklm}` is the
FOURTEEN-term fourth-variation inhomogeneity obtained by differentiating the Jet₃ source `Θ₃^{hkl}`
once more (product/chain rule, adding the direction `m`), i.e. the next level of the Faà-di-Bruno
expansion.  With `P^x = Φ(ι x)` the first variations, `Q^{xy}` the second variations and `Q^{xyz}`
the third variations (abstract `∃`-object arguments, exactly as `Φ`/`Q` are abstract arguments of
`expJet3Rhs`), the fourteen terms are one term for each partition of `{h,k,l,m}` other than the single
full block (which feeds the homogeneous `DF·R` term):

* **`1+1+1+1`** (one term): `D⁴F(P^h)(P^k)(P^l)(P^m)`;
* **`2+1+1`** (six terms): `D³F(P^·)(P^·)(Q^{··})` — one second-variation pair, two first variations;
* **`2+2`** (three terms): `D²F(Q^{··})(Q^{··})` — two second-variation pairs;
* **`3+1`** (four terms): `D²F(P^·)(Q^{···})` — one first variation, one third variation,

with `D⁴F = fderiv (fderiv (fderiv (fderiv F)))` (`contDiff_fderiv4_geodesicField`),
`D³F = fderiv (fderiv (fderiv F))` (`contDiff_fderiv3_geodesicField`),
`D²F = fderiv (fderiv F)` (`contDiff_fderiv2_geodesicField`), `Y_v t = expTube p v t`,
`ι = expJetIota`.

This brick delivers the source `def` (`expJet4Rhs`), its unfolding lemma (`expJet4Rhs_apply`), its
`[0,1]` continuity (`expJet4Rhs_continuousOn`) and its uniform `[0,1]` norm bound
(`expJet4Rhs_norm_le`) — the Jet₄ well-posedness data the (next) `expJet4Fund` construction consumes.

## Honest firewall (binding)

**What is proven here:** the definition, continuity and norm bound of the fourth-variation ODE source
field `Θ₄^{hklm}` — a mechanical one-order-higher mirror of the `expJet3Rhs` block.

**What is NOT closed:** this does NOT build the Jet₄ fourth-variation fundamental solution
(`expJet4Fund`), does NOT discharge `hfd3` / `ContDiff¹ (fderiv³ exp_p)`, does NOT establish
`exp_p ∈ C⁴`, does NOT reach `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`, and is NOT
numerical-`G` / the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

-- The codomain of `D⁴F` is a QUADRUPLY-nested continuous-linear-map space
-- `E →L E →L E →L E →L E`; its normed-group instance chains one level deeper than the `D³F` case, so
-- we raise the pending-instance synthesis depth (exactly as in `ExpMapContDiff4.lean`).
set_option maxSynthPendingDepth 4

variable {n : ℕ}

/-! ### Generic multilinear CLM-application norm bounds

Local copies of the `ExpMapContDiff3` private helpers, plus one order higher (`clmApply4_norm_le`).
Kept fully generic (abstract normed spaces, no tube atoms) so the quadruply-nested-CLM `whnf` never
fires here. -/

/-- **Generic CLM-application norm bound.**  `‖C a‖ ≤ KC · Ka`. -/
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

/-- **Generic trilinear CLM-application norm bound.**  `‖B a b c‖ ≤ KB · Ka · Kb · Kc`. -/
private theorem clmApply3_norm_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] H) (a : E) (b : F) (c : G) {KB Ka Kb Kc : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) (hc : ‖c‖ ≤ Kc) :
    ‖B a b c‖ ≤ KB * Ka * Kb * Kc :=
  clmApply2_norm_le (B a) b c (mul_nonneg hKB hKa) hKb (clmApply_norm_le B a hKB hB ha) hb hc

/-- **Generic quadrilinear CLM-application norm bound.**  `‖B a b c d‖ ≤ KB · Ka · Kb · Kc · Kd`.
    The direct one-order-higher analog of `clmApply3_norm_le`: apply the outer `B` to `a`
    (`clmApply_norm_le`), then the resulting trilinear CLM `B a` to `b, c, d`
    (`clmApply3_norm_le`).  Kept generic so the quadruply-nested-CLM `whnf` never fires. -/
private theorem clmApply4_norm_le {E F G H I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup I] [NormedSpace ℝ I]
    (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] H →L[ℝ] I) (a : E) (b : F) (c : G) (d : H)
    {KB Ka Kb Kc Kd : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKc : 0 ≤ Kc)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) (hc : ‖c‖ ≤ Kc) (hd : ‖d‖ ≤ Kd) :
    ‖B a b c d‖ ≤ KB * Ka * Kb * Kc * Kd :=
  clmApply3_norm_le (B a) b c d (mul_nonneg hKB hKa) hKb hKc
    (clmApply_norm_le B a hKB hB ha) hb hc hd

/-! ### The Jet₄ fourth-variation ODE source `Θ₄^{hklm}` -/

/-- **The inhomogeneous source term `Θ₄^{hklm}(t)` of the Jet₄ fourth-variation ODE.**  The
    fourteen-term fourth-variation inhomogeneity (one pure `D⁴F` contraction of four first variations
    `Φ(ι·)`, six `D³F` terms pairing a second variation `Q^{··}` with two first variations, three
    `D²F` cross-terms pairing two second variations, and four `D²F` cross-terms pairing a first
    variation with a third variation `Q^{···}`), the one-order-higher analog of `expJet3Rhs`.

    `D⁴F x : E →L E →L E →L E →L E` applied to four vectors, `D³F x : E →L E →L E →L E` applied to
    three vectors, and `D²F x : E →L E →L E` applied to two vectors all land in
    `E = Point n × Point n`. -/
noncomputable def expJet4Rhs (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (h k l m : Point n) (t : ℝ) :
    Point n × Point n :=
  -- (1+1+1+1) — the pure `D⁴F` contraction of the four first variations.
  (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m))
  -- (2+1+1) — six `D³F` terms: one second variation, two first variations.
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhk t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhl t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qkl t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlm t)
  -- (2+2) — three `D²F` terms: two second variations.
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhk t) (Qlm t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhl t) (Qkm t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhm t) (Qkl t)
  -- (3+1) — four `D²F` terms: one first variation, one third variation.
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qklm t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qhlm t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Qhkm t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Φ t (expJetIota m)) (Qhkl t)

@[simp] theorem expJet4Rhs_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (h k l m : Point n) (t : ℝ) :
    expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m))
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhk t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhl t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qkl t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlm t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhk t) (Qlm t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhl t) (Qkm t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhm t) (Qkl t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Qklm t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Qhlm t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota l)) (Qhkm t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota m)) (Qhkl t) := rfl

/-- **`Θ₄^{hklm}` is continuous on `[0,1]`.**  For `‖v‖ ≤ expRho`, `Φ` and the ten second/third
    variations all continuous on `[0,1]`: `D⁴F`/`D³F`/`D²F` are continuous
    (`contDiff_fderiv4/3/2_geodesicField`), `t ↦ Y_v t` is continuous on `[0,1]`
    (`expTube_continuousOn`), so `t ↦ D⁴F/D³F/D²F(Y_v t)` are continuous there; each first variation
    `t ↦ Φ t (ι·)` is continuous (`ContinuousOn.clm_apply` against a fixed vector); the multi-CLM
    applications assemble via `ContinuousOn.clm_apply` (four/three/two-fold), and `ContinuousOn.add`
    combines the fourteen terms. -/
theorem expJet4Rhs_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hΦ : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (h k l m : Point n) :
    ContinuousOn
      (fun t => expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
      (Set.Icc (0 : ℝ) 1) := by
  -- `t ↦ D⁴F/D³F/D²F(Y_v t)` continuous on `[0,1]`.
  have hD4cont : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) :=
    (contDiff_fderiv4_geodesicField g gi hC).continuous
  have hD3cont : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) :=
    (contDiff_fderiv3_geodesicField g gi hC).continuous
  have hD2cont : Continuous (fderiv ℝ (fderiv ℝ (geodesicField g gi))) :=
    (contDiff_fderiv2_geodesicField g gi hC).continuous
  have hYcont := expTube_continuousOn g gi hC p v hv
  have hA4 : ContinuousOn
      (fun t => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
        (expTube g gi hC p v t)) (Set.Icc (0 : ℝ) 1) := hD4cont.comp_continuousOn hYcont
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
  have hPm : ContinuousOn (fun t => Φ t (expJetIota m)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  -- assemble the fourteen terms.
  have ht1 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
        (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)))
      (Set.Icc (0 : ℝ) 1) :=
    (((hA4.clm_apply hPh).clm_apply hPk).clm_apply hPl).clm_apply hPm
  have ht2 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhk t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA3.clm_apply hPl).clm_apply hPm).clm_apply hQhk
  have ht3 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhl t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA3.clm_apply hPk).clm_apply hPm).clm_apply hQhl
  have ht4 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhm t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA3.clm_apply hPk).clm_apply hPl).clm_apply hQhm
  have ht5 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qkl t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA3.clm_apply hPh).clm_apply hPm).clm_apply hQkl
  have ht6 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkm t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA3.clm_apply hPh).clm_apply hPl).clm_apply hQkm
  have ht7 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlm t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA3.clm_apply hPh).clm_apply hPk).clm_apply hQlm
  have ht8 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhk t) (Qlm t))
      (Set.Icc (0 : ℝ) 1) := (hA2.clm_apply hQhk).clm_apply hQlm
  have ht9 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhl t) (Qkm t))
      (Set.Icc (0 : ℝ) 1) := (hA2.clm_apply hQhl).clm_apply hQkm
  have ht10 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhm t) (Qkl t))
      (Set.Icc (0 : ℝ) 1) := (hA2.clm_apply hQhm).clm_apply hQkl
  have ht11 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Qklm t)) (Set.Icc (0 : ℝ) 1) :=
    (hA2.clm_apply hPh).clm_apply hQklm
  have ht12 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Qhlm t)) (Set.Icc (0 : ℝ) 1) :=
    (hA2.clm_apply hPk).clm_apply hQhlm
  have ht13 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota l)) (Qhkm t)) (Set.Icc (0 : ℝ) 1) :=
    (hA2.clm_apply hPl).clm_apply hQhkm
  have ht14 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota m)) (Qhkl t)) (Set.Icc (0 : ℝ) 1) :=
    (hA2.clm_apply hPm).clm_apply hQhkl
  simpa only [expJet4Rhs_apply] using
    (((((((((((((ht1.add ht2).add ht3).add ht4).add ht5).add ht6).add ht7).add ht8).add
      ht9).add ht10).add ht11).add ht12).add ht13).add ht14)

/-- **Uniform `[0,1]` norm bound of `Θ₄^{hklm}`.**  For `‖v‖ ≤ expRho`, `t ∈ [0,1]`, given the `D⁴F`
    tube bound `Kstar4`, the `D³F` tube bound `Kstar3`, the `D²F` tube bound `Kstar2`, a `[0,1]`-bound
    `Cphi` on `‖Φ t‖`, and `[0,1]`-bounds on the ten second/third variations:
    the fourteen-term Faà-di-Bruno bound.  Quadruple `le_opNorm` via `clmApply4_norm_le` for the
    `D⁴F` term, triple via `clmApply3_norm_le` for each of the six `D³F` terms, double via
    `clmApply2_norm_le` for the three `D²F` `2+2` terms and the four `D²F` `3+1` terms, and
    `‖ι m‖ ≤ ‖m‖` (`expJetIota` norm-`≤ 1`).  The nonnegativity of the pair-`Q` bounds appearing in
    an outer slot is derived from the bound hypotheses at the given `t` (norm-nonneg + the bound), so
    no extra nonneg hypotheses are needed beyond `Kstar4/Kstar3/Kstar2/Cphi`.  The ODE well-posedness
    bound the (next) `R^{hklm}` construction consumes. -/
theorem expJet4Rhs_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (h k l m : Point n)
    (Kstar4 Kstar3 Kstar2 Cphi : ℝ)
    (Cq_hk Cq_hl Cq_hm Cq_kl Cq_km Cq_lm : ℝ)
    (Cq_hkl Cq_hkm Cq_hlm Cq_klm : ℝ)
    (hKstar40 : 0 ≤ Kstar4) (hKstar30 : 0 ≤ Kstar3) (hKstar20 : 0 ≤ Kstar2) (hCphi0 : 0 ≤ Cphi)
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
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
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
        + Kstar2 * (Cphi * ‖m‖) * Cq_hkl := by
  set D4 := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)
    with hD4
  set D3 := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t) with hD3
  set D2 := fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t) with hD2
  -- first-variation vector bounds `‖Φ t (ι x)‖ ≤ Cphi·‖x‖`.
  have hP : ∀ x : Point n, ‖Φ t (expJetIota x)‖ ≤ Cphi * ‖x‖ := by
    intro x
    have hιx : ‖expJetIota (n := n) x‖ ≤ ‖x‖ := by
      refine ((expJetIota (n := n)).le_opNorm x).trans ?_
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg x)
    calc ‖Φ t (expJetIota x)‖ ≤ ‖Φ t‖ * ‖expJetIota (n := n) x‖ := (Φ t).le_opNorm _
      _ ≤ Cphi * ‖x‖ := mul_le_mul (hCphi t ht) hιx (norm_nonneg _) hCphi0
  have hnn : ∀ x : Point n, 0 ≤ Cphi * ‖x‖ := fun x => mul_nonneg hCphi0 (norm_nonneg _)
  -- nonnegativity of the pair-`Q` bounds appearing in an outer slot (2+2 terms).
  have hCqhk0 : 0 ≤ Cq_hk := (norm_nonneg _).trans (hCqhk t ht)
  have hCqhl0 : 0 ≤ Cq_hl := (norm_nonneg _).trans (hCqhl t ht)
  have hCqhm0 : 0 ≤ Cq_hm := (norm_nonneg _).trans (hCqhm t ht)
  -- the fourteen term-wise bounds.
  have hb1 : ‖D4 (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l))
      (Φ t (expJetIota m))‖
      ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn h) (hnn k) (hnn l)
      (hKstar4 t ht) (hP h) (hP k) (hP l) (hP m)
  have hb2 : ‖D3 (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhk t)‖
      ≤ Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hk :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn l) (hnn m) (hKstar3 t ht) (hP l) (hP m) (hCqhk t ht)
  have hb3 : ‖D3 (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhl t)‖
      ≤ Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hl :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn k) (hnn m) (hKstar3 t ht) (hP k) (hP m) (hCqhl t ht)
  have hb4 : ‖D3 (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhm t)‖
      ≤ Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hm :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn k) (hnn l) (hKstar3 t ht) (hP k) (hP l) (hCqhm t ht)
  have hb5 : ‖D3 (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qkl t)‖
      ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_kl :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) (hnn m) (hKstar3 t ht) (hP h) (hP m) (hCqkl t ht)
  have hb6 : ‖D3 (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkm t)‖
      ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_km :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) (hnn l) (hKstar3 t ht) (hP h) (hP l) (hCqkm t ht)
  have hb7 : ‖D3 (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlm t)‖
      ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lm :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) (hnn k) (hKstar3 t ht) (hP h) (hP k) (hCqlm t ht)
  have hb8 : ‖D2 (Qhk t) (Qlm t)‖ ≤ Kstar2 * Cq_hk * Cq_lm :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqhk0 (hKstar2 t ht) (hCqhk t ht) (hCqlm t ht)
  have hb9 : ‖D2 (Qhl t) (Qkm t)‖ ≤ Kstar2 * Cq_hl * Cq_km :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqhl0 (hKstar2 t ht) (hCqhl t ht) (hCqkm t ht)
  have hb10 : ‖D2 (Qhm t) (Qkl t)‖ ≤ Kstar2 * Cq_hm * Cq_kl :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqhm0 (hKstar2 t ht) (hCqhm t ht) (hCqkl t ht)
  have hb11 : ‖D2 (Φ t (expJetIota h)) (Qklm t)‖ ≤ Kstar2 * (Cphi * ‖h‖) * Cq_klm :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn h) (hKstar2 t ht) (hP h) (hCqklm t ht)
  have hb12 : ‖D2 (Φ t (expJetIota k)) (Qhlm t)‖ ≤ Kstar2 * (Cphi * ‖k‖) * Cq_hlm :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn k) (hKstar2 t ht) (hP k) (hCqhlm t ht)
  have hb13 : ‖D2 (Φ t (expJetIota l)) (Qhkm t)‖ ≤ Kstar2 * (Cphi * ‖l‖) * Cq_hkm :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn l) (hKstar2 t ht) (hP l) (hCqhkm t ht)
  have hb14 : ‖D2 (Φ t (expJetIota m)) (Qhkl t)‖ ≤ Kstar2 * (Cphi * ‖m‖) * Cq_hkl :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn m) (hKstar2 t ht) (hP m) (hCqhkl t ht)
  -- combine via triangle inequality (`Θ₄ = t₁ + ⋯ + t₁₄`).
  rw [expJet4Rhs_apply, ← hD4, ← hD3, ← hD2]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add
              ((norm_add_le _ _).trans (add_le_add
                ((norm_add_le _ _).trans (add_le_add
                  ((norm_add_le _ _).trans (add_le_add
                    ((norm_add_le _ _).trans (add_le_add
                      ((norm_add_le _ _).trans (add_le_add
                        ((norm_add_le _ _).trans (add_le_add
                          ((norm_add_le _ _).trans (add_le_add hb1 hb2))
                          hb3))
                        hb4))
                      hb5))
                    hb6))
                  hb7))
                hb8))
              hb9))
            hb10))
          hb11))
        hb12))
      hb13))
    hb14)

end QIQTH.ExpMap
