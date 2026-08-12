/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapContDiffFour
import QIQTH.ExpJet4Rhs
import Mathlib

/-!
# JET-5 TOWER — phase 1 (brick J4-645): the Rung-5 reduction mirror + the D5 statement layer

Toward discharging `hch5` (chart ∈ C⁵, the ONLY remaining K1 regularity input after `WhiteW1`,
consumed there as the labelled antecedent of `white_K1BudgetW_h0h1_of_chartC5`).  This file lands
phase 1 of the Jet-5 campaign, the faithful one-Fréchet-order-up mirror of the Jet-4 tower
(`ExpMapContDiff4` → `ExpJet4Rhs` → `ExpJet4FundGlobal`/`Bounds` → `ExpJet4Val*` → `ExpJet4D*`
→ `ExpMapFDeriv3` → `ExpMapContDiffFour`):

* `contDiff_fderiv5_geodesicField` — the geodesic field's **fifth Fréchet derivative** `D⁵F` is
  `C^∞` (one `.fderiv_right` above Rung 4; the field is `C^∞`).
* ★ `expMap_contDiffOn_five_of_fderiv4_contDiffOn_one` — the **proven Rung-5 reduction**: IF the
  fourth-derivative map `v ↦ fderiv⁴ exp_p v` is `ContDiffOn ℝ 1` on the exp-ball, THEN `exp_p`
  is `ContDiffOn ℝ 5` there.  Mechanical mirror of the Rung-4 reduction
  (`expMap_contDiffOn_four_of_fderiv3_contDiffOn_one`): bootstrap off the UNCONDITIONAL
  `expMap_contDiffOn_four`, then chain `contDiffOn_succ_of_fderivWithin` four times on the open
  ball (`fderivWithin = fderiv` via `fderivWithin_of_isOpen`).
* `expJet5Rhs` — the **fifth-variation ODE inhomogeneity `Θ₅^{hklmr}`**: differentiating the
  Jet₄ source once more (adding the direction `r`), the fifth variation `R^{hklmr}(t)` solves the
  INHOMOGENEOUS linear ODE `R′ = DF(Y_v t)·R + Θ₅^{hklmr}(t)`, `R(0) = 0`, whose source is the
  **51-term** Faà-di-Bruno inhomogeneity — one term per partition of `{h,k,l,m,r}` other than the
  single full block (Bell(5) − 1 = 51): `1+1+1+1+1` (one `D⁵F` term), `2+1+1+1` (ten `D⁴F`),
  `2+2+1` (fifteen `D³F`), `3+1+1` (ten `D³F`), `3+2` (ten `D²F`), `4+1` (five `D²F`), with
  `P^x = Φ(ιx)` the first variations and `Q^{··}`/`Q^{···}`/`Q^{····}` the abstract
  second/third/fourth variations (25 abstract `Q`-inputs), exactly as `expJet4Rhs` keeps its ten.
* `expJet5Rhs_continuousOn` — `[0,1]` continuity of `Θ₅` (the well-posedness datum the phase-2
  `expJet5Fund` glue construction will consume).
* `IsExpJet5FundSol` — the **fundamental-solution SHAPE** of the D5 system (initial condition,
  `[0,1]` continuity, global integral equation, inhomogeneous derivative law), the exact mirror of
  the `expJet4Fund` conclusion.  Inhabitance (existence) is NOT claimed here — it is the phase-2
  glue mirror.
* `expJet5Fund_unique` / `expJet5FundSol_unique` — **uniqueness** of the D5 IVP: the inhomogeneity
  is CONSTANT in `R`, so the difference of two solutions solves the HOMOGENEOUS Jacobi equation and
  the source-independent Grönwall engine (`gronwall_vec_residual_Icc`, residual `0`) kills it.
  The cheap first crux lemma: uniqueness at order 5 is verbatim order-4 — only the source symbol
  changes, because the homogeneous linear part `DF(Y_v t)·R` is IDENTICAL at every jet order.

## The honest scope of the D5 Grönwall crux (binding)

The Jet-4 crux (`expJet4Val_v_two_pt_diff` → `expJetD4_two_pt_diff`) was: the VALUE two-point
Lipschitz estimate `‖R^{hklm}_v(1) − R^{hklm}_w(1)‖ ≤ C·‖v − w‖` carrying the genuine
`hLipD4F`/`Kstar4` tube data, lifted to the operator-norm bound on the packaged quadrilinear CLM.
Its order-5 mirror needs, on top of THIS file: (J5-2) `expJet5Rhs_norm_le` (51-term bound) +
`expJet5Fund` existence (glue mirror of `expJet4Fund_glue`/`expJet4FundGlobal`) + value bounds;
(J5-3) `expJet5Val_v_two_pt_diff` — the two-point Grönwall crux at order 5, carrying `hLipD5F` +
`Kstar5` (one-order-up tube data; SAME architecture, one more curvature-derivative term in the
inhomogeneity difference); (J5-4) the quintilinear CLM packaging `expJetD5` +
`expJetD5_two_pt_diff`; (J5-5) `expMap_fderiv4_hasFDerivAt` + the assembly discharging `hfd4`,
closing `expMap_contDiffOn_five` UNCONDITIONALLY; (J5-6) the chart weld
(`uniformFlowExp_contDiffAt_five`, mirror of `ChartThirdJet.uniformFlowExp_contDiffAt_four`),
which is what `hch5` literally asks for.  ⚠ KEY STRUCTURAL FACT: the whole tower is
METRIC-GENERIC — its ONLY metric input is `hC : ∀ a b c, ContDiff ℝ ⊤ (christoffel ·)`, which
the polynomial witness `curvedRNCMetric κ` supplies for free at EVERY order; the Jet-5 wall is
PURE smooth-dependence-on-IC ODE machinery, with zero metric-regularity residue.

## Honest firewall (binding)

**What is proven here:** the Rung-5 reduction (conditional on `hfd4`, carried as an EXPLICIT
hypothesis and genuinely consumed), the D5 statement layer (source, continuity, solution shape),
and D5 IVP uniqueness.  **What is NOT closed:** `hfd4` is NOT discharged; `expJet5Fund` existence,
the order-5 two-point Grönwall crux, `expJetD5`, `exp_p ∈ C⁵`, and `hch5` are NOT established;
`a₁ = R/6` remains CONDITIONAL (flat tower non-vacuous; curved owes the Jet-5 completion + the
Duhamel carry + fat-K carriers + capstone co-instantiation at the corrected witness + prior
piles).  NOT κ = 1/6, NOT the heat-kernel parametrix, NOT numerical-`G` / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

-- The codomain of `D⁵F` is a QUINTUPLY-nested continuous-linear-map space; raise the
-- pending-instance synthesis depth one level above the Jet-4 files.
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
-- The 51-term source: elaborating the sum tree (and the `rfl`/`simpa` against it) recurses deeper
-- than the default 512.
set_option maxRecDepth 16384

variable {n : ℕ}

/-! ### §1. The geodesic field's fifth Fréchet derivative `D⁵F` is `C^∞` -/

/-- The geodesic field's **fifth Fréchet derivative** `D⁵F = fderiv⁵ F` is `C^∞` (`D⁴F` is `C^∞`
    by `contDiff_fderiv4_geodesicField`; differentiate once more). -/
theorem contDiff_fderiv5_geodesicField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))) :=
  (contDiff_fderiv4_geodesicField g gi hC).fderiv_right le_top

/-! ### §2. The Rung-5 reduction to the crux `ContDiff¹ (fderiv⁴ exp_p)` -/

/-- **★ The Rung-5 reduction (proven).**  If the fourth-derivative map `v ↦ fderiv⁴ exp_p v` is
    `ContDiffOn ℝ 1` on the ball `‖v‖ < expRho`, then `exp_p` is `ContDiffOn ℝ 5` there.  The
    mechanical mirror of `expMap_contDiffOn_four_of_fderiv3_contDiffOn_one`, one Fréchet order
    higher: bootstrap off the UNCONDITIONAL Rung-4 capstone `expMap_contDiffOn_four` (⇒ `F₁ :=
    fderiv exp_p ∈ C³`, `F₂ ∈ C²`, `F₃ ∈ C¹` on the open ball via
    `ContDiffOn.fderiv_of_isOpen`), then chain `contDiffOn_succ_of_fderivWithin` four times
    (`fderivWithin = fderiv` on the open ball).  HONEST: this ISOLATES the remaining Rung-5
    obligation `hfd4` (the Jet₅ fundamental-solution / Grönwall sub-campaign, phases J5-2…J5-5);
    it does NOT discharge it. -/
theorem expMap_contDiffOn_five_of_fderiv4_contDiffOn_one
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hfd4 : ContDiffOn ℝ 1
      (fun v => fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ
        (expMap g gi hC p) w) z) y) v)
      (Metric.ball (0 : Point n) (expRho g gi hC p))) :
    ContDiffOn ℝ 5 (expMap g gi hC p) (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  set s : Set (Point n) := Metric.ball (0 : Point n) (expRho g gi hC p) with hsdef
  -- `F₁ := fderiv exp_p` is `ContDiffOn ℝ 3` on the open ball (Rung 4).
  have hF1cd3 : ContDiffOn ℝ 3 (fun v => fderiv ℝ (expMap g gi hC p) v) s :=
    (expMap_contDiffOn_four g gi hC p).fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  -- `F₂ := fderiv F₁` is `ContDiffOn ℝ 2`; `F₃ := fderiv F₂` is `ContDiffOn ℝ 1`.
  have hF2cd2 : ContDiffOn ℝ 2
      (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) s :=
    hF1cd3.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hF3cd1 : ContDiffOn ℝ 1
      (fun y => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) y) s :=
    hF2cd2.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hF3diff : DifferentiableOn ℝ
      (fun y => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) y) s :=
    hF3cd1.differentiableOn (by norm_num)
  -- Step 1: `ContDiffOn ℝ 2 F₃ s`, using the crux `hfd4`.
  have hfw_F4 : ContDiffOn ℝ 1
      (fun v => fderivWithin ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ
        (expMap g gi hC p) w) z) y) s v) s :=
    hfd4.congr (fun v hv => fderivWithin_of_isOpen Metric.isOpen_ball hv)
  have hF3cd2 : ContDiffOn ℝ (1 + 1)
      (fun y => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) y) s :=
    contDiffOn_succ_of_fderivWithin hF3diff (by simp) hfw_F4
  have e2 : (1 : WithTop ℕ∞) + 1 = 2 := by norm_num
  rw [e2] at hF3cd2
  -- Step 2: `ContDiffOn ℝ 3 F₂ s`.
  have hF2diff : DifferentiableOn ℝ
      (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) s :=
    hF2cd2.differentiableOn (by norm_num)
  have hfw_F3 : ContDiffOn ℝ 2
      (fun v => fderivWithin ℝ
        (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) s v) s :=
    hF3cd2.congr (fun v hv => fderivWithin_of_isOpen Metric.isOpen_ball hv)
  have hF2cd3 : ContDiffOn ℝ (2 + 1)
      (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) s :=
    contDiffOn_succ_of_fderivWithin hF2diff (by simp) hfw_F3
  have e3 : (2 : WithTop ℕ∞) + 1 = 3 := by norm_num
  rw [e3] at hF2cd3
  -- Step 3: `ContDiffOn ℝ 4 F₁ s`.
  have hF1diff : DifferentiableOn ℝ (fun v => fderiv ℝ (expMap g gi hC p) v) s :=
    hF1cd3.differentiableOn (by norm_num)
  have hfw_F2 : ContDiffOn ℝ 3
      (fun v => fderivWithin ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) s v) s :=
    hF2cd3.congr (fun v hv => fderivWithin_of_isOpen Metric.isOpen_ball hv)
  have hF1cd4 : ContDiffOn ℝ (3 + 1) (fun v => fderiv ℝ (expMap g gi hC p) v) s :=
    contDiffOn_succ_of_fderivWithin hF1diff (by simp) hfw_F2
  have e4 : (3 : WithTop ℕ∞) + 1 = 4 := by norm_num
  rw [e4] at hF1cd4
  -- Step 4: `ContDiffOn ℝ 5 exp_p s`.
  have hexpdiff : DifferentiableOn ℝ (expMap g gi hC p) s :=
    (expMap_contDiffOn_one g gi hC p).differentiableOn (by norm_num)
  have hfw_F1 : ContDiffOn ℝ 4 (fun v => fderivWithin ℝ (expMap g gi hC p) s v) s :=
    hF1cd4.congr (fun v hv => fderivWithin_of_isOpen Metric.isOpen_ball hv)
  have hres : ContDiffOn ℝ (4 + 1) (expMap g gi hC p) s :=
    contDiffOn_succ_of_fderivWithin hexpdiff (by simp) hfw_F1
  have e5 : (4 : WithTop ℕ∞) + 1 = 5 := by norm_num
  rwa [e5] at hres

/-! ### §3. The Jet₅ fifth-variation ODE source `Θ₅^{hklmr}` (51 terms) -/

/-- **The inhomogeneous source term `Θ₅^{hklmr}(t)` of the Jet₅ fifth-variation ODE.**  The
    51-term fifth-variation inhomogeneity (one term per partition of `{h,k,l,m,r}` other than the
    full block, which feeds the homogeneous `DF·R` term): one pure `D⁵F` contraction of five first
    variations, ten `D⁴F` terms (pair + three firsts), fifteen `D³F` terms (two pairs + one
    first), ten `D³F` terms (triple + two firsts), ten `D²F` terms (triple + pair), five `D²F`
    terms (quadruple + one first).  One-order-higher analog of `expJet4Rhs` (fourteen terms). -/
noncomputable def expJet5Rhs (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (h k l m r : Point n) (t : ℝ) :
    Point n × Point n :=
  (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r))
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhk t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhl t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qkl t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qkm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qkr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qlm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qlr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qmr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Qkl t) (Qmr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Qkm t) (Qlr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Qkr t) (Qlm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Qhl t) (Qmr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Qhm t) (Qlr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Qhr t) (Qlm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota l)) (Qhk t) (Qmr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota l)) (Qhm t) (Qkr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota l)) (Qhr t) (Qkm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota m)) (Qhk t) (Qlr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota m)) (Qhl t) (Qkr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota m)) (Qhr t) (Qkl t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota r)) (Qhk t) (Qlm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota r)) (Qhl t) (Qkm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota r)) (Qhm t) (Qkl t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhkl t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhkm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhkr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qhlm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhlr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhmr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Qklm t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qklr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkmr t)
  + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlmr t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Qhkl t) (Qmr t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Qhkm t) (Qlr t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Qhkr t) (Qlm t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Qhlm t) (Qkr t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Qhlr t) (Qkm t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Qhmr t) (Qkl t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Qklm t) (Qhr t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Qklr t) (Qhm t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Qkmr t) (Qhl t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Qlmr t) (Qhk t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Φ t (expJetIota h)) (Qklmr t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Φ t (expJetIota k)) (Qhlmr t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Φ t (expJetIota l)) (Qhkmr t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Φ t (expJetIota m)) (Qhklr t)
  + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Φ t (expJetIota r)) (Qhklm t)

@[simp] theorem expJet5Rhs_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (h k l m r : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r))
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhk t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhl t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qkl t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qkm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qkr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qlm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qlr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qmr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Qkl t) (Qmr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Qkm t) (Qlr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Qkr t) (Qlm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Qhl t) (Qmr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Qhm t) (Qlr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Qhr t) (Qlm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota l)) (Qhk t) (Qmr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota l)) (Qhm t) (Qkr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota l)) (Qhr t) (Qkm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota m)) (Qhk t) (Qlr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota m)) (Qhl t) (Qkr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota m)) (Qhr t) (Qkl t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota r)) (Qhk t) (Qlm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota r)) (Qhl t) (Qkm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota r)) (Qhm t) (Qkl t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhkl t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhkm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhkr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qhlm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhlr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhmr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Qklm t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qklr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkmr t)
      + (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlmr t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Qhkl t) (Qmr t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Qhkm t) (Qlr t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Qhkr t) (Qlm t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Qhlm t) (Qkr t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Qhlr t) (Qkm t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Qhmr t) (Qkl t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Qklm t) (Qhr t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Qklr t) (Qhm t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Qkmr t) (Qhl t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Qlmr t) (Qhk t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota h)) (Qklmr t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota k)) (Qhlmr t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota l)) (Qhkmr t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota m)) (Qhklr t)
      + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
          (Φ t (expJetIota r)) (Qhklm t) := rfl

set_option maxHeartbeats 6400000 in
/-- **`Θ₅^{hklmr}` is continuous on `[0,1]`.**  Mirror of `expJet4Rhs_continuousOn` at 51 terms:
    `D⁵F/D⁴F/D³F/D²F` are continuous, the tube is continuous on `[0,1]`, the first variations are
    `ContinuousOn.clm_apply` against fixed vectors, and the multi-CLM applications assemble
    term-by-term.  The well-posedness datum the phase-2 `expJet5Fund` glue consumes. -/
theorem expJet5Rhs_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hΦ : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1))
    (h k l m r : Point n) :
    ContinuousOn
      (fun t => expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
      (Set.Icc (0 : ℝ) 1) := by
  have hD5cont : Continuous
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))) :=
    (contDiff_fderiv5_geodesicField g gi hC).continuous
  have hD4cont : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) :=
    (contDiff_fderiv4_geodesicField g gi hC).continuous
  have hD3cont : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) :=
    (contDiff_fderiv3_geodesicField g gi hC).continuous
  have hD2cont : Continuous (fderiv ℝ (fderiv ℝ (geodesicField g gi))) :=
    (contDiff_fderiv2_geodesicField g gi hC).continuous
  have hYcont := expTube_continuousOn g gi hC p v hv
  have hA5 : ContinuousOn
      (fun t => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
        (expTube g gi hC p v t)) (Set.Icc (0 : ℝ) 1) := hD5cont.comp_continuousOn hYcont
  have hA4 : ContinuousOn
      (fun t => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
        (expTube g gi hC p v t)) (Set.Icc (0 : ℝ) 1) := hD4cont.comp_continuousOn hYcont
  have hA3 : ContinuousOn
      (fun t => fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
      (Set.Icc (0 : ℝ) 1) := hD3cont.comp_continuousOn hYcont
  have hA2 : ContinuousOn
      (fun t => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
      (Set.Icc (0 : ℝ) 1) := hD2cont.comp_continuousOn hYcont
  have hPh : ContinuousOn (fun t => Φ t (expJetIota h)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  have hPk : ContinuousOn (fun t => Φ t (expJetIota k)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  have hPl : ContinuousOn (fun t => Φ t (expJetIota l)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  have hPm : ContinuousOn (fun t => Φ t (expJetIota m)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  have hPr : ContinuousOn (fun t => Φ t (expJetIota r)) (Set.Icc (0 : ℝ) 1) :=
    hΦ.clm_apply continuousOn_const
  have ht1 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r))) (Set.Icc (0 : ℝ) 1) :=
    (((((hA5.clm_apply hPh).clm_apply hPk).clm_apply hPl).clm_apply hPm).clm_apply hPr)
  have ht2 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
        (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhk t)) (Set.Icc (0 : ℝ) 1) :=
    ((((hA4.clm_apply hPl).clm_apply hPm).clm_apply hPr).clm_apply hQhk)
  have ht3 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhl t)) (Set.Icc (0 : ℝ) 1) :=
    ((((hA4.clm_apply hPk).clm_apply hPm).clm_apply hPr).clm_apply hQhl)
  have ht4 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhm t)) (Set.Icc (0 : ℝ) 1) :=
    ((((hA4.clm_apply hPk).clm_apply hPl).clm_apply hPr).clm_apply hQhm)
  have ht5 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhr t)) (Set.Icc (0 : ℝ) 1) :=
    ((((hA4.clm_apply hPk).clm_apply hPl).clm_apply hPm).clm_apply hQhr)
  have ht6 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qkl t)) (Set.Icc (0 : ℝ) 1) :=
    ((((hA4.clm_apply hPh).clm_apply hPm).clm_apply hPr).clm_apply hQkl)
  have ht7 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qkm t)) (Set.Icc (0 : ℝ) 1) :=
    ((((hA4.clm_apply hPh).clm_apply hPl).clm_apply hPr).clm_apply hQkm)
  have ht8 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qkr t)) (Set.Icc (0 : ℝ) 1) :=
    ((((hA4.clm_apply hPh).clm_apply hPl).clm_apply hPm).clm_apply hQkr)
  have ht9 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qlm t)) (Set.Icc (0 : ℝ) 1) :=
    ((((hA4.clm_apply hPh).clm_apply hPk).clm_apply hPr).clm_apply hQlm)
  have ht10 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qlr t)) (Set.Icc (0 : ℝ) 1) :=
    ((((hA4.clm_apply hPh).clm_apply hPk).clm_apply hPm).clm_apply hQlr)
  have ht11 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qmr t)) (Set.Icc (0 : ℝ) 1) :=
    ((((hA4.clm_apply hPh).clm_apply hPk).clm_apply hPl).clm_apply hQmr)
  have ht12 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Qkl t) (Qmr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPh).clm_apply hQkl).clm_apply hQmr)
  have ht13 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Qkm t) (Qlr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPh).clm_apply hQkm).clm_apply hQlr)
  have ht14 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Qkr t) (Qlm t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPh).clm_apply hQkr).clm_apply hQlm)
  have ht15 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Qhl t) (Qmr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPk).clm_apply hQhl).clm_apply hQmr)
  have ht16 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Qhm t) (Qlr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPk).clm_apply hQhm).clm_apply hQlr)
  have ht17 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Qhr t) (Qlm t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPk).clm_apply hQhr).clm_apply hQlm)
  have ht18 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota l)) (Qhk t) (Qmr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPl).clm_apply hQhk).clm_apply hQmr)
  have ht19 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota l)) (Qhm t) (Qkr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPl).clm_apply hQhm).clm_apply hQkr)
  have ht20 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota l)) (Qhr t) (Qkm t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPl).clm_apply hQhr).clm_apply hQkm)
  have ht21 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota m)) (Qhk t) (Qlr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPm).clm_apply hQhk).clm_apply hQlr)
  have ht22 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota m)) (Qhl t) (Qkr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPm).clm_apply hQhl).clm_apply hQkr)
  have ht23 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota m)) (Qhr t) (Qkl t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPm).clm_apply hQhr).clm_apply hQkl)
  have ht24 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota r)) (Qhk t) (Qlm t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPr).clm_apply hQhk).clm_apply hQlm)
  have ht25 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota r)) (Qhl t) (Qkm t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPr).clm_apply hQhl).clm_apply hQkm)
  have ht26 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota r)) (Qhm t) (Qkl t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPr).clm_apply hQhm).clm_apply hQkl)
  have ht27 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhkl t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPm).clm_apply hPr).clm_apply hQhkl)
  have ht28 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhkm t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPl).clm_apply hPr).clm_apply hQhkm)
  have ht29 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhkr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPl).clm_apply hPm).clm_apply hQhkr)
  have ht30 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qhlm t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPk).clm_apply hPr).clm_apply hQhlm)
  have ht31 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhlr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPk).clm_apply hPm).clm_apply hQhlr)
  have ht32 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhmr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPk).clm_apply hPl).clm_apply hQhmr)
  have ht33 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Qklm t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPh).clm_apply hPr).clm_apply hQklm)
  have ht34 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qklr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPh).clm_apply hPm).clm_apply hQklr)
  have ht35 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkmr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPh).clm_apply hPl).clm_apply hQkmr)
  have ht36 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlmr t)) (Set.Icc (0 : ℝ) 1) :=
    (((hA3.clm_apply hPh).clm_apply hPk).clm_apply hQlmr)
  have ht37 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Qhkl t) (Qmr t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hQhkl).clm_apply hQmr)
  have ht38 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Qhkm t) (Qlr t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hQhkm).clm_apply hQlr)
  have ht39 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Qhkr t) (Qlm t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hQhkr).clm_apply hQlm)
  have ht40 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Qhlm t) (Qkr t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hQhlm).clm_apply hQkr)
  have ht41 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Qhlr t) (Qkm t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hQhlr).clm_apply hQkm)
  have ht42 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Qhmr t) (Qkl t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hQhmr).clm_apply hQkl)
  have ht43 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Qklm t) (Qhr t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hQklm).clm_apply hQhr)
  have ht44 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Qklr t) (Qhm t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hQklr).clm_apply hQhm)
  have ht45 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Qkmr t) (Qhl t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hQkmr).clm_apply hQhl)
  have ht46 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Qlmr t) (Qhk t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hQlmr).clm_apply hQhk)
  have ht47 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota h)) (Qklmr t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hPh).clm_apply hQklmr)
  have ht48 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota k)) (Qhlmr t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hPk).clm_apply hQhlmr)
  have ht49 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota l)) (Qhkmr t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hPl).clm_apply hQhkmr)
  have ht50 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota m)) (Qhklr t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hPm).clm_apply hQhklr)
  have ht51 : ContinuousOn
      (fun t => (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
        (Φ t (expJetIota r)) (Qhklm t)) (Set.Icc (0 : ℝ) 1) :=
    ((hA2.clm_apply hPr).clm_apply hQhklm)
  simpa only [expJet5Rhs_apply] using
    ((((((((((((((((((((((((((((((((((((((((((((((((((ht1.add ht2).add ht3).add ht4).add ht5).add ht6).add ht7).add ht8).add ht9).add ht10).add ht11).add ht12).add ht13).add ht14).add ht15).add ht16).add ht17).add ht18).add ht19).add ht20).add ht21).add ht22).add ht23).add ht24).add ht25).add ht26).add ht27).add ht28).add ht29).add ht30).add ht31).add ht32).add ht33).add ht34).add ht35).add ht36).add ht37).add ht38).add ht39).add ht40).add ht41).add ht42).add ht43).add ht44).add ht45).add ht46).add ht47).add ht48).add ht49).add ht50).add ht51)

/-! ### §4. The D5 fundamental-solution SHAPE and its uniqueness -/

/-- **The fundamental-solution shape of the D5 system** (mirror of the `expJet4Fund` conclusion):
    `R 0 = 0`, `[0,1]` continuity, the GLOBAL integral equation, and the inhomogeneous Jet₅
    derivative law.  ⚠ Inhabitance (existence, via the glue mirror of `expJet4Fund_glue`) is the
    phase-2 obligation and is NOT claimed in this file. -/
def IsExpJet5FundSol (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (h k l m r : Point n) (R : ℝ → (Point n × Point n)) : Prop :=
  R 0 = 0 ∧
  ContinuousOn R (Set.Icc (0 : ℝ) 1) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1,
    R t = (0 : Point n × Point n) + ∫ s in (0 : ℝ)..t,
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt R
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
      (Set.Icc (0 : ℝ) 1) t)

set_option maxHeartbeats 2000000 in
/-- **Uniqueness of the Jet₅ fifth-variation IVP on `[0,1]`.**  Mirror of `expJet4Fund_unique`:
    the inhomogeneous source `Θ₅^{hklmr}` is CONSTANT in `R`, so two solutions with the same IC
    agree — the difference solves the HOMOGENEOUS Jacobi equation (the 51-term sources cancel)
    with `S 0 = 0`, and `gronwall_vec_residual_Icc` with residual `ρ = 0` forces `‖S t‖ ≤ 0`.
    The Grönwall uniqueness engine is SOURCE-INDEPENDENT: verbatim order-4, only the source symbol
    changes. -/
theorem expJet5Fund_unique (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (h k l m r : Point n)
    (R₁ R₂ : ℝ → (Point n × Point n)) (hR₁0 : R₁ 0 = 0) (hR₂0 : R₂ 0 = 0)
    (hderiv₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R₁
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₁ t)
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
        (Set.Icc (0 : ℝ) 1) t)
    (hderiv₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R₂
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₂ t)
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
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
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
            - ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₂ t)
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R₁ t - R₂ t) + 0 := by
        rw [map_sub, add_zero]; abel
      rwa [hval] at hd)
    (fun t ht => hKstar t ht)
    (fun _ _ => by simp)
  intro t ht
  have h0 : ‖R₁ t - R₂ t‖ ≤ 0 := by simpa using hgron t ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

/-- **Uniqueness for shape solutions**: any two `IsExpJet5FundSol` witnesses agree on `[0,1]`. -/
theorem expJet5FundSol_unique (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (h k l m r : Point n)
    (R₁ R₂ : ℝ → (Point n × Point n))
    (h1 : IsExpJet5FundSol g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r R₁)
    (h2 : IsExpJet5FundSol g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r R₂) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, R₁ t = R₂ t :=
  expJet5Fund_unique g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv h k l m r R₁ R₂
    h1.1 h2.1 h1.2.2.2 h2.2.2.2

end QIQTH.ExpMap
