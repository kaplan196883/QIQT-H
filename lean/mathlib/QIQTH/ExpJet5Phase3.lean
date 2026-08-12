/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5Phase2
import QIQTH.ExpJet4DFull
import Mathlib

/-!
# JET-5 TOWER — phase 3 (brick J4-647): the value-bounds bridge

Toward discharging `hch5` (chart ∈ C⁵, the sole remaining K1 regularity input): this file lands
the **value-bounds bridge** between the banked D5 well-posedness layer (`ExpJet5Phase1/2`) and the
D5 two-point Grönwall crux (J5-3) — the faithful one-Fréchet-order-up mirror of the Jet-4 value
layer (`ExpJet4FundBounds` + `ExpJet4D.expJet4Val` + `ExpJet4DFull.expJet3CurveG/expJet4ValG`):

* ★ `expJet5Fund_value_bound` / `expJet5Fund_value_bound_Icc` — the Grönwall **a-priori value
  bounds** for the `[0,1]` fifth-variation fundamental solution: the 51-term source bound
  (`expJet5Rhs_norm_le`) is fed as the residual ρ₅ into `gronwall_vec_residual(_Icc)` ⟹
  `‖R(t)‖ ≤ ρ₅·e^{Kstar}` (mirror of `expJet4Fund_value_bound(_Icc)`, fourteen → fifty-one
  terms; the polynomial is SCRIPT-GENERATED in exactly the `expJet5Rhs_norm_le` term order —
  no-false-bound discipline).
* `expJet4Curve` / `expJet4Curve_one` / `expJet4Curve_continuousOn` — the **order-4 curve
  mirror**: the `expJet4Fund` witness kept as a WHOLE curve `t ↦ R^{hklm}_v(t)` (mirror of
  `expJet3Curve` one order up); its `t = 1` value is `expJet4Val`.
* `expJet4CurveG` / `expJet4CurveG_one` / `expJet4CurveG_continuousOn` — the **genuine**
  order-4 curve: `expJet4Curve` with the six pair-`Q··` slots instantiated by `expJet2Curve` and
  the four triple-`Q···` slots by `expJet3CurveG` (mirror of `expJet3CurveG` one order up); its
  `t = 1` value is `expJet4ValG`.  This is the QUADRUPLE-slot feeder of `expJet5ValG`.
* ★ `expJet5Val` — the fifth-variation VALUE `R^{hklmr}_v(1)` (the `expJet5Fund` witness at
  `t = 1`, 25 abstract `Q`-slots; mirror of `expJet4Val`).
* ★ `expJet5ValG` — the **genuine** fifth-variation value: the 25 `Q`-slots instantiated by the
  ACTUAL lower-jet curves — ten pair slots := `expJet2Curve`, ten triple slots := `expJet3CurveG`,
  five quadruple slots := `expJet4CurveG` (mirror of `expJet4ValG` one order up).
* `expJet5ValG_norm_le` — the uniform 5-linear value bound
  `‖expJet5ValG h k l m r‖ ≤ M·‖h‖·‖k‖·‖l‖·‖m‖·‖r‖` (pair/triple/quadruple curve bounds from
  `expJet2Fund_value_bound_Icc` / `expJet3Fund_value_bound_Icc` / `expJet4Fund_value_bound_Icc`
  fed into the 51-term `expJet5Fund_value_bound`; mirror of `expJet4ValG_norm_le`).
* Non-vacuity gates (cp466 discipline — antecedent inhabitance at the GENUINELY CURVED witness
  `g^κ = curvedRNCMetric (−1)`): `expJet5Fund_value_bound_gate` (the value bound runs end-to-end
  on the actual curved D5 fundamental solution) and `expJet5ValG_norm_le_gate` (the genuine value
  layer fires at curved data).

## Honest firewall (binding)

**What is proven here:** the D5 a-priori value bounds, the order-4 curve mirrors, the order-5
value definitions with the 25 slots instantiated by the genuine lower-jet curves, and the uniform
5-linear value bound — the direct prerequisites of the D5 two-point Grönwall crux (J5-3).
**What is NOT closed:** (J5-3) `expJet5Val_v_two_pt_diff` (the two-point Grönwall crux carrying
`hLipD5F`/`Kstar5`), (J5-4) the quintilinear CLM packaging `expJetD5`(+`_two_pt_diff`) and the
matched-`Q` multilinearity layer, (J5-5) `expMap_fderiv4_hasFDerivAt` + assembly discharging
`hfd4` (⟹ `expMap_contDiffOn_five` UNCONDITIONAL), (J5-6) the chart weld = `hch5`.
`exp_p ∈ C⁵` is NOT established.  `a₁ = R/6` remains CONDITIONAL (flat tower non-vacuous;
curved owes the Jet-5 completion + the Duhamel carry + fat-K carriers + capstone co-instantiation
at the corrected witness + prior piles).  NOT κ = 1/6, NOT the heat-kernel parametrix, NOT
numerical-`G` / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

-- The codomain of `D⁵F` is a QUINTUPLY-nested continuous-linear-map space; raise the
-- pending-instance synthesis depth one level above the Jet-4 files (as in `ExpJet5Phase1/2`).
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
-- The 51-term residual polynomial: elaborating the sum tree recurses deeper than the default 512.
set_option maxRecDepth 16384

variable {n : ℕ}

/-! ### §1. The D5 Grönwall a-priori value bounds (mirror of `ExpJet4FundBounds`) -/

set_option maxHeartbeats 12800000 in
/-- **★ `R^{hklmr}(1)` value bound.**  For the inhomogeneous Jet₅ solution `R` (`R 0 = 0`,
    `R' = DF(Y_v)(R) + Θ₅^{hklmr}`), with a `[0,1]` Jacobi bound `Kstar` on `‖DF(Y_v t)‖`, the
    `D⁵F/D⁴F/D³F/D²F` tube bounds `Kstar5/4/3/2`, a `[0,1]`-bound `Cphi` on `‖Φ t‖`, and
    `[0,1]`-bounds on the 25 abstract `Q`-variations, the 51-term source bound
    (`expJet5Rhs_norm_le`) is fed as the residual ρ₅ into `gronwall_vec_residual` ⟹
    `‖R 1‖ ≤ ρ₅·e^{Kstar}`.  Mirror of `expJet4Fund_value_bound` one order up. -/
theorem expJet5Fund_value_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (h k l m r : Point n)
    (Kstar Kstar5 Kstar4 Kstar3 Kstar2 Cphi : ℝ)
    (Cq_hk Cq_hl Cq_hm Cq_hr Cq_kl Cq_km Cq_kr Cq_lm Cq_lr Cq_mr : ℝ)
    (Cq_hkl Cq_hkm Cq_hkr Cq_hlm Cq_hlr Cq_hmr Cq_klm Cq_klr Cq_kmr Cq_lmr : ℝ)
    (Cq_hklm Cq_hklr Cq_hkmr Cq_hlmr Cq_klmr : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar50 : 0 ≤ Kstar5) (hKstar40 : 0 ≤ Kstar4)
    (hKstar30 : 0 ≤ Kstar3) (hKstar20 : 0 ≤ Kstar2) (hCphi0 : 0 ≤ Cphi)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hKstar5 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
        (expTube g gi hC p v t)‖ ≤ Kstar5)
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
    (hCqhr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhr t‖ ≤ Cq_hr)
    (hCqkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq_kl)
    (hCqkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkm t‖ ≤ Cq_km)
    (hCqkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkr t‖ ≤ Cq_kr)
    (hCqlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlm t‖ ≤ Cq_lm)
    (hCqlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlr t‖ ≤ Cq_lr)
    (hCqmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qmr t‖ ≤ Cq_mr)
    (hCqhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkl t‖ ≤ Cq_hkl)
    (hCqhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkm t‖ ≤ Cq_hkm)
    (hCqhkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkr t‖ ≤ Cq_hkr)
    (hCqhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlm t‖ ≤ Cq_hlm)
    (hCqhlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlr t‖ ≤ Cq_hlr)
    (hCqhmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmr t‖ ≤ Cq_hmr)
    (hCqklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklm t‖ ≤ Cq_klm)
    (hCqklr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklr t‖ ≤ Cq_klr)
    (hCqkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmr t‖ ≤ Cq_kmr)
    (hCqlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmr t‖ ≤ Cq_lmr)
    (hCqhklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklm t‖ ≤ Cq_hklm)
    (hCqhklr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklr t‖ ≤ Cq_hklr)
    (hCqhkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkmr t‖ ≤ Cq_hkmr)
    (hCqhlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlmr t‖ ≤ Cq_hlmr)
    (hCqklmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklmr t‖ ≤ Cq_klmr)
    (R : ℝ → (Point n × Point n)) (hR0 : R 0 = 0)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
        (Set.Icc (0 : ℝ) 1) t) :
    ‖R 1‖ ≤ (Kstar5 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖)
          + Kstar4 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hk
          + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hl
          + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hm
          + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hr
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_kl
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_km
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_kr
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_lm
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_lr
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_mr
          + Kstar3 * (Cphi * ‖h‖) * Cq_kl * Cq_mr
          + Kstar3 * (Cphi * ‖h‖) * Cq_km * Cq_lr
          + Kstar3 * (Cphi * ‖h‖) * Cq_kr * Cq_lm
          + Kstar3 * (Cphi * ‖k‖) * Cq_hl * Cq_mr
          + Kstar3 * (Cphi * ‖k‖) * Cq_hm * Cq_lr
          + Kstar3 * (Cphi * ‖k‖) * Cq_hr * Cq_lm
          + Kstar3 * (Cphi * ‖l‖) * Cq_hk * Cq_mr
          + Kstar3 * (Cphi * ‖l‖) * Cq_hm * Cq_kr
          + Kstar3 * (Cphi * ‖l‖) * Cq_hr * Cq_km
          + Kstar3 * (Cphi * ‖m‖) * Cq_hk * Cq_lr
          + Kstar3 * (Cphi * ‖m‖) * Cq_hl * Cq_kr
          + Kstar3 * (Cphi * ‖m‖) * Cq_hr * Cq_kl
          + Kstar3 * (Cphi * ‖r‖) * Cq_hk * Cq_lm
          + Kstar3 * (Cphi * ‖r‖) * Cq_hl * Cq_km
          + Kstar3 * (Cphi * ‖r‖) * Cq_hm * Cq_kl
          + Kstar3 * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hkl
          + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hkm
          + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hkr
          + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_hlm
          + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hlr
          + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hmr
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖r‖) * Cq_klm
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_klr
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_kmr
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lmr
          + Kstar2 * Cq_hkl * Cq_mr
          + Kstar2 * Cq_hkm * Cq_lr
          + Kstar2 * Cq_hkr * Cq_lm
          + Kstar2 * Cq_hlm * Cq_kr
          + Kstar2 * Cq_hlr * Cq_km
          + Kstar2 * Cq_hmr * Cq_kl
          + Kstar2 * Cq_klm * Cq_hr
          + Kstar2 * Cq_klr * Cq_hm
          + Kstar2 * Cq_kmr * Cq_hl
          + Kstar2 * Cq_lmr * Cq_hk
          + Kstar2 * (Cphi * ‖h‖) * Cq_klmr
          + Kstar2 * (Cphi * ‖k‖) * Cq_hlmr
          + Kstar2 * (Cphi * ‖l‖) * Cq_hkmr
          + Kstar2 * (Cphi * ‖m‖) * Cq_hklr
          + Kstar2 * (Cphi * ‖r‖) * Cq_hklm) * Real.exp Kstar := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num [Set.mem_Icc]
  have hCqhk0 : 0 ≤ Cq_hk := (norm_nonneg _).trans (hCqhk 0 hmem0)
  have hCqhl0 : 0 ≤ Cq_hl := (norm_nonneg _).trans (hCqhl 0 hmem0)
  have hCqhm0 : 0 ≤ Cq_hm := (norm_nonneg _).trans (hCqhm 0 hmem0)
  have hCqhr0 : 0 ≤ Cq_hr := (norm_nonneg _).trans (hCqhr 0 hmem0)
  have hCqkl0 : 0 ≤ Cq_kl := (norm_nonneg _).trans (hCqkl 0 hmem0)
  have hCqkm0 : 0 ≤ Cq_km := (norm_nonneg _).trans (hCqkm 0 hmem0)
  have hCqkr0 : 0 ≤ Cq_kr := (norm_nonneg _).trans (hCqkr 0 hmem0)
  have hCqlm0 : 0 ≤ Cq_lm := (norm_nonneg _).trans (hCqlm 0 hmem0)
  have hCqlr0 : 0 ≤ Cq_lr := (norm_nonneg _).trans (hCqlr 0 hmem0)
  have hCqmr0 : 0 ≤ Cq_mr := (norm_nonneg _).trans (hCqmr 0 hmem0)
  have hCqhkl0 : 0 ≤ Cq_hkl := (norm_nonneg _).trans (hCqhkl 0 hmem0)
  have hCqhkm0 : 0 ≤ Cq_hkm := (norm_nonneg _).trans (hCqhkm 0 hmem0)
  have hCqhkr0 : 0 ≤ Cq_hkr := (norm_nonneg _).trans (hCqhkr 0 hmem0)
  have hCqhlm0 : 0 ≤ Cq_hlm := (norm_nonneg _).trans (hCqhlm 0 hmem0)
  have hCqhlr0 : 0 ≤ Cq_hlr := (norm_nonneg _).trans (hCqhlr 0 hmem0)
  have hCqhmr0 : 0 ≤ Cq_hmr := (norm_nonneg _).trans (hCqhmr 0 hmem0)
  have hCqklm0 : 0 ≤ Cq_klm := (norm_nonneg _).trans (hCqklm 0 hmem0)
  have hCqklr0 : 0 ≤ Cq_klr := (norm_nonneg _).trans (hCqklr 0 hmem0)
  have hCqkmr0 : 0 ≤ Cq_kmr := (norm_nonneg _).trans (hCqkmr 0 hmem0)
  have hCqlmr0 : 0 ≤ Cq_lmr := (norm_nonneg _).trans (hCqlmr 0 hmem0)
  have hCqhklm0 : 0 ≤ Cq_hklm := (norm_nonneg _).trans (hCqhklm 0 hmem0)
  have hCqhklr0 : 0 ≤ Cq_hklr := (norm_nonneg _).trans (hCqhklr 0 hmem0)
  have hCqhkmr0 : 0 ≤ Cq_hkmr := (norm_nonneg _).trans (hCqhkmr 0 hmem0)
  have hCqhlmr0 : 0 ≤ Cq_hlmr := (norm_nonneg _).trans (hCqhlmr 0 hmem0)
  have hCqklmr0 : 0 ≤ Cq_klmr := (norm_nonneg _).trans (hCqklmr 0 hmem0)
  have hρ0 : (0 : ℝ) ≤ Kstar5 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖)
        + Kstar4 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hk
        + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hl
        + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hm
        + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hr
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_kl
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_km
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_kr
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_lm
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_lr
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_mr
        + Kstar3 * (Cphi * ‖h‖) * Cq_kl * Cq_mr
        + Kstar3 * (Cphi * ‖h‖) * Cq_km * Cq_lr
        + Kstar3 * (Cphi * ‖h‖) * Cq_kr * Cq_lm
        + Kstar3 * (Cphi * ‖k‖) * Cq_hl * Cq_mr
        + Kstar3 * (Cphi * ‖k‖) * Cq_hm * Cq_lr
        + Kstar3 * (Cphi * ‖k‖) * Cq_hr * Cq_lm
        + Kstar3 * (Cphi * ‖l‖) * Cq_hk * Cq_mr
        + Kstar3 * (Cphi * ‖l‖) * Cq_hm * Cq_kr
        + Kstar3 * (Cphi * ‖l‖) * Cq_hr * Cq_km
        + Kstar3 * (Cphi * ‖m‖) * Cq_hk * Cq_lr
        + Kstar3 * (Cphi * ‖m‖) * Cq_hl * Cq_kr
        + Kstar3 * (Cphi * ‖m‖) * Cq_hr * Cq_kl
        + Kstar3 * (Cphi * ‖r‖) * Cq_hk * Cq_lm
        + Kstar3 * (Cphi * ‖r‖) * Cq_hl * Cq_km
        + Kstar3 * (Cphi * ‖r‖) * Cq_hm * Cq_kl
        + Kstar3 * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hkl
        + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hkm
        + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hkr
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_hlm
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hlr
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hmr
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖r‖) * Cq_klm
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_klr
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_kmr
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lmr
        + Kstar2 * Cq_hkl * Cq_mr
        + Kstar2 * Cq_hkm * Cq_lr
        + Kstar2 * Cq_hkr * Cq_lm
        + Kstar2 * Cq_hlm * Cq_kr
        + Kstar2 * Cq_hlr * Cq_km
        + Kstar2 * Cq_hmr * Cq_kl
        + Kstar2 * Cq_klm * Cq_hr
        + Kstar2 * Cq_klr * Cq_hm
        + Kstar2 * Cq_kmr * Cq_hl
        + Kstar2 * Cq_lmr * Cq_hk
        + Kstar2 * (Cphi * ‖h‖) * Cq_klmr
        + Kstar2 * (Cphi * ‖k‖) * Cq_hlmr
        + Kstar2 * (Cphi * ‖l‖) * Cq_hkmr
        + Kstar2 * (Cphi * ‖m‖) * Cq_hklr
        + Kstar2 * (Cphi * ‖r‖) * Cq_hklm := by positivity
  have hΘbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t‖
        ≤ Kstar5 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖)
            + Kstar4 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hk
            + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hl
            + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hm
            + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hr
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_kl
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_km
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_kr
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_lm
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_lr
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_mr
            + Kstar3 * (Cphi * ‖h‖) * Cq_kl * Cq_mr
            + Kstar3 * (Cphi * ‖h‖) * Cq_km * Cq_lr
            + Kstar3 * (Cphi * ‖h‖) * Cq_kr * Cq_lm
            + Kstar3 * (Cphi * ‖k‖) * Cq_hl * Cq_mr
            + Kstar3 * (Cphi * ‖k‖) * Cq_hm * Cq_lr
            + Kstar3 * (Cphi * ‖k‖) * Cq_hr * Cq_lm
            + Kstar3 * (Cphi * ‖l‖) * Cq_hk * Cq_mr
            + Kstar3 * (Cphi * ‖l‖) * Cq_hm * Cq_kr
            + Kstar3 * (Cphi * ‖l‖) * Cq_hr * Cq_km
            + Kstar3 * (Cphi * ‖m‖) * Cq_hk * Cq_lr
            + Kstar3 * (Cphi * ‖m‖) * Cq_hl * Cq_kr
            + Kstar3 * (Cphi * ‖m‖) * Cq_hr * Cq_kl
            + Kstar3 * (Cphi * ‖r‖) * Cq_hk * Cq_lm
            + Kstar3 * (Cphi * ‖r‖) * Cq_hl * Cq_km
            + Kstar3 * (Cphi * ‖r‖) * Cq_hm * Cq_kl
            + Kstar3 * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hkl
            + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hkm
            + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hkr
            + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_hlm
            + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hlr
            + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hmr
            + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖r‖) * Cq_klm
            + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_klr
            + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_kmr
            + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lmr
            + Kstar2 * Cq_hkl * Cq_mr
            + Kstar2 * Cq_hkm * Cq_lr
            + Kstar2 * Cq_hkr * Cq_lm
            + Kstar2 * Cq_hlm * Cq_kr
            + Kstar2 * Cq_hlr * Cq_km
            + Kstar2 * Cq_hmr * Cq_kl
            + Kstar2 * Cq_klm * Cq_hr
            + Kstar2 * Cq_klr * Cq_hm
            + Kstar2 * Cq_kmr * Cq_hl
            + Kstar2 * Cq_lmr * Cq_hk
            + Kstar2 * (Cphi * ‖h‖) * Cq_klmr
            + Kstar2 * (Cphi * ‖k‖) * Cq_hlmr
            + Kstar2 * (Cphi * ‖l‖) * Cq_hkmr
            + Kstar2 * (Cphi * ‖m‖) * Cq_hklr
            + Kstar2 * (Cphi * ‖r‖) * Cq_hklm :=
    fun t ht => expJet5Rhs_norm_le g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r Kstar5 Kstar4 Kstar3 Kstar2 Cphi Cq_hk Cq_hl Cq_hm Cq_hr Cq_kl Cq_km Cq_kr Cq_lm Cq_lr Cq_mr Cq_hkl Cq_hkm Cq_hkr Cq_hlm Cq_hlr Cq_hmr Cq_klm Cq_klr Cq_kmr Cq_lmr Cq_hklm Cq_hklr Cq_hkmr Cq_hlmr Cq_klmr
      hKstar50 hKstar40 hKstar30 hKstar20 hCphi0
      hKstar5 hKstar4 hKstar3 hKstar2 hCphi
      hCqhk hCqhl hCqhm hCqhr hCqkl hCqkm hCqkr hCqlm hCqlr hCqmr hCqhkl hCqhkm hCqhkr hCqhlm hCqhlr hCqhmr hCqklm hCqklr hCqkmr hCqlmr hCqhklm hCqhklr hCqhkmr hCqhlmr hCqklmr t ht
  exact gronwall_vec_residual R
    (fun t => expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar _ hKstar0 hρ0 hR0 hderiv hKstar hΘbd

set_option maxHeartbeats 12800000 in
/-- **The `[0,1]`-uniform value bound for the fifth variation `R^{hklmr}`.**  The `∀ t ∈ [0,1]`
    mirror of `expJet5Fund_value_bound` (its `t = 1` endpoint): the 51-term `Θ₅^{hklmr}` source
    bound fed into the `[0,1]`-uniform vector Grönwall (`gronwall_vec_residual_Icc`) gives
    `‖R t‖ ≤ ρ₅·e^{Kstar}` for every `t`.  Mirror of `expJet4Fund_value_bound_Icc`. -/
theorem expJet5Fund_value_bound_Icc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (h k l m r : Point n)
    (Kstar Kstar5 Kstar4 Kstar3 Kstar2 Cphi : ℝ)
    (Cq_hk Cq_hl Cq_hm Cq_hr Cq_kl Cq_km Cq_kr Cq_lm Cq_lr Cq_mr : ℝ)
    (Cq_hkl Cq_hkm Cq_hkr Cq_hlm Cq_hlr Cq_hmr Cq_klm Cq_klr Cq_kmr Cq_lmr : ℝ)
    (Cq_hklm Cq_hklr Cq_hkmr Cq_hlmr Cq_klmr : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar50 : 0 ≤ Kstar5) (hKstar40 : 0 ≤ Kstar4)
    (hKstar30 : 0 ≤ Kstar3) (hKstar20 : 0 ≤ Kstar2) (hCphi0 : 0 ≤ Cphi)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hKstar5 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
        (expTube g gi hC p v t)‖ ≤ Kstar5)
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
    (hCqhr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhr t‖ ≤ Cq_hr)
    (hCqkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq_kl)
    (hCqkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkm t‖ ≤ Cq_km)
    (hCqkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkr t‖ ≤ Cq_kr)
    (hCqlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlm t‖ ≤ Cq_lm)
    (hCqlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlr t‖ ≤ Cq_lr)
    (hCqmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qmr t‖ ≤ Cq_mr)
    (hCqhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkl t‖ ≤ Cq_hkl)
    (hCqhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkm t‖ ≤ Cq_hkm)
    (hCqhkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkr t‖ ≤ Cq_hkr)
    (hCqhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlm t‖ ≤ Cq_hlm)
    (hCqhlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlr t‖ ≤ Cq_hlr)
    (hCqhmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmr t‖ ≤ Cq_hmr)
    (hCqklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklm t‖ ≤ Cq_klm)
    (hCqklr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklr t‖ ≤ Cq_klr)
    (hCqkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmr t‖ ≤ Cq_kmr)
    (hCqlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmr t‖ ≤ Cq_lmr)
    (hCqhklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklm t‖ ≤ Cq_hklm)
    (hCqhklr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklr t‖ ≤ Cq_hklr)
    (hCqhkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkmr t‖ ≤ Cq_hkmr)
    (hCqhlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlmr t‖ ≤ Cq_hlmr)
    (hCqklmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklmr t‖ ≤ Cq_klmr)
    (R : ℝ → (Point n × Point n)) (hR0 : R 0 = 0)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt R
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
        (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖R t‖ ≤ (Kstar5 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖)
          + Kstar4 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hk
          + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hl
          + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hm
          + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hr
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_kl
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_km
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_kr
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_lm
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_lr
          + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_mr
          + Kstar3 * (Cphi * ‖h‖) * Cq_kl * Cq_mr
          + Kstar3 * (Cphi * ‖h‖) * Cq_km * Cq_lr
          + Kstar3 * (Cphi * ‖h‖) * Cq_kr * Cq_lm
          + Kstar3 * (Cphi * ‖k‖) * Cq_hl * Cq_mr
          + Kstar3 * (Cphi * ‖k‖) * Cq_hm * Cq_lr
          + Kstar3 * (Cphi * ‖k‖) * Cq_hr * Cq_lm
          + Kstar3 * (Cphi * ‖l‖) * Cq_hk * Cq_mr
          + Kstar3 * (Cphi * ‖l‖) * Cq_hm * Cq_kr
          + Kstar3 * (Cphi * ‖l‖) * Cq_hr * Cq_km
          + Kstar3 * (Cphi * ‖m‖) * Cq_hk * Cq_lr
          + Kstar3 * (Cphi * ‖m‖) * Cq_hl * Cq_kr
          + Kstar3 * (Cphi * ‖m‖) * Cq_hr * Cq_kl
          + Kstar3 * (Cphi * ‖r‖) * Cq_hk * Cq_lm
          + Kstar3 * (Cphi * ‖r‖) * Cq_hl * Cq_km
          + Kstar3 * (Cphi * ‖r‖) * Cq_hm * Cq_kl
          + Kstar3 * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hkl
          + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hkm
          + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hkr
          + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_hlm
          + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hlr
          + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hmr
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖r‖) * Cq_klm
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_klr
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_kmr
          + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lmr
          + Kstar2 * Cq_hkl * Cq_mr
          + Kstar2 * Cq_hkm * Cq_lr
          + Kstar2 * Cq_hkr * Cq_lm
          + Kstar2 * Cq_hlm * Cq_kr
          + Kstar2 * Cq_hlr * Cq_km
          + Kstar2 * Cq_hmr * Cq_kl
          + Kstar2 * Cq_klm * Cq_hr
          + Kstar2 * Cq_klr * Cq_hm
          + Kstar2 * Cq_kmr * Cq_hl
          + Kstar2 * Cq_lmr * Cq_hk
          + Kstar2 * (Cphi * ‖h‖) * Cq_klmr
          + Kstar2 * (Cphi * ‖k‖) * Cq_hlmr
          + Kstar2 * (Cphi * ‖l‖) * Cq_hkmr
          + Kstar2 * (Cphi * ‖m‖) * Cq_hklr
          + Kstar2 * (Cphi * ‖r‖) * Cq_hklm) * Real.exp Kstar := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num [Set.mem_Icc]
  have hCqhk0 : 0 ≤ Cq_hk := (norm_nonneg _).trans (hCqhk 0 hmem0)
  have hCqhl0 : 0 ≤ Cq_hl := (norm_nonneg _).trans (hCqhl 0 hmem0)
  have hCqhm0 : 0 ≤ Cq_hm := (norm_nonneg _).trans (hCqhm 0 hmem0)
  have hCqhr0 : 0 ≤ Cq_hr := (norm_nonneg _).trans (hCqhr 0 hmem0)
  have hCqkl0 : 0 ≤ Cq_kl := (norm_nonneg _).trans (hCqkl 0 hmem0)
  have hCqkm0 : 0 ≤ Cq_km := (norm_nonneg _).trans (hCqkm 0 hmem0)
  have hCqkr0 : 0 ≤ Cq_kr := (norm_nonneg _).trans (hCqkr 0 hmem0)
  have hCqlm0 : 0 ≤ Cq_lm := (norm_nonneg _).trans (hCqlm 0 hmem0)
  have hCqlr0 : 0 ≤ Cq_lr := (norm_nonneg _).trans (hCqlr 0 hmem0)
  have hCqmr0 : 0 ≤ Cq_mr := (norm_nonneg _).trans (hCqmr 0 hmem0)
  have hCqhkl0 : 0 ≤ Cq_hkl := (norm_nonneg _).trans (hCqhkl 0 hmem0)
  have hCqhkm0 : 0 ≤ Cq_hkm := (norm_nonneg _).trans (hCqhkm 0 hmem0)
  have hCqhkr0 : 0 ≤ Cq_hkr := (norm_nonneg _).trans (hCqhkr 0 hmem0)
  have hCqhlm0 : 0 ≤ Cq_hlm := (norm_nonneg _).trans (hCqhlm 0 hmem0)
  have hCqhlr0 : 0 ≤ Cq_hlr := (norm_nonneg _).trans (hCqhlr 0 hmem0)
  have hCqhmr0 : 0 ≤ Cq_hmr := (norm_nonneg _).trans (hCqhmr 0 hmem0)
  have hCqklm0 : 0 ≤ Cq_klm := (norm_nonneg _).trans (hCqklm 0 hmem0)
  have hCqklr0 : 0 ≤ Cq_klr := (norm_nonneg _).trans (hCqklr 0 hmem0)
  have hCqkmr0 : 0 ≤ Cq_kmr := (norm_nonneg _).trans (hCqkmr 0 hmem0)
  have hCqlmr0 : 0 ≤ Cq_lmr := (norm_nonneg _).trans (hCqlmr 0 hmem0)
  have hCqhklm0 : 0 ≤ Cq_hklm := (norm_nonneg _).trans (hCqhklm 0 hmem0)
  have hCqhklr0 : 0 ≤ Cq_hklr := (norm_nonneg _).trans (hCqhklr 0 hmem0)
  have hCqhkmr0 : 0 ≤ Cq_hkmr := (norm_nonneg _).trans (hCqhkmr 0 hmem0)
  have hCqhlmr0 : 0 ≤ Cq_hlmr := (norm_nonneg _).trans (hCqhlmr 0 hmem0)
  have hCqklmr0 : 0 ≤ Cq_klmr := (norm_nonneg _).trans (hCqklmr 0 hmem0)
  have hρ0 : (0 : ℝ) ≤ Kstar5 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖)
        + Kstar4 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hk
        + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hl
        + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hm
        + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hr
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_kl
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_km
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_kr
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_lm
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_lr
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_mr
        + Kstar3 * (Cphi * ‖h‖) * Cq_kl * Cq_mr
        + Kstar3 * (Cphi * ‖h‖) * Cq_km * Cq_lr
        + Kstar3 * (Cphi * ‖h‖) * Cq_kr * Cq_lm
        + Kstar3 * (Cphi * ‖k‖) * Cq_hl * Cq_mr
        + Kstar3 * (Cphi * ‖k‖) * Cq_hm * Cq_lr
        + Kstar3 * (Cphi * ‖k‖) * Cq_hr * Cq_lm
        + Kstar3 * (Cphi * ‖l‖) * Cq_hk * Cq_mr
        + Kstar3 * (Cphi * ‖l‖) * Cq_hm * Cq_kr
        + Kstar3 * (Cphi * ‖l‖) * Cq_hr * Cq_km
        + Kstar3 * (Cphi * ‖m‖) * Cq_hk * Cq_lr
        + Kstar3 * (Cphi * ‖m‖) * Cq_hl * Cq_kr
        + Kstar3 * (Cphi * ‖m‖) * Cq_hr * Cq_kl
        + Kstar3 * (Cphi * ‖r‖) * Cq_hk * Cq_lm
        + Kstar3 * (Cphi * ‖r‖) * Cq_hl * Cq_km
        + Kstar3 * (Cphi * ‖r‖) * Cq_hm * Cq_kl
        + Kstar3 * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hkl
        + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hkm
        + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hkr
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_hlm
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hlr
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hmr
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖r‖) * Cq_klm
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_klr
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_kmr
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lmr
        + Kstar2 * Cq_hkl * Cq_mr
        + Kstar2 * Cq_hkm * Cq_lr
        + Kstar2 * Cq_hkr * Cq_lm
        + Kstar2 * Cq_hlm * Cq_kr
        + Kstar2 * Cq_hlr * Cq_km
        + Kstar2 * Cq_hmr * Cq_kl
        + Kstar2 * Cq_klm * Cq_hr
        + Kstar2 * Cq_klr * Cq_hm
        + Kstar2 * Cq_kmr * Cq_hl
        + Kstar2 * Cq_lmr * Cq_hk
        + Kstar2 * (Cphi * ‖h‖) * Cq_klmr
        + Kstar2 * (Cphi * ‖k‖) * Cq_hlmr
        + Kstar2 * (Cphi * ‖l‖) * Cq_hkmr
        + Kstar2 * (Cphi * ‖m‖) * Cq_hklr
        + Kstar2 * (Cphi * ‖r‖) * Cq_hklm := by positivity
  have hΘbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t‖
        ≤ Kstar5 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖)
            + Kstar4 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hk
            + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hl
            + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hm
            + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hr
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_kl
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_km
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_kr
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_lm
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_lr
            + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_mr
            + Kstar3 * (Cphi * ‖h‖) * Cq_kl * Cq_mr
            + Kstar3 * (Cphi * ‖h‖) * Cq_km * Cq_lr
            + Kstar3 * (Cphi * ‖h‖) * Cq_kr * Cq_lm
            + Kstar3 * (Cphi * ‖k‖) * Cq_hl * Cq_mr
            + Kstar3 * (Cphi * ‖k‖) * Cq_hm * Cq_lr
            + Kstar3 * (Cphi * ‖k‖) * Cq_hr * Cq_lm
            + Kstar3 * (Cphi * ‖l‖) * Cq_hk * Cq_mr
            + Kstar3 * (Cphi * ‖l‖) * Cq_hm * Cq_kr
            + Kstar3 * (Cphi * ‖l‖) * Cq_hr * Cq_km
            + Kstar3 * (Cphi * ‖m‖) * Cq_hk * Cq_lr
            + Kstar3 * (Cphi * ‖m‖) * Cq_hl * Cq_kr
            + Kstar3 * (Cphi * ‖m‖) * Cq_hr * Cq_kl
            + Kstar3 * (Cphi * ‖r‖) * Cq_hk * Cq_lm
            + Kstar3 * (Cphi * ‖r‖) * Cq_hl * Cq_km
            + Kstar3 * (Cphi * ‖r‖) * Cq_hm * Cq_kl
            + Kstar3 * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hkl
            + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hkm
            + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hkr
            + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_hlm
            + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hlr
            + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hmr
            + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖r‖) * Cq_klm
            + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_klr
            + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_kmr
            + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lmr
            + Kstar2 * Cq_hkl * Cq_mr
            + Kstar2 * Cq_hkm * Cq_lr
            + Kstar2 * Cq_hkr * Cq_lm
            + Kstar2 * Cq_hlm * Cq_kr
            + Kstar2 * Cq_hlr * Cq_km
            + Kstar2 * Cq_hmr * Cq_kl
            + Kstar2 * Cq_klm * Cq_hr
            + Kstar2 * Cq_klr * Cq_hm
            + Kstar2 * Cq_kmr * Cq_hl
            + Kstar2 * Cq_lmr * Cq_hk
            + Kstar2 * (Cphi * ‖h‖) * Cq_klmr
            + Kstar2 * (Cphi * ‖k‖) * Cq_hlmr
            + Kstar2 * (Cphi * ‖l‖) * Cq_hkmr
            + Kstar2 * (Cphi * ‖m‖) * Cq_hklr
            + Kstar2 * (Cphi * ‖r‖) * Cq_hklm :=
    fun t ht => expJet5Rhs_norm_le g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r Kstar5 Kstar4 Kstar3 Kstar2 Cphi Cq_hk Cq_hl Cq_hm Cq_hr Cq_kl Cq_km Cq_kr Cq_lm Cq_lr Cq_mr Cq_hkl Cq_hkm Cq_hkr Cq_hlm Cq_hlr Cq_hmr Cq_klm Cq_klr Cq_kmr Cq_lmr Cq_hklm Cq_hklr Cq_hkmr Cq_hlmr Cq_klmr
      hKstar50 hKstar40 hKstar30 hKstar20 hCphi0
      hKstar5 hKstar4 hKstar3 hKstar2 hCphi
      hCqhk hCqhl hCqhm hCqhr hCqkl hCqkm hCqkr hCqlm hCqlr hCqmr hCqhkl hCqhkm hCqhkr hCqhlm hCqhlr hCqhmr hCqklm hCqklr hCqkmr hCqlmr hCqhklm hCqhklr hCqhkmr hCqhlmr hCqklmr t ht
  exact gronwall_vec_residual_Icc R
    (fun t => expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar _ hKstar0 hρ0 hR0 hderiv hKstar hΘbd

/-! ### §2. The order-4 curve mirrors `expJet4Curve` / `expJet4CurveG`

Mirror of `expJet3Curve` (`ExpJet4D.lean`) / `expJet3CurveG` (`ExpJet4DFull.lean`) one Fréchet
order up: the `expJet4Fund` witness kept as a WHOLE curve (the Jet₅ source `expJet5Rhs` feeds the
fourth variations pointwise), then the genuine version with the pair/triple slots instantiated by
`expJet2Curve` / `expJet3CurveG`.  The `t = 1` values are `expJet4Val` / `expJet4ValG`. -/

/-- The **fourth-variation curve** `t ↦ R^{hklm}_v(t)`: the chosen `expJet4Fund` witness for the
    direction quadruple `(h,k,l,m)` with abstract `Q··`/`Q···` inputs.  Mirror of `expJet3Curve`
    one order up; its `t = 1` value is `expJet4Val`. -/
noncomputable def expJet4Curve (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
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
    (h k l m : Point n) : ℝ → (Point n × Point n) :=
  (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose

/-- `expJet4Curve` is continuous on `[0,1]` (the `expJet4Fund` witness spec). -/
theorem expJet4Curve_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
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
    ContinuousOn (expJet4Curve g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m) (Set.Icc (0 : ℝ) 1) :=
  (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec.2.1

/-- The `t = 1` value of `expJet4Curve` is `expJet4Val`. -/
theorem expJet4Curve_one (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
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
    expJet4Curve g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m 1 = expJet4Val g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m := rfl

/-- The **genuine fourth-variation curve** `t ↦ R^{hklm}_v(t)` with the six pair-`Q··` slots
    instantiated by `expJet2Curve` and the four triple-`Q···` slots by `expJet3CurveG` (exactly the
    slot-filling of `expJet4ValG`).  Mirror of `expJet3CurveG` one order up; the QUADRUPLE-slot
    feeder of `expJet5ValG`. -/
noncomputable def expJet4CurveG (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l m : Point n) : ℝ → (Point n × Point n) :=
  expJet4Curve g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m)
    h k l m

/-- `expJet4CurveG` is continuous on `[0,1]`. -/
theorem expJet4CurveG_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l m : Point n) :
    ContinuousOn (expJet4CurveG g gi hC p v Φ hv hΦcont h k l m) (Set.Icc (0 : ℝ) 1) :=
  expJet4Curve_continuousOn g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m)
    h k l m

/-- The `t = 1` value of `expJet4CurveG` is `expJet4ValG`. -/
theorem expJet4CurveG_one (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l m : Point n) :
    expJet4CurveG g gi hC p v Φ hv hΦcont h k l m 1
      = expJet4ValG g gi hC p v Φ hv hΦcont h k l m := rfl

/-! ### §3. The fifth-variation value `expJet5Val` and its genuine instantiation `expJet5ValG` -/

/-- **★ The fifth-variation value** `R^{hklmr}_v(1)`: the chosen `expJet5Fund` witness at `t = 1`,
    with the 25 abstract `Q`-slots.  Mirror of `expJet4Val` one order up.  NOTE: `expJet5Fund`
    takes `hv`/continuity AFTER the `Q`-slots, so the argument order here follows `expJet5Fund`
    (not `expJet4Val`). -/
noncomputable def expJet5Val (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
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
    (h k l m r : Point n) : Point n × Point n :=
  (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose 1

/-- **★ The genuine fifth-variation value** `R^{hklmr}_v(1)` with all 25 `Q`-slots instantiated by
    the ACTUAL lower-jet curves: the ten pair-`Q··` slots by `expJet2Curve`, the ten
    triple-`Q···` slots by `expJet3CurveG`, and the five quadruple-`Q····` slots by
    `expJet4CurveG`.  Mirror of `expJet4ValG` one order up; the datum the J5-4 `expJetD5`
    packaging will consume. -/
noncomputable def expJet5ValG (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l m r : Point n) : Point n × Point n :=
  expJet5Val g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont h r)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k r)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l r)
    (expJet2Curve g gi hC p v Φ hv hΦcont m r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h m r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k m r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont l m r)
    (expJet4CurveG g gi hC p v Φ hv hΦcont h k l m)
    (expJet4CurveG g gi hC p v Φ hv hΦcont h k l r)
    (expJet4CurveG g gi hC p v Φ hv hΦcont h k m r)
    (expJet4CurveG g gi hC p v Φ hv hΦcont h l m r)
    (expJet4CurveG g gi hC p v Φ hv hΦcont k l m r)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k r)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l r)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h m r)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l r)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k m r)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont l m r)
    (expJet4CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l m)
    (expJet4CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l r)
    (expJet4CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m r)
    (expJet4CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m r)
    (expJet4CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m r)
    h k l m r

/-! ### §4. The uniform 5-linear value bound (mirror of `expJet4ValG_norm_le`) -/

set_option maxHeartbeats 25600000 in
/-- **Uniform 5-linear value bound for `expJet5ValG`.**  A single `M ≥ 0` with
    `‖expJet5ValG h k l m r‖ ≤ M·‖h‖·‖k‖·‖l‖·‖m‖·‖r‖` for all `(h,k,l,m,r)`, from the `[0,1]`
    tube bounds `Kstar/Kstar5/4/3/2`, the `Φ` compactness bound `Cphi`, the pair-curve bounds
    (`expJet2Fund_value_bound_Icc`), the triple-curve bounds (`expJet3Fund_value_bound_Icc`) and
    the quadruple-curve bounds (`expJet4Fund_value_bound_Icc`) fed into the 51-term
    `expJet5Fund_value_bound`.  Mirror of `expJet4ValG_norm_le` one order up. -/
theorem expJet5ValG_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h k l m r : Point n,
      ‖expJet5ValG g gi hC p v Φ hv hΦcont h k l m r‖ ≤ M * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ := by
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨Kstar5, hKstar50, hKstar5u⟩ := expJet_fderiv5_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar4, hKstar40, hKstar4u⟩ := expJet_fderiv4_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hKstar3u⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar2, hKstar20, hKstar2u⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  have hKstar5 := hKstar5u v hv
  have hKstar4 := hKstar4u v hv
  have hKstar3 := hKstar3u v hv
  have hKstar2 := hKstar2u v hv
  obtain ⟨Cb, hCb⟩ := (isCompact_Icc).exists_bound_of_continuousOn hΦcont
  set Cphi : ℝ := max Cb 0 with hCphidef
  have hCphi0 : 0 ≤ Cphi := le_max_right _ _
  have hCphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi :=
    fun t ht => (hCb t ht).trans (le_max_left _ _)
  refine ⟨(Kstar5 * Cphi ^ 5 + 10 * (Kstar4 * Cphi ^ 3 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 15 * (Kstar3 * Cphi * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2) + 10 * (Kstar3 * Cphi ^ 2 * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar)) + 10 * (Kstar2 * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 5 * (Kstar2 * Cphi * ((Kstar4 * Cphi ^ 4 + 6 * (Kstar3 * Cphi ^ 2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2) + 4 * (Kstar2 * Cphi * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar))) * Real.exp Kstar))) * Real.exp Kstar, by positivity, fun h k l m r => ?_⟩
  -- pair-curve bounds on `[0,1]`
  have pb : ∀ a b : Point n,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖expJet2Curve g gi hC p v Φ hv hΦcont a b t‖
        ≤ (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖a‖ * ‖b‖ := by
    intro a b
    obtain ⟨-, -, -, hderiv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont a b).choose_spec
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ a b Kstar Kstar2 Cphi hKstar0 hKstar20 hCphi0
      hKstar hKstar2 hCphi (expJet2Curve g gi hC p v Φ hv hΦcont a b)
      ((expJet2Fund g gi hC p v Φ hv hΦcont a b).choose_spec).1 hderiv
  -- triple-curve bounds on `[0,1]`
  have tb : ∀ a b c : Point n,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖expJet3CurveG g gi hC p v Φ hv hΦcont a b c t‖
        ≤ ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖a‖ * ‖b‖ * ‖c‖ := by
    intro a b c t ht
    obtain ⟨hR0, -, -, hRderiv⟩ :=
      (expJet3Fund g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv hΦcont b c)
        (expJet2Curve g gi hC p v Φ hv hΦcont a c)
        (expJet2Curve g gi hC p v Φ hv hΦcont a b) hv hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont b c)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont a c)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont a b) a b c).choose_spec
    exact (expJet3Fund_value_bound_Icc g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont b c)
      (expJet2Curve g gi hC p v Φ hv hΦcont a c)
      (expJet2Curve g gi hC p v Φ hv hΦcont a b) a b c
      Kstar Kstar3 Kstar2 Cphi
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖b‖ * ‖c‖)
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖a‖ * ‖c‖)
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖a‖ * ‖b‖)
      hKstar0 hKstar30 hKstar20 hCphi0 hKstar hKstar3 hKstar2 hCphi
      (pb b c) (pb a c) (pb a b)
      (expJet3CurveG g gi hC p v Φ hv hΦcont a b c) hR0 hRderiv t ht).trans (le_of_eq (by ring))
  -- quadruple-curve bounds on `[0,1]` (via the fourteen-term `expJet4Fund_value_bound_Icc`)
  have qb : ∀ a b c d : Point n,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖expJet4CurveG g gi hC p v Φ hv hΦcont a b c d t‖
        ≤ ((Kstar4 * Cphi ^ 4 + 6 * (Kstar3 * Cphi ^ 2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2) + 4 * (Kstar2 * Cphi * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar))) * Real.exp Kstar) * ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by
    intro a b c d t ht
    obtain ⟨hR0, -, -, hRderiv⟩ :=
      (expJet4Fund g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv hΦcont a b)
        (expJet2Curve g gi hC p v Φ hv hΦcont a c)
        (expJet2Curve g gi hC p v Φ hv hΦcont a d)
        (expJet2Curve g gi hC p v Φ hv hΦcont b c)
        (expJet2Curve g gi hC p v Φ hv hΦcont b d)
        (expJet2Curve g gi hC p v Φ hv hΦcont c d)
        (expJet3CurveG g gi hC p v Φ hv hΦcont a b c)
        (expJet3CurveG g gi hC p v Φ hv hΦcont a b d)
        (expJet3CurveG g gi hC p v Φ hv hΦcont a c d)
        (expJet3CurveG g gi hC p v Φ hv hΦcont b c d)
        hv hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont a b)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont a c)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont a d)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont b c)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont b d)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont c d)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont a b c)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont a b d)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont a c d)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont b c d)
        a b c d).choose_spec
    exact (expJet4Fund_value_bound_Icc g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont a b)
      (expJet2Curve g gi hC p v Φ hv hΦcont a c)
      (expJet2Curve g gi hC p v Φ hv hΦcont a d)
      (expJet2Curve g gi hC p v Φ hv hΦcont b c)
      (expJet2Curve g gi hC p v Φ hv hΦcont b d)
      (expJet2Curve g gi hC p v Φ hv hΦcont c d)
      (expJet3CurveG g gi hC p v Φ hv hΦcont a b c)
      (expJet3CurveG g gi hC p v Φ hv hΦcont a b d)
      (expJet3CurveG g gi hC p v Φ hv hΦcont a c d)
      (expJet3CurveG g gi hC p v Φ hv hΦcont b c d)
      a b c d Kstar Kstar4 Kstar3 Kstar2 Cphi
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖a‖ * ‖b‖)
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖a‖ * ‖c‖)
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖a‖ * ‖d‖)
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖b‖ * ‖c‖)
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖b‖ * ‖d‖)
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖c‖ * ‖d‖)
      (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖a‖ * ‖b‖ * ‖c‖)
      (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖a‖ * ‖b‖ * ‖d‖)
      (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖a‖ * ‖c‖ * ‖d‖)
      (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖b‖ * ‖c‖ * ‖d‖)
      hKstar0 hKstar40 hKstar30 hKstar20 hCphi0 hKstar hKstar4 hKstar3 hKstar2 hCphi
      (pb a b) (pb a c) (pb a d) (pb b c) (pb b d) (pb c d)
      (tb a b c) (tb a b d) (tb a c d) (tb b c d)
      (expJet4CurveG g gi hC p v Φ hv hΦcont a b c d) hR0 hRderiv t ht).trans (le_of_eq (by ring))
  obtain ⟨hRt0, -, -, hRtderiv⟩ :=
    (expJet5Fund g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h m)
      (expJet2Curve g gi hC p v Φ hv hΦcont h r)
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont k m)
      (expJet2Curve g gi hC p v Φ hv hΦcont k r)
      (expJet2Curve g gi hC p v Φ hv hΦcont l m)
      (expJet2Curve g gi hC p v Φ hv hΦcont l r)
      (expJet2Curve g gi hC p v Φ hv hΦcont m r)
      (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
      (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
      (expJet3CurveG g gi hC p v Φ hv hΦcont h k r)
      (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
      (expJet3CurveG g gi hC p v Φ hv hΦcont h l r)
      (expJet3CurveG g gi hC p v Φ hv hΦcont h m r)
      (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
      (expJet3CurveG g gi hC p v Φ hv hΦcont k l r)
      (expJet3CurveG g gi hC p v Φ hv hΦcont k m r)
      (expJet3CurveG g gi hC p v Φ hv hΦcont l m r)
      (expJet4CurveG g gi hC p v Φ hv hΦcont h k l m)
      (expJet4CurveG g gi hC p v Φ hv hΦcont h k l r)
      (expJet4CurveG g gi hC p v Φ hv hΦcont h k m r)
      (expJet4CurveG g gi hC p v Φ hv hΦcont h l m r)
      (expJet4CurveG g gi hC p v Φ hv hΦcont k l m r)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k r)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l r)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h m r)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l r)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k m r)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont l m r)
      (expJet4CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l m)
      (expJet4CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l r)
      (expJet4CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m r)
      (expJet4CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m r)
      (expJet4CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m r)
      h k l m r).choose_spec
  have hbd := expJet5Fund_value_bound g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont h r)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k r)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l r)
    (expJet2Curve g gi hC p v Φ hv hΦcont m r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h m r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k m r)
    (expJet3CurveG g gi hC p v Φ hv hΦcont l m r)
    (expJet4CurveG g gi hC p v Φ hv hΦcont h k l m)
    (expJet4CurveG g gi hC p v Φ hv hΦcont h k l r)
    (expJet4CurveG g gi hC p v Φ hv hΦcont h k m r)
    (expJet4CurveG g gi hC p v Φ hv hΦcont h l m r)
    (expJet4CurveG g gi hC p v Φ hv hΦcont k l m r)
    h k l m r Kstar Kstar5 Kstar4 Kstar3 Kstar2 Cphi
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖r‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖r‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖h‖ * ‖m‖ * ‖r‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖r‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖k‖ * ‖m‖ * ‖r‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * ‖l‖ * ‖m‖ * ‖r‖)
    (((Kstar4 * Cphi ^ 4 + 6 * (Kstar3 * Cphi ^ 2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2) + 4 * (Kstar2 * Cphi * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar))) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖)
    (((Kstar4 * Cphi ^ 4 + 6 * (Kstar3 * Cphi ^ 2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2) + 4 * (Kstar2 * Cphi * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar))) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖)
    (((Kstar4 * Cphi ^ 4 + 6 * (Kstar3 * Cphi ^ 2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2) + 4 * (Kstar2 * Cphi * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar))) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖)
    (((Kstar4 * Cphi ^ 4 + 6 * (Kstar3 * Cphi ^ 2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2) + 4 * (Kstar2 * Cphi * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar))) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖)
    (((Kstar4 * Cphi ^ 4 + 6 * (Kstar3 * Cphi ^ 2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2) + 4 * (Kstar2 * Cphi * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar))) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖)
    hKstar0 hKstar50 hKstar40 hKstar30 hKstar20 hCphi0
    hKstar hKstar5 hKstar4 hKstar3 hKstar2 hCphi
    (pb h k) (pb h l) (pb h m) (pb h r) (pb k l) (pb k m) (pb k r) (pb l m) (pb l r) (pb m r)
    (tb h k l) (tb h k m) (tb h k r) (tb h l m) (tb h l r) (tb h m r) (tb k l m) (tb k l r) (tb k m r) (tb l m r)
    (qb h k l m) (qb h k l r) (qb h k m r) (qb h l m r) (qb k l m r)
    _ hRt0 hRtderiv
  calc ‖expJet5ValG g gi hC p v Φ hv hΦcont h k l m r‖
      ≤ _ := hbd
    _ = (Kstar5 * Cphi ^ 5 + 10 * (Kstar4 * Cphi ^ 3 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 15 * (Kstar3 * Cphi * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2) + 10 * (Kstar3 * Cphi ^ 2 * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar)) + 10 * (Kstar2 * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar) * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 5 * (Kstar2 * Cphi * ((Kstar4 * Cphi ^ 4 + 6 * (Kstar3 * Cphi ^ 2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar)) + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2) + 4 * (Kstar2 * Cphi * ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar))) * Real.exp Kstar))) * Real.exp Kstar * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ := by ring

/-! ### §5. Non-vacuity gates (cp466 discipline — antecedent inhabitance at curved data) -/

open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp in
/-- **Non-vacuity gate: the D5 value bound runs end-to-end at the GENUINELY CURVED witness.**
    At `g^κ = curvedRNCMetric (−1)` (`hC` from `curvedRNC_hChr`, `p = v = 0`, `hv` from
    `expRho_pos`) with the zero abstract variations, the ACTUAL curved D5 fundamental solution
    (an `IsExpJet5FundSol` witness) satisfies `‖R t‖ ≤ 0` on `[0,1]`: every antecedent of
    `expJet5Fund_value_bound_Icc` is DISCHARGED (tube bounds from the four `_unif` compactness
    lemmas, `Cphi = Cq = 0`) and the 51-term residual collapses to `0` — consistent, since the
    zero-variation solution IS zero.  NOT `a₁ = R/6`. -/
theorem expJet5Fund_value_bound_gate (h k l m r : Point n) :
    ∃ R : ℝ → (Point n × Point n),
      IsExpJet5FundSol (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 (fun _ => 0)
        (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        h k l m r R ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖R t‖ ≤ 0 := by
  have hv : ‖(0 : Point n)‖ ≤ expRho (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) (by norm_num)) (0 : Point n) := by
    simpa using (expRho_pos (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) (by norm_num)) 0).le
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 hv
  obtain ⟨K5, hK50, hK5⟩ := expJet_fderiv5_tube_bddAbove_unif (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨K4, hK40, hK4⟩ := expJet_fderiv4_tube_bddAbove_unif (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨K3, hK30, hK3⟩ := expJet_fderiv3_tube_bddAbove_unif (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨K2, hK20, hK2⟩ := expJet_fderiv2_tube_bddAbove_unif (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨R, hR0, hRcont, hRint, hRderiv⟩ :=
    expJet5Fund (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 (fun _ => 0)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      hv continuousOn_const
      continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const
      h k l m r
  refine ⟨R, ⟨hR0, hRcont, hRint, hRderiv⟩, fun t ht => ?_⟩
  have hb := expJet5Fund_value_bound_Icc (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    h k l m r Kstar K5 K4 K3 K2 0
    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    hKstar0 hK50 hK40 hK30 hK20 le_rfl
    hKstar (fun s hs => hK5 0 hv s hs) (fun s hs => hK4 0 hv s hs)
    (fun s hs => hK3 0 hv s hs) (fun s hs => hK2 0 hv s hs)
    (fun s _ => by simp)
    (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp)
    R hR0 hRderiv t ht
  simpa only [mul_zero, zero_mul, add_zero, zero_add] using hb

open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp in
/-- **Non-vacuity gate: the genuine value layer fires at the GENUINELY CURVED witness.**  All
    antecedents of `expJet5ValG_norm_le` are jointly DISCHARGED at `g^κ = curvedRNCMetric (−1)`
    (`p = v = 0`, `Φ = 0`): the genuine fifth-variation value with the full lower-jet curve
    instantiation admits a uniform 5-linear bound at curved data.  NOT `a₁ = R/6`. -/
theorem expJet5ValG_norm_le_gate :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h k l m r : Point n,
      ‖expJet5ValG (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 (fun _ => 0)
        (by simpa using (expRho_pos (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1))
          (curvedRNC_hChr (-1) (by norm_num)) 0).le)
        continuousOn_const h k l m r‖ ≤ M * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ :=
  expJet5ValG_norm_le (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 (fun _ => 0)
    (by simpa using (expRho_pos (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) (by norm_num)) 0).le)
    continuousOn_const

end QIQTH.ExpMap
