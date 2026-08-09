/-
  SmoothCarrierGrounding — J4-478: GROUND the `hSmooth` in-gate smooth-object regularity carriers of the
  J4-477 `LeafBoxSplice` splice ledger — the three box-continuity inputs
    • `hParamDeriv`  — the heatParametrix `τ`-derivative slice's joint box continuity,
    • `hComposite1`  — the `C^∞` chart-composite's FIRST spatial partial's box continuity (per `k`),
    • `hComposite2`  — the composite's SECOND spatial partial's box continuity (per `i j`),
  consumed by `LeafBoxSplice.leafBox_of_boundary` / `LeafBoxSplice.hIterBase_final`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It only
  REDUCES the three `hSmooth` box carriers to their honest lower-level pieces: the BANKED parametrix
  jet joint continuities (`ParametrixSpatialPartials` / `TransitionAnnulusCont` / `ChartComposedHeatOp`),
  the Mathlib-banked cutoff smoothness (`radialCutoff_contDiff`), the coefficient-regularity carries
  (`hΘc`/`hΘne`/`huc`/`hw`), and the honest CHART-JET carries (first jet `hWc1cont`, second jet / the
  W-HESSIAN `hWc2cont`).  a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring
  stack.  No `sorry` (header prose excepted), no `:= True`, no new axioms; std-3 only.  No existing file
  edited.

  ── THE COMPOSITE STRUCTURE.  The in-gate ungated composite factors DEFEQ through the `C^∞` manifold
     PROFILE `prof τ w' = radialCutoff a b w' · heatParametrix 1 Θ* u* τ w'` (`Θ* = vanVleck g`,
     `u* = transportCoeff (transportOp (vanVleck g) g gi)`):
       `globalCutoffParametrixWitnessN 1 Θ* u* a b W τ x' 0 = prof τ (W₀ x')`,   `W₀ = W 0`.
     (Def-unfold of `globalCutoffParametrixWitnessN`.)  The chart-composed spatial partials then unfold
     by the coordinate CHAIN RULES `pd_comp` (first) / `pd_pd_comp_local` (second) at the `C^∞` profile.

  ── THE GATES per carrier.
     • `hParamDeriv`.  The `radialCutoff` factor is `τ`-INDEPENDENT, so `deriv_const_mul_field` pulls it
       out: the slice = `radialCutoff a b (W₀ ·) · deriv (heatParametrix … · (W₀ ·))`.  The parametrix
       `τ`-derivative composed with the chart is the banked
       `ChartComposedHeatOp.chartComposed_dtau_jointContinuousOn`; the cutoff factor is continuous.
       ⇒ FULLY GROUNDED to (banked parametrix `∂_τ`) + (`radialCutoff` cont) + coefficient regularity.
     • `hComposite1`.  `pd_comp` at `prof`:
         `pd (prof τ ∘ W₀) k = ∑ c, (pd prof τ c ∘ W₀) · (pd (W₀·c) k)`.
       The profile FIRST-partial-composed `pd prof τ c ∘ W₀` is discharged by the manifold PRODUCT RULE
       (`profPd_composed`): four banked factors (`pd radialCutoff`, `heatParametrix`-value,
       `radialCutoff`, `heatParametrix`-`pd`).  The chart first jet is `hWc1cont`.  ⇒ FULLY GROUNDED to
       banks + `hWc1cont` + coefficient regularity.
     • `hComposite2`.  `pd_pd_comp_local` at `prof`:
         `pd² (prof τ ∘ W₀) = ∑ (pd² prof τ ∘ W₀)·(pd W₀)·(pd W₀) + ∑ (pd prof τ ∘ W₀)·(pd² W₀)`.
       The profile SECOND-partial-composed `pd² prof τ ∘ W₀` is discharged by the SECOND manifold
       PRODUCT RULE (`pd_pd_mul` ⇒ `profPdPd_composed`): eight banked factors.  But the SECOND block
       carries `pd (fun y => pd (W₀·a) j y) i` — the CHART HESSIAN `hWc2cont`, which is EXACTLY the
       queued 2nd-order jet atom (`hcont2` / `C₂` territory).  ⇒ REDUCED honestly: hComposite2's sole
       genuine residual (beyond banks + `hWc1cont` + coefficient regularity) is the W-HESSIAN carry.

  ── ★★ THE THREAD CONVERGENCE.  `hComposite2` bottoms out on the CHART HESSIAN joint continuity
     `pd (fun y => pd (uniformInverseChart …·a) j y) i`.  This is the SAME 2nd-order chart-jet atom that
     the queued C₂ / `hcont2` derivative-sup chain (`BaseSlotAmpDeriv` `C₂`/`M₂chart`, the recognized J3
     base-point-regularity blocker `FlowJointRegularity`/`BasepointFDeriv`) needs.  The htermBox splice
     chain and the derivative-sup chain CONVERGE on ONE geometric analytic wall: the second field-jet of
     the uniform inverse chart.  NO fresh wall is introduced here.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    • `pd_pd_mul`             — the general 2nd-order product rule for `pd (pd (f·g) c) d` (`C^∞` `f`,`g`).
    • `profPd_composed`       — the profile FIRST-partial composed with `W₀`, jointly box-continuous
        (manifold product rule ⇒ four banked factors).
    • `profPdPd_composed`     — the profile SECOND-partial composed with `W₀`, jointly box-continuous
        (`pd_pd_mul` ⇒ eight banked factors).
    • `hParamDeriv_grounded`  — ★★★ the `hParamDeriv` box carrier, GROUNDED (per box).
    • `hComposite1_grounded`  — ★★★ the `hComposite1` box carrier, GROUNDED (per box, per `k`).
    • `hComposite2_grounded`  — ★★★ the `hComposite2` box carrier, REDUCED to the W-Hessian (per box, `i j`).
    • `smoothCarriers_family` — ★★★ the three `∀ τ₀ ∈ Ioc 0 T, ∀ R` families in the EXACT shapes
        `LeafBoxSplice.hIterBase_final` consumes for `hParamDeriv`/`hComposite1`/`hComposite2`.
    • `smooth_ledger` (+ intro) — THE SMOOTH LEDGER: the surviving surface after grounding.

  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.LeafBoxSplice
import QIQTH.ChartComposedHeatOp

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LaplaceBeltrami
open QIQTH.HeatParametrixAnsatz QIQTH.HeatTransportRecursion
open QIQTH.ParametrixFunction QIQTH.VanVleck
open QIQTH.ChartComposedHeatOp
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.SmoothCarrierGrounding

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The general 2nd-order product rule `pd (pd (f·g) c) d`.
    ############################################################################### -/

/-- **`pd_pd_mul` — the 2nd-order product rule.**  For `C^∞` fields `f`, `g`, the second coordinate
    partial of the product expands into the four Leibniz terms:
      `pd (fun w => pd (fun y => f y·g y) c w) d x
         = pd (pd f c) d x · g x + pd f c x · pd g d x
           + pd f d x · pd g c x + f x · pd (pd g c) d x`.
    Route: the inner first partial equals the Leibniz sum on a NEIGHBOURHOOD (`pd_mul` pointwise,
    `pd_congr_of_eventuallyEq`), then `pd_add` and `pd_mul` twice; `ring` reconciles associativity.
    NOT `a₁ = R/6`. -/
theorem pd_pd_mul (f g : Point n → ℝ)
    (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f) (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (c d : Fin n) (x : Point n) :
    pd (fun w => pd (fun y => f y * g y) c w) d x
      = pd (fun w => pd f c w) d x * g x + pd f c x * pd g d x
        + pd f d x * pd g c x + f x * pd (fun w => pd g c w) d x := by
  have hfdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hgdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hpdf : Differentiable ℝ (fun y => pd f c y) :=
    (contDiff_pd_inf f hf c).differentiable (by simp)
  have hpdg : Differentiable ℝ (fun y => pd g c y) :=
    (contDiff_pd_inf g hg c).differentiable (by simp)
  have hev : (fun w => pd (fun y => f y * g y) c w)
      =ᶠ[nhds x] (fun w => pd f c w * g w + f w * pd g c w) := by
    refine Filter.Eventually.of_forall (fun w => ?_)
    exact pd_mul f g c w
      (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt f c w (hfdiff w))
      (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt g c w (hgdiff w))
  rw [QIQTH.D2HExpandRecon.pd_congr_of_eventuallyEq _ _ d x hev,
      pd_add (fun w => pd f c w * g w) (fun w => f w * pd g c w) d x
        (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ d x ((hpdf x).mul (hgdiff x)))
        (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ d x ((hfdiff x).mul (hpdg x))),
      pd_mul (fun w => pd f c w) g d x
        (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ d x (hpdf x))
        (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ d x (hgdiff x)),
      pd_mul f (fun w => pd g c w) d x
        (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ d x (hfdiff x))
        (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ d x (hpdg x))]
  ring

/-! ###############################################################################
    ### The profile jets composed with the chart `W₀`.
    ############################################################################### -/

/-- **`profPd_composed` — the profile FIRST partial, chart-composed, jointly box-continuous.**  On the
    positive-time box `Icc (τ₀/2) T ×ˢ closedBall 0 R` (`0 < τ₀`), the first partial of the `C^∞` profile
    `prof τ w' = radialCutoff a b w' · heatParametrix 1 Θ* u* τ w'` evaluated at the chart image
    `W₀ p.2` is jointly continuous in `p`.  Route: `pd_mul` at the manifold point ⇒ four factors, each
    banked: `pd radialCutoff` (`contDiff_pd_inf` ∘ chart), `heatParametrix` value
    (`heatParametrix_value_jointContinuousOn_pos` ∘ chart-lift `Φ`), `radialCutoff` value, and
    `heatParametrix` first partial (`heatParametrix_pd_jointContinuousOn` ∘ `Φ`).  Carries `hΘc`/`hΘne`/
    `huc`/`hw` (coefficient regularity) + `hWc2` (chart `C²` on the ball).  NOT `a₁ = R/6`. -/
theorem profPd_composed (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (T R : ℝ) (c : Fin n)
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a',
      ContDiffAt ℝ 2 (fun y => uniformInverseChart g gi hChr hK 0 y a') z) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun w' => radialCutoff a b w'
              * heatParametrix 1 (vanVleck g)
                  (transportCoeff (transportOp (vanVleck g) g gi)) p.1 w') c
          (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  have ht1 : 0 < τ₀ / 2 := by linarith
  have hWcont := chart_continuousOn_of_c2 (uniformInverseChart g gi hChr hK 0) R hWc2
  have hW2 : ContinuousOn
      (fun p : ℝ × Point n => uniformInverseChart g gi hChr hK 0 p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    hWcont.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hΦcont := chartLift_continuousOn (uniformInverseChart g gi hChr hK 0) (τ₀ / 2) T R hWcont
  have hΦmaps := chartLift_mapsTo (uniformInverseChart g gi hChr hK 0) (τ₀ / 2) T R ht1
  -- the four banked factors
  have h_pdRC : ContinuousOn
      (fun p : ℝ × Point n => pd (radialCutoff a b) c (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    (contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) c).continuous.comp_continuousOn hW2
  have h_valHP : ContinuousOn
      (fun p : ℝ × Point n =>
        heatParametrix 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) p.1
          (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
    simpa [Function.comp] using
      (QIQTH.TransitionAnnulusCont.heatParametrix_value_jointContinuousOn_pos 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) hΘc hΘne huc).comp hΦcont hΦmaps
  have h_valRC : ContinuousOn
      (fun p : ℝ × Point n => radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    (radialCutoff_contDiff a b).continuous.comp_continuousOn hW2
  have h_pdHP : ContinuousOn
      (fun p : ℝ × Point n =>
        pd (heatParametrix 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) p.1) c
          (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
    simpa [Function.comp] using
      (QIQTH.ParametrixSpatialPartials.heatParametrix_pd_jointContinuousOn 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) c hw).comp hΦcont hΦmaps
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        pd (radialCutoff a b) c (uniformInverseChart g gi hChr hK 0 p.2)
            * heatParametrix 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) p.1
                (uniformInverseChart g gi hChr hK 0 p.2)
          + radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2)
            * pd (heatParametrix 1 (vanVleck g)
                  (transportCoeff (transportOp (vanVleck g) g gi)) p.1) c
                (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    (h_pdRC.mul h_valHP).add (h_valRC.mul h_pdHP)
  refine hClosed.congr (fun p hp => ?_)
  have hPdf : PdiffAt (radialCutoff a b) c (uniformInverseChart g gi hChr hK 0 p.2) :=
    QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ c _
      ((radialCutoff_contDiff a b).contDiffAt.differentiableAt (by simp))
  have hPdg : PdiffAt
      (heatParametrix 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) p.1) c
      (uniformInverseChart g gi hChr hK 0 p.2) :=
    QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ c _
      ((heatParametrix_contDiff_space 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) p.1 hw).contDiffAt.differentiableAt (by simp))
  exact pd_mul (radialCutoff a b)
    (heatParametrix 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) p.1)
    c (uniformInverseChart g gi hChr hK 0 p.2) hPdf hPdg

/-- **`profPdPd_composed` — the profile SECOND partial, chart-composed, jointly box-continuous.**  On
    the positive-time box, the mixed second partial `pd (fun w => pd (prof τ) c w) d` of the `C^∞`
    profile evaluated at `W₀ p.2` is jointly continuous.  Route: `pd_pd_mul` at the manifold point ⇒
    eight banked factors (`pd (pd radialCutoff)` / `radialCutoff` / `pd radialCutoff` composed with the
    chart, and `heatParametrix` value / first-`pd` / second-`pd` composed with the chart-lift `Φ`).
    Carries the same coefficient regularity + `hWc2` as `profPd_composed`.  NOT `a₁ = R/6`. -/
theorem profPdPd_composed (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (T R : ℝ) (c d : Fin n)
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a',
      ContDiffAt ℝ 2 (fun y => uniformInverseChart g gi hChr hK 0 y a') z) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun w => pd (fun w' => radialCutoff a b w'
              * heatParametrix 1 (vanVleck g)
                  (transportCoeff (transportOp (vanVleck g) g gi)) p.1 w') c w) d
          (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  have ht1 : 0 < τ₀ / 2 := by linarith
  have hWcont := chart_continuousOn_of_c2 (uniformInverseChart g gi hChr hK 0) R hWc2
  have hW2 : ContinuousOn
      (fun p : ℝ × Point n => uniformInverseChart g gi hChr hK 0 p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    hWcont.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hΦcont := chartLift_continuousOn (uniformInverseChart g gi hChr hK 0) (τ₀ / 2) T R hWcont
  have hΦmaps := chartLift_mapsTo (uniformInverseChart g gi hChr hK 0) (τ₀ / 2) T R ht1
  -- eight banked factors
  have h_pdpdRC : ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun w => pd (radialCutoff a b) c w) d (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    (contDiff_pd_inf _ (contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) c) d).continuous.comp_continuousOn hW2
  have h_valHP : ContinuousOn
      (fun p : ℝ × Point n =>
        heatParametrix 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) p.1
          (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
    simpa [Function.comp] using
      (QIQTH.TransitionAnnulusCont.heatParametrix_value_jointContinuousOn_pos 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) hΘc hΘne huc).comp hΦcont hΦmaps
  have h_pdRCc : ContinuousOn
      (fun p : ℝ × Point n => pd (radialCutoff a b) c (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    (contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) c).continuous.comp_continuousOn hW2
  have h_pdHPd : ContinuousOn
      (fun p : ℝ × Point n =>
        pd (heatParametrix 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) p.1) d
          (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
    simpa [Function.comp] using
      (QIQTH.ParametrixSpatialPartials.heatParametrix_pd_jointContinuousOn 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) d hw).comp hΦcont hΦmaps
  have h_pdRCd : ContinuousOn
      (fun p : ℝ × Point n => pd (radialCutoff a b) d (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    (contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) d).continuous.comp_continuousOn hW2
  have h_pdHPc : ContinuousOn
      (fun p : ℝ × Point n =>
        pd (heatParametrix 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) p.1) c
          (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
    simpa [Function.comp] using
      (QIQTH.ParametrixSpatialPartials.heatParametrix_pd_jointContinuousOn 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) c hw).comp hΦcont hΦmaps
  have h_valRC : ContinuousOn
      (fun p : ℝ × Point n => radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    (radialCutoff_contDiff a b).continuous.comp_continuousOn hW2
  have h_pdpdHP : ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun w => pd (heatParametrix 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) p.1) c w) d
          (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
    simpa [Function.comp] using
      (QIQTH.ParametrixSpatialPartials.heatParametrix_pd_pd_jointContinuousOn 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) d c hw).comp hΦcont hΦmaps
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun w => pd (radialCutoff a b) c w) d (uniformInverseChart g gi hChr hK 0 p.2)
            * heatParametrix 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) p.1
                (uniformInverseChart g gi hChr hK 0 p.2)
          + pd (radialCutoff a b) c (uniformInverseChart g gi hChr hK 0 p.2)
            * pd (heatParametrix 1 (vanVleck g)
                  (transportCoeff (transportOp (vanVleck g) g gi)) p.1) d
                (uniformInverseChart g gi hChr hK 0 p.2)
          + pd (radialCutoff a b) d (uniformInverseChart g gi hChr hK 0 p.2)
            * pd (heatParametrix 1 (vanVleck g)
                  (transportCoeff (transportOp (vanVleck g) g gi)) p.1) c
                (uniformInverseChart g gi hChr hK 0 p.2)
          + radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2)
            * pd (fun w => pd (heatParametrix 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) p.1) c w) d
                (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    (((h_pdpdRC.mul h_valHP).add (h_pdRCc.mul h_pdHPd)).add (h_pdRCd.mul h_pdHPc)).add
      (h_valRC.mul h_pdpdHP)
  refine hClosed.congr (fun p hp => ?_)
  exact pd_pd_mul (radialCutoff a b)
    (heatParametrix 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) p.1)
    (radialCutoff_contDiff a b)
    (heatParametrix_contDiff_space 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) p.1 hw)
    c d (uniformInverseChart g gi hChr hK 0 p.2)

/-! ###############################################################################
    ### ★★★ `hParamDeriv_grounded` — the parametrix `τ`-derivative box carrier.
    ############################################################################### -/

/-- **★★★ `hParamDeriv_grounded`.**  On the positive-time box `Icc (τ₀/2) T ×ˢ closedBall 0 R`
    (`0 < τ₀`), the `hParamDeriv` box carrier of `LeafBoxSplice.leafBox_of_boundary` — the joint
    continuity of the chart-composed parametrix `τ`-derivative slice
      `p ↦ deriv (fun u => radialCutoff a b (W₀ p.2) · heatParametrix 1 Θ* u* u (W₀ p.2)) p.1` —
    is GROUNDED: the `τ`-independent `radialCutoff` factor pulls out (`deriv_const_mul_field`), leaving
    the banked `ChartComposedHeatOp.chartComposed_dtau_jointContinuousOn` times the continuous cutoff
    factor.  Carries only `hΘc`/`hΘne`/`huc` + `hWc2`; none the conclusion.  NOT `a₁ = R/6`. -/
theorem hParamDeriv_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (T R : ℝ)
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a',
      ContDiffAt ℝ 2 (fun y => uniformInverseChart g gi hChr hK 0 y a') z) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        deriv (fun u => radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2)
            * heatParametrix 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) u
                (uniformInverseChart g gi hChr hK 0 p.2)) p.1)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  have ht1 : 0 < τ₀ / 2 := by linarith
  have hWcont := chart_continuousOn_of_c2 (uniformInverseChart g gi hChr hK 0) R hWc2
  have hW2 : ContinuousOn
      (fun p : ℝ × Point n => uniformInverseChart g gi hChr hK 0 p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    hWcont.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hRC : ContinuousOn
      (fun p : ℝ × Point n => radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2))
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    (radialCutoff_contDiff a b).continuous.comp_continuousOn hW2
  have hEq :
      (fun p : ℝ × Point n =>
        deriv (fun u => radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2)
            * heatParametrix 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) u
                (uniformInverseChart g gi hChr hK 0 p.2)) p.1)
      = fun p : ℝ × Point n =>
          radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2)
            * deriv (fun s => heatParametrix 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) s
                (uniformInverseChart g gi hChr hK 0 p.2)) p.1 := by
    funext p; rw [deriv_const_mul_field]
  rw [hEq]
  exact hRC.mul
    (chartComposed_dtau_jointContinuousOn 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) (uniformInverseChart g gi hChr hK 0)
      (τ₀ / 2) T R ht1 hΘc hΘne huc hWc2)

/-! ###############################################################################
    ### ★★★ `hComposite1_grounded` — the composite FIRST spatial partial box carrier.
    ############################################################################### -/

/-- **★★★ `hComposite1_grounded`.**  On the positive-time box (`0 < τ₀`), the `hComposite1` box carrier
    (per `k`) — the joint continuity of the `C^∞` chart-composite's FIRST spatial partial
      `p ↦ pd (fun x' => globalCutoffParametrixWitnessN 1 Θ* u* a b (uniformInverseChart …) p.1 x' 0) k p.2` —
    is GROUNDED.  Route: def-unfold to `prof ∘ W₀`, `pd_comp` at the `C^∞` profile ⇒
    `∑ c, (pd prof c ∘ W₀)·(pd (W₀·c) k)`; the profile jet is `profPd_composed`, the chart first jet is
    `hWc1cont`.  Carries banks + `hWc1cont` + coefficient regularity + `hWc2`; none the conclusion.
    NOT `a₁ = R/6`. -/
theorem hComposite1_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (T R : ℝ) (k : Fin n)
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a',
      ContDiffAt ℝ 2 (fun y => uniformInverseChart g gi hChr hK 0 y a') z)
    (hWc1cont : ∀ a' i, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => uniformInverseChart g gi hChr hK 0 y a') i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hChr hK) p.1 x' 0) k p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        ∑ c, pd (fun w' => radialCutoff a b w'
                * heatParametrix 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) p.1 w') c
              (uniformInverseChart g gi hChr hK 0 p.2)
            * pd (fun y => uniformInverseChart g gi hChr hK 0 y c) k p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
    continuousOn_finsetSum _ (fun c _ =>
      (profPd_composed g gi hChr hK a b hτ₀ T R c hΘc hΘne huc hw hWc2).mul (hWc1cont c k))
  refine hClosed.congr (fun p hp => ?_)
  simp only [globalCutoffParametrixWitnessN]
  have hProf : DifferentiableAt ℝ
      (fun w' => radialCutoff a b w'
        * heatParametrix 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) p.1 w')
      (uniformInverseChart g gi hChr hK 0 p.2) :=
    ((radialCutoff_contDiff a b).mul
      (heatParametrix_contDiff_space 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) p.1 hw)).contDiffAt.differentiableAt (by simp)
  have hWdiff : DifferentiableAt ℝ (uniformInverseChart g gi hChr hK 0) p.2 :=
    differentiableAt_pi.mpr (fun a' => (hWc2 p.2 hp.2 a').differentiableAt (by norm_num))
  exact pd_comp
    (fun w' => radialCutoff a b w'
      * heatParametrix 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) p.1 w')
    (uniformInverseChart g gi hChr hK 0) k p.2 hProf hWdiff

/-! ###############################################################################
    ### ★★★ `hComposite2_grounded` — the composite SECOND spatial partial box carrier.
    ############################################################################### -/

/-- **★★★ `hComposite2_grounded`.**  On the positive-time box (`0 < τ₀`), the `hComposite2` box carrier
    (per `i j`) — the joint continuity of the `C^∞` chart-composite's SECOND spatial partial
      `p ↦ pd (fun y => pd (fun x' => globalCutoffParametrixWitnessN … p.1 x' 0) j y) i p.2` —
    is REDUCED honestly.  Route: def-unfold to `prof ∘ W₀`, `pd_pd_comp_local` at the `C^∞` profile ⇒
      `∑ a (∑ b (pd² prof ∘ W₀)·(pd W₀))·(pd W₀) + ∑ a (pd prof ∘ W₀)·(pd² W₀)`,
    with `pd² prof ∘ W₀` = `profPdPd_composed`, `pd prof ∘ W₀` = `profPd_composed`, `pd W₀` =
    `hWc1cont`, and — in the second block — `pd² W₀` = the CHART HESSIAN carry `hWc2cont`.
    ⚠ THE THREAD CONVERGENCE: `hWc2cont` (`pd (fun y => pd (W₀·a) j y) i`) is EXACTLY the queued
    2nd-order chart-jet atom of the C₂ / `hcont2` derivative-sup chain (`BaseSlotAmpDeriv`, the J3
    base-point-regularity blocker).  The htermBox splice and the derivative-sup chain CONVERGE here; no
    fresh wall.  Carries banks + `hWc1cont` + `hWc2cont` + coefficient regularity + `hWc2`.
    NOT `a₁ = R/6`. -/
theorem hComposite2_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (T R : ℝ) (i j : Fin n)
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a',
      ContDiffAt ℝ 2 (fun y => uniformInverseChart g gi hChr hK 0 y a') z)
    (hWc1cont : ∀ a' i, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => uniformInverseChart g gi hChr hK 0 y a') i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hWc2cont : ∀ a' i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => uniformInverseChart g gi hChr hK 0 z a') j y) i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y : Point n =>
              pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) a b
                    (uniformInverseChart g gi hChr hK) p.1 x' 0) j y) i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        (∑ a', (∑ b', pd (fun w => pd (fun w' => radialCutoff a b w'
                    * heatParametrix 1 (vanVleck g)
                        (transportCoeff (transportOp (vanVleck g) g gi)) p.1 w') a' w) b'
                  (uniformInverseChart g gi hChr hK 0 p.2)
                * pd (fun y => uniformInverseChart g gi hChr hK 0 y b') i p.2)
              * pd (fun y => uniformInverseChart g gi hChr hK 0 y a') j p.2)
          + ∑ a', pd (fun w' => radialCutoff a b w'
                  * heatParametrix 1 (vanVleck g)
                      (transportCoeff (transportOp (vanVleck g) g gi)) p.1 w') a'
                (uniformInverseChart g gi hChr hK 0 p.2)
              * pd (fun y => pd (fun z => uniformInverseChart g gi hChr hK 0 z a') j y) i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
    refine (continuousOn_finsetSum _ (fun a' _ => ?_)).add
      (continuousOn_finsetSum _ (fun a' _ =>
        (profPd_composed g gi hChr hK a b hτ₀ T R a' hΘc hΘne huc hw hWc2).mul (hWc2cont a' i j)))
    exact (continuousOn_finsetSum _ (fun b' _ =>
      (profPdPd_composed g gi hChr hK a b hτ₀ T R a' b' hΘc hΘne huc hw hWc2).mul
        (hWc1cont b' i))).mul (hWc1cont a' j)
  refine hClosed.congr (fun p hp => ?_)
  simp only [globalCutoffParametrixWitnessN]
  have hProf : ContDiffAt ℝ 2
      (fun w' => radialCutoff a b w'
        * heatParametrix 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) p.1 w')
      (uniformInverseChart g gi hChr hK 0 p.2) :=
    ((radialCutoff_contDiff a b).mul
      (heatParametrix_contDiff_space 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) p.1 hw)).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hWc2z : ∀ a', ContDiffAt ℝ 2 (fun y => uniformInverseChart g gi hChr hK 0 y a') p.2 :=
    fun a' => hWc2 p.2 hp.2 a'
  exact pd_pd_comp_local
    (fun w' => radialCutoff a b w'
      * heatParametrix 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) p.1 w')
    (uniformInverseChart g gi hChr hK 0) i j p.2 hProf hWc2z

/-! ###############################################################################
    ### ★★★ `smoothCarriers_family` — the three `∀ τ₀ ∈ Ioc 0 T, ∀ R` families.
    ############################################################################### -/

/-- **★★★ `smoothCarriers_family`.**  The three `hSmooth` box carriers as `∀ τ₀ ∈ Ioc 0 T, ∀ R`
    families in the EXACT shapes `LeafBoxSplice.hIterBase_final` consumes for
    `hParamDeriv`/`hComposite1`/`hComposite2`, produced by the per-box grounded theorems at each
    `(τ₀, R)` (with `τ₀ ∈ Ioc 0 T ⇒ 0 < τ₀`).  All three stand on the geometry/coefficient regularity
    (`hΘc`/`hΘne`/`huc`/`hw`) + the chart-jet carries: `hWc2fam` (chart `C²` on every ball), `hWc1fam`
    (chart FIRST jet joint continuity per box), and `hWc2fam` (the W-HESSIAN — the queued 2nd-order jet
    atom, feeding ONLY `hComposite2`).  ⚠ NOT `a₁ = R/6`. -/
theorem smoothCarriers_family (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b T : ℝ)
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hWc2fam : ∀ R : ℝ, ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a',
      ContDiffAt ℝ 2 (fun y => uniformInverseChart g gi hChr hK 0 y a') z)
    (hWc1fam : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ a' i, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => uniformInverseChart g gi hChr hK 0 y a') i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hWc2contfam : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ a' i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => uniformInverseChart g gi hChr hK 0 z a') j y) i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    (∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ContinuousOn
        (fun p : ℝ × Point n =>
          deriv (fun u => radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2)
              * heatParametrix 1 (vanVleck g)
                  (transportCoeff (transportOp (vanVleck g) g gi)) u
                  (uniformInverseChart g gi hChr hK 0 p.2)) p.1)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
      ∧ (∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k, ContinuousOn
        (fun p : ℝ × Point n =>
          pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) a b
                (uniformInverseChart g gi hChr hK) p.1 x' 0) k p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
      ∧ (∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ i j, ContinuousOn
        (fun p : ℝ × Point n =>
          pd (fun y : Point n =>
                pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
                      (transportCoeff (transportOp (vanVleck g) g gi)) a b
                      (uniformInverseChart g gi hChr hK) p.1 x' 0) j y) i p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) := by
  refine ⟨fun τ₀ hτ₀ R => ?_, fun τ₀ hτ₀ R k => ?_, fun τ₀ hτ₀ R i j => ?_⟩
  · exact hParamDeriv_grounded g gi hChr hK a b hτ₀.1 T R hΘc hΘne huc (hWc2fam R)
  · exact hComposite1_grounded g gi hChr hK a b hτ₀.1 T R k hΘc hΘne huc hw (hWc2fam R)
      (hWc1fam τ₀ hτ₀ R)
  · exact hComposite2_grounded g gi hChr hK a b hτ₀.1 T R i j hΘc hΘne huc hw (hWc2fam R)
      (hWc1fam τ₀ hτ₀ R) (hWc2contfam τ₀ hτ₀ R)

/-! ###############################################################################
    ### THE SMOOTH LEDGER — the surviving surface after the `hSmooth` grounding.
    ############################################################################### -/

/-- **`smooth_ledger`.**  THE ENUMERATED SURVIVING SURFACE after the J4-478 `hSmooth` grounding.  A
    genuine conjunction (non-vacuous plumbing witness); each conjunct SATISFIABLE, none the conclusion.

    THE SMOOTH LEDGER — the state of the `LeafBoxSplice` `hSmooth` group after `smoothCarriers_family`:
      1. `hParam`   — the parametrix `τ`-derivative slice carrier: FULLY GROUNDED
         (`hParamDeriv_grounded`) to the banked chart-composed `∂_τ` parametrix
         (`ChartComposedHeatOp.chartComposed_dtau_jointContinuousOn`) times the continuous cutoff.
      2. `hComp1`   — the composite FIRST spatial partial carrier: FULLY GROUNDED
         (`hComposite1_grounded`) via `pd_comp` at the `C^∞` profile ⇒ `profPd_composed` (manifold
         product rule, four banked parametrix/cutoff factors) + the chart first jet `hWc1cont`.
      3. `hComp2`   — the composite SECOND spatial partial carrier: REDUCED (`hComposite2_grounded`)
         via `pd_pd_comp_local` at the `C^∞` profile ⇒ `profPdPd_composed` (`pd_pd_mul`, eight banked
         factors) + the chart first jet `hWc1cont` + THE CHART HESSIAN `hWc2cont`.
      4. `hCoeff`   — the coefficient regularity `hΘc`/`hΘne`/`huc`/`hw` + the chart `C²`-on-ball carry
         `hWc2` (van-Vleck / transport / cutoff smoothness banks + the chart's own `C²`).

    ★★ THE THREAD CONVERGENCE.  The `hComp2` residual `hWc2cont` (chart Hessian
    `pd (fun y => pd (W₀·a) j y) i`) is the SAME 2nd-order chart-jet atom the queued C₂ / `hcont2`
    derivative-sup chain needs (`BaseSlotAmpDeriv`, the J3 base-point-regularity blocker
    `FlowJointRegularity`/`BasepointFDeriv`).  The htermBox splice and the derivative-sup chain converge
    on ONE geometric analytic wall — the second field-jet of the uniform inverse chart.  No fresh wall.

    DISCHARGED (NOT in this ledger): the def-unfold `globalCutoffParametrixWitnessN → prof ∘ W₀`, the
    chain rules `pd_comp`/`pd_pd_comp_local`, the manifold product rules `pd_mul`/`pd_pd_mul`, and every
    banked parametrix jet joint continuity.  ⚠ NOT `a₁ = R/6`; CONDITIONAL on exactly this surface. -/
def smooth_ledger (hParam hComp1 hComp2 hCoeff : Prop) : Prop :=
  hParam ∧ hComp1 ∧ hComp2 ∧ hCoeff

/-- The smooth ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem smooth_ledger_intro {hParam hComp1 hComp2 hCoeff : Prop}
    (h1 : hParam) (h2 : hComp1) (h3 : hComp2) (h4 : hCoeff) :
    smooth_ledger hParam hComp1 hComp2 hCoeff :=
  ⟨h1, h2, h3, h4⟩

end QIQTH.SmoothCarrierGrounding

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.SmoothCarrierGrounding.pd_pd_mul
#print axioms QIQTH.SmoothCarrierGrounding.profPd_composed
#print axioms QIQTH.SmoothCarrierGrounding.profPdPd_composed
#print axioms QIQTH.SmoothCarrierGrounding.hParamDeriv_grounded
#print axioms QIQTH.SmoothCarrierGrounding.hComposite1_grounded
#print axioms QIQTH.SmoothCarrierGrounding.hComposite2_grounded
#print axioms QIQTH.SmoothCarrierGrounding.smoothCarriers_family
#print axioms QIQTH.SmoothCarrierGrounding.smooth_ledger_intro
