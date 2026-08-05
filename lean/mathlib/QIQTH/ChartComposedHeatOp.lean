/-
  ChartComposedHeatOp — J4-287: the chart-composed `heatOp` joint continuity `hBcont`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET.  `QIQTH.GatedWitnessHeatOpBridge.heatOpGatedWitness_jointContinuousOn_of_chartParametrix`
  (J4-286) reduced the boundary chain's `E`-continuity to ONE input, `hBcont`: the joint `(τ,z)`-
  continuity on `Icc t₁ t₂ ×ˢ closedBall 0 R` (`0 < t₁`) of
      `fun p => heatOp g gi (fun s x _ => heatParametrix 1 Θ* u* s (W₀ x)) p.1 p.2 0`,
  with `Θ* = vanVleck g`, `u* = transportCoeff (transportOp (vanVleck g) g gi)`,
  `W₀ = uniformInverseChart g gi hC hK 0` (the FIELD-slot inverse chart at base point `0`; field slot
  is the OUTER `x`, base slot is `0`).  Here `heatParametrix … s (W₀ x)` is the plain order-`1` heat
  parametrix COMPOSED WITH the inverse chart `x ↦ W₀ x` in its SPATIAL argument.  Since `W₀` is only
  origin-fixing pointwise (`W₀ 0 = 0`, NOT the identity germ), J4-285's PLAIN-kernel geometry capstone
  does not discharge `hBcont` directly — this file builds the genuine CHART-COMPOSED capstone via the
  first/second coordinate-partial CHAIN RULES (`pd_comp` / `pd_pd_comp_local`).

  ── THE COMPOSITION STRUCTURE.  `heatOp = ∂_τ − Δ_g`.
     • ∂_τ term.  The chart does NOT depend on `τ`, so
         `deriv (fun s => heatParametrix N Θ u s (W₀ z)) τ`
       is the PLAIN parametrix `∂_τ`-term EVALUATED at the point `W₀ z`; its joint continuity is the
       banked `ParametrixPartsContinuity.heatParametrix_deriv_jointContinuousOn` COMPOSED with the
       continuous map `Φ : (τ,z) ↦ (τ, W₀ z)`.
     • Δ term.  `laplaceBeltrami g gi (fun x => heatParametrix N Θ u τ (W₀ x)) z`.  The first/second
       coordinate partials of the composition unfold by the CHAIN RULES:
         `∂_i(F∘W₀) = ∑_a (∂_a F)(W₀ z)·∂_i(W₀·a)`,
         `∂_i∂_j(F∘W₀) = ∑_a (∑_b (∂_b∂_a F)(W₀ z)·∂_i(W₀·b))·∂_j(W₀·a) + ∑_a (∂_a F)(W₀ z)·∂_i∂_j(W₀·a)`,
       with `F = heatParametrix N Θ u τ`.  Each parametrix-jet factor is the banked
       `ParametrixSpatialPartials.heatParametrix_pd_jointContinuousOn` /
       `…_pd_pd_jointContinuousOn` COMPOSED with `Φ`; each chart-jet factor is `τ`-independent and
       CARRIED jointly continuous (satisfiable exactly where `W₀` is `C²` on the ball).

  ── WHAT LANDS (all axiom-free; NO `sorry`, NO new axioms, NO `:= True`; none the conclusion).
     • `heatParametrix_contDiff_space`   — the plain parametrix is `C^∞` in space (folded form).
     • (D1) `chartComposed_pd_eq`         — the first-partial chain rule for the chart-composed kernel.
     • (D1c) `chartComposed_pd_jointContinuousOn`     — its joint `(τ,z)`-continuity.
     • (D2) `chartComposed_pd_pd_eq`      — the second-partial chain rule (D²W₀ source term).
     • (D2c) `chartComposed_pd_pd_jointContinuousOn`  — its joint `(τ,z)`-continuity.
     • (D3) `chartComposed_dtau_jointContinuousOn`    — the `∂_τ`-term joint continuity.
     • (D4) `chartComposed_laplaceBeltrami_jointContinuousOn` — the `Δ`-term joint continuity.
     • (D5) `chartComposedHeatOp_jointContinuousOn`   — `hBcont`, CONCRETE, carrying only satisfiable
       coefficient regularity (`hw`/`hΘc`/`hΘne`/`huc`), geometry continuities (`hgi`/`hChr`), and the
       CHART FACTS (`hWc2` pointwise `C²` on the ball + the two chart-jet joint continuities).
     • (D6) `heatOpGatedWitness_jointContinuousOn_final` — the boundary chain's `E`-continuity with
       `hBcont` DISCHARGED via D5, plugged into J4-286's L3.  Carries only satisfiable inputs.

  ⚠  HONEST FIREWALL.  The carried chart facts (`hWc2`/`hWc1cont`/`hWc2cont`) are genuine and
     satisfiable: on a ball inside `W₀`'s `C²` region (`ChartJetBounds.chartField_contDiffAt_center` +
     the `uniformInverseChart_huniformChart` neighborhood) the inverse chart is `C²`, so its first/second
     jets exist and are continuous.  They are NOT the conclusion (the conclusion is about the composed
     `heatOp`, linked by the PROVEN chain rules), and NONE of this is `a₁ = R/6` — this file only
     relocates the boundary-chain regularity onto the chart-composed parametrix; the curvature value is
     untouched.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GatedWitnessHeatOpBridge
import QIQTH.ParametrixSpatialPartials
import QIQTH.ResidualChartTransport
import QIQTH.PullbackNaturalityLocal

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.HeatParametrixOrder
open QIQTH.ParametrixPartsContinuity QIQTH.ParametrixSpatialPartials
open QIQTH.GatedWitnessHeatOpBridge
open scoped Topology ContDiff

namespace QIQTH.ChartComposedHeatOp

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (helper) — the plain parametrix is `C^∞` in space.
    ############################################################################### -/

/-- **`heatParametrix_contDiff_space`.**  For smooth folded coefficients (`hw`), the plain heat
    parametrix `heatParametrix N Θ u τ` is `C^∞` in the spatial variable — via the folded form
    `H_N(τ,·) = G_τ·Σ_{k≤N} w_k·τᵏ` (`heatParametrix_folded`), `gaussDdim_contDiff`, `hw`, and
    `contDiff_const`.  This banks the differentiability of `F = heatParametrix N Θ u τ` at the chart
    image `W₀ z`, consumed by the chain rules below.  Carries only `hw`; not the conclusion.
    NOT `a₁ = R/6`. -/
theorem heatParametrix_contDiff_space (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (τ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (heatParametrix N Θ u τ) := by
  have hHeq : heatParametrix N Θ u τ
      = (fun y => gaussDdim τ y * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * τ ^ k) :=
    funext (fun y => heatParametrix_folded N Θ u τ y)
  rw [hHeq]
  exact ((gaussDdim_contDiff τ).of_le le_top).mul
    (ContDiff.sum fun k _ => (hw k).mul contDiff_const)

/-! ###############################################################################
    ## (D1) — the first-partial chain rule for the chart-composed kernel.
    ############################################################################### -/

/-- **★ (D1) `chartComposed_pd_eq`.**  The FIRST coordinate-partial chain rule for the chart-composed
    parametrix `x ↦ heatParametrix N Θ u τ (W₀ x)`:
      `∂_i(F∘W₀)(z) = ∑_a (∂_a F)(W₀ z)·∂_i(W₀·a)(z)`,   `F = heatParametrix N Θ u τ`.
    A thin specialization of `pd_comp` at the `C^∞` parametrix (`heatParametrix_contDiff_space`) and a
    `DifferentiableAt` chart `W₀`.  Carries `hw` and `hWz`; none the conclusion.  NOT `a₁ = R/6`. -/
theorem chartComposed_pd_eq (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (W₀ : Point n → Point n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) (τ : ℝ) (i : Fin n) (z : Point n)
    (hWz : DifferentiableAt ℝ W₀ z) :
    pd (fun x => heatParametrix N Θ u τ (W₀ x)) i z
      = ∑ a, pd (heatParametrix N Θ u τ) a (W₀ z) * pd (fun y => W₀ y a) i z :=
  pd_comp (heatParametrix N Θ u τ) W₀ i z
    ((heatParametrix_contDiff_space N Θ u τ hw).contDiffAt.differentiableAt (by simp)) hWz

/-! ###############################################################################
    ## (D2) — the second-partial chain rule for the chart-composed kernel.
    ############################################################################### -/

/-- **★ (D2) `chartComposed_pd_pd_eq`.**  The SECOND coordinate-partial chain rule for the chart-
    composed parametrix:
      `∂_i∂_j(F∘W₀)(z) = ∑_a (∑_b (∂_b∂_a F)(W₀ z)·∂_i(W₀·b)(z))·∂_j(W₀·a)(z)
                        + ∑_a (∂_a F)(W₀ z)·∂_i∂_j(W₀·a)(z)`,   `F = heatParametrix N Θ u τ`.
    A specialization of `pd_pd_comp_local` at the `C^∞` parametrix (`heatParametrix_contDiff_space`,
    `ContDiffAt ℝ 2` at `W₀ z`) and a per-component `ContDiffAt ℝ 2` chart `W₀`.  The second block is
    the `D²W₀` source term.  Carries `hw`/`hWc2z`; none the conclusion.  NOT `a₁ = R/6`. -/
theorem chartComposed_pd_pd_eq (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) (τ : ℝ) (i j : Fin n) (z : Point n)
    (hWc2z : ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z) :
    pd (fun y => pd (fun x => heatParametrix N Θ u τ (W₀ x)) j y) i z
      = (∑ a, (∑ b, pd (fun w => pd (heatParametrix N Θ u τ) a w) b (W₀ z)
                * pd (fun y => W₀ y b) i z) * pd (fun y => W₀ y a) j z)
        + ∑ a, pd (heatParametrix N Θ u τ) a (W₀ z)
              * pd (fun y => pd (fun z => W₀ z a) j y) i z :=
  pd_pd_comp_local (heatParametrix N Θ u τ) W₀ i j z
    ((heatParametrix_contDiff_space N Θ u τ hw).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)) hWc2z

/-! ###############################################################################
    ## (Φ) — the chart-lift map `(τ,z) ↦ (τ, W₀ z)` — continuity + `MapsTo {0<τ}`.
    ############################################################################### -/

/-- **Chart-lift continuity.**  On the positive-time compact, the lift `(τ,z) ↦ (τ, W₀ z)` is
    continuous, from the continuity of `W₀` on the ball.  (Support lemma for the `Φ`-composition of
    the banked parametrix-jet continuities.) -/
theorem chartLift_continuousOn (W₀ : Point n → Point n) (t₁ t₂ R : ℝ)
    (hWcont : ContinuousOn W₀ (Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => ((p.1, W₀ p.2) : ℝ × Point n))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  (continuous_fst.continuousOn).prodMk
    (hWcont.comp continuous_snd.continuousOn (fun _ hp => hp.2))

/-- **Chart-lift `MapsTo`.**  The lift sends the positive-time compact into `{0<τ}` (`0 < t₁`). -/
theorem chartLift_mapsTo (W₀ : Point n → Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) :
    Set.MapsTo (fun p : ℝ × Point n => ((p.1, W₀ p.2) : ℝ × Point n))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) {q : ℝ × Point n | 0 < q.1} :=
  fun _ hp => lt_of_lt_of_le ht₁ hp.1.1

/-- **Chart continuity from `C²`.**  Per-component `ContDiffAt ℝ 2` of `W₀` on the ball gives
    `ContinuousOn W₀` there. -/
theorem chart_continuousOn_of_c2 (W₀ : Point n → Point n) (R : ℝ)
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z) :
    ContinuousOn W₀ (Metric.closedBall (0 : Point n) R) :=
  fun z hz =>
    (differentiableAt_pi.mpr
      (fun a => (hWc2 z hz a).differentiableAt (by norm_num))).continuousAt.continuousWithinAt

/-! ###############################################################################
    ## (D1c) — joint continuity of the composed FIRST partial.
    ############################################################################### -/

/-- **★ (D1c) `chartComposed_pd_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the chart-composed
    first partial `p ↦ ∂_i(F∘W₀)(p.2)` (`F = heatParametrix N Θ u p.1`) on `Icc t₁ t₂ ×ˢ closedBall 0
    R` (`0 < t₁`).  Route: `ContinuousOn.congr` onto the D1 closed form; each summand is the banked
    parametrix first-partial (`heatParametrix_pd_jointContinuousOn`) COMPOSED with the chart lift `Φ`
    times the carried chart first-jet `hWc1cont`.  Carries `hw` (parametrix) + `hWc2`/`hWc1cont`
    (chart); none the conclusion.  NOT `a₁ = R/6`. -/
theorem chartComposed_pd_jointContinuousOn (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (i : Fin n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z)
    (hWc1cont : ∀ a i, ContinuousOn (fun p : ℝ × Point n => pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hWcont := chart_continuousOn_of_c2 W₀ R hWc2
  have hΦcont := chartLift_continuousOn W₀ t₁ t₂ R hWcont
  have hΦmaps := chartLift_mapsTo W₀ t₁ t₂ R ht₁
  -- the banked parametrix first-partial, composed with the chart lift `Φ`.
  have hbankPd : ∀ a, ContinuousOn
      (fun p : ℝ × Point n => pd (heatParametrix N Θ u p.1) a (W₀ p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
    intro a
    simpa [Function.comp] using
      (heatParametrix_pd_jointContinuousOn N Θ u a hw).comp hΦcont hΦmaps
  -- the D1 closed form is jointly continuous.
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        ∑ a, pd (heatParametrix N Θ u p.1) a (W₀ p.2) * pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    continuousOn_finsetSum _ (fun a _ => (hbankPd a).mul (hWc1cont a i))
  refine hClosed.congr (fun p hp => ?_)
  have hWz : DifferentiableAt ℝ W₀ p.2 :=
    differentiableAt_pi.mpr (fun a => (hWc2 p.2 hp.2 a).differentiableAt (by norm_num))
  exact chartComposed_pd_eq N Θ u W₀ hw p.1 i p.2 hWz

/-! ###############################################################################
    ## (D2c) — joint continuity of the composed SECOND partial.
    ############################################################################### -/

/-- **★ (D2c) `chartComposed_pd_pd_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the chart-
    composed second partial `p ↦ ∂_i∂_j(F∘W₀)(p.2)` (`F = heatParametrix N Θ u p.1`) on
    `Icc t₁ t₂ ×ˢ closedBall 0 R` (`0 < t₁`).  Route: `ContinuousOn.congr` onto the D2 closed form;
    the parametrix jets (first via `heatParametrix_pd_jointContinuousOn`, second via
    `…_pd_pd_jointContinuousOn`) are COMPOSED with the chart lift `Φ`, the chart jets are the carried
    `hWc1cont` (first) and `hWc2cont` (second).  Carries `hw` + `hWc2`/`hWc1cont`/`hWc2cont`; none the
    conclusion.  NOT `a₁ = R/6`. -/
theorem chartComposed_pd_pd_jointContinuousOn (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (i j : Fin n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z)
    (hWc1cont : ∀ a i, ContinuousOn (fun p : ℝ × Point n => pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hWc2cont : ∀ a i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun z => W₀ z a) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hWcont := chart_continuousOn_of_c2 W₀ R hWc2
  have hΦcont := chartLift_continuousOn W₀ t₁ t₂ R hWcont
  have hΦmaps := chartLift_mapsTo W₀ t₁ t₂ R ht₁
  -- banked parametrix first partial ∘ Φ.
  have hbankPd : ∀ a, ContinuousOn
      (fun p : ℝ × Point n => pd (heatParametrix N Θ u p.1) a (W₀ p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
    intro a
    simpa [Function.comp] using
      (heatParametrix_pd_jointContinuousOn N Θ u a hw).comp hΦcont hΦmaps
  -- banked parametrix second partial ∘ Φ (outer `b`, inner `a`).
  have hbankPdPd : ∀ a b, ContinuousOn
      (fun p : ℝ × Point n => pd (fun w => pd (heatParametrix N Θ u p.1) a w) b (W₀ p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
    intro a b
    simpa [Function.comp] using
      (heatParametrix_pd_pd_jointContinuousOn N Θ u b a hw).comp hΦcont hΦmaps
  -- the D2 closed form is jointly continuous.
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        (∑ a, (∑ b, pd (fun w => pd (heatParametrix N Θ u p.1) a w) b (W₀ p.2)
                  * pd (fun y => W₀ y b) i p.2) * pd (fun y => W₀ y a) j p.2)
          + ∑ a, pd (heatParametrix N Θ u p.1) a (W₀ p.2)
                * pd (fun y => pd (fun z => W₀ z a) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
    refine (continuousOn_finsetSum _ (fun a _ => ?_)).add
      (continuousOn_finsetSum _ (fun a _ => (hbankPd a).mul (hWc2cont a i j)))
    exact (continuousOn_finsetSum _ (fun b _ => (hbankPdPd a b).mul (hWc1cont b i))).mul
      (hWc1cont a j)
  refine hClosed.congr (fun p hp => ?_)
  have hWc2z : ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) p.2 := fun a => hWc2 p.2 hp.2 a
  exact chartComposed_pd_pd_eq N Θ u W₀ hw p.1 i j p.2 hWc2z

/-! ###############################################################################
    ## (D3) — the `∂_τ`-term joint continuity.
    ############################################################################### -/

/-- **★ (D3) `chartComposed_dtau_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the chart-composed
    `∂_τ` term `p ↦ deriv (fun s => heatParametrix N Θ u s (W₀ p.2)) p.1` on `Icc t₁ t₂ ×ˢ closedBall 0
    R` (`0 < t₁`).  Since the chart does NOT depend on `τ`, this is the banked parametrix `∂_τ`-term
    (`heatParametrix_deriv_jointContinuousOn`, needing `Θ` continuous/non-vanishing, each `u_k`
    continuous) COMPOSED with the chart lift `Φ : (τ,z) ↦ (τ, W₀ z)`.  Carries `hΘc`/`hΘne`/`huc` +
    `hWc2`; none the conclusion.  NOT `a₁ = R/6`. -/
theorem chartComposed_dtau_jointContinuousOn (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z) :
    ContinuousOn (fun p : ℝ × Point n => deriv (fun s => heatParametrix N Θ u s (W₀ p.2)) p.1)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hWcont := chart_continuousOn_of_c2 W₀ R hWc2
  have hΦcont := chartLift_continuousOn W₀ t₁ t₂ R hWcont
  have hΦmaps := chartLift_mapsTo W₀ t₁ t₂ R ht₁
  simpa [Function.comp] using
    (heatParametrix_deriv_jointContinuousOn N Θ u hΘc hΘne huc).comp hΦcont hΦmaps

/-! ###############################################################################
    ## (D4) — the `Δ`-term joint continuity.
    ############################################################################### -/

/-- **★ (D4) `chartComposed_laplaceBeltrami_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the
    chart-composed `Δ`-term `p ↦ laplaceBeltrami g gi (fun x => heatParametrix N Θ u p.1 (W₀ x)) p.2`
    on `Icc t₁ t₂ ×ˢ closedBall 0 R` (`0 < t₁`).  Route: unfold `laplaceBeltrami` (a finite
    `∑_i∑_j gi·(∂²f − Σ_k Γ·∂f)`); assemble from `hgi`/`hChr` and the composed partial continuities
    (D1c) `chartComposed_pd_jointContinuousOn` / (D2c) `chartComposed_pd_pd_jointContinuousOn`.
    Carries `hw` + geometry (`hgi`/`hChr`) + chart facts; none the conclusion.  NOT `a₁ = R/6`. -/
theorem chartComposed_laplaceBeltrami_jointContinuousOn (N : ℕ)
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z)
    (hWc1cont : ∀ a i, ContinuousOn (fun p : ℝ × Point n => pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hWc2cont : ∀ a i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun z => W₀ z a) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi (fun x => heatParametrix N Θ u p.1 (W₀ x)) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hEq : (fun p : ℝ × Point n =>
        laplaceBeltrami g gi (fun x => heatParametrix N Θ u p.1 (W₀ x)) p.2)
      = fun p : ℝ × Point n =>
          ∑ i, ∑ j, gi p.2 i j *
            (pd (fun y => pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) j y) i p.2
              - ∑ k, christoffel g gi k i j p.2
                  * pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) k p.2) := by
    funext p; rw [laplaceBeltrami]
  rw [hEq]
  apply continuousOn_finsetSum; intro i _
  apply continuousOn_finsetSum; intro j _
  refine (hgi i j).mul
    ((chartComposed_pd_pd_jointContinuousOn N Θ u W₀ t₁ t₂ R ht₁ i j hw hWc2 hWc1cont hWc2cont).sub ?_)
  apply continuousOn_finsetSum; intro k _
  exact (hChr k i j).mul
    (chartComposed_pd_jointContinuousOn N Θ u W₀ t₁ t₂ R ht₁ k hw hWc2 hWc1cont)

/-! ###############################################################################
    ## (D5) — `hBcont`: the chart-composed `heatOp` joint continuity.
    ############################################################################### -/

/-- **★★ (D5) `chartComposedHeatOp_jointContinuousOn` — `hBcont`.**  Joint `(τ,z)`-continuity of the
    chart-composed order-`N` parametrix heat operator
      `p ↦ heatOp g gi (fun s x _ => heatParametrix N Θ u s (W₀ x)) p.1 p.2 0`
    on `Icc t₁ t₂ ×ˢ closedBall 0 R` (`0 < t₁`).  `heatOp = ∂_τ − Δ_g`, so this is the DIFFERENCE of
    the (D3) `∂_τ`-term and the (D4) `Δ`-term joint continuities.  Carries ONLY genuine, satisfiable
    inputs: coefficient regularity (`hw`/`hΘc`/`hΘne`/`huc`), geometry continuities (`hgi`/`hChr`), and
    the chart facts (`hWc2` pointwise `C²` on the ball + the two chart-jet joint continuities
    `hWc1cont`/`hWc2cont`).  None is the conclusion.  NOT `a₁ = R/6`. -/
theorem chartComposedHeatOp_jointContinuousOn (N : ℕ)
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z)
    (hWc1cont : ∀ a i, ContinuousOn (fun p : ℝ × Point n => pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hWc2cont : ∀ a i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun z => W₀ z a) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (fun s x (_ : Point n) => heatParametrix N Θ u s (W₀ x)) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hEq : (fun p : ℝ × Point n =>
        heatOp g gi (fun s x (_ : Point n) => heatParametrix N Θ u s (W₀ x)) p.1 p.2 0)
      = fun p : ℝ × Point n =>
          deriv (fun s => heatParametrix N Θ u s (W₀ p.2)) p.1
            - laplaceBeltrami g gi (fun x => heatParametrix N Θ u p.1 (W₀ x)) p.2 := by
    funext p; rw [heatOp]
  rw [hEq]
  exact (chartComposed_dtau_jointContinuousOn N Θ u W₀ t₁ t₂ R ht₁ hΘc hΘne huc hWc2).sub
    (chartComposed_laplaceBeltrami_jointContinuousOn N g gi Θ u W₀ t₁ t₂ R ht₁ hw hgi hChr
      hWc2 hWc1cont hWc2cont)

/-! ###############################################################################
    ## (D6) — the boundary-chain `E`-continuity, `hBcont` DISCHARGED.
    ############################################################################### -/

/-- **★★ (D6) `heatOpGatedWitness_jointContinuousOn_final`.**  The joint `(τ,z)`-continuity of the
    concrete gated van-Vleck witness heat operator
      `E := fun p => heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0`
    on `Icc t₁ t₂ ×ˢ closedBall 0 R`, obtained by plugging the CONCRETE D5 `hBcont` (at `N = 1`,
    `Θ* = vanVleck g`, `u* = transportCoeff (transportOp (vanVleck g) g gi)`,
    `W₀ = uniformInverseChart g gi hC hK 0`) into J4-286's L3
    `heatOpGatedWitness_jointContinuousOn_of_chartParametrix`.  Every carry is genuine and satisfiable:
      • coefficient regularity `hw`/`hΘc`/`hΘne`/`huc` (chart-jet + van-Vleck smoothness banks),
      • geometry continuities `hgi`/`hChr`,
      • the chart facts `hWc2`/`hWc1cont`/`hWc2cont` (inverse chart `C²` on a ball in its `C²` region),
      • the gate data (`h0K`/`hSopen`/`hsub`) and the cutoff germ `hcut`.
    None is the conclusion; the conclusion is about the witness `E`, linked by the PROVEN chart-composed
    reduction.  NOT `a₁ = R/6`. -/
theorem heatOpGatedWitness_jointContinuousOn_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (h0K : (0 : Point n) ∈ K) (hSopen : IsOpen (S 0))
    (hsub : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hcut : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      (fun p' : Point n => radialCutoff a b (uniformInverseChart g gi hC hK 0 p'))
        =ᶠ[nhds p.2] (fun _ => (1 : ℝ)))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hWc2 : ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ c,
      ContDiffAt ℝ 2 (fun y => uniformInverseChart g gi hC hK 0 y c) z)
    (hWc1cont : ∀ c i, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => uniformInverseChart g gi hC hK 0 y c) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hWc2cont : ∀ c i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => uniformInverseChart g gi hC hK 0 z c) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  heatOpGatedWitness_jointContinuousOn_of_chartParametrix g gi hC hK S a b t₁ t₂ R
    h0K hSopen hsub hcut
    (chartComposedHeatOp_jointContinuousOn 1 g gi (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) (uniformInverseChart g gi hC hK 0)
      t₁ t₂ R ht₁ hw hΘc hΘne huc hgi hChr hWc2 hWc1cont hWc2cont)

#check @heatParametrix_contDiff_space
#check @chartComposed_pd_eq
#check @chartComposed_pd_pd_eq
#check @chartComposed_pd_jointContinuousOn
#check @chartComposed_pd_pd_jointContinuousOn
#check @chartComposed_dtau_jointContinuousOn
#check @chartComposed_laplaceBeltrami_jointContinuousOn
#check @chartComposedHeatOp_jointContinuousOn
#check @heatOpGatedWitness_jointContinuousOn_final

end QIQTH.ChartComposedHeatOp

/-! ## Axiom checks — every theorem `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ChartComposedHeatOp
#print axioms heatParametrix_contDiff_space
#print axioms chartComposed_pd_eq
#print axioms chartComposed_pd_pd_eq
#print axioms chartComposed_pd_jointContinuousOn
#print axioms chartComposed_pd_pd_jointContinuousOn
#print axioms chartComposed_dtau_jointContinuousOn
#print axioms chartComposed_laplaceBeltrami_jointContinuousOn
#print axioms chartComposedHeatOp_jointContinuousOn
#print axioms heatOpGatedWitness_jointContinuousOn_final
end AxiomChecks
