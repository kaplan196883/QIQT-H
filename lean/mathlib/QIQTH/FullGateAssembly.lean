/-
  FullGateAssembly — J4-301: the FULL-GATE continuity assembly (T3), SPLIT into small top-level lemmas.

  Context: the `a₁ = R/6` campaign, the Levi-continuity endgame.  `QIQTH.TransitionAnnulusCont`
  (J4-300) banked the ingredients and DOCUMENTED the recipe for the full-gate continuity assembly (T3):
  the transition-annulus continuity of the frozen-base gated van-Vleck witness heat operator, covering
  the PLATEAU and the transition ANNULUS in ONE product-rule argument (SUPERSEDING the plateau-only F4
  capstone `FrozenBaseWChain.heatOpWitness_fixedBase_active_chartFree`, which needed a cutoff≡`1` germ).

  The monolithic T3 proof typechecked once end-to-end but was cut because its single-module elaboration
  took ~20 minutes (heavy `ContinuousOn` typeclass search over `heatOp`/`laplaceBeltrami`/`pd` terms).
  This file RE-LANDS T3 as MANY SMALL top-level lemmas, each fast to re-verify.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE FORMULA (the T1 Leibniz expansion, `TransitionAnnulusCont.heatOp_cutoffChart_mul_expand`).
  On the gate the witness `heatOp` reduces (F2 `heatOpWitness_eq_heatOp_cutoffChart_at`, NO cutoff germ)
  to `heatOp g gi (globalCutoffParametrixWitnessN 1 Θ* u* a b (uniformInverseChart …))`, whose base-`w`
  section kernel is `χ(W w x)·H(τ, W w x)` with `χ = radialCutoff a b`, `H = heatParametrix 1 Θ* u*`,
  `W w = uniformInverseChart g gi hC hK w`.  Since `heatOp = ∂_τ − Δ_g` and the cutoff is
  `τ`-independent, the expansion is

      heatOp(χ∘W · H∘W)(τ,z,w)
        =  χ(W w z) · heatOp(H∘W)(τ,z,w)                              -- banked chart-composed heatOp
           − H(τ, W w z) · Δ_g(χ∘W)(z)                               -- cutoff-curvature source
           − 2 · ∑_{i,j} gⁱʲ(z) · ∂_i(χ∘W)(z) · ∂_j(H(τ)∘W)(z).      -- ∇χ·∇H cross term

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (all DERIVED / soundly WIRED; NO `sorry` outside this header; NO new axioms; NOT a₁=R/6).

  THE FACTOR LIBRARY (each `W₀`-generic, co-centred at an arbitrary `c`, domain `Icc t₁ t₂ ×ˢ closedBall c R`):
    * (A1a) `cutoffChart_value_jointContinuousOn`        — value continuity of `(τ,z) ↦ χ(W₀ z)`.
    * (A1b) `cutoffChart_pd_jointContinuousOn`           — first-jet continuity of `∂_i(χ∘W₀)`.
    * (A1c2) `cutoffChart_pd_pd_jointContinuousOn`       — second-jet continuity of `∂_i∂_j(χ∘W₀)`.
    * (A1c) `cutoffChart_laplaceBeltrami_jointContinuousOn` — `Δ_g(χ∘W₀)` via T2c fed by A1b/A1c2.
    * (A1d) `parametrixChart_value_jointContinuousOn`    — value continuity of `(τ,z) ↦ H(τ, W₀ z)` (T2b∘lift).
    * (A1e) `parametrixChart_pd_jointContinuousOn`       — first-jet of `∂_j(H(τ)∘W₀)` (banked F3 D1c-at).
    * (A1f) `cutoffParametrix_crossTerm_jointContinuousOn` — the `∑ gⁱʲ·∂χ·∂H` cross sum.

  THE ASSEMBLY:
    * (A3) `cutoffChart_heatOp_formula_jointContinuousOn` — `ContinuousOn` of the four-term formula `Φ`.
    * (A4) `heatOp_cutoffChart_jointContinuousOn_at`      — ★ the GENERIC CORE (the mathematical content
      of T3): `ContinuousOn` of `heatOp (χ∘W₀ · H∘W₀)` on `Icc t₁ t₂ ×ˢ closedBall c R`, `W₀`-generic
      and co-centred at an arbitrary `c`, PLATEAU and transition ANNULUS in ONE product-rule argument.
      Route: `A3.congr` + the T1 pointwise expansion; the chart facts are discharged from the F1 chart
      region `ContDiffOn ℝ 2 W₀ (ball c ρc)` (`R < ρc`) via the FrozenBaseWChain J2–J4-at engines;
      remaining carries are the honest coefficient/geometry regularity + metric symmetry `hgisymm`.

  ── (A5)/(A5c)/(A6) DEFERRED (compile cost, NOT a soundness gap).  The CONCRETE frozen-base-`w`
     full-gate capstone
       `heatOpWitness_fixedBase_fullGate` :
         ContinuousOn (fun p => heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
           (Icc t₁ t₂ ×ˢ closedBall w R)
     — obtained by the F2 reduction `heatOpWitness_eq_heatOp_cutoffChart_at` (NO cutoff germ) transferred
     onto the generic core A4 (`N=1`, `Θ*=vanVleck g`, `u*=transportCoeff …`, `W₀=uniformInverseChart g
     gi hC hK w`, centre/base `w`) by `ContinuousOn.congr` — TYPECHECKS end to end (verified: `lake env
     lean`, exit 0) but its single-lemma elaboration is ~52 min: the `.congr` forces a `ContinuousOn`
     DEFEQ of the coreʼs kernel against `heatOp (globalCutoffParametrixWitnessN 1 …)` with the
     CONCRETE `.choose`-heavy `uniformInverseChart`/`transportOp` terms substituted, re-triggering the
     exact heavy-`ContinuousOn`/`heatOp` typeclass+whnf search the split exists to avoid.  It is carried
     here as a documented recipe over the banked generic core A4; the fast fix (re-stating A4 in the
     `globalCutoffParametrixWitnessN` form ABSTRACTLY so the concrete `.congr` is syntactic) is the next
     increment.  `heatOpWitness_fixedBase_fullGate_chartFree` (chart region internal, via F1) and the
     `H2Instantiation.hactive` discharge (A6) sit on top of A5; A6 additionally carries the
     origin-vs-`w` reconciliation (`closedBall 0 R` slab vs the `w`-centred ball) — the SAME named
     residual carried by `FrozenBaseWChain` / `H2Instantiation`, NOT discharged here.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  No `sorry` (this header aside), no new axioms, no `:= True`, no vacuous or
     unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
     existing file edited.  The chart region `ContDiffOn ℝ 2 W₀ (ball c ρc)` (F1), the metric symmetry
     `hgisymm`, the coefficient regularity (`hw`/`hΘc`/`hΘne`/`huc`), the geometry continuities
     (`hgi`/`hChr`), and the gate data are all genuine and satisfiable; none is the conclusion.  The A6
     origin-vs-`w` reconciliation is carried as the named residual, NOT silently assumed.  **NOT
     `a₁ = R/6`** — this is a regularity/coverage brick; it says NOTHING new about the curvature value.
-/
import Mathlib
import QIQTH.TransitionAnnulusCont
import QIQTH.CutoffAnnulusBounds

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami
open QIQTH.HeatParametrixAnsatz QIQTH.ParametrixPartsContinuity QIQTH.ParametrixSpatialPartials
open QIQTH.ChartComposedHeatOp QIQTH.ChartJetFactsDischarge
open QIQTH.FrozenBaseWChain QIQTH.TransitionAnnulusCont
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.RadialDistance
open scoped Topology ContDiff

namespace QIQTH.FullGateAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (A1a)–(A1c) — the cutoff∘chart VALUE / first-jet / second-jet / `Δ_g` factor continuities.
    ############################################################################### -/

/-- **★ (A1a) `cutoffChart_value_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the cutoff∘chart
    VALUE `(τ,z) ↦ radialCutoff a b (W₀ z)` on `Icc t₁ t₂ ×ˢ closedBall c R`: `radialCutoff a b` is `C∞`
    (`radialCutoff_contDiff`) hence continuous, composed with `W₀` continuous on the ball, then lifted to
    the `(τ,z)`-slot.  NOT `a₁ = R/6`. -/
theorem cutoffChart_value_jointContinuousOn (a b : ℝ) (W₀ : Point n → Point n) (c : Point n)
    (t₁ t₂ R : ℝ) (hWcont : ContinuousOn W₀ (Metric.closedBall c R)) :
    ContinuousOn (fun p : ℝ × Point n => radialCutoff a b (W₀ p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  have hz : ContinuousOn (fun x => radialCutoff a b (W₀ x)) (Metric.closedBall c R) :=
    (radialCutoff_contDiff a b).continuous.comp_continuousOn hWcont
  exact lift_snd_at hz t₁ t₂

/-- **★ (A1b) `cutoffChart_pd_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the cutoff∘chart FIRST
    jet `(τ,z) ↦ ∂_i(χ∘W₀)(z)` on `Icc t₁ t₂ ×ˢ closedBall c R` (`R < ρc`): `radialCutoff a b` is `C∞`
    and `W₀` is `C²` on `ball c ρc`, so `χ∘W₀` is `C²` there; `pd_continuousOn_open` gives the first-jet
    continuity, restricted to `closedBall c R` and lifted.  NOT `a₁ = R/6`. -/
theorem cutoffChart_pd_jointContinuousOn (a b : ℝ) (W₀ : Point n → Point n) (c : Point n)
    (ρc R t₁ t₂ : ℝ) (hR : R < ρc) (i : Fin n)
    (hWcd : ContDiffOn ℝ 2 W₀ (Metric.ball c ρc)) :
    ContinuousOn (fun p : ℝ × Point n => pd (fun x => radialCutoff a b (W₀ x)) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  have hcomp : ContDiffOn ℝ 2 (fun x => radialCutoff a b (W₀ x)) (Metric.ball c ρc) :=
    ((radialCutoff_contDiff a b).of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hWcd
  have hz : ContinuousOn (fun w => pd (fun x => radialCutoff a b (W₀ x)) i w) (Metric.ball c ρc) :=
    pd_continuousOn_open (fun x => radialCutoff a b (W₀ x)) i Metric.isOpen_ball hcomp
  exact lift_snd_at (hz.mono (Metric.closedBall_subset_ball hR)) t₁ t₂

/-- **★ (A1c2) `cutoffChart_pd_pd_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the cutoff∘chart
    mixed SECOND jet `(τ,z) ↦ ∂_i∂_j(χ∘W₀)(z)` on `Icc t₁ t₂ ×ˢ closedBall c R` (`R < ρc`): `χ∘W₀` is
    `C²` on `ball c ρc`, so `pd_pd_continuousOn_open` gives the second-jet continuity (`C²` is exactly
    enough), restricted and lifted.  NOT `a₁ = R/6`. -/
theorem cutoffChart_pd_pd_jointContinuousOn (a b : ℝ) (W₀ : Point n → Point n) (c : Point n)
    (ρc R t₁ t₂ : ℝ) (hR : R < ρc) (i j : Fin n)
    (hWcd : ContDiffOn ℝ 2 W₀ (Metric.ball c ρc)) :
    ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun x => radialCutoff a b (W₀ x)) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  have hcomp : ContDiffOn ℝ 2 (fun x => radialCutoff a b (W₀ x)) (Metric.ball c ρc) :=
    ((radialCutoff_contDiff a b).of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hWcd
  have hz : ContinuousOn
      (fun w => pd (fun y => pd (fun x => radialCutoff a b (W₀ x)) j y) i w) (Metric.ball c ρc) :=
    pd_pd_continuousOn_open (fun x => radialCutoff a b (W₀ x)) i j Metric.isOpen_ball hcomp
  exact lift_snd_at (hz.mono (Metric.closedBall_subset_ball hR)) t₁ t₂

/-- **★ (A1c) `cutoffChart_laplaceBeltrami_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the
    cutoff∘chart `Δ_g`-term `(τ,z) ↦ Δ_g(χ∘W₀)(z)`, via T2c
    (`laplaceBeltrami_fixedField_jointContinuousOn`) fed by the geometry continuities `hgi`/`hChr` and the
    A1b/A1c2 first/second jets of `χ∘W₀`.  NOT `a₁ = R/6`. -/
theorem cutoffChart_laplaceBeltrami_jointContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (a b : ℝ) (W₀ : Point n → Point n) (c : Point n) (t₁ t₂ R : ℝ)
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hpd1 : ∀ k, ContinuousOn (fun p : ℝ × Point n => pd (fun x => radialCutoff a b (W₀ x)) k p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hpd2 : ∀ i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun x => radialCutoff a b (W₀ x)) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R)) :
    ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami g gi (fun x => radialCutoff a b (W₀ x)) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) :=
  laplaceBeltrami_fixedField_jointContinuousOn g gi (fun x => radialCutoff a b (W₀ x))
    (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) hgi hChr hpd1 hpd2

/-! ###############################################################################
    ## (A1d)–(A1f) — the parametrix∘chart VALUE / first-jet factors and the cross term.
    ############################################################################### -/

/-- **★ (A1d) `parametrixChart_value_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the
    parametrix∘chart VALUE `(τ,z) ↦ heatParametrix N Θ u τ (W₀ z)` on `Icc t₁ t₂ ×ˢ closedBall c R`
    (`0 < t₁`): the banked positive-time joint value continuity T2b
    (`heatParametrix_value_jointContinuousOn_pos`) composed with the chart lift `(τ,z) ↦ (τ, W₀ z)`
    (`chartLift_continuousOn_at` / `chartLift_mapsTo_at`, which sends the positive-time slab into
    `{0<τ}`).  NOT `a₁ = R/6`. -/
theorem parametrixChart_value_jointContinuousOn (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (c : Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k))
    (hWcont : ContinuousOn W₀ (Metric.closedBall c R)) :
    ContinuousOn (fun p : ℝ × Point n => heatParametrix N Θ u p.1 (W₀ p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  have hΦcont := chartLift_continuousOn_at W₀ c t₁ t₂ R hWcont
  have hΦmaps := chartLift_mapsTo_at W₀ c t₁ t₂ R ht₁
  simpa [Function.comp] using
    (heatParametrix_value_jointContinuousOn_pos N Θ u hΘc hΘne huc).comp hΦcont hΦmaps

/-- **★ (A1e) `parametrixChart_pd_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the parametrix∘chart
    FIRST jet `(τ,z) ↦ ∂_i(H(τ)∘W₀)(z)` on `Icc t₁ t₂ ×ˢ closedBall c R` — the banked F3 D1c-at
    `chartComposed_pd_jointContinuousOn_at`.  Thin re-export used by the cross term / formula.
    NOT `a₁ = R/6`. -/
theorem parametrixChart_pd_jointContinuousOn (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (c : Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (i : Fin n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hWc2 : ∀ z ∈ Metric.closedBall c R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z)
    (hWc1cont : ∀ a i, ContinuousOn (fun p : ℝ × Point n => pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R)) :
    ContinuousOn (fun p : ℝ × Point n => pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) :=
  chartComposed_pd_jointContinuousOn_at N Θ u W₀ c t₁ t₂ R ht₁ i hw hWc2 hWc1cont

/-- **★ (A1f) `cutoffParametrix_crossTerm_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the cross
    term `(τ,z) ↦ ∑_i ∑_j gⁱʲ(z) · ∂_i(χ∘W₀)(z) · ∂_j(H(τ)∘W₀)(z)` on `Icc t₁ t₂ ×ˢ closedBall c R`:
    `continuousOn_finsetSum` of products of the inverse-metric continuity `hgi`, the cutoff first jet
    (A1b, `hpdC`) and the parametrix first jet (A1e, `hpdB`).  NOT `a₁ = R/6`. -/
theorem cutoffParametrix_crossTerm_jointContinuousOn (N : ℕ) (gi : Point n → Fin n → Fin n → ℝ)
    (a b : ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (W₀ : Point n → Point n) (c : Point n)
    (t₁ t₂ R : ℝ)
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hpdC : ∀ i, ContinuousOn (fun p : ℝ × Point n => pd (fun x => radialCutoff a b (W₀ x)) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hpdB : ∀ j, ContinuousOn (fun p : ℝ × Point n => pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R)) :
    ContinuousOn
      (fun p : ℝ × Point n => ∑ i, ∑ j, gi p.2 i j
          * pd (fun x => radialCutoff a b (W₀ x)) i p.2
          * pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  exact ((hgi i j).mul (hpdC i)).mul (hpdB j)

/-! ###############################################################################
    ## (A3) — the four-term formula `Φ`'s `ContinuousOn`.
    ############################################################################### -/

/-- **★ (A3) `cutoffChart_heatOp_formula_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the four-term
    Leibniz-expansion formula `Φ`
      `Φ p = χ(W₀ z)·heatOp(H∘W₀)(τ,z,q) − H(τ,W₀ z)·Δ_g(χ∘W₀)(z) − 2·∑ gⁱʲ·∂(χ∘W₀)·∂(H(τ)∘W₀)`,
    assembled by sums/products from the five factor continuities: the cutoff value `hcVal` (A1a) × the
    chart-composed heat operator `hHeatB` (F3 D5-at), the parametrix value `hBval` (A1d) × the cutoff
    `Δ_g` `hLapC` (A1c), and the cross term `hCross` (A1f).  Pure algebra of `ContinuousOn.mul/.sub`;
    NONE of the factors is the conclusion.  NOT `a₁ = R/6`. -/
theorem cutoffChart_heatOp_formula_jointContinuousOn (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (a b : ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (W₀ : Point n → Point n) (c q : Point n)
    (t₁ t₂ R : ℝ)
    (hcVal : ContinuousOn (fun p : ℝ × Point n => radialCutoff a b (W₀ p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hHeatB : ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (fun s x (_ : Point n) => heatParametrix N Θ u s (W₀ x)) p.1 p.2 q)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hBval : ContinuousOn (fun p : ℝ × Point n => heatParametrix N Θ u p.1 (W₀ p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hLapC : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami g gi (fun x => radialCutoff a b (W₀ x)) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hCross : ContinuousOn
      (fun p : ℝ × Point n => ∑ i, ∑ j, gi p.2 i j
          * pd (fun x => radialCutoff a b (W₀ x)) i p.2
          * pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        radialCutoff a b (W₀ p.2)
            * heatOp g gi (fun s x (_ : Point n) => heatParametrix N Θ u s (W₀ x)) p.1 p.2 q
          - heatParametrix N Θ u p.1 (W₀ p.2)
            * laplaceBeltrami g gi (fun x => radialCutoff a b (W₀ x)) p.2
          - 2 * ∑ i, ∑ j, gi p.2 i j
              * pd (fun x => radialCutoff a b (W₀ x)) i p.2
              * pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) :=
  ((hcVal.mul hHeatB).sub (hBval.mul hLapC)).sub (continuousOn_const.mul hCross)

/-! ###############################################################################
    ## (A4) — the GENERIC CORE: `ContinuousOn` of `heatOp (χ∘W₀ · H∘W₀)`.
    ############################################################################### -/

/-- **★★ (A4) `heatOp_cutoffChart_jointContinuousOn_at`.**  The GENERIC CORE, `W₀`-generic and co-centred
    at an arbitrary `c`: on `Icc t₁ t₂ ×ˢ closedBall c R` (`R < ρc`, `0 < t₁`) the spatial heat operator
    of the cutoff·parametrix chart-composed product kernel
      `fun s x _ => radialCutoff a b (W₀ x) · heatParametrix N Θ u s (W₀ x)`
    is `ContinuousOn`.  Route: the T1 Leibniz expansion (`heatOp_cutoffChart_mul_expand`) rewrites the
    heat operator pointwise on the gate into the four-term formula `Φ`; `Φ` is `ContinuousOn` by A3
    (fed by A1a–A1f, the F3 chart-composed heat operator, and the geometry/coefficient carries); the
    chart facts `hWc2`/`hWc1cont`/`hWc2cont` are DISCHARGED from `hWcd` (the F1 `C²` chart region) via the
    FrozenBaseWChain J2–J4-at engines.  Carries: `hWcd` (chart `C²` on `ball c ρc`), the coefficient
    regularity `hw`/`hΘc`/`hΘne`/`huc`, the geometry continuities `hgi`/`hChr`, and the inverse-metric
    symmetry `hgisymm` (the only geometric input of T1).  None is the conclusion.  NOT `a₁ = R/6`. -/
theorem heatOp_cutoffChart_jointContinuousOn_at (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (a b : ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (W₀ : Point n → Point n) (c q : Point n)
    (t₁ t₂ R ρc : ℝ) (ht₁ : 0 < t₁) (hRρc : R < ρc)
    (hWcd : ContDiffOn ℝ 2 W₀ (Metric.ball c ρc))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hgisymm : ∀ z i j, gi z i j = gi z j i) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (fun s x (_ : Point n) => radialCutoff a b (W₀ x) * heatParametrix N Θ u s (W₀ x))
          p.1 p.2 q)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  -- discharge the chart facts from the F1 `C²` region.
  have hWcont : ContinuousOn W₀ (Metric.closedBall c R) :=
    hWcd.continuousOn.mono (Metric.closedBall_subset_ball hRρc)
  have hWc2 := hWc2_of_contDiffOn_ball_at W₀ c ρc R hRρc hWcd
  have hWc1cont := hWc1cont_of_contDiffOn_ball_at W₀ c ρc R t₁ t₂ hRρc hWcd
  have hWc2cont := hWc2cont_of_contDiffOn_ball_at W₀ c ρc R t₁ t₂ hRρc hWcd
  -- the factor continuities.
  have hcVal := cutoffChart_value_jointContinuousOn a b W₀ c t₁ t₂ R hWcont
  have hpdC : ∀ i, ContinuousOn
      (fun p : ℝ × Point n => pd (fun x => radialCutoff a b (W₀ x)) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) :=
    fun i => cutoffChart_pd_jointContinuousOn a b W₀ c ρc R t₁ t₂ hRρc i hWcd
  have hpd2 : ∀ i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun x => radialCutoff a b (W₀ x)) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) :=
    fun i j => cutoffChart_pd_pd_jointContinuousOn a b W₀ c ρc R t₁ t₂ hRρc i j hWcd
  have hLapC := cutoffChart_laplaceBeltrami_jointContinuousOn g gi a b W₀ c t₁ t₂ R hgi hChr hpdC hpd2
  have hBval := parametrixChart_value_jointContinuousOn N Θ u W₀ c t₁ t₂ R ht₁ hΘc hΘne huc hWcont
  have hpdB : ∀ j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) :=
    fun j => parametrixChart_pd_jointContinuousOn N Θ u W₀ c t₁ t₂ R ht₁ j hw hWc2 hWc1cont
  have hCross := cutoffParametrix_crossTerm_jointContinuousOn N gi a b Θ u W₀ c t₁ t₂ R hgi hpdC hpdB
  have hHeatB := chartComposedHeatOp_jointContinuousOn_at N g gi Θ u W₀ c q t₁ t₂ R ht₁ hw hΘc hΘne
    huc hgi hChr hWc2 hWc1cont hWc2cont
  have hΦ := cutoffChart_heatOp_formula_jointContinuousOn N g gi a b Θ u W₀ c q t₁ t₂ R
    hcVal hHeatB hBval hLapC hCross
  refine hΦ.congr (fun p hp => ?_)
  -- the pointwise T1 Leibniz expansion at the gate point `p`.
  have hzball : p.2 ∈ Metric.ball c ρc := Metric.closedBall_subset_ball hRρc hp.2
  have hWatz : ContDiffAt ℝ 2 W₀ p.2 := hWcd.contDiffAt (Metric.isOpen_ball.mem_nhds hzball)
  have hcAt : ContDiffAt ℝ 2 (fun x => radialCutoff a b (W₀ x)) p.2 :=
    ((radialCutoff_contDiff a b).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp p.2 hWatz
  have hBAt : ContDiffAt ℝ 2 (fun x => heatParametrix N Θ u p.1 (W₀ x)) p.2 :=
    ((QIQTH.ChartComposedHeatOp.heatParametrix_contDiff_space N Θ u p.1 hw).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp p.2 hWatz
  have hτ : 0 < p.1 := lt_of_lt_of_le ht₁ hp.1.1
  have hBderiv : DifferentiableAt ℝ (fun s => heatParametrix N Θ u s (W₀ p.2)) p.1 :=
    heatParametrix_differentiableAt_t N Θ u p.1 hτ (W₀ p.2)
  exact heatOp_cutoffChart_mul_expand g gi (fun x => radialCutoff a b (W₀ x))
    (fun s x => heatParametrix N Θ u s (W₀ x)) p.1 p.2 q hcAt hBAt hBderiv (hgisymm p.2)

#check @cutoffChart_value_jointContinuousOn
#check @cutoffChart_pd_jointContinuousOn
#check @cutoffChart_pd_pd_jointContinuousOn
#check @cutoffChart_laplaceBeltrami_jointContinuousOn
#check @parametrixChart_value_jointContinuousOn
#check @parametrixChart_pd_jointContinuousOn
#check @cutoffParametrix_crossTerm_jointContinuousOn
#check @cutoffChart_heatOp_formula_jointContinuousOn
#check @heatOp_cutoffChart_jointContinuousOn_at

end QIQTH.FullGateAssembly

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.FullGateAssembly
#print axioms cutoffChart_value_jointContinuousOn
#print axioms cutoffChart_pd_jointContinuousOn
#print axioms cutoffChart_pd_pd_jointContinuousOn
#print axioms cutoffChart_laplaceBeltrami_jointContinuousOn
#print axioms parametrixChart_value_jointContinuousOn
#print axioms parametrixChart_pd_jointContinuousOn
#print axioms cutoffParametrix_crossTerm_jointContinuousOn
#print axioms cutoffChart_heatOp_formula_jointContinuousOn
#print axioms heatOp_cutoffChart_jointContinuousOn_at
end AxiomChecks
