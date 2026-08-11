/-
  CurvedA1HAdom — J4-600: the `hAdom` carry DISCHARGED — the global all-`(p,q)` witness Gaussian
  domination for the genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`), produced JOINTLY
  with `hBdom` at ONE set of gate parameters, so the capstone's `hInnerCont` reduction now owes
  EXACTLY `{hmeas, hcont}`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  J4-599 (`CurvedA1ReachAlign`) closed the reach alignment: `curved_hBdom_unconditional`
  produces gate parameters `0 < a < b < c` with the width-2 Levi domination `hBdom` given only the
  mainline carries {`hChr`, `hw`, `hu`}, and `curved_hInnerCont_of_meas` reduces the capstone's
  carried `hInnerCont` to the THREE raw carries `{hAdom, hmeas, hcont}` AT ITS OWN ∃ parameters.
  The `hAdom` binder (the D1 witness Gaussian domination, all `p q`):

      `∀ τ > 0, ∀ p q, |vanVleckGatedWitness g^K gi^K hChr hK (constGate … c) a b τ p q|
         ≤ (A₀ + A₁·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p − q)` .

  ── ★★ THE POINT (J4-600).  `hAdom` is ALREADY BANKED in exactly this shape — at a FREE choice of
  `(a,b)` but at ITS OWN gate radius: `CurvedRNCBaseWitnessDomAdom.curvedRNC_baseWitness_dom_adom`
  (J4-535) proves it via the generic recenter-of-domination
  `ConcreteDominations.exists_D1_constants_of_gateSqControl`, whose ONLY geometric input is a
  `GateSqControl` certificate — discharged for ANY flow-ball gate radius `c` with `c ≤ r₁`
  (near-isometry reach, `uniformFlowExp_hdisp_ball`) and `c < δ₀` (chart-inverse reach,
  `uniformInverseChart_huniformChart`) by `gateSqControl_of_flowBall`.  The consumer
  (`curved_hInnerCont_of_meas` / `curved_hInnerCont_of_dominations`) needs `hAdom` at the SAME
  `(a,b,c)` as `hBdom` — the J4-598/599 parameter-compatibility lesson.  Since the J4-599
  prescribed-ceiling pkg `curvedRNC_heatOp_dom_pkg_prescribed` accepts an ARBITRARY radius ceiling
  `ε > 0`, prescribing `ε := min δjet (min r₁ (δ₀/2))` makes the pkg's OWN produced radius `c`
  simultaneously satisfy `c < δjet` (the `hEmeas` jet reach — the J4-599 route to `hBdom`), `c < r₁`
  and `c < δ₀` (the `GateSqControl` radii — the route to `hAdom`).  Joint production at ONE `(a,b,c)`
  follows; `exists_D1_constants_of_gateSqControl` takes `(a,b)` free, so the pkg's `(a,b)` feed it
  directly, with the SAME mainline amplitude carry `hw`.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_hAdom_hBdom_at_gate` — ★★★ THE JOINT PRODUCTION: for `κ < 0`, `1 ≤ n`, `T > 0`, GIVEN
      only {`hChr`, `hw`, `hu`}: ∃ gate parameters `0 < a < b < c` with BOTH the EXACT `hAdom` binder
      (∃ `A₀, A₁ ≥ 0`, all `τ > 0`, ALL `p q`) AND the EXACT width-2 `hBdom` binder (∃ `C_L ≥ 0`,
      on `(0,T]`) at those SAME parameters.
    • `curved_hInnerCont_of_two` — ★★ THE CONSUMPTION CERTIFICATE: the capstone's carried
      `hInnerCont` conclusion reduced to EXACTLY `{hmeas, hcont}` — the `hAdom`, `hBdom`, AND
      `hEmeas` slots ALL internally discharged at one compatible parameter set.
    • `curved_hAdom_satisfiable` — ★ non-vacuity: `g^K` genuinely curved (`∃ w, 1 < det`).

  ── ADVERSARIAL NOTES.  The `√(3/2)ⁿ` prefactor and width `(3/2)·τ` are NOT re-derived here — they
  are the banked D1 constants of `exists_D1_constants_of_gateSqControl` (J4-113), whose Gaussian
  bookkeeping (recentring `gaussDdim (3/2·τ)(p−q)` against the amplitude sup via the `GateSqControl`
  square comparison `rncRadialSq (p−q) ≤ (3/2)·rncRadialSq (W q p)`) is a PROVED theorem, not a
  normalization guess.  The gate parameters remain GENUINE (`0 < a < b < c`, `c` small but inhabited;
  the capstone consumes `a b c` free).  The witness is genuinely curved (`κ < 0`,
  `Ric(0) = n(n−1)κ ≠ 0`); off the gate the witness vanishes and the bound is trivially true — the
  content is ON the gate, where it is the banked amplitude × Gaussian estimate.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`, and a₁ = R/6 remains CONDITIONAL even with `hAdom` landed:
  `hInnerCont` still owes `{hmeas, hcont}`, and the curved capstone still owes the census/domination
  piles, the rest of the convergence trio, `hmassone`'s pre-ρ carriers, and the `hjets` residual
  (+ the labelled mainline carries {`hChr`, `hw`, `hu`}).  Everything here is TRUE for `g^K`
  (`κ < 0`), DERIVED from PROVED machinery (NOT axiomatized, NOT the `a₁` conclusion); the `R/6`
  value is unaffected.  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous hypothesis,
  no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedRNCHeatOpDomPkg
import QIQTH.GatedWitnessPackage
import QIQTH.CurvedA1HContDom
import QIQTH.CurvedA1HBdom
import QIQTH.CurvedA1GateS1
import QIQTH.CurvedA1HEmeas
import QIQTH.ReachRequant
import QIQTH.CurvedA1ReachAlign
import QIQTH.ConcreteDominations
import QIQTH.NearIsometryBudget
import QIQTH.UniformChartRadius
import QIQTH.CurvedRNCBaseWitnessDomAdom

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.GateOpennessExport QIQTH.S1TripleHEmeasGate QIQTH.ConstRadiusGateExport
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCPosDef QIQTH.GaussGaugeToHgauge
open QIQTH.CurvedRNCHeatOpDomPkg
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.CurvedA1HAdom

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### (B1) — ★★★ THE JOINT PRODUCTION: `hAdom` + `hBdom` at ONE set of gate parameters. -/

/-- **★★★ J4-600 (B1) — `curved_hAdom_hBdom_at_gate`.**  THE JOINT `hAdom`/`hBdom` PRODUCTION for
    the genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`), `1 ≤ n`, any ceiling `T > 0`,
    GIVEN only the mainline-standard carried geometric inputs {`hChr`, `hw`, `hu`}: there are gate
    parameters `0 < a < b < c` such that BOTH
    * `hAdom` (∃ `A₀, A₁ ≥ 0`): the D1 witness Gaussian domination for ALL `τ > 0`, ALL `p q`
      (the EXACT binder consumed by `curved_hInnerCont_of_meas`/`curved_hInnerCont_of_dominations`),
    * `hBdom` (∃ `C_L ≥ 0`): the width-2 Levi-series Gaussian domination on `(0,T]`,
    hold AT THOSE SAME parameters.  Route: prescribe the J4-599 pkg ceiling
    `ε := min δjet (min r₁ (δ₀/2))`, so the pkg's own radius `c` clears the `hEmeas` jet reach
    (⟹ `hBdom`, verbatim J4-599 assembly) AND the `GateSqControl` radii
    (⟹ `hAdom`, via the banked `gateSqControl_of_flowBall` +
    `exists_D1_constants_of_gateSqControl` at the pkg's own `(a,b)`).  NOT `a₁ = R/6`. -/
theorem curved_hAdom_hBdom_at_gate (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) k))
    (T : ℝ) (hT : 0 < T) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      (∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) ∧
      (∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b))
            s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y)) := by
  classical
  have hn0 : 0 < n := by omega
  -- 1. the requantified jet reach for `g^K` — available BEFORE the gate parameters (J4-599 R13).
  obtain ⟨δjet, hδjet, hjet⟩ :=
    QIQTH.ReachRequant.tripleHEmeas_flowball_requant hn0 (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (fun a b => curvedRNCInv_contDiff κ hκ.le a b)
      (curvedRNCMetric_hgpos κ hκ.le)
      hu
      (fun i j => (curvedRNCInv_contDiff κ hκ.le i j).continuous.measurable)
      (fun k i j => (hChr k i j).continuous.measurable)
  -- 2. the two banked UNIFORM flow-ball radii for the `GateSqControl` (J4-535 route).
  obtain ⟨r₁, hr₁pos, hdisp⟩ :=
    uniformFlowExp_hdisp_ball (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
  obtain ⟨δ₀, hδ₀pos, hchart⟩ :=
    uniformInverseChart_huniformChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
  -- 3. ★ THE JOINT CEILING: pkg radius below the jet reach AND both GateSqControl radii.
  set ε : ℝ := min δjet (min r₁ (δ₀ / 2)) with hεdef
  have hε : 0 < ε := lt_min hδjet (lt_min hr₁pos (half_pos hδ₀pos))
  obtain ⟨a, b, C, c, ha, hab, hC0, hbc, hcε, hpkg, -⟩ :=
    QIQTH.CurvedA1ReachAlign.curvedRNC_heatOp_dom_pkg_prescribed κ hκ hChr hw T ε hε
  have hcδjet : c < δjet := lt_of_lt_of_le hcε (min_le_left _ _)
  have hcr₁ : c < r₁ :=
    lt_of_lt_of_le hcε (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδ₀ : c < δ₀ :=
    lt_of_lt_of_le hcε (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (half_le_self hδ₀pos.le)))
  refine ⟨a, b, c, ha, hab, hbc, ?_, ?_⟩
  · -- ── `hAdom`: GateSqControl at the pkg's OWN radius `c` → the banked D1 recentring.
    have hinv : ∀ q ∈ ({(0 : Point n)} : Set (Point n)), ∀ v : Point n, ‖v‖ < c →
        uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) q
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) q v) = v := by
      intro q hq v hv
      obtain ⟨hgerms, -⟩ := hchart q hq
      obtain ⟨hgerm, -⟩ := hgerms v (lt_trans hv hcδ₀)
      simpa using hgerm.eq_of_nhds
    have hgate : GateSqControl ({(0 : Point n)} : Set (Point n))
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
        (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))) :=
      gateSqControl_of_flowBall ({(0 : Point n)} : Set (Point n))
        (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))))
        (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))))
        c r₁ hcr₁.le hinv hdisp
    obtain ⟨A₀, A₁, hA₀, hA₁, hdom⟩ :=
      exists_D1_constants_of_gateSqControl (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ)))
        a b
        (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))))
        ({(0 : Point n)} : Set (Point n))
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
        ha hab hw hgate
    exact ⟨A₀, A₁, hA₀, hA₁, fun τ hτ p q => hdom τ p q hτ⟩
  · -- ── `hBdom`: the verbatim J4-599 assembly (`c < δjet` discharges the reach antecedent).
    have hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)
          w.1 w.2.1 w.2.2) :=
      hjet a b ha hab c hbc hcδjet
    have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
        heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)
          τ p q = 0 :=
      heatOp_gatedWitnessN1_eq_zero_of_nonpos (curvedRNCMetric κ) (curvedRNCInv κ) hn
        ({(0 : Point n)} : Set (Point n))
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
        (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) a b
        (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))))
    have hInt : IterConvIntegrableW
        (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b))
        (2 : ℝ) (0 : ℝ) (C * (1 + T)) :=
      iterConvIntegrableW_of_locally_bound_baseMeas _ (C * (1 + T)) hEzero hEmeas
        (fun T' hT' => ⟨C * (1 + T'), mul_nonneg hC0 (by linarith),
          fun τ p q hτ hτT' => hpkg T' τ p q hτ hτT'⟩)
    obtain ⟨C_L, hCL0, hdom⟩ :=
      leviSeries_dominatedW_le _ (C * (1 + T)) T (mul_nonneg hC0 (by linarith)) hT
        (fun τ p q hτ hτT => hpkg T τ p q hτ hτT) hInt
    refine ⟨C_L, hCL0, fun s hs hsT z y => ?_⟩
    have h := hdom s z y hs hsT
    rwa [baseKernelW_zero_apply] at h

/-! ### (B2) — ★★ the consumption certificate: `hInnerCont` reduced to `{hmeas, hcont}` ONLY. -/

/-- **★★ J4-600 (B2) — `curved_hInnerCont_of_two`.**  THE CONSUMPTION CERTIFICATE: the capstone's
    carried `hInnerCont` conclusion for `g^K = curvedRNCMetric κ` (`κ < 0`) — the interior-time
    `ContinuousOn` of the inner space-time pairing on `Ioo 0 u` — at ∃ gate parameters, given ONLY
    the TWO remaining raw carries `{hmeas, hcont}` at those parameters.  The `hAdom`, `hBdom`, AND
    `hEmeas` slots are ALL internally discharged (joint production, B1).  After this brick the
    `hInnerCont` reduction owes exactly `{hmeas, hcont}`.  NOT `a₁ = R/6`. -/
theorem curved_hInnerCont_of_two (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) k))
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      ((∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b
              (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                    ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
                  a b)) s z 0)
          (volume : Measure (Point n))) →
      (∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
        ContinuousAt
          (fun s => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b
              (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                    ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
                  a b)) s z 0) s₀) →
      ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b
            (u - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
                a b)) s z 0)
        (Set.Ioo 0 u)) := by
  classical
  obtain ⟨a, b, c, ha, hab, hbc, ⟨A₀, A₁, hA₀, hA₁, hAdom⟩, ⟨C_L, hCL0, hBdom⟩⟩ :=
    curved_hAdom_hBdom_at_gate κ hκ hn hChr hw hu T hT
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  intro hmeas hcont
  exact QIQTH.CurvedA1HContDom.curved_hInnerCont_of_dominations κ hChr
    ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) a b c T U hUT
    A₀ A₁ C_L hA₀ hA₁ hCL0 hAdom hBdom hmeas hcont

/-! ### (B3) — non-vacuity. -/

/-- **★ J4-600 (B3) — `curved_hAdom_satisfiable`.**  Non-vacuity of the witness: for `κ < 0`,
    `n ≥ 2`, `g^K = curvedRNCMetric κ` is genuinely curved (`∃ w, 1 < det g^K w`) — the joint
    `hAdom`/`hBdom` production and the `{hmeas, hcont}` reduction are NOT secretly about the flat
    kernel.  Re-exports `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`.  NOT `a₁ = R/6`. -/
theorem curved_hAdom_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  (QIQTH.CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable κ hκ hn).2

end QIQTH.CurvedA1HAdom

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1HAdom

#print axioms curved_hAdom_hBdom_at_gate
#print axioms curved_hInnerCont_of_two
#print axioms curved_hAdom_satisfiable

end AxiomChecks
