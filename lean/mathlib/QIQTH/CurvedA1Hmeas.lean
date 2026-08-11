/-
  CurvedA1Hmeas — J4-601: the `hmeas` interior z-slice eventual-`AEStronglyMeasurable` carry of the
  reduced `hInnerCont` (J4-600's `curved_hInnerCont_of_two`) DISCHARGED CARRY-FREE — and, by the SAME
  mechanism, the `hcont` carry too, CLOSING the `hInnerCont` reduction — together with an explicit
  ADVERSARIAL DEGENERACY PIN recording WHY the discharge is this cheap.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; this proves NOTHING about the coefficient.  `a₁ = R/6`
  remains CONDITIONAL: the curved capstone still owes the census/domination piles, the rest of the
  convergence trio, `hmassone`'s pre-ρ carriers, and the `hjets` residual (+ the labelled mainline
  carries {`hChr`, `hw`, `hu`}).

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_gatedWitness_offOrigin_zero` — the STRUCTURAL KEY: the J4-592→600 `hInnerCont` chain
      pins the gated-witness base compact to the SINGLETON `hK := isCompact_singleton {0}`
      (read the binders of `CurvedA1HAdom.curved_hInnerCont_of_two` verbatim), and the gate
      `gatedKernel K S H τ p q = if q ∈ K then (if p ∈ S q then H τ p q else 0) else 0` KILLS every
      source point `q = z ∉ K`.  Hence the witness z-slice `z ↦ W (u−s) 0 z` vanishes for EVERY
      `z ≠ 0` and EVERY time (positive or not).
    • `curved_hmeas_at_gate` — ★★ the EXACT `hmeas` binder of `curved_hInnerCont_of_two`, at FREE
      gate parameters `a b c` (pure measurability is radius-independent, so it composes with the
      consumer's ∃-parameters with NO joint production needed): for `u ∈ U`, `s₀ ∈ Ioo 0 u`,
      ∀ᶠ `s` in `𝓝 s₀` (in fact for ALL `s : ℝ` — the ∀ᶠ is `Eventually.of_forall`-trivial), the
      z-slice `z ↦ W (u−s) 0 z · L s z 0` is a.e. EQUAL TO `0` (supported in the Lebesgue-null
      `{0}`, `n ≥ 1`), hence `AEStronglyMeasurable`.  CARRY-FREE.
    • `curved_hcont_at_gate` — ★★ the `hcont` binder by the SAME mechanism: for a.e. `z` (namely all
      `z ≠ 0`) the time path `s ↦ W (u−s) 0 z · L s z 0` is IDENTICALLY `0` (the witness factor dies
      at every `s`), hence `ContinuousAt` everywhere.  CARRY-FREE.
    • `curved_hInnerCont_of_cont` — the J4-601-named reduction: `hInnerCont` from ONLY `hcont`
      (hmeas fed internally).
    • `curved_hInnerCont_closed` — ★★★ the CLOSURE: the capstone's carried `hInnerCont` conclusion
      for `g^K` (κ < 0) with NO `hmeas`/`hcont` carry at all — only the mainline-standard labelled
      inputs {`hChr`, `hw`, `hu`} + window data survive.
    • `curved_innerPairing_zero` — ⚠⚠ THE ADVERSARIAL DEGENERACY PIN (std-3): at the singleton base
      compact the inner pairing `∫ z, W (u−s) 0 z · L s z 0` is IDENTICALLY ZERO for every `s, u`.
      So the `hInnerCont` conclusion just closed is the continuity of the CONSTANT-0 function: TRUE,
      NON-vacuous as a theorem, but ANALYTICALLY EMPTY.  This is the same `K = {0}` source-support
      collapse family as the cp466 vacuity pin (`CurvedA1FarConsumeCheck.witness_baseIntegral_zero`):
      there `hframeK` FORCED `K = {0}`; here the J4-592+ center-gauge chain HARD-CODES
      `hK := isCompact_singleton {0}` in the statement itself.  Consequence (recorded honestly): the
      entire J4-592→601 `hInnerCont` tower at THIS witness carries no `a₁` content — the genuine
      analytic content of `hInnerCont` lives only at a NON-collapsed base compact `K` (e.g. a closed
      ball), where `hmeas`/`hcont` would again be REAL carries (Levi z-slice measurability + a.e.
      time continuity).  DO NOT record "hInnerCont analytically closed"; record "hInnerCont closed
      at the singleton-collapsed witness + degeneracy pinned".
    • `curved_hmeas_satisfiable` — ★ the usual curvature gate: `g^K` genuinely curved for `κ < 0`,
      `n ≥ 2` (`∃ w, 1 < det g^K w`) — the METRIC is not secretly flat (the degeneracy above is in
      the GATE SUPPORT, not the metric).

  ── WHY TRUE / NOT VACUOUS AS THEOREMS.  Every statement is a genuine PROVED fact about the
  genuinely-curved `g^K` (`κ < 0`): a.e.-zero functions ARE `AEStronglyMeasurable`, identically-zero
  paths ARE continuous, and the pin is an exact computation.  No hypothesis equals (or trivially
  yields) a conclusion; the consumer's ∃-parameter structure is respected (our suppliers are ∀ in
  `a b c`, so they instantiate at whatever parameters `curved_hInnerCont_of_two` produces — the
  param-compatibility lesson, discharged by QUANTIFIER SHAPE rather than joint production).

  ── HONEST RESIDUAL.  `hInnerCont` for the singleton-based curved chain: CLOSED (no residual).  BUT
  the closure mechanism simultaneously PINS that this carrier was degenerate at this witness; the
  real analytic wall (Levi-series z-slice measurability + dominated time continuity at a
  NON-collapsed `K`) remains open and is where a future re-based `hInnerCont` must be fought.
  `a₁ = R/6` remains CONDITIONAL — census/domination piles, convergence trio, `hmassone` pre-ρ,
  `hjets` residual (+ labelled {`hChr`, `hw`, `hu`}) all still owed.  No `sorry`, no `admit`, no new
  axioms, no `:= True`, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedA1HAdom

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCPosDef
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.CurvedA1Hmeas

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### (M0) — the structural key: the singleton-gated witness kills every off-origin source. -/

/-- **`curved_gatedWitness_offOrigin_zero` — THE STRUCTURAL KEY.**  The J4-592→600 chain pins the
    witness base compact to `{0}` (`hK := isCompact_singleton`); the hard gate
    `gatedKernel K S H τ p q` vanishes whenever the SOURCE point `q ∉ K`.  Hence the witness z-slice
    `z ↦ W τ 0 z` is `0` at every `z ≠ 0`, for EVERY time `τ` (positive or not — the gate is
    `τ`-independent).  NOT `a₁ = R/6`. -/
theorem curved_gatedWitness_offOrigin_zero (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (a b c τ : ℝ) {z : Point n} (hz : z ≠ 0) :
    vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b
      τ (0 : Point n) z = 0 := by
  have hzK : z ∉ ({(0 : Point n)} : Set (Point n)) := by simpa using hz
  simp only [vanVleckGatedWitness]
  exact gatedKernel_apply_of_notMem _ _ _ τ (0 : Point n) z (Or.inl hzK)

/-- The off-origin set is a.e.-full: `{0}` is Lebesgue-null in `Point n = Fin n → ℝ` for `n ≥ 1`. -/
theorem offOrigin_ae (hn : 1 ≤ n) :
    ∀ᵐ z ∂(volume : Measure (Point n)), z ≠ (0 : Point n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [MeasureTheory.ae_iff]
  have hset : {z : Point n | ¬ z ≠ (0 : Point n)} = {(0 : Point n)} := by
    ext z; simp
  rw [hset]
  exact MeasureTheory.measure_singleton (0 : Point n)

/-! ### (M1) — ★★ the EXACT `hmeas` binder, carry-free, at FREE gate parameters. -/

/-- **★★ J4-601 (M1) — `curved_hmeas_at_gate`.**  The EXACT `hmeas` binder of
    `CurvedA1HAdom.curved_hInnerCont_of_two`, at FREE gate parameters `a b c` (pure measurability is
    radius-independent — the ∀-in-`a b c` shape instantiates at whatever ∃-parameters the consumer
    produces).  The ∀ᶠ is `Eventually.of_forall`-TRIVIAL: for EVERY `s : ℝ` the z-slice
    `z ↦ W (u−s) 0 z · L s z 0` is supported in the Lebesgue-null `{0}` (the singleton gate kills
    every `z ≠ 0` at every time), hence a.e. equal to the constant `0` and `AEStronglyMeasurable`.
    CARRY-FREE.  ⚠ See `curved_innerPairing_zero` for why this cheapness is a DEGENERACY finding.
    NOT `a₁ = R/6`. -/
theorem curved_hmeas_at_gate (κ : ℝ) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (a b c : ℝ) (U : Set ℝ) :
    ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
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
        (volume : Measure (Point n)) := by
  intro u _ s₀ _
  refine Filter.Eventually.of_forall (fun s => ?_)
  have h0 : AEStronglyMeasurable (fun _ : Point n => (0 : ℝ)) (volume : Measure (Point n)) :=
    aestronglyMeasurable_const
  refine h0.congr ?_
  filter_upwards [offOrigin_ae hn] with z hz
  rw [curved_gatedWitness_offOrigin_zero κ hChr a b c (u - s) hz, zero_mul]

/-! ### (M2) — ★★ the `hcont` binder, carry-free, by the same mechanism. -/

/-- **★★ J4-601 (M2) — `curved_hcont_at_gate`.**  The EXACT `hcont` binder of
    `curved_hInnerCont_of_two`, at FREE gate parameters: for a.e. `z` (all `z ≠ 0`) the time path
    `s ↦ W (u−s) 0 z · L s z 0` is IDENTICALLY `0` — the singleton-gated witness factor dies at
    every `s`, so the path is constant and `ContinuousAt` everywhere.  CARRY-FREE.  ⚠ Same
    degeneracy caveat as `curved_hmeas_at_gate`.  NOT `a₁ = R/6`. -/
theorem curved_hcont_at_gate (κ : ℝ) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (a b c : ℝ) (U : Set ℝ) :
    ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
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
                a b)) s z 0) s₀ := by
  intro u _ s₀ _
  filter_upwards [offOrigin_ae hn] with z hz
  have hfun : (fun s => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b
        (u - s) 0 z
      * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
            a b)) s z 0) = fun _ : ℝ => (0 : ℝ) := by
    funext s
    rw [curved_gatedWitness_offOrigin_zero κ hChr a b c (u - s) hz, zero_mul]
  rw [hfun]
  exact continuousAt_const

/-! ### (M3) — the reductions: `hInnerCont` from `hcont` only, and fully CLOSED. -/

/-- **★★ J4-601 (M3a) — `curved_hInnerCont_of_cont`.**  The capstone's carried `hInnerCont`
    conclusion for `g^K` at ∃ gate parameters, given ONLY the `hcont` carry at those parameters —
    `hmeas` is fed internally by `curved_hmeas_at_gate` (param-compatible by its ∀-in-`a b c`
    quantifier shape).  NOT `a₁ = R/6`. -/
theorem curved_hInnerCont_of_cont (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
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
      ((∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
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
  obtain ⟨a, b, c, ha, hab, hbc, himpl⟩ :=
    QIQTH.CurvedA1HAdom.curved_hInnerCont_of_two κ hκ hn hChr hw hu T hT U hUT
  exact ⟨a, b, c, ha, hab, hbc,
    fun hcont => himpl (curved_hmeas_at_gate κ hn hChr a b c U) hcont⟩

/-- **★★★ J4-601 (M3b) — `curved_hInnerCont_closed`.**  THE CLOSURE: the capstone's carried
    `hInnerCont` conclusion for `g^K = curvedRNCMetric κ` (`κ < 0`) with NO `hmeas`/`hcont` carry at
    all — both are fed internally (`curved_hmeas_at_gate` / `curved_hcont_at_gate`).  Only the
    mainline-standard labelled inputs {`hChr`, `hw`, `hu`} + window data remain.  ⚠⚠ READ
    `curved_innerPairing_zero` BEFORE crediting this: at the singleton-collapsed base compact the
    inner pairing is IDENTICALLY `0`, so this `ContinuousOn` is the continuity of the constant-0
    function — closed, true, and analytically EMPTY at this witness.  NOT `a₁ = R/6`. -/
theorem curved_hInnerCont_closed (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
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
        (Set.Ioo 0 u) := by
  obtain ⟨a, b, c, ha, hab, hbc, himpl⟩ :=
    QIQTH.CurvedA1HAdom.curved_hInnerCont_of_two κ hκ hn hChr hw hu T hT U hUT
  exact ⟨a, b, c, ha, hab, hbc,
    himpl (curved_hmeas_at_gate κ hn hChr a b c U) (curved_hcont_at_gate κ hn hChr a b c U)⟩

/-! ### (M4) — ⚠⚠ the ADVERSARIAL DEGENERACY PIN. -/

/-- **⚠⚠ J4-601 (M4) — `curved_innerPairing_zero` — THE DEGENERACY PIN.**  At the singleton base
    compact `hK = isCompact_singleton {0}` HARD-CODED by the J4-592→600 `hInnerCont` chain, the
    inner space-time pairing is IDENTICALLY ZERO: `∫ z, W (u−s) 0 z · L s z 0 = 0` for EVERY
    `s, u, a, b, c` (`n ≥ 1`) — the gated witness's source support is the Lebesgue-null `{0}`.
    Hence the `hInnerCont` conclusion (`curved_hInnerCont_closed`) is the continuity of the
    CONSTANT-0 function.  The same `K = {0}` source-collapse family as
    `CurvedA1FarConsumeCheck.witness_baseIntegral_zero` (cp466): there `hframeK` FORCED `K = {0}`;
    here it is pinned in the statement.  The genuine analytic content of an `hInnerCont` carrier
    lives only at a NON-collapsed base compact.  NOT `a₁ = R/6`. -/
theorem curved_innerPairing_zero (κ : ℝ) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (a b c u s : ℝ) :
    (∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b
        (u - s) 0 z
      * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
            a b)) s z 0) = 0 := by
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards [offOrigin_ae hn] with z hz
  rw [curved_gatedWitness_offOrigin_zero κ hChr a b c (u - s) hz, zero_mul]
  rfl

/-! ### (M5) — ★ the curvature gate (the METRIC is genuinely curved; the collapse is in the GATE). -/

/-- **★ J4-601 (M5) — `curved_hmeas_satisfiable`.**  For `κ < 0`, `n ≥ 2`, `g^K = curvedRNCMetric κ`
    is GENUINELY CURVED (`∃ w, 1 < det g^K w`) — the metric side is not secretly flat.  (The M4 pin
    shows the DEGENERACY is in the singleton gate support, not the metric.)  Re-exports
    `CurvedA1HAdom.curved_hAdom_satisfiable`.  NOT `a₁ = R/6`. -/
theorem curved_hmeas_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  QIQTH.CurvedA1HAdom.curved_hAdom_satisfiable κ hκ hn

end QIQTH.CurvedA1Hmeas

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1Hmeas

#print axioms curved_gatedWitness_offOrigin_zero
#print axioms curved_hmeas_at_gate
#print axioms curved_hcont_at_gate
#print axioms curved_hInnerCont_of_cont
#print axioms curved_hInnerCont_closed
#print axioms curved_innerPairing_zero
#print axioms curved_hmeas_satisfiable

end AxiomChecks
