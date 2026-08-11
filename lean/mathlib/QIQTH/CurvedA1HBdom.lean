/-
  CurvedA1HBdom — J4-597: discharging (modulo the single M1 measurability carry) `hBdom`, the
  width-2 Levi-series Gaussian domination for the genuinely-curved witness `g^K` — the exposed
  bottleneck of the J4-596 `hContDom`/`hInnerCont` reduction and the D2 convergence-trio frontier.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  J4-596 (`CurvedA1HContDom.curved_hInnerCont_of_dominations`) reduced the carried
  `hInnerCont` binder of the non-vacuous center-gauge curved a₁ = R/6 capstone ALL THE WAY to the
  four raw carries `{hAdom, hBdom, hmeas, hcont}` for `g^K = curvedRNCMetric κ`.  Of these, `hBdom`
  — the width-2 Levi domination
      `∀ s ∈ (0,T], ∀ z y, |leviSeries (heatOp g^K gi^K W) s z y| ≤ C_L · gaussDdim (2s) (z−y)`
  (`W` the gated van-Vleck parametrix witness on the constant-radius flow-ball gate) — was the
  explicitly-flagged frontier: `ConcreteDominations` — "NOT attempted: (D2) the Levi-series
  domination".  THIS brick assembles it from banked machinery.

  ── ★★ VERDICT (J4-597).  The banked pieces COMPOSE, at the pkg's own gate parameters, with NO
     width slippage and NO cap:
       • `CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg` (J4-536) — the CLEAN (uncapped) all-`t'`
         width-2 defect bound `|heatOp g^K gi^K W τ p q| ≤ (C·(1+t'))·baseKernelW 2 0 τ p q`, for
         ∃ gate parameters `0 < a < b < c`;
       • `HeatResidualBound.iterConvIntegrableW_of_locally_bound_baseMeas` (J4-109) — the per-step
         integrability family `hInt` from `hEzero` (banked:
         `heatOp_gatedWitnessN1_eq_zero_of_nonpos`, needs `1 ≤ n`) + the ONE genuine measurability
         `hEmeas` (joint `StronglyMeasurable` of the defect kernel — the M1 wall) + the local bound;
       • `HeatResidualBound.leviSeries_dominatedW_le` (J4-114 D2 engine) — `|leviSeries E| ≤
         C_L·baseKernelW 2 0` on `(0,T]`, `C_L = ∑' C^(k+1)·modelCoeff 0 T (k+1)` finite by the
         Γ/factorial decay.  WIDTH BOOKKEEPING: the engine's iterated majorant `iterKernelW 2 0 k`
         FACTORS (`iterKernelW_eq`) as `modelCoeff 0 τ k · gaussDdim (2τ)` — the Gaussian width
         stays EXACTLY 2 at every Duhamel iterate (the Levi/Friedman fixed-width phenomenon: the
         `k`-dependence is absorbed into the factorially-decaying scalar `modelCoeff`, not the
         width), so the series bound is at width `2s` — the EXACT `hBdom` width, no widening;
       • `ParametrixHEboundWiring.baseKernelW_zero_apply` — `baseKernelW 2 0 s z y =
         gaussDdim (2s) (z−y)`, the literal `hBdom` right-hand side.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_hBdom_at_gate` — ★★ for `κ < 0`, `1 ≤ n`, any ceiling `T > 0`: ∃ gate parameters
      `0 < a < b < c` such that, GIVEN the single joint strong measurability `hEmeas` of the defect
      kernel (the honest M1 carry), ∃ `C_L ≥ 0` with the EXACT `hBdom` binder shape of
      `CurvedA1HContDom.curved_hContDom_at_gate` at `K = {0}`:
          `∀ s, 0 < s → s ≤ T → ∀ z y, |leviSeries (heatOp g^K gi^K W) s z y|
             ≤ C_L · gaussDdim (2·s) (z − y)`.
      The bound is CLEAN (no `min`-cap) and at the CLEAN width 2 — no width lie.
    • `curved_hInnerCont_of_pkg` — ★★ the CONSUMPTION certificate: the produced `hBdom` genuinely
      fills the J4-596 builder's slot.  At the same ∃ gate parameters, given `hEmeas` + the three
      remaining carries `{hAdom, hmeas, hcont}` at those parameters, the capstone's `hInnerCont`
      `ContinuousOn` conclusion HOLDS for `g^K` — via
      `CurvedA1HContDom.curved_hInnerCont_of_dominations` with the `hBdom` slot supplied HERE.
    • `curved_hBdom_satisfiable` — ★ non-vacuity: for `κ < 0`, `n ≥ 2`, `g^K` is genuinely curved
      (`∃ w, 1 < det g^K w`).  Re-exports `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`.

  ── HONEST RESIDUAL (what is NOT discharged).  The ONE remaining hypothesis of the produced
     `hBdom` is `hEmeas` — the joint `StronglyMeasurable` of the curved defect kernel at the pkg's
     gate (the M1 wall).  The banked suppliers (`ChartJetHessianMixed.tripleHEmeas_concrete`,
     `GatedRepSFix.tripleHEmeas_concrete_v4`) each still carry their measurable-supplier data
     blocks (`hcarTau`/`hcarField`/`hcarField2`), so wiring `hEmeas` unconditionally is a SEPARATE
     thread — NOT pretended closed here.  Also: the gate parameters `a b c` are EXISTENTIAL (the
     pkg's own), not universal — the J4-596 builder consumes them fine (its `a b c T` are free),
     as `curved_hInnerCont_of_pkg` PROVES, but `hBdom` at arbitrary user-chosen gate parameters is
     not claimed.  `hAdom` (global all-`p,q` witness domination), `hmeas`, `hcont` remain carried.

  ⚠ HONEST FIREWALL.  This attacks `hBdom`, one of the four raw carries of the reduced
  `hInnerCont`, and the D2/convergence-trio frontier; it proves NOTHING about `R/6`.  a₁ = R/6
  remains CONDITIONAL regardless: the curved capstone still owes `hEmeas` (here), `hAdom`, `hmeas`,
  `hcont`, the census/measurability/domination piles, the rest of the convergence trio,
  `hmassone`'s pre-ρ carriers, and the `hjets` residual.  Everything here is TRUE for the
  genuinely-curved `g^K` (`κ < 0`, `Ric ≠ 0`), DERIVED from the PROVED pkg + engine (NOT
  axiomatized, NOT the `a₁` conclusion); the `R/6` value is unaffected.  No `sorry`, no `admit`,
  no new axioms, no `:= True`, no vacuous hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedRNCHeatOpDomPkg
import QIQTH.GatedWitnessPackage
import QIQTH.CurvedA1HContDom

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LeviSeries
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussGaugeToHgauge QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCHeatOpDomPkg
open scoped Topology

namespace QIQTH.CurvedA1HBdom

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ J4-597 — `curved_hBdom_at_gate`: THE WIDTH-2 LEVI DOMINATION FOR `g^K`, MODULO THE SINGLE
    M1 MEASURABILITY CARRY.**  For the genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`),
    `1 ≤ n`, and any ceiling `T > 0`: there are gate parameters `0 < a < b < c` such that, GIVEN
    the joint strong measurability `hEmeas` of the heatOp defect kernel (the honest M1 wall — the
    ONE remaining hypothesis), there is `C_L ≥ 0` with the EXACT `hBdom` binder shape consumed by
    `CurvedA1HContDom.curved_hContDom_at_gate` at `K = {0}`:
        `∀ s, 0 < s → s ≤ T → ∀ z y, |leviSeries (heatOp g^K gi^K W) s z y|
           ≤ C_L · gaussDdim (2·s) (z − y)`.
    Route: `curvedRNC_heatOp_dom_pkg` (the CLEAN uncapped all-`t'` width-2 defect bound) →
    `iterConvIntegrableW_of_locally_bound_baseMeas` (`hInt`, with `hEzero` banked via
    `heatOp_gatedWitnessN1_eq_zero_of_nonpos`) → `leviSeries_dominatedW_le` (the D2 engine; the
    iterated majorants stay at width EXACTLY 2, the `k`-growth absorbed into the factorially-
    decaying `modelCoeff` scalars) → `baseKernelW_zero_apply`.  The bound is CLEAN (no cap) and at
    the CLEAN width 2 (no widening).  NOT `a₁ = R/6`. -/
theorem curved_hBdom_at_gate (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (T : ℝ) (hT : 0 < T) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      (StronglyMeasurable (fun w : ℝ × Point n × Point n =>
          heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)
            w.1 w.2.1 w.2.2) →
        ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
          |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b))
              s z y|
            ≤ C_L * gaussDdim (2 * s) (z - y)) := by
  classical
  obtain ⟨a, b, C, c, ha, hab, hC0, hbc, hpkg, -⟩ :=
    curvedRNC_heatOp_dom_pkg κ hκ hChr hw T
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  intro hEmeas
  -- `hEzero`: the defect kernel vanishes at nonpositive time (banked; `vanVleckGatedWitness`
  -- unfolds definitionally to the `gatedKernel` form the banked lemma is phrased against).
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
  -- `hInt`: the per-step integrability family, from `hEzero` + `hEmeas` + the local pkg bound.
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
  -- the D2 engine: the width-2 Levi-series domination on `(0,T]`.
  obtain ⟨C_L, hCL0, hdom⟩ :=
    leviSeries_dominatedW_le _ (C * (1 + T)) T (mul_nonneg hC0 (by linarith)) hT
      (fun τ p q hτ hτT => hpkg T τ p q hτ hτT) hInt
  refine ⟨C_L, hCL0, fun s hs hsT z y => ?_⟩
  have h := hdom s z y hs hsT
  rwa [baseKernelW_zero_apply] at h

/-- **★★ J4-597 — `curved_hInnerCont_of_pkg`: THE CONSUMPTION CERTIFICATE.**  The `hBdom` produced
    by `curved_hBdom_at_gate` GENUINELY FILLS the `hBdom` slot of the J4-596 builder: at the same
    ∃ gate parameters `a b c`, given the M1 carry `hEmeas` and the three remaining raw carries
    `{hAdom, hmeas, hcont}` at those parameters, the capstone's carried `hInnerCont` conclusion —
    the interior-time `ContinuousOn` of the inner space-time pairing on `Ioo 0 u` — HOLDS for
    `g^K`, via `CurvedA1HContDom.curved_hInnerCont_of_dominations` (J4-596) with the `hBdom` slot
    supplied by THIS brick.  After this, the `hInnerCont` reduction owes `{hEmeas, hAdom, hmeas,
    hcont}` — the `hBdom` slot is closed.  NOT `a₁ = R/6`. -/
theorem curved_hInnerCont_of_pkg (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      ∀ (_ : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
          heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)
            w.1 w.2.1 w.2.2))
        (A₀ A₁ : ℝ), 0 ≤ A₀ → 0 ≤ A₁ →
        (∀ τ, 0 < τ → ∀ p q : Point n,
          |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b τ p q|
            ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) →
        (∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
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
          (Set.Ioo 0 u) := by
  classical
  obtain ⟨a, b, c, ha, hab, hbc, hBdomOf⟩ := curved_hBdom_at_gate κ hκ hn hChr hw T hT
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  intro hEmeas A₀ A₁ hA₀ hA₁ hAdom hmeas hcont
  obtain ⟨C_L, hCL0, hBdom⟩ := hBdomOf hEmeas
  exact QIQTH.CurvedA1HContDom.curved_hInnerCont_of_dominations κ hChr
    ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) a b c T U hUT
    A₀ A₁ C_L hA₀ hA₁ hCL0 hAdom hBdom hmeas hcont

/-- **★ J4-597 — `curved_hBdom_satisfiable`: THE NON-VACUITY CERTIFICATE.**  For `κ < 0`, `n ≥ 2`,
    the witness `g^K = curvedRNCMetric κ` underlying the `hBdom` discharge is GENUINELY CURVED:
    `∃ w, 1 < det g^K w` — the domination is NOT secretly about the flat kernel.  Re-exports
    `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`.  NOT `a₁ = R/6`. -/
theorem curved_hBdom_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  (QIQTH.CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable κ hκ hn).2

end QIQTH.CurvedA1HBdom

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1HBdom

#print axioms curved_hBdom_at_gate
#print axioms curved_hInnerCont_of_pkg
#print axioms curved_hBdom_satisfiable

end AxiomChecks
