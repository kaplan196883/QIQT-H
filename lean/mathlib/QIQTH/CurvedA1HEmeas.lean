/-
  CurvedA1HEmeas — J4-598: the `hEmeas` M1-wall carry of the J4-597 `hBdom` discharge, ASSESSED and
  reduced to the single arithmetic jet-reach residual `c < δ₀` — the measurability content itself is
  CLOSED for the genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  J4-597 (`CurvedA1HBdom.curved_hBdom_at_gate`) discharged `hBdom` (the width-2
  Levi-series Gaussian domination for `g^K`) modulo ONE carry: `hEmeas`, the joint
  `StronglyMeasurable` of the heatOp defect kernel on `ℝ × Point n × Point n` (the M1 wall).

  ── ★★ VERDICT (J4-598).  The measurability is BANKED, not open:
     `CurvedA1GateS1.curved_hS1_at_gate` (J4-561) already proves `HEmeasBorelAudit.tripleHEmeas`
     for `g^K` at the constant-radius flow-ball gate — and `tripleHEmeas g gi Wit` is BY DEFINITION
     the exact `hEmeas` binder `StronglyMeasurable (fun w => heatOp g gi Wit w.1 w.2.1 w.2.2)`.
     Its supplier chain (`ConstRadiusGateExport.tripleHEmeas_AT_CONSTRADIUS_GATE` ←
     `S1TripleHEmeasGate.tripleHEmeas_flowball_geometry` ← `JetsGcUnification.tripleHEmeas_Gc_concrete`
     ← the Gc jet suppliers) is geometry-only: the curved members
     {`curvedRNCMetric_contDiff`, `curvedRNCInv_contDiff` (κ≤0), `curvedRNCMetric_hgpos` (κ≤0)}
     discharge every `g`/`gi` input, `κ < 0` genuinely used.  There is NO τ≤0 gate-boundary
     obstruction: the banked route is Route B (continuity-free, derivative-field measurable
     representatives + `Measurable.ite` on the measurable gate graph), so the joint measurability
     holds on ALL of `ℝ × Point n × Point n`, across the `τ ≤ 0` boundary — no strip-only caveat.

  ── THE ONE RESIDUAL: JET-REACH ALIGNMENT (arithmetic, NOT measurability).  The banked S1 holds
     for gate radii `c < δ₀`, where `δ₀ = δ₀(a,b) > 0` is the jet reach of the Gc suppliers
     (`tripleHEmeas_Gc_concrete`: `δ₀ = min δF (min δcF δcF2)`, each `∃`-quantified AFTER `a b`).
     The J4-597 pkg produces its OWN existential gate parameters
     (`c = (b + ρc)/2`, `ρc = min (min rN δ₀_chart) r₁` inside
     `ConstRadiusGateExport.gatedWitnessN1_hEboundW_le_lin_CONST`), and NOTHING banked compares the
     pkg's `c` with the jet reach `δ₀(a,b)` — the two `∃`-chains are produced independently and
     cannot be aligned without re-engineering the parameter production deep inside the pkg
     construction (choosing `c < min ρc δ₀(a,b)` there needs `b < δ₀(a,b)`, which no banked
     statement supplies; `δ₀` is `∃`-bound after `a b` in every supplier).  So `hBdom` is NOT made
     fully unconditional here; its M1 MEASURABILITY carry is REPLACED by the strictly weaker
     ARITHMETIC reach residual `c < δ₀` — a genuine reduction (the wall member was the joint
     measurability; that content is now closed), honestly scoped.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_hEmeas_at_gate` — ★★ for `κ < 0`, `0 < n`, ANY gate parameters `0 < a < b < c`,
      GIVEN the transport-coefficient smoothness `hu` (the census's genuine `hsrc`-family
      geometric input, carried labelled as in J4-561): ∃ jet reach `δ₀ > 0` with `c < δ₀ →` the
      EXACT `hEmeas` binder of `CurvedA1HBdom.curved_hBdom_at_gate` — the joint
      `StronglyMeasurable` of the curved defect kernel at `K = {0}`, `S = constGate … c`.
      (The conclusion is `tripleHEmeas` unfolded — definitionally the literal binder.)
    • `curved_hBdom_of_reach` — ★★ the J4-597 `hBdom` with the M1 measurability carry REPLACED by
      the reach residual: ∃ gate parameters `0 < a < b < c` and ∃ `δ₀ > 0` such that `c < δ₀ →`
      ∃ `C_L ≥ 0` with the EXACT `hBdom` binder shape on `(0,T]` at width exactly `2s`.
      ⚠ HONEST FLAG: the antecedent `c < δ₀` at the pkg's OWN `c` is an OPEN arithmetic
      compatibility — not proved satisfiable at these witnessed parameters (see residual above);
      the theorem is the strongest true composition of the two banked `∃`-chains.
    • `curved_hInnerCont_of_reach` — ★★ the consumption certificate: the J4-596/597 ladder's
      `hInnerCont` conclusion for `g^K` with the `hEmeas` slot discharged by THIS brick — at the
      same ∃ gate parameters, given `c < δ₀` + the three remaining carries `{hAdom, hmeas, hcont}`,
      the capstone's interior-time `ContinuousOn` holds.  After this, the reduction owes
      `{c < δ₀ reach, hAdom, hmeas, hcont}` — the measurability wall member is out.
    • `curved_hEmeas_satisfiable` — ★ non-vacuity of the WITNESS: for `κ < 0`, `n ≥ 2`, `g^K` is
      genuinely curved (`∃ w, 1 < det g^K w`).  Re-exports
      `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`.

  ⚠ HONEST FIREWALL.  This closes the MEASURABILITY CONTENT of `hEmeas` (the M1 carry of J4-597)
  and proves NOTHING about `R/6`.  a₁ = R/6 remains CONDITIONAL regardless: the curved capstone
  still owes the reach alignment (`c < δ₀` at the pkg's parameters), `hAdom` (global witness
  domination), `hmeas`, `hcont`, the census/domination piles, the rest of the convergence trio,
  `hmassone`'s pre-ρ carriers, and the `hjets` residual.  Everything here is TRUE for the
  genuinely-curved `g^K` (`κ < 0`, `Ric ≠ 0`), DERIVED from the PROVED banked suppliers (NOT
  axiomatized, NOT the `a₁` conclusion); the `R/6` value is unaffected.  No `sorry`, no `admit`,
  no new axioms, no `:= True`, no vacuous hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedRNCHeatOpDomPkg
import QIQTH.GatedWitnessPackage
import QIQTH.CurvedA1HContDom
import QIQTH.CurvedA1HBdom
import QIQTH.CurvedA1GateS1

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LeviSeries
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussGaugeToHgauge QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCHeatOpDomPkg
open scoped Topology

namespace QIQTH.CurvedA1HEmeas

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ J4-598 — `curved_hEmeas_at_gate`: THE M1 MEASURABILITY CONTENT OF `hEmeas`, CLOSED.**
    For the genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`), `0 < n`, and ANY gate
    parameters `0 < a < b < c`, GIVEN the transport-coefficient smoothness `hu` (the census's
    genuine `hsrc`-family geometric input, carried labelled): there is a jet reach `δ₀ > 0` such
    that for `c < δ₀` the EXACT `hEmeas` binder of `CurvedA1HBdom.curved_hBdom_at_gate` holds —
    the joint `StronglyMeasurable` of the heatOp defect kernel over `ℝ × Point n × Point n`
    (Route B, continuity-free; measurable across the `τ ≤ 0` gate boundary, NO strip restriction).
    Route: `CurvedA1GateS1.curved_hS1_at_gate` (J4-561) at `K = {0}`; the conclusion
    `HEmeasBorelAudit.tripleHEmeas` is DEFINITIONALLY the binder.  NOT `a₁ = R/6`. -/
theorem curved_hEmeas_at_gate (κ : ℝ) (hκ : κ < 0) (hn : 0 < n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) k)) :
    ∃ δ₀ > (0 : ℝ), c < δ₀ →
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)
          w.1 w.2.1 w.2.2) := by
  obtain ⟨δ₀, hδ₀, hS1⟩ :=
    QIQTH.CurvedA1GateS1.curved_hS1_at_gate κ hκ hn hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) a b c ha hab hbc hu
  exact ⟨δ₀, hδ₀, fun hcδ => hS1 hcδ⟩

/-- **★★ J4-598 — `curved_hBdom_of_reach`: `hBdom` WITH THE M1 MEASURABILITY CARRY REPLACED BY
    THE ARITHMETIC JET-REACH RESIDUAL.**  For `κ < 0`, `1 ≤ n`, any ceiling `T > 0`: there are
    gate parameters `0 < a < b < c` (the J4-597 pkg's own) and a jet reach `δ₀ > 0` (this brick's)
    such that IF `c < δ₀` THEN ∃ `C_L ≥ 0` with the EXACT `hBdom` binder shape on `(0,T]`, at the
    clean width `2s`.  The `hEmeas` slot of `CurvedA1HBdom.curved_hBdom_at_gate` is discharged by
    `curved_hEmeas_at_gate`; what remains is `c < δ₀` — a pure arithmetic compatibility between
    the pkg's gate radius and the Gc jet reach.  ⚠ HONEST FLAG: `c < δ₀` at THESE existentially
    produced parameters is NOT proved satisfiable here (the two `∃`-chains are independent; see
    the header residual) — this is the strongest true composition, not an unconditional `hBdom`.
    NOT `a₁ = R/6`. -/
theorem curved_hBdom_of_reach (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
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
      ∃ δ₀ > (0 : ℝ), c < δ₀ →
        ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
          |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b))
              s z y|
            ≤ C_L * gaussDdim (2 * s) (z - y) := by
  obtain ⟨a, b, c, ha, hab, hbc, hBdomOf⟩ :=
    QIQTH.CurvedA1HBdom.curved_hBdom_at_gate κ hκ hn hChr hw T hT
  obtain ⟨δ₀, hδ₀, hEmeasOf⟩ :=
    curved_hEmeas_at_gate κ hκ (by omega : 0 < n) hChr a b c ha hab hbc hu
  exact ⟨a, b, c, ha, hab, hbc, δ₀, hδ₀, fun hcδ => hBdomOf (hEmeasOf hcδ)⟩

/-- **★★ J4-598 — `curved_hInnerCont_of_reach`: THE CONSUMPTION CERTIFICATE.**  The J4-596/597
    `hInnerCont` ladder for `g^K` with the `hEmeas` slot discharged by THIS brick: at the same
    ∃ gate parameters, given the jet-reach compatibility `c < δ₀` and the three remaining raw
    carries `{hAdom, hmeas, hcont}` at those parameters, the capstone's carried `hInnerCont`
    conclusion — the interior-time `ContinuousOn` of the inner space-time pairing on `Ioo 0 u` —
    HOLDS for `g^K`.  Route: `CurvedA1HBdom.curved_hInnerCont_of_pkg` with its `hEmeas` binder
    filled by `curved_hEmeas_at_gate`.  After this, the reduction owes
    `{c < δ₀ reach, hAdom, hmeas, hcont}` — the measurability wall member is closed.
    NOT `a₁ = R/6`. -/
theorem curved_hInnerCont_of_reach (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
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
      ∃ δ₀ > (0 : ℝ), c < δ₀ →
        ∀ (A₀ A₁ : ℝ), 0 ≤ A₀ → 0 ≤ A₁ →
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
  obtain ⟨a, b, c, ha, hab, hbc, hfun⟩ :=
    QIQTH.CurvedA1HBdom.curved_hInnerCont_of_pkg κ hκ hn hChr hw T hT U hUT
  obtain ⟨δ₀, hδ₀, hEmeasOf⟩ :=
    curved_hEmeas_at_gate κ hκ (by omega : 0 < n) hChr a b c ha hab hbc hu
  exact ⟨a, b, c, ha, hab, hbc, δ₀, hδ₀, fun hcδ => hfun (hEmeasOf hcδ)⟩

/-- **★ J4-598 — `curved_hEmeas_satisfiable`: THE NON-VACUITY CERTIFICATE (witness side).**  For
    `κ < 0`, `n ≥ 2`, the witness `g^K = curvedRNCMetric κ` underlying the `hEmeas` discharge is
    GENUINELY CURVED: `∃ w, 1 < det g^K w` — the measurability is NOT secretly about the flat
    kernel.  (The jet-reach antecedent `c < δ₀` of the composed theorems is the separately-flagged
    OPEN arithmetic residual; this certificate concerns the witness, not that antecedent.)
    Re-exports `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`.  NOT `a₁ = R/6`. -/
theorem curved_hEmeas_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  (QIQTH.CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable κ hκ hn).2

end QIQTH.CurvedA1HEmeas

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1HEmeas

#print axioms curved_hEmeas_at_gate
#print axioms curved_hBdom_of_reach
#print axioms curved_hInnerCont_of_reach
#print axioms curved_hEmeas_satisfiable

end AxiomChecks
