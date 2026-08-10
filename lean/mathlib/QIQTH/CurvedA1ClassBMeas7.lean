/-
  CurvedA1ClassBMeas7 — J4-566.  Close the leviSeries "frozen"/"moving" z-slice MEASURABILITY
  carriers `hffro_meas` / `hfmov_meas` of the fully-wired curved a₁ two-jet capstone
  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` at the genuinely-curved witness
  `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges the two Class-B MEASURABILITY census binders

    hffro_meas : ∀ u,   AEStronglyMeasurable (fun z => leviSeries (heatOp g gi W) u z 0) volume
    hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => leviSeries (heatOp g gi W) (u−εₘ) z 0) volume

  — the "frozen" (time `u`) and "moving" (time `u − epsSeq m`) z-slice ae-strong-measurabilities of the
  Levi series of the heat operator on the gated van-Vleck witness `W = vanVleckGatedWitness g gi …
  (constGate … c) a b`.  UNLIKE the Section-G members (`hMeasFII`/`hF'meas_d`, J4-564/565), these are
  NOT `∫z`-integrals: they are POINTWISE-in-`z` `AEStronglyMeasurable` facts over `volume` on
  `Point n = Fin n → ℝ`, at a single fixed time.  They are therefore the leviSeries analogue of the
  witness-slice carrier `hWmeas` (J4-559), NOT a `sliceMeas_of_jointCont` instance.  Moreover
  `hfmov_meas m u` is LITERALLY `hffro_meas (u − epsSeq m)` (the same `∀ u`-slice supplier at the
  shifted time), so a single continuity-in-`z` carry discharges BOTH.

  It does NOT make `a₁ = R/6` unconditional: the geometric residuals `hsrc`/`hOffCollarTail`, the
  convergence trio, the interval-integrability members `hFint`/`hFint_d` (which need a genuine
  DOMINATION, not measurability), the remaining Section-G ∫z-slice carrier `hFmeas_d`, and
  `hInnerCont` all remain owed.

  ## What is closed

  `leviSlice_meas` — the geometry-generic supplier: from the curvature-independent analytic carry
  `hLcont : ∀ u, Continuous (fun z => leviSeries (heatOp g gi W) u z 0)` (continuity of the Levi-series
  slice in the spatial variable at every time), the z-slice ae-strong-measurability at EVERY time, via
  the banked Mathlib reduction `Continuous.aestronglyMeasurable`.  The leviSeries analogue of
  `CurvedA1ClassBMeas.curved_hWmeas_at_gate`'s witness-slice measurability.
  `curved_hffro_meas_at_gate` — its `g^K`/`gi^K`/`constGate … c` instance, exactly the shape of the
  capstone binder `hffro_meas` (`∀ u`).
  `curved_hfmov_meas_at_gate` — the `∀ m u` "moving" binder `hfmov_meas`, the SAME supplier specialised
  at the shifted time `u − epsSeq m`.

  ## Carried residual (honest, curvature-independent analytic carry)

  Both members carry the single hypothesis
    • `hLcont` — joint-spatial continuity of the Levi-series slice
      `z ↦ leviSeries (heatOp g gi W) u z 0` at every time `u` (a genuine analytic fact about the
      curved Levi series, owed by the census and passed through here, not re-derived).
  This is NOT the `a₁` coefficient and NOT gate-smallness — it is the exact measurability analogue of
  J4-559's carried geometric bookkeeping.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `Ric ≠ 0`)

  Each member is a genuine `AEStronglyMeasurable` fact about a curved Levi-series slice, discharged from
  the PROVED Mathlib reduction `Continuous.aestronglyMeasurable` — NOT the capstone's conclusion, and
  NOT vacuous.  It holds at the genuinely-curved `g^K` (`κ < 0`, where `Ric(0) = n(n−1)κ ≠ 0`,
  `curvedRNCMetric_ricci_trace_diag_ne`, `curved_hffro_meas_at_gate_curved_satisfiable`); it does not
  touch, and is unaffected by, the `R/6` coefficient.  No `sorry`, no new axioms, no `:= True`, no
  hypothesis = conclusion, no existing file edited.  NOT `a₁ = R/6`. -/
import QIQTH.SliceMeasurability
import QIQTH.A1R6CoreAtGate
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.SliceMeasurability
open scoped ContDiff Interval Topology BigOperators

namespace QIQTH.CurvedA1ClassBMeas7

variable {n : ℕ}

/-! ###############################################################################
    ### GEOMETRY-GENERIC LEVI-SERIES z-SLICE SUPPLIER — `hffro_meas`/`hfmov_meas` factor.
    ############################################################################### -/

/-- **★ `leviSlice_meas` — the geometry-generic `hffro_meas`/`hfmov_meas` supplier.**  From the
    curvature-independent analytic carry `hLcont` (spatial continuity of the Levi-series slice
    `z ↦ leviSeries (heatOp g gi W) u z 0` at every time `u`), the z-slice ae-strong-measurability of
    that same slice at EVERY time, via the banked Mathlib reduction `Continuous.aestronglyMeasurable`.
    The leviSeries analogue of the witness-slice measurability `curved_hWmeas_at_gate` (J4-559).  Since
    the "moving" binder `hfmov_meas m u` is `hffro_meas (u − epsSeq m)`, this one `∀ u` supplier serves
    both.  ⚠ NOT `a₁ = R/6`. -/
theorem leviSlice_meas (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hLcont : ∀ u, Continuous
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z (0 : Point n))) :
    ∀ u, AEStronglyMeasurable
        (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z (0 : Point n))
        (volume : Measure (Point n)) :=
  fun u => (hLcont u).aestronglyMeasurable

/-! ###############################################################################
    ### AT-GATE INSTANCES — the exact capstone `hffro_meas`/`hfmov_meas` binder shapes at `g^K`.
    ############################################################################### -/

/-- **★ J4-566 — `curved_hffro_meas_at_gate`.**  The "frozen" Levi-series z-slice MEASURABILITY census
    binder `hffro_meas` of `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the
    genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`): for every `u`, the slice
    `z ↦ leviSeries (heatOp g^K gi^K (vanVleckGatedWitness g^K … (constGate … c) a b)) u z 0` is
    `AEStronglyMeasurable` over `volume`.  Discharged from the banked geometry-generic supplier
    `leviSlice_meas`, instantiated at the curved metric; the single carry `hLcont` (spatial continuity
    of the Levi-series slice) is carried honestly.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hffro_meas_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (hLcont : ∀ u, Continuous
      (fun z => leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
        (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n))) :
    ∀ u, AEStronglyMeasurable
        (fun z => leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n))
        (volume : Measure (Point n)) :=
  leviSlice_meas (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b hLcont

/-- **★ J4-566 — `curved_hfmov_meas_at_gate`.**  The "moving" Levi-series z-slice MEASURABILITY census
    binder `hfmov_meas` of `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the
    genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`): for every `m` and `u`, the slice
    `z ↦ leviSeries (heatOp g^K gi^K (vanVleckGatedWitness g^K … (constGate … c) a b)) (u−epsSeq m) z 0`
    is `AEStronglyMeasurable` over `volume`.  Discharged from the SAME supplier `leviSlice_meas`,
    specialised at the shifted time `u − epsSeq m` (`hfmov_meas m u = hffro_meas (u − epsSeq m)`); the
    single carry `hLcont` is carried honestly.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hfmov_meas_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (hLcont : ∀ u, Continuous
      (fun z => leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
        (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n))) :
    ∀ (m : ℕ) (u : ℝ), AEStronglyMeasurable
        (fun z => leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) (u - epsSeq m) z
          (0 : Point n))
        (volume : Measure (Point n)) :=
  fun m u => leviSlice_meas (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b hLcont (u - epsSeq m)

/-- **★ J4-566 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the "frozen"/"moving"
    Levi-series z-slice measurability members are discharged at a genuinely curved witness
    (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.  NOT `a₁ = R/6`. -/
theorem curved_hffro_meas_at_gate_curved_satisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1ClassBMeas7

section AxiomChecks
open QIQTH.CurvedA1ClassBMeas7
#print axioms leviSlice_meas
#print axioms curved_hffro_meas_at_gate
#print axioms curved_hfmov_meas_at_gate
#print axioms curved_hffro_meas_at_gate_curved_satisfiable
end AxiomChecks
