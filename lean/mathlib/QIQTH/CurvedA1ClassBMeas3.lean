/-
  CurvedA1ClassBMeas3 — J4-562.  Close the s-slice ∫z-convolution MEASURABILITY family
  {`hmeasLo`, `hmeasHi`, `hmeas2Lo`} of the fully-wired curved a₁ two-jet capstone
  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` at the genuinely-curved witness
  `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges THREE mechanical MEASURABILITY census
  binders — the s-slice ae-strong-measurability of the `heatOp · leviSeries` pairing on the `Lo`/`Hi`
  windows (`hmeasLo`/`hmeasHi`) and of the `witnessSecondXDeriv · leviSeries` pairing on the `Lo`
  window (`hmeas2Lo`) — for `g^K`, from the banked geometry-generic s-slice supplier
  `SliceMeasurability.{hmeasLo_slice, hmeasHi_slice, hmeas2Lo_slice}` (J4-383).  It does NOT make
  `a₁ = R/6` unconditional: the geometric residuals `hsrc`/`hOffCollarTail`, the convergence trio,
  and the rest of the census (the W2 diff-under-∫ family `hFmeas`/`hFint`/`hF'meas`, Section-G
  `hMeasFII`/`hFmeas_d`/`hFint_d`/`hF'meas_d`, the leviSeries joint slices, `hInnerCont`) all remain
  owed.

  ## What is closed

  `curved_hmeasLo_at_gate`, `curved_hmeasHi_at_gate`, `curved_hmeas2Lo_at_gate` — the EXACT shapes of
  the capstone binders `hmeasLo`, `hmeasHi`, `hmeas2Lo` at `g := curvedRNCMetric κ`,
  `gi := curvedRNCInv κ`, `S := constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c`.  Each is the
  literal instantiation of the geometry-generic banked supplier at the curved metric — the supplier's
  `g gi hChr hK S a b` slot filled by the curved data, so the supplier's conclusion closes the binder
  verbatim.  The supplier route is the SFinite product-marginal Fubini measurability
  (`InnerMeasFubini.innerIntegral_aesm`) fed by two joint-continuity data on the positive-time strip.

  ## Carried residuals (honest, curvature-independent analytic carries)

  Each member carries the four supplier carries {`hUT`, `hεU`, `hHeatCont`/`hSecCont`, `hBcont`}:
    • `hUT`, `hεU` — the window bounds `u ≤ T`, `epsSeq m ≤ u` (satisfiable window bookkeeping);
    • `hHeatCont` — joint continuity of `(τ,z) ↦ heatOp g^K gi^K (vanVleckGatedWitness …) τ 0 z` on the
      positive-time strip `Ioc 0 T ×ˢ univ`  (for `hmeasLo`/`hmeasHi`);
    • `hSecCont` — joint continuity of `(τ,z) ↦ witnessSecondXDeriv g^K gi^K … i τ z` on the strip,
      per `i`  (for `hmeas2Lo`);
    • `hBcont` — joint continuity of the Levi-series factor on the strip.
  These are genuine analytic facts about the curved witness on the positive-time strip, owed by the
  census and passed through here (not re-derived) — the measurability analogue of J4-559's carried
  {`hSm`, `hVmap`}.  They are NOT the `a₁` coefficient and NOT gate-smallness.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `Ric ≠ 0`)

  Each member is a genuine `AEStronglyMeasurable` fact about a curved s-slice integral, discharged from
  a banked supplier — NOT the capstone's conclusion, and NOT vacuous.  They hold at the genuinely-curved
  `g^K` (`κ < 0`, where `Ric(0) = n(n−1)κ ≠ 0`, `curvedRNCMetric_ricci_trace_diag_ne`,
  `curved_hmeasLo_at_gate_curved_satisfiable`); they do not touch, and are unaffected by, the `R/6`
  coefficient.  No `sorry`, no new axioms, no `:= True`, no hypothesis = conclusion, no existing file
  edited.  NOT `a₁ = R/6`. -/
import QIQTH.SliceMeasurability
import QIQTH.A1R6CoreAtGate
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.SliceMeasurability
open scoped ContDiff Interval Topology BigOperators

namespace QIQTH.CurvedA1ClassBMeas3

variable {n : ℕ}

/-- **★ J4-562 — `curved_hmeasLo_at_gate`.**  The MEASURABILITY census binder `hmeasLo` of
    `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the genuinely-curved witness
    `g^K = curvedRNCMetric κ`: for every `m` and every `u ∈ U`, the s-slice map
    `s ↦ ∫ z, heatOp g^K gi^K (vanVleckGatedWitness …) (u−s) 0 z · leviSeries … s z 0` is
    `AEStronglyMeasurable` on `volume.restrict (uIoc 0 (u − εₘ))`.  Discharged from the banked
    geometry-generic s-slice supplier `SliceMeasurability.hmeasLo_slice`, instantiated at the curved
    metric.  The four supplier carries {`hUT`, `hεU`, `hHeatCont`, `hBcont`} are carried honestly.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hmeasLo_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c T : ℝ) (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hHeatCont : ContinuousOn
      (fun p : ℝ × Point n =>
        heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) p.1 0 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) :=
  hmeasLo_slice (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U hUT hεU hHeatCont hBcont

/-- **★ J4-562 — `curved_hmeasHi_at_gate`.**  The MEASURABILITY census binder `hmeasHi` of
    `curved_a1_R6_fully_wired`, at `g^K = curvedRNCMetric κ`: the same `heatOp · leviSeries` s-slice map
    is `AEStronglyMeasurable` on the `Hi` window `volume.restrict (uIoc (u − εₘ) u)`.  Discharged from
    `SliceMeasurability.hmeasHi_slice` (which handles the single null endpoint `s = u` by an
    `Ioo → Ioc` transfer) instantiated at the curved metric.  Carries {`hUT`, `hεU`, `hHeatCont`,
    `hBcont`} honestly.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hmeasHi_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c T : ℝ) (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hHeatCont : ContinuousOn
      (fun p : ℝ × Point n =>
        heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) p.1 0 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)) :=
  hmeasHi_slice (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U hUT hεU hHeatCont hBcont

/-- **★ J4-562 — `curved_hmeas2Lo_at_gate`.**  The MEASURABILITY census binder `hmeas2Lo` of
    `curved_a1_R6_fully_wired`, at `g^K = curvedRNCMetric κ`: for every `m`, `i` and `u ∈ U`, the
    s-slice map `s ↦ ∫ z, witnessSecondXDeriv g^K gi^K … i (u−s) z · leviSeries … s z 0` is
    `AEStronglyMeasurable` on `volume.restrict (uIoc 0 (u − εₘ))`.  Discharged from
    `SliceMeasurability.hmeas2Lo_slice` instantiated at the curved metric.  Carries {`hUT`, `hεU`,
    `hSecCont`, `hBcont`} honestly (the per-`i` second-`x`-derivative continuity replaces `hHeatCont`).
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hmeas2Lo_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c T : ℝ) (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) :=
  hmeas2Lo_slice (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U hUT hεU hSecCont hBcont

/-- **★ J4-562 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the three s-slice
    measurability members are discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat
    `δ`.  NOT `a₁ = R/6`. -/
theorem curved_hmeasLo_at_gate_curved_satisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1ClassBMeas3

section AxiomChecks
open QIQTH.CurvedA1ClassBMeas3
#print axioms curved_hmeasLo_at_gate
#print axioms curved_hmeasHi_at_gate
#print axioms curved_hmeas2Lo_at_gate
#print axioms curved_hmeasLo_at_gate_curved_satisfiable
end AxiomChecks
