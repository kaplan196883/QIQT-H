/-
  CurvedA1ClassBMeas6 — J4-565.  Close the Section-G error-kernel-DERIVATIVE ∫z-slice MEASURABILITY
  carrier `hF'meas_d` of the fully-wired curved a₁ two-jet capstone
  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` at the genuinely-curved witness
  `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges the Section-G MEASURABILITY census binder
  `hF'meas_d` — the s-slice ae-strong-measurability of the error-kernel-DERIVATIVE · leviSeries
  pairing
  `s ↦ ∫ z, deriv (fun r => vanVleckGatedWitness g^K gi^K … r 0 z) (u−s) · leviSeries … s z 0`
  on the `Lo` window `uIoc 0 (u − εₘ)` — for `g^K`, from the banked geometry-generic s-slice Fubini
  core `SliceMeasurability.sliceMeas_of_jointCont` (J4-383).  The first factor here is the
  τ-derivative of the RAW gated witness, `deriv (fun r => vanVleckGatedWitness … r 0 z) τ` (the
  error-kernel-derivative numerator), NOT the raw witness of `hMeasFII` (J4-564) nor the
  `witnessFieldDeriv2` of `hF'meas` (J4-563).  On the `Lo` window the shift `τ = u − s ∈ [εₘ, u)
  ⊆ (0,T]`, so the Fubini core applies DIRECTLY (no null-endpoint transfer), exactly as
  `hFmeas_slice`/`hmeas2Lo_slice`.  It does NOT make `a₁ = R/6` unconditional: the geometric
  residuals `hsrc`/`hOffCollarTail`, the convergence trio, the interval-integrability members
  `hFint`/`hFint_d` (which need a genuine DOMINATION, not measurability), the remaining Section-G
  ∫z-slice carrier `hFmeas_d` (with its unconstrained shift), the leviSeries joint slices
  (`hffro_meas`/`hfmov_meas`), and `hInnerCont` all remain owed.

  ## What is closed

  `hFpmeas_d_slice` — the geometry-generic Section-G ∫z-slice error-kernel-DERIVATIVE measurability
  supplier (the `deriv`-kernel analogue of `SliceMeasurability.hmeas2Lo_slice`), a direct
  instantiation of the banked Fubini core `sliceMeas_of_jointCont` at the τ-derivative first factor
  on the `Lo` window `uIoc 0 (u − εₘ)`.
  `curved_hFpmeas_d_at_gate` — its `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`,
  `S := constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c` instance, exactly the shape of the
  capstone binder `hF'meas_d`.

  ## Carried residuals (honest, curvature-independent analytic carries)

  Each member carries {`hUT`, `hεU`, `hFIIDerivCont`, `hBcont`}:
    • `hUT`, `hεU` — the window bounds `u ≤ T`, `epsSeq m ≤ u` (satisfiable window bookkeeping);
    • `hFIIDerivCont` — joint continuity of
      `(τ,z) ↦ deriv (fun r => vanVleckGatedWitness g^K gi^K … r 0 z) τ` on the positive-time strip
      `Ioc 0 T ×ˢ univ`  (the error-kernel-derivative numerator);
    • `hBcont` — joint continuity of the Levi-series factor on the strip.
  These are genuine analytic facts about the curved witness's τ-derivative on the positive-time
  strip, owed by the census and passed through here (not re-derived) — the exact measurability
  analogue of J4-564's carried {`hFIICont`, `hBcont`}.  They are NOT the `a₁` coefficient and NOT
  gate-smallness.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `Ric ≠ 0`)

  The member is a genuine `AEStronglyMeasurable` fact about a curved s-slice derivative integral,
  discharged from the banked Fubini core — NOT the capstone's conclusion, and NOT vacuous.  It holds
  at the genuinely-curved `g^K` (`κ < 0`, where `Ric(0) = n(n−1)κ ≠ 0`,
  `curvedRNCMetric_ricci_trace_diag_ne`, `curved_hFpmeas_d_at_gate_curved_satisfiable`); it does not
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

namespace QIQTH.CurvedA1ClassBMeas6

variable {n : ℕ}

/-! ###############################################################################
    ### GEOMETRY-GENERIC SECTION-G SLICE SUPPLIER — error-kernel-DERIVATIVE · leviSeries factor.
    ############################################################################### -/

/-- **★ `hFpmeas_d_slice` — the geometry-generic Section-G `hF'meas_d` supplier.**  s-slice
    ae-strong-measurability of the error-kernel-DERIVATIVE · leviSeries pairing
    `s ↦ ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u−s)
        · leviSeries … s z 0` on the `Lo` window `uIoc 0 (u − εₘ)`.  On this window the shift
    `τ = u − s ∈ [εₘ, u) ⊆ (0,T]`, so the banked Fubini core `sliceMeas_of_jointCont` applies
    directly (the τ-derivative analogue of `hmeas2Lo_slice`).  Honest carries:
    {`hUT`, `hεU`, `hFIIDerivCont`, `hBcont`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hFpmeas_d_slice (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hFIIDerivCont : ContinuousOn
      (fun p : ℝ × Point n =>
        deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 p.2) p.1)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m u hu
  have hεpos := epsSeq_pos m
  have hεu : epsSeq m ≤ u := hεU m u hu
  have huT : u ≤ T := hUT u hu
  have hIeq : Set.uIoc 0 (u - epsSeq m) = Set.Ioc 0 (u - epsSeq m) :=
    Set.uIoc_of_le (by linarith)
  rw [hIeq]
  have hmaps : ∀ s ∈ Set.Ioc (0 : ℝ) (u - epsSeq m), (0 : ℝ) < u - s ∧ u - s ≤ T := by
    intro s hs
    exact ⟨by linarith [hs.2, hεpos], by linarith [hs.1, huT]⟩
  have hsub : Set.Ioc (0 : ℝ) (u - epsSeq m) ⊆ Set.Ioc 0 T :=
    Set.Ioc_subset_Ioc_right (by linarith)
  exact sliceMeas_of_jointCont
    (fun τ z => deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) τ)
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    T u (Set.Ioc 0 (u - epsSeq m)) measurableSet_Ioc hmaps hsub hFIIDerivCont hBcont

/-! ###############################################################################
    ### AT-GATE INSTANCE — the exact capstone `hF'meas_d` binder shape at `g^K`.
    ############################################################################### -/

/-- **★ J4-565 — `curved_hFpmeas_d_at_gate`.**  The Section-G error-kernel-DERIVATIVE MEASURABILITY
    census binder `hF'meas_d` of `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the
    genuinely-curved witness `g^K = curvedRNCMetric κ`: for every `m` and `u ∈ U`, the s-slice map
    `s ↦ ∫ z, deriv (fun r => vanVleckGatedWitness g^K gi^K … r 0 z) (u−s) · leviSeries … s z 0` is
    `AEStronglyMeasurable` on `volume.restrict (uIoc 0 (u − εₘ))`.  Discharged from the banked
    geometry-generic Section-G derivative slice supplier `hFpmeas_d_slice`, instantiated at the
    curved metric.  The four supplier carries {`hUT`, `hεU`, `hFIIDerivCont`, `hBcont`} are carried
    honestly.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFpmeas_d_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c T : ℝ) (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hFIIDerivCont : ContinuousOn
      (fun p : ℝ × Point n =>
        deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 p.2) p.1)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ)
                hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (u - s)
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) :=
  hFpmeas_d_slice (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U hUT hεU hFIIDerivCont hBcont

/-- **★ J4-565 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the
    diagonal metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the
    Section-G error-kernel-DERIVATIVE s-slice measurability member is discharged at a genuinely
    curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.  NOT `a₁ = R/6`. -/
theorem curved_hFpmeas_d_at_gate_curved_satisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1ClassBMeas6

section AxiomChecks
open QIQTH.CurvedA1ClassBMeas6
#print axioms hFpmeas_d_slice
#print axioms curved_hFpmeas_d_at_gate
#print axioms curved_hFpmeas_d_at_gate_curved_satisfiable
end AxiomChecks
