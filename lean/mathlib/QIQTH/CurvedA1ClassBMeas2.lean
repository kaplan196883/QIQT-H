/-
  CurvedA1ClassBMeas2 — J4-560.  Close the next thinnest genuinely-closable Class-B census member of
  the fully-wired curved a₁ two-jet capstone `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`
  at the genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges ONE mechanical Class-B census binder — the
  gate-centre OPENNESS `hopenS0` — for `g^K` from a banked geometry-only supplier.  It does NOT make
  `a₁ = R/6` unconditional: the geometric residuals `hsrc`/`hOffCollarTail`, the convergence trio, and
  the rest of the measurability/gate census (`hS1`, `hmeasLo`/`hmeasHi`/`hmeas2Lo`, the W2 diff-under-∫
  family `hFmeas`/`hFint`/`hF'meas`, Section-G `hMeasFII`/`hFmeas_d`, …) all remain owed.

  ## What is closed

  `curved_hopenS0_at_gate` — the EXACT shape of the capstone binder
    `hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0)`
  produced, for `g^K = curvedRNCMetric κ`, from the banked geometry-only gate-radius floor
  `CompactTubeLemma.flowBall_gateRadius_floor` (a thin re-exposure of
  `ConcreteGateAssembly.reachableGate_concrete`, itself the quantitative inverse-function
  `ApproximatesLinearOn` chart spec).  That supplier gives a UNIFORM reach `c₀ > 0` such that for every
  radius `0 < c < c₀` and every base `z ∈ K` the flow-ball gate `uniformFlowExp g^K gi^K hChr hK z ''
  Metric.ball 0 c` is open.  Since `constGate g^K gi^K hChr hK c 0` unfolds definitionally to
  `uniformFlowExp g^K gi^K hChr hK 0 '' Metric.ball 0 c`, taking the base `z = 0 ∈ K` gives the exact
  binder.  The supplier needs ONLY the christoffel smoothness `hChr` and the base compactness `hK` — NO
  transport-coefficient smoothness, NO metric `ContDiff`, NO det-positivity — so `κ` is unconstrained
  (works for every `κ`, in particular the genuinely curved `κ < 0`).

  ## Carried residual (honest)

  The gate-smallness `0 < c < c₀` (the chart-reach floor `c < δ₀`) is carried honestly as the
  conclusion's antecedent: the openness of the flow-ball image is a LOCAL fact valid only within the
  chart reach.  ⚠ This CHANGES/CONSTRAINS the gate parameter `c`: the fully-wired capstone binds
  `a b c` with `0 < a < b < c` but supplies NO upper bound `c < c₀`, so `hopenS0` cannot be discharged
  at the capstone's arbitrary `c`.  Choosing a small gate `c ∈ (b, c₀)` (a legitimate base-point / gate
  choice) is exactly what closes it; the curvature-independent floor `c₀` is exposed here as an `∃`.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `Ric ≠ 0`)

  The member is a genuine OPENNESS fact (the gate `constGate … c 0` is a nonempty flow-ball image and,
  for `0 < c < c₀`, an open set), discharged from a banked supplier — NOT the capstone's conclusion,
  and NOT vacuous.  It holds at the genuinely-curved `g^K` (`κ < 0`, where `Ric(0) = n(n−1)κ ≠ 0`,
  `curvedRNCMetric_ricci_trace_diag_ne`, `curved_hopenS0_at_gate_curved_satisfiable`); it does not
  touch, and is unaffected by, the `R/6` coefficient.  No `sorry`, no new axioms, no `:= True`, no
  hypothesis = conclusion, no existing file edited.  NOT `a₁ = R/6`. -/
import QIQTH.CompactTubeLemma
import QIQTH.A1R6CoreAtGate
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle

open QIQTH.Curvature QIQTH.A1R6CoreAtGate QIQTH.CompactTubeLemma
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open scoped ContDiff

namespace QIQTH.CurvedA1ClassBMeas2

variable {n : ℕ}

/-- **★ J4-560 — `curved_hopenS0_at_gate`.**  The Class-B census binder `hopenS0` of
    `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the genuinely-curved witness
    `g^K = curvedRNCMetric κ`: there is a uniform chart reach `c₀ > 0` such that for every gate radius
    `0 < c < c₀` the gate centre is open, i.e. `(0 : Point n) ∈ K → IsOpen (constGate (curvedRNCMetric κ)
    (curvedRNCInv κ) hChr hK c 0)`.  Discharged from the banked geometry-only gate-radius floor
    `CompactTubeLemma.flowBall_gateRadius_floor` (`= ConcreteGateAssembly.reachableGate_concrete`),
    taking the base `z = 0`.  `constGate … c 0` is defeq to `uniformFlowExp … 0 '' Metric.ball 0 c`.
    Needs ONLY `hChr` + `hK` — no transport smoothness, no metric `ContDiff`, no det-positivity — so
    `κ` is unconstrained.  The gate-smallness `0 < c < c₀` is carried honestly as an antecedent.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hopenS0_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ c₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < c₀ →
      ((0 : Point n) ∈ K →
        IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0)) := by
  obtain ⟨c₀, hc₀, hspec⟩ :=
    flowBall_gateRadius_floor (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
  exact ⟨c₀, hc₀, fun c hc0 hcc0 h0 => (hspec c hc0 hcc0 0 h0).1⟩

/-- **★ J4-560 — `curved_hopenS0_at_gate_of_lt`.**  The same binder wired to the capstone's actual
    parameter block plus the honest gate-smallness `c < c₀`: given `0 < a`, `a < b`, `b < c` (so the
    gate radius `c` is positive) and `c < c₀` (the chart reach), the `hopenS0` binder of
    `curved_a1_R6_fully_wired` discharges outright.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hopenS0_at_gate_of_lt (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    ∃ c₀ > (0 : ℝ), c < c₀ →
      ((0 : Point n) ∈ K →
        IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0)) := by
  obtain ⟨c₀, hc₀, hspec⟩ := curved_hopenS0_at_gate κ hChr hK
  exact ⟨c₀, hc₀, fun hcc0 => hspec c (lt_trans (lt_trans ha hab) hbc) hcc0⟩

/-- **★ J4-560 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `K ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric K` is nonzero, so `hopenS0` is discharged
    at a genuinely curved witness (`K < 0 ⊂ K ≠ 0`), NOT the flat `δ`.  NOT `a₁ = R/6`. -/
theorem curved_hopenS0_at_gate_curved_satisfiable (K : ℝ) (hK : K ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) K y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne K hK hn c

end QIQTH.CurvedA1ClassBMeas2

section AxiomChecks
open QIQTH.CurvedA1ClassBMeas2
#print axioms curved_hopenS0_at_gate
#print axioms curved_hopenS0_at_gate_of_lt
#print axioms curved_hopenS0_at_gate_curved_satisfiable
end AxiomChecks
