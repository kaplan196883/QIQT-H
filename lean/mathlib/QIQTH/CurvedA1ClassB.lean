/-
  CurvedA1ClassB — J4-558.  Close the thinnest genuinely-closable Class-B census member of the
  fully-wired curved a₁ two-jet capstone `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`
  at the genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges ONE mechanical Class-B census binder — the
  gate-centre membership `hmemS0` — for `g^K` from a banked geometry-only supplier.  It does NOT make
  `a₁ = R/6` unconditional: the geometric residuals `hsrc`/`hOffCollarTail`, the rest of the
  convergence trio, and the remaining measurability/gate census (`hopenS0` needs the chart-reach
  smallness `c < δ₀`, `hS1`, …) all remain owed.

  ## What is closed

  `curved_hmemS0_at_gate` — the exact shape of the capstone binder
    `hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0`
  produced, for ANY `c > 0`, by the banked geometry-only fact
  `ConcreteGateInstantiation.hS0_concrete` (`φ_0 0 = 0` via `uniformFlowExp_zero`, `0 < c`, `0 ∈ K`).
  Since `constGate g gi hChr hK c 0` unfolds definitionally to
  `uniformFlowExp g gi hChr hK 0 '' Metric.ball 0 c`, this is a pure interface rethread — no new math.

  `curved_hmemS0_at_gate_of_lt` — the SAME fact wired to the capstone's actual parameter block: the
  capstone binds `a b c` with `ha : 0 < a`, `hab : a < b`, `hbc : b < c`, so `0 < c` and the binder
  discharges outright.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `K ≠ 0`)

  The member is a genuine membership fact (the gate `constGate … c 0` is a nonempty open flow-ball
  image, and `0` is its centre), discharged from a banked supplier — NOT the capstone's conclusion,
  and NOT vacuous.  It holds at the genuinely-curved `g^K` (`κ < 0`, where `Ric(0) = n(n−1)κ ≠ 0`,
  `curvedRNCMetric_ricci_trace_diag_ne`); it does not touch, and is unaffected by, the `R/6`
  coefficient.  No `sorry`, no new axioms, no `:= True`, no hypothesis = conclusion, no existing file
  edited.  NOT `a₁ = R/6`. -/
import QIQTH.ConcreteGateInstantiation
import QIQTH.A1R6CoreAtGate
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle

open QIQTH.Curvature QIQTH.A1R6CoreAtGate QIQTH.ConcreteGateInstantiation
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open scoped ContDiff

namespace QIQTH.CurvedA1ClassB

variable {n : ℕ}

/-- **★ J4-558 — `curved_hmemS0_at_gate`.**  The Class-B census binder `hmemS0` of
    `curved_a1_R6_fully_wired`, at the genuinely-curved witness `g^K = curvedRNCMetric κ`, discharged
    from the banked geometry-only fact `ConcreteGateInstantiation.hS0_concrete` (`φ_0 0 = 0` via
    `uniformFlowExp_zero`).  Holds for ANY `c > 0`; `constGate … c 0` is defeq to
    `uniformFlowExp … 0 '' Metric.ball 0 c`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hmemS0_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) (hc0 : 0 < c) :
    (0 : Point n) ∈ K →
      (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0 :=
  fun h0 => hS0_concrete (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK h0 c hc0

/-- **★ J4-558 — `curved_hmemS0_at_gate_of_lt`.**  The same binder wired to the capstone's actual
    parameter block: the capstone binds `a b c` with `0 < a`, `a < b`, `b < c`, so `0 < c` and the
    `hmemS0` binder of `curved_a1_R6_fully_wired` discharges outright.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hmemS0_at_gate_of_lt (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    (0 : Point n) ∈ K →
      (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0 :=
  curved_hmemS0_at_gate κ hChr hK c (lt_trans (lt_trans ha hab) hbc)

end QIQTH.CurvedA1ClassB

section AxiomChecks
open QIQTH.CurvedA1ClassB
#print axioms curved_hmemS0_at_gate
#print axioms curved_hmemS0_at_gate_of_lt
end AxiomChecks
