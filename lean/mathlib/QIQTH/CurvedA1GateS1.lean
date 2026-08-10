/-
  CurvedA1GateS1 — J4-561.  Close the const-radius GATE-PACKAGE member `hS1` (`tripleHEmeas`) of the
  fully-wired curved a₁ two-jet capstone `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` at the
  genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges ONE gate/measurability census binder — the
  base joint strong measurability `hS1 = HEmeasBorelAudit.tripleHEmeas … (vanVleckGatedWitness …
  (constGate …) …)` — for `g^K`, from the banked geometry-only supplier
  `ConstRadiusGateExport.tripleHEmeas_AT_CONSTRADIUS_GATE`.  It does NOT make `a₁ = R/6` unconditional:
  the carried transport-coefficient smoothness `hu` (the genuine `hsrc`-family geometric input), the
  geometric residuals `hsrc`/`hOffCollarTail`, the convergence trio, and the rest of the census all
  remain owed.

  ## What is closed

  `curved_hS1_at_gate` — the EXACT shape of the capstone binder
    `hS1 : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
             (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
               (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)`
  produced, for `g^K`, from `ConstRadiusGateExport.tripleHEmeas_AT_CONSTRADIUS_GATE` (the S1 fact at the
  literal constant-radius flow-ball gate `fun z => φ_z '' ball 0 c`, the `Measurable cf` residue
  DISSOLVED to `measurable_const`).  Because `constGate g^K gi^K hChr hK c` unfolds definitionally to
  `fun z => uniformFlowExp g^K gi^K hChr hK z '' Metric.ball 0 c`, the supplier's gate and the capstone's
  gate are the SAME term, so the supplier's conclusion closes the binder verbatim.

  ## Banked supplier + discharged geometry

  The supplier's `g`/`gi`-geometry inputs are the banked curved members:
    • `hg`      = `curvedRNCMetric_contDiff κ`               (metric `C^∞`),
    • `hgiC`    = `curvedRNCInv_contDiff κ hκ.le`             (inverse `C^∞`, `K ≤ 0`),
    • `hgpos`   = `curvedRNCMetric_hgpos κ hκ.le`             (`det g^K > 0`, `K ≤ 0`),
    • `hgiMeas` = `(curvedRNCInv_contDiff …).continuous.measurable`   (inverse measurability),
    • `hchr`    = `(hChr …).continuous.measurable`            (christoffel measurability),
  so `κ < 0` is genuinely used (via `hκ.le`) — this is the honestly-curved witness, not the flat `δ`.

  ## Carried residual (honest, LABELLED)

  1. The transport-coefficient smoothness
       `hu : ∀ k, ContDiff ℝ ⊤ (transportCoeff (transportOp (vanVleck g^K) g^K gi^K) k)`
     is CARRIED as a hypothesis — the genuine `hsrc`-family geometric input.  It is a true fact (the van
     Vleck transport recursion has `C^∞` coefficients for the `C^∞` metric `g^K`), owed by the census;
     it is NOT re-derived here, so it is passed through and labelled.
  2. The gate-smallness `c < δ₀` (the JET reach of `tripleHEmeas_flowball_geometry`, a-priori different
     from the chart reach `c < ρc`) is carried honestly as the conclusion's ANTECEDENT — a satisfiable
     smallness condition on the gate radius, never assumed outright.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `Ric ≠ 0`)

  The member is a genuine measurability fact (`tripleHEmeas` = joint strong measurability of the gated
  van-Vleck witness), discharged from a banked supplier — NOT the capstone's conclusion, and NOT
  vacuous.  It holds at the genuinely-curved `g^K` (`κ < 0`, where `Ric(0) = n(n−1)κ ≠ 0`,
  `curvedRNCMetric_ricci_trace_diag_ne`, `curved_hS1_at_gate_curved_satisfiable`); it does not touch,
  and is unaffected by, the `R/6` coefficient.  The carried `hu` is a genuine, satisfiable geometric
  fact (`C^∞` of the smooth `g^K` transport coefficients).  No `sorry`, no new axioms, no `:= True`, no
  hypothesis = conclusion, no existing file edited.  NOT `a₁ = R/6`. -/
import QIQTH.ConstRadiusGateExport
import QIQTH.A1R6CoreAtGate
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCPosDef

open QIQTH.Curvature QIQTH.A1R6CoreAtGate QIQTH.ConstRadiusGateExport
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.HeatResidualBound QIQTH.HeatTransportRecursion QIQTH.VanVleck QIQTH.ParametrixFunction
open scoped ContDiff

namespace QIQTH.CurvedA1GateS1

variable {n : ℕ}

/-- **★ J4-561 — `curved_hS1_at_gate`.**  The const-radius gate-package census binder `hS1`
    (`HEmeasBorelAudit.tripleHEmeas` of the gated van-Vleck witness at the literal constant-radius
    flow-ball gate `constGate = fun z => φ_z '' ball 0 c`) of
    `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the genuinely-curved witness
    `g^K = curvedRNCMetric κ` (`κ < 0`): there is a JET reach `δ₀ > 0` such that `c < δ₀ → hS1`.
    Discharged from the banked geometry-only supplier
    `ConstRadiusGateExport.tripleHEmeas_AT_CONSTRADIUS_GATE`, whose `g`/`gi`-geometry inputs are the
    banked curved members {`curvedRNCMetric_contDiff`, `curvedRNCInv_contDiff`, `curvedRNCMetric_hgpos`}
    (+ their `.continuous.measurable` measurability shadows).  The transport-coefficient smoothness `hu`
    is CARRIED as a labelled hypothesis (the genuine `hsrc`-family geometric input); the gate-smallness
    `c < δ₀` is carried honestly as the conclusion's antecedent.  Uses `κ < 0` via `hκ.le`.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hS1_at_gate (κ : ℝ) (hκ : κ < 0) (hn : 0 < n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    -- CARRIED (labelled): the transport-coefficient smoothness — the genuine `hsrc`-family geometric
    -- input.  A true `C^∞` fact of the van-Vleck transport recursion for the smooth metric `g^K`, owed
    -- by the census and passed through here (not re-derived).
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) k)) :
    ∃ δ₀ > (0 : ℝ), c < δ₀ →
      QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
        (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) := by
  obtain ⟨δ₀, hδ₀pos, hS1⟩ :=
    tripleHEmeas_AT_CONSTRADIUS_GATE hn (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b c ha hab hbc
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (fun a b => curvedRNCInv_contDiff κ hκ.le a b)
      (curvedRNCMetric_hgpos κ hκ.le)
      hu
      (fun i j => (curvedRNCInv_contDiff κ hκ.le i j).continuous.measurable)
      (fun k i j => (hChr k i j).continuous.measurable)
  exact ⟨δ₀, hδ₀pos, hS1⟩

/-- **★ J4-561 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so `hS1` is discharged at a
    genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.  NOT `a₁ = R/6`. -/
theorem curved_hS1_at_gate_curved_satisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1GateS1

section AxiomChecks
open QIQTH.CurvedA1GateS1
#print axioms curved_hS1_at_gate
#print axioms curved_hS1_at_gate_curved_satisfiable
end AxiomChecks
