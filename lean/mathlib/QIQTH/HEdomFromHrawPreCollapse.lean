/-
  HEdomFromHrawPreCollapse — the ABSTRACT-`g` `hEdom` discharge for the LIVE order-1 capstone's
  `hDuhamel`/`hDConv` shared `hDaLimLU` census (mirroring J4-896's `hmassone` wiring).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure COMPOSITION / RE-EXPOSURE brick.  It threads the banked `HrawPreCollapse.hEdom_concrete_final`
  (stated GENERICALLY in `gatedKernel K S H`) through the DEFINITIONAL equality
      `vanVleckGatedWitness g gi hChr hK S a b
         = gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
             (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK))`
  (the `def` body, `ConvApproximants.lean:161-166`), producing the EXACT `hEdom` ∃-shape carried by the
  live `hDaLimLU` census (`HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL`'s `hEdom` binder,
  `HDuhamelExportRethread.lean:304-306`, and `DaLimLUConcreteDischarge.hDaLimLU_concrete`'s `hEdom`
  binder, `DaLimLUConcreteDischarge.lean:166`), reducing it to the NAMED, SATISFIABLE on-gate width-4/3
  QUADRATIC parametrix carry `hgate`.  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE EXACT SHAPE consumed by the census (character-checked against source).

  Both `hDuhamel` (via `truncatedDuhamelCore_AT_GATE_FULL`, which forwards `hEdom` into
  `DaLimLUConcreteDischarge.hDaLimLU_concrete`) and `hDConv` (which shares the same `hDaLimLU` data)
  carry, at the concrete witness (`vanVleckGatedWitness g gi hChr hK S a b`):
      `hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
          |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
            ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)`
  at *some* `E₀ E₁ ≥ 0`.  This file PRODUCES the `∃ E₀ E₁, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ …` form from which the
  downstream consumer `obtain`s the constants — the honest reachable grading (the constants are proved,
  not free) — for ABSTRACT `g gi K S`.

  ## THE DEFEQ MATCH (mirroring J4-896's `constGate_eq_liveGate` `rfl` check).

  `HrawPreCollapse.hEdom_concrete_final` is stated GENERICALLY in the kernel `gatedKernel K S H`.  The
  live census kernel `vanVleckGatedWitness g gi hChr hK S a b` is DEFINITIONALLY `gatedKernel K S H` at
  `H = globalCutoffParametrixWitnessN 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) a b
  (uniformInverseChart g gi hChr hK)`, so `hEdom_concrete_final` at that `H` yields the census binder
  shape with NO adapter (`vanVleckGatedWitness_eq_gatedKernel`, `rfl`).

  ## HONEST SURVIVING CARRY.  This discharges the `hEdom` census binder MODULO the NAMED, SATISFIABLE
  on-gate width-4/3 QUADRATIC parametrix carry `hgate` (the per-base M2 parametrix/amplitude sup-bound
  data glued along the gate = flow-ball; the genuine T2-quadratic grading).  `hgate` is NOT the
  conclusion (width-4/3 QUADRATIC on the gate vs the width-3/2 affine ∃-shape everywhere).  This is the
  EXACT same `hgate` `HrawPreCollapse.hEdom_concrete_final` already reduces to — this file merely
  re-exposes it at the LIVE `vanVleckGatedWitness` kernel.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HrawPreCollapse
import QIQTH.ConvApproximants

open Set Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.RadialDistance
open QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators

namespace QIQTH.HEdomFromHrawPreCollapse

variable {n : ℕ}

/-! ###############################################################################
    ### The defeq character-check (mirroring J4-896's `constGate_eq_liveGate`).
    ############################################################################### -/

/-- **Character-check (defeq, `rfl`).**  The LIVE census kernel `vanVleckGatedWitness g gi hChr hK S a b`
    is DEFINITIONALLY `gatedKernel K S H` at the order-1 van-Vleck parametrix
    `H = globalCutoffParametrixWitnessN 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi))
    a b (uniformInverseChart g gi hChr hK)` (the `def` body).  This is what makes
    `hEdom_from_hrawPreCollapse` below the discharge at the LIVE capstone's own kernel via the GENERIC
    `HrawPreCollapse.hEdom_concrete_final`.  ⚠ NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitness_eq_gatedKernel
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) :
    vanVleckGatedWitness g gi hChr hK S a b
      = gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK)) :=
  rfl

/-! ###############################################################################
    ### The ABSTRACT-`g` `hEdom` discharge — exact census-binder shape.
    ############################################################################### -/

/-- **★★ `hEdom_from_hrawPreCollapse` — the ABSTRACT-`g` `hEdom` binder.**  The EXACT `hEdom` ∃-shape
    carried by the shared `hDaLimLU` census of `hDuhamel`
    (`HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL`, its `hEdom` binder, lines 304-306) and
    `hDConv` (the same `hDaLimLU` data), for ABSTRACT `g gi K S`:
        `∃ E₀ E₁, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ>0, ∀ p q,
            |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
              ≤ (E₀ + E₁·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p−q)`,
    obtained by threading the banked GENERIC `HrawPreCollapse.hEdom_concrete_final` through the
    definitional equality `vanVleckGatedWitness_eq_gatedKernel`.

    The surviving carry is the NAMED, SATISFIABLE on-gate width-4/3 QUADRATIC parametrix bound `hgate`
    (the exact carry `hEdom_concrete_final` reduces to) — NOT the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hEdom_from_hrawPreCollapse
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q))) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) :=
  QIQTH.HrawPreCollapse.hEdom_concrete_final g gi K S
    (globalCutoffParametrixWitnessN 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK))
    P hP hgate

end QIQTH.HEdomFromHrawPreCollapse

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HEdomFromHrawPreCollapse
#print axioms vanVleckGatedWitness_eq_gatedKernel
#print axioms hEdom_from_hrawPreCollapse
end AxiomChecks
