/-
  ConstGateAssembly — J4-408: Sol #18 final-assembly brick #1, THE FIXED-GATE G₁/CENSUS BRIDGE.
  `ConstGateAssemblyData` + `constGate_assembly_data_from_data`: a `Prop` bundle of the base-layer
  (G₁) census facts stated AT THE LITERAL constant-radius gate `G₀ := constGate g gi hChr hK c`, plus
  a constructor that supplies them from the semantic inputs — the parametric census builders re-run at
  `G₀`, with honest satisfiable carries for what still resists.  ONE brick of the `a₁ = R/6`
  heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠⚠⚠ HONESTY FIREWALL — THIS FILE IS **NOT** `a₁ = R/6`. ⚠⚠⚠
  Nothing here proves anything new about `R/6`.  `ConstGateAssemblyData` is a CARRIER structure and
  `constGate_assembly_data_from_data` is a CONDITIONAL bundling: three of its fields are closed by
  already-banked builders re-run at the literal gate (the fixed-gate hEdom, the fixed-gate S1, and the
  nonpositive-time vanishing), while the remaining fields (`hpkgBound`, `hmemS0`, `hopenS0`) are carried
  honestly as SATISFIABLE hypotheses (their `∃`-choosing producer `constRadius_package_and_S1` chooses
  its own `(a,b,c,C)`, so the values do not defeq-match a caller-chosen literal gate — exactly the
  Section-C/H carries of `A1R6FromLabelled.a1_R6_from_labelled`).  Every hypothesis is satisfiable and
  NONE of them is the conclusion; no `sorry`, no `:= True`, no new axiom.  `a₁ = R/6` stays CONDITIONAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FIXED-GATE hEdom VERDICT (Sol #18, "copy the proof one layer earlier").
  `CommonGateShell.hEdom_from_geometry` IS `∃`-shaped — `∃ a b, 0<a ∧ a<b ∧ ∃ S, ∃ E₀ E₁, …` — and its
  witnesses are the INTERNAL `(m/8, m/4, φ_·''ball 0 (m/2))` of `affineGateBound_concrete`, which do NOT
  defeq-match the caller's literal `constGate g gi hChr hK c` at a chosen `(a,b)`.  So it CANNOT be used
  directly at `G₀`.  The "one layer earlier" copy is the affine bridge
  `HgateAffineRepair.hEdom_vanVleck_of_hgate_affine`, which takes `(S, a, b)` EXPLICITLY and produces the
  width-3/2 `hEdom` `∃ E₀ E₁`-shape at exactly that literal gate from the on-gate affine width-4/3
  quadratic carry `hgate`.  We instantiate it at `S := constGate g gi hChr hK c` and carry `hgate`
  honestly.  (The `constGate` `S`-shape `fun z => φ_z '' ball 0 c` IS the census machinery's own gate.)

  ## THE SUPPLIER MAP (which banked theorem feeds each field AT the literal gate `G₀`).
    • `hEdom`     ← `HgateAffineRepair.hEdom_vanVleck_of_hgate_affine` at `S := constGate g gi hChr hK c`
                    (from the honest on-gate affine carry `hgate`);          [real fixed-gate builder]
    • `hEz`       ← `DataPileWitnessAudit.hEzeroE_concrete` at the same gate (geometry only, needs 1≤n);
                                                                             [real fixed-gate builder]
    • `hS1`       ← `GatedRepSFix.tripleHEmeas_concrete_v4` at the same gate (from the satisfiable
                    `hKSmeas`/`hcarTau`/`hcarField`/`hcarField2`/`hgi`/`hchr` carriers);
                                                                             [real fixed-gate builder]
    • `hpkgBound` ← honest carry (the all-`t` width-2 package bound; satisfiable via
                    `ConstRadiusGateExport.constRadius_package_and_S1`, `∃`-witness mismatch);
    • `hmemS0`/`hopenS0` ← honest carries (the two gate-centre exports; same satisfiability certificate).

  ## WHAT THE SEVEN v3 SLOTS CONSUME (the `A1R6SlotAdapters.a1_R6_slots_AT_GATE` hypothesis inventory)
  and which banked theorem supplies each AT the literal gate — for the J4-409 handoff:
    • `hDuhamel` slot ← `HDuhamelExportRethread.hDuhamelSlot_AT_GATE` (from a `TruncatedDuhamelCore`,
                        itself `truncatedDuhamelCore_AT_GATE_FULL`);
    • `hDConv`   slot ← `HDConvGateThreading.hDConv_W1free` (its W1-free census + the `Da`-limit
                        `hDaLimLU = DaLimLUGoal …` [J4-337 `hDaLimLU_from_labelled` at `S := constGate`]
                        + the boundary loc-unif `hbdryLU` [J4-310 `hbdryLU_CONCRETE`]);
    • `hCConv`   slot ← `CConvV2Facade.hCConvSlot_AT_GATE_v2` (open-nbhd + linewise-`HasDerivAt` family
                        + the L2 sliver census).
  Together with the core `A1R6CoreAtGate.wide_a1_R6_core_AT_CONSTRADIUS`'s `htr`
  (`A1R6SlotAdapters.htr_adapter`) and package/S1 antecedents (this bundle), those close the a₁ two-jet.
  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.A1R6CoreAtGate
import QIQTH.HgateAffineRepair
import QIQTH.GatedRepSFix

open MeasureTheory Finset Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.HeatKernelA1 QIQTH.ExpMap
open QIQTH.A1R6CoreAtGate QIQTH.HgateAffineRepair QIQTH.GatedRepSFix
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.ConstGateAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE BUNDLE — the base-layer (G₁) census facts at the literal constant-radius gate.
    ############################################################################### -/

/-- **★★★ J4-408 — `ConstGateAssemblyData`.**  The `Prop` bundle of the base-layer (G₁) census facts,
    ALL stated at the ONE literal constant-radius gate `G₀ := constGate g gi hChr hK c` with the caller's
    cutoffs `(a,b)` and package constant `C`:
      • `hEdom`     — the width-3/2 affine Gaussian domination (`∃ E₀ E₁`-shape) of the gated van-Vleck
                      heat operator;
      • `hEz`       — the nonpositive-time vanishing of that operator;
      • `hS1`       — the joint strong-measurability triple `HEmeasBorelAudit.tripleHEmeas`;
      • `hpkgBound` — the all-`t` width-2 Gaussian package bound (constant `C·(1+t')`);
      • `hmemS0`/`hopenS0` — the two gate-centre exports (`0 ∈ S 0`, `IsOpen (S 0)`).
    A carrier structure only — every field is a CONDITIONAL analytic/geometric fact; ⚠ NOT `a₁ = R/6`. -/
structure ConstGateAssemblyData (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b C : ℝ) : Prop where
  /-- the width-3/2 affine Gaussian domination at the literal gate (`∃ E₀ E₁`-shape). -/
  hEdom : ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)
  /-- the nonpositive-time vanishing at the literal gate. -/
  hEz : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q = 0
  /-- the S1 joint strong-measurability triple at the literal gate. -/
  hS1 : QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
  /-- the all-`t` width-2 Gaussian package bound (constant `C·(1+t')`). -/
  hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q
  /-- gate-centre membership. -/
  hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0
  /-- gate-centre openness. -/
  hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0)

/-! ###############################################################################
    ### THE THREE FIXED-GATE FIELD BUILDERS (split into private lemmas).
    ############################################################################### -/

/-- **(field builder) `constGate_hEdom`.**  The width-3/2 affine Gaussian domination at the literal gate,
    from the honest on-gate affine width-4/3 quadratic carry `hgate` — the "one layer earlier" copy of
    the `∃`-shaped `hEdom_from_geometry`, via `HgateAffineRepair.hEdom_vanVleck_of_hgate_affine` at
    `S := constGate g gi hChr hK c`.  ⚠ NOT `a₁ = R/6`. -/
private theorem constGate_hEdom (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
        p ∈ closure (constGate g gi hChr hK c q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q))) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) :=
  hEdom_vanVleck_of_hgate_affine g gi hChr hK (constGate g gi hChr hK c) a b P₀ P₁ hP₀ hP₁ hgate

/-- **(field builder) `constGate_hEz`.**  The nonpositive-time vanishing of the gated van-Vleck heat
    operator at the literal gate, from geometry alone (needs `1 ≤ n`), via
    `DataPileWitnessAudit.hEzeroE_concrete`.  ⚠ NOT `a₁ = R/6`. -/
private theorem constGate_hEz (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b : ℝ) (hn : 1 ≤ n) :
    ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q = 0 :=
  hEzeroE_concrete g gi hChr hK (constGate g gi hChr hK c) a b hn

/-- **(field builder) `constGate_hS1`.**  The S1 joint strong-measurability triple
    `HEmeasBorelAudit.tripleHEmeas` at the literal gate, from the satisfiable v4 carriers
    (`hKSmeas` / `hcarTau` / `hcarField` / `hcarField2` / `hgi` / `hchr`), via
    `GatedRepSFix.tripleHEmeas_concrete_v4` at `S := constGate g gi hChr hK c`.  ⚠ NOT `a₁ = R/6`. -/
private theorem constGate_hS1 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2})
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b k w.1 w.2.1 w.2.2 = 0))
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            pd (fun y => pd (fun x =>
                vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b w.1 x w.2.2) j y)
              i w.2.1 = 0))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) :=
  tripleHEmeas_concrete_v4 hn g gi hChr hK (constGate g gi hChr hK c) a b
    hKSmeas hcarTau hcarField hcarField2 hgi hchr

/-! ###############################################################################
    ### THE BRIDGE — `constGate_assembly_data_from_data`.
    ############################################################################### -/

/-- **★★★ J4-408 — `constGate_assembly_data_from_data`.**  Assembles the base-layer `ConstGateAssemblyData`
    bundle at the literal constant-radius gate `G₀ := constGate g gi hChr hK c` from the semantic inputs.
    Three fields are closed by banked builders re-run at `G₀` (`hEdom` ← the affine bridge from the
    on-gate carry `hgate`; `hEz` ← geometry; `hS1` ← the v4 measurability carriers), and the remaining
    three (`hpkgBound`, `hmemS0`, `hopenS0`) are carried honestly — SATISFIABLE via
    `ConstRadiusGateExport.constRadius_package_and_S1`, whose own `∃`-witnesses do not defeq-match a
    caller-chosen literal gate (the same carry pattern as `A1R6FromLabelled.a1_R6_from_labelled`'s
    Sections C/H).  Every hypothesis is satisfiable; NONE is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem constGate_assembly_data_from_data (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b C : ℝ)
    -- ── the `hEdom` field: the honest on-gate affine width-4/3 quadratic carry (Sol #15):
    (P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
        p ∈ closure (constGate g gi hChr hK c q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))
    -- ── the `hS1` field: the satisfiable v4 measurability carriers at the literal gate:
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2})
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b k w.1 w.2.1 w.2.2 = 0))
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            pd (fun y => pd (fun x =>
                vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b w.1 x w.2.2) j y)
              i w.2.1 = 0))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    -- ── the `hpkgBound`/`hmemS0`/`hopenS0` fields: honest carries (satisfiable via `constRadius_package_and_S1`):
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0)) :
    ConstGateAssemblyData g gi hChr hK c a b C where
  hEdom := constGate_hEdom g gi hChr hK c a b P₀ P₁ hP₀ hP₁ hgate
  hEz := constGate_hEz g gi hChr hK c a b hn
  hS1 := constGate_hS1 hn g gi hChr hK c a b hKSmeas hcarTau hcarField hcarField2 hgiMeas hchrMeas
  hpkgBound := hpkgBound
  hmemS0 := hmemS0
  hopenS0 := hopenS0

end QIQTH.ConstGateAssembly

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ConstGateAssembly
#print axioms constGate_assembly_data_from_data
end AxiomChecks
