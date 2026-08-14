/-
  A1R6FromDataGated — J4-748: the GATED-SEAM re-plumb of the public capstone `a1_R6_from_data`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a
  DROP-IN SUPPLIER SWAP of the base-layer S1 (joint strong-measurability) field.  No `sorry` (prose
  excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no
  conclusion-in-disguise.  No existing file is edited — only NEW declarations are added.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS DOES (the J4-747 flag, executed).

  The banked capstone `A1R6FromData.a1_R6_from_data` sources its `ConstGateAssemblyData.hS1` field
  (the S1 triple `HEmeasBorelAudit.tripleHEmeas`) via `ConstGateAssembly.constGate_hS1`, which calls
  `GatedRepSFix.tripleHEmeas_concrete_v4` — the RAW-CHART route.  Each of the three v4 measurability
  carriers `hcarTau`/`hcarField`/`hcarField2` carries a conjunct
    `Measurable (fun w => uniformInverseChart g gi hChr hK w.2.2 w.2.1)`,
  the `.choose`-opacity WALL flagged by J4-747: the `.choose`-built `uniformInverseChart` forgot the
  inverse off the flow image, so `q ↦ Classical.choose (h q)` carries no measurable-in-`q` structure
  there.

  This file re-routes `hS1` through `GatedChartMeasAudit.tripleHEmeas_concrete_v3` — the GATED seam —
  which produces the SAME conclusion `tripleHEmeas g gi (vanVleckGatedWitness … (constGate …) a b)`
  but consumes, in place of the raw chart-measurability conjunct, a single MEASURABLE joint
  right-inverse `Gc` (`Measurable Gc`) together with the GUARDED on-support agreement
  `amplitude-factor ≠ 0 ⟹ uniformInverseChart … = Gc(…)`.  The raw-chart wall is ELIMINATED from all
  three carriers.  (`hWG_of_unguarded` certifies the guarded agreement is strictly WEAKER than the
  unguarded chart representative, hence non-vacuous.)

  Everything else is IDENTICAL to `a1_R6_from_data`: the geometric conclusion carries the Ricci source
  `(∑ᵢ ricci g gi i i 0)/6` (NOT an abstract `Ric`), and the gate is the literal constructed flow-ball
  `constGate g gi hChr hK c` (NOT a free/assumed `S`).  The capstone body is a ONE-LINE application of
  the banked firing lemma `FinalA1SlotsAtConstGate.fire`, unchanged; only the base-layer bundle it is
  fed is rebuilt through the gated `hS1`.

  ## WHAT REMAINS CONDITIONAL (unchanged).  Same as `a1_R6_from_data`: the `A1R6GateSlots` censuses,
  the `hgate`/`hpkgBound`/`hmemS0`/`hopenS0` carries, `hGauss`, and the deep convergence-trio content.
  The swap touches ONLY the S1 measurability seam.  ⚠ NOT `a₁ = R/6`.

  ## NOTE ON FULL CARRIER ELIMINATION (why NOT attempted here).  `JetsGcUnification.
  tripleHEmeas_Gc_concrete` proves S1 at the concrete flow-ball gate from PURE GEOMETRY (no
  hcar carriers), but only for a radius `c` in a geometry-determined window `(b, δ₀)`.  Feeding it
  would force `c` to become an existentially-constructed gate radius, which cascades into requiring
  `hgate`/`hpkgBound`/`hmemS0`/`hopenS0`/`slots` ALL to be discharged at that same constructed `c` —
  a far larger surgery than this local S1-seam swap.  It is deferred; here `c` stays a free caller
  parameter and the gated carriers are reshaped, not eliminated.
-/
import Mathlib
import QIQTH.A1R6FromData
import QIQTH.GatedChartMeasAudit

open MeasureTheory Finset Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.HeatKernelA1 QIQTH.ExpMap
open QIQTH.A1R6CoreAtGate QIQTH.A1R6SlotAdapters QIQTH.ConstGateAssembly QIQTH.FinalA1Slots
open QIQTH.HgateAffineRepair QIQTH.GatedRepSFix QIQTH.GatedChartMeasAudit
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.A1R6FromDataGated

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (G1) THE GATED BASE-LAYER BUILDER — `constGate_assembly_data_from_data_gated`.
    ###############################################################################

    Rebuilds the `ConstGateAssemblyData` bundle at the literal constant-radius gate
    `G₀ := constGate g gi hChr hK c` IDENTICALLY to `ConstGateAssembly.constGate_assembly_data_from_data`
    EXCEPT the `hS1` field is sourced from the GATED `GatedChartMeasAudit.tripleHEmeas_concrete_v3`
    (the raw-chart wall dropped for `Gc` + guarded agreement) rather than the raw
    `GatedRepSFix.tripleHEmeas_concrete_v4`.  All five other fields (`hEdom`, `hEz`, `hpkgBound`,
    `hmemS0`, `hopenS0`) are built via the same banked public lemmas.  ⚠ NOT `a₁ = R/6`. -/
theorem constGate_assembly_data_from_data_gated (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b C : ℝ)
    -- ── the `hEdom` field: the honest on-gate affine width-4/3 quadratic carry (UNCHANGED):
    (P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
        p ∈ closure (constGate g gi hChr hK c q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))
    -- ── the `hS1` field: the GATED carriers (raw-chart wall ELIMINATED for `Gc` + guarded agreement):
    (hKmeasSet : MeasurableSet K)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1 ≠ 0 ∨ Cfield w.2.2 w.2.1 ≠ 0) →
            uniformInverseChart g gi hChr hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1 ≠ 0) →
            uniformInverseChart g gi hChr hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2 ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1))
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
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
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1 ≠ 0
              ∨ pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1 ≠ 0) →
            uniformInverseChart g gi hChr hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2 ∧
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
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    -- ── the `hpkgBound`/`hmemS0`/`hopenS0` fields: honest carries (UNCHANGED):
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0)) :
    ConstGateAssemblyData g gi hChr hK c a b C where
  hEdom := hEdom_vanVleck_of_hgate_affine g gi hChr hK (constGate g gi hChr hK c) a b P₀ P₁ hP₀ hP₁ hgate
  hEz := hEzeroE_concrete g gi hChr hK (constGate g gi hChr hK c) a b hn
  hS1 := tripleHEmeas_concrete_v3 hn g gi hChr hK (constGate g gi hChr hK c) a b
      hKmeasSet Gc hGmeas hcarTau hcarField hcarField2 hgiMeas hchrMeas
  hpkgBound := hpkgBound
  hmemS0 := hmemS0
  hopenS0 := hopenS0

/-! ###############################################################################
    ### (G2) THE GATED PUBLIC CAPSTONE — `a1_R6_from_data_gated`.
    ###############################################################################

    IDENTICAL to `A1R6FromData.a1_R6_from_data` — same geometric conclusion (Ricci source
    `(∑ᵢ ricci g gi i i 0)/6`) at the same literal constructed flow-ball gate `constGate g gi hChr hK c`
    — EXCEPT the base-layer bundle fed to `FinalA1SlotsAtConstGate.fire` is built through the GATED
    `constGate_assembly_data_from_data_gated` (raw-chart wall eliminated for `Gc` + guarded agreement)
    rather than the raw `constGate_assembly_data_from_data`.  A ONE-LINE apply-wrapper.  ⚠ NOT
    `a₁ = R/6`. -/
theorem a1_R6_from_data_gated (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    -- ── (A) base geometry / gauge binders:
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (a b c C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    -- ── (B) the `ConstGateAssemblyData` semantic carries (GATED S1 seam):
    (P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
        p ∈ closure (constGate g gi hChr hK c q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))
    -- the GATED measurability carriers (raw-chart wall dropped for `Gc` + guarded agreement):
    (hKmeasSet : MeasurableSet K)
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1 ≠ 0 ∨ Cfield w.2.2 w.2.1 ≠ 0) →
            uniformInverseChart g gi hChr hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1 ≠ 0) →
            uniformInverseChart g gi hChr hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2 ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1))
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
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
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1 ≠ 0
              ∨ pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1 ≠ 0) →
            uniformInverseChart g gi hChr hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2 ∧
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
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    -- the honest package / gate-centre carries (UNCHANGED):
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0))
    -- ── (C) the ONE semantic slot package (UNCHANGED):
    (slots : A1R6GateSlots g gi hChr hK c a b t)
    -- ── (D) the single labelled gauge carry (UNCHANGED):
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i)) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) :=
  FinalA1SlotsAtConstGate.fire g gi t ht hn hChr hK hK0
    hg hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hCnn
    (constGate_assembly_data_from_data_gated hn g gi hChr hK c a b C
      P₀ P₁ hP₀ hP₁ hgate hKmeasSet Gc hGmeas hcarTau hcarField hcarField2 hgiMeas hchrMeas
      hpkgBound hmemS0 hopenS0)
    (finalA1Slots_from_data g gi hChr hK c a b t slots
      hg hgsymm hgiC hgi hdg0 hGauss)

end QIQTH.A1R6FromDataGated

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.A1R6FromDataGated
#print axioms constGate_assembly_data_from_data_gated
#print axioms a1_R6_from_data_gated
end AxiomChecks
