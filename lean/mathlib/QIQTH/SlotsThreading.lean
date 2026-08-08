/-
  SlotsThreading — J4-413: Sol #18 closing sequence 3/4, THE SLOTS THREADING.

  We THREAD the three census sub-carriers of the `slots` binder of the constRadius-absorbed capstone
  `ConstRadiusAbsorb.a1_R6_from_data_v3` (J4-412).  The `slots` binder is
      `slots : ∀ a b c, 0 < a → a < b → b < c → A1R6GateSlots g gi hChr hK c a b t`,
  whose producer `A1R6SlotAdapters.a1_R6_slots_AT_GATE` assembles the shallow slot package
  `A1R6GateSlots` from three legs at a literal gate:
    • the `hDuhamel` field ← a `TruncatedDuhamelCore` (the Duhamel core carrier);
    • the `hDConv`   field ← the W1-free census (`HDConvGateThreading.hDConv_W1free`);
    • the `hCConv`   field ← the L2 sliver census (`CConvV2Facade.hCConvSlot_AT_GATE_v2`).

  This file:
    • (T2) `hCConvSlot_threaded` — the L2 threading: `hCConvSlot_AT_GATE_v2` with its sliver census
      DISCHARGED by the F-pile firings `PerUProviders.hlin_field_concrete` (the `hlin` linewise field),
      `HD1Concrete.{hb_concrete, hbulk_tendsto_concrete}` + `FrozenGermInternal.fbulkInt` (the
      `sSet`/`hb`/`hbulk_tendsto`/`fbulk` census members), keeping the genuine analytic sliver carries
      explicit (`fderivBulk`/`gderiv`/`hbulkderiv`/`hsliver`/`hcont` + the `hGint` integrability + the
      linewise provider `hProv`).  Conclusion is the EXACT `hCConv` field of `A1R6GateSlots`.
    • `a1R6GateSlots_threaded` — the L2-THREADED single-gate assembler of `A1R6GateSlots`:
      the `hDuhamel` field from a carried `TruncatedDuhamelCore`, the `hDConv` field from a carried
      `DifferentiableAt` (the field `hDConv_W1free` produces), and the `hCConv` field from the F-pile
      firings (T2).
    • (T3) `a1_R6_from_data_v4` — the v3 with the single `slots` binder REPLACED by three
      ∀-over-gates census sub-carrier groups (the Duhamel core carrier + the `hDConv` field carrier +
      the L2 residuals), the assembler applied inside for each admissible gate triple.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  binder-threading / re-plumbing brick.  `a1_R6_from_data_v4` is STILL the maximally-unconditional
  **CONDITIONAL** a₁ two-jet — replacing the `slots` binder by its three sub-carrier groups closes
  NOTHING deeper.  What remains CONDITIONAL is UNCHANGED from `a1_R6_from_data_v3`:
    (a) the Duhamel core carrier (the ~90-binder Duhamel census inside `TruncatedDuhamelCore`, the
        convergence-trio content — NEVER claimed closed);
    (b) the `hDConv` field carrier (the W1-free census of `hDConv_W1free` is NOT re-exposed here — it is
        carried as the `DifferentiableAt` FIELD it produces, ∀-over-gates; the RESIDUE);
    (c) the L2 residuals (the linewise provider `hProv`, the sliver data `fderivBulk`/`gderiv`, the
        integrability `hGint`, and the analytic sliver carries `hbulkderiv`/`hsliver`/`hcont`) —
        genuine satisfiable analytic inputs, none the conclusion;
    (d) the remaining `ConstGateAssemblyData` carries and the base-metric identification `hgPull`,
        inherited verbatim from v3.
  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited,
  nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CConvV2Facade
import QIQTH.PerUProviders
import QIQTH.HD1Concrete
import QIQTH.FrozenGermInternal
import QIQTH.A1R6SlotAdapters
import QIQTH.HDuhamelExportRethread
import QIQTH.HDConvGateThreading
import QIQTH.ConstRadiusAbsorb

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.HeatKernelA1 QIQTH.ExpMap
open QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade QIQTH.PerUProviders QIQTH.HD1Concrete
open QIQTH.A1R6CoreAtGate QIQTH.A1R6SlotAdapters
open QIQTH.HDuhamelExportRethread QIQTH.HDConvGateThreading
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon QIQTH.ConstRadiusAbsorb
open scoped Topology BigOperators Interval ContDiff

namespace QIQTH.SlotsThreading

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (T2) `hCConvSlot_threaded` — the L2 slot with its sliver census threaded from the F-pile.
    ############################################################################### -/

/-- **★★★ (T2) `hCConvSlot_threaded`.**  The EXACT `hCConv` field of `A1R6GateSlots` at the concrete
    van-Vleck gated witness `H := vanVleckGatedWitness g gi hChr hK S a b` with source
    `F := leviSeries (heatOp g gi H)`:
      `ContDiffAt ℝ 2 (fun p ↦ heatConv H F t p 0) 0`,
    obtained from `CConvV2Facade.hCConvSlot_AT_GATE_v2` with its L2 sliver census THREADED by the
    F-pile firings:
      • the `hlin` linewise `HasDerivAt` family ← `PerUProviders.hlin_field_concrete` (from its
        7-leg per-`(x,i)` provider `hProv`);
      • `sSet := univ`, `hsOpen := isOpen_univ`, `hsnhds := univ_mem`;
      • `fbulk := FrozenGermInternal.fbulkInt g gi hChr hK S a b t`;
      • `bb := fun i m ↦ (C₀ i + C₁ i)·2√εₘ + C₂ i·εₘ`, `hb ← HD1Concrete.hb_concrete`;
      • `hbulk_tendsto ← HD1Concrete.hbulk_tendsto_concrete` (on the integrability carry `hGint`);
    keeping the genuine analytic sliver carries explicit (`fderivBulk`/`gderiv`, `hbulkderiv`,
    `hsliver`, `hcont`) and the linewise provider `hProv`.  Every surviving carry is satisfiable,
    non-vacuous, strictly lower-level than the `C²` conclusion, and NONE is the conclusion.
    ⚠ NOT `a₁ = R/6`. -/
theorem hCConvSlot_threaded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ) (ht : 0 < t)
    -- the OPEN field neighbourhood of `0`:
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    -- the linewise `hlin` provider (the 7-leg per-`(x,i)` diff-under-∫ census):
    (hProv : ∀ x ∈ u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (t - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 t))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume 0 t ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 t)) ∧
        IntervalIntegrable bound volume 0 t ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (t - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w))
    -- the analytic sliver carries (the residual L2 data):
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : Fin n → ℝ)
    (hGint : ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 t)
    (hbulkderiv : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b t i m)
          (fderivBulk i m x) x)
    (hsliver : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk i m x) (gderiv i x)
          ≤ (C₀ i + C₁ i) * (2 * Real.sqrt (epsSeq m)) + C₂ i * epsSeq m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) (Set.univ : Set (Point n))) :
    ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
        (0 : Point n) :=
  hCConvSlot_AT_GATE_v2 g gi hChr hK S a b t
    u hu_open hu0
    (hlin_field_concrete g gi hChr hK S a b t u hProv)
    (Set.univ) isOpen_univ univ_mem
    (fun i m => QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b t i m)
    fderivBulk gderiv
    (fun i m => (C₀ i + C₁ i) * (2 * Real.sqrt (epsSeq m)) + C₂ i * epsSeq m)
    (fun i => hb_concrete (C₀ i) (C₁ i) (C₂ i))
    hbulkderiv
    (fun i x _hx => hbulk_tendsto_concrete g gi hChr hK S a b i t ht x (hGint i x))
    hsliver hcont

/-! ###############################################################################
    ### `a1R6GateSlots_threaded` — the L2-threaded single-gate assembler of `A1R6GateSlots`.
    ############################################################################### -/

/-- **★★★ `a1R6GateSlots_threaded`.**  The L2-THREADED single-gate assembler: builds the shallow slot
    package `A1R6GateSlots g gi hChr hK c a b t` at the literal constant-radius gate from three
    sub-carriers:
      • `core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK (constGate …) a b) t` — the
        Duhamel core carrier; the `hDuhamel` field is produced by `HDuhamelExportRethread.hDuhamelSlot_AT_GATE`;
      • `hDConvField : DifferentiableAt …` — the `hDConv` field carrier (the field `hDConv_W1free`
        produces; its W1-free census is NOT re-exposed here — carried as the field, the RESIDUE);
      • the L2 residuals (`u`/`hu_open`/`hu0`, `hProv`, `fderivBulk`/`gderiv`/`C₀`/`C₁`/`C₂`, `hGint`,
        `hbulkderiv`/`hsliver`/`hcont`) → the `hCConv` field via (T2) `hCConvSlot_threaded`.
    Each field is closed by ONE explicit application; every carry is honest and satisfiable, NONE is the
    conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem a1R6GateSlots_threaded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b t : ℝ) (ht : 0 < t)
    -- ── the Duhamel core carrier:
    (core : TruncatedDuhamelCore g gi
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) t)
    -- ── the `hDConv` field carrier (the W1-free `DifferentiableAt`, RESIDUE):
    (hDConvField : DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
        u 0 0) t)
    -- ── the L2 residuals (threaded via T2):
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (hProv : ∀ x ∈ u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (t - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          (volume.restrict (Set.uIoc 0 t))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (t - s) x z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) volume 0 t ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          (volume.restrict (Set.uIoc 0 t)) ∧
        IntervalIntegrable bound volume 0 t ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0‖
            ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b
              (t - s) (Function.update x i w) z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s)
                (Function.update x i w) z
              * leviSeries (heatOp g gi
                  (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) w))
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : Fin n → ℝ)
    (hGint : ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 t)
    (hbulkderiv : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK (constGate g gi hChr hK c) a b t i m)
          (fderivBulk i m x) x)
    (hsliver : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk i m x) (gderiv i x)
          ≤ (C₀ i + C₁ i) * (2 * Real.sqrt (epsSeq m)) + C₂ i * epsSeq m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) (Set.univ : Set (Point n))) :
    A1R6GateSlots g gi hChr hK c a b t :=
  { hDuhamel := hDuhamelSlot_AT_GATE g gi hChr hK (constGate g gi hChr hK c) a b t core
    hDConv := hDConvField
    hCConv := hCConvSlot_threaded g gi hChr hK (constGate g gi hChr hK c) a b t ht
      u hu_open hu0 hProv fderivBulk gderiv C₀ C₁ C₂ hGint hbulkderiv hsliver hcont }

/-! ###############################################################################
    ### `L2Residual` — the bundled L2 residual carrier (one binder for the whole L2 group).
    ############################################################################### -/

/-- **`L2Residual`.**  The bundled L2-residual carrier at the literal constant-radius gate: the
    existential package of the L2 sliver DATA (`u`, `fderivBulk`, `gderiv`, `C₀`/`C₁`/`C₂`) together
    with the honest analytic props (`IsOpen u`, `0 ∈ u`, the linewise provider `hProv`, the
    integrability `hGint`, and the sliver carries `hbulkderiv`/`hsliver`/`hcont`) that (T2)
    `hCConvSlot_threaded` consumes.  Bundling these into ONE `Prop` keeps the `a1_R6_from_data_v4`
    signature to a single L2 binder ∀-over-gates.  Every component is satisfiable and non-vacuous;
    NONE is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
def L2Residual (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b t : ℝ) : Prop :=
  ∃ (u : Set (Point n))
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : Fin n → ℝ),
    IsOpen u ∧ (0 : Point n) ∈ u ∧
    (∀ x ∈ u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (t - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          (volume.restrict (Set.uIoc 0 t))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (t - s) x z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) volume 0 t ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          (volume.restrict (Set.uIoc 0 t)) ∧
        IntervalIntegrable bound volume 0 t ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0‖
            ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b
              (t - s) (Function.update x i w) z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s)
                (Function.update x i w) z
              * leviSeries (heatOp g gi
                  (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) w)) ∧
    (∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 t) ∧
    (∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK (constGate g gi hChr hK c) a b t i m)
          (fderivBulk i m x) x) ∧
    (∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk i m x) (gderiv i x)
          ≤ (C₀ i + C₁ i) * (2 * Real.sqrt (epsSeq m)) + C₂ i * epsSeq m) ∧
    (∀ i : Fin n, ContinuousOn (gderiv i) (Set.univ : Set (Point n)))

/-! ###############################################################################
    ### (T3) `a1_R6_from_data_v4` — the v3 with the `slots` binder threaded into three sub-carriers.
    ############################################################################### -/

/-- **★★★★★ (T3) `a1_R6_from_data_v4`.**  The constRadius-absorbed capstone
    `ConstRadiusAbsorb.a1_R6_from_data_v3` (J4-412) with its single semantic `slots` binder
    `slots : ∀ a b c, … → A1R6GateSlots g gi hChr hK c a b t` REPLACED by its three census
    sub-carrier groups, each ∀-over-gates:
      • `coreSlots`   — the Duhamel core carrier (`TruncatedDuhamelCore …`), feeding the `hDuhamel`
        field via `HDuhamelExportRethread.hDuhamelSlot_AT_GATE`;
      • `hDConvSlots` — the `hDConv` field carrier (`DifferentiableAt …`, the field `hDConv_W1free`
        produces; its W1-free census is NOT re-exposed — the RESIDUE);
      • `L2Slots`     — the L2 residual bundle (`L2Residual`), threaded into the `hCConv` field via
        (T2) `hCConvSlot_threaded` (`hlin`/`sSet`/`hb`/`hbulk_tendsto`/`fbulk` discharged from the
        F-pile firings, the analytic sliver carries kept explicit).
    The assembler `a1R6GateSlots_threaded` is applied inside for each admissible gate triple to
    reconstruct `A1R6GateSlots`, then re-exported through v3.  All the remaining v3 binders (base
    geometry/gauge, the constant-radius geometry-only inputs, the ∀-over-gates `ConstGateAssemblyData`
    carriers `hgate`/`hKSmeas`/`hcarTau`/`hcarField`/`hcarField2`, and group (D′)) are inherited
    VERBATIM.

    ⚠ THE HONEST SUMMARY.  This is the maximally-unconditional **CONDITIONAL** a₁ two-jet, NOT an
    unconditional `a₁ = R/6`.  Threading the `slots` binder into its three sub-carriers is pure
    re-plumbing; it closes NOTHING deeper.  What remains CONDITIONAL is UNCHANGED from v3: the Duhamel
    core (with the convergence-trio content NEVER claimed closed), the `hDConv` W1-free field (its
    census not re-exposed — the RESIDUE), the L2 residual analytic carries, the remaining
    `ConstGateAssemblyData` carries, and `hgPull` (group (D′)).  ⚠ NOT `a₁ = R/6`. -/
theorem a1_R6_from_data_v4 (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
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
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    (hgate : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
        (∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
          p ∈ closure (constGate g gi hChr hK c q) →
          |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
            ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                    * gaussDdim (4 / 3 * τ) (p - q))))
    (hKSmeas : ∀ c : ℝ, MeasurableSet {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2})
    (hcarTau : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ a b c : ℝ, 0 < a → a < b → b < c → ∀ k : Fin n,
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
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
    (hcarField2 : ∀ a b c : ℝ, 0 < a → a < b → b < c → ∀ i j : Fin n,
        ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
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
    -- ── the THREE census sub-carrier groups replacing the single `slots` binder, ∀-over-gates:
    (coreSlots : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        TruncatedDuhamelCore g gi
          (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) t)
    (hDConvSlots : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        DifferentiableAt ℝ
          (fun u => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u 0 0) t)
    (L2Slots : ∀ a b c : ℝ, 0 < a → a < b → b < c → L2Residual g gi hChr hK c a b t)
    -- ── (D′) group (D) ABSORBED (unchanged from v3):
    (gb gib : Point n → Fin n → Fin n → ℝ)
    (hCb : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel gb gib a b c y))
    (hgPull : g = expPullbackMetric gb gib hCb 0)
    (hsymmb : ∀ y a b, gb y a b = gb y b a)
    (hinvb : ∀ y a b, (∑ σ, gb y a σ * gib y σ b) = if a = b then 1 else 0)
    (hgb : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gb y a b))
    (hgaugeb : ∀ a b, gb 0 a b = if a = b then 1 else 0) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
    (heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
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
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  refine a1_R6_from_data_v3 hn g gi t ht hChr hK hK0
    hg hgsymm hgiC hgpos hg0 hgi hΓ hdg0 hsrc
    hgnd hinvF hframeK hw hu hgiMeas hchrMeas
    hgate hKSmeas hcarTau hcarField hcarField2
    (fun a b c ha hab hbc => ?_)
    gb gib hCb hgPull hsymmb hinvb hgb hgaugeb
  -- reconstruct the `A1R6GateSlots` package at the admissible gate from the three sub-carriers.
  obtain ⟨u, fderivBulk, gderiv, C₀, C₁, C₂,
          hu_open, hu0, hProv, hGint, hbulkderiv, hsliver, hcont⟩ := L2Slots a b c ha hab hbc
  exact a1R6GateSlots_threaded g gi hChr hK c a b t ht
    (coreSlots a b c ha hab hbc) (hDConvSlots a b c ha hab hbc)
    u hu_open hu0 hProv fderivBulk gderiv C₀ C₁ C₂ hGint hbulkderiv hsliver hcont

end QIQTH.SlotsThreading

/-! ###############################################################################
    ### THE AUDIT — `#print axioms` (must be `std-3`).
    ############################################################################### -/
section AxiomChecks
open QIQTH.SlotsThreading
#print axioms hCConvSlot_threaded
#print axioms a1R6GateSlots_threaded
#print axioms a1_R6_from_data_v4
end AxiomChecks
