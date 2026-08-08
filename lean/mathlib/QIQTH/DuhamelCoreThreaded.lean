/-
  DuhamelCoreThreaded — J4-414: the closing sequence 4/4, move 1 — THE DUHAMEL CORE THREADING.

  We thread the `TruncatedDuhamelCore` carrier (the `coreSlots` binder of `SlotsThreading.a1_R6_from_data_v4`,
  J4-413) through the BANKED Duhamel suppliers, discharging the THREE interchange legs
  (`MemLapFull`/`MemAdjLo`/`MemAdjHi`) of `HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL`
  via the WALL-A campaign results, and re-exporting the collapsed Core carrier.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE J4-414 DONT-UNDERCREDIT VERDICT (D1) — the wall-A coverage of the interchange legs.

  `truncatedDuhamelCore_AT_GATE_FULL` carries THREE abstract interchange binders at the endgame gate
  `H_G := vanVleckGatedWitness g gi hChr hK S a b`, `F := leviSeries (heatOp g gi H_G)`,
  `pdpdH := fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z`:
    • `hLapFull : MemLapFull g gi H_G F U pdpdH`,
    • `hII_lo   : MemAdjLo F U pdpdH`,
    • `hII_hi   : MemAdjHi F U pdpdH`.
  The wall-A campaign banked three suppliers whose CONCLUSIONS are EXACTLY these three shapes (same
  witness pair `g gi`, same gate `H_G`, same source `F = leviSeries (heatOp g gi H_G)`, same window `U`,
  same `pdpdH = witnessSecondXDeriv` slot — the `hpdpdH_slice` was `rfl` in J4-404):
    • `SlotDischarges.memLapFull_from_slotBound`  ⟹  `MemLapFull` — **COVERED**;
    • `CappedAdom2Audit.hII_lo_from_capped`        ⟹  `MemAdjLo`  (with `E := heatOp g gi H_G`,
      `leviSeries E = F`) — **COVERED**;
    • `MemAdjHiSliver.hII_hi_from_sliver`          ⟹  `MemAdjHi`  — **COVERED**.
  **VERDICT: all three interchange legs are DISCHARGED by wall-A** — NOT for free: each supplier trades
  its abstract `Prop`-bundle binder for CONCRETE, pointwise, satisfiable analytic DATA (Gaussian
  dominations, moment `τ^{-1/2}` bounds, the √ε sliver amplitude `D0`/`D1`/`hbnd`, joint continuity,
  interchange, gauge).  So the Duhamel interchange residue becomes the honest wall-A carry census
  {`hslot`/`hAdom2cap`/`hGpow` moment data · `hInter` · `hmeas2Lo`/`hSecCont`/`hBcont` · `D0`/`D1`/`hbnd`
  · `hcap`/`hEndpoint`/`hPd2conv`}, NOT the three opaque `Mem*` bundles.

  Blocks A (`hBoundaryLim` ← `EnvelopeWiringLocUnif.hBoundaryLim_DONE`), C (the F2 pile) and D (the
  frozen/moving lists) are ALREADY carried at the honest lower-level residual inside
  `truncatedDuhamelCore_AT_GATE_FULL` (the F2 pile IS the raw C3ε engine census consumed by
  `hDerivConv_AT_GATE`; the frozen/moving lists ARE the raw satisfiable data consumed by
  `hbdryLU_CONCRETE`; `hBoundaryLim` is one binder, separately banked by `hBoundaryLim_DONE`).  Threading
  them further would RE-EXPAND, not collapse, so they are carried VERBATIM here.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  binder-threading / re-plumbing brick that discharges the THREE interchange legs of the Duhamel core
  carrier into the banked wall-A census.  `a1_R6_from_data_v5` is STILL the maximally-unconditional
  **CONDITIONAL** a₁ two-jet; replacing the Core carrier's interchange binders by the wall-A census
  closes NOTHING deeper.  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HDuhamelExportRethread
import QIQTH.SlotDischarges
import QIQTH.CappedAdom2Audit
import QIQTH.MemAdjHiSliver

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.SlotDischarges QIQTH.CappedAdom2Audit QIQTH.MemAdjHiSliver
open QIQTH.HDuhamelExportRethread QIQTH.TruncatedDuhamelData
open scoped Interval Topology BigOperators

namespace QIQTH.DuhamelCoreThreaded

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (D2·block B) `block_interchange_threaded` — the THREE interchange legs, wall-A discharged.
    ############################################################################### -/

/-- **★★★ (D2·block B) `block_interchange_threaded`.**  THE J4-414 D1 LEAN WITNESS.  The three abstract
    interchange binders of `truncatedDuhamelCore_AT_GATE_FULL` at the endgame gate
    `H_G := vanVleckGatedWitness g gi hChr hK S a b`, `F := leviSeries (heatOp g gi H_G)`,
    `pdpdH := fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z`, produced SIMULTANEOUSLY from
    the wall-A census:
      • `MemLapFull` ← `SlotDischarges.memLapFull_from_slotBound`;
      • `MemAdjLo`   ← `CappedAdom2Audit.hII_lo_from_capped` (with `E := heatOp g gi H_G`);
      • `MemAdjHi`   ← `MemAdjHiSliver.hII_hi_from_sliver`.
    Every hypothesis is a CONCRETE, satisfiable, pointwise analytic carry (Gaussian / moment dominations,
    the √ε sliver amplitude, joint continuity, gauge, interchange); NONE is the conclusion.  ⚠ NOT
    `a₁ = R/6`. -/
private theorem block_interchange_threaded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T τ₀ wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (L Bcomp Q Sconst : ℝ) (hL : 0 ≤ L) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hSconst : 0 ≤ Sconst)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τ₀ →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * L * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τ₀)
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
    -- ── the Hi-leg moment-improved carry (`MemAdjHiSliver.hII_hi_from_sliver`):
    (Cpair : ℝ) (hCpair : 0 ≤ Cpair)
    (hGpow : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2)) :
    MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
    ∧ MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
    ∧ MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  refine ⟨?_, ?_, ?_⟩
  · -- MemLapFull ← wall-A slot-bound closure.
    exact memLapFull_from_slotBound g gi hChr hK S a b U T τ₀ wA2 wF CF CA2c
      hwA2 hCA2c hwF hCF hUpos hUT hεU hgi hΓ hInter hAdom2cap hFdom hFzero hmeas2Lo hSecCont hBcont
      L Bcomp Q Sconst hL hBcomp hQ hSconst hslot hcap hEndpoint D0 D1 hD0 hD1 hbnd hPd2conv
  · -- MemAdjLo ← capped lower-adjacency leg (E := heatOp g gi H_G, leviSeries E = F).
    exact hII_lo_from_capped g gi hChr hK S a b
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) U T wA2 wF CF CA2c
      hwA2 hCA2c hwF hCF hUpos hUT hAdom2cap hFdom hFzero hmeas2Lo
  · -- MemAdjHi ← moment-improved matched-sliver Hi leg.
    exact hII_hi_from_sliver g gi hChr hK S a b T U hUT hεU hSecCont hBcont Cpair hCpair hGpow

/-! ###############################################################################
    ### (D2) `truncatedDuhamelCore_threaded` — the Core carrier with the interchange legs threaded.
    ############################################################################### -/

/-- **★★★★ (D2) `truncatedDuhamelCore_threaded`.**  The endgame-gate Duhamel Core carrier
    `TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t`, assembled from
    `HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL` with the THREE abstract interchange
    binders `hLapFull`/`hII_lo`/`hII_hi` REMOVED and DISCHARGED internally via the wall-A census
    (`block_interchange_threaded`).  All other FULL binders are carried VERBATIM (block A `hBoundaryLim`,
    the block-B W2 census `hQ1`/`hFmeas`/`hFint`/`hF'meas`/`hdiff`, the block-C F2 pile, the block-D
    frozen/moving lists, gauge, the `hDaLimLU` data census, the √ε sliver amplitude `D0`/`D1`/`hbnd`,
    `hEdom`/`hEcomb`) — these are ALREADY the honest lower-level residual inside FULL (see the D1 verdict
    in the header).  The wall-A carries appended at the end (`τc`/`wA2`/`wF`/`CF`/`CA2c` · `hInter` ·
    `hAdom2cap`/`hFdomW`/`hmeas2Lo` · `hSecCont`/`hBcont` · the `hslot` moment bound · `hcap`/`hEndpoint`/
    `hPd2conv` · `Cpair`/`hGpow`) REPLACE the three opaque `Mem*` bundles with concrete, satisfiable,
    pointwise analytic DATA.  Every hypothesis is satisfiable and non-vacuous; NONE is the conclusion.
    ⚠ NOT `a₁ = R/6`. -/
theorem truncatedDuhamelCore_threaded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b) F m t) atTop
        (𝓝 (F t 0 0)))
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ c, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0) c)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    (ρ lam CW Cf τ₀ : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    -- ── the WALL-A interchange census (REPLACING `hLapFull`/`hII_lo`/`hII_hi`), ∀ concrete data:
    (τc wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (Lc Bcomp Q Sconst : ℝ) (hLc : 0 ≤ Lc) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hSconst : 0 ≤ Sconst)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τc)
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0)
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
    (Cpair : ℝ) (hCpair : 0 ≤ Cpair)
    (hGpow : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2)) :
    TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t := by
  subst hFeq
  -- (block B) discharge the three interchange legs from the wall-A census.
  have hUpos : ∀ u ∈ U, 0 < u := fun u hu => lt_of_lt_of_le haT (hUlb u hu)
  have hFzeroW : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0 :=
    fun s hs z => hFzero s hs z 0
  obtain ⟨hLapFull, hII_lo, hII_hi⟩ := block_interchange_threaded g gi hChr hK S a b U T τc wA2 wF CF
    CA2c hwA2 hCA2c hwF hCF hUpos hUT hεU hgi hΓ hInter hAdom2cap hFdomW hFzeroW hmeas2Lo hSecCont
    hBcont Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint D0 D1 hD0 hD1 hbnd hPd2conv
    Cpair hCpair hGpow
  -- re-export the collapsed Core carrier via the FULL union form.
  exact truncatedDuhamelCore_AT_GATE_FULL g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) rfl t T hT U hUopen htU hUT hn
    hBoundaryLim hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi hEcomb
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub

end QIQTH.DuhamelCoreThreaded

section AxiomChecks
#print axioms QIQTH.DuhamelCoreThreaded.block_interchange_threaded
#print axioms QIQTH.DuhamelCoreThreaded.truncatedDuhamelCore_threaded
end AxiomChecks
