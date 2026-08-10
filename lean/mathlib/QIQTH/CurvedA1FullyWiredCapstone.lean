/-
  CurvedA1FullyWiredCapstone — J4-551.  THE FULLY-WIRED curved Seeley–DeWitt a₁ two-jet capstone at the
  genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This ASSEMBLES the curved a₁ two-jet capstone
  `CurvedA1Assembled.curved_a1_R6_assembled` at `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`, with:
    • the 8-member geometric gauge bundle (`hg`/`hgsymm`/`hgiC`/`hg0`/`hgi`/`hΓ`/`hdg0`/`hGauss`)
      DISCHARGED from `CurvedRNCGaugeBundle.curvedRNC_geomGaugeBundle` (J4-525);
    • `hgpos` (det > 0) DISCHARGED from `CurvedRNCPosDef.curvedRNCMetric_det_pos` (`K ≤ 0`);
    • LEG 1 `hDa` FED by `CurvedA1FullyWired.curved_hDa_at_gate` (J4-549);
    • LEG 2 `core` FED by `CurvedA1Leg2Core.curved_core_at_gate` (J4-550).
  The two legs' shared binders (the matched-sliver `MemAdjHi` moment, the W2 differentiation-under-∫
  family, the capped 2nd-derivative Gaussian family `hAdom2cap`, `hmeasLo`/`hmeasHi`/`hmeas2Lo`,
  `hPd2conv`, `wA`/`CA`/`wA2`/`CA2c`, `hK0`/`hframeK`) are UNIFIED — bound ONCE and consumed by both.

  ## Two theorems

  * `curved_a1_R6_geomWired` — the INTERMEDIATE capstone: `curved_a1_R6_assembled` with ONLY the
    `g`/`gi`-geometry binders discharged (gauge bundle + `hgpos`); `hDa`/`core` remain EXTERNAL binders.
  * `curved_a1_R6_fully_wired` — the FULL capstone: `curved_a1_R6_geomWired` with `hDa`/`core` FED by the
    two curved leg suppliers (J4-549/550), leaving ONLY the analytic/physical residuals.

  ## What is CARRIED (honest residue of `curved_a1_R6_fully_wired`)

    • MemAdjHi/matched-sliver moment (shared `hII_hi`), MemAdjLo (`hII_lo`), MemInterchange (`hInter`),
      MemECombine (`hEcomb`) — the convergence-census members;
    • the convergence trio: the Levi source envelope (`dataLevi`), the E-combination
      (`DaTrunc`/`LapTrunc` reps `hDa`/`hLap`/…), the atomic interchange `hPd2conv`, the W2
      differentiation-under-∫ family, the `hBoundaryLim`/frozen-moving boundary lists;
    • the measurability/window carriers (`hmeasLo`/`hmeasHi`/`hmeas2Lo`/`hFmeas`/… + the gate package
      `hpkgBound`/`hmemS0`/`hopenS0`/`hS1` + window `U`/`aa`/`hau`);
    • the SDW source `hsrc` (`transportCoeff` regularity) and the Section-A/C/G/H analytic-census carries.

  ⚠  `a₁ = R/6` stays CONDITIONAL.  The fully-wired curved a₁ two-jet holds for `g^K` (`κ < 0`) only
  GIVEN the carried residuals — they are owed analytic/physical inputs; the coefficient is NOT
  unconditional.  For `g^K` the conclusion coefficient `(∑_i ricci (curvedRNCMetric κ) (curvedRNCInv κ)
  i i 0)/6 = n(n−1)κ/6 ≠ 0` (`curvedRNCMetric_ricci_trace_diag_ne`) — genuinely curved, NOT flat-only.
  No `sorry`, no new axioms, no `:= True`, no hypothesis = conclusion, no existing file edited.  NOT
  `a₁ = R/6`. -/
import Mathlib
import QIQTH.CurvedA1Assembled
import QIQTH.CurvedA1FullyWired
import QIQTH.CurvedA1Leg2Core
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCPosDef

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.HEmeasRecon QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami
open QIQTH.CConvV2DerivRep QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.LeviSeriesLocalData QIQTH.GaussianWidthTolerant QIQTH.HeatKernelA1
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.VanVleck
open QIQTH.NCRiemannTwoJet QIQTH.GlobalRawBoundFacade QIQTH.HDuhamelExportRethread
open QIQTH.HDConvGateThreading QIQTH.CConvV2Facade QIQTH.A1R6CoreAtGate
open QIQTH.A1R6SlotAdapters QIQTH.HDerivConvComposition
open QIQTH.RadialDistance QIQTH.A1R6FromLabelled QIQTH.CurvedRNCGaussWitness
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening
open QIQTH.CappedAdom2Audit QIQTH.DaLimLUCapped QIQTH.DaLimLUCappedStep2 QIQTH.DaLimLUCappedStep3
open QIQTH.GaussGaugeToHgauge QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.CurvedA1Assembled QIQTH.CurvedA1FullyWired QIQTH.CurvedA1Leg2Core
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.CurvedA1FullyWiredCapstone

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-- **★★★ J4-551 (helper) — `curved_a1_R6_geomWired`.**  The curved a₁ two-jet capstone
    `curved_a1_R6_assembled` at `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ` (`κ < 0`), with ONLY the
    `g`/`gi`-geometry binders discharged: the 8-member gauge bundle from `curvedRNC_geomGaugeBundle`
    (J4-525) and `hgpos` from `curvedRNCMetric_det_pos`.  `hDa`/`core` remain EXTERNAL binders (fed by the
    legs in `curved_a1_R6_fully_wired`).  Same conclusion as `curved_a1_R6_assembled`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_a1_R6_geomWired (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (t T : ℝ) (ht : 0 < t) (hT : 0 < T) (hn : 1 ≤ n)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (a b c C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ) (curvedRNCInv κ) (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ) (curvedRNCInv κ)) 0)))
    -- ═══ SECTION C — the constant-radius package facts ═══
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0))
    (hS1 : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))
    -- ═══ SECTION D — ★ LEG 1 (Da-limit) — the capped-route output, EXTERNAL binder (J4-541) ═══
    (hDa : DaLimLUGoal (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
      (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U)
    -- ═══ SECTION E — ★ LEG 2 (Duhamel-core) — the capped-route output, EXTERNAL binder (J4-547) ═══
    (core : TruncatedDuhamelCore (curvedRNCMetric κ) (curvedRNCInv κ)
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) t)
    -- ═══ SECTION F — the W1-free boundary loc-unif slot, EXTERNAL binder ═══
    (hbdry : QIQTH.LocUnifDerivConv.hbdryLUTarget
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
      (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U)
    -- ═══ SECTION G — the hDConv F2 regularity census (for `a1_R6_slots_AT_GATE`) ═══
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ p q = 0)
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ cc : ℝ, 0 < cc ∧ ∀ u ∈ U, cc ≤ u)
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ cc, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (u - s)
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      HasDerivAt (fun cc => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) cc)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
          (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- ═══ SECTION H — the hCConv sliver census (for `a1_R6_slots_AT_GATE`) ═══
    (uSet : Set (Point n)) (hu_open : IsOpen uSet) (hu0 : (0 : Point n) ∈ uSet)
    (hlin : ∀ x ∈ uSet, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
          (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) t
          (Function.update x i w) 0)
        ((Dmap (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z,
          witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet) :
    heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (trueHeatKernel (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i : Fin n, ricci (curvedRNCMetric κ) (curvedRNCInv κ) i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ) (curvedRNCInv κ)) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
                            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  obtain ⟨hg, hgsymm, hgiC, hg0, hgi, hΓ, hdg0, hGauss, hinvF⟩ := curvedRNC_geomGaugeBundle κ hκ
  exact curved_a1_R6_assembled (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK hK0 t T ht hT hn
    U hUopen htU hUpos hUT a b c C ha hab hbc hCnn
    hg hgsymm hgiC (fun v => curvedRNCMetric_det_pos κ hκ.le v) hg0 hgi hΓ hdg0 hsrc hGauss
    hpkgBound hmemS0 hopenS0 hS1 hDa core hbdry
    A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hFdom hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    uSet hu_open hu0 hlin sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb
    hbulkderiv hbulk_tendsto hsliver hcont


/-- **★★★ J4-551 — `curved_a1_R6_fully_wired` — THE FULLY-WIRED curved a₁ TWO-JET CAPSTONE at `g^K`.**
    `curved_a1_R6_geomWired` with LEG 1 `hDa` FED by `curved_hDa_at_gate` (J4-549) and LEG 2 `core` FED by
    `curved_core_at_gate` (J4-550), at `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ` (`κ < 0`).  The two
    legs' shared binders (matched-sliver `MemAdjHi` `hII_hi`, the W2 diff-under-∫ family, `hAdom2cap`,
    `hmeasLo`/`hmeasHi`/`hmeas2Lo`, `hPd2conv`, `wA`/`CA`/`wA2`/`CA2c`, `hK0`/`hframeK`, `aa`/`haa`/`hau`)
    are UNIFIED — bound once, consumed by both.  Discharges the geometric gauge bundle + `hgpos` internally.
    Carries ONLY the analytic/physical residuals: the `MemAdjHi`/`MemAdjLo`/`MemInterchange`/`MemECombine`
    census, the convergence trio (Levi envelope / E-combination / `hPd2conv`), the measurability/window
    carriers + gate package (`hpkgBound`/`hmemS0`/`hopenS0`/`hS1`), the SDW source `hsrc`, and the
    Section-G/H analytic census.  For `g^K` the coefficient `(∑_i ricci (curvedRNCMetric κ)
    (curvedRNCInv κ) i i 0)/6 = n(n−1)κ/6 ≠ 0` — genuinely curved.  ⚠ `a₁ = R/6` stays CONDITIONAL. -/
theorem curved_a1_R6_fully_wired (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    -- ═══ gauge FROM GEOMETRY raw inputs (feed both the outer `hgi`/`hΓ` and `curved_leg2_hLapFull`) ═══
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, (curvedRNCMetric κ) q i j = (if i = j then (1 : ℝ) else 0))
    -- ═══ LEG-2 numeric parameters (for `curved_leg2_hLapFull`) ═══
    (wA CA wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    -- ═══ LEG-2 analytic residuals (frozen-side interchange + strip/LO dominations + Pd2 carrier) ═══
    (hInter : MemInterchange (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z))
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u x 0) i y) i 0)))
    -- ═══ SHARED (leg-2 ∧ FULL): the matched-sliver `MemAdjHi` residual + the √ε sliver amplitude bundle ═══
    (hII_hi : MemAdjHi (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    -- ═══ FULL-only: the W1-free boundary slot ═══
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) m t) atTop
        (𝓝 (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) t 0 0)))
    -- ═══ FULL-only: the W2 differentiation-under-∫ family ═══
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) y z
                * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
            (∫ z, witnessFieldDeriv2 (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) w)
    -- ═══ FULL-only: the LO adjacency member + Gaussian dominations + strip integrabilities + E-combine ═══
    (hII_lo : MemAdjLo (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z))
    (E₀ E₁ C_L aa : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haa : 0 < aa)
    (hau : ∀ u ∈ U, aa ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n,
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))))
    -- ═══ FULL-only: the F2 regularity pile + hFII tail-integrability pile (for `hDerivConv_AT_GATE`) ═══
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ cc : ℝ, 0 < cc ∧ ∀ u ∈ U, cc ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ cc, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (u - s)
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      HasDerivAt (fun cc => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) cc)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
          (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- ═══ FULL-only: the frozen/moving satisfiable lists (for `hbdryLU_CONCRETE`) ═══
    (ρ lam CW Cf τ0fr : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ0fr : 0 < τ0fr)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ0fr → ∀ z,
      |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n)
            - leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)
            - leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    (CLevi : ℝ) (dataLevi : LeviSeriesLocalData
        (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) CLevi T)
    (τ₀ : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) i T τ₀)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    (P : ℝ) (hP : 0 ≤ P)
    (hraw : GlobalGatedRawBound (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) P)
    (hDa_ec : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (u - s)
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ) (fun x => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) x z) 0
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ) (fun x => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) x z) 0
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ) (fun x => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) x z) 0
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (ht : 0 < t)
    (C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ) (curvedRNCInv κ) (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ) (curvedRNCInv κ)) 0)))
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0))
    (hS1 : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))
    (hbdry : QIQTH.LocUnifDerivConv.hbdryLUTarget
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
      (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U)
    (uSet : Set (Point n)) (hu_open : IsOpen uSet) (hu0 : (0 : Point n) ∈ uSet)
    (hlin : ∀ x ∈ uSet, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
          (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) t
          (Function.update x i w) 0)
        ((Dmap (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z,
          witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet) :
    heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (trueHeatKernel (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i : Fin n, ricci (curvedRNCMetric κ) (curvedRNCInv κ) i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ) (curvedRNCInv κ)) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
                            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  have hUpos : ∀ u ∈ U, 0 < u := fun u hu => lt_of_lt_of_le haa (hau u hu)
  refine curved_a1_R6_geomWired κ hκ hChr hK hK0 t T ht hT hn U hUopen htU hUpos hUT a b c C ha hab hbc hCnn hsrc hpkgBound hmemS0 hopenS0 hS1 ?_ ?_ hbdry
    A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hFdom hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    uSet hu_open hu0 hlin sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb hbulkderiv hbulk_tendsto hsliver hcont
  · exact curved_hDa_at_gate κ hκ hChr hK a b c T U hUopen hn hK0 hframeK V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff aa haa hau hUT CLevi dataLevi wA CA wA2 CA2c hwA hCA hwA2 hCA2c hAdomHeat hAdom2cap hmeasLo hmeasHi hmeas2Lo hII_hi τ₀ dataAmp hεaa hετ₀ P hP hraw hPd2conv hDa_ec hLap hLapZ hEZ hLapS hES
  · exact curved_core_at_gate κ hκ hChr hK a b c t T hT U hUopen htU hUT hn hK0 hframeK wA CA wA2 wF CF CA2c hwA hCA hwA2 hCA2c hwF hCF hInter hAdomHeat hAdom2cap hFdomW hmeasLo hmeasHi hmeas2Lo hPd2conv hII_hi D0 D1 hD0 hD1 hbnd hBoundaryLim V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff hII_lo E₀ E₁ C_L aa hE₀ hE₁ hC_L haa hau hEdom hFdom hFzero hIlo hIhi hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross ρ lam CW Cf τ0fr ta tb hρ hlam hCW hτ0fr hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd hWDom hmass hmassone hmod hsup hUsub

/-- **★ J4-551 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `K ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric K` is nonzero, so the fully-wired capstone's
    conclusion coefficient `n(n−1)K/6 ≠ 0` is genuinely curved.  NOT `a₁ = R/6`. -/
theorem curved_a1_R6_fully_wired_curved_satisfiable (K : ℝ) (hK : K ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) K y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne K hK hn c

end QIQTH.CurvedA1FullyWiredCapstone

section AxiomChecks
open QIQTH.CurvedA1FullyWiredCapstone
#print axioms curved_a1_R6_geomWired
#print axioms curved_a1_R6_fully_wired
#print axioms curved_a1_R6_fully_wired_curved_satisfiable
end AxiomChecks
