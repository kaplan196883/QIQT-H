/-
  HDConvAtGateConstGateHAdom — J4-1103: specialize `HDConvGateThreading.hDConv_AT_GATE`'s gate `S` to
  the CONCRETE flow-ball gate `constGate g gi hChr hK c` and discharge its `hAdom`/`hWDom` census
  members (+ the entire `τ₀/CW/lam` sub-bundle) INTERNALLY from the already-banked
  `HAdomHWDomFromConcreteDominations.hAdom_hWDom_from_gateSqControl` fed the CONCRETE `GateSqControl`
  certificate `GateSqControlFromFlowBall.gateSqControl_constGate` (J4-900), which routes through the
  chart-reachability / near-isometry machinery (`uniformInverseChart_leftInverse_of_lt` +
  `uniformFlowExp_hdisp_ball`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  COMPOSITION / gate-specialization brick.  No `sorry` (header prose excepted), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS DISPATCH.  J4-1102's own header flagged an OPEN follow-up: `hAdom`'s literal `∀ p q` type
  in `HDConvGateThreading.hDConv_AT_GATE` is strictly stronger than the `p = 0`-only
  `WideAmplitudeData.zeroth_domination_global`, and was described as needing "a separate, not-yet-
  attempted refactor".  Direct audit (this dispatch) traced the on-gate unfold
  (`AmplitudePackage.vanVleckGatedWitness_gate_apply`) and confirmed: for GENERAL `(p, q)` the on-gate
  value routes through `uniformInverseChart g gi hC hK q p` — the chart evaluated at a MOVING base point
  `p`, not the fixed `p = 0` slice — so bridging `zeroth_domination_global` to the general-`p` `hAdom`
  genuinely is NOT a trivial restatement; it requires chart/near-isometry machinery.

  BUT that machinery is ALREADY BUILT AND BANKED, TWICE:
    (a) `GateSqControlFromFlowBall.gateSqControl_constGate` + `HAdomHWDomFromConcreteDominations.
        hAdom_hWDom_from_gateSqControl` (J4-900, abstract in the metric `g gi`) — together discharge
        BOTH `hAdom` (exact `∀ p q` shape, unconditional `τ > 0`) AND `hWDom` simultaneously, for
        `S := constGate g gi hChr hK c` (the flow-ball gate), for every small enough radius `c ≤ c₀`,
        from geometry (`GateSqControl`, itself proved from `uniformInverseChart_leftInverse_of_lt` +
        `uniformFlowExp_hdisp_ball`) plus the one standing smoothness carry `hw`.
    (b) `CurvedHDConvSlotThreading.curvedHDConv_fed_slots_at_constGate` (J4-679) re-derives the SAME
        width-3/2 `hAdom` shape at the CURVED witness specifically — confirming (a) is not an isolated
        curiosity but the general pattern the curved tower already leans on.

  So `hAdom` is NOT "not yet attempted" — it is ALREADY discharged for `S := constGate`.  What was
  missing (per `gpt-5.6-sol` (high) consult, 2026-08-24, confirming this exact scope): a file that
  SPECIALIZES `HDConvGateThreading.hDConv_AT_GATE`'s abstract-`S` statement to `S := constGate g gi hChr
  hK c`, for a `c` known SMALL ENOUGH (`c ≤ flowBallRadiusThreshold …`), and feeds (a)'s output in,
  shrinking the exposed binder list by the `hAdom` sub-bundle (`A₀ A₁ hA₀ hA₁ hAdom`, 5 binders) AND the
  `hWDom` sub-bundle (`τ₀ hτ₀ CW lam hCW hlam hWDom`, 7 binders) — 12 binders total — at the cost of
  THREE mild new carries `ha : 0 < a`, `hab : a < b`, `hw` (the standing amplitude-smoothness carry) plus
  the radius-window side-condition `hcle : c ≤ flowBallRadiusThreshold g gi hChr hK` (satisfiable —
  see NON-VACUITY below).  Fixing `c` UP FRONT (rather than existentializing it inside the theorem, as an
  earlier draft attempted) keeps the abstract source `F` genuinely abstract with a single `hFeq`, exactly
  mirroring `hDConv_AT_GATE`'s own shape — no `F`-threading complications.  This dispatch lands exactly
  that.  Sol flagged (and this file respects): do NOT combine this with J4-1102's
  `HDConvGateCensusDerivWired.hDConv_derivSide_census_wired` `hgate` binder — that binder's own
  universally-quantified field slot forces `S z = Set.univ` on `K`, which is INCOMPATIBLE with the
  finite-radius `constGate` for nonempty `K` (a genuine, file-scoped vacuity trap Sol caught) — so this
  file touches ONLY `hDConv_AT_GATE`'s `hAdom`/`hWDom`, never `hDConv_derivSide_census_wired`'s `hgate`.

  ## NON-VACUITY.  `flowBallRadiusThreshold g gi hChr hK := (gateSqControl_constGate …).choose` is an
  EXPLICIT `c₀ = min δ₀ r₁ > 0` produced from geometry alone (chart-inverse germ + near-isometry budget,
  both independently banked with their own positive radii) — `flowBallRadiusThreshold_pos` proves it
  positive, so the side-condition `0 < c ∧ c ≤ flowBallRadiusThreshold …` is genuinely satisfiable
  (e.g. `c := flowBallRadiusThreshold …` itself), not an empty window.

  ⚠  STILL NOT `a₁ = R/6`.  `hDConv_AT_GATE`'s OTHER ~40 census members (DaLimLU diff-under-∫∫ families,
  `MemLapFull`/`MemAdjLo`/`MemAdjHi`/`MemECombine`, the F2 pile, `hIlo`/`hIhi`, the frozen/moving list
  minus `hWDom`) remain FULLY OPEN, untouched by this brick — this is a 12-binder reduction out of ~50,
  not a discharge of the arrow.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.
-/
import Mathlib
import QIQTH.HDConvGateThreading
import QIQTH.GateSqControlFromFlowBall
import QIQTH.InnerKernelJointMeas

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.ETailRateBound QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.HDConvGateThreading QIQTH.GateSqControlFromFlowBall QIQTH.A1R6CoreAtGate
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HAdomHWDomFromConcreteDominations QIQTH.ResidueBound
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HDConvAtGateConstGateHAdom

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The satisfiable radius-window threshold (from `gateSqControl_constGate`).
    ############################################################################### -/

/-- **`flowBallRadiusThreshold`.**  A concrete positive gate-radius threshold `c₀` — the `Classical.choose`
    witness of `GateSqControlFromFlowBall.gateSqControl_constGate` — below which the flow-ball gate
    `constGate g gi hChr hK c` carries the `GateSqControl` chart/near-isometry certificate. ⚠ NOT
    `a₁ = R/6`. -/
noncomputable def flowBallRadiusThreshold (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) : ℝ :=
  (QIQTH.GateSqControlFromFlowBall.gateSqControl_constGate g gi hChr hK).choose

/-- **`flowBallRadiusThreshold_pos`.**  The threshold is positive. ⚠ NOT `a₁ = R/6`. -/
theorem flowBallRadiusThreshold_pos (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    0 < flowBallRadiusThreshold g gi hChr hK :=
  (QIQTH.GateSqControlFromFlowBall.gateSqControl_constGate g gi hChr hK).choose_spec.1

/-- **`flowBallRadiusThreshold_spec`.**  Below the threshold, the flow-ball gate carries the
    `GateSqControl` certificate. ⚠ NOT `a₁ = R/6`. -/
theorem flowBallRadiusThreshold_spec (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) (hc : 0 < c)
    (hcle : c ≤ flowBallRadiusThreshold g gi hChr hK) :
    GateSqControl K (constGate g gi hChr hK c) (uniformInverseChart g gi hChr hK) :=
  (QIQTH.GateSqControlFromFlowBall.gateSqControl_constGate g gi hChr hK).choose_spec.2 c hc hcle

/-! ###############################################################################
    ### J4-1103 — `hDConv_AT_GATE` specialized to `constGate`, `hAdom`/`hWDom` DISCHARGED.
    ############################################################################### -/

/-- **★★★ J4-1103 — `hDConv_AT_GATE_constGate`.**  `HDConvGateThreading.hDConv_AT_GATE` at the concrete
    flow-ball gate `S := constGate g gi hChr hK c` (for `c` below `flowBallRadiusThreshold`), with its
    `hAdom` (5 binders: `A₀ A₁ hA₀ hA₁ hAdom`) and `hWDom` (7 binders: `τ₀ hτ₀ CW lam hCW hlam hWDom`)
    sub-bundles DISCHARGED INTERNALLY from `HAdomHWDomFromConcreteDominations.
    hAdom_hWDom_from_gateSqControl` fed the concrete `GateSqControl` certificate
    (`flowBallRadiusThreshold_spec`, J4-900 chart/near-isometry machinery). All other ~40
    `hDConv_AT_GATE` census members are carried verbatim (untouched, still fully open). Three mild new
    carries `ha : 0 < a`, `hab : a < b`, `hw` (standing amplitude smoothness) plus the radius side
    condition `hcle` are required by the discharge. ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_AT_GATE_constGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) (hc : 0 < c)
    (hcle : c ≤ flowBallRadiusThreshold g gi hChr hK)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k : Point n → ℝ))
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c)
        a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    -- ── the `hDaLimLU` data census (from `hDaLimLU_concrete`), at `S = constGate g gi hChr hK c` ──────
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F
            u (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
            (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
            (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i
              (u - s) (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w)
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (hII_lo : MemAdjLo F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (hII_hi : MemAdjHi F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u)
    (hEdom : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
              * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
              * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F)
    -- ── the F2 pile + `hFII` pile (for `hDConv_W1free`), `hAdom`/`hWDom` DROPPED (discharged below) ──
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
          * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ u ∈ U, c₁ ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b
            (u - s) 0 z * F s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ cc, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (cc - s) 0 z
        * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
        * F s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r
          0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z)
          (cc - s) * F s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      HasDerivAt (fun cc => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b
          (cc - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z)
          (cc - s) * F s z 0) cc)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F (u + h)
          (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F (u + h)
              (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F u
              (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F u
              (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- ── the frozen/moving satisfiable lists (for `hbdryLU_CONCRETE`), `hWDom` sub-bundle DROPPED ──────
    (ρ Cf Cmass : ℝ) (ta tb : ℝ) (hρ : 0 < ρ)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z)
        volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hmass : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b
        (epsSeq m) (0 : Point n) z| ≤ Cmass)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (epsSeq m)
            (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb) :
    DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
        u 0 0) t := by
  -- discharge `hAdom` + `hWDom` from the CONCRETE `GateSqControl` certificate at this fixed `c`.
  obtain ⟨A₀, A₁, hA₀, hA₁, CW, lam, hCW, hlam, hAdomC, hWDomC⟩ :=
    QIQTH.HAdomHWDomFromConcreteDominations.hAdom_hWDom_from_gateSqControl g gi hChr hK
      (constGate g gi hChr hK c) a b ha hab (1 : ℝ) one_pos hw
      (flowBallRadiusThreshold_spec g gi hChr hK c hc hcle)
  -- `hAzero` — the witness vanishes at `τ ≤ 0`: off-gate trivially (`gatedKernel_apply_of_notMem`),
  -- on-gate because the underlying `N = 1` parametrix's leading `gaussDdim τ` factor vanishes
  -- (`heatParametrix_eq_zero_of_nonpos`, `0 < n` from `hn : 1 ≤ n`).
  have hAzeroC : ∀ τ, τ ≤ 0 → ∀ p q : Point n,
      vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ p q = 0 := by
    intro τ hτ p q
    unfold vanVleckGatedWitness
    by_cases hq : q ∈ K
    · by_cases hp : p ∈ constGate g gi hChr hK c q
      · rw [QIQTH.HeatResidualBound.gatedKernel_apply_of_mem K _ _ τ hq hp]
        simp only [globalCutoffParametrixWitnessN]
        rw [QIQTH.InnerKernelJointMeas.heatParametrix_eq_zero_of_nonpos hn 1 _ _ τ _ hτ]
        ring
      · exact QIQTH.HeatResidualBound.gatedKernel_apply_of_notMem K _ _ τ p q (Or.inr hp)
    · exact QIQTH.HeatResidualBound.gatedKernel_apply_of_notMem K _ _ τ p q (Or.inl hq)
  -- `hDConv_AT_GATE` demands ONE shared constant bounding both `hWDom` and `hmass`; `CW` (from the
  -- geometry discharge) and `Cmass` (the caller's mass carry) are a priori unrelated, so widen both to
  -- `CW' := max CW Cmass` (sound: `gaussDdim ≥ 0`, so `CW * g ≤ CW' * g`; and `Cmass ≤ CW'` directly).
  set CW' : ℝ := max CW Cmass with hCW'def
  have hCW' : 0 ≤ CW' := le_trans hCW (le_max_left CW Cmass)
  have hWDomC' : ∀ τ : ℝ, 0 < τ → τ ≤ (1 : ℝ) → ∀ z : Point n,
      |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z|
        ≤ CW' * gaussDdim (lam * τ) z := by
    intro τ hτ hτ1 z
    exact le_trans (hWDomC τ hτ hτ1 z)
      (mul_le_mul_of_nonneg_right (le_max_left CW Cmass) (gaussDdim_nonneg _ _))
  have hmass' : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b
      (epsSeq m) (0 : Point n) z| ≤ CW' :=
    hmass.mono (fun m hm => le_trans hm (le_max_right CW Cmass))
  exact QIQTH.HDConvGateThreading.hDConv_AT_GATE g gi hChr hK (constGate g gi hChr hK c) a b F hFeq
    t T hT U hUopen htU hUT hn
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi hEcomb
    A₀ A₁ hA₀ hA₁ hAdomC hAzeroC
    hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff
    L hLnn hCross
    ρ lam CW' Cf (1 : ℝ) ta tb hρ hlam hCW' one_pos hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDomC' hmass' hmassone hmod hsup hUsub

end QIQTH.HDConvAtGateConstGateHAdom

section AxiomChecks
open QIQTH.HDConvAtGateConstGateHAdom
#print axioms flowBallRadiusThreshold_pos
#print axioms flowBallRadiusThreshold_spec
#print axioms hDConv_AT_GATE_constGate
end AxiomChecks
