/-
  HDConvLiveGateWired — the `hDConv` analog of `HDuhamelLiveGateWired` (J4-895): the pure,
  audit-verified OPAQUE→NAMED conversion of the LIVE order-1 capstone's `hDConv` antecedent.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure COMPOSITION / API-alignment / wiring brick — it reduces the LIVE order-1 capstone's opaque
  carried `hDConv` antecedent (an unnamed `DifferentiableAt` in the RAW `gatedKernel` /
  `globalCutoffParametrixWitnessN` form) to the ALREADY-BANKED, fully-enumerated census of
  `HDConvGateThreading.hDConvSlot_AT_GATE`.  No `sorry` (header prose excepted), no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding)
  the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE EXACT-GATE MATCH (character-checked, load-bearing).

  The LIVE capstone
  `GatedGlobalWitnessN1CapstoneReachAligned.trueKernel_diagonal_a1_eq_R6_residual_N1_reachAligned`
  chooses its concrete order-1 kernel as
      `H := gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)`
      `        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK))`
  with `S := fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c`, and carries the
  opaque `hDConv` antecedent
      `DifferentiableAt ℝ (fun w => heatConv H (leviSeries (heatOp g gi H)) w 0 0) t`.

  Now `vanVleckGatedWitness g gi hChr hK S a b` is DEFINED (`ConvApproximants`) as EXACTLY that
  `gatedKernel …` form, so the capstone's `H` is **definitionally (`rfl`) equal** to
  `vanVleckGatedWitness g gi hChr hK S a b` — the kernel `HDConvGateThreading` was built against.  This
  is verified below by the `rfl` `example gateForm_eq_vanVleckGatedWitness`, so the wiring instantiates
  at the capstone's OWN `g, gi, hChr, hK, S, a, b, t` with NO adapter and NO gate mismatch, and the
  conclusion is stated in the capstone's OWN raw `gatedKernel` form (guarding the defeq explicitly).

  ## WHAT THIS FILE LANDS.
    • `hDConv_live_gate_wired` — the LIVE capstone's `hDConv` antecedent proposition (raw `gatedKernel`
      form), now a THEOREM CONDITIONAL on the ALREADY-BANKED `hDConvSlot_AT_GATE` ~130-binder census
      (the F2 regularity pile, the `hFII` tail-integrability pile, the `hDaLimLU` data census, the
      frozen/moving lists).  UNLIKE `hDuhamel`, the `hDConv` slot IS the `DifferentiableAt` directly, so
      NO `hBoundaryLim` slot is needed (the pointwise boundary limit is required only for `hDuhamel`'s
      heat-operator identity, NOT for `DifferentiableAt`).  Route: `hDConvSlot_AT_GATE` at
      `H = vanVleckGatedWitness g gi hChr hK S a b`, matched to the capstone's raw form by the `rfl`
      defeq above.  Opaque carried antecedent ⟹ named census.

  ⚠  STILL NOT `a₁ = R/6`.  Discharging the census members is NOT attempted here.  Note (per the campaign
  ledger) that the census binders are PROPOSITIONALLY IDENTICAL to those of
  `HDuhamelLiveGateWired.hDuhamel_live_gate_wired` (minus the `hBoundaryLim` slot), at the SAME
  `vanVleckGatedWitness g gi hChr hK S a b` kernel — so the standalone J4-896..908 discharges
  (`hmassone`, `hEdom`, the `MemLapFull`/`MemAdjLo`/`MemAdjHi`/`MemECombine` interchange bundles,
  `hAdom`, `hWDom`, `hFzero`, `hAzero`, `hmod`, `hsup`, `hUfloor`, the four F2 inner-`s`
  measurability/continuity binders) apply VERBATIM to this census.  The center-identity sub-leg bottoms
  out at the named geometry floor `RadialGaugeInterface.RadialNormalCoordinateGauge` + the base-point
  geodesic pullback bridge (J4-903), a recognized irreducible carry.  a₁ = R/6 remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`.
-/
import QIQTH.HDConvGateThreading
import QIQTH.GatedGlobalWitnessN1CapstoneReachAligned

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.ETailRateBound QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Interval Topology BigOperators

namespace QIQTH.HDConvLiveGateWired

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The EXACT-GATE defeq character-check (`rfl`): the LIVE capstone's `H`-form
    ### is definitionally `vanVleckGatedWitness g gi hChr hK S a b`.
    ############################################################################### -/

/-- **Character-check (defeq, `rfl`).**  The concrete gate kernel the LIVE capstone
    `trueKernel_diagonal_a1_eq_R6_residual_N1_reachAligned` selects (its `H`) is DEFINITIONALLY equal to
    `vanVleckGatedWitness g gi hChr hK S a b` — the kernel `HDConvGateThreading` is built against.  This
    is what makes the wiring below a direct instantiation at the capstone's own parameters with no gate
    mismatch, in the capstone's OWN raw `gatedKernel` form.  ⚠ NOT `a₁ = R/6`. -/
example (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) :
    (gatedKernel K S
        (globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK)))
      = vanVleckGatedWitness g gi hChr hK S a b := rfl

/-! ###############################################################################
    ### The LIVE `hDConv` slot, reduced from opaque antecedent to named census.
    ############################################################################### -/

/-- **★★★ `hDConv_live_gate_wired`.**  The LIVE order-1 capstone's `hDConv` antecedent — the diagonal
    time-`DifferentiableAt` of the moving-source heat convolution at the concrete van-Vleck gated
    witness, stated in the capstone's OWN raw `gatedKernel` / `globalCutoffParametrixWitnessN` form —
    reduced from an OPAQUE carried arrow to a THEOREM CONDITIONAL on the ALREADY-BANKED, fully-enumerated
    `HDConvGateThreading.hDConvSlot_AT_GATE` census.  The census binders (F2 pile, `hFII` pile,
    `hDaLimLU` data census, frozen/moving lists) are reproduced VERBATIM from `hDConvSlot_AT_GATE`; the
    conclusion is the EXACT capstone `hDConv` slot at `H = gatedKernel K S (globalCutoffParametrixWitnessN
    1 …)`, which is `rfl`-defeq to `vanVleckGatedWitness g gi hChr hK S a b` (per the character-check
    above).  NO `hBoundaryLim` (unneeded for `DifferentiableAt`).  Pure wiring; NONE of the hypotheses is
    the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_live_gate_wired (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
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
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b) F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hII_lo : MemAdjLo F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hII_hi : MemAdjHi F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
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
    (hUsub : U ⊆ Set.Icc ta tb) :
    DifferentiableAt ℝ
      (fun w => heatConv
        (gatedKernel K S
          (globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK)))
        (leviSeries (heatOp g gi
          (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK)))))
        w 0 0) t :=
  QIQTH.HDConvGateThreading.hDConvSlot_AT_GATE g gi hChr hK S a b F hFeq t T hT U hUopen htU hUT hn
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi hEcomb
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub

end QIQTH.HDConvLiveGateWired

section AxiomChecks
open QIQTH.HDConvLiveGateWired
#print axioms hDConv_live_gate_wired
end AxiomChecks
