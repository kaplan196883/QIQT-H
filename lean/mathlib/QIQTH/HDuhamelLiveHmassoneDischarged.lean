/-
  HDuhamelLiveHmassoneDischarged — feed the BANKED abstract-`g` `hmassone` discharge (J4-896,
  `HmassoneFromGateAnnulusSplit.hmassone_from_gate_annulus_split`) INTO the LIVE order-1 `hDuhamel`
  slot (via `HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL` + `hDuhamelSlot_AT_GATE`),
  ELIMINATING the analytic approximate-identity limit `hmassone` from the live `hDuhamel` antecedent
  surface.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure COMPOSITION / dependency-normalization brick — the missing composition step between two ALREADY
  banked results, this time on the `hDuhamel` surface (J4-977 performed the SAME move on `hDConv`
  only; the `hDuhamel` Core assembly was left carrying the `hmassone` binder):

    • `HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL` (J4-311): the LIVE order-1
      `hDuhamel` slot's `TruncatedDuhamelCore` at the concrete van-Vleck gated witness, reduced to the
      honest satisfiable UNION census — one member of which is the OPAQUE analytic limit
          `hmassone : Tendsto (fun m => ∫ z, Wit (epsSeq m) 0 z) atTop (𝓝 1)`
      (the mass-normalization / approximate-identity boundary trace as `ε → 0`);

    • `HmassoneFromGateAnnulusSplit.hmassone_from_gate_annulus_split` (J4-896): the abstract-`g`
      discharge of EXACTLY that `hmassone` proposition, down to the SATISFIABLE pre-`ρ`
      gate-activation triple `{rS, hKball, hSact}` + the base metric/gauge carriers
      `{hgCD, hgiCD, hgpos, hgdet0, h0Kmem}` + the census's OWN witness-slice measurability `hWmeas`
      (= `hWslice`) and zeroth wide domination `hWDom` (= `hDom`).

  This file COMPOSES them and then bridges through `HDuhamelExportRethread.hDuhamelSlot_AT_GATE`
  (`TruncatedDuhamelData.hDuhamel_of_truncatedData`) to the EXACT `hDuhamel` capstone-slot identity
      `heatOp g gi (H*L) t 0 0 = L t 0 0 + heatConv (heatOp g gi H) L t 0 0`
  (`L := leviSeries (heatOp g gi H)`, `H := vanVleckGatedWitness …`).  Net effect: the OPAQUE
  approximate-identity analytic LIMIT `hmassone` is GONE from the live `hDuhamel` surface, traded for
  elementary satisfiable geometry + gate-activation inputs (all supplied by the capstone's own
  geometry).  Every other census binder is reproduced verbatim from `truncatedDuhamelCore_AT_GATE_FULL`.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.
    • `hDuhamelSlot_hmassone_discharged` — the EXACT `hDuhamel` antecedent proposition of the LIVE
      order-1 capstone at the concrete gate (`heatOp g gi (H*L) = L + E*L`), now a THEOREM whose
      antecedent surface NO LONGER carries the analytic approximate-identity limit `hmassone`.  Every
      other census binder is reproduced verbatim from `truncatedDuhamelCore_AT_GATE_FULL`; `hmassone`
      is replaced by the satisfiable geometry/gate carriers of the banked J4-896 discharge, from which
      it is reconstructed internally.

  ⚠  STILL NOT `a₁ = R/6`.  Discharging the REMAINING census members (the `RadialNormalCoordinateGauge`
  centre-identity leg + its geodesic-pullback bridge `hpull` — the opaque-chart wall — the Gaussian
  dominations, interchange bundles, sliver carries, plus the single W1-free `hBoundaryLim` slot) is NOT
  attempted here.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`; this brick only
  NORMALIZES the `hDuhamel` dependency by eliminating one analytic-limit binder in favour of
  satisfiable geometry inputs — the `hDuhamel` analogue of J4-977's `hDConv` normalization.
-/
import QIQTH.HDuhamelExportRethread
import QIQTH.HmassoneFromGateAnnulusSplit

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.ETailRateBound QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Interval Topology BigOperators

namespace QIQTH.HDuhamelLiveHmassoneDischarged

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `hDuhamelSlot_hmassone_discharged`.**  The EXACT `hDuhamel` antecedent proposition of the
    LIVE order-1 capstone at the concrete van-Vleck gated witness — the parametrix Duhamel identity
    `heatOp g gi (H*L) t 0 0 = L t 0 0 + heatConv (heatOp g gi H) L t 0 0`
    (`L := leviSeries (heatOp g gi H)`) — with the analytic approximate-identity LIMIT `hmassone`
    ELIMINATED from the antecedent surface.  Every other binder is verbatim from
    `HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL`; `hmassone` is DERIVED internally from
    `HmassoneFromGateAnnulusSplit.hmassone_from_gate_annulus_split` fed with the census's own
    `hWmeas`/`hWDom` + the (satisfiable, capstone-geometry-supplied) carriers
    `{hgCD, hgiCD, hgpos, h0Kmem, hgdet0, ha, hab, rS, hrS, hKball, hSact}`.  Pure composition; NONE of
    the hypotheses is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hDuhamelSlot_hmassone_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    -- ★ the single W1-free boundary slot (provider `hBoundaryLim_DONE`):
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b) F m t) atTop
        (𝓝 (F t 0 0)))
    -- ── the `hDaLimLU` data census (from `hDaLimLU_concrete`) ────────────────────────────────────
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
    -- ── the F2 pile + `hFII` pile (for `hDerivConv_AT_GATE`) ─────────────────────────────────────
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
    -- ── the frozen/moving satisfiable lists (for `hbdryLU_CONCRETE`) ─────────────────────────────
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
    -- ── `hmassone` is NO LONGER a binder here — it is DERIVED from the carriers below ──────────────
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    -- ── the SATISFIABLE geometry / gate-activation carriers of the banked J4-896 `hmassone` discharge ─
    (hgCD : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiCD : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hgdet0 : Matrix.det (g 0) = 1)
    (ha : 0 < a) (hab : a < b)
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z) :
    heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
      = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
        + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0 := by
  -- Derive the eliminated `hmassone` from the banked J4-896 discharge, reusing the census's own
  -- `hWmeas` (= `hWslice`) and `hWDom` (= `hDom`), plus the satisfiable geometry/gate carriers.
  have hmassone : Tendsto
      (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1) :=
    QIQTH.HmassoneFromGateAnnulusSplit.hmassone_from_gate_annulus_split
      g gi hChr hK h0Kmem hgCD hgiCD hgpos S a b ha hab hgdet0 rS hrS hKball hSact hWmeas
      lam τ₀ CW hlam hτ₀ hCW hWDom
  -- Assemble the `hDuhamel` Core at the concrete gate (J4-311 FULL), now with `hmassone` supplied.
  have core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t :=
    QIQTH.HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL g gi hChr hK S a b F hFeq
      t T hT U hUopen htU hUT hn hBoundaryLim
      hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
      hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
      E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi hEcomb
      A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
      nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
      ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
      hWDom hmass hmassone hmod hsup hUsub
  -- Bridge the Core to the EXACT `hDuhamel` capstone-slot identity.
  exact QIQTH.HDuhamelExportRethread.hDuhamelSlot_AT_GATE g gi hChr hK S a b t core

end QIQTH.HDuhamelLiveHmassoneDischarged

section AxiomChecks
open QIQTH.HDuhamelLiveHmassoneDischarged
#print axioms hDuhamelSlot_hmassone_discharged
end AxiomChecks
