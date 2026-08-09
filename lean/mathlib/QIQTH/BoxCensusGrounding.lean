/-
  BoxCensusGrounding — J4-469: GROUND THE `hSecBoxes` / `hBBoxes` BOX-FAMILY CARRIES.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  continues the phase-2..11 census-surface reduction (`HcapEndpointGrounding.v2Census_phase11`) by
  GROUNDING the two positive-time-compact box-family carries — `hSecBoxes` (the second-`x`-derivative
  box family feeding `hSecCont`) and `hBBoxes` (the Levi-slice box family feeding `hBcont`) — one
  level DOWN, onto their honest lower-level suppliers.

  ── `hBBoxes` (the LEVI SIDE).  GENUINE WIRE.  The demanded box shape
       `∀ τ₀∈Ioc 0 T, ∀ R, ContinuousOn (fun p ↦ leviSeries E p.1 p.2 0) (Icc (τ₀/2) T ×ˢ ball 0 R)`
     (with `E := heatOp g gi H_G`) is EXACTLY the conclusion of the banked Weierstrass box
     continuity `LeviMTest.leviSeries_boxContOn`.  Fed the width-2 domination (`data.hmajor`) and
     `data.hC`/`data.hT` from the ALREADY-PRESENT phase-11 `LeviSeriesLocalData` package, the ONLY
     residue is the per-`k` termwise box continuity of `iterE E (k+1)` (`htermBox`) — a strictly
     lower-level carry (single-term joint continuity, NOT the summed Levi slice).  So `hBBoxes` is
     REPLACED by `htermBox`.

  ── `hSecBoxes` (the WITNESS SIDE).  HONEST REDUCTION.  By definition
       `witnessSecondXDeriv g gi hChr hK S a b i τ z
          = pd (fun x ↦ pd (fun x' ↦ vanVleckGatedWitness … τ x' z) i x) i 0`,
     so `p ↦ witnessSecondXDeriv … i p.1 p.2` IS the gated-witness second spatial partial evaluated
     at the FIXED RNC center `0`, jointly continuous in `(τ, z) = (p.1, p.2)`.  THE GATE:  the only
     banked second-order joint-continuity supplier is `ChartComposedHeatOp.chartComposed_pd_pd_
     jointContinuousOn`, but it keys the second partial at the VARYING base point `p.2` of the
     UNGATED chart-composed parametrix `heatParametrix N Θ u`, whereas the census object here is
     keyed at the FIXED base `0` of the GATED witness (cutoff-`S`-composed).  The gate + base-`0`
     keying is a genuine mismatch — NO banked supplier transports.  So `hSecBoxes` is REDUCED (via
     defeq of `witnessSecondXDeriv`) to the witness second-spatial-partial box carry `hpd2diag` (the
     `NonLeviBoxContinuity.hpd2` diagonal), a genuinely-buried atom named honestly.  NO discharge.

  ── WHAT LANDS.
    • `hBBoxes_grounded`  — ★★★ the census `hBBoxes` shape, PRODUCED from `LeviSeriesLocalData` +
        `htermBox` via `leviSeries_boxContOn`.
    • `hSecBoxes_grounded` — ★★★ the census `hSecBoxes` shape, REDUCED (defeq) to the witness
        second-spatial-partial box carry `hpd2diag`.
    • `v2Census_phase12`  — ★★★★★ `v2Census_phase11` with the `hSecBoxes` AND `hBBoxes` binders
        REMOVED and supplied internally (from `hpd2diag` and `data`+`htermBox` respectively).

  NO `sorry`, NO `:= True`, NO new axioms; std-3 only.  No existing file edited.
  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HcapEndpointGrounding
import QIQTH.LeviMTest

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.WitnessMeasDeriv QIQTH.SupConstantFamily QIQTH.UngatedChainRule QIQTH.PullbackMetric
open QIQTH.DuhamelCoreThreaded QIQTH.PerUCensusTuple QIQTH.W2Finish
open QIQTH.HDuhamelExportRethread QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.V2CensusInstantiation QIQTH.WallAInstantiation QIQTH.WallAThreading
open QIQTH.HInterGrounding QIQTH.HAdom2capGrounding
open QIQTH.InnerDataInstantiation QIQTH.InnerDataEnvelope QIQTH.HdiffGrounding
open QIQTH.InnerDataCensusThread QIQTH.PresentationBridges QIQTH.CLSlotWire
open QIQTH.SliverTailMatched QIQTH.AmplitudeDataOnCollar
open QIQTH.AmpGeometryBundle QIQTH.DataAmpAssembly
open QIQTH.OffSVanishing QIQTH.HcapEndpointGrounding
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.BoxCensusGrounding

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ `hBBoxes_grounded` — the census `hBBoxes` Levi box family, from `data` + `htermBox`.
    ############################################################################### -/

/-- **★★★ `hBBoxes_grounded`.**  THE `hBBoxes` DISCHARGE (the LEVI side).  The census Levi-slice box
    family — `∀ τ₀∈Ioc 0 T, ∀ R, ContinuousOn (fun p ↦ leviSeries E p.1 p.2 0) (Icc (τ₀/2) T ×ˢ
    ball 0 R)` — is PRODUCED, at each `(τ₀, R)`, by the banked Weierstrass box continuity
    `LeviMTest.leviSeries_boxContOn`, fed the width-2 domination `data.hmajor` and `data.hC`/`data.hT`
    from the `LeviSeriesLocalData E C T` package, leaving ONLY the per-`k` termwise box continuity
    `htermBox` of `iterE E (k+1)` as the (strictly lower-level) residue.  Generic in `E`; at the
    census it is `E := heatOp g gi (vanVleckGatedWitness …)`, `C := Cdata`.  ⚠ NOT `a₁ = R/6`. -/
theorem hBBoxes_grounded {E : ℝ → Point n → Point n → ℝ} {C T : ℝ}
    (data : LeviSeriesLocalData E C T)
    (htermBox : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro τ₀ hτ₀ R
  exact QIQTH.LeviMTest.leviSeries_boxContOn E C T τ₀ R data.hC data.hT hτ₀.1 hτ₀.2
    (fun k τ p q hτ hτT => data.hmajor k τ p q hτ hτT) (htermBox τ₀ hτ₀ R)

/-! ###############################################################################
    ### ★★★ `hSecBoxes_grounded` — the census `hSecBoxes` box family, reduced (defeq) to `hpd2diag`.
    ############################################################################### -/

/-- **★★★ `hSecBoxes_grounded`.**  THE `hSecBoxes` REDUCTION (the WITNESS side).  Since
    `witnessSecondXDeriv g gi hChr hK S a b i τ z
        = pd (fun x ↦ pd (fun x' ↦ vanVleckGatedWitness … τ x' z) i x) i 0`
    by definition, the census box family — `∀ i, ∀ τ₀∈Ioc 0 T, ∀ R, ContinuousOn (fun p ↦
    witnessSecondXDeriv … i p.1 p.2) (Icc (τ₀/2) T ×ˢ ball 0 R)` — is DEFEQ to the gated-witness
    second-spatial-partial box family `hpd2diag` (the `NonLeviBoxContinuity.hpd2` diagonal, keyed at
    the FIXED RNC center `0`).  ⚠ THE GATE:  the banked second-order supplier
    `ChartComposedHeatOp.chartComposed_pd_pd_jointContinuousOn` keys at the VARYING base of the
    UNGATED chart-composed parametrix — a genuine gate + base-`0` keying mismatch — so `hSecBoxes`
    does NOT wire to it; it is HONESTLY carried as the genuinely-buried second-partial atom.  ⚠ NOT
    `a₁ = R/6`. -/
theorem hSecBoxes_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hpd2diag : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          pd (fun x : Point n =>
              pd (fun x' : Point n =>
                vanVleckGatedWitness g gi hChr hK S a b p.1 x' p.2) i x) i (0 : Point n))
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro i τ₀ hτ₀ R
  exact hpd2diag i τ₀ hτ₀ R

/-! ###############################################################################
    ### ★★★★★ `v2Census_phase12` — phase-11 with `hSecBoxes` AND `hBBoxes` supplied internally.
    ############################################################################### -/

/-- **★★★★★ `v2Census_phase12`.**  `HcapEndpointGrounding.v2Census_phase11` with the `hSecBoxes` AND
    `hBBoxes` box-family carries REMOVED from the ∃-body: `hBBoxes` is SUPPLIED INTERNALLY via
    `hBBoxes_grounded` from the ALREADY-PRESENT `LeviSeriesLocalData` package `data` plus the new
    lower-level per-`k` termwise box carry `htermBox`; and `hSecBoxes` via `hSecBoxes_grounded` from
    the new witness second-spatial-partial box carry `hpd2diag`.  The signature is exactly
    `v2Census_phase11`'s minus `{hSecBoxes, hBBoxes}` plus `{hpd2diag, htermBox}`.

    ⚠  THE GATE.  Both reconstructed carries reference the ∃-obtained `S`; `hBBoxes_grounded` is a
    verbatim `leviSeries_boxContOn` wire and `hSecBoxes_grounded` is a defeq restatement, so the swap
    is exact.  ⚠ Pure surface re-plumbing; closes NOTHING deeper.  NOT `a₁ = R/6`. -/
theorem v2Census_phase12 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hwtop : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hn : 1 ≤ n) (T : ℝ) (hT : 0 < T) :
    ∃ (a b : ℝ) (S : Point n → Set (Point n)), 0 < a ∧ a < b ∧
      ∀ (F : ℝ → Point n → Point n → ℝ)
        (_hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
        (t : ℝ) (U : Set ℝ) (_hUopen : IsOpen U) (_htU : t ∈ U)
        (_hUT : ∀ u ∈ U, u ≤ T)
        (_hBoundaryLim : Tendsto
            (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b) F m t) atTop
            (𝓝 (F t 0 0)))
        (_hgi : MemGaugeGi (n := n) gi) (_hΓ : MemGaugeGamma (n := n) g gi)
        (V : Set (Point n)) (_hVopen : IsOpen V) (_hV0 : (0 : Point n) ∈ V)
        (snb : Set ℝ) (_hsnb : snb ∈ 𝓝 (0 : ℝ))
        (_hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
            pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u
                (u - epsSeq m) x 0) i y
              = ∫ s in (0)..(u - epsSeq m),
                  ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
        (_hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z * F s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (_hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
            volume 0 (u - epsSeq m))
        (_hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (bnd : ℕ → Fin n → ℝ → ℝ)
        (_hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
            IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
        (_hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
            s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
              ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                  (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
        (D0 D1 : Fin n → ℝ) (_hD0 : ∀ i, 0 ≤ D0 i) (_hD1 : ∀ i, 0 ≤ D1 i)
        (_hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
            |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
                witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
              ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
        (E₀ E₁ C_L aT : ℝ) (_hE₀ : 0 ≤ E₀) (_hE₁ : 0 ≤ E₁) (_hC_L : 0 ≤ C_L) (_haT : 0 < aT)
        (_hUlb : ∀ u ∈ U, aT ≤ u)
        (_hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
            |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
              ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
        (_hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
        (_hIlo : ∀ (m : ℕ), ∀ u ∈ U,
            IntervalIntegrable (fun s => ∫ (z : Point n),
                heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
              volume 0 (u - epsSeq m))
        (_hIhi : ∀ (m : ℕ), ∀ u ∈ U,
            IntervalIntegrable (fun s => ∫ (z : Point n),
                heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
              volume (u - epsSeq m) u)
        (_hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F)
        (A₀ A₁ : ℝ) (_hA₀ : 0 ≤ A₀) (_hA₁ : 0 ≤ A₁)
        (_hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
            |vanVleckGatedWitness g gi hChr hK S a b τ p q|
              ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
        (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
        (_hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
            (volume.restrict (Set.uIoc 0 u)))
        (_hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
        (_hInnerCont : ∀ u ∈ U,
            ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
              (Set.Ioo 0 u))
        (nb : ℕ → ℝ → Set ℝ) (_hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
        (_hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ c, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
          (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (_hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
        (_hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
          (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s) * F s z 0)
          (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (boundD : ℕ → ℝ → ℝ → ℝ)
        (_hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
        (_hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
          ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0‖
            ≤ boundD m u s)
        (_hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
          HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
            (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0) c)
        (L : ℕ → ℝ → ℝ) (_hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
        (_hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
          |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m + k) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m + k) 0 0
              + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m) 0 0|
            ≤ L m u * (|h| * |k|))
        (ρ lam CW Cf τ₀ : ℝ) (ta tb : ℝ)
        (_hρ : 0 < ρ) (_hlam : 0 < lam) (_hCW : 0 ≤ CW) (_hτ₀ : 0 < τ₀)
        (_hWmeas : ∀ τ, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z) volume)
        (_hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
        (_hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
        (_hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
        (_hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
        (_hWDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
          |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
        (_hmass : ∀ᶠ m in atTop,
          ∫ z, |vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z| ≤ CW)
        (_hmassone : Tendsto
            (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
        (_hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
            ∀ z ∈ Metric.ball (0 : Point n) δ,
              |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
        (_hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
            ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
              |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
        (_hUsub : U ⊆ Set.Icc ta tb)
        (τc wA2 : ℝ)
        (_hwA2 : 0 < wA2)
        (hτc : epsSeq 0 ≤ τc)
        (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
        (Cdata : ℝ)
        (data : LeviSeriesLocalData
            (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) Cdata T)
        -- ★ THE `hSecBoxes` BINDER of `v2Census_phase11` IS REPLACED BY THIS LOWER-LEVEL CARRY:
        (hpd2diag : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
          ContinuousOn
            (fun p : ℝ × Point n =>
              pd (fun x : Point n =>
                  pd (fun x' : Point n =>
                    vanVleckGatedWitness g gi hChr hK S a b p.1 x' p.2) i x) i (0 : Point n))
            (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
        -- ★ THE `hBBoxes` BINDER of `v2Census_phase11` IS REPLACED BY THIS LOWER-LEVEL CARRY:
        (htermBox : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
          ContinuousOn
            (fun p : ℝ × Point n =>
              iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) p.1 p.2 0)
            (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
        (Ccrude : ℝ) (_hCcrude : 0 ≤ Ccrude)
        (_hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
            |witnessSecondXDeriv g gi hChr hK S a b i τ z|
              ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z))
        (Lc Bcomp Q Sconst : ℝ)
        (hLc : 0 ≤ Lc) (_hBcomp : 0 ≤ Bcomp) (_hQ : 0 ≤ Q) (_hSconst : 0 ≤ Sconst)
        (rr0 cc : ℝ)
        (ampData : ∀ i : Fin n,
          AmplitudeDerivativeDataOn g gi hChr hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τc
            (collarRegime (K := K) rr0 cc τc))
        (qcF IchartF : Fin n → ℝ → ℝ → Point n → ℝ)
        (_hgateC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          ∀ z ∈ collar (cc * Real.sqrt τ), z ∈ K ∧ ‖z‖ < rr0)
        (_hoffC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          ∀ z ∈ (collar (cc * Real.sqrt τ))ᶜ,
            witnessSecondXDeriv g gi hChr hK S a b i τ z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
              = IchartF i τ s z
                + z i / (2 * τ) * gaussDdim τ z * (ampData i).A1amp τ z
                    * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
                + gaussDdim τ z * (ampData i).A2amp τ z
                    * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (_hWintC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          Integrable (fun z => witnessSecondXDeriv g gi hChr hK S a b i τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        (_hf2C : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          Integrable (fun z => z i / (2 * τ) * gaussDdim τ z * (ampData i).A1amp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        (_hf3C : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          Integrable (fun z => gaussDdim τ z * (ampData i).A2amp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        (_hqzC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc → ∀ z w,
          |(ampData i).Aamp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
              - (ampData i).Aamp τ w
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s w 0|
            ≤ Lc * dist z w)
        (_hqzmeasC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          AEStronglyMeasurable (fun z => (ampData i).Aamp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        (_hqcC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc → ∀ z w,
          |qcF i τ s z - qcF i τ s w| ≤ Lc * dist z w)
        (_hqcmeasC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          AEStronglyMeasurable (qcF i τ s) volume)
        (_h0C : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          (ampData i).Aamp τ 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s 0 0
            = qcF i τ s 0)
        (_hIchartC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          IntegrableOn (IchartF i τ s) (collar (cc * Real.sqrt τ))ᶜ volume)
        (_hcompC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          ‖∫ z in (collar (cc * Real.sqrt τ))ᶜ,
              (IchartF i τ s z - hessGaussFactor i τ z * qcF i τ s z)‖ ≤ Bcomp / Real.sqrt τ)
        (_hf2boundC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          |∫ z, z i / (2 * τ) * gaussDdim τ z * (ampData i).A1amp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
            ≤ Q / Real.sqrt τ)
        (_hf3boundC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          |∫ z, gaussDdim τ z * (ampData i).A2amp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
            ≤ Sconst)
        (ρc : ℝ) (_hρc : 0 < ρc)
        (_hwInf : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
          (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
        (_hC1geom : ∀ (i : Fin n), ∀ w ∈ snb,
          ContinuousOn
            (fun q : ℝ × Point n =>
              uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1))
            (Set.Icc (w - ρc) (w + ρc) ×ˢ K)
          ∧ Set.MapsTo
            (fun q : ℝ × Point n =>
              (q.2, uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1)))
            (Set.Icc (w - ρc) (w + ρc) ×ˢ K)
            (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hChr hK))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              IsUnit (fderiv ℝ (uniformFlowExp g gi hChr hK q.2)
                (uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1))))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              fderiv ℝ (uniformInverseChart g gi hChr hK q.2) (Function.update (0 : Point n) i q.1)
                = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hChr hK q.2)
                    (uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1))))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              DifferentiableAt ℝ (uniformInverseChart g gi hChr hK q.2)
                (Function.update (0 : Point n) i q.1))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              S q.2 ∈ nhds (Function.update (0 : Point n) i q.1)))
        (hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) w.1 w.2.1 w.2.2))
        (hGateCoreRR : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
            s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (znb : Set ℝ) (C₂ : ℝ),
              znb ∈ 𝓝 w ∧ 0 ≤ C₂ ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                    (Function.update (0 : Point n) i w') z) volume) ∧
              AEStronglyMeasurable
                (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
                volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                    (Function.update (0 : Point n) i w) z) volume ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
                |witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                    (Function.update (0 : Point n) i w') z| ≤ C₂) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    witnessFieldDeriv g gi hChr hK S a b i (u - s) x' z) i
                  (Function.update (0 : Point n) i w')))
        (nbP : ℝ → Set (Point n)) (_hnbP_open : ∀ u ∈ U, IsOpen (nbP u))
        (_hnbP0 : ∀ u ∈ U, (0 : Point n) ∈ nbP u)
        (_hProvP : ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
          ∃ (snbx : Set ℝ) (bound : ℝ → ℝ),
            snbx ∈ 𝓝 (x i) ∧
            (∀ w, AEStronglyMeasurable
              (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) (Function.update x i w) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
              (volume.restrict (Set.uIoc 0 u))) ∧
            IntervalIntegrable
              (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume 0 u ∧
            AEStronglyMeasurable
              (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
              (volume.restrict (Set.uIoc 0 u)) ∧
            IntervalIntegrable bound volume 0 u ∧
            (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
              ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bound s) ∧
            (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
              HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
                  (Function.update x i w) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
                (∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w))
        (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
        (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
        (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
        (_hGintP : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
                ∂(volume : Measure (Point n)))
            volume 0 u)
        (_hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
            HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m)
              (fderivBulk u i m x) x)
        (_hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
            dist (fderivBulk u i m x) (gderiv u i x)
              ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
        (_hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
        (_hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
            (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
                (u - epsSeq m) x 0) i y)
              =ᶠ[𝓝 (0 : Point n)]
              QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m),
        TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t := by
  obtain ⟨a, b, S, ha, hab, hbody11⟩ :=
    QIQTH.HcapEndpointGrounding.v2Census_phase11 g gi hg hChr hK hgnd hgsymm hinvF hframeK hwtop
      hdg0 hg0 hn T hT
  refine ⟨a, b, S, ha, hab, fun F hFeq t U hUopen htU hUT hBoundaryLim hgi hΓ V hVopen hV0
    snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero
    hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff
    L hLnn hCross ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd
    hfmov_bdd hWDom hmass hmassone hmod hsup hUsub τc wA2 hwA2 hτc hεU Cdata data hpd2diag htermBox
    Ccrude hCcrude hcrude Lc Bcomp Q Sconst hLc hBcomp hQ hSconst
    rr0 cc ampData qcF IchartF hgateC hoffC hWintC hf2C hf3C hqzC hqzmeasC hqcC hqcmeasC
    h0C hIchartC hcompC hf2boundC hf3boundC
    ρc hρc hwInf hC1geom hEmeas hGateCoreRR nbP hnbP_open hnbP0 hProvP
    fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1 => ?_⟩
  -- ★ GROUND `hSecBoxes` from the witness second-spatial-partial box carry `hpd2diag`.
  have hSecBoxes := hSecBoxes_grounded g gi hChr hK S a b T hpd2diag
  -- ★ GROUND `hBBoxes` from the banked `LeviSeriesLocalData` package + the termwise box carry.
  have hBBoxes := hBBoxes_grounded data htermBox
  -- ★ THREAD both reconstructed box families through the phase-11 body.
  exact hbody11 F hFeq t U hUopen htU hUT hBoundaryLim hgi hΓ V hVopen hV0
    snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero
    hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff
    L hLnn hCross ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd
    hfmov_bdd hWDom hmass hmassone hmod hsup hUsub τc wA2 hwA2 hτc hεU Cdata data hSecBoxes hBBoxes
    Ccrude hCcrude hcrude Lc Bcomp Q Sconst hLc hBcomp hQ hSconst
    rr0 cc ampData qcF IchartF hgateC hoffC hWintC hf2C hf3C hqzC hqzmeasC hqcC hqcmeasC
    h0C hIchartC hcompC hf2boundC hf3boundC
    ρc hρc hwInf hC1geom hEmeas hGateCoreRR nbP hnbP_open hnbP0 hProvP
    fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1

/-! ###############################################################################
    ### THE BOX LEDGER — the surviving box residue after `hSecBoxes`/`hBBoxes` grounding.
    ############################################################################### -/

/-- **`box_census_grounding_residuals`.**  THE ENUMERATED SURVIVING RESIDUALS after the J4-469
    box-family grounding.  A genuine conjunction (non-vacuous plumbing witness), machine-checkable;
    each conjunct SATISFIABLE, none the conclusion.

    THE BOX LEDGER (what `v2Census_phase12` carries in place of the two box families):
      1. `hTermBox`  — the per-`k` termwise box continuity of `iterE E (k+1)` that now REPLACES the
         whole Levi-slice box family `hBBoxes` (fed the banked `LeviSeriesLocalData` domination);
      2. `hPd2Diag`  — the gated-witness second-spatial-partial box carry (keyed at the RNC center
         `0`) that now REPLACES the second-`x`-derivative box family `hSecBoxes` (defeq);
      3. `hRest`     — the UNCHANGED phase-11 body carries (`hτc`, `data`, `hAzero`, the slot /
         gate / envelope / geometry census, `hEmeas`, `hGateCoreRR`, `hProvP`, …).

    DISCHARGED (NOT in this ledger): BOTH box families of the phase-11 core — `hBBoxes` VERBATIM-wired
    to `leviSeries_boxContOn` (residue `hTermBox`), `hSecBoxes` reduced (defeq) to `hPd2Diag`.  ⚠ THE
    GATE: no banked supplier discharges `hPd2Diag` (the gate + base-`0` keying blocks the ungated
    `chartComposed_pd_pd_jointContinuousOn` wire); it stays an honest carry.  ⚠ NOT `a₁ = R/6`;
    CONDITIONAL on exactly this surface. -/
def box_census_grounding_residuals (hTermBox hPd2Diag hRest : Prop) : Prop :=
  hTermBox ∧ hPd2Diag ∧ hRest

/-- The box ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem box_census_grounding_residuals_intro {hTermBox hPd2Diag hRest : Prop}
    (h1 : hTermBox) (h2 : hPd2Diag) (h3 : hRest) :
    box_census_grounding_residuals hTermBox hPd2Diag hRest :=
  ⟨h1, h2, h3⟩

end QIQTH.BoxCensusGrounding

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.BoxCensusGrounding.hBBoxes_grounded
#print axioms QIQTH.BoxCensusGrounding.hSecBoxes_grounded
#print axioms QIQTH.BoxCensusGrounding.v2Census_phase12
#print axioms QIQTH.BoxCensusGrounding.box_census_grounding_residuals_intro
