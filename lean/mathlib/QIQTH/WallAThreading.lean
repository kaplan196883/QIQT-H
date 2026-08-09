/-
  WallAThreading — J4-459: THREAD `wallA_phase1` INTO THE V3 CORE AT THE WITNESS.

  This shrinks the `a₁ = R/6` block-B conditional surface.  `V2CensusInstantiation.v2Census_phase1`
  (J4-429) reproduces the v3-core conclusion `TruncatedDuhamelCore` from the enumerated group-(1)-(4)
  carries — and among those carries it CARRIED all SIX block-B wall-A members verbatim
  (`hFdomW`, `hmeas2Lo`, `hSecCont`, `hBcont`, plus the two genuine carries `hInter`, `hAdom2cap`).

  `WallAInstantiation.wallA_phase1` (J4-458) showed that FOUR of those six members
  (`hFdomW`/`hmeas2Lo`/`hSecCont`/`hBcont`) are NOT independent carries: they reduce to a SMALLER input
  set — the `LeviSeriesLocalData` envelope package, two positive-time-compact box families, the group-(A)
  scaffolding `hUT`/`hεU`, and the two genuine carries `hInter`/`hAdom2cap`.

  `v2Census_phase2` (this brick) THREADS `wallA_phase1` into `v2Census_phase1` at the witness: it supplies
  the four derived block-B members INTERNALLY from `wallA_phase1`'s smaller input set, so its own binder
  list is `v2Census_phase1`'s MINUS the six block-B members PLUS `wallA_phase1`'s inputs (the envelope
  package + the two box families; `hInter`/`hAdom2cap` stay as the two genuine carries; `hUT`/`hεU`/`wA2`/
  `CA2c` were already present).  The conclusion is the SAME v3-core `TruncatedDuhamelCore`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  surviving labelled carries.  This is pure threading: the four derived block-B members move from
  independent carries into internal suppliers, shrinking the carried surface to {`hInter`, `hAdom2cap`}
  + the envelope/box/scaffolding families.  Every remaining carry is genuine, satisfiable, non-vacuous,
  strictly lower-level than its target, and never the conclusion.  NO `sorry` (header prose excepted),
  NO `:= True`, NO new axioms, NO existing file edited, nothing wired into `AxiomAudit`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MomentWallCoverage
import QIQTH.V2CensusInstantiation
import QIQTH.WallAInstantiation

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.DuhamelCoreThreaded QIQTH.PerUCensusTuple QIQTH.W2Finish
open QIQTH.HDuhamelExportRethread QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData QIQTH.DaLimLUConcreteDischarge
open QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.TerminalCoverage QIQTH.MomentWallCoverage QIQTH.DaLimEasyTranche
open QIQTH.JointContinuityAtoms QIQTH.SliceMeasurability
open QIQTH.V2CensusInstantiation QIQTH.WallAInstantiation
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.WallAThreading

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★★ `v2Census_phase2` — the v3-core conclusion with the four derived block-B members
    ###                          SUPPLIED INTERNALLY from `wallA_phase1` (= WALL-A THREADED).
    ############################################################################### -/

/-- **★★★★ `v2Census_phase2`.**  THE WALL-A-THREADED TERMINAL CROSS-CHECK.  It is `v2Census_phase1` with
    the four DERIVED block-B wall-A members (`hFdomW`, `hmeas2Lo`, `hSecCont`, `hBcont`) removed from the
    carried surface and supplied INTERNALLY from `wallA_phase1`'s smaller input set — the
    `LeviSeriesLocalData` envelope package (`data`), the two positive-time-compact box families
    (`hSecBoxes`, `hBBoxes`), the group-(A) scaffolding `hUT`/`hεU`, and the two genuine carries
    `hInter`/`hAdom2cap`.  The block-B width is fixed to `wF := 2` and `CF` is extracted from the Levi
    envelope; everything else is threaded verbatim to `v2Census_phase1`.  The conclusion is the SAME
    v3-core `TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t`.

    THAT THIS TYPECHECKS certifies the block-B carried surface has shrunk: four of the six block-B members
    are no longer independent carries — they collapse onto the envelope + two box families + the group-(A)
    scaffolding — leaving only the two genuine carries `hInter`/`hAdom2cap` (plus the satisfiable
    envelope/box inputs).  ⚠ THE HONEST SUMMARY: pure threading at the wall-A leg; it closes NOTHING
    deeper.  Every remaining carry is satisfiable, non-vacuous, strictly lower-level, and NONE is
    `a₁ = R/6`.  ⚠ NOT `a₁ = R/6`. -/
theorem v2Census_phase2 (g gi : Point n → Fin n → Fin n → ℝ)
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
    -- ── the WALL-A interchange census (block B), THREADED via `wallA_phase1`.
    -- data + positivity that stay (the two genuine carries need `wA2`/`CA2c`):
    (τc wA2 : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    -- `wallA_phase1`'s SMALLER input set for the four derived block-B members
    -- (`hFdomW`/`hmeas2Lo`/`hSecCont`/`hBcont`), replacing them as carries:
    (Cdata : ℝ)
    (data : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) Cdata T)
    (hSecBoxes : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hBBoxes : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    -- the TWO genuine carries (unchanged):
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (Lc Bcomp Q Sconst : ℝ) (hLc : 0 ≤ Lc) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hSconst : 0 ≤ Sconst)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τc)
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0)
    -- ── (group 2) the inner-`z` `hdiff` census:
    (hInnerData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
          znb ∈ 𝓝 w ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume) ∧
          Integrable
            (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume ∧
          Integrable bnd volume ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            ‖witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd z) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            HasDerivAt (fun w' => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
              (witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w'))
    -- ── (group 3) the per-`u` `hPd2conv` census:
    (nbP : ℝ → Set (Point n)) (hnbP_open : ∀ u ∈ U, IsOpen (nbP u))
    (hnbP0 : ∀ u ∈ U, (0 : Point n) ∈ nbP u)
    (hProvP : ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
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
    (hGintP : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y)
          =ᶠ[𝓝 (0 : Point n)]
          QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m) :
    TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t := by
  -- ★ THREAD `wallA_phase1`: supply the four derived block-B members INTERNALLY.
  obtain ⟨hInter', hAdom2cap', hFdomW_ex, hmeas2Lo', hSecCont', hBcont'⟩ :=
    QIQTH.WallAInstantiation.wallA_phase1 g gi hChr hK S a b U T Cdata hUT hεU wA2 CA2c
      data hSecBoxes hBBoxes hInter hAdom2cap
  -- extract the Levi-envelope constant `CF` (with `wF := 2`) from `hFdomW`.
  obtain ⟨CF, hCF, hFdomW⟩ := hFdomW_ex
  -- re-supply the enumerated group-(1)-(4) surface (block-B four now internal) to `v2Census_phase1`.
  exact QIQTH.V2CensusInstantiation.v2Census_phase1 g gi hChr hK S a b F hFeq
    t T hT U hUopen htU hUT hn hBoundaryLim hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas
    bnd hbdd hbound D0 D1 hD0 hD1 hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi
    hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub
    τc wA2 2 CF CA2c hwA2 hCA2c (by norm_num) hCF hεU
    hInter' hAdom2cap' hFdomW hmeas2Lo' hSecCont' hBcont'
    Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint
    hInnerData
    nbP hnbP_open hnbP0 hProvP fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1

/-! ###############################################################################
    ### `wallAThreaded_core` — the wall-A-threaded terminal cross-check (alias of `v2Census_phase2`).
    ############################################################################### -/

/-- **★★★★★ `wallAThreaded_core`.**  THE WALL-A-THREADED TERMINAL CROSS-CHECK, made machine-checked:
    `v2Census_phase2` under its audit name.  Its statement — consuming the group-(1)-(4) carry surface
    with the four derived block-B members REPLACED by `wallA_phase1`'s smaller input set (envelope + two
    box families + `hInter`/`hAdom2cap`) and producing the v3-core conclusion — certifies the block-B
    carried surface has shrunk to {`hInter`, `hAdom2cap`} + the envelope/box/scaffolding families.
    ⚠ NOT `a₁ = R/6`. -/
def wallAThreaded_core := @v2Census_phase2

end QIQTH.WallAThreading

/-! ## THE BLOCK-B FINAL LEDGER — the shrunken wall-A block-B surface.

  With `v2Census_phase2` / `wallAThreaded_core` threading `wallA_phase1` into `v2Census_phase1` at the
  witness, the v3-core BLOCK-B wall-A conditional surface is now, in full:

    surface member                       verdict            satisfied by
    ──────────────────────────────────   ────────────────   ───────────────────────────────────────────
    `hInter`                             GENUINE CARRY      the atomic diff-under-∫ interchange bundle at
      (`MemInterchange W F U (…)`)                          the witness; no banked supplier — it IS the
                                                            input the wall-A leg reduces to.
    `hAdom2cap`                          GENUINE CARRY      the clean second-`x`-derivative Gaussian cap
      (`≤ CA2c m · G_{wA2·τ}`)                              `CA2c·G_{wA2·τ}`; no banked bound of this shape
                                                            (CensusDominations D3; banked = crude `τ⁻¹`).
    `data`                               SATISFIABLE INPUT  the `LeviSeriesLocalData (heatOp g gi W) Cdata
      (`LeviSeriesLocalData … Cdata T`)                     T` envelope package (RNC geometry pile); via
                                                            `wallA_hFdomW_bridge` ⇒ `hFdomW` (`wF:=2`).
    `hSecBoxes`                          SATISFIABLE INPUT  the positive-time-compact box family
      (`witnessSecondXDeriv` boxes)                         `Icc (τ₀/2) T ×ˢ closedBall 0 R`; via
                                                            `wallA_hSecCont_verbatim` ⇒ `hSecCont`, and
                                                            (with `hUT`/`hεU`) ⇒ `hmeas2Lo`.
    `hBBoxes`                            SATISFIABLE INPUT  the positive-time-compact Levi-slice box
      (Levi-slice boxes)                                   family; via `wallA_hBcont_bridge` ⇒ `hBcont`,
                                                            and (with `hUT`/`hεU`) ⇒ `hmeas2Lo`.
    `hUT`, `hεU`                         GROUP-(A) SCAFFOLD  domain floor/ceiling (already present in the
                                                            group-(A) surface); feed the `hmeas2Lo` fold.

  ── WHAT MOVED.  Four block-B members are NO LONGER independent carries — they are supplied internally:
      • `hFdomW`   ← `wallA_hFdomW_bridge` from `data`   (`wF := 2`, `CF` from the Levi envelope);
      • `hSecCont` ← `wallA_hSecCont_verbatim` from `hSecBoxes`;
      • `hBcont`   ← `wallA_hBcont_bridge` from `hBBoxes`;
      • `hmeas2Lo` ← `SliceMeasurability.hmeas2Lo_slice` (folds onto `hSecCont`/`hBcont`/`hUT`/`hεU`).
    So the six-member block-B carried surface collapses to the TWO genuine carries {`hInter`, `hAdom2cap`}
    + the THREE satisfiable envelope/box inputs {`data`, `hSecBoxes`, `hBBoxes`} + the already-present
    group-(A) scaffolding {`hUT`, `hεU`}.  Each is genuine, satisfiable, non-vacuous, strictly
    lower-level than its target, and NONE is the conclusion.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  THIS IS **NOT** `a₁ = R/6`, AND MAKES NO CLAIM OF UNCONDITIONALITY.  `a₁ = R/6` remains CONDITIONAL
  on: (i) the enumerated carries themselves (`hInter`, `hAdom2cap`, and the envelope/box inputs are
  INPUTS here, not theorems), and (ii) the DEEP convergence-trio + geometric-wiring content that lives
  INSIDE those carries (true-kernel existence / Levi convergence / Seeley-DeWitt geometric
  identification), which is NEVER claimed closed.  Shrinking the block-B carried surface closes NOTHING
  deeper.
-/

section AxiomChecks
open QIQTH.WallAThreading
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms v2Census_phase2
#print axioms wallAThreaded_core
end AxiomChecks
