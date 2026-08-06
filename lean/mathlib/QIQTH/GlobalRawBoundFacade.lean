/-
  GlobalRawBoundFacade — J4-337: the `hraw` PACKAGING (Sol consult #10, bricks C1–C3) plus the
  ONE-THEOREM Da-limit assembly `hDaLimLU_from_labelled` (the whole `DaLimLUConcreteDischarge.
  hDaLimLU_concrete` hypothesis pile threaded over the LABELLED-input list).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  PACKAGING + COMPOSITION brick over the banked `hDaLimLU` census dischargers (J4-331..336).  No `sorry`
  (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  hypothesis equal to (or trivially yielding) the conclusion, no existing file edited, nothing committed.
  `hDaLimLU_concrete` remains the concrete-gate `Da`-limit and is NOT the `a₁ = R/6` diagonal statement;
  `a₁ = R/6` stays CONDITIONAL on the whole `hDuhamel`/convergence-trio + geometric-wiring stack AND on
  the three surviving LABELLED inputs threaded here (`hraw`, the `AmplitudeDerivativeData` bundle whose
  hard field is `hD2Hexpand`, and `hPd2conv`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DELIVERABLES.

  •  (C1) `GlobalGatedRawBound` — the consumer-facing width-1 predicate, copied VERBATIM from the `hraw`
     binder of `DaLimHardTranche.hEdom_of_gaussPoly_residual`: the honest PRE-COLLAPSE exposed-polynomial
     residual bound `|heatOp g gi H τ p q| ≤ P·((r²/τ + 1)·gaussDdim τ (p−q))`, `r² = rncRadialSq (p−q)`.

  •  (C2) `hEdom_of_globalRawBound` — the consumer adapter: from `GlobalGatedRawBound g gi H P` (`P ≥ 0`)
     produce the `∃ E₀ E₁, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ hEdom` shape (the ∃-form the banked bridge yields; the
     `hDaLimLU_concrete` binder carries EXPLICIT constants, so the assembly `obtain`s them).  Via the
     banked bridge `DaLimHardTranche.hEdom_of_gaussPoly_residual` (`GlobalGatedRawBound` is defeq to its
     `hraw` hypothesis).

  •  (C3) The per-group sub-assemblies + the ONE-theorem capstone `hDaLimLU_from_labelled`:
       - (gauge)          `gauge_from_geometry`         : `MemGaugeGi ∧ MemGaugeGamma`.
       - (source)         `source_from_leviData`        : width-2 `hFdom` (∃) ∧ `hFzero`.
       - (integrability)  `integrability_from_dominations` : `hIlo ∧ hIhi ∧ hII_lo ∧ hII_hi`.
       - (sliver)         `sliver_from_ampData`         : the `√ε` sliver amplitudes (∃ `D0 D1`).
       - (E-combination)  `eCombine_from_data`          : `MemECombine`.
       - (hLapFull)       `memLapFull_from_labelled`     : `MemLapFull` from `hPd2conv` + the sliver sum.
       - ★ CAPSTONE       `hDaLimLU_from_labelled`      : `DaLimLUGoal g gi H_G (leviSeries E) U` from the
                          labelled inputs + banked side conditions (surviving-hypothesis census in its
                          docstring).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DaLimCensusRecon
import QIQTH.DaLimEasyTranche
import QIQTH.DaLimHardTranche
import QIQTH.FrozenLaplaceSliver

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open scoped Interval Topology BigOperators

namespace QIQTH.GlobalRawBoundFacade

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (C1) — the consumer-facing width-1 `GlobalGatedRawBound` predicate.
    ############################################################################### -/

/-- **★ (C1) — `GlobalGatedRawBound`.**  The consumer-facing width-1 residual predicate, copied
    VERBATIM from the `hraw` binder of `DaLimHardTranche.hEdom_of_gaussPoly_residual`: the honest
    PRE-COLLAPSE exposed-polynomial residual shape of the `N = 1` parametrix — ONE derivative hit on the
    Gaussian exposes ONE `r²/τ` factor (plus the `τ⁰` coefficient term):
      `∀ τ > 0, ∀ p q, |heatOp g gi H τ p q| ≤ P·((rncRadialSq (p−q)/τ + 1)·gaussDdim τ (p−q))`.
    The banked coefficient chain (`gatedWitnessN1_hEboundW_le_vanVleck_final`) COLLAPSES this exposed
    form into a width-2 bound (absorbing `r²/τ` into the width), so `GlobalGatedRawBound` is NOT
    bank-dischargeable at the global gated level without a `_narrow` re-run of that read-only chain;
    it is KEPT LABELLED (per Sol consult #10, brick C).  Its own proof (loc-unif M2 + finite-cover +
    cutoff absorption) is a SEPARATE later campaign, not on this critical path.  NOT `a₁ = R/6`. -/
def GlobalGatedRawBound (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (P : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
    |heatOp g gi H τ p q|
      ≤ P * ((rncRadialSq (p - q) / τ + 1) * gaussDdim τ (p - q))

/-! ###############################################################################
    ### (C2) — the consumer adapter `hEdom_of_globalRawBound`.
    ############################################################################### -/

/-- **★ (C2) — `hEdom_of_globalRawBound`.**  THE CONSUMER ADAPTER: from the labelled width-1 predicate
    `GlobalGatedRawBound g gi H P` (with `P ≥ 0`) produce the width-3/2 residual domination in the ∃-form
      `∃ E₀ E₁, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ > 0, ∀ p q,
          |heatOp g gi H τ p q| ≤ (E₀ + E₁·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p−q)`.
    (`E₀ = 13·P`, `E₁ = 0`.)  This is the exact `hEdom` shape the `DaLimLUConcreteDischarge.
    hDaLimLU_concrete` binder wants, but the CONSTANTS are packaged existentially — the banked bridge
    yields the ∃-form, and `hDaLimLU_concrete` carries the explicit `E₀ E₁` binders, so the capstone
    `obtain`s the constants from this ∃ (the honest match).  Route: `GlobalGatedRawBound` is defeq to the
    `hraw` hypothesis of `DaLimHardTranche.hEdom_of_gaussPoly_residual`, applied directly.  NOT
    `a₁ = R/6`. -/
theorem hEdom_of_globalRawBound (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (P : ℝ) (hP : 0 ≤ P)
    (hraw : GlobalGatedRawBound g gi H P) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi H τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) :=
  QIQTH.DaLimHardTranche.hEdom_of_gaussPoly_residual g gi H P hP hraw

/-! ###############################################################################
    ### (C3·gauge) — the RNC gauge group.
    ############################################################################### -/

/-- **★ (C3·gauge) — `gauge_from_geometry`.**  The gauge sub-assembly: both RNC census binders
    `MemGaugeGi gi` (`g⁻¹(0) = δ`) and `MemGaugeGamma g gi` (`Γ(0) = 0`), from the frame condition
    `hframeK` (with `0 ∈ K`), the inverse relation `hinvF`, and the first-derivative gauge `hdg0`.
    Thin composition of `DaLimCensusRecon.memGaugeGi_of_geometry` / `memGaugeGamma_of_hdg0`.  Every carry
    is a satisfiable RNC-geometry fact (the flat metric satisfies all).  NOT `a₁ = R/6`. -/
theorem gauge_from_geometry (g gi : Point n → Fin n → Fin n → ℝ) {K : Set (Point n)}
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    (hdg0 : ∀ c d e, pd (fun y => g y c d) e (0 : Point n) = 0) :
    MemGaugeGi (n := n) gi ∧ MemGaugeGamma (n := n) g gi :=
  ⟨QIQTH.DaLimCensusRecon.memGaugeGi_of_geometry g gi hK0 hframeK hinvF,
   QIQTH.DaLimCensusRecon.memGaugeGamma_of_hdg0 g gi hdg0⟩

/-! ###############################################################################
    ### (C3·source) — the Levi-source group (width-2 `hFdom` + `hFzero`).
    ############################################################################### -/

/-- **★ (C3·source) — `source_from_leviData`.**  The source sub-assembly at the endgame gate
    `F := leviSeries (heatOp g gi H_G)`: the width-2 Gaussian domination `hFdom` (∃ `C_L`) and the
    nonpositive-time vanishing `hFzero`, in the EXACT shapes `DaLimLUConcreteDischarge.hDaLimLU_concrete`
    wants.  From `DaLimEasyTranche.hFdom_concrete` (extracting `C_L` from the banked `LeviSeriesLocalData`
    width-2 envelope) and `DaLimEasyTranche.hFzero_concrete` (needs `1 ≤ n`).  The carry is the
    `LeviSeriesLocalData` package (RNC geometry pile behind the landed J4-324 Levi domination).  NOT
    `a₁ = R/6`. -/
theorem source_from_leviData (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T C : ℝ) (hn : 1 ≤ n)
    (dataLevi : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C T) :
    (∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s : ℝ, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
      ∧ (∀ s : ℝ, s ≤ 0 → ∀ z y : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y = 0) :=
  ⟨QIQTH.DaLimEasyTranche.hFdom_concrete
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C T dataLevi,
   QIQTH.DaLimEasyTranche.hFzero_concrete g gi hChr hK S a b hn⟩

/-! ###############################################################################
    ### (C3·integrability) — the strip / adjacency interval-integrability group.
    ############################################################################### -/

/-- **★ (C3·integrability) — `integrability_from_dominations`.**  The integrability sub-assembly: all
    four `hDaLimLU_concrete` binders `hIlo`, `hIhi` (strip, `A := heatOp g gi H_G`) and `hII_lo`,
    `hII_hi` (`MemAdjLo`/`MemAdjHi`, `A := witnessSecondXDeriv`), at `F := leviSeries (heatOp g gi H_G)`.
    Each leg is `DaLimEasyTranche.hI*_concrete` / `hII_*_concrete` (all via the generic Gaussian-pairing
    engine `pairing_intervalIntegrable`).  Carries: the heat-operator Gaussian domination (`hAdomHeat`,
    width `wA`), the second-`x`-derivative Gaussian domination (`hAdom2`, width `wA2`), the width-`wF`
    Levi bound (`hFdomW`), the source vanishing (`hFzero`), and the four `s`-profile measurabilities
    (`hmeasLo`/`hmeasHi`/`hmeas2Lo`/`hmeas2Hi`) — no singular prefactor.  NOT `a₁ = R/6`. -/
theorem integrability_from_dominations (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T wA CA wA2 CA2 wF CF : ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2 : 0 ≤ CA2) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2 : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2 * gaussDdim (wA2 * τ) (0 - z))
    (hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeas2Hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u))) :
    (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
      ∧ (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume (u - epsSeq m) u)
      ∧ MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
          (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
      ∧ MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
          (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
  ⟨QIQTH.DaLimEasyTranche.hIlo_concrete g gi hChr hK S a b U T wA CA wF CF
      hwA hCA hwF hCF hUpos hUT hAdomHeat hFdomW hFzero hmeasLo,
   QIQTH.DaLimEasyTranche.hIhi_concrete g gi hChr hK S a b U T wA CA wF CF
      hwA hCA hwF hCF hUpos hUT hAdomHeat hFdomW hFzero hmeasHi,
   QIQTH.DaLimEasyTranche.hII_lo_concrete g gi hChr hK S a b
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) U T wA2 CA2 wF CF
      hwA2 hCA2 hwF hCF hUpos hUT hAdom2 hFdomW hFzero hmeas2Lo,
   QIQTH.DaLimEasyTranche.hII_hi_concrete g gi hChr hK S a b
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) U T wA2 CA2 wF CF
      hwA2 hCA2 hwF hCF hUpos hUT hAdom2 hFdomW hFzero hmeas2Hi⟩

/-! ###############################################################################
    ### (C3·sliver) — the `√ε` sliver amplitude group.
    ############################################################################### -/

/-- **★ (C3·sliver) — `sliver_from_ampData`.**  The sliver sub-assembly: the `√ε` amplitude bound
    `hbnd` with its `D0`/`D1` companions, produced existentially from the per-coordinate
    `AmplitudeDerivativeData` bundle (its ONE hard field is `hD2Hexpand`, the Leibniz–Gaussian identity
    for the concrete second `x`-derivative — the CARRIED derivative-layer geometry) plus the satisfiable
    short-time budget (`aa ≤ u ≤ T`, `ε_m < aa/2`, `ε_m ≤ τ₀`).  Thin re-export of
    `DaLimHardTranche.hbnd_concrete`.  NOT `a₁ = R/6`. -/
theorem sliver_from_ampData (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (T τ₀ aa : ℝ) (haa : 0 < aa)
    (data : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b F i T τ₀)
    (hau : ∀ u ∈ U, aa ≤ u) (hUT : ∀ u ∈ U, u ≤ T)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀) :
    ∃ D0 D1 : Fin n → ℝ, (∀ i, 0 ≤ D0 i) ∧ (∀ i, 0 ≤ D1 i) ∧
      ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m :=
  QIQTH.DaLimHardTranche.hbnd_concrete g gi hChr hK S a b F U T τ₀ aa haa data hau hUT hεaa hετ₀

/-! ###############################################################################
    ### (C3·E-combination) — the `MemECombine` group.
    ############################################################################### -/

/-- **★ (C3·E-combination) — `eCombine_from_data`.**  The `E`-combination sub-assembly: the
    `MemECombine g gi H F` census binder (`∀ m u, DaTrunc = LapTrunc + Etrunc`) from the six per-`(m,u)`
    representation/integrability sub-facts.  Thin re-export of `DaLimCensusRecon.memECombine_of_data`.
    NOT `a₁ = R/6`. -/
theorem eCombine_from_data (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ)
    (hDa : ∀ (m : ℕ) (u : ℝ), DaTrunc H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ), LapTrunc g gi H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi H (u - s) 0 z * F s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m)) :
    MemECombine g gi H F :=
  QIQTH.DaLimCensusRecon.memECombine_of_data g gi H F hDa hLap hLapZ hEZ hLapS hES

/-! ###############################################################################
    ### (C3·hLapFull) — the untruncated-interchange group from `hPd2conv`.
    ############################################################################### -/

/-- **★ (C3·hLapFull) — `memLapFull_from_labelled`.**  The Laplacian-comparison sub-assembly: the
    `MemLapFull g gi H F U pdpdH` census binder (`∀ u ∈ U, Δ_g(H*F) 0 = ∑ᵢ ∫₀ᵘ ∫ pdpdH·F`) from the
    labelled atomic second-partial carrier `hPd2conv`, the frozen-side interchange `hInter`
    (`MemInterchange`), the adjacency integrabilities `hII_lo`/`hII_hi`, and the `√ε` sliver amplitudes
    `hbnd` (whose sum → 0 rate is supplied INTERNALLY by `DaLimLUWallRecon.sliver_sum_bound_U`).  Applies
    `FrozenLaplaceSliver.hLapFull_of_pd2conv` per `u ∈ U`.  NO full-side interchange is presupposed (the
    circular route is avoided — see the `FrozenLaplaceSliver` header verdict).  NOT `a₁ = R/6`. -/
theorem memLapFull_from_labelled (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (hInter : MemInterchange H F U pdpdH)
    (hII_lo : MemAdjLo F U pdpdH) (hII_hi : MemAdjHi F U pdpdH)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0))) :
    MemLapFull g gi H F U pdpdH := by
  obtain ⟨B, hSliver, hBlim⟩ := QIQTH.DaLimLUWallRecon.sliver_sum_bound_U
    (fun i m u => ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    D0 D1 hD0 hD1 hbnd
  intro u hu
  exact QIQTH.FrozenLaplaceSliver.hLapFull_of_pd2conv g gi H F u hgi hΓ pdpdH
    (fun m i => hInter m i u hu) (fun m i => hII_lo m i u hu) (fun m i => hII_hi m i u hu)
    B (fun m => hSliver m u hu) hBlim (hPd2conv u hu)

/-! ###############################################################################
    ### (C3·capstone) — ★★★ `hDaLimLU_from_labelled`: the whole Da-limit pile as ONE theorem.
    ############################################################################### -/

/-- **★★★ (C3·capstone) — `hDaLimLU_from_labelled`.**  THE ONE-THEOREM Da-limit ASSEMBLY: the complete
    loc-unif `Da`-limit conclusion `DaLimLUGoal g gi H_G (leviSeries E) U` (the exact conclusion of
    `DaLimLUConcreteDischarge.hDaLimLU_concrete`), at the endgame gate `H_G := vanVleckGatedWitness …`,
    `E := heatOp g gi H_G`, `F := leviSeries E`, `pdpdH := witnessSecondXDeriv …`, derived from ONLY the
    labelled inputs + banked side conditions, with every `hDaLimLU_concrete` binder plumbed through its
    banked discharger.

    ── THE COMPLETE SURVIVING-HYPOTHESIS CENSUS (every argument, honestly labelled) ──────────────────
    (i)  GEOMETRY / GAUGE RAW  →  `gauge_from_geometry` ⟹ `hgi`/`hΓ`:
         `hK0` (`0 ∈ K`), `hframeK` (RNC frame `g = δ` on `K`), `hinvF` (inverse relation),
         `hdg0` (`∂_e g_{ab}(0) = 0`).
    (ii) THE W2 differentiation-under-∫ FAMILY  →  `witness_MemInterchange` ⟹ `hInter` (consumed inside
         `hDaLimLU_concrete` for `hInterchange`, AND fed to `memLapFull_from_labelled`):
         `V`/`hVopen`/`hV0`, `snb`/`hsnb`, `hQ1`, `hFmeas`, `hFint`, `hF'meas`, `bnd`, `hbdd`, `hbound`,
         `hdiff` — the honest `hasFDerivAt_integral_of_dominated`-shaped diff-under-∫ facts on
         `witnessFieldDeriv`/`witnessFieldDeriv2`.  SATISFIABLE (majorant `bnd m i s` interval-
         integrable, `snb` a derivative neighbourhood — no singular prefactor).
    (iii) THE TIME FLOOR / WINDOW  — DATA:  `aa`/`haa` (`0 < aa`), `hau` (`∀ u ∈ U, aa ≤ u`),
         `hUTle` (`∀ u ∈ U, u ≤ T`).  (`aT := aa`, `hUlb := hau`.)
    (iv) THE LEVI SOURCE ENVELOPE  →  `source_from_leviData` ⟹ `hFdom`/`hFzero` (and, via `y = 0` +
         `sub_zero`, the width-2 `hFdomW` fed to integrability):  `C`, `dataLevi : LeviSeriesLocalData E C T`,
         `hn` (`1 ≤ n`).
    (v)  THE INTEGRABILITY DOMINATIONS  →  `integrability_from_dominations` ⟹
         `hIlo`/`hIhi`/`hII_lo`/`hII_hi`:  `wA`/`CA`/`hwA`/`hCA` + `hAdomHeat` (heat-operator Gaussian
         bound), `wA2`/`CA2`/`hwA2`/`hCA2` + `hAdom2` (second-`x`-derivative Gaussian bound), and the four
         `s`-profile measurabilities `hmeasLo`/`hmeasHi`/`hmeas2Lo`/`hmeas2Hi`.  No singular prefactor.
    (vi) THE √ε SLIVER BUNDLE  →  `sliver_from_ampData` ⟹ `D0`/`D1`/`hD0`/`hD1`/`hbnd` (fed to both
         `hDaLimLU_concrete` and `memLapFull_from_labelled`):  `τ₀`, `dataAmp : ∀ i, AmplitudeDerivativeData …`
         (its ONE hard field is `hD2Hexpand` — the CARRIED derivative-layer Leibniz–Gaussian identity),
         `hεaa` (`ε_m < aa/2`), `hετ₀` (`ε_m ≤ τ₀`).
    (vii) ★ THE LABELLED RESIDUAL RAW BOUND  →  `hEdom_of_globalRawBound` ⟹ `hEdom` (∃ `E₀ E₁`):
         `P`/`hP`, `hraw : GlobalGatedRawBound g gi H_G P`.  KEPT LABELLED (Sol consult #10, brick C).
    (viii) ★ THE LABELLED ATOMIC INTERCHANGE CARRIER  →  `memLapFull_from_labelled` ⟹ `hLapFull`:
         `hPd2conv` (`∀ u ∈ U, ∀ i, Tendsto (∂ᵢ∂ᵢ frozen 0) → (∂ᵢ∂ᵢ full 0)`).  KEPT LABELLED.
    (ix) THE E-COMBINATION CARRIES  →  `eCombine_from_data` ⟹ `hEcomb`:
         `hDa`, `hLap`, `hLapZ`, `hEZ`, `hLapS`, `hES` (Fubini/representation facts).

    ⚠ Every hypothesis is SATISFIABLE and NON-VACUOUS; NONE is the conclusion.  The THREE surviving
    LABELLED inputs are `hraw` (the width-1 residual), `dataAmp`'s `hD2Hexpand` field, and `hPd2conv` —
    each the subject of a separate later derivation campaign, none on this critical path.  This is the
    honest one-theorem packaging of the entire `hDaLimLU` census over the labelled-input list.  `a₁ = R/6`
    remains CONDITIONAL.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_from_labelled (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U) (hn : 1 ≤ n)
    -- (i) geometry / gauge raw inputs:
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    (hdg0 : ∀ c d e, pd (fun y => g y c d) e (0 : Point n) = 0)
    -- (ii) the W2 differentiation-under-∫ family (at `F := leviSeries (heatOp g gi H_G)`):
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w)
    -- (iii) the residual-domination time floor / window:
    (aa : ℝ) (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u) (hUTle : ∀ u ∈ U, u ≤ T)
    -- (iv) the Levi source envelope package:
    (C : ℝ) (dataLevi : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C T)
    -- (v) the integrability Gaussian dominations + measurabilities:
    (wA CA wA2 CA2 : ℝ) (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2 : 0 ≤ CA2)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2 : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2 * gaussDdim (wA2 * τ) (0 - z))
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeas2Hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    -- (vi) the √ε sliver amplitude bundle:
    (τ₀ : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τ₀)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    -- (vii) ★ the labelled residual gated raw bound:
    (P : ℝ) (hP : 0 ≤ P)
    (hraw : GlobalGatedRawBound g gi (vanVleckGatedWitness g gi hChr hK S a b) P)
    -- (viii) ★ the labelled atomic interchange carrier:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
    -- (ix) the E-combination carries:
    (hDa : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc g gi (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m)) :
    DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U := by
  -- abbreviations kept implicit via the literal expressions.
  -- (i) gauge.
  obtain ⟨hgi, hΓ⟩ := gauge_from_geometry g gi hK0 hframeK hinvF hdg0
  -- (ii) the frozen-side interchange member (from the W2 family) — reused for `hLapFull`.
  have hInter :
      MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
    QIQTH.SecondOrderInterchangeConcrete.witness_MemInterchange g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (0 : ℝ) U
      V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
  -- (iii)/(iv) source envelope: width-2 `hFdom`, `hFzero`, and the derived width-2 `hFdomW`.
  obtain ⟨⟨C_L, hCL0, hFdom⟩, hFzero⟩ :=
    source_from_leviData g gi hChr hK S a b T C hn dataLevi
  have hFzero0 : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0 :=
    fun s hs z => hFzero s hs z 0
  have hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
        ≤ C_L * gaussDdim (2 * s) z := by
    intro s hs hsT z
    have h := hFdom s hs hsT z 0
    rwa [sub_zero] at h
  have hUpos : ∀ u ∈ U, 0 < u := fun u hu => lt_of_lt_of_le haa (hau u hu)
  -- (v) integrability legs.
  obtain ⟨hIlo, hIhi, hII_lo, hII_hi⟩ :=
    integrability_from_dominations g gi hChr hK S a b U T wA CA wA2 CA2 2 C_L
      hwA hCA hwA2 hCA2 (by norm_num) hCL0 hUpos hUTle hAdomHeat hAdom2 hFdomW hFzero0
      hmeasLo hmeasHi hmeas2Lo hmeas2Hi
  -- (vi) sliver amplitudes.
  obtain ⟨D0, D1, hD0, hD1, hbnd⟩ :=
    sliver_from_ampData g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U T τ₀ aa haa
      dataAmp hau hUTle hεaa hετ₀
  -- (vii) ★ residual width-3/2 domination from the labelled raw bound.
  obtain ⟨E₀, E₁, hE₀, hE₁, hEdom⟩ :=
    hEdom_of_globalRawBound g gi (vanVleckGatedWitness g gi hChr hK S a b) P hP hraw
  -- (viii) ★ untruncated interchange (`hLapFull`) from the labelled atomic carrier.
  have hLapFull :
      MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
    memLapFull_from_labelled g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
      hgi hΓ hInter hII_lo hII_hi D0 D1 hD0 hD1 hbnd hPd2conv
  -- (ix) E-combination.
  have hEcomb :
      MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) :=
    eCombine_from_data g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      hDa hLap hLapZ hEZ hLapS hES
  -- ★★★ thread every discharged binder into the concrete-gate Da-limit.
  exact QIQTH.DaLimLUConcreteDischarge.hDaLimLU_concrete g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) T U hUopen hn
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aa hE₀ hE₁ hCL0 haa hau hUTle hEdom hFdom hFzero hIlo hIhi hEcomb

end QIQTH.GlobalRawBoundFacade

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.GlobalRawBoundFacade.hEdom_of_globalRawBound
#print axioms QIQTH.GlobalRawBoundFacade.gauge_from_geometry
#print axioms QIQTH.GlobalRawBoundFacade.source_from_leviData
#print axioms QIQTH.GlobalRawBoundFacade.integrability_from_dominations
#print axioms QIQTH.GlobalRawBoundFacade.sliver_from_ampData
#print axioms QIQTH.GlobalRawBoundFacade.eCombine_from_data
#print axioms QIQTH.GlobalRawBoundFacade.memLapFull_from_labelled
#print axioms QIQTH.GlobalRawBoundFacade.hDaLimLU_from_labelled
