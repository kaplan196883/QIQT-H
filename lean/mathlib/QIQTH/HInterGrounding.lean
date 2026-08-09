/-
  HInterGrounding — J4-460: GROUND THE `hInter` INTERCHANGE BUNDLE.

  `WallAThreading.v2Census_phase2` (J4-459) threaded the wall-A block-B surface down to two genuine
  carries: `hInter` (the `MemInterchange` diff-under-∫ interchange bundle at the witness) and
  `hAdom2cap`.  This brick attacks `hInter`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GATE  (satisfiability check before building).

  SHAPE.  `hInter : MemInterchange (vanVleckGatedWitness …) (leviSeries (heatOp g gi …)) U (…)` unfolds
  (`DaLimLUWallRecon.MemInterchange` is an `abbrev`) to
      `∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
         pd (fun y => pd (fun x => heatConvFrozen H_G F u (u − epsSeq m) x 0) i y) i 0
           = ∫ s in (0)..(u − epsSeq m), ∫ z, witnessSecondXDeriv … i (u − s) z · F s z 0`.
  This is EXACTLY the conclusion of the BANKED engine
  `SecondOrderInterchangeConcrete.witness_MemInterchange` (J4-256, std-3), instantiated at
  `F := leviSeries (heatOp g gi H_G)`.  So `hInter` is NOT an atomic wall — it is the engine output.

  m-UNIFORMITY TRAP — CLEARED.  `MemInterchange` is a PER-`(m,i,u)` EQUALITY (the diff-under-∫
  interchange for a single fixed truncation index `m`), NOT a series/limit.  No summability or
  `m`-independent dominator is required: the engine's dominator slot `bound : ℕ → Fin n → ℝ → ℝ` is
  itself per-`(m,i)` and only interval-integrable on `[0, u − epsSeq m]` per `(m,i,u)`.  So `hInter` is
  PER-`m` ADMISSIBLE — the trap that killed the whole-time `hAdom2` does NOT apply here.

  QUANTIFIER-ORDER / CENTERING — CLEAR.  The engine consumes carries of shape `∀ m i, ∀ u ∈ U, …` and
  produces `∀ m i, ∀ u ∈ U, [eq]` (same order).  The kernel is centered at the base point `0`
  (`pd … i 0`, `witnessSecondXDeriv … i (u−s) z`, field nbhd `V ∋ 0`, scalar nbhd `snb ∈ 𝓝 0`).

  VERDICT.  `hInter` is GROUNDED (reduced), NOT walled.  It discharges through the banked engine to the
  diff-under-∫ carry family {`hQ1`, `hFmeas`/`hFint`/`hF'meas`, the dominator triple
  `bound`/`hbdd`/`hbound`, `hdiff`} + the field/scalar nbhds.  In the MAJORANT route the dominator
  triple is ALSO discharged internally (from the on-gate shifted second-order domination `hOn` + the
  Levi source bound `hF` via the W2 majorant), leaving only {`hOn`, `hF`, `hQ1`, measurabilities,
  `hdiff`} + `hεU`.  Both are strictly-lower-level differentiation-under-∫ facts about the concrete
  witness, each satisfiable and non-vacuous, NONE the conclusion.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It grounds
  ONE of the two block-B genuine carries by exhibiting the banked engine that produces it; `a₁ = R/6`
  remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack AND on the surviving
  carries (the diff-under-∫ family here is INPUT, not theorem; `hAdom2cap` is untouched).  Every
  hypothesis is genuine, satisfiable, non-vacuous, strictly lower-level than its target, and never the
  conclusion.  NO `sorry` (header prose excepted), NO `:= True`, NO new axioms, NO existing file edited,
  nothing wired into `AxiomAudit`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WallAThreading
import QIQTH.SecondOrderInterchangeConcrete

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.DuhamelCoreThreaded QIQTH.PerUCensusTuple QIQTH.W2Finish
open QIQTH.HDuhamelExportRethread QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.SecondOrderInterchangeConcrete
open QIQTH.V2CensusInstantiation QIQTH.WallAInstantiation QIQTH.WallAThreading
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HInterGrounding

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ `hInter_grounded` — the `MemInterchange` bundle from the banked W2 engine.
    ############################################################################### -/

/-- **★★★ `hInter_grounded`.**  THE `hInter` BUNDLE, GROUNDED.  It produces the verbatim
    `DaLimLUWallRecon.MemInterchange (vanVleckGatedWitness …) F U (fun i τ z => witnessSecondXDeriv … i τ z)`
    member — the block-B genuine carry `hInter` — from the diff-under-∫ carry family via the banked engine
    `SecondOrderInterchangeConcrete.witness_MemInterchange` (J4-256).  The carries are the honest
    lower-level differentiation-under-∫ facts about the concrete `N = 1` van-Vleck gated witness:
    the first-order interchange `hQ1` on the open field nbhd `V ∋ 0`, the `∫z`/`∫s` measurabilities
    `hFmeas`/`hFint`/`hF'meas`, the interval-integrable dominator triple `bound`/`hbdd`/`hbound`, and the
    `∫z`-derivative `HasDerivAt` family `hdiff`.  NONE is the conclusion; each is satisfiable and
    non-vacuous.  Pure grounding through the banked engine.  ⚠ NOT `a₁ = R/6`. -/
theorem hInter_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (acut bcut : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S acut bcut) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bound : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bound m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bound m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w) :
    MemInterchange (vanVleckGatedWitness g gi hC hK S acut bcut) F U
      (fun i τ z => witnessSecondXDeriv g gi hC hK S acut bcut i τ z) :=
  witness_MemInterchange g gi hC hK S acut bcut F 0 U V hVopen hV0 snb hsnb
    hQ1 hFmeas hFint hF'meas bound hbdd hbound hdiff

/-! ###############################################################################
    ### ★★★ `hInter_grounded_majorant` — the same bundle with the dominator triple discharged.
    ############################################################################### -/

/-- **★★★ `hInter_grounded_majorant`.**  THE `hInter` BUNDLE, GROUNDED WITH THE DOMINATOR TRIPLE
    DISCHARGED INTERNALLY.  Produces the same `MemInterchange` member as `hInter_grounded`, but the
    `bound`/`hbdd`/`hbound` triple is supplied by the W2 majorant (`witness_MemInterchange_majorant`,
    J4-256) from the ON-GATE shifted second-order Gaussian domination `hOn` (the field-shifted
    near-isometry chart-jet estimate) + the Levi source width-2 bound `hF`.  The engine's `epsSeq m ≤ u`
    eventual-window antecedent is DISCHARGED here from the domain floor `hεU` (present in the wall-A
    surface), so the output is the verbatim un-antecedented `MemInterchange` member.  The surviving
    carries are {`hOn`, `hF`, `hQ1`, `hFmeas`/`hFint`/`hF'meas`, `hdiff`} + `hεU` — the dominator triple
    is GONE.  Each is a genuine differentiation-under-∫ / on-gate-domination fact, NONE the conclusion.
    ⚠ NOT `a₁ = R/6`. -/
theorem hInter_grounded_majorant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (acut bcut : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (T α Csec C_L : ℝ)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hα : 0 < α) (hCsec : 0 ≤ Csec) (hC_L : 0 ≤ C_L)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hOn : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ (s w : ℝ) (z : Point n),
        0 < u - s → s ≤ T → w ∈ snb → z ∈ K →
        |witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) (Function.update (0 : Point n) i w) z|
          ≤ Csec * (u - s)⁻¹ * gaussDdim (α * (u - s)) z)
    (hF : ∀ (s : ℝ) (z : Point n), 0 < s → s ≤ T → |F s z 0| ≤ C_L * gaussDdim (2 * s) z)
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S acut bcut) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u) :
    MemInterchange (vanVleckGatedWitness g gi hC hK S acut bcut) F U
      (fun i τ z => witnessSecondXDeriv g gi hC hK S acut bcut i τ z) := by
  intro m i u hu
  exact witness_MemInterchange_majorant g gi hC hK S acut bcut F U T α Csec C_L
    hUpos hUT hα hCsec hC_L V hVopen hV0 snb hsnb hOn hF hQ1 hFmeas hFint hF'meas hdiff
    m i u hu (hεU m u hu)

/-! ###############################################################################
    ### ★★★★ `v2Census_phase3` — `v2Census_phase2` with `hInter` GROUNDED (dropped for `hdiff`).
    ############################################################################### -/

/-- **★★★★ `v2Census_phase3`.**  THE hInter-GROUNDED TERMINAL CROSS-CHECK.  It is `v2Census_phase2` with
    the block-B genuine carry `hInter` (`MemInterchange …`) REMOVED from the carried surface and supplied
    INTERNALLY from `hInter_grounded` — which consumes the diff-under-∫ family ALREADY present in
    `v2Census_phase2` (`hQ1`, `hFmeas`/`hFint`/`hF'meas`, the dominator triple `bnd`/`hbdd`/`hbound`) plus
    the single strictly-lower-level new carry `hdiff` (the `∫z`-derivative `HasDerivAt` family).  So its
    binder list is `v2Census_phase2`'s MINUS `hInter` PLUS `hdiff`.  The conclusion is the SAME v3-core
    `TruncatedDuhamelCore`.  THAT THIS TYPECHECKS certifies `hInter` is no longer an independent block-B
    carry — it collapses onto the engine's diff-under-∫ family, leaving `hAdom2cap` as the SOLE remaining
    block-B genuine carry.  ⚠ Pure grounding at the interchange leg; closes NOTHING deeper.  NOT
    `a₁ = R/6`. -/
theorem v2Census_phase3 (g gi : Point n → Fin n → Fin n → ℝ)
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
    -- ★ the SINGLE new (strictly-lower-level) carry replacing `hInter`: the `∫z`-derivative family.
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
    (τc wA2 : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
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
  -- ★ GROUND `hInter` from the diff-under-∫ family already present + the new `hdiff` carry.
  have hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
    rw [← hFeq]
    exact hInter_grounded g gi hChr hK S a b F U V hVopen hV0 snb hsnb
      hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
  exact QIQTH.WallAThreading.v2Census_phase2 g gi hChr hK S a b F hFeq
    t T hT U hUopen htU hUT hn hBoundaryLim hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas
    bnd hbdd hbound D0 D1 hD0 hD1 hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi
    hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub
    τc wA2 CA2c hwA2 hCA2c hεU Cdata data hSecBoxes hBBoxes
    hInter hAdom2cap
    Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint
    hInnerData
    nbP hnbP_open hnbP0 hProvP fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1

end QIQTH.HInterGrounding

/-! ## THE hInter LEDGER — the grounded block-B genuine carry.

  With `hInter_grounded` / `hInter_grounded_majorant`, the block-B genuine carry `hInter`
  (`MemInterchange (vanVleckGatedWitness …) (leviSeries (heatOp g gi …)) U (witnessSecondXDeriv …)`)
  is GROUNDED — it is the output of the banked W2 differentiation-under-∫ engine
  `SecondOrderInterchangeConcrete.witness_MemInterchange` (J4-256, std-3), not an atomic wall.

    route                    supplier                              surviving carries
    ──────────────────────   ───────────────────────────────────  ─────────────────────────────────
    `hInter_grounded`        `witness_MemInterchange`              `hQ1` (1st-order interchange on
                             (pure threading form)                 `V ∋ 0`), `hFmeas`/`hFint`/`hF'meas`
                                                                   (∫z/∫s measurabilities), the
                                                                   dominator triple
                                                                   `bound`/`hbdd`/`hbound`, `hdiff`
                                                                   (∫z-derivative HasDerivAt family).
    `hInter_grounded_        `witness_MemInterchange_majorant`     `hOn` (on-gate shifted 2nd-order
      majorant`              + `hεU` (domain floor discharges       Gaussian domination), `hF` (Levi
                             the `epsSeq m ≤ u` window)             source width-2 bound), `hQ1`,
                                                                   `hFmeas`/`hFint`/`hF'meas`, `hdiff`.
                                                                   ★ dominator triple DISCHARGED
                                                                     (W2 majorant, internal).

  GATE FACTS.  (i) `MemInterchange` is a per-`(m,i,u)` EQUALITY — no summability / `m`-uniform
  dominator needed; per-`m` carries are admissible (the `hAdom2` uniformity trap does NOT recur).
  (ii) Quantifier order `∀ m i, ∀ u ∈ U` is preserved end-to-end.  (iii) Everything is centered at the
  base point `0` (`pd … i 0`, `V ∋ 0`, `snb ∈ 𝓝 0`).

  ── WHAT MOVED.  `hInter` is no longer presented as an atomic wall — it is REDUCED to the banked
  diff-under-∫ engine's carry family (and, in the majorant route, further to {`hOn`, `hF`} + the
  measurability/`HasDerivAt` families, with the dominator triple discharged internally).  Each surviving
  carry is genuine, satisfiable, non-vacuous, strictly lower-level than `hInter`, and NONE is the
  conclusion.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  THIS IS **NOT** `a₁ = R/6`.  Grounding `hInter` through the banked engine closes NOTHING deeper:
  the diff-under-∫ carry family (`hQ1`/measurabilities/`hdiff`, and `hOn`/`hF` in the majorant route)
  are INPUTS here, not theorems, and the second block-B genuine carry `hAdom2cap` is untouched.
  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.
-/

section AxiomChecks
open QIQTH.HInterGrounding
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms hInter_grounded
#print axioms hInter_grounded_majorant
#print axioms v2Census_phase3
end AxiomChecks
