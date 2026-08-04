/-
  HDConvThreading — J4-209 (Sol final plan Phase 7): THREADING the `hDConv` slot of the `∞`-capstone
  `CConvConcreteThreading.a1_R6_of_residue_inf_v5` from the ALREADY-BANKED providers.

  One brick of the `a₁ = R/6` heat-kernel campaign.  ⚠ HONEST FIREWALL: this is NOT `a₁ = R/6`, and
  proves NOTHING about `R/6`.  It only wires the `DifferentiableAt` (`hDConv`) carry of the v5 capstone
  down to its minimal true residue.  No `sorry`, no new axioms, no vacuous / unsatisfiable hypotheses,
  none equal to the conclusion.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE `hDConv` SLOT (verbatim, `CConvConcreteThreading.a1_R6_of_residue_inf_v5`, J4-207):

      hDConv : DifferentiableAt ℝ
        (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t

  This is EXACTLY the conclusion of `ConvCarriesDischarge.hDConv_gatedWitnessN1_of_delta_final` (J4-117),
  the concrete `hDConv` consumer whose carries are `{hMeasFII, hpar, htime, hR, hDelta}` + the D1/Levi
  Gaussian dominations.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★★★  THE FULL AUDIT — each carry of the `hDConv` chain → its banked provider (or genuine residue).
  ══════════════════════════════════════════════════════════════════════════════════════════════════
  Let  H := vanVleckGatedWitness g gi hChr hK S a b ,  F := leviSeries (heatOp g gi H) .

    ┌──────────┬────────────────────────────────────────────────────────────────────────────────────┐
    │  SLOT    │  BANKED PROVIDER (name, ns QIQTH.HeatResidualBound)  /  residue it carries            │
    ├──────────┼────────────────────────────────────────────────────────────────────────────────────┤
    │ hMeasFII │  CARRIED (base `s`-measurability of `s ↦ ∫ z, H(u−s)0z·F s z0`).  No provider — a     │
    │          │  genuine deferred measurability fact (feeds BOTH `hDConv` directly and R4).           │
    ├──────────┼────────────────────────────────────────────────────────────────────────────────────┤
    │ hpar     │  `F2FamilyDischarge.hpar_discharge` (J4-145 R2).  Da := `DaTrunc H F`.  Residue = the  │
    │          │  C3ε under-∫ engine family (nb/hFmeas/hFint/hF'meas/boundD/hbdd/hbound/hpardiff).      │
    ├──────────┼────────────────────────────────────────────────────────────────────────────────────┤
    │ htime    │  `F2FamilyDischarge.htime_discharge` (J4-145 R1).  Residue = `hUfloor` + inner-        │
    │          │  continuity `hInnerCont` (+ `hFII`, itself R4 = `heatConvInner_intervalIntegrable_H`  │
    │          │  from the dominations + `hMeasFII`).                                                   │
    ├──────────┼────────────────────────────────────────────────────────────────────────────────────┤
    │ hR       │  `F2FamilyDischarge.hR_discharge` (J4-145 R3).  Residue = cross-Lipschitz `hCross`     │
    │          │  (+ `0 ≤ L`) — the mixed-second-difference bound.                                      │
    ├──────────┼────────────────────────────────────────────────────────────────────────────────────┤
    │ hDelta   │  `BoundaryAssembly.hDelta_gatedWitnessN1_final` (J4-120 CAP).  `hBoundary` (Brick 2,   │
    │          │  the moving-peak concentration) is DISCHARGED inside it via                            │
    │          │  `boundary_tendstoLocallyUniformlyOn`.  Residue it still carries:                      │
    │          │    (a) the near-diagonal parametrix family (r₀/τ₀/u₀/u₁/hAnear/hu₀cont/hu₀one/         │
    │          │        hu₀bdd/hu₁bdd), dominations (hAdom/hAzero/hBdom), Levi continuity (hBcont),     │
    │          │        base measurability (hAmeas/hBmeas/hu₀meas/hu₁meas);  ALL satisfiable analytic   │
    │          │        data at the concrete witness;                                                   │
    │          │    (b) `hDaLim` in the loc-unif shape `TendstoLocallyUniformlyOn (fun m u=>DaTrunc H F  │
    │          │        m u) DaLim atTop U`  — the HARD limit `hDaLimLU`.                                │
    ├──────────┼────────────────────────────────────────────────────────────────────────────────────┤
    │ hDaLim   │  `DaLimLocUnif.hDaLimLU_discharge` (U3).  ONE level deeper still: reduces `hDaLimLU`    │
    │ (=hDaLim │  to the sliver/tail/interchange geometric family (pdpdH / hInterchange / hLapFull /    │
    │  LU)     │  hII_lo / hII_hi / B·hSliver·hBlim / Be·hEbnd·hEblim / hEcomb + RNC gauge hgi·hΓ).     │
    │          │  THIS is the genuine hard heat-kernel content (L3/L4).  Carried here (NOT threaded     │
    │          │  deeper) to keep the residue a single clean loc-unif limit.                            │
    └──────────┴────────────────────────────────────────────────────────────────────────────────────┘

  VERDICT.  Every carry of the `hDConv` chain has a banked provider; the SOLE irreducible hard residue is
  `hDaLimLU` (the locally-uniform `Da`-limit → `Δ_g(H*F) + E*F`), itself further reducible (U3) to the
  L3/L4 sliver/interchange family.  Everything else is dominations / measurability / near-diagonal
  parametrix / C3ε engine / cross-Lipschitz / floor — genuine satisfiable analytic data at the concrete
  gated van-Vleck witness, NONE the conclusion.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (this file, ns `QIQTH.HDConvThreading`).

    (1) `hDConv_from_banked` — the `hDConv` `DifferentiableAt` slot of the v5 capstone, assembled by
        composing `hDConv_gatedWitnessN1_of_delta_final ∘ {hpar_discharge, htime_discharge, hR_discharge,
        heatConvInner_intervalIntegrable_H, hDelta_gatedWitnessN1_final}`.  Conditional ONLY on the true
        residue above (with `hDaLimLU` carried as a single loc-unif limit).

    (2) `a1_R6_of_residue_inf_v6` — `a1_R6_of_residue_inf_v5` with the `hDConv` black-box REPLACED, in
        place, by that residue: internally re-derives `hDConv` via `hDConv_from_banked` and feeds v5.
        NOT `a₁ = R/6`; the remaining carries are honest analytic inputs + `hDaLimLU`.
-/
import Mathlib
import QIQTH.ConvCarriesDischarge
import QIQTH.BoundaryAssembly
import QIQTH.F2FamilyDischarge
import QIQTH.DaLimLocUnif
import QIQTH.CConvConcreteThreading

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound
open QIQTH.CConvFacade QIQTH.LeviSeries
open QIQTH.CConvConcreteThreading
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HDConvThreading

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (1) `hDConv_from_banked` — the v5 `hDConv` slot from the banked providers.
    ############################################################################### -/

/-- **★★★ J4-209 (1) — `hDConv_from_banked`.**  THE `hDConv` `DifferentiableAt` carry of
    `CConvConcreteThreading.a1_R6_of_residue_inf_v5`, assembled from the banked chain
        `hDConv_gatedWitnessN1_of_delta_final`  (consumer, J4-117)
          ∘  `hpar_discharge` / `htime_discharge` / `hR_discharge` / `heatConvInner_intervalIntegrable_H`
             (F2 group, J4-145)
          ∘  `hDelta_gatedWitnessN1_final`  (hDelta with `hBoundary` discharged, J4-120).
    The derivative family `Da` is fixed to the truncated Laplacian `DaTrunc H F`, so the `hpar` slot's
    derivative and the `hDelta` slot's `Da` agree.  ⚠ CONDITIONAL only on the true residue (see the file
    header AUDIT): the near-diagonal parametrix family + D1/Levi dominations + base measurability/
    continuity + the C3ε engine family + cross-Lipschitz + floor + inner-continuity, AND the single hard
    locally-uniform `Da`-limit `hDaLimLU`.  NONE is the conclusion, none vacuous.  NOT `a₁ = R/6`. -/
theorem hDConv_from_banked (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    -- near-diagonal parametrix family (for `hDelta`):
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        vanVleckGatedWitness g gi hChr hK S a b τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    -- D1 / Levi Gaussian dominations:
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    -- Levi continuity + base measurabilities (for `hDelta`):
    (hBcont : ContinuousOn
        (fun x : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
        (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable
        (fun z : Point n => vanVleckGatedWitness g gi hChr hK S a b τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable
        (fun z : Point n => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    -- base `s`-measurability (`hMeasFII`; feeds `hDConv` directly AND R4):
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    -- R1 (`htime`) carries:
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (Set.Ioo 0 u))
    -- R2 (`hpar`) carries (the C3ε under-∫ engine family):
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
      HasDerivAt (fun a' => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) a')
    -- R3 (`hR`) carries (cross-Lipschitz mixed-second-difference):
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- the single hard residue: the locally-uniform `Da`-limit (`hDaLimLU`):
    (DaLim : ℝ → ℝ)
    (hDaLimLU : TendstoLocallyUniformlyOn
        (fun m u => DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u)
        DaLim atTop U) :
    DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t := by
  -- R4: `hFII` (interval-integrability of the inner pairing) from the dominations + `hMeasFII`.
  have hFII := heatConvInner_intervalIntegrable_H
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    T U hUpos hUT A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hMeasFII
  -- R2: `hpar` (Da := DaTrunc) from the C3ε engine family.
  have hpar := hpar_discharge
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    U nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
  -- R1: `htime` from the floor + inner-continuity (+ `hFII`).
  have htime := htime_discharge
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    U hUfloor hFII hInnerCont
  -- R3: `hR` from the cross-Lipschitz bound.
  have hR := hR_discharge
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    U L hLnn hCross
  -- `hDelta` (with `hBoundary` discharged) from the near-diagonal parametrix + `hDaLimLU`.
  have hDelta := hDelta_gatedWitnessN1_final g gi hChr hK S a b T hT U hUopen hUpos hUT
    r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ hA₀ hA₁ hAdom C_L hC_L hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    (fun m u => DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u)
    DaLim hDaLimLU
  -- compose into the concrete `hDConv` consumer.
  exact hDConv_gatedWitnessN1_of_delta_final g gi hChr hK S a b t T hT U hUopen htU hUpos hUT
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hMeasFII
    (fun m u => DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u)
    hpar htime hR _ hDelta

/-! ###############################################################################
    ### (3) `a1_R6_of_residue_inf_v6` — v5 with `hDConv` REPLACED by its residue.
    ############################################################################### -/

/-- **★★★ J4-209 (3) — `a1_R6_of_residue_inf_v6`.**  Exactly `CConvConcreteThreading.a1_R6_of_residue_inf_v5`
    with the black-box `hDConv : DifferentiableAt ℝ (fun u => heatConv H F u 0 0) t` carry REMOVED and
    supplied INTERNALLY by `hDConv_from_banked` from the strictly-lower analytic residue (near-diagonal
    parametrix + D1/Levi dominations + base measurability/continuity + the C3ε engine family + cross-
    Lipschitz + floor + inner-continuity) and the single hard locally-uniform `Da`-limit `hDaLimLU`.  All
    other v5 carries (Ricci-source RNC data, the Levi/Duhamel interface `hInt`/`hDuhamel`/`hInter`, the
    `C²` facade bundles + `hD1`) are threaded through VERBATIM.  ⚠ STILL NOT `a₁ = R/6`; the residue is
    honest satisfiable analytic data + `hDaLimLU`, none the conclusion, none vacuous. -/
theorem a1_R6_of_residue_inf_v6 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) 2 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
        = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
          + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0)
    (hInter : heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
            (fun τ p q => (-1 : ℝ) ^ (k + 1)
              * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) τ p q)
            t 0 0)
    (hCH : ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n))
    -- the CConv `C²` threading ingredient set (v5, verbatim):
    (uu : Set (Point n)) (hu_open : IsOpen uu) (hu0 : (0 : Point n) ∈ uu)
    (Bs Ba Bd Cf : ℝ) (Dmap : Point n → (Point n →L[ℝ] ℝ))
    (metric : CConvMetricData g gi)
    (chart : CConvChartGateData g gi hChr hK S a b t uu)
    (source : CConvSourceData
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) t Cf)
    (derivData : CConvDerivativeData g gi hChr hK S a b t uu
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      Dmap)
    (env : CConvEnvelopeData g gi hChr hK S a b t uu Bs Ba Bd)
    (hD1 : ContDiffAt ℝ 1 Dmap (0 : Point n))
    -- ★ the `hDConv` residue (replacing the v5 black-box `hDConv`):
    (T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        vanVleckGatedWitness g gi hChr hK S a b τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn
        (fun x : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
        (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable
        (fun z : Point n => vanVleckGatedWitness g gi hChr hK S a b τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable
        (fun z : Point n => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
      HasDerivAt (fun a' => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) a')
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    (DaLim : ℝ → ℝ)
    (hDaLimLU : TendstoLocallyUniformlyOn
        (fun m u => DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u)
        DaLim atTop U) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- re-derive the `hDConv` `DifferentiableAt` slot from the banked residue.
  have hDConv := hDConv_from_banked g gi hChr hK S a b t T hT U hUopen htU hUpos hUT
    r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
    L hLnn hCross DaLim hDaLimLU
  -- feed the v5 capstone with `hDConv` now discharged.
  exact a1_R6_of_residue_inf_v5 g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0
    hg hg0 hgi hΓ hdg0 htr hsrc hEboundW_le hInt hDuhamel hInter hDConv hCH
    uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hD1

end QIQTH.HDConvThreading

section AxiomChecks
open QIQTH.HDConvThreading
#print axioms hDConv_from_banked
#print axioms a1_R6_of_residue_inf_v6
end AxiomChecks
