/-
  EveryCeilingFamilies — J4-388: THE EVERY-CEILING GAUSSIAN-DOMINATION FAMILIES.
  Discharging the every-ceiling carries `hAdomEvery` / `hFdomEvery` of the `s`-leg widening
  (`ESLegWidening.hES_all` / `hLapS_all`, J4-387) DOWN to the banked geometric suppliers, and
  delivering the honest verdict + capped-refinement unlock for the laplaceBeltrami-slice family
  `hLapDomEvery`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  SURVIVING labelled census carries.  This file only REDUCES the two every-ceiling Gaussian-domination
  carries of the `s`-leg widening (`hAdomEvery`, `hFdomEvery`) to their banked FIXED-ceiling suppliers
  (the affine `hEdom` inner bound J4-380, and the `dataLevi` / `source_from_leviData` Levi-envelope
  J4-385/…) — a pure every-ceiling quantifier reduction, no new analytic content.  For the
  laplaceBeltrami-slice family `hLapDomEvery` it delivers the τ-lower-bound VERDICT plus a lower-capped
  pairing engine that unlocks it from the crude `τ⁻¹` bank.  NO `sorry` (header prose excepted), NO new
  axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to (or trivially yielding) the
  conclusion, NO existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS.

  •  (F1) `hAdomEvery_from_hEdom` — THE EVERY-CEILING HEAT FAMILY, `hAdomEvery`, from geometry.  For each
     ceiling `Tc` apply the J4-382 fixed-`T` repackaging `CensusDominations.hAdomHeat_from_hEdom` at
     `T := max Tc 0` to the UNCAPPED affine `hEdom` inner bound
     (`CommonGateShell.hEdom_from_geometry`, ∀ τ>0), yielding the `hAdomEvery` carry shape with
     `wA := 3/2`, `CA := (E₀ + E₁·(max Tc 0))·√(3/2)ⁿ` (the `max … 0` keeps `CA ≥ 0` for `Tc < 0`, where
     the body is vacuous).

  •  (F2) `hFdomEvery_from_dataLevi` — THE EVERY-CEILING LEVI ENVELOPE, `hFdomEvery`, from the `dataLevi`
     carries.  The `dataLevi` builder's `hpkgBound` carry is ALL-`t'`-shaped (`∀ t' τ p q, …`), so ONE
     carry serves EVERY ceiling: for each `Tc > 0` run `DataLeviDischarge.dataLevi_from_geometry` at
     `T := Tc` and `GlobalRawBoundFacade.source_from_leviData` to extract `C_L`, then specialize `y := 0`
     (`sub_zero`) to the `hFdomEvery` shape with `wF := 2`, `CF := C_L`.  For `Tc ≤ 0` the body is vacuous
     (witness `wF := 2`, `CF := 0`).

  •  (F4) `hES_hypothesis_light` — the census `hES` `∀ (m u)` shape (`ESLegWidening.hES_all`) with the
     two every-ceiling Gaussian-domination carries THREADED to geometry via F1 + F2.  Residual carries:
     `hFzero` (banked `hFzero_concrete`, not required here — kept as the honest binder), the affine
     `hEdom` inner bound (F1 supplier), the `dataLevi` carries `hEmeas`/`hpkgBound` (F2 suppliers), and
     the `∀ u` slice measurability `hmeas`.

  ── F3 — THE laplaceBeltrami-SLICE FAMILY `hLapDomEvery`: THE τ-LOWER-BOUND VERDICT + CAPPED UNLOCK ──
     VERDICT: **YES, the τ-lower-bound unlocks the family.**  On the pairing interval `[0, u−ε_m]` the
     first factor is evaluated at time `τ = u − s` with `s ∈ (0, u−ε_m]`, hence `τ ∈ [ε_m, u)` — `τ` is
     BOUNDED BELOW by `ε_m > 0`.  So the laplaceBeltrami domination is only needed for `τ ≥ ε_m`, NOT
     down to `0`.  A crude `C·τ⁻¹·gaussDdim (wL·τ) (0−z)` bound (the ONLY banked second-derivative
     envelope — its `τ⁻¹` blows up as `τ → 0`) restricted to `τ ≥ ε_m` becomes `(C/ε_m)·gaussDdim …`,
     a GENUINE Gaussian bound.  The CURRENT engine `DaLimEasyTranche.pairing_intervalIntegrable` demands
     the domination for ALL `0 < τ ≤ Tc` (down to `0`), so the uncapped `hLapDomEvery` carry can NOT
     absorb the crude bank.  This file supplies the honest fix — a lower-capped v2 of the engine (NOT
     editing the old):
       •  `pairing_intervalIntegrable_lowerCapped` — the pairing interval-integrability whose first
          factor domination `hAdom` is only required on `[ε_m, Tc]` (given the strip endpoints `≤ u−ε_m`).
       •  `gaussDdim_crude_to_capped` — the arithmetic unlock: `τ⁻¹ ≤ ε_m⁻¹` on `[ε_m, ∞)` turns a crude
          `C·τ⁻¹·G` bound into the capped `(C·ε_m⁻¹)·G` Gaussian bound.
       •  `hLapS_all_capped` — the census `hLapS` `∀ (m u)` shape fed by the CAPPED every-ceiling
          laplaceBeltrami family `hLapDomEveryCapped` (weaker — only `τ ≥ ε_m`, so the crude bank
          satisfies it) + the F2-style `hFdomEvery`.
     ⚠ The capped family itself still rests on the surviving crude second-derivative bank (the `hAdom2`
     residue), so `hLapDomEvery` is NOT fully geometry-discharged — only its consumption is made crude-
     compatible.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusDominations
import QIQTH.DataLeviDischarge
import QIQTH.GlobalRawBoundFacade
import QIQTH.ESLegWidening

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.LeviSeriesLocalData
open QIQTH.DaLimLUWallRecon QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing QIQTH.CConvV2WitnessStar
open QIQTH.GaussianWidthTolerant QIQTH.HEmeasBorelAudit QIQTH.LaplaceBeltrami
open scoped Interval Topology BigOperators

namespace QIQTH.EveryCeilingFamilies

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (F1) — the every-ceiling HEAT family `hAdomEvery` from geometry.
    ############################################################################### -/

/-- **★ (F1) — `hAdomEvery_from_hEdom`.**  THE EVERY-CEILING HEAT-KERNEL GAUSSIAN DOMINATION `hAdomEvery`
    (the `ESLegWidening.hES_all` carry shape) from the UNCAPPED affine `hEdom` inner bound
    (`CommonGateShell.hEdom_from_geometry`, ∀ τ>0).  For each ceiling `Tc` the J4-382 monotone repackaging
    `CensusDominations.hAdomHeat_from_hEdom` at `T := max Tc 0` gives the fixed-ceiling body; the `max … 0`
    absorption keeps `CA = (E₀ + E₁·(max Tc 0))·√(3/2)ⁿ ≥ 0` even for `Tc < 0` (where the body is
    vacuously satisfied).  `wA := 3/2`.  ⚠ NOT `a₁ = R/6`. -/
theorem hAdomEvery_from_hEdom (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (E₀ E₁ : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hEdom : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) :
    ∀ Tc : ℝ, ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ Tc → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z) := by
  intro Tc
  refine ⟨3 / 2, (E₀ + E₁ * max Tc 0) * Real.sqrt (3 / 2) ^ n, by norm_num, ?_, ?_⟩
  · have hT : (0 : ℝ) ≤ max Tc 0 := le_max_right _ _
    have hlin : (0 : ℝ) ≤ E₁ * max Tc 0 := mul_nonneg hE₁ hT
    exact mul_nonneg (by linarith) (pow_nonneg (Real.sqrt_nonneg _) n)
  · intro τ hτ0 hτTc z
    have hτT : τ ≤ max Tc 0 := le_trans hτTc (le_max_left _ _)
    exact QIQTH.CensusDominations.hAdomHeat_from_hEdom g gi hChr hK S a b (max Tc 0)
      E₀ E₁ hE₁ hEdom τ hτ0 hτT z

/-! ###############################################################################
    ### (F2) — the every-ceiling LEVI envelope `hFdomEvery` from the `dataLevi` carries.
    ############################################################################### -/

/-- **★ (F2) — `hFdomEvery_from_dataLevi`.**  THE EVERY-CEILING LEVI-SOURCE GAUSSIAN DOMINATION
    `hFdomEvery` (the `ESLegWidening.hES_all` / `hLapS_all` carry shape) from the `dataLevi` carries
    `hEmeas` / `hpkgBound`.  The builder's `hpkgBound` carry is ALL-`t'`-shaped, so ONE carry serves
    EVERY ceiling: for each `Tc > 0` run `DataLeviDischarge.dataLevi_from_geometry` at `T := Tc` (giving
    `LeviSeriesLocalData … (C·(1+Tc)) Tc`) and `GlobalRawBoundFacade.source_from_leviData` to extract the
    width-2 `C_L`, then specialize `y := 0` (`sub_zero`).  `wF := 2`, `CF := C_L`.  For `Tc ≤ 0` the body
    is vacuous (`wF := 2`, `CF := 0`).  Carries: `C`/`hCnn`, `hn` (`1 ≤ n`), `hEmeas`, `hpkgBound`.
    ⚠ NOT `a₁ = R/6`. -/
theorem hFdomEvery_from_dataLevi (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (C : ℝ) (hCnn : 0 ≤ C) (hn : 1 ≤ n)
    (hEmeas : tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b))
    (hpkgBound : ∀ (t' τ : ℝ) (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
      ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z := by
  intro Tc
  rcases le_or_gt Tc 0 with hTc | hTc
  · exact ⟨2, 0, by norm_num, le_refl 0,
      fun s hs hsTc _z => absurd hs (not_lt.mpr (le_trans hsTc hTc))⟩
  · have dataLevi := QIQTH.DataLeviDischarge.dataLevi_from_geometry
      g gi hChr hK S a b C Tc hCnn hTc hn hEmeas hpkgBound
    obtain ⟨⟨C_L, hCL0, hFdom⟩, _hFzero⟩ :=
      QIQTH.GlobalRawBoundFacade.source_from_leviData g gi hChr hK S a b Tc (C * (1 + Tc)) hn dataLevi
    refine ⟨2, C_L, by norm_num, hCL0, ?_⟩
    intro s hs hsTc z
    have h := hFdom s hs hsTc z 0
    rwa [sub_zero] at h

/-! ###############################################################################
    ### (F4) — the census `hES` `∀ (m u)` shape with F1 + F2 threaded to geometry.
    ############################################################################### -/

/-- **★ (F4) — `hES_hypothesis_light`.**  The census (ix) `hES` binder in its `∀ (m u)` shape
    (`ESLegWidening.hES_all`), with the two EVERY-CEILING Gaussian-domination carries `hAdomEvery` /
    `hFdomEvery` THREADED to geometry via F1 (`hAdomEvery_from_hEdom`, from the affine `hEdom` inner bound)
    and F2 (`hFdomEvery_from_dataLevi`, from the `dataLevi` carries).  Residual carries: `hFzero` (the Levi
    source vanishing — banked by `hFzero_concrete`, kept here as the honest binder), the affine `hEdom`
    inner bound (`hE₀`/`hE₁`/`hEdom`), the `dataLevi` carries (`C`/`hCnn`/`hEmeas`/`hpkgBound`), and the
    `∀ u` slice measurability `hmeas`.  ⚠ NOT `a₁ = R/6`. -/
theorem hES_hypothesis_light (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (E₀ E₁ : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hEdom : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (C : ℝ) (hCnn : 0 ≤ C)
    (hEmeas : tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b))
    (hpkgBound : ∀ (t' τ : ℝ) (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmeas : ∀ (m : ℕ) (u : ℝ), AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m) :=
  QIQTH.ESLegWidening.hES_all g gi hChr hK S a b hFzero
    (hAdomEvery_from_hEdom g gi hChr hK S a b E₀ E₁ hE₀ hE₁ hEdom)
    (hFdomEvery_from_dataLevi g gi hChr hK S a b C hCnn hn hEmeas hpkgBound)
    hmeas

/-! ###############################################################################
    ### (F3) — the τ-lower-bound unlock: lower-capped pairing engine + crude conversion.
    ############################################################################### -/

/-- **★ (F3·engine) — `pairing_intervalIntegrable_lowerCapped`.**  A LOWER-CAPPED v2 of
    `DaLimEasyTranche.pairing_intervalIntegrable` (the old file UNCHANGED).  On the pairing interval the
    first factor is evaluated at `τ = u − s`; if BOTH strip endpoints satisfy `α, β ≤ u − ε_m` then
    `s ≤ u − ε_m`, hence `τ = u − s ≥ ε_m`.  So the first-factor domination `hAdom` is only required on
    `[ε_m, Tc]` (never down to `0`) — this is what lets a crude `τ⁻¹` bound feed the engine.  Everything
    else is verbatim the banked engine.  ⚠ NOT `a₁ = R/6`. -/
theorem pairing_intervalIntegrable_lowerCapped
    (A F : ℝ → Point n → Point n → ℝ)
    (u Tc εₘ wA CA wF CF : ℝ)
    (hu : 0 < u) (huTc : u ≤ Tc) (hεₘ : 0 < εₘ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hAdom : ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
        |A τ 0 z| ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
        |F s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, F s z 0 = 0)
    (α β : ℝ) (hαcap : α ≤ u - εₘ) (hβcap : β ≤ u - εₘ)
    (hmeas : AEStronglyMeasurable
        (fun s => ∫ z, A (u - s) 0 z * F s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc α β))) :
    IntervalIntegrable (fun s => ∫ z, A (u - s) 0 z * F s z 0) volume α β := by
  set M : ℝ := CA * CF * gaussDdim (min wA wF * u) (0 : Point n) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; exact mul_nonneg (mul_nonneg hCA hCF) (gaussDdim_nonneg _ _)
  have hgconst : IntegrableOn (fun _ : ℝ => M) (Set.uIoc α β) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hune : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ u := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton u
  refine (intervalIntegrable_iff).mpr (Integrable.mono' hgconst hmeas ?_)
  filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae hune] with s hsmem hsne
  have hub : s ∈ Set.Ioc (min α β) (max α β) := hsmem
  have hslo : s ≤ u - εₘ := le_trans hub.2 (max_le hαcap hβcap)
  have hsu' : s ≤ u := by linarith
  rcases le_or_gt s 0 with hs0 | hs0
  · have hzeroFun : (fun z => A (u - s) 0 z * F s z 0) = fun _ => (0 : ℝ) := by
      funext z; rw [hFzero s hs0 z, mul_zero]
    have hI0 : (∫ z, A (u - s) 0 z * F s z 0) = 0 := by
      rw [hzeroFun]; exact integral_zero (Point n) ℝ
    simp only [hI0, norm_zero]; exact hMnn
  · have hsu : s < u := lt_of_le_of_ne hsu' hsne
    have hts : 0 < u - s := by linarith
    have hτlo : εₘ ≤ u - s := by linarith
    set Dz : Point n → ℝ :=
      fun z => (CA * CF) * (gaussDdim (wA * (u - s)) z * gaussDdim (wF * s) z) with hDzdef
    have hDz_int : Integrable Dz volume := by
      rw [hDzdef]
      exact (gaussDdim_pair_integrable (wA * (u - s)) (wF * s)).const_mul (CA * CF)
    have hpt : ∀ z : Point n, ‖A (u - s) 0 z * F s z 0‖ ≤ Dz z := by
      intro z
      rw [Real.norm_eq_abs, abs_mul]
      have hAz := hAdom (u - s) hτlo (by linarith) z
      rw [gaussDdim_zero_sub] at hAz
      have hFz := hFdom s hs0 (le_trans hsu' huTc) z
      rw [hDzdef]
      calc |A (u - s) 0 z| * |F s z 0|
          ≤ (CA * gaussDdim (wA * (u - s)) z) * (CF * gaussDdim (wF * s) z) :=
            mul_le_mul hAz hFz (abs_nonneg _) (mul_nonneg hCA (gaussDdim_nonneg _ _))
        _ = (CA * CF) * (gaussDdim (wA * (u - s)) z * gaussDdim (wF * s) z) := by ring
    have hpair_le : gaussDdim (wA * (u - s) + wF * s) (0 : Point n)
        ≤ gaussDdim (min wA wF * u) (0 : Point n) :=
      gaussDdim_zero_antitone (min wA wF * u) (wA * (u - s) + wF * s)
        (mul_pos (lt_min hwA hwF) hu) (abLowerW wA u wF s hs0.le hsu')
    have hDz_le : ∫ z, Dz z ≤ M := by
      have hval : (∫ z, Dz z) = (CA * CF) * gaussDdim (wA * (u - s) + wF * s) (0 : Point n) := by
        rw [hDzdef, integral_const_mul,
          gaussDdim_pairing_integral (wA * (u - s)) (wF * s) (mul_pos hwA hts) (mul_pos hwF hs0)]
      rw [hval, hMdef]
      calc (CA * CF) * gaussDdim (wA * (u - s) + wF * s) (0 : Point n)
          ≤ (CA * CF) * gaussDdim (min wA wF * u) (0 : Point n) :=
            mul_le_mul_of_nonneg_left hpair_le (mul_nonneg hCA hCF)
        _ = CA * CF * gaussDdim (min wA wF * u) (0 : Point n) := by ring
    calc ‖∫ z, A (u - s) 0 z * F s z 0‖
        ≤ ∫ z, ‖A (u - s) 0 z * F s z 0‖ :=
          norm_integral_le_integral_norm (fun z => A (u - s) 0 z * F s z 0)
      _ ≤ ∫ z, Dz z :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hDz_int (ae_of_all _ hpt)
      _ ≤ M := hDz_le

/-- **★ (F3·arithmetic) — `gaussDdim_crude_to_capped`.**  THE UNLOCK ARITHMETIC.  A crude
    `C·τ⁻¹·gaussDdim (wL·τ) (0−z)` bound valid on `(0, Tc]` — whose `τ⁻¹` prefactor blows up as `τ → 0`
    — restricted to the lower-capped range `[ε_m, Tc]` becomes the GENUINE Gaussian bound
    `(C·ε_m⁻¹)·gaussDdim (wL·τ) (0−z)`, via `τ⁻¹ ≤ ε_m⁻¹` for `τ ≥ ε_m > 0`.  Generic in `A`; this is
    exactly what makes the crude second-derivative bank feed `pairing_intervalIntegrable_lowerCapped`.
    ⚠ NOT `a₁ = R/6`. -/
theorem gaussDdim_crude_to_capped (A : ℝ → Point n → Point n → ℝ)
    (Tc εₘ Ccrude wL : ℝ) (hεₘ : 0 < εₘ) (hCcrude : 0 ≤ Ccrude)
    (hcrude : ∀ τ : ℝ, 0 < τ → τ ≤ Tc → ∀ z : Point n,
        |A τ 0 z| ≤ Ccrude * τ⁻¹ * gaussDdim (wL * τ) (0 - z)) :
    ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
      |A τ 0 z| ≤ (Ccrude * εₘ⁻¹) * gaussDdim (wL * τ) (0 - z) := by
  intro τ hτlo hτTc z
  have hτ0 : 0 < τ := lt_of_lt_of_le hεₘ hτlo
  refine le_trans (hcrude τ hτ0 hτTc z) ?_
  have hinv : τ⁻¹ ≤ εₘ⁻¹ := by gcongr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinv hCcrude) (gaussDdim_nonneg _ _)

/-- **★ (F3·consumption) — `hLapS_all_capped`.**  The census (ix) `hLapS` binder in its `∀ (m u)` shape
    (cf. `ESLegWidening.hLapS_all`), fed by the CAPPED every-ceiling laplaceBeltrami-slice family
    `hLapDomEveryCapped` (∀ `Tc`, ∀ `ε_m > 0`, the domination on `[ε_m, Tc]` — WEAKER than the uncapped
    `hLapDomEvery`, so the crude `τ⁻¹` bank satisfies it via `gaussDdim_crude_to_capped`) together with the
    F2-style `hFdomEvery`.  CASE 1 (`u − ε_m ≤ 0`) is `ESLegWidening.intervalIntegrable_of_deg`; CASE 2
    (`u − ε_m > 0`) is `pairing_intervalIntegrable_lowerCapped` at ceiling `Tc := u`, lower cap
    `ε_m := epsSeq m`, strip `[0, u−ε_m]` (both endpoints `≤ u − ε_m`).  ⚠ NOT `a₁ = R/6`. -/
theorem hLapS_all_capped (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hLapDomEveryCapped : ∀ Tc : ℝ, ∀ εₘ : ℝ, 0 < εₘ → ∃ wL CL : ℝ, 0 < wL ∧ 0 ≤ CL ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |laplaceBeltrami g gi
              (fun x => vanVleckGatedWitness g gi hChr hK S a b τ x z) 0|
            ≤ CL * gaussDdim (wL * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hmeas : ∀ (m : ℕ) (u : ℝ), AEStronglyMeasurable
        (fun s => ∫ z, laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m) := by
  intro m u
  rcases le_or_gt (u - epsSeq m) 0 with hdeg | hpos
  · exact QIQTH.ESLegWidening.intervalIntegrable_of_deg
      (fun τ _ z => laplaceBeltrami g gi
        (fun x => vanVleckGatedWitness g gi hChr hK S a b τ x z) 0)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      u (u - epsSeq m) hdeg hFzero
  · have hεpos := epsSeq_pos m
    have hu0 : 0 < u := by linarith
    obtain ⟨wL, CL, hwL, hCL, hLapDom⟩ := hLapDomEveryCapped u (epsSeq m) hεpos
    obtain ⟨wF, CF, hwF, hCF, hFdom⟩ := hFdomEvery u
    exact pairing_intervalIntegrable_lowerCapped
      (fun τ _ z => laplaceBeltrami g gi
        (fun x => vanVleckGatedWitness g gi hChr hK S a b τ x z) 0)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      u u (epsSeq m) wL CL wF CF hu0 le_rfl hεpos hwL hCL hwF hCF hLapDom hFdom hFzero
      0 (u - epsSeq m) (by linarith) le_rfl (hmeas m u)

end QIQTH.EveryCeilingFamilies

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.EveryCeilingFamilies.hAdomEvery_from_hEdom
#print axioms QIQTH.EveryCeilingFamilies.hFdomEvery_from_dataLevi
#print axioms QIQTH.EveryCeilingFamilies.hES_hypothesis_light
#print axioms QIQTH.EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped
#print axioms QIQTH.EveryCeilingFamilies.gaussDdim_crude_to_capped
#print axioms QIQTH.EveryCeilingFamilies.hLapS_all_capped
