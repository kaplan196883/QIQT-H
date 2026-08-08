/-
  InnerDiffFamily — J4-437 (Sol #20 item (i), the a₁ = R/6 convergence-trio campaign): THE
  DIFF-UNDER-∫ FAMILY OPENER.  Bridges the banked carrier-level frozen first-order interchange
  `W2Finish.w2_hQ1` (a SHARED-`V`, `∀ m i, ∀ u∈U, ∀ y∈V` equality shape) into the EXACT `hQ1` binder
  that the group-(3) per-`u` census `PerUCensusInstantiation.{hfrozen_pd1_perU_of_hQ1, perUCensus_phase1}`
  consumes (a PER-`(u,i,m)` existential `∃ V ∈ 𝓝 0` shape, with RHS the banked truncated primitive
  `FrozenGermInternal.fbulkInt …`), and threads it all the way to the per-`u` census `Tendsto`.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves NOTHING about
  `R/6`.  `a₁ = R/6` remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring
  stack AND on the surviving labelled carries threaded here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem here re-threads BANKED, satisfiable diff-under-∫ data into the
  exact `hQ1` shape the census binds.  NONE proves `a₁ = R/6`.  Each carried hypothesis is genuine,
  satisfiable, non-vacuous, and never the conclusion.  No `sorry` (header prose excepted), no `:= True`,
  no new axioms, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DIFF-UNDER-∫ BINDER MAP.

  ── hQ1 (THE census demanded statement, `PerUCensusInstantiation.perUCensus_phase1` binder):
       `∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∃ V ∈ 𝓝 (0 : Point n), ∀ y ∈ V,
          pd (fun x => heatConvFrozen W (leviSeries (heatOp g gi W)) u (u − εₘ) x 0) i y
            = fbulkInt g gi hC hK S a b u i m y`
     at `W := vanVleckGatedWitness g gi hC hK S a b`.  The census allows `V` to be chosen PER `(u,i,m)`.
     `fbulkInt … u i m y` is (definitionally) the truncated primitive
       `∫ s in (0)..(u−εₘ), ∫ z, witnessFieldDeriv … i (u−s) y z · leviSeries (heatOp g gi W) s z 0`.
     SUPPLIER (banked): `W2Finish.w2_hQ1` gives this equality on a SHARED open field nbhd `V ∋ 0` from
     the seven-leg frozen provider `hFrozenData`, itself firing `SecondOrderInterchange.
     pd_heatConvFrozen_interchange` per `(m,i,u,y)`.  Route to the census shape: supply the SAME `V`
     for every `(u,i,m)` (an m-UNIFORM nbhd — stronger than the census needs; dodges the m-collapse
     trap), and rewrite the RHS integral to `fbulkInt …` definitionally.
     DOMINATOR / m-UNIFORMITY: the seven `hFrozenData` legs live on the m-INDEPENDENT nbhd `V` (no
     nbhd collapse), but their `s`-dominator `boundY` and the truncated windows `uIoc 0 (u−εₘ)` are
     PER-`m`.  For hQ1 this is FINE — hQ1 is a per-`m` EQUALITY, with NO series over `m`; the
     m-summability requirement lives ONLY in the order-2 sliver carries (`hbulkderiv`/`hsliver`),
     which are SEPARATE census carries, NOT opened here.  ⟹ hQ1 legs = per-m-OK.

  ── hProv (the SEVEN-leg linewise diff-under-∫ provider, `perUCensus_phase1` binder, DIAGONAL window):
     the `t := u`, non-truncated `heatConv` analogue (`= J4-405 PerUProviders.hlin_field_concrete`
     input).  BANKED-CONCRETE at the shape level (threaded through `CConvV2DerivRep.hlin_as_D`); its
     seven legs are the measurability / interval-integrability / domination / HasDerivAt inputs.  OPEN
     as data (carried, not re-proved here).  DOMINATOR: `bound` is per-`(x,i)` (existential); the
     window `uIoc 0 t` is m-INDEPENDENT (diagonal).  m-UNIFORMITY: n/a (no `m` in `hProv`).

  ── hbulkderiv (bulk order-2 differentiation, `perUCensus_phase1` binder):
       `∀ u∈U, ∀ i m, ∀ x ∈ univ, HasFDerivAt (fbulkInt … u i m) (fderivBulk u i m x) x`.
     OPEN (carried).  On the FULL bulk cutoff `univ` (the moving endpoint is handled by the sliver
     machinery, NOT here).  DOMINATOR: the order-2 majorant.  ⚠ m-UNIFORMITY: this is where the trap
     bites — the order-2 majorants feeding `hsliver` MUST be summable/`O(√εₘ)` (they are: the census
     `hsliver` bound is `(C₀+C₁)·2√εₘ + C₂·εₘ → 0`).  FLAGGED as the genuine m-summable tranche; NOT
     opened here.

  ── WHAT LANDS (this file, ns `QIQTH.InnerDiffFamily`).
    • `innerDiff_census_hQ1_of_carrier` — the pure shape bridge: carrier-level shared-`V` equality
      (the exact `w2_hQ1` conclusion) ⟶ the census per-`(u,i,m)` existential `hQ1`.
    • `innerDiff_census_hQ1_of_frozenData` — ★ the census `hQ1`, DISCHARGED from the seven-leg frozen
      provider `hFrozenData` via the banked `W2Finish.w2_hQ1`.  THE hQ1 opener, in the census's exact
      shape.
    • `innerDiff_phase1` — ★★ the per-`u` census `Tendsto` (= `perUCensus_phase1`'s conclusion), with
      the `hQ1` binder DISCHARGED internally from `hFrozenData`; every other census field kept as an
      enumerated carry.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.W2Finish
import QIQTH.FrozenGermInternal
import QIQTH.PerUCensusInstantiation

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade QIQTH.Pd2ConvDissolution
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.InnerDiffFamily

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### `innerDiff_census_hQ1_of_carrier` — the pure carrier→census `hQ1` shape bridge.
    ############################################################################### -/

/-- **`innerDiff_census_hQ1_of_carrier`.**  THE SHAPE BRIDGE.  Given a SINGLE field neighborhood
    `V ∈ 𝓝 0` and the carrier-level frozen first-order interchange equality on `V` (the VERBATIM
    conclusion of `W2Finish.w2_hQ1`), produce the group-(3) per-`u` census `hQ1` binder — the
    PER-`(u,i,m)` existential `∃ V ∈ 𝓝 0, ∀ y ∈ V, pd (frozen germ) i y = fbulkInt … u i m y`.
    We supply the SAME `V` for every `(u,i,m)` (an m-UNIFORM nbhd; the census only needs SOME nbhd,
    so this is stronger and avoids any m-collapse), and the RHS integral is `fbulkInt … u i m y`
    definitionally.  Pure quantifier/shape plumbing; the honest carry `hcarrier` is strictly lower
    level than the census `Tendsto` conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem innerDiff_census_hQ1_of_carrier (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (V : Set (Point n)) (hV : V ∈ 𝓝 (0 : Point n))
    (hcarrier : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) :
    ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        ∃ V ∈ 𝓝 (0 : Point n),
          ∀ y ∈ V, pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
              (u - epsSeq m) x 0) i y
            = QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m y := by
  intro u hu i m
  refine ⟨V, hV, fun y hy => ?_⟩
  exact hcarrier m i u hu y hy

/-! ###############################################################################
    ### ★ `innerDiff_census_hQ1_of_frozenData` — the census `hQ1`, from the frozen provider.
    ############################################################################### -/

/-- **★ `innerDiff_census_hQ1_of_frozenData`.**  THE hQ1 OPENER, in the census's exact shape.  Given
    a field neighborhood `V ∈ 𝓝 0` and the SEVEN-leg frozen first-order diff-under-∫ provider
    `hFrozenData` (the `F3` carry of `W2Finish.w2_hQ1`: per `(m,i,u∈U,y∈V)` a real-line nbhd
    `snb ∈ 𝓝 (y i)`, the witness / field-derivative pairing measurabilities and interval-
    integrabilities, an interval-integrable `s`-dominator, and the outer `s`-level `HasDerivAt`
    family), produce the group-(3) census `hQ1` binder
      `∀ u ∈ U, ∀ i m, ∃ V ∈ 𝓝 0, ∀ y ∈ V,
         pd (frozen germ) i y = fbulkInt g gi hC hK S a b u i m y`.
    Route: `W2Finish.w2_hQ1` fires `SecondOrderInterchange.pd_heatConvFrozen_interchange` per
    `(m,i,u,y)` to the shared-`V` equality; `innerDiff_census_hQ1_of_carrier` re-wraps it into the
    per-`(u,i,m)` existential.  The honest carry is `hFrozenData`, the diff-under-∫ side conditions —
    strictly lower level than the census `Tendsto`.  m-UNIFORMITY: `V` is m-INDEPENDENT (no nbhd
    collapse); the per-`m` `s`-dominators are ADMISSIBLE because hQ1 is a per-`m` equality with no
    series over `m`.  ⚠ NOT `a₁ = R/6`. -/
theorem innerDiff_census_hQ1_of_frozenData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (V : Set (Point n)) (hV : V ∈ 𝓝 (0 : Point n))
    (hFrozenData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) ∧
          IntervalIntegrable
            (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            volume 0 (u - epsSeq m) ∧
          AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))) ∧
          IntervalIntegrable bound volume 0 (u - epsSeq m) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ bound s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
              (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w)) :
    ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        ∃ V ∈ 𝓝 (0 : Point n),
          ∀ y ∈ V, pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
              (u - epsSeq m) x 0) i y
            = QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m y :=
  innerDiff_census_hQ1_of_carrier g gi hC hK S a b U V hV
    (QIQTH.W2Finish.w2_hQ1 g gi hC hK S a b U V hFrozenData)

/-! ###############################################################################
    ### ★★ `innerDiff_phase1` — the per-`u` census `Tendsto`, `hQ1` discharged from `hFrozenData`.
    ############################################################################### -/

/-- **★★ `innerDiff_phase1`.**  THE per-`u` census `Tendsto` (= the conclusion of
    `PerUCensusInstantiation.perUCensus_phase1` / `PerUCensusTuple.hPd2conv_perU_fired`), with the
    `hQ1` census binder DISCHARGED INTERNALLY from the seven-leg frozen diff-under-∫ provider
    `hFrozenData` on the field neighborhood `V ∈ 𝓝 0` (via `innerDiff_census_hQ1_of_frozenData`), and
    every OTHER census field kept as an ENUMERATED CARRY: the heat-time domain `U`/`hUpos`, the field
    nbhd `nb`/`hnb_open`/`hnb0`, the seven-leg linewise DIAGONAL provider `hProv` (= J4-405's input
    carry), the order-2 derivative fields `fderivBulk`/`gderiv` + rate constants `C₀`/`C₁`/`C₂`, the
    interval-integrability `hGint`, the bulk order-2 differentiation `hbulkderiv`, the `O(√ε)` sliver
    bound `hsliver`, and the order-2 field continuity `hcont`.  Conclusion = the exact per-`u`
    frozen→full second-partial `Tendsto` binder.  Pure composition: `perUCensus_phase1` with `hQ1`
    supplied by the opener.  Every carry is satisfiable, non-vacuous, strictly lower-level than the
    conclusion, and none equals `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem innerDiff_phase1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hGint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (V : Set (Point n)) (hV : V ∈ 𝓝 (0 : Point n))
    (hFrozenData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) ∧
          IntervalIntegrable
            (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            volume 0 (u - epsSeq m) ∧
          AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))) ∧
          IntervalIntegrable bound volume 0 (u - epsSeq m) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ bound s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
              (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w)) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.PerUCensusInstantiation.perUCensus_phase1 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hGint hbulkderiv hsliver hcont
    (innerDiff_census_hQ1_of_frozenData g gi hC hK S a b U V hV hFrozenData)

end QIQTH.InnerDiffFamily

/-! ## THE DIFF LEDGER — the honest per-item table (with the m-uniformity column).

  `innerDiff_phase1` reproduces the per-`u` census `Tendsto` from the census carries, with the `hQ1`
  binder DISCHARGED-THIS-BRICK (traded for the seven-leg frozen diff-under-∫ provider `hFrozenData`
  via `innerDiff_census_hQ1_of_frozenData` ∘ the banked `W2Finish.w2_hQ1`).  Per-item status:

    item          role                                          status         m-UNIFORMITY
    ───────────   ───────────────────────────────────────────  ─────────────  ─────────────────────
    hQ1           frozen 1st-order interchange, census shape    ★ DISCHARGED   V m-INDEPENDENT (shared
                  (`∃ V∈𝓝0, pd (frozen germ)= fbulkInt…`)       (this brick)   nbhd; no collapse); the
                                                                               per-`m` `s`-dominators
                                                                               are ADMISSIBLE — hQ1 is
                                                                               a per-`m` EQUALITY, NO
                                                                               series over `m`.
    ├ hFrozenData·snb        real-line nbhd 𝓝(y i)              CARRY (leg 1)  n/a (per-y)
    ├ hFrozenData·hFmeas     witness pairing `s`-aesm, ∀w       CARRY (leg 2)  window uIoc0(u−εₘ) per-m;
    │                                                                          bank: W2Package Fubini
    ├ hFrozenData·hFint      witness pairing interval-integr.   CARRY (leg 3)  per-m window; bank:
    │                                                                          W2Finish.w2_hFint engine
    ├ hFrozenData·hF'meas    field-deriv pairing `s`-aesm       CARRY (leg 4)  per-m window
    ├ hFrozenData·bound,hbdd interval-integrable `s`-dominator  CARRY (leg 5)  PER-m (admissible: no
    │                                                                          m-series in hQ1)
    ├ hFrozenData·hbound     `‖·‖ ≤ bound` on window, ∀w∈snb    CARRY (leg 6)  per-m
    └ hFrozenData·hdiff      outer `s`-level HasDerivAt family  CARRY (leg 7)  per-m
    hProv         7-leg linewise provider, DIAGONAL window      CARRY          n/a (no `m`); window
                  (= J4-405 `hlin_field_concrete` input)                       uIoc 0 u m-INDEPENDENT
    hbulkderiv    bulk order-2 diff of `fbulkInt…` on univ      CARRY          ⚠ order-2 majorants MUST
                                                                               be m-SUMMABLE — the trap;
                                                                               NOT opened here
    hsliver       `O(√ε)` x-uniform sliver dist-bound           CARRY          ★ m-SUMMABLE: bound
                                                                               `(C₀+C₁)·2√εₘ+C₂εₘ → 0`
    hcont         order-2 field continuity on univ              CARRY          n/a
    hGint         `s`-profile interval-integrability            CARRY          n/a (diagonal)
    U,hUpos,nb,…  domain / nbhd / order-2 data                  CARRY (data)   n/a

  ⚠ VERDICT.  hQ1 is discharged in the census's EXACT shape down to the seven `hFrozenData` legs; the
  V is supplied m-UNIFORMLY (stronger than the census's per-`(u,i,m)` existential needs), so the
  M-UNIFORMITY TRAP does NOT bite at the hQ1 level — the per-`m` `s`-dominators are admissible because
  hQ1 carries no series over `m`.  The genuine m-summability requirement lives in the ORDER-2 sliver
  carries (`hbulkderiv`/`hsliver`), which `hsliver` already meets (`O(√εₘ) → 0`); those are SEPARATE
  census carries, NOT opened here.  This brick proves NOTHING about `a₁ = R/6`; it certifies the hQ1
  binder as reducible to the diff-under-∫ side conditions.  `a₁ = R/6` remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.InnerDiffFamily
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms innerDiff_census_hQ1_of_carrier
#print axioms innerDiff_census_hQ1_of_frozenData
#print axioms innerDiff_phase1
end AxiomChecks
