/-
  F2CarryDischarge2 — J4-246: the F2 CARRY DISCHARGE — driving the three honest J4-245 carries of
  `InnerMeasFubini.f2Pack_concrete` (`hInner`, `hWitDeriv`, `hContDom`) toward zero-carry.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It discharges
  two of the three honest carries that `InnerMeasFubini.f2Pack_concrete` still consumes as inputs,
  reducing each to strictly lighter, satisfiable, non-vacuous suppliers that are ALREADY BANKED
  (or are honest geometric/analytic data), and re-bundles the F2 pile in `f2Pack_concrete_v2`.
  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses,
  no conclusion-in-disguise.  No existing file is edited.

  ── WHAT IS DISCHARGED HERE (axiom-free, no `sorry`).

    (i)  `hInner_discharged` — the UNGATED order-`1` global-cutoff parametrix joint `(s,z)`
         ae-measurability at FIELD POINT `0`, window `uIoc 0 d`, measure `volume`.  Route: the outer
         kernel `(τ,w) ↦ radialCutoff a b w · heatParametrix 1 Θ u τ w` is globally Borel-measurable
         (`InnerKernelJointMeas.witnessInner_measurable_uncurry`), and the section map
         `(s,z) ↦ (c−s, V z 0)` is product-ae-measurable (`s`-affine measurable ×
         `InnerKernelJointMeas.aemeasurable_chart_snd` at field `0`), so `Measurable.comp_aemeasurable`
         closes it — the witness is definitionally that composition.  Reduces `hInner` to
         `{hΘc, hΘne, huc, hVmap0}` (van-Vleck / transport continuity + the field-`0` chart
         `volume`-measurability), the direct `hinnerJ_discharged` route at the fixed field point `0`.

    (ii) `hWitDeriv_discharged` — the `∂_τ` witness-field joint `(s,z)` ae-measurability at field
         point `0`.  Route: `HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4` proves the FULL joint
         `(τ,p,q)` strong measurability of `(τ,p,q) ↦ ∂_τ [vanVleckGatedWitness … τ p q]` (via the
         everywhere `τ`-derivative identity `witnessTauDeriv_eq_gatedTauRepProdS` to the globally
         Borel `gatedTauRepProdS` representative), and `(s,z) ↦ (c−s, 0, z)` is measurable, so
         `StronglyMeasurable.comp_measurable` gives the section.  Reduces `hWitDeriv` to
         `{hn, hKSmeas, hcar}` — the FULL-gate measurability + the SATISFIABLE (S-membership as
         hypothesis) `Cfield` amplitude-derivative carrier.

  ── WHAT STAYS CARRIED IN `f2Pack_concrete_v2` (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hKm`, `hSm0` — geometric gate measurability (`MeasurableSet K`, `MeasurableSet {z | 0 ∈ S z}`).
    • `hBcont`, `hUpos`, `hUT` — the caller's own Levi-strip continuity + window bounds.
    • `hLeviJoint` — the Levi-series joint `(s,z)` measurability on the truncated window (its own
      lower-level discharge from `hBcont`/`hFzero` is the separate re-thread task, out of scope here).
    • `hContDom` — the per-interior-point dominated-continuity datum for `hInnerCont` (its reduction to
      the raw Gaussian dominations is the remaining `(iii)` analytic task).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InnerMeasFubini
import QIQTH.InnerKernelJointMeas
import QIQTH.HgateSatAudit

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.InnerKernelJointMeas QIQTH.HgateSatAudit
open scoped Interval Topology BigOperators

namespace QIQTH.F2CarryDischarge2

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (i) — `hInner_discharged`: the ungated inner parametrix joint `(s,z)` measurability
    ###       at field point `0`, reduced to `{hΘc, hΘne, huc, hVmap0}`.
    ############################################################################### -/

/-- **★★ `hInner_discharged` — THE `hInner` CARRY, DISCHARGED at field point `0`.**  The UNGATED
    order-`1` global-cutoff parametrix witness joint `(s,z)`-ae-strong-measurability, exactly the
    `hInner` shape `InnerMeasFubini.f2Pack_concrete` consumes (`∀ c d`, window `uIoc 0 d`, measure
    `volume`, field point `0`).  Route: the outer kernel is globally Borel (`witnessInner_measurable_uncurry`)
    and the section `(s,z) ↦ (c−s, V z 0)` is product-ae-measurable (affine × `aemeasurable_chart_snd`).
    Reduces `hInner` to the lighter suppliers `{hΘc, hΘne, huc, hVmap0}`.  NOT `a₁ = R/6`. -/
theorem hInner_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hVmap0 : AEMeasurable
      (fun z : Point n => uniformInverseChart g gi hChr hK z (0 : Point n)) volume) :
    ∀ c d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hChr hK) (c - p.1) 0 p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))) := by
  intro c d
  have houter := witnessInner_measurable_uncurry (n := n)
    (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) a b hΘc hΘne huc
  have hchart : AEMeasurable
      (fun p : ℝ × Point n => uniformInverseChart g gi hChr hK p.2 (0 : Point n))
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))) :=
    aemeasurable_chart_snd (volume.restrict (Set.uIoc 0 d)) volume
      (uniformInverseChart g gi hChr hK) (0 : Point n) hVmap0
  have hpair : AEMeasurable
      (fun p : ℝ × Point n =>
        (c - p.1, uniformInverseChart g gi hChr hK p.2 (0 : Point n)))
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))) :=
    ((measurable_const.sub measurable_fst).aemeasurable).prodMk hchart
  exact (houter.comp_aemeasurable hpair).aestronglyMeasurable

/-! ###############################################################################
    ### (ii) — `hWitDeriv_discharged`: the `∂_τ` witness-field joint `(s,z)` measurability
    ###        at field point `0`, reduced to `{hn, hKSmeas, hcar}`.
    ############################################################################### -/

/-- **★★ `hWitDeriv_discharged` — THE `hWitDeriv` CARRY, DISCHARGED at field point `0`.**  The
    `∂_τ`-witness joint `(s,z)`-ae-strong-measurability, exactly the `hWitDeriv` shape
    `InnerMeasFubini.f2Pack_concrete` consumes (`∀ c d`, window `uIoc 0 d`, measure `volume`, field
    point `0`).  Route: `HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4` gives the FULL joint
    `(τ,p,q)` strong measurability of the `∂_τ` witness kernel, and `(s,z) ↦ (c−s, 0, z)` is
    measurable, so `StronglyMeasurable.comp_measurable` yields the section (the field point `0`
    substitution is definitional).  Reduces `hWitDeriv` to the SATISFIABLE `{hn, hKSmeas, hcar}`.
    NOT `a₁ = R/6`. -/
theorem hWitDeriv_discharged (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1)) :
    ∀ c d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 p.2) (c - p.1))
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))) := by
  intro c d
  have hSM := tauDeriv_prod_stronglyMeasurable_v4 hn g gi hChr hK S a b hKSmeas hcar
  have hφ : Measurable
      (fun p : ℝ × Point n => ((c - p.1, (0 : Point n), p.2) : ℝ × Point n × Point n)) :=
    (measurable_const.sub measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  exact (hSM.comp_measurable hφ).aestronglyMeasurable

/-! ###############################################################################
    ### ★ THE F2 PACK — v2: the four concrete slots, with `hInner` and `hWitDeriv`
    ###   internally discharged from their lighter suppliers.
    ############################################################################### -/

/-- **★★★ `f2Pack_concrete_v2` — THE F2 SUPPLY WITH `hInner`/`hWitDeriv` DISCHARGED.**  Identical
    conclusion (the four deferred F2 slots `hMeasFII`/`hInnerCont`/`hFmeas`/`hF'meas`) to
    `InnerMeasFubini.f2Pack_concrete`, but the two J4-245 carries `hInner` and `hWitDeriv` are now
    BUILT INTERNALLY by `hInner_discharged` / `hWitDeriv_discharged` from their strictly lighter,
    banked-supplier inputs:
      • `hInner`     ← `{hΘc, hΘne, huc, hVmap0}` (van-Vleck / transport continuity + field-`0`
                        chart `volume`-measurability);
      • `hWitDeriv`  ← `{hn, hKSmeas, hcar}` (FULL-gate measurability + the SATISFIABLE `Cfield`
                        amplitude-derivative carrier — S-membership on the hypothesis side).
    The remaining carried inputs `{hKm, hSm0, hLeviJoint, hBcont, hUpos, hUT, hContDom}` are exactly
    the v2'-level binders (`hLeviJoint`'s `hBcont`/`hFzero` reduction and `hContDom`'s raw-Gaussian
    reduction are the separate remaining tasks).  Each carried input is satisfiable, non-vacuous,
    none the conclusion.  NOT `a₁ = R/6`. -/
theorem f2Pack_concrete_v2 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hVmap0 : AEMeasurable
      (fun z : Point n => uniformInverseChart g gi hChr hK z (0 : Point n)) volume)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hBcont : ContinuousOn
      (fun x : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hContDom : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u,
        ∃ bound : Point n → ℝ, Integrable bound (volume : Measure (Point n)) ∧
          (∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume : Measure (Point n))) ∧
          (∀ᶠ s in 𝓝 s₀, ∀ᵐ z ∂(volume : Measure (Point n)),
            ‖vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖
              ≤ bound z) ∧
          (∀ᵐ z ∂(volume : Measure (Point n)), ContinuousAt
            (fun s => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) s₀)) :
    -- (F2-a) hMeasFII
    (∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    -- (F2-b) hInnerCont
    ∧ (∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (Set.Ioo 0 u))
    -- (F2-c) hFmeas
    ∧ (∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    -- (F2-d) hF'meas
    ∧ (∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) :=
  QIQTH.InnerMeasFubini.f2Pack_concrete g gi hChr hK S a b T U hKm hSm0
    (hInner_discharged g gi hChr hK a b hΘc hΘne huc hVmap0)
    (hWitDeriv_discharged hn g gi hChr hK S a b hKSmeas hcar)
    hLeviJoint hBcont hUpos hUT hContDom

end QIQTH.F2CarryDischarge2

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.F2CarryDischarge2
#print axioms hInner_discharged
#print axioms hWitDeriv_discharged
#print axioms f2Pack_concrete_v2
end AxiomChecks
