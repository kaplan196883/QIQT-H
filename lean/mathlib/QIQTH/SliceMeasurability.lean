/-
  SliceMeasurability — J4-383: the s-slice MEASURABILITY supplier (census pile (v)).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  This file supplies the FOUR carried s-slice
  ae-strong-measurability facts that the census strip / adjacency members
  (`CensusSweepOne.census_strip`, `CensusSweepOne.census_adj`) still consume as hypotheses —
      `hmeasLo`, `hmeasHi`  (the `heatOp · leviSeries` pairing),
      `hmeas2Lo`, `hmeas2Hi`  (the `witnessSecondXDeriv · leviSeries` pairing)
  — as genuine (std-3, axiom-free) theorems, built by composition of ALREADY-BANKED suppliers
  (the Fubini inner-integral engine `InnerMeasFubini.innerIntegral_aesm`) and a handful of honest,
  satisfiable, non-vacuous carries.  No `sorry`, no new axioms, no `:= True`, no vacuous or
  unsatisfiable hypotheses, no conclusion-in-disguise.

  ## THE STRUCTURAL ROUTE — route (a), joint CONTINUITY + Fubini.

    Each of the four facts is `s ↦ ∫ z, Φ(u−s, z) · Ψ(s, z)` on a window measure
    `volume.restrict (uIoc · ·)`, where
      • Φ = the FIRST factor evaluated at the SHIFTED time `u − s`:  either
          `heatOp g gi (vanVleckGatedWitness …) (u−s) 0 z`  (the `hmeasLo/Hi` pairing) or
          `witnessSecondXDeriv g gi hChr hK S a b i (u−s) z`  (the `hmeas2Lo/Hi` pairing);
      • Ψ = the Levi-series factor `leviSeries (heatOp g gi (vanVleckGatedWitness …)) s z 0`.

    The clean route is the SFinite product-marginal Fubini measurability
    (`InnerMeasFubini.innerIntegral_aesm`, i.e. `AEStronglyMeasurable.integral_prod_right'`):
    it reduces the s-slice map to the JOINT `(s,z)`-ae-strong-measurability of the product
    integrand.  Each factor's joint measurability is discharged from a carried joint
    CONTINUITY datum on the positive-time strip `Ioc 0 T ×ˢ univ` via
    `ContinuousOn.aestronglyMeasurable` + `Measure.prod_restrict` (exactly the banked
    `InnerMeasFubini.leviJoint_of_hBcont` route), composed with the continuous shift
    `s ↦ u − s` for the first factor.

    • The `Lo` window `uIoc 0 (u − εₘ)` sends `s ∈ (0, u−εₘ]` to `τ = u−s ∈ [εₘ, u) ⊆ (0,T]`,
      so the shifted first factor stays inside the continuity strip DIRECTLY.
    • The `Hi` window `uIoc (u − εₘ) u` sends `s ∈ (u−εₘ, u]` to `τ = u−s ∈ [0, εₘ)`, which
      hits `τ = 0` at the single endpoint `s = u`.  Since `{u}` is `volume`-null, we prove the
      fact on the OPEN window `Ioo (u−εₘ) u` (where `τ ∈ (0, εₘ) ⊆ (0,T]`) and transfer to
      `uIoc (u − εₘ) u` by the measure equality `restrict (Ioc ·) = restrict (Ioo ·)`
      (`Measure.restrict_congr_set Ioo_ae_eq_Ioc`).

  ── HONEST CARRIED INPUTS (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hHeatCont` — joint continuity of `(τ,z) ↦ heatOp g gi (vanVleckGatedWitness …) τ 0 z` on
      `Ioc 0 T ×ˢ univ` (satisfiable for the concrete Levi residual away from `τ = 0`; the
      `HeatOpWitnessContinuity` positive-time route — analogous to the banked `hBcont`).
    • `hSecCont` — joint continuity of `(τ,z) ↦ witnessSecondXDeriv g gi hChr hK S a b i τ z` on
      `Ioc 0 T ×ˢ univ` (the second-`x`-derivative continuity, per `i`).
    • `hBcont` — the caller's own Levi-strip joint continuity (the SAME carry as
      `InnerMeasFubini.hMeasFII_concrete`).
    • `hUT`, `hεU` — the window bounds `u ≤ T`, `epsSeq m ≤ u` (satisfiable: in the facade
      `epsSeq m < aa/2 ≤ u/2 < u ≤ T`).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InnerMeasFubini
import QIQTH.AmplitudePackage

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.InnerMeasFubini
open scoped Interval Topology BigOperators

namespace QIQTH.SliceMeasurability

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ENGINE A — the shifted first-factor joint `(s,z)` measurability from joint continuity.
    ############################################################################### -/

/-- **★ `shiftFactor_jointAESM`.**  If the two-variable factor `(τ,z) ↦ Φ τ z` is jointly
    `ContinuousOn` the positive-time strip `Ioc 0 T ×ˢ univ`, and the shift `s ↦ u − s` maps the
    measurable window `I` into `(0,T]` (i.e. `∀ s ∈ I, 0 < u−s ≤ T`), then the SHIFTED factor
    `(s,z) ↦ Φ (u−s) z` is `AEStronglyMeasurable` w.r.t. `(volume.restrict I).prod volume`.
    Route: `ContinuousOn.comp` with the continuous shift `s ↦ (u−s, z)` and the `MapsTo` datum,
    then `ContinuousOn.aestronglyMeasurable` + `Measure.prod_restrict` — exactly the banked
    `InnerMeasFubini.leviJoint_of_hBcont` closing.  NOT `a₁ = R/6`. -/
theorem shiftFactor_jointAESM (Φ : ℝ → Point n → ℝ) (T u : ℝ) (I : Set ℝ)
    (hI : MeasurableSet I)
    (hmaps : ∀ s ∈ I, (0 : ℝ) < u - s ∧ u - s ≤ T)
    (hcont : ContinuousOn (fun p : ℝ × Point n => Φ p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    AEStronglyMeasurable (fun p : ℝ × Point n => Φ (u - p.1) p.2)
      ((volume.restrict I).prod (volume : Measure (Point n))) := by
  have hσ : Continuous (fun p : ℝ × Point n => ((u - p.1, p.2) : ℝ × Point n)) := by fun_prop
  have hmapsto : Set.MapsTo (fun p : ℝ × Point n => ((u - p.1, p.2) : ℝ × Point n))
      (I ×ˢ (Set.univ : Set (Point n))) (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))) := by
    intro p hp
    exact ⟨Set.mem_Ioc.mpr (hmaps p.1 hp.1), Set.mem_univ _⟩
  have hcomp : ContinuousOn (fun p : ℝ × Point n => Φ (u - p.1) p.2)
      (I ×ˢ (Set.univ : Set (Point n))) :=
    hcont.comp hσ.continuousOn hmapsto
  have hms : MeasurableSet (I ×ˢ (Set.univ : Set (Point n))) := hI.prod MeasurableSet.univ
  have haesm := hcomp.aestronglyMeasurable
    (μ := (volume : Measure ℝ).prod (volume : Measure (Point n))) hms
  rwa [← Measure.prod_restrict, Measure.restrict_univ] at haesm

/-! ###############################################################################
    ### ENGINE B — the un-shifted factor joint `(s,z)` measurability from joint continuity.
    ############################################################################### -/

/-- **★ `factor_jointAESM_of_contOn`.**  If `(s,z) ↦ Ψ s z` is jointly `ContinuousOn` the
    positive-time strip `Ioc 0 T ×ˢ univ` and the measurable window `I ⊆ Ioc 0 T`, then
    `(s,z) ↦ Ψ s z` is `AEStronglyMeasurable` w.r.t. `(volume.restrict I).prod volume`.  This
    generalizes the banked `InnerMeasFubini.leviJoint_of_hBcont` (there `I = uIoc 0 u`) to an
    arbitrary measurable sub-window.  NOT `a₁ = R/6`. -/
theorem factor_jointAESM_of_contOn (Ψ : ℝ → Point n → ℝ) (T : ℝ) (I : Set ℝ)
    (hI : MeasurableSet I) (hsub : I ⊆ Set.Ioc 0 T)
    (hcont : ContinuousOn (fun p : ℝ × Point n => Ψ p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    AEStronglyMeasurable (fun p : ℝ × Point n => Ψ p.1 p.2)
      ((volume.restrict I).prod (volume : Measure (Point n))) := by
  have hsubprod : I ×ˢ (Set.univ : Set (Point n)) ⊆ Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)) :=
    Set.prod_mono hsub (subset_refl _)
  have hms : MeasurableSet (I ×ˢ (Set.univ : Set (Point n))) := hI.prod MeasurableSet.univ
  have haesm := (hcont.mono hsubprod).aestronglyMeasurable
    (μ := (volume : Measure ℝ).prod (volume : Measure (Point n))) hms
  rwa [← Measure.prod_restrict, Measure.restrict_univ] at haesm

/-! ###############################################################################
    ### THE REUSABLE CORE — s-slice product measurability from the two joint continuities.
    ############################################################################### -/

/-- **★★★ `sliceMeas_of_jointCont` — THE REUSABLE CORE.**  From joint continuity of the first
    factor `Φ` and the Levi factor `Ψ` on the strip `Ioc 0 T ×ˢ univ`, plus the shift `MapsTo`
    datum and `I ⊆ Ioc 0 T`, the s-slice map `s ↦ ∫ z, Φ (u−s) z · Ψ s z` is
    `AEStronglyMeasurable` w.r.t. `volume.restrict I`.  Both factors' joint `(s,z)` measurability
    (Engine A shifted, Engine B unshifted) are `.mul`-joined and integrated out by the Fubini
    engine `InnerMeasFubini.innerIntegral_aesm`.  NOT `a₁ = R/6`. -/
theorem sliceMeas_of_jointCont (Φ Ψ : ℝ → Point n → ℝ) (T u : ℝ) (I : Set ℝ)
    (hI : MeasurableSet I)
    (hmaps : ∀ s ∈ I, (0 : ℝ) < u - s ∧ u - s ≤ T)
    (hsub : I ⊆ Set.Ioc 0 T)
    (hΦcont : ContinuousOn (fun p : ℝ × Point n => Φ p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hΨcont : ContinuousOn (fun p : ℝ × Point n => Ψ p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    AEStronglyMeasurable (fun s => ∫ z, Φ (u - s) z * Ψ s z)
      ((volume : Measure ℝ).restrict I) := by
  have hΦ := shiftFactor_jointAESM Φ T u I hI hmaps hΦcont
  have hΨ := factor_jointAESM_of_contOn Ψ T I hI hsub hΨcont
  exact innerIntegral_aesm
    (fun p : ℝ × Point n => Φ (u - p.1) p.2 * Ψ p.1 p.2) (hΦ.mul hΨ)

/-! ###############################################################################
    ### THE FOUR CONCRETE CENSUS FACTS.
    ############################################################################### -/

/-- **★★ `hmeasLo_slice` — THE `hmeasLo` CENSUS FACT.**  s-slice ae-strong-measurability of the
    `heatOp · leviSeries` pairing on the `Lo` window `uIoc 0 (u − εₘ)`.  On this window the shift
    `τ = u − s ∈ [εₘ, u) ⊆ (0,T]`, so the `sliceMeas_of_jointCont` core applies directly.
    Honest carries: {`hUT`, `hεU`, `hHeatCont`, `hBcont`}.  NOT `a₁ = R/6`. -/
theorem hmeasLo_slice (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hHeatCont : ContinuousOn
      (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 0 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m u hu
  have hεpos := epsSeq_pos m
  have hεu : epsSeq m ≤ u := hεU m u hu
  have huT : u ≤ T := hUT u hu
  have hIeq : Set.uIoc 0 (u - epsSeq m) = Set.Ioc 0 (u - epsSeq m) :=
    Set.uIoc_of_le (by linarith)
  rw [hIeq]
  have hmaps : ∀ s ∈ Set.Ioc (0 : ℝ) (u - epsSeq m), (0 : ℝ) < u - s ∧ u - s ≤ T := by
    intro s hs
    exact ⟨by linarith [hs.2, hεpos], by linarith [hs.1, huT]⟩
  have hsub : Set.Ioc (0 : ℝ) (u - epsSeq m) ⊆ Set.Ioc 0 T :=
    Set.Ioc_subset_Ioc_right (by linarith)
  exact sliceMeas_of_jointCont
    (fun τ z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z)
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    T u (Set.Ioc 0 (u - epsSeq m)) measurableSet_Ioc hmaps hsub hHeatCont hBcont

/-- **★★ `hmeasHi_slice` — THE `hmeasHi` CENSUS FACT.**  s-slice ae-strong-measurability of the
    `heatOp · leviSeries` pairing on the `Hi` window `uIoc (u − εₘ) u`.  The shift `τ = u − s`
    hits `0` at the single null endpoint `s = u`; we prove the fact on the OPEN window
    `Ioo (u−εₘ) u` (where `τ ∈ (0, εₘ) ⊆ (0,T]`) and transfer by `restrict_congr_set`.
    Honest carries: {`hUT`, `hεU`, `hHeatCont`, `hBcont`}.  NOT `a₁ = R/6`. -/
theorem hmeasHi_slice (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hHeatCont : ContinuousOn
      (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 0 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)) := by
  intro m u hu
  have hεpos := epsSeq_pos m
  have hεu : epsSeq m ≤ u := hεU m u hu
  have huT : u ≤ T := hUT u hu
  have hmaps : ∀ s ∈ Set.Ioo (u - epsSeq m) u, (0 : ℝ) < u - s ∧ u - s ≤ T := by
    intro s hs
    exact ⟨by linarith [hs.2], by linarith [hs.1, hεu, huT]⟩
  have hsub : Set.Ioo (u - epsSeq m) u ⊆ Set.Ioc 0 T := by
    intro s hs
    exact ⟨by linarith [hs.1, hεu], by linarith [hs.2, huT]⟩
  have key := sliceMeas_of_jointCont
    (fun τ z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z)
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    T u (Set.Ioo (u - epsSeq m) u) measurableSet_Ioo hmaps hsub hHeatCont hBcont
  have hmeq : (volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)
      = (volume : Measure ℝ).restrict (Set.Ioo (u - epsSeq m) u) := by
    rw [Set.uIoc_of_le (by linarith : u - epsSeq m ≤ u)]
    exact (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  rw [hmeq]
  exact key

/-- **★★ `hmeas2Lo_slice` — THE `hmeas2Lo` CENSUS FACT.**  s-slice ae-strong-measurability of the
    `witnessSecondXDeriv · leviSeries` pairing on the `Lo` window `uIoc 0 (u − εₘ)`, per `i`.
    Honest carries: {`hUT`, `hεU`, `hSecCont`, `hBcont`}.  NOT `a₁ = R/6`. -/
theorem hmeas2Lo_slice (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m i u hu
  have hεpos := epsSeq_pos m
  have hεu : epsSeq m ≤ u := hεU m u hu
  have huT : u ≤ T := hUT u hu
  have hIeq : Set.uIoc 0 (u - epsSeq m) = Set.Ioc 0 (u - epsSeq m) :=
    Set.uIoc_of_le (by linarith)
  rw [hIeq]
  have hmaps : ∀ s ∈ Set.Ioc (0 : ℝ) (u - epsSeq m), (0 : ℝ) < u - s ∧ u - s ≤ T := by
    intro s hs
    exact ⟨by linarith [hs.2, hεpos], by linarith [hs.1, huT]⟩
  have hsub : Set.Ioc (0 : ℝ) (u - epsSeq m) ⊆ Set.Ioc 0 T :=
    Set.Ioc_subset_Ioc_right (by linarith)
  exact sliceMeas_of_jointCont
    (fun τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    T u (Set.Ioc 0 (u - epsSeq m)) measurableSet_Ioc hmaps hsub (hSecCont i) hBcont

/-- **★★ `hmeas2Hi_slice` — THE `hmeas2Hi` CENSUS FACT.**  s-slice ae-strong-measurability of the
    `witnessSecondXDeriv · leviSeries` pairing on the `Hi` window `uIoc (u − εₘ) u`, per `i`.
    Same null-endpoint transfer (`Ioo → Ioc`) as `hmeasHi_slice`.
    Honest carries: {`hUT`, `hεU`, `hSecCont`, `hBcont`}.  NOT `a₁ = R/6`. -/
theorem hmeas2Hi_slice (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)) := by
  intro m i u hu
  have hεpos := epsSeq_pos m
  have hεu : epsSeq m ≤ u := hεU m u hu
  have huT : u ≤ T := hUT u hu
  have hmaps : ∀ s ∈ Set.Ioo (u - epsSeq m) u, (0 : ℝ) < u - s ∧ u - s ≤ T := by
    intro s hs
    exact ⟨by linarith [hs.2], by linarith [hs.1, hεu, huT]⟩
  have hsub : Set.Ioo (u - epsSeq m) u ⊆ Set.Ioc 0 T := by
    intro s hs
    exact ⟨by linarith [hs.1, hεu], by linarith [hs.2, huT]⟩
  have key := sliceMeas_of_jointCont
    (fun τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    T u (Set.Ioo (u - epsSeq m) u) measurableSet_Ioo hmaps hsub (hSecCont i) hBcont
  have hmeq : (volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)
      = (volume : Measure ℝ).restrict (Set.Ioo (u - epsSeq m) u) := by
    rw [Set.uIoc_of_le (by linarith : u - epsSeq m ≤ u)]
    exact (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  rw [hmeq]
  exact key

/-! ###############################################################################
    ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound).
    ############################################################################### -/

#check @shiftFactor_jointAESM
#check @factor_jointAESM_of_contOn
#check @sliceMeas_of_jointCont
#check @hmeasLo_slice
#check @hmeasHi_slice
#check @hmeas2Lo_slice
#check @hmeas2Hi_slice

#print axioms shiftFactor_jointAESM
#print axioms factor_jointAESM_of_contOn
#print axioms sliceMeas_of_jointCont
#print axioms hmeasLo_slice
#print axioms hmeasHi_slice
#print axioms hmeas2Lo_slice
#print axioms hmeas2Hi_slice

end QIQTH.SliceMeasurability
