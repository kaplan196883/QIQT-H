/-
  HCConvTractableCarriesClosed — Step 1 of the hCConv carry-audit (external gpt-5.6-sol sequencing):
  BANK the two TRACTABLE facade carries of `CConvV2Facade.hCConvSlot_AT_GATE_v2`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  It does NOT close `hCConv`.  No `sorry`, no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE AUDIT VERDICT (this session).  The live facade `hCConvSlot_AT_GATE_v2` carries, on the spatial
  `C²` convolution slot, the census
      `{hlin, hbulkderiv, hbulk_tendsto, hsliver, hcont}`   (+ the neighbourhood / data fields).
  Of these, TWO are already essentially closed by BANKED engines and are eliminated here:

    • `hbulk_tendsto` — the BULK pointwise convergence `fbulkInt … m x → ∫₀ᵗ ∫z witnessFieldDeriv·Levi`
      as `m → ∞`.  BANKED: `HD1Concrete.hbulk_tendsto_concrete` (= `HD1ConcreteWiring.
      bulk_tendsto_of_primitive` ∘ `MovingFBoundaryLim.tendsto_comp_epsSeq`, Mathlib endpoint
      primitive-continuity), needing ONLY the base interval-integrability `hGint` of the `s`-profile
      `s ↦ ∫z witnessFieldDeriv … i (t−s) x z · leviSeries … s z 0` — a per-slice, non-geometric,
      universally-carried analytic fact.  Also internalised alongside it: the `hb` vanishing sliver
      rate (`HD1Concrete.hb_concrete`) and the whole `{sSet, hsOpen, hsnhds}` neighbourhood block
      (`sSet := Set.univ`).

    • `hbulkderiv` — the BULK order-2 differentiation `HasFDerivAt (fbulkInt … i m) (fderivBulk i m x) x`.
      BANKED engine: `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` (= the J4-197 double-integral
      Leibniz engine `EboundWiringHD1.hasFDerivAt_doubleIntegral_of_dominated` at the concrete kernel
      pair `witnessFieldDeriv·Levi` / `kPrime`).  In `hCConvSlot_bulkderivClosed` the abstract data
      fields `fderivBulk`/`gderiv` are INSTANTIATED at the concrete `FderivBulkConcrete.fderivBulkInt`/
      `gderivInt`, and `hbulkderiv` is DISCHARGED per slice from the engine's own per-slice
      integrability / measurability / domination / differentiability census — genuine satisfiable,
      non-chart-entangled analytic inputs (the per-slice first-order `hd` differentiability is a
      per-point, NOT joint-second-order, fact).

  ## WHAT LANDS (ns `QIQTH.HCConvTractableCarriesClosed`).

    • `hCConvSlot_bulkTendstoClosed` — ★★  the EXACT capstone `C²` antecedent
        `ContDiffAt ℝ 2 (fun p ↦ heatConv (vanVleck…) (leviSeries…) t p 0) 0`,
      assembled from the facade L1 bridge `CConvV2Facade.hfam_v2` + the `hD1` slot fired by
      `HD1Concrete.hD1_concrete` (which discharges `hbulk_tendsto`/`hb`/`sSet` internally) via
      `SpatialC2.hCConv_reduction`.  Relative to `hCConvSlot_AT_GATE_v2`, the carries
      `hbulk_tendsto`, `hb`, `sSet`, `hsOpen`, `hsnhds` are GONE; in their place the per-slice
      interval-integrability `hGint` and the (data) sliver constants `C₀ C₁ C₂` appear.  Remaining
      open census: `{hlin, hbulkderiv, hsliver, hcont}` + `hGint`.

    • `hCConvSlot_bulkderivClosed` — ★★★  additionally INSTANTIATES `fderivBulk := fderivBulkInt`,
      `gderiv := gderivInt` (concrete), and DISCHARGES `hbulkderiv` from the banked
      `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` engine, exposing its per-slice census.  Remaining
      open census: `{hlin, hsliver, hcont}` (now stated of the CONCRETE `fderivBulkInt`/`gderivInt`,
      so the sliver identity `FderivBulkConcrete.gderiv_sub_fderivBulk_eq_sliver` connects them to the
      geometric interface) + `hGint` + the engine's per-slice `bulkCensus` (integrability /
      measurability / domination / first-order differentiability — none the geometric frontier).

  Every hypothesis is satisfiable, non-vacuous, and strictly lower-level than the `C²` conclusion.
  NONE equals `a₁ = R/6`.  NOT `a₁ = R/6`; `hCConv` NOT closed.
-/
import Mathlib
import QIQTH.CConvV2Facade
import QIQTH.HD1Concrete
import QIQTH.FderivBulkConcrete

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.HeatDuhamel QIQTH.CConvFacade
open QIQTH.TrueHeatKernel QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade
open scoped Topology BigOperators Interval ContDiff

namespace QIQTH.HCConvTractableCarriesClosed

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### Step 1a — `hbulk_tendsto` (+ `hb`, `sSet`) ELIMINATED at the facade `C²` level.
    ############################################################################### -/

/-- **★★ `hCConvSlot_bulkTendstoClosed`.**  The EXACT `hCConv` capstone antecedent
      `ContDiffAt ℝ 2 (fun p ↦ heatConv (vanVleck…) (leviSeries…) t p 0) 0`,
    with the facade carries `hbulk_tendsto`, `hb`, and the neighbourhood block `{sSet, hsOpen, hsnhds}`
    ELIMINATED: the `hD1` slot is fired by `HD1Concrete.hD1_concrete`, which discharges those members
    internally (`sSet := Set.univ`; `hbulk_tendsto` via `bulk_tendsto_of_primitive` on the per-slice
    integrability `hGint`; `hb` via `sliver_bound_tendsto_zero`), and the `C²` lift reuses the facade
    L1 bridge `CConvV2Facade.hfam_v2` + `SpatialC2.hCConv_reduction`.  Remaining open census:
    `{hlin, hbulkderiv, hsliver, hcont}` + the per-slice `hGint` (and the sliver-rate data `C₀ C₁ C₂`).
    NOT `a₁ = R/6`. -/
theorem hCConvSlot_bulkTendstoClosed (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ) (ht : 0 < t)
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (hlin : ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t
          (Function.update x i w) 0)
        ((Dmap g gi hChr hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : Fin n → ℝ)
    (hGint : ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 t)
    (hbulkderiv : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b t i m)
          (fderivBulk i m x) x)
    (hsliver : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk i m x) (gderiv i x)
          ≤ (C₀ i + C₁ i) * (2 * Real.sqrt (epsSeq m)) + C₂ i * epsSeq m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) (Set.univ : Set (Point n))) :
    ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
        (0 : Point n) := by
  -- (L2) the `C¹` regularity of the representative, from the concrete `hD1` assembly (which
  -- discharges `hbulk_tendsto`, `hb`, and the `sSet` neighbourhood block internally).
  have hD1 : ContDiffAt ℝ 1 (Dmap g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t) (0 : Point n) :=
    QIQTH.HD1Concrete.hD1_concrete g gi hChr hK S a b t ht fderivBulk gderiv C₀ C₁ C₂
      hGint hbulkderiv hsliver hcont
  -- (L1) the `∃`-`HasFDerivAt` family, from the linewise family + the `hD1`-bridge.
  have hfam := hfam_v2 g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t
    u hu_open hu0 hlin hD1
  -- (L1 + L2) lift to `C²` via `2 = 1 + 1`.
  exact hCConv_reduction (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t
    (Dmap g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t)
    hfam hD1

/-! ###############################################################################
    ### Step 1b — `hbulkderiv` ELIMINATED via the concrete Leibniz engine; data made concrete.
    ############################################################################### -/

/-- **★★★ `hCConvSlot_bulkderivClosed`.**  The EXACT `hCConv` capstone antecedent, with BOTH tractable
    facade carries eliminated: on top of `hCConvSlot_bulkTendstoClosed` (which kills `hbulk_tendsto`,
    `hb`, `sSet`), this INSTANTIATES the abstract data fields at the concrete
    `FderivBulkConcrete.fderivBulkInt`/`gderivInt` and DISCHARGES `hbulkderiv` per slice from the banked
    double-integral Leibniz engine `FderivBulkConcrete.fderivBulkInt_hasFDerivAt` (J4-197/J4-778).  The
    engine's own per-slice census — integrability (`hKint`), measurability (`hKmeas`/`hK'meas`/`hGmeas`/
    `hG'meas`), domination (`hK'bound`/`hboundz_int`/`hG'bound`), the endpoint integrability (`hGint'` on
    `0..(t−εₘ)`) and the PER-POINT first-order differentiability (`hd`) — is exposed as the two grouped
    carries `bulkCensusSlice` (the `x`-uniform members) and `bulkCensusAtx` (the base-point members).
    NONE is the joint-second-order geometric frontier.

    Remaining open census: `{hlin, hsliver, hcont}` — now stated of the CONCRETE `fderivBulkInt`/
    `gderivInt`, so `FderivBulkConcrete.gderiv_sub_fderivBulk_eq_sliver` makes `hsliver` a bound on the
    ε-window integral that the geometric sliver interface controls — plus the base integrability
    `hGintFull` (for `hbulk_tendsto`) and the engine's per-slice `bulkCensus*`.  NOT `a₁ = R/6`. -/
theorem hCConvSlot_bulkderivClosed (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ) (ht : 0 < t)
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (hlin : ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t
          (Function.update x i w) 0)
        ((Dmap g gi hChr hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (C₀ C₁ C₂ : Fin n → ℝ)
    (Cst : Fin n → ℕ → ℝ) (boundz : Fin n → ℕ → ℝ → Point n → ℝ)
    (hGintFull : ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 t)
    (bulkCensusSlice : ∀ (i : Fin n) (m : ℕ),
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ x ∈ (Set.univ : Set (Point n)), Integrable
              (fun z => witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ x ∈ (Set.univ : Set (Point n)), AEStronglyMeasurable
              (fun z => witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ x ∈ (Set.univ : Set (Point n)), AEStronglyMeasurable
              (fun z => QIQTH.FderivBulkConcrete.kPrime g gi hChr hK S a b i t s x z) volume)
        ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ᵐ z ∂volume, ∀ x ∈ (Set.univ : Set (Point n)),
              ‖QIQTH.FderivBulkConcrete.kPrime g gi hChr hK S a b i t s x z‖ ≤ boundz i m s z)
        ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → Integrable (boundz i m s) volume)
        ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ᵐ z ∂volume,
            ∀ x ∈ (Set.univ : Set (Point n)),
              DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hChr hK S a b i (t - s) y z) x)
        ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ x ∈ (Set.univ : Set (Point n)),
              ‖∫ z, QIQTH.FderivBulkConcrete.kPrime g gi hChr hK S a b i t s x z‖
                ≤ Cst i m * (t - s)⁻¹))
    (bulkCensusAtx : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        (∀ᶠ y in 𝓝 x, AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (t - epsSeq m))))
        ∧ IntervalIntegrable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume 0 (t - epsSeq m)
        ∧ AEStronglyMeasurable
            (fun s => ∫ z, QIQTH.FderivBulkConcrete.kPrime g gi hChr hK S a b i t s x z)
            (volume.restrict (Set.uIoc 0 (t - epsSeq m))))
    (hsliver : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (QIQTH.FderivBulkConcrete.fderivBulkInt g gi hChr hK S a b t i m x)
            (QIQTH.FderivBulkConcrete.gderivInt g gi hChr hK S a b t i x)
          ≤ (C₀ i + C₁ i) * (2 * Real.sqrt (epsSeq m)) + C₂ i * epsSeq m)
    (hcont : ∀ i : Fin n,
        ContinuousOn (QIQTH.FderivBulkConcrete.gderivInt g gi hChr hK S a b t i)
          (Set.univ : Set (Point n))) :
    ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
        (0 : Point n) := by
  refine hCConvSlot_bulkTendstoClosed g gi hChr hK S a b t ht u hu_open hu0 hlin
    (fun i m => QIQTH.FderivBulkConcrete.fderivBulkInt g gi hChr hK S a b t i m)
    (fun i => QIQTH.FderivBulkConcrete.gderivInt g gi hChr hK S a b t i)
    C₀ C₁ C₂ hGintFull ?_ hsliver hcont
  -- discharge `hbulkderiv` per slice from the banked Leibniz engine.
  intro i m x hx
  obtain ⟨hKint, hKmeas, hK'meas, hK'bound, hboundz_int, hd, hG'bound⟩ := bulkCensusSlice i m
  obtain ⟨hGmeas, hGint', hG'meas⟩ := bulkCensusAtx i m x hx
  exact QIQTH.FderivBulkConcrete.fderivBulkInt_hasFDerivAt g gi hChr hK S a b t ht i m x
    (Cst i m) (boundz i m)
    hKint hKmeas hK'meas hK'bound hboundz_int hd hGmeas hGint' hG'meas hG'bound

end QIQTH.HCConvTractableCarriesClosed

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HCConvTractableCarriesClosed
#print axioms hCConvSlot_bulkTendstoClosed
#print axioms hCConvSlot_bulkderivClosed
end AxiomChecks
