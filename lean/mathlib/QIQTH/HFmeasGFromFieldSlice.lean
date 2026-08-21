/-
  HFmeasGFromFieldSlice — REDUCE the F-slice product-measurability carrier `hFmeasG` of J4-970/971/972's
  FTC-in-`c` bridge (`censusFTC_bridge` / `hfar_concrete_of_engine` / `hRint_of_hEnv`) from the ENTANGLED
  product `witness(u'−s) 0 z · F s z 0` to the PURE, honest F-side slice measurability
      `hFslice : ∀ s, AEStronglyMeasurable (fun z ↦ F s z 0) volume`,
  by DISCHARGING the WITNESS factor's slice measurability from the banked witness-side infrastructure
  (`vanVleckGatedWitness_slice_aestronglyMeasurable`, J4-… WitnessMeasDeriv) via `AEStronglyMeasurable.mul`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE / carrier-reduction brick.  No `sorry`, no new axioms, no `:= True`, no vacuous
  / unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## WHAT J4-970/971/972 LEFT.  After J4-972 the FTC-in-`c` bridge's three carriers `{hFmeasG, hEnv,
  hRint}` reduced to `{hFmeasG, hEnv}` (`hRint` discharged from `hEnv`).  The remaining
      `hFmeasG : ∀ s u', AEStronglyMeasurable (fun z ↦ vanVleckGatedWitness … (u'−s) 0 z · F s z 0) volume`
  is a PRODUCT measurability entangling the WITNESS factor and the free field factor `F`.  Sol's J4-971
  audit flagged `hFmeasG` as a genuine F-SIDE regularity carry (F is unconstrained, so witness-side infra
  alone cannot discharge it).  THIS FILE makes that precise: it PEELS OFF the witness factor (banked-
  dischargeable) so the ONLY irreducible residue is the pure F-slice measurability `hFslice`.

  ## THE ROUTE (routine, but genuine).  `AEStronglyMeasurable (W · F) = AEStronglyMeasurable W ·
  AEStronglyMeasurable F` (`.mul`).  The witness slice `z ↦ vanVleckGatedWitness … (u'−s) 0 z` is
  `AEStronglyMeasurable` by the BANKED `vanVleckGatedWitness_slice_aestronglyMeasurable` from the witness-
  side carries `{hKm (K measurable), hSm0 (gate preimage at 0 measurable), hIn (order-1 global-cutoff
  parametrix slice z-ae-measurable)}` — exactly the `InnerMeasFubini`/`WitnessMeasDeriv` gate-indicator
  measurability lever, ALREADY established elsewhere in the tower.  The field slice `z ↦ F s z 0` is the
  honest F-side carry `hFslice`.  Their product is `hFmeasG`.

  ## WHAT THIS DOES — AND DOES NOT — DO.  It reduces `hFmeasG` (product) → `{hKm, hSm0, hIn, hFslice}`,
  i.e. peels the witness factor onto the banked witness-side measurability infra, leaving the pure F-slice
  measurability `hFslice` as the ONLY new F-side residue — which then joins the honest F-side data family
  `{hFdom, hmeas, hbase}` (the G3 F-bound family / window measurability) inside `hEnv`.  Because `F` is
  UNCONSTRAINED in the H_far/hCross chain, `hFslice` CANNOT be eliminated (a non-measurable `F` is the
  obstruction) — this is an honest carrier REDUCTION, not a full discharge.  It does NOT discharge `hrate`,
  the G3 F-bound, nor touch the chart-CoV/census scalar inequality (the opaque chart wall inside `hrate`).
  It discharges NONE of `{hballrate, hDuhamel, hDConv, hCConv}` as a top-level τ-carry.  `a₁ = R/6` remains
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WitnessMeasDeriv

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.WitnessMeasDeriv
open scoped Interval Topology BigOperators

namespace QIQTH.HFmeasGFromFieldSlice

variable {n : ℕ}

/-! ###############################################################################
    ### §A — the ABSTRACT product-measurability splitter (pure `AEStronglyMeasurable.mul`).
    ############################################################################### -/

/-- **★ `aesm_mul_of_slices` — the abstract product splitter.**  For any measure space `(α, ν)` and any two
    real-valued `AEStronglyMeasurable` slices `W`, `Fp`, their pointwise product is `AEStronglyMeasurable`.
    Pure `AEStronglyMeasurable.mul`.  NOT `a₁ = R/6`. -/
theorem aesm_mul_of_slices {α : Type*} [MeasurableSpace α] {ν : Measure α} {W Fp : α → ℝ}
    (hW : AEStronglyMeasurable W ν) (hF : AEStronglyMeasurable Fp ν) :
    AEStronglyMeasurable (fun z => W z * Fp z) ν :=
  hW.mul hF

/-! ###############################################################################
    ### §B — THE CONCRETE REDUCTION: `hFmeasG` from banked witness-slice infra + pure F-slice carry.
    ############################################################################### -/

/-- **★★★ `hFmeasG_of_field_slice` — the FTC-bridge product-measurability carrier `hFmeasG` REDUCED to a
    pure F-slice carry.**  For the concrete gated van-Vleck witness `A := vanVleckGatedWitness g gi hC hK S
    cutA cutB` and free field `F`, GIVEN the WITNESS-SIDE measurability carries
      • `hKm` — `MeasurableSet K`,
      • `hSm0` — `MeasurableSet {z | (0 : Point n) ∈ S z}` (gate preimage at field point `0`),
      • `hIn` — the order-1 global-cutoff parametrix slice is `z`-ae-measurable at every time `τ` and
        field point `0` (the banked `InnerMeasFubini`/`WitnessMeasDeriv` inner-measurability datum),
    and the PURE F-SIDE carry
      • `hFslice` — `∀ s, AEStronglyMeasurable (fun z ↦ F s z 0) volume`,
    the product slice-measurability the engine needs holds:
        `∀ s u', AEStronglyMeasurable (fun z ↦ vanVleckGatedWitness … (u'−s) 0 z · F s z 0) volume`.
    Route: the banked `vanVleckGatedWitness_slice_aestronglyMeasurable` discharges the witness factor from
    `{hKm, hSm0, hIn}`; `.mul` with `hFslice` gives the product.  So `hFmeasG` is NO LONGER an entangled
    witness·F carry: its ONLY new residue is the honest F-side slice measurability `hFslice`.  NOT
    `a₁ = R/6`. -/
theorem hFmeasG_of_field_slice
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hIn : ∀ τ : ℝ, AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) cutA cutB
        (uniformInverseChart g gi hC hK) τ (0 : Point n) z)
      (volume : Measure (Point n)))
    (hFslice : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z 0) (volume : Measure (Point n))) :
    ∀ s u' : ℝ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (u' - s) 0 z * F s z 0) volume := by
  intro s u'
  refine aesm_mul_of_slices ?_ (hFslice s)
  exact vanVleckGatedWitness_slice_aestronglyMeasurable g gi hC hK S cutA cutB (u' - s)
    (0 : Point n) hKm hSm0 (hIn (u' - s))

/-! ###############################################################################
    ### §C — NON-VACUITY (TEETH).  The abstract splitter is satisfiable with the product genuinely
    ###       ACTIVE (non-a.e.-zero), NOT a `0 = 0` collapse.
    ############################################################################### -/

/-- **Non-vacuity (TEETH) of `aesm_mul_of_slices`.**  The two slice-measurability hypotheses are jointly
    satisfiable at a GENUINELY non-trivial instance — the one-point (Dirac) measure `ν = Measure.dirac ()`
    with `W := fun _ ↦ 1`, `Fp := fun _ ↦ 1` — with the resulting product `(W · Fp) () = 1 ≠ 0` genuinely
    ACTIVE (the conclusion is a real measurability of a non-a.e.-zero function, NOT `0 = 0`).  Confirms the
    splitter is not vacuously conditioned. -/
theorem aesm_mul_of_slices_hyp_satisfiable :
    ∃ (α : Type) (_ : MeasurableSpace α) (ν : Measure α) (W Fp : α → ℝ),
      AEStronglyMeasurable W ν ∧
      AEStronglyMeasurable Fp ν ∧
      AEStronglyMeasurable (fun z => W z * Fp z) ν ∧
      ∃ a : α, (fun z => W z * Fp z) a ≠ 0 := by
  refine ⟨Unit, inferInstance, Measure.dirac (), (fun _ => 1), (fun _ => 1),
    aestronglyMeasurable_const, aestronglyMeasurable_const, ?_, ?_⟩
  · exact aesm_mul_of_slices aestronglyMeasurable_const aestronglyMeasurable_const
  · exact ⟨(), by norm_num⟩

end QIQTH.HFmeasGFromFieldSlice

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HFmeasGFromFieldSlice
#print axioms aesm_mul_of_slices
#print axioms hFmeasG_of_field_slice
#print axioms aesm_mul_of_slices_hyp_satisfiable
end AxiomChecks
