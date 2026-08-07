/-
  W2Package — J4-396 (the D pile): the W2 differentiation-under-∫ package.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves
  NOTHING about `R/6`.  `a₁ = R/6` remains CONDITIONAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  Every theorem here is a re-threading of BANKED, satisfiable measurability
  data through the banked Fubini inner-integral engine `InnerMeasFubini.innerIntegral_aesm`.  NONE
  proves `a₁ = R/6`.  Each carried hypothesis is genuine, satisfiable, non-vacuous, and never the
  conclusion.  No `sorry` (header prose excepted), no `:= True`, no new axioms, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT — THE DEMAND (the census (ii) block).

  The census (ii) block of `GlobalRawBoundFacade.hDaLimLU_from_labelled` (mirrored in
  `CensusGeometryThread`) supplies EIGHT differentiation-under-∫ fields at
      `W := vanVleckGatedWitness g gi hChr hK S a b`,
      `F := leviSeries (heatOp g gi W)`,
  that are CONSUMED, verbatim, by the aggregation point
      `SecondOrderInterchangeConcrete.witness_MemInterchange`
  (the ENGINE FIRING, whose 8 binders `hQ1`/`hFmeas`/`hFint`/`hF'meas`/`bound`/`hbdd`/`hbound`/`hdiff`
  ARE the census (ii) fields, producing the `DaLimLUWallRecon.MemInterchange` member).

  ── THE DEMAND-vs-SUPPLY MAP (Phase 1 verdict).

    field      demand shape                                supplier / route
    ─────      ───────────────────────────────────────     ─────────────────────────────────────
    hQ1        `pd (heatConvFrozen …) i y = ∫∫ dH·F`        `SecondOrderInterchange.
               (first-order interchange on `V ∋ 0`)         pd_heatConvFrozen_interchange` at the
                                                            witness — MAPPED CARRY (heavier; the
                                                            first-order diff-under-∫ representation).
    hFmeas     `s ↦ ∫z dH i (u−s)(update 0 i w) z·F`        ★ DISCHARGED HERE (`w2_hFmeas`) —
               s-ae-measurability, ∀ w                       `innerIntegral_aesm` on the joint carries
                                                            `hWFDjoint`·`hLeviJoint`.  Verbatim mirror
                                                            of `InnerMeasFubini.hFmeas_concrete` at the
                                                            FIRST field-derivative kernel.
    hFint      `s ↦ ∫z dH i (u−s) 0 z·F`                     `ConvCarriesDischarge.
               interval-integrability                        heatConvInner_intervalIntegrable_
                                                            gaussianDom` — MAPPED CARRY (its window is
                                                            `0..u`, not the truncated `0..(u−εₘ)`, and
                                                            it needs the `(A₀+A₁τ)` Gaussian shape, not
                                                            the first-derivative `τ⁻¹` bound; adaptation
                                                            deferred).
    hF'meas    `s ↦ ∫z dHH i (u−s) 0 z·F`                    ★ DISCHARGED HERE (`w2_hF'meas`) —
               s-ae-measurability                            `innerIntegral_aesm` on the joint carries
                                                            `hWFD2joint`·`hLeviJoint`.  Verbatim mirror
                                                            of `InnerMeasFubini.hF'meas_concrete` at the
                                                            SECOND field-derivative kernel.
    bound      `ℕ → Fin n → ℝ → ℝ`                           SUPPLIED INTERNALLY by the W2 majorant
    hbdd       `IntervalIntegrable (bound m i) 0 (u−εₘ)`     (`witness_MemInterchange_majorant`:
    hbound     `‖∫z dHH·F‖ ≤ bound m i s` on the window       `bound := secondBoundConst n Csec C_L α m`,
               (∀ w ∈ snb)                                    `hbdd` = `secondBoundConst_
                                                            intervalIntegrable`, `hbound` =
                                                            `witness_secondOrder_hbound_slot` from the
                                                            on-gate shifted domination `hOn` + Levi
                                                            bound `hF`).  NOT re-exposed here.
    hdiff      `HasDerivAt (w ↦ ∫z dH i(u−s)(update 0 i w))  `SecondOrderInterchange.
               (∫z dHH i(u−s)(update 0 i w)) w`              innerZ_line_hasDerivAt` (per `s`-slice) —
               (∀ᵐ s, ∀ w ∈ snb)                             MAPPED CARRY (the inner-slice `√ε`-route
                                                            HasDerivAt engine; the SECOND-order analogue
                                                            of `CConvV2DerivRep.hlin_linewise`'s
                                                            `hdiff`, one derivative order up).

  ── PER-RUNG-FAMILY IDENTITY VERDICT.  The frozen-side W2 carries beneath `htermBoxEvery`
     (`IterEEngineWiring`'s per-rung `hmeas`/`hcont` CONVOLUTION carries, J4-395) are the SAME
     Fubini inner-integral family: they too are `s ↦ ∫z (kernel)·(source)` slots discharged by
     `innerIntegral_aesm` on a JOINT `(s,z)`-measurability supplied by `.mul` of a witness/kernel
     leg and a source leg.  The measurability ENGINE (`innerIntegral_aesm` + `.mul` + a gated
     joint-measurability lever) is COMMON; only the two joint legs differ (frozen-side: the
     rung-`k` `iterE` source; census (ii): the `leviSeries` source and the field-derivative kernel).
     One measurability package (this file's `w2_hFmeas`/`w2_hF'meas` pattern) serves BOTH once fed
     the appropriate joint legs — the joint carries `hWFDjoint`/`hWFD2joint`/`hLeviJoint` are the
     per-family plug points.

  ── BANKED SUPPLIERS CONSULTED.
    • `InnerMeasFubini.innerIntegral_aesm` — the Fubini inner-integral engine
      (`AEStronglyMeasurable.integral_prod_right'`): a joint `(s,z)`-measurability on `μ.prod volume`
      integrates out to the `s`-slice measurability.  THE engine every F2 slot runs on.
    • `InnerMeasFubini.hFmeas_concrete` / `.hF'meas_concrete` — the PRECEDENTS: the very same
      `innerIntegral_aesm ((witness leg).mul (levi leg))` pattern, at the WITNESS VALUE (0-th) and
      the `∂_τ`-witness kernels.  This file lifts that pattern one field-derivative order up.
    • `FixedGateSourceProviders.leviSource_joint_aesm` — the joint `(s,z)`-measurability of the
      `leviSeries` factor from a `LeviSeriesLocalData` package (satisfies `hLeviJoint`).
    • `SecondOrderInterchangeConcrete.witness_MemInterchange{,_majorant}` — the AGGREGATION point the
      8 fields feed; the majorant already discharges the `bound`/`hbdd`/`hbound` triple.

  ── HONEST CARRIES (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hWFDjoint`  — joint `(s,z)`-ae-measurability of the FIRST field-derivative kernel
      `(s,z) ↦ witnessFieldDeriv … i (u−s) (update 0 i w) z` on the truncated product measure.  The
      spatial-derivative analogue of `InnerMeasFubini.hWitDeriv` (the `∂_τ`-witness joint carry);
      satisfiable from the gate/Gaussian/amplitude structure measured jointly.
    • `hWFD2joint` — joint `(s,z)`-ae-measurability of the SECOND field-derivative kernel
      `(s,z) ↦ witnessFieldDeriv2 … i (u−s) 0 z`, same route one order up.
    • `hLeviJoint` — joint `(s,z)`-ae-measurability of the `leviSeries` factor on each truncated
      window (satisfiable from `leviSource_joint_aesm`, restricted to the sub-window).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.EngineInstantiation
import QIQTH.InnerMeasFubini

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open scoped Interval Topology BigOperators

namespace QIQTH.W2Package

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### FIELD hFmeas — the FIRST field-derivative-kernel `s`-measurability.
    ############################################################################### -/

/-- **★★ `w2_hFmeas` — THE CENSUS (ii) `hFmeas` FIELD, DISCHARGED.**  The `w`-parametrized
    `s`-ae-strong-measurability of the inner space-time pairing at the FIRST field-derivative kernel,
    on the truncated window `(0, u − εₘ]`:
      `s ↦ ∫ z, witnessFieldDeriv … i (u−s) (update 0 i w) z · leviSeries (heatOp g gi W) s z 0`.
    Runs the banked Fubini engine `InnerMeasFubini.innerIntegral_aesm` on the product of the two
    carried joint `(s,z)`-measurabilities: the FIRST field-derivative kernel leg `hWFDjoint` and the
    `leviSeries` source leg `hLeviJoint`, joined by `.mul`.  VERBATIM the pattern of
    `InnerMeasFubini.hFmeas_concrete`, lifted from the witness value to its first field-derivative.
    Honest carries: {`hWFDjoint`, `hLeviJoint`}.  NOT `a₁ = R/6`. -/
theorem w2_hFmeas (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hWFDjoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hChr hK S a b i (u - p.1) (Function.update (0 : Point n) i w) p.2)
      ((volume.restrict (Set.uIoc 0 (u - epsSeq m))).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
          (Function.update (0 : Point n) i w) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m i u hu w
  exact QIQTH.InnerMeasFubini.innerIntegral_aesm
    (fun p : ℝ × Point n =>
      witnessFieldDeriv g gi hChr hK S a b i (u - p.1) (Function.update (0 : Point n) i w) p.2
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
    ((hWFDjoint m i u hu w).mul (hLeviJoint (u - epsSeq m)))

/-! ###############################################################################
    ### FIELD hF'meas — the SECOND field-derivative-kernel `s`-measurability.
    ############################################################################### -/

/-- **★★ `w2_hF'meas` — THE CENSUS (ii) `hF'meas` FIELD, DISCHARGED.**  The `s`-ae-strong-measurability
    of the inner space-time pairing at the SECOND field-derivative kernel (field point `0`), on the
    truncated window `(0, u − εₘ]`:
      `s ↦ ∫ z, witnessFieldDeriv2 … i (u−s) 0 z · leviSeries (heatOp g gi W) s z 0`.
    Runs `InnerMeasFubini.innerIntegral_aesm` on the product of the two carried joint
    `(s,z)`-measurabilities — the SECOND field-derivative kernel leg `hWFD2joint` and the `leviSeries`
    source leg `hLeviJoint` — joined by `.mul`.  VERBATIM the pattern of
    `InnerMeasFubini.hF'meas_concrete`, at the SECOND field-derivative kernel.  Honest carries:
    {`hWFD2joint`, `hLeviJoint`}.  NOT `a₁ = R/6`. -/
theorem w2_hF'meas (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hWFD2joint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        witnessFieldDeriv2 g gi hChr hK S a b i (u - p.1) (0 : Point n) p.2)
      ((volume.restrict (Set.uIoc 0 (u - epsSeq m))).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m i u hu
  exact QIQTH.InnerMeasFubini.innerIntegral_aesm
    (fun p : ℝ × Point n =>
      witnessFieldDeriv2 g gi hChr hK S a b i (u - p.1) (0 : Point n) p.2
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
    ((hWFD2joint m i u hu).mul (hLeviJoint (u - epsSeq m)))

/-! ###############################################################################
    ### THE W2 MEASURABILITY PAIR — the two discharged fields bundled.
    ############################################################################### -/

/-- **★★★ `w2_measPack` — THE TWO DISCHARGED W2 MEASURABILITY FIELDS, BUNDLED.**  Packages exactly the
    two census (ii) fields this brick discharges — `hFmeas` (first field-derivative kernel) and
    `hF'meas` (second field-derivative kernel) — from the three honest joint `(s,z)`-measurability
    carries {`hWFDjoint`, `hWFD2joint`, `hLeviJoint`}.  The remaining census (ii) fields are supplied
    elsewhere: `bound`/`hbdd`/`hbound` INTERNALLY by the W2 majorant
    (`witness_MemInterchange_majorant`, from `hOn` + `hF`), and `hQ1`/`hFint`/`hdiff` as the mapped
    interchange / interval-integrability / inner-slice-HasDerivAt carries.  Does NOT re-expose those
    fields.  Each input carry is satisfiable, non-vacuous, never the conclusion.  NOT `a₁ = R/6`. -/
theorem w2_measPack (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hWFDjoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hChr hK S a b i (u - p.1) (Function.update (0 : Point n) i w) p.2)
      ((volume.restrict (Set.uIoc 0 (u - epsSeq m))).prod (volume : Measure (Point n))))
    (hWFD2joint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        witnessFieldDeriv2 g gi hChr hK S a b i (u - p.1) (0 : Point n) p.2)
      ((volume.restrict (Set.uIoc 0 (u - epsSeq m))).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n)))) :
    -- (hFmeas) the first field-derivative-kernel `s`-measurability
    (∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
          (Function.update (0 : Point n) i w) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    -- (hF'meas) the second field-derivative-kernel `s`-measurability
    ∧ (∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) :=
  ⟨w2_hFmeas g gi hChr hK S a b U hWFDjoint hLeviJoint,
   w2_hF'meas g gi hChr hK S a b U hWFD2joint hLeviJoint⟩

end QIQTH.W2Package

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.W2Package
#print axioms w2_hFmeas
#print axioms w2_hF'meas
#print axioms w2_measPack
end AxiomChecks
