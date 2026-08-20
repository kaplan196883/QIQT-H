/-
  HmassoneFromGateAnnulusSplit — J4-896: the ABSTRACT-`g` `hmassone` discharge for the LIVE
  order-1 capstone's `hDuhamel`/`hDConv` shared frozen/moving census.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure COMPOSITION brick.  It discharges — for ABSTRACT `g gi S` — the exact `hmassone` binder carried
  by `HDuhamelExportRethread.hbdryLU_CONCRETE` / `hDerivConv_conditional` / `truncatedDuhamelCore_AT_
  GATE_FULL` (and hence by the LIVE capstone's `hDuhamel_live_gate_wired`), reducing it to the
  satisfiable PRE-`ρ` carriers of the banked `GateAnnulusSplit.chartImage_approx_identity_final`.
  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE EXACT SHAPE consumed by the census (character-checked against source).

  The frozen/moving census that feeds both `hDuhamel` (via `hDuhamel_live_gate_wired`, its `hmassone`
  binder, `HDuhamelLiveGateWired.lean:217-218`) and `hDConv` (via `HDerivConvComposition.hbdryLU_
  CONCRETE`, its `hmassone` binder, `HDerivConvComposition.lean:133`) carries, at the concrete witness:
      `hmassone : Tendsto
          (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z)
          atTop (𝓝 1)`.
  This file PROVES that exact proposition — for ABSTRACT `g gi S` — so it plugs into the abstract-`S`
  census binder with NO adapter.

  ## THE ABSTRACT-`g` GENERALIZATION (vs. the curved specialization).

  `CurvedA1HmassoneFinal.curved_hmassone_final_at_gate` (J4-591) already composes
  `GateAnnulusSplit.chartImage_approx_identity_final` (the FIXED-`f` FINAL) at `f ≡ 1` with
  `epsSeq → 𝓝[>]0` to produce this `hmassone` shape — but it is SPECIALIZED to `g := curvedRNCMetric κ`
  / `gi := curvedRNCInv κ`.  The LIVE order-1 capstone is over ABSTRACT `g` (cp765 audit); the curved
  specialization does NOT serve it (and re-instantiating `g := curvedRNCMetric κ` re-enters the cp466
  `hframeK ⟹ K = {0}` vacuity family).  Since `chartImage_approx_identity_final` is ALREADY stated
  generically in the abstract metric `g gi` (with the metric carries `{hg, hgi, hgpos}`, the gauge
  `det g 0 = 1`, and the gate/domination carries as HYPOTHESES), the generalization is immediate: strip
  `curvedRNCMetric κ` to abstract `g gi` + the carried metric facts.  We also DROP the vacuous `∃ ρ`
  wrapper of the curved brick (`ρ` never appears in the `hmassone` body), so the conclusion is EXACTLY
  the census binder shape.

  ## WHAT THIS FILE LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `hmassone_from_gate_annulus_split` — ★★ the ABSTRACT-`g` `hmassone` binder shape, obtained as the
      `f ≡ 1` case of `GateAnnulusSplit.chartImage_approx_identity_final` composed with `epsSeq → 𝓝[>]0`.
      Carried surface = the base geometry/gauge `{hChr, hK, K ∈ 𝓝 0, hg, hgi, hgpos, det g 0 = 1}`
      (ALL present in / derivable from the live capstone), the PRE-`ρ` gate-activation triple
      `{rS, hKball, hSact}`, the witness-slice measurability `hWslice` (= the census member `hWmeas`),
      and the zeroth wide domination `hDom` (= the census member `hWDom`).
    • `constGate_eq_liveGate` — the defeq character-check (`rfl`): `constGate g gi hChr hK c` is
      definitionally the LIVE capstone's chosen gate `fun z => uniformFlowExp … z '' ball 0 c`.
    • `hmassone_at_constGate` — the same discharge instantiated at `S := constGate g gi hChr hK c`,
      i.e. at the LIVE capstone's own gate, demonstrating the direct live-gate wiring.

  ## HONEST RESIDUAL.  This discharges the `hmassone` census binder MODULO the satisfiable PRE-`ρ`
  carriers `{rS, hKball, hSact}` (gate activation near `0`, satisfiable from `K ∈ 𝓝 0` + gate
  reachability), `hWslice` (already carried as `hWmeas`), and `hDom` (already carried as `hWDom`).  The
  metric carries `{hg, hgi, hgpos}` and gauge `det g 0 = 1` are supplied by the capstone's own geometry.
  None of these is the conclusion.  This CLOSES the `hmassone` member of the shared frozen/moving census
  (opaque carried limit ⟹ theorem conditional on satisfiable pre-`ρ` inputs); the OTHER census members
  (RadialNormalCoordinateGauge centre-identity leg, Gaussian dominations, interchange bundles, sliver
  carries) are untouched.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GateAnnulusSplit
import QIQTH.A1R6CoreAtGate

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.A1R6CoreAtGate QIQTH.ExpMap
open scoped Topology

namespace QIQTH.HmassoneFromGateAnnulusSplit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The ABSTRACT-`g` `hmassone` discharge — exact census-binder shape.
    ############################################################################### -/

/-- **★★ J4-896 — `hmassone_from_gate_annulus_split` — the ABSTRACT-`g` `hmassone` binder.**  The EXACT
    `hmassone` proposition carried by the shared frozen/moving census of `hDuhamel`
    (`HDuhamelLiveGateWired.lean:217-218`) and `hDConv` (`HDerivConvComposition.lean:133`), for ABSTRACT
    `g gi S`:
        `Tendsto (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) 0 z) atTop (𝓝 1)`,
    obtained as the `f ≡ 1` special case of the banked FIXED-`f` FINAL
    `GateAnnulusSplit.chartImage_approx_identity_final` (which discharges `hGgate` from the external
    gate-activation triple `{rS, hKball, hSact}` and `hSupp` by the Gaussian-tail annulus split fed by
    the zeroth domination `hDom` + `hWslice`), composed with `epsSeq → 𝓝[>]0`.

    This is the ABSTRACT-`g` generalization of `CurvedA1HmassoneFinal.curved_hmassone_final_at_gate`
    (which is specialized to `g := curvedRNCMetric κ`), obtained by keeping the metric carries
    `{hg, hgi, hgpos}` + gauge `det g 0 = 1` as HYPOTHESES (all supplied by the live capstone's own
    geometry).  The vacuous `∃ ρ` wrapper of the curved brick is DROPPED, so the conclusion is EXACTLY
    the census binder.  ⚠ NOT `a₁ = R/6`. -/
theorem hmassone_from_gate_annulus_split
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1)
    -- gate-activation carries (discharge `hGgate`, PRE-`ρ`):
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z)
    -- witness-slice measurability (= the census member `hWmeas`):
    (hWslice : ∀ τ : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z) volume)
    -- zeroth wide domination (= the census member `hWDom`):
    (lam τ₀ CW : ℝ) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hCW : 0 ≤ CW)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z) :
    Tendsto (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z)
      atTop (𝓝 1) := by
  -- the `f ≡ 1` case of the banked FIXED-`f` FINAL (CoV bundle + measurability + `hbound`/`hlocal`
  -- discharged AND `hGgate`/`hSupp` discharged from the pre-`ρ` gate/domination carries).
  obtain ⟨ρ, hρ, hlim⟩ := QIQTH.GateAnnulusSplit.chartImage_approx_identity_final
    g gi hChr hK h0Kmem hg hgi hgpos S a b ha hab hgdet0
    (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩ continuousAt_const
    rS hrS hKball hSact hWslice
    lam τ₀ CW hlam hτ₀ hCW hDom
  -- `hlim : Tendsto (fun τ => ∫ z, Wit τ 0 z · 1) (𝓝[>]0) (𝓝 1)`.
  -- `epsSeq → 𝓝[>]0` (positive, → 0).
  have heps : Tendsto (epsSeq : ℕ → ℝ) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      epsSeq_tendsto (Filter.Eventually.of_forall (fun m => epsSeq_pos m))
  -- compose and clean up `f 0 = 1`, `Wit · 1 = Wit`, `∘ epsSeq`.
  have hcomp := hlim.comp heps
  simpa using hcomp

/-! ###############################################################################
    ### The defeq character-check + the LIVE-gate instantiation.
    ############################################################################### -/

/-- **Character-check (defeq, `rfl`).**  `constGate g gi hChr hK c` is DEFINITIONALLY the LIVE order-1
    capstone's chosen gate `fun z => uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`
    (`GatedGlobalWitnessN1CapstoneReachAligned`'s `S`, per `HDuhamelLiveGateWired.lean:21`).  This is
    what makes `hmassone_at_constGate` below the discharge at the capstone's OWN gate.  ⚠ NOT
    `a₁ = R/6`. -/
example (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) :
    constGate g gi hChr hK c
      = fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c := rfl

/-- **★ `hmassone_at_constGate` — the `hmassone` discharge at the LIVE capstone's own gate.**  The
    `S := constGate g gi hChr hK c` instantiation of `hmassone_from_gate_annulus_split`, i.e. the exact
    `hmassone` proposition at the LITERAL constant-radius flow-ball gate the LIVE capstone selects
    (defeq to its own `S`, per `constGate_eq_liveGate`).  ⚠ NOT `a₁ = R/6`. -/
theorem hmassone_at_constGate
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b c : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1)
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS,
      (0 : Point n) ∈ constGate g gi hChr hK c z)
    (hWslice : ∀ τ : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z)
        volume)
    (lam τ₀ CW : ℝ) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hCW : 0 ≤ CW)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z|
        ≤ CW * gaussDdim (lam * τ) z) :
    Tendsto (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b
        (epsSeq m) (0 : Point n) z) atTop (𝓝 1) :=
  hmassone_from_gate_annulus_split g gi hChr hK h0Kmem hg hgi hgpos
    (constGate g gi hChr hK c) a b ha hab hgdet0 rS hrS hKball hSact hWslice
    lam τ₀ CW hlam hτ₀ hCW hDom

end QIQTH.HmassoneFromGateAnnulusSplit

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HmassoneFromGateAnnulusSplit
#print axioms hmassone_from_gate_annulus_split
#print axioms hmassone_at_constGate
end AxiomChecks
