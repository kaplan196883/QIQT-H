/-
  CurvedA1HmassoneFinal — J4-591: shedding `hmassone`'s LAST two carriers `hGgate`/`hSupp` via the
  banked gate-support split — the mass-side endgame for the curved a₁ = R/6 capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  J4-590 (`CurvedA1HmassoneBound.curved_hmassone_via_bundle_at_gate`) reduced the
  center-gauge curved capstone's carried base-mass limit `hmassone` to the EnrichedChartBundle W1
  capstone (M1–M4 CoV bundle, chart-image + Layer-C measurability, `hbound`, `hlocal` ALL
  discharged) modulo only TWO carriers, stated on the PRODUCED radius `ρ`:
    • `hGgate` : the witness gate is active on `ball 0 ρ`;
    • `hSupp`  : the witness vanishes off `ball 0 ρ`, τ-uniformly.
  Those two are the awkward ρ-dependent carriers — the caller had to satisfy them for the very `ρ`
  the theorem produces.

  ── ★★ VERDICT (J4-591).  `hGgate`/`hSupp` are ELIMINATED by the banked
     `GateAnnulusSplit.chartImage_approx_identity_final` (the FIXED-`f` FINAL), which internally caps
     the enriched bundle at `min ρA rS`, discharges `hGgate` on the produced ball via
     `hGgate_of_gate_activation` from an EXTERNAL gate-activation triple `{rS, hKball, hSact}`
     (independent of `ρ`), and handles `hSupp` by the Gaussian-tail annulus split
     (`offBall_integral_tendsto_zero`) fed by the zeroth wide domination
     (`WideAmplitudeData.zeroth_domination_global`-shape) `hDom` plus the witness-slice
     measurability `hWslice`.  Composing the `f ≡ 1` case with `epsSeq → 𝓝[>]0` gives the EXACT
     capstone `hmassone`, now with NO `hGgate`/`hSupp` in the conclusion — the ρ-gate carriers are
     GONE.  The replacement carriers `{rS, hKball, hSact, hWslice, hDom}` are PRE-`ρ`, satisfiable
     geometric/analytic facts (NOT the `a₁` conclusion).

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_hmassone_final_at_gate` — ★★ the curved base-mass limit `hmassone` with `hGgate`/`hSupp`
      DISCHARGED.  The EXACT `hmassone` shape carried by the center-gauge curved capstone, obtained as
      the `f ≡ 1` case of `GateAnnulusSplit.chartImage_approx_identity_final` composed with
      `epsSeq → 𝓝[>]0`.  The metric carries `{hg, hgi, hgpos}` and the gauge `det g^K 0 = 1` are
      discharged INTERNALLY; the carried surface is the PRE-`ρ` gate-activation triple
      `{rS, hKball, hSact}`, the witness-slice measurability `hWslice`, and the zeroth wide domination
      `hDom`.  This STRICTLY IMPROVES `curved_hmassone_via_bundle_at_gate`: `hGgate`/`hSupp` (the two
      ρ-dependent carriers) are removed from the conclusion.
    • `curved_hmassone_final_curved_satisfiable` — ★ the NON-VACUITY certificate (re-exported from
      `curved_hmassoneBound_satisfiable`): for `κ < 0`, `n ≥ 2`, the gauge `det g^K 0 = 1` holds WHILE
      `g^K` is GENUINELY CURVED (`∃ w, 1 < det g^K w`), so the discharged reduction is NOT the flat
      kernel and NOT a `K = {0}` collapse.

  ── HONEST RESIDUAL.  This CLOSES `hmassone`'s ρ-gate carriers (`hGgate`/`hSupp`).  `hmassone` is now
     unconditional-in-`ρ` MODULO the satisfiable PRE-`ρ` carriers `{rS, hKball, hSact, hWslice, hDom}`:
       • `hKball`/`rS` — satisfiable from `K ∈ 𝓝 0` (a ball inside `K`);
       • `hSact`      — the gate activation `0 ∈ constGate … c z` for `z` near `0` (reachability of the
                        origin by the flow-exp, `ConcreteGateAssembly.reachableGate_concrete`-shape);
       • `hWslice`    — per-`τ` witness-slice measurability;
       • `hDom`       — the zeroth Gaussian domination (`WideAmplitudeData.zeroth_domination_global`).
     These are HONEST inputs, none the conclusion.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  The curved a₁ = R/6 capstone is
  NON-VACUOUS (J4-587) but CONDITIONAL on carried residuals; `hmassone` is now down to the four
  satisfiable pre-`ρ` carriers above (the ρ-gate carriers `hGgate`/`hSupp` are CLOSED).  Everything
  here is TRUE for the genuinely-curved `g^K` (`κ ≤ 0`, `Ric ≠ 0`), DERIVED from the PROVED
  gate/annulus-split machinery, NOT axiomatized, NOT the `a₁` conclusion.  No `sorry`, no new axioms,
  no `:= True`, no vacuous / conclusion-in-disguise hypothesis, no existing file edited, nothing
  committed.
-/
import Mathlib
import QIQTH.CurvedA1HmassoneBound
import QIQTH.GateAnnulusSplit

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ChartImageAIConcrete QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.RadialDistance
open scoped Topology

namespace QIQTH.CurvedA1HmassoneFinal

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The curved base-mass limit `hmassone` — `hGgate`/`hSupp` discharged. -/

/-- **★★ J4-591 — `curved_hmassone_final_at_gate` — the curved `hmassone` with the ρ-gate carriers
    `hGgate`/`hSupp` DISCHARGED.**  The EXACT `hmassone` shape carried by the center-gauge curved
    capstone,
        `Tendsto (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (epsSeq m) 0 z) atTop (𝓝 1)`,
    obtained as the `f ≡ 1` special case of the banked FIXED-`f` FINAL
    `GateAnnulusSplit.chartImage_approx_identity_final` (which discharges `hGgate` from the external
    gate-activation triple `{rS, hKball, hSact}` and `hSupp` by the Gaussian-tail annulus split fed by
    the zeroth domination `hDom` + `hWslice`), composed with `epsSeq → 𝓝[>]0`.

    The metric carries `{curvedRNCMetric_contDiff, curvedRNCInv_contDiff (κ ≤ 0),
    curvedRNCMetric_hgpos (κ ≤ 0)}` and the gauge `det g^K 0 = 1`
    (`curvedRNCMetric_det_center`) are discharged INTERNALLY.  The carried surface is the PRE-`ρ`
    (i.e. `ρ`-INDEPENDENT) gate-activation triple `{rS, hKball, hSact}`, the witness-slice
    measurability `hWslice`, and the zeroth wide domination `hDom`.

    This STRICTLY IMPROVES `CurvedA1HmassoneBound.curved_hmassone_via_bundle_at_gate` (which carried
    `hGgate`/`hSupp` on the PRODUCED `ρ`): those two carriers are REMOVED from the conclusion.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hmassone_final_at_gate (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (a b c : ℝ) (ha : 0 < a) (hab : a < b)
    -- gate-activation carries (discharge `hGgate`, PRE-`ρ`):
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS,
      (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z)
    -- witness-slice measurability (for the annulus split's integrability):
    (hWslice : ∀ τ : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z) volume)
    -- zeroth wide domination (discharge `hSupp` by the annulus split):
    (lam τ₀ CW : ℝ) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hCW : 0 ≤ CW)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z|
        ≤ CW * gaussDdim (lam * τ) z) :
    ∃ ρ > (0 : ℝ),
      Tendsto (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
          (epsSeq m) (0 : Point n) z) atTop (𝓝 1) := by
  -- metric carries for `g^K`, `κ ≤ 0`.
  have hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => curvedRNCMetric κ y a b) :=
    fun a b => curvedRNCMetric_contDiff κ a b
  have hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => curvedRNCInv κ y a b) :=
    fun a b => curvedRNCInv_contDiff κ hκ a b
  have hgpos : ∀ v : Point n, 0 < Matrix.det (curvedRNCMetric κ v) := curvedRNCMetric_hgpos κ hκ
  -- the curved gauge `det g^K 0 = 1`.
  have hgdet0 : Matrix.det (curvedRNCMetric κ (0 : Point n)) = 1 :=
    QIQTH.CurvedA1HmassoneBound.curvedRNCMetric_det_center κ
  -- the `f ≡ 1` case of the banked FIXED-`f` FINAL (CoV bundle + measurability + `hbound`/`hlocal`
  -- discharged AND `hGgate`/`hSupp` discharged from the pre-`ρ` gate/domination carries).
  obtain ⟨ρ, hρ, hlim⟩ := QIQTH.GateAnnulusSplit.chartImage_approx_identity_final
    (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK h0Kmem hg hgi hgpos
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b ha hab hgdet0
    (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩ continuousAt_const
    rS hrS hKball hSact hWslice
    lam τ₀ CW hlam hτ₀ hCW hDom
  refine ⟨ρ, hρ, ?_⟩
  -- `hlim : Tendsto (fun τ => ∫ z, Wit τ 0 z · 1) (𝓝[>]0) (𝓝 1)`.
  -- `epsSeq → 𝓝[>]0` (positive, → 0).
  have heps : Tendsto (epsSeq : ℕ → ℝ) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      epsSeq_tendsto (Filter.Eventually.of_forall (fun m => epsSeq_pos m))
  -- compose and clean up `f 0 = 1`, `Wit · 1 = Wit`, `∘ epsSeq`.
  have hcomp := hlim.comp heps
  simpa using hcomp

/-! ### Non-vacuity: the gauge holds while `g^K` is genuinely curved (re-export). -/

/-- **★ `curved_hmassone_final_curved_satisfiable` — the NON-VACUITY certificate.**  Re-exports
    `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`: for `κ < 0` and `n ≥ 2` the discharged
    `hmassone` reduction is NOT secretly the flat kernel and NOT a `K = {0}` collapse — the gauge input
    `det g^K(0) = 1` holds WHILE `g^K` is GENUINELY CURVED (`∃ w, 1 < det g^K w`,
    `det g^K(w) = (1 − (K/3)‖w‖²)^(n−1) > 1` at `‖w‖ > 0`, `K < 0`).  NOT `a₁ = R/6`. -/
theorem curved_hmassone_final_curved_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    Matrix.det (curvedRNCMetric κ (0 : Point n)) = 1
      ∧ ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  QIQTH.CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable κ hκ hn

end QIQTH.CurvedA1HmassoneFinal

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1HmassoneFinal

#print axioms curved_hmassone_final_at_gate
#print axioms curved_hmassone_final_curved_satisfiable

end AxiomChecks
