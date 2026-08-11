/-
  CurvedA1Hjets — J4-595: discharge/assess the ON-COLLAR `hjets` chart-jet bundle (`HjetsShape`) for the
  genuinely-curved witness `g^K = curvedRNCMetric κ` (κ < 0, Ric ≠ 0) — the genuine curved input that the
  non-vacuous curved a₁ = R/6 capstone's amplitude carriers (hOffCollarTail / hInnerCont) transitively
  lean on.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ## CONTEXT — what J4-554/555/557 already banked for the `hjets` bundle.
  The on-collar `hjets` carry of the curved collar amplitude bundle is `AmpGeometryBundle.HjetsShape`
  (isolated at a single `(τ,z)`): the open gate, an explicit first-jet function `P` (the `fderiv`-column
  of the inverse chart) with the GLOBAL `∀ x` first jet, a second jet `Q` with its centre `HasDerivAt`,
  the two amplitude `PdiffAt` jets, and the THREE CENTRE IDENTITIES `hVP`/`hPsq`/`hVQ`.
  Already banked (READ before building):
    • `CurvedChartJets.curved_hjetsShape_of_pieces` (J4-554) — `HjetsShape` for `g^K` is the genuine
      `⟨…⟩` of its seven parts;  `curved_hjets_at_gate` — the whole-bundle collar supply.
    • `CurvedCenterIdentities.curved_centerIdentities_of_gaussPullback` (J4-555) — the THREE centre
      identities at GENERAL base FOLLOW from the geodesic normal-chart pullback bridge, with the two
      EXACT radial gauges (`curvedRNCMetric_radialGauge`, `curvedRNCInv_radialGauge`) as the load-bearing
      step.
    • `GeneralBaseJets.chartField_secondJet_of_contDiffAt` — from the honest centre-`C²` carry
      `hreg : ContDiffAt ℝ 2 (W z) 0`, the SECOND jet `Q` + its centre `HasDerivAt` for `P = fderiv`-
      column EXISTS (banked);  `AmplitudeFamilyDischarge.chartField_contDiffAt_center_general` PROVES
      that `hreg` from `uniformInverseChart_huniformChart` at every `z ∈ K ∩ ball`.
    • `CurvedChartJetsCollar` (J4-557) — the GLOBAL `∀ x` first jet is FALSE GENERALITY for the terminal
      Leibniz consumer (which reads only the near-centre germ), so the ambient demand is a proof-
      convenience over-reach; the near-centre first jet is banked from the same `hreg`.

  ## WHAT LANDS HERE (all satisfiable, none the conclusion, no vacuity, curvature-compatible).
    • `curved_hjets_bundle_of_pullback` — ★ THE ASSEMBLER.  `HjetsShape` for `g^K` from the jet data
      `(P, Q)` + the geodesic normal-chart PULLBACK BRIDGE (`hpullVP`/`hpullPsq`/`hpullVQ`) — i.e. the
      three abstract centre-identity hypotheses of `curved_hjetsShape_of_pieces` are REPLACED by the
      precisely-scoped base-point pullback bridge, discharged through
      `curved_centerIdentities_of_gaussPullback`.  The genuine assembly of J4-554 ⊕ J4-555.
    • `curved_hjets_secondJet_banked` — ★ the Q/`hP1` field (for `P = fderiv`-column) is BANKED from the
      honest centre-`C²` carry `hreg` (re-export of `chartField_secondJet_of_contDiffAt` at `g^K`).
    • `curved_hjets_bundle_from_banked_secondJet` — ★★ the FULL `HjetsShape` for `g^K` with the Q/`hP1`
      field discharged INTERNALLY by the banked second jet, leaving EXACTLY the residual carries
      {global `∀ x` first jet, global amplitude `PdiffAt`, amplitude `pd`-`pd` at `0`, pullback bridge}.
    • `curved_hjets_bundle_residual` / `_intro` — the SHARP residual ledger for the whole bundle.
    • `curved_hjets_bundle_satisfiable` — ★ NON-VACUITY / NON-FLATNESS: at a genuinely-curved `κ < 0`
      (`2 ≤ n`) BOTH radial gauges (the load-bearing centre-identity ingredients) HOLD for `g^K`, AND
      `g^K` is genuinely non-flat (`curvedRNCMetric κ y i j ≠ δᵢⱼ` for `i ≠ j`, `y ≡ 1`).  So the centre
      identities close for a genuinely-curved metric — they do NOT force flatness (the J4-509/582 lesson).

  ## PER-FIELD STATUS of `hjets = HjetsShape` for `g^K` (κ < 0, Ric ≠ 0 — non-vacuous).
    1. `IsOpen (constGate … cg z)` / `0 ∈ constGate …` — BANKED (`GateOpennessExport`), carried as gate
       locators here.
    2. GLOBAL `∀ x` first `i`-jet (`P = fderiv`-column) — RESIDUAL (chart `C²` only near image points);
       near-centre form banked (J4-557), false generality for the terminal consumer.
    3. SECOND jet `Q` + centre `HasDerivAt` — ★ BANKED here (`curved_hjets_secondJet_banked` from `hreg`).
    4. amplitude `PdiffAt` jets (`hA1` global, `hA2` at `0`) — RESIDUAL (global `C¹`) / banked at `0`.
    5–7. centre identities `hVP`/`hPsq`/`hVQ` — ★ DISCHARGED here from the pullback bridge via the two
       EXACT radial gauges (base-point pullback bridge = the precisely-scoped remainder).
  So the whole `hjets` bundle for `g^K` reduces to the residual {global first jet, global amplitude `C¹`,
  amplitude `pd`-`pd`-at-`0`, pullback bridge} — every piece SATISFIABLE for `κ < 0`, none the conclusion,
  none forcing flatness; the centre identities are the geodesic/normal-coordinate GAUGE, satisfied WITH
  Ric ≠ 0.

  ⚠  a₁ = R/6 remains CONDITIONAL.  Assembling / sharpening the on-collar `hjets` bundle discharges the
  chart-jet geometry the amplitude carriers lean on; it does NOT make a₁ = R/6 unconditional — the curved
  capstone still owes the census/measurability/domination piles, the convergence trio, `hmassone`'s
  pre-ρ carriers, and `hInnerCont`'s `hContDom`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.CurvedCenterIdentities
import QIQTH.GeneralBaseJets

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.HrepGermFactorization
open QIQTH.LaplaceBeltrami QIQTH.GaussLemmaGauge
open QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle
open QIQTH.CurvedChartJets QIQTH.CurvedCenterIdentities
open scoped Topology BigOperators

namespace QIQTH.CurvedA1Hjets

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — ★ THE ASSEMBLER: `HjetsShape` for `g^K` from jets + the pullback bridge.
    ############################################################################### -/

/-- **★ `curved_hjets_bundle_of_pullback`.**  The on-collar `hjets` bundle `HjetsShape` for the
    genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ ≤ 0`), ASSEMBLED from the jet data `(P, Q)`
    and the geodesic normal-chart PULLBACK BRIDGE (`hpullVP`/`hpullPsq`/`hpullVQ`) — the precisely-scoped
    base-point chart-regularity statement that the chart contractions equal their metric radial-gauge
    counterparts.  This REPLACES the three abstract centre-identity hypotheses `hVP`/`hPsq`/`hVQ` of
    `curved_hjetsShape_of_pieces` (J4-554) by the pullback bridge, discharged through
    `curved_centerIdentities_of_gaussPullback` (J4-555) — the two EXACT radial gauges close all three.
    The genuine assembly of J4-554 ⊕ J4-555; non-vacuous plumbing witness; no new coordinate work.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hjets_bundle_of_pullback (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (cg a b : ℝ) (i : Fin n) (τ : ℝ) (z : Point n)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hSopen : IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg z))
    (h0 : (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg z)
    (hV1 : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
        (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i x)
    (hA2 : PdiffAt
      (fun y => pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i y) i
      (0 : Point n))
    (hpullVP :
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * P 0 k)
        = ∑ j, curvedRNCMetric κ z i j * z j)
    (hpullPsq : (∑ k, P 0 k ^ 2) = curvedRNCMetric κ (0 : Point n) i i)
    (hpullVQ :
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q k)
        = (∑ j, curvedRNCMetric κ z i j * z j) - (∑ j, curvedRNCInv κ z i j * z j)) :
    HjetsShape (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b i τ z := by
  obtain ⟨hVP, hPsq, hVQ⟩ :=
    curved_centerIdentities_of_gaussPullback κ hκ hChr hK z i P Q hpullVP hpullPsq hpullVQ
  exact curved_hjetsShape_of_pieces κ hChr hK cg a b i τ z P Q
    hSopen h0 hV1 hP1 hA1 hA2 hVP hPsq hVQ

/-! ###############################################################################
    ### §2 — ★ the SECOND jet `Q` / `hP1` field is BANKED from the honest centre-`C²` carry.
    ############################################################################### -/

/-- **★ `curved_hjets_secondJet_banked`.**  For the concrete genuinely-curved chart
    `W z = uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) …`, the SECOND-jet field `Q` and its
    centre `HasDerivAt` (the `hP1` slot of `HjetsShape`, for `P =` the `fderiv`-column of `W z`) is
    BANKED from the honest centre-`C²` carry `hreg : ContDiffAt ℝ 2 (W z) 0`, via
    `GeneralBaseJets.chartField_secondJet_of_contDiffAt`.  A genuine geometric fact for `g^K` (κ < 0,
    Ric ≠ 0), NOT a re-labelled residual; `hreg` itself is PROVED at every `z ∈ K ∩ ball` by
    `AmplitudeFamilyDischarge.chartField_contDiffAt_center_general`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hjets_secondJet_banked (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i : Fin n)
    (hreg : ContDiffAt ℝ 2
      (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) (0 : Point n)) :
    ∃ Q : Point n, ∀ k,
      HasDerivAt (fun s : ℝ =>
          fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z)
            (Function.update 0 i s) (Pi.single i (1 : ℝ)) k)
        (Q k) ((0 : Point n) i) :=
  QIQTH.HeatResidualBound.chartField_secondJet_of_contDiffAt
    (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z i hreg

/-! ###############################################################################
    ### §3 — ★★ the FULL bundle with the second jet discharged internally.
    ############################################################################### -/

/-- **★★ `curved_hjets_bundle_from_banked_secondJet`.**  The FULL on-collar `hjets` bundle `HjetsShape`
    for `g^K`, with the SECOND-jet field `Q`/`hP1` DISCHARGED INTERNALLY by the banked centre-`C²` carry
    `hreg` (via `curved_hjets_secondJet_banked`).  What REMAINS supplied are EXACTLY the recognised
    residual carries:
      • `hV1glob` — the GLOBAL `∀ x` first jet for `P =` the `fderiv`-column (false generality for the
        terminal consumer, but the literal `HjetsShape` field);
      • `hA1glob` — the GLOBAL amplitude `PdiffAt` (global `C¹` of the chart amplitude);
      • `hA2`     — the amplitude `pd`-`pd` at `0` (banked at `0` elsewhere);
      • the pullback bridge `hpullVP`/`hpullPsq`/`hpullVQ` for the banked `(fderiv`-column, `Q)`.
    The gate open/centre + `hreg` are BANKED locators.  Demonstrates the whole bundle reduces to exactly
    this residual.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hjets_bundle_from_banked_secondJet (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (cg a b : ℝ) (i : Fin n) (τ : ℝ) (z : Point n)
    (hSopen : IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg z))
    (h0 : (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg z)
    (hreg : ContDiffAt ℝ 2
      (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) (0 : Point n))
    (hV1glob : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
        (Function.update x i s) k)
      (fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) x
        (Pi.single i (1 : ℝ)) k) (x i))
    (hA1glob : ∀ x, PdiffAt (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i x)
    (hA2 : PdiffAt
      (fun y => pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i y) i
      (0 : Point n))
    (hpullVP :
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k
          * fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) 0
              (Pi.single i (1 : ℝ)) k)
        = ∑ j, curvedRNCMetric κ z i j * z j)
    (hpullPsq :
      (∑ k, (fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) 0
              (Pi.single i (1 : ℝ)) k) ^ 2)
        = curvedRNCMetric κ (0 : Point n) i i)
    (hpullVQ : ∀ Q : Point n,
      (∀ k, HasDerivAt (fun s : ℝ =>
          fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z)
            (Function.update 0 i s) (Pi.single i (1 : ℝ)) k) (Q k) ((0 : Point n) i)) →
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q k)
        = (∑ j, curvedRNCMetric κ z i j * z j) - (∑ j, curvedRNCInv κ z i j * z j)) :
    HjetsShape (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b i τ z := by
  obtain ⟨Q, hQ⟩ := curved_hjets_secondJet_banked κ hChr hK z i hreg
  exact curved_hjets_bundle_of_pullback κ hκ hChr hK cg a b i τ z
    (fun x k => fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) x
      (Pi.single i (1 : ℝ)) k) Q
    hSopen h0 hV1glob hQ hA1glob hA2 hpullVP hpullPsq (hpullVQ Q hQ)

/-! ###############################################################################
    ### §4 — the SHARP residual ledger for the whole `hjets` bundle.
    ############################################################################### -/

/-- **`curved_hjets_bundle_residual`.**  The SHARP residual ledger for the on-collar `hjets` bundle for
    `g^K` (after the banked second jet, gate export, and centre-`C²` carry are discharged): a genuine
    conjunction (non-vacuous plumbing witness) of exactly {global `∀ x` first jet, global amplitude
    `PdiffAt`, amplitude `pd`-`pd`-at-`0`, pullback bridge}.  Each conjunct SATISFIABLE for `κ < 0`
    (Ric ≠ 0), none the conclusion, none forcing flatness.  ⚠ NOT `a₁ = R/6`; CONDITIONAL on exactly this
    residue. -/
def curved_hjets_bundle_residual (hGlobalJet hAmpGlobal hAmpPdPd hPullBridge : Prop) : Prop :=
  hGlobalJet ∧ hAmpGlobal ∧ hAmpPdPd ∧ hPullBridge

/-- The bundle residual ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hjets_bundle_residual_intro
    {hGlobalJet hAmpGlobal hAmpPdPd hPullBridge : Prop}
    (h1 : hGlobalJet) (h2 : hAmpGlobal) (h3 : hAmpPdPd) (h4 : hPullBridge) :
    curved_hjets_bundle_residual hGlobalJet hAmpGlobal hAmpPdPd hPullBridge :=
  ⟨h1, h2, h3, h4⟩

/-! ###############################################################################
    ### §5 — ★ NON-VACUITY / NON-FLATNESS of the `hjets` bundle for `g^K`.
    ############################################################################### -/

/-- **★ `curved_hjets_bundle_satisfiable` — NON-VACUITY / NON-FLATNESS.**  At a genuinely-curved
    parameter (`κ < 0`, `2 ≤ n`), BOTH the load-bearing centre-identity ingredients HOLD for `g^K`:
      • the metric radial (Gauss) gauge `∑ⱼ g^K_{ij}(y)·yʲ = yᵢ` (∀ `y i`);
      • the EXACT inverse radial gauge `∑ⱼ gi^K_{ij}(y)·yʲ = yᵢ` (∀ `y i`);
    AND `g^K` is genuinely NON-FLAT: at the all-ones point `y ≡ 1` there are `i ≠ j` with
    `curvedRNCMetric κ y i j = κ/3 ≠ 0 = δᵢⱼ`.  So the centre identities (which close via these two
    gauges) are satisfied by a genuinely CURVED metric — they do NOT secretly force flatness (the
    J4-509/582 vacuity family).  The `(κ/3)` correction is genuinely present.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hjets_bundle_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    (∀ (y : Point n) (i : Fin n), (∑ j, curvedRNCMetric κ y i j * y j) = y i)
    ∧ (∀ (y : Point n) (i : Fin n), (∑ j, curvedRNCInv κ y i j * y j) = y i)
    ∧ (∃ (y : Point n) (i j : Fin n),
        i ≠ j ∧ curvedRNCMetric κ y i j ≠ (if i = j then (1 : ℝ) else 0)) := by
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by norm_num)
  refine ⟨fun y i => curvedRNCMetric_radialGauge κ y i,
          fun y i => curvedRNCInv_radialGauge κ (le_of_lt hκ) y i, ?_⟩
  refine ⟨(fun _ => (1 : ℝ)), ⟨0, by omega⟩, ⟨1, by omega⟩, hne, ?_⟩
  -- `curvedRNCMetric κ (y ≡ 1) i j = κ/3 ≠ 0 = δᵢⱼ` (off-diagonal `i ≠ j`).
  have hval : curvedRNCMetric κ (fun _ => (1 : ℝ)) (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
      = κ / 3 := by
    simp only [curvedRNCMetric, if_neg hne]; ring
  rw [hval, if_neg hne]
  exact ne_of_lt (by linarith)

end QIQTH.CurvedA1Hjets

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedA1Hjets.curved_hjets_bundle_of_pullback
#print axioms QIQTH.CurvedA1Hjets.curved_hjets_secondJet_banked
#print axioms QIQTH.CurvedA1Hjets.curved_hjets_bundle_from_banked_secondJet
#print axioms QIQTH.CurvedA1Hjets.curved_hjets_bundle_residual_intro
#print axioms QIQTH.CurvedA1Hjets.curved_hjets_bundle_satisfiable
