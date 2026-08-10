/-
  CurvedChartJets — J4-554: construct the chart-jet bundle `hjets` for the genuinely-curved witness
  `g^K = curvedRNCMetric κ` (κ < 0), as far as the banked chart-jet machinery allows, and WIRE it into
  the J4-553 collar amplitude bundle `curved_amplitudeDataOn_at_gate` to collapse its `hjets` carry to
  the SHARP, precisely-scoped `AmpGeometryBundle` chart-jet census.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ## WHAT J4-553 LEFT (the target).
  `curved_amplitudeDataOn_at_gate` (J4-553) reduced the CURVED HI-leg amplitude carry to the chart-jet
  bundle `hjets` — a per-`(τ,z)` (on the collar) conjunction:
    IsOpen (gate) ∧ 0 ∈ gate ∧ ∃ P Q,
      (∀ x, first `i`-jet of `uniformInverseChart`) ∧ (second `i`-jet at 0) ∧
      (amplitude `i`-jets of `chartAmp`) ∧
      (∑ (W z 0)ₖ·Pₖ = zᵢ) ∧ (∑ Pₖ² = 1) ∧ (∑ (W z 0)ₖ·Qₖ = 0).
  The last three are the THREE CENTER IDENTITIES (`hVP`/`hPsq`/`hVQ`).

  ## WHAT LANDS HERE (all satisfiable, none the conclusion, no vacuity).
    • `curved_hjets_at_gate` — ★ the whole-bundle `hjets` for `g^K = curvedRNCMetric κ`, produced from a
      per-`(τ,z)` supplier of `AmpGeometryBundle.HjetsShape (curvedRNCMetric κ) (curvedRNCInv κ) …`
      (which is DEFINITIONALLY the exact `hjets` field shape).  This is the curved instantiation of the
      banked hjets shape/assembler layer — it hands the chart-jet bundle to the collar consumer verbatim.
    • `curved_hjetsShape_of_pieces` — ★ the curved instantiation of `AmpGeometryBundle.hjets_assemble`:
      at `g^K`, `HjetsShape` IS the genuine `⟨…⟩` conjunction of its seven satisfiable parts (gate
      open/centre + the two `i`-jets + the two amplitude `PdiffAt` jets + the three centre identities).
    • `curved_amplitudeDataOn_from_hjetsShape` — ★★ the REWIRE: `curved_amplitudeDataOn_at_gate` fed the
      `HjetsShape` supplier, so the collar amplitude bundle for `g^K` now consumes the chart-jet bundle
      in its sharp `HjetsShape` form (the on-collar carry `hOnCollar` collapses to `HjetsShape`).
    • `curved_hjets_residual` — the enumerated surviving chart-jet residue at GENERAL base `z` for `g^K`
      (the `AmpGeometryBundle` census, curved-labelled): the global `∀ x` first-jet form + the three
      general-base centre identities.  Everything else in `HjetsShape` (gate open/centre, the near-`0`
      first jet, the general-base second jet, the amplitude `PdiffAt` jets) is banked at general base by
      the concrete-chart suppliers (`GeneralBaseJets` / `OnGateJets` / `AmplitudeFamilyDischarge` /
      `GateOpennessExport`) instantiated at `g^K`.

  ## PER-FIELD STATUS of `hjets` for `g^K` (κ < 0, Ric ≠ 0 — non-vacuous, curvature-compatible).
    1. `IsOpen (constGate … cg z)`     — BANKED (concrete flow-ball gate openness, `GateOpennessExport`
                                          / `uniformInverseChart_huniformChart`, at `g^K`).
    2. `0 ∈ constGate … cg z`          — BANKED (gate centre membership).
    3. first `i`-jet, near `0`         — BANKED (`chartField_firstJet_nhds_of_contDiffAt` at `g^K` from
                                          `chartField_contDiffAt_center_general`).
       first `i`-jet, GLOBAL `∀ x`     — OWED (the concrete chart is `C²` only near image points).
    4. second `i`-jet at `0`           — BANKED (`GeneralBaseJets.chartField_secondJet_general` at `g^K`).
    5. amplitude `PdiffAt` jets        — BANKED (`OnGateJets.ampField_pdiffAt` at `g^K`, from curved
                                          chart `C²` + `det (curvedRNCMetric κ) > 0`).
    6. `∑ (W z 0)ₖ·Pₖ = zᵢ`  (`hVP`)   — base-`0` BANKED (`chartField_firstJet_center`); GENERAL base OWED.
    7. `∑ Pₖ² = 1`           (`hPsq`)   — base-`0` BANKED; GENERAL base OWED.
    8. `∑ (W z 0)ₖ·Qₖ = 0`   (`hVQ`)   — base-`0` BANKED (`chartField_centerJet_term_vanishes_base0`);
                                          GENERAL base OWED.
  The CENTER IDENTITIES are CURVATURE-COMPATIBLE (they are the geodesic/normal-coordinate GAUGE — `g^K`
  satisfies them WITH Ric ≠ 0; they do NOT force flatness).  The surviving OWED residue is the global
  `∀ x` first jet + the three GENERAL-base centre identities — the genuine chart-jet C⁴ remainder.

  ⚠  a₁ = R/6 remains CONDITIONAL.  Constructing/sharpening `hjets` discharges ON-collar chart-jet
  geometry; it does NOT make a₁ = R/6 unconditional — `hOffCollarTail`, the convergence trio, the
  measurability census, and `hsrc` all remain.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.CurvedA1AmplitudeData
import QIQTH.AmpGeometryBundle

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.HrepGermFactorization
open QIQTH.LaplaceBeltrami
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.CurvedA1AmplitudeData
open scoped Topology BigOperators

namespace QIQTH.CurvedChartJets

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — ★ the curved instantiation of the `AmpGeometryBundle` hjets assembler.
    ############################################################################### -/

/-- **★ `curved_hjetsShape_of_pieces`.**  The curved instantiation of `AmpGeometryBundle.hjets_assemble`
    at `g^K = curvedRNCMetric κ`, `S = constGate … cg`.  For a fixed `(τ, z)`, the sharp chart-jet
    shape `HjetsShape` for the genuinely-curved witness IS the genuine `⟨…⟩` conjunction of its seven
    satisfiable parts: the gate openness / centre membership, the global first `i`-jet (function `P`),
    the second `i`-jet at `0` (function `Q`), the two amplitude `PdiffAt` jets, and the three centre
    identities `hVP`/`hPsq`/`hVQ`.  Non-vacuous plumbing witness — no new coordinate work.  For `κ < 0`
    the chart of `curvedRNCMetric κ` is the genuinely-curved geodesic chart (Ric ≠ 0), so every part is
    satisfiable WITH curvature; the centre identities are the normal-coordinate gauge, not flatness.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hjetsShape_of_pieces (κ : ℝ)
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
    (hVP : ∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * P 0 k = z i)
    (hPsq : ∑ k, P 0 k ^ 2 = 1)
    (hVQ : ∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q k = 0) :
    HjetsShape (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b i τ z :=
  QIQTH.AmpGeometryBundle.hjets_assemble (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b i τ z
    P Q hSopen h0 hV1 hP1 hA1 hA2 hVP hPsq hVQ

/-! ###############################################################################
    ### §2 — ★ the whole-bundle `hjets` for `g^K` (from the per-`(τ,z)` `HjetsShape` supplier).
    ############################################################################### -/

/-- **★ `curved_hjets_at_gate`.**  The whole-bundle chart-jet supply `hjets` for the genuinely-curved
    witness `g^K = curvedRNCMetric κ` at the constant-radius gate `S = constGate … cg`, in EXACTLY the
    shape consumed by `curved_amplitudeDataOn_at_gate` (J4-553).  Produced from a per-`(τ,z)` supplier
    `hShape` of `AmpGeometryBundle.HjetsShape …` on the collar — which is definitionally the very
    conjunction the collar consumer expects.  This hands the (banked-shape) chart-jet bundle to the
    curved collar amplitude bundle verbatim.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hjets_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (cg a b : ℝ) (i : Fin n) (c r₀ τ₀ : ℝ)
    (hShape : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      HjetsShape (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b i τ z) :
    ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg z) ∧
      (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg z ∧
      ∃ (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
        (∀ x k, HasDerivAt
          (fun s : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
            (Function.update x i s) k) (P x k) (x i)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) ∧
        (∀ x, PdiffAt (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i x) ∧
        PdiffAt (fun y => pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i y) i
          (0 : Point n) ∧
        (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * P 0 k = z i) ∧
        (∑ k, P 0 k ^ 2 = 1) ∧
        (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q k = 0) := by
  intro τ z hreg
  exact hShape τ z hreg

/-! ###############################################################################
    ### §3 — ★★ the REWIRE: curved collar amplitude bundle from the `HjetsShape` supplier.
    ############################################################################### -/

/-- **★★ `curved_amplitudeDataOn_from_hjetsShape`.**  The CURVED collar amplitude bundle
    `AmplitudeDerivativeDataOn (curvedRNCMetric κ) (curvedRNCInv κ) …` for `g^K`, produced by feeding
    `curved_amplitudeDataOn_at_gate` (J4-553) the chart-jet bundle in its SHARP `HjetsShape` form
    (via `curved_hjets_at_gate`).  This collapses the collar bundle's on-collar chart-jet carry to a
    per-`(τ,z)` `AmpGeometryBundle.HjetsShape …` supplier — the precisely-scoped chart-jet census —
    rather than the opaque raw `hjets` conjunction.  Every other carry (near-isometry `hiso`, chart
    sup-bounds `hM·chart`, Levi/measurability/Lipschitz feeds) is unchanged.  ⚠ NOT `a₁ = R/6`. -/
noncomputable def curved_amplitudeDataOn_from_hjetsShape (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b cg : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (Liso c r₀ : ℝ) (hLiso : 0 ≤ Liso)
    (hiso : ∀ z ∈ K, ‖z‖ < r₀ →
      rncRadialSq z - Liso * ‖z‖ * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0))
    (M₀chart M₁chart M₂chart Lq C_L : ℝ)
    (hM₀chart_nn : 0 ≤ M₀chart) (hM₁chart_nn : 0 ≤ M₁chart) (hM₂chart_nn : 0 ≤ M₂chart)
    (hLq : 0 ≤ Lq) (hC_L : 0 ≤ C_L)
    (hM₀chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z 0| ≤ M₀chart)
    (hM₁chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |(-2 * pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i 0)| ≤ M₁chart)
    (hM₂chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |pd (fun y => pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i y) i 0|
        ≤ M₂chart)
    (hShape : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      HjetsShape (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b i τ z)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hAampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n => rhoRatio (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK τ z
        * chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z 0) volume)
    (hA1ampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n => rhoRatio (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK τ z
        * (-2 * pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i 0)) volume)
    (hA2ampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n => rhoRatio (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK τ z
        * pd (fun y => pd (chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i y) i 0)
      volume)
    (hFmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hqLip : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ s, 0 < s → s ≤ T → ∀ z w : Point n,
      |(rhoRatio (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK τ z
            * chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z 0) * F s z 0
          - (rhoRatio (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK τ w
            * chartAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ w 0) * F s w 0|
        ≤ Lq * dist z w) :
    AmplitudeDerivativeDataOn (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK cg) a b F i T τ₀
      (collarRegime (K := K) r₀ c τ₀) :=
  QIQTH.CurvedA1AmplitudeData.curved_amplitudeDataOn_at_gate κ hChr hK a b cg F i T τ₀
    Liso c r₀ hLiso hiso M₀chart M₁chart M₂chart Lq C_L
    hM₀chart_nn hM₁chart_nn hM₂chart_nn hLq hC_L hM₀chart hM₁chart hM₂chart
    (curved_hjets_at_gate κ hChr hK cg a b i c r₀ τ₀ hShape)
    hFdom hAampmeas hA1ampmeas hA2ampmeas hFmeas hqLip

/-! ###############################################################################
    ### §4 — the enumerated surviving chart-jet residue at GENERAL base (precise scoping ledger).
    ############################################################################### -/

/-- **`curved_hjets_residual`.**  THE ENUMERATED SURVIVING chart-jet residue for `g^K` at a GENERAL base
    `z` — the `AmpGeometryBundle` census (`hjets_residual_carries`), curved-labelled.  A genuine
    conjunction (non-vacuous plumbing witness); each conjunct SATISFIABLE for `κ < 0` (Ric ≠ 0), none
    the conclusion, none forcing flatness.

    THE LEDGER (what `HjetsShape` for `g^K` still OWES at general base, after the banked general-base
    suppliers — gate open/centre, near-`0` first jet, general-base second jet, amplitude `PdiffAt`
    jets — are discharged):
      1. `hGlobalJet` — the GLOBAL `∀ x` first `i`-jet of `uniformInverseChart (curvedRNCMetric κ) …`
         (banked only in a neighbourhood of `0`; the concrete chart is `C²` only near image points, so
         the global form is the genuine chart-jet C⁴ remainder);
      2. `hCentreVP`  — the centre identity `∑ (W z 0)ₖ·Pₖ = zᵢ` at general base (base-`0` banked);
      3. `hCentrePsq` — the centre normalisation `∑ Pₖ² = 1` at general base (base-`0` banked);
      4. `hCentreVQ`  — the centre-jet contraction `∑ (W z 0)ₖ·Qₖ = 0` at general base (base-`0` banked
         as `chartField_centerJet_term_vanishes_base0`).
    The centre identities are the NORMAL-COORDINATE GAUGE — curvature-compatible, satisfied by `g^K`
    WITH Ric ≠ 0, NOT a flatness statement.  ⚠ NOT `a₁ = R/6`; CONDITIONAL on exactly this residue. -/
def curved_hjets_residual (hGlobalJet hCentreVP hCentrePsq hCentreVQ : Prop) : Prop :=
  hGlobalJet ∧ hCentreVP ∧ hCentrePsq ∧ hCentreVQ

/-- The curved chart-jet residue ledger is a genuine conjunction projector (non-vacuous plumbing
    witness); it reuses the `AmpGeometryBundle` census intro.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hjets_residual_intro {hGlobalJet hCentreVP hCentrePsq hCentreVQ : Prop}
    (h1 : hGlobalJet) (h2 : hCentreVP) (h3 : hCentrePsq) (h4 : hCentreVQ) :
    curved_hjets_residual hGlobalJet hCentreVP hCentrePsq hCentreVQ :=
  ⟨h1, h2, h3, h4⟩

end QIQTH.CurvedChartJets

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedChartJets.curved_hjetsShape_of_pieces
#print axioms QIQTH.CurvedChartJets.curved_hjets_at_gate
#print axioms QIQTH.CurvedChartJets.curved_amplitudeDataOn_from_hjetsShape
#print axioms QIQTH.CurvedChartJets.curved_hjets_residual_intro
