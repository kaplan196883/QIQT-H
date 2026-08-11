/-
  CurvedA1HmassoneBound — J4-590: shedding `hmassone`'s `hbound`/`hlocal` carriers via the
  EnrichedChartBundle — the mass-side endgame for the curved a₁ = R/6 capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the curved capstone owes `hmassone`, down to FOUR carries — J4-589).  The center-gauge
  curved capstone `CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center` is NON-VACUOUS at a
  genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`, `Ric ≠ 0`) but CARRIES the heat-kernel
  unit-mass limit `hmassone`.  J4-589 (`CurvedA1WbvCoV.curved_hmassone_via_v2_at_gate`) reduced the
  carried surface to FOUR — `hGgate`, `hSupp`, `hbound`, `hlocal` — by discharging the base-varying
  change-of-variables bundle M1–M4, the chart-image measurability, and the Layer-C measurability
  through `FixedFTrioDischarge.chartImage_approx_identity_v2`.  The J4-589 verdict flagged
  `hbound`/`hlocal` as needing the ENRICHED partial-homeomorph bundle.

  ── ★★ VERDICT (J4-590): `hbound`/`hlocal` are ALREADY DISCHARGED, GENERICALLY, by the ENRICHED
     bundle brick `EnrichedChartBundle.chartImage_approx_identity_v3` (J4-278).  "Don't-undercredit":
     `chartImage_approx_identity_v3` re-runs `ContDiffAt.toOpenPartialHomeomorph` on the near-identity
     `Wbv`, projects out the inverse's continuity on `Ω`, the openness of `Ω`, `V 0 = 0`, the
     derivative pin `f' = fderiv Wbv`, a uniform Jacobian lower bound `1/2 < |det f'|`, and the
     det-continuity/normalisation at the centre, then closes `hbound` from the banked amplitude
     sup-bound `BaseSlotAmplitude.baseSlotAmp_bound` + the carried `|f| ≤ Cf` + the Jacobian lower
     bound, and `hlocal` from the product-filter limit `amp · f / |det| → A₀ · f0 / 1 = f0`
     (`baseSlotAmp_joint_limit`, `bundleV_tendsto_zero`, `bundleDet_tendsto_one`, `f`-continuity,
     `A₀ = 1` via `baseChartAmp_centre_eq_one`).  It carries ONLY `hGgate`/`hSupp`.  Since it is generic
     in `(g, gi, f)`, the CURVED `hmassone` for `g^K` is the `f ≡ 1` INSTANTIATION — no new
     enriched-homeomorph construction needed.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_hmassone_via_bundle_at_gate` — ★★ the curved base-mass limit `hmassone` with the CoV
      bundle, chart-image + Layer-C measurability, AND `hbound`/`hlocal` ALL discharged.  The EXACT
      `hmassone` shape carried by the center-gauge curved capstone, obtained as the `f ≡ 1` case of
      `EnrichedChartBundle.chartImage_approx_identity_v3` composed with `epsSeq → 𝓝[>]0`.  The carried
      surface shrinks from J4-589's FOUR inputs to TWO — `hGgate` and `hSupp` — stated in terms of the
      produced radius `ρ` (no `V`/`f'` exposed).  The additional carries `0 < a < b` and
      `det g^K 0 = 1` are DERIVED internally / satisfiable (see `curved_hmassoneBound_satisfiable`).
      This STRICTLY IMPROVES `curved_hmassone_via_v2_at_gate`.
    • `curved_hmassoneBound_satisfiable` — ★ the NON-VACUITY certificate.  For `κ < 0`, `n ≥ 2`, the
      gauge `det g^K 0 = 1` (the `hgdet0` input) holds WHILE `g^K` is GENUINELY CURVED
      (`∃ w, 1 < det g^K w`, since `det g^K(w) = (1 − (K/3)‖w‖²)^(n−1) > 1` for `‖w‖ > 0`, `K < 0`).
      So the discharged reduction is NOT secretly the flat kernel.

  ── HONEST RESIDUAL.  After this brick `hmassone` is reduced to `hGgate`/`hSupp` ONLY (plus the
     satisfiable standing carries `0 < a < b`, `det g^K 0 = 1`, and the metric regularity/positivity
     that `g^K` supplies for `κ ≤ 0`).  `hGgate`/`hSupp` are the gate-activation / τ-uniform-support
     ball-vs-annulus split (obstruction (B)) — a SEPARATE thread (`GateAnnulusSplit`), NOT addressed
     here.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  The curved a₁ = R/6 capstone is
  NON-VACUOUS (J4-587) but CONDITIONAL on carried residuals INCLUDING `hmassone` (⟵ now down to
  `hGgate`/`hSupp`).  Everything here is TRUE for the genuinely-curved `g^K` (`κ ≤ 0`, `Ric ≠ 0`):
  the amplitude is BOUNDED and its moving average CONCENTRATES at `1` — the mass normalisation — and
  is DERIVED from the PROVED enriched-bundle machinery, NOT axiomatized, NOT the `a₁` conclusion.
  No `sorry`, no new axioms, no `:= True`, no vacuous / conclusion-in-disguise hypothesis, no existing
  file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedA1WbvCoV
import QIQTH.EnrichedChartBundle
import QIQTH.CurvedRNCVanVleckBound

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ChartImageAIConcrete QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.RadialDistance
open scoped Topology

namespace QIQTH.CurvedA1HmassoneBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The gauge value at the centre for the curved witness. -/

/-- **`hgdet0` for `g^K` — the curved gauge normalisation.**  `det g^K(0) = 1`: the exact van-Vleck
    determinant `det g^K(w) = (1 − (K/3)‖w‖²)^(n−1)` collapses to `1^(n−1) = 1` at `w = 0`
    (`rncRadialSq 0 = 0`).  NOT `a₁ = R/6`. -/
theorem curvedRNCMetric_det_center (κ : ℝ) :
    Matrix.det (curvedRNCMetric κ (0 : Point n)) = 1 := by
  rw [QIQTH.CurvedRNCVanVleckBound.curvedRNCMetric_det κ (0 : Point n) (by simp)]
  simp

/-! ### The reduced curved base-mass limit — `hmassone` from only TWO carries. -/

/-- **★★ J4-590 — `curved_hmassone_via_bundle_at_gate` — the curved `hmassone`, base-varying CoV
    bundle + chart-image measurability + Layer-C measurability + `hbound` + `hlocal` ALL discharged.**
    The EXACT `hmassone` shape carried by the center-gauge curved capstone,
        `Tendsto (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (epsSeq m) 0 z) atTop (𝓝 1)`,
    obtained as the `f ≡ 1` special case of the enriched W1 capstone
    `EnrichedChartBundle.chartImage_approx_identity_v3` (M1–M4, `hΩmeas`, `hΩnhds`, `hmeas`, `hbound`,
    `hlocal` ALL discharged), composed with `epsSeq → 𝓝[>]0`.

    The carried surface shrinks from J4-589's FOUR inputs to TWO — stated in terms of the produced
    radius `ρ`:
      • `hGgate` : the witness gate is active on `ball 0 ρ`;
      • `hSupp`  : the witness vanishes off `ball 0 ρ`, τ-uniformly.
    This STRICTLY IMPROVES `CurvedA1WbvCoV.curved_hmassone_via_v2_at_gate` (which carried `hbound`,
    `hlocal` on top of these two).  Metric carries via `{curvedRNCMetric_contDiff,
    curvedRNCInv_contDiff (κ ≤ 0), curvedRNCMetric_hgpos (κ ≤ 0)}`; the gauge `det g^K 0 = 1` is
    derived internally; `0 < a < b` is a satisfiable input.
    ⚠ This DISCHARGES the carried `hmassone` MODULO ONLY `hGgate`/`hSupp` (the gate/support split, a
    separate brick).  NOT `a₁ = R/6`. -/
theorem curved_hmassone_via_bundle_at_gate (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (a b c : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ρ > (0 : ℝ),
      (∀ z ∈ Metric.ball (0 : Point n) ρ,
        z ∈ K ∧ (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z) →
      (∀ τ, ∀ z, z ∉ Metric.ball (0 : Point n) ρ →
        vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z = 0) →
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
  have hgdet0 : Matrix.det (curvedRNCMetric κ (0 : Point n)) = 1 := curvedRNCMetric_det_center κ
  -- the `f ≡ 1` case of the ENRICHED W1 capstone (CoV bundle + measurability + `hbound`/`hlocal`
  -- discharged), for the constant gate witness.
  obtain ⟨ρ, hρ, himpl⟩ := QIQTH.EnrichedChartBundle.chartImage_approx_identity_v3
    (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK h0Kmem hg hgi hgpos
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b ha hab hgdet0
    (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩ continuousAt_const
  refine ⟨ρ, hρ, fun hGgate hSupp => ?_⟩
  -- `𝓝[>]0`-form base mass → `f 0 = 1`.
  have hbase := himpl hGgate hSupp
  -- `epsSeq → 𝓝[>]0` (positive, → 0).
  have heps : Tendsto (epsSeq : ℕ → ℝ) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      epsSeq_tendsto (Filter.Eventually.of_forall (fun m => epsSeq_pos m))
  -- compose and clean up `f 0 = 1`, `Wit · 1 = Wit`, `∘ epsSeq`.
  have hcomp := hbase.comp heps
  simpa using hcomp

/-! ### Non-vacuity: the gauge holds while `g^K` is genuinely curved. -/

/-- **★ `curved_hmassoneBound_satisfiable` — the NON-VACUITY certificate.**  For `κ < 0` and `n ≥ 2`
    the discharged `hmassone` reduction is NOT secretly the flat kernel: the gauge input
    `det g^K(0) = 1` holds WHILE `g^K` is GENUINELY CURVED — there is `w` with `1 < det g^K(w)`
    (`det g^K(w) = (1 − (K/3)‖w‖²)^(n−1) > 1` at any `w` with `‖w‖ > 0`, since `K < 0` makes the base
    `> 1` and the exponent `n − 1 ≥ 1`).  NOT `a₁ = R/6`. -/
theorem curved_hmassoneBound_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    Matrix.det (curvedRNCMetric κ (0 : Point n)) = 1
      ∧ ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) := by
  refine ⟨curvedRNCMetric_det_center κ, ⟨fun _ => (1 : ℝ), ?_⟩⟩
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : rncRadialSq (fun _ => (1 : ℝ) : Point n) = (n : ℝ) := by
    simp [rncRadialSq]
  have hα1 : (1 : ℝ) < 1 - κ / 3 * rncRadialSq (fun _ => (1 : ℝ) : Point n) := by
    rw [hr]; nlinarith [hκ, hn']
  have hαne : (1 - κ / 3 * rncRadialSq (fun _ => (1 : ℝ) : Point n)) ≠ 0 :=
    (by linarith : (0 : ℝ) < 1 - κ / 3 * rncRadialSq (fun _ => (1 : ℝ) : Point n)).ne'
  rw [QIQTH.CurvedRNCVanVleckBound.curvedRNCMetric_det κ (fun _ => (1 : ℝ)) hαne]
  exact one_lt_pow₀ hα1 (by omega)

end QIQTH.CurvedA1HmassoneBound

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1HmassoneBound

#print axioms curvedRNCMetric_det_center
#print axioms curved_hmassone_via_bundle_at_gate
#print axioms curved_hmassoneBound_satisfiable

end AxiomChecks
