/-
  CurvedA1WbvCoV — J4-589: the mass-side endgame — the BASE-VARYING change-of-variables (CoV)
  bundle M1–M4 for the curved chart `Wbv`, and the reduced curved `hmassone`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the curved a₁ = R/6 capstone owes `hmassone` — J4-588).  The center-gauge curved capstone
  `CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center` is NON-VACUOUS at a genuinely-curved
  witness `g^K = curvedRNCMetric κ` (`κ < 0`, `Ric ≠ 0`) but CARRIES the heat-kernel unit-mass limit
      `hmassone : Tendsto (fun m => ∫ z, Wit (epsSeq m) 0 z) atTop (𝓝 1)`,
      `Wit := vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate …) a b`.
  J4-588 (`CurvedA1Hmassone.curved_hmassone_at_gate`) reduced `hmassone` to the `f ≡ 1` case of the
  W1 approximate-identity capstone `ChartImageAIConcrete.chartImage_approx_identity_conditional`,
  CARRYING a TWELVE-input surface, of which J4-588 flagged the BASE-VARYING CoV bundle M1–M4 for
      `Wbv : z ↦ uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0`
  (the derivative field `f'`, injectivity, left inverse `V`, positive Jacobian) as the "acknowledged
  MISSING brick".

  ── ★★ VERDICT (J4-589): the base-varying CoV bundle M1–M4 for `Wbv` is ALREADY BANKED — UNCONDITIONAL
     — and metric-GENERIC.  "Don't-undercredit" applies to J4-588's own residual list.  The M1–M4
     bundle for the base-varying chart was made UNCONDITIONAL (given only the standing geometry
     `hC`, `hK`, `K ∈ 𝓝 0`) in J4-274 `TerminalVelC2.baseVaryingIFTPackage_unconditional`: the
     `.choose`/joint-base J3 base-slot-regularity blocker was discharged through the geodesic-reversal /
     terminal-velocity `C²` route (`GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt` ∘
     `TerminalVelC2.terminalVel0_contDiffAt_two`), so NO regularity hypothesis remains.  Because that
     bundle is generic in `(g, gi)`, the CURVED bundle for `g^K = curvedRNCMetric κ` is a DIRECT
     INSTANTIATION — no new construction, no residual.  Moreover the chart-image measurability `hΩmeas`
     (J4-275 `chartImage_measurableSet_of_bundle`) and the Layer-C measurability member `hmeas`
     (J4-277 `chartImage_trio_hmeas`) are ALSO discharged generically, collapsing the W1 capstone to
     `FixedFTrioDischarge.chartImage_approx_identity_v2` with only FOUR carries (`hGgate`, `hSupp`,
     `hbound`, `hlocal`).

     ⚠ ORIENTATION FIREWALL — the two chart slots are DIFFERENT functions.  J4-577/578 banked, for the
     genuinely-curved witness, `hreg : ∀ z ∈ ball, ContDiffAt ℝ 2 (uniformInverseChart g^K gi^K hChr hK z) 0`
     — the FIELD-slot `C²` (base `z` FIXED, function of the FIELD argument, at field point `0`), i.e.
     regularity of `Wfv`.  The M1–M4 bundle needs `ContDiffAt ℝ 2 (fun z => uniformInverseChart … z 0) 0`
     — the BASE-slot `C²` (base VARYING, field FIXED at `0`), i.e. regularity of `Wbv`.  `Wbv ≠ Wfv`
     (they agree only at `0`); so `hreg` does NOT supply the bundle's input.  That base-slot input is
     the one discharged unconditionally through the terminal-velocity route in J4-274 — NOT via `hreg`.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_Wbv_CoV_bundle_at_gate` — ★★ the FULL M1–M4 CoV bundle for the curved `Wbv`, UNCONDITIONAL
      given the interior-basepoint gate `K ∈ 𝓝 0`.  A direct instantiation of
      `baseVaryingIFTPackage_unconditional` at `(curvedRNCMetric κ, curvedRNCInv κ)`: there is `ρ > 0`,
      an inverse `V`, and a derivative field `f'` with M1 (`HasFDerivWithinAt`), M2 (`InjOn`),
      M3 (left inverse), M4 (`0 < |det f'|`) on `ball 0 ρ`, plus `MeasurableSet (ball 0 ρ)` and the
      image neighbourhood `Wbv '' (ball 0 ρ) ∈ 𝓝 0`.  This DISCHARGES the base-varying CoV carriers
      of J4-588's `curved_hmassone_at_gate` for `g^K`.
    • `curved_Wbv_hasFDeriv_center_at_gate` — ★ the NON-VACUITY / near-identity anchor.  For the curved
      `Wbv`, `HasFDerivAt Wbv (-id) 0`: the base-varying chart is genuinely differentiable at the
      centre with the invertible derivative `-id` (`|det| = 1 > 0`), certifying `Wbv` is a genuine
      near-identity diffeomorphism on a small ball — the bundle is NOT vacuous.
    • `curved_hmassone_via_v2_at_gate` — ★★ the REDUCED curved base-mass limit.  The EXACT `hmassone`
      shape carried by the curved capstone, obtained as the `f ≡ 1` case of `chartImage_approx_identity_v2`
      (M1–M4, `hΩmeas`, `hΩnhds`, `hmeas` ALL discharged) composed with `epsSeq → 𝓝[>]0`.  The carried
      surface shrinks from J4-588's TWELVE inputs to FOUR (`hGgate`, `hSupp`, `hbound`, `hlocal`), stated
      as an implication under the CoV bundle's `(ρ, V, f')`.  This STRICTLY IMPROVES `curved_hmassone_at_gate`.

  ── HONEST RESIDUAL (what is still owed for `hmassone`, and WHY).  The FOUR remaining carries:
      (C1) `hGgate` / (C2) `hSupp` — the gate-activation / τ-uniform-support ball-vs-annulus split
            (obstruction (B), a separate thread); and
      (C4) `hbound` / (C5) `hlocal` — the a.e.-boundedness and joint `(τ,w) → (0⁺,0)` limit of the moving
            integrand over the WHOLE chart image `Ω`.  Per the J4-277 HONEST RESIDUAL, C4/C5 need a
            UNIFORM amplitude sup-bound and a UNIFORM Jacobian lower bound `|det f'| ≥ c > 0` over `Ω`,
            plus inverse-continuity `V w → 0` and `|det f'(V w)| → 1` — which require the ENRICHED
            partial-homeomorph bundle (`EnrichedChartBundle`), a separate brick, NOT performed here.
    These FOUR are genuine, simultaneously-satisfiable inputs, each strictly weaker than the `Tendsto`
    conclusion; none is the conclusion in disguise.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  The curved a₁ = R/6 capstone is
  NON-VACUOUS (J4-587) but CONDITIONAL on carried residuals INCLUDING `hmassone` (⟵ this CoV bundle +
  the FOUR remaining amplitude/gate carries).  Everything here is TRUE for the genuinely-curved
  `g^K` (`κ ≤ 0`, `Ric ≠ 0`): `Wbv` IS a near-identity diffeo on a small ball, so M1–M4 hold; the
  bundle is DERIVED from the PROVED terminal-velocity machinery, NOT axiomatized, NOT the `a₁`
  conclusion.  No `sorry`, no new axioms, no `:= True`, no vacuous / conclusion-in-disguise hypothesis,
  no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedA1Hmassone
import QIQTH.FixedFTrioDischarge
import QIQTH.CurvedRNCPosDef

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ChartImageAIConcrete QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.TerminalVelC2 QIQTH.FixedFTrioDischarge QIQTH.BaseVaryingIFTPackage
open scoped Topology

namespace QIQTH.CurvedA1WbvCoV

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The full base-varying M1–M4 CoV bundle for the curved chart `Wbv`. -/

/-- **★★ J4-589 — `curved_Wbv_CoV_bundle_at_gate` — the base-varying CoV bundle M1–M4 for `g^K`.**
    For the genuinely-curved witness `g^K = curvedRNCMetric κ`, given the interior-basepoint gate
    `K ∈ 𝓝 0`, there is a CoV radius `ρ > 0`, an inverse `V`, and a derivative field `f'` such that
    the base-varying chart `Wbv : z ↦ uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0`
    satisfies the FULL change-of-variables bundle on `ball 0 ρ`:
      (M1) `∀ z ∈ ball 0 ρ, HasFDerivWithinAt Wbv (f' z) (ball 0 ρ) z`;
      (M2) `Set.InjOn Wbv (ball 0 ρ)`;
      (M3) `∀ z ∈ ball 0 ρ, V (Wbv z) = z`;
      (M4) `∀ z ∈ ball 0 ρ, 0 < |(f' z).det|`;
    plus `MeasurableSet (ball 0 ρ)` and the image neighbourhood `Wbv '' (ball 0 ρ) ∈ 𝓝 0`.

    UNCONDITIONAL (no regularity hypothesis): a DIRECT instantiation of
    `TerminalVelC2.baseVaryingIFTPackage_unconditional` at `(curvedRNCMetric κ, curvedRNCInv κ)`, whose
    `.choose`/joint-base J3 blocker was discharged through the geodesic-reversal / terminal-velocity
    `C²` route (J4-274).  This DISCHARGES the base-varying CoV carriers (M1–M4 + `hΩnhds`) of J4-588's
    `curved_hmassone_at_gate` for `g^K`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_Wbv_CoV_bundle_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      MeasurableSet (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          HasFDerivWithinAt
            (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) (f' z)
            (Metric.ball (0 : Point n) ρ) z)
      ∧ Set.InjOn
          (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
          (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          V (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) = z)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ, 0 < |(f' z).det|)
      ∧ (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
          '' (Metric.ball (0 : Point n) ρ) ∈ 𝓝 (0 : Point n) :=
  baseVaryingIFTPackage_unconditional (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK h0Kmem

/-! ### The near-identity anchor (non-vacuity of the bundle). -/

/-- **★ J4-589 — `curved_Wbv_hasFDeriv_center_at_gate` — the curved `Wbv` is a near-identity at `0`.**
    For the curved witness `g^K`, the base-varying chart `Wbv` is differentiable at the centre with
    the INVERTIBLE derivative `-id` (`|det(-id)| = 1 > 0`).  Certifies that the CoV bundle of
    `curved_Wbv_CoV_bundle_at_gate` is anchored to a GENUINE near-identity diffeomorphism — NOT
    vacuous.  A direct instantiation of `BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center`,
    itself derived from the banked quadratic displacement bound `‖Wbv z + z‖ ≤ C ‖z‖²`.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_Wbv_hasFDeriv_center_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    HasFDerivAt
      (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
      ((ContinuousLinearEquiv.neg ℝ : Point n ≃L[ℝ] Point n) : Point n →L[ℝ] Point n)
      (0 : Point n) :=
  baseVaryingChart_hasFDerivAt_center (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK h0Kmem

/-! ### The reduced curved base-mass limit — `hmassone` from only FOUR carries. -/

/-- **★★ J4-589 — `curved_hmassone_via_v2_at_gate` — the curved `hmassone`, base-varying CoV bundle +
    chart-image measurability + Layer-C measurability ALL discharged.**  The EXACT `hmassone` shape
    carried by the center-gauge curved capstone,
        `Tendsto (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (epsSeq m) 0 z) atTop (𝓝 1)`,
    obtained as the `f ≡ 1` special case of the v2 W1 capstone
    `FixedFTrioDischarge.chartImage_approx_identity_v2` (M1–M4, `hΩmeas`, `hΩnhds`, `hmeas` discharged),
    composed with `epsSeq → 𝓝[>]0`.

    The carried surface shrinks from J4-588's TWELVE inputs to FOUR — stated as an implication under the
    CoV bundle's produced `(ρ, V, f')`:
      • `hGgate` : the witness gate is active on `ball 0 ρ`;
      • `hSupp`  : the witness vanishes off `ball 0 ρ`, τ-uniformly;
      • `hbound` : a.e.-boundedness of the moving integrand on `Ω`, eventually in `τ`;
      • `hlocal` : the joint `(τ,w) → (0⁺,0)` limit of the moving integrand to `1`.
    This STRICTLY IMPROVES `CurvedA1Hmassone.curved_hmassone_at_gate` (which carried M1–M4, `hΩmeas`,
    `hΩnhds`, `hmeas` on top of these four).  Metric carries via
    `{curvedRNCMetric_contDiff, curvedRNCInv_contDiff (κ ≤ 0), curvedRNCMetric_hgpos (κ ≤ 0)}`.
    ⚠ This DISCHARGES the carried `hmassone` MODULO the FOUR named residuals (`hbound`/`hlocal` need the
    enriched partial-homeomorph bundle — a separate brick).  NOT `a₁ = R/6`. -/
theorem curved_hmassone_via_v2_at_gate (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) (a b c : ℝ) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      (∀ z ∈ Metric.ball (0 : Point n) ρ,
        z ∈ K ∧ (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z) →
      (∀ τ, ∀ z, z ∉ Metric.ball (0 : Point n) ρ →
        vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z = 0) →
      (∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ᵐ w ∂(volume.restrict
            ((fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
              '' (Metric.ball (0 : Point n) ρ))),
          ‖chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ (V w) 0
            * (1 : ℝ) / |(f' (V w)).det|‖ ≤ C) →
      (∀ ε > 0, ∃ r > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ᵐ w ∂(volume.restrict
            ((fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
              '' (Metric.ball (0 : Point n) ρ))),
          ‖w‖ < r →
            ‖chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ (V w) 0
              * (1 : ℝ) / |(f' (V w)).det| - (1 : ℝ)‖ < ε) →
      Tendsto (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
          (epsSeq m) (0 : Point n) z) atTop (𝓝 1) := by
  -- metric carries for `g^K`, `κ ≤ 0`.
  have hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => curvedRNCMetric κ y a b) :=
    fun a b => curvedRNCMetric_contDiff κ a b
  have hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => curvedRNCInv κ y a b) :=
    fun a b => curvedRNCInv_contDiff κ hκ a b
  have hgpos : ∀ v : Point n, 0 < Matrix.det (curvedRNCMetric κ v) := curvedRNCMetric_hgpos κ hκ
  -- the `f ≡ 1` case of the v2 W1 capstone (CoV bundle + `hΩmeas` + `hmeas` discharged).
  obtain ⟨ρ, hρ, V, f', himpl⟩ := chartImage_approx_identity_v2
    (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK h0Kmem hg hgi hgpos
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (fun _ => (1 : ℝ)) measurable_const
  refine ⟨ρ, hρ, V, f', fun hGgate hSupp hbound hlocal => ?_⟩
  -- `𝓝[>]0`-form base mass → `f 0 = 1`.
  have hbase := himpl hGgate hSupp hbound hlocal
  -- `epsSeq → 𝓝[>]0` (positive, → 0).
  have heps : Tendsto (epsSeq : ℕ → ℝ) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      epsSeq_tendsto (Filter.Eventually.of_forall (fun m => epsSeq_pos m))
  -- compose and clean up `f 0 = 1`, `Wit · 1 = Wit`, `∘ epsSeq`.
  have hcomp := hbase.comp heps
  simpa using hcomp

end QIQTH.CurvedA1WbvCoV

/-! ### Axiom audit. -/

section AxiomChecks

open QIQTH.CurvedA1WbvCoV

#print axioms curved_Wbv_CoV_bundle_at_gate
#print axioms curved_Wbv_hasFDeriv_center_at_gate
#print axioms curved_hmassone_via_v2_at_gate

end AxiomChecks
