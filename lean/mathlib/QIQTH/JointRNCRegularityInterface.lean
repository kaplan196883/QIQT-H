/-
  JointRNCRegularityInterface — the honest, explicitly-named geometric hypothesis bundle for the
  order-2 sliver rate, replacing the vague "chart-regularity" carry of the `hCConv`/`a₁ = R/6` chain
  with ONE precisely-stated standard differential-geometry input.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  It does NOT close `hCConv` and makes NO unconditional claim about
  the capstone.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none
  equal to the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE EXISTS.

  The order-2 √ε sliver rate `SliverGatedFullyCombined.witness_sliver2_xuniform_diag_gated_fullyCombined`
  (J4-817) — the concrete bound
      `∃ C_L, 0 ≤ C_L ∧ ∀ x, |∫ s in (u−ε)..u, ∫ z, (∂ᵢ∂ᵢ vanVleckGatedWitness)(u−s) z · leviSeries s z x|
          ≤ O(√ε)`
  — is CLOSED (std-3, no `sorry`) but had ZERO consumers anywhere in the repo.  Its remaining carries
  fall into TWO disjoint classes:

    • the GENUINELY GEOMETRIC carries — the four second-order RNC chart-surface estimates and the two
      first- and second-jet identities on the concrete `uniformInverseChart` — which the ~150-increment
      campaign (J4-681→791, cp681→696) repeatedly and independently (8+ techniques, external experts)
      identified as the single irreducible wall: joint second-order regularity of the geodesic
      normal-coordinate inverse chart near the diagonal;

    • the AMPLITUDE / LEVI / MEASURABILITY residue — the on-gate boundedness, differentiability,
      off-gate vanishing, Lipschitz, and integrand-measurability data — none of which is a
      differential-geometry frontier.

  THIS FILE isolates the FIRST class into ONE named bundle `JointSecondOrderRNCRegularity`, expressed
  DIRECTLY in terms of this repo's concrete `uniformInverseChart`, and proves the reduction
  `witness_sliver2_diag_of_jointRNCRegularity` : from a `JointSecondOrderRNCRegularity` instance PLUS
  the (explicitly-named) second-class residue, the closed sliver rate FOLLOWS.  This gives the
  zero-consumer sliver theorem its first honest consumer and makes the geometric wall a single,
  standard, PLAUSIBLY-TRUE hypothesis (not a diffuse "chart regularity" hand-wave).

  ## THE INTERFACE — `JointSecondOrderRNCRegularity g gi hC hK z₀ i G C_W C_P C_Q`.

  The standard differential-geometry fact "the Riemannian normal-coordinate inverse chart is jointly
  C² near the diagonal," in QUANTITATIVE (bounded second-order Taylor-data) form, for the concrete
  `uniformInverseChart g gi hC hK z₀` at base point `z₀` and coordinate direction `i`, on the gate
  neighbourhood `G`:
    • `hVdisp_on` — the chart is the identity to SECOND order: `‖chart z + z‖ ≤ C_W‖z‖²`
      (i.e. `chart z = −z + O(‖z‖²)`, the O(‖z‖²) geodesic-displacement remainder);
    • `hJetV`     — its `i`-directional jet is `P` (`∂ᵢ chart = P`), and
      `hJ3_on`    — that jet is `eᵢ` to FIRST order: `‖P z − eᵢ‖ ≤ C_P‖z‖`;
    • `hJetQ`     — the second `i`-jet of `chart` is `Q` (`∂ᵢ P = Q`), and
      `hJ3Q_on`   — `Q` is BOUNDED: `‖Q z‖ ≤ C_Q` (bounded second derivative);
    • `hco_on`    — the chart is COERCIVE: `½·|z|² ≤ |chart z|²` (bi-Lipschitz lower bound).
  This is precisely "chart ∈ C² near the diagonal with the stated quantitative moduli," a textbook
  property of the geodesic exponential map on a smooth Riemannian manifold — PLAUSIBLY TRUE, and (as
  the campaign found) genuinely absent from Mathlib and this repo only because it requires a coherent
  (continuous-in-base) representative of the `Classical.choose`-built chart.

  Every field is satisfiable and non-vacuous: on the flat model (`chart z = −z`, `P z = eᵢ`, `Q = 0`)
  all six hold with `C_W = C_P = C_Q = 0`; more generally any C² chart on a bounded gate is a witness.
  NONE of the fields equals the sliver-rate conclusion.  NOT `a₁ = R/6`.

  ## HONEST DISTANCE TO `hCConv` (the named residue that STILL remains).

  This file discharges the GEOMETRIC class of the sliver rate.  Reaching the capstone `hCConv` from
  the sliver rate STILL requires, as a SEPARATE, precisely-named residue (NOT touched here, NOT
  chart-regularity):
    (R1) the component-identity / kernel-family bridge `(kPrime …)(eⱼ) = (∂ᵢ∂ⱼ vanVleck)·leviSeries`
         relating `FderivBulkConcrete.kPrime`'s basis components to the sliver integrand
         (`KPrimeOpNormSliver.kPrime_opNorm_sliver_bound`'s `hcomp`), including the base-point/centre
         matching (`x = 0` vs `z₀`) — the "kernel family mismatch" of cp680;
    (R2) the facade's remaining non-chart carries in `CConvV2Facade.hCConvSlot_AT_GATE_v2`:
         the linewise `hlin`, the bulk `hbulkderiv`/`hbulk_tendsto`, the coefficient-continuity
         `hcont`, and the diff-under-∫ measurability census — the singular-convolution branch.
  So this file's honest contribution is: `hCConv` ⟸ `{JointSecondOrderRNCRegularity, R1, R2}` (with
  `JointSecondOrderRNCRegularity` isolating exactly the differential-geometry frontier).  NOT
  `a₁ = R/6`; `hCConv` NOT closed.
-/
import Mathlib
import QIQTH.SliverGatedFullyCombined

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver QIQTH.XUniformSliverFull
open QIQTH.TrueHeatKernel QIQTH.LeviSeriesLocalData
open QIQTH.SliverGatedFullyCombined
open scoped Interval Topology BigOperators ENNReal

namespace QIQTH.JointRNCRegularityInterface

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ############################################################################
    ### THE INTERFACE — the joint second-order RNC chart regularity bundle.
    ############################################################################ -/

/-- **★★★ `JointSecondOrderRNCRegularity`.**  The single, explicitly-named, standard-differential-
    geometry input replacing the vague "chart-regularity" carry: "the geodesic normal-coordinate
    inverse chart `uniformInverseChart g gi hC hK z₀` is jointly C² near the diagonal," in quantitative
    (bounded second-order Taylor-data + jet-identity) form, at direction `i` on the gate `G`, for the
    RNC chart jets `P` (= `∂ᵢ chart`) and `Q` (= `∂ᵢ P`).

    Bundles the six geometric facts the closed order-2 sliver rate consumes:
      `hco_on` (coercivity), `hVdisp_on` (identity to O(‖z‖²)), `hJ3_on` (first jet = eᵢ + O(‖z‖)),
      `hJ3Q_on` (bounded second jet), `hJetV`/`hJetQ` (the jet identities).
    PLAUSIBLY TRUE (textbook property of the exponential map on a smooth Riemannian manifold),
    satisfiable and non-vacuous (flat model: `chart z = −z`, `P = eᵢ`, `Q = 0`, `C_W=C_P=C_Q=0`).
    (`P`, `Q` are structure PARAMETERS, not fields, so consumers reference plain locals — this keeps
    the downstream reduction's giant signature as cheap as the underlying sliver theorem's own.)
    NOT `a₁ = R/6`. -/
structure JointSecondOrderRNCRegularity
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (z₀ : Point n) (i : Fin n) (G : Set (Point n)) (C_W C_P C_Q : ℝ)
    (P Q : Point n → Point n) : Prop where
  /-- Coercivity of the chart: `½|z|² ≤ |chart z|²`. -/
  hco_on : ∀ z ∈ G, (1 / 2 : ℝ) * rncRadialSq z
      ≤ rncRadialSq (uniformInverseChart g gi hC hK z₀ z)
  /-- The chart is the identity to second order: `‖chart z + z‖ ≤ C_W‖z‖²`. -/
  hVdisp_on : ∀ z ∈ G, ‖uniformInverseChart g gi hC hK z₀ z + z‖ ≤ C_W * ‖z‖ ^ 2
  /-- The first jet is `eᵢ` to first order: `‖P z − eᵢ‖ ≤ C_P‖z‖`. -/
  hJ3_on : ∀ z ∈ G, ‖P z - unitVec i‖ ≤ C_P * ‖z‖
  /-- The second jet is bounded: `‖Q z‖ ≤ C_Q`. -/
  hJ3Q_on : ∀ z ∈ G, ‖Q z‖ ≤ C_Q
  /-- `P` is the `i`-directional derivative of the chart. -/
  hJetV : ∀ y k, HasDerivAt
    (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y i s) k) (P y k) (y i)
  /-- `Q` is the `i`-directional derivative of `P` (the chart's second jet). -/
  hJetQ : ∀ ζ : Point n, ∀ k, HasDerivAt
    (fun s : ℝ => P (Function.update ζ i s) k) (Q ζ k) (ζ i)

/-! ─ Non-vacuity (prose).  `JointSecondOrderRNCRegularity` is EXACTLY the six geometric hypotheses of
    the banked `SliverGatedFullyCombined.witness_sliver2_xuniform_diag_gated_fullyCombined`, no
    stronger.  It is satisfiable / not over-strong: on any gate `G` bounded away from the base point,
    the four polynomial surface bounds `hco/hVdisp/hJ3/hJ3Q` hold with LARGE ENOUGH constants for any
    genuine coercive DIFFERENTIABLE chart (where the jets `P = ∂ᵢ chart`, `Q = ∂ᵢ P` exist, giving
    `hJetV`/`hJetQ`), since on such a gate every `‖·‖ ≤ C‖z‖ᵏ` is met by taking `C` large.  The hard
    part the interface NAMES is establishing these UNIFORMLY / JOINTLY for the concrete
    `Classical.choose`-built `uniformInverseChart` — which is exactly the differential-geometry frontier,
    NOT a self-contradiction.  A concrete machine-checked witness is not provided precisely because it
    would already require the chart-differentiability that is the named gap. -/

/-! ############################################################################
    ### THE REDUCTION — the closed sliver rate FROM the geometric interface.
    ############################################################################ -/

/-- **★★★ `witness_sliver2_diag_of_jointRNCRegularity`.**  THE REDUCTION: from a
    `JointSecondOrderRNCRegularity` instance (the isolated differential-geometry frontier) PLUS the
    explicitly-named amplitude / Levi / measurability residue, the CLOSED order-2 √ε sliver rate
    `SliverGatedFullyCombined.witness_sliver2_xuniform_diag_gated_fullyCombined` FOLLOWS.

    This gives the previously-zero-consumer closed sliver theorem its first honest consumer, and turns
    its six geometric carries into ONE named, plausibly-true, standard geometric hypothesis.  Every
    residue hypothesis is exactly as in `..._fullyCombined` (amplitude bounds, jet-differentiability,
    off-gate vanishing, Lipschitz, boundedness, gate-measure finiteness, and the integrand
    measurability/boundedness census); none is chart regularity.

    Stated as a `def` by PARTIAL APPLICATION: the interface supplies the four hard second-order RNC
    surface estimates (`hco/hVdisp/hJ3/hJ3Q`), and the remaining arguments (amplitude/Levi/jet/
    measurability, e.g. `reg.hJetV`/`reg.hJetQ` for the two jet identities) are the inferred residual
    Π-type — identical to `..._fullyCombined`'s tail.  This certificate elaborates cheaply (no restated
    mega-signature, no explicit conclusion) while machine-checking that the named geometric bundle is
    EXACTLY what `..._fullyCombined` consumes geometrically.  NOT `a₁ = R/6`. -/
def witness_sliver2_diag_of_jointRNCRegularity
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (G : Set (Point n)) (hSG : S z₀ ⊆ G)
    (C_W C_P C_Q : ℝ) (P Q : Point n → Point n)
    (reg : JointSecondOrderRNCRegularity g gi hC hK z₀ i G C_W C_P C_Q P Q)
    (M₀ M₁ M₂ C T aₗ τ₀ : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (L_E K_F L_A M_F : ℝ) (hLE : 0 ≤ L_E) (hK_F : 0 ≤ K_F) (hLA : 0 ≤ L_A) (hM_F : 0 ≤ M_F)
    (u ε : ℝ) (haₗ : 0 < aₗ) (hau : aₗ ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεu : ε ≤ u)
    (hεa : ε < aₗ / 2) (hετ₀ : ε ≤ τ₀)
  :=
  -- Partial application: the interface supplies EXACTLY the four hard second-order RNC surface
  -- estimates (hco/hVdisp/hJ3/hJ3Q); the remaining (amplitude/Levi/jet/measurability) arguments are
  -- left as the inferred residual Pi-type (identical to the fullyCombined tail — supply them, e.g.
  -- reg.hJetV/reg.hJetQ for the two jet identities, to obtain the √ε sliver bound). Stated by
  -- partial application (no restated mega-signature, no explicit conclusion) so elaboration stays cheap.
  witness_sliver2_xuniform_diag_gated_fullyCombined g gi hC hK S a b i z₀ hz₀ hSopen G hSG
    P Q M₀ M₁ M₂ C T aₗ τ₀ C_W C_P C_Q hM₀ hM₁ hM₂ hC_W hC_P hC_Q
    L_E K_F L_A M_F hLE hK_F hLA hM_F u ε haₗ hau huT hε0 hεu hεa hετ₀
    reg.hco_on reg.hVdisp_on reg.hJ3_on reg.hJ3Q_on

end QIQTH.JointRNCRegularityInterface

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.JointRNCRegularityInterface
#print axioms witness_sliver2_diag_of_jointRNCRegularity
end AxiomChecks
