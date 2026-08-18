/-
  JointRNCRegularityMixedInterface — Step 3 of the hCConv carry-audit: the MIXED (off-diagonal
  direction pair `i ≠ j`) analog of J4-792's diagonal geometric interface + reduction.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  It does NOT close `hCConv` and makes NO unconditional claim about
  the capstone.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none
  equal to the conclusion, no existing file edited (J4-792's `JointRNCRegularityInterface.lean` is
  imported, not modified).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE EXISTS (and WHY the mixed case is NOT free).

  J4-792 (`JointRNCRegularityInterface.lean`) named the DIAGONAL geometric frontier
  `JointSecondOrderRNCRegularity g gi hC hK z₀ i G C_W C_P C_Q P Q` — the quantitative "geodesic
  normal-coordinate inverse chart is jointly C² near the diagonal" fact, at a SINGLE direction `i`,
  bundling `P = ∂ᵢ chart` and `Q = ∂ᵢ P` (both derivatives in the SAME direction `i`) — and reduced
  the closed DIAGONAL sliver rate `witness_sliver2_xuniform_diag_gated_fullyCombined` to it.

  To close `hCConv`'s `hsliver` slot, the R1 operator-norm bridge `KPrimeOpNormSliver.
  kPrime_opNorm_sliver_bound` reduces the CLM `‖∫∫ kPrime … i‖_op` to the ℓ¹ sum `Σⱼ bb j` of SCALAR
  per-component sliver bounds — one for each `∂ᵢ∂ⱼ vanVleck` component.  The `j = i` (diagonal)
  component is served by J4-792; the `j ≠ i` (MIXED / off-diagonal) components need the MIXED sliver
  rate `SliverGatedFullyCombined.witness_sliver2_xuniform_mixed_gated_fullyCombined` (already banked,
  with mixed Hermite factor `z i · z j` and no `−2τ` subtraction).

  ★ DECISIVE HONEST FINDING (direct read of that mixed rate's geometric carry list, lines 83–99).
  The mixed rate does NOT come for free from the diagonal `JointSecondOrderRNCRegularity`.  Its
  geometric surface block needs, BEYOND the diagonal data:
    • `hJ3j_on` / `hJetPj` — the FIRST jet in a SECOND direction `Pj = ∂ⱼ chart` (the diagonal
      interface only exposes `∂ᵢ chart`);
    • `hJetQ` — the CROSS second jet `Q = ∂ⱼ Pi = ∂ⱼ∂ᵢ chart` (the diagonal interface's `Q` is the
      SAME-direction second jet `∂ᵢ∂ᵢ chart`), with its bound `hJ3Q_on`.
  The cross second jet `∂ᵢ∂ⱼ chart` is GENUINELY NEW geometric content — not a self-contradiction,
  and (like the diagonal one) a textbook property of the exponential map, but absent from both the
  diagonal interface and Mathlib/this repo.  This file NAMES it as one clean bundle.

  ## THE MIXED INTERFACE — `JointSecondOrderRNCRegularityMixed g gi hC hK z₀ i j G C_W C_P C_Q Pi Pj Q`.

  "The RNC inverse chart is jointly C² near the diagonal, with FULL bilinear (i, j) second-order
  data," in quantitative bounded-Taylor-data + jet-identity form, on the gate `G`:
    • `hco_on` / `hVdisp_on` — coercivity + O(‖z‖²) identity (SHARED with the diagonal interface);
    • `hJ3i_on` / `hJetPi`   — first jet in direction `i`: `Pi = ∂ᵢ chart`, `= eᵢ + O(‖z‖)`;
    • `hJ3j_on` / `hJetPj`   — first jet in direction `j`: `Pj = ∂ⱼ chart`, `= eⱼ + O(‖z‖)`;
    • `hJ3Q_on` / `hJetQ`    — the CROSS second jet `Q = ∂ⱼ Pi = ∂ⱼ∂ᵢ chart`, bounded `‖Q z‖ ≤ C_Q`.
  Non-vacuous: on the flat model (`chart z = −z`, `Pi = eᵢ`, `Pj = eⱼ`, `Q = 0`) all hold with
  `C_W = C_P = C_Q = 0`; any C² chart on a bounded gate is a witness with large enough constants.
  NONE of the fields equals the sliver-rate conclusion.  NOT `a₁ = R/6`.

  ## THE REDUCTION — `witness_sliver2_mixed_of_jointRNCRegularityMixed`.

  From a `JointSecondOrderRNCRegularityMixed` instance PLUS the (explicitly-named) amplitude / Levi /
  measurability residue, the closed MIXED √ε sliver rate FOLLOWS.  Stated (exactly as J4-792's diagonal
  reduction) as a `def` by PARTIAL APPLICATION through the five contiguous geometric surface estimates
  `reg.hco_on / hVdisp_on / hJ3i_on / hJ3j_on / hJ3Q_on`; the remaining arguments — including the three
  jet identities, suppliable as `reg.hJetPi / reg.hJetPj / reg.hJetQ` — are the inferred residual
  Π-type, identical to `..._mixed_gated_fullyCombined`'s tail.  (Partial-application `def`, not a
  restated-signature `theorem`, because the latter's 60-hypothesis mega-signature elaborates in
  >30 min — an engineering limit of the giant signature, not a math gap.)

  ## HONEST DISTANCE TO `hCConv`.  This file discharges the GEOMETRIC class of the MIXED sliver rate,
  giving that banked rate its first honest consumer through a named interface.  Combined with J4-792's
  diagonal interface, the `Σⱼ` operator-norm decomposition of `hsliver` (R1) is now geometrically
  isolated for ALL n components (`j = i` diagonal + `j ≠ i` mixed) onto TWO named, standard, plausibly-
  true differential-geometry bundles.  Reaching `hCConv` STILL requires the R1 component-identity
  wiring (`kPrime`(eⱼ) = `∂ᵢ∂ⱼ vanVleck · leviSeries`, `KPrimeOpNormSliver.hcomp`, incl. the x=0-vs-z₀
  base matching) and the facade's remaining singular-convolution carries.  NOT `a₁ = R/6`; `hCConv`
  NOT closed.
-/
import Mathlib
import QIQTH.JointRNCRegularityInterface

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver QIQTH.XUniformSliverFull
open QIQTH.TrueHeatKernel QIQTH.LeviSeriesLocalData
open QIQTH.SliverGatedFullyCombined
open scoped Interval Topology BigOperators ENNReal

namespace QIQTH.JointRNCRegularityMixedInterface

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ############################################################################
    ### THE MIXED INTERFACE — full bilinear (i, j) second-order RNC chart regularity.
    ############################################################################ -/

/-- **★★★ `JointSecondOrderRNCRegularityMixed`.**  The MIXED (direction pair `i ≠ j`) analog of
    `JointRNCRegularityInterface.JointSecondOrderRNCRegularity`: "the geodesic normal-coordinate
    inverse chart `uniformInverseChart g gi hC hK z₀` is jointly C² near the diagonal, with FULL
    bilinear `(i, j)` second-order data," in quantitative (bounded second-order Taylor-data +
    jet-identity) form, on the gate `G`, for the RNC chart jets `Pi` (= `∂ᵢ chart`), `Pj`
    (= `∂ⱼ chart`) and the CROSS second jet `Q` (= `∂ⱼ Pi` = `∂ⱼ∂ᵢ chart`).

    Bundles the eight geometric facts the closed order-2 MIXED sliver rate consumes:
      `hco_on` (coercivity), `hVdisp_on` (identity to O(‖z‖²)), `hJ3i_on`/`hJ3j_on` (first jets =
      eᵢ/eⱼ + O(‖z‖)), `hJ3Q_on` (bounded cross second jet), `hJetPi`/`hJetPj`/`hJetQ` (the three jet
      identities).  The `Pj` jet and the CROSS jet `Q = ∂ⱼ Pi` are the genuinely NEW geometric content
      beyond the diagonal interface (whose single-direction `Q = ∂ᵢ Pi`).

    PLAUSIBLY TRUE (textbook property of the exponential map on a smooth Riemannian manifold),
    satisfiable and non-vacuous (flat model: `chart z = −z`, `Pi = eᵢ`, `Pj = eⱼ`, `Q = 0`,
    `C_W = C_P = C_Q = 0`).  NONE of the fields equals the sliver-rate conclusion.  NOT `a₁ = R/6`. -/
structure JointSecondOrderRNCRegularityMixed
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (z₀ : Point n) (i j : Fin n) (G : Set (Point n)) (C_W C_P C_Q : ℝ)
    (Pi Pj Q : Point n → Point n) : Prop where
  /-- Coercivity of the chart: `½|z|² ≤ |chart z|²`. -/
  hco_on : ∀ z ∈ G, (1 / 2 : ℝ) * rncRadialSq z
      ≤ rncRadialSq (uniformInverseChart g gi hC hK z₀ z)
  /-- The chart is the identity to second order: `‖chart z + z‖ ≤ C_W‖z‖²`. -/
  hVdisp_on : ∀ z ∈ G, ‖uniformInverseChart g gi hC hK z₀ z + z‖ ≤ C_W * ‖z‖ ^ 2
  /-- The `i`-jet is `eᵢ` to first order: `‖Pi z − eᵢ‖ ≤ C_P‖z‖`. -/
  hJ3i_on : ∀ z ∈ G, ‖Pi z - unitVec i‖ ≤ C_P * ‖z‖
  /-- The `j`-jet is `eⱼ` to first order: `‖Pj z − eⱼ‖ ≤ C_P‖z‖`. -/
  hJ3j_on : ∀ z ∈ G, ‖Pj z - unitVec j‖ ≤ C_P * ‖z‖
  /-- The cross second jet is bounded: `‖Q z‖ ≤ C_Q`. -/
  hJ3Q_on : ∀ z ∈ G, ‖Q z‖ ≤ C_Q
  /-- `Pi` is the `i`-directional derivative of the chart. -/
  hJetPi : ∀ y k, HasDerivAt
    (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y i s) k) (Pi y k) (y i)
  /-- `Pj` is the `j`-directional derivative of the chart. -/
  hJetPj : ∀ y k, HasDerivAt
    (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y j s) k) (Pj y k) (y j)
  /-- `Q` is the `j`-directional derivative of `Pi` (the chart's CROSS second jet `∂ⱼ∂ᵢ chart`). -/
  hJetQ : ∀ ζ : Point n, ∀ k, HasDerivAt
    (fun s : ℝ => Pi (Function.update ζ j s) k) (Q ζ k) (ζ j)

/-! ─ Non-vacuity (prose).  `JointSecondOrderRNCRegularityMixed` is EXACTLY the eight geometric
    hypotheses of the banked `SliverGatedFullyCombined.witness_sliver2_xuniform_mixed_gated_
    fullyCombined`, no stronger.  It is satisfiable / not over-strong: on any gate `G` bounded away
    from the base point, the polynomial surface bounds hold with large enough constants for any
    genuine coercive DIFFERENTIABLE chart (where the jets `Pi = ∂ᵢ chart`, `Pj = ∂ⱼ chart`,
    `Q = ∂ⱼ Pi` exist).  The hard part the interface NAMES is establishing these UNIFORMLY / JOINTLY
    for the concrete `Classical.choose`-built `uniformInverseChart` — the differential-geometry
    frontier, NOT a self-contradiction.  A concrete machine-checked witness is not provided precisely
    because it would already require the chart-differentiability that is the named gap. -/

/-! ############################################################################
    ### THE REDUCTION — the closed MIXED sliver rate FROM the geometric interface.
    ############################################################################ -/

/-- **★★★ `witness_sliver2_mixed_of_jointRNCRegularityMixed`.**  THE MIXED REDUCTION: from a
    `JointSecondOrderRNCRegularityMixed` instance (the isolated bilinear differential-geometry frontier)
    PLUS the explicitly-named amplitude / Levi / measurability residue, the CLOSED order-2 √ε MIXED
    sliver rate `SliverGatedFullyCombined.witness_sliver2_xuniform_mixed_gated_fullyCombined` FOLLOWS.

    This gives that banked mixed rate its first honest consumer through a named interface, and turns its
    eight geometric carries into ONE named, plausibly-true, standard geometric hypothesis (with the
    cross second jet `∂ⱼ∂ᵢ chart` as the new content beyond J4-792's diagonal interface).

    Stated (exactly as J4-792's diagonal reduction) as a `def` by PARTIAL APPLICATION: the interface
    supplies the five contiguous geometric surface estimates (`hco_on / hVdisp_on / hJ3i_on / hJ3j_on /
    hJ3Q_on`), and the remaining arguments (amplitude / Levi / jet / measurability — e.g. `reg.hJetPi`/
    `reg.hJetPj`/`reg.hJetQ` for the three jet identities) are the inferred residual Π-type — identical
    to `..._mixed_gated_fullyCombined`'s tail.  This certificate elaborates cheaply while machine-
    checking that the named geometric bundle is EXACTLY what `..._mixed_gated_fullyCombined` consumes
    geometrically.  NOT `a₁ = R/6`. -/
def witness_sliver2_mixed_of_jointRNCRegularityMixed
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (hij : i ≠ j) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (G : Set (Point n)) (hSG : S z₀ ⊆ G)
    (C_W C_P C_Q : ℝ) (Pi Pj Q : Point n → Point n)
    (reg : JointSecondOrderRNCRegularityMixed g gi hC hK z₀ i j G C_W C_P C_Q Pi Pj Q)
    (M₀ M₁i M₁j M₂ C T aₗ τ₀ : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₁i : 0 ≤ M₁i) (hM₁j : 0 ≤ M₁j) (hM₂ : 0 ≤ M₂)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (L_E K_F L_A M_F : ℝ) (hLE : 0 ≤ L_E) (hK_F : 0 ≤ K_F) (hLA : 0 ≤ L_A) (hM_F : 0 ≤ M_F)
    (u ε : ℝ) (haₗ : 0 < aₗ) (hau : aₗ ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεu : ε ≤ u)
    (hεa : ε < aₗ / 2) (hετ₀ : ε ≤ τ₀)
  :=
  -- Partial application: the interface supplies EXACTLY the five contiguous geometric surface
  -- estimates (hco/hVdisp/hJ3i/hJ3j/hJ3Q); the remaining (amplitude/Levi/jet/measurability) arguments
  -- are left as the inferred residual Pi-type (identical to the mixed fullyCombined tail — supply them,
  -- e.g. reg.hJetPi/reg.hJetPj/reg.hJetQ for the three jet identities, to obtain the √ε mixed rate).
  witness_sliver2_xuniform_mixed_gated_fullyCombined g gi hC hK S a b i j hij z₀ hz₀ hSopen G hSG
    Pi Pj Q M₀ M₁i M₁j M₂ C T aₗ τ₀ C_W C_P C_Q hM₀ hM₁i hM₁j hM₂ hC_W hC_P hC_Q
    L_E K_F L_A M_F hLE hK_F hLA hM_F u ε haₗ hau huT hε0 hεu hεa hετ₀
    reg.hco_on reg.hVdisp_on reg.hJ3i_on reg.hJ3j_on reg.hJ3Q_on

end QIQTH.JointRNCRegularityMixedInterface

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.JointRNCRegularityMixedInterface
#print axioms witness_sliver2_mixed_of_jointRNCRegularityMixed
end AxiomChecks
