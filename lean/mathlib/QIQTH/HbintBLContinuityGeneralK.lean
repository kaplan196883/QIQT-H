/-
  HbintBLContinuityGeneralK — the GENERAL-`K` discharge of the `BL`-continuity elementary carry of the
  J4-907/J4-983 interior tube-cover `hbint` route, for the CONCRETE downstream weight shape
  `BL s z := CB s · gaussDdim (2·s) z` (the width-`2s` Levi envelope shape actually instantiated at
  `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries`, J4-913 §1).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (cp1001's correction).  `HbintRequant.hbint_interior_via_tube_cover_requant` (R6) reduces the
  tube-cover `hbint` integrability, for a GENERAL compact `K` (not merely the degenerate singleton
  `K = {0}` of `HbintFullyClosedCurved`), to exactly TWO elementary carries:
    • `hBLK`  : `∀ᵐ s, s ∈ uIoc 0 (t−εₘ) → ContinuousOn (BL s) K`
    • `hbnd`  : `∀ᵐ s, s ∈ uIoc 0 (t−εₘ) → ∃ C, ∀ z ∈ K, ‖BL s z · (⨆ …)‖ ≤ C`
  `HbintFullyClosedCurved` discharges BOTH at `K = {0}` via singleton-topology triviality
  (`continuousOn_singleton`; boundedness by the value at the point) — a mechanism that is SPECIFIC to
  the degenerate singleton and does NOT generalize to a genuinely-curved, positive-measure `K`.

  ## THE GENUINE GENERAL-`K` PIECE — `hBLK` closes UNCONDITIONALLY for the CONCRETE `BL` shape.

  `BL`, as an ABSTRACT parameter of R6, cannot be continuous on a general `K` for free — continuity is a
  genuine hypothesis on an arbitrary function.  But `BL` is NOT abstract at the point `hbint` is actually
  consumed: `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries` (J4-913) instantiates it CONCRETELY as
  `BL s z := CB s · gaussDdim (2·s) z`, where `gaussDdim` is the `d`-dimensional heat Gaussian.  The
  banked lemma `FlowJointRegularity.gaussDdim_cont (t : ℝ) : Continuous (fun x => gaussDdim t x)` is
  UNCONDITIONAL — continuous in the spatial variable for EVERY fixed width `t`, no positivity
  side-condition, no compactness, no chart data, no dependence on `K` at all.  Hence, for this concrete
  `BL`, `ContinuousOn (BL s) K` holds for EVERY `s` (not merely a.e.) and EVERY set `K` (not merely a
  singleton) — a real, non-degenerate discharge of the `hBLK` carry for genuinely-curved positive-measure
  `K`.

  This file: (1) proves that unconditional discharge; (2) specializes R6 to the concrete `BL` shape,
  showing the tube-cover `hbint` route for THIS `BL` now depends on exactly ONE remaining elementary
  carry — `hbnd` — instead of two.

  ## THE HONEST RESIDUAL — `hbnd` remains open for general `K` (per gpt-5.6-sol consultation, 2026-08-23).

  `hbnd` needs a SINGLE constant `C` bounding `BL(s,z)·BF(s,z)` UNIFORMLY over ALL `z ∈ K` (not a.e. `z`,
  not with a `z`-dependent constant), where `BF s z := ⨆ x, ‖fderiv … x‖`.  The existing machinery that
  discharges the structurally similar `hFd` sup-boundedness carry
  (`HFdRequant.hFd_ciSup_of_coreCont_requant` / `hgate_coreCont_requant`) only produces an A.E.-`z`,
  `z`-DEPENDENT bound (`∀ᵐ z, BddAbove (…)`) — strictly weaker than what `hbnd` needs.  Upgrading to a
  `K`-uniform bound would need `z ↦ BF(z)` continuous on ALL of `K` (not just `interior K`); the banked
  joint-continuity lemma feeding it, `HbintInteriorTubeCoverRoute.interiorFieldHessianNorm_continuousOn`,
  is proved ONLY on `interior K ×ˢ concreteKx(b)`, because its own inputs (`generalCenter_chartC2_tube`
  via `uniformInverseChart_jointContDiffAt_generalCenter`) are quantified `∀ z₀ ∈ interior K` for their
  chart-openness argument, NOT `∀ z₀ ∈ K`.  This does not extend to boundary points of `K` without new
  analytic content (chart/Hessian estimates uniform up to the boundary, or an explicit integrable
  majorant) — a genuine architectural gap, NOT a bookkeeping requantification, confirmed via
  `mcp__OpenAI__ask` (`gpt-5.6-sol`, high effort) before this file was written.  `hbnd`, `hmeas`, and
  `hBFpeak` all remain OPEN for `fb`'s genuine closure.

  ⚠ HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  ONLY the `hBLK` half of ONE `hbint` sub-route's two elementary carries, for the concrete downstream
  `BL` shape, at GENERAL `K`.  It does NOT close `hbint` itself (that needs `hbnd` too), does NOT close
  `hmeas` or `hBFpeak`, and does NOT touch `hDuhamel`/`hDConv`.  `a₁ = R/6` remains STRICTLY CONDITIONAL
  on {hDuhamel, hDConv, hCConv}.  No existing file is edited; no `sorry`, no new axioms, no `:= True`.
-/
import Mathlib
import QIQTH.HbintRequant
import QIQTH.FlowJointRegularity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HbintRequant
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.HbintBLContinuityGeneralK

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — the concrete `BL` weight is globally continuous, UNCONDITIONALLY.
    ############################################################################### -/

/-- **★ `concreteBL_continuous`.**  The downstream Levi-envelope weight `BL s z := CB s · gaussDdim
    (2s) z` (`MixedEnvelopeAssembly` J4-913 §1 shape) is CONTINUOUS in `z`, for every fixed `s` — a
    direct consequence of the UNCONDITIONAL `gaussDdim_cont`, no positivity/compactness/chart side
    conditions.  NOT `a₁ = R/6`. -/
theorem concreteBL_continuous (CB : ℝ → ℝ) (s : ℝ) :
    Continuous (fun z : Point n => CB s * gaussDdim (2 * s) z) :=
  continuous_const.mul (gaussDdim_cont (2 * s))

/-- **★★ `hBLK_concreteBL_generalK`.**  The `hBLK` elementary carry of R6
    (`HbintRequant.hbint_interior_via_tube_cover_requant`), for the concrete weight `BL := CB ·
    gaussDdim(2·)`, discharged UNCONDITIONALLY for ANY set `K` (not merely the degenerate singleton
    `K = {0}`) and EVERY `s` (not merely a.e.) — the weight's continuity is global and has no dependence
    on `K` whatsoever.  NOT `a₁ = R/6`. -/
theorem hBLK_concreteBL_generalK (K : Set (Point n)) (CB : ℝ → ℝ) (t : ℝ) (m : ℕ) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ContinuousOn (fun z : Point n => CB s * gaussDdim (2 * s) z) K :=
  ae_of_all volume (fun s _ => (concreteBL_continuous CB s).continuousOn)

/-! ###############################################################################
    ### §2 — R6 specialized to the concrete `BL`: down to ONE remaining carry (`hbnd`).
    ############################################################################### -/

/-- **★★★ `hbint_interior_via_tube_cover_requant_concreteBL`.**  `HbintRequant.hbint_interior_via_tube_cover_requant`
    (R6) specialized at the concrete downstream weight `BL := CB · gaussDdim(2·)` — the shape actually
    instantiated by `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries`.  Since `hBLK` is now
    UNCONDITIONALLY discharged for this `BL` at ANY compact `K` (`hBLK_concreteBL_generalK`), the
    tube-cover `hbint` route for this `BL` depends on exactly ONE remaining elementary carry — `hbnd`,
    the `K`-uniform sup-bound — rather than two.  `hbnd` itself is NOT discharged here (see the file
    docstring: it is a genuine architectural gap for general `K`, confirmed via `gpt-5.6-sol`
    consultation, distinct from and strictly harder than the closed `hFd` carry).  NOT `a₁ = R/6`. -/
theorem hbint_interior_via_tube_cover_requant_concreteBL
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (i : Fin n) (t : ℝ) (m : ℕ)
    (CB : ℝ → ℝ) (hnull : volume (frontier K) = 0)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ r₀ > (0 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b →
      b < uniformFlowRadius g gi hC hK →
      ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        b < r₀ →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∃ C : ℝ, ∀ z ∈ K, ‖(CB s * gaussDdim (2 * s) z) *
              (⨆ x : Point n,
                ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)‖ ≤ C) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          Integrable (fun z => (CB s * gaussDdim (2 * s) z) *
            (⨆ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume := by
  obtain ⟨r₀, hr₀, δ₀, hδ₀, hR6⟩ :=
    hbint_interior_via_tube_cover_requant g gi hC hK hKne i t m
      (fun s z => CB s * gaussDdim (2 * s) z) hnull hw
  refine ⟨r₀, hr₀, δ₀, hδ₀, ?_⟩
  intro a b ha hab hbρ c hbc hcδ S hS hbr₀ hbnd
  exact hR6 a b ha hab hbρ c hbc hcδ S hS hbr₀ (hBLK_concreteBL_generalK K CB t m) hbnd

end QIQTH.HbintBLContinuityGeneralK

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HbintBLContinuityGeneralK
#print axioms concreteBL_continuous
#print axioms hBLK_concreteBL_generalK
#print axioms hbint_interior_via_tube_cover_requant_concreteBL
end AxiomChecks
