/-
  TruncatedDuhamelData — J4-210 (Sol final plan Ph8): THE `TruncatedDuhamelData` FACADE.

  A PACKAGING brick.  It does NOT reprove any analysis and proves NOTHING about `R/6`.  It only
  gives SEMANTIC STRUCTURE to the flat "Levi/Duhamel interface" cluster of hypothesis slots that the
  `∞`-capstone `CConvConcreteThreading.a1_R6_of_residue_inf_v5` (and its threaded sibling
  `HDConvThreading.a1_R6_of_residue_inf_v6`) carries — bundling those verbatim slots into four
  `: Prop` data structures + adapters, mirroring the `CConvFacade` (J4-183) five-bundle style.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  THE FLAT SLOT BEING PACKAGED — the Levi/Duhamel interface of the capstone (v5, VERBATIM;
  identical in v6).  With `Wit := vanVleckGatedWitness g gi hChr hK S a b` these are, in order:

    (hEboundW_le) ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi Wit τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q
    (hInt)        IterConvIntegrableW (heatOp g gi Wit) 2 0 C
    (hDuhamel)    heatOp g gi (fun u p q => heatConv Wit (leviSeries (heatOp g gi Wit)) u p q) t 0 0
                    = leviSeries (heatOp g gi Wit) t 0 0
                      + heatConv (heatOp g gi Wit) (leviSeries (heatOp g gi Wit)) t 0 0
    (hInter)      heatConv (heatOp g gi Wit) (leviSeries (heatOp g gi Wit)) t 0 0
                    = ∑' k : ℕ, heatConv (heatOp g gi Wit)
                        (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi Wit) (k + 1) τ p q)
                        t 0 0
    (hDConv)      DifferentiableAt ℝ
                    (fun u => heatConv Wit (leviSeries (heatOp g gi Wit)) u 0 0) t

  The AxiomAudit calls `hDuhamel` "the net ~40-hypothesis" slot: it is a single algebraic identity
  in the capstone, but its DISCHARGE unfolds to ~40 analytic facts (the true-kernel limit family).

  ─────────────────────────────────────────────────────────────────────────────────────────────
  THE FOUR SEMANTIC BUNDLES (Sol recipe).  Each field = ONE capstone slot, VERBATIM shape:

    • `TruncatedDuhamelCore`  — hDuhamel  (the truncated-Duhamel algebraic identity).
    • `BulkLimitData`         — hDConv    (the bulk/interior time-differentiability limit).
    • `EndpointData`          — hEboundW_le + hInt  (endpoint envelope bound + integrability).
    • `InterchangeData`       — hInter    (the tsum·heatConv integral-interchange fact).

  FIREWALL.  No field is `True`, vacuous, or the capstone conclusion `a₁ = R/6`
  (= a `trueHeatKernel`-diagonal statement, which appears nowhere here).  Every field is a
  strictly-lower analytic INGREDIENT.  Bundles are parameterized by an ABSTRACT kernel `Wit`; the
  residual operator is the concrete `heatOp g gi Wit`, so instantiating `Wit := vanVleckGatedWitness …`
  reproduces the v5/v6 slots up to `rfl`.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  PROVIDER STATUS PER BUNDLE FIELD (honest; BANKED = wired here / BANKED* = provider exists but not
  re-plumbed here / DATA = satisfiable analytic fact / WALL = genuine hard content):

    • TruncatedDuhamelCore.hIdentity  — BANKED  (`truncatedDuhamelCore_of_daLim`, wraps
        `HeatResidualBound.hDuhamel_leviSeries_of_daLim`; residue = 3 truncation-limit DATA facts
        `hBoundaryLim`/`hDaLim`/`hDerivConv`, the last resting on the `hDaLimLU` loc-unif WALL).
    • InterchangeData.hSeries         — BANKED  (`interchangeData_of_banked`, wraps
        `HeatResidualBound.heatConv_leviSeries_interchange`; residue = `{C, hC, hEbound(∀τ>0),
        hEzero, hEmeas, ht}`, all DATA — dominated-convergence interchange, no wall).
    • EndpointData.hEbound            — DATA    (geometric envelope; banked producer
        `EboundWiringHD1.hEboundW_from_geometry`; taken as input of `endpointData_of_banked`).
    • EndpointData.hIntegrable        — BANKED  (inside `endpointData_of_banked`, via
        `HeatResidualBound.iterConvIntegrableW_of_bound_baseMeas` from the same envelope bound).
    • BulkLimitData.hDiff             — BANKED* (`HDConvThreading.hDConv_from_banked`; NOT re-plumbed
        here — its residue is the large near-diagonal ODE / sliver family, out of scope for this
        thin facade.  Left as an explicit hypothesis of `BulkLimitData`; SAID SO here.)

  NOTE ON `hDuhamel_of_truncatedData`.  It depends ONLY on `TruncatedDuhamelCore` — the hDuhamel
  identity is exactly the Core field, and injecting the sibling bundles as arguments it does not use
  would be a fake dependency (firewall).  The genuine four-bundle assembly that feeds the capstone is
  `duhamelInterface_of_truncatedData`, which produces the full 5-slot conjunction, all bundles
  load-bearing.

  ⚠ STILL NOT `a₁ = R/6`.  This file only re-groups + re-plumbs banked/analytic ingredients.
-/
import QIQTH.DuhamelLimitWiring
import QIQTH.LeviInterchange

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound QIQTH.LaplaceBeltrami
open scoped BigOperators Topology

namespace QIQTH.TruncatedDuhamelData

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### THE FOUR `: Prop` DATA BUNDLES (fields = VERBATIM capstone slot shapes).
    ############################################################################### -/

/-- **`TruncatedDuhamelCore`.**  The truncated-Duhamel algebraic identity — the `hDuhamel` slot of
    `CConvConcreteThreading.a1_R6_of_residue_inf_v5` (identical in v6).  `Wit` is the abstract kernel;
    the residual operator is `heatOp g gi Wit`.  The single field is the exact identity
    `heatOp g gi (H*F) = F + E*F` at `t, 0, 0`. -/
structure TruncatedDuhamelCore (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t : ℝ) : Prop where
  /-- Feeds the capstone `hDuhamel` slot VERBATIM. -/
  hIdentity :
    heatOp g gi (fun u p q => heatConv Wit (leviSeries (heatOp g gi Wit)) u p q) t 0 0
      = leviSeries (heatOp g gi Wit) t 0 0
        + heatConv (heatOp g gi Wit) (leviSeries (heatOp g gi Wit)) t 0 0

/-- **`BulkLimitData`.**  The bulk/interior limit datum — the `hDConv` slot of the v5 capstone: the
    outer-time differentiability of the heat convolution at `t`.  (This is the truncation→full /
    interior limit surviving as a differentiability fact.)  Banked producer:
    `HDConvThreading.hDConv_from_banked` (not re-plumbed here — its residue is the large near-diagonal
    ODE family; see file header). -/
structure BulkLimitData (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t : ℝ) : Prop where
  /-- Feeds the capstone `hDConv` slot VERBATIM. -/
  hDiff :
    DifferentiableAt ℝ (fun u => heatConv Wit (leviSeries (heatOp g gi Wit)) u 0 0) t

/-- **`EndpointData`.**  The endpoint/boundary behaviour of the residual operator: the time-endpoint
    Gaussian envelope bound `hEbound` (the `hEboundW_le` slot) and the iterated-convolution
    integrability `hIntegrable` (the `hInt` slot) of the v5 capstone.  Fields VERBATIM. -/
structure EndpointData (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t C : ℝ) : Prop where
  /-- Feeds the capstone `hEboundW_le` slot VERBATIM. -/
  hEbound : ∀ τ p q, 0 < τ → τ ≤ t →
    |heatOp g gi Wit τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q
  /-- Feeds the capstone `hInt` slot VERBATIM. -/
  hIntegrable : IterConvIntegrableW (heatOp g gi Wit) (2 : ℝ) (0 : ℝ) C

/-- **`InterchangeData`.**  The integral-interchange fact — the `hInter` slot of the v5 capstone:
    the heat convolution against the Levi series equals the term-by-term series over the signed
    iterated kernels.  Field VERBATIM. -/
structure InterchangeData (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t : ℝ) : Prop where
  /-- Feeds the capstone `hInter` slot VERBATIM. -/
  hSeries :
    heatConv (heatOp g gi Wit) (leviSeries (heatOp g gi Wit)) t 0 0
      = ∑' k : ℕ, heatConv (heatOp g gi Wit)
          (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi Wit) (k + 1) τ p q) t 0 0

/-! ###############################################################################
    ### THE ADAPTERS — re-plumbing the bundles into the exact capstone slots.
    ############################################################################### -/

/-- **`hDuhamel_of_truncatedData`.**  The adapter producing EXACTLY the v5/v6 `hDuhamel` slot
    proposition, from the `TruncatedDuhamelCore` bundle.  Pure projection (defeq-level).  Depends
    only on `Core`: the identity IS the Core field, and taking the sibling bundles it does not use
    would be a fake dependency (firewall).  The four-bundle capstone-feeding assembly is
    `duhamelInterface_of_truncatedData`.  NOT `a₁ = R/6`. -/
theorem hDuhamel_of_truncatedData (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (core : TruncatedDuhamelCore g gi Wit t) :
    heatOp g gi (fun u p q => heatConv Wit (leviSeries (heatOp g gi Wit)) u p q) t 0 0
      = leviSeries (heatOp g gi Wit) t 0 0
        + heatConv (heatOp g gi Wit) (leviSeries (heatOp g gi Wit)) t 0 0 :=
  core.hIdentity

/-- **★ `duhamelInterface_of_truncatedData`.**  The genuine four-bundle assembly: from the four
    `: Prop` bundles it produces the FULL Levi/Duhamel-interface conjunction the `∞`-capstone consumes
    — the five v5/v6 slots `hEboundW_le ∧ hInt ∧ hDuhamel ∧ hInter ∧ hDConv`, VERBATIM.  Every bundle
    is load-bearing.  Pure re-plumbing (defeq-level projection).  NOT `a₁ = R/6`. -/
theorem duhamelInterface_of_truncatedData (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t C : ℝ)
    (core : TruncatedDuhamelCore g gi Wit t)
    (bulk : BulkLimitData g gi Wit t)
    (endpoint : EndpointData g gi Wit t C)
    (inter : InterchangeData g gi Wit t) :
    (∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi Wit τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    ∧ IterConvIntegrableW (heatOp g gi Wit) (2 : ℝ) (0 : ℝ) C
    ∧ (heatOp g gi (fun u p q => heatConv Wit (leviSeries (heatOp g gi Wit)) u p q) t 0 0
        = leviSeries (heatOp g gi Wit) t 0 0
          + heatConv (heatOp g gi Wit) (leviSeries (heatOp g gi Wit)) t 0 0)
    ∧ (heatConv (heatOp g gi Wit) (leviSeries (heatOp g gi Wit)) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi Wit)
            (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi Wit) (k + 1) τ p q) t 0 0)
    ∧ DifferentiableAt ℝ (fun u => heatConv Wit (leviSeries (heatOp g gi Wit)) u 0 0) t :=
  ⟨endpoint.hEbound, endpoint.hIntegrable, core.hIdentity, inter.hSeries, bulk.hDiff⟩

/-! ###############################################################################
    ### CONCRETE PROVIDERS — populating bundle fields from banked machinery.
    ############################################################################### -/

/-- **`truncatedDuhamelCore_of_daLim`.**  Builds `TruncatedDuhamelCore` from the three
    truncation-limit facts consumed by `HeatResidualBound.hDuhamel_leviSeries_of_daLim` (J4-122): the
    boundary limit, the `Da`-limit and the derivative-of-convolution limit.  Genuine composition — the
    Core field IS that banked theorem's conclusion.  The three inputs are analytic DATA (`hDaLim`
    rests on the loc-unif `hDaLimLU` limit, the sole hard content).  NOT `a₁ = R/6`. -/
theorem truncatedDuhamelCore_of_daLim (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (hBoundaryLim : Filter.Tendsto
        (fun m => BoundaryTrunc Wit (leviSeries (heatOp g gi Wit)) m t) Filter.atTop
        (𝓝 (leviSeries (heatOp g gi Wit) t 0 0)))
    (hDaLim : Filter.Tendsto
        (fun m => DaTrunc Wit (leviSeries (heatOp g gi Wit)) m t) Filter.atTop
        (𝓝 (laplaceBeltrami g gi
                (fun x => heatConv Wit (leviSeries (heatOp g gi Wit)) t x 0) 0
              + heatConv (heatOp g gi Wit) (leviSeries (heatOp g gi Wit)) t 0 0)))
    (hDerivConv : Filter.Tendsto
        (fun m => DaTrunc Wit (leviSeries (heatOp g gi Wit)) m t
          + BoundaryTrunc Wit (leviSeries (heatOp g gi Wit)) m t) Filter.atTop
        (𝓝 (deriv (fun u => heatConv Wit (leviSeries (heatOp g gi Wit)) u 0 0) t))) :
    TruncatedDuhamelCore g gi Wit t :=
  ⟨hDuhamel_leviSeries_of_daLim g gi Wit t hBoundaryLim hDaLim hDerivConv⟩

/-- **`interchangeData_of_banked`.**  Builds `InterchangeData` from
    `HeatResidualBound.heatConv_leviSeries_interchange` (J4-131) at the residual operator
    `E := heatOp g gi Wit` and diagonal `x = y = 0`.  Genuine composition — the residue
    `{C, hC, hEbound, hEzero, hEmeas, ht}` is all satisfiable analytic DATA (the dominated-convergence
    Volterra interchange; no wall).  NOT `a₁ = R/6`. -/
theorem interchangeData_of_banked (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t C : ℝ) (hC : 0 ≤ C)
    (hEbound : ∀ τ p q, 0 < τ →
        |heatOp g gi Wit τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi Wit τ p q = 0)
    (hEmeas : StronglyMeasurable
        (fun q : ℝ × Point n × Point n => heatOp g gi Wit q.1 q.2.1 q.2.2))
    (ht : 0 < t) :
    InterchangeData g gi Wit t :=
  ⟨heatConv_leviSeries_interchange (heatOp g gi Wit) C hC hEbound hEzero hEmeas t ht 0 0⟩

/-- **`endpointData_of_banked`.**  Builds `EndpointData` from an (unrestricted-in-`τ`) Gaussian
    envelope bound + support-in-positive-time + strong measurability.  The `hEbound` slot is the
    envelope bound weakened to `τ ≤ t` (geometric DATA, banked producer
    `EboundWiringHD1.hEboundW_from_geometry`); the `hIntegrable` slot is produced HERE via
    `HeatResidualBound.iterConvIntegrableW_of_bound_baseMeas`.  NOT `a₁ = R/6`. -/
theorem endpointData_of_banked (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t C : ℝ)
    (hEbound : ∀ τ p q, 0 < τ →
        |heatOp g gi Wit τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi Wit τ p q = 0)
    (hEmeas : StronglyMeasurable
        (fun q : ℝ × Point n × Point n => heatOp g gi Wit q.1 q.2.1 q.2.2)) :
    EndpointData g gi Wit t C where
  hEbound := fun τ p q hτ _ => hEbound τ p q hτ
  hIntegrable := iterConvIntegrableW_of_bound_baseMeas (heatOp g gi Wit) C hEbound hEzero hEmeas

end QIQTH.TruncatedDuhamelData

section AxiomChecks
open QIQTH.TruncatedDuhamelData
#print axioms hDuhamel_of_truncatedData
#print axioms duhamelInterface_of_truncatedData
#print axioms truncatedDuhamelCore_of_daLim
#print axioms interchangeData_of_banked
#print axioms endpointData_of_banked
end AxiomChecks
