/-
  SupConstantFamily — J4-431 (the sup/constant family): GROUNDING the enumerated sup/constant carries
  of the four terminal groups at the TRUE witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the `a₁ = R/6` convergence-trio campaign.  `a₁ = R/6` remains CONDITIONAL on the whole
  convergence-trio + geometric-wiring stack.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms; std-3 only.  No existing file edited.

  ── THE SUP/CONSTANT FAMILY (Sol #20, the rank-1 target).  The enumerated carries at the terminal
  floor (J4-429) include a family of sup/constant inputs used across groups (1)/(2):
      • `C₁`   — first-order on-gate sup of the witness field derivative,
      • `C₂`   — second-order on-gate sup,
      • `C_L`  — the Levi Gaussian-domination constant,
      • `Mqc`/`M` — amplitude sups of `qc = chartAmp·F` and `A1amp·F`/`A2amp·F`,
      • `Sconst`  — the mass-bound constant.
  This brick GROUNDS the ones that are genuinely reachable from BANKED continuity/compactness data, and
  records the exact obstruction for the rest.  THE SUP LEDGER (end of file) is the honest table.

  ── THE ROUTE (Sol #20, binding).  Compactness: continuous explicit fields on a compact set attain
  bounded norms.  ⚠  THE `.choose` TRAP is respected everywhere — we NEVER sup over a pointwise
  `.choose`-selected derivative germ.  Every grounded sup below runs through a VISIBLY-CONTINUOUS
  explicit field on a compact set:
      • `C_L` is INSTANTIATED from the banked `leviSeries_gatedWitnessN1_dominated` (NOT reproved);
      • `M₀chart` (the zeroth chart-amplitude center-value sup, feeding `Mqc`/`M₀`) is grounded on the
        collar via `BaseSlotAmplitude.baseSlotAmp_bound` — a genuine `IsCompact.exists_bound_of_
        continuousOn` over `[0,τ₀] ×ˢ closedBall 0 ρ`, with continuity banked in `baseSlotAmp_
        continuousOn` (composition of `radialCutoff_contDiff`, `vanVleck_continuous`, `huc_discharged`
        with the base-varying chart continuity from the CoV bundle).

  ── WHAT LANDS.
    • `levi_C_L_grounded`               — ★ C_L: the banked Levi Gaussian domination, instantiated.
    • `chartAmp_center_eq_chartFieldAmp`— the `chartAmp = chartFieldAmp` center-value bridge (a `ring`
        reassociation), so the banked base-slot bound transports to the `chartAmp` carry shape.
    • `chartAmp_center_sup_onCollar`    — ★★ M₀chart / Mqc-amplitude-factor: the collar-restricted
        zeroth chart-amplitude center-value sup, grounded by compactness.
    • `supConstant_phase1`              — ★★★ the packaged grounded amplitude sup in its carry shape.

  ⚠  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.BaseSlotAmplitude
import QIQTH.AmplitudeDataOnCollar
import QIQTH.GatedWitnessPackage

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.PullbackMetric QIQTH.LaplaceBeltrami QIQTH.ResidueBound
open QIQTH.HrepGermFactorization QIQTH.AmplitudeDataOnCollar QIQTH.BaseSlotAmplitude
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.SupConstantFamily

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (b) C_L — the Levi Gaussian-domination constant, INSTANTIATED.
    ############################################################################### -/

/-- **★ `levi_C_L_grounded` — C_L GROUNDED (instantiation of the banked Levi domination).**  This is
    NOT a reproof: it delegates verbatim to `HeatResidualBound.leviSeries_gatedWitnessN1_dominated`,
    exposing the Levi Gaussian-domination constant `C_L` (`|leviSeries E τ p q| ≤ C_L·baseKernelW 2 0`
    on `(0,T]`, conditional on the single base joint strong measurability `hEmeas` = the standing M1
    carry).  The return type is exactly the banked conclusion.  ⚠ NOT `a₁ = R/6`. -/
def levi_C_L_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hn : 1 ≤ n) (T : ℝ) (hT : 0 < T) :=
  leviSeries_gatedWitnessN1_dominated g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0 hn T hT

/-! ###############################################################################
    ### (a) THE AMPLITUDE CENTER-VALUE SUP — the `chartAmp = chartFieldAmp` bridge.
    ############################################################################### -/

/-- **`chartAmp_center_eq_chartFieldAmp`.**  The two concrete on-gate amplitude presentations agree at
    the field centre `x' = 0`: `chartAmp … τ z 0 = chartFieldAmp … τ z 0`.  They differ only by the
    associativity of the triple product (`radialCutoff · Θ^{-½} · (u₀+u₁τ)`); `ring` closes it.  This
    lets the banked BASE-SLOT bound (stated for `chartFieldAmp`) transport to the `chartAmp` carry shape
    that the collar bundle / slot dominators demand.  ⚠ NOT `a₁ = R/6`. -/
theorem chartAmp_center_eq_chartFieldAmp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n) :
    chartAmp g gi hC hK a b τ z 0 = chartFieldAmp g gi hC hK a b τ z 0 := by
  simp only [chartAmp, chartFieldAmp]
  ring

/-- **★★ `chartAmp_center_sup_onCollar` — M₀chart / the `Mqc` amplitude factor, GROUNDED.**  From only
    the standing geometry `(hC, hK, K ∈ 𝓝 0)` and the metric carries `{hg, hgi, hgpos}`, there EXIST a
    base radius `ρ > 0` and a NONNEGATIVE constant `M₀` such that on the collar regime with radius
    `r₀ = ρ` (any collar slope `c`, time cap `τ₀`) the zeroth chart-amplitude center value is bounded:
      `∀ τ z, collarRegime ρ c τ₀ τ z → |chartAmp … τ z 0| ≤ M₀`.
    Route (Sol #20, compactness — NO `.choose`): `BaseSlotAmplitude.baseSlotAmp_bound` supplies the
    τ-uniform bound `|chartFieldAmp … τ z 0| ≤ CA` on `[0,τ₀] ×ˢ closedBall 0 ρ` (genuine
    `IsCompact.exists_bound_of_continuousOn` on a visibly-continuous field); the collar regime confines
    `τ ∈ (0,τ₀] ⊆ [0,τ₀]` and `‖z‖ < ρ ⟹ z ∈ closedBall 0 ρ`; the center-value bridge transports it to
    `chartAmp`.  This is the EXACT `amplitudeDataOn_concrete.hM₀chart` carry shape (with `r₀ := ρ`), and
    the amplitude factor of the `Mqc = sup|chartAmp·F|` / `M₀ = sup|Aamp|` sups.  ⚠ NOT `a₁ = R/6`. -/
theorem chartAmp_center_sup_onCollar (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b c τ₀ : ℝ) :
    ∃ ρ > (0 : ℝ), ∃ M₀ : ℝ, 0 ≤ M₀ ∧
      ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
        |chartAmp g gi hC hK a b τ z 0| ≤ M₀ := by
  obtain ⟨ρ, hρ, CA, hCA⟩ := baseSlotAmp_bound g gi hC hK h0Kmem hg hgi hgpos a b τ₀
  refine ⟨ρ, hρ, max CA 0, le_max_right _ _, fun τ z hreg => ?_⟩
  obtain ⟨hτpos, hττ₀, _hzK, hzρ, _hzc⟩ := hreg
  have hzball : z ∈ Metric.closedBall (0 : Point n) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hzρ.le
  rw [chartAmp_center_eq_chartFieldAmp]
  exact le_trans (hCA τ ⟨hτpos.le, hττ₀⟩ z hzball) (le_max_left _ _)

/-! ###############################################################################
    ### THE PACKAGE.
    ############################################################################### -/

/-- **★★★ `supConstant_phase1` — the grounded amplitude sup in its carry shape.**  Packages the
    genuinely-grounded zeroth chart-amplitude center-value sup on the collar (the `M₀chart` /
    `Mqc`-amplitude / `M₀` carry).  Combined with `levi_C_L_grounded` (the C_L carry, disjoint
    hypothesis set), these are the two members of the sup/constant family reachable from banked
    continuity/compactness at this brick; the derivative-order sups (`C₁`/`C₂`/`M₁chart`/`M₂chart` and
    hence the `M`/`Sconst` products) are OBSTRUCTED pending a base-slot field-DERIVATIVE bound (see THE
    SUP LEDGER).  ⚠ NOT `a₁ = R/6`. -/
theorem supConstant_phase1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b c τ₀ : ℝ) :
    ∃ ρ > (0 : ℝ), ∃ M₀ : ℝ, 0 ≤ M₀ ∧
      ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
        |chartAmp g gi hC hK a b τ z 0| ≤ M₀ :=
  chartAmp_center_sup_onCollar g gi hC hK h0Kmem hg hgi hgpos a b c τ₀

end QIQTH.SupConstantFamily

/-! ## THE SUP LEDGER — the honest per-constant table.

  Each sup/constant of the family is classified GROUNDED (with the route) / GATE-RESTRICTED (mismatch
  named) / OBSTRUCTED (exact obstruction).

    ┌──────────┬───────────────────────────────────────────────────────────────────────────────────┐
    │ CONSTANT │ STATUS                                                                              │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ C_L      │ GROUNDED (banked).  `levi_C_L_grounded` instantiates                                │
    │          │ `leviSeries_gatedWitnessN1_dominated`: `∃ C_L ≥ 0, |leviSeries| ≤ C_L·baseKernelW`   │
    │          │ on `(0,T]`, conditional only on the base joint measurability `hEmeas` (M1 carry).    │
    │          │ ⚠ shape mismatch to the InnerDataEnvelope carry `|Lev| ≤ C_L·gaussDdim σ`: needs the │
    │          │ `baseKernelW 2 0 = gaussDdim (2τ)` rewrite (`baseKernelW_zero_apply`) + width pick —  │
    │          │ a one-step bridge, deferred (not a new obstruction).                                 │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ Mqc /    │ GROUNDED (amplitude factor), GATE-RESTRICTED.  `chartAmp_center_sup_onCollar`:       │
    │ M₀chart /│ `∃ ρ,M₀≥0, ∀τz, collarRegime ρ c τ₀ τ z → |chartAmp … τ z 0| ≤ M₀`, via              │
    │ M₀ (Aamp)│ `baseSlotAmp_bound` compactness (banked continuity; NO `.choose`).  This is the EXACT │
    │          │ `amplitudeDataOn_concrete.hM₀chart` shape (r₀ := ρ).                                 │
    │          │ ⚠ MISMATCH to the SlotIII `hMA : ∀ τ z, |chartAmp … τ z 0| ≤ M_A` (GLOBAL, no        │
    │          │ regime): the global sup is FALSE off-collar in general (radialCutoff bounds the       │
    │          │ support but the joint-`z` continuity bound is only banked on the compact ball).       │
    │          │ ⚠ For `Mqc = sup|chartAmp·F|`: the F factor is Gaussian-bounded but only `s`-locally  │
    │          │ (`F ≤ C_L·gaussDdim(2s)`, peak blows up as `s→0`), so the amplitude·Levi product sup  │
    │          │ as an `s`-UNIFORM constant is CARRIED into the slot's pointwise `hdom`, not a bare    │
    │          │ constant here — the amplitude FACTOR is what this brick grounds.                     │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ C₁       │ OBSTRUCTED.  `C₁ = sup_gate |witnessFieldDeriv|` is the first FIELD-slot derivative of │
    │          │ the witness at the base.  The banked derivative bounds (`amp_deriv_bound_*`,          │
    │          │ `witnessFieldDeriv2_gate_abs_le`) are at a FIXED base over the field slot, or germ-   │
    │          │ local; there is NO banked JOINT-in-base continuous field for `z ↦ witnessFieldDeriv`  │
    │          │ to run compactness over.  Needs a base-slot field-DERIVATIVE continuity brick (the    │
    │          │ `BaseSlotAmplitude` analogue for the first derivative).                              │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ C₂       │ OBSTRUCTED (same as C₁, one derivative order up): `sup_gate |witnessFieldDeriv2|`.    │
    │          │ Needs the base-slot SECOND-derivative continuity brick.                              │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ M₁chart /│ OBSTRUCTED.  `M₁chart = sup |∂ᵢ chartAmp … 0|`, `M₂chart = sup |∂ᵢ² chartAmp … 0|`   │
    │ M₂chart  │ (FIELD-slot center partials, varying over the base `z`).  Banked field-slot deriv     │
    │          │ bounds are per-fixed-base; the base-VARYING deriv field is not banked continuous.     │
    │          │ Same obstruction as C₁/C₂ (base-slot derivative continuity).                         │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ M        │ OBSTRUCTED.  `M = sup |A1amp·F| = sup |ρ·(−2∂ᵢchartAmp 0)·F|`.  F is `z`-uniformly     │
    │          │ Gaussian-bounded and ρ is collar-bounded (`rhoRatio_le_collarK`), but the            │
    │          │ `∂ᵢ chartAmp 0` base-slot derivative sup is OBSTRUCTED (= M₁chart).                   │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ Sconst   │ OBSTRUCTED.  `Sconst = sup |A2amp·F| = sup |ρ·(∂ᵢ²chartAmp 0)·F|`.  Same as M, one    │
    │          │ derivative order up (= M₂chart).                                                     │
    └──────────┴───────────────────────────────────────────────────────────────────────────────────┘

  SUMMARY.  GROUNDED this brick: C_L (banked instantiation), M₀chart / Mqc-amplitude-factor / M₀
  (compactness).  OBSTRUCTED (single shared wall = a base-slot field-DERIVATIVE continuity brick, the
  `BaseSlotAmplitude` analogue for `∂` and `∂²`): C₁, C₂, M₁chart, M₂chart, and hence M, Sconst.  The
  `.choose` trap FORCED nothing to the finite-subcover route — every grounded sup used a banked
  visibly-continuous field over a compact set; the obstructed ones are honestly blocked precisely
  BECAUSE no such banked continuous derivative field exists yet (we did NOT fabricate one via `.choose`).

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.SupConstantFamily
#print axioms levi_C_L_grounded
#print axioms chartAmp_center_eq_chartFieldAmp
#print axioms chartAmp_center_sup_onCollar
#print axioms supConstant_phase1
end AxiomChecks
