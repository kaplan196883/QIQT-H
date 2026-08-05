/-
  InverseChartNormalJets — J4-251: wide-route bricks 2+3, the INVERSE-CHART NORMAL-JET width gate
  + the FIXED GATE RECORD that `GaussianWidthTransfer` (J4-250) consumes.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It PACKAGES
  the already-derived inverse-chart near-isometry into the exact radial WIDTH-GATE shape the generic
  Gaussian width-transfer bricks consume, and bundles the admissible `(η, lam)` width-gap choice into a
  single reusable record.  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypotheses, no conclusion-in-disguise.  No existing file is edited.

  ── DON'T-UNDER-CREDIT FINDING (the decisive one).
  The near-isometry the wide campaign needs is **already fully DERIVED, axiom-free**, in
  `InverseChartDisplacement.lean`:
      `chartW0_nearIsometry`  gives, for every `S ⊆ K ∩ ball 0 r`,
        * `hcoarse₀`  (with `c = 1/2`):  `∀ z ∈ S, c·rncRadialSq z ≤ rncRadialSq (W₀ z)`, and
        * `hasymp₀`:  the sharp `(1±δ)` two-sided form on `rncRadialSq z < r'²`,
  where `W₀ z := uniformInverseChart g gi hC hK z 0` is the normal coordinate of the origin seen from the
  base `z`.  The SIGN is `W₀ z ≈ −z` (`chartW0_displacement`: `‖W₀ z + z‖ ≤ C_W‖z‖²`), but `rncRadialSq`
  is EVEN (`rncRadialSq_neg`) so the radial-square gate does not see the sign.  Underneath it is the
  banked EXP-side quadratic displacement + a Mathlib `ApproximatesLinearOn` surjectivity root, NOT the
  base-side `C¹` (which was never established) — so the honest route is the DISPLACEMENT route, not a
  base-side third jet.  The `hcoarse₀` shape is LITERALLY the `gaussDdim_width_ratio_le` radial gate
  `(1−η)·r²(z) ≤ r²(w)` with `w = W₀ z` and `1−η = c`.

  ── WHAT LANDS HERE (all DERIVED; NOT `a₁ = R/6`).

    (1)  `chart_width_gate` — THE WIDTH GATE.  From `chartW0_nearIsometry`'s coarse constant `c > 0`, an
         explicit admissible width-gap `(η, lam) = (1−c, 1/c + 1)` with `η < 1`, `1 < lam`, `1/lam < 1−η`,
         and, on `z ∈ K`, `‖z‖ < r`, the exact gate
             `(1−η)·rncRadialSq z ≤ rncRadialSq (W₀ z)`.

    (2)  `FixedFlowGateData` — THE FIXED GATE RECORD.  Bundles the ordered radial-cutoff radii
         `0 < a < b < r`, the width-gap `(η, lam)` with `η < 1 < lam` and `1/lam < 1−η`, and the proved
         width gate on `‖z‖ < r`.  `FixedFlowGateData.of_geometry` is the CONSTRUCTOR from `(hC, hK)`.

    (3)  `FixedFlowGateData.gate` — the downstream-ready hypothesis instance, and
         `FixedFlowGateData.poly_absorb` — the CAPSTONE feeding the gate straight into
         `gaussDdim_poly_absorb`: for every `k`, an explicit `C > 0` with, uniformly over `τ > 0` and
         every gate point `z`,
             `(rncRadialSq z / τ)ᵏ · gaussDdim τ (W₀ z) ≤ C · gaussDdim (lam·τ) z`.

  NOT `a₁ = R/6`.  The base-point MEASURABILITY of `z ↦ W₀ z` (`hWmeas₀`) is an ORTHOGONAL carried input
  (see `InverseChartDisplacement`/`FlowJointRegularity`), not touched here; the width gate is pointwise.
-/
import Mathlib
import QIQTH.InverseChartDisplacement
import QIQTH.GaussianWidthTransfer

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTransfer
open scoped Topology BigOperators

namespace QIQTH.InverseChartNormalJets

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (1) — the width gate (inverse-chart near-isometry ⟶ radial width gap).
    ############################################################################### -/

/-- **★ `chart_width_gate` — THE INVERSE-CHART WIDTH GATE.**  From the already-derived coarse
    near-isometry `chartW0_nearIsometry` (constant `c > 0`), there is a radius `r > 0` and an explicit
    admissible width-gap pair `(η, lam) = (1−c, 1/c + 1)` with `η < 1`, `1 < lam`, `1/lam < 1−η`, and
    the exact `gaussDdim_width_ratio_le` radial gate holds at every base point `z ∈ K`, `‖z‖ < r`:
        `(1−η)·rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)`.
    (`1−η = c`; the `W₀ z ≈ −z` sign is invisible to the even `rncRadialSq`.)  NOT `a₁ = R/6`. -/
theorem chart_width_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∃ η lam : ℝ, η < 1 ∧ 1 < lam ∧ 1 / lam < 1 - η ∧
      ∀ z ∈ K, ‖z‖ < r →
        (1 - η) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0) := by
  obtain ⟨r, hr, hni⟩ := chartW0_nearIsometry g gi hC hK
  -- the coarse near-isometry on the full active set `S = K ∩ ball 0 r`.
  obtain ⟨hcoarse, _⟩ := hni (K ∩ Metric.ball 0 r) (Set.Subset.rfl)
  obtain ⟨c, hc0, hcbound⟩ := hcoarse
  refine ⟨r, hr, 1 - c, 1 / c + 1, by linarith, ?_, ?_, ?_⟩
  · -- `1 < 1/c + 1`.
    have hpos : 0 < 1 / c := by positivity
    linarith
  · -- `1/(1/c + 1) < 1 - (1 - c) = c`.
    have hden : 0 < 1 / c + 1 := by positivity
    rw [show (1 : ℝ) - (1 - c) = c by ring, div_lt_iff₀ hden]
    have : c * (1 / c + 1) = 1 + c := by field_simp
    rw [this]; linarith
  · intro z hz hzr
    have hmem : z ∈ K ∩ Metric.ball 0 r := ⟨hz, mem_ball_zero_iff.mpr hzr⟩
    have hb := hcbound z hmem
    -- `1 - (1 - c) = c`.
    rwa [show (1 : ℝ) - (1 - c) = c by ring]

/-! ###############################################################################
    ### (2) — the fixed gate record + its constructor from the geometry.
    ############################################################################### -/

/-- **★★ `FixedFlowGateData` — THE FIXED GATE RECORD (wide-route brick 2).**  A single bundle of the
    width-gap choice for the inverse-chart Gaussian, downstream of the geometry `(hC, hK)`:
      * ordered radial-cutoff radii `0 < a < b < r` (the `radialCutoff a b` inner/outer + gate radius);
      * a width-gap pair `(η, lam)` with `η < 1`, `1 < lam`, `1/lam < 1−η` (exactly the
        `gaussDdim_poly_absorb` hypotheses);
      * the proved radial WIDTH GATE `(1−η)·rncRadialSq z ≤ rncRadialSq (W₀ z)` on `‖z‖ < r`.
    Satisfiable and non-vacuous — `FixedFlowGateData.of_geometry` constructs one from `(hC, hK)`.
    NOT `a₁ = R/6`. -/
structure FixedFlowGateData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) where
  /-- inner radial-cutoff radius. -/
  a : ℝ
  /-- outer radial-cutoff radius. -/
  b : ℝ
  /-- the gate radius. -/
  r : ℝ
  /-- the width-gap tolerance `η`. -/
  eta : ℝ
  /-- the width-gap dilation `lam`. -/
  lam : ℝ
  ha : 0 < a
  hab : a < b
  hbr : b < r
  heta : eta < 1
  hlam : 1 < lam
  hgap : 1 / lam < 1 - eta
  hgate : ∀ z ∈ K, ‖z‖ < r →
    (1 - eta) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)

/-- **★ `FixedFlowGateData.of_geometry` — THE CONSTRUCTOR (wide-route brick 3).**  Builds a fixed gate
    record from the geometry alone.  The width-gap `(η, lam)` is pinned by the near-isometry coarse
    constant via `chart_width_gate`; the ordered cutoff radii are `a := r/3 < b := 2r/3 < r`.
    NOT `a₁ = R/6`. -/
noncomputable def FixedFlowGateData.of_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    FixedFlowGateData g gi hC hK := by
  classical
  choose r hr η lam hη hlam hgap hgate using chart_width_gate g gi hC hK
  exact
    { a := r / 3
      b := 2 * r / 3
      r := r
      eta := η
      lam := lam
      ha := by linarith
      hab := by linarith
      hbr := by linarith
      heta := hη
      hlam := hlam
      hgap := hgap
      hgate := hgate }

/-! ###############################################################################
    ### (3) — the downstream-ready gate instance + the poly-absorb capstone.
    ############################################################################### -/

/-- **`FixedFlowGateData.gate` — the downstream-ready hypothesis instance.**  Re-exports the record's
    width gate in exactly the `gaussDdim_width_ratio_le` / `gaussDdim_poly_absorb` shape.  NOT `a₁=R/6`. -/
theorem FixedFlowGateData.gate {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} (D : FixedFlowGateData g gi hC hK)
    {z : Point n} (hz : z ∈ K) (hzr : ‖z‖ < D.r) :
    (1 - D.eta) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0) :=
  D.hgate z hz hzr

/-- **★★ `FixedFlowGateData.poly_absorb` — THE CAPSTONE (gate ⟶ Gaussian polynomial absorption).**  For
    a fixed gate record `D` and every `k`, there is an explicit `C > 0` such that, uniformly over `τ > 0`
    and every gate base point `z ∈ K`, `‖z‖ < D.r`,
        `(rncRadialSq z / τ)ᵏ · gaussDdim τ (W₀ z) ≤ C · gaussDdim (D.lam·τ) z`.
    The record's `(η, lam)` meet the `gaussDdim_poly_absorb` hypotheses, and `D.gate` supplies the radial
    gate at `w = W₀ z`.  This is the exact shape the wide `hAnear` / `hD2Hexpand` analogues consume.
    NOT `a₁ = R/6`. -/
theorem FixedFlowGateData.poly_absorb {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} (D : FixedFlowGateData g gi hC hK) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ z ∈ K, ‖z‖ < D.r →
      (rncRadialSq z / τ) ^ k * gaussDdim τ (uniformInverseChart g gi hC hK z 0)
        ≤ C * gaussDdim (D.lam * τ) z := by
  obtain ⟨C, hC0, habs⟩ :=
    gaussDdim_poly_absorb (n := n) D.heta D.hlam D.hgap k
  refine ⟨C, hC0, ?_⟩
  intro τ hτ z hz hzr
  exact habs τ hτ (uniformInverseChart g gi hC hK z 0) z (D.gate hz hzr)

end QIQTH.InverseChartNormalJets

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.InverseChartNormalJets.chart_width_gate
#print axioms QIQTH.InverseChartNormalJets.FixedFlowGateData.of_geometry
#print axioms QIQTH.InverseChartNormalJets.FixedFlowGateData.gate
#print axioms QIQTH.InverseChartNormalJets.FixedFlowGateData.poly_absorb
