/-
  HgateAffineRepair — J4-368: the AFFINE `hgate` binder repair (Sol consult #15, the sixth
  interface-shape finding).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  PACKAGING / BINDER-SHAPE-REPAIR brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It
  takes the banked `hgate → hEdom → DaLimLU` chain (J4-362 / J4-364 / J4-366 / J4-367, all READ-ONLY)
  and REPAIRS the shape of the surviving on-gate labelled carry `hgate`: the τ-UNIFORM constant `P`
  carried by the banked assembly is UNSATISFIABLE for the concrete `N = 1` witness (the residual term
  `τ·(Δu₁)·G` grows linearly in `τ` while the τ-uniform RHS stays bounded per `(p,q)`).  The HONEST
  shape is AFFINE: `(P₀ + P₁·τ)` in place of `P`.  This file threads the affine factor through the
  width absorption unchanged and re-threads the assembly over the affine carry.  NO `sorry` (header
  prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to
  (or trivially yielding) the conclusion, NO existing file edited, nothing committed.  `a₁ = R/6` stays
  CONDITIONAL on the whole convergence / geometric-wiring stack AND on the surviving LABELLED inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THE AFFINE SHAPE IS THE HONEST ONE (Sol #15).  For the concrete `N = 1` witness the M2
  residual carries a term `τ·(Δu₁)·G_{4/3τ}` whose sup over `(p,q)` is `Θ(τ)`, NOT `O(1)`.  The
  τ-uniform binder `hgate : |heatOp …| ≤ P·(quadPoly·G)` therefore CANNOT hold with a fixed `P` (fails
  as `τ → ∞` at fixed radial ratio).  The affine binder `|heatOp …| ≤ (P₀ + P₁·τ)·(quadPoly·G)` IS
  satisfiable — `P₀` absorbs the width-1/amplitude terms, `P₁` the linear-in-τ residual term — and the
  downstream `hEdom` ∃-shape `(E₀ + E₁·τ)·√(3/2)ⁿ·G_{(3/2)τ}` (the exact object `hDaLimLU_from_labelled_v2`
  consumes) ALREADY allows `E₁ ≠ 0`; only the current wrappers hard-code `E₁ = 0`.  This brick simply
  threads a genuine `E₁ = P₁·Cabs`.

  ## THE KEY OBSERVATION (A1 verdict).  The width-absorption fact
      `quadPoly(r²/τ)·G_{w₀τ} ≤ Cabs·G_{(3/2)τ}`   (`Cabs = √(3/2/w₀)ⁿ·(2k₁² + k₁ + 1)`)
  is a POINTWISE inequality INDEPENDENT of the outer constant (`quadPoly_width_absorb`, extracted from
  the banked `HrawPreCollapse.hEdom_of_quadPoly_residual_width` internal chain).  Hence the affine
  version is the clean `mul_le_mul` route:
      `(P₀ + P₁τ)·quadPoly·G_{w₀} ≤ (P₀ + P₁τ)·Cabs·G_{3/2} ≤ (P₀·Cabs + P₁·Cabs·τ)·√(3/2)ⁿ·G_{3/2}`
  (the last step absorbs `√(3/2)ⁿ ≥ 1`).  NO affine CLONES of the M1/M2 width lemmas were needed — the
  P-independence of the absorption is what makes the repair a one-liner over the banked pointwise fact.

  ## DELIVERABLES.
  •  (A2) `grade₂` / `sqrt_le_one_add` / `grade_two_le_quadPoly` / `weighted_grade_le` — the grading
     helper (Sol brick 1): the five-monomial `1 + √x + x + x√x + x²` grade dominated by `5·(x²+x+1)`,
     and its weighted generalisation.
  •  (A1) `quadPoly_width_absorb` — the P-INDEPENDENT pointwise width absorption.
  •  (A1) `AffineGateBound` — the affine on-gate predicate.
  •  (A1) `gatedRawBoundQuadWidth_affine_of_onGate` — the affine gate assembly (off-gate via the J4-359
     support confinement).
  •  (A1) `hEdom_of_affine_quadPoly_residual_width` — the affine width-`w₀` → width-3/2 `hEdom` bridge.
  •  (A1) `hEdom_concrete_final_affine` — the affine analogue of `HrawPreCollapse.hEdom_concrete_final`.
  •  (R2) `hEdom_vanVleck_of_hgate_affine` — the affine bridge for the concrete van-Vleck gate.
  •  (A3) `hDaLimLU_from_hgate_affine_census_v2` — the assembly re-threaded over the AFFINE `hgate`
     carry (verbatim `FrozenGermInternal.hDaLimLU_from_hgate_census_v2` with the τ-uniform `(P, hP)`
     replaced by the affine `(P₀, P₁, hP₀, hP₁)` and the affine `hgate`).  Same conclusion
     `DaLimLUGoal g gi (vanVleckGatedWitness …) (leviSeries …) U`.

  ## SATISFIABILITY / HONESTY.  `AffineGateBound` is SATISFIABLE for the concrete `N = 1` witness (Sol
  #15: `P₀` absorbs the O(1) terms, `P₁` the linear-in-τ residual `τ·(Δu₁)·G`) — precisely the shape the
  τ-uniform binder FAILED to satisfy.  Every hypothesis is non-vacuous and NONE equals the conclusion
  (`hgate` is an on-gate width-4/3 affine QUADRATIC bound; the conclusion is the loc-unif `Da`-limit).
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GlobalRawBoundFacade
import QIQTH.WidthMarginEngine
import QIQTH.HrawCampaignOne
import QIQTH.HrawChartTransfer
import QIQTH.HrawPreCollapse
import QIQTH.LabelledRethreadV2
import QIQTH.Pd2ConvPerU
import QIQTH.HgateCensusAssembly
import QIQTH.FrozenGermInternal

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.GlobalRawBoundFacade QIQTH.ResidueBound
open scoped Interval Topology BigOperators

namespace QIQTH.HgateAffineRepair

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (A2) — the grading helper (Sol brick 1).
    ############################################################################### -/

/-- **★ (A2) — `grade₂`.**  The five-monomial `√`-graded polynomial `1 + √x + x + x·√x + x²` that the
    raw pre-absorption residual estimate exposes (the `√`-graded interpolation between the constant,
    linear, and quadratic residual powers).  NOT `a₁ = R/6`. -/
noncomputable def grade₂ (x : ℝ) : ℝ := 1 + Real.sqrt x + x + x * Real.sqrt x + x ^ 2

/-- **★ (A2) — `sqrt_le_one_add`.**  `√x ≤ 1 + x` for `x ≥ 0` (via `√x ≤ √((1+x)²) = 1 + x`, since
    `x ≤ (1+x)²`).  NOT `a₁ = R/6`. -/
theorem sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  have h1x : (0 : ℝ) ≤ 1 + x := by linarith
  have h : Real.sqrt x ≤ Real.sqrt ((1 + x) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hx])
  rwa [Real.sqrt_sq h1x] at h

/-- **★ (A2) — `grade_two_le_quadPoly`.**  The grade `1 + √x + x + x√x + x²` is dominated by
    `5·(x² + x + 1)` for `x ≥ 0` (each monomial ≤ `x² + x + 1`, via `√x ≤ 1 + x` and `x√x ≤ x + x²`).
    NOT `a₁ = R/6`. -/
theorem grade_two_le_quadPoly {x : ℝ} (hx : 0 ≤ x) : grade₂ x ≤ 5 * (x ^ 2 + x + 1) := by
  unfold grade₂
  have hs := sqrt_le_one_add hx
  have hxsx : x * Real.sqrt x ≤ x + x ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hs hx]
  nlinarith [hs, hxsx, hx, sq_nonneg x]

/-- **★ (A2) — `weighted_grade_le`.**  The weighted grade `c₀ + c₁√x + c₂x + c₃(x√x) + c₄x²` with
    nonneg weights is dominated by `(c₀ + c₁ + c₂ + c₃ + c₄)·(x² + x + 1)` for `x ≥ 0` — each monomial
    `tᵢ ≤ x² + x + 1`, so `cᵢ·tᵢ ≤ cᵢ·(x² + x + 1)`, summed.  NOT `a₁ = R/6`. -/
theorem weighted_grade_le {x c₀ c₁ c₂ c₃ c₄ : ℝ} (hx : 0 ≤ x)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) :
    c₀ + c₁ * Real.sqrt x + c₂ * x + c₃ * (x * Real.sqrt x) + c₄ * x ^ 2
      ≤ (c₀ + c₁ + c₂ + c₃ + c₄) * (x ^ 2 + x + 1) := by
  have hs := sqrt_le_one_add hx
  have hxsx : x * Real.sqrt x ≤ x + x ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hs hx]
  nlinarith [mul_nonneg hc₀ (by nlinarith [hx, sq_nonneg x] : (0 : ℝ) ≤ x ^ 2 + x + 1 - 1),
    mul_nonneg hc₁ (by nlinarith [hs, sq_nonneg x] : (0 : ℝ) ≤ x ^ 2 + x + 1 - Real.sqrt x),
    mul_nonneg hc₂ (by nlinarith [sq_nonneg x] : (0 : ℝ) ≤ x ^ 2 + x + 1 - x),
    mul_nonneg hc₃ (by nlinarith [hxsx] : (0 : ℝ) ≤ x ^ 2 + x + 1 - x * Real.sqrt x),
    mul_nonneg hc₄ (by nlinarith [hx] : (0 : ℝ) ≤ x ^ 2 + x + 1 - x ^ 2)]

/-! ###############################################################################
    ### (A1) — the P-independent pointwise width absorption.
    ############################################################################### -/

/-- **★ (A1) — `quadPoly_width_absorb`.**  THE P-INDEPENDENT POINTWISE WIDTH ABSORPTION (extracted from
    the banked `HrawPreCollapse.hEdom_of_quadPoly_residual_width` internal chain).  For `0 < w₀ < 3/2`
    and `τ > 0`, the exposed QUADRATIC polynomial times the width-`w₀` Gaussian is dominated by a fixed
    constant `Cabs = √(3/2/w₀)ⁿ·(2k₁² + k₁ + 1)` (`k₁ = 4·w₀·(3/2)/(3/2−w₀)`) times the width-3/2
    Gaussian:
        `((r²/τ)² + r²/τ + 1)·G_{w₀τ}(v) ≤ Cabs·G_{(3/2)τ}(v)`.
    Route: the `m = 0, 1, 2` width absorptions `WidthMarginEngine.rncRadialSq_pow_mul_gaussDdim_le_width`
    eat the `1`, `r²/τ`, `(r²/τ)²` terms into constants × `G_{3/2}` (dividing by `τ`, `τ²`).  This fact
    carries NO outer constant, so the affine bridge is a clean `mul_le_mul`.  NOT `a₁ = R/6`. -/
theorem quadPoly_width_absorb {w₀ : ℝ} (hw₀ : 0 < w₀) (hw₀lt : w₀ < 3 / 2)
    {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (w₀ * τ) v
      ≤ (Real.sqrt (3 / 2 / w₀) ^ n
          * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2 + 4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1))
          * gaussDdim (3 / 2 * τ) v := by
  have hden : 0 < 3 / 2 - w₀ := by linarith
  have hG0 : 0 ≤ gaussDdim (3 / 2 * τ) v := gaussDdim_nonneg _ _
  -- `m = 0` width widening
  have h0 : gaussDdim (w₀ * τ) v ≤ Real.sqrt (3 / 2 / w₀) ^ n * gaussDdim (3 / 2 * τ) v := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_pow_mul_gaussDdim_le_width 0
      (c := w₀) (d := 3 / 2) hw₀ hw₀lt hτ v
    simpa using h
  -- `m = 1` polynomial absorption
  have h1 : rncRadialSq v * gaussDdim (w₀ * τ) v
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) * τ
          * gaussDdim (3 / 2 * τ) v := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_pow_mul_gaussDdim_le_width 1
      (c := w₀) (d := 3 / 2) hw₀ hw₀lt hτ v
    simpa using h
  -- `m = 2` polynomial absorption
  have h2 : rncRadialSq v ^ 2 * gaussDdim (w₀ * τ) v
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2) * τ ^ 2
          * gaussDdim (3 / 2 * τ) v := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_pow_mul_gaussDdim_le_width 2
      (c := w₀) (d := 3 / 2) hw₀ hw₀lt hτ v
    simpa [Nat.factorial] using h
  -- divide the `m = 1` absorption by `τ`
  have hdiv1 : rncRadialSq v * gaussDdim (w₀ * τ) v / τ
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀))
          * gaussDdim (3 / 2 * τ) v := by
    rw [div_le_iff₀ hτ]
    calc rncRadialSq v * gaussDdim (w₀ * τ) v
        ≤ Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) * τ
            * gaussDdim (3 / 2 * τ) v := h1
      _ = Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀))
            * gaussDdim (3 / 2 * τ) v * τ := by ring
  -- divide the `m = 2` absorption by `τ²`
  have hdiv2 : rncRadialSq v ^ 2 * gaussDdim (w₀ * τ) v / τ ^ 2
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2)
          * gaussDdim (3 / 2 * τ) v := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < τ ^ 2)]
    calc rncRadialSq v ^ 2 * gaussDdim (w₀ * τ) v
        ≤ Real.sqrt (3 / 2 / w₀) ^ n * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2) * τ ^ 2
            * gaussDdim (3 / 2 * τ) v := h2
      _ = Real.sqrt (3 / 2 / w₀) ^ n * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2)
            * gaussDdim (3 / 2 * τ) v * τ ^ 2 := by ring
  -- expand the quadratic exposed polynomial
  have hexpand : ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (w₀ * τ) v
      = rncRadialSq v ^ 2 * gaussDdim (w₀ * τ) v / τ ^ 2
          + rncRadialSq v * gaussDdim (w₀ * τ) v / τ + gaussDdim (w₀ * τ) v := by
    field_simp
  calc ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (w₀ * τ) v
      = rncRadialSq v ^ 2 * gaussDdim (w₀ * τ) v / τ ^ 2
          + rncRadialSq v * gaussDdim (w₀ * τ) v / τ + gaussDdim (w₀ * τ) v := hexpand
    _ ≤ Real.sqrt (3 / 2 / w₀) ^ n * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2)
            * gaussDdim (3 / 2 * τ) v
          + Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀))
            * gaussDdim (3 / 2 * τ) v
          + Real.sqrt (3 / 2 / w₀) ^ n * gaussDdim (3 / 2 * τ) v :=
        add_le_add (add_le_add hdiv2 hdiv1) h0
    _ = (Real.sqrt (3 / 2 / w₀) ^ n
            * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2 + 4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1))
          * gaussDdim (3 / 2 * τ) v := by ring

/-! ###############################################################################
    ### (A1) — the affine on-gate predicate, gate assembly, and `hEdom` bridge.
    ############################################################################### -/

/-- **★ (A1) — `AffineGateBound`.**  The AFFINE on-gate width-4/3 QUADRATIC residual predicate: the
    HONEST replacement (Sol #15) for the UNSATISFIABLE τ-uniform on-gate carry — the outer factor is
    `(P₀ + P₁·τ)` (affine in `τ`) rather than a fixed `P`:
        `∀ τ>0, ∀ q ∈ K, ∀ p ∈ closure (S q),
            |heatOp g gi (gatedKernel K S H) τ p q|
              ≤ (P₀ + P₁·τ)·(((r²/τ)² + r²/τ + 1)·gaussDdim ((4/3)·τ) (p−q))`.
    SATISFIABLE for the concrete `N = 1` witness (`P₀` absorbs the O(1) width-1/amplitude terms, `P₁`
    the linear-in-`τ` residual `τ·(Δu₁)·G`).  NOT `a₁ = R/6`. -/
def AffineGateBound (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (P₀ P₁ : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
    |heatOp g gi (gatedKernel K S H) τ p q|
      ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
              * gaussDdim (4 / 3 * τ) (p - q))

/-- **★ (A1) — `gatedRawBoundQuadWidth_affine_of_onGate`.**  THE AFFINE GATE ASSEMBLY: the global affine
    width-4/3 QUADRATIC bound (all `p q`) follows from the ON-GATE affine bound alone, with the off-gate
    region discharged by the J4-359 support confinement
    `HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport` (LHS `= 0 ≤` the nonneg RHS; nonnegativity
    of `(P₀ + P₁·τ)` uses `0 ≤ P₀`, `0 ≤ P₁`, `τ > 0`).  NOT `a₁ = R/6`. -/
theorem gatedRawBoundQuadWidth_affine_of_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (gatedKernel K S H) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q))) :
    ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi (gatedKernel K S H) τ p q|
        ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                * gaussDdim (4 / 3 * τ) (p - q)) := by
  intro τ hτ p q
  have hfac0 : 0 ≤ P₀ + P₁ * τ := add_nonneg hP₀ (mul_nonneg hP₁ hτ.le)
  have hRHS : 0 ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
      * gaussDdim (4 / 3 * τ) (p - q)) := by
    have hX0 : 0 ≤ rncRadialSq (p - q) / τ := div_nonneg (rncRadialSq_nonneg _) hτ.le
    have hpoly0 : 0 ≤ (rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1 := by positivity
    exact mul_nonneg hfac0 (mul_nonneg hpoly0 (gaussDdim_nonneg _ _))
  by_cases hq : q ∈ K
  · by_cases hp : p ∈ closure (S q)
    · exact hgate τ hτ q hq p hp
    · rw [QIQTH.HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport g gi K S H τ p q (Or.inr hp),
        abs_zero]
      exact hRHS
  · rw [QIQTH.HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport g gi K S H τ p q (Or.inl hq),
      abs_zero]
    exact hRHS

/-- **★ (A1) — `hEdom_of_affine_quadPoly_residual_width`.**  THE AFFINE QUADRATIC BRIDGE.  From the
    global AFFINE width-`w₀` (`0 < w₀ < 3/2`) QUADRATIC bound (all `p q`), with `P₀, P₁ ≥ 0`, the
    width-3/2 `hEdom` ∃-shape follows with a GENUINE `E₁ = P₁·Cabs` (NOT `E₁ = 0`).  Route: the
    P-INDEPENDENT `quadPoly_width_absorb` gives `quadPoly·G_{w₀} ≤ Cabs·G_{3/2}` pointwise; multiplying
    by the nonneg affine factor `(P₀ + P₁τ)` and absorbing `√(3/2)ⁿ ≥ 1` gives
        `(P₀ + P₁τ)·quadPoly·G_{w₀} ≤ (P₀·Cabs + P₁·Cabs·τ)·√(3/2)ⁿ·G_{3/2}`.
    `E₀ = P₀·Cabs`, `E₁ = P₁·Cabs`.  NO affine clones of the M1/M2 width lemmas needed.  NOT `a₁ = R/6`. -/
theorem hEdom_of_affine_quadPoly_residual_width (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) {w₀ : ℝ} (hw₀ : 0 < w₀) (hw₀lt : w₀ < 3 / 2)
    (P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hraw : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (w₀ * τ) (p - q))) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi H τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  -- the P-independent pointwise absorption, packaged as a single τ-uniform constant `Cabs`.
  obtain ⟨Cabs, hCabs0, habs⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ), 0 < τ → ∀ v : Point n,
      ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (w₀ * τ) v
        ≤ C * gaussDdim (3 / 2 * τ) v := by
    have hden : 0 < 3 / 2 - w₀ := by linarith
    have hk1 : 0 ≤ 4 * w₀ * (3 / 2) / (3 / 2 - w₀) := le_of_lt (div_pos (by positivity) hden)
    have hfac : (0 : ℝ) ≤ 2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2
        + 4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1 := by
      nlinarith [hk1, sq_nonneg (4 * w₀ * (3 / 2) / (3 / 2 - w₀))]
    refine ⟨Real.sqrt (3 / 2 / w₀) ^ n
        * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2 + 4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1),
      mul_nonneg (by positivity) hfac, ?_⟩
    intro τ hτ v
    exact quadPoly_width_absorb hw₀ hw₀lt hτ v
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (3 / 2) ^ n := by
    have h1' : (1 : ℝ) ≤ Real.sqrt (3 / 2) := by
      have h2' := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      rwa [Real.sqrt_one] at h2'
    calc (1 : ℝ) = 1 ^ n := (one_pow n).symm
      _ ≤ Real.sqrt (3 / 2) ^ n := pow_le_pow_left₀ (by norm_num) h1' n
  refine ⟨P₀ * Cabs, P₁ * Cabs, mul_nonneg hP₀ hCabs0, mul_nonneg hP₁ hCabs0, fun τ hτ p q => ?_⟩
  have hfac0 : 0 ≤ P₀ + P₁ * τ := add_nonneg hP₀ (mul_nonneg hP₁ hτ.le)
  have hG0 : 0 ≤ gaussDdim (3 / 2 * τ) (p - q) := gaussDdim_nonneg _ _
  calc |heatOp g gi H τ p q|
      ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
              * gaussDdim (w₀ * τ) (p - q)) := hraw τ hτ p q
    _ ≤ (P₀ + P₁ * τ) * (Cabs * gaussDdim (3 / 2 * τ) (p - q)) :=
        mul_le_mul_of_nonneg_left (habs τ hτ (p - q)) hfac0
    _ ≤ (P₀ + P₁ * τ) * (Cabs * (Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))) := by
        apply mul_le_mul_of_nonneg_left _ hfac0
        apply mul_le_mul_of_nonneg_left _ hCabs0
        exact le_mul_of_one_le_left hG0 hsqrt1
    _ = (P₀ * Cabs + P₁ * Cabs * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by ring

/-- **★★ (A1) — `hEdom_concrete_final_affine`.**  THE AFFINE `hraw` FINISH.  From the ON-GATE ambient
    width-4/3 AFFINE QUADRATIC carry `AffineGateBound g gi K S H P₀ P₁` (`P₀, P₁ ≥ 0`) the width-3/2
    `hEdom` ∃-shape follows — the EXACT binder `hDaLimLU_from_labelled_v2` consumes.  This is the honest
    affine analogue of `HrawPreCollapse.hEdom_concrete_final`: the affine gate assembly lifts to the
    global affine width-4/3 QUADRATIC bound, and the affine bridge (`4/3 < 3/2`) discharges it with a
    genuine `E₁ = P₁·Cabs`.  NOT `a₁ = R/6`. -/
theorem hEdom_concrete_final_affine (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hgate : AffineGateBound g gi K S H P₀ P₁) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi (gatedKernel K S H) τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  have hglob := gatedRawBoundQuadWidth_affine_of_onGate g gi K S H P₀ P₁ hP₀ hP₁ hgate
  exact hEdom_of_affine_quadPoly_residual_width g gi (gatedKernel K S H)
    (by norm_num) (by norm_num) P₀ P₁ hP₀ hP₁ hglob

/-! ###############################################################################
    ### (R2) — the affine `hgate` → `hEdom` bridge for the concrete van-Vleck gate.
    ############################################################################### -/

/-- **★ (R2) — `hEdom_vanVleck_of_hgate_affine`.**  THE AFFINE BRIDGE for the concrete van-Vleck gate
    `H_G := vanVleckGatedWitness g gi hChr hK S a b`.  From the ON-GATE ambient width-4/3 AFFINE
    QUADRATIC carry `hgate` (outer factor `(P₀ + P₁·τ)`) produce the width-3/2 `hEdom` ∃-shape, via
    `hEdom_concrete_final_affine` after ONE controlled head-delta `simp only [vanVleckGatedWitness]`
    (which rewrites ONLY the head constant to `gatedKernel K S (globalCutoffParametrixWitnessN 1 …)` —
    it NEVER touches the `.choose`-heavy `uniformInverseChart` internals; the same trick as the banked
    `LabelledRethreadV2.hEdom_vanVleck_of_hgate`).  `hgate` is NAMED, SATISFIABLE (Sol #15) and NOT the
    conclusion.  NOT `a₁ = R/6`. -/
theorem hEdom_vanVleck_of_hgate_affine (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b P₀ P₁ : ℝ)
    (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q))) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  simp only [vanVleckGatedWitness] at hgate ⊢
  exact hEdom_concrete_final_affine g gi K S _ P₀ P₁ hP₀ hP₁ hgate

/-! ###############################################################################
    ### (A3) — the assembly re-thread over the AFFINE `hgate` carry.
    ############################################################################### -/

/-- **★★★ (A3) — `hDaLimLU_from_hgate_affine_census_v2`.**  THE AFFINE ASSEMBLY RE-THREAD.  VERBATIM
    `FrozenGermInternal.hDaLimLU_from_hgate_census_v2` with the τ-UNIFORM on-gate carry `(P, hP, hgate)`
    replaced by the HONEST AFFINE carry `(P₀, P₁, hP₀, hP₁, hgate)` (outer factor `(P₀ + P₁·τ)`, Sol
    #15).  Same conclusion `DaLimLUGoal g gi (vanVleckGatedWitness …) (leviSeries …) U`.  The body is a
    single application of the banked `LabelledRethreadV2.hDaLimLU_from_labelled_v2` (which consumes the
    `hEdom` ∃ directly), with step (vii) fed by the AFFINE bridge `hEdom_vanVleck_of_hgate_affine` and
    step (viii) fed by the SAME per-`u` sliver census + internal frozen germ (from `hQ1`) plumbing that
    `FrozenGermInternal` / `HgateCensusAssembly` use — i.e. the affine repair is localized to the
    `hgate → hEdom` step; every other binder is verbatim.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_from_hgate_affine_census_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U) (hn : 1 ≤ n)
    -- (i) geometry / gauge raw inputs:
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    (hdg0 : ∀ c d e, pd (fun y => g y c d) e (0 : Point n) = 0)
    -- (ii) the W2 differentiation-under-∫ family (at `F := leviSeries (heatOp g gi H_G)`):
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w)
    -- (iii) the residual-domination time floor / window:
    (aa : ℝ) (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u) (hUTle : ∀ u ∈ U, u ≤ T)
    -- (iv) the Levi source envelope package:
    (C : ℝ) (dataLevi : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C T)
    -- (v) the integrability Gaussian dominations + measurabilities:
    (wA CA wA2 CA2 : ℝ) (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2 : 0 ≤ CA2)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2 : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2 * gaussDdim (wA2 * τ) (0 - z))
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeas2Hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    -- (vi) the √ε sliver amplitude bundle:
    (τ₀ : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τ₀)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    -- (vii) ★ THE HONEST AFFINE on-gate width-4/3 QUADRATIC carry (outer factor `(P₀ + P₁·τ)`, Sol #15):
    (P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))
    -- (viii) ★ THE PER-`u` SLIVER CENSUS + FULL-side germ link (frozen germ link is built INTERNALLY
    --        from `hQ1`; `fbulk` is SPECIALIZED to `FrozenGermInternal.fbulkInt …`):
    (sSet : ℝ → Set (Point n))
    (hsOpen : ∀ u ∈ U, IsOpen (sSet u))
    (hsnhds : ∀ u ∈ U, sSet u ∈ 𝓝 (0 : Point n))
    (gcoef : ℝ → Fin n → Point n → ℝ)
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (bb : ℝ → Fin n → ℕ → ℝ)
    (hb : ∀ u ∈ U, ∀ i : Fin n, Tendsto (bb u i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ sSet u,
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m)
          (fderivBulk u i m x) x)
    (hbulk_tendsto : ∀ u ∈ U, ∀ i : Fin n, ∀ x ∈ sSet u,
        Tendsto (fun m => QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m x) atTop
          (𝓝 (gcoef u i x)))
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ sSet u,
        dist (fderivBulk u i m x) (gderiv u i x) ≤ bb u i m)
    (hfull_pd1 : ∀ u ∈ U, ∀ i : Fin n,
        (fun y => pd (fun x => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y)
          =ᶠ[𝓝 (0 : Point n)] gcoef u i)
    -- (ix) the E-combination carries:
    (hDa : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc g gi (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m)) :
    DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U :=
  QIQTH.LabelledRethreadV2.hDaLimLU_from_labelled_v2 g gi hChr hK S a b T U hUopen hn
    hK0 hframeK hinvF hdg0
    V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    aa haa hau hUTle C dataLevi
    wA CA wA2 CA2 hwA hCA hwA2 hCA2 hAdomHeat hAdom2
    hmeasLo hmeasHi hmeas2Lo hmeas2Hi
    τ₀ dataAmp hεaa hετ₀
    -- (vii) ★ the width-3/2 `hEdom` ∃ from the AFFINE bridge:
    (hEdom_vanVleck_of_hgate_affine g gi hChr hK S a b P₀ P₁ hP₀ hP₁ hgate)
    -- (viii) ★ the atomic per-`u` interchange carrier from the sliver census + internal frozen germ:
    (QIQTH.Pd2ConvPerU.hPd2conv_perU g gi hChr hK S a b U sSet hsOpen hsnhds
      gcoef gderiv (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b) fderivBulk bb hb
      hbulkderiv hbulk_tendsto hsliver hfull_pd1
      (fun u _hu i m => QIQTH.Pd2ConvPerU.hfrozen_pd1_from_hQ1
        (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u m i
        (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m) V (hVopen.mem_nhds hV0)
        (hQ1 m i u _hu)))
    hDa hLap hLapZ hEZ hLapS hES

end QIQTH.HgateAffineRepair

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HgateAffineRepair.grade₂
#print axioms QIQTH.HgateAffineRepair.sqrt_le_one_add
#print axioms QIQTH.HgateAffineRepair.grade_two_le_quadPoly
#print axioms QIQTH.HgateAffineRepair.weighted_grade_le
#print axioms QIQTH.HgateAffineRepair.quadPoly_width_absorb
#print axioms QIQTH.HgateAffineRepair.AffineGateBound
#print axioms QIQTH.HgateAffineRepair.gatedRawBoundQuadWidth_affine_of_onGate
#print axioms QIQTH.HgateAffineRepair.hEdom_of_affine_quadPoly_residual_width
#print axioms QIQTH.HgateAffineRepair.hEdom_concrete_final_affine
#print axioms QIQTH.HgateAffineRepair.hEdom_vanVleck_of_hgate_affine
#print axioms QIQTH.HgateAffineRepair.hDaLimLU_from_hgate_affine_census_v2
