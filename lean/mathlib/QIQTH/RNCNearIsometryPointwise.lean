/-
  RNCNearIsometryPointwise — the ABSTRACT POINTWISE near-isometry primitive `hco ⟸ hVdisp`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6` and proves nothing new about `R/6`.  It is one
  geometry-layer analytic brick of the a₁=R/6 mixed-sliver campaign's chart-surface residue
  (J4-795).  It supplies the exact SHAPE of the sliver hypothesis `hco` of
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed`

      `hco : (1 / 2) · rncRadialSq z ≤ rncRadialSq (V z)`   (the RNC near-isometry / coercivity)

  as a *pointwise consequence* of the sliver hypothesis `hVdisp`

      `hVdisp : ‖V z + z‖ ≤ C_W · ‖z‖²`                     (the RNC quadratic displacement bound),

  for an ARBITRARY displacement map `V : Point n → Point n` (chart-agnostic), on the explicit radius
  where `n · C_W · ‖z‖ ≤ 1/4`.  This is the reusable analytic KERNEL of the "coercivity from
  near-identity displacement" step: whoever supplies `hVdisp` on a gate ball gets `hco` for free.

  ── WHY THIS IS NON-REDUNDANT.  `InverseChartDisplacement.chartW0_nearIsometry` already proves the
  coarse `c = 1/2` bound, but only for the *concrete* chart `W₀ z = uniformInverseChart … z 0`, phrased
  over an active set `S ⊆ K ∩ ball 0 r`, and routed through the two-sided error
  `chartW0_rncRadialSq_error` (via `rncRadialSq_add_le`, constant `L = 2n·C_W + 3n·C_W²`).  This file
  gives instead the CHART-AGNOSTIC, PER-POINT primitive in exactly the sliver's `∀ z, (1/2)·rncRadialSq
  z ≤ rncRadialSq (V z)` shape, via a direct coordinatewise `∑`-expansion with the cleaner radius
  `n·C_W·‖z‖ ≤ 1/4`.  It is the object a per-point `hco` discharge (or a future gating layer) calls.

  ── HONEST SCOPE (what is NOT closed).  The sliver's `hco`/`hVdisp` are literally *global* `∀ z : Point
  n`.  For the concrete `V = W₀` the displacement bound holds only on a ball (`chartW0_displacement`),
  because off the injectivity ball the `.choose`-built chart is junk; the global `∀ z` form needs the
  gating layer (concrete instantiation), not built here.  Independently, the jet-gap estimates
  `hJ3i`/`hJ3j`/`hJ3Q` are one Fréchet order up and remain blocked at the frozen `uniformChart_exists`
  spec (J4-556 substrate-rebuild wall).  This brick discharges the `hco`↔`hVdisp` reduction only.

  No `sorry`, no new axioms, no `:= True`; every hypothesis satisfiable (`V = -id`, `C_W = 0` gives
  both sides `rncRadialSq z`) and non-vacuous; none equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InverseChartDisplacement

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatResidualBound
open scoped BigOperators

namespace QIQTH.RNCNearIsometryPointwise

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ THE POINTWISE NEAR-ISOMETRY PRIMITIVE — `nearIsometry_lower_of_quadraticDisplacement`.**
    For any displacement map `V : Point n → Point n`, if the quadratic displacement bound
    `‖V z + z‖ ≤ C_W · ‖z‖²` holds at `z` (the sliver's `hVdisp` shape, so `V z ≈ −z`) and `z` is inside
    the coercivity radius `n · C_W · ‖z‖ ≤ 1/4`, then the ℓ²-squared coercivity
    `(1/2) · rncRadialSq z ≤ rncRadialSq (V z)` (the sliver's `hco` shape) holds.

    Proof (direct coordinatewise `∑`-expansion, `b := V z + z`, `V z i = b i − z i`):
    `rncRadialSq z − rncRadialSq (V z) = ∑ (2·bᵢ·zᵢ − bᵢ²) ≤ 2·∑|zᵢ||bᵢ| ≤ 2·n·‖z‖·‖b‖
      ≤ 2·n·C_W·‖z‖³ = 2·(n·C_W·‖z‖)·‖z‖² ≤ 2·(1/4)·‖z‖² ≤ (1/2)·rncRadialSq z`
    (the last step via `‖z‖² ≤ rncRadialSq z`).  ⚠ NOT `a₁ = R/6`. -/
theorem nearIsometry_lower_of_quadraticDisplacement
    (V : Point n → Point n) (C_W : ℝ) (_hCW : 0 ≤ C_W) (z : Point n)
    (hVdisp : ‖V z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hrad : (n : ℝ) * C_W * ‖z‖ ≤ 1 / 4) :
    (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (V z) := by
  set b : Point n := V z + z with hbdef
  have hVzi : ∀ i, V z i = b i - z i := by
    intro i; rw [hbdef]; simp [Pi.add_apply]
  have hb : ‖b‖ ≤ C_W * ‖z‖ ^ 2 := hVdisp
  have hbnn : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hb_i : ∀ i, |b i| ≤ ‖b‖ := fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b i
  have hz_i : ∀ i, |z i| ≤ ‖z‖ := fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z i
  -- coordinatewise expansion of the ℓ² gap.
  have hexp : rncRadialSq z - rncRadialSq (V z) = ∑ i, (2 * b i * z i - b i ^ 2) := by
    simp only [rncRadialSq]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hVzi i]; ring
  -- bound the gap by `2·n·‖z‖·‖b‖`.
  have hgap : rncRadialSq z - rncRadialSq (V z) ≤ 2 * ((n : ℝ) * (‖z‖ * ‖b‖)) := by
    rw [hexp]
    calc ∑ i, (2 * b i * z i - b i ^ 2)
        ≤ ∑ _i : Fin n, 2 * (‖z‖ * ‖b‖) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have h1 : 2 * b i * z i - b i ^ 2 ≤ 2 * (b i * z i) := by nlinarith [sq_nonneg (b i)]
          have h2 : b i * z i ≤ |z i| * |b i| := by
            have := le_abs_self (b i * z i)
            rw [abs_mul] at this
            nlinarith [this]
          have h3 : |z i| * |b i| ≤ ‖z‖ * ‖b‖ :=
            mul_le_mul (hz_i i) (hb_i i) (abs_nonneg _) hznn
          linarith
      _ = 2 * ((n : ℝ) * (‖z‖ * ‖b‖)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  -- `n·‖z‖·‖b‖ ≤ n·C_W·‖z‖³`.
  have hstep : (n : ℝ) * (‖z‖ * ‖b‖) ≤ (n : ℝ) * C_W * ‖z‖ ^ 3 := by
    have hbz : ‖z‖ * ‖b‖ ≤ ‖z‖ * (C_W * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left hb hznn
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hbz hnn]
  -- `2·n·C_W·‖z‖³ ≤ (1/2)·rncRadialSq z` via `n·C_W·‖z‖ ≤ 1/4` and `‖z‖² ≤ rncRadialSq z`.
  have hzsq : ‖z‖ ^ 2 ≤ rncRadialSq z := norm_sq_le_rncRadialSq z
  have hcube : (n : ℝ) * C_W * ‖z‖ ^ 3 ≤ (1 / 4) * ‖z‖ ^ 2 :=
    by nlinarith [mul_le_mul_of_nonneg_right hrad (sq_nonneg ‖z‖), hznn]
  nlinarith [hgap, hstep, hcube, hzsq]

/-! ### Concrete corollary — the sliver `hco` for the van-Vleck chart `V = W₀`, per-point on a ball. -/

/-- **★ CONCRETE `hco` FOR THE VAN-VLECK CHART — `chartW0_hco_ball`.**  Instantiating the pointwise
    primitive at the concrete inverse-chart origin coordinate `W₀ z = uniformInverseChart g gi hC hK z 0`
    (the map that plays the role of `V` in the mixed sliver's normal form) via the banked displacement
    bound `chartW0_displacement`: there is an explicit radius `r > 0` such that for every base point
    `z ∈ K` with `‖z‖ < r`, the sliver's `hco` shape holds at the concrete chart:
        `(1/2) · rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)`.
    This is the per-point (chart-agnostic-primitive-routed) discharge of the mixed sliver's `hco`
    hypothesis for the concrete `V = W₀`, on the injectivity ball.  ⚠ NOT `a₁ = R/6` — the *global*
    `∀ z` sliver form still needs the gating layer, and `hVdisp`/`hJ3*` are separate carries. -/
theorem chartW0_hco_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ z ∈ K, ‖z‖ < r →
      (1 / 2 : ℝ) * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0) := by
  obtain ⟨r₁, hr₁, C_W, hCW0, hD1⟩ := chartW0_displacement g gi hC hK
  refine ⟨min r₁ (1 / (4 * ((n : ℝ) * C_W + 1))), lt_min hr₁ (by positivity), ?_⟩
  intro z hzK hzr
  have hzr₁ : ‖z‖ < r₁ := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzR : ‖z‖ < 1 / (4 * ((n : ℝ) * C_W + 1)) := lt_of_lt_of_le hzr (min_le_right _ _)
  -- displacement bound in the `‖z‖^2` shape the primitive consumes.
  have hVdisp : ‖uniformInverseChart g gi hC hK z 0 + z‖ ≤ C_W * ‖z‖ ^ 2 := by
    have := hD1 z hzK hzr₁; nlinarith [this, sq_nonneg ‖z‖]
  -- the coercivity radius `n·C_W·‖z‖ ≤ 1/4`.
  have hnn : (0 : ℝ) ≤ (n : ℝ) * C_W := mul_nonneg (Nat.cast_nonneg n) hCW0
  have hrad : (n : ℝ) * C_W * ‖z‖ ≤ 1 / 4 := by
    have hden : (0 : ℝ) < 4 * ((n : ℝ) * C_W + 1) := by positivity
    have hzle : ‖z‖ ≤ 1 / (4 * ((n : ℝ) * C_W + 1)) := le_of_lt hzR
    have hmul : (n : ℝ) * C_W * ‖z‖
        ≤ (n : ℝ) * C_W * (1 / (4 * ((n : ℝ) * C_W + 1))) :=
      mul_le_mul_of_nonneg_left hzle hnn
    have hbound : (n : ℝ) * C_W * (1 / (4 * ((n : ℝ) * C_W + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ hden]; nlinarith [hnn]
    linarith
  exact nearIsometry_lower_of_quadraticDisplacement
    (fun w => uniformInverseChart g gi hC hK w 0) C_W hCW0 z hVdisp hrad

end QIQTH.RNCNearIsometryPointwise

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.RNCNearIsometryPointwise.nearIsometry_lower_of_quadraticDisplacement
#print axioms QIQTH.RNCNearIsometryPointwise.chartW0_hco_ball
