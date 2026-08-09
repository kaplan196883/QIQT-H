/-
  LayerBChangeVars — J4-515: the LAYER-B change-of-variables MAJORANT brick (audit-first, smallest
  solid unit) — the Gaussian-PHASE DOMINATION for the base-varying inverse chart `W₀`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the a₁=R/6 heat-kernel campaign; CONDITIONAL and EFFECTIVELY FLAT-ONLY).  The a₁ mainline
  is ONE-CHANNEL-FLAT; curved a₁ is a mechanical rethread + a concrete change-of-variables (CoV)
  bundle `hcov` (interface in `MassChartBridge`) away.  J4-510/511 decoupled `hmassone` from the
  flat-forcing `hframeK` MODULO the ABSTRACT CoV `hcov` for the base-varying chart
      `W₀ z := uniformInverseChart g gi hC hK z 0`   (normal coordinate of the origin seen from `z`).
  J4-514 (`LayerAFactorization`) built the on-gate factorisation with origin-value = 1.  The concrete
  `hcov` still needs the **Layer-B CoV bundle** for `W₀`: injectivity (M1), left inverse (M2), positive
  Jacobian (M3), `HasFDerivWithinAt`/`|det DW₀(0)| = 1` (M4), and the Gaussian-phase domination.

  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It builds
  the SMALLEST solid Layer-B unit: the **Gaussian-phase MAJORANT**.  Per Sol's verdict, the
  `|det DW₀(0)| = 1` route is BLOCKED (no banked base-point `fderiv` of `z ↦ W₀ z`; the chart is
  `.choose`-built, blocker (2) of `InverseChartDisplacement`), so we build the domination, which is
  robustly banked via the two-sided near-isometry `chartW0_rncRadialSq_error`.

  ── WHAT IS BANKED (reused, not rebuilt — all axiom-free std-3, curved `g` generic).
    * `chartW0_rncRadialSq_error` (`InverseChartDisplacement`) — the TWO-SIDED ℓ²-near-isometry error
        `|rncRadialSq(W₀ z) − rncRadialSq z| ≤ L·‖z‖·rncRadialSq z`  for `z∈K`, `‖z‖<r₀`, explicit `L≥0`.
    * `gaussDdim_eq_exp`, `gaussDdimWide` (`ResidueBound`) — closed exp forms
        `gaussDdim τ v = (√(4πτ))⁻ⁿ·exp(−r²/4τ)`,  `gaussDdimWide τ v = (√(4πτ))⁻ⁿ·exp(−r²/8τ)`.

  ── WHAT THIS FILE PROVES (the genuine new Layer-B content).
    (1)  `chartW0_radialSq_half_lower` — ★ the half radial lower bound on a small ball:
             `(1/2)·rncRadialSq z ≤ rncRadialSq (W₀ z)`   for `z∈K`, `‖z‖` small.
         From the two-sided error, shrinking the radius so `L·‖z‖ ≤ 1/2` (`L=0`-safe formulation).
    (2)  `gaussDdim_chartW0_le_wide` — ★★ THE GAUSSIAN-PHASE DOMINATION (constant `C = 1`, prefactors
         cancel):  `gaussDdim τ (W₀ z) ≤ gaussDdimWide τ z`   for `z∈K`, `‖z‖` small, `∀τ>0`.
         From (1): `rncRadialSq(W₀ z) ≥ ½·rncRadialSq z ⟹ exp(−rncRadialSq(W₀z)/4τ) ≤
         exp(−rncRadialSq z/8τ)`.  ⚠ NOTE THE WIDTH CHANGE `4τ → 8τ` — a WIDENED Gaussian.
    (★gate)  `phase_domination_curved_satisfiable` — the SATISFIABILITY GATE: the core half-lower
         inequality is inhabited by a GENUINELY DISTORTING (non-isometric) radial map `W z = (4/5)·z`
         (`c ≠ ±1`), certifying the domination does NOT secretly force the isometric/flat `W z = ±z`.

  ⚠  THE WIDTH QUESTION (Sol-confirmed, honest scoping).  The widened Gaussian `gaussDdimWide` is a
  valid MAJORANT for integrability / `hbound` / tail / off-diagonal control — but it carries the WRONG
  total mass (`∫_{ℝⁿ} gaussDdimWide τ = 2^{n/2} ≠ 1`), so it must NOT be used to compute the unit mass.
  The exact unit mass = 1 comes from the EXACT (un-widened) `gaussDdim` after the exact CoV (or from
  asymptotically sharp `(1±δ)` comparisons, `δ→0`).  Hence this brick discharges the INTEGRABILITY /
  DOMINATION side conditions of the concrete `hcov`, NOT the exact CoV equality itself.

  ── WHAT REMAINS of the Layer-B bundle (NOT discharged here): M1 injectivity of `z↦W₀ z`, M2 left
     inverse + support/cutoff transport, M3 positive/absolute Jacobian on the domain, M4
     `HasFDerivWithinAt` / `|det DW₀(0)| = 1` (needs the currently-unbanked base-point `fderiv`), the
     EXACT CoV equality (Jacobian cancellation), and the `MassChartBridge` assembly.

  No `sorry`, no new axioms, no `:= True`, no vacuous hypotheses, no conclusion-in-disguise.  No
  existing file is edited.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InverseChartDisplacement
import QIQTH.ResidueBound

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.RNCDecay
open QIQTH.HeatResidualBound
open scoped Topology BigOperators

namespace QIQTH.LayerBChangeVars

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### (1) — the half radial lower bound `(1/2)·rncRadialSq z ≤ rncRadialSq (W₀ z)`. -/

/-- **★ J4-515 (Layer-B/1) — THE HALF RADIAL LOWER BOUND.**  There is `r > 0` such that for every base
    point `z ∈ K` with `‖z‖ < r`, the inverse-chart origin coordinate `W₀ z = uniformInverseChart …`
    satisfies
        `(1/2)·rncRadialSq z ≤ rncRadialSq (W₀ z)`.
    Route: the banked TWO-SIDED near-isometry error `chartW0_rncRadialSq_error` gives
    `rncRadialSq z − L·‖z‖·rncRadialSq z ≤ rncRadialSq(W₀ z)`; on the shrunk ball `‖z‖ < 1/(2(L+1))`
    (so `L·‖z‖ ≤ 1/2`, `L = 0`-safe) the deficit `L·‖z‖·rncRadialSq z ≤ (1/2)·rncRadialSq z`.  Curved:
    inherits the full `g`-genericity of `chartW0_rncRadialSq_error` (only `hC` = `christoffel` regular).
    NOT `a₁ = R/6`. -/
theorem chartW0_radialSq_half_lower (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ z ∈ K, ‖z‖ < r →
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0) := by
  obtain ⟨r₀, hr₀, L, hL0, hraw⟩ := chartW0_rncRadialSq_error g gi hC hK
  refine ⟨min r₀ (1 / (2 * (L + 1))), lt_min hr₀ (by positivity), ?_⟩
  intro z hz hzr
  have hzr₀ : ‖z‖ < r₀ := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzL : ‖z‖ < 1 / (2 * (L + 1)) := lt_of_lt_of_le hzr (min_le_right _ _)
  obtain ⟨hlow, _⟩ := hraw z hz hzr₀
  have hLz : L * ‖z‖ ≤ 1 / 2 := by
    have hstep : L * ‖z‖ ≤ L * (1 / (2 * (L + 1))) := mul_le_mul_of_nonneg_left hzL.le hL0
    have hbound : L * (1 / (2 * (L + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith [hL0]
    linarith
  nlinarith [hlow, hLz, rncRadialSq_nonneg z]

/-! ### (2) — the Gaussian-phase domination `gaussDdim τ (W₀ z) ≤ gaussDdimWide τ z`. -/

/-- **★★ J4-515 (Layer-B/2) — THE GAUSSIAN-PHASE DOMINATION.**  There is `r > 0` such that for every
    base point `z ∈ K` with `‖z‖ < r` and every `τ > 0`, the chart-image Gaussian is dominated by the
    WIDENED Gaussian at the un-transported argument (constant `C = 1`, prefactors cancel):
        `gaussDdim τ (W₀ z) ≤ gaussDdimWide τ z`.
    Route: `chartW0_radialSq_half_lower` gives `rncRadialSq(W₀ z) ≥ (1/2)·rncRadialSq z`, hence
    `−rncRadialSq(W₀ z)/(4τ) ≤ −rncRadialSq z/(8τ)`; `Real.exp` monotone, common nonneg prefactor
    `(√(4πτ))⁻ⁿ`.  ⚠ WIDTH CHANGE `4τ → 8τ`: `gaussDdimWide` is a MAJORANT for integrability / `hbound`
    / tail control ONLY — it carries the WRONG total mass (`∫ gaussDdimWide = 2^{n/2} ≠ 1`), so it must
    NOT be used to compute the unit mass (that needs the exact `gaussDdim` after the exact CoV).  Curved:
    inherits `g`-genericity from (1).  NOT `a₁ = R/6`. -/
theorem gaussDdim_chartW0_le_wide (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ z ∈ K, ‖z‖ < r → ∀ τ : ℝ, 0 < τ →
      gaussDdim τ (uniformInverseChart g gi hC hK z 0) ≤ gaussDdimWide τ z := by
  obtain ⟨r, hr, hhalf⟩ := chartW0_radialSq_half_lower g gi hC hK
  refine ⟨r, hr, fun z hz hzr τ hτ => ?_⟩
  have hlow := hhalf z hz hzr
  rw [gaussDdim_eq_exp, gaussDdimWide]
  have hτ4 : (0 : ℝ) < 4 * τ := by positivity
  have hτ8 : (0 : ℝ) < 8 * τ := by positivity
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  set A : ℝ := rncRadialSq (uniformInverseChart g gi hC hK z 0) with hAdef
  set B : ℝ := rncRadialSq z with hBdef
  have hexp : -A / (4 * τ) ≤ -B / (8 * τ) := by
    have hnum : (0 : ℝ) ≤ 2 * A - B := by linarith [hlow]
    have heq : -B / (8 * τ) - -A / (4 * τ) = (2 * A - B) / (8 * τ) := by
      field_simp; ring
    have hge : (0 : ℝ) ≤ (2 * A - B) / (8 * τ) := div_nonneg hnum (le_of_lt hτ8)
    linarith [heq, hge]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)

/-! ### (★gate) — the satisfiability gate: the half-lower bound tolerates genuine (non-isometric)
    radial distortion, so the domination is NOT secretly flat. -/

/-- **★ J4-515 (Layer-B satisfiability GATE) — THE DOMINATION DOES NOT FORCE AN ISOMETRY.**  The core
    half-lower inequality `(1/2)·rncRadialSq z ≤ rncRadialSq (W z)` is inhabited by a GENUINELY
    DISTORTING radial map `W z = c·z` with `c = 4/5 ≠ ±1` (`c² = 16/25 ≥ 1/2`), for EVERY `z`.  This
    certifies the phase domination does NOT secretly require the isometric / flat behaviour `W z = ±z`:
    it tolerates a real radial contraction (the curved-normal-coordinate distortion).  Curved-inhabited.
    NOT `a₁ = R/6`. -/
theorem phase_domination_curved_satisfiable :
    ∃ c : ℝ, c ≠ 1 ∧ c ≠ -1 ∧ ∀ z : Point n,
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (fun i => c * z i) := by
  refine ⟨4 / 5, by norm_num, by norm_num, fun z => ?_⟩
  have hscale : rncRadialSq (fun i => (4 / 5 : ℝ) * z i) = (4 / 5 : ℝ) ^ 2 * rncRadialSq z := by
    simp only [rncRadialSq, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hscale]
  nlinarith [rncRadialSq_nonneg z]

end QIQTH.LayerBChangeVars

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.LayerBChangeVars

#print axioms chartW0_radialSq_half_lower
#print axioms gaussDdim_chartW0_le_wide
#print axioms phase_domination_curved_satisfiable

end AxiomChecks
