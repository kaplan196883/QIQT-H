/-
  ChartGeneralChangeVarEvalSlot — J4-1012: the GENERIC (non-Gaussian-specialized) weighted
  change-of-variables, applied at the EVAL-slot chart of general base `q₀`, and instantiated at the
  composed integrand `gaussDdim τ (T_x (W_x z))` that `hcomp`'s near carry `nb`'s STEP-4c residual
  (r6) genuinely needs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  J4-1011 (`ChartIFTPackageGeneralQ0`) built the EVAL-slot local IFT/CoV package at a
  general interior base `q₀`, but its concrete corollary (`chart_gaussian_change_variables_concrete_
  generalQ0`) is SPECIALIZED to the bare Gaussian `gaussDdim τ (W_{q₀} z)` — i.e. `φ := gaussDdim τ`
  applied DIRECTLY to the moving chart value.  `nb`'s STEP-4c composition instead needs the Gaussian
  applied to `T_x (W_x z)` — the near-isometry `T_x := terminalVelAt g gi hC hK x` COMPOSED with the
  eval-slot chart, via the evenness link `HCompNearCarryFullyClosed.gaussDdim_reversal_link`:
      `gaussDdim τ (U z x) = gaussDdim τ (T_x (W_x z))`   (eventually, `z` near `x`),
  `W_x z := uniformInverseChart g gi hC hK x z`.  The existing `ChartGaussianChangeVar.chart_gaussian_
  change_variables` / its `generalQ0` corollary do NOT cover this: their integrand shape is hard-wired
  to `gaussDdim τ (W z)`, not `φ (W z)` for an arbitrary `φ`.  Sol `gpt-5.6-sol` (high, this dispatch's
  predecessor) flagged exactly this — "a generic (non-Gaussian-specialized) weighted CoV to transport
  `∫ G_τ(T_x(W_x z)) · B(z) dz` itself" — as the remaining moving piece.

  THIS FILE supplies it in two layers:
    • `chart_general_change_variables` — the ABSTRACT generalization of `ChartGaussianChangeVar.
      chart_gaussian_change_variables` to an ARBITRARY integrand function `φ : Point n → ℝ` in place
      of the hard-wired `gaussDdim τ`.  Same proof (Mathlib's unconditional Bochner CoV
      `integral_image_eq_integral_abs_det_fderiv_smul` + the on-`S` `V`/`J` cancellation), with `φ`
      threaded through instead of `gaussDdim τ`.
    • `chart_general_change_variables_concrete_generalQ0` — the concrete corollary at the eval-slot
      chart `W_{q₀}` (general interior `q₀`), using J4-1011's IFT package M1–M4.
    • `evalSlot_terminalVel_weighted_CoV` — the TARGETED instantiation at `φ := fun w => gaussDdim τ
      (terminalVelAt g gi hC hK x w)`, `q₀ := x`: literally transports
          `∫ z in ball x ρ, gaussDdim τ (T_x (W_x z)) · B z`
      onto the chart-image integral `∫ w in W_x '' (ball x ρ), gaussDdim τ (T_x w) · (B (V w) / J (V w))`.
      This is EXACTLY item (a) of the remaining STEP-4c composition Sol flagged: the weighted CoV
      transport of the `T_x`-composed Gaussian.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  supplies item (a) (the weighted CoV transport) ALONE.  It does **NOT** supply item (b) — the domain
  reconciliation identifying the CoV image `W_x '' (ball x ρ)` with `terminalVelAt_chartReplace_
  sliver_bound`'s domain `ball 0 R` (or a genuine sub-ball restriction lemma between them) — nor does
  it compose this transport with the evenness link (`gaussDdim_reversal_link`), with `nb`'s literal
  `kPrime` factorization (`HCompNearCarryKPrimeBaseFieldCoV`), or with `terminalVelAt_chartReplace_
  sliver_bound` itself to produce a literal difference-form bound on `nb`.  Those remain SEPARATE,
  NOT-attempted next steps.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none
  equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ChartIFTPackageGeneralQ0
import QIQTH.GeodesicReversalRouteAtPoint

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.JointRNCRegularityLocalGeneralK
open QIQTH.GeodesicReversalRouteAtPoint
open scoped Topology

namespace QIQTH.ChartGeneralChangeVarEvalSlot

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the ABSTRACT generic-integrand change of variables.
    ############################################################################### -/

/-- **★ `chart_general_change_variables` — the GENERIC (non-Gaussian-specialized) weighted CoV.**
    Generalizes `ChartGaussianChangeVar.chart_gaussian_change_variables` from the hard-wired
    integrand `gaussDdim τ` to an ARBITRARY `φ : Point n → ℝ`: for a map `W` differentiable with
    derivative `f' z` and injective on a measurable set `S`, with left inverse `V` and everywhere-
    positive Jacobian `J` on `S`,
        `∫ z in S, φ (W z) · B z = ∫ w in W '' S, φ w · (B (V w) / J (V w))`.
    Identical proof route (Mathlib's unconditional Bochner CoV, then on-`S` cancellation), with `φ`
    threaded through in place of `gaussDdim τ`.  NOT `a₁ = R/6`. -/
theorem chart_general_change_variables
    (φ : Point n → ℝ) (S : Set (Point n)) (W V : Point n → Point n)
    (f' : Point n → (Point n →L[ℝ] Point n)) (J B : Point n → ℝ)
    (hS : MeasurableSet S)
    (hfd : ∀ z ∈ S, HasFDerivWithinAt W (f' z) S z)
    (hinj : Set.InjOn W S)
    (hV : ∀ z ∈ S, V (W z) = z)
    (hJ : ∀ z ∈ S, J z = |(f' z).det|)
    (hJpos : ∀ z ∈ S, 0 < J z) :
    (∫ z in S, φ (W z) * B z)
      = ∫ w in W '' S, φ w * (B (V w) / J (V w)) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul
        (volume) hS hfd hinj (fun w => φ w * (B (V w) / J (V w)))]
  refine setIntegral_congr_fun hS (fun z hz => ?_)
  simp only [smul_eq_mul]
  rw [hV z hz, hJ z hz]
  have hdpos : 0 < |(f' z).det| := by rw [← hJ z hz]; exact hJpos z hz
  have hd : |(f' z).det| ≠ 0 := ne_of_gt hdpos
  field_simp

/-! ###############################################################################
    ### §2 — the concrete corollary at the eval-slot chart, general interior `q₀`.
    ############################################################################### -/

/-- **`chart_general_change_variables_concrete_generalQ0`.**  Instantiates `chart_general_change_
    variables` at the concrete eval-slot chart `W_{q₀} = uniformInverseChart g gi hC hK q₀` (general
    interior `q₀`), with the M1–M4 bundle discharged by `ChartIFTPackageGeneralQ0.chartIFTPackage_
    generalQ0`, for an ARBITRARY `φ`:
        `∫ z in ball q₀ ρ, φ (W_{q₀} z) · B z = ∫ w in W_{q₀} '' (ball q₀ ρ), φ w · (B (V w) / |det|)`.
    General-`φ` analogue of `ChartIFTPackageGeneralQ0.chart_gaussian_change_variables_concrete_
    generalQ0`.  NOT `a₁ = R/6`. -/
theorem chart_general_change_variables_concrete_generalQ0
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (φ : Point n → ℝ) (B : Point n → ℝ) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      (∫ z in Metric.ball q₀ ρ, φ (uniformInverseChart g gi hC hK q₀ z) * B z)
        = ∫ w in (uniformInverseChart g gi hC hK q₀) '' (Metric.ball q₀ ρ),
            φ w * (B (V w) / |(f' (V w)).det|) := by
  obtain ⟨ρ, hρ, V, f', hS, hfd, hinj, hV, hJpos, _⟩ :=
    QIQTH.ChartIFTPackageGeneralQ0.chartIFTPackage_generalQ0 g gi hC hK hq₀
  exact ⟨ρ, hρ, V, f',
    chart_general_change_variables φ (Metric.ball q₀ ρ)
      (uniformInverseChart g gi hC hK q₀) V f' (fun z => |(f' z).det|) B
      hS hfd hinj hV (fun _ _ => rfl) hJpos⟩

/-! ###############################################################################
    ### §3 — the TARGETED instantiation: `φ := gaussDdim τ ∘ terminalVelAt … x`.
    ############################################################################### -/

/-- **★★ `evalSlot_terminalVel_weighted_CoV` — item (a) of `nb`'s STEP-4c residual (r6).**  The
    eval-slot CoV, at base `q₀ := x`, specialized to `φ := fun w => gaussDdim τ (T_x w)`,
    `T_x := terminalVelAt g gi hC hK x`: transports the WEIGHTED integral of the `T_x`-COMPOSED
    Gaussian
        `∫ z in ball x ρ, gaussDdim τ (T_x (W_x z)) · B z`
    onto the chart-image integral
        `∫ w in W_x '' (ball x ρ), gaussDdim τ (T_x w) · (B (V w) / |det|)`,
    `W_x z := uniformInverseChart g gi hC hK x z`.  This is the LITERAL weighted CoV transport Sol
    flagged as remaining (item (a)): it is NOT the bare-Gaussian CoV of `ChartIFTPackageGeneralQ0`
    (which cannot absorb the `T_x` composition), but the genuinely generalized version via §1's
    generic-`φ` template.  Domain reconciliation with `terminalVelAt_chartReplace_sliver_bound`'s
    `ball 0 R` (item (b)) and composition with the evenness link / literal `kPrime` factorization
    remain SEPARATE, NOT supplied here.  NOT `a₁ = R/6`. -/
theorem evalSlot_terminalVel_weighted_CoV
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x : Point n} (hxint : x ∈ interior K)
    (τ : ℝ) (B : Point n → ℝ) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      (∫ z in Metric.ball x ρ,
          gaussDdim τ (terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z)) * B z)
        = ∫ w in (uniformInverseChart g gi hC hK x) '' (Metric.ball x ρ),
            gaussDdim τ (terminalVelAt g gi hC hK x w) * (B (V w) / |(f' (V w)).det|) := by
  exact chart_general_change_variables_concrete_generalQ0 g gi hC hK hxint
    (fun w => gaussDdim τ (terminalVelAt g gi hC hK x w)) B

end QIQTH.ChartGeneralChangeVarEvalSlot

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.ChartGeneralChangeVarEvalSlot
#print axioms chart_general_change_variables
#print axioms chart_general_change_variables_concrete_generalQ0
#print axioms evalSlot_terminalVel_weighted_CoV
end AxiomChecks
