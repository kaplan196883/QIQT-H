/-
  ReversalLinkBallIntegral — J4-1013: lifting `HCompNearCarryFullyClosed.gaussDdim_reversal_link`'s
  LOCAL (`=ᶠ[𝓝 x]`) evenness/reversal equality of Gaussians to a LITERAL, radius-explicit weighted
  BALL-INTEGRAL identity — the sub-piece Sol `gpt-5.6-sol` (high, this dispatch's plan-review)
  recommended as the smallest genuinely non-vacuous next increment on `hcomp`'s near carry `nb`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  `nb`'s STEP-4c composition needs to bridge:
    • J4-1010's `kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp` — `kPrime`'s literal integrand
      factors as the BASE-slot Gaussian `gaussDdim (t−s) (U z x) · Bfac z`, `U z x := uniformInverseChart
      g gi hC hK z x` (`z` = moving chart BASE, `x` = fixed field point);
    • J4-1012's `evalSlot_terminalVel_weighted_CoV` — the weighted change-of-variables transports the
      EVAL-slot, `T_x`-COMPOSED shape `gaussDdim τ (T_x (W_x z))`, `W_x z := uniformInverseChart g gi hC
      hK x z` (`x` fixed BASE, `z` moving FIELD), `T_x := terminalVelAt g gi hC hK x`.
  `HCompNearCarryFullyClosed.gaussDdim_reversal_link` connects these two POINTWISE shapes, but only as
  a `Filter.EventuallyEq` (`=ᶠ[𝓝 x]`) — a LOCAL, radius-FREE statement.  To actually compose it with an
  INTEGRAL (either the literal `kPrime` integral or J4-1012's CoV, both stated over an explicit ball
  `ball x ρ`), the `=ᶠ` needs to be converted into an EXPLICIT radius `r > 0` with the pointwise equality
  holding on `dist z x < r`, and then LIFTED to a ball-integral identity for every `0 < ρ ≤ r`.

  gpt-5.6-sol (high, this dispatch, plan-reviewed before Lean) confirmed: (i) full closure of `nb` from
  the currently-banked pieces is NOT justified — the uncontrolled existential radii from J4-1012's IFT
  package and J4-879's near-isometry data have no established comparability, and even with a domain
  match the transformed weight/Jacobian is not yet dominated by J4-879's moment weight; (ii) the
  smallest genuinely non-vacuous, non-trivial sub-lemma to bank THIS round is exactly this radius-
  explicit ball-integral lift of the reversal link.

  THIS FILE supplies it:
    • `reversal_link_ball_radius` — extracts an explicit `r > 0` from `gaussDdim_reversal_link`'s
      `=ᶠ[𝓝 x]` via `Metric.eventually_nhds_iff`, with the POINTWISE equality holding for every `z` with
      `dist z x < r`.
    • `reversal_link_ball_integral` — the payoff: for EVERY `0 < ρ ≤ r` and EVERY amplitude `B`,
          `∫ z in ball x ρ, gaussDdim τ (U z x) · B z = ∫ z in ball x ρ, gaussDdim τ (T_x (W_x z)) · B z`
      — a literal, radius-controlled weighted ball-integral identity connecting the BASE-slot Gaussian
      shape `kPrime` factors into (item 5 above) to the EVAL-slot `T_x`-composed shape J4-1012's CoV
      consumes (item 2 above), on the SAME explicit ball `ball x ρ` for any `ρ` not exceeding `r`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It removes
  ONE genuine obstruction (converting the `=ᶠ[𝓝 x]` evenness/reversal link into a literal, radius-
  explicit weighted ball-integral identity) but does **NOT**:
    • reconcile `r` (this file) with J4-1012's IFT-package `ρ` or J4-879's near-isometry-data `R` — no
      comparability between these THREE independently-existentially-quantified radii is established;
    • compose this identity with J4-1012's weighted CoV, J4-1010's `kPrime` factorization, or J4-879's
      `terminalVelAt_chartReplace_sliver_bound` into any literal difference-form bound on `nb`;
    • supply any domain-containment fact `W_x''(ball x ρ) ⊆ ball 0 R` (Sol: NOT derivable from the
      banked chart∘exp=id germ alone — would need `ContinuousAt W_x x` with `W_x x = 0`, not yet banked
      in this form) or any weight/Jacobian domination against J4-879's moment weight.
  Those remain SEPARATE, NOT-attempted next steps.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryFullyClosed

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.GeodesicReversalRouteAtPoint
open QIQTH.FlatHeatEquation
open scoped Topology

namespace QIQTH.ReversalLinkBallIntegral

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — extracting an explicit radius from the `=ᶠ[𝓝 x]` reversal link.
    ############################################################################### -/

/-- **`reversal_link_ball_radius`.**  `gaussDdim_reversal_link`'s local (`=ᶠ[𝓝 x₀]`) equality,
    converted via `Metric.eventually_nhds_iff` into an EXPLICIT radius `r > 0` with the pointwise
    equality
        `gaussDdim τ (U z x₀) = gaussDdim τ (T_x₀ (U x₀ z))`
    holding for EVERY `z` with `dist z x₀ < r`, `U z x₀ := uniformInverseChart g gi hC hK z x₀`,
    `T_x₀ := terminalVelAt g gi hC hK x₀`.  NOT `a₁ = R/6`. -/
theorem reversal_link_ball_radius (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀Kmem : K ∈ 𝓝 x₀) (τ : ℝ) :
    ∃ r > (0 : ℝ), ∀ z : Point n, dist z x₀ < r →
      gaussDdim τ (uniformInverseChart g gi hC hK z x₀)
        = gaussDdim τ (terminalVelAt g gi hC hK x₀ (uniformInverseChart g gi hC hK x₀ z)) := by
  have hev := QIQTH.HCompNearCarryFullyClosed.gaussDdim_reversal_link g gi hC hK hx₀Kmem τ
  obtain ⟨r, hr, hspec⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨r, hr, fun z hz => hspec hz⟩

/-! ###############################################################################
    ### §2 — the payoff: the radius-controlled weighted ball-integral identity.
    ############################################################################### -/

/-- **★★ `reversal_link_ball_integral` — the literal, radius-controlled ball-integral lift.**  For
    EVERY `0 < ρ ≤ r` (`r` from §1) and EVERY amplitude `B : Point n → ℝ`,
        `∫ z in ball x₀ ρ, gaussDdim τ (U z x₀) · B z`
          `= ∫ z in ball x₀ ρ, gaussDdim τ (T_x₀ (U x₀ z)) · B z`,
    `U z x₀ := uniformInverseChart g gi hC hK z x₀` (the BASE-slot shape `kPrime`'s literal factorization,
    J4-1010, produces), `U x₀ z := uniformInverseChart g gi hC hK x₀ z` (the EVAL-slot chart J4-1012's
    weighted CoV is stated for), `T_x₀ := terminalVelAt g gi hC hK x₀`.  This is a LITERAL weighted
    ball-integral identity on the SAME explicit domain `ball x₀ ρ`, for ANY `ρ` not exceeding the
    radius `r` produced here — the smallest genuinely non-vacuous sub-lemma Sol (high, plan-review)
    flagged as the next tractable increment.  Does NOT reconcile `r` with J4-1012's `ρ` or J4-879's
    `R`, nor compose further.  NOT `a₁ = R/6`. -/
theorem reversal_link_ball_integral (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀Kmem : K ∈ 𝓝 x₀) (τ : ℝ) :
    ∃ r > (0 : ℝ), ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ∀ B : Point n → ℝ,
      (∫ z in Metric.ball x₀ ρ, gaussDdim τ (uniformInverseChart g gi hC hK z x₀) * B z)
        = ∫ z in Metric.ball x₀ ρ,
            gaussDdim τ (terminalVelAt g gi hC hK x₀ (uniformInverseChart g gi hC hK x₀ z)) * B z := by
  obtain ⟨r, hr, hspec⟩ := reversal_link_ball_radius g gi hC hK hx₀Kmem τ
  refine ⟨r, hr, fun ρ hρ hρr B => ?_⟩
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  have hzlt : dist z x₀ < r := lt_of_lt_of_le (Metric.mem_ball.mp hz) hρr
  dsimp only
  rw [hspec z hzlt]

end QIQTH.ReversalLinkBallIntegral

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.ReversalLinkBallIntegral
#print axioms reversal_link_ball_radius
#print axioms reversal_link_ball_integral
end AxiomChecks
