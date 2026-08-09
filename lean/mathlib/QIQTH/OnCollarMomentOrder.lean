/-
  OnCollarMomentOrder — J4-492: the near-diagonal (ON-collar) moment-order bound, carrying the
  (I1)-closed collar constants `M₀/M₁/M₂` into the near-diagonal moment integral.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  No `sorry` (header prose excepted),
  no `:= True`, no new axioms, no vacuous / unsatisfiable hypothesis, no result equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.  std-3 only.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT — the COMPLEMENTARY leg to J4-491's far field.  The on-collar (near-diagonal) sliver
  integrand `witnessSecondXDeriv · F` expands (on the √ε collar, `SliverBoundOnCollar.sliverIntegrand_on_collar`)
  into the 3-term Gaussian shape
      `(z_i²−2τ)/(4τ²)·G_τ·Aamp  +  z_i/(2τ)·G_τ·A1amp  +  G_τ·A2amp`,
  with the amplitudes bounded by the (I1)-closed COLLAR constants of
  `C2AggregatorPhase6.collarSupConstants_of_reach` (J4-490):  `|Aamp| ≤ M₀`, `|A1amp| ≤ M₁`,
  `|A2amp| ≤ M₂`.  Taking absolute values (`|z_i²−2τ| ≤ ‖z‖²+2τ`, `|z_i| ≤ ‖z‖`), the on-collar
  integrand is dominated by the Gaussian-moment envelope
      `onCollarDom τ M₀ M₁ M₂ z
         := M₀·(1/(4τ²))·((‖z‖²+2τ)·G_τ) + M₁·(1/(2τ))·(‖z‖·G_τ) + M₂·G_τ`,   `G_τ = gaussDdim τ z`,
  the HESSIAN coefficient carrying the on-collar `M₀` (= `Aamp` sup), the GRADIENT `M₁`, the MASS `M₂`.

  ## WHAT LANDS (the near-diagonal τ-order — the mirror image of J4-491).
    ★  `onCollarDom_eq_farFieldDom` — the envelope is (up to the term reordering `M₁,M₂,M₀`) the SAME
       Gaussian-moment object as `FarFieldDecay.farFieldDom` (a pure `ring` regroup), so the banked
       far-field integral computation is reused verbatim — NO new analysis.
    ★  `onCollarDom_integral_le` — the FULL-space closed form
         `∫_z onCollarDom τ M₀ M₁ M₂ z  ≤  M₁·(3n/4)/√τ  +  M₂  +  M₀·(n+1)/(2τ)`,
       via `FarFieldMomentOrder.farFieldDom_integral_le`.  Hessian term `M₀·(n+1)/(2τ)` is the DOMINANT
       `O(1/τ)`; gradient `O(τ^{-1/2})`; mass `O(1)`.
    ★★★ `onCollarDom_setIntegral_le` — the GENUINE NEAR-DIAGONAL statement: on ANY measurable subdomain
       `A` (in particular the collar `{‖z‖ ≤ c√τ}` or the chart ball `{‖z‖ < r₀}`) the restricted moment
       integral inherits the SAME `O(1/τ)` order,
         `∫_{z ∈ A} onCollarDom τ M₀ M₁ M₂ z  ≤  M₁·(3n/4)/√τ + M₂ + M₀·(n+1)/(2τ)`,
       because the envelope is nonnegative (`onCollarDom_nonneg`) and full-space-integrable
       (`onCollarDom_integrable`), so `setIntegral_le_integral` restricts.  This is the on-collar leg's
       carry — controlled ENTIRELY by the (I1)-closed constants `M₀/M₁/M₂`.
    ★  `onCollarMoment_order` — the headline specialisation to the collar `collar (c√τ)`.

  ## THE GATE (satisfiability — checked BEFORE building).  REACHABLE.  `M₀,M₁,M₂ ≥ 0` are EXACTLY the
  (I1)-closed collar sups delivered nonneg by `collarSupConstants_of_reach`; the moments `‖z‖`, `‖z‖²`
  are relative to the DIAGONAL CENTER `0` (the width-τ Gaussian `gaussDdim τ z` is centered at `0`, the
  near-diagonal point), so the centering trap is avoided; the moment envelope is BANKED and TRUE; any
  measurable `A` is inhabited (e.g. the collar, nonempty for `τ > 0`).  No false pointwise inequality,
  no divergent width, no single-coordinate envelope masquerading as a full contraction.

  ## HONEST DISTANCE.  Unlike the far-field leg (whose `M1F/M2F/Mqc` are the OFF-collar GLOBAL sups,
  DISJOINT from the collar constants), THIS leg's `M₀/M₁/M₂` ARE the (I1)-closed ON-collar constants of
  `collarSupConstants_of_reach`.  Together with J4-491's far-field `O(1/τ)` the FULL heat-trace remainder
  (collar ⊔ far field) is now τ-order-controlled: the on-collar leg by the (I1)-closed constants, the far
  field by the global Gaussian remainder.  ⚠ NOT `a₁ = R/6`; `a₁ = R/6` remains CONDITIONAL on the whole
  convergence-trio + geometric-wiring stack.
-/
import QIQTH.FarFieldMomentOrder

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ResidueBound QIQTH.FarFieldDecay QIQTH.FarFieldMomentOrder QIQTH.SliverTailMatched
open scoped BigOperators

namespace QIQTH.OnCollarMomentOrder

variable {n : ℕ}

set_option maxHeartbeats 1200000

/-! ###############################################################################
    ### THE ON-COLLAR (near-diagonal) GAUSSIAN-MOMENT ENVELOPE.
    ############################################################################### -/

/-- **`onCollarDom`.**  THE Gaussian-moment dominator of the on-collar sliver integrand `‖·‖` on the
    √ε collar (from `SliverBoundOnCollar.sliverIntegrand_on_collar` after `|z_i²−2τ| ≤ ‖z‖²+2τ`,
    `|z_i| ≤ ‖z‖`, and the (I1)-closed amplitude sups `|Aamp| ≤ M₀`, `|A1amp| ≤ M₁`, `|A2amp| ≤ M₂`):
      `onCollarDom τ M₀ M₁ M₂ z
         := M₀·(1/(4τ²))·((‖z‖²+2τ)·G_τ) + M₁·(1/(2τ))·(‖z‖·G_τ) + M₂·G_τ`,   `G_τ = gaussDdim τ z`.
    The HESSIAN coefficient carries the on-collar `M₀` (= `Aamp` sup), the GRADIENT `M₁`, the MASS `M₂`.
    ⚠ NOT `a₁ = R/6`. -/
noncomputable def onCollarDom (τ M₀ M₁ M₂ : ℝ) (z : Point n) : ℝ :=
  M₀ * (1 / (4 * τ ^ 2)) * ((‖z‖ ^ 2 + 2 * τ) * gaussDdim τ z)
    + M₁ * (1 / (2 * τ)) * (‖z‖ * gaussDdim τ z)
    + M₂ * gaussDdim τ z

/-- **`onCollarDom_eq_farFieldDom`.**  The on-collar envelope is — up to the term reordering
    `(M₁, M₂, M₀)` — the SAME Gaussian-moment object as `FarFieldDecay.farFieldDom` (a pure `ring`
    regroup).  This lets the banked far-field integral computation be reused verbatim.  ⚠ NOT
    `a₁ = R/6`. -/
theorem onCollarDom_eq_farFieldDom (τ M₀ M₁ M₂ : ℝ) (z : Point n) :
    onCollarDom τ M₀ M₁ M₂ z = farFieldDom τ M₁ M₂ M₀ z := by
  unfold onCollarDom farFieldDom; ring

/-- **`onCollarDom_nonneg`.**  The on-collar envelope is nonnegative (its coefficients `M₀,M₁,M₂ ≥ 0`,
    the Gaussian `G_τ ≥ 0`).  ⚠ NOT `a₁ = R/6`. -/
theorem onCollarDom_nonneg (τ M₀ M₁ M₂ : ℝ) (hτ : 0 < τ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (z : Point n) :
    0 ≤ onCollarDom τ M₀ M₁ M₂ z := by
  rw [onCollarDom_eq_farFieldDom]
  exact farFieldDom_nonneg τ M₁ M₂ M₀ hτ hM₁ hM₂ hM₀ z

/-- **`onCollarDom_integrable`.**  The on-collar envelope is full-space integrable (congruent to the
    banked-integrable `farFieldDom`).  ⚠ NOT `a₁ = R/6`. -/
theorem onCollarDom_integrable (τ M₀ M₁ M₂ : ℝ) (hτ : 0 < τ) :
    Integrable (onCollarDom (n := n) τ M₀ M₁ M₂) volume :=
  (farFieldDom_integrable τ M₁ M₂ M₀ hτ).congr
    (ae_of_all _ (fun z => (onCollarDom_eq_farFieldDom τ M₀ M₁ M₂ z).symm))

/-! ###############################################################################
    ### ★ THE FULL-SPACE ON-COLLAR MOMENT ORDER (dominant `O(1/τ)`).
    ############################################################################### -/

/-- **★ `onCollarDom_integral_le` — the on-collar moment ORDER (full space).**  The on-collar
    Gaussian-moment envelope integrates to the explicit closed form, each summand's τ-order manifest:
      `∫_z onCollarDom τ M₀ M₁ M₂ z  ≤  M₁·(3n/4)/√τ  +  M₂  +  M₀·(n+1)/(2τ)`.
    The Hessian term `M₀·(n+1)/(2τ)` (carrying the on-collar `Aamp` sup `M₀`) is the honest DOMINANT
    `O(1/τ)`; the gradient term is `O(τ^{-1/2})`, the mass term `O(1)`.  Reuses
    `FarFieldMomentOrder.farFieldDom_integral_le` verbatim via `onCollarDom_eq_farFieldDom`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem onCollarDom_integral_le (τ M₀ M₁ M₂ : ℝ) (hτ : 0 < τ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) :
    ∫ z : Point n, onCollarDom τ M₀ M₁ M₂ z
      ≤ M₁ * (n : ℝ) * 3 / 4 / Real.sqrt τ + M₂ + M₀ * ((n : ℝ) + 1) / (2 * τ) := by
  have heq : ∫ z : Point n, onCollarDom τ M₀ M₁ M₂ z
      = ∫ z : Point n, farFieldDom τ M₁ M₂ M₀ z :=
    integral_congr_ae (ae_of_all _ (fun z => onCollarDom_eq_farFieldDom τ M₀ M₁ M₂ z))
  rw [heq]
  exact farFieldDom_integral_le τ M₁ M₂ M₀ hτ hM₁ hM₂ hM₀

/-! ###############################################################################
    ### ★★★ THE GENUINE NEAR-DIAGONAL BOUND — the on-collar leg's carry on any subdomain.
    ############################################################################### -/

/-- **★★★ `onCollarDom_setIntegral_le` — the NEAR-DIAGONAL on-collar moment order.**  On ANY measurable
    subdomain `A` (in particular the collar `{‖z‖ ≤ c√τ}` or the chart ball `{‖z‖ < r₀}`) the restricted
    on-collar moment integral inherits the SAME `O(1/τ)` order as the full space:
      `∫_{z ∈ A} onCollarDom τ M₀ M₁ M₂ z  ≤  M₁·(3n/4)/√τ + M₂ + M₀·(n+1)/(2τ)`.
    Because `onCollarDom ≥ 0` (`onCollarDom_nonneg`) and is full-space integrable
    (`onCollarDom_integrable`), `setIntegral_le_integral` restricts the full-space bound to `A`.  This
    is the ON-collar leg's carry — controlled ENTIRELY by the (I1)-closed collar constants `M₀/M₁/M₂` of
    `collarSupConstants_of_reach`.  The COMPLEMENT of J4-491's far-field `O(1/τ)`.  ⚠ NOT `a₁ = R/6`. -/
theorem onCollarDom_setIntegral_le (τ M₀ M₁ M₂ : ℝ) (hτ : 0 < τ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (A : Set (Point n)) :
    ∫ z in A, onCollarDom τ M₀ M₁ M₂ z
      ≤ M₁ * (n : ℝ) * 3 / 4 / Real.sqrt τ + M₂ + M₀ * ((n : ℝ) + 1) / (2 * τ) := by
  refine le_trans ?_ (onCollarDom_integral_le τ M₀ M₁ M₂ hτ hM₀ hM₁ hM₂)
  exact setIntegral_le_integral (onCollarDom_integrable τ M₀ M₁ M₂ hτ)
    (ae_of_all _ (fun z => onCollarDom_nonneg τ M₀ M₁ M₂ hτ hM₀ hM₁ hM₂ z))

/-- **★★★ `onCollarMoment_order` — the headline collar specialisation.**  On the √ε collar
    `collar (c√τ) = {z : ‖z‖ ≤ c√τ}` the on-collar Gaussian-moment integral is `O(1/τ)`:
      `∫_{z ∈ collar (c√τ)} onCollarDom τ M₀ M₁ M₂ z  ≤  M₁·(3n/4)/√τ + M₂ + M₀·(n+1)/(2τ)`.
    This is the near-diagonal moment carry that combines with `FarFieldMomentOrder.farFieldDom_integral_le`
    (the off-collar `O(1/τ)`) to control the FULL heat-trace remainder (collar ⊔ far field).  ⚠ NOT
    `a₁ = R/6`. -/
theorem onCollarMoment_order (τ M₀ M₁ M₂ c : ℝ) (hτ : 0 < τ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) :
    ∫ z in collar (n := n) (c * Real.sqrt τ), onCollarDom τ M₀ M₁ M₂ z
      ≤ M₁ * (n : ℝ) * 3 / 4 / Real.sqrt τ + M₂ + M₀ * ((n : ℝ) + 1) / (2 * τ) :=
  onCollarDom_setIntegral_le τ M₀ M₁ M₂ hτ hM₀ hM₁ hM₂ (collar (n := n) (c * Real.sqrt τ))

end QIQTH.OnCollarMomentOrder

/-! ###############################################################################
    ## J4-492 LEDGER — the near-diagonal (on-collar) moment order.
    ###############################################################################

  WHAT LANDS.  `onCollarDom_setIntegral_le` / `onCollarMoment_order` bound the near-diagonal on-collar
  Gaussian-moment integral by the explicit closed form `M₁·(3n/4)/√τ + M₂ + M₀·(n+1)/(2τ)`, exhibiting
  the on-collar decay order term-by-term: gradient `O(τ^{-1/2})`, mass `O(1)`, Hessian `O(τ^{-1})`
  (DOMINANT).  The dominator carries the (I1)-closed COLLAR constants `M₀/M₁/M₂` of
  `C2AggregatorPhase6.collarSupConstants_of_reach` (M₀ = `Aamp`/Hessian sup, M₁ = `A1amp`/gradient sup,
  M₂ = `A2amp`/mass sup), so the on-collar leg's τ-order is controlled by (I1) `hReach` ALONE.

  THE GATE (satisfiability).  REACHABLE.  `M₀,M₁,M₂ ≥ 0` are the nonneg (I1)-closed collar sups; the
  moments are centered at the diagonal `0` (the width-τ Gaussian `gaussDdim τ z`); any measurable `A`
  (collar / ball) is inhabited.  No false pointwise inequality, no divergent width, no centering error.

  DON'T-UNDERCREDIT.  The heavy analysis was ALREADY BANKED and reused verbatim: the full-space moment
  computation `FarFieldMomentOrder.farFieldDom_integral_le` (its width-τ moments `normPow_gauss_tau`,
  mass identity `gaussDdim_integral_eq_one`, integrability `normPow_gauss_integrable`), and the observation
  (`onCollarDom_eq_farFieldDom`, a `ring` regroup) that the on-collar envelope is the SAME Gaussian-moment
  object as the far-field one under the term reordering `(M₁,M₂,M₀)`.  The genuinely NEW content is the
  DOMAIN RESTRICTION to the near-diagonal region (`setIntegral_le_integral`, nonneg envelope) and the
  KEYING of the dominator to the on-collar sliver coefficient structure (Hessian↔M₀, gradient↔M₁,
  mass↔M₂), matching the `collarSupConstants_of_reach` constants — a thin, honest adapter (mirroring the
  `GateFarFieldSplit.comparison_gate_bound` restriction idiom), NOT a re-derivation.

  HONEST DISTANCE.  In CONTRAST to J4-491 (far-field, whose sups are the OFF-collar GLOBAL ones, DISJOINT
  from the collar constants), THIS leg's `M₀/M₁/M₂` ARE the (I1)-closed ON-collar constants.  Together the
  two legs τ-order-control the FULL heat-trace remainder: on-collar by (I1) `hReach`, far field by the
  global Gaussian remainder.  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio +
  geometric-wiring stack; this brick only makes the on-collar moment order explicit and (I1)-carried.
-/

section AxiomChecks
open QIQTH.OnCollarMomentOrder
#print axioms onCollarDom_eq_farFieldDom
#print axioms onCollarDom_nonneg
#print axioms onCollarDom_integrable
#print axioms onCollarDom_integral_le
#print axioms onCollarDom_setIntegral_le
#print axioms onCollarMoment_order
end AxiomChecks
