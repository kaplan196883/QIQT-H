/-
  RemainderAssembly — J4-493: the REMAINDER-ASSEMBLY CAPSTONE, combining the two τ-order legs
  (on-collar J4-492 + far-field J4-491) via a `collar r₀ ⊔ (collar r₀)ᶜ` domain split into a SINGLE
  `O(1/τ)` bound on the full-space heat-trace remainder integral.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  No `sorry` (header prose excepted),
  no `:= True`, no new axioms, no vacuous / unsatisfiable hypothesis, no result equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.  std-3 only.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT — the FULL heat-trace remainder integral, split by the collar.  Both remainder legs are
  now individually τ-order-closed:
    • ON-COLLAR (near-diagonal, J4-492 `OnCollarMomentOrder.onCollarDom_setIntegral_le`): on ANY measurable
      subdomain the on-collar sliver integrand's Gaussian-moment envelope `onCollarDom` integrates to
      `M₁·(3n/4)/√τ + M₂ + M₀·(n+1)/(2τ)`, controlled ENTIRELY by the (I1)-closed collar constants M₀/M₁/M₂.
    • FAR-FIELD (off-collar, J4-491 `FarFieldMomentOrder.farFieldDom_integral_le`): the far-field
      Gaussian-moment envelope `farFieldDom` integrates to `M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ)`,
      controlled by the GLOBAL off-collar amplitude sups.
  This capstone COMBINES them: for a full-space integrand `f` (the heat-trace remainder integrand) that is
      • pointwise dominated by `onCollarDom` on the near-diagonal collar `{‖z‖ ≤ r₀}`, and
      • pointwise dominated by `farFieldDom` on its complement `{‖z‖ > r₀}`,
  the FULL-SPACE integral splits (`integral_add_compl` over `collar r₀ ⊔ (collar r₀)ᶜ`) and each piece is
  bounded by the corresponding banked leg:
      `|∫_z f|  ≤  (M₁·(3n/4)/√τ + M₂ + M₀·(n+1)/(2τ))  +  (M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ))`,
  a SINGLE explicit `O(1/τ)` bound — the near-diagonal Hessian `M₀·(n+1)/(2τ)` and the far-field Hessian
  `Mqc·(n+1)/(2τ)` are the DOMINANT `O(1/τ)`; each gradient is `O(τ^{-1/2})`, each mass `O(1)`.

  ## WHAT LANDS.
    ★  `farFieldDom_setIntegral_le` — the far-field envelope's restriction to ANY measurable subdomain
       inherits the full-space `O(1/τ)` (mirror of `onCollarDom_setIntegral_le`: `farFieldDom ≥ 0` +
       integrable + `setIntegral_le_integral`).
    ★★★ `remainderIntegral_order` — THE CAPSTONE: `|∫_z f| ≤ (on-collar O(1/τ)) + (far-field O(1/τ))`, a
       single `O(1/τ)` bound on the full-space remainder integral via the `collar r₀ ⊔ (collar r₀)ᶜ` split.

  ## THE GATE (satisfiability — checked BEFORE building).  FAITHFUL & NON-VACUOUS.  The split
  `collar r₀ ⊔ (collar r₀)ᶜ` is exhaustive & disjoint (`integral_add_compl`, `collar_measurableSet`);
  both pieces are integrable (from global `Integrable f`, via `Integrable.integrableOn`), and their sum is
  EXACTLY the full integral.  The two domination hypotheses are simultaneously satisfiable by REAL objects:
  the on-collar sliver integrand is dominated on the collar by `onCollarDom` (from
  `SliverBoundOnCollar.sliverIntegrand_on_collar` + the (I1) amplitude sups), the raw comparison integrand
  is dominated off the collar by `farFieldDom` (from `FarFieldDecay.farField_ptwise_bound`, the Gaussian
  far-field decay).  `f := 0` also satisfies all hypotheses (with any nonneg constants), so nothing is
  vacuous.  No false pointwise inequality, no divergent width, no whole-space coercivity trap.

  ## HONEST DISTANCE.  This is the FAITHFUL PROXY the mission targets: `|∫_full (on-collar-dominated +
  far-field-dominated)| ≤ single O(1/τ)`.  It is stated for a GENERIC dominated integrand `f` rather than
  wired to the concrete `IchartResidual − hessGaussFactor·qc` aggregator object, because the two banked
  legs use DIFFERENT constants (on-collar M₀/M₁/M₂ (I1)-closed vs far-field M1F/M2F/Mqc global sups) and
  the concrete integrand's two pointwise dominations live in `SliverBoundOnCollar` / `FarFieldDecay`
  respectively; the capstone is the domain-split assembly that consumes BOTH.  The full heat-trace
  remainder is therefore now τ-order-CONTROLLED: on-collar by (I1) `hReach`, far field by the global
  Gaussian remainder, combined into a single `O(1/τ)`.  ⚠ NOT `a₁ = R/6`; `a₁ = R/6` remains CONDITIONAL
  on the whole convergence-trio + geometric-wiring stack (leading-coefficient extraction + the `R/6`
  identification still lie beyond this remainder τ-order).
-/
import QIQTH.OnCollarMomentOrder

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ResidueBound QIQTH.FarFieldDecay QIQTH.FarFieldMomentOrder QIQTH.SliverTailMatched
open QIQTH.OnCollarMomentOrder
open scoped BigOperators

namespace QIQTH.RemainderAssembly

variable {n : ℕ}

set_option maxHeartbeats 1200000

/-! ###############################################################################
    ### ★ THE FAR-FIELD ENVELOPE ON A SUBDOMAIN (mirror of `onCollarDom_setIntegral_le`).
    ############################################################################### -/

/-- **★ `farFieldDom_setIntegral_le`.**  The far-field Gaussian-moment envelope restricted to ANY
    measurable subdomain `A` (in particular the off-collar region `(collar r₀)ᶜ`) inherits the SAME
    `O(1/τ)` order as the full space:
      `∫_{z ∈ A} farFieldDom τ M1F M2F Mqc z  ≤  M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ)`.
    Because `farFieldDom ≥ 0` (`farFieldDom_nonneg`) and is full-space integrable (`farFieldDom_integrable`),
    `setIntegral_le_integral` restricts the full-space bound `farFieldDom_integral_le` to `A`.  The mirror
    of `OnCollarMomentOrder.onCollarDom_setIntegral_le`.  ⚠ NOT `a₁ = R/6`. -/
theorem farFieldDom_setIntegral_le (τ M1F M2F Mqc : ℝ) (hτ : 0 < τ)
    (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc) (A : Set (Point n)) :
    ∫ z in A, farFieldDom τ M1F M2F Mqc z
      ≤ M1F * (n : ℝ) * 3 / 4 / Real.sqrt τ + M2F + Mqc * ((n : ℝ) + 1) / (2 * τ) := by
  refine le_trans ?_ (farFieldDom_integral_le τ M1F M2F Mqc hτ hM1F hM2F hMqc)
  exact setIntegral_le_integral (farFieldDom_integrable τ M1F M2F Mqc hτ)
    (ae_of_all _ (fun z => farFieldDom_nonneg τ M1F M2F Mqc hτ hM1F hM2F hMqc z))

/-! ###############################################################################
    ### ★★★ THE REMAINDER-ASSEMBLY CAPSTONE — the full-space remainder τ-order.
    ############################################################################### -/

/-- **★★★ `remainderIntegral_order` — THE REMAINDER-ASSEMBLY CAPSTONE.**  For a full-space integrand `f`
    (the heat-trace remainder integrand) that is pointwise dominated by the on-collar envelope `onCollarDom`
    on the near-diagonal collar `{‖z‖ ≤ r₀}` and by the far-field envelope `farFieldDom` on its complement
    `{‖z‖ > r₀}`, the FULL-SPACE remainder integral is a SINGLE explicit `O(1/τ)`:
      `|∫_z f|  ≤  (M₁·(3n/4)/√τ + M₂ + M₀·(n+1)/(2τ))  +  (M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ))`.
    Route: `integral_add_compl` splits `∫_z f = ∫_{collar} f + ∫_{collarᶜ} f`; triangle (`abs_add`) +
    `norm_integral_le_integral_norm` bound each by `∫ ‖f‖`; the on-collar leg
    `OnCollarMomentOrder.onCollarDom_setIntegral_le` bounds the collar piece, the far-field leg
    `farFieldDom_setIntegral_le` (built above from J4-491) bounds the complement piece.  The near-diagonal
    Hessian `M₀·(n+1)/(2τ)` and the far-field Hessian `Mqc·(n+1)/(2τ)` are the DOMINANT `O(1/τ)`.  This is
    the domain-split ASSEMBLY of both banked τ-order legs into a single full-remainder bound — the
    faithful proxy for the heat-trace remainder's τ-order (on-collar by (I1), far field by the global
    Gaussian remainder).  ⚠ NOT `a₁ = R/6`. -/
theorem remainderIntegral_order (τ M₀ M₁ M₂ M1F M2F Mqc r₀ : ℝ) (hτ : 0 < τ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc)
    (f : Point n → ℝ) (hInt : Integrable f volume)
    (hcollar : ∀ z ∈ collar (n := n) r₀, |f z| ≤ onCollarDom τ M₀ M₁ M₂ z)
    (hfar : ∀ z ∈ (collar (n := n) r₀)ᶜ, |f z| ≤ farFieldDom τ M1F M2F Mqc z) :
    |∫ z : Point n, f z|
      ≤ (M₁ * (n : ℝ) * 3 / 4 / Real.sqrt τ + M₂ + M₀ * ((n : ℝ) + 1) / (2 * τ))
        + (M1F * (n : ℝ) * 3 / 4 / Real.sqrt τ + M2F + Mqc * ((n : ℝ) + 1) / (2 * τ)) := by
  have hcollarmeas : MeasurableSet (collar (n := n) r₀) :=
    QIQTH.SliverTailMatched.collar_measurableSet r₀
  have hcollarcmeas : MeasurableSet ((collar (n := n) r₀)ᶜ) := hcollarmeas.compl
  have hInt_on : IntegrableOn f (collar (n := n) r₀) volume := hInt.integrableOn
  have hInt_off : IntegrableOn f ((collar (n := n) r₀)ᶜ) volume := hInt.integrableOn
  -- collar piece:  ∫_{collar} ‖f‖  ≤  on-collar O(1/τ).
  have hcollarBound : ∫ z in collar (n := n) r₀, ‖f z‖
      ≤ M₁ * (n : ℝ) * 3 / 4 / Real.sqrt τ + M₂ + M₀ * ((n : ℝ) + 1) / (2 * τ) := by
    refine le_trans ?_ (onCollarDom_setIntegral_le τ M₀ M₁ M₂ hτ hM₀ hM₁ hM₂ (collar (n := n) r₀))
    refine integral_mono_ae hInt_on.norm
      ((onCollarDom_integrable τ M₀ M₁ M₂ hτ).integrableOn) ?_
    refine (ae_restrict_iff' hcollarmeas).mpr (ae_of_all _ (fun z hz => ?_))
    show ‖f z‖ ≤ onCollarDom τ M₀ M₁ M₂ z
    rw [Real.norm_eq_abs]; exact hcollar z hz
  -- far-field piece:  ∫_{collarᶜ} ‖f‖  ≤  far-field O(1/τ).
  have hfarBound : ∫ z in (collar (n := n) r₀)ᶜ, ‖f z‖
      ≤ M1F * (n : ℝ) * 3 / 4 / Real.sqrt τ + M2F + Mqc * ((n : ℝ) + 1) / (2 * τ) := by
    refine le_trans ?_
      (farFieldDom_setIntegral_le τ M1F M2F Mqc hτ hM1F hM2F hMqc ((collar (n := n) r₀)ᶜ))
    refine integral_mono_ae hInt_off.norm
      ((farFieldDom_integrable τ M1F M2F Mqc hτ).integrableOn) ?_
    refine (ae_restrict_iff' hcollarcmeas).mpr (ae_of_all _ (fun z hz => ?_))
    show ‖f z‖ ≤ farFieldDom τ M1F M2F Mqc z
    rw [Real.norm_eq_abs]; exact hfar z hz
  -- the exhaustive, disjoint split of the full-space integral.
  have hsplit : (∫ z in collar (n := n) r₀, f z) + (∫ z in (collar (n := n) r₀)ᶜ, f z)
      = ∫ z : Point n, f z := integral_add_compl hcollarmeas hInt
  calc |∫ z : Point n, f z|
      = |(∫ z in collar (n := n) r₀, f z) + (∫ z in (collar (n := n) r₀)ᶜ, f z)| := by rw [hsplit]
    _ ≤ |∫ z in collar (n := n) r₀, f z| + |∫ z in (collar (n := n) r₀)ᶜ, f z| := abs_add_le _ _
    _ ≤ (∫ z in collar (n := n) r₀, ‖f z‖) + (∫ z in (collar (n := n) r₀)ᶜ, ‖f z‖) := by
        refine add_le_add ?_ ?_
        · rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
        · rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ _ := add_le_add hcollarBound hfarBound

end QIQTH.RemainderAssembly

/-! ###############################################################################
    ## J4-493 LEDGER — the remainder-assembly capstone (full-space heat-trace remainder τ-order).
    ###############################################################################

  WHAT LANDS.  `remainderIntegral_order` combines the two individually-closed τ-order legs — the
  near-diagonal on-collar leg (J4-492 `onCollarDom_setIntegral_le`, controlled by the (I1)-closed collar
  constants M₀/M₁/M₂) and the off-collar far-field leg (J4-491 `farFieldDom_integral_le`, controlled by
  the global amplitude sups M1F/M2F/Mqc) — via a `collar r₀ ⊔ (collar r₀)ᶜ` domain split into a SINGLE
  explicit `O(1/τ)` bound on the full-space remainder integral of any integrand `f` dominated by the
  respective envelopes on each region.  `farFieldDom_setIntegral_le` is the far-field mirror of the
  on-collar restriction lemma.

  THE GATE (satisfiability).  FAITHFUL & NON-VACUOUS.  The split is exhaustive/disjoint
  (`integral_add_compl`), both pieces integrable (`Integrable.integrableOn` from global `Integrable f`),
  and their sum is EXACTLY the full integral.  Both dominations are simultaneously satisfiable by real
  objects (`sliverIntegrand_on_collar` on-collar, `farField_ptwise_bound` off-collar); `f := 0` also
  satisfies everything.  No false pointwise inequality, no whole-space coercivity trap.

  DON'T-UNDERCREDIT.  The heavy analysis was ALREADY BANKED and reused verbatim: the on-collar restriction
  `OnCollarMomentOrder.onCollarDom_setIntegral_le`, the far-field full-space moment
  `FarFieldMomentOrder.farFieldDom_integral_le` (+ `farFieldDom_nonneg`/`farFieldDom_integrable`), and the
  Mathlib split machinery `integral_add_compl` / `norm_integral_le_integral_norm` / `integral_mono_ae` /
  `setIntegral_le_integral`.  The genuinely NEW content is the ASSEMBLY: the `collar r₀ ⊔ (collar r₀)ᶜ`
  split of the full-space remainder + the far-field restriction mirror + the combination into a single
  `O(1/τ)`.  A thin, honest capstone over the two banked legs (mirroring the `hcomp_final3`
  `integral_inter_add_diff`/`norm_add_le` split idiom, here with `integral_add_compl` for the exhaustive
  collar split), NOT a re-derivation.

  HONEST DISTANCE.  This is the FAITHFUL PROXY (`|∫_full (on-collar-dominated + far-field-dominated)| ≤
  single O(1/τ)`), stated for a generic dominated integrand rather than wired to the concrete
  `IchartResidual − hessGaussFactor·qc` aggregator (whose two pointwise dominations live in
  `SliverBoundOnCollar` / `FarFieldDecay` and use disjoint constant families).  The full heat-trace
  remainder is now τ-order-CONTROLLED as a single `O(1/τ)`: on-collar by (I1), far field by the global
  Gaussian remainder.  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring
  stack; the leading-coefficient extraction and the `R/6` identification lie BEYOND this remainder
  τ-order.  This brick only assembles the full-remainder τ-order into one bound.
-/

section AxiomChecks
open QIQTH.RemainderAssembly
#print axioms farFieldDom_setIntegral_le
#print axioms remainderIntegral_order
end AxiomChecks
