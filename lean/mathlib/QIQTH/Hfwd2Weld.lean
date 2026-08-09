/-
  Hfwd2Weld — J4-484: THE WELD — the forward SECOND jet joint continuity `hFwd2` from the VELOCITY
  slot (J4-480) + the BASE slot (J4-483), and the chart-Hessian base continuity it discharges.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.
  std-3 only.  No existing file is edited.

  ── THE TWO SLOTS (banked).  J4-480 (`Flow3Regularity.forward2_velocitySlot`) discharged the
  VELOCITY-slot half of `hFwd2` (`ContinuousAt (fun v => fderiv² (uniformFlowExp z) v) v₀` at every
  reachable `v₀`); J4-483 (`HbaseJ2Assembly.uniformFlowExp_fderiv2_base_modulus`) discharged the
  BASE-slot modulus (`‖fderiv²(uniformFlowExp q) v − fderiv²(uniformFlowExp q') v‖ ≤ Λ₂·‖q − q'‖` on the
  reachable interior).  THIS BRICK is the `z₀`-anchored triangle (the J4-435
  `JacobiCLMExposure.forwardFlowJet_continuousOn` template ONE ORDER UP) welding them into the joint
  `hFwd2` on `K ×ˢ ball 0 (uniformFlowRadius)`, then feeding `hFwd2` into
  `ChartSecondJet.chartSecondJet_continuousOn_of_forward2`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## ⚠ THE REACHABILITY GAP (sub-task (i): NOT bankable — the flagged (I1) input).

  BOTH second-jet slots carry the per-base reachability guard `‖v‖ < expRho g gi hC q` (the price of
  the `C³`/`C⁴` overlap-bridge regularity, valid only inside the injectivity ball `expRho q`).  The
  target `hFwd2` demands continuity on the FULL `K ×ˢ ball 0 (uniformFlowRadius)`.  To cover that ball
  the slots need `‖v‖ < expRho q` for EVERY `q ∈ K` with `‖v‖ < uniformFlowRadius` — i.e. the
  K-uniform reachability `∀ q ∈ K, uniformFlowRadius ≤ expRho q`.

  This is NOT bankable and NOT provable in-repo: `expRho` (`ExpMap.expRho`) is an OPAQUE, `irreducible`
  `Classical.choose` from `exists_confined_tube_family` carrying NO continuity, NO lower
  semicontinuity, and NO uniform-over-`K` lower bound; `uniformFlowRadius` is a SEPARATE opaque
  `.choose` with NO banked relation to `expRho`.  This is EXACTLY the (I1) uniform-injectivity-radius
  input flagged across the repo (`CommonNondegRadius`, `UniformExpSecondJet`, `BasepointSecondJet`,
  `FlowVelocitySecondJet`, … all carry `hr_lt : ∀ q ∈ K, r < expRho q` as a HYPOTHESIS, never as a
  conclusion; `UniformFlowNondeg` calls it "UNPROVABLE — `expRho` carries no continuity").

  So the WELD lands CONDITIONAL on the labelled, satisfiable, non-vacuous geometric input
      `hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q`.
  This is a TRUE geometric fact (the compact-uniform flow radius can be taken below the injectivity
  radius); it is simply not extractable from the opaque `.choose` selectors.  Discharging it is the
  (I1) uniform-injectivity-radius campaign (lower semicontinuity of `expRho` over `K`), a separate
  multi-session smooth-dependence effort — NOT this weld.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `uniformFlowExp_forward2_continuousOn_of_reach` — ★★ THE WELD → `hFwd2`.  Given `hReach`, the
      joint-in-`(z,v)` continuity of the forward SECOND jet `(z,v) ↦ fderiv² (uniformFlowExp … z) v`
      on `K ×ˢ ball 0 (uniformFlowRadius)`.  The `z₀`-anchored triangle
      (`forwardFlowJet_continuousOn` one order up): VELOCITY slot (`forward2_velocitySlot`) +
      BASE modulus (`uniformFlowExp_fderiv2_base_modulus`) squeezed to `0`, added to the velocity
      tendsto, `abel`'d together.

    * `chartSecondJet_continuousOn_of_reach` — ★★★ THE CHART HESSIAN BASE CONTINUITY, hFwd2-discharged.
      Feeds the welded `hFwd2` into `ChartSecondJet.chartSecondJet_continuousOn_of_forward2`: the chart
      SECOND field-jet `z ↦ fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart … z) y) 0` is
      base-continuous on `U`, with the `hFwd2` atom REPLACED by `hReach` (the sole `hFwd2`→`hReach`
      substitution; the remaining `hW0`/`horigin`/`hunit`/`hid2` are the same geometric carries the
      reduction always had).

  ⚠ CARRIED (labelled, satisfiable, non-vacuous, NEVER a conclusion):
    * `hReach` — the K-uniform reachability `∀ q ∈ K, uniformFlowRadius ≤ expRho q` (the (I1) input).
    * the per-`z` chart carries `hW0`/`horigin`/`hunit`/`hid2` (geometric; from the reduction).

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HbaseJ2Assembly
import QIQTH.ChartSecondJet

open Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.HbaseJ2Assembly QIQTH.Flow3Regularity QIQTH.JacobiCLMExposure QIQTH.ChartFieldJacobian
open scoped Topology

namespace QIQTH.Hfwd2Weld

variable {n : ℕ}

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

/-! ###############################################################################
    ### ★★ THE WELD — the joint forward SECOND jet `hFwd2` (conditional on `hReach`).
    ############################################################################### -/

/-- **★★ `uniformFlowExp_forward2_continuousOn_of_reach` — THE WELD → `hFwd2`.**  Given the K-uniform
    reachability `hReach : ∀ q ∈ K, uniformFlowRadius ≤ expRho q`, the joint-in-`(z,v)` continuity of
    the forward-flow SECOND jet `(z,v) ↦ fderiv ℝ (fderiv ℝ (uniformFlowExp … z)) v` on
    `K ×ˢ ball 0 (uniformFlowRadius)`.  The `z₀`-anchored triangle of
    `JacobiCLMExposure.forwardFlowJet_continuousOn` ONE DERIVATIVE UP: the VELOCITY slot
    (`Flow3Regularity.forward2_velocitySlot`, `hReach` supplying `‖v‖ < expRho p.1`) gives the
    fixed-base tendsto; the BASE modulus (`HbaseJ2Assembly.uniformFlowExp_fderiv2_base_modulus`,
    `hReach` supplying both `‖v‖ < expRho x.1`, `‖v‖ < expRho p.1`) squeezes the base-difference to `0`;
    their sum, `abel`'d, is the joint tendsto.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_forward2_continuousOn_of_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q) :
    ContinuousOn
      (fun p : Point n × Point n =>
        fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) p.2)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
  classical
  -- the nested-CLM `ContinuousAdd` synthesis is expensive; cache it once (via `IsTopologicalAddGroup`).
  haveI hCA : ContinuousAdd (Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    (inferInstance :
      IsTopologicalAddGroup (Point n →L[ℝ] Point n →L[ℝ] Point n)).toContinuousAdd
  obtain ⟨Λ, hΛ0, hmod⟩ := uniformFlowExp_fderiv2_base_modulus g gi hC hK
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hw₀ : ‖p.2‖ < uniformFlowRadius g gi hC hK := by rwa [mem_ball_zero_iff] at hp2
  have hvexp : ‖p.2‖ < expRho g gi hC p.1 := lt_of_lt_of_le hw₀ (hReach p.1 hp1)
  -- VELOCITY slot at the fixed base `p.1`.
  have hvel : ContinuousAt
      (fun w : Point n => fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) w) p.2 :=
    forward2_velocitySlot g gi hC hK p.1 hp1 p.2 hvexp hw₀
  have hfst : Tendsto (fun x : Point n × Point n => x.1)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 p.1) :=
    (continuous_fst.tendsto p).mono_left nhdsWithin_le_nhds
  have hsndp : Tendsto (fun x : Point n × Point n => x.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 p.2) :=
    (continuous_snd.tendsto p).mono_left nhdsWithin_le_nhds
  have hsnd : Tendsto (fun x : Point n × Point n =>
        fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) x.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p)
      (𝓝 (fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) p.2)) :=
    hvel.tendsto.comp hsndp
  have htend : Tendsto (fun x : Point n × Point n => Λ * ‖x.1 - p.1‖)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 0) := by
    have hc : Continuous (fun z : Point n => Λ * ‖z - p.1‖) := by fun_prop
    have h := (hc.tendsto p.1).comp hfst
    simpa using h
  -- BASE modulus squeezes the base-difference to `0` (both `expRho` guards from `hReach`).
  have hdiff : Tendsto (fun x : Point n × Point n =>
        fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK x.1)) x.2
          - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) x.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 0) := by
    have hbound : ∀ᶠ x : Point n × Point n in
        𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p,
        ‖fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK x.1)) x.2
            - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) x.2‖
          ≤ Λ * ‖x.1 - p.1‖ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx2' : ‖x.2‖ < uniformFlowRadius g gi hC hK := by rwa [mem_ball_zero_iff] at hx2
      have hxexp : ‖x.2‖ < expRho g gi hC x.1 := lt_of_lt_of_le hx2' (hReach x.1 hx1)
      have hpexp : ‖x.2‖ < expRho g gi hC p.1 := lt_of_lt_of_le hx2' (hReach p.1 hp1)
      exact hmod x.1 hx1 p.1 hp1 x.2 hxexp hpexp hx2'
    exact squeeze_zero_norm'
      (f := fun x : Point n × Point n =>
        fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK x.1)) x.2
          - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) x.2)
      hbound htend
  have hcomb := hdiff.add hsnd
  simp only [zero_add] at hcomb
  exact Filter.Tendsto.congr (fun x => by abel) hcomb

/-! ###############################################################################
    ### ★★★ THE CHART HESSIAN BASE CONTINUITY — hFwd2 discharged into the reduction.
    ############################################################################### -/

/-- **★★★ `chartSecondJet_continuousOn_of_reach` — THE CHART HESSIAN BASE CONTINUITY, hFwd2-discharged.**
    Feeds the welded `hFwd2` (`uniformFlowExp_forward2_continuousOn_of_reach`) into the J4-479 reduction
    `ChartSecondJet.chartSecondJet_continuousOn_of_forward2`.  For `U ⊆ K` with the banked origin
    section `hW0`, origin smallness `horigin`, nondegeneracy `hunit`, and the per-`z` 2nd-jet IFT
    identity `hid2` (all supplied by `ChartSecondJet`), the chart SECOND field-jet at the field centre
        `z ↦ fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart … z) y) 0`
    is base-continuous on `U` — with the `hFwd2` atom DISCHARGED, its ONLY replacement being the
    K-uniform reachability `hReach`.  NOT `a₁ = R/6`. -/
theorem chartSecondJet_continuousOn_of_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {U : Set (Point n)} (hUK : U ⊆ K)
    (hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q)
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) U)
    (horigin : ∀ z ∈ U,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK)
    (hunit : ∀ z ∈ U, IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)))
    (hid2 : ∀ z ∈ U,
      fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0
        = (-ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))).comp
          ((fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
                (uniformInverseChart g gi hC hK z 0)).comp
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0))))) :
    ContinuousOn
      (fun z : Point n => fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0) U :=
  ChartSecondJet.chartSecondJet_continuousOn_of_forward2 g gi hC hK hUK hW0 horigin hunit
    (uniformFlowExp_forward2_continuousOn_of_reach g gi hC hK hReach) hid2

end QIQTH.Hfwd2Weld

/-! ## THE WALL LEDGER (post J4-484).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE CONVERGENT WALL.  Both a₁=R/6 consumer chains bottom out on the chart SECOND field-jet        │
  │  (`ChartSecondJet`, J4-479), reduced to the atom `hFwd2` — the joint continuity of the FORWARD     │
  │  SECOND jet `(z,v) ↦ fderiv²(uniformFlowExp z) v` on `K ×ˢ ball 0 (uniformFlowRadius)`.             │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE SLOTS (banked).  VELOCITY: `Flow3Regularity.forward2_velocitySlot` (J4-480, unconditional     │
  │  fibre-continuity, guard `‖v‖ < expRho z`).  BASE: `HbaseJ2Assembly.uniformFlowExp_fderiv2_base_    │
  │  modulus` (J4-483, Lipschitz-in-base modulus, guard `‖v‖ < expRho q ∧ < expRho q'`).               │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE WELD (this brick).  `uniformFlowExp_forward2_continuousOn_of_reach` — the `z₀`-anchored        │
  │  triangle (`forwardFlowJet_continuousOn` one order up): squeeze the base-difference to `0` (base    │
  │  modulus) + add the velocity tendsto, `abel`.  Yields `hFwd2` on the FULL ball, CONDITIONAL on the  │
  │  K-uniform reachability `hReach : ∀ q ∈ K, uniformFlowRadius ≤ expRho q`.                           │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE DISCHARGE.  `chartSecondJet_continuousOn_of_reach` feeds the welded `hFwd2` into              │
  │  `ChartSecondJet.chartSecondJet_continuousOn_of_forward2` — the `hFwd2` atom is DISCHARGED, its     │
  │  ONLY replacement the `hReach` input; `hW0`/`horigin`/`hunit`/`hid2` are the reduction's standing   │
  │  geometric carries.                                                                                │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── ⚠ THE WALL STATUS: PARTIAL (conditional on `hReach`), NOT fully fallen.  The `hFwd2` atom is fully
  built and discharged EXCEPT for the ONE genuinely non-bankable input: the K-uniform reachability
  `hReach : ∀ q ∈ K, uniformFlowRadius ≤ expRho q`.  `expRho` (`ExpMap.expRho`) is an OPAQUE
  `irreducible` `Classical.choose` (no continuity, no lower semicontinuity, no uniform-over-`K` lower
  bound); `uniformFlowRadius` is a SEPARATE opaque `.choose` with no banked relation to `expRho`.  This
  IS the (I1) uniform-injectivity-radius input flagged across the repo (`hr_lt : ∀ q ∈ K, r < expRho q`
  is carried as a HYPOTHESIS everywhere — `CommonNondegRadius`, `UniformExpSecondJet`,
  `BasepointSecondJet`, `FlowVelocitySecondJet`, `UniformFlowNondeg`'s "UNPROVABLE" note).  So the wall
  did NOT fall UNCONDITIONALLY.  What DID fall: the entire weld ARCHITECTURE — velocity + base slots →
  joint `hFwd2` → chart Hessian base continuity — is now a proved chain, gated by the SINGLE (I1) input,
  no longer by any second-variation ODE / regularity work.

  ── DONT-UNDERCREDIT.  Both slots were ALREADY BANKED (J4-480 velocity, J4-483 base modulus); the
  reduction `chartSecondJet_continuousOn_of_forward2` was ALREADY BANKED (J4-479); the first-order weld
  template `forwardFlowJet_continuousOn` was ALREADY BANKED (J4-435).  So this brick is a pure
  triangle-weld ASSEMBLY (the J4-435 template one derivative up) + the reduction plug-in — NOT a new ODE
  or regularity effort.  The (I1) reachability gap was ALREADY KNOWN (repo-wide `hr_lt` carries); this
  brick did NOT discover it, it merely names it precisely at the `hFwd2` boundary.

  ── WHAT REMAINS.  (I1) the K-uniform reachability `∀ q ∈ K, uniformFlowRadius ≤ expRho q` (lower
  semicontinuity of `expRho` over `K` — a separate multi-session smooth-dependence campaign, the SAME
  gap gating every `hr_lt` carry in the repo).  Discharging (I1) turns
  `uniformFlowExp_forward2_continuousOn_of_reach` and `chartSecondJet_continuousOn_of_reach`
  unconditional in `hReach`, at which point the convergent wall falls outright.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.Hfwd2Weld
#print axioms uniformFlowExp_forward2_continuousOn_of_reach
#print axioms chartSecondJet_continuousOn_of_reach
end AxiomChecks
