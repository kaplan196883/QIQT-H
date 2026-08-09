/-
  Flow3Regularity — J4-480: the C³ velocity-slot regularity of the uniform flow — phase 1 of the
  `hFwd2` (forward SECOND jet) effort for the a₁ = R/6 convergent wall.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.
  std-3 only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GATE (verdict: NOT tower-capped — the C⁴ side-route already banks C³).

  J4-479 (`ChartSecondJet`) reduced the chart Hessian to the atom `hFwd2` (joint continuity of the
  forward SECOND jet `(z,v) ↦ fderiv ℝ (fderiv ℝ (uniformFlowExp … z)) v`), whose VELOCITY-slot half
  needs the flow to be `C³` in the velocity slot (`ChartSecondJet.fderiv_right` at order 3).  The
  J4-479 ledger recorded "only C² is banked (`contDiffAt2_uniformFlowExp`)" and flagged the C³ as a
  "strictly higher, genuinely multi-brick ODE effort".

  ── THE GATE INSPECTION.  How does `contDiffAt2_uniformFlowExp`
  (`PullbackNaturalityLocal.lean`) get C²?  It is BESPOKE: it assembles THREE explicit Fréchet layers
  banked FOR `uniformFlowExp` directly —
      `uniformFlowExp_hasFDerivAt` (Dφ), `uniformFlowExp_fderiv_hasFDerivAt` (D²φ),
      `uniformFlowExp_hessianMap_differentiableAt` (D²φ continuous) —
  fed twice through `contDiffAt_succ_iff_hasFDerivAt`.  That direct Fréchet tower STRUCTURALLY caps at
  C² (there is NO fourth banked Fréchet layer `uniformFlowExp_...D⁴...`).  So the naive gate reading is
  "tower-capped, need a bespoke third variational layer".

  ── BUT the tower is NOT actually capped: a SIDE ROUTE already banks C⁴.  `ChartThirdJet` (J4-192)
  proved `uniformFlowExp_contDiffAt_four` — `ContDiffAt ℝ 4 (uniformFlowExp g gi hC hK z) v` at every
  reachable field point — via the ODE-uniqueness OVERLAP BRIDGE `expMap_eq_uniformFlowExp_on_overlap`
  (`uniformFlowExp z =ᶠ[𝓝 v] expMap z` on `‖v‖ < min (expRho z) (uniformFlowRadius)`) transporting the
  UNCONDITIONAL `exp∈C⁴` tower `ExpMap.expMap_contDiffOn_four` through `ContDiffAt.congr_of_eventuallyEq`.
  So the C³ velocity regularity is a ONE-LINE downgrade (`.of_le`) of that already-landed C⁴ — NOT a
  new multi-brick ODE / second-variation Grönwall.  The ONLY price is the extra guard
  `‖v‖ < expRho g gi hC z` that the direct-tower C² does not carry (the overlap bridge is valid only
  inside the injectivity ball `expRho z`).

  VERDICT:  gate (i) NEAR-COPY — but via the `expMap ↔ uniformFlowExp` overlap C⁴ side-route rather
  than a generic-k ODE argument, and carrying the extra reachability guard `‖v‖ < expRho z`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `contDiffAt3_uniformFlowExp` — ★ THE C³ FORWARD MAP.  `ContDiffAt ℝ 3 (uniformFlowExp g gi hC hK z) v`
      at every reachable field point (`‖v‖ < expRho g gi hC z`, `‖v‖ < uniformFlowRadius g gi hC hK`),
      a `.of_le` downgrade of the banked C⁴ `ChartThirdJet.uniformFlowExp_contDiffAt_four`.

    * `forward2_velocitySlot` — ★★ THE VELOCITY-SLOT HALF OF `hFwd2`.  Mirrors `ForwardFlowJet`'s TERM 2
      (`forwardFlowJet_velocityContinuousAt`, C² ⟹ first-jet velocity continuity) ONE ORDER UP: from the
      C³ forward map, `ContDiffAt.fderiv_right` twice (`2+1≤3`, then `1+1≤2`) makes the forward SECOND jet
      `v ↦ fderiv ℝ (fderiv ℝ (uniformFlowExp … z)) v` a `ContDiffAt ℝ 1`, hence `ContinuousAt`, at any
      reachable `v₀`.  This is the derivable velocity-slot half of `ChartSecondJet.hFwd2`.

  ⚠ WHAT REMAINS for the full `hFwd2` (future J4-481+; NOT here):
    * the BASE-slot half — the second-jet base modulus `hbaseJ2`
        `‖fderiv² (uniformFlowExp q) w − fderiv² (uniformFlowExp q') w‖ ≤ exp L·‖q − q'‖`,
      the operator-level one-order-up analogue of `ForwardFlowJet.hbaseJ` (a TRUE geodesic-flow fact,
      the SECOND-variation Grönwall — same `.choose`/spec-exposure gap as the first-jet base modulus);
    * a K-uniform reachability radius over `expRho z` (per-base `.choose`-fixed) to sew the per-`z`
      velocity slot into the joint `K ×ˢ ball` continuity `hFwd2` demands.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ChartThirdJet

open Filter
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.ChartThirdJet
open scoped Topology

namespace QIQTH.Flow3Regularity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE C³ FORWARD MAP — `uniformFlowExp` is `C³` at reachable points.
    ############################################################################### -/

/-- **★ `contDiffAt3_uniformFlowExp`.**  The flow exponential `φ_z := uniformFlowExp g gi hC hK z` is
    `ContDiffAt ℝ 3` at every reachable field point `v` with `‖v‖ < expRho g gi hC z` and
    `‖v‖ < uniformFlowRadius g gi hC hK`.  A `.of_le (3 ≤ 4)` downgrade of the already-banked C⁴
    `ChartThirdJet.uniformFlowExp_contDiffAt_four` (which routes the unconditional `exp∈C⁴` tower
    through the `expMap ↔ uniformFlowExp` overlap bridge).  NOT `a₁ = R/6`. -/
theorem contDiffAt3_uniformFlowExp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (hz : z ∈ K) (v : Point n)
    (hvexp : ‖v‖ < expRho g gi hC z) (hvuf : ‖v‖ < uniformFlowRadius g gi hC hK) :
    ContDiffAt ℝ 3 (uniformFlowExp g gi hC hK z) v :=
  (uniformFlowExp_contDiffAt_four g gi hC hK z hz v hvexp hvuf).of_le (by norm_num)

/-! ###############################################################################
    ### ★★ THE VELOCITY-SLOT HALF OF `hFwd2` — TERM 2 one order up.
    ############################################################################### -/

/-- **★★ `forward2_velocitySlot` — the velocity-slot half of `hFwd2`.**  For a fixed base `z ∈ K` and a
    velocity `v₀` reachable (`‖v₀‖ < expRho g gi hC z`, `‖v₀‖ < uniformFlowRadius g gi hC hK`), the
    forward-flow SECOND jet in the velocity slot
        `v ↦ fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z)) v`
    is `ContinuousAt` at `v₀`.  Mirrors `ForwardFlowJet.forwardFlowJet_velocityContinuousAt` (C² ⟹
    first-jet velocity continuity) one derivative up: from the C³ forward map
    (`contDiffAt3_uniformFlowExp`), `ContDiffAt.fderiv_right (m := 2)` (`2+1≤3`) gives the first-jet map
    `C²`, and a second `ContDiffAt.fderiv_right (m := 1)` (`1+1≤2`) gives the second-jet map `C¹`, hence
    `ContinuousAt`.  This is the derivable velocity-slot half of `ChartSecondJet.hFwd2`.
    NOT `a₁ = R/6`. -/
theorem forward2_velocitySlot (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (hz : z ∈ K) (v₀ : Point n)
    (hvexp : ‖v₀‖ < expRho g gi hC z) (hvuf : ‖v₀‖ < uniformFlowRadius g gi hC hK) :
    ContinuousAt
      (fun v : Point n => fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z)) v) v₀ := by
  have hc3 : ContDiffAt ℝ 3 (uniformFlowExp g gi hC hK z) v₀ :=
    contDiffAt3_uniformFlowExp g gi hC hK z hz v₀ hvexp hvuf
  exact (((hc3.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
    (by norm_num))).continuousAt

end QIQTH.Flow3Regularity

/-! ## THE C3 LEDGER (post J4-480).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE GATE.  `contDiffAt2_uniformFlowExp` gets C² BESPOKE (three explicit Fréchet layers banked    │
  │  FOR `uniformFlowExp` — Dφ / D²φ / D²φ-continuous — fed twice through                              │
  │  `contDiffAt_succ_iff_hasFDerivAt`).  That DIRECT tower structurally caps at C².  BUT the tower is │
  │  NOT capped: `ChartThirdJet.uniformFlowExp_contDiffAt_four` (J4-192) already banks C⁴ at reachable │
  │  points via the `expMap ↔ uniformFlowExp` OVERLAP BRIDGE transporting the unconditional            │
  │  `ExpMap.expMap_contDiffOn_four` tower.  VERDICT: near-copy — C³ is a one-line `.of_le` downgrade  │
  │  of that C⁴, carrying the extra reachability guard `‖v‖ < expRho z`.                               │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (i) THE C³ FORWARD MAP — `contDiffAt3_uniformFlowExp` (DERIVED): `.of_le (3 ≤ 4)` of the banked   │
  │  C⁴.  Guards: `‖v‖ < expRho z` AND `‖v‖ < uniformFlowRadius`.                                      │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (ii) THE VELOCITY-SLOT HALF OF `hFwd2` — `forward2_velocitySlot` (DERIVED): TERM 2 of J4-434 one  │
  │  order up.  C³ ⟹ (`fderiv_right` ×2, `2+1≤3` then `1+1≤2`) the forward SECOND jet                  │
  │  `v ↦ fderiv² (uniformFlowExp z) v` is `C¹`, hence `ContinuousAt`, at any reachable `v₀`.          │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  WHAT REMAINS for full `hFwd2` (future J4-481+):  the BASE-slot second-jet modulus `hbaseJ2` (the  │
  │  SECOND-variation Grönwall, operator one-order-up analogue of `ForwardFlowJet.hbaseJ`; same        │
  │  `.choose`/spec-exposure gap) + a K-uniform reachability radius over the per-base `expRho z`.      │
  │  Then the `z₀`-anchored triangle (verbatim `ForwardFlowJet.forwardFlowJet_continuousWithinAt_...`) │
  │  welds VELOCITY (this file) + BASE into the joint `hFwd2` on `K ×ˢ ball`.                           │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── DONT-UNDERCREDIT.  The J4-479 ledger's "C³ flow regularity … a strictly higher, genuinely
  multi-brick ODE effort" was STALE for the regularity half: `ChartThirdJet.uniformFlowExp_contDiffAt_four`
  (J4-192) already banks C⁴ (hence C³) at reachable points.  So the C³ regularity is a one-liner; the
  genuine remaining ODE effort is ONLY the base-slot second-variation modulus, not the velocity slot.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.Flow3Regularity
#print axioms contDiffAt3_uniformFlowExp
#print axioms forward2_velocitySlot
end AxiomChecks
