/-
  ForwardFlowJet — J4-434: the `hFwd` atom — joint-in-`(z,v)` continuity of the FORWARD geodesic-flow
  first jet `(z, v) ↦ fderiv ℝ (uniformFlowExp g gi hC hK z) v`.  ONE brick of the a₁ = R/6
  convergence-trio campaign; **NOT `a₁ = R/6`** and proves NOTHING about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  No `sorry` (header prose excepted), no `:= True`, no new axioms, no vacuous /
  unsatisfiable hypotheses, no result that is a conclusion-in-disguise.  std-3 only.  No existing file
  is edited.

  ── THE OBJECT (J4-433 `ChartFieldJacobian`).  The J3 base-continuity of the `.choose`-built chart
  field-slot Jacobian was reduced (route (c), IFT) to ONE geometry-only forward carry:
        `hFwd : ContinuousOn ((z,v) ↦ fderiv ℝ (uniformFlowExp g gi hC hK z) v) (U ×ˢ ball 0 ρ)`
  — the JOINT-in-`(z,v)` continuity of the FORWARD-flow first jet.  This file attacks `hFwd`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE hFwd DIAGNOSIS.

  ### THE TEMPLATE.  The VALUE level already banks this shape: `FlowJointContinuity`
  (`uniformFlowExp_joint_continuousWithinAt`) proves the joint continuity of the point-value flow
  `(q,w) ↦ uniformFlowExp … q w` on `K ×ˢ ball 0 ρ` by a `q₀`-ANCHORED TRIANGLE
        ‖φ(q,w) − φ(q₀,w₀)‖ ≤ ‖φ(q,w) − φ(q₀,w)‖ + ‖φ(q₀,w) − φ(q₀,w₀)‖,
  welding TWO banked single-slot facts:
    • TERM 1 (base slot, uniform in `w`):  the value base modulus W3
      `GeodesicGronwall.uniformFlowExp_base_diff_bound` — `‖φ_q w − φ_{q₀} w‖ ≤ exp L·‖q − q₀‖`;
    • TERM 2 (velocity slot at FIXED `q₀`):  `contDiffAt2_uniformFlowExp … q₀ … w₀ |>.continuousAt`.
  This file mirrors that triangle **exactly one derivative up**, for the operator-valued first jet
  `D(q,w) := fderiv ℝ (uniformFlowExp g gi hC hK q) w  :  Point n →L[ℝ] Point n`.

  ### TERM 2 (velocity slot) — **DERIVED here.**  `contDiffAt2_uniformFlowExp … q₀ hq₀ w₀ hw₀` gives
  `ContDiffAt ℝ 2 (uniformFlowExp … q₀) w₀`; `ContDiffAt.fderiv_right (1 + 1 ≤ 2)` then hands the
  Jacobian map `w ↦ D(q₀,w)` a `ContDiffAt ℝ 1`, hence `ContinuousAt` at `w₀`.  This is
  `forwardFlowJet_velocityContinuousAt`, the genuinely-new derivable half of the triangle.

  ### TERM 1 (base slot) — **the honest carry (route (a), spec-exposure-blocked).**  The Jacobian is
  the velocity Jacobi endpoint operator along the base geodesic: `uniformFlowExp_hasFDerivAt`
  constructs `fderiv (uniformFlowExp q) v = (fun δ ↦ (V_{q,v} δ 1).1)` with `V_{q,v}` a Jacobi field
  along the base tube through `(q,v)`.  So the base-slot modulus IS in principle a two-solution Jacobi
  Grönwall (`BasepointJetModulus.jacobi_twopoint_diff_bound`): two Jacobi fields with the SAME seed
  `(0,δ)` along the two base tubes (through `(q,v)`, `(q₀,v)`) differ by `Dcoef·Jb·exp K`, with
  `Dcoef ≤ M₂·‖q − q₀‖·exp K₀` (base-tube separation × field `C²` bound) and `Jb ≤ ‖δ‖·exp K` — giving
  the OPERATOR modulus `‖D(q,v) − D(q₀,v)‖ ≤ Λ·‖q − q₀‖`, uniform in `v`.
  **BUT** the endpoint Jacobi CLM `V_{q,v}` is INTERNAL to the proof of `uniformFlowExp_hasFDerivAt`
  (a local `set V := …choose`); the `.choose` tower exposes only `∃ L, HasFDerivAt (uniformFlowExp q) L v`
  (existence — `L` identified with NOTHING accessible), the per-fixed-`q` velocity `ContDiffAt`, the
  UNIFORM Jacobian bound (`uniformFlowExp_fderiv_uniform_bound`) and the near-isometry
  `‖D_q v − id‖ ≤ C_D‖v‖` — but **NO base-point modulus of the Jacobian**, and no spec lemma exposing
  `V_{q,v}` as an accessible Jacobi CLM.  Per the DEFEQ / `.choose` lesson, route (a) cannot be lifted
  without re-opening `UniformFlowFDeriv` to bank the Jacobi-CLM structure — a genuine multi-brick chunk
  (exactly as `FlowJointRegularity` audit §1/§3 flagged: "a stability route is available IN PRINCIPLE …
  NOT landed here").  So TERM 1 is carried as the named first-jet base modulus `hbaseJ`, the
  one-derivative-up analogue of the value-level `uniformFlowExp_base_diff_bound`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `forwardFlowJet_velocityContinuousAt` — **★ TERM 2 (DERIVED).**  Velocity-slot continuity of the
      forward-flow Jacobian at a fixed base `q₀`: `ContinuousAt (fun w ↦ D(q₀,w)) w₀`, from the banked
      per-`q` velocity `C²` (`contDiffAt2_uniformFlowExp`) via `ContDiffAt.fderiv_right`.

    * `forwardFlowJet_continuousWithinAt_of_baseMod` — **★★ THE hFwd WELD (`ContinuousWithinAt`).**  The
      `q₀`-anchored triangle, one derivative up: from the carried first-jet base modulus `hbaseJ`
      (TERM 1) + the derived velocity continuity (TERM 2), the forward-flow Jacobian
      `(q,w) ↦ D(q,w)` is jointly `ContinuousWithinAt` on `K ×ˢ ball 0 ρ` at any `(q₀,w₀)`,
      `q₀ ∈ K`, `‖w₀‖ < ρ`.  Verbatim structure of `uniformFlowExp_joint_continuousWithinAt`.

    * `forwardFlowJet_continuousOn_of_baseMod` — **★★★ THE hFwd ATOM (`ContinuousOn`).**  `ContinuousOn`
      packaging on the whole product region `K ×ˢ ball 0 ρ` — i.e. `hFwd` itself, on the honest
      differentiability domain (the flow Jacobian exists only inside the uniform flow radius), conditional
      only on the single carried first-jet base modulus.

    * `chartFieldJacobian_continuousOn_of_baseMod` — **the J3 wiring.**  Feeding the hFwd atom (on the
      ball) into the J4-433 IFT reduction: for `U ⊆ K` with the banked origin-section continuity `hW0`,
      the origin smallness `‖W z 0‖ < ρ`, the nondegeneracy `hunit` and the IFT identity `hIFT`, the chart
      field-slot Jacobian `z ↦ fderiv ℝ (uniformInverseChart … z) 0` is base-continuous on `U` — modulo
      the SAME single carry `hbaseJ`.  (Re-derives the short `Ring.inverse`-composition of
      `chartFieldJacobian_continuousOn_of_forwardJointCont` on the honest ball domain, since the flow
      Jacobian is not continuous off the flow radius.)

  ⚠ CARRIED (labelled, satisfiable, non-vacuous, NEVER a conclusion):
    * `hbaseJ` — the first-jet base modulus
        `‖fderiv (uniformFlowExp q) w − fderiv (uniformFlowExp q') w‖ ≤ exp L·‖q − q'‖`  (‖w‖ ≤ ρ),
      the operator-level one-derivative-up analogue of `uniformFlowExp_base_diff_bound`.  A GENUINE
      geodesic-flow fact (true), derivable via `jacobi_twopoint_diff_bound` once the endpoint velocity
      Jacobi CLM is banked as a spec lemma — the precise missing ingredient for Sol #21.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ChartFieldJacobian
import QIQTH.FlowJointContinuity

open Filter
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.ForwardFlowJet

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ TERM 2 (DERIVED) — velocity-slot continuity of the forward-flow Jacobian.
    ############################################################################### -/

/-- **★ `forwardFlowJet_velocityContinuousAt` — TERM 2, DERIVED.**  For a fixed base `q₀ ∈ K` and a
    velocity `w₀` strictly inside the uniform flow radius, the forward-flow first jet in the velocity
    slot `w ↦ fderiv ℝ (uniformFlowExp g gi hC hK q₀) w` is `ContinuousAt` at `w₀`.  From the banked
    per-`q` velocity `C²` (`contDiffAt2_uniformFlowExp`) via `ContDiffAt.fderiv_right` (`1 + 1 ≤ 2`,
    yielding a `ContDiffAt ℝ 1` Jacobian map) then `.continuousAt`.  NOT `a₁ = R/6`. -/
theorem forwardFlowJet_velocityContinuousAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (q₀ : Point n) (hq₀ : q₀ ∈ K) (w₀ : Point n)
    (hw₀ : ‖w₀‖ < uniformFlowRadius g gi hC hK) :
    ContinuousAt (fun w : Point n => fderiv ℝ (uniformFlowExp g gi hC hK q₀) w) w₀ := by
  have hc2 : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK q₀) w₀ :=
    contDiffAt2_uniformFlowExp g gi hC hK q₀ hq₀ w₀ hw₀
  exact (hc2.fderiv_right (m := 1) (by norm_num)).continuousAt

/-! ###############################################################################
    ### ★★ THE hFwd WELD — the `q₀`-anchored triangle, one derivative up.
    ############################################################################### -/

/-- **★★ `forwardFlowJet_continuousWithinAt_of_baseMod` — THE hFwd WELD.**  Mirrors
    `FlowJointContinuity.uniformFlowExp_joint_continuousWithinAt` one derivative up.  From the carried
    first-jet base modulus `hbaseJ` (TERM 1) and the derived velocity-slot continuity (TERM 2), the
    forward-flow first jet `(q,w) ↦ fderiv ℝ (uniformFlowExp g gi hC hK q) w` is jointly
    `ContinuousWithinAt` on the product region `K ×ˢ ball 0 ρ` at any `(q₀,w₀)` with `q₀ ∈ K`,
    `‖w₀‖ < ρ`.  The `q₀`-anchored triangle: TERM 1 `→ 0` squeezed by `hbaseJ` (uniform in `w`, so it
    survives `w → w₀`); TERM 2 `→ D(q₀,w₀)` by the velocity slot at the FIXED base `q₀`.  NOT
    `a₁ = R/6`. -/
theorem forwardFlowJet_continuousWithinAt_of_baseMod (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {L : ℝ}
    (hbaseJ : ∀ q ∈ K, ∀ q' ∈ K, ∀ w : Point n, ‖w‖ ≤ uniformFlowRadius g gi hC hK →
      ‖fderiv ℝ (uniformFlowExp g gi hC hK q) w - fderiv ℝ (uniformFlowExp g gi hC hK q') w‖
        ≤ Real.exp L * ‖q - q'‖)
    (q₀ : Point n) (hq₀ : q₀ ∈ K) (w₀ : Point n)
    (hw₀ : ‖w₀‖ < uniformFlowRadius g gi hC hK) :
    ContinuousWithinAt
      (fun p : Point n × Point n => fderiv ℝ (uniformFlowExp g gi hC hK p.1) p.2)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) (q₀, w₀) := by
  classical
  -- velocity-slot continuity at the FIXED base `q₀`.
  have hvel : ContinuousAt (fun w : Point n => fderiv ℝ (uniformFlowExp g gi hC hK q₀) w) w₀ :=
    forwardFlowJet_velocityContinuousAt g gi hC hK q₀ hq₀ w₀ hw₀
  -- projections restricted to the within-set filter.
  have hfst : Tendsto (fun p : Point n × Point n => p.1)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] (q₀, w₀)) (𝓝 q₀) :=
    (continuous_fst.tendsto (q₀, w₀)).mono_left nhdsWithin_le_nhds
  have hsndp : Tendsto (fun p : Point n × Point n => p.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] (q₀, w₀)) (𝓝 w₀) :=
    (continuous_snd.tendsto (q₀, w₀)).mono_left nhdsWithin_le_nhds
  -- TERM 2 → `D(q₀,w₀)` by velocity-slot continuity ∘ snd.
  have hsnd : Tendsto (fun p : Point n × Point n => fderiv ℝ (uniformFlowExp g gi hC hK q₀) p.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] (q₀, w₀))
      (𝓝 (fderiv ℝ (uniformFlowExp g gi hC hK q₀) w₀)) :=
    hvel.tendsto.comp hsndp
  -- TERM 1 → 0, squeezed by the first-jet base modulus `hbaseJ` (uniform in `w`).
  have htend : Tendsto (fun p : Point n × Point n => Real.exp L * ‖p.1 - q₀‖)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] (q₀, w₀)) (𝓝 0) := by
    have hc : Continuous (fun x : Point n => Real.exp L * ‖x - q₀‖) := by fun_prop
    have h := (hc.tendsto q₀).comp hfst
    simpa using h
  have hdiff : Tendsto (fun p : Point n × Point n =>
        fderiv ℝ (uniformFlowExp g gi hC hK p.1) p.2
          - fderiv ℝ (uniformFlowExp g gi hC hK q₀) p.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] (q₀, w₀)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ htend
    filter_upwards [self_mem_nhdsWithin] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp2' : ‖p.2‖ ≤ uniformFlowRadius g gi hC hK :=
      le_of_lt (by rwa [mem_ball_zero_iff] at hp2)
    exact hbaseJ p.1 hp1 q₀ hq₀ p.2 hp2'
  -- combine: (term1) + (term2) = D, limit 0 + D(q₀,w₀) = D(q₀,w₀).
  have hcomb := hdiff.add hsnd
  simp only [zero_add] at hcomb
  exact Filter.Tendsto.congr (fun p => by abel) hcomb

/-- **★★★ `forwardFlowJet_continuousOn_of_baseMod` — THE hFwd ATOM.**  `ContinuousOn` packaging of the
    weld on the whole product region `K ×ˢ ball 0 ρ` — the joint-in-`(z,v)` continuity of the
    forward-flow first jet `(z,v) ↦ fderiv ℝ (uniformFlowExp g gi hC hK z) v`, on the honest
    differentiability domain (inside the uniform flow radius), conditional only on the single carried
    first-jet base modulus `hbaseJ`.  This is exactly `hFwd`.  NOT `a₁ = R/6`. -/
theorem forwardFlowJet_continuousOn_of_baseMod (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {L : ℝ}
    (hbaseJ : ∀ q ∈ K, ∀ q' ∈ K, ∀ w : Point n, ‖w‖ ≤ uniformFlowRadius g gi hC hK →
      ‖fderiv ℝ (uniformFlowExp g gi hC hK q) w - fderiv ℝ (uniformFlowExp g gi hC hK q') w‖
        ≤ Real.exp L * ‖q - q'‖) :
    ContinuousOn
      (fun p : Point n × Point n => fderiv ℝ (uniformFlowExp g gi hC hK p.1) p.2)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact forwardFlowJet_continuousWithinAt_of_baseMod g gi hC hK hbaseJ p.1 hp1 p.2
    (by rwa [mem_ball_zero_iff] at hp2)

/-! ###############################################################################
    ### THE J3 WIRING — chart field-Jacobian base-continuity from the hFwd atom.
    ############################################################################### -/

/-- **`chartFieldJacobian_continuousOn_of_baseMod` — the J3 wiring.**  Feeds the hFwd atom (on the ball)
    into the J4-433 IFT reduction.  For `U ⊆ K` with the banked origin-section continuity `hW0`, the
    origin smallness `‖W z 0‖ < ρ` (so the section `z ↦ (z, W z 0)` maps `U` into `K ×ˢ ball 0 ρ`), the
    nondegeneracy `hunit` and the IFT identity `hIFT` (both supplied by
    `ChartFieldJacobian.chartFieldJacobian_facts_of_small` / `chartFieldJacobian_eq_ringInverse`), the
    chart field-slot Jacobian `z ↦ fderiv ℝ (uniformInverseChart g gi hC hK z) 0` is base-continuous on
    `U`, modulo the single carried first-jet base modulus `hbaseJ`.  Mechanism (verbatim the short
    `Ring.inverse`-composition of `chartFieldJacobian_continuousOn_of_forwardJointCont`, on the honest
    ball domain): `hIFT` rewrites the target to `Ring.inverse (D(z, W z 0))`; the inner map is the hFwd
    atom composed with the (continuous, in-ball) origin section; `Ring.inverse` is continuous at each
    unit.  NOT `a₁ = R/6`. -/
theorem chartFieldJacobian_continuousOn_of_baseMod (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {U : Set (Point n)} (hUK : U ⊆ K) {L : ℝ}
    (hbaseJ : ∀ q ∈ K, ∀ q' ∈ K, ∀ w : Point n, ‖w‖ ≤ uniformFlowRadius g gi hC hK →
      ‖fderiv ℝ (uniformFlowExp g gi hC hK q) w - fderiv ℝ (uniformFlowExp g gi hC hK q') w‖
        ≤ Real.exp L * ‖q - q'‖)
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) U)
    (horigin : ∀ z ∈ U,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK)
    (hunit : ∀ z ∈ U, IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)))
    (hIFT : ∀ z ∈ U, fderiv ℝ (uniformInverseChart g gi hC hK z) 0
      = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
          (uniformInverseChart g gi hC hK z 0))) :
    ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0) U := by
  -- the hFwd atom on `K ×ˢ ball 0 ρ`.
  have hFwd := forwardFlowJet_continuousOn_of_baseMod g gi hC hK hbaseJ
  -- the origin-section pairing `z ↦ (z, W z 0)` is continuous, and maps `U` into `K ×ˢ ball 0 ρ`.
  have hpair : ContinuousOn
      (fun z : Point n => (z, uniformInverseChart g gi hC hK z 0)) U :=
    continuousOn_id.prodMk hW0
  have hmaps : Set.MapsTo (fun z : Point n => (z, uniformInverseChart g gi hC hK z 0)) U
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) :=
    fun z hz => ⟨hUK hz, by rw [mem_ball_zero_iff]; exact horigin z hz⟩
  -- the inner forward-Jacobian along the origin section is continuous on `U`.
  have hinner : ContinuousOn
      (fun z : Point n => fderiv ℝ (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0)) U :=
    hFwd.comp hpair hmaps
  -- `Ring.inverse` of the inner map is continuous on `U` (continuity at each unit value).
  have hRinv : ContinuousOn
      (fun z : Point n => Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0))) U := by
    intro z₀ hz₀
    obtain ⟨u₀, hu₀⟩ := hunit z₀ hz₀
    have hca : ContinuousAt Ring.inverse
        (fderiv ℝ (uniformFlowExp g gi hC hK z₀) (uniformInverseChart g gi hC hK z₀ 0)) := by
      rw [← hu₀]; exact (contDiffAt_ringInverse (n := 1) ℝ u₀).continuousAt
    exact hca.tendsto.comp (hinner z₀ hz₀)
  -- transfer through the IFT identity.
  exact hRinv.congr hIFT

end QIQTH.ForwardFlowJet

/-! ## THE hFwd VERDICT (post J4-434).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  BEFORE (J4-433):  the chart field-Jacobian base-continuity was reduced, via route (c) (IFT), to  │
  │  the OPAQUE geometry-only forward carry                                                            │
  │      `hFwd : ContinuousOn ((z,v) ↦ fderiv ℝ (uniformFlowExp … z) v) (U ×ˢ ball 0 ρ)`.             │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  AFTER (J4-434):  `hFwd` is BUILT (`forwardFlowJet_continuousOn_of_baseMod`) by the `q₀`-anchored │
  │  triangle mirroring the VALUE-level `uniformFlowExp_joint_continuousWithinAt` one derivative up:   │
  │    • TERM 2 (velocity slot) = DERIVED (`forwardFlowJet_velocityContinuousAt`, from                 │
  │      `contDiffAt2_uniformFlowExp` + `ContDiffAt.fderiv_right`);                                    │
  │    • TERM 1 (base slot) = the single carried first-jet base modulus `hbaseJ`.                      │
  │  And the J3 chart continuity is wired (`chartFieldJacobian_continuousOn_of_baseMod`) modulo the    │
  │  SAME `hbaseJ` (+ banked origin continuity / nondeg / IFT).                                        │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE MISSING INGREDIENT (Sol #21).  `hbaseJ` = the first-jet base modulus                          │
  │      `‖fderiv (uniformFlowExp q) w − fderiv (uniformFlowExp q') w‖ ≤ exp L·‖q − q'‖`  (‖w‖ ≤ ρ),   │
  │  the operator-level one-derivative-up analogue of `uniformFlowExp_base_diff_bound`.  It is a TRUE  │
  │  geodesic-flow fact, derivable via `BasepointJetModulus.jacobi_twopoint_diff_bound` (two Jacobi    │
  │  fields, same seed `(0,δ)`, along the two base tubes; `Dcoef ≤ M₂·‖q−q'‖·exp`, `Jb ≤ ‖δ‖·exp` ⟹    │
  │  the operator modulus).  The PRECISE spec-exposure gap: the endpoint velocity Jacobi CLM `V_{q,v}` │
  │  is INTERNAL to `uniformFlowExp_hasFDerivAt` (a local `.choose`); banking it as a spec lemma       │
  │  `∃ V, (∀ δ, HasDerivAt (V δ) …) ∧ fderiv (uniformFlowExp q) v = (fun δ ↦ (V δ 1).1)` is the       │
  │  recommended J4-435, after which `hbaseJ` (hence `hFwd`, hence J3) discharges unconditionally.     │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.ForwardFlowJet
#print axioms forwardFlowJet_velocityContinuousAt
#print axioms forwardFlowJet_continuousWithinAt_of_baseMod
#print axioms forwardFlowJet_continuousOn_of_baseMod
#print axioms chartFieldJacobian_continuousOn_of_baseMod
end AxiomChecks
