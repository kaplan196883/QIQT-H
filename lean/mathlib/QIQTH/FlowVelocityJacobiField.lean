/-
  FlowVelocityJacobiField — J4-32: DISCHARGING the endpoint two-point bound `hbnd` of the second-order
  velocity Jacobi jet from PRIMITIVE base-geodesic ODE data, and CONSTRUCTING the position-valued
  second-order velocity field `Z` from a phase-space second-order variation field.

  ## Context

  `FlowVelocitySecondJet` (J4-31) reduced `(J)` / the unconditional common exp-nondegeneracy radius over
  a compact `K` to the concrete second-order velocity Jacobi jet DATA:

    * `hid`  — the IDENTIFICATION `fderiv²(Fam q) v a b = Z q v a b 1` (the velocity-slot second-order
      variational-equation identification of the flow-endpoint 2-jet with an ODE object), and
    * `hbnd` — the vector-level two-point endpoint bound
      `‖Z q v a b 1 − Z q' v a b 1‖ ≤ Λ·dist(q,q')·‖a‖·‖b‖`.

  The direction-agnostic two-point ODE ENGINE `flowVelocity_secondJet_endpoint_twopoint_bound`
  (`FlowVelocitySecondJet`) already bounds the endpoint difference of two INHOMOGENEOUS second-order
  velocity fields `Z₁, Z₂` solving `Z' = DF(Y)·Z + Source` along two base geodesics `Y₁, Y₂` with the
  SAME seed, by `(Dcoef·Xb + Dsrc)·exp K`.  This file packages that engine, per direction pair `(a,b)`,
  with the bilinearly-scaled uniform constants (coefficient separation `∝ dist`, field bound `∝ ‖a‖·‖b‖`,
  source separation `∝ dist·‖a‖·‖b‖`), delivering `hbnd` with `Λ = (D₀·X₀ + Sr₀)·exp K'`.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `flowVelocity_secondJet_hbnd_of_ode_data` — **(the ODE→`hbnd` bridge).**  Given a PHASE-SPACE
    second-order velocity field `Zf : … → ℝ → Point n × Point n` and a source `Src` such that, for all
    `q, q' ∈ K`, `v ∈ B̄(0,r)`, `a, b`, the field `Zf q v a b` solves the inhomogeneous linearized
    geodesic ODE `Z' = DF(Y_{q,v})·Z + Src` on `[0,1]` (`hZ`), the two `q`/`q'` fields share the seed
    (`h0`), the base-curve coefficient is bounded (`hKb`) and its `q`/`q'` separation is `≤ D₀·dist q q'`
    (`hAd`), the field is bounded `‖Zf q v a b τ‖ ≤ X₀·‖a‖·‖b‖` (`hXb`), and the sources separate by
    `≤ Sr₀·dist q q'·‖a‖·‖b‖` (`hSd`), then the POSITION endpoint two-point bound
        `‖(Zf q v a b 1).1 − (Zf q' v a b 1).1‖ ≤ (D₀·X₀ + Sr₀)·exp K'·dist q q'·‖a‖·‖b‖`
    holds.  DERIVED per `(a,b)` from `flowVelocity_secondJet_endpoint_twopoint_bound` with
    `Dcoef := D₀·dist q q'`, `Xb := X₀·‖a‖·‖b‖`, `Dsrc := Sr₀·dist q q'·‖a‖·‖b‖`, then projecting onto the
    position component (`Prod.fst_sub` + `Prod.norm_def`) and collecting the constant by `ring`.  This is
    exactly the `hbnd` shape of `FlowVelocitySecondJet` with `Λ = (D₀·X₀ + Sr₀)·exp K'`.

  * `expMap_common_nondeg_radius_of_velocity_ode_data` — **(the `(J)` capstone from ODE data + `hid`).**
    CONSTRUCTS the position field `Z q v a b τ := (Zf q v a b τ).1` from the supplied phase field, DERIVES
    `hbnd` (via the bridge above), and chains through
    `FlowVelocitySecondJet.expMap_common_nondeg_radius_of_velocity_jet_data` to the UNCONDITIONAL common
    exp-nondegeneracy radius over `K`.  `hbnd` is DERIVED here (not carried); the carried genuine inputs
    are the base-geodesic ODE / `BoundedGeometry`-style regularity data (`hZ`, `h0`, `hKb`, `hAd`, `hXb`,
    `hSd`, the nonnegativity of the uniform constants) and the still-firewalled second-order velocity jet
    IDENTIFICATION `hid` (plus the `(I1)` radius and the weld).

  DERIVED vs CARRIED.  DERIVED = the ODE→`hbnd` bridge (from the two-point engine) and the `hbnd`
  discharge in the capstone.  CARRIED genuine inputs (NOT the conclusion, NOT `hbnd`):
    * `hZ`, `h0`, `hKb`, `hAd`, `hXb`, `hSd` — the base-geodesic second-order variation ODE facts and the
      uniform two-point constant bounds (the honest `BoundedGeometry` regularity data, more primitive than
      the endpoint bound `hbnd` they entail);
    * `hid` — the second-order velocity jet IDENTIFICATION (the velocity-slot analogue of the base-point
      second jet `HasFDerivAt (fun δ => V δ t) L₂ 0` that `BasepointJacobi2`'s honest checkpoint records as
      NOT-yet-built), plus the exp↔flow 2nd-jet weld `hweld` and the `(I1)` uniform injectivity radius.

  HONEST CHECKPOINT (binding).  This DISCHARGES `hbnd` from primitive base-geodesic ODE data (moving it
  from carried to derived) and CONSTRUCTS the position field `Z` from a phase-space field, thereby
  REDUCING `(J)` / the unconditional common radius over `K` from the two carried inputs `{hid, hbnd}` to
  the single carried IDENTIFICATION `hid` plus the base-geodesic ODE / geometry data.  It does NOT build
  `hid` itself (the second-order velocity jet ODE identification — the genuinely-unbuilt frontier), NOT
  Raychaudhuri (L3), NOT `a₁ = R/6`.
-/
import QIQTH.FlowVelocitySecondJet
import QIQTH.BasepointSecondJetFDeriv
import QIQTH.BasepointFDeriv
import QIQTH.BasepointJacobi2
import QIQTH.DecayOrderThree
import QIQTH.UniformFlowBridge
import QIQTH.BoundedGeometry
import QIQTH.BoundedGeometryConfine
import QIQTH.JacobiEquation
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **The ODE→`hbnd` bridge (endpoint two-point bound from primitive base-geodesic ODE data).**
    Let `Zf : Point n → Point n → Point n → Point n → ℝ → Point n × Point n` be a PHASE-SPACE second-order
    velocity field and `Src` a source, such that for all `q, q' ∈ K`, `v ∈ B̄(0,r)`, and all direction
    pairs `(a,b)`:
      * `Zf q v a b` solves the inhomogeneous linearized geodesic ODE
        `Z' = DF(Y q v)·Z + Src q v a b` on `[0,1]` (`hZ`),
      * the `q`/`q'` fields share the seed at `0` (`h0`),
      * the base-curve coefficient `‖DF(Y q v τ)‖ ≤ K'` (`hKb`) with `q`/`q'` separation
        `‖DF(Y q v τ) − DF(Y q' v τ)‖ ≤ D₀·dist q q'` (`hAd`),
      * the field is bilinearly bounded `‖Zf q v a b τ‖ ≤ X₀·‖a‖·‖b‖` (`hXb`), and
      * the sources separate by `‖Src q v a b τ − Src q' v a b τ‖ ≤ Sr₀·dist q q'·‖a‖·‖b‖` (`hSd`).
    Then the POSITION endpoint two-point bound holds:
        `‖(Zf q v a b 1).1 − (Zf q' v a b 1).1‖ ≤ (D₀·X₀ + Sr₀)·exp K'·dist q q'·‖a‖·‖b‖`.
    DERIVED per `(a,b)` from `flowVelocity_secondJet_endpoint_twopoint_bound` (`Dcoef := D₀·dist q q'`,
    `Xb := X₀·‖a‖·‖b‖`, `Dsrc := Sr₀·dist q q'·‖a‖·‖b‖`), projected to the position component and collected
    by `ring`.  This is the `hbnd` shape of `FlowVelocitySecondJet` with `Λ = (D₀·X₀ + Sr₀)·exp K'`. -/
theorem flowVelocity_secondJet_hbnd_of_ode_data (g gi : Point n → Fin n → Fin n → ℝ)
    {K : Set (Point n)} {r K' D₀ X₀ Sr₀ : ℝ} (hK'0 : 0 ≤ K')
    (Y : Point n → Point n → ℝ → Point n × Point n)
    (Zf Src : Point n → Point n → Point n → Point n → ℝ → Point n × Point n)
    (hZ : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Zf q v a b)
          (fderiv ℝ (geodesicField g gi) (Y q v τ) (Zf q v a b τ) + Src q v a b τ) τ)
    (h0 : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      Zf q v a b 0 = Zf q' v a b 0)
    (hKb : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y q v τ)‖ ≤ K')
    (hAd : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y q v τ) - fderiv ℝ (geodesicField g gi) (Y q' v τ)‖
        ≤ D₀ * dist q q')
    (hXb : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Zf q v a b τ‖ ≤ X₀ * ‖a‖ * ‖b‖)
    (hSd : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Src q v a b τ - Src q' v a b τ‖ ≤ Sr₀ * dist q q' * ‖a‖ * ‖b‖) :
    ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ‖(Zf q v a b 1).1 - (Zf q' v a b 1).1‖
        ≤ (D₀ * X₀ + Sr₀) * Real.exp K' * dist q q' * ‖a‖ * ‖b‖ := by
  intro q hq q' hq' v hv a b
  -- the phase-space endpoint two-point bound from the direction-agnostic two-point ODE engine.
  have hphase :
      ‖Zf q v a b 1 - Zf q' v a b 1‖
        ≤ (D₀ * dist q q' * (X₀ * ‖a‖ * ‖b‖) + Sr₀ * dist q q' * ‖a‖ * ‖b‖) * Real.exp K' :=
    flowVelocity_secondJet_endpoint_twopoint_bound g gi hK'0
      (Y₁ := Y q v) (Y₂ := Y q' v) (Z₁ := Zf q v a b) (Z₂ := Zf q' v a b)
      (S₁ := Src q v a b) (S₂ := Src q' v a b)
      (K := K') (Dcoef := D₀ * dist q q') (Xb := X₀ * ‖a‖ * ‖b‖)
      (Dsrc := Sr₀ * dist q q' * ‖a‖ * ‖b‖)
      (fun τ hτ => hZ q hq v hv a b τ hτ)
      (fun τ hτ => hZ q' hq' v hv a b τ hτ)
      (h0 q hq q' hq' v hv a b)
      (fun τ hτ => hKb q hq v hv τ hτ)
      (fun τ hτ => hAd q hq q' hq' v hv τ hτ)
      (fun τ hτ => hXb q' hq' v hv a b τ hτ)
      (fun τ hτ => hSd q hq q' hq' v hv a b τ hτ)
  -- project onto the position component and collect the constant.
  calc ‖(Zf q v a b 1).1 - (Zf q' v a b 1).1‖
      = ‖(Zf q v a b 1 - Zf q' v a b 1).1‖ := by rw [Prod.fst_sub]
    _ ≤ ‖Zf q v a b 1 - Zf q' v a b 1‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    _ ≤ (D₀ * dist q q' * (X₀ * ‖a‖ * ‖b‖) + Sr₀ * dist q q' * ‖a‖ * ‖b‖) * Real.exp K' := hphase
    _ = (D₀ * X₀ + Sr₀) * Real.exp K' * dist q q' * ‖a‖ * ‖b‖ := by ring

/-- **`(J)` capstone from ODE data + the second-order jet identification.**  With the `(I1)` uniform
    injectivity radius `hr_lt`, the exp↔flow 2nd-jet weld `hweld`, the second-order velocity jet
    IDENTIFICATION `hid` (`fderiv²(Fam q) v a b = (Zf q v a b 1).1`), and the base-geodesic second-order
    variation ODE data (`hZ`, `h0`, `hKb`, `hAd`, `hXb`, `hSd` with nonnegative uniform constants),
    there is a single `ρ₀ > 0` with `IsUnit (fderiv ℝ (expMap g gi hC q) v)` for all `q ∈ K`, `‖v‖ < ρ₀`.

    DERIVED: the position field `Z q v a b τ := (Zf q v a b τ).1` is CONSTRUCTED from the phase field,
    `hbnd` is DERIVED via `flowVelocity_secondJet_hbnd_of_ode_data` (with
    `Λ = (D₀·X₀ + Sr₀)·exp K' ≥ 0`), and the result is chained through
    `expMap_common_nondeg_radius_of_velocity_jet_data`.  So `hbnd` is no longer carried — it is derived
    from the primitive base-geodesic ODE / `BoundedGeometry`-style regularity data.  The remaining carried
    genuine input is the second-order velocity jet identification `hid` (plus the weld and the `(I1)`
    radius). -/
theorem expMap_common_nondeg_radius_of_velocity_ode_data (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {r K' D₀ X₀ Sr₀ : ℝ} (hr : 0 < r)
    (hK'0 : 0 ≤ K') (hD₀ : 0 ≤ D₀) (hX₀ : 0 ≤ X₀) (hSr₀ : 0 ≤ Sr₀)
    (hr_lt : ∀ q ∈ K, r < expRho g gi hC q)
    (Fam : Point n → Point n → Point n)
    (Y : Point n → Point n → ℝ → Point n × Point n)
    (Zf Src : Point n → Point n → Point n → Point n → ℝ → Point n × Point n)
    (hweld : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r,
      fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v
        = fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v)
    (hid : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      (fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v) a b = (Zf q v a b 1).1)
    (hZ : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Zf q v a b)
          (fderiv ℝ (geodesicField g gi) (Y q v τ) (Zf q v a b τ) + Src q v a b τ) τ)
    (h0 : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      Zf q v a b 0 = Zf q' v a b 0)
    (hKb : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y q v τ)‖ ≤ K')
    (hAd : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y q v τ) - fderiv ℝ (geodesicField g gi) (Y q' v τ)‖
        ≤ D₀ * dist q q')
    (hXb : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Zf q v a b τ‖ ≤ X₀ * ‖a‖ * ‖b‖)
    (hSd : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Src q v a b τ - Src q' v a b τ‖ ≤ Sr₀ * dist q q' * ‖a‖ * ‖b‖) :
    ∃ ρ₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      IsUnit (fderiv ℝ (expMap g gi hC q) v) := by
  -- CONSTRUCT the position field `Z` from the phase field `Zf`.
  set Z : Point n → Point n → Point n → Point n → ℝ → Point n :=
    fun q v a b τ => (Zf q v a b τ).1 with hZdef
  -- the uniform Lipschitz constant, nonnegative.
  set Λ : ℝ := (D₀ * X₀ + Sr₀) * Real.exp K' with hΛdef
  have hΛ : 0 ≤ Λ := by rw [hΛdef]; positivity
  -- DERIVE `hbnd` for the constructed `Z` from the ODE data.
  have hbnd : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ‖Z q v a b 1 - Z q' v a b 1‖ ≤ Λ * dist q q' * ‖a‖ * ‖b‖ := by
    intro q hq q' hq' v hv a b
    have := flowVelocity_secondJet_hbnd_of_ode_data g gi hK'0 Y Zf Src
      hZ h0 hKb hAd hXb hSd q hq q' hq' v hv a b
    rw [hΛdef]
    simpa only [hZdef] using this
  -- chain through the `FlowVelocitySecondJet` capstone (with `hid` for the constructed `Z`).
  exact expMap_common_nondeg_radius_of_velocity_jet_data g gi hC hK hr hΛ hr_lt Fam Z
    hweld hid hbnd

end QIQTH.ExpMap

