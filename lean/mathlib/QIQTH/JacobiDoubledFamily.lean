/-
  JacobiDoubledFamily — J4-39: the CLOSE assembly bridge for the compact-uniform local `a₁ = R/6`
  gate `(J)`.  Eliminating the opaque second-order velocity jet identification `hid` from the `(J)`
  capstone by DERIVING it, over the compact `K`, from GENUINE doubled-family ODE / confinement / first-
  jet-link data via `hid_of_doubled_data`, and chaining to
  `expMap_common_nondeg_radius_of_velocity_ode_data`.

  ## Context

  `JacobiOperatorFDeriv` (J4-37) landed `hid_of_doubled_data` — the POINTWISE assembly of the second-
  order velocity jet identification
      `hid : (fderiv ℝ (fun w => fderiv ℝ Fam w) v) a b = (Zf a b 1).1`
  from the doubled families `Y`/`Vf` (integral curves of `G = doubledField g gi` through the perturbed
  IC), the first-jet link `hlink`, the jet-map regularity `hdiff`, and the `Zf` second-variation ODE
  data.  `JacobiUniformSupply` (J4-38) landed `(S3)` — the jet-map differentiability
  `expMap_jetMap_differentiableAt_uniform` — DERIVED from `exp_q ∈ C⁴`, discharging `hdiff` over `K`.

  The `(J)` capstone `expMap_common_nondeg_radius_of_velocity_ode_data` (`FlowVelocityJacobiField`)
  produces the uniform common exp-nondegeneracy radius from ODE data PLUS the opaque input `hid`.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `expMap_common_nondeg_radius_of_doubled_supply` — **the CLOSE bridge.**  Specialising the family
    `Fam := fun q => expMap g gi hC q` (so the exp↔flow weld `hweld` is `rfl` and `hdiff` is discharged
    by `(S3)`), it CARRIES the doubled-family SUPPLY data over `K` — the doubled families `Y`/`Vf` as
    integral curves of `doubledField g gi` through the perturbed IC `((q, v+s·a),(0,b))` confined in a
    (per-`(q,v)`) compact convex `S`, the first-jet link `hlink`, and the second-variation `Zf` ODE data
    — DERIVES `hid` for every `q ∈ K`, `v ∈ B̄(0,r)`, `a`, `b` via `hid_of_doubled_data`, and chains
    through the capstone with the base-geodesic ODE / geometry data (`hZ`, `h0cap`, `hKbcap`, `hAd`,
    `hXb`, `hSd`) to the UNCONDITIONAL common radius.

    So `hid` is DERIVED here — NOT carried.  The final theorem's hypotheses are ONLY genuine doubled-
    family ODE / confinement / first-jet-link data and base-geodesic ODE / geometry data; there is NO
    `hid`, NO `HasFDerivAt` of the jet map, NO `hbnd`/`hunif`/`hFoplip`, and the conclusion (the uniform
    common nondeg radius over `K`) is NOT among the hypotheses.

  ## HONEST CHECKPOINT (binding) — what is discharged and what remains

  This DISCHARGES the `hid`-carrying firewall: `(J)` (the uniform common exp-nondeg radius over `K`) now
  follows WITHOUT the opaque second-order velocity jet identification `hid`, from the doubled-family
  SUPPLY plus base-geodesic ODE / geometry data.  The firewall MOVES from "assume the second-derivative
  identity `hid`" to "supply genuine doubled integral curves + the first-variation endpoint link
  `hlink`" — a cleaner, more-primitive firewall (per GPT-5.5: `hlink` is FIRST-jet information, the
  first-variation endpoint formula, and is NOT circular with the SECOND-jet `hid`, which the pointwise
  engine `hid_of_doubled_data` obtains by differentiating `hlink` once more in the `s` direction and
  matching the second-variation ODE).

  `(J)` is NOT yet FULLY closed as a self-contained theorem depending on `hC`/`K` alone: the doubled-
  family SUPPLY `(S1)` — exhibiting `Y`/`Vf` as genuine confined integral curves uniformly over `K`
  (`geodesic_apriori_confinement_uniform` ⊗ Jacobi/linearized existence packaged as a doubled flow) —
  and the first-jet link `(S2)` `hlink` remain the carried construction residual, to be discharged by a
  genuine geodesic⊕Jacobi doubled-flow construction (the confinement over the direction set being the
  key quantitative step).  This file does NOT construct the doubled families, does NOT smuggle
  `hid`/`hbnd`/`hunif`/`hFoplip`, does NOT build the covariant `D²/dτ²`, NOT Raychaudhuri (L3), NOT
  `a₁ = R/6`.
-/
import QIQTH.JacobiOperatorFDeriv
import QIQTH.JacobiUniformSupply
import QIQTH.FlowVelocityJacobiField
import QIQTH.VelocitySecondJetId
import QIQTH.BoundedGeometryConfine
import QIQTH.UniformFlowBridge
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **The CLOSE bridge — `(J)` from doubled-family supply, WITHOUT the opaque `hid`.**

    Specialising `Fam := fun q => expMap g gi hC q`, so the exp↔flow weld is `rfl` and the jet-map
    differentiability `hdiff` is discharged by `(S3)` (`expMap_jetMap_differentiableAt_uniform`), this
    carries the doubled-family SUPPLY over the compact `K`:
      * the doubled families `Y q v a b s τ` — integral curves of `G = doubledField g gi` on `[0,1]`
        with base IC perturbed by `s·((0,a),(0,0))` (`hYode`, `hIC`), confined in a per-`(q,v)` compact
        convex `S q v` (`hmem`);
      * the doubled variation fields `Vf q v a b τ` solving the doubled linearized ODE with seed
        `((0,a),(0,0))` (`hVode`, `hV0`);
      * the first-jet link `hlink : (Y q v a b s 1).2.1 = fderiv ℝ (expMap g gi hC q) (v+s•a) b`;
      * the phase second-order field `Zf q v a b τ` solving the matching second-variation ODE (`hZf`,
        `h0d`, `hKbd`);
    together with the base-geodesic second-order variation ODE / geometry data the capstone consumes for
    the endpoint two-point bound (`hZ`, `h0cap`, `hKbcap`, `hAd`, `hXb`, `hSd`).  It DERIVES `hid` for
    every `q ∈ K`, `v ∈ B̄(0,r)`, `a`, `b` via `hid_of_doubled_data`, and chains to
    `expMap_common_nondeg_radius_of_velocity_ode_data`, yielding a single `ρ₀ > 0` with
    `IsUnit (fderiv ℝ (expMap g gi hC q) v)` for all `q ∈ K`, `‖v‖ < ρ₀`.

    `hid` is DERIVED, not carried; the carried inputs are the doubled-family supply data and the base-
    geodesic ODE / geometry data. -/
theorem expMap_common_nondeg_radius_of_doubled_supply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {r K' D₀ X₀ Sr₀ : ℝ} (hr : 0 < r)
    (hK'0 : 0 ≤ K') (hD₀ : 0 ≤ D₀) (hX₀ : 0 ≤ X₀) (hSr₀ : 0 ≤ Sr₀)
    (hr_lt : ∀ q ∈ K, r < expRho g gi hC q)
    -- base-geodesic curve, phase second-order field, source (for the capstone `hbnd`):
    (Ybase : Point n → Point n → ℝ → Point n × Point n)
    (Zf Src : Point n → Point n → Point n → Point n → ℝ → Point n × Point n)
    -- doubled families and per-`(q,v)` confinement set:
    (Y : Point n → Point n → Point n → Point n → ℝ → ℝ →
      (Point n × Point n) × (Point n × Point n))
    (Vf : Point n → Point n → Point n → Point n → ℝ →
      (Point n × Point n) × (Point n × Point n))
    (S : Point n → Point n → Set ((Point n × Point n) × (Point n × Point n)))
    -- (S1) doubled-family confinement:
    (hScompact : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, IsCompact (S q v))
    (hSconvex : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, Convex ℝ (S q v))
    -- (S1) doubled-family ODE / IC / confinement:
    (hYode : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n, ∀ s : ℝ,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Y q v a b s) (doubledField g gi (Y q v a b s τ)) τ)
    (hVode : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Vf q v a b)
          (fderiv ℝ (doubledField g gi) (Y q v a b 0 τ) (Vf q v a b τ)) τ)
    (hV0 : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      Vf q v a b 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))))
    (hIC : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n, ∀ s : ℝ,
      Y q v a b s 0 - Y q v a b 0 0
        = s • (((0 : Point n), a), ((0 : Point n), (0 : Point n))))
    (hmem : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n, ∀ s : ℝ,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y q v a b s τ ∈ S q v)
    -- (S2) first-jet link:
    (hlink : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n, ∀ s : ℝ,
      (Y q v a b s 1).2.1 = fderiv ℝ (expMap g gi hC q) (v + s • a) b)
    -- (S1) doubled second-variation `Zf` ODE data (pointwise, for `hid_of_doubled_data`):
    (hZf : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun τ => Zf q v a b τ)
          (fderiv ℝ (geodesicField g gi) (Y q v a b 0 τ).1 (Zf q v a b τ)
            + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y q v a b 0 τ).1 (Vf q v a b τ).1
                (Y q v a b 0 τ).2) τ)
    (h0d : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      (Vf q v a b 0).2 = Zf q v a b 0)
    (hKbd : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ‖fderiv ℝ (geodesicField g gi) (Y q v a b 0 τ).1‖ ≤ K')
    -- base-geodesic second-order variation ODE / geometry data (for the capstone `hbnd`):
    (hZ : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Zf q v a b)
          (fderiv ℝ (geodesicField g gi) (Ybase q v τ) (Zf q v a b τ) + Src q v a b τ) τ)
    (h0cap : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      Zf q v a b 0 = Zf q' v a b 0)
    (hKbcap : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Ybase q v τ)‖ ≤ K')
    (hAd : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Ybase q v τ) - fderiv ℝ (geodesicField g gi) (Ybase q' v τ)‖
        ≤ D₀ * dist q q')
    (hXb : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Zf q v a b τ‖ ≤ X₀ * ‖a‖ * ‖b‖)
    (hSd : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Src q v a b τ - Src q' v a b τ‖ ≤ Sr₀ * dist q q' * ‖a‖ * ‖b‖) :
    ∃ ρ₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      IsUnit (fderiv ℝ (expMap g gi hC q) v) := by
  -- DERIVE `hid` over `K` from the doubled-family supply via `hid_of_doubled_data` (`Fam := exp_q`).
  have hid : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r, ∀ a b : Point n,
      (fderiv ℝ (fun w => fderiv ℝ ((fun q => expMap g gi hC q) q) w) v) a b
        = (Zf q v a b 1).1 := by
    intro q hq v hv a b
    have hdiff : DifferentiableAt ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v :=
      expMap_jetMap_differentiableAt_uniform g gi hC hr_lt q hq v hv
    exact hid_of_doubled_data g gi hC hK'0 (hScompact q hq v hv) (hSconvex q hq v hv)
      (Y q v) (Vf q v) hdiff
      (fun a b s τ hτ => hYode q hq v hv a b s τ hτ)
      (fun a b τ hτ => hVode q hq v hv a b τ hτ)
      (fun a b => hV0 q hq v hv a b)
      (fun a b s => hIC q hq v hv a b s)
      (fun a b s τ hτ => hmem q hq v hv a b s τ hτ)
      (fun a b s => hlink q hq v hv a b s)
      (fun a b τ hτ => hZf q hq v hv a b τ hτ)
      (fun a b => h0d q hq v hv a b)
      (fun a b τ hτ => hKbd q hq v hv a b τ hτ)
      a b
  -- chain to the `(J)` capstone with the DERIVED `hid` and the base-geodesic ODE / geometry data.
  exact expMap_common_nondeg_radius_of_velocity_ode_data g gi hC hK hr hK'0 hD₀ hX₀ hSr₀ hr_lt
    (fun q => expMap g gi hC q) Ybase Zf Src (fun q _ v _ => rfl) hid
    hZ h0cap hKbcap hAd hXb hSd

end QIQTH.ExpMap
