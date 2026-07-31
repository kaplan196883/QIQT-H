/-
  BasepointJetLipschitz — J4-30 (the SECOND-ORDER weld): moving the operator q-Lipschitz input
  `hoplip` of the velocity 2-jet off the opaque `Classical.choose` tube `expTube` and onto the
  CONCRETE uniform-confinement flow-endpoint family `F`.

  ## Context

  `BasepointJetModulus` (J4-29) reduced the joint-continuity input `(J)` — hence the common
  exp-nondegeneracy radius over a compact base set `K` — to the SINGLE operator q-Lipschitz bound

    `hoplip : ‖fderiv²(exp_q) v − fderiv²(exp_{q'}) v‖ ≤ Λ·dist(q,q')`

  uniform over `v ∈ B̄(0,r)`, `q,q' ∈ K`, via `expMap_second_jet_hunif_of_op_lipschitz`.  But that
  bound is stated on the concrete `expMap g gi hC q`, which is welded to a per-`q` OPAQUE tube
  `expTube` (`irreducible`, `Classical.choose`), so it cannot be attacked directly.

  `UniformFlowBridge` (J4-20) supplies, over a compact `K`, a single overlap radius `ρ > 0` and, for
  each `q ∈ K`, a CONCRETE uniform-confinement geodesic-flow endpoint `F : Point n → Point n`
  (`F w = (Y_{q,w} 1).1`, each `Y_{q,w}` a genuine `(-2,2)` integral curve of `geodesicField` through
  `(q,w)`) agreeing with `expMap g gi hC q` on the OPEN overlap ball `‖·‖ < min (expRho q) ρ`, with
  the FIRST Fréchet derivatives already welded there
  (`fderiv_expMap_eq_uniform_flow_on_overlap` : `fderiv (exp_q) = fderiv F` on the overlap).

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `fderiv2_eqOn_of_fderiv_eqOn_isOpen` — **(the pure-analysis 2nd-order weld engine).**  For any two
    maps `f, F : E → E'` whose Fréchet derivatives AGREE on an OPEN set `U`
    (`Set.EqOn (fderiv ℝ f) (fderiv ℝ F) U`), their SECOND Fréchet derivatives agree on `U` too
    (`Set.EqOn (fderiv ℝ (fderiv ℝ f)) (fderiv ℝ (fderiv ℝ F)) U`).  Proof: at each `v ∈ U` the open
    set is a neighbourhood, so the first-derivative equality is an `EventuallyEq`, and
    `Filter.EventuallyEq.fderiv_eq` differentiates it once more.  Reusable, geometry-free.

  * `fderiv2_expMap_eq_uniform_flow_on_overlap` — **(the concrete 2nd-order weld, capstone of step 1).**
    Iterating the first-order flow bridge with the engine: over a compact `K` there is a single overlap
    radius `ρ > 0` such that at every `q ∈ K` the CONCRETE flow endpoint `F` satisfies
        `fderiv²(exp_q) v = fderiv²(F) v`   for `‖v‖ < min (expRho g gi hC q) ρ`,
    with `F`'s full uniform-flow spec exposed (each `Y_{q,w}`, `‖w‖ ≤ ρ`, a `(-2,2)` integral curve
    through `(q,w)`, `C₀‖w‖`-confined).  This moves the exp velocity 2-jet onto a concrete W-family,
    NOT welded to the opaque `expTube`.

  * `expMap_second_jet_hunif_of_flow_op_lipschitz` — **(the reduction of `hunif` to the F-side).**  If a
    family `Fam : Point n → Point n → Point n` welds to the exp velocity 2-jet on `B̄(0,r)`
    (`hweld`, produced by `fderiv2_expMap_eq_uniform_flow_on_overlap` for `r` inside the overlap) and
    carries the operator q-Lipschitz bound
        `‖fderiv²(Fam q) v − fderiv²(Fam q') v‖ ≤ Λ·dist(q,q')`   (`hFoplip`, uniform over `B̄(0,r)`),
    then `hunif` holds — chained through `expMap_second_jet_hunif_of_op_lipschitz`.  So `(J)` is reduced
    to the CONCRETE flow-side op-Lipschitz bound `hFoplip`, with the opaque-tube firewall dissolved.

  DERIVED vs CARRIED.  DERIVED = the 2nd-order weld engine, the concrete exp↔flow 2nd-jet weld, and the
  reduction chaining.  CARRIED genuine input for the FULL discharge of `(J)`: the flow-side op-Lipschitz
  bound `hFoplip` — a concrete statement about the flow endpoint `F` (its velocity 2nd jet is the
  second-order velocity Jacobi field along the geodesic through `(q,v)`; the two-point `q` vs `q'`
  difference is bounded by `linODE_twopoint_diff_bound` fed with the velocity-2nd-jet ODE
  `jacobiVariation_secondOrder` and the uniform-over-`K` `BoundedGeometry` constants).  `hFoplip` is NOT
  the conclusion and is NOT welded to `expTube`.

  HONEST CHECKPOINT (binding).  This DISCHARGES the 2nd-order weld (step 1 of J4-30): `hoplip`/`hunif`
  are moved from the opaque `expTube` onto the concrete flow endpoint `F`.  It does NOT identify
  `fderiv²(F)` with the concrete velocity 2nd-jet Jacobi field (the second-order variational-equation
  identification), does NOT wire that field's two-point difference through
  `linODE_twopoint_diff_bound`, and does NOT assemble the uniform `Λ` from `BoundedGeometry` — so it
  does NOT yet discharge `hFoplip` itself.  It does NOT build Raychaudhuri (L3) nor `a₁ = R/6`.
-/
import QIQTH.BasepointJetModulus
import QIQTH.UniformFlowBridge
import QIQTH.JacobiEquation
import QIQTH.BoundedGeometry
import QIQTH.BoundedGeometryConfine
import QIQTH.BasepointSecondJet
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **The pure-analysis 2nd-order weld engine.**  If two maps `f, F : E → E'` have Fréchet derivatives
    that AGREE on an OPEN set `U`, then their SECOND Fréchet derivatives agree on `U` as well.  At each
    `v ∈ U` the open set is a neighbourhood of `v`, so the first-derivative equality upgrades to an
    `EventuallyEq` at `𝓝 v`, and `Filter.EventuallyEq.fderiv_eq` differentiates it once more.  Pure
    analysis, geometry-free, reusable. -/
theorem fderiv2_eqOn_of_fderiv_eqOn_isOpen {E E' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {f F : E → E'} {U : Set E} (hU : IsOpen U)
    (hfd : Set.EqOn (fderiv ℝ f) (fderiv ℝ F) U) :
    Set.EqOn (fderiv ℝ (fderiv ℝ f)) (fderiv ℝ (fderiv ℝ F)) U := by
  intro v hv
  exact (Filter.eventuallyEq_of_mem (hU.mem_nhds hv) hfd).fderiv_eq

/-- **The concrete 2nd-order weld over a compact base set (capstone of J4-30 step 1).**  Iterating the
    first-order flow bridge `fderiv_expMap_eq_uniform_flow_on_overlap` with the 2nd-order weld engine
    `fderiv2_eqOn_of_fderiv_eqOn_isOpen`: over a compact `K` there is a single overlap radius `ρ > 0`
    and a confinement constant `C₀ ≥ 0` such that at every `q ∈ K` the CONCRETE uniform-flow endpoint
    `F : Point n → Point n` (its full uniform-flow spec exposed) satisfies

      `fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v
         = fderiv ℝ (fun w => fderiv ℝ F w) v`   for all `‖v‖ < min (expRho g gi hC q) ρ`.

    This transfers the exp-map velocity SECOND jet onto a concrete geodesic-flow W-family — NOT welded
    to the opaque `expTube` — so the operator q-Lipschitz input `hoplip` can now be attacked on `F`.
    DERIVED via the flow bridge (first-order weld) + the 2nd-order weld engine. -/
theorem fderiv2_expMap_eq_uniform_flow_on_overlap
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ q ∈ K,
      ∃ F : Point n → Point n,
        (∀ w : Point n, ‖w‖ ≤ ρ →
          ∃ Y : ℝ → Point n × Point n,
            Y 0 = (q, w) ∧
            (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1,
              ‖Y t - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖) ∧
            F w = (Y 1).1) ∧
        (∀ w : Point n, ‖w‖ < min (expRho g gi hC q) ρ →
          expMap g gi hC q w = F w) ∧
        (∀ v : Point n, ‖v‖ < min (expRho g gi hC q) ρ →
          fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v
            = fderiv ℝ (fun w => fderiv ℝ F w) v) := by
  obtain ⟨ρ, hρ, C₀, hC₀, hfam⟩ := fderiv_expMap_eq_uniform_flow_on_overlap g gi hC hK
  refine ⟨ρ, hρ, C₀, hC₀, ?_⟩
  intro q hq
  obtain ⟨F, hFspec, hFeq, hFfd⟩ := hfam q hq
  refine ⟨F, hFspec, hFeq, ?_⟩
  -- The open overlap ball is a neighbourhood of every interior velocity.
  set c : ℝ := min (expRho g gi hC q) ρ with hc
  have hopen : IsOpen {w : Point n | ‖w‖ < c} :=
    isOpen_lt continuous_norm continuous_const
  have hEqOn : Set.EqOn (fderiv ℝ (expMap g gi hC q)) (fderiv ℝ F)
      {w : Point n | ‖w‖ < c} := fun w hw => hFfd w hw
  -- differentiate the first-order weld once more.
  have h2 := fderiv2_eqOn_of_fderiv_eqOn_isOpen hopen hEqOn
  intro v hv
  exact h2 (show v ∈ {w : Point n | ‖w‖ < c} from hv)

/-- **The reduction of `hunif` to the concrete flow-side op-Lipschitz bound.**  Given a family
    `Fam : Point n → Point n → Point n` that (i) WELDS to the exp velocity 2-jet on the closed ball
    `B̄(0,r)` — `fderiv²(exp_q) v = fderiv²(Fam q) v` for all `q ∈ K`, `v ∈ B̄(0,r)` (`hweld`, delivered
    by `fderiv2_expMap_eq_uniform_flow_on_overlap` whenever `r` is inside the overlap) — and (ii)
    carries the OPERATOR q-Lipschitz bound
        `‖fderiv²(Fam q) v − fderiv²(Fam q') v‖ ≤ Λ·dist(q,q')`   (`hFoplip`, uniform over `B̄(0,r)`),
    the base-point uniform modulus `hunif` holds.  Chained through the route-P capstone
    `expMap_second_jet_hunif_of_op_lipschitz`.  This REDUCES `(J)`'s remaining base-point input to the
    concrete flow-side op-Lipschitz bound `hFoplip`, with the opaque-`expTube` firewall dissolved.
    DERIVED — the carried genuine input is `hFoplip` (about the concrete flow endpoint), NOT the
    conclusion. -/
theorem expMap_second_jet_hunif_of_flow_op_lipschitz (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} {r Λ : ℝ} (hΛ : 0 ≤ Λ)
    (Fam : Point n → Point n → Point n)
    (hweld : ∀ q ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r,
      fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v
        = fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v)
    (hFoplip : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r,
      ‖fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v
        - fderiv ℝ (fun w => fderiv ℝ (Fam q') w) v‖ ≤ Λ * dist q q') :
    ∀ ε > 0, ∃ δ > 0, ∀ q ∈ K, ∀ q' ∈ K, dist q q' < δ →
        ∀ v ∈ Metric.closedBall (0 : Point n) r,
          |‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v‖
            - ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q') w) v‖| ≤ ε := by
  refine expMap_second_jet_hunif_of_op_lipschitz g gi hC hΛ (fun q hq q' hq' v hv => ?_)
  rw [hweld q hq v hv, hweld q' hq' v hv]
  exact hFoplip q hq q' hq' v hv

end QIQTH.ExpMap
