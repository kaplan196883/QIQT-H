/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.

# J4-53: Uniform-flow transfer layer (Layer 2 of the (J) re-architecture)

The compact-uniform exp-nondegeneracy gate (J) has its entire doubled-family supply proved
(`expMap_common_nondeg_radius_of_doubled_supply`, `JacobiDoubledFamily.lean`), but its final
assembly is blocked on `hr_lt : ∀ q ∈ K, r < expRho g gi hC q`, where `expRho g gi hC q` is a
per-`q` OPAQUE `Classical.choose` selector (`ExpMap.lean:728`) with NO uniform-over-`K`
provenance — so `hr_lt` is unprovable from `hC`/`IsCompact K` alone.

The clean fix (GPT-5.5 consult) is to RE-ARCHITECT the (J) result onto the UNIFORM-flow
endpoint `F` supplied by `geodesic_apriori_confinement_uniform` — which carries a SINGLE uniform
confinement radius `ρ_K` over the compact `K`, with no opaque per-`q` selector — proving
nondegeneracy for `F` and carrying `F` (not `expMap`) as "the exp map" for the compact-uniform
result.

This file lands the **generic, reusable Layer-2 transfer lemmas** of that re-architecture: if two
maps agree on a ball around `0`, their Fréchet derivatives agree at every interior point, so a
uniform nondegeneracy radius for a "flow" map `F` transfers to a uniform nondegeneracy radius for a
"target" map `Exp` on the smaller (intersection) ball.  These are stated for an abstract normed
space `E` and an abstract base set `K` — no geometry, no opaque selectors — hence GUARANTEED green
and reusable both by the (J) re-architecture (`E := Point n`) and elsewhere.

HONEST SCOPE.  This file provides ONLY the transfer (Layer-2) plumbing.  It does NOT close (J):
producing the `F`-side hypotheses of `compact_nondeg_of_uniform_flow_eqOn` — a UNIFORM `Set.EqOn`
on `ball 0 ρ_K` (Layer-2 input `hEq`) and the `F`-side nondegeneracy `hUnitF` (Layer-1) — remains
the outstanding obligation of the (J) bridge refactor.  See the file firewall below.
-/
import QIQTH.UniformFlowBridge
import QIQTH.CommonNondegRadius
import QIQTH.JacobiDoubledFamily
import Mathlib

namespace QIQTH.ExpMap

open Set

set_option maxHeartbeats 400000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Transfer 1 — ball-agreement upgrades to a germ equality.**  If `f` and `F` agree on the open
ball `Metric.ball 0 R` and `v` is an interior point (`‖v‖ < R`), then `f` and `F` agree on a
neighbourhood of `v`, i.e. `f =ᶠ[𝓝 v] F`.  Via `Metric.isOpen_ball.mem_nhds` +
`Filter.eventuallyEq_of_mem`. -/
lemma eventuallyEq_of_eqOn_ball {f F : E → E} {R : ℝ} {v : E}
    (hEq : Set.EqOn f F (Metric.ball 0 R)) (hv : ‖v‖ < R) : f =ᶠ[nhds v] F := by
  have hvmem : v ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hv
  exact Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hvmem) hEq

/-- **Transfer 2 — nondegeneracy transports along ball-agreement.**  If `f` and `F` agree on
`Metric.ball 0 R`, `v` is interior (`‖v‖ < R`), and the Fréchet derivative of `F` at `v` is a unit
(nondegenerate), then so is the Fréchet derivative of `f` at `v`.  The germ equality forces the
Jacobians to coincide (`Filter.EventuallyEq.fderiv_eq`). -/
lemma isUnit_fderiv_of_eqOn_ball {f F : E → E} {R : ℝ} {v : E}
    (hEq : Set.EqOn f F (Metric.ball 0 R)) (hv : ‖v‖ < R)
    (hF : IsUnit (fderiv ℝ F v)) : IsUnit (fderiv ℝ f v) := by
  rw [(eventuallyEq_of_eqOn_ball hEq hv).fderiv_eq]; exact hF

/-- **Transfer 3 — compact-uniform nondegeneracy from a uniform-flow model (Layer 2 capstone).**
Let `Exp, F : Q → E → E` be two families indexed by a base set `K ⊆ Q`.  Suppose:

* on the ball `Metric.ball 0 ρeq`, `Exp q` agrees with the flow model `F q` for every `q ∈ K`
  (`hEq` — the UNIFORM ball agreement supplied by the flow bridge), and
* the flow model `F q` is nondegenerate on the ball `Metric.ball 0 ρF` uniformly over `q ∈ K`
  (`hUnitF` — the `F`-side uniform nondegeneracy).

Then `Exp q` is nondegenerate on the COMMON ball of radius `min ρeq ρF`, uniformly over `q ∈ K`.

This is the exact shape needed for the (J) re-architecture: it produces the compact-uniform
`∃ ρ0 > 0, ∀ q ∈ K, ∀ v, ‖v‖ < ρ0 → IsUnit (fderiv ℝ (Exp q) v)` conclusion of
`expMap_common_nondeg_radius_of_doubled_supply` WITHOUT ever mentioning the opaque per-`q`
selector `expRho`, provided the two uniform inputs `hEq`/`hUnitF` are supplied for `F`. -/
theorem compact_nondeg_of_uniform_flow_eqOn {Q : Type*} {Exp F : Q → E → E} {K : Set Q}
    {ρeq ρF : ℝ} (hρeq : 0 < ρeq) (hρF : 0 < ρF)
    (hEq : ∀ q ∈ K, Set.EqOn (Exp q) (F q) (Metric.ball 0 ρeq))
    (hUnitF : ∀ q ∈ K, ∀ v : E, ‖v‖ < ρF → IsUnit (fderiv ℝ (F q) v)) :
    ∃ ρ0 > (0 : ℝ), ∀ q ∈ K, ∀ v : E, ‖v‖ < ρ0 → IsUnit (fderiv ℝ (Exp q) v) := by
  refine ⟨min ρeq ρF, lt_min hρeq hρF, ?_⟩
  intro q hq v hv
  have hveq : ‖v‖ < ρeq := lt_of_lt_of_le hv (min_le_left _ _)
  have hvF : ‖v‖ < ρF := lt_of_lt_of_le hv (min_le_right _ _)
  exact isUnit_fderiv_of_eqOn_ball (hEq q hq) hveq (hUnitF q hq v hvF)

/-!
### File firewall — what remains for the (J) re-architecture.

`compact_nondeg_of_uniform_flow_eqOn` reduces compact-uniform nondegeneracy of the target family
`Exp := fun q => expMap g gi hC q` to TWO uniform-flow obligations for the model family `F`:

* `hEq` (Layer-2 input, UNIFORM `Set.EqOn` on `ball 0 ρeq`).  ⚠ NOT yet available uniformly.
  `UniformFlowBridge.fderiv_expMap_eq_uniform_flow_on_overlap` currently gives `expMap q = F q`
  only on the OVERLAP ball `‖w‖ < min (expRho g gi hC q) ρ` — which still contains the opaque
  `expRho g gi hC q`.  Upgrading this to `Set.EqOn (expMap q) (F q) (ball 0 ρ_K)` needs the
  ODE-uniqueness endpoint bridge run at the UNIFORM radius `ρ_K` (dropping the `expRho` guard),
  i.e. `expMap_eq_flow_endpoint` must be reproved with the uniform-flow confinement replacing the
  opaque-tube confinement.  ALTERNATIVELY, carry `F` itself as "the exp map" and never transfer
  back to `expMap` — then `hEq` is `Set.EqOn.refl` and drops out.

* `hUnitF` (Layer-1 input, `F`-side uniform nondegeneracy on `ball 0 ρ_K`).  ⚠ NOT yet available.
  Requires the doubled-family (J) supply re-linked to `F`'s Jacobian rather than `expMap`'s: the
  first-jet link `hlink` (currently `(Y … 1).2.1 = fderiv ℝ (expMap g gi hC q) (v+s•a) b`, gated by
  `hrad : ‖v+s•a‖ < expRho q`) must be restated with `F q` in place of `expMap g gi hC q`, at which
  point the `expRho`-gate is replaced by the uniform `ρ_K`-gate and `hr_lt` disappears.

Both obligations are LOCAL to the (J) bridge: `expMap_common_nondeg_radius_of_doubled_supply` is
consumed only by `AxiomAudit.lean` (`#print axioms`) and produced-for by `CommonNondegRadius.lean`;
the a₁=R/6 recenter/pullback-metric chain (`RecenterA1Capstone.trueKernel_diagonal_a1_recenter`,
`PullbackMetric.expPullbackMetric`) does NOT consume the compact-uniform (J) result — it uses the
per-point openness-of-units nondegeneracy `PullbackMetricNondegNearZero.expPullbackMetric_isUnit_near_zero`.
Hence the re-architecture does NOT ripple into the pullback-metric/recenter machinery.
-/

end QIQTH.ExpMap
