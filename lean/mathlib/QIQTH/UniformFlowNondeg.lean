/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.

# J4-54: The uniform-flow exp endpoint `uniformFlowExp` (K1 of the (J) re-architecture)

The compact-uniform exp-nondegeneracy gate (J),
  `∃ ρ₀>0, ∀ q∈K, ∀ v, ‖v‖<ρ₀ → IsUnit (fderiv ℝ (expMap g gi hC q) v)`,
is blocked because its ENTIRE existing proof chain routes through the per-`q` OPAQUE
`expRho g gi hC q` (a `Classical.choose` injectivity radius, `ExpMap.lean`) and needs the
hypothesis `hr_lt : ∀ q ∈ K, r < expRho g gi hC q`, which is UNPROVABLE — `expRho` carries no
uniform-over-`K` provenance.

The fix (GPT-5.5 consult; J4-53 scope investigation) is to RE-ARCHITECT (J) onto a UNIFORM-flow
endpoint map that carries a GENUINE uniform radius `ρ_K` supplied by the compact-uniform
Picard–Lindelöf confinement lemma `geodesic_apriori_confinement_uniform`
(`BoundedGeometryConfine.lean`) — so `expRho`/`hr_lt` never appear.

## What lands here (K1 — GREEN, self-contained, NO opaque per-`q` selector)

The uniform-flow endpoint, previously a LOCAL `set F := fun w => (Yfun w 1).1` inside
`UniformFlowBridge.fderiv_expMap_eq_uniform_flow_on_overlap`, is HOISTED to repo-level named
definitions:

* `uniformFlowRadius g gi hC hK` — the SINGLE uniform confinement radius `ρ_K > 0` over the
  compact base set `K` (`uniformFlowRadius_pos`).  Genuine provenance: the compact-uniform PL
  datum inside `geodesic_apriori_confinement_uniform`.  NOT the opaque `expRho`.
* `uniformFlowConst g gi hC hK` — the uniform confinement constant `C₀ ≥ 0`
  (`uniformFlowConst_nonneg`).
* `uniformFlowTube g gi hC hK q w` — the confined geodesic phase-flow through `(q, w)` (a genuine
  `(-2,2)` integral curve of `geodesicField`), Skolemized at the named radius.
* `uniformFlowExp g gi hC hK q : Point n → Point n` — the POSITION endpoint map
  `w ↦ (uniformFlowTube … q w 1).1`.  This is the `F` carried "as the exp map" downstream.

with spec lemmas exposing, for every `q ∈ K` and `‖w‖ ≤ ρ_K`, the tube's initial condition,
geodesic ODE, and `C₀‖w‖`-confinement (`uniformFlowTube_spec` and its projections), plus the
endpoint identity `uniformFlowExp_eq`.  A COMPATIBILITY lemma `expMap_eq_uniformFlowExp_on_overlap`
(NOT on the (J)-for-F path — it deliberately keeps the `expRho` overlap guard) records that on the
overlap ball the two maps agree, via the existing ODE-uniqueness bridge.

`uniformFlowExp` is a GENUINE geodesic-flow endpoint (for `q ∈ K`, `‖w‖ ≤ ρ_K` the tube is a real
integral curve of the geodesic field from `(q, w)` — see `uniformFlowTube_spec_ode`), NOT vacuous.

## HONEST FIREWALL — (J)-for-F is NOT closed here (K2/K3 remain).

Closing
  (J)-for-F:  `∃ ρ₀>0, ∀ q∈K, ∀ v, ‖v‖<ρ₀ → IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v)`
requires DIFFERENTIABILITY of `uniformFlowExp q` in `w`, which this file does NOT provide.  The
uniform flow `α` inside `geodesic_apriori_confinement_uniform` is built from Mathlib's
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`, which supplies
only Lipschitz-in-INITIAL-CONDITION dependence (`hlip`), NOT C¹/`HasFDerivAt`-in-IC.  Hence
`uniformFlowExp q` is only Lipschitz in `w`; `fderiv ℝ (uniformFlowExp q) w` is junk unless `F`'s
differentiability at `w` is established INDEPENDENTLY (routing it through `expMap` agreement would
re-import `expRho`).  Mathlib has NO C¹-in-IC PL-flow theorem (confirmed).

The remaining work (K2/K3), per GPT-5.5 (model gpt-5.5, reasoning high):

* (K2) A NEW reusable variational-flow theorem
    `endpoint_hasFDerivAt_of_quadratic_remainder` :
      given two integral curves `y_x`, `y_{x+h}` of the geodesic spray on `[0,1]` inside the
      confinement tube, the Lipschitz-in-IC bound `‖y_{x+h}(t) − y_x(t)‖ ≤ C_ic‖h‖`, the operator
      variational flow `Φ_x` (`Φ_x' = DV(y_x)∘Φ_x`, `Φ_x(0)=id`), and a QUADRATIC Taylor remainder
      for the spray on the tube `‖V z − V y − DV y (z−y)‖ ≤ C₂‖z−y‖²`, prove
        `‖y_{x+h}(1) − y_x(1) − Φ_x(1) h‖ ≤ C‖h‖²`,
      hence `HasFDerivAt (fun x => y_x 1) (Φ_x 1) x` — via an inhomogeneous linear Grönwall
      (`linODE_twopoint_diff_bound`-style) on `r_h := δ_h − ζ_h`.  Specializing to the initial
      point `(q, w/s)` and projecting the position component gives BOTH differentiability of
      `uniformFlowExp q` at `w` AND `fderiv ℝ (uniformFlowExp q) w = π ∘ Φ 1 ∘ ι`, with NO `expRho`.
      This replaces the `expRho`-gated `expDiff_flow_isGeodesicVariation`/`hasFDerivAt_expMap`.
      Needs a strengthened confinement lemma (`…_uniform_C1`) carrying the quadratic remainder /
      `DV`-Lipschitz bound on the tube (derivable from smoothness+compactness of the spray).

* (K3) `Φ_w(0)=id` at `w=0` (constant geodesic) + a Grönwall comparison of the variational flows
    for `w` and `0` giving `‖Φ_w(1) − id‖ ≤ C_D‖w‖` uniformly over `q ∈ K`; then for
    `‖w‖ < min(ρ_K, 1/(2 C_D))`, `‖fderiv − id‖ < 1` ⟹ `IsUnit` (Neumann series).  Concludes
    (J)-for-F with hyps ONLY `hC` + `IsCompact K`.

Both K2/K3 are LOCAL to the (J) bridge; the a₁=R/6 recenter/pullback-metric chain consumes the
per-point openness-of-units nondegeneracy, NOT the compact-uniform (J) result (see
`UniformFlowTransfer.lean` firewall).
-/
import QIQTH.BoundedGeometryConfine
import QIQTH.UniformFlowBridge
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set

set_option maxHeartbeats 800000

variable {n : ℕ}

/-! ### K1a — the named uniform radius and constant -/

/-- **The uniform confinement radius `ρ_K > 0`** over the compact base set `K`, extracted from the
compact-uniform Picard–Lindelöf datum `geodesic_apriori_confinement_uniform`.  This is a GENUINE
uniform-over-`K` radius (no opaque per-`q` `expRho` selector). -/
noncomputable def uniformFlowRadius (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) : ℝ :=
  (geodesic_apriori_confinement_uniform g gi hC hK).choose

/-- **The uniform confinement constant `C₀ ≥ 0`** over `K`. -/
noncomputable def uniformFlowConst (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) : ℝ :=
  (geodesic_apriori_confinement_uniform g gi hC hK).choose_spec.2.choose

theorem uniformFlowRadius_pos (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    0 < uniformFlowRadius g gi hC hK :=
  (geodesic_apriori_confinement_uniform g gi hC hK).choose_spec.1

theorem uniformFlowConst_nonneg (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    0 ≤ uniformFlowConst g gi hC hK :=
  (geodesic_apriori_confinement_uniform g gi hC hK).choose_spec.2.choose_spec.1

/-- **Named-radius restatement of the compact-uniform confinement family.**  For every `q ∈ K` and
`‖v‖ ≤ ρ_K` there is a geodesic phase-tube `Y` through `(q, v)` on `(-2,2) ⊇ [0,1]`, `C₀‖v‖`-confined
near `(q, 0)` on `[0,1]`. -/
theorem uniformFlow_family (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ uniformFlowRadius g gi hC hK →
      ∃ Y : ℝ → Point n × Point n, Y 0 = (q, v) ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖Y t - ((q, 0) : Point n × Point n)‖ ≤ uniformFlowConst g gi hC hK * ‖v‖ :=
  (geodesic_apriori_confinement_uniform g gi hC hK).choose_spec.2.choose_spec.2

/-! ### K1b — the uniform tube and the uniform-flow endpoint map `uniformFlowExp` -/

/-- **Total Skolemization datum for the uniform tube.**  For every `(q, w)` there is a curve `Y`
which, WHEN `q ∈ K` and `‖w‖ ≤ ρ_K`, is the confined geodesic tube through `(q, w)`.  (Off that
domain it is the constant `(q, w)`, a harmless total default.) -/
theorem uniformFlow_tube_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q w : Point n) :
    ∃ Y : ℝ → Point n × Point n,
      (q ∈ K → ‖w‖ ≤ uniformFlowRadius g gi hC hK →
        Y 0 = (q, w) ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖Y t - ((q, 0) : Point n × Point n)‖ ≤ uniformFlowConst g gi hC hK * ‖w‖)) := by
  by_cases h : q ∈ K ∧ ‖w‖ ≤ uniformFlowRadius g gi hC hK
  · obtain ⟨Y, hY⟩ := uniformFlow_family g gi hC hK q h.1 w h.2
    exact ⟨Y, fun _ _ => hY⟩
  · exact ⟨fun _ => (q, w), fun hq hw => absurd ⟨hq, hw⟩ h⟩

/-- **The uniform confined geodesic tube through `(q, w)`** — the Skolemized curve of
`uniformFlow_tube_exists`.  A genuine `(-2,2)` integral curve of `geodesicField` from `(q, w)` when
`q ∈ K`, `‖w‖ ≤ ρ_K`. -/
noncomputable def uniformFlowTube (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q w : Point n) : ℝ → Point n × Point n :=
  (uniformFlow_tube_exists g gi hC hK q w).choose

/-- **The uniform-flow exp endpoint map** `uniformFlowExp g gi hC hK q : Point n → Point n`,
`w ↦ (uniformFlowTube … q w 1).1` — the position endpoint of the confined geodesic tube through
`(q, w)`.  This is the `F` re-architecture target carried "as the exp map" downstream (with the
GENUINE uniform radius `ρ_K`, no opaque `expRho`). -/
noncomputable def uniformFlowExp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) : Point n → Point n :=
  fun w => (uniformFlowTube g gi hC hK q w 1).1

@[simp] theorem uniformFlowExp_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q w : Point n) :
    uniformFlowExp g gi hC hK q w = (uniformFlowTube g gi hC hK q w 1).1 := rfl

/-! ### K1c — spec lemmas for the uniform tube (IC / ODE / confinement) -/

/-- **Bundled uniform-tube spec.**  For `q ∈ K` and `‖w‖ ≤ ρ_K`: the tube has initial condition
`(q, w)`, solves the geodesic ODE on `(-2,2)`, and is `C₀‖w‖`-confined near `(q, 0)` on `[0,1]`. -/
theorem uniformFlowTube_spec (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (w : Point n)
    (hw : ‖w‖ ≤ uniformFlowRadius g gi hC hK) :
    uniformFlowTube g gi hC hK q w 0 = (q, w) ∧
    (∀ t ∈ Set.Ioo (-2 : ℝ) 2,
      HasDerivAt (uniformFlowTube g gi hC hK q w)
        (geodesicField g gi (uniformFlowTube g gi hC hK q w t)) t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖uniformFlowTube g gi hC hK q w t - ((q, 0) : Point n × Point n)‖
        ≤ uniformFlowConst g gi hC hK * ‖w‖) :=
  (uniformFlow_tube_exists g gi hC hK q w).choose_spec hq hw

/-- Initial condition of the uniform tube. -/
theorem uniformFlowTube_spec_ic (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (w : Point n)
    (hw : ‖w‖ ≤ uniformFlowRadius g gi hC hK) :
    uniformFlowTube g gi hC hK q w 0 = (q, w) :=
  (uniformFlowTube_spec g gi hC hK q hq w hw).1

/-- Geodesic ODE of the uniform tube. -/
theorem uniformFlowTube_spec_ode (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (w : Point n)
    (hw : ‖w‖ ≤ uniformFlowRadius g gi hC hK) :
    ∀ t ∈ Set.Ioo (-2 : ℝ) 2,
      HasDerivAt (uniformFlowTube g gi hC hK q w)
        (geodesicField g gi (uniformFlowTube g gi hC hK q w t)) t :=
  (uniformFlowTube_spec g gi hC hK q hq w hw).2.1

/-- `C₀‖w‖`-confinement of the uniform tube on `[0,1]`. -/
theorem uniformFlowTube_spec_conf (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (w : Point n)
    (hw : ‖w‖ ≤ uniformFlowRadius g gi hC hK) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖uniformFlowTube g gi hC hK q w t - ((q, 0) : Point n × Point n)‖
        ≤ uniformFlowConst g gi hC hK * ‖w‖ :=
  (uniformFlowTube_spec g gi hC hK q hq w hw).2.2

/-! ### K1d — compatibility with `expMap` on the overlap (NOT on the (J)-for-F path)

This records that `uniformFlowExp` agrees with `expMap` on the OVERLAP ball.  It deliberately keeps
the `expRho` guard and is therefore NOT part of the `expRho`-free (J)-for-F target; it exists only
to certify that `uniformFlowExp` is the correct object (the flow endpoint that welds to `expMap`).
DERIVED via the existing ODE-uniqueness bridge `expMap_eq_flow_endpoint`. -/
theorem expMap_eq_uniformFlowExp_on_overlap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (w : Point n)
    (hw : ‖w‖ < min (expRho g gi hC q) (uniformFlowRadius g gi hC hK)) :
    expMap g gi hC q w = uniformFlowExp g gi hC hK q w := by
  have hwρK : ‖w‖ ≤ uniformFlowRadius g gi hC hK :=
    le_of_lt (lt_of_lt_of_le hw (min_le_right _ _))
  have hwρ : ‖w‖ ≤ expRho g gi hC q := le_of_lt (lt_of_lt_of_le hw (min_le_left _ _))
  have hic := uniformFlowTube_spec_ic g gi hC hK q hq w hwρK
  have hode := uniformFlowTube_spec_ode g gi hC hK q hq w hwρK
  have hconf := uniformFlowTube_spec_conf g gi hC hK q hq w hwρK
  exact expMap_eq_flow_endpoint g gi hC q w hwρ hic hode hconf

end QIQTH.ExpMap
