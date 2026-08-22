/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.

# J4-NEXT: `uniformFlowExp` K-independence congruence (ODE-uniqueness bridge)

`uniformFlowExp g gi hC hK q`/`uniformFlowTube g gi hC hK q` (`UniformFlowNondeg.lean`) are built
from `geodesic_apriori_confinement_uniform g gi hC hK`, a `Classical.choose` datum that GENUINELY
depends on the ambient compact set `K`.  Consequently, for two different compact sets `K`, `K'`
both containing a point `z`, `uniformFlowExp g gi hC hK z` and `uniformFlowExp g gi hC hK' z` are
NOT definitionally/`rfl`-equal — they are Skolemized from independent choices.

This file supplies the missing CONGRUENCE: on the shared valid-radius ball (`‖w‖ ≤ min ρ_K ρ_K'`),
the two flows agree POINTWISE, by genuine ODE uniqueness — mirroring the EXACT proof shape of the
already-banked `expMap_eq_flow_endpoint` (`UniformFlowBridge.lean`), but generalized to compare
TWO ARBITRARY confined integral curves of `geodesicField` sharing an initial condition (no
reference to `expMap`/`expTube` at all).

## What lands here

* `geodesicField_confined_curves_agree` — the generic two-curve ODE-uniqueness lemma: any two
  integral curves of `geodesicField` through the same `(q, v)`, each `Cᵢ‖v‖`-confined near `(q,0)`
  on `[0,1]`, agree on `[0,1]` (`Set.EqOn`).  DERIVED via `ODE_solution_unique_of_mem_Icc_right`
  on the compact convex ball `closedBall (q,0) (max (C₁‖v‖) (C₂‖v‖))` (Lipschitz there by
  `ContDiff.contDiffOn.exists_lipschitzOnWith`).  No uniqueness hypothesis is assumed — it is
  proved, exactly as in `expMap_eq_flow_endpoint`.
* `uniformFlowTube_K_indep` — instantiates the generic lemma twice (once against `hK`'s spec, once
  against `hK'`'s spec) to show `uniformFlowTube g gi hC hK z w` and `uniformFlowTube g gi hC hK' z w`
  agree on `[0,1]`, for `z ∈ K ∩ K'` and `‖w‖ ≤ min ρ_K ρ_K'`.
* `uniformFlowExp_K_indep` — the position-endpoint (`t = 1`) corollary:
    `uniformFlowExp g gi hC hK z w = uniformFlowExp g gi hC hK' z w`.
  This is the K-independence congruence recommended by cp988's diagnostic (the fix for the
  `uniformFlowExp g gi hC hK z` vs `uniformFlowExp g gi hC hK' z` mismatch blocking `hxmem`'s
  chart-coverage argument): it lets a `uniformFlowExp` value built from ANY compact set containing
  `z` be freely rewritten to the value built from any OTHER compact set containing `z`, PROVIDED
  `w` lies in the (radius-min) overlap ball — genuine ODE uniqueness, not `rfl`.

## Honest scope note

This is the K-INDEPENDENCE piece only.  It does NOT by itself resolve `hxmem`'s chart-coverage
fixed-point obstruction (cp988): that obstruction is that the coverage RADIUS `r(K)` used to pick a
shrunk ball `K := closedBall x ρ` is itself a function of `K` (via `uniformFlowRadius g gi hC hK`),
so "fix an ambient `K₀`, derive constants once, then shrink only the quantifier ball" requires a
comparison `uniformFlowRadius g gi hC hK₀ ≤ uniformFlowRadius g gi hC hKρ` (or a common lower bound)
that this file does NOT supply — K-independence identifies the flow VALUES on the overlap, it says
nothing about how the RADII `ρ_K`/`ρ_{K'}` compare across different `K`.  Per gpt-5.6-sol
(reasoning high) consult, this congruence is exactly the right piece to bank and stop at; the
radius-monotonicity/common-lower-bound question is separate, additional content.

a₁=R/6 remains STRICTLY CONDITIONAL on {hDuhamel, hDConv, hCConv}, UNCHANGED. NOT a₁=R/6.
-/
import QIQTH.UniformFlowNondeg
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- **Generic two-curve ODE-uniqueness lemma.**  If `Y₁` and `Y₂` are BOTH integral curves of
`geodesicField` through the SAME initial condition `(q, v)` on `(-2, 2)`, each staying
`Cᵢ‖v‖`-confined near `(q, 0)` on `[0,1]` (for possibly DIFFERENT constants `C₁ ≠ C₂`), then they
agree on `[0,1]`.  Pure ODE uniqueness (`ODE_solution_unique_of_mem_Icc_right`); no reference to
`expMap`/`expTube`.  Same proof shape as `expMap_eq_flow_endpoint` (`UniformFlowBridge.lean`). -/
theorem geodesicField_confined_curves_agree
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q v : Point n)
    {C₁ C₂ : ℝ} {Y₁ Y₂ : ℝ → Point n × Point n}
    (hY1_0 : Y₁ 0 = (q, v))
    (hY1deriv : ∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y₁ (geodesicField g gi (Y₁ t)) t)
    (hY1conf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Y₁ t - ((q, 0) : Point n × Point n)‖ ≤ C₁ * ‖v‖)
    (hY2_0 : Y₂ 0 = (q, v))
    (hY2deriv : ∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y₂ (geodesicField g gi (Y₂ t)) t)
    (hY2conf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Y₂ t - ((q, 0) : Point n × Point n)‖ ≤ C₂ * ‖v‖) :
    Set.EqOn Y₁ Y₂ (Set.Icc (0 : ℝ) 1) := by
  set e : Point n × Point n := (q, 0) with he
  set R : ℝ := max (C₁ * ‖v‖) (C₂ * ‖v‖) with hR
  set S : Set (Point n × Point n) := Metric.closedBall e R with hS
  have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := by
    intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIco_sub : Set.Ico (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := by
    intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨Kq, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) (by rw [hS]; exact convex_closedBall e R)
      (by rw [hS]; exact isCompact_closedBall e R)
  have hcont1 : ContinuousOn Y₁ (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hY1deriv t (hIcc_sub ht)).continuousAt.continuousWithinAt
  have hcont2 : ContinuousOn Y₂ (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hY2deriv t (hIcc_sub ht)).continuousAt.continuousWithinAt
  have hmem1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₁ t ∈ S := by
    intro t ht
    rw [hS, Metric.mem_closedBall, dist_eq_norm]
    exact le_trans (hY1conf t ht) (le_max_left _ _)
  have hmem2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₂ t ∈ S := by
    intro t ht
    rw [hS, Metric.mem_closedBall, dist_eq_norm]
    exact le_trans (hY2conf t ht) (le_max_right _ _)
  have ha : Y₁ 0 = Y₂ 0 := by rw [hY1_0, hY2_0]
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => geodesicField g gi)
      (s := fun _ => S) (K := Kq)
      (fun t _ => hLip) hcont1
      (fun t ht => (hY1deriv t (hIco_sub ht)).hasDerivWithinAt)
      (fun t ht => hmem1 t (Set.Ico_subset_Icc_self ht))
      hcont2
      (fun t ht => (hY2deriv t (hIco_sub ht)).hasDerivWithinAt)
      (fun t ht => hmem2 t (Set.Ico_subset_Icc_self ht))
      ha

/-- **The `uniformFlowTube` K-independence congruence.**  For a point `z` in TWO compact sets `K`,
`K'` and `w` in the OVERLAP radius ball (`‖w‖ ≤ min ρ_K ρ_K'`), the two confined tubes built from
`hK` and `hK'` agree on `[0,1]`.  DERIVED via `geodesicField_confined_curves_agree` applied to the
already-banked `uniformFlowTube_spec_ic/ode/conf` (`UniformFlowNondeg.lean`) for both `hK` and
`hK'` — genuine ODE uniqueness, NOT `rfl` (the two tubes are Skolemized from independent
`Classical.choose` data). -/
theorem uniformFlowTube_K_indep
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K K' : Set (Point n)} (hK : IsCompact K) (hK' : IsCompact K')
    (z : Point n) (hz : z ∈ K) (hz' : z ∈ K') (w : Point n)
    (hw : ‖w‖ ≤ min (uniformFlowRadius g gi hC hK) (uniformFlowRadius g gi hC hK')) :
    Set.EqOn (uniformFlowTube g gi hC hK z w) (uniformFlowTube g gi hC hK' z w)
      (Set.Icc (0 : ℝ) 1) := by
  have hw1 : ‖w‖ ≤ uniformFlowRadius g gi hC hK := le_trans hw (min_le_left _ _)
  have hw2 : ‖w‖ ≤ uniformFlowRadius g gi hC hK' := le_trans hw (min_le_right _ _)
  obtain ⟨hic1, hode1, hconf1⟩ := uniformFlowTube_spec g gi hC hK z hz w hw1
  obtain ⟨hic2, hode2, hconf2⟩ := uniformFlowTube_spec g gi hC hK' z hz' w hw2
  exact geodesicField_confined_curves_agree g gi hC z w hic1 hode1 hconf1 hic2 hode2 hconf2

/-- **The `uniformFlowExp` K-independence congruence.**  For a point `z` in TWO compact sets `K`,
`K'` and `w` in the overlap radius ball, the position-endpoint (`uniformFlowExp`) values built from
`hK` and `hK'` agree.  The value at `w` can be freely transported between ANY two compact sets
containing `z`, provided `w` lies in the (radius-min) overlap ball. -/
theorem uniformFlowExp_K_indep
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K K' : Set (Point n)} (hK : IsCompact K) (hK' : IsCompact K')
    (z : Point n) (hz : z ∈ K) (hz' : z ∈ K') (w : Point n)
    (hw : ‖w‖ ≤ min (uniformFlowRadius g gi hC hK) (uniformFlowRadius g gi hC hK')) :
    uniformFlowExp g gi hC hK z w = uniformFlowExp g gi hC hK' z w := by
  have h1 : uniformFlowTube g gi hC hK z w 1 = uniformFlowTube g gi hC hK' z w 1 :=
    uniformFlowTube_K_indep g gi hC hK hK' z hz hz' w hw (Set.right_mem_Icc.mpr (by norm_num))
  show (uniformFlowTube g gi hC hK z w 1).1 = (uniformFlowTube g gi hC hK' z w 1).1
  rw [h1]

end QIQTH.ExpMap
