/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.

# J4-20: ODE-uniqueness bridge — `expMap`'s opaque tube = uniform-confinement flow

`expMap g gi hC q v = (expTube g gi hC q v 1).1` is welded to a per-`q` OPAQUE
`Classical.choose` selector (`expTube`, `irreducible`), carrying only a per-`q` confinement
radius `expRho g gi hC q` and constant `expConst g gi hC q`, with NO uniform-over-`K`
provenance.  Meanwhile `geodesic_apriori_confinement_uniform` supplies, for a compact base
set `K`, a SINGLE radius `ρ` and constant `C₀` valid for every `q ∈ K` together with a
uniform-confinement geodesic flow `Y` through `(q, v)`.

Both `expTube g gi hC q v` and the uniform flow `Y` are integral curves of
`geodesicField g gi` on `(-2, 2) ⊇ [0,1]` with the same initial condition `(q, v)` at
`t = 0`.  Grönwall/Picard–Lindelöf uniqueness (`ODE_solution_unique_of_mem_Icc_right`,
initial time = left endpoint `0`) forces them to COINCIDE on `[0,1]`.  Evaluating the
position component at `t = 1` yields

  `expMap g gi hC q v = (Y 1).1`   (the uniform-flow position endpoint).

This is the transfer mechanism: uniform-over-`q` properties of the uniform flow move onto
`expMap` on the overlap ball `‖v‖ ≤ min (expRho g gi hC q) ρ`.  The `fderiv` corollary
promotes the pointwise identity (which holds on the OPEN overlap ball) to an
`EventuallyEq`, hence to equality of Jacobians via `Filter.EventuallyEq.fderiv_eq`.

HONEST: the endpoint equality is DERIVED from genuine ODE uniqueness
(`ODE_solution_unique_of_mem_Icc_right`); no uniqueness step is carried as a hypothesis.
-/
import QIQTH.BoundedGeometryConfine
import QIQTH.ExpMap
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal
open Set

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- **ODE-uniqueness endpoint bridge (core).**  If `Y` is ANY integral curve of the geodesic
field through `(q, v)` on `(-2, 2)` that stays `C₀‖v‖`-confined near `(q, 0)` on `[0,1]`, then
its position endpoint at `t = 1` equals `expMap g gi hC q v`.  Proof: `expTube g gi hC q v`
(for `‖v‖ ≤ expRho`) and `Y` both solve `x' = geodesicField x` on `[0,1]` with the same
initial value `(q, v)` at `t = 0` and both stay inside the compact ball `closedBall (q,0) R`
(`R = max (expConst‖v‖) (C₀‖v‖)`), on which `geodesicField` is Lipschitz; hence they coincide
on `[0,1]` by `ODE_solution_unique_of_mem_Icc_right`.  DERIVED — no uniqueness hypothesis. -/
theorem expMap_eq_flow_endpoint
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q v : Point n) (hvρ : ‖v‖ ≤ expRho g gi hC q)
    {C₀ : ℝ} {Y : ℝ → Point n × Point n}
    (hY0 : Y 0 = (q, v))
    (hYderiv : ∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t)
    (hYconf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Y t - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖) :
    expMap g gi hC q v = (Y 1).1 := by
  obtain ⟨hf0, hfderiv, hfconf⟩ := expTube_spec g gi hC q v hvρ
  -- The compact confinement ball containing BOTH trajectories on `[0,1]`.
  set e : Point n × Point n := (q, 0) with he
  set R : ℝ := max (expConst g gi hC q * ‖v‖) (C₀ * ‖v‖) with hR
  set S : Set (Point n × Point n) := Metric.closedBall e R with hS
  -- Interval inclusions.
  have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := by
    intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIco_sub : Set.Ico (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := by
    intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- `geodesicField` is Lipschitz on the compact convex ball `S`.
  obtain ⟨Kq, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) (by rw [hS]; exact convex_closedBall e R)
      (by rw [hS]; exact isCompact_closedBall e R)
  -- Continuity on `[0,1]` from the derivatives on `(-2,2)`.
  have hcont_f : ContinuousOn (expTube g gi hC q v) (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hfderiv t (hIcc_sub ht)).continuousAt.continuousWithinAt
  have hcont_g : ContinuousOn Y (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hYderiv t (hIcc_sub ht)).continuousAt.continuousWithinAt
  -- Membership in `S` on `[0,1]` from the two confinements.
  have hmem_f : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC q v t ∈ S := by
    intro t ht
    rw [hS, Metric.mem_closedBall, dist_eq_norm]
    exact le_trans (hfconf t ht) (le_max_left _ _)
  have hmem_g : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y t ∈ S := by
    intro t ht
    rw [hS, Metric.mem_closedBall, dist_eq_norm]
    exact le_trans (hYconf t ht) (le_max_right _ _)
  -- Same initial value at `t = 0`.
  have ha : expTube g gi hC q v 0 = Y 0 := by rw [hf0, hY0]
  -- Grönwall uniqueness on `[0,1]` (initial time = left endpoint `0`).
  have hEqOn : Set.EqOn (expTube g gi hC q v) Y (Set.Icc (0 : ℝ) 1) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ => geodesicField g gi)
      (s := fun _ => S) (K := Kq)
      (fun t _ => hLip) hcont_f
      (fun t ht => (hfderiv t (hIco_sub ht)).hasDerivWithinAt)
      (fun t ht => hmem_f t (Set.Ico_subset_Icc_self ht))
      hcont_g
      (fun t ht => (hYderiv t (hIco_sub ht)).hasDerivWithinAt)
      (fun t ht => hmem_g t (Set.Ico_subset_Icc_self ht))
      ha
  -- Evaluate the position component at `t = 1`.
  have h1 : expTube g gi hC q v 1 = Y 1 := hEqOn (Set.right_mem_Icc.mpr (by norm_num))
  show (expTube g gi hC q v 1).1 = (Y 1).1
  rw [h1]

/-- **Uniform-flow endpoint bridge over a compact base set.**  For a compact base set `K`
there is a SINGLE radius `ρ > 0` such that for every `q ∈ K` and every velocity `v` with
`‖v‖ ≤ min (expRho g gi hC q) ρ`, `expMap g gi hC q v` equals the position endpoint of the
uniform-confinement geodesic flow `Y` through `(q, v)` (from
`geodesic_apriori_confinement_uniform`).  DERIVED via `expMap_eq_flow_endpoint`. -/
theorem expMap_eq_uniform_flow_on_overlap
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n,
        ‖v‖ ≤ min (expRho g gi hC q) ρ →
      ∃ Y : ℝ → Point n × Point n,
        Y 0 = (q, v) ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t) ∧
        expMap g gi hC q v = (Y 1).1 := by
  obtain ⟨ρ, hρ, C₀, hC₀, hfam⟩ := geodesic_apriori_confinement_uniform g gi hC hK
  refine ⟨ρ, hρ, ?_⟩
  intro q hq v hv
  have hvρ : ‖v‖ ≤ expRho g gi hC q := le_trans hv (min_le_left _ _)
  have hvr : ‖v‖ ≤ ρ := le_trans hv (min_le_right _ _)
  obtain ⟨Y, hY0, hYderiv, hYconf⟩ := hfam q hq v hvr
  exact ⟨Y, hY0, hYderiv, expMap_eq_flow_endpoint g gi hC q v hvρ hY0 hYderiv hYconf⟩

/-- **Jacobian transfer on the overlap.**  For a compact base set `K` there is a single
radius `ρ > 0` such that at every `q ∈ K` the uniform-confinement flow endpoint
`F w = (Yfun w 1).1` agrees with `expMap g gi hC q` on the OPEN overlap ball
`‖w‖ < min (expRho g gi hC q) ρ`, and consequently their Fréchet derivatives coincide there:

  `fderiv ℝ (expMap g gi hC q) v = fderiv ℝ F v`   for `‖v‖ < min (expRho g gi hC q) ρ`.

`F` is exposed together with its uniform-flow spec (each `Yfun w`, for `‖w‖ ≤ ρ`, is a
genuine `(-2,2)` integral curve of `geodesicField` through `(q, w)` confined by `C₀‖w‖`), so
uniform-over-`K` Jacobian bounds of the flow endpoint transfer onto `expMap`'s Jacobian on
the overlap.  The pointwise identity is DERIVED via `expMap_eq_flow_endpoint`; the
`fderiv` step is `Filter.EventuallyEq.fderiv_eq` on the open overlap ball. -/
theorem fderiv_expMap_eq_uniform_flow_on_overlap
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
          fderiv ℝ (expMap g gi hC q) v = fderiv ℝ F v) := by
  obtain ⟨ρ, hρ, C₀, hC₀, hfam⟩ := geodesic_apriori_confinement_uniform g gi hC hK
  refine ⟨ρ, hρ, C₀, hC₀, ?_⟩
  intro q hq
  -- Skolemize the per-`w` uniform-flow existential into a function `Yfun` of `w`.
  have hchoose : ∀ w : Point n, ∃ Y : ℝ → Point n × Point n, ‖w‖ ≤ ρ →
      Y 0 = (q, w) ∧
      (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖Y t - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖) := by
    intro w
    by_cases hw : ‖w‖ ≤ ρ
    · obtain ⟨Y, hY⟩ := hfam q hq w hw; exact ⟨Y, fun _ => hY⟩
    · exact ⟨fun _ => 0, fun h => absurd h hw⟩
  choose Yfun hYfun using hchoose
  set F : Point n → Point n := fun w => (Yfun w 1).1 with hFdef
  -- (1) `F` is the uniform-flow endpoint, with its spec exposed.
  have hspec : ∀ w : Point n, ‖w‖ ≤ ρ →
      ∃ Y : ℝ → Point n × Point n,
        Y 0 = (q, w) ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖Y t - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖) ∧
        F w = (Y 1).1 := by
    intro w hw
    obtain ⟨hY0, hYd, hYc⟩ := hYfun w hw
    exact ⟨Yfun w, hY0, hYd, hYc, rfl⟩
  -- (2) `expMap = F` on the open overlap ball (ODE-uniqueness endpoint bridge).
  have hEq : ∀ w : Point n, ‖w‖ < min (expRho g gi hC q) ρ →
      expMap g gi hC q w = F w := by
    intro w hw
    have hwρ : ‖w‖ ≤ expRho g gi hC q := le_of_lt (lt_of_lt_of_le hw (min_le_left _ _))
    have hwr : ‖w‖ ≤ ρ := le_of_lt (lt_of_lt_of_le hw (min_le_right _ _))
    obtain ⟨hY0, hYd, hYc⟩ := hYfun w hwr
    exact expMap_eq_flow_endpoint g gi hC q w hwρ hY0 hYd hYc
  refine ⟨F, hspec, hEq, ?_⟩
  -- (3) Jacobians coincide on the open overlap ball, via `EventuallyEq.fderiv_eq`.
  intro v hv
  set c : ℝ := min (expRho g gi hC q) ρ with hc
  -- The open overlap ball `{w | ‖w‖ < c}` is a neighbourhood of `v`.
  have hball_eq : {w : Point n | ‖w‖ < c} = Metric.ball (0 : Point n) c := by
    ext w; simp [Metric.mem_ball, dist_eq_norm]
  have hopen : IsOpen {w : Point n | ‖w‖ < c} := by
    rw [hball_eq]; exact Metric.isOpen_ball
  have hvmem : v ∈ {w : Point n | ‖w‖ < c} := hv
  have hmem_nhds : {w : Point n | ‖w‖ < c} ∈ nhds v := hopen.mem_nhds hvmem
  have hEqOn : Set.EqOn (expMap g gi hC q) F {w : Point n | ‖w‖ < c} := fun w hw => hEq w hw
  have hEv : (expMap g gi hC q) =ᶠ[nhds v] F :=
    Filter.eventuallyEq_of_mem hmem_nhds hEqOn
  exact hEv.fderiv_eq

end QIQTH.ExpMap
