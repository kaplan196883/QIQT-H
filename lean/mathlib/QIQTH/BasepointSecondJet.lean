/-
  BasepointSecondJet — J4-26 (J-d assembly): honest firewalled reduction of the JOINT-continuity
  input `(J) hjoint` of `UniformSecondJetCompact`.

  ## Target

  `UniformSecondJetCompact.expMap_second_jet_bddOn_uniform_of_joint_cont` carries the single input

    (J)  `hjoint : ContinuousOn (fun p : Point n × Point n =>
              ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p.1) w) p.2‖) (K ×ˢ closedBall 0 r)`

  — JOINT continuity of the exp-map VELOCITY second-jet operator norm in `(base q, velocity v)` on the
  compact product `K × B̄(0,r)`.  It bundles TWO independent regularity facts:
    (a)  continuity in the velocity `v` at each fixed base `q`, and
    (b)  continuity in the base `q`, UNIFORMLY in `v` (a base-point modulus of the velocity 2-jet).

  ## What lands here (DERIVED; honest firewall; no `sorry`, no hyp = conclusion)

  * `joint_continuousOn_of_fiber_cont_of_uniform` — **(d2) the general joint-continuity assembly**, pure
    topology / real analysis, reusable: for `f : X → Y → ℝ` (`X` pseudometric, `Y` topological), if every
    fibre `y ↦ f x y` is continuous on `B` (`hfib`) and the base-family carries a UNIFORM-in-`y` modulus
    `∀ ε>0 ∃ δ>0, dist x x' < δ → ∀ y ∈ B, |f x y − f x' y| ≤ ε` (`hunif`), then `(x,y) ↦ f x y` is
    continuous on `K ×ˢ B`.  Standard `ε/2 + ε/2` triangle split, no compactness needed.

  * `expMap_second_jet_joint_cont_of_base_uniform` — **the reduction of `(J)`.**  DISCHARGES half (a)
    OUTRIGHT from the PROVEN unconditional `ContDiff⁴` tower (`ExpMapContDiffFour.expMap_contDiffOn_four`):
    `exp_q ∈ C⁴` on the open injectivity ball ⟹ `fderiv (fderiv exp_q)` is `ContDiffOn ℝ 2` there
    (two `ContDiffOn.fderiv_of_isOpen` steps) ⟹ continuous ⟹ (via `‖·‖` continuous, restricted to
    `closedBall 0 r ⊆ ball 0 (expRho q)` for `r < expRho q`) fibre-continuous.  The ONLY carried input is
    the base-point uniform modulus `(b) hunif` — a STRICTLY WEAKER, purely base-point (`q`-side) fact,
    IMPLIED by `hjoint` (on the compact product `hjoint` ⟹ uniform continuity ⟹ `hunif`).  So `(J)`'s
    velocity-continuity half is now closed against the C⁴ result; the remaining gap is only the base-point
    uniform modulus of the velocity 2-jet.

  * `expMap_common_nondeg_radius_of_base_uniform` — chains the reduction into
    `UniformSecondJetCompact.expMap_common_nondeg_radius_of_joint_cont`: the common exp-nondegeneracy
    radius over a compact `K` reduced to `(I1)`-radius (via `r < expRho q`) plus the base-point uniform
    modulus `hunif` — `hjoint` fully replaced.

  HONEST CHECKPOINT (binding).  This CLOSES `(J)`'s fibre (velocity-`v`) half against the proven C⁴
  regularity and reduces `(J)` to the SINGLE strictly-weaker base-point uniform-modulus input `hunif`.
  It does NOT discharge `hunif` — that is the base-point continuity of the velocity 2-jet, which the
  base-point smooth-dependence machinery (`BasepointFDeriv`/`BasepointSmoothDep`) proves only for an
  ABSTRACT confined tube family; welding it to the CONCRETE `expMap g gi hC q` runs through the opaque
  per-`q` `Classical.choose` tube `expTube` (the firewall noted in both `BasepointSmoothDep` and
  `UniformSecondJetCompact`).  It does NOT build the base-point 2nd-order jet (d1), NOT Raychaudhuri (L3),
  NOT `a₁ = R/6`.
-/
import QIQTH.BasepointFDeriv
import QIQTH.BasepointSmoothDep
import QIQTH.DecayOrderThree
import QIQTH.UniformSecondJetCompact
import QIQTH.ExpMapContDiffFour
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000

variable {n : ℕ}

/-- **(d2) general joint-continuity assembly (pure topology / real analysis, reusable).**  For a
    real-valued `f : X → Y → ℝ` with `X` pseudometric and `Y` topological, joint continuity on
    `K ×ˢ B` follows from
    * `hfib` : every fibre `y ↦ f x y` is continuous on `B` (for `x ∈ K`), and
    * `hunif` : a base modulus uniform in the fibre —
      `∀ ε>0 ∃ δ>0, ∀ x x' ∈ K, dist x x' < δ → ∀ y ∈ B, |f x y − f x' y| ≤ ε`.
    Standard `ε/2 + ε/2` triangle split at each `(x₀, y₀)`; no compactness required. -/
theorem joint_continuousOn_of_fiber_cont_of_uniform
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y]
    (f : X → Y → ℝ) {K : Set X} {B : Set Y}
    (hfib : ∀ x ∈ K, ContinuousOn (fun y => f x y) B)
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ x' ∈ K, dist x x' < δ →
        ∀ y ∈ B, |f x y - f x' y| ≤ ε) :
    ContinuousOn (fun p : X × Y => f p.1 p.2) (K ×ˢ B) := by
  rintro ⟨x0, y0⟩ ⟨hx0, hy0⟩
  refine Metric.tendsto_nhds.2 (fun ε hε => ?_)
  obtain ⟨δ, hδ0, hδ⟩ := hunif (ε / 2) (by positivity)
  -- fibre continuity at `x₀`: eventual `ε/2` bound in the fibre nbhd-within.
  have hfibev : ∀ᶠ y in 𝓝[B] y0, |f x0 y - f x0 y0| < ε / 2 := by
    have hc : ContinuousWithinAt (fun y => f x0 y) B y0 := hfib x0 hx0 y0 hy0
    have hcm := Metric.tendsto_nhds.1 hc (ε / 2) (by positivity)
    refine hcm.mono (fun y hy => ?_)
    rwa [Real.dist_eq] at hy
  -- `snd` pushes the product nbhd-within into the fibre nbhd-within.
  have hsnd : Filter.Tendsto (Prod.snd : X × Y → Y)
      (𝓝[K ×ˢ B] (x0, y0)) (𝓝[B] y0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(continuous_snd.tendsto (x0, y0)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with p hp using hp.2
  have hfst : Filter.Tendsto (Prod.fst : X × Y → X)
      (𝓝[K ×ˢ B] (x0, y0)) (𝓝 x0) :=
    (continuous_fst.tendsto (x0, y0)).mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ p in 𝓝[K ×ˢ B] (x0, y0), |f x0 p.2 - f x0 y0| < ε / 2 :=
    hsnd.eventually hfibev
  have h2 : ∀ᶠ p in 𝓝[K ×ˢ B] (x0, y0), dist p.1 x0 < δ :=
    Metric.tendsto_nhds.1 hfst δ hδ0
  have h3 : ∀ᶠ p in 𝓝[K ×ˢ B] (x0, y0), p ∈ K ×ˢ B := self_mem_nhdsWithin
  filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
  obtain ⟨hpK, hpB⟩ := hp3
  simp only [Real.dist_eq]
  have hbase : |f p.1 p.2 - f x0 p.2| ≤ ε / 2 := hδ p.1 hpK x0 hx0 hp2 p.2 hpB
  calc |f p.1 p.2 - f x0 y0|
      ≤ |f p.1 p.2 - f x0 p.2| + |f x0 p.2 - f x0 y0| := abs_sub_le _ _ _
    _ < ε := by linarith [hbase, hp1]

/-- **Reduction of `(J) hjoint`.**  The velocity second-jet operator norm
    `(q, v) ↦ ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v‖` is JOINTLY continuous on
    `K ×ˢ closedBall 0 r`, GIVEN only the base-point uniform modulus `hunif`.

    DERIVED: the fibre half (continuity in `v` at fixed `q`) is discharged OUTRIGHT from the proven
    unconditional `ContDiff⁴` tower — `exp_q ∈ C⁴` on `ball 0 (expRho q)` gives `fderiv (fderiv exp_q)`
    `ContDiffOn ℝ 2` there (two `ContDiffOn.fderiv_of_isOpen` steps), hence continuous, hence (composed
    with `‖·‖` and restricted to `closedBall 0 r ⊆ ball 0 (expRho q)` under `r < expRho q`) fibre
    continuous.  The compact-`K` joint continuity then follows from
    `joint_continuousOn_of_fiber_cont_of_uniform`.  The ONLY carried obligation is `hunif`, a strictly
    weaker base-point (`q`-side) uniform modulus, IMPLIED by (and therefore weaker than) `hjoint`. -/
theorem expMap_second_jet_joint_cont_of_base_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (r : ℝ)
    (hr_lt : ∀ q ∈ K, r < expRho g gi hC q)
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ q ∈ K, ∀ q' ∈ K, dist q q' < δ →
        ∀ v ∈ Metric.closedBall (0 : Point n) r,
          |‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v‖
            - ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q') w) v‖| ≤ ε) :
    ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p.1) w) p.2‖)
      (K ×ˢ Metric.closedBall (0 : Point n) r) := by
  have hfib : ∀ q ∈ K, ContinuousOn
      (fun v => ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v‖)
      (Metric.closedBall (0 : Point n) r) := by
    intro q hq
    have hsub : Metric.closedBall (0 : Point n) r ⊆ Metric.ball 0 (expRho g gi hC q) :=
      Metric.closedBall_subset_ball (hr_lt q hq)
    have h4 : ContDiffOn ℝ 4 (expMap g gi hC q)
        (Metric.ball (0 : Point n) (expRho g gi hC q)) := expMap_contDiffOn_four g gi hC q
    have h3 : ContDiffOn ℝ 3 (fderiv ℝ (expMap g gi hC q))
        (Metric.ball (0 : Point n) (expRho g gi hC q)) :=
      h4.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
    have h2 : ContDiffOn ℝ 2 (fderiv ℝ (fderiv ℝ (expMap g gi hC q)))
        (Metric.ball (0 : Point n) (expRho g gi hC q)) :=
      h3.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
    have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ (expMap g gi hC q)))
        (Metric.ball (0 : Point n) (expRho g gi hC q)) := h2.continuousOn
    exact (hcont.mono hsub).norm
  exact joint_continuousOn_of_fiber_cont_of_uniform
    (fun q v => ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v‖) hfib hunif

/-- **Common exp-nondegeneracy radius over `K`, reduced to `(I1)` ∧ the base-point uniform modulus.**
    Chaining `expMap_second_jet_joint_cont_of_base_uniform` into
    `UniformSecondJetCompact.expMap_common_nondeg_radius_of_joint_cont`: a single radius `ρ₀ > 0` with
    `IsUnit (fderiv ℝ (expMap g gi hC q) v)` for all `q ∈ K`, `‖v‖ < ρ₀`, conditional only on the
    uniform injectivity radius `r < expRho q` and the base-point uniform modulus `hunif`.  `hjoint` is
    fully replaced (its velocity-continuity half discharged against `ContDiff⁴`). -/
theorem expMap_common_nondeg_radius_of_base_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (r : ℝ) (hr : 0 < r)
    (hr_lt : ∀ q ∈ K, r < expRho g gi hC q)
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ q ∈ K, ∀ q' ∈ K, dist q q' < δ →
        ∀ v ∈ Metric.closedBall (0 : Point n) r,
          |‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v‖
            - ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q') w) v‖| ≤ ε) :
    ∃ ρ₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      IsUnit (fderiv ℝ (expMap g gi hC q) v) := by
  have hjoint := expMap_second_jet_joint_cont_of_base_uniform g gi hC r hr_lt hunif
  exact expMap_common_nondeg_radius_of_joint_cont g gi hC hK r hr
    (fun q hq => (hr_lt q hq).le) hjoint

end QIQTH.ExpMap
