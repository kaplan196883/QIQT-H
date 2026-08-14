/-
  ImageAnnulusFrontier — J4-735 (A): THE ELEMENTARY IMAGE-ANNULUS DECOMPOSITION.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` (`R/6` stays a labelled carrier, untouched).
  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── PURPOSE (the missing elementary lemma of J4-734).
    The `hflowTruncNear` clause (iii) at the concrete gate is a frontier→sphere-image containment
    `frontier (φ_w '' ball 0 c) ⊆ φ_w '' sphere 0 c`.  The elementary set-theoretic core of that leg
    — `f '' closedBall \ f '' ball ⊆ f '' sphere` — was absent from `QIQTH/`.  This file supplies it.

    ★ NO injectivity is needed for THIS direction (contrary to a first guess): if `y = f z` with
    `z ∈ closedBall` and `y ∉ f '' ball`, then `z ∉ ball` (else `f z ∈ f '' ball`), so
    `z ∈ closedBall \ ball = sphere`, whence `y ∈ f '' sphere`.  Injectivity would only be needed for the
    reverse inclusion, which is not what the frontier leg consumes.

  ── WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited).
    * `closedBall_diff_ball_eq_sphere` — the metric annulus identity `closedBall c r \ ball c r = sphere c r`.
    * `image_closedBall_diff_image_ball_subset_image_sphere` — ★ the image-annulus containment.
    * `frontier_image_ball_subset_image_sphere` — ★ the frontier→sphere-image corollary used by clause (iii),
      given the two honest geometric facts `closure (f '' ball) ⊆ f '' closedBall` (continuity/compactness)
      and `f '' ball ⊆ interior (f '' ball)` i.e. `IsOpen (f '' ball)` (open-mapping).  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib

open Set Metric

namespace QIQTH.ImageAnnulusFrontier

variable {α : Type*} {β : Type*} [PseudoMetricSpace α]

/-- **The metric annulus identity.**  In any pseudometric space, the closed ball minus the open ball of
the same centre/radius is exactly the sphere. -/
theorem closedBall_diff_ball_eq_sphere (c : α) (r : ℝ) :
    Metric.closedBall c r \ Metric.ball c r = Metric.sphere c r := by
  ext z
  simp only [Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere, not_lt]
  constructor
  · rintro ⟨hle, hge⟩; exact le_antisymm hle hge
  · rintro heq; exact ⟨le_of_eq heq, ge_of_eq heq⟩

/-- **★ The image-annulus containment (no injectivity needed).**  For ANY map `f : α → β`, the image of
the closed ball minus the image of the open ball is contained in the image of the sphere:
`f '' closedBall c r \ f '' ball c r ⊆ f '' sphere c r`.

Proof: `y = f z` with `z ∈ closedBall`, `y ∉ f '' ball`; then `z ∉ ball` (else `f z ∈ f '' ball`), so
`z ∈ closedBall \ ball = sphere`, whence `y ∈ f '' sphere`. -/
theorem image_closedBall_diff_image_ball_subset_image_sphere (f : α → β) (c : α) (r : ℝ) :
    f '' Metric.closedBall c r \ f '' Metric.ball c r ⊆ f '' Metric.sphere c r := by
  rintro y ⟨⟨z, hzcb, rfl⟩, hynb⟩
  have hznb : z ∉ Metric.ball c r := fun hz => hynb ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  rw [← closedBall_diff_ball_eq_sphere]
  exact ⟨hzcb, hznb⟩

/-- **★ The frontier→sphere-image corollary (the clause (iii) leg).**  If `f '' ball c r` is open
(`hopen`) and its closure sits inside the image of the closed ball (`hclos`, a continuity/compactness
fact), then the frontier of `f '' ball c r` is contained in `f '' sphere c r`.

This is exactly the shape `hflowTruncNear` clause (iii) needs at the concrete gate: `frontier (S w)` with
`S w = f '' ball 0 c` lands in `f '' sphere 0 c`, i.e. every boundary point is the flow-image of a
sphere-radius velocity. -/
theorem frontier_image_ball_subset_image_sphere (f : α → β) (c : α) (r : ℝ)
    [TopologicalSpace β]
    (hopen : IsOpen (f '' Metric.ball c r))
    (hclos : closure (f '' Metric.ball c r) ⊆ f '' Metric.closedBall c r) :
    frontier (f '' Metric.ball c r) ⊆ f '' Metric.sphere c r := by
  intro y hy
  have hy' : y ∈ closure (f '' Metric.ball c r) \ (f '' Metric.ball c r) := by
    rw [frontier_eq_closure_inter_closure] at hy
    refine ⟨hy.1, ?_⟩
    have : y ∈ closure ((f '' Metric.ball c r)ᶜ) := hy.2
    rwa [hopen.isClosed_compl.closure_eq, Set.mem_compl_iff] at this
  exact image_closedBall_diff_image_ball_subset_image_sphere f c r ⟨hclos hy'.1, hy'.2⟩

end QIQTH.ImageAnnulusFrontier

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ImageAnnulusFrontier
#check @closedBall_diff_ball_eq_sphere
#check @image_closedBall_diff_image_ball_subset_image_sphere
#check @frontier_image_ball_subset_image_sphere
#print axioms closedBall_diff_ball_eq_sphere
#print axioms image_closedBall_diff_image_ball_subset_image_sphere
#print axioms frontier_image_ball_subset_image_sphere
end AxiomChecks
