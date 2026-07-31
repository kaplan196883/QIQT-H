/-
  Christoffel2Jet — J4-22 sub-brick (J-a): uniform sup-bound on the SECOND Fréchet derivative of the
  Christoffel symbols over a compact set.

  ## Context (the `(J)`-tower)

  `UniformSecondJetCompact.lean` (J4-21) reduced the uniform exp second-jet package to a single clean
  qualitative input `(J)`: JOINT continuity of the exp-map second-jet operator norm in `(base q,
  velocity v)` on a compact product `K ×ˢ B̄(0,r)`.  Its file-header investigation established that
  `(J)` is a GENUINE second-order joint-smooth-dependence-on-IC gap: the repo's smooth-dependence
  development (`GeodesicSmoothDep`) is first-order only, and Mathlib's Picard–Lindelöf flow is only
  Lipschitz-in-IC.  The exp map itself is welded to a per-`q` OPAQUE `Classical.choose` tube
  (`expTube`, `irreducible`), so there is currently NO handle on `q ↦ expMap g gi hC q v` regularity
  in the BASE point `q` — that base-point second-order smooth dependence is the true core of `(J)`.

  Any from-scratch route to `(J)` (route R-b of the J4-21 header: a uniform Grönwall on the SECOND
  variational equation) CONSUMES a uniform bound on the Christoffel 2-jet as the coefficient data of
  the second variational ODE.  This file lands exactly that coefficient bound — the faithful
  one-Fréchet-order-up MIRROR of `BoundedGeometry.christoffel_fderiv_bddOn_compact`.

  ## What lands (axiom-clean, no `sorry`)

  `christoffel_fderiv2_bddOn_compact` — a single `Kb ≥ 0` bounding
  `‖fderiv ℝ (fun z => fderiv ℝ (Γ^a_{bc}) z) y‖` uniformly over `y ∈ K` and all index triples.
  DERIVED purely from continuity + compactness: the nested second Fréchet derivative of each
  `ContDiff ℝ ⊤` Christoffel component is continuous (`ContDiff.fderiv_right` one order up, then
  `ContDiff.continuous_fderiv`), so the finite sum of its operator norms is continuous and attains a
  bound on the compact `K` (`IsCompact.exists_bound_of_continuousOn`).

  HONEST SCOPE: this is the COEFFICIENT-bound prerequisite (`J-a`) only.  It does NOT close `(J)`: the
  remaining core is the base-point second-order smooth dependence of the geodesic flow, absent from
  both Mathlib and the repo.  This file builds no variational equation, no base-point regularity, and
  makes no claim on `(J)` itself.
-/
import Mathlib
import QIQTH.BoundedGeometry

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset

variable {n : ℕ}

/-- **J4-22 (J-a) — uniform sup-bound on the SECOND derivatives of the Christoffel symbols over a
    compact set.**  The faithful one-Fréchet-order-up mirror of `christoffel_fderiv_bddOn_compact`.
    Each component `christoffel g gi a b c` is `ContDiff ℝ ⊤` (carried `hC`); hence
    `fun z => fderiv ℝ (Γ^a_{bc}) z` is `ContDiff ℝ ⊤` (`ContDiff.fderiv_right`), so its own Fréchet
    derivative — the nested second jet `fderiv ℝ (fun z => fderiv ℝ (Γ^a_{bc}) z)` — is CONTINUOUS
    (`ContDiff.continuous_fderiv`).  The finite sum of the operator norms is therefore continuous and
    attains a bound `C` on the compact `K` (`IsCompact.exists_bound_of_continuousOn`); each individual
    nested-second-jet norm is a single nonnegative summand `≤` the sum `≤ C ≤ max C 0`, uniformly over
    all `y ∈ K` and all index triples `(a,b,c)`.

    This is the uniform Christoffel-2-jet COEFFICIENT bound a from-scratch uniform Grönwall on the
    second geodesic variational equation would consume; it does NOT by itself close the joint
    second-jet continuity input `(J)` (whose core is base-point smooth dependence of the flow). -/
theorem christoffel_fderiv2_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ y ∈ K, ∀ a b c,
      ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b c w) z) y‖ ≤ Kb := by
  have hFcont : Continuous
      (fun y => ∑ a, ∑ b, ∑ c,
        ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b c w) z) y‖) := by
    refine continuous_finsetSum _ (fun a _ => ?_)
    refine continuous_finsetSum _ (fun b _ => ?_)
    refine continuous_finsetSum _ (fun c _ => ?_)
    exact (((hC a b c).fderiv_right (m := ⊤) le_top).continuous_fderiv (by simp)).norm
  obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn hFcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y hy a b c => ?_⟩
  have hle : ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b c w) z) y‖
      ≤ ∑ a, ∑ b, ∑ c,
          ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b c w) z) y‖ := by
    calc ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b c w) z) y‖
        ≤ ∑ c', ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b c' w) z) y‖ :=
          Finset.single_le_sum
            (f := fun c' => ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b c' w) z) y‖)
            (fun _ _ => by positivity) (mem_univ c)
      _ ≤ ∑ b', ∑ c', ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b' c' w) z) y‖ :=
          Finset.single_le_sum
            (f := fun b' =>
              ∑ c', ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b' c' w) z) y‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (mem_univ b)
      _ ≤ ∑ a', ∑ b', ∑ c',
            ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a' b' c' w) z) y‖ :=
          Finset.single_le_sum
            (f := fun a' =>
              ∑ b', ∑ c', ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a' b' c' w) z) y‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
            (mem_univ a)
  calc ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b c w) z) y‖
      ≤ ∑ a, ∑ b, ∑ c,
          ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b c w) z) y‖ := hle
    _ ≤ ‖∑ a, ∑ b, ∑ c,
          ‖fderiv ℝ (fun z => fderiv ℝ (fun w => christoffel g gi a b c w) z) y‖‖ := by
        rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ C := hCb y hy
    _ ≤ max C 0 := le_max_left _ _

end QIQTH.ExpMap
