/-
  BoundedGeometry — uniform sup-bounds on the ambient geometric data over a COMPACT set.

  Part A of J4-16 (the reachable prerequisite of the bounded-geometry bottleneck, Brick A of the
  two-point phase).  The Christoffel symbols `christoffel g gi a b c`, the geodesic field
  `geodesicField g gi`, and their first derivatives are `ContDiff ℝ ⊤` whenever the carried `hC`
  holds, hence CONTINUOUS, hence BOUNDED on any compact set (a continuous real/normed-valued
  function attains a bound on a compact set: `IsCompact.exists_bound_of_continuousOn`).

  These are the clean `∃ bound, ∀ y ∈ K, …` uniform-over-compact lemmas, DERIVED purely from
  continuity + compactness.  They feed the uniform-confinement sub-brick (A2) — a uniform-in-`q`
  Grönwall estimate needs a christoffel bound and a geodesic-field derivative (Lipschitz) bound on a
  fixed compact thickening — and the uniform residual-constant of Brick B.

  HONEST: these are boundedness facts only.  They do NOT by themselves make
  `geodesic_apriori_confinement`'s radius/constant uniform over a compact base set (that confinement
  is routed through Mathlib's point-local Picard–Lindelöf constructors, whose radii are opaque — see
  the J4-16 Part-B scope); the uniform confinement is a re-derivation that CONSUMES these bounds.
-/
import Mathlib
import QIQTH.Geodesic

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset

variable {n : ℕ}

/-- **Uniform sup-bound on the Christoffel symbols over a compact set.**  Each component
    `christoffel g gi a b c` is `ContDiff ℝ ⊤` (carried `hC`), hence continuous; the finite sum of
    absolute values `∑_{a,b,c} |Γ^a_{bc}|` is therefore continuous and attains a bound `C` on the
    compact `K` (`IsCompact.exists_bound_of_continuousOn`).  Each individual `|Γ^a_{bc} y|` is a
    single nonnegative summand, hence `≤` the sum `≤ C ≤ max C 0`.  The bound is uniform over all
    `y ∈ K` and all index triples `(a,b,c)`. -/
theorem christoffel_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ y ∈ K, ∀ a b c, |christoffel g gi a b c y| ≤ Kb := by
  have hFcont : Continuous (fun y => ∑ a, ∑ b, ∑ c, |christoffel g gi a b c y|) := by
    refine continuous_finsetSum _ (fun a _ => ?_)
    refine continuous_finsetSum _ (fun b _ => ?_)
    refine continuous_finsetSum _ (fun c _ => ?_)
    exact ((hC a b c).continuous).abs
  obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn hFcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y hy a b c => ?_⟩
  have hle : |christoffel g gi a b c y| ≤ ∑ a, ∑ b, ∑ c, |christoffel g gi a b c y| := by
    calc |christoffel g gi a b c y|
        ≤ ∑ c', |christoffel g gi a b c' y| :=
          Finset.single_le_sum (f := fun c' => |christoffel g gi a b c' y|)
            (fun i _ => abs_nonneg _) (mem_univ c)
      _ ≤ ∑ b', ∑ c', |christoffel g gi a b' c' y| :=
          Finset.single_le_sum (f := fun b' => ∑ c', |christoffel g gi a b' c' y|)
            (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (mem_univ b)
      _ ≤ ∑ a', ∑ b', ∑ c', |christoffel g gi a' b' c' y| :=
          Finset.single_le_sum (f := fun a' => ∑ b', ∑ c', |christoffel g gi a' b' c' y|)
            (fun i _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (mem_univ a)
  calc |christoffel g gi a b c y|
      ≤ ∑ a, ∑ b, ∑ c, |christoffel g gi a b c y| := hle
    _ ≤ ‖∑ a, ∑ b, ∑ c, |christoffel g gi a b c y|‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ C := hCb y hy
    _ ≤ max C 0 := le_max_left _ _

/-- **Uniform sup-bound on the first derivatives of the Christoffel symbols over a compact set.**
    Same route as `christoffel_bddOn_compact`, applied to the (continuous, since `Γ` is `ContDiff ⊤`)
    Fréchet derivatives `fderiv ℝ (Γ^a_{bc})`; bounds the operator norm uniformly over `y ∈ K` and
    all triples.  This is the Lipschitz-modulus data a uniform Grönwall estimate consumes. -/
theorem christoffel_fderiv_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ y ∈ K, ∀ a b c,
      ‖fderiv ℝ (fun z => christoffel g gi a b c z) y‖ ≤ Kb := by
  have hFcont : Continuous
      (fun y => ∑ a, ∑ b, ∑ c, ‖fderiv ℝ (fun z => christoffel g gi a b c z) y‖) := by
    refine continuous_finsetSum _ (fun a _ => ?_)
    refine continuous_finsetSum _ (fun b _ => ?_)
    refine continuous_finsetSum _ (fun c _ => ?_)
    exact ((hC a b c).continuous_fderiv (by simp)).norm
  obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn hFcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y hy a b c => ?_⟩
  have hle : ‖fderiv ℝ (fun z => christoffel g gi a b c z) y‖
      ≤ ∑ a, ∑ b, ∑ c, ‖fderiv ℝ (fun z => christoffel g gi a b c z) y‖ := by
    calc ‖fderiv ℝ (fun z => christoffel g gi a b c z) y‖
        ≤ ∑ c', ‖fderiv ℝ (fun z => christoffel g gi a b c' z) y‖ :=
          Finset.single_le_sum
            (f := fun c' => ‖fderiv ℝ (fun z => christoffel g gi a b c' z) y‖)
            (fun i _ => norm_nonneg _) (mem_univ c)
      _ ≤ ∑ b', ∑ c', ‖fderiv ℝ (fun z => christoffel g gi a b' c' z) y‖ :=
          Finset.single_le_sum
            (f := fun b' => ∑ c', ‖fderiv ℝ (fun z => christoffel g gi a b' c' z) y‖)
            (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (mem_univ b)
      _ ≤ ∑ a', ∑ b', ∑ c', ‖fderiv ℝ (fun z => christoffel g gi a' b' c' z) y‖ :=
          Finset.single_le_sum
            (f := fun a' => ∑ b', ∑ c', ‖fderiv ℝ (fun z => christoffel g gi a' b' c' z) y‖)
            (fun i _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (mem_univ a)
  calc ‖fderiv ℝ (fun z => christoffel g gi a b c z) y‖
      ≤ ∑ a, ∑ b, ∑ c, ‖fderiv ℝ (fun z => christoffel g gi a b c z) y‖ := hle
    _ ≤ ‖∑ a, ∑ b, ∑ c, ‖fderiv ℝ (fun z => christoffel g gi a b c z) y‖‖ := by
        rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ C := hCb y hy
    _ ≤ max C 0 := le_max_left _ _

/-- **Uniform norm-bound on the geodesic field over a compact set of phase points.**  The geodesic
    field `F(x,v) = (v, −Γ(x)(v,v))` is `ContDiff ℝ ⊤` (`contDiff_geodesicField`), hence continuous,
    hence bounded on any compact `K ⊆ Point n × Point n`.  (Note the domain is phase space: the
    velocity-quadratic second component is unbounded over non-compact velocities, so `K` must live in
    `Point n × Point n`.) -/
theorem geodesicField_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n × Point n)} (hK : IsCompact K) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ K, ‖geodesicField g gi z‖ ≤ Kb := by
  obtain ⟨C, hCb⟩ :=
    hK.exists_bound_of_continuousOn (contDiff_geodesicField g gi hC).continuous.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hCb z hz).trans (le_max_left _ _)⟩

/-- **Uniform bound on the derivative of the geodesic field over a compact set of phase points.**
    `fderiv ℝ (geodesicField g gi)` is continuous (`geodesicField` is `ContDiff ⊤`), hence its
    operator norm is bounded on any compact `K ⊆ Point n × Point n`.  On a convex such `K` this bound
    is exactly a uniform Lipschitz modulus for the geodesic field
    (`Convex.lipschitzOnWith_of_nnnorm_fderiv_le`) — the uniform-in-base-point Grönwall input A2
    needs. -/
theorem geodesicField_fderiv_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n × Point n)} (hK : IsCompact K) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ K, ‖fderiv ℝ (geodesicField g gi) z‖ ≤ Kb := by
  have hDFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn hDFcont.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hCb z hz).trans (le_max_left _ _)⟩

end QIQTH.ExpMap
