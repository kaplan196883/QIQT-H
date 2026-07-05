/-
  Geodesic — the geodesic ODE of a component connection: local existence + uniqueness.

  GEO1 of THE_GEODESIC_PLAN.md.  Component-level, in a fixed coordinate chart
  `Point n = Fin n → ℝ`, on the `christoffel` symbols of `QIQTH/Curvature.lean`.

  The second-order geodesic equation `γ'' + Γ(γ)(γ',γ') = 0` is rewritten as a FIRST-order
  autonomous system on the phase space `Point n × Point n`, with vector field
  `F(x,v) = (v, −Γ(x)(v,v))` (`geodesicField`).  This field is `C^∞` whenever the Christoffel
  symbols are (`contDiff_geodesicField`), so Mathlib's Picard–Lindelöf theorem
  (`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`) gives a local
  integral curve through any initial phase point (`geodesic_local_existence`), and
  `ODE_solution_unique_of_mem_Ioo` gives uniqueness on any set where the field is Lipschitz
  (`geodesic_local_unique`).  The phase space is finite-dimensional, so `CompleteSpace` /
  `NormedSpace ℝ` are automatic.

  HONEST CAPTION (binding): this is geodesic EXISTENCE only.  It does NOT build the exponential
  map or normal coordinates, does NOT discharge the carried RNC normal-coordinate gauge (that is
  gated on smooth dependence of ODE solutions on the initial condition — a theorem Mathlib LACKS,
  only Lipschitz dependence is present), and does NOT move numerical-G (species count N, granularity
  scale Λ_s, the E/ξ term remain).  Component geodesics exist and are unique; nothing more.
-/
import Mathlib
import QIQTH.Curvature

namespace QIQTH.Geodesic

open QIQTH.Curvature
open Finset

variable {n : ℕ}

/-- **The geodesic vector field** on the phase space `Point n × Point n`.  Writing the second-order
    geodesic equation `γ'' + Γ(γ)(γ',γ') = 0` as a first-order autonomous system, the field is
    `F(x,v) = (v, −Γ(x)(v,v))`, i.e. the first component is the velocity and the second is the
    geodesic acceleration `−∑_{j,k} Γ^i_{jk}(x) v^j v^k`. -/
noncomputable def geodesicField (g gi : Point n → Fin n → Fin n → ℝ) :
    (Point n × Point n) → (Point n × Point n) :=
  fun p => (p.2, fun i => -∑ j, ∑ k, christoffel g gi i j k p.1 * p.2 j * p.2 k)

/-- **The geodesic field is `C^∞`** whenever the Christoffel symbols are.  Assembled from the
    smoothness of the coordinate/velocity projections (`contDiff_fst`/`contDiff_snd`/`contDiff_apply`)
    and of `christoffel` (the carried `hC`), through products (`ContDiff.mul`), finite sums
    (`ContDiff.sum`), negation, and the product/pi structure of the phase space
    (`ContDiff.prodMk`, `contDiff_pi`). -/
theorem contDiff_geodesicField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (geodesicField g gi) := by
  apply ContDiff.prodMk contDiff_snd
  rw [contDiff_pi]
  intro i
  apply ContDiff.neg
  refine ContDiff.sum fun j _ => ?_
  refine ContDiff.sum fun k _ => ?_
  exact (((hC i j k).comp contDiff_fst).mul
      ((contDiff_apply ℝ ℝ j).comp contDiff_snd)).mul ((contDiff_apply ℝ ℝ k).comp contDiff_snd)

/-- **Local existence of geodesics (Picard–Lindelöf).**  For any initial phase point
    `z₀ = (x₀, v₀) ∈ Point n × Point n` and any base time `t₀`, there is a curve `γ : ℝ → Point n ×
    Point n` with `γ t₀ = z₀` that solves the first-order geodesic system `γ' t = F(γ t)` on an open
    interval `(t₀ − ε, t₀ + ε)`.  The first component is then a geodesic of the component connection.
    Uses the `C¹` Picard–Lindelöf lemma
    `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`.

    HONEST: existence only — this is NOT the exponential map, NOT normal coordinates, and does NOT
    discharge the carried RNC gauge (that needs smooth dependence on the initial condition, absent
    from Mathlib). -/
theorem geodesic_local_existence (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (z₀ : Point n × Point n) (t₀ : ℝ) :
    ∃ γ : ℝ → Point n × Point n, γ t₀ = z₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt γ (geodesicField g gi (γ t)) t :=
  (((contDiff_geodesicField g gi hC).of_le le_top).contDiffAt
    (x := z₀)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-- **Local uniqueness of geodesics (Grönwall).**  Two integral curves of the geodesic field that
    stay inside a set `S` on which the field is `K`-Lipschitz and that agree at one time `t₀` in an
    open interval `(a, b)` agree on all of `(a, b)`.  Since `geodesicField` is `C^∞`
    (`contDiff_geodesicField`), it is Lipschitz on every bounded set, so such an `S` always exists;
    it is exposed as the hypothesis `hK`.  Uses `ODE_solution_unique_of_mem_Ioo`.

    HONEST: uniqueness of the component geodesic — not the exponential map / normal coordinates. -/
theorem geodesic_local_unique (g gi : Point n → Fin n → Fin n → ℝ)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    {γ₁ γ₂ : ℝ → Point n × Point n} {K : NNReal} {S : Set (Point n × Point n)}
    (hK : LipschitzOnWith K (geodesicField g gi) S)
    (h1 : ∀ t ∈ Set.Ioo a b, HasDerivAt γ₁ (geodesicField g gi (γ₁ t)) t ∧ γ₁ t ∈ S)
    (h2 : ∀ t ∈ Set.Ioo a b, HasDerivAt γ₂ (geodesicField g gi (γ₂ t)) t ∧ γ₂ t ∈ S)
    (heq : γ₁ t₀ = γ₂ t₀) :
    Set.EqOn γ₁ γ₂ (Set.Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (v := fun _ => geodesicField g gi) (s := fun _ => S)
    (fun _ _ => hK) ht₀ h1 h2 heq

end QIQTH.Geodesic
