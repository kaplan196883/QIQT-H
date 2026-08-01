/-
  UniformPullbackEntryBound — J4-64 (Brick-A β): the UNIFORM (over `q ∈ K`, `‖v‖ ≤ r₀`) `C⁰` bound on
  the pullback-metric ENTRIES `uniformFlowPullbackMetric g gi hC hK q v i j`.

  ## Context

  Brick-A(β) re-architects the residual chain off the opaque per-`q` `expMap`/`expRho` onto the
  compact-uniform flow endpoint `uniformFlowExp` (radius `ρ_K = uniformFlowRadius`, NO `expRho`).
  Two uniform-over-`K` ingredients are already in place:

  * `uniformFlowExp_displacement_uniform_bound` (J4-62, `UniformFlowRegBound`):
      `∃ M ≥ 0, ∀ q ∈ K, ∀ ‖v‖ ≤ ρ_K, ‖uniformFlowExp q v − q‖ ≤ M` — the endpoint stays in a fixed
      compact tube neighbourhood, so the sampled ambient metric `g(uniformFlowExp q v)` lives in a
      fixed compact set;
  * `uniformFlowExp_fderiv_uniform_bound` (J4-63, `UniformFlowJacobianBound`):
      `∃ Mj, ∀ q ∈ K, ∀ ‖v‖ < ρ_K, ‖fderiv (uniformFlowExp q) v‖ ≤ Mj` (`Mj = e^{K_f}`, q-independent).

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no smuggled bound, no `expRho`)

  * `uniformFlowExp_metric_entry_uniform_bound` (Q1) — the UNIFORM `g`-factor bound:
      `∃ Mg0 ≥ 0, ∀ q ∈ K, ∀ ‖v‖ ≤ ρ_K, ∀ a b, |g (uniformFlowExp q v) a b| ≤ Mg0`.
    ROUTE: displacement bound (J4-62) + `K ⊆ closedBall p₀ R` ⟹ `uniformFlowExp q v ∈ closedBall p₀ (R+M)`
    (a fixed compact `T`); `∑_{a,b} |g · a b|` is continuous (from the carried metric regularity `hg`),
    hence bounded on `T` via `IsCompact.exists_bound_of_continuousOn`; a single entry `≤` that sum `≤` bound.

  * `uniformFlowPullbackMetric_entry_uniform_bound` (Q2+Q3) — the UNIFORM entry bound:
      `∃ r₀ > 0, ∃ Mg, ∀ q ∈ K, ∀ ‖v‖ ≤ r₀, ∀ i j, |uniformFlowPullbackMetric g gi hC hK q v i j| ≤ Mg`,
    with `r₀ = ρ_K/2` and `Mg = ∑_{a,b} Mg0·Mj'·Mj'` (`Mj' = max Mj 0`).
    ROUTE (Cauchy–Schwarz / triangle): `g̃_{ij} = ∑_{a,b} g_{ab}·J_{ai}·J_{bj}`; per Jacobian entry
    `|J_{ai}| = |(fderiv v)(e_i) a| ≤ ‖(fderiv v)(e_i)‖ ≤ ‖fderiv v‖·‖e_i‖ ≤ Mj·1 ≤ Mj'`
    (`norm_le_pi_norm` + `ContinuousLinearMap.le_opNorm` + `Pi.norm_single`, `norm_one`); triangle over the
    finite double sum + termwise `mul_le_mul` closes it.

  ## HONEST SCOPE (binding)

  The metric-regularity input `hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b)` is a GENUINE geometric
  hypothesis (the ambient metric is smooth — the SAME shape carried in `ChristoffelSmooth`,
  `C4cDecomposition`, `AnnulusContinuityWithinRho`).  It is NOT the conclusion and NOT derivable from
  `hC` (which constrains only the Christoffel symbols).  The conclusion — a uniform entry bound `Mg`,
  chosen BEFORE `q, v` are introduced — is genuinely DERIVED.  No `sorry`, no new axioms, no vacuous
  hypotheses, no `expRho`.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowPullback
import QIQTH.UniformFlowJacobianBound
import QIQTH.UniformFlowRegBound
import QIQTH.UniformFlowNondeg
import QIQTH.BoundedGeometry
import Mathlib

open Finset
open QIQTH.Curvature QIQTH.ExpMap
open scoped BigOperators

namespace QIQTH.PullbackMetric

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### Q1 — the uniform `g`-factor bound at the uniform-flow endpoint. -/

/-- **Q1 — the UNIFORM ambient-metric bound at the uniform-flow exp endpoint over `K`.**

    There is a single `Mg0 ≥ 0` such that for every base point `q ∈ K` and every velocity `v` with
    `‖v‖ ≤ ρ_K` (`ρ_K = uniformFlowRadius`), every entry of the ambient metric sampled at the endpoint
    is bounded: `|g (uniformFlowExp g gi hC hK q v) a b| ≤ Mg0`.

    DERIVED from the endpoint-displacement bound (J4-62) — which confines the endpoint to a fixed
    compact ball `T = closedBall p₀ (R+M)` (`K ⊆ closedBall p₀ R`) — together with the GENUINE metric
    regularity `hg` (each `g · a b` is `C^∞`, hence continuous), so `∑_{a,b} |g · a b|` attains a bound
    on the compact `T`.  A single entry is `≤` that sum `≤` the bound.  No `expRho`, no smuggled bound. -/
theorem uniformFlowExp_metric_entry_uniform_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ Mg0 : ℝ, 0 ≤ Mg0 ∧ ∀ q ∈ K, ∀ v : Point n,
      ‖v‖ ≤ uniformFlowRadius g gi hC hK →
      ∀ a b, |g (uniformFlowExp g gi hC hK q v) a b| ≤ Mg0 := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · -- Vacuous over an empty base set.
    refine ⟨0, le_refl 0, ?_⟩
    intro q hq; rw [hKe] at hq; exact absurd hq (Set.notMem_empty q)
  -- Displacement bound + enclosing ball.
  obtain ⟨M, hM0, hMbound⟩ := uniformFlowExp_displacement_uniform_bound g gi hC hK
  obtain ⟨p₀, _hp₀⟩ := hKne
  obtain ⟨R, hRsub⟩ := hK.isBounded.subset_closedBall p₀
  -- Continuity of `∑_{a,b} |g · a b|` (from the carried metric regularity `hg`).
  have hGcont : Continuous (fun x : Point n => ∑ a, ∑ b, |g x a b|) := by
    refine continuous_finsetSum _ (fun a _ => ?_)
    refine continuous_finsetSum _ (fun b _ => ?_)
    exact ((hg a b).continuous).abs
  -- The fixed compact tube-neighbourhood `T`.
  set T : Set (Point n) := Metric.closedBall p₀ (R + M) with hTdef
  have hTcompact : IsCompact T := isCompact_closedBall _ _
  obtain ⟨C, hCb⟩ := hTcompact.exists_bound_of_continuousOn hGcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq v hv a b
  -- The endpoint is confined to `T`.
  have hxT : uniformFlowExp g gi hC hK q v ∈ T := by
    rw [hTdef, Metric.mem_closedBall]
    have hdisp : ‖uniformFlowExp g gi hC hK q v - q‖ ≤ M := hMbound q hq v hv
    have hqp : dist q p₀ ≤ R := Metric.mem_closedBall.mp (hRsub hq)
    calc dist (uniformFlowExp g gi hC hK q v) p₀
        ≤ dist (uniformFlowExp g gi hC hK q v) q + dist q p₀ := dist_triangle _ _ _
      _ ≤ M + R := add_le_add (by rw [dist_eq_norm]; exact hdisp) hqp
      _ = R + M := by ring
  -- A single entry `≤` the double sum `≤` the compact bound.
  have hle : |g (uniformFlowExp g gi hC hK q v) a b|
      ≤ ∑ a', ∑ b', |g (uniformFlowExp g gi hC hK q v) a' b'| := by
    calc |g (uniformFlowExp g gi hC hK q v) a b|
        ≤ ∑ b', |g (uniformFlowExp g gi hC hK q v) a b'| :=
          Finset.single_le_sum
            (f := fun b' => |g (uniformFlowExp g gi hC hK q v) a b'|)
            (fun i _ => abs_nonneg _) (mem_univ b)
      _ ≤ ∑ a', ∑ b', |g (uniformFlowExp g gi hC hK q v) a' b'| :=
          Finset.single_le_sum
            (f := fun a' => ∑ b', |g (uniformFlowExp g gi hC hK q v) a' b'|)
            (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (mem_univ a)
  calc |g (uniformFlowExp g gi hC hK q v) a b|
      ≤ ∑ a', ∑ b', |g (uniformFlowExp g gi hC hK q v) a' b'| := hle
    _ ≤ ‖∑ a', ∑ b', |g (uniformFlowExp g gi hC hK q v) a' b'|‖ := by
        rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ C := hCb _ hxT
    _ ≤ max C 0 := le_max_left _ _

/-! ### Q2 + Q3 — the uniform pullback-metric ENTRY bound. -/

/-- **★ J4-64 (Q2+Q3) — the UNIFORM `C⁰` entry bound on the uniform-flow pullback metric.**

    There is a uniform radius `r₀ = ρ_K/2 > 0` and a single constant `Mg` such that for every base
    point `q ∈ K` and every velocity `v` with `‖v‖ ≤ r₀`, EVERY entry of the pullback metric is bounded:
        `|uniformFlowPullbackMetric g gi hC hK q v i j| ≤ Mg`.

    The constant `Mg = ∑_{a,b} Mg0·Mj'·Mj'` is chosen BEFORE `q, v` are introduced (genuinely uniform):
    `Mg0` is the Q1 uniform ambient-metric bound; `Mj' = max Mj 0` with `Mj` the J4-63 uniform Jacobian
    bound.  Proof: `g̃_{ij} = ∑_{a,b} g_{ab}·J_{ai}·J_{bj}` (the definition of `uniformFlowPullbackMetric`);
    each Jacobian entry `|J_{ai}| ≤ ‖(fderiv v)(e_i)‖ ≤ ‖fderiv v‖·‖e_i‖ ≤ Mj·1 ≤ Mj'`; a triangle bound
    over the finite double sum plus termwise `mul_le_mul` closes it.

    The metric regularity `hg` (each `g · a b` is `C^∞`) is carried HONESTLY as geometry — it is NOT the
    conclusion, and NOT derivable from `hC`.  No `sorry`, no new axioms, no `expRho`. -/
theorem uniformFlowPullbackMetric_entry_uniform_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ Mg : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ r₀ →
      ∀ i j, |uniformFlowPullbackMetric g gi hC hK q v i j| ≤ Mg := by
  obtain ⟨Mg0, hMg0nn, hMg0⟩ := uniformFlowExp_metric_entry_uniform_bound g gi hg hC hK
  obtain ⟨Mj, hMj⟩ := uniformFlowExp_fderiv_uniform_bound g gi hC hK
  set Mj' : ℝ := max Mj 0 with hMj'def
  have hMj'nn : 0 ≤ Mj' := le_max_right _ _
  have hρ0 : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨uniformFlowRadius g gi hC hK / 2, by positivity,
    ∑ _a : Fin n, ∑ _b : Fin n, Mg0 * Mj' * Mj', ?_⟩
  intro q hq v hv i j
  -- Radius alignment: `‖v‖ ≤ ρ_K/2 ⟹ ‖v‖ ≤ ρ_K` and `‖v‖ < ρ_K`.
  have hvρ : ‖v‖ ≤ uniformFlowRadius g gi hC hK := hv.trans (by linarith)
  have hvρ' : ‖v‖ < uniformFlowRadius g gi hC hK := hv.trans_lt (by linarith)
  -- Uniform Jacobian ENTRY bound: `|J_{ki}| ≤ Mj'`.
  have hJbound : ∀ (k : Fin n) (a : Fin n),
      |(fderiv ℝ (uniformFlowExp g gi hC hK q) v) (Pi.single k 1) a| ≤ Mj' := by
    intro k a
    have hop : ‖fderiv ℝ (uniformFlowExp g gi hC hK q) v‖ ≤ Mj := hMj q hq v hvρ'
    calc |(fderiv ℝ (uniformFlowExp g gi hC hK q) v) (Pi.single k 1) a|
        = ‖(fderiv ℝ (uniformFlowExp g gi hC hK q) v) (Pi.single k 1) a‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(fderiv ℝ (uniformFlowExp g gi hC hK q) v) (Pi.single k 1)‖ := norm_le_pi_norm _ a
      _ ≤ ‖fderiv ℝ (uniformFlowExp g gi hC hK q) v‖ * ‖(Pi.single k 1 : Point n)‖ :=
          (fderiv ℝ (uniformFlowExp g gi hC hK q) v).le_opNorm _
      _ = ‖fderiv ℝ (uniformFlowExp g gi hC hK q) v‖ * 1 := by rw [Pi.norm_single, norm_one]
      _ = ‖fderiv ℝ (uniformFlowExp g gi hC hK q) v‖ := mul_one _
      _ ≤ Mj := hop
      _ ≤ Mj' := le_max_left _ _
  -- Uniform ambient-metric ENTRY bound (Q1).
  have hgentry : ∀ a b, |g (uniformFlowExp g gi hC hK q v) a b| ≤ Mg0 := hMg0 q hq v hvρ
  -- Unfold the pullback metric and bound the finite double sum.
  simp only [uniformFlowPullbackMetric]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum (fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum (fun b _ => ?_)
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hgentry a b) (hJbound i a) (abs_nonneg _) hMg0nn)
    (hJbound j b) (abs_nonneg _) (mul_nonneg hMg0nn hMj'nn)

end QIQTH.PullbackMetric
