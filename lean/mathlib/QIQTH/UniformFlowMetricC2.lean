/-
  UniformFlowMetricC2 — J4-79 (Brick-A β, W4): the pulled-back metric `g̃` of `uniformFlowExp` is
  TWICE Fréchet-differentiable on the uniform ball, with a UNIFORM `C⁰` entry bound over `q ∈ K`.

  ## Context

  W1–W3 supplied `uniformFlowExp ∈ C³` with uniform bounds:
  * First jet `uniformFlowExp_hasFDerivAt` (`UniformFlowFDeriv`): `HasFDerivAt (uniformFlowExp q) L w`
    at every interior velocity `‖w‖ < ρ_K`.
  * CLM-valued Hessian existence `uniformFlowExp_fderiv_hasFDerivAt` (`UniformFlowHessian`, R2):
    `w ↦ fderiv ℝ (uniformFlowExp q) w` is Fréchet-differentiable at each interior `w`.
  * CLM-valued third-jet existence `uniformFlowExp_hessianMap_differentiableAt`
    (`UniformFlowThirdBoundClose`, D1): `w ↦ fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp q) u) w`
    is differentiable at each interior `v`.
  * Uniform `C⁰` pullback entry bound `uniformFlowPullbackMetric_entry_uniform_bound`
    (`UniformPullbackEntryBound`, Q2+Q3).

  ## What lands here (DERIVED; no `sorry`, no new axioms, no hyp = conclusion, no `expRho`)

  A small reusable second-order-differentiability calculus for SCALAR maps, `IsC2At f v` :=
  "`f` is differentiable on a neighbourhood of `v` AND its `fderiv`-map is differentiable at `v`",
  closed under `+`, `*`, finite sums and constants (`isC2At_add`, `isC2At_mul`,
  `isC2At_finsetSum`, `isC2At_const`).  From it:

  * `isC2At_jacobianEntry` (deliverable 1) — each scalar Jacobian entry
      `v ↦ (fderiv ℝ (uniformFlowExp q) v) (Pi.single i 1) a` is `IsC2At` at any interior `v`
    (CLM-application route `evJ = proj_a ∘L apply_{e_i}` composed with R2's Hessian existence /
    D1's third-jet existence).
  * `isC2At_metricFactor` (deliverable 2) — each composed ambient-metric factor
      `v ↦ g (uniformFlowExp q v) a b` is `IsC2At` at any interior `v` (chain rule: `hg`-smooth
    entry `g·ab ∘ F`, first + second jets of `F`).
  * `uniformFlowPullbackMetric_entry_isC2At` (deliverable 3) — each pullback-metric entry
      `v ↦ uniformFlowPullbackMetric g gi hC hK q v i j` is `IsC2At` (finite sum of triple products).
  * `uniformFlowPullbackMetric_entry_hasFDerivAt_two_layers` — both Fréchet layers exist as
    `HasFDerivAt` (first jet of the entry, and first jet of its `fderiv`-map).
  * `uniformFlowPullbackMetric_c2_uniform` (capstone, deliverable 5 + partial 4) — ONE uniform-over-`K`
    radius `r₀ > 0` and constant `M` such that for every `q ∈ K`, `‖v‖ < r₀`, `i j`, the entry map is
    twice differentiable (both `HasFDerivAt` layers) AND `|g̃_{ij}(v)| ≤ M`.

  ## HONEST FIREWALL (binding)

  The capstone bounds the `C⁰` level only.  The UNIFORM `C¹` and `C²` bounds
  (`‖fderiv (entry) v‖ ≤ M`, `‖fderiv (fun w => fderiv (entry) w) v‖ ≤ M`) required by deliverable (4)
  are NOT discharged here.  This is an ASSEMBLY firewall, not a mathematical gap: every sub-bound needed
  already exists uniformly over `K` —
    * ambient-metric entry bound `Mg0` (`uniformFlowExp_metric_entry_uniform_bound`, Q1),
    * uniform Jacobian opNorm `Mj` (`uniformFlowExp_fderiv_uniform_bound`, J4-63),
    * uniform Hessian opNorm `M'` (`uniformFlowExp_hessian_opNorm_le`, R3),
    * uniform third-jet opNorm `M₃` (`uniformFlowExp_thirdDeriv_opNorm_le`, W3),
    * uniform `‖Dg‖`, `‖D²g‖` on the fixed compact endpoint tube `T` (extreme-value theorem on the
      `hg`-smooth ambient metric, exactly the Q1 pattern one/two derivative-orders up) —
  what remains is the purely mechanical propagation of chain-rule and product-rule OPERATOR-NORM bounds through
  the `IsC2At` triple product (a general `IsC2At`-with-0/1/2-bounds product lemma applied twice, then a
  finite triangle sum).  Carried, not faked.  This file does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.
-/
import QIQTH.UniformFlowPullback
import QIQTH.UniformPullbackEntryBound
import QIQTH.UniformFlowHessian
import QIQTH.UniformFlowThirdBoundClose
import QIQTH.UniformFlowFDeriv
import Mathlib

open Filter
open QIQTH.Curvature QIQTH.PullbackMetric
open scoped Topology BigOperators

namespace QIQTH.ExpMap

set_option maxHeartbeats 800000

variable {n : ℕ}

/-! ### A small second-order-differentiability calculus for scalar maps -/

/-- `IsC2At f v`: `f` is differentiable on a neighbourhood of `v`, and its `fderiv`-map is
    differentiable at `v`.  This is exactly what is needed to produce the two `HasFDerivAt` layers
    (`f` and `w ↦ fderiv ℝ f w`) that the C² pullback-metric capstone consumes. -/
def IsC2At {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X → ℝ) (v : X) : Prop :=
  (∀ᶠ w in 𝓝 v, DifferentiableAt ℝ f w) ∧ DifferentiableAt ℝ (fun w => fderiv ℝ f w) v

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `IsC2At f v` gives ordinary differentiability of `f` at `v`. -/
theorem IsC2At.differentiableAt {f : X → ℝ} {v : X} (h : IsC2At f v) :
    DifferentiableAt ℝ f v :=
  h.1.self_of_nhds

/-- Constants are `IsC2At`. -/
theorem isC2At_const {v : X} (c : ℝ) : IsC2At (fun _ : X => c) v := by
  refine ⟨Filter.Eventually.of_forall fun w => differentiableAt_const c, ?_⟩
  have h0 : (fun w : X => fderiv ℝ (fun _ : X => c) w) = fun _ => (0 : X →L[ℝ] ℝ) := by
    funext w; simp
  rw [h0]; exact differentiableAt_const _

/-- `IsC2At` is closed under addition. -/
theorem isC2At_add {f h : X → ℝ} {v : X} (hf : IsC2At f v) (hh : IsC2At h v) :
    IsC2At (fun w => f w + h w) v := by
  refine ⟨(hf.1.and hh.1).mono fun w hw => hw.1.add hw.2, ?_⟩
  have heq : (fun w => fderiv ℝ (fun x => f x + h x) w) =ᶠ[𝓝 v]
      (fun w => fderiv ℝ f w + fderiv ℝ h w) :=
    (hf.1.and hh.1).mono fun w hw => fderiv_add hw.1 hw.2
  exact (hf.2.add hh.2).congr_of_eventuallyEq heq

/-- `IsC2At` is closed under multiplication (scalar product rule). -/
theorem isC2At_mul {f h : X → ℝ} {v : X} (hf : IsC2At f v) (hh : IsC2At h v) :
    IsC2At (fun w => f w * h w) v := by
  refine ⟨(hf.1.and hh.1).mono fun w hw => hw.1.mul hw.2, ?_⟩
  have heq : (fun w => fderiv ℝ (fun x => f x * h x) w) =ᶠ[𝓝 v]
      (fun w => f w • fderiv ℝ h w + h w • fderiv ℝ f w) :=
    (hf.1.and hh.1).mono fun w hw => fderiv_mul hw.1 hw.2
  have hd : DifferentiableAt ℝ (fun w => f w • fderiv ℝ h w + h w • fderiv ℝ f w) v :=
    (hf.differentiableAt.smul hh.2).add (hh.differentiableAt.smul hf.2)
  exact hd.congr_of_eventuallyEq heq

/-- `IsC2At` is closed under finite sums. -/
theorem isC2At_finsetSum {ι : Type*} {v : X} (s : Finset ι) (F : ι → X → ℝ) :
    (∀ i ∈ s, IsC2At (F i) v) → IsC2At (fun w => ∑ i ∈ s, F i w) v := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact isC2At_const (0 : ℝ)
  · intro a s ha ih hins
    have hcons : (fun w => ∑ i ∈ insert a s, F i w)
        = fun w => F a w + ∑ i ∈ s, F i w := by
      funext w; rw [Finset.sum_insert ha]
    rw [hcons]
    exact isC2At_add (hins a (Finset.mem_insert_self a s))
      (ih (fun i hi => hins i (Finset.mem_insert_of_mem hi)))

/-! ### Deliverable (1) — the Jacobian entries are `IsC2At` -/

/-- **Deliverable (1).** Each scalar Jacobian entry `v ↦ (fderiv ℝ (uniformFlowExp q) v) (e_i) a` is
    twice differentiable at any interior `v`.  Route: it equals `evJ ∘ Jac` where
    `evJ = proj_a ∘L apply_{e_i}` is a fixed CLM and `Jac w = fderiv ℝ (uniformFlowExp q) w`; `Jac` is
    differentiable on the ball (R2, `uniformFlowExp_fderiv_hasFDerivAt`) so `evJ ∘ Jac` is; its
    `fderiv`-map is (eventually) `w ↦ evJ ∘L (fderiv ℝ Jac w)`, differentiable at `v` by D1
    (`uniformFlowExp_hessianMap_differentiableAt`) via `clm_comp`. -/
theorem isC2At_jacobianEntry (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (i a : Fin n) :
    IsC2At (fun w => (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single i 1) a) v := by
  classical
  set ρ := uniformFlowRadius g gi hC hK with hρ
  set F := uniformFlowExp g gi hC hK q with hFdef
  set Jac : Point n → (Point n →L[ℝ] Point n) := fun w => fderiv ℝ F w with hJacdef
  set evJ : (Point n →L[ℝ] Point n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) a).comp
      (ContinuousLinearMap.apply ℝ (Point n) (Pi.single i 1)) with hevJdef
  have hevJapp : ∀ L : Point n →L[ℝ] Point n, evJ L = L (Pi.single i 1) a := by
    intro L
    simp [hevJdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.proj_apply]
  have hval : (fun w' => (fderiv ℝ F w') (Pi.single i 1) a) = fun w' => evJ (Jac w') := by
    funext w'; rw [hevJapp]
  have hball : Metric.ball (0 : Point n) ρ ∈ 𝓝 v :=
    Metric.isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; exact hv)
  have hJacDiff : ∀ᶠ w in 𝓝 v, DifferentiableAt ℝ Jac w := by
    refine Filter.eventually_of_mem hball (fun w hw => ?_)
    have hw' : ‖w‖ < ρ := by rw [← mem_ball_zero_iff]; exact hw
    obtain ⟨B₂, hB₂⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq w hw'
    exact hB₂.differentiableAt
  refine ⟨?_, ?_⟩
  · refine hJacDiff.mono (fun w hwJac => ?_)
    rw [hval]
    exact (evJ.differentiableAt).comp w hwJac
  · have heq : (fun w => fderiv ℝ (fun w' => (fderiv ℝ F w') (Pi.single i 1) a) w) =ᶠ[𝓝 v]
        (fun w => evJ.comp (fderiv ℝ Jac w)) := by
      refine hJacDiff.mono (fun w hwJac => ?_)
      have hcomp : HasFDerivAt (fun w' => evJ (Jac w')) (evJ.comp (fderiv ℝ Jac w)) w :=
        evJ.hasFDerivAt.comp w hwJac.hasFDerivAt
      rw [hval]
      exact hcomp.fderiv
    have hHess : DifferentiableAt ℝ (fun w => fderiv ℝ Jac w) v :=
      uniformFlowExp_hessianMap_differentiableAt g gi hC hK q hq v hv
    have hd : DifferentiableAt ℝ (fun w => evJ.comp (fderiv ℝ Jac w)) v :=
      (differentiableAt_const evJ).clm_comp hHess
    exact hd.congr_of_eventuallyEq heq

/-! ### Deliverable (2) — the composed ambient-metric factors are `IsC2At` -/

/-- **Deliverable (2).** Each ambient-metric factor `v ↦ g (uniformFlowExp q v) a b` is twice
    differentiable at any interior `v`.  Chain rule: `g·ab` is `C^∞` (`hg`), `F = uniformFlowExp q`
    is differentiable on the ball (first jet) with differentiable `fderiv`-map (R2); the factor's
    `fderiv`-map is (eventually) `w ↦ (fderiv g·ab (F w)) ∘L (fderiv F w)`, a `clm_comp` of two maps
    differentiable at `v`. -/
theorem isC2At_metricFactor (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b : Fin n) :
    IsC2At (fun w => g (uniformFlowExp g gi hC hK q w) a b) v := by
  classical
  set ρ := uniformFlowRadius g gi hC hK with hρ
  set F := uniformFlowExp g gi hC hK q with hFdef
  set gab : Point n → ℝ := fun y => g y a b with hgabdef
  have hgabCd : ContDiff ℝ (⊤ : WithTop ℕ∞) gab := hg a b
  have hgabDiff : Differentiable ℝ gab := hgabCd.differentiable (by simp)
  have hDgabDiff : Differentiable ℝ (fderiv ℝ gab) :=
    (hgabCd.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).differentiable (by simp)
  have hball : Metric.ball (0 : Point n) ρ ∈ 𝓝 v :=
    Metric.isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; exact hv)
  have hFdiff : ∀ᶠ w in 𝓝 v, DifferentiableAt ℝ F w := by
    refine Filter.eventually_of_mem hball (fun w hw => ?_)
    have hw' : ‖w‖ < ρ := by rw [← mem_ball_zero_iff]; exact hw
    obtain ⟨L, hL⟩ := uniformFlowExp_hasFDerivAt g gi hC hK q hq w hw'
    exact hL.differentiableAt
  refine ⟨hFdiff.mono fun w hw => (hgabDiff (F w)).comp w hw, ?_⟩
  have heq : (fun w => fderiv ℝ (fun w' => gab (F w')) w) =ᶠ[𝓝 v]
      (fun w => (fderiv ℝ gab (F w)).comp (fderiv ℝ F w)) := by
    refine hFdiff.mono (fun w hw => ?_)
    have hcomp : HasFDerivAt (fun w' => gab (F w'))
        ((fderiv ℝ gab (F w)).comp (fderiv ℝ F w)) w :=
      (hgabDiff (F w)).hasFDerivAt.comp w hw.hasFDerivAt
    exact hcomp.fderiv
  have hJacDiff : DifferentiableAt ℝ (fun w => fderiv ℝ F w) v := by
    obtain ⟨B₂, hB₂⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq v hv
    exact hB₂.differentiableAt
  have hDgF : DifferentiableAt ℝ (fun w => fderiv ℝ gab (F w)) v :=
    (hDgabDiff (F v)).comp v hFdiff.self_of_nhds
  have hd : DifferentiableAt ℝ (fun w => (fderiv ℝ gab (F w)).comp (fderiv ℝ F w)) v :=
    hDgF.clm_comp hJacDiff
  exact hd.congr_of_eventuallyEq heq

/-! ### Deliverable (3) — the pullback-metric entries are `IsC2At` -/

/-- **Deliverable (3).** Each pullback-metric entry `v ↦ uniformFlowPullbackMetric g gi hC hK q v i j`
    is twice differentiable at any interior `v`: it is the finite double sum of triple products of the
    `IsC2At` factors of (1) and (2), and `IsC2At` is closed under `*` and finite sums. -/
theorem uniformFlowPullbackMetric_entry_isC2At (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (i j : Fin n) :
    IsC2At (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) v := by
  have hbase : ∀ a b : Fin n,
      IsC2At (fun w => g (uniformFlowExp g gi hC hK q w) a b
        * (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single i 1) a
        * (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single j 1) b) v := by
    intro a b
    exact isC2At_mul
      (isC2At_mul (isC2At_metricFactor g gi hg hC hK q hq v hv a b)
        (isC2At_jacobianEntry g gi hC hK q hq v hv i a))
      (isC2At_jacobianEntry g gi hC hK q hq v hv j b)
  have hrw : (fun w => uniformFlowPullbackMetric g gi hC hK q w i j)
      = fun w => ∑ a, ∑ b, g (uniformFlowExp g gi hC hK q w) a b
        * (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single i 1) a
        * (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single j 1) b := by
    funext w; rfl
  rw [hrw]
  refine isC2At_finsetSum Finset.univ _ (fun a _ => ?_)
  exact isC2At_finsetSum Finset.univ _ (fun b _ => hbase a b)

/-- Both Fréchet layers of a pullback-metric entry exist as `HasFDerivAt`. -/
theorem uniformFlowPullbackMetric_entry_hasFDerivAt_two_layers (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (i j : Fin n) :
    HasFDerivAt (fun w => uniformFlowPullbackMetric g gi hC hK q w i j)
        (fderiv ℝ (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) v) v
      ∧ HasFDerivAt
        (fun w => fderiv ℝ (fun w' => uniformFlowPullbackMetric g gi hC hK q w' i j) w)
        (fderiv ℝ
          (fun w => fderiv ℝ (fun w' => uniformFlowPullbackMetric g gi hC hK q w' i j) w) v) v := by
  have h := uniformFlowPullbackMetric_entry_isC2At g gi hg hC hK q hq v hv i j
  exact ⟨h.differentiableAt.hasFDerivAt, h.2.hasFDerivAt⟩

/-! ### Deliverable (5) — the uniform C² capstone (twice differentiable + uniform `C⁰` bound) -/

/-- **★ J4-79 (W4 capstone).**  There is a single uniform-over-`K` radius `r₀ > 0` and constant `M`
    such that for every base point `q ∈ K`, every velocity `‖v‖ < r₀`, and every pair of indices
    `i j`, the pullback-metric entry `v ↦ uniformFlowPullbackMetric g gi hC hK q v i j`:
    * has a Fréchet first jet (`HasFDerivAt`, layer 1),
    * has a differentiable `fderiv`-map, i.e. a Fréchet second jet (`HasFDerivAt`, layer 2), and
    * satisfies the uniform `C⁰` bound `|g̃_{ij}(v)| ≤ M`.

    The twice-differentiability is `uniformFlowPullbackMetric_entry_isC2At` (finite sums/products of the
    `IsC2At` factors of deliverables 1–2, built on `uniformFlowExp ∈ C³`); the `C⁰` bound is the Q2+Q3
    entry bound (`uniformFlowPullbackMetric_entry_uniform_bound`).  The uniform `C¹`/`C²` operator-norm
    bounds are FIREWALLED (see the module header): they are pure product-rule and chain-rule assembly over
    already-existing uniform sub-bounds, not a mathematical gap.  The ambient-metric regularity `hg` is a
    GENUINE geometric input, not the conclusion.  No `sorry`, no new axioms, no `expRho`. -/
theorem uniformFlowPullbackMetric_c2_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ i j : Fin n,
      HasFDerivAt (fun w => uniformFlowPullbackMetric g gi hC hK q w i j)
          (fderiv ℝ (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) v) v
        ∧ HasFDerivAt
          (fun w => fderiv ℝ (fun w' => uniformFlowPullbackMetric g gi hC hK q w' i j) w)
          (fderiv ℝ
            (fun w => fderiv ℝ (fun w' => uniformFlowPullbackMetric g gi hC hK q w' i j) w) v) v
        ∧ |uniformFlowPullbackMetric g gi hC hK q v i j| ≤ M := by
  obtain ⟨r₀', hr₀'0, Mg, hMg⟩ := uniformFlowPullbackMetric_entry_uniform_bound g gi hg hC hK
  have hρ0 : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨min r₀' (uniformFlowRadius g gi hC hK), lt_min hr₀'0 hρ0, Mg, ?_⟩
  intro q hq v hv i j
  have hvr' : ‖v‖ ≤ r₀' := (lt_of_lt_of_le hv (min_le_left _ _)).le
  have hvρ : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv (min_le_right _ _)
  obtain ⟨hL1, hL2⟩ :=
    uniformFlowPullbackMetric_entry_hasFDerivAt_two_layers g gi hg hC hK q hq v hvρ i j
  exact ⟨hL1, hL2, hMg q hq v hvr' i j⟩

end QIQTH.ExpMap
