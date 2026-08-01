/-
  UniformFlowMetricC2Bound — J4-79b (Brick-A β, W4 FINISHER): the UNIFORM (over `q ∈ K`, `‖v‖ < r₀`)
  `C⁰`+`C¹`+`C²` operator-norm bounds on the entries of the pulled-back metric `g̃` of `uniformFlowExp`.

  ## Context

  J4-79 (`UniformFlowMetricC2`) proved twice-Fréchet-differentiability (`IsC2At`) of every pullback-metric
  entry (via `isC2At_jacobianEntry`, `isC2At_metricFactor`, `uniformFlowPullbackMetric_entry_isC2At`) and a
  UNIFORM `C⁰` entry bound (capstone `uniformFlowPullbackMetric_c2_uniform`).  Its DOCUMENTED firewall was the
  UNIFORM `C¹` and `C²` operator-norm bounds of the entry maps.  THIS FILE DISCHARGES THAT FIREWALL.

  All the constituent uniform sub-bounds already exist from `hC` + `IsCompact K` (+ `hg` for the metric):
  * ambient-metric entry bound `Mg0` (`uniformFlowExp_metric_entry_uniform_bound`, Q1),
  * uniform Jacobian opNorm `Mj` (`uniformFlowExp_fderiv_uniform_bound`, J4-63),
  * uniform Hessian opNorm `M'` (`uniformFlowExp_hessian_opNorm_le`, R3),
  * uniform third-jet opNorm `M₃` (`uniformFlowExp_thirdDeriv_opNorm_le`, W3),
  * uniform `‖Dg‖`, `‖D²g‖` on the fixed compact endpoint tube (extreme-value theorem, Q1 pattern one/two
    derivative-orders up — `uniformFlowExp_tube_continuous_bound` below).

  ## What lands here (DERIVED; no `sorry`, no new axioms, no hyp = conclusion, no `expRho`)

  A small reusable *second-order bound-propagation calculus*, `HasC2BoundAt f v A₀ A₁ A₂` :=
  "`IsC2At f v` AND `|f v| ≤ A₀ ∧ ‖Df v‖ ≤ A₁ ∧ ‖D(Df) v‖ ≤ A₂`", closed under:
  * `hasC2BoundAt_const`, `HasC2BoundAt.add` (bounds add), and
  * `HasC2BoundAt.mul` — the linchpin product rule: bounds `A₀B₀`, `A₀B₁+A₁B₀`, `A₀B₂+2A₁B₁+A₂B₀`
    (from `fderiv_mul` at the `C¹` level and the once-more-differentiated `smul` product rule at `C²`),
  * `HasC2BoundAt.finsetSum` (bounds sum).

  From these plus the sub-bounds:
  * `uniformFlowExp_tube_continuous_bound` — EVT bound of any continuous `φ` at the confined endpoint;
  * `metricFactor_c2Bound` — uniform `C²` bounds on the ambient-metric factor `w ↦ g(F w) a b`
    (`C¹` chain rule; `C²` = the `clm_comp` derivative of the chain-rule formula, bounded via `compL`);
  * `jacobianEntry_c2Bound` — uniform `C²` bounds on the Jacobian entry `w ↦ (DF w)(e_i) a`
    (`C¹` = `evJ ∘ Hess`, `C²` = `Ψ ∘ Third` with `‖evJ‖, ‖Ψ‖ ≤ 1`);
  * `uniformFlowPullbackMetric_entry_hasC2BoundAt` — assembly: the entry is the finite double sum of triple
    products, `HasC2BoundAt.mul` twice + `HasC2BoundAt.finsetSum`.
  * `uniformFlowPullbackMetric_c2_uniform_full` (**★ J4-79b capstone, W4 COMPLETE**) — ONE uniform-over-`K`
    radius `r₀ > 0` and constant `M` s.t. for every `q ∈ K`, `‖v‖ < r₀`, `i j`, the entry has both
    `HasFDerivAt` layers AND `|g̃_{ij}(v)| ≤ M ∧ ‖D g̃_{ij}(v)‖ ≤ M ∧ ‖D(D g̃_{ij})(v)‖ ≤ M`.
    Hypotheses ONLY `hg` (genuine metric regularity) + `hC` + `IsCompact K`.

  NO firewall remains at the entry level.  This file does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.
-/
import QIQTH.UniformFlowMetricC2
import QIQTH.UniformFlowHessianDiag
import QIQTH.UniformFlowThirdUncond
import QIQTH.UniformFlowJacobianBound
import Mathlib

open Filter
open QIQTH.Curvature QIQTH.PullbackMetric
open scoped Topology BigOperators

namespace QIQTH.ExpMap

set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 4

variable {n : ℕ}

/-! ### A reusable EVT bound at the confined uniform-flow endpoint -/

/-- **The uniform tube bound.**  For any continuous scalar `φ` there is a single constant `G ≥ 0` such
    that `|φ (uniformFlowExp q v)| ≤ G` for every `q ∈ K` and `‖v‖ ≤ ρ_K`.  Route (the Q1 pattern):
    the endpoint-displacement bound (J4-62) confines `uniformFlowExp q v` to a fixed compact tube
    `T = closedBall p₀ (R+M)`, on which the continuous `φ` is bounded by the extreme-value theorem. -/
theorem uniformFlowExp_tube_continuous_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (φ : Point n → ℝ) (hφ : Continuous φ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ q ∈ K, ∀ v : Point n,
      ‖v‖ ≤ uniformFlowRadius g gi hC hK →
      |φ (uniformFlowExp g gi hC hK q v)| ≤ G := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, le_refl 0, ?_⟩
    intro q hq; rw [hKe] at hq; exact absurd hq (Set.notMem_empty q)
  obtain ⟨M, hM0, hMbound⟩ := uniformFlowExp_displacement_uniform_bound g gi hC hK
  obtain ⟨p₀, _hp₀⟩ := hKne
  obtain ⟨R, hRsub⟩ := hK.isBounded.subset_closedBall p₀
  set T : Set (Point n) := Metric.closedBall p₀ (R + M) with hTdef
  have hTcompact : IsCompact T := isCompact_closedBall _ _
  obtain ⟨C, hCb⟩ := hTcompact.exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq v hv
  have hxT : uniformFlowExp g gi hC hK q v ∈ T := by
    rw [hTdef, Metric.mem_closedBall]
    have hdisp : ‖uniformFlowExp g gi hC hK q v - q‖ ≤ M := hMbound q hq v hv
    have hqp : dist q p₀ ≤ R := Metric.mem_closedBall.mp (hRsub hq)
    calc dist (uniformFlowExp g gi hC hK q v) p₀
        ≤ dist (uniformFlowExp g gi hC hK q v) q + dist q p₀ := dist_triangle _ _ _
      _ ≤ M + R := add_le_add (by rw [dist_eq_norm]; exact hdisp) hqp
      _ = R + M := by ring
  calc |φ (uniformFlowExp g gi hC hK q v)|
      = ‖φ (uniformFlowExp g gi hC hK q v)‖ := (Real.norm_eq_abs _).symm
    _ ≤ C := hCb _ hxT
    _ ≤ max C 0 := le_max_left _ _

/-! ### The second-order bound-propagation calculus -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `HasC2BoundAt f v A₀ A₁ A₂`: `f` is `IsC2At` at `v` with `C⁰/C¹/C²` operator-norm bounds
    `A₀, A₁, A₂` on `|f|`, `‖fderiv f‖`, `‖fderiv (fderiv-map)‖`. -/
def HasC2BoundAt (f : X → ℝ) (v : X) (A₀ A₁ A₂ : ℝ) : Prop :=
  IsC2At f v ∧ |f v| ≤ A₀ ∧ ‖fderiv ℝ f v‖ ≤ A₁ ∧
    ‖fderiv ℝ (fun w => fderiv ℝ f w) v‖ ≤ A₂

/-- Constants have `HasC2BoundAt` with `C¹`/`C²` bound `0`. -/
theorem hasC2BoundAt_const (c : ℝ) (v : X) : HasC2BoundAt (fun _ : X => c) v |c| 0 0 := by
  refine ⟨isC2At_const c, le_refl _, ?_, ?_⟩
  · have h1 : fderiv ℝ (fun _ : X => c) v = 0 := by simp
    rw [h1]; exact norm_zero.le
  · have h0 : (fun w : X => fderiv ℝ (fun _ : X => c) w) = fun _ => (0 : X →L[ℝ] ℝ) := by
      funext w; simp
    rw [h0]
    have h2 : fderiv ℝ (fun _ : X => (0 : X →L[ℝ] ℝ)) v = (0 : X →L[ℝ] X →L[ℝ] ℝ) := by simp
    rw [h2]; exact (norm_zero (E := X →L[ℝ] X →L[ℝ] ℝ)).le

/-- `HasC2BoundAt` is closed under addition (bounds add). -/
theorem HasC2BoundAt.add {f h : X → ℝ} {v : X} {A₀ A₁ A₂ B₀ B₁ B₂ : ℝ}
    (hf : HasC2BoundAt f v A₀ A₁ A₂) (hh : HasC2BoundAt h v B₀ B₁ B₂) :
    HasC2BoundAt (fun w => f w + h w) v (A₀ + B₀) (A₁ + B₁) (A₂ + B₂) := by
  obtain ⟨hfC, hf0, hf1, hf2⟩ := hf
  obtain ⟨hhC, hh0, hh1, hh2⟩ := hh
  refine ⟨isC2At_add hfC hhC, ?_, ?_, ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add hf0 hh0)
  · have hfda : fderiv ℝ (fun w => f w + h w) v = fderiv ℝ f v + fderiv ℝ h v :=
      fderiv_add hfC.differentiableAt hhC.differentiableAt
    rw [hfda]
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add hf1 hh1)
  · have heq : (fun w => fderiv ℝ (fun x => f x + h x) w) =ᶠ[𝓝 v]
        (fun w => fderiv ℝ f w + fderiv ℝ h w) :=
      (hfC.1.and hhC.1).mono fun w hw => fderiv_add hw.1 hw.2
    rw [heq.fderiv_eq]
    have hHF : fderiv ℝ (fun w => fderiv ℝ f w + fderiv ℝ h w) v
        = fderiv ℝ (fun w => fderiv ℝ f w) v + fderiv ℝ (fun w => fderiv ℝ h w) v :=
      (hfC.2.hasFDerivAt.add hhC.2.hasFDerivAt).fderiv
    rw [hHF]
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add hf2 hh2)

/-- `HasC2BoundAt` is closed under multiplication with the second-order Leibniz bounds
    `A₀B₀`, `A₀B₁+A₁B₀`, `A₀B₂+2A₁B₁+A₂B₀`. -/
theorem HasC2BoundAt.mul {f h : X → ℝ} {v : X} {A₀ A₁ A₂ B₀ B₁ B₂ : ℝ}
    (hf : HasC2BoundAt f v A₀ A₁ A₂) (hh : HasC2BoundAt h v B₀ B₁ B₂) :
    HasC2BoundAt (fun w => f w * h w) v (A₀ * B₀) (A₀ * B₁ + A₁ * B₀)
      (A₀ * B₂ + 2 * A₁ * B₁ + A₂ * B₀) := by
  obtain ⟨hfC, hf0, hf1, hf2⟩ := hf
  obtain ⟨hhC, hh0, hh1, hh2⟩ := hh
  have hA0 : 0 ≤ A₀ := (abs_nonneg _).trans hf0
  have hB0 : 0 ≤ B₀ := (abs_nonneg _).trans hh0
  have hA1 : 0 ≤ A₁ := (norm_nonneg _).trans hf1
  have hB1 : 0 ≤ B₁ := (norm_nonneg _).trans hh1
  refine ⟨isC2At_mul hfC hhC, ?_, ?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul hf0 hh0 (abs_nonneg _) hA0
  · have hfd : fderiv ℝ (fun w => f w * h w) v = f v • fderiv ℝ h v + h v • fderiv ℝ f v :=
      fderiv_mul hfC.differentiableAt hhC.differentiableAt
    rw [hfd]
    refine (ContinuousLinearMap.opNorm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine add_le_add ?_ ?_
    · exact mul_le_mul hf0 hh1 (norm_nonneg _) hA0
    · rw [mul_comm A₁ B₀]; exact mul_le_mul hh0 hf1 (norm_nonneg _) hB0
  · have heq : (fun w => fderiv ℝ (fun x => f x * h x) w) =ᶠ[𝓝 v]
        (fun w => f w • fderiv ℝ h w + h w • fderiv ℝ f w) :=
      (hfC.1.and hhC.1).mono fun w hw => fderiv_mul hw.1 hw.2
    rw [heq.fderiv_eq]
    have hf' : HasFDerivAt f (fderiv ℝ f v) v := hfC.differentiableAt.hasFDerivAt
    have hh' : HasFDerivAt h (fderiv ℝ h v) v := hhC.differentiableAt.hasFDerivAt
    have hDh' : HasFDerivAt (fun w => fderiv ℝ h w) (fderiv ℝ (fun w => fderiv ℝ h w) v) v :=
      hhC.2.hasFDerivAt
    have hDf' : HasFDerivAt (fun w => fderiv ℝ f w) (fderiv ℝ (fun w => fderiv ℝ f w) v) v :=
      hfC.2.hasFDerivAt
    have hfe : fderiv ℝ (fun w => f w • fderiv ℝ h w + h w • fderiv ℝ f w) v
        = (f v • fderiv ℝ (fun w => fderiv ℝ h w) v + (fderiv ℝ f v).smulRight (fderiv ℝ h v))
          + (h v • fderiv ℝ (fun w => fderiv ℝ f w) v + (fderiv ℝ h v).smulRight (fderiv ℝ f v)) :=
      ((hf'.smul hDh').add (hh'.smul hDf')).fderiv
    rw [hfe]
    have hbT1 : ‖f v • fderiv ℝ (fun w => fderiv ℝ h w) v + (fderiv ℝ f v).smulRight (fderiv ℝ h v)‖
        ≤ A₀ * B₂ + A₁ * B₁ := by
      refine (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul hf0 hh2 (norm_nonneg _) hA0
      · rw [ContinuousLinearMap.norm_smulRight_apply]; exact mul_le_mul hf1 hh1 (norm_nonneg _) hA1
    have hbT2 : ‖h v • fderiv ℝ (fun w => fderiv ℝ f w) v + (fderiv ℝ h v).smulRight (fderiv ℝ f v)‖
        ≤ B₀ * A₂ + B₁ * A₁ := by
      refine (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul hh0 hf2 (norm_nonneg _) hB0
      · rw [ContinuousLinearMap.norm_smulRight_apply]; exact mul_le_mul hh1 hf1 (norm_nonneg _) hB1
    have hsum_eq : (A₀ * B₂ + A₁ * B₁) + (B₀ * A₂ + B₁ * A₁)
        = A₀ * B₂ + 2 * A₁ * B₁ + A₂ * B₀ := by ring
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans
      ((add_le_add hbT1 hbT2).trans (le_of_eq hsum_eq))

/-- `HasC2BoundAt` is closed under finite sums (bounds sum). -/
theorem HasC2BoundAt.finsetSum {ι : Type*} {v : X} (s : Finset ι) (F : ι → X → ℝ)
    (A B C : ι → ℝ) :
    (∀ i ∈ s, HasC2BoundAt (F i) v (A i) (B i) (C i)) →
      HasC2BoundAt (fun w => ∑ i ∈ s, F i w) v (∑ i ∈ s, A i) (∑ i ∈ s, B i) (∑ i ∈ s, C i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    simpa using hasC2BoundAt_const (0 : ℝ) v
  · intro a s ha ih hins
    have hcons : (fun w => ∑ i ∈ insert a s, F i w) = fun w => F a w + ∑ i ∈ s, F i w := by
      funext w; rw [Finset.sum_insert ha]
    rw [hcons, Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hins a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hins i (Finset.mem_insert_of_mem hi)))

/-! ### B2 — the per-factor uniform `C²` bounds -/

/-- **Uniform `C²` bounds on the ambient-metric factor** `w ↦ g (uniformFlowExp q w) a b`, over `q ∈ K`,
    `‖v‖ < r₀`, all `a b`.  `C⁰` = Q1; `C¹` = chain rule `(Dg ∘ F) · DF`; `C²` = the `clm_comp`
    derivative of the chain-rule formula, its two summands bounded via `compL`/`flip` (norm `≤ ‖·‖`). -/
theorem metricFactor_c2Bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ Cm0 Cm1 Cm2 : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ a b : Fin n,
      HasC2BoundAt (fun w => g (uniformFlowExp g gi hC hK q w) a b) v Cm0 Cm1 Cm2 := by
  obtain ⟨Mg0, hMg0nn, hMg0⟩ := uniformFlowExp_metric_entry_uniform_bound g gi hg hC hK
  obtain ⟨Mj, hMj⟩ := uniformFlowExp_fderiv_uniform_bound g gi hC hK
  set Mj' : ℝ := max Mj 0 with hMj'def
  have hMj'nn : 0 ≤ Mj' := le_max_right _ _
  obtain ⟨rH, hrH0, hrHρ, M', hM'⟩ := uniformFlowExp_hessian_opNorm_le g gi hC hK
  set M'' : ℝ := max M' 0 with hM''def
  have hM''nn : 0 ≤ M'' := le_max_right _ _
  have hφ1cont : Continuous (fun x : Point n => ∑ a, ∑ b, ‖fderiv ℝ (fun y => g y a b) x‖) := by
    refine continuous_finsetSum _ (fun a _ => ?_)
    refine continuous_finsetSum _ (fun b _ => ?_)
    exact (((hg a b).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous).norm
  obtain ⟨G₁, hG₁nn, hG₁⟩ := uniformFlowExp_tube_continuous_bound g gi hC hK _ hφ1cont
  have hφ2cont : Continuous
      (fun x : Point n => ∑ a, ∑ b, ‖fderiv ℝ (fun w => fderiv ℝ (fun y => g y a b) w) x‖) := by
    refine continuous_finsetSum _ (fun a _ => ?_)
    refine continuous_finsetSum _ (fun b _ => ?_)
    exact ((((hg a b).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).fderiv_right
      (m := (⊤ : WithTop ℕ∞)) le_top).continuous).norm
  obtain ⟨G₂, hG₂nn, hG₂⟩ := uniformFlowExp_tube_continuous_bound g gi hC hK _ hφ2cont
  refine ⟨rH, hrH0, Mg0, G₁ * Mj', G₁ * M'' + Mj' * (G₂ * Mj'), ?_⟩
  intro q hq v hv a b
  have hvρ : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv hrHρ
  have hvρle : ‖v‖ ≤ uniformFlowRadius g gi hC hK := hvρ.le
  set F := uniformFlowExp g gi hC hK q with hFdef
  have hFdiff : DifferentiableAt ℝ F v := by
    obtain ⟨L, hL⟩ := uniformFlowExp_hasFDerivAt g gi hC hK q hq v hvρ
    exact hL.differentiableAt
  have hgabDiff : Differentiable ℝ (fun y => g y a b) := (hg a b).differentiable (by simp)
  have hDgabDiff : Differentiable ℝ (fun w => fderiv ℝ (fun y => g y a b) w) :=
    ((hg a b).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).differentiable (by simp)
  obtain ⟨B₂, hB₂⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq v hvρ
  rw [← hFdef] at hB₂
  have hMjv : ‖fderiv ℝ F v‖ ≤ Mj' := (hMj q hq v hvρ).trans (le_max_left _ _)
  have hB₂bd : ‖B₂‖ ≤ M'' := by
    rw [← hB₂.fderiv]; exact (hM' q hq v hv).trans (le_max_left _ _)
  have hG₁ab : ‖fderiv ℝ (fun y => g y a b) (F v)‖ ≤ G₁ := by
    have hsum : ‖fderiv ℝ (fun y => g y a b) (F v)‖
        ≤ ∑ a', ∑ b', ‖fderiv ℝ (fun y => g y a' b') (F v)‖ := by
      refine le_trans (Finset.single_le_sum
        (f := fun b' => ‖fderiv ℝ (fun y => g y a b') (F v)‖)
        (fun i _ => norm_nonneg _) (Finset.mem_univ b)) ?_
      exact Finset.single_le_sum
        (f := fun a' => ∑ b', ‖fderiv ℝ (fun y => g y a' b') (F v)‖)
        (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    exact hsum.trans ((le_abs_self _).trans (hG₁ q hq v hvρle))
  have hG₂ab : ‖fderiv ℝ (fun w => fderiv ℝ (fun y => g y a b) w) (F v)‖ ≤ G₂ := by
    have hsum : ‖fderiv ℝ (fun w => fderiv ℝ (fun y => g y a b) w) (F v)‖
        ≤ ∑ a', ∑ b', ‖fderiv ℝ (fun w => fderiv ℝ (fun y => g y a' b') w) (F v)‖ := by
      refine le_trans (Finset.single_le_sum
        (f := fun b' => ‖fderiv ℝ (fun w => fderiv ℝ (fun y => g y a b') w) (F v)‖)
        (fun i _ => by positivity) (Finset.mem_univ b)) ?_
      exact Finset.single_le_sum
        (f := fun a' => ∑ b', ‖fderiv ℝ (fun w => fderiv ℝ (fun y => g y a' b') w) (F v)‖)
        (fun i _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ a)
    exact hsum.trans ((le_abs_self _).trans (hG₂ q hq v hvρle))
  have hFdiffEv : ∀ᶠ w in 𝓝 v, DifferentiableAt ℝ F w := by
    have hball : Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) ∈ 𝓝 v :=
      Metric.isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; exact hvρ)
    refine Filter.eventually_of_mem hball (fun w hw => ?_)
    have hw' : ‖w‖ < uniformFlowRadius g gi hC hK := by rw [← mem_ball_zero_iff]; exact hw
    obtain ⟨L, hL⟩ := uniformFlowExp_hasFDerivAt g gi hC hK q hq w hw'
    exact hL.differentiableAt
  refine ⟨isC2At_metricFactor g gi hg hC hK q hq v hvρ a b, ?_, ?_, ?_⟩
  · show |g (F v) a b| ≤ Mg0
    exact hMg0 q hq v hvρle a b
  · -- C¹ : ‖(Dg (F v)) ∘L (DF v)‖ ≤ G₁ * Mj'
    have hcomp1 : HasFDerivAt (fun w => g (F w) a b)
        ((fderiv ℝ (fun y => g y a b) (F v)).comp (fderiv ℝ F v)) v :=
      (hgabDiff (F v)).hasFDerivAt.comp v hFdiff.hasFDerivAt
    rw [hcomp1.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hG₁ab hMjv (norm_nonneg _) hG₁nn)
  · -- C² : the clm_comp derivative, bounded via compL/flip
    have heqm : (fun w => fderiv ℝ (fun w' => g (F w') a b) w) =ᶠ[𝓝 v]
        (fun w => (fderiv ℝ (fun y => g y a b) (F w)).comp (fderiv ℝ F w)) := by
      refine hFdiffEv.mono (fun w hw => ?_)
      have hcomp : HasFDerivAt (fun w' => g (F w') a b)
          ((fderiv ℝ (fun y => g y a b) (F w)).comp (fderiv ℝ F w)) w :=
        (hgabDiff (F w)).hasFDerivAt.comp w hw.hasFDerivAt
      exact hcomp.fderiv
    rw [heqm.fderiv_eq]
    have hA : HasFDerivAt (fun w => fderiv ℝ (fun y => g y a b) (F w))
        ((fderiv ℝ (fun w => fderiv ℝ (fun y => g y a b) w) (F v)).comp (fderiv ℝ F v)) v :=
      (hDgabDiff (F v)).hasFDerivAt.comp v hFdiff.hasFDerivAt
    rw [(hA.clm_comp hB₂).fderiv]
    refine le_trans (ContinuousLinearMap.opNorm_add_le _ _) ?_
    refine add_le_add ?_ ?_
    · -- ‖(compL (Dg)).comp B₂‖ ≤ G₁ * M''
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      refine mul_le_mul ?_ hB₂bd (norm_nonneg _) hG₁nn
      refine le_trans (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun H => ?_)) hG₁ab
      rw [ContinuousLinearMap.compL_apply]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    · -- ‖(flip (DF)).comp ((D²g)∘L(DF))‖ ≤ Mj' * (G₂ * Mj')
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      refine mul_le_mul ?_ ?_ (norm_nonneg _) hMj'nn
      · refine le_trans (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun f => ?_)) hMjv
        rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (le_of_eq (mul_comm _ _))
      · refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        exact mul_le_mul hG₂ab hMjv (norm_nonneg _) hG₂nn

/-- **Uniform `C²` bounds on the Jacobian entry** `w ↦ (fderiv (uniformFlowExp q) w) e_i a`, over
    `q ∈ K`, `‖v‖ < r₀`, all `i a`.  `Je = evJ ∘ Jac` with `evJ = proj_a ∘L apply_{e_i}` (`‖evJ‖ ≤ 1`);
    `C⁰ ≤ Mj`; `C¹ = evJ ∘L Hess` (`≤ M'`); `C² = Ψ ∘L Third` with `Ψ = compL evJ` (`‖Ψ‖ ≤ 1`, `≤ M₃`). -/
theorem jacobianEntry_c2Bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ Cj0 Cj1 Cj2 : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ i a : Fin n,
      HasC2BoundAt (fun w => (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single i 1) a)
        v Cj0 Cj1 Cj2 := by
  obtain ⟨Mj, hMj⟩ := uniformFlowExp_fderiv_uniform_bound g gi hC hK
  set Mj' : ℝ := max Mj 0 with hMj'def
  obtain ⟨rH, hrH0, hrHρ, M', hM'⟩ := uniformFlowExp_hessian_opNorm_le g gi hC hK
  set M'' : ℝ := max M' 0 with hM''def
  obtain ⟨rT, hrT0, M₃, hM₃⟩ := uniformFlowExp_thirdDeriv_opNorm_le g gi hC hK
  set M₃' : ℝ := max M₃ 0 with hM₃'def
  refine ⟨min rH rT, lt_min hrH0 hrT0, Mj', M'', M₃', ?_⟩
  intro q hq v hv i a
  have hvrH : ‖v‖ < rH := lt_of_lt_of_le hv (min_le_left _ _)
  have hvrT : ‖v‖ < rT := lt_of_lt_of_le hv (min_le_right _ _)
  have hvρ : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hvrH hrHρ
  classical
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
  have hevJnorm : ‖evJ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun L => ?_)
    rw [hevJapp, one_mul]
    calc ‖L (Pi.single i 1) a‖ ≤ ‖L (Pi.single i 1)‖ := norm_le_pi_norm _ a
      _ ≤ ‖L‖ * ‖(Pi.single i 1 : Point n)‖ := L.le_opNorm _
      _ = ‖L‖ := by rw [Pi.norm_single, norm_one, mul_one]
  obtain ⟨B₂, hB₂⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq v hvρ
  rw [← hFdef] at hB₂
  have hB₂bd : ‖B₂‖ ≤ M'' := by
    rw [← hB₂.fderiv]; exact (hM' q hq v hvrH).trans (le_max_left _ _)
  have hball : Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) ∈ 𝓝 v :=
    Metric.isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; exact hvρ)
  have hJacDiff : ∀ᶠ w in 𝓝 v, DifferentiableAt ℝ Jac w := by
    refine Filter.eventually_of_mem hball (fun w hw => ?_)
    have hw' : ‖w‖ < uniformFlowRadius g gi hC hK := by rw [← mem_ball_zero_iff]; exact hw
    obtain ⟨B, hB⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq w hw'
    exact hB.differentiableAt
  refine ⟨isC2At_jacobianEntry g gi hC hK q hq v hvρ i a, ?_, ?_, ?_⟩
  · show |(fderiv ℝ F v) (Pi.single i 1) a| ≤ Mj'
    calc |(fderiv ℝ F v) (Pi.single i 1) a|
        = ‖(fderiv ℝ F v) (Pi.single i 1) a‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(fderiv ℝ F v) (Pi.single i 1)‖ := norm_le_pi_norm _ a
      _ ≤ ‖fderiv ℝ F v‖ * ‖(Pi.single i 1 : Point n)‖ := (fderiv ℝ F v).le_opNorm _
      _ = ‖fderiv ℝ F v‖ := by rw [Pi.norm_single, norm_one, mul_one]
      _ ≤ Mj := hMj q hq v hvρ
      _ ≤ Mj' := le_max_left _ _
  · -- C¹ : ‖evJ ∘L B₂‖ ≤ M''
    have hC1id : fderiv ℝ (fun w => (fderiv ℝ F w) (Pi.single i 1) a) v = evJ.comp B₂ := by
      have hcomp : HasFDerivAt (fun w => evJ (Jac w)) (evJ.comp B₂) v :=
        evJ.hasFDerivAt.comp v hB₂
      rw [hval]; exact hcomp.fderiv
    rw [hC1id]
    calc ‖evJ.comp B₂‖ ≤ ‖evJ‖ * ‖B₂‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * M'' := mul_le_mul hevJnorm hB₂bd (by positivity) zero_le_one
      _ = M'' := one_mul _
  · -- C² : ‖Ψ ∘L Third‖ ≤ M₃'
    have heq : (fun w => fderiv ℝ (fun w' => (fderiv ℝ F w') (Pi.single i 1) a) w) =ᶠ[𝓝 v]
        (fun w => evJ.comp (fderiv ℝ Jac w)) := by
      refine hJacDiff.mono (fun w hwJac => ?_)
      have hcomp : HasFDerivAt (fun w' => evJ (Jac w')) (evJ.comp (fderiv ℝ Jac w)) w :=
        evJ.hasFDerivAt.comp w hwJac.hasFDerivAt
      rw [hval]; exact hcomp.fderiv
    rw [heq.fderiv_eq]
    have hHessMap : DifferentiableAt ℝ (fun w => fderiv ℝ Jac w) v :=
      uniformFlowExp_hessianMap_differentiableAt g gi hC hK q hq v hvρ
    have hc : HasFDerivAt (fun _ : Point n => evJ)
        (0 : Point n →L[ℝ] ((Point n →L[ℝ] Point n) →L[ℝ] ℝ)) v := hasFDerivAt_const _ _
    have hcomp2 : HasFDerivAt (fun w => evJ.comp (fderiv ℝ Jac w)) _ v :=
      hc.clm_comp hHessMap.hasFDerivAt
    rw [hcomp2.fderiv, ContinuousLinearMap.comp_zero, add_zero]
    have hM₃v : ‖fderiv ℝ (fun w => fderiv ℝ Jac w) v‖ ≤ M₃' :=
      (hM₃ q hq v hvrT).trans (le_max_left _ _)
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    refine (mul_le_mul ?_ hM₃v (by positivity) zero_le_one).trans (le_of_eq (one_mul _))
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun H => ?_)
    rw [ContinuousLinearMap.compL_apply, one_mul]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by have := mul_le_mul_of_nonneg_right hevJnorm (norm_nonneg H); rwa [one_mul] at this)

/-! ### B3 — assembly: the pullback-metric entry has uniform `C²` bounds -/

/-- **Uniform `C²` bounds on the pullback-metric entry.**  `g̃_{ij} = ∑_{a,b} g_{ab}·J_{ai}·J_{bj}` is the
    finite double sum of triple products of the `HasC2BoundAt` factors of `metricFactor_c2Bound` and
    `jacobianEntry_c2Bound`; `HasC2BoundAt.mul` (twice per term) + `HasC2BoundAt.finsetSum` assemble it. -/
theorem uniformFlowPullbackMetric_entry_hasC2BoundAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∃ M0 M1 M2 : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ i j : Fin n,
      HasC2BoundAt (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) v M0 M1 M2 := by
  obtain ⟨rM, hrM0, Cm0, Cm1, Cm2, hM⟩ := metricFactor_c2Bound g gi hg hC hK
  obtain ⟨rJ, hrJ0, Cj0, Cj1, Cj2, hJ⟩ := jacobianEntry_c2Bound g gi hC hK
  set P1_0 := Cm0 * Cj0 with hP1_0
  set P1_1 := Cm0 * Cj1 + Cm1 * Cj0 with hP1_1
  set P1_2 := Cm0 * Cj2 + 2 * Cm1 * Cj1 + Cm2 * Cj0 with hP1_2
  set T0 := P1_0 * Cj0 with hT0
  set T1 := P1_0 * Cj1 + P1_1 * Cj0 with hT1
  set T2 := P1_0 * Cj2 + 2 * P1_1 * Cj1 + P1_2 * Cj0 with hT2
  refine ⟨min rM rJ, lt_min hrM0 hrJ0,
    ∑ _a : Fin n, ∑ _b : Fin n, T0, ∑ _a : Fin n, ∑ _b : Fin n, T1,
    ∑ _a : Fin n, ∑ _b : Fin n, T2, ?_⟩
  intro q hq v hv i j
  have hvM : ‖v‖ < rM := lt_of_lt_of_le hv (min_le_left _ _)
  have hvJ : ‖v‖ < rJ := lt_of_lt_of_le hv (min_le_right _ _)
  have hrw : (fun w => uniformFlowPullbackMetric g gi hC hK q w i j)
      = fun w => ∑ a, ∑ b, g (uniformFlowExp g gi hC hK q w) a b
        * (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single i 1) a
        * (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single j 1) b := by
    funext w; rfl
  rw [hrw]
  refine HasC2BoundAt.finsetSum Finset.univ
    (fun a => fun w => ∑ b : Fin n, g (uniformFlowExp g gi hC hK q w) a b
        * (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single i 1) a
        * (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single j 1) b)
    (fun _ => ∑ _b : Fin n, T0) (fun _ => ∑ _b : Fin n, T1) (fun _ => ∑ _b : Fin n, T2)
    (fun a _ => ?_)
  refine HasC2BoundAt.finsetSum Finset.univ
    (fun b => fun w => g (uniformFlowExp g gi hC hK q w) a b
        * (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single i 1) a
        * (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single j 1) b)
    (fun _ => T0) (fun _ => T1) (fun _ => T2) (fun b _ => ?_)
  exact ((hM q hq v hvM a b).mul (hJ q hq v hvJ i a)).mul (hJ q hq v hvJ j b)

/-! ### B4 — the W4 capstone -/

/-- **★ J4-79b (W4 FINISHER).**  ONE uniform-over-`K` radius `r₀ > 0` and constant `M` such that for every
    base point `q ∈ K`, velocity `‖v‖ < r₀`, and indices `i j`, the pullback-metric entry
    `w ↦ uniformFlowPullbackMetric g gi hC hK q w i j`:
    * has a Fréchet first jet (`HasFDerivAt`, layer 1),
    * has a differentiable `fderiv`-map, i.e. a Fréchet second jet (`HasFDerivAt`, layer 2), and
    * satisfies the UNIFORM `C⁰`, `C¹`, `C²` operator-norm bounds
        `|g̃_{ij}(v)| ≤ M`, `‖D g̃_{ij}(v)‖ ≤ M`, `‖D(D g̃_{ij})(v)‖ ≤ M`.

    This discharges J4-79's documented `C¹`/`C²` firewall in full.  Hypotheses ONLY `hg` (genuine ambient
    metric regularity) + `hC` + `IsCompact K`.  No `sorry`, no new axioms, no `expRho`. -/
theorem uniformFlowPullbackMetric_c2_uniform_full (g gi : Point n → Fin n → Fin n → ℝ)
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
        ∧ |uniformFlowPullbackMetric g gi hC hK q v i j| ≤ M
        ∧ ‖fderiv ℝ (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) v‖ ≤ M
        ∧ ‖fderiv ℝ (fun w => fderiv ℝ (fun w' => uniformFlowPullbackMetric g gi hC hK q w' i j) w) v‖
            ≤ M := by
  obtain ⟨r₀, hr₀0, M0, M1, M2, hEntry⟩ :=
    uniformFlowPullbackMetric_entry_hasC2BoundAt g gi hg hC hK
  refine ⟨r₀, hr₀0, max M0 (max M1 M2), ?_⟩
  intro q hq v hv i j
  obtain ⟨hIsC2, hC0, hCd1, hCd2⟩ := hEntry q hq v hv i j
  refine ⟨hIsC2.differentiableAt.hasFDerivAt, hIsC2.2.hasFDerivAt, ?_, ?_, ?_⟩
  · exact hC0.trans (le_max_left _ _)
  · exact hCd1.trans ((le_max_left M1 M2).trans (le_max_right _ _))
  · exact hCd2.trans ((le_max_right M1 M2).trans (le_max_right _ _))

end QIQTH.ExpMap
