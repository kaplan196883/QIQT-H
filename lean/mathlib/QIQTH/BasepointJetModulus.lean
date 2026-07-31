/-
  BasepointJetModulus — J4-29 (bricks 1–3 toward `hunif`): the base-point (`q`-side) MODULUS of the
  velocity 2-jet, for the ABSTRACT confined-tube family, via a two-point Grönwall + a pure-analysis
  Lipschitz→modulus assembly.  Route P (Lipschitz-in-`q`, uniform in the velocity direction ⟹ `hunif`).

  ## Context

  `BasepointSecondJet` (J4-26) reduced the JOINT-continuity input `(J)` of the compact-uniform exp
  second-jet to the SINGLE base-point uniform modulus

    `hunif : ∀ ε>0 ∃ δ>0 ∀ q q'∈K, dist q q'<δ → ∀ v∈B̄(0,r),
        |‖fderiv²(exp_q) v‖ − ‖fderiv²(exp_{q'}) v‖| ≤ ε`.

  This file produces the ODE ENGINE and the pure-analysis ASSEMBLY that turn a q-Lipschitz bound on the
  velocity 2-jet OPERATOR (uniform in the direction `v`) into exactly `hunif`.  It targets the abstract
  family; the weld to the concrete `expMap g gi hC q` through the opaque `Classical.choose` tube is the
  separate next step (J4-30, via `UniformFlowBridge`).

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `linODE_twopoint_diff_bound` — **(brick 1, the genuinely-new ODE engine).**  A pure, geometry-free
    two-point Grönwall for the difference of two solutions of two (possibly different) linear ODEs
    `X₁' = A₁·X₁ + b₁`, `X₂' = A₂·X₂ + b₂` on `[0,1]` with the SAME initial value.  Writing
    `D = X₁ − X₂`, one has `D' = A₁·D + N` with `N = (A₁ − A₂)·X₂ + (b₁ − b₂)`, so with `‖A₁‖ ≤ K`,
    `‖A₁ − A₂‖ ≤ Dcoef`, `‖X₂‖ ≤ Xb`, `‖b₁ − b₂‖ ≤ Dsrc`, Mathlib's inhomogeneous Grönwall
    (`norm_le_gronwallBound_of_norm_deriv_right_le`, `gronwallBound_zero_le_exp`) gives
    `‖X₁ t − X₂ t‖ ≤ (Dcoef·Xb + Dsrc)·exp K`.  Reusable for BOTH homogeneous Jacobi fields (`b = 0`)
    and the inhomogeneous second-order velocity jet (`b` = curvature source).

  * `jacobi_twopoint_diff_bound` — **(brick 1, geodesic specialization).**  For two base geodesics
    `Y₁, Y₂` (integral curves) and two Jacobi fields `J₁` (along `Y₁`), `J₂` (along `Y₂`) with the SAME
    seed at `0`, the endpoint difference is bounded by the base-curve coefficient separation:
    `‖J₁ t − J₂ t‖ ≤ Dcoef·Jb·exp K`, where `Dcoef` bounds `‖DF(Y₁) − DF(Y₂)‖` (the two-point analogue
    of the C² field bound) and `Jb` bounds `‖J₂‖`.  This is the exact "bases `q` vs `q'`" difference —
    the two-point analogue of `jacobiSol_unique` (which is the `q = q'` diagonal, `Dcoef = 0`).

  * `hunif_of_lipschitz` — **(brick 3, pure real analysis).**  For `f : X → Y → ℝ` (`X` pseudometric)
    that is Lipschitz-in-`x` UNIFORMLY in `y ∈ B` with a single modulus `Λ` over `K`
    (`|f x y − f x' y| ≤ Λ·dist x x'`), the `∀ε ∃δ` base-point modulus holds with `δ := ε/(Λ+1)`.

  * `expMap_second_jet_hunif_of_op_lipschitz` — **(route-P capstone: the `hunif` reduction).**  From the
    OPERATOR q-Lipschitz bound `‖fderiv²(exp_q) v − fderiv²(exp_{q'}) v‖ ≤ Λ·dist q q'` (uniform over
    `v ∈ B̄(0,r)`, `q,q' ∈ K`), the reverse triangle inequality `abs_norm_sub_norm_le` plus
    `hunif_of_lipschitz` deliver exactly `hunif` — the argument required by
    `BasepointSecondJet.expMap_second_jet_joint_cont_of_base_uniform`.

  * `expMap_second_jet_joint_cont_of_op_lipschitz`,
    `expMap_common_nondeg_radius_of_op_lipschitz` — chaining the reduction into `BasepointSecondJet`:
    the exp velocity 2-jet's compact joint continuity and the common exp-nondegeneracy radius over `K`
    are now reduced to the single OPERATOR q-Lipschitz input `hoplip` (plus the `(I1)` radius).

  DERIVED vs CARRIED.  DERIVED = the ODE engine (Grönwall), the Jacobi difference bound, the
  Lipschitz→modulus assembly, and the reverse-triangle reduction.  CARRIED genuine inputs: the linear
  ODEs / Jacobi equations along the base geodesics, the coefficient-difference bound `Dcoef` (two-point
  analogue of the C² field bound — a genuine geometric-regularity fact, NOT the conclusion), the field
  norm bounds, and — for the capstone — the operator q-Lipschitz bound `hoplip` (the honest reduced
  input, strictly the OPERATOR difference; the produced `hunif` is on the weaker NORM difference).

  HONEST CHECKPOINT (binding).  This lands the two-point q-Grönwall engine and REDUCES `hunif` (abstract
  family) to the operator q-Lipschitz bound `hoplip`.  It does NOT weld to the concrete `expMap` through
  the opaque `Classical.choose` tube (that is J4-30, via `UniformFlowBridge` `D²exp = D²F`); does NOT
  discharge `hoplip` for the concrete velocity 2-jet (needs the second-order velocity-jet ODE fed into
  `linODE_twopoint_diff_bound` + the uniform-over-`K` `BoundedGeometry` constants); does NOT build
  Raychaudhuri (L3) nor `a₁ = R/6`.
-/
import QIQTH.BasepointSecondJetFDeriv
import QIQTH.BasepointJacobi2
import QIQTH.BasepointFDeriv
import QIQTH.BoundedGeometry
import QIQTH.BasepointSecondJet
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **Brick 1 — the two-point linear-ODE difference Grönwall (geometry-free engine).**
    Let `X₁, X₂` solve two (possibly different) linear ODEs on `[0,1]`:
    `X₁' = A₁·X₁ + b₁` and `X₂' = A₂·X₂ + b₂`, with the SAME initial value `X₁ 0 = X₂ 0`.  If the first
    coefficient is bounded `‖A₁ t‖ ≤ K`, the coefficients differ by `‖A₁ t − A₂ t‖ ≤ Dcoef`, the second
    solution is bounded `‖X₂ t‖ ≤ Xb`, and the sources differ by `‖b₁ t − b₂ t‖ ≤ Dsrc`, then
        `‖X₁ t − X₂ t‖ ≤ (Dcoef·Xb + Dsrc)·exp K`   for all `t ∈ [0,1]`.

    Proof: `D = X₁ − X₂` obeys `D' = A₁·D + N`, `N = (A₁ − A₂)·X₂ + (b₁ − b₂)` (linearity of the two
    ODEs), so `‖D'‖ ≤ K‖D‖ + (Dcoef·Xb + Dsrc)` with `D 0 = 0`; Mathlib's inhomogeneous Grönwall
    (`norm_le_gronwallBound_of_norm_deriv_right_le`, `gronwallBound_zero_le_exp`) closes it. -/
theorem linODE_twopoint_diff_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A₁ A₂ : ℝ → (E →L[ℝ] E)} {X₁ X₂ b₁ b₂ : ℝ → E} {K Dcoef Xb Dsrc : ℝ} (hK0 : 0 ≤ K)
    (hX1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt X₁ (A₁ t (X₁ t) + b₁ t) t)
    (hX2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt X₂ (A₂ t (X₂ t) + b₂ t) t)
    (h0 : X₁ 0 = X₂ 0)
    (hKb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A₁ t‖ ≤ K)
    (hAd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A₁ t - A₂ t‖ ≤ Dcoef)
    (hXb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖X₂ t‖ ≤ Xb)
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖b₁ t - b₂ t‖ ≤ Dsrc) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖X₁ t - X₂ t‖ ≤ (Dcoef * Xb + Dsrc) * Real.exp K := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have hDcoef0 : 0 ≤ Dcoef := le_trans (norm_nonneg _) (hAd 0 h0mem)
  have hXb0 : 0 ≤ Xb := le_trans (norm_nonneg _) (hXb 0 h0mem)
  have hDsrc0 : 0 ≤ Dsrc := le_trans (norm_nonneg _) (hbd 0 h0mem)
  have hCtot0 : 0 ≤ Dcoef * Xb + Dsrc := add_nonneg (mul_nonneg hDcoef0 hXb0) hDsrc0
  -- the residual ODE value `N` and the rewrite of the difference derivative.
  have hval : ∀ t : ℝ,
      (A₁ t (X₁ t) + b₁ t) - (A₂ t (X₂ t) + b₂ t)
        = A₁ t (X₁ t - X₂ t) + ((A₁ t - A₂ t) (X₂ t) + (b₁ t - b₂ t)) := by
    intro t
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ => X₁ τ - X₂ τ)
        (A₁ t (X₁ t - X₂ t) + ((A₁ t - A₂ t) (X₂ t) + (b₁ t - b₂ t))) t := by
    intro t ht
    have h := (hX1 t ht).sub (hX2 t ht)
    rwa [hval t] at h
  have hcont : ContinuousOn (fun τ => X₁ τ - X₂ τ) (Set.Icc 0 1) :=
    fun t ht => ((key t ht).continuousAt).continuousWithinAt
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun τ => X₁ τ - X₂ τ)
    (f' := fun t => A₁ t (X₁ t - X₂ t) + ((A₁ t - A₂ t) (X₂ t) + (b₁ t - b₂ t)))
    (δ := 0) (K := K) (ε := Dcoef * Xb + Dsrc) (a := 0) (b := 1)
    hcont
    (fun x hx => (key x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (by show ‖X₁ 0 - X₂ 0‖ ≤ 0; rw [h0]; simp)
    (by
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      show ‖A₁ x (X₁ x - X₂ x) + ((A₁ x - A₂ x) (X₂ x) + (b₁ x - b₂ x))‖
        ≤ K * ‖X₁ x - X₂ x‖ + (Dcoef * Xb + Dsrc)
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hKb x hx') (norm_nonneg _))
      · refine (norm_add_le _ _).trans (add_le_add ?_ (hbd x hx'))
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hAd x hx') (hXb x hx') (norm_nonneg _) hDcoef0))
  intro t ht
  refine (hmain t ht).trans ?_
  rw [sub_zero]
  exact gronwallBound_zero_le_exp K (Dcoef * Xb + Dsrc) t hK0 hCtot0 ht.1 ht.2

/-- **Brick 1 (geodesic specialization) — two-point difference of Jacobi fields along two base
    geodesics.**  Let `J₁, J₂` be Jacobi fields along the base geodesics `Y₁, Y₂` respectively
    (`Jᵢ' = DF(Yᵢ)·Jᵢ`) with the SAME seed `J₁ 0 = J₂ 0`.  If the Jacobi coefficient of `Y₁` is bounded
    `‖DF(Y₁ τ)‖ ≤ K`, the two coefficient fields differ by `‖DF(Y₁ τ) − DF(Y₂ τ)‖ ≤ Dcoef` (the
    two-point analogue of the C² field bound — a genuine geometric-regularity input, controlled by
    `M₂·dist(Y₁,Y₂)`), and `‖J₂ τ‖ ≤ Jb`, then
        `‖J₁ t − J₂ t‖ ≤ Dcoef·Jb·exp K`.
    This is the base-point (`q` vs `q'`) two-point difference; the `q = q'` diagonal (`Dcoef = 0`) is
    exactly `jacobiSol_unique`.  DERIVED from `linODE_twopoint_diff_bound` (`b = 0`, `Dsrc = 0`). -/
theorem jacobi_twopoint_diff_bound (g gi : Point n → Fin n → Fin n → ℝ)
    {Y₁ Y₂ J₁ J₂ : ℝ → Point n × Point n} {K Dcoef Jb : ℝ} (hK0 : 0 ≤ K)
    (hJ1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J₁ (fderiv ℝ (geodesicField g gi) (Y₁ τ) (J₁ τ)) τ)
    (hJ2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J₂ (fderiv ℝ (geodesicField g gi) (Y₂ τ) (J₂ τ)) τ)
    (h0 : J₁ 0 = J₂ 0)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y₁ τ)‖ ≤ K)
    (hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y₁ τ) - fderiv ℝ (geodesicField g gi) (Y₂ τ)‖ ≤ Dcoef)
    (hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J₂ τ‖ ≤ Jb) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖J₁ t - J₂ t‖ ≤ Dcoef * Jb * Real.exp K := by
  have hbnd := linODE_twopoint_diff_bound (E := Point n × Point n)
    (A₁ := fun τ => fderiv ℝ (geodesicField g gi) (Y₁ τ))
    (A₂ := fun τ => fderiv ℝ (geodesicField g gi) (Y₂ τ))
    (X₁ := J₁) (X₂ := J₂) (b₁ := fun _ => 0) (b₂ := fun _ => 0)
    (K := K) (Dcoef := Dcoef) (Xb := Jb) (Dsrc := 0) hK0
    (fun t ht => by simpa using hJ1 t ht)
    (fun t ht => by simpa using hJ2 t ht)
    h0 hKb hAd hJb (fun t _ => by simp)
  intro t ht
  simpa using hbnd t ht

/-- **Brick 3 — Lipschitz-in-`x` (uniform in the fibre `y`) ⟹ the base-point `∀ε ∃δ` modulus.**
    Pure real analysis: for `f : X → Y → ℝ` (`X` pseudometric) with a single Lipschitz modulus `Λ ≥ 0`
    over `K`, uniform in `y ∈ B` (`|f x y − f x' y| ≤ Λ·dist x x'`), the base-point modulus holds with
    `δ := ε/(Λ+1)`.  This is the assembly that turns the ODE-supplied q-Lipschitz bound of the 2-jet
    into the `hunif` shape. -/
theorem hunif_of_lipschitz {X Y : Type*} [PseudoMetricSpace X]
    (f : X → Y → ℝ) {K : Set X} {B : Set Y} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : ∀ x ∈ K, ∀ x' ∈ K, ∀ y ∈ B, |f x y - f x' y| ≤ Λ * dist x x') :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ x' ∈ K, dist x x' < δ →
      ∀ y ∈ B, |f x y - f x' y| ≤ ε := by
  intro ε hε
  have hden : (0 : ℝ) < Λ + 1 := by linarith
  refine ⟨ε / (Λ + 1), by positivity, fun x hx x' hx' hdist y hy => ?_⟩
  have hstep : Λ * dist x x' ≤ ε := by
    have h1 : Λ * dist x x' ≤ Λ * (ε / (Λ + 1)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hdist) hΛ
    refine h1.trans ?_
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith [hε.le, hΛ, mul_nonneg hΛ hε.le]
  exact (hlip x hx x' hx' y hy).trans hstep

/-- **Route-P capstone — the `hunif` reduction.**  From the OPERATOR q-Lipschitz bound on the exp
    velocity 2-jet `‖fderiv²(exp_q) v − fderiv²(exp_{q'}) v‖ ≤ Λ·dist q q'` (uniform over the direction
    `v ∈ B̄(0,r)`, `q,q' ∈ K`), the reverse triangle inequality `abs_norm_sub_norm_le` bounds the NORM
    difference and `hunif_of_lipschitz` delivers exactly the base-point uniform modulus `hunif` required
    by `BasepointSecondJet.expMap_second_jet_joint_cont_of_base_uniform`.  Honest firewalled reduction:
    the carried input `hoplip` is the strictly-stronger OPERATOR difference; the produced `hunif` is the
    weaker NORM difference. -/
theorem expMap_second_jet_hunif_of_op_lipschitz (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} {r Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hoplip : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r,
      ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v
        - fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q') w) v‖ ≤ Λ * dist q q') :
    ∀ ε > 0, ∃ δ > 0, ∀ q ∈ K, ∀ q' ∈ K, dist q q' < δ →
        ∀ v ∈ Metric.closedBall (0 : Point n) r,
          |‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v‖
            - ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q') w) v‖| ≤ ε := by
  refine hunif_of_lipschitz
    (fun q v => ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v‖)
    (K := K) (B := Metric.closedBall (0 : Point n) r) hΛ (fun q hq q' hq' v hv => ?_)
  exact (abs_norm_sub_norm_le _ _).trans (hoplip q hq q' hq' v hv)

/-- **Chained joint continuity from the operator q-Lipschitz input.**  Feeding the reduced `hunif`
    (`expMap_second_jet_hunif_of_op_lipschitz`) into `expMap_second_jet_joint_cont_of_base_uniform`: the
    exp velocity second-jet operator norm is jointly continuous on `K ×ˢ B̄(0,r)` given only the `(I1)`
    radius (`r < expRho q`) and the operator q-Lipschitz bound `hoplip`. -/
theorem expMap_second_jet_joint_cont_of_op_lipschitz (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} {r Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hr_lt : ∀ q ∈ K, r < expRho g gi hC q)
    (hoplip : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r,
      ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v
        - fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q') w) v‖ ≤ Λ * dist q q') :
    ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p.1) w) p.2‖)
      (K ×ˢ Metric.closedBall (0 : Point n) r) :=
  expMap_second_jet_joint_cont_of_base_uniform g gi hC r hr_lt
    (expMap_second_jet_hunif_of_op_lipschitz g gi hC hΛ hoplip)

/-- **Common exp-nondegeneracy radius over `K` from the operator q-Lipschitz input.**  Chaining the
    reduced `hunif` into `expMap_common_nondeg_radius_of_base_uniform`: a single `ρ₀ > 0` with
    `IsUnit (fderiv ℝ (expMap g gi hC q) v)` for all `q ∈ K`, `‖v‖ < ρ₀`, conditional only on the `(I1)`
    uniform injectivity radius and the operator q-Lipschitz bound `hoplip`. -/
theorem expMap_common_nondeg_radius_of_op_lipschitz (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {r Λ : ℝ} (hr : 0 < r) (hΛ : 0 ≤ Λ)
    (hr_lt : ∀ q ∈ K, r < expRho g gi hC q)
    (hoplip : ∀ q ∈ K, ∀ q' ∈ K, ∀ v ∈ Metric.closedBall (0 : Point n) r,
      ‖fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q) w) v
        - fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC q') w) v‖ ≤ Λ * dist q q') :
    ∃ ρ₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      IsUnit (fderiv ℝ (expMap g gi hC q) v) :=
  expMap_common_nondeg_radius_of_base_uniform g gi hC hK r hr hr_lt
    (expMap_second_jet_hunif_of_op_lipschitz g gi hC hΛ hoplip)

end QIQTH.ExpMap
