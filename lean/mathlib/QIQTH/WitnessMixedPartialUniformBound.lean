/-
  WitnessMixedPartialUniformBound — Task E (plan v3, `tranquil-stargazing-fox.md`): assemble a UNIFORM
  bound on the base-slot regularity of the witness — valid throughout a CONVEX NEIGHBOURHOOD of `q = 0`,
  not merely at the single point — by combining Task A (`UniformFlowExpBasepointJacobiExplicit`, the
  per-`q` base-slot Jacobi field + Fréchet derivative) with Task B (`InverseChartSecondJetODEBridge`, the
  base-parameter ODE of the inverse chart's second field-jet) via a COMPACTNESS/BOUNDEDNESS argument.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is the
  q-block boundedness ingredient of the joint-Lipschitz route to `hCConv` (plan v3, Task E).  No `sorry`,
  no new axioms, no vacuous / unsatisfiable hypotheses, no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY A BOUNDEDNESS (NOT SMOOTHNESS) ARGUMENT WORKS.

  The joint-Lipschitz route to `hCConv` (plan v3, Task F) block-chains the mean-value inequality across a
  CONVEX product neighbourhood.  For the q-block it needs only that the base-slot partial derivative of
  the witness is UNIFORMLY BOUNDED over a convex neighbourhood of `q = 0` — **not** continuous in `q`,
  **not** coherent across base points.  This is exactly what the `.choose`-incoherence firewall of the
  inverse chart does NOT block (it blocks CONTINUITY of the third partials in `q`, never per-point
  existence + a uniform bound).

  The uniformity comes for free from a **GRÖNWALL** estimate, NOT from any continuity in `q`.  Task A's
  per-`q` base-slot Jacobi field `J_q` solves the linear ODE `J' = DF(tube_q τ)·J`, seed `J_q 0 = (u,0)`.
  If the base points `q` range over a FIXED convex compact neighbourhood `N` of `0`, ALL the geodesic
  tubes `uniformFlowTube q v · ` stay inside ONE fixed compact phase ball `S₀` (uniform confinement), so
  the field generator `DF` is bounded by ONE constant `Kf` on `S₀`, UNIFORMLY over `q ∈ N`.  Grönwall then
  gives `‖J_q τ‖ ≤ ‖(u,0)‖·e^{Kf} = ‖u‖·e^{Kf}` for every `q ∈ N`, every `τ ∈ [0,1]`, every direction
  `u` — a bound INDEPENDENT of `q`.  Since Task A identifies the base-slot Fréchet derivative endpoint
  `L_q u = (J_q 1).1`, this yields `‖L_q‖ ≤ e^{Kf}` UNIFORMLY over the neighbourhood.

  ## WHAT LANDS (all DERIVED; NO `sorry`, no new axioms, NOT `a₁ = R/6`).

    * ★ `uniformFlowExp_base_deriv_uniform_bound` — **the uniform base-slot derivative bound (Part 1).**
      For a velocity `v` (`‖v‖ ≤ ρ`) and a convex closed-ball neighbourhood `‖q‖ ≤ r₀` whose `σ`-thickening
      stays inside the compact base set `K`, there is ONE constant `M = e^{Kf}` with: for every `q` with
      `‖q‖ ≤ r₀`, the base-slot Fréchet derivative `L_q` of `q' ↦ uniformFlowExp q' v` exists and
      `‖L_q‖ ≤ M`.  Combines Task A's per-`q` field + endpoint identification with a uniform Grönwall
      bound on the FIXED phase ball `S₀ = closedBall (0,0) (C₀‖v‖ + r₀)` — the exact boundedness argument
      the plan calls for.  This is the FIRST-order base regularity (of the flow endpoint), uniform over
      the neighbourhood.

    * `ift_secondJet_base_ode_deriv_norm_le` — **the abstract second-jet ODE-derivative norm bound.**
      The base-parameter derivative of the inverse chart's applied second field-jet (Task B's
      `ift_secondJet_base_ode_hasDerivAt` value) is bounded, for `‖a‖ ≤ 1`, `‖b‖ ≤ 1`, by an explicit
      polynomial in the operator norms of the forward jets `I₀ = (Dφ)⁻¹`, `A' = ∂_s Dφ`, `H = D²φ`,
      `H' = ∂_s D²φ`.  Pure CLM norm sub-multiplicativity.

    * ★ `ift_secondJet_base_ode_uniform_bound` — **the uniform second-jet base-derivative bound (Part 2).**
      Wrapping the abstract bound with UNIFORM (over `q ∈ N`) bounds on the four forward jets gives a
      single constant `M₂` with: for every `q ∈ N` and every unit `a,b`, the second-jet base-derivative
      `∂_q∂²_p H(q)` has norm `≤ M₂`.  This is the exact q-block shape Task F consumes, CONDITIONAL on the
      uniform forward-jet bounds (see HONEST SCOPE).

  ## HONEST SCOPE (what is NOT closed here).  Part 1 is FULLY concrete and unconditional over the
  neighbourhood (it uses only the smooth, `.choose`-free forward flow `uniformFlowExp`).  Part 2 is the
  ABSTRACT operator-calculus uniformisation of Task B: it takes the forward jets `A = Dφ`, `H = D²φ` and
  their base derivatives `A', H'` as families with UNIFORM operator-norm bounds over `q ∈ N`.  Those
  bounds are the same forward-jet data Task B already carries; wiring them to the concrete
  `uniformFlowExp` needs the base-slot differentiability of `fderiv`/`fderiv²` of the flow (the
  `BaseFlowHderFamily` second-order tower), which is NOT done here.  So Part 2's uniform `∂_q∂²_p H`
  bound is CONDITIONAL on those uniform forward-jet bounds; Part 1's flow-endpoint uniform bound is
  UNCONDITIONAL.  Neither is `a₁ = R/6`.

  No `sorry`, no new axioms, no `:= True`; every hypothesis satisfiable and non-vacuous; none equals the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.UniformFlowExpBasepointJacobiExplicit
import QIQTH.InverseChartSecondJetODEBridge

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

variable {n : ℕ}

set_option maxHeartbeats 2000000

/-! ### Part 1 — the uniform base-slot derivative bound over a convex neighbourhood.

    Combines Task A's per-`q` base-slot Jacobi field + endpoint identification with a uniform Grönwall
    bound on a FIXED phase ball, yielding ONE constant bounding `‖∂_q uniformFlowExp‖` for every `q` in
    the convex closed-ball neighbourhood `‖q‖ ≤ r₀`. -/

/-- ★ **THE UNIFORM BASE-SLOT DERIVATIVE BOUND (Part 1).**

    Fix a compact base set `K`, a velocity `v` with `‖v‖ ≤ ρ_K`, a radius `r₀ > 0`, and a thickening
    `σ > 0` such that the whole `(r₀+σ)`-ball lies in `K` (`hKball`).  Then there is ONE constant
    `M ≥ 0` such that for EVERY base point `q` with `‖q‖ ≤ r₀` (a convex neighbourhood of `0`), the
    base-slot Fréchet derivative `L` of `q' ↦ uniformFlowExp g gi hC hK q' v` exists at `q` and
    `‖L‖ ≤ M`.

    The constant is `M = e^{Kf}`, `Kf` the uniform operator-norm bound of `fderiv (geodesicField)` on the
    FIXED phase ball `S₀ = closedBall (0,0) (C₀‖v‖ + r₀)` that contains every geodesic tube for
    `‖q‖ ≤ r₀`.  Uniformity is a Grönwall boundedness fact — NO continuity/coherence in `q` is used, so the
    `.choose`-incoherence firewall does not block it.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_base_deriv_uniform_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (v : Point n) (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK)
    (r₀ σ : ℝ) (hr₀ : 0 < r₀) (hσ : 0 < σ)
    (hKball : ∀ x : Point n, ‖x‖ ≤ r₀ + σ → x ∈ K) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ q : Point n, ‖q‖ ≤ r₀ →
        ∃ L : Point n →L[ℝ] Point n,
          HasFDerivAt (fun q' => uniformFlowExp g gi hC hK q' v) L q ∧ ‖L‖ ≤ M := by
  classical
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- the FIXED phase ball containing every geodesic tube for `‖q‖ ≤ r₀`.
  set Rphase : ℝ := C₀ * ‖v‖ + r₀ with hRphasedef
  set S₀ : Set (Point n × Point n) := Metric.closedBall ((0, 0) : Point n × Point n) Rphase with hS₀def
  have hS₀compact : IsCompact S₀ := isCompact_closedBall _ _
  -- the UNIFORM field-generator bound on the fixed ball.
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hS₀compact
  refine ⟨Real.exp Kf, (Real.exp_pos _).le, ?_⟩
  intro q hq
  -- `q` and its `σ`-thickening land in `K`.
  have hqσball : ∀ δ : Point n, ‖δ‖ ≤ σ → q + δ ∈ K := by
    intro δ hδ
    refine hKball (q + δ) ?_
    calc ‖q + δ‖ ≤ ‖q‖ + ‖δ‖ := norm_add_le _ _
      _ ≤ r₀ + σ := add_le_add hq hδ
  have hqK : q ∈ K := hKball q (le_trans hq (by linarith))
  -- extract the base-slot Fréchet derivative `L` at `q` (direction `0` — `L` is direction-independent).
  obtain ⟨_, L, _, _, _, hFD, _⟩ :=
    uniformFlowExp_basepoint_jacobi_explicit g gi hC hK q v hv σ hσ hqσball 0
  refine ⟨L, hFD, ?_⟩
  -- operator-norm bound: for every direction `u`, `‖L u‖ ≤ e^{Kf}·‖u‖`.
  refine ContinuousLinearMap.opNorm_le_bound L (Real.exp_pos _).le (fun u => ?_)
  -- re-instantiate Task A in direction `u`; identify its derivative with `L`.
  obtain ⟨Ju, Lu, hJu0, hJuode, _, hFDu, hLuend⟩ :=
    uniformFlowExp_basepoint_jacobi_explicit g gi hC hK q v hv σ hσ hqσball u
  have hLL : Lu = L := hFDu.unique hFD
  -- every tube point sits in the fixed phase ball `S₀`.
  have htubeS₀ : ∀ x ∈ Set.Icc (0 : ℝ) 1, uniformFlowTube g gi hC hK q v x ∈ S₀ := by
    intro x hx
    have h00 : ((0, 0) : Point n × Point n) = 0 := rfl
    rw [hS₀def, Metric.mem_closedBall, dist_eq_norm, h00, sub_zero]
    have hconf : ‖uniformFlowTube g gi hC hK q v x - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ :=
      uniformFlowTube_spec_conf g gi hC hK q hqK v hv x hx
    have hq0 : ‖((q, 0) : Point n × Point n)‖ ≤ r₀ := by
      rw [Prod.norm_def]; simp only [norm_zero, max_eq_left (norm_nonneg _)]; exact hq
    calc ‖uniformFlowTube g gi hC hK q v x‖
        = ‖(uniformFlowTube g gi hC hK q v x - (q, 0)) + (q, 0)‖ := by rw [sub_add_cancel]
      _ ≤ ‖uniformFlowTube g gi hC hK q v x - ((q, 0) : Point n × Point n)‖
            + ‖((q, 0) : Point n × Point n)‖ := norm_add_le _ _
      _ ≤ C₀ * ‖v‖ + r₀ := add_le_add hconf hq0
      _ = Rphase := by rw [hRphasedef]
  -- Grönwall on the Jacobi factor along the tube, generator bounded by `Kf`.
  have hJucont : ContinuousOn Ju (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => ((hJuode τ hτ).continuousAt).continuousWithinAt
  have hfbd : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v x)‖ ≤ Kf :=
    fun x hx => hKf _ (htubeS₀ x (Set.Ico_subset_Icc_self hx))
  have hJubound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖Ju x‖ ≤ gronwallBound ‖((u, 0) : Point n × Point n)‖ Kf 0 (x - 0) :=
    norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖((u, 0) : Point n × Point n)‖)
      (K := Kf) (ε := 0) (a := 0) (b := 1) hJucont
      (fun x hx => (hJuode x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
      (le_of_eq (by rw [hJu0]))
      (fun x hx => by
        have hle := (fderiv ℝ (geodesicField g gi)
          (uniformFlowTube g gi hC hK q v x)).le_opNorm (Ju x)
        calc ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v x) (Ju x)‖
            ≤ ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v x)‖ * ‖Ju x‖ := hle
          _ ≤ Kf * ‖Ju x‖ := mul_le_mul_of_nonneg_right (hfbd x hx) (norm_nonneg _)
          _ = Kf * ‖Ju x‖ + 0 := by ring)
  -- at `τ = 1`: `‖Ju 1‖ ≤ ‖(u,0)‖·e^{Kf}`.
  have hnorm_u0 : ‖((u, 0) : Point n × Point n)‖ = ‖u‖ := by
    rw [Prod.norm_def]; simp only [norm_zero, max_eq_left (norm_nonneg _)]
  have hJu1 : ‖Ju 1‖ ≤ ‖u‖ * Real.exp Kf := by
    have h1 := hJubound 1 (Set.right_mem_Icc.mpr zero_le_one)
    rw [sub_zero, gronwallBound_ε0, mul_one, hnorm_u0] at h1
    exact h1
  -- conclude `‖L u‖ = ‖(Ju 1).1‖ ≤ ‖Ju 1‖ ≤ ‖u‖·e^{Kf} = e^{Kf}·‖u‖`.
  rw [← hLL, hLuend]
  calc ‖(Ju 1).1‖ ≤ ‖Ju 1‖ := (le_max_left _ _).trans_eq (Prod.norm_def _).symm
    _ ≤ ‖u‖ * Real.exp Kf := hJu1
    _ = Real.exp Kf * ‖u‖ := by ring

/-! ### Part 2 — the uniform second-jet base-derivative bound over the neighbourhood.

    The base-parameter derivative of the inverse chart's applied second field-jet (Task B's
    `InverseChartSecondJetODEBridge.ift_secondJet_base_ode_hasDerivAt` value) is bounded by an explicit
    polynomial in the operator norms of the forward jets.  Wrapping with UNIFORM (over `q ∈ N`) bounds on
    those jets gives a single constant `M₂` bounding `∂_q∂²_p H(q)` for every `q ∈ N`. -/

section SecondJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Norm bound for a single CLM application, `‖I x‖ ≤ cI·cx`, from operator-norm bounds. -/
private theorem clm_apply_norm_le' (I : E →L[ℝ] E) (x : E) {cI cx : ℝ}
    (hI : ‖I‖ ≤ cI) (hx : ‖x‖ ≤ cx) (hcI : 0 ≤ cI) : ‖I x‖ ≤ cI * cx :=
  (I.le_opNorm x).trans (mul_le_mul hI hx (norm_nonneg _) hcI)

/-- Norm bound for a bilinear CLM application, `‖F x y‖ ≤ cF·cx·cy`, from operator-norm bounds. -/
private theorem clm2_apply_norm_le' (F : E →L[ℝ] (E →L[ℝ] E)) (x y : E) {cF cx cy : ℝ}
    (hF : ‖F‖ ≤ cF) (hx : ‖x‖ ≤ cx) (hy : ‖y‖ ≤ cy) (hcF : 0 ≤ cF) (hcx : 0 ≤ cx) :
    ‖F x y‖ ≤ cF * cx * cy :=
  (F.le_opNorm₂ x y).trans
    (mul_le_mul (mul_le_mul hF hx (norm_nonneg _) hcF) hy (norm_nonneg _) (mul_nonneg hcF hcx))

/-- **`ift_secondJet_base_ode_deriv_norm_le` — the abstract second-jet ODE-derivative norm bound.**
    The base-parameter derivative VALUE of the inverse chart's applied second field-jet (Task B's raw
    product-rule form) is bounded, for unit vectors `‖a‖ ≤ 1`, `‖b‖ ≤ 1`, by an explicit polynomial in
    the operator norms of `I₀ = (Dφ)⁻¹`, `Ip = ∂_s(Dφ)⁻¹`, `H₀ = D²φ`, `Hp' = ∂_s D²φ`.  Pure CLM norm
    sub-multiplicativity.  NOT `a₁ = R/6`. -/
theorem ift_secondJet_base_ode_deriv_norm_le
    (I₀ Ip : E →L[ℝ] E) (H₀ Hp' : E →L[ℝ] (E →L[ℝ] E)) {cI cIp cH cH' : ℝ}
    (hcI : ‖I₀‖ ≤ cI) (hcIp : ‖Ip‖ ≤ cIp) (hcH : ‖H₀‖ ≤ cH) (hcH' : ‖Hp'‖ ≤ cH')
    (hcI0 : 0 ≤ cI) (hcIp0 : 0 ≤ cIp) (hcH0 : 0 ≤ cH) (hcH'0 : 0 ≤ cH')
    {a b : E} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖-(Ip (H₀ (I₀ a) (I₀ b))
        + I₀ (Hp' (I₀ a) (I₀ b) + (H₀ (Ip a)) (I₀ b) + (H₀ (I₀ a)) (Ip b)))‖
      ≤ cIp * (cH * cI * cI) + cI * (cH' * cI * cI + cH * cIp * cI + cH * cI * cIp) := by
  have hIa : ‖I₀ a‖ ≤ cI := by simpa using clm_apply_norm_le' I₀ a hcI ha hcI0
  have hIb : ‖I₀ b‖ ≤ cI := by simpa using clm_apply_norm_le' I₀ b hcI hb hcI0
  have hIpa : ‖Ip a‖ ≤ cIp := by simpa using clm_apply_norm_le' Ip a hcIp ha hcIp0
  have hIpb : ‖Ip b‖ ≤ cIp := by simpa using clm_apply_norm_le' Ip b hcIp hb hcIp0
  -- `w = H₀ (I₀ a) (I₀ b)`
  have hw : ‖H₀ (I₀ a) (I₀ b)‖ ≤ cH * cI * cI :=
    clm2_apply_norm_le' H₀ (I₀ a) (I₀ b) hcH hIa hIb hcH0 hcI0
  -- the three summands of `W`
  have hW1 : ‖Hp' (I₀ a) (I₀ b)‖ ≤ cH' * cI * cI :=
    clm2_apply_norm_le' Hp' (I₀ a) (I₀ b) hcH' hIa hIb hcH'0 hcI0
  have hW2 : ‖(H₀ (Ip a)) (I₀ b)‖ ≤ cH * cIp * cI :=
    clm2_apply_norm_le' H₀ (Ip a) (I₀ b) hcH hIpa hIb hcH0 hcIp0
  have hW3 : ‖(H₀ (I₀ a)) (Ip b)‖ ≤ cH * cI * cIp :=
    clm2_apply_norm_le' H₀ (I₀ a) (Ip b) hcH hIa hIpb hcH0 hcI0
  have hW : ‖Hp' (I₀ a) (I₀ b) + (H₀ (Ip a)) (I₀ b) + (H₀ (I₀ a)) (Ip b)‖
      ≤ cH' * cI * cI + cH * cIp * cI + cH * cI * cIp := by
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add hW1 hW2)) hW3
  -- `‖Ip w‖ ≤ cIp·(cH·cI·cI)`, `‖I₀ W‖ ≤ cI·(…)`
  have hIpw : ‖Ip (H₀ (I₀ a) (I₀ b))‖ ≤ cIp * (cH * cI * cI) :=
    (Ip.le_opNorm _).trans (mul_le_mul hcIp hw (norm_nonneg _) hcIp0)
  have hI0W : ‖I₀ (Hp' (I₀ a) (I₀ b) + (H₀ (Ip a)) (I₀ b) + (H₀ (I₀ a)) (Ip b))‖
      ≤ cI * (cH' * cI * cI + cH * cIp * cI + cH * cI * cIp) :=
    (I₀.le_opNorm _).trans (mul_le_mul hcI hW (norm_nonneg _) hcI0)
  rw [norm_neg]
  exact (norm_add_le _ _).trans (add_le_add hIpw hI0W)

/-- **`ift_secondJet_base_ode_deriv_exists_bound` — Task B derivative WITH an explicit norm bound.**
    The applied inverse second jet along a base-perturbed forward family has a base-parameter derivative
    (`ift_secondJet_applied_hasDerivAt`) whose norm is bounded by the explicit polynomial `Mpoly`, given
    operator-norm bounds on the forward jets `A' = ∂_s Dφ` (bound `cA`), `I₀ = (Dφ)⁻¹` (`cI`),
    `H₀ = D²φ` (`cH`), `H' = ∂_s D²φ` (`cH'`).  The inverse-jet bound `‖Ip‖ ≤ cI·cA·cI` is derived
    internally by CLM sub-multiplicativity.  NOT `a₁ = R/6`. -/
theorem ift_secondJet_base_ode_deriv_exists_bound
    {A : ℝ → (E →L[ℝ] E)} {A' : E →L[ℝ] E} {H : ℝ → (E →L[ℝ] E →L[ℝ] E)}
    {H' : E →L[ℝ] E →L[ℝ] E} {s₀ : ℝ}
    (hA : HasDerivAt A A' s₀) (hH : HasDerivAt H H' s₀) (hunit : IsUnit (A s₀))
    {cI cA cH cH' : ℝ}
    (hcI : ‖Ring.inverse (A s₀)‖ ≤ cI) (hcA : ‖A'‖ ≤ cA) (hcH : ‖H s₀‖ ≤ cH) (hcH' : ‖H'‖ ≤ cH')
    (hcI0 : 0 ≤ cI) (hcA0 : 0 ≤ cA) (hcH0 : 0 ≤ cH) (hcH'0 : 0 ≤ cH')
    {a b : E} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ∃ d : E, HasDerivAt
      (fun s => -(Ring.inverse (A s)) (H s (Ring.inverse (A s) a) (Ring.inverse (A s) b))) d s₀
      ∧ ‖d‖ ≤ cI * cA * cI * (cH * cI * cI)
          + cI * (cH' * cI * cI + cH * (cI * cA * cI) * cI + cH * cI * (cI * cA * cI)) := by
  refine ⟨_, QIQTH.InverseChartSecondJetODEBridge.ift_secondJet_applied_hasDerivAt hA hH hunit a b, ?_⟩
  -- bound `‖Ip‖ = ‖-(I₀·A'·I₀)‖ ≤ cI·cA·cI`.
  set I₀ : E →L[ℝ] E := Ring.inverse (A s₀) with hI₀def
  have hIp : ‖-(I₀ * A' * I₀)‖ ≤ cI * cA * cI := by
    rw [norm_neg]
    calc ‖I₀ * A' * I₀‖ ≤ ‖I₀ * A'‖ * ‖I₀‖ := norm_mul_le _ _
      _ ≤ (‖I₀‖ * ‖A'‖) * ‖I₀‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (cI * cA) * cI := by
            refine mul_le_mul (mul_le_mul hcI hcA (norm_nonneg _) hcI0) hcI (norm_nonneg _)
              (mul_nonneg hcI0 hcA0)
      _ = cI * cA * cI := by ring
  exact ift_secondJet_base_ode_deriv_norm_le I₀ (-(I₀ * A' * I₀)) (H s₀) H'
    hcI hIp hcH hcH' hcI0 (by positivity) hcH0 hcH'0 ha hb

/-- **★ `ift_secondJet_base_ode_uniform_bound` — THE UNIFORM SECOND-JET BASE-DERIVATIVE BOUND (Part 2).**

    Let `N` be a neighbourhood set and, for each `q ∈ N`, let `A q`, `H q` be the forward jets `Dφ`, `D²φ`
    of the `q`-based inverse-chart family (with base derivatives `Ader q`, `Hder q` at `s = 0` and a unit
    Jacobian at `s = 0`), subject to UNIFORM operator-norm bounds `cI, cA, cH, cH'` over all `q ∈ N`.
    Then there is a SINGLE constant `M₂ ≥ 0` such that for every `q ∈ N` and every pair of unit vectors
    `a, b`, the base-parameter derivative of the applied second field-jet `∂_q∂²_p H(q)` exists and has
    norm `≤ M₂`.

    This is the exact q-block shape Task F consumes, obtained by a BOUNDEDNESS argument (uniform jet
    bounds ⟹ uniform derivative bound), NOT a smoothness/continuity-in-`q` argument — so the
    `.choose`-incoherence firewall does not block it.  CONDITIONAL on the uniform forward-jet bounds
    (see the file's HONEST SCOPE — wiring `A q = Dφ_q`, `H q = D²φ_q` to the concrete `uniformFlowExp` is
    the separate `BaseFlowHderFamily` second-order wiring, not done here).  NOT `a₁ = R/6`. -/
theorem ift_secondJet_base_ode_uniform_bound {X : Type*} (N : Set X)
    (A : X → ℝ → (E →L[ℝ] E)) (Ader : X → (E →L[ℝ] E))
    (H : X → ℝ → (E →L[ℝ] E →L[ℝ] E)) (Hder : X → (E →L[ℝ] E →L[ℝ] E))
    {cI cA cH cH' : ℝ} (hcI0 : 0 ≤ cI) (hcA0 : 0 ≤ cA) (hcH0 : 0 ≤ cH) (hcH'0 : 0 ≤ cH')
    (hA : ∀ q ∈ N, HasDerivAt (A q) (Ader q) 0) (hH : ∀ q ∈ N, HasDerivAt (H q) (Hder q) 0)
    (hunit : ∀ q ∈ N, IsUnit (A q 0))
    (hcI : ∀ q ∈ N, ‖Ring.inverse (A q 0)‖ ≤ cI) (hcA : ∀ q ∈ N, ‖Ader q‖ ≤ cA)
    (hcH : ∀ q ∈ N, ‖H q 0‖ ≤ cH) (hcH' : ∀ q ∈ N, ‖Hder q‖ ≤ cH') :
    ∃ M₂ : ℝ, 0 ≤ M₂ ∧
      ∀ q ∈ N, ∀ a b : E, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
        ∃ d : E, HasDerivAt
          (fun s => -(Ring.inverse (A q s)) (H q s (Ring.inverse (A q s) a) (Ring.inverse (A q s) b)))
          d 0
          ∧ ‖d‖ ≤ M₂ := by
  refine ⟨cI * cA * cI * (cH * cI * cI)
      + cI * (cH' * cI * cI + cH * (cI * cA * cI) * cI + cH * cI * (cI * cA * cI)), by positivity, ?_⟩
  intro q hq a b ha hb
  exact ift_secondJet_base_ode_deriv_exists_bound (hA q hq) (hH q hq) (hunit q hq)
    (hcI q hq) (hcA q hq) (hcH q hq) (hcH' q hq) hcI0 hcA0 hcH0 hcH'0 ha hb

end SecondJet

end QIQTH.ExpMap
