/-
  GeodesicJointSecondFDerivLipschitz — Lipschitz-in-base-point of the JOINT SECOND-order geodesic-flow
  Fréchet derivative map `Ξ₀ ↦ L(Ξ₀)` on the DOUBLED phase space (plan `tranquil-stargazing-fox.md`,
  Task D step (a) — the "doubled Task B").

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  MOTIVATION — the exact order-up mirror of `GeodesicJointFDerivLipschitz` (first-order Task B).

  `GeodesicJointSecondFDerivAtPointLocal.doubledFlow_endpoint_joint_hasFDerivAt_exists_atPoint`
  (J4-850) and its concrete non-vacuous witness
  `UniformFlowJointSecondFDerivNonzeroSeed.uniformFlow_joint_secondFDeriv_witness_nonzeroSeed`
  (J4-851) produce, for each doubled base state `Ξ₀`, the JOINT SECOND-order Fréchet derivative
  `L(Ξ₀)` of the doubled-flow endpoint `fun Ξ => W Ξ t` on the doubled phase space
  `E := (Point n × Point n) × (Point n × Point n)`, characterised by `L(Ξ₀) Ξ = V_{Ξ₀} Ξ t` where
  `V_{Ξ₀} Ξ` is the DOUBLED Jacobi field (integral curve of the linearized `doubledField` ODE) along
  the reference doubled curve `W Ξ₀` seeded at `Ξ`.  The neighborhood-quality `ContDiffOn ℝ 1`
  upgrade of the DOUBLED flow (equivalently the `ContDiffOn ℝ 2` of the base flow, via the
  finite-basis transfer) needs this derivative map to vary CONTINUOUSLY — indeed LIPSCHITZ — in the
  doubled base point `Ξ₀`.  This file supplies exactly that operator-norm Lipschitz bound.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  FIELD-AGNOSTIC REUSE vs GENUINELY NEW WORK (the step-3 determination of the plan).

  The first-order Task-B engine chain was:
    `fderiv_geodesicField_twopoint_dist_bound`  (base-curve separation → coefficient-field separation)
      feeding  `jacobi_twopoint_diff_bound`  (coefficient separation → Jacobi-field separation)
      plus a homogeneous Jacobi growth bound  `jacobi_field_norm_bound`
      plus `ContinuousLinearMap.opNorm_le_bound`.

  Of these, `jacobi_field_norm_bound` and the deepest engine `linODE_twopoint_diff_bound` (which
  `jacobi_twopoint_diff_bound` is a thin geodesic wrapper of) are FIELD-AGNOSTIC — they take an
  arbitrary normed space `E` and an arbitrary ODE coefficient map, NOT hardwired to `geodesicField`.
  So they are REUSED VERBATIM here (on `E =` the doubled phase space, coefficient
  `fderiv (doubledField)`), with `linODE_twopoint_diff_bound` called directly (no doubled wrapper).

  The two Lipschitz-modulus producers and the coefficient-separation bound, by contrast, WERE
  hardcoded to `geodesicField`.  Their doubled analogues are the genuinely-new (but mechanical) work
  of this file, and they are built from ALREADY-BANKED abstract/doubled pieces with NO new geometric
  input:
    * `doubledField_lipschitzOnWith_of_isCompact_convex` — `doubledField` Lipschitz on compact convex
      `S`, from `doubledField_fderiv_bddOn_compact` + `Convex.lipschitzOnWith_of_nnnorm_fderiv_le`;
    * `fderiv_doubledField_lipschitzOnWith_of_isCompact_convex` — `fderiv (doubledField)` Lipschitz on
      compact convex `S`, from `doubledField_fderiv2_bddOn_compact` (its `‖D²(doubledField)‖`-bound) +
      the same mean-value producer;
    * `fderiv_doubledField_twopoint_dist_bound` — the coefficient-field separation
      `‖DG(Y₁ τ) − DG(Y₂ τ)‖ ≤ Lg·e^{Kg}·dist(Y₁ 0, Y₂ 0)`, the DOUBLED analogue of
      `fderiv_geodesicField_twopoint_dist_bound`, built from the ABSTRACT two-point flow-Grönwall
      `QIQTH.AutonomousDep.autonomous_twopoint_gronwall` (applied to `Φ := doubledField g gi`) + the
      `Lg`-Lipschitz control of `fderiv (doubledField)`.

  So step 3's answer: MOSTLY field-agnostic reuse (the two Grönwall engines), plus a small amount of
  genuinely-new-but-mechanical doubled coefficient-Lipschitz plumbing, all discharged from banked
  doubled/abstract lemmas.  NO new coefficient-separation content specific to the nested structure of
  `fderiv (doubledField)` is needed — the abstract Grönwall + the compact `D²`-bound suffice, exactly
  as one level down.

  WHAT LANDS HERE (axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited):

  * `doubledField_lipschitzOnWith_of_isCompact_convex`,
    `fderiv_doubledField_lipschitzOnWith_of_isCompact_convex`,
    `fderiv_doubledField_twopoint_dist_bound` — the three doubled coefficient-Lipschitz lemmas.

  * `doubledFlow_joint_fderiv_lipschitz_in_basepoint` — ★ the abstract operator-norm Lipschitz bound
    `‖L₁ − L₂‖ ≤ Lg·e^{Kg}·e^{Kbd}·e^{Kbd}·dist(Y₁ 0, Y₂ 0)` for the two doubled second-order
    derivative maps `L₁, L₂` based at the two reference doubled geodesics `Y₁, Y₂` (with doubled Jacobi
    families `V₁, V₂` seeded at `Ξ`).  The EXACT order-up mirror of
    `geodesicFlow_joint_fderiv_lipschitz_in_basepoint`.

  * `doubledFlow_joint_fderiv_lipschitz_in_basepoint_compact` — the concrete-facing corollary that
    DISCHARGES the two Lipschitz moduli `Kg, Lg` and the coefficient bound `Kbd` from `IsCompact S`,
    `Convex ℝ S`, and the Christoffel smoothness `hC`, leaving only the doubled geodesic/Jacobi ODE
    data (exactly J4-850/851's supplied data at two base points) as hypotheses.  Delivers
    `∃ C ≥ 0, ‖L₁ − L₂‖ ≤ C·dist(Y₁ 0, Y₂ 0)`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  HONEST CHECKPOINT (binding).  This is the operator-norm Lipschitz dependence of the JOINT
  SECOND-order derivative map on the doubled base point — the missing continuity ingredient for the
  Task-D `ContDiffOn ℝ 1` (doubled) / `ContDiffOn ℝ 2` (base) upgrade.  The base points, reference
  doubled geodesics `Y₁, Y₂`, doubled Jacobi families `V₁, V₂`, and derivative CLMs `L₁, L₂` are
  supplied as hypotheses at exactly the same abstraction level as J4-850/851 (they are the doubled
  second-order theorem's own supplied data at two nearby base points, GENUINELY SATISFIABLE at a
  curved witness by the concrete `uniformFlow_joint_secondFDeriv_witness_nonzeroSeed` construction —
  see NON-VACUITY below).  It does NOT itself assemble the doubled `ContDiffOn ℝ 1`, NOT the
  finite-basis transfer to `ContDiffOn ℝ 2` of the base flow, NOT the IFT inverse, NOT discharge the
  RNC hypotheses, and does NOT bear on `hCConv`.  a₁=R/6 remains CONDITIONAL on
  {hDuhamel, hDConv, hCConv}.

  NON-VACUITY.  The abstract theorem's hypotheses are the two-base-point instance of the doubled
  second-order data.  Their joint satisfiability at a genuinely CURVED field is witnessed concretely:
  `UniformFlowJointSecondFDerivNonzeroSeed` already constructs, for the confined uniform doubled flow
  and EVERY (curved) metric, a doubled family `W`, doubled Jacobi block `V`, and CLM `L` along a
  pad-continuous nonzero-seed reference — exactly the per-base-point data these hypotheses require, at
  two nearby base points inside the windowed control set.  Hence no vacuous / unsatisfiable antecedent
  (unlike the retired J4-548 / J4-847 global-`∀ξ` constructions).
-/
import Mathlib
import QIQTH.BasepointJetModulus
import QIQTH.GeodesicJointFDerivLipschitz
import QIQTH.JacobiOperatorBaseDeriv
import QIQTH.AutonomousSmoothDep
import QIQTH.GeodesicJointSecondFDerivAtPointLocal

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- **`doubledField` is Lipschitz on any compact convex doubled phase set.**  Its Fréchet derivative
    is bounded on the compact `S` (`doubledField_fderiv_bddOn_compact`), and the mean-value theorem on
    the convex `S` (`Convex.lipschitzOnWith_of_nnnorm_fderiv_le`) turns that bound into a Lipschitz
    modulus.  The doubled analogue of `geodesicField_lipschitzOnWith_of_isCompact_convex`. -/
theorem doubledField_lipschitzOnWith_of_isCompact_convex
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set ((Point n × Point n) × (Point n × Point n))}
    (hS : IsCompact S) (hSc : Convex ℝ S) :
    ∃ Kg : ℝ≥0, LipschitzOnWith Kg (doubledField g gi) S := by
  obtain ⟨Kb, hKb0, hbd⟩ := doubledField_fderiv_bddOn_compact g gi hC hS
  refine ⟨⟨Kb, hKb0⟩, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => ((contDiff_doubledField g gi hC).differentiable (by simp)).differentiableAt)
    (fun x hx => ?_) hSc
  exact_mod_cast hbd x hx

/-- **`fderiv (doubledField)` is Lipschitz on any compact convex doubled phase set.**  `doubledField`
    is `C^∞`, so `fderiv (doubledField)` is `C^∞` too, hence `fderiv² (doubledField)` is continuous and
    bounded on the compact `S` (`doubledField_fderiv2_bddOn_compact`); the mean-value theorem on the
    convex `S` converts that into a Lipschitz modulus for `fderiv (doubledField)`.  The doubled
    analogue of `fderiv_geodesicField_lipschitzOnWith_of_isCompact_convex`. -/
theorem fderiv_doubledField_lipschitzOnWith_of_isCompact_convex
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set ((Point n × Point n) × (Point n × Point n))}
    (hS : IsCompact S) (hSc : Convex ℝ S) :
    ∃ Lg : ℝ≥0, LipschitzOnWith Lg (fderiv ℝ (doubledField g gi)) S := by
  have hDf : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (doubledField g gi)) :=
    (contDiff_doubledField g gi hC).fderiv_right le_top
  have hcont : Continuous (fun x => ‖fderiv ℝ (fderiv ℝ (doubledField g gi)) x‖) :=
    (hDf.continuous_fderiv (by simp)).norm
  obtain ⟨C, hCb⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (hDf.differentiable (by simp)).differentiableAt) (fun x hx => ?_) hSc
  have h : ‖fderiv ℝ (fderiv ℝ (doubledField g gi)) x‖ ≤ max C 0 :=
    ((Real.le_norm_self _).trans (hCb x hx)).trans (le_max_left _ _)
  exact_mod_cast h

/-- **Two-point Lipschitz bound for the doubled `A`-operator `fderiv (doubledField)`.**
    If `Y₁, Y₂` are two integral curves of the autonomous doubled field on `[0,1]` that both stay in a
    set `S` on which `doubledField` is `Kg`-Lipschitz and `fderiv (doubledField)` is `Lg`-Lipschitz,
    then along the whole interval
    `‖DG(Y₁ τ) − DG(Y₂ τ)‖ ≤ Lg·e^{Kg}·dist(Y₁ 0, Y₂ 0)`, `DG = fderiv (doubledField)`.

    Proof: the ABSTRACT two-point flow-Grönwall `QIQTH.AutonomousDep.autonomous_twopoint_gronwall`
    (applied to `Φ := doubledField g gi`) bounds the phase distance
    `dist (Y₁ τ) (Y₂ τ) ≤ dist (Y₁ 0) (Y₂ 0)·e^{Kg τ}`, and the `Lg`-Lipschitz control of
    `fderiv (doubledField)` on `S` (`LipschitzOnWith.dist_le_mul`) turns that into the stated
    operator-norm bound (using `e^{Kg τ} ≤ e^{Kg}` since `τ ≤ 1`, `Kg ≥ 0`).  The exact order-up
    mirror of `fderiv_geodesicField_twopoint_dist_bound`. -/
theorem fderiv_doubledField_twopoint_dist_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    {S : Set ((Point n × Point n) × (Point n × Point n))} {Kg Lg : ℝ≥0}
    (hLip : LipschitzOnWith Kg (doubledField g gi) S)
    (hLip2 : LipschitzOnWith Lg (fderiv ℝ (doubledField g gi)) S)
    {Y₁ Y₂ : ℝ → (Point n × Point n) × (Point n × Point n)}
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (doubledField g gi (Y₁ t)) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (doubledField g gi (Y₂ t)) t)
    (hS1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₁ t ∈ S)
    (hS2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₂ t ∈ S) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (doubledField g gi) (Y₁ τ) - fderiv ℝ (doubledField g gi) (Y₂ τ)‖
        ≤ (Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0) := by
  intro τ hτ
  -- Two-point flow-Grönwall (abstract): phase distance controlled by the initial distance.
  have hg : dist (Y₁ τ) (Y₂ τ) ≤ dist (Y₁ 0) (Y₂ 0) * Real.exp ((Kg : ℝ) * τ) :=
    QIQTH.AutonomousDep.autonomous_twopoint_gronwall (doubledField g gi) hLip h1 h2 hS1 hS2 τ hτ
  -- `Lg`-Lipschitz control of `fderiv (doubledField)` on `S`.
  have hlip2τ :
      ‖fderiv ℝ (doubledField g gi) (Y₁ τ) - fderiv ℝ (doubledField g gi) (Y₂ τ)‖
        ≤ (Lg : ℝ) * dist (Y₁ τ) (Y₂ τ) := by
    have h := hLip2.dist_le_mul (Y₁ τ) (hS1 τ hτ) (Y₂ τ) (hS2 τ hτ)
    rwa [dist_eq_norm] at h
  refine hlip2τ.trans ?_
  have hexp : Real.exp ((Kg : ℝ) * τ) ≤ Real.exp Kg := by
    apply Real.exp_le_exp.mpr
    have : (Kg : ℝ) * τ ≤ (Kg : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hτ.2 (NNReal.coe_nonneg Kg)
    simpa using this
  calc (Lg : ℝ) * dist (Y₁ τ) (Y₂ τ)
      ≤ (Lg : ℝ) * (dist (Y₁ 0) (Y₂ 0) * Real.exp ((Kg : ℝ) * τ)) :=
        mul_le_mul_of_nonneg_left hg (NNReal.coe_nonneg Lg)
    _ ≤ (Lg : ℝ) * (dist (Y₁ 0) (Y₂ 0) * Real.exp Kg) := by
        apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg Lg)
        exact mul_le_mul_of_nonneg_left hexp dist_nonneg
    _ = (Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0) := by ring

/-- **★ Lipschitz-in-base-point of the joint SECOND-order geodesic-flow Fréchet derivative map
    (abstract).**  The EXACT order-up mirror of `geodesicFlow_joint_fderiv_lipschitz_in_basepoint`, on
    the doubled phase space `E = (Point n × Point n) × (Point n × Point n)` with `doubledField` in
    place of `geodesicField`.

    Let `Y₁, Y₂` be two reference doubled geodesics (integral curves of the doubled field on `[0,1]`)
    staying in a phase set `S` on which `doubledField` is `Kg`-Lipschitz and `fderiv (doubledField)` is
    `Lg`-Lipschitz, with the coefficient bound `‖DG(Yᵢ τ)‖ ≤ Kbd` along both.  Let `V₁, V₂` be the two
    doubled Jacobi families along `Y₁, Y₂` respectively (`Vᵢ' = DG(Yᵢ)·Vᵢ`, `Vᵢ Ξ 0 = Ξ`), and
    `L₁, L₂` the J4-850/851 endpoint derivative CLMs (`Lᵢ Ξ = Vᵢ Ξ t`).  Then
      `‖L₁ − L₂‖ ≤ Lg·e^{Kg}·e^{Kbd}·e^{Kbd}·dist(Y₁ 0, Y₂ 0)`.

    PROOF — the two-level Grönwall combination, one order up:
    `fderiv_doubledField_twopoint_dist_bound` gives the coefficient-field separation
    `‖DG(Y₁ τ) − DG(Y₂ τ)‖ ≤ Lg·e^{Kg}·dist(Y₁ 0, Y₂ 0)`; the FIELD-AGNOSTIC `linODE_twopoint_diff_bound`
    (fed that separation, the coefficient bound `Kbd` along `Y₁`, and the single-field growth bound
    `‖V₂ Ξ τ‖ ≤ ‖Ξ‖·e^{Kbd}` from the FIELD-AGNOSTIC `jacobi_field_norm_bound`) gives the per-seed
    bound `‖V₁ Ξ t − V₂ Ξ t‖ ≤ Lg·e^{Kg}·dist·(‖Ξ‖·e^{Kbd})·e^{Kbd}`; `opNorm_le_bound` concludes. -/
theorem doubledFlow_joint_fderiv_lipschitz_in_basepoint
    (g gi : Point n → Fin n → Fin n → ℝ)
    {S : Set ((Point n × Point n) × (Point n × Point n))} {Kg Lg : ℝ≥0}
    (hLip : LipschitzOnWith Kg (doubledField g gi) S)
    (hLip2 : LipschitzOnWith Lg (fderiv ℝ (doubledField g gi)) S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {Y₁ Y₂ : ℝ → (Point n × Point n) × (Point n × Point n)}
    (h1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (doubledField g gi (Y₁ τ)) τ)
    (h2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (doubledField g gi (Y₂ τ)) τ)
    (hS1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y₁ τ ∈ S)
    (hS2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y₂ τ ∈ S)
    {Kbd : ℝ} (hKbd0 : 0 ≤ Kbd)
    (hKb1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (doubledField g gi) (Y₁ τ)‖ ≤ Kbd)
    (hKb2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (doubledField g gi) (Y₂ τ)‖ ≤ Kbd)
    {V₁ V₂ : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n))}
    (hV1ode : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V₁ Ξ) (fderiv ℝ (doubledField g gi) (Y₁ τ) (V₁ Ξ τ)) τ)
    (hV2ode : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V₂ Ξ) (fderiv ℝ (doubledField g gi) (Y₂ τ) (V₂ Ξ τ)) τ)
    (hV10 : ∀ Ξ : (Point n × Point n) × (Point n × Point n), V₁ Ξ 0 = Ξ)
    (hV20 : ∀ Ξ : (Point n × Point n) × (Point n × Point n), V₂ Ξ 0 = Ξ)
    {L₁ L₂ : ((Point n × Point n) × (Point n × Point n)) →L[ℝ]
      ((Point n × Point n) × (Point n × Point n))}
    (hL1eq : ∀ Ξ : (Point n × Point n) × (Point n × Point n), L₁ Ξ = V₁ Ξ t)
    (hL2eq : ∀ Ξ : (Point n × Point n) × (Point n × Point n), L₂ Ξ = V₂ Ξ t) :
    ‖L₁ - L₂‖ ≤ (Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd * dist (Y₁ 0) (Y₂ 0) := by
  -- coefficient-field separation via the doubled two-level Grönwall.
  have hD0 := fderiv_doubledField_twopoint_dist_bound g gi hLip hLip2 h1 h2 hS1 hS2
  -- single-field growth bound for the second doubled Jacobi family (linear in the seed).
  have hJb2 : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖V₂ Ξ τ‖ ≤ ‖Ξ‖ * Real.exp Kbd := by
    intro Ξ τ hτ
    have hb := jacobi_field_norm_bound hKbd0 (hV2ode Ξ) hKb2 τ hτ
    rwa [hV20 Ξ] at hb
  -- per-seed two-point doubled-Jacobi difference, packaged as an operator bound.
  have hper : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ‖(L₁ - L₂) Ξ‖ ≤
      ((Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd * dist (Y₁ 0) (Y₂ 0)) * ‖Ξ‖ := by
    intro Ξ
    rw [ContinuousLinearMap.sub_apply, hL1eq Ξ, hL2eq Ξ]
    have h0 : V₁ Ξ 0 = V₂ Ξ 0 := by rw [hV10 Ξ, hV20 Ξ]
    -- FIELD-AGNOSTIC two-point linear-ODE difference (no doubled wrapper needed).
    have hdiff := linODE_twopoint_diff_bound
      (E := (Point n × Point n) × (Point n × Point n))
      (A₁ := fun τ => fderiv ℝ (doubledField g gi) (Y₁ τ))
      (A₂ := fun τ => fderiv ℝ (doubledField g gi) (Y₂ τ))
      (X₁ := V₁ Ξ) (X₂ := V₂ Ξ) (b₁ := fun _ => 0) (b₂ := fun _ => 0)
      (K := (Kbd : ℝ)) (Dcoef := (Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0))
      (Xb := ‖Ξ‖ * Real.exp Kbd) (Dsrc := 0) hKbd0
      (fun τ hτ => by simpa using hV1ode Ξ τ hτ)
      (fun τ hτ => by simpa using hV2ode Ξ τ hτ)
      h0 hKb1 hD0 (fun τ hτ => hJb2 Ξ τ hτ) (fun τ _ => by simp)
    have hdiff' := hdiff t ht
    calc ‖V₁ Ξ t - V₂ Ξ t‖
        ≤ (((Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0)) * (‖Ξ‖ * Real.exp Kbd) + 0)
            * Real.exp Kbd := hdiff'
      _ = ((Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd * dist (Y₁ 0) (Y₂ 0)) * ‖Ξ‖ := by
          ring
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ hper
  have hLgnn : (0 : ℝ) ≤ (Lg : ℝ) := NNReal.coe_nonneg Lg
  have hdnn : (0 : ℝ) ≤ dist (Y₁ 0) (Y₂ 0) := dist_nonneg
  positivity

/-- **★ Lipschitz-in-base-point of the joint SECOND-order geodesic-flow Fréchet derivative map
    (concrete-facing).**  The compact-set corollary of `doubledFlow_joint_fderiv_lipschitz_in_basepoint`:
    given `IsCompact S`, `Convex ℝ S`, and the Christoffel smoothness `hC`, the two Lipschitz moduli
    `Kg, Lg` and the coefficient bound `Kbd` are all PRODUCED from compactness
    (`doubledField_lipschitzOnWith_of_isCompact_convex`,
    `fderiv_doubledField_lipschitzOnWith_of_isCompact_convex`, `doubledField_fderiv_bddOn_compact`).
    Leaves only the doubled geodesic/Jacobi ODE data (J4-850/851's supplied data at the two base
    points) as hypotheses, and delivers a single Lipschitz constant `C ≥ 0`:
      `‖L₁ − L₂‖ ≤ C·dist(Y₁ 0, Y₂ 0)`.  The order-up mirror of
    `geodesicFlow_joint_fderiv_lipschitz_in_basepoint_compact`. -/
theorem doubledFlow_joint_fderiv_lipschitz_in_basepoint_compact
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set ((Point n × Point n) × (Point n × Point n))}
    (hScomp : IsCompact S) (hSconv : Convex ℝ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {Y₁ Y₂ : ℝ → (Point n × Point n) × (Point n × Point n)}
    (h1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (doubledField g gi (Y₁ τ)) τ)
    (h2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (doubledField g gi (Y₂ τ)) τ)
    (hS1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y₁ τ ∈ S)
    (hS2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y₂ τ ∈ S)
    {V₁ V₂ : ((Point n × Point n) × (Point n × Point n)) → ℝ →
      ((Point n × Point n) × (Point n × Point n))}
    (hV1ode : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V₁ Ξ) (fderiv ℝ (doubledField g gi) (Y₁ τ) (V₁ Ξ τ)) τ)
    (hV2ode : ∀ Ξ : (Point n × Point n) × (Point n × Point n), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V₂ Ξ) (fderiv ℝ (doubledField g gi) (Y₂ τ) (V₂ Ξ τ)) τ)
    (hV10 : ∀ Ξ : (Point n × Point n) × (Point n × Point n), V₁ Ξ 0 = Ξ)
    (hV20 : ∀ Ξ : (Point n × Point n) × (Point n × Point n), V₂ Ξ 0 = Ξ)
    {L₁ L₂ : ((Point n × Point n) × (Point n × Point n)) →L[ℝ]
      ((Point n × Point n) × (Point n × Point n))}
    (hL1eq : ∀ Ξ : (Point n × Point n) × (Point n × Point n), L₁ Ξ = V₁ Ξ t)
    (hL2eq : ∀ Ξ : (Point n × Point n) × (Point n × Point n), L₂ Ξ = V₂ Ξ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖L₁ - L₂‖ ≤ C * dist (Y₁ 0) (Y₂ 0) := by
  obtain ⟨Kbd, hKbd0, hbd⟩ := doubledField_fderiv_bddOn_compact g gi hC hScomp
  obtain ⟨Kg, hLip⟩ := doubledField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
  obtain ⟨Lg, hLip2⟩ := fderiv_doubledField_lipschitzOnWith_of_isCompact_convex g gi hC hScomp hSconv
  refine ⟨(Lg : ℝ) * Real.exp Kg * Real.exp Kbd * Real.exp Kbd, ?_, ?_⟩
  · have hLgnn : (0 : ℝ) ≤ (Lg : ℝ) := NNReal.coe_nonneg Lg
    positivity
  · exact doubledFlow_joint_fderiv_lipschitz_in_basepoint g gi hLip hLip2 ht h1 h2 hS1 hS2
      hKbd0 (fun τ hτ => hbd _ (hS1 τ hτ)) (fun τ hτ => hbd _ (hS2 τ hτ))
      hV1ode hV2ode hV10 hV20 hL1eq hL2eq

end QIQTH.ExpMap
