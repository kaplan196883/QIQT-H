/-
  GeneralCenterCoherentInverseChart — J4-891: the GENERAL-CENTER (nonzero-velocity) Task-E/Task-F
  analogue.  It applies Mathlib's inverse function theorem to the augmented map
  `G(q,v) = (q, uniformFlowExp g gi hC hK q v)` at an ARBITRARY interior base point `z₀` and an
  ARBITRARY (small) velocity `v₀`, producing a genuinely COHERENT jointly-`ContDiffAt ℝ 2` geodesic
  exp INVERSE chart at the general centre `(z₀, uniformFlowExp z₀ v₀)`, and reconciles it with the
  concrete `uniformInverseChart` to get JOINT `ContDiffAt ℝ 2` of `uniformInverseChart` there.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / inverse-function / Neumann-series plumbing.  No `sorry`, no new axioms, no vacuous /
  unsatisfiable hypotheses, no conclusion-in-disguise, no existing file edited.  `a₁ = R/6` remains
  CONDITIONAL on {hDuhamel, hDConv, hCConv}.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE NEW MATHEMATICAL CONTENT — invertibility of the joint derivative AWAY from `v = 0`.

  At velocity `0` (J4-855 Task E) the joint derivative of `G` is `(h,w) ↦ (h, h + w)`, trivially a
  linear isomorphism, because at zero velocity the reference geodesic is the CONSTANT curve, forcing
  BOTH partial derivatives of `exp` to the identity.  At a NONZERO velocity `v₀` this is no longer
  automatic: the velocity-slot derivative
    `B := D_v (uniformFlowExp z₀ ·)(v₀) = fderiv ℝ (uniformFlowExp g gi hC hK z₀) v₀`
  is a genuine (Jacobi-field endpoint) map, invertible only ABSENT conjugate points.  The joint
  derivative `D G_{(z₀,v₀)}(h,w) = (h, A h + B w)` (with `A := D_q (uniformFlowExp · v₀)(z₀)`) is a
  linear isomorphism IFF `B` is invertible — its inverse being `(a,b) ↦ (a, B⁻¹(b - A a))`.

  This file establishes `B`'s invertibility QUANTITATIVELY, via the banked near-identity Jacobian
  bound `uniformFlowExp_fderiv_near_id_quant` (`‖B - id‖ ≤ C_D‖v₀‖`): for `‖v₀‖` small enough that
  `‖B - id‖ < 1`, a Neumann series (`Units.oneSub`) gives `B⁻¹` explicitly, so `D G` is a genuine
  `ContinuousLinearEquiv` and `ContDiffAt.to_localInverse` applies.  The smallness radius `r₀` (which
  bundles the flow radius, the germ radius, and the Neumann threshold `1/(C_D+1)`) is EXACTLY where
  the b-tube frontier's "small enough to avoid conjugate points" constraint lives — it is positive,
  so the construction is genuinely NON-VACUOUS for every (curved) metric.

  ## THE DELIVERABLES.

  * `generalCenter_coherent_joint_chart` — ★ Task-E at the general centre.  GIVEN the invertibility
    datum `‖B - id‖ < 1` (an honest, checkable, satisfiable hypothesis), there is a coherent chart
    `chartCoherent`, jointly `ContDiffAt ℝ 2` at `(z₀, exp z₀ v₀)`, with `chartCoherent z₀ (exp z₀ v₀)
    = v₀` and the coherent inverse-chart identity near the centre.

  * `uniformInverseChart_jointContDiffAt_generalCenter` — ★★ Task-F at the general centre, WITH the
    invertibility datum DISCHARGED.  There is a radius `r₀ > 0` such that for EVERY interior base
    `z₀` and EVERY velocity `‖v₀‖ < r₀`, the concrete `uniformInverseChart g gi hC hK` is jointly
    `ContDiffAt ℝ 2` at `(z₀, uniformFlowExp z₀ v₀)`.  The invertibility is DERIVED, not assumed —
    the near-identity bound makes it automatic below `r₀`.

  ## WHAT THIS FILE DOES NOT DO.
  It supplies the per-point general-centre joint `C²` inverse chart (the Task-E-analogue IFT step at
  `v₀ ≠ 0`, and its Task-F reconciliation).  It does NOT run the compactness assembly (piece (iv) of
  J4-889) that would cover the whole compact `b`-tube with such charts to build `hbint`'s cover `W`,
  does NOT close `hbint`, and does NOT bear on `hCConv`.  a₁=R/6 remains CONDITIONAL.
-/
import Mathlib
import QIQTH.GeneralCenterJointC2Flow
import QIQTH.UniformFlowJointFDerivAtPointConcrete
import QIQTH.NearIsometryBudget
import QIQTH.UniformFlowNondeg
import QIQTH.UniformChartRadius

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★ Task-E at the GENERAL CENTRE — the coherent jointly-`ContDiffAt ℝ 2` inverse chart at
    `(z₀, exp z₀ v₀)`.**  For an interior base point `z₀ ∈ interior K`, a velocity `v₀` with
    `‖v₀‖ < uniformFlowRadius`, and the invertibility datum `‖B - id‖ < 1` on the velocity-slot
    derivative `B := fderiv ℝ (uniformFlowExp g gi hC hK z₀) v₀`, there is a chart `chartCoherent`
    (the `.2`-slot of Mathlib's IFT local inverse of `G(q,v) = (q, uniformFlowExp q v)`) that is
    jointly `ContDiffAt ℝ 2` at the centre `(z₀, exp z₀ v₀)`, sends the centre to `v₀`, and satisfies
    the coherent inverse-chart identity `uniformFlowExp q (chartCoherent q p) = p` near the centre.
    Built ONCE, coherently, with NO per-point `Classical.choose`.  The invertibility of the joint
    derivative is established by writing `D G(h,w) = (h, A h + B w)` and inverting `B` via a Neumann
    series (`Units.oneSub`), giving the explicit inverse `(a,b) ↦ (a, B⁻¹(b - A a))`.  NOT `a₁=R/6`. -/
theorem generalCenter_coherent_joint_chart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K)
    (v₀ : Point n) (hv₀ρ : ‖v₀‖ < uniformFlowRadius g gi hC hK)
    (hInv : ‖fderiv ℝ (uniformFlowExp g gi hC hK z₀) v₀
              - ContinuousLinearMap.id ℝ (Point n)‖ < 1) :
    ∃ chartCoherent : Point n → Point n → Point n,
      ContDiffAt ℝ 2 (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
        ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∧
      chartCoherent z₀ (uniformFlowExp g gi hC hK z₀ v₀) = v₀ ∧
      (∀ᶠ ξ in nhds ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n),
        uniformFlowExp g gi hC hK ξ.1 (chartCoherent ξ.1 ξ.2) = ξ.2) := by
  classical
  have hz₀K : z₀ ∈ K := interior_subset hz₀
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (1) the joint Fréchet derivative `L` of `uniformFlowExp` at `(z₀,v₀)`.
  obtain ⟨ε, hεpos, hadm⟩ := admissibleBall_of_normVelLt g gi hC hK z₀ hz₀ v₀ hv₀ρ
  obtain ⟨L, hL_exp⟩ :=
    uniformFlow_joint_expEndpoint_hasFDerivAt_atBasepoint g gi hC hK
      ((z₀, v₀) : Point n × Point n) hεpos (fun ξ hξ => (hadm ξ hξ).1) (fun ξ hξ => (hadm ξ hξ).2)
  -- the two slot inclusions and the two partial derivatives `A` (base) and `B` (velocity).
  set inrCLM : (Point n) →L[ℝ] (Point n × Point n) :=
    (0 : Point n →L[ℝ] Point n).prod (ContinuousLinearMap.id ℝ (Point n)) with hinrdef
  set inlCLM : (Point n) →L[ℝ] (Point n × Point n) :=
    (ContinuousLinearMap.id ℝ (Point n)).prod (0 : Point n →L[ℝ] Point n) with hinldef
  set B : (Point n) →L[ℝ] (Point n) := L.comp inrCLM with hBdef
  set A : (Point n) →L[ℝ] (Point n) := L.comp inlCLM with hAdef
  -- chain rule: `fderiv (uniformFlowExp z₀) v₀ = B`.
  have hinclV : HasFDerivAt (fun w : Point n => ((z₀, w) : Point n × Point n)) inrCLM v₀ :=
    (hasFDerivAt_const (z₀ : Point n) (v₀ : Point n)).prodMk (hasFDerivAt_id (v₀ : Point n))
  have hcompV := hL_exp.comp v₀ hinclV
  have hBval : fderiv ℝ (uniformFlowExp g gi hC hK z₀) v₀ = B := by
    rw [hBdef]; exact hcompV.fderiv
  have hBnid : ‖B - ContinuousLinearMap.id ℝ (Point n)‖ < 1 := by rw [← hBval]; exact hInv
  -- slot identities `A h = L (h,0)` and `B w = L (0,w)`.
  have hAh : ∀ h : Point n, A h = L ((h, 0) : Point n × Point n) := by
    intro h
    rw [hAdef, hinldef]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
  have hL0w : ∀ w : Point n, L ((0, w) : Point n × Point n) = B w := by
    intro w
    rw [hBdef, hinrdef]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
  -- `L (h,w) = A h + B w`.
  have hLsplit : ∀ h w : Point n, L ((h, w) : Point n × Point n) = A h + B w := by
    intro h w
    rw [hAh h, ← hL0w w, ← map_add]
    congr 1
    rw [Prod.mk_add_mk, add_zero, zero_add]
  have hLsub : ∀ x : Point n × Point n, L x - A x.1 = B x.2 := by
    intro x
    have h : L x = A x.1 + B x.2 := hLsplit x.1 x.2
    rw [h]; abel
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (2) invertibility of `B` via the Neumann series (`Units.oneSub`).
  set t : (Point n) →L[ℝ] (Point n) := (1 : (Point n) →L[ℝ] (Point n)) - B with htdef
  have ht1 : ‖t‖ < 1 := by
    rw [htdef, norm_sub_rev, ContinuousLinearMap.one_def]; exact hBnid
  set u : ((Point n) →L[ℝ] (Point n))ˣ := Units.oneSub t ht1 with hudef
  have huval : (↑u : (Point n) →L[ℝ] (Point n)) = B := by
    rw [hudef, Units.val_oneSub, htdef]; abel
  set Binv : (Point n) →L[ℝ] (Point n) := ↑u⁻¹ with hBinvdef
  have hBinvB : ∀ w : Point n, Binv (B w) = w := by
    intro w
    have h1 : (↑u⁻¹ * ↑u : (Point n) →L[ℝ] (Point n)) = 1 := u.inv_mul
    rw [huval] at h1
    have h2 := congrArg (fun f : (Point n) →L[ℝ] (Point n) => f w) h1
    simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, hBinvdef] using h2
  have hBBinv : ∀ w : Point n, B (Binv w) = w := by
    intro w
    have h1 : (↑u * ↑u⁻¹ : (Point n) →L[ℝ] (Point n)) = 1 := u.mul_inv
    rw [huval] at h1
    have h2 := congrArg (fun f : (Point n) →L[ℝ] (Point n) => f w) h1
    simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, hBinvdef] using h2
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (3) the augmented map `G` and its derivative `f₁ = (h,w) ↦ (h, A h + B w)`, a `≃L`.
  set f₁ : (Point n × Point n) →L[ℝ] (Point n × Point n) :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).prod L with hf₁def
  set f₂ : (Point n × Point n) →L[ℝ] (Point n × Point n) :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).prod
      (Binv.comp ((ContinuousLinearMap.snd ℝ (Point n) (Point n))
        - A.comp (ContinuousLinearMap.fst ℝ (Point n) (Point n)))) with hf₂def
  have hf₁apply : ∀ y : Point n × Point n, f₁ y = ((y.1, L y) : Point n × Point n) := by
    intro y
    rw [hf₁def]
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst']
  have hf₂apply : ∀ y : Point n × Point n,
      f₂ y = ((y.1, Binv (y.2 - A y.1)) : Point n × Point n) := by
    intro y
    rw [hf₂def]
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hli : Function.LeftInverse f₂ f₁ := by
    intro x
    rw [hf₁apply x, hf₂apply]
    calc ((x.1, Binv (((x.1, L x) : Point n × Point n).2
              - A ((x.1, L x) : Point n × Point n).1)) : Point n × Point n)
        = ((x.1, Binv (L x - A x.1)) : Point n × Point n) := rfl
      _ = ((x.1, Binv (B x.2)) : Point n × Point n) := by rw [hLsub x]
      _ = ((x.1, x.2) : Point n × Point n) := by rw [hBinvB]
      _ = x := rfl
  have hri : Function.RightInverse f₂ f₁ := by
    intro x
    rw [hf₂apply x, hf₁apply]
    calc ((((x.1, Binv (x.2 - A x.1)) : Point n × Point n).1,
              L ((x.1, Binv (x.2 - A x.1)) : Point n × Point n)) : Point n × Point n)
        = ((x.1, L ((x.1, Binv (x.2 - A x.1)) : Point n × Point n)) : Point n × Point n) := rfl
      _ = ((x.1, A x.1 + B (Binv (x.2 - A x.1))) : Point n × Point n) := by
            rw [hLsplit x.1 (Binv (x.2 - A x.1))]
      _ = ((x.1, A x.1 + (x.2 - A x.1)) : Point n × Point n) := by rw [hBBinv]
      _ = ((x.1, x.2) : Point n × Point n) := by congr 1; abel
      _ = x := rfl
  set equiv : (Point n × Point n) ≃L[ℝ] (Point n × Point n) :=
    ContinuousLinearEquiv.equivOfInverse f₁ f₂ hli hri with hequivdef
  have hcoe : (equiv : (Point n × Point n) →L[ℝ] (Point n × Point n)) = f₁ := by
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearEquiv.coe_coe, hequivdef]
    exact ContinuousLinearEquiv.equivOfInverse_apply f₁ f₂ hli hri x
  have hGfd : HasFDerivAt
      (fun ξ : Point n × Point n => ((ξ.1, uniformFlowExp g gi hC hK ξ.1 ξ.2) : Point n × Point n))
      f₁ ((z₀, v₀) : Point n × Point n) := by
    rw [hf₁def]
    exact (hasFDerivAt_fst).prodMk hL_exp
  have hG' : HasFDerivAt
      (fun ξ : Point n × Point n => ((ξ.1, uniformFlowExp g gi hC hK ξ.1 ξ.2) : Point n × Point n))
      (equiv : (Point n × Point n) →L[ℝ] (Point n × Point n)) ((z₀, v₀) : Point n × Point n) := by
    rw [hcoe]; exact hGfd
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (4) `ContDiffAt ℝ 2 G (z₀,v₀)` from the general-centre Task D (piece ii), then apply the IFT.
  obtain ⟨U, hUopen, hUmem, hcdon⟩ :=
    uniformFlow_joint_contDiffOn_two_witness_generalCenter g gi hC hK z₀ hz₀ v₀ hv₀ρ
  have hexpCDAt : ContDiffAt ℝ 2
      (fun ξ : Point n × Point n => uniformFlowExp g gi hC hK ξ.1 ξ.2) ((z₀, v₀) : Point n × Point n) :=
    hcdon.contDiffAt (hUopen.mem_nhds hUmem)
  have hGCDAt : ContDiffAt ℝ 2
      (fun ξ : Point n × Point n => ((ξ.1, uniformFlowExp g gi hC hK ξ.1 ξ.2) : Point n × Point n))
      ((z₀, v₀) : Point n × Point n) :=
    (contDiff_fst.contDiffAt).prodMk hexpCDAt
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  refine ⟨fun q p => (hGCDAt.localInverse hG' hn2 (q, p)).2, ?_, ?_, ?_⟩
  · -- (a) joint `ContDiffAt ℝ 2`.
    have hLIcd : ContDiffAt ℝ 2 (hGCDAt.localInverse hG' hn2)
        ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) := by
      have h := hGCDAt.to_localInverse hG' hn2
      dsimp only at h
      exact h
    exact hLIcd.snd
  · -- (b) `chartCoherent z₀ (exp z₀ v₀) = v₀`.
    have h := hGCDAt.localInverse_apply_image hG' hn2
    dsimp only at h
    show (hGCDAt.localInverse hG' hn2 (z₀, uniformFlowExp g gi hC hK z₀ v₀)).2 = v₀
    rw [h]
  · -- (c) the coherent inverse-chart identity, from the eventual right inverse.
    have hs : HasStrictFDerivAt
        (fun ξ : Point n × Point n => ((ξ.1, uniformFlowExp g gi hC hK ξ.1 ξ.2) : Point n × Point n))
        (equiv : (Point n × Point n) →L[ℝ] (Point n × Point n)) ((z₀, v₀) : Point n × Point n) :=
      hGCDAt.hasStrictFDerivAt' hG' hn2
    have hev := hs.eventually_right_inverse
    dsimp only at hev
    filter_upwards [hev] with ξ hξ
    have hfst : (hGCDAt.localInverse hG' hn2 ξ).1 = ξ.1 := (Prod.ext_iff.mp hξ).1
    have hsnd : uniformFlowExp g gi hC hK (hGCDAt.localInverse hG' hn2 ξ).1
        (hGCDAt.localInverse hG' hn2 ξ).2 = ξ.2 := (Prod.ext_iff.mp hξ).2
    rw [hfst] at hsnd
    exact hsnd

/-- **★★ Task-F at the GENERAL CENTRE, WITH invertibility discharged — joint `ContDiffAt ℝ 2` of the
    concrete `uniformInverseChart` at `(z₀, exp z₀ v₀)`, for every small `v₀`.**  There is a radius
    `r₀ > 0` (bundling the flow radius, the germ radius `δ₀`, and the Neumann threshold `1/(C_D+1)`)
    such that for EVERY interior base `z₀ ∈ interior K` and EVERY velocity `‖v₀‖ < r₀`, the concrete
    `Classical.choose`-built `uniformInverseChart g gi hC hK` is jointly `ContDiffAt ℝ 2` at
    `(z₀, uniformFlowExp z₀ v₀)`.  The invertibility of the joint derivative away from `v = 0` is
    DERIVED (not assumed): below `r₀`, the banked near-identity Jacobian bound
    `uniformFlowExp_fderiv_near_id_quant` forces `‖B - id‖ < 1`, so `generalCenter_coherent_joint_chart`
    applies, and the coherent chart is reconciled with `uniformInverseChart` by local-inverse
    uniqueness (the germ property `uniformInverseChart_huniformChart`).  `r₀ > 0`, so this is
    genuinely NON-VACUOUS for every (curved) metric.  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_jointContDiffAt_generalCenter (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∀ z₀ : Point n, z₀ ∈ interior K → ∀ v₀ : Point n, ‖v₀‖ < r₀ →
      ContDiffAt ℝ 2
        (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2)
        ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) := by
  classical
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hnid⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  obtain ⟨δ₀, hδ₀pos, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  have hρpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  have hCD1pos : (0 : ℝ) < C_D + 1 := by linarith
  set r₀ : ℝ := min (min (uniformFlowRadius g gi hC hK) δ₀) (min ρ₀ (1 / (C_D + 1))) with hr₀def
  have hr₀pos : 0 < r₀ := by
    rw [hr₀def]
    refine lt_min (lt_min hρpos hδ₀pos) (lt_min hρ₀pos ?_)
    positivity
  refine ⟨r₀, hr₀pos, ?_⟩
  intro z₀ hz₀ v₀ hv₀
  have hz₀K : z₀ ∈ K := interior_subset hz₀
  -- unpack the four radius bounds.
  have hv₀ρ : ‖v₀‖ < uniformFlowRadius g gi hC hK := by
    have hle : r₀ ≤ uniformFlowRadius g gi hC hK := by
      rw [hr₀def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hv₀δ₀ : ‖v₀‖ < δ₀ := by
    have hle : r₀ ≤ δ₀ := by
      rw [hr₀def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hv₀ρ₀ : ‖v₀‖ < ρ₀ := by
    have hle : r₀ ≤ ρ₀ := by
      rw [hr₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hv₀inv : ‖v₀‖ < 1 / (C_D + 1) := by
    have hle : r₀ ≤ 1 / (C_D + 1) := by
      rw [hr₀def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  -- invertibility: `‖B - id‖ < 1` (DERIVED from the near-identity bound + Neumann threshold).
  have hInv : ‖fderiv ℝ (uniformFlowExp g gi hC hK z₀) v₀
                - ContinuousLinearMap.id ℝ (Point n)‖ < 1 := by
    have hb := hnid z₀ hz₀K v₀ hv₀ρ₀
    have hCDv : C_D * ‖v₀‖ < 1 := by
      have h1 : C_D * ‖v₀‖ ≤ C_D * (1 / (C_D + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hv₀inv) hCD0
      have h2 : C_D * (1 / (C_D + 1)) < 1 := by
        rw [mul_one_div, div_lt_one hCD1pos]; linarith
      linarith
    linarith [hb]
  -- the general-centre coherent chart.
  obtain ⟨chartCoherent, hcd, hval, hinv⟩ :=
    generalCenter_coherent_joint_chart g gi hC hK z₀ hz₀ v₀ hv₀ρ hInv
  -- reconciliation: `uniformInverseChart = chartCoherent` near `(z₀, exp z₀ v₀)`.
  have hEq : (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2)
      =ᶠ[nhds ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n)]
      (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2) := by
    -- base point stays in `interior K` (hence in `K`).
    have hball : ∀ᶠ ξ in nhds ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n),
        ξ.1 ∈ interior K := by
      have hopen : IsOpen {ξ : Point n × Point n | ξ.1 ∈ interior K} :=
        isOpen_interior.preimage continuous_fst
      exact hopen.mem_nhds hz₀
    -- the chart value stays within the germ radius `δ₀` (joint continuity + value `v₀`, `‖v₀‖<δ₀`).
    have hsmall : ∀ᶠ ξ in nhds ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n),
        chartCoherent ξ.1 ξ.2 ∈ Metric.ball (0 : Point n) δ₀ := by
      have hcont : ContinuousAt (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
          ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) := hcd.continuousAt
      refine hcont.eventually_mem ?_
      show Metric.ball (0 : Point n) δ₀ ∈ nhds (chartCoherent z₀ (uniformFlowExp g gi hC hK z₀ v₀))
      rw [hval]
      exact Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hv₀δ₀)
    filter_upwards [hinv, hball, hsmall] with ξ hξinv hξball hξsmall
    have hξ1K : ξ.1 ∈ K := interior_subset hξball
    set v : Point n := chartCoherent ξ.1 ξ.2 with hvdef
    have hvδ₀ : ‖v‖ < δ₀ := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hξsmall
    obtain ⟨hgerm, _hWc2⟩ := (hchart ξ.1 hξ1K).1 v hvδ₀
    have hleft : uniformInverseChart g gi hC hK ξ.1 (uniformFlowExp g gi hC hK ξ.1 v) = v :=
      hgerm.eq_of_nhds
    have hforward : uniformFlowExp g gi hC hK ξ.1 v = ξ.2 := hξinv
    rw [hforward] at hleft
    show uniformInverseChart g gi hC hK ξ.1 ξ.2 = chartCoherent ξ.1 ξ.2
    rw [← hvdef]; exact hleft
  exact hcd.congr_of_eventuallyEq hEq

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms generalCenter_coherent_joint_chart
#print axioms uniformInverseChart_jointContDiffAt_generalCenter
end AxiomChecks
