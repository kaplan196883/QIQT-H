/-
  UniformFlowCoherentJointChart — plan `tranquil-stargazing-fox.md` Task E: the genuinely COHERENT
  jointly-`ContDiffAt ℝ 2` geodesic exponential inverse chart, built ONCE from Mathlib's inverse
  function theorem applied to the augmented map `G(q,v) = (q, uniformFlowExp g gi hC hK q v)`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DELIVERABLE — plan Task-E target: a COHERENT joint local inverse `chartCoherent`.

  * `uniformFlow_coherent_joint_chart` — ★ for `K := Metric.closedBall q₀ 1`, there is a chart
    `chartCoherent : Point n → Point n → Point n` (the `.2`-component of Mathlib's IFT local inverse
    `G⁻¹` of `G(q,v) = (q, uniformFlowExp g gi hC hK q v)`) such that
      (1) `fun ξ => chartCoherent ξ.1 ξ.2` is jointly `ContDiffAt ℝ 2` at `(q₀, q₀)`;
      (2) `chartCoherent q₀ q₀ = 0`;
      (3) `∀ᶠ ξ in 𝓝 (q₀,q₀), uniformFlowExp g gi hC hK ξ.1 (chartCoherent ξ.1 ξ.2) = ξ.2`
          — the genuine COHERENT inverse-chart property (`exp_q (log_q p) = p` near the diagonal),
          built ONCE, globally coherent by construction, NO per-point `Classical.choose`.

  ## METHOD — one application of Mathlib's `ContDiffAt.to_localInverse`.
  The invertibility datum is `D G_{(q₀,0)}(h,w) = (h, h+w)`: at zero velocity the reference geodesic
  is CONSTANT (`uniformFlowExp_zero`), so both partial derivatives are the identity
    * `D_v uniformFlowExp(q₀,0) = id` — the velocity-slot derivative at zero (`uniformFlowExp_fderiv_
      near_id_quant` at `v = 0`, where the `C_D·‖v‖` near-identity bound becomes an EXACT identity);
    * `D_q uniformFlowExp(·,0)(q₀) = id` — the base-slot derivative, since `q ↦ uniformFlowExp q 0 = q`
      near `q₀` (`uniformFlowExp_zero`, so the map is literally the identity on a neighbourhood).
  The joint Fréchet derivative `L` (existing by `uniformFlow_joint_expEndpoint_hasFDerivAt_atBasepoint`)
  is identified with `(h,w) ↦ h+w` by restricting `L` to each slot via composition with the inclusions
  `w ↦ (q₀,w)` / `q ↦ (q,0)` and `HasFDerivAt.unique` against the two identity partials.  Then
  `G' := (h,w) ↦ (h, h+w)` is a continuous linear EQUIVALENCE (inverse `(a,b) ↦ (a, b-a)`, both
  continuous linear — `ContinuousLinearEquiv.equivOfInverse`), and Task-D's joint `ContDiffOn ℝ 2`
  (`uniformFlow_joint_contDiffOn_two_witness`) upgrades to `ContDiffAt ℝ 2 G (q₀,0)`, so
  `ContDiffAt.to_localInverse` delivers the coherent, jointly-`ContDiffAt ℝ 2` inverse at `G(q₀,0) =
  (q₀,q₀)`.  The block structure (`G⁻¹` preserves the `q`-slot) and the inverse-chart identity come
  from the local homeomorphism's eventual right-inverse.

  ## WHAT THIS FILE DOES NOT DO.
  It builds the COHERENT joint chart (Task E).  It does NOT reconcile with `uniformInverseChart`
  (Task F), NOT discharge the RNC hypotheses (Task G), and does NOT bear on `hCConv`.  a₁=R/6 remains
  CONDITIONAL on {hDuhamel, hDConv, hCConv}.
-/
import Mathlib
import QIQTH.UniformFlowJointContDiffTwoConcrete
import QIQTH.UniformFlowJointFDerivAtPointConcrete
import QIQTH.NearIsometryBudget
import QIQTH.UniformFlowNondeg

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★ Task-E target — the COHERENT jointly-`ContDiffAt ℝ 2` geodesic exp inverse chart.**
    For `K := Metric.closedBall q₀ 1`, there is a chart `chartCoherent : Point n → Point n → Point n`
    (the `.2`-slot of Mathlib's IFT local inverse of `G(q,v) = (q, uniformFlowExp g gi hC hK q v)`)
    that is jointly `ContDiffAt ℝ 2` at `(q₀,q₀)`, vanishes at the diagonal point, and satisfies the
    genuine inverse-chart identity `uniformFlowExp g gi hC hK q (chartCoherent q p) = p` near
    `(q₀,q₀)`.  Built ONCE, coherently, with NO per-point `Classical.choose`. -/
theorem uniformFlow_coherent_joint_chart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) :
    ∃ chartCoherent : Point n → Point n → Point n,
      ContDiffAt ℝ 2 (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
        ((q₀, q₀) : Point n × Point n) ∧
      chartCoherent q₀ q₀ = 0 ∧
      (∀ᶠ ξ in nhds ((q₀, q₀) : Point n × Point n),
        uniformFlowExp g gi hC (isCompact_closedBall q₀ 1) ξ.1 (chartCoherent ξ.1 ξ.2) = ξ.2) := by
  classical
  set hK : IsCompact (Metric.closedBall q₀ 1) := isCompact_closedBall q₀ 1 with hKdef
  set K : Set (Point n) := Metric.closedBall q₀ 1 with hKsetdef
  have hq₀K : q₀ ∈ K := by rw [hKsetdef]; exact Metric.mem_closedBall_self zero_le_one
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (1) the joint Fréchet derivative `L` of `uniformFlowExp` at `(q₀,0)`.
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρpos : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set r : ℝ := min 1 ρ with hrdef
  have hr : 0 < r := lt_min zero_lt_one hρpos
  have hqmem : ∀ ξ ∈ Metric.ball ((q₀, 0) : Point n × Point n) r, ξ.1 ∈ K := by
    intro ξ hξ
    rw [Metric.mem_ball] at hξ
    rw [hKsetdef, Metric.mem_closedBall]
    have hle : dist ξ.1 q₀ ≤ dist ξ ((q₀, 0) : Point n × Point n) := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    calc dist ξ.1 q₀ ≤ r := le_of_lt (lt_of_le_of_lt hle hξ)
      _ ≤ 1 := by rw [hrdef]; exact min_le_left _ _
  have hvmem : ∀ ξ ∈ Metric.ball ((q₀, 0) : Point n × Point n) r, ‖ξ.2‖ ≤ ρ := by
    intro ξ hξ
    rw [Metric.mem_ball] at hξ
    have hle : dist ξ.2 (0 : Point n) ≤ dist ξ ((q₀, 0) : Point n × Point n) := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    have hlt : ‖ξ.2‖ < r := by rw [← dist_zero_right]; exact lt_of_le_of_lt hle hξ
    calc ‖ξ.2‖ ≤ r := hlt.le
      _ ≤ ρ := by rw [hrdef]; exact min_le_right _ _
  obtain ⟨L, hL_exp⟩ :=
    uniformFlow_joint_expEndpoint_hasFDerivAt_atBasepoint g gi hC hK
      ((q₀, 0) : Point n × Point n) hr hqmem hvmem
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (2) velocity-slot identification: `L (0, w) = w`.
  have hinclV : HasFDerivAt (fun w : Point n => ((q₀, w) : Point n × Point n))
      ((0 : Point n →L[ℝ] Point n).prod (ContinuousLinearMap.id ℝ (Point n))) 0 :=
    (hasFDerivAt_const (q₀ : Point n) (0 : Point n)).prodMk (hasFDerivAt_id (0 : Point n))
  have hcompV := hL_exp.comp (0 : Point n) hinclV
  have h1v : fderiv ℝ (fun w : Point n => uniformFlowExp g gi hC hK q₀ w) 0
      = L.comp ((0 : Point n →L[ℝ] Point n).prod (ContinuousLinearMap.id ℝ (Point n))) :=
    hcompV.fderiv
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hnid⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  have hnid0 := hnid q₀ hq₀K 0 (by rw [norm_zero]; exact hρ₀pos)
  rw [norm_zero, mul_zero] at hnid0
  have hnid_exact : fderiv ℝ (fun w : Point n => uniformFlowExp g gi hC hK q₀ w) 0
      = ContinuousLinearMap.id ℝ (Point n) := sub_eq_zero.mp (norm_le_zero_iff.mp hnid0)
  have hLcompV : L.comp ((0 : Point n →L[ℝ] Point n).prod (ContinuousLinearMap.id ℝ (Point n)))
      = ContinuousLinearMap.id ℝ (Point n) := h1v.symm.trans hnid_exact
  have hL0w : ∀ w : Point n, L ((0, w) : Point n × Point n) = w := by
    intro w
    have := ContinuousLinearMap.ext_iff.mp hLcompV w
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using this
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (3) base-slot identification: `L (h, 0) = h`.
  have hinclQ : HasFDerivAt (fun q : Point n => ((q, (0 : Point n)) : Point n × Point n))
      ((ContinuousLinearMap.id ℝ (Point n)).prod (0 : Point n →L[ℝ] Point n)) q₀ :=
    (hasFDerivAt_id q₀).prodMk (hasFDerivAt_const (0 : Point n) q₀)
  have hcompQ := hL_exp.comp q₀ hinclQ
  have h1q : fderiv ℝ (fun q : Point n => uniformFlowExp g gi hC hK q 0) q₀
      = L.comp ((ContinuousLinearMap.id ℝ (Point n)).prod (0 : Point n →L[ℝ] Point n)) :=
    hcompQ.fderiv
  have hbaseEv : (fun q : Point n => uniformFlowExp g gi hC hK q 0) =ᶠ[nhds q₀] id := by
    filter_upwards [Metric.ball_mem_nhds q₀ one_pos] with q hq
    have hqK : q ∈ K := by
      rw [hKsetdef, Metric.mem_closedBall]
      exact le_of_lt (by rwa [Metric.mem_ball] at hq)
    exact uniformFlowExp_zero g gi hC hK q hqK
  have hbaseFD : HasFDerivAt (fun q : Point n => uniformFlowExp g gi hC hK q 0)
      (ContinuousLinearMap.id ℝ (Point n)) q₀ :=
    (hasFDerivAt_id q₀).congr_of_eventuallyEq hbaseEv
  have hLcompQ : L.comp ((ContinuousLinearMap.id ℝ (Point n)).prod (0 : Point n →L[ℝ] Point n))
      = ContinuousLinearMap.id ℝ (Point n) := h1q.symm.trans hbaseFD.fderiv
  have hLh0 : ∀ h : Point n, L ((h, 0) : Point n × Point n) = h := by
    intro h
    have := ContinuousLinearMap.ext_iff.mp hLcompQ h
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using this
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (4) assemble `L (h, w) = h + w`, hence `L = fst + snd`.
  have hLhw : ∀ hh ww : Point n, L ((hh, ww) : Point n × Point n) = hh + ww := by
    intro hh ww
    have e : ((hh, ww) : Point n × Point n)
        = ((hh, 0) : Point n × Point n) + ((0, ww) : Point n × Point n) := by
      rw [Prod.mk_add_mk, add_zero, zero_add]
    rw [e, map_add, hLh0 hh, hL0w ww]
  have hLeqfs : L = (ContinuousLinearMap.fst ℝ (Point n) (Point n))
      + (ContinuousLinearMap.snd ℝ (Point n) (Point n)) := by
    apply ContinuousLinearMap.ext
    intro x
    have hx : L x = x.1 + x.2 := by
      have := hLhw x.1 x.2
      rwa [Prod.mk.eta] at this
    rw [hx, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
  rw [hLeqfs] at hL_exp
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (5) the augmented map `G` and its derivative `f₁ = (h,w) ↦ (h, h+w)`.
  set f₁ : (Point n × Point n) →L[ℝ] (Point n × Point n) :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).prod
      ((ContinuousLinearMap.fst ℝ (Point n) (Point n))
        + (ContinuousLinearMap.snd ℝ (Point n) (Point n))) with hf₁def
  set f₂ : (Point n × Point n) →L[ℝ] (Point n × Point n) :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).prod
      ((ContinuousLinearMap.snd ℝ (Point n) (Point n))
        - (ContinuousLinearMap.fst ℝ (Point n) (Point n))) with hf₂def
  have hGfd : HasFDerivAt
      (fun ξ : Point n × Point n => ((ξ.1, uniformFlowExp g gi hC hK ξ.1 ξ.2) : Point n × Point n))
      f₁ ((q₀, 0) : Point n × Point n) := by
    rw [hf₁def]
    exact (hasFDerivAt_fst).prodMk hL_exp
  -- `f₁` is a continuous linear equivalence with explicit inverse `f₂`.
  have hli : Function.LeftInverse f₂ f₁ := by
    intro x
    have e1 : f₁ x = ((x.1, x.1 + x.2) : Point n × Point n) := by
      simp [hf₁def, ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    rw [e1]
    simp [hf₂def, ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hri : Function.RightInverse f₂ f₁ := by
    intro x
    have e2 : f₂ x = ((x.1, x.2 - x.1) : Point n × Point n) := by
      simp [hf₂def, ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    rw [e2]
    simp [hf₁def, ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  set equiv : (Point n × Point n) ≃L[ℝ] (Point n × Point n) :=
    ContinuousLinearEquiv.equivOfInverse f₁ f₂ hli hri with hequivdef
  have hcoe : (equiv : (Point n × Point n) →L[ℝ] (Point n × Point n)) = f₁ := by
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearEquiv.coe_coe, hequivdef]
    exact ContinuousLinearEquiv.equivOfInverse_apply f₁ f₂ hli hri x
  have hG' : HasFDerivAt
      (fun ξ : Point n × Point n => ((ξ.1, uniformFlowExp g gi hC hK ξ.1 ξ.2) : Point n × Point n))
      (equiv : (Point n × Point n) →L[ℝ] (Point n × Point n)) ((q₀, 0) : Point n × Point n) := by
    rw [hcoe]; exact hGfd
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (6) `ContDiffAt ℝ 2 G (q₀,0)` from Task D, then apply the IFT.
  obtain ⟨U, hUopen, hUmem, hcdon⟩ := uniformFlow_joint_contDiffOn_two_witness g gi hC q₀
  have hexpCDAt : ContDiffAt ℝ 2
      (fun ξ : Point n × Point n => uniformFlowExp g gi hC hK ξ.1 ξ.2) ((q₀, 0) : Point n × Point n) :=
    hcdon.contDiffAt (hUopen.mem_nhds hUmem)
  have hGCDAt : ContDiffAt ℝ 2
      (fun ξ : Point n × Point n => ((ξ.1, uniformFlowExp g gi hC hK ξ.1 ξ.2) : Point n × Point n))
      ((q₀, 0) : Point n × Point n) :=
    (contDiff_fst.contDiffAt).prodMk hexpCDAt
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  -- the value of `G` at `(q₀,0)` is `(q₀,q₀)`.
  have hGval : ((q₀, uniformFlowExp g gi hC hK q₀ 0) : Point n × Point n) = ((q₀, q₀) : Point n × Point n) := by
    rw [uniformFlowExp_zero g gi hC hK q₀ hq₀K]
  -- the coherent chart.
  refine ⟨fun q p => (hGCDAt.localInverse hG' hn2 (q, p)).2, ?_, ?_, ?_⟩
  · -- (a) joint `ContDiffAt ℝ 2`.
    have hLIcd : ContDiffAt ℝ 2 (hGCDAt.localInverse hG' hn2) ((q₀, q₀) : Point n × Point n) := by
      have h := hGCDAt.to_localInverse hG' hn2
      dsimp only at h
      rwa [hGval] at h
    exact hLIcd.snd
  · -- (b) `chartCoherent q₀ q₀ = 0`.
    have h := hGCDAt.localInverse_apply_image hG' hn2
    dsimp only at h
    rw [hGval] at h
    show (hGCDAt.localInverse hG' hn2 (q₀, q₀)).2 = 0
    rw [h]
  · -- (c) the coherent inverse-chart identity, from the eventual right inverse.
    have hs : HasStrictFDerivAt
        (fun ξ : Point n × Point n => ((ξ.1, uniformFlowExp g gi hC hK ξ.1 ξ.2) : Point n × Point n))
        (equiv : (Point n × Point n) →L[ℝ] (Point n × Point n)) ((q₀, 0) : Point n × Point n) :=
      hGCDAt.hasStrictFDerivAt' hG' hn2
    have hev := hs.eventually_right_inverse
    dsimp only at hev
    rw [hGval] at hev
    filter_upwards [hev] with ξ hξ
    -- `hξ : ((LI ξ).1, uniformFlowExp .. (LI ξ).1 (LI ξ).2) = ξ`.
    have hfst : (hGCDAt.localInverse hG' hn2 ξ).1 = ξ.1 := (Prod.ext_iff.mp hξ).1
    have hsnd : uniformFlowExp g gi hC hK (hGCDAt.localInverse hG' hn2 ξ).1
        (hGCDAt.localInverse hG' hn2 ξ).2 = ξ.2 := (Prod.ext_iff.mp hξ).2
    rw [hfst] at hsnd
    exact hsnd

end QIQTH.ExpMap
