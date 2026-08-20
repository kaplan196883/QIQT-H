/-
  UniformFlowCoherentJointChartGeneralK — GENERALIZATION of J4-855
  (`UniformFlowCoherentJointChart.lean`) and its Task-D dependency
  (`uniformFlow_joint_contDiffOn_two_witness`, `UniformFlowJointContDiffTwoConcrete.lean`)
  from the FIXED compact `K := Metric.closedBall q₀ 1` to an ARBITRARY compact `K` and an ARBITRARY
  INTERIOR base point `z₀ ∈ interior K`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing.  No `sorry`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise, no existing file edited.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DELIVERABLES.

  * `uniformFlowExp_eq_of_admissible` — **cross-`K` agreement of the flow-exp endpoint.**  For TWO
    compact sets `K₁`, `K₂` both containing the base point `q`, and `‖w‖` within BOTH uniform radii,
    the two flow-exp endpoints coincide:
        `uniformFlowExp g gi hC hK₁ q w = uniformFlowExp g gi hC hK₂ q w`.
    Proof = ODE uniqueness: both tubes solve the SAME geodesic phase-ODE with the SAME initial
    condition `(q, w)`, and (confinement) both stay in a common convex compact ball where
    `geodesicField` is Lipschitz; Mathlib's two-trajectory comparison at `δ = dist q q = 0` forces
    equality on `[0,1]`, project the position slot at `t = 1`.  This is the object-independence that
    lets the fixed-`K` Task-D transport to a general `K`.

  * `uniformFlow_joint_contDiffOn_two_witness_generalK` — **general-`K` Task D.**  For an arbitrary
    compact `K` and interior base point `z₀ ∈ interior K`, there is an OPEN neighbourhood `U` of
    `(z₀, 0)` on which `fun ξ => uniformFlowExp g gi hC hK ξ.1 ξ.2` is jointly `ContDiffOn ℝ 2`.
    Proof: the fixed-radius closed-ball Task-D at `z₀` (for `K₂ := closedBall z₀ 1`) supplies the
    joint `ContDiffOn ℝ 2` of the `hK₂`-exp near `(z₀,0)`; on a small neighbourhood where the base
    point lands in `K ∩ K₂` and the velocity is within both radii, `uniformFlowExp_eq_of_admissible`
    equates it to the `hK`-exp, transport via `ContDiffOn.congr`.

  * `uniformFlow_coherent_joint_chart_generalK` — **general-`K` J4-855.**  For arbitrary compact `K`
    and interior base point `z₀ ∈ interior K`, there is a coherent chart `chartCoherent` jointly
    `ContDiffAt ℝ 2` at `(z₀,z₀)`, vanishing at the diagonal point, with the coherent inverse-chart
    identity near `(z₀,z₀)` — verbatim J4-855's IFT construction, now with the fixed `K` replaced by
    the abstract `K` (its only fixed-`K` dependency, Task D, is supplied by the general-`K` version).

  ## WHAT THIS FILE DOES NOT DO.
  It builds the general-`K` COHERENT joint chart at an interior base point.  It does NOT reconcile
  with `uniformInverseChart` (that is the general-`K` Task F, a separate file), NOT discharge the RNC
  hypotheses, and does NOT bear on `hCConv`.  a₁=R/6 remains CONDITIONAL.
-/
import Mathlib
import QIQTH.UniformFlowJointContDiffTwoConcrete
import QIQTH.UniformFlowJointFDerivAtPointConcrete
import QIQTH.NearIsometryBudget
import QIQTH.UniformFlowNondeg
import QIQTH.GeodesicGronwall

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **Cross-`K` agreement of the uniform flow-exp endpoint.**  For two compact sets `K₁`, `K₂` both
    admitting the base point `q` and both admitting the velocity `w` (`‖w‖ ≤ ρ_{Kᵢ}`), the two
    flow-exp endpoints coincide.  ODE uniqueness: identical geodesic phase-ODE, identical IC `(q,w)`,
    both confined to a common convex compact ball; Mathlib's two-trajectory comparison at `δ = 0`. -/
theorem uniformFlowExp_eq_of_admissible (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K₁ K₂ : Set (Point n)} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (q w : Point n) (hq₁ : q ∈ K₁) (hq₂ : q ∈ K₂)
    (hw₁ : ‖w‖ ≤ uniformFlowRadius g gi hC hK₁)
    (hw₂ : ‖w‖ ≤ uniformFlowRadius g gi hC hK₂) :
    uniformFlowExp g gi hC hK₁ q w = uniformFlowExp g gi hC hK₂ q w := by
  set C₀₁ : ℝ := uniformFlowConst g gi hC hK₁ with hC₀₁def
  set C₀₂ : ℝ := uniformFlowConst g gi hC hK₂ with hC₀₂def
  have hC₀₁0 : 0 ≤ C₀₁ := uniformFlowConst_nonneg g gi hC hK₁
  have hC₀₂0 : 0 ≤ C₀₂ := uniformFlowConst_nonneg g gi hC hK₂
  -- common confinement ball.
  set Rrad : ℝ := ‖((q, 0) : Point n × Point n)‖ + (C₀₁ + C₀₂) * ‖w‖ with hRraddef
  obtain ⟨L, hLip⟩ :=
    QIQTH.GeodesicGronwall.geodesicField_lipschitzOnWith_closedBall g gi hC Rrad
  -- specs of both tubes.
  have hic₁ := uniformFlowTube_spec_ic g gi hC hK₁ q hq₁ w hw₁
  have hode₁ := uniformFlowTube_spec_ode g gi hC hK₁ q hq₁ w hw₁
  have hconf₁ := uniformFlowTube_spec_conf g gi hC hK₁ q hq₁ w hw₁
  have hic₂ := uniformFlowTube_spec_ic g gi hC hK₂ q hq₂ w hw₂
  have hode₂ := uniformFlowTube_spec_ode g gi hC hK₂ q hq₂ w hw₂
  have hconf₂ := uniformFlowTube_spec_conf g gi hC hK₂ q hq₂ w hw₂
  have hIco : ∀ s ∈ Set.Ico (0 : ℝ) 1, s ∈ Set.Ioo (-2 : ℝ) 2 := by
    intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hIcc : ∀ s ∈ Set.Icc (0 : ℝ) 1, s ∈ Set.Ioo (-2 : ℝ) 2 := by
    intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- both tubes live in `closedBall 0 Rrad`.
  have hmem₁ : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      uniformFlowTube g gi hC hK₁ q w s ∈ Metric.closedBall (0 : Point n × Point n) Rrad := by
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := hconf₁ s (Set.Ico_subset_Icc_self hs)
    calc ‖uniformFlowTube g gi hC hK₁ q w s‖
        ≤ ‖((q, 0) : Point n × Point n)‖
            + ‖uniformFlowTube g gi hC hK₁ q w s - ((q, 0) : Point n × Point n)‖ := by
          have := norm_add_le ((q, 0) : Point n × Point n)
            (uniformFlowTube g gi hC hK₁ q w s - ((q, 0) : Point n × Point n))
          simpa using this
      _ ≤ ‖((q, 0) : Point n × Point n)‖ + C₀₁ * ‖w‖ := by linarith [h1]
      _ ≤ Rrad := by rw [hRraddef]; nlinarith [mul_nonneg hC₀₂0 (norm_nonneg w)]
  have hmem₂ : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      uniformFlowTube g gi hC hK₂ q w s ∈ Metric.closedBall (0 : Point n × Point n) Rrad := by
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := hconf₂ s (Set.Ico_subset_Icc_self hs)
    calc ‖uniformFlowTube g gi hC hK₂ q w s‖
        ≤ ‖((q, 0) : Point n × Point n)‖
            + ‖uniformFlowTube g gi hC hK₂ q w s - ((q, 0) : Point n × Point n)‖ := by
          have := norm_add_le ((q, 0) : Point n × Point n)
            (uniformFlowTube g gi hC hK₂ q w s - ((q, 0) : Point n × Point n))
          simpa using this
      _ ≤ ‖((q, 0) : Point n × Point n)‖ + C₀₂ * ‖w‖ := by linarith [h1]
      _ ≤ Rrad := by rw [hRraddef]; nlinarith [mul_nonneg hC₀₁0 (norm_nonneg w)]
  have hcont₁ : ContinuousOn (uniformFlowTube g gi hC hK₁ q w) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => ((hode₁ s (hIcc s hs)).continuousAt).continuousWithinAt
  have hcont₂ : ContinuousOn (uniformFlowTube g gi hC hK₂ q w) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => ((hode₂ s (hIcc s hs)).continuousAt).continuousWithinAt
  have haIC : dist (uniformFlowTube g gi hC hK₁ q w 0) (uniformFlowTube g gi hC hK₂ q w 0)
      ≤ (0 : ℝ) := by rw [hic₁, hic₂, dist_self]
  have hbnd := dist_le_of_trajectories_ODE_of_mem
    (v := fun (_ : ℝ) (p : Point n × Point n) => geodesicField g gi p)
    (s := fun (_ : ℝ) => Metric.closedBall (0 : Point n × Point n) Rrad)
    (K := L) (a := 0) (b := 1)
    (f := uniformFlowTube g gi hC hK₁ q w) (g := uniformFlowTube g gi hC hK₂ q w)
    (δ := (0 : ℝ))
    (fun s _ => hLip)
    hcont₁
    (fun s hs => (hode₁ s (hIco s hs)).hasDerivWithinAt)
    hmem₁
    hcont₂
    (fun s hs => (hode₂ s (hIco s hs)).hasDerivWithinAt)
    hmem₂
    haIC
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hd := hbnd 1 ht1
  simp only [zero_mul] at hd
  have heqtube : uniformFlowTube g gi hC hK₁ q w 1 = uniformFlowTube g gi hC hK₂ q w 1 :=
    dist_le_zero.mp hd
  rw [uniformFlowExp_eq, uniformFlowExp_eq, heqtube]

/-- **★ general-`K` Task D.**  For an ARBITRARY compact `K` and an ARBITRARY interior base point
    `z₀ ∈ interior K`, there is an OPEN neighbourhood `U` of `(z₀, 0)` on which
    `fun ξ => uniformFlowExp g gi hC hK ξ.1 ξ.2` is jointly `ContDiffOn ℝ 2`.  Transported from the
    fixed-radius closed-ball Task-D (`uniformFlow_joint_contDiffOn_two_witness` at `z₀`) via the
    cross-`K` agreement `uniformFlowExp_eq_of_admissible` and `ContDiffOn.congr`. -/
theorem uniformFlow_joint_contDiffOn_two_witness_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K) :
    ∃ (U : Set (Point n × Point n)), IsOpen U ∧
      ((z₀, (0 : Point n)) : Point n × Point n) ∈ U ∧
      ContDiffOn ℝ 2
        (fun ξ : Point n × Point n => uniformFlowExp g gi hC hK ξ.1 ξ.2) U := by
  classical
  -- fixed-radius reference set `K₂ := closedBall z₀ 1`.
  set hK₂ : IsCompact (Metric.closedBall z₀ 1) := isCompact_closedBall z₀ 1 with hK₂def
  -- fixed-`K` Task D at `z₀`.
  obtain ⟨U₂, hU₂open, hU₂mem, hcd₂⟩ := uniformFlow_joint_contDiffOn_two_witness g gi hC z₀
  -- interior gives a ball `⊆ K`.
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz₀)
  -- uniform radii.
  set ρ₁ : ℝ := uniformFlowRadius g gi hC hK with hρ₁def
  set ρ₂ : ℝ := uniformFlowRadius g gi hC hK₂ with hρ₂def
  have hρ₁pos : 0 < ρ₁ := uniformFlowRadius_pos g gi hC hK
  have hρ₂pos : 0 < ρ₂ := uniformFlowRadius_pos g gi hC hK₂
  -- neighbourhood radius: small enough for `K`-membership (`< r₁`, `< 1`) and both velocity bounds.
  set ε : ℝ := min (min r₁ 1) (min ρ₁ ρ₂) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (lt_min hr₁pos zero_lt_one) (lt_min hρ₁pos hρ₂pos)
  set U : Set (Point n × Point n) := U₂ ∩ Metric.ball ((z₀, 0) : Point n × Point n) ε with hUdef
  have hUopen : IsOpen U := hU₂open.inter Metric.isOpen_ball
  have hUmem : ((z₀, (0 : Point n)) : Point n × Point n) ∈ U := by
    rw [hUdef]; exact ⟨hU₂mem, Metric.mem_ball_self hεpos⟩
  refine ⟨U, hUopen, hUmem, ?_⟩
  -- pointwise agreement on `U`.
  have hagree : ∀ ξ ∈ U,
      uniformFlowExp g gi hC hK₂ ξ.1 ξ.2 = uniformFlowExp g gi hC hK ξ.1 ξ.2 := by
    intro ξ hξ
    have hξball : ξ ∈ Metric.ball ((z₀, 0) : Point n × Point n) ε := hξ.2
    rw [Metric.mem_ball] at hξball
    -- base distance and velocity norm both `< ε`.
    have hbdist : dist ξ.1 z₀ < ε := by
      calc dist ξ.1 z₀ ≤ dist ξ ((z₀, 0) : Point n × Point n) := by
            rw [Prod.dist_eq]; exact le_max_left _ _
        _ < ε := hξball
    have hvnorm : ‖ξ.2‖ < ε := by
      rw [← dist_zero_right]
      calc dist ξ.2 (0 : Point n) ≤ dist ξ ((z₀, 0) : Point n × Point n) := by
            rw [Prod.dist_eq]; exact le_max_right _ _
        _ < ε := hξball
    -- `ξ.1 ∈ K`.
    have hξ1K : ξ.1 ∈ K := by
      apply interior_subset
      apply hr₁sub
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hbdist (le_trans (min_le_left _ _) (min_le_left _ _))
    -- `ξ.1 ∈ closedBall z₀ 1`.
    have hξ1K₂ : ξ.1 ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (lt_of_lt_of_le hbdist (le_trans (min_le_left _ _) (min_le_right _ _)))
    -- velocity bounds.
    have hvρ₁ : ‖ξ.2‖ ≤ ρ₁ :=
      le_of_lt (lt_of_lt_of_le hvnorm (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hvρ₂ : ‖ξ.2‖ ≤ ρ₂ :=
      le_of_lt (lt_of_lt_of_le hvnorm (le_trans (min_le_right _ _) (min_le_right _ _)))
    exact uniformFlowExp_eq_of_admissible g gi hC hK₂ hK ξ.1 ξ.2 hξ1K₂ hξ1K hvρ₂ hvρ₁
  -- restrict the fixed-`K` `ContDiffOn ℝ 2` to `U` and transport across the agreement.
  have hcd₂U : ContDiffOn ℝ 2
      (fun ξ : Point n × Point n => uniformFlowExp g gi hC hK₂ ξ.1 ξ.2) U :=
    hcd₂.mono (Set.inter_subset_left)
  exact hcd₂U.congr (fun ξ hξ => (hagree ξ hξ).symm)

/-- **★ general-`K` J4-855 — the COHERENT jointly-`ContDiffAt ℝ 2` geodesic exp inverse chart at an
    arbitrary interior base point.**  For an ARBITRARY compact `K` and interior base point
    `z₀ ∈ interior K`, there is a chart `chartCoherent : Point n → Point n → Point n` (the `.2`-slot of
    Mathlib's IFT local inverse of `G(q,v) = (q, uniformFlowExp g gi hC hK q v)`) that is jointly
    `ContDiffAt ℝ 2` at `(z₀,z₀)`, vanishes at the diagonal point, and satisfies the genuine
    inverse-chart identity `uniformFlowExp g gi hC hK q (chartCoherent q p) = p` near `(z₀,z₀)`.  Built
    ONCE, coherently, with NO per-point `Classical.choose`.  Verbatim J4-855 with the fixed
    `closedBall z₀ 1` replaced by the abstract `K` (its Task-D dependency supplied by the general-`K`
    version above). -/
theorem uniformFlow_coherent_joint_chart_generalK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z₀ : Point n) (hz₀ : z₀ ∈ interior K) :
    ∃ chartCoherent : Point n → Point n → Point n,
      ContDiffAt ℝ 2 (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2)
        ((z₀, z₀) : Point n × Point n) ∧
      chartCoherent z₀ z₀ = 0 ∧
      (∀ᶠ ξ in nhds ((z₀, z₀) : Point n × Point n),
        uniformFlowExp g gi hC hK ξ.1 (chartCoherent ξ.1 ξ.2) = ξ.2) := by
  classical
  have hq₀K : z₀ ∈ K := interior_subset hz₀
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz₀)
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (1) the joint Fréchet derivative `L` of `uniformFlowExp` at `(z₀,0)`.
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  have hρpos : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  set r : ℝ := min r₁ ρ with hrdef
  have hr : 0 < r := lt_min hr₁pos hρpos
  have hqmem : ∀ ξ ∈ Metric.ball ((z₀, 0) : Point n × Point n) r, ξ.1 ∈ K := by
    intro ξ hξ
    rw [Metric.mem_ball] at hξ
    apply interior_subset; apply hr₁sub; rw [Metric.mem_ball]
    have hle : dist ξ.1 z₀ ≤ dist ξ ((z₀, 0) : Point n × Point n) := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    calc dist ξ.1 z₀ ≤ dist ξ ((z₀, 0) : Point n × Point n) := hle
      _ < r := hξ
      _ ≤ r₁ := by rw [hrdef]; exact min_le_left _ _
  have hvmem : ∀ ξ ∈ Metric.ball ((z₀, 0) : Point n × Point n) r, ‖ξ.2‖ ≤ ρ := by
    intro ξ hξ
    rw [Metric.mem_ball] at hξ
    have hle : dist ξ.2 (0 : Point n) ≤ dist ξ ((z₀, 0) : Point n × Point n) := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    have hlt : ‖ξ.2‖ < r := by rw [← dist_zero_right]; exact lt_of_le_of_lt hle hξ
    calc ‖ξ.2‖ ≤ r := hlt.le
      _ ≤ ρ := by rw [hrdef]; exact min_le_right _ _
  obtain ⟨L, hL_exp⟩ :=
    uniformFlow_joint_expEndpoint_hasFDerivAt_atBasepoint g gi hC hK
      ((z₀, 0) : Point n × Point n) hr hqmem hvmem
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (2) velocity-slot identification: `L (0, w) = w`.
  have hinclV : HasFDerivAt (fun w : Point n => ((z₀, w) : Point n × Point n))
      ((0 : Point n →L[ℝ] Point n).prod (ContinuousLinearMap.id ℝ (Point n))) 0 :=
    (hasFDerivAt_const (z₀ : Point n) (0 : Point n)).prodMk (hasFDerivAt_id (0 : Point n))
  have hcompV := hL_exp.comp (0 : Point n) hinclV
  have h1v : fderiv ℝ (fun w : Point n => uniformFlowExp g gi hC hK z₀ w) 0
      = L.comp ((0 : Point n →L[ℝ] Point n).prod (ContinuousLinearMap.id ℝ (Point n))) :=
    hcompV.fderiv
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hnid⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  have hnid0 := hnid z₀ hq₀K 0 (by rw [norm_zero]; exact hρ₀pos)
  rw [norm_zero, mul_zero] at hnid0
  have hnid_exact : fderiv ℝ (fun w : Point n => uniformFlowExp g gi hC hK z₀ w) 0
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
      ((ContinuousLinearMap.id ℝ (Point n)).prod (0 : Point n →L[ℝ] Point n)) z₀ :=
    (hasFDerivAt_id z₀).prodMk (hasFDerivAt_const (0 : Point n) z₀)
  have hcompQ := hL_exp.comp z₀ hinclQ
  have h1q : fderiv ℝ (fun q : Point n => uniformFlowExp g gi hC hK q 0) z₀
      = L.comp ((ContinuousLinearMap.id ℝ (Point n)).prod (0 : Point n →L[ℝ] Point n)) :=
    hcompQ.fderiv
  have hbaseEv : (fun q : Point n => uniformFlowExp g gi hC hK q 0) =ᶠ[nhds z₀] id := by
    filter_upwards [Metric.ball_mem_nhds z₀ hr₁pos] with q hq
    have hqK : q ∈ K := interior_subset (hr₁sub hq)
    exact uniformFlowExp_zero g gi hC hK q hqK
  have hbaseFD : HasFDerivAt (fun q : Point n => uniformFlowExp g gi hC hK q 0)
      (ContinuousLinearMap.id ℝ (Point n)) z₀ :=
    (hasFDerivAt_id z₀).congr_of_eventuallyEq hbaseEv
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
      f₁ ((z₀, 0) : Point n × Point n) := by
    rw [hf₁def]
    exact (hasFDerivAt_fst).prodMk hL_exp
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
      (equiv : (Point n × Point n) →L[ℝ] (Point n × Point n)) ((z₀, 0) : Point n × Point n) := by
    rw [hcoe]; exact hGfd
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- (6) `ContDiffAt ℝ 2 G (z₀,0)` from general-`K` Task D, then apply the IFT.
  obtain ⟨U, hUopen, hUmem, hcdon⟩ :=
    uniformFlow_joint_contDiffOn_two_witness_generalK g gi hC hK z₀ hz₀
  have hexpCDAt : ContDiffAt ℝ 2
      (fun ξ : Point n × Point n => uniformFlowExp g gi hC hK ξ.1 ξ.2) ((z₀, 0) : Point n × Point n) :=
    hcdon.contDiffAt (hUopen.mem_nhds hUmem)
  have hGCDAt : ContDiffAt ℝ 2
      (fun ξ : Point n × Point n => ((ξ.1, uniformFlowExp g gi hC hK ξ.1 ξ.2) : Point n × Point n))
      ((z₀, 0) : Point n × Point n) :=
    (contDiff_fst.contDiffAt).prodMk hexpCDAt
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hGval : ((z₀, uniformFlowExp g gi hC hK z₀ 0) : Point n × Point n)
      = ((z₀, z₀) : Point n × Point n) := by
    rw [uniformFlowExp_zero g gi hC hK z₀ hq₀K]
  refine ⟨fun q p => (hGCDAt.localInverse hG' hn2 (q, p)).2, ?_, ?_, ?_⟩
  · have hLIcd : ContDiffAt ℝ 2 (hGCDAt.localInverse hG' hn2) ((z₀, z₀) : Point n × Point n) := by
      have h := hGCDAt.to_localInverse hG' hn2
      dsimp only at h
      rwa [hGval] at h
    exact hLIcd.snd
  · have h := hGCDAt.localInverse_apply_image hG' hn2
    dsimp only at h
    rw [hGval] at h
    show (hGCDAt.localInverse hG' hn2 (z₀, z₀)).2 = 0
    rw [h]
  · have hs : HasStrictFDerivAt
        (fun ξ : Point n × Point n => ((ξ.1, uniformFlowExp g gi hC hK ξ.1 ξ.2) : Point n × Point n))
        (equiv : (Point n × Point n) →L[ℝ] (Point n × Point n)) ((z₀, 0) : Point n × Point n) :=
      hGCDAt.hasStrictFDerivAt' hG' hn2
    have hev := hs.eventually_right_inverse
    dsimp only at hev
    rw [hGval] at hev
    filter_upwards [hev] with ξ hξ
    have hfst : (hGCDAt.localInverse hG' hn2 ξ).1 = ξ.1 := (Prod.ext_iff.mp hξ).1
    have hsnd : uniformFlowExp g gi hC hK (hGCDAt.localInverse hG' hn2 ξ).1
        (hGCDAt.localInverse hG' hn2 ξ).2 = ξ.2 := (Prod.ext_iff.mp hξ).2
    rw [hfst] at hsnd
    exact hsnd

end QIQTH.ExpMap
