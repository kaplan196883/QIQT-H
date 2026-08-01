/-
  UniformFlowJetZero — J4-82: the `uniformFlowExp` inverse-metric RNC jet-at-`0` deviation `hdev`.

  ## Context — the ONE remaining consumer metric-side firewall.

  `cutoffResidual_expPullback_hEboundW` (`RecenterCutoffC3.lean:97`) consumes, on the metric side, the
  quadratic deviation

    `hdev : ∀ᶠ v in 𝓝 0, ∀ i j, |g̃⁻¹(v) i j − δ_ij| ≤ M · rncRadialSq v`

  (the `O(r²)` decay of the pullback inverse metric off the RNC centre).  J4-81
  (`UniformFlowMetricInvProps.lean`) delivered every OTHER consumer-shaped inverse-metric input over the
  uniform-flow endpoint map `uniformFlowExp g gi hC hK q` — the ONLY remaining firewall was `hdev`.

  ## What this file delivers.

  This file DISCHARGES `hdev` for `uniformFlowPullbackMetricInv` (capstone
  `uniformFlowPullbackMetricInv_dev`) by a TRANSFER + TAYLOR route:

    * `uniformFlowPullbackMetricInv_eq_expPullbackMetricInv_eventually` — the WELD transfer: on the open
      overlap ball around `0`, `uniformFlowExp g gi hC hK q = expMap g gi hC q` (ODE-uniqueness bridge
      `expMap_eq_uniformFlowExp_on_overlap`, J4-20).  Equal maps ⟹ equal Fréchet derivatives
      (`EventuallyEq.fderiv_eq`) ⟹ equal pullback metrics (same formula in `F`, `DF`) ⟹ equal operator
      inverses (`Ring.inverse` of equal CLMs) ⟹ `g̃⁻¹` entries agree `=ᶠ[𝓝 0]`.  NO nondegeneracy needed.

    * `expPullbackMetricInv_dev` — the TAYLOR bound on the `expPullbackMetric` side, where the RNC jets are
      already proven: `g̃⁻¹(0) = δ` (frame), `∂g̃⁻¹(0) = 0` (`pd_expPullbackMetricInv_zero_clean`, this
      file — a hypothesis-clean re-derivation avoiding the `∀y` nondegeneracy of the old
      `pd_expPullbackMetricInv_zero`) and `g̃⁻¹ ∈ C²` (`expPullbackMetricInv_contDiffAt_two`).  A `C²`
      field vanishing to 2nd order is `O(r²)` (`RNCDecay.decay_order_two_radial`, fed by the generic
      `contDiffAt_two_quadratic_decay` of this file).

  Combining the two (`filter_upwards`) gives `hdev` for `uniformFlowPullbackMetricInv`.

  ## Honest hypotheses (all genuine, satisfiable by `g = gi = δ`, none is the conclusion).

  `hg` (metric `C^∞`), `hC` (Christoffel `C^∞`), `IsCompact K`, `hgsymm` (metric symmetry),
  `hinvF` (the ambient inverse relation `∑σ g_{aσ} gi_{σb} = δ`, standard `g/gi` pairing) and the
  per-`q` orthonormal-frame normalization `hframe : g q = δ` (identical to the consumer's `hframe`).
  NO `hgnd`, NO `expRho` in any statement (only in proof-internal welds), NO `sorry`, NO new axioms.
  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowMetricInvProps
import QIQTH.RecenterConnectC3
import QIQTH.PullbackMetricNondegNearZero
import QIQTH.UniformFlowNondeg
import QIQTH.ExpMap
import Mathlib

open QIQTH.Curvature QIQTH.PullbackMetric QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.HeatResidualBound QIQTH.LaplaceBeltrami
open Set Filter
open scoped Topology BigOperators Matrix

namespace QIQTH.ExpMap

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### General calculus helpers. -/

/-- **`pd` of an eventually-constant field vanishes at `0`.**  If `F =ᶠ[𝓝 0] const c`, then every
    coordinate partial `∂_e F(0) = 0`.  (`pd` sees only the germ; the coordinate ray `t ↦ update 0 e t`
    tends to `0`, so `F` is locally constant along it.) -/
theorem pd_eventuallyEq_const_zero {F : Point n → ℝ} {c : ℝ} (e : Fin n)
    (h : F =ᶠ[nhds (0 : Point n)] (fun _ => c)) :
    pd F e (0 : Point n) = 0 := by
  have hγ0 : Function.update (0 : Point n) e ((0 : Point n) e) = (0 : Point n) :=
    Function.update_eq_self e (0 : Point n)
  have htend : Filter.Tendsto (fun t : ℝ => Function.update (0 : Point n) e t)
      (nhds ((0 : Point n) e)) (nhds (0 : Point n)) := by
    have hc : ContinuousAt (Function.update (0 : Point n) e) ((0 : Point n) e) :=
      (hasDerivAt_update (0 : Point n) e ((0 : Point n) e)).continuousAt
    have hct := hc.tendsto
    rwa [hγ0] at hct
  have hcomp : (fun t : ℝ => F (Function.update (0 : Point n) e t))
      =ᶠ[nhds ((0 : Point n) e)] (fun _ => c) := htend.eventually h
  simp only [pd]
  rw [hcomp.deriv_eq]
  exact deriv_const _ _

/-- **A whole Fréchet derivative vanishes from vanishing partials.**  If `F` is differentiable at `0`
    and every coordinate partial `∂_e F(0) = 0`, then `fderiv ℝ F 0 = 0` (a linear map vanishing on the
    standard basis `Pi.single e 1` is zero). -/
theorem fderiv_zero_of_pd_zero {F : Point n → ℝ} (hdiff : DifferentiableAt ℝ F 0)
    (hpd : ∀ e, pd F e 0 = 0) : fderiv ℝ F 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.zero_apply]
  conv_lhs => rw [eq_sum_smul_single x]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro e _
  rw [map_smul, smul_eq_mul, ← pd_eq_fderiv F e 0 hdiff, hpd e, mul_zero]

/-- **Second-order Taylor bound from a `C²`-at-`0` germ vanishing to 2nd order.**  For `F : Point n → ℝ`
    that is `ContDiffAt ℝ 2` at `0` with `F 0 = c` and all first partials `∂_e F(0) = 0`, the deviation
    `F − c` decays quadratically near `0`:  `∃ ρ > 0, ∃ M ≥ 0, ∀ v, rncRadial v ≤ ρ →
    |F v − c| ≤ M · rncRadialSq v`.  DERIVED: `fderiv F 0 = 0` (`fderiv_zero_of_pd_zero`), a `ContDiffOn`
    ball from `ContDiffAt`, a compact `‖D²(F−c)‖` bound, and `RNCDecay.decay_order_two_radial`. -/
theorem contDiffAt_two_quadratic_decay (F : Point n → ℝ) (c : ℝ)
    (hF : ContDiffAt ℝ 2 F 0) (hF0 : F 0 = c) (hpd : ∀ e, pd F e 0 = 0) :
    ∃ ρ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ v : Point n, rncRadial v ≤ ρ →
      |F v - c| ≤ M * rncRadialSq v := by
  have hFdiff : DifferentiableAt ℝ F 0 := hF.differentiableAt (by norm_num)
  have hdF0 : fderiv ℝ F 0 = 0 := fderiv_zero_of_pd_zero hFdiff hpd
  have hf : ContDiffAt ℝ 2 (fun v => F v - c) 0 := hF.sub contDiffAt_const
  have hf0 : (fun v => F v - c) 0 = 0 := by simp [hF0]
  have hdf0 : fderiv ℝ (fun v => F v - c) 0 = 0 := by rw [fderiv_sub_const]; exact hdF0
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (le_refl (2 : WithTop ℕ∞)) (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hballρ : Metric.closedBall (0 : Point n) (r / 2) ⊆ Metric.ball 0 r :=
    Metric.closedBall_subset_ball (by linarith)
  have hfball : ContDiffOn ℝ 2 (fun v => F v - c) (Metric.ball (0 : Point n) r) := hfu.mono hball
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ (fun v => F v - c)) (Metric.ball (0 : Point n) r) :=
    hfball.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hf0diffOn : DifferentiableOn ℝ (fun v => F v - c) (Metric.ball (0 : Point n) r) :=
    hfball.differentiableOn (by norm_num)
  have hf1diffOn : DifferentiableOn ℝ (fderiv ℝ (fun v => F v - c)) (Metric.ball (0 : Point n) r) :=
    hf1.differentiableOn (by norm_num)
  -- Compact bound on the nested second derivative.  We let `exists_bound_of_continuousOn` IMPOSE the
  -- metric-topology `ContinuousOn` goal and prove it pointwise from `ContDiffAt.fderiv_right` — never
  -- naming the strong-topology `ContinuousOn` (which would trigger the `ContinuousLinearMap`/metric and
  -- `Pi`/metric instance diamonds).
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : Point n) (r / 2)).exists_bound_of_continuousOn
    (f := fun w : Point n => fderiv ℝ (fderiv ℝ (fun v => F v - c)) w)
    (by
      intro w hw
      have hwball : w ∈ Metric.ball (0 : Point n) r := hballρ hw
      exact ((((hfball.contDiffAt (Metric.isOpen_ball.mem_nhds hwball)).fderiv_right
          (m := 1) (by norm_num)).fderiv_right (m := 0)
          (by norm_num)).continuousAt).continuousWithinAt)
  have hdiff : ∀ w ∈ Metric.closedBall (0 : Point n) (r / 2),
      DifferentiableAt ℝ (fun v => F v - c) w :=
    fun w hw => (hf0diffOn w (hballρ hw)).differentiableAt (Metric.isOpen_ball.mem_nhds (hballρ hw))
  have hdiff2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r / 2),
      DifferentiableAt ℝ (fderiv ℝ (fun v => F v - c)) w :=
    fun w hw => (hf1diffOn w (hballρ hw)).differentiableAt (Metric.isOpen_ball.mem_nhds (hballρ hw))
  have hbound2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r / 2),
      ‖fderiv ℝ (fderiv ℝ (fun v => F v - c)) w‖ ≤ max 0 M0 :=
    fun w hw => le_trans (hM0 w hw) (le_max_right _ _)
  refine ⟨r / 2, by positivity, max 0 M0, le_max_left _ _, fun v hv => ?_⟩
  have hdecay := decay_order_two_radial (fun v => F v - c) (max 0 M0) (r / 2) (by positivity)
    hf0 hdf0 hdiff hdiff2 hbound2 hv
  rw [rncRadial_sq] at hdecay
  exact hdecay

/-! ### The `expPullbackMetric` inverse first-jet at `0`, hypothesis-clean. -/

/-- **`∂g̃⁻¹(0) = 0` (hypothesis-clean).**  Every first partial of the `expPullbackMetric` inverse
    vanishes at the RNC centre.  Same collapse as `pd_expPullbackMetricInv_zero` (differentiate
    `∑σ g̃⁻¹_{iσ}·g̃_{σj} = δ`), but the pointwise inverse identity is derived on a `𝓝 0`-ball from the
    near-`0` nondegeneracy `expPullbackMetric_isUnit_near_zero` (via `sum_invMat_mul`) and fed to
    `pd_eventuallyEq_const_zero` — so NO `∀y` `hinvT` is carried (only `hinv` at `p`). -/
theorem pd_expPullbackMetricInv_zero_clean (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hframe : ∀ i j, g p i j = (if i = j then (1 : ℝ) else 0))
    (i j e : Fin n) :
    pd (fun x => expPullbackMetricInv g gi hC p x i j) e (0 : Point n) = 0 := by
  have hPgti : ∀ σ, PdiffAt (fun x => expPullbackMetricInv g gi hC p x i σ) e 0 := fun σ =>
    PdiffAt_of_contDiffAt _ e 0
      ((expPullbackMetricInv_contDiffAt_two g gi hC p hinv hg i σ).of_le (by norm_num))
  have hPgt : ∀ σ, PdiffAt (fun x => expPullbackMetric g gi hC p x σ j) e 0 := fun σ =>
    PdiffAt_of_contDiffAt _ e 0
      ((contDiffAt2_expPullbackMetric_zero g gi hC p hg σ j).of_le (by norm_num))
  -- pointwise inverse identity `∑σ g̃⁻¹·g̃ = δ` holds on a `𝓝 0`-ball (near-`0` nondegeneracy).
  obtain ⟨ρ₀, hρ₀, hunit⟩ := expPullbackMetric_isUnit_near_zero g gi hC p hg hinv
  have hPconst : (fun x => ∑ σ, expPullbackMetricInv g gi hC p x i σ
      * expPullbackMetric g gi hC p x σ j)
      =ᶠ[nhds (0 : Point n)] (fun _ => (if i = j then (1 : ℝ) else 0)) := by
    have hset : {x : Point n | ‖x‖ < ρ₀} ∈ nhds (0 : Point n) :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hρ₀)
    filter_upwards [hset] with x hx
    simpa only [expPullbackMetricInv] using
      sum_invMat_mul (fun a b => expPullbackMetric g gi hC p x a b) (hunit x hx) i j
  have hpdF : pd (fun x => ∑ σ, expPullbackMetricInv g gi hC p x i σ
      * expPullbackMetric g gi hC p x σ j) e 0 = 0 :=
    pd_eventuallyEq_const_zero e hPconst
  rw [pd_sum Finset.univ (fun σ x => expPullbackMetricInv g gi hC p x i σ
        * expPullbackMetric g gi hC p x σ j) e 0 (fun σ _ => (hPgti σ).mul (hPgt σ)),
    Finset.sum_congr rfl (fun σ _ => pd_mul (fun x => expPullbackMetricInv g gi hC p x i σ)
        (fun x => expPullbackMetric g gi hC p x σ j) e 0 (hPgti σ) (hPgt σ))] at hpdF
  have hgt0 : ∀ σ, expPullbackMetric g gi hC p 0 σ j = (if σ = j then (1 : ℝ) else 0) := fun σ => by
    rw [expPullbackMetric_at_zero g gi hC p σ j]; exact hframe σ j
  have hpdgt0 : ∀ σ, pd (fun x => expPullbackMetric g gi hC p x σ j) e 0 = 0 := fun σ =>
    pd_expPullbackMetric_at_zero g gi hC p hsymm0 hinv hg σ j e
  simp only [hgt0, hpdgt0, mul_zero, add_zero, mul_ite, mul_one] at hpdF
  rw [Finset.sum_ite_eq' Finset.univ j (fun σ => pd (fun x => expPullbackMetricInv g gi hC p x i σ) e 0)]
    at hpdF
  simpa using hpdF

/-! ### The `expPullbackMetric`-side quadratic deviation `hdev`. -/

/-- **`hdev` for the `expPullbackMetric` inverse.**  `∃ M ≥ 0, ∀ᶠ v in 𝓝 0, ∀ i j,
    |g̃⁻¹(v) i j − δ_ij| ≤ M · rncRadialSq v` — the `O(r²)` RNC decay of the pullback inverse metric off
    the centre.  Per-entry via `contDiffAt_two_quadratic_decay` (`g̃⁻¹` is `C²`, `g̃⁻¹(0) = δ` from the
    frame, `∂g̃⁻¹(0) = 0` from `pd_expPullbackMetricInv_zero_clean`), then a uniform `M` (sum over the
    finite index set) and finite intersection of the eventual balls (`Filter.eventually_all`). -/
theorem expPullbackMetricInv_dev (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hframe : ∀ i j, g p i j = (if i = j then (1 : ℝ) else 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ v in nhds (0 : Point n), ∀ i j : Fin n,
      |expPullbackMetricInv g gi hC p v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v := by
  classical
  have hgip : ∀ i j : Fin n, gi p i j = (if i = j then (1 : ℝ) else 0) := by
    intro i j
    have h := hinv i j
    simp only [hframe, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h
  have hcontR : Continuous (rncRadial : Point n → ℝ) := by
    unfold rncRadial
    exact Real.continuous_sqrt.comp rncRadialSq_contDiff.continuous
  have hev : ∀ i j : Fin n, ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ v in nhds (0 : Point n),
      |expPullbackMetricInv g gi hC p v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v := by
    intro i j
    obtain ⟨ρ, hρ, M, hM, hb⟩ := contDiffAt_two_quadratic_decay
      (fun v => expPullbackMetricInv g gi hC p v i j) (if i = j then (1 : ℝ) else 0)
      (expPullbackMetricInv_contDiffAt_two g gi hC p hinv hg i j)
      (by show expPullbackMetricInv g gi hC p 0 i j = (if i = j then (1 : ℝ) else 0)
          rw [expPullbackMetricInv_zero g gi hC p hinv i j]; exact hgip i j)
      (fun e => pd_expPullbackMetricInv_zero_clean g gi hC p hsymm0 hinv hg hframe i j e)
    refine ⟨M, hM, ?_⟩
    have hset : {v : Point n | rncRadial v < ρ} ∈ nhds (0 : Point n) :=
      (isOpen_lt hcontR continuous_const).mem_nhds (by simpa using hρ)
    filter_upwards [hset] with v hv
    exact hb v (le_of_lt hv)
  choose Mf hMf0 hMfev using hev
  refine ⟨∑ i, ∑ j, Mf i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hMf0 i j)), ?_⟩
  have hall : ∀ᶠ v in nhds (0 : Point n), ∀ i j : Fin n,
      |expPullbackMetricInv g gi hC p v i j - (if i = j then (1 : ℝ) else 0)|
        ≤ Mf i j * rncRadialSq v := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact hMfev i j
  filter_upwards [hall] with v hv
  intro i j
  refine le_trans (hv i j) ?_
  apply mul_le_mul_of_nonneg_right _ (rncRadialSq_nonneg v)
  calc Mf i j ≤ ∑ j', Mf i j' :=
        Finset.single_le_sum (fun j' _ => hMf0 i j') (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Mf i' j' :=
        Finset.single_le_sum (fun i' _ => Finset.sum_nonneg (fun j' _ => hMf0 i' j'))
          (Finset.mem_univ i)

/-! ### The weld transfer: `uniformFlowExp` inverse metric = `expMap` inverse metric near `0`. -/

/-- **Weld transfer of the inverse metric.**  On a `𝓝 0`-neighbourhood, the `uniformFlowExp` pullback
    inverse metric agrees entrywise with the `expMap` pullback inverse metric at base point `q`.
    DERIVED (no nondegeneracy): the ODE-uniqueness bridge `expMap_eq_uniformFlowExp_on_overlap` (J4-20)
    gives `uniformFlowExp q = expMap q` on the open overlap ball; equal maps ⟹ equal `fderiv`
    (`EventuallyEq.fderiv_eq`) ⟹ equal pullback metrics (same formula in `F`, `DF`) ⟹ equal operator
    inverses `Ring.inverse (matToCLM ·)` ⟹ equal entries. -/
theorem uniformFlowPullbackMetricInv_eq_expPullbackMetricInv_eventually
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) :
    ∀ᶠ v in nhds (0 : Point n), ∀ i j : Fin n,
      uniformFlowPullbackMetricInv g gi hC hK q v i j = expPullbackMetricInv g gi hC q v i j := by
  set c : ℝ := min (expRho g gi hC q) (uniformFlowRadius g gi hC hK) with hc
  have hcpos : 0 < c := lt_min (expRho_pos g gi hC q) (uniformFlowRadius_pos g gi hC hK)
  have hballOpen : IsOpen {w : Point n | ‖w‖ < c} := isOpen_lt continuous_norm continuous_const
  have hmem : {w : Point n | ‖w‖ < c} ∈ nhds (0 : Point n) :=
    hballOpen.mem_nhds (by simpa using hcpos)
  have hEqOn : Set.EqOn (uniformFlowExp g gi hC hK q) (expMap g gi hC q) {w : Point n | ‖w‖ < c} :=
    fun w hw => (expMap_eq_uniformFlowExp_on_overlap g gi hC hK q hq w hw).symm
  filter_upwards [hmem] with v hv
  have hval : uniformFlowExp g gi hC hK q v = expMap g gi hC q v := hEqOn hv
  have hev : (uniformFlowExp g gi hC hK q) =ᶠ[nhds v] (expMap g gi hC q) :=
    Filter.eventuallyEq_of_mem (hballOpen.mem_nhds hv) hEqOn
  have hfd : fderiv ℝ (uniformFlowExp g gi hC hK q) v = fderiv ℝ (expMap g gi hC q) v :=
    hev.fderiv_eq
  have hmetric : ∀ a b, uniformFlowPullbackMetric g gi hC hK q v a b
      = expPullbackMetric g gi hC q v a b := by
    intro a b
    simp only [uniformFlowPullbackMetric, expPullbackMetric, hval, hfd]
  intro i j
  simp only [uniformFlowPullbackMetricInv, expPullbackMetricInv]
  rw [show (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)
        = (fun a b => expPullbackMetric g gi hC q v a b) from
      funext fun a => funext fun b => hmetric a b]

/-! ### ★ Capstone — the consumer `hdev` for `uniformFlowPullbackMetricInv`. -/

/-- **★ J4-82 capstone — the inverse-metric quadratic deviation `hdev` over `uniformFlowExp`.**
    `∃ M ≥ 0, ∀ᶠ v in 𝓝 0, ∀ i j, |g̃⁻¹(v) i j − δ_ij| ≤ M · rncRadialSq v` for
    `g̃⁻¹ = uniformFlowPullbackMetricInv g gi hC hK q` — the FIREWALL input of
    `cutoffResidual_expPullback_hEboundW` (`RecenterCutoffC3.lean:97`), re-targeted onto the
    uniform-flow endpoint map.  Combines the weld transfer
    (`uniformFlowPullbackMetricInv_eq_expPullbackMetricInv_eventually`) with the `expMap`-side Taylor
    bound (`expPullbackMetricInv_dev`).  Hypotheses ONLY `hC`+`IsCompact K`+`hg`+`hgsymm`+`hinvF`+
    `hframe(q)`, all genuine (satisfiable by `g = gi = δ`, none is the conclusion); NO `expRho` in the
    statement.  NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetricInv_dev (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (q : Point n) (hq : q ∈ K)
    (hframe : ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ v in nhds (0 : Point n), ∀ i j : Fin n,
      |uniformFlowPullbackMetricInv g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)|
        ≤ M * rncRadialSq v := by
  obtain ⟨M, hM0, hdevexp⟩ :=
    expPullbackMetricInv_dev g gi hC q hgsymm (fun a b => hinvF q a b) hg hframe
  have hAeq := uniformFlowPullbackMetricInv_eq_expPullbackMetricInv_eventually g gi hC hK q hq
  refine ⟨M, hM0, ?_⟩
  filter_upwards [hdevexp, hAeq] with v hdv haeq
  intro i j
  rw [haeq i j]
  exact hdv i j

/-! ### The UNIFORM-`M` layer: jet values transfer + Taylor from the uniform `C²` packet.

The per-`q` capstone above transfers the whole deviation bound through the weld (per-`q` constant `M`).
The J4-83 uniform assembly needs ONE `M` over `q ∈ K`; for that we transfer ONLY the jet VALUES at `0`
(`g̃(0) = δ`, `∂g̃(0) = 0`) through the weld, and re-run the Taylor bound with the UNIFORM constants of
`uniformFlowPullbackMetric_c2_uniform_full`, pushing through the inverse with
`uniformInverseMetric_bound` via `A⁻¹ − 1 = A⁻¹(1 − A)`. -/

/-- **Germ congruence of `pd`.**  `F =ᶠ[𝓝 x] G ⟹ ∂_e F(x) = ∂_e G(x)` (`pd` sees only the germ; the
    coordinate ray is continuous, so the eventual equality pulls back along it). -/
theorem pd_congr_eventuallyEq {F G : Point n → ℝ} (e : Fin n) {x : Point n}
    (h : F =ᶠ[nhds x] G) : pd F e x = pd G e x := by
  have hγ0 : Function.update x e (x e) = x := Function.update_eq_self e x
  have htend : Filter.Tendsto (fun t : ℝ => Function.update x e t) (nhds (x e)) (nhds x) := by
    have hc : ContinuousAt (Function.update x e) (x e) :=
      (hasDerivAt_update x e (x e)).continuousAt
    have hct := hc.tendsto
    rwa [hγ0] at hct
  have hcomp : (fun t : ℝ => F (Function.update x e t))
      =ᶠ[nhds (x e)] (fun t => G (Function.update x e t)) := htend.eventually h
  simp only [pd]
  exact hcomp.deriv_eq

/-- **Weld transfer of the FORWARD metric.**  On a `𝓝 0`-neighbourhood, the `uniformFlowExp` pullback
    metric agrees entrywise with the `expMap` pullback metric at base point `q` (same mechanism as the
    inverse weld: `expMap_eq_uniformFlowExp_on_overlap` + `EventuallyEq.fderiv_eq`). -/
theorem uniformFlowPullbackMetric_eq_expPullbackMetric_eventually
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) :
    ∀ᶠ v in nhds (0 : Point n), ∀ i j : Fin n,
      uniformFlowPullbackMetric g gi hC hK q v i j = expPullbackMetric g gi hC q v i j := by
  set c : ℝ := min (expRho g gi hC q) (uniformFlowRadius g gi hC hK) with hc
  have hcpos : 0 < c := lt_min (expRho_pos g gi hC q) (uniformFlowRadius_pos g gi hC hK)
  have hballOpen : IsOpen {w : Point n | ‖w‖ < c} := isOpen_lt continuous_norm continuous_const
  have hmem : {w : Point n | ‖w‖ < c} ∈ nhds (0 : Point n) :=
    hballOpen.mem_nhds (by simpa using hcpos)
  have hEqOn : Set.EqOn (uniformFlowExp g gi hC hK q) (expMap g gi hC q) {w : Point n | ‖w‖ < c} :=
    fun w hw => (expMap_eq_uniformFlowExp_on_overlap g gi hC hK q hq w hw).symm
  filter_upwards [hmem] with v hv
  intro i j
  have hval : uniformFlowExp g gi hC hK q v = expMap g gi hC q v := hEqOn hv
  have hev : (uniformFlowExp g gi hC hK q) =ᶠ[nhds v] (expMap g gi hC q) :=
    Filter.eventuallyEq_of_mem (hballOpen.mem_nhds hv) hEqOn
  have hfd : fderiv ℝ (uniformFlowExp g gi hC hK q) v = fderiv ℝ (expMap g gi hC q) v :=
    hev.fderiv_eq
  simp only [uniformFlowPullbackMetric, expPullbackMetric, hval, hfd]

/-- **RNC jet values at `0` of the `uniformFlowExp` pullback metric.**  `g̃(0) = δ` (frame) and
    `∂g̃(0) = 0` — transferred through the forward weld from the proven `expPullbackMetric` jet library
    (`expPullbackMetric_at_zero`, `pd_expPullbackMetric_at_zero`), using germ-locality of the value and
    of `pd` (`pd_congr_eventuallyEq`). -/
theorem uniformFlowPullbackMetric_jet_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (q : Point n) (hq : q ∈ K)
    (hframe : ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0)) :
    (∀ i j, uniformFlowPullbackMetric g gi hC hK q 0 i j = (if i = j then (1 : ℝ) else 0))
    ∧ (∀ i j e, pd (fun v => uniformFlowPullbackMetric g gi hC hK q v i j) e (0 : Point n) = 0) := by
  have hB := uniformFlowPullbackMetric_eq_expPullbackMetric_eventually g gi hC hK q hq
  constructor
  · intro i j
    have h0 := hB.self_of_nhds
    rw [h0 i j, expPullbackMetric_at_zero g gi hC q i j]
    exact hframe i j
  · intro i j e
    have hent : (fun v => uniformFlowPullbackMetric g gi hC hK q v i j)
        =ᶠ[nhds (0 : Point n)] (fun v => expPullbackMetric g gi hC q v i j) :=
      hB.mono fun v hv => hv i j
    rw [pd_congr_eventuallyEq e hent]
    exact pd_expPullbackMetric_at_zero g gi hC q hgsymm (fun a b => hinvF q a b) hg i j e

/-- **UNIFORM forward-metric quadratic deviation.**  ONE radius `r₀ > 0` and ONE constant `M ≥ 0` with
    `|g̃(v) i j − δ_ij| ≤ M·‖v‖²` for every `q ∈ K`, `‖v‖ ≤ r₀`.  Taylor (`RNCDecay.decay_order_two`)
    from the transferred jet values at `0` (`uniformFlowPullbackMetric_jet_zero`) and the UNIFORM `C²`
    packet `uniformFlowPullbackMetric_c2_uniform_full` (both `HasFDerivAt` layers + `‖D²‖ ≤ M`). -/
theorem uniformFlowPullbackMetric_dev_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0)) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ r₀ → ∀ i j : Fin n,
      |uniformFlowPullbackMetric g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)|
        ≤ M * ‖v‖ ^ 2 := by
  obtain ⟨r₀, hr₀0, M, hpk⟩ := uniformFlowPullbackMetric_c2_uniform_full g gi hg hC hK
  refine ⟨r₀ / 2, by positivity, max 0 M, le_max_left _ _, ?_⟩
  intro q hq v hv i j
  obtain ⟨hjet0, hjetpd⟩ :=
    uniformFlowPullbackMetric_jet_zero g gi hC hK hg hgsymm hinvF q hq (hframeK q hq)
  set f : Point n → ℝ :=
    fun w => uniformFlowPullbackMetric g gi hC hK q w i j - (if i = j then (1 : ℝ) else 0) with hf
  have hballs : ∀ w : Point n, w ∈ Metric.closedBall (0 : Point n) (r₀ / 2) → ‖w‖ < r₀ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    linarith
  have hfd_eq : fderiv ℝ f
      = fderiv ℝ (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) := by
    funext w
    exact fderiv_sub_const _
  -- value jet.
  have hf0 : f 0 = 0 := by rw [hf]; simp only [hjet0 i j, sub_self]
  -- derivative jet: `fderiv f 0 = 0` from the vanishing partials + packet differentiability at `0`.
  have h0mem : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀0
  have hdf0 : fderiv ℝ f 0 = 0 := by
    rw [hfd_eq]
    exact fderiv_zero_of_pd_zero
      ((hpk q hq 0 h0mem i j).1.differentiableAt) (fun e => hjetpd i j e)
  -- differentiability + bound hypotheses on the closed half-ball, from the uniform packet.
  have hdiff : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2), DifferentiableAt ℝ f w := by
    intro w hw
    exact ((hpk q hq w (hballs w hw) i j).1.differentiableAt).sub (differentiableAt_const _)
  have hdiff2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2),
      DifferentiableAt ℝ (fderiv ℝ f) w := by
    intro w hw
    rw [hfd_eq]
    exact (hpk q hq w (hballs w hw) i j).2.1.differentiableAt
  have hbound2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2),
      ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ max 0 M := by
    intro w hw
    rw [hfd_eq]
    exact le_trans (hpk q hq w (hballs w hw) i j).2.2.2.2 (le_max_right _ _)
  have hdecay := decay_order_two f (max 0 M) (r₀ / 2) (by positivity)
    hf0 hdf0 hdiff hdiff2 hbound2 hv
  simpa only [hf] using hdecay

/-- **★ J4-82 UNIFORM capstone — `hdev` with ONE constant over `q ∈ K`.**
    `∃ r₀ > 0, ∃ M ≥ 0, ∀ q ∈ K, ∀ ‖v‖ < r₀, ∀ i j, |g̃⁻¹(v) i j − δ_ij| ≤ M · rncRadialSq v` for
    `g̃⁻¹ = uniformFlowPullbackMetricInv g gi hC hK q` — the uniform-in-`q` strengthening of
    `uniformFlowPullbackMetricInv_dev` (which the J4-83 uniform-B packet needs).  Neumann push through
    the uniform inverse bound: `A⁻¹ − 1 = A⁻¹(1 − A)` (`Ring.inverse_mul_cancel`), so the entry
    deviation is `≤ ‖A⁻¹‖ · ‖(1−A)e_j‖ ≤ Kinv · M_dev·‖v‖² ≤ Kinv·M_dev · rncRadialSq v`
    (`uniformInverseMetric_bound` + `uniformFlowPullbackMetric_dev_uniform`; `‖v‖² ≤ rncRadialSq v` on
    the sup-norm chart).  Hypotheses ONLY `hg`+`hC`+`hK`+`hgnd`+`hgsymm`+`hinvF`+`hframeK`, all genuine
    (satisfiable by `g = gi = δ`); NO `expRho` in the statement.  NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetricInv_dev_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0)) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ i j : Fin n,
      |uniformFlowPullbackMetricInv g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)|
        ≤ M * rncRadialSq v := by
  obtain ⟨r₁, hr₁0, Md, hMd0, hdev⟩ :=
    uniformFlowPullbackMetric_dev_uniform g gi hC hK hg hgsymm hinvF hframeK
  obtain ⟨r₂, hr₂0, Kinv, hinvB⟩ := uniformInverseMetric_bound g gi hg hC hK hgnd
  refine ⟨min r₁ r₂, lt_min hr₁0 hr₂0, max 0 Kinv * Md,
    mul_nonneg (le_max_left _ _) hMd0, ?_⟩
  intro q hq v hv i j
  have hv1 : ‖v‖ ≤ r₁ := le_of_lt (lt_of_lt_of_le hv (min_le_left _ _))
  have hv2 : ‖v‖ < r₂ := lt_of_lt_of_le hv (min_le_right _ _)
  obtain ⟨hU, hKn, _⟩ := hinvB q hq v hv2
  set A : Point n →L[ℝ] Point n :=
    matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b) with hA
  -- the Neumann identity `A⁻¹(1 − A) = A⁻¹ − 1`.
  have hid : Ring.inverse A * (1 - A) = Ring.inverse A - 1 := by
    rw [mul_sub, mul_one, Ring.inverse_mul_cancel _ hU]
  -- entries of `(1 − A)e_j` are the forward-metric deviations.
  have hzk : ∀ k : Fin n, ((1 - A) (Pi.single j (1 : ℝ))) k
      = (if k = j then (1 : ℝ) else 0) - uniformFlowPullbackMetric g gi hC hK q v k j := by
    intro k
    have hAw : (A (Pi.single j (1 : ℝ))) k = uniformFlowPullbackMetric g gi hC hK q v k j := by
      rw [hA, matToCLM_apply]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, Pi.sub_apply, hAw,
      Pi.single_apply]
  have hznorm : ‖(1 - A) (Pi.single j (1 : ℝ))‖ ≤ Md * ‖v‖ ^ 2 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    rw [Real.norm_eq_abs, hzk k, abs_sub_comm]
    exact hdev q hq v hv1 k j
  -- the entry deviation IS the `i`-th coordinate of `A⁻¹((1−A)e_j)`.
  have hmain : uniformFlowPullbackMetricInv g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)
      = ((Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))) i := by
    have hRA : Ring.inverse A ((1 - A) (Pi.single j (1 : ℝ)))
        = Ring.inverse A (Pi.single j (1 : ℝ)) - Pi.single j (1 : ℝ) := by
      have h1 : (1 - A) (Pi.single j (1 : ℝ))
          = Pi.single j (1 : ℝ) - A (Pi.single j (1 : ℝ)) := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
      have h2 : Ring.inverse A (A (Pi.single j (1 : ℝ))) = Pi.single j (1 : ℝ) := by
        rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hU,
          ContinuousLinearMap.one_apply]
      rw [h1, map_sub, h2]
    rw [hRA, Pi.sub_apply, Pi.single_apply]
    simp only [uniformFlowPullbackMetricInv, hA]
  rw [hmain]
  calc |((Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))) i|
      = ‖((Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))) i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖(Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))‖ := norm_le_pi_norm _ i
    _ ≤ ‖Ring.inverse A‖ * ‖(1 - A) (Pi.single j (1 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ max 0 Kinv * (Md * ‖v‖ ^ 2) :=
        mul_le_mul (le_trans hKn (le_max_right _ _)) hznorm (norm_nonneg _) (le_max_left _ _)
    _ ≤ max 0 Kinv * Md * rncRadialSq v := by
        have hsq : ‖v‖ ^ 2 ≤ rncRadialSq v := by
          rw [← rncRadial_sq]
          nlinarith [norm_le_rncRadial v, norm_nonneg v, rncRadial_nonneg v]
        calc max 0 Kinv * (Md * ‖v‖ ^ 2) = max 0 Kinv * Md * ‖v‖ ^ 2 := by ring
          _ ≤ max 0 Kinv * Md * rncRadialSq v := by
              apply mul_le_mul_of_nonneg_left hsq
              exact mul_nonneg (le_max_left _ _) hMd0

end QIQTH.ExpMap
