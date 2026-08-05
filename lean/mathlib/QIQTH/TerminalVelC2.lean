/-
  TerminalVelC2 — J4-274: `hT0`, the terminal-velocity `C²` at the centre.

  ROLE.  `QIQTH.GeodesicReversalRoute` (J4-273) reduced the last structural blocker of the W1
  chart-image approximate identity — the base-slot regularity `hbaseC2` consumed by
  `QIQTH.BaseVaryingIFTPackage.baseVaryingIFTPackage` — to a SINGLE fixed-base fact

      hT0 : ContDiffAt ℝ 2 (terminalVel0 g gi hC hK) 0 ,

  where `terminalVel0 v := (uniformFlowTube g gi hC hK 0 v 1).2` is the VELOCITY component at time
  `1` of the confined geodesic from `(0, v)`.  This file DISCHARGES `hT0` unconditionally (given the
  interior basepoint `0 ∈ K`), and composes it into the unconditional M1–M4 change-of-variables
  bundle `baseVaryingIFTPackage_unconditional`.

  ── THE ROUTE (a): geodesic homogeneity ⇒ velocity endpoint = differential-of-`exp` on the diagonal.
    For a geodesic `γ_v(t) = exp_0(t v)` the velocity at time `1` is `γ_v'(1) = D exp_0(v)[v]`.
    Concretely, the RESCALED phase curve `Z t := scaleVel s (Y (s·t))` (`Y := uniformFlowTube 0 v`,
    `scaleVel s (x,w) = (x, s·w)`) solves the SAME autonomous geodesic system whenever `Y` does —
    because the geodesic acceleration `−Γ(x)(w,w)` is QUADRATIC in `w`, so
    `geodesicField (scaleVel s p) = s · scaleVel s (geodesicField p)` (`geodesicField_scaleVel`).
    ODE uniqueness then gives the REPARAMETRISATION identity (`uniformFlow_scale_position`)

        uniformFlowExp 0 (s • v) = (uniformFlowTube 0 v s).1        for `s ∈ [0,1]`.

    Differentiating in `s` at `s = 1` (from the left, on `Iic 1`): the LEFT side has derivative
    `fderiv (uniformFlowExp 0) v [v]` (chain rule, banked position regularity), the RIGHT side has
    derivative `(uniformFlowTube 0 v 1).2 = terminalVel0 v` (the tube ODE, whose position slot's
    time-derivative is the velocity slot).  Uniqueness of the within-derivative gives

        terminalVel0 v = fderiv ℝ (uniformFlowExp 0) v [v]        (`terminalVel0_apply_eq_fderiv_diag`).

    The RIGHT side is `C³` at `0`: the position endpoint `uniformFlowExp 0` is `C⁴`
    (`ChartThirdJet.uniformFlowExp_contDiffAt_four`, the banked jet-4 tower), so `fderiv` is `C³`
    (`ContDiffAt.fderiv_right`), and the diagonal evaluation `v ↦ (fderiv .. v) v` is `C³`
    (`ContDiffAt.clm_apply`).  Hence `terminalVel0` is `C³ ≥ C²` at `0`.

  ── WHAT IS BANKED vs NEW (honest firewall — NOT `a₁ = R/6`).
    • BANKED (reused, not reproved): the position endpoint `C⁴`
      (`uniformFlowExp_contDiffAt_four` ⟵ `expMap_contDiffOn_four`, the jet-4 tower); the uniform-tube
      IC/ODE/confinement specs; `ODE_solution_unique_of_mem_Icc_right`.
    • NEW here: the velocity-slot scaling algebra (`scaleVel`, `geodesicField_scaleVel`), the
      reparametrisation ODE-uniqueness lemma (`uniformFlow_scale_position` — mirrors
      `uniformFlow_reversal_reach`), the diagonal identity, and the `C²` conclusion.  NO NEW velocity
      jet tower: the velocity `C²` is EXTRACTED from the banked POSITION `C⁴` through the exact
      homogeneity identity — one Fréchet order is SPENT (`C⁴ → C³`), matching the audit's
      "velocity slot is one order less".

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  No `sorry` (prose only), no new
  axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypotheses.  The
  homogeneity identity is a genuine ODE-uniqueness fact linking two DIFFERENT objects (the velocity
  endpoint and the position differential); it does not trivially yield the conclusion.  No existing
  file is edited.
-/
import Mathlib
import QIQTH.ChartThirdJet
import QIQTH.GeodesicReversalRoute

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.ChartThirdJet
  QIQTH.GeodesicReversalRoute
open scoped Topology

namespace QIQTH.TerminalVelC2

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The velocity-scaling continuous-linear map and the scaling algebra. -/

/-- **`scaleVel s` — the velocity-scaling continuous-linear map** `(x, w) ↦ (x, s • w)` on the
    geodesic phase space `Point n × Point n`. -/
noncomputable def scaleVel (s : ℝ) : (Point n × Point n) →L[ℝ] (Point n × Point n) :=
  (ContinuousLinearMap.id ℝ (Point n)).prodMap (s • ContinuousLinearMap.id ℝ (Point n))

@[simp] theorem scaleVel_apply (s : ℝ) (p : Point n × Point n) :
    scaleVel s p = (p.1, s • p.2) := by
  apply Prod.ext
  · simp [scaleVel, Prod.map_fst]
  · simp [scaleVel, Prod.map_snd]

/-- For `0 ≤ s ≤ 1`, `scaleVel s` is norm-nonexpansive: `‖scaleVel s p‖ ≤ ‖p‖`. -/
theorem scaleVel_norm_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (p : Point n × Point n) :
    ‖scaleVel s p‖ ≤ ‖p‖ := by
  rw [scaleVel_apply, Prod.norm_def, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  exact max_le_max le_rfl (mul_le_of_le_one_left (norm_nonneg _) hs1)

/-- **The geodesic field is SCALING-COMPATIBLE.**  Because the geodesic acceleration `−Γ(x)(w,w)` is
    QUADRATIC (even, degree-2 homogeneous) in the velocity `w`,
        `geodesicField (scaleVel s p) = s • scaleVel s (geodesicField p)`.
    This is the pointwise fact that makes the rescaled curve `t ↦ scaleVel s (Y (s·t))` solve the
    SAME autonomous geodesic system as `Y`. -/
theorem geodesicField_scaleVel (g gi : Point n → Fin n → Fin n → ℝ) (s : ℝ) (p : Point n × Point n) :
    geodesicField g gi (scaleVel s p) = s • scaleVel s (geodesicField g gi p) := by
  apply Prod.ext
  · -- position slot: `(scaleVel s p).2 = s • (geodesicField p).1`, both `s • p.2`.
    simp only [geodesicField, scaleVel_apply, Prod.smul_fst]
  · -- velocity slot: the degree-2 homogeneity of the Christoffel quadratic.
    funext i
    simp only [geodesicField, scaleVel_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [mul_neg, mul_neg, neg_inj]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-! ### The reparametrisation (homogeneity) identity, via scaling + ODE uniqueness. -/

/-- **REPARAMETRISATION / HOMOGENEITY.**  At base `0 ∈ K`, for `‖v‖ ≤ ρ_K` and `s ∈ [0,1]`,
        `uniformFlowExp 0 (s • v) = (uniformFlowTube 0 v s).1`.
    Proof: the rescaled curve `Z t := scaleVel s (Y (s·t))` (`Y := uniformFlowTube 0 v`) solves the
    SAME geodesic system (`geodesicField_scaleVel`) with `Z 0 = (0, s • v) = uniformFlowTube 0 (s•v) 0`;
    both curves are confined to the common ball `closedBall 0 (C₀‖v‖)` on `[0,1]` (`scaleVel s` is
    nonexpansive for `s ∈ [0,1]`, and `st ∈ [0,1]`), on which `geodesicField` is Lipschitz, so
    `ODE_solution_unique_of_mem_Icc_right` forces `Z 1 = uniformFlowTube 0 (s•v) 1`.  The position slot
    reads `(Y s).1 = uniformFlowExp 0 (s • v)`.  FULLY DERIVED.  NOT `a₁ = R/6`. -/
theorem uniformFlow_scale_position (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (v : Point n)
    (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    uniformFlowExp g gi hC hK 0 (s • v) = (uniformFlowTube g gi hC hK 0 v s).1 := by
  obtain ⟨hs0, hs1⟩ := hs
  set Y : ℝ → Point n × Point n := uniformFlowTube g gi hC hK 0 v with hYdef
  set sv : Point n := s • v with hsvdef
  have hsv_le : ‖sv‖ ≤ uniformFlowRadius g gi hC hK := by
    rw [hsvdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    calc s * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg v)
      _ = ‖v‖ := one_mul _
      _ ≤ _ := hv
  set Z : ℝ → Point n × Point n := fun t => scaleVel s (Y (s * t)) with hZdef
  set V : ℝ → Point n × Point n := uniformFlowTube g gi hC hK 0 sv with hVdef
  -- Specs.
  have hY0 : Y 0 = (0, v) := uniformFlowTube_spec_ic g gi hC hK 0 h0K v hv
  have hYode : ∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t :=
    uniformFlowTube_spec_ode g gi hC hK 0 h0K v hv
  have hYconf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Y t - ((0, 0) : Point n × Point n)‖ ≤ uniformFlowConst g gi hC hK * ‖v‖ :=
    uniformFlowTube_spec_conf g gi hC hK 0 h0K v hv
  have hV0 : V 0 = (0, sv) := uniformFlowTube_spec_ic g gi hC hK 0 h0K sv hsv_le
  have hVode : ∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt V (geodesicField g gi (V t)) t :=
    uniformFlowTube_spec_ode g gi hC hK 0 h0K sv hsv_le
  have hVconf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖V t - ((0, 0) : Point n × Point n)‖ ≤ uniformFlowConst g gi hC hK * ‖sv‖ :=
    uniformFlowTube_spec_conf g gi hC hK 0 h0K sv hsv_le
  -- Interval helpers.
  have hst_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, s * t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    refine ⟨mul_nonneg hs0 ht.1, ?_⟩
    calc s * t ≤ 1 * 1 := mul_le_mul hs1 ht.2 ht.1 (by norm_num)
      _ = 1 := by norm_num
  have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIco_sub : Set.Ico (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- `Z` solves the geodesic ODE on `[0,1]`.
  have hZderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Z (geodesicField g gi (Z t)) t := by
    intro t ht
    have hst_ioo : s * t ∈ Set.Ioo (-2 : ℝ) 2 := hIcc_sub (hst_mem t ht)
    have hlin : HasDerivAt (fun r : ℝ => s * r) s t := by
      simpa using (hasDerivAt_id t).const_mul s
    have hcomp : HasDerivAt (fun r => Y (s * r)) (s • geodesicField g gi (Y (s * t))) t :=
      (hYode (s * t) hst_ioo).scomp t hlin
    have hZd : HasDerivAt Z (scaleVel s (s • geodesicField g gi (Y (s * t)))) t := by
      have hh := (scaleVel s).hasFDerivAt.comp_hasDerivAt t hcomp
      simpa [hZdef, Function.comp_def] using hh
    have hval : scaleVel s (s • geodesicField g gi (Y (s * t))) = geodesicField g gi (Z t) := by
      rw [hZdef, map_smul, geodesicField_scaleVel g gi s (Y (s * t))]
    rwa [hval] at hZd
  -- Common confinement ball and Lipschitz field.
  set R : ℝ := uniformFlowConst g gi hC hK * ‖v‖ with hRdef
  set S : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) R with hSdef
  obtain ⟨Kq, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) (by rw [hSdef]; exact convex_closedBall _ R)
      (by rw [hSdef]; exact isCompact_closedBall _ R)
  have hcont_Z : ContinuousOn Z (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hZderiv t ht).continuousAt.continuousWithinAt
  have hcont_V : ContinuousOn V (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hVode t (hIcc_sub ht)).continuousAt.continuousWithinAt
  have hmem_Z : ∀ t ∈ Set.Icc (0 : ℝ) 1, Z t ∈ S := by
    intro t ht
    rw [hSdef, Metric.mem_closedBall, dist_zero_right, hZdef]
    have hsc : ‖scaleVel s (Y (s * t))‖ ≤ ‖Y (s * t)‖ := scaleVel_norm_le s hs0 hs1 (Y (s * t))
    have hYb : ‖Y (s * t)‖ ≤ R := by
      have hc := hYconf (s * t) (hst_mem t ht)
      have he : Y (s * t) - ((0, 0) : Point n × Point n) = Y (s * t) := by simp
      rw [he] at hc; exact hc
    exact le_trans hsc hYb
  have hmem_V : ∀ t ∈ Set.Icc (0 : ℝ) 1, V t ∈ S := by
    intro t ht
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]
    have hc := hVconf t ht
    have he : V t - ((0, 0) : Point n × Point n) = V t := by simp
    rw [he] at hc
    have hsvv : uniformFlowConst g gi hC hK * ‖sv‖ ≤ R := by
      rw [hRdef, hsvdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      have hsvle : s * ‖v‖ ≤ ‖v‖ := by nlinarith [norm_nonneg v, hs1, hs0]
      nlinarith [uniformFlowConst_nonneg g gi hC hK, hsvle, norm_nonneg v]
    exact le_trans hc hsvv
  -- Same initial value at `t = 0`.
  have ha : Z 0 = V 0 := by
    rw [hZdef, hV0]
    simp only [mul_zero, hY0, scaleVel_apply]
    rw [hsvdef]
  -- Grönwall uniqueness on `[0,1]`.
  have hEqOn : Set.EqOn Z V (Set.Icc (0 : ℝ) 1) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ => geodesicField g gi)
      (s := fun _ => S) (K := Kq)
      (fun t _ => hLip) hcont_Z
      (fun t ht => (hZderiv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => hmem_Z t (Set.Ico_subset_Icc_self ht))
      hcont_V
      (fun t ht => (hVode t (hIco_sub ht)).hasDerivWithinAt)
      (fun t ht => hmem_V t (Set.Ico_subset_Icc_self ht))
      ha
  have h1 : Z 1 = V 1 := hEqOn (Set.right_mem_Icc.mpr (by norm_num))
  have hZ1 : (Z 1).1 = (Y s).1 := by rw [hZdef]; simp [mul_one]
  have hV1 : (V 1).1 = uniformFlowExp g gi hC hK 0 sv := by
    rw [hVdef]; exact (uniformFlowExp_eq g gi hC hK 0 sv).symm
  rw [← hV1, ← h1]; exact hZ1

/-! ### The diagonal identity: velocity endpoint = differential of the exp endpoint on `(v, v)`. -/

/-- **THE DIAGONAL IDENTITY.**  At a reachable field point `v`
    (`‖v‖ < expRho 0`, `‖v‖ < ρ_K`) with base `0 ∈ K`,
        `(uniformFlowTube 0 v 1).2 = fderiv ℝ (uniformFlowExp 0) v [v]`.
    Proof: differentiate the reparametrisation identity `uniformFlow_scale_position` in `s` at `s = 1`
    (within `Iic 1`).  The left side `s ↦ uniformFlowExp 0 (s • v)` has within-derivative
    `fderiv (uniformFlowExp 0) v [v]` (chain rule); the right side `s ↦ (uniformFlowTube 0 v s).1` has
    within-derivative `(uniformFlowTube 0 v 1).2` (the tube ODE: the position slot's time-derivative
    is the velocity slot).  Uniqueness of the within-derivative closes it.  NOT `a₁ = R/6`. -/
theorem terminalVel0_apply_eq_fderiv_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (v : Point n)
    (hvexp : ‖v‖ < expRho g gi hC 0) (hvuf : ‖v‖ < uniformFlowRadius g gi hC hK) :
    (uniformFlowTube g gi hC hK 0 v 1).2
      = fderiv ℝ (uniformFlowExp g gi hC hK 0) v v := by
  have hvuf_le : ‖v‖ ≤ uniformFlowRadius g gi hC hK := hvuf.le
  -- Banked position regularity at `v`.
  have hcd4 : ContDiffAt ℝ 4 (uniformFlowExp g gi hC hK 0) v :=
    uniformFlowExp_contDiffAt_four g gi hC hK 0 h0K v hvexp hvuf
  have hFD : HasFDerivAt (uniformFlowExp g gi hC hK 0)
      (fderiv ℝ (uniformFlowExp g gi hC hK 0) v) v :=
    (hcd4.differentiableAt (by norm_num)).hasFDerivAt
  -- (Dψ) the right side (position endpoint at scaled time) has within-derivative = velocity endpoint.
  have h1mem : (1 : ℝ) ∈ Set.Ioo (-2 : ℝ) 2 := by norm_num
  have hode1 : HasDerivAt (uniformFlowTube g gi hC hK 0 v)
      (geodesicField g gi (uniformFlowTube g gi hC hK 0 v 1)) 1 :=
    uniformFlowTube_spec_ode g gi hC hK 0 h0K v hvuf_le 1 h1mem
  have hψ : HasDerivAt (fun s => (uniformFlowTube g gi hC hK 0 v s).1)
      ((uniformFlowTube g gi hC hK 0 v 1).2) 1 := by
    have hh := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt 1 hode1
    simpa only [Function.comp_def, ContinuousLinearMap.coe_fst'] using hh
  -- (Dφ) the left side has within-derivative `fderiv (uniformFlowExp 0) v [v]`.
  have hsv : HasDerivAt (fun s : ℝ => s • v) v 1 := by
    have hh := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v).hasDerivAt (x := (1 : ℝ))
    simpa [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply] using hh
  have hφ : HasDerivAt (fun s : ℝ => uniformFlowExp g gi hC hK 0 (s • v))
      (fderiv ℝ (uniformFlowExp g gi hC hK 0) v v) 1 := by
    have hFD1 : HasFDerivAt (uniformFlowExp g gi hC hK 0)
        (fderiv ℝ (uniformFlowExp g gi hC hK 0) v) ((1 : ℝ) • v) := by rw [one_smul]; exact hFD
    have hh := hFD1.comp_hasDerivAt (1 : ℝ) hsv
    simpa [Function.comp_def] using hh
  -- (H) the two sides agree on a left-neighbourhood of `s = 1`.
  have hmem : Set.Icc (1 / 2 : ℝ) 1 ∈ 𝓝[Set.Iic 1] (1 : ℝ) := by
    have h1 : Set.Iic 1 ∩ Set.Ioi (1 / 2 : ℝ) ∈ 𝓝[Set.Iic 1] (1 : ℝ) :=
      inter_mem_nhdsWithin (Set.Iic 1) (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
    exact mem_of_superset h1 (fun x hx => ⟨le_of_lt hx.2, hx.1⟩)
  have hhom : (fun s : ℝ => uniformFlowExp g gi hC hK 0 (s • v))
      =ᶠ[𝓝[Set.Iic 1] (1 : ℝ)] (fun s : ℝ => (uniformFlowTube g gi hC hK 0 v s).1) := by
    filter_upwards [hmem] with s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
    exact uniformFlow_scale_position g gi hC hK h0K v hvuf_le s hs01
  -- Transfer `hφ`'s derivative onto the right-side function, then uniqueness with `hψ`.
  have hφ' : HasDerivWithinAt (fun s : ℝ => (uniformFlowTube g gi hC hK 0 v s).1)
      (fderiv ℝ (uniformFlowExp g gi hC hK 0) v v) (Set.Iic 1) 1 :=
    (hφ.hasDerivWithinAt).congr_of_eventuallyEq hhom.symm
      (by rw [one_smul, uniformFlowExp_eq])
  have heq := UniqueDiffWithinAt.eq_deriv (Set.Iic 1) (uniqueDiffWithinAt_Iic 1)
    hφ' hψ.hasDerivWithinAt
  exact heq.symm

/-! ### `hT0` — the terminal-velocity `C²` at the centre. -/

/-- **★★ `hT0` — the terminal-velocity `C²` at the centre, UNCONDITIONAL (given `0 ∈ K`).**  The
    velocity endpoint `terminalVel0 v = (uniformFlowTube 0 v 1).2` is `ContDiffAt ℝ 2` at `0`.  Via
    the diagonal identity `terminalVel0_apply_eq_fderiv_diag`, `terminalVel0 =ᶠ[𝓝 0] (v ↦
    fderiv (uniformFlowExp 0) v [v])`; the position endpoint is `C⁴`
    (`uniformFlowExp_contDiffAt_four`), so `fderiv` is `C³` (`ContDiffAt.fderiv_right`) and the
    diagonal `C³` (`ContDiffAt.clm_apply`), hence `C² ≤ C³`.  This DISCHARGES the single residual of
    the geodesic-reversal route.  NOT `a₁ = R/6`. -/
theorem terminalVel0_contDiffAt_two (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    ContDiffAt ℝ 2 (terminalVel0 g gi hC hK) 0 := by
  -- Banked position `C⁴` at the centre.
  have hcd4 : ContDiffAt ℝ 4 (uniformFlowExp g gi hC hK 0) 0 :=
    uniformFlowExp_contDiffAt_four g gi hC hK 0 h0K 0
      (by simpa using expRho_pos g gi hC 0)
      (by simpa using uniformFlowRadius_pos g gi hC hK)
  have hfd3 : ContDiffAt ℝ 3 (fderiv ℝ (uniformFlowExp g gi hC hK 0)) 0 :=
    hcd4.fderiv_right (m := 3) (by norm_num)
  have hF3 : ContDiffAt ℝ 3
      (fun v => fderiv ℝ (uniformFlowExp g gi hC hK 0) v v) 0 :=
    hfd3.clm_apply contDiffAt_id
  have hF2 : ContDiffAt ℝ 2
      (fun v => fderiv ℝ (uniformFlowExp g gi hC hK 0) v v) 0 :=
    hF3.of_le (by norm_num)
  -- `terminalVel0 =ᶠ[𝓝 0] (v ↦ fderiv (uniformFlowExp 0) v [v])`.
  have hEq : terminalVel0 g gi hC hK
      =ᶠ[𝓝 (0 : Point n)] (fun v => fderiv ℝ (uniformFlowExp g gi hC hK 0) v v) := by
    have hball : Metric.ball (0 : Point n)
        (min (expRho g gi hC 0) (uniformFlowRadius g gi hC hK)) ∈ 𝓝 (0 : Point n) :=
      Metric.ball_mem_nhds _ (lt_min (expRho_pos g gi hC 0) (uniformFlowRadius_pos g gi hC hK))
    filter_upwards [hball] with v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    have hvexp : ‖v‖ < expRho g gi hC 0 := lt_of_lt_of_le hv (min_le_left _ _)
    have hvuf : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv (min_le_right _ _)
    exact terminalVel0_apply_eq_fderiv_diag g gi hC hK h0K v hvexp hvuf
  exact hF2.congr_of_eventuallyEq hEq

/-! ### The unconditional M1–M4 change-of-variables bundle. -/

/-- **★★ `baseVaryingIFTPackage_unconditional` — the M1–M4 base-varying CoV bundle, UNCONDITIONAL.**
    Composes the discharged `hT0` (`terminalVel0_contDiffAt_two`) through the geodesic-reversal
    transfer `baseVaryingIFTPackage_of_terminalVel_contDiffAt`, so the `.choose`/joint-base J3 blocker
    of the W1 chart-image approximate identity is fully removed: NO regularity hypothesis beyond the
    standing geometry `(hC, hK, K ∈ 𝓝 0)`.  NOT `a₁ = R/6`. -/
theorem baseVaryingIFTPackage_unconditional (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    ∃ ρ > (0 : ℝ), ∃ (Vinv : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      MeasurableSet (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0) (f' z)
            (Metric.ball (0 : Point n) ρ) z)
      ∧ Set.InjOn (fun z => uniformInverseChart g gi hC hK z 0) (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          Vinv (uniformInverseChart g gi hC hK z 0) = z)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ, 0 < |(f' z).det|)
      ∧ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)
          ∈ 𝓝 (0 : Point n) :=
  baseVaryingIFTPackage_of_terminalVel_contDiffAt g gi hC hK h0Kmem
    (terminalVel0_contDiffAt_two g gi hC hK (mem_of_mem_nhds h0Kmem))

end QIQTH.TerminalVelC2

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.TerminalVelC2
#print axioms geodesicField_scaleVel
#print axioms uniformFlow_scale_position
#print axioms terminalVel0_apply_eq_fderiv_diag
#print axioms terminalVel0_contDiffAt_two
#print axioms baseVaryingIFTPackage_unconditional
end AxiomChecks
