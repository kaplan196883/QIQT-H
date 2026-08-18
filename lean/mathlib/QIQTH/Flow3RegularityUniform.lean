/-
  Flow3RegularityUniform — Plan v6/v7 Task N: the two `expRho`-FREE downstream second-jet slots,
  re-anchored on the NEW UNCONDITIONAL C⁴ regularity `uniformFlowExp_contDiffOn_four_uniform`
  (`UniformFlowExpContDiffFourUniform`, Task M), dropping the `expRho` reachability guard entirely.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.
  std-3 only.  No existing file is edited.  NO `expRho` anywhere.

  ── WHY THIS IS NOW POSSIBLE.  `Flow3Regularity.forward2_velocitySlot` (J4-480) and
  `HbaseJ2Assembly.uniformFlowExp_fderiv2_base_modulus` (J4-483) both carried the per-base reachability
  guard `‖v‖ < expRho g gi hC q`, purely because their C³ regularity was BORROWED from the
  `expMap ↔ uniformFlowExp` OVERLAP BRIDGE (`ChartThirdJet.uniformFlowExp_contDiffAt_four`), valid only
  inside the injectivity ball `expRho q`.  Plan v6/v7 Task M re-derived that C⁴ regularity DIRECTLY on
  the uniform confinement tube (`ExpMap.contDiffAt4_uniformFlowExp`,
  `HeatResidualBound.uniformFlowExp_contDiffOn_four_uniform`), UNCONDITIONALLY, with NO `expRho`.  So
  both slots can be re-anchored on the uniform C⁴, dropping the `expRho` guard: the ONLY use of the
  guard in either proof was to obtain the C³/C² differentiability of the forward map at `v`, which the
  uniform C⁴ now supplies from `‖v‖ < uniformFlowRadius` alone.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms, NO `expRho`; NOT `a₁ = R/6`).
    * `forward2_velocitySlot'` — ★ the VELOCITY-slot half of `hFwd2`, `expRho`-FREE.  Exact mirror of
      `Flow3Regularity.forward2_velocitySlot`, but the C³ forward map is a `.of_le (3 ≤ 4)` downgrade of
      the UNCONDITIONAL `ExpMap.contDiffAt4_uniformFlowExp` (needing only `‖v‖ < uniformFlowRadius`),
      NOT the `expRho`-gated `contDiffAt3_uniformFlowExp`.
    * `uniformFlowExp_fderiv2_base_modulus'` — ★★ hbaseJ2 (uniform interior), `expRho`-FREE.  Line-for-
      line mirror of `HbaseJ2Assembly.uniformFlowExp_fderiv2_base_modulus`, with the two `expRho` guards
      dropped from the statement and the two forward-map `C²`-differentiability facts (`hf2q`, `hf2q'`)
      re-anchored on `ExpMap.contDiffAt4_uniformFlowExp` (`.of_le` to C³ then `.fderiv_right`) instead of
      the `expRho`-gated `contDiffAt3_uniformFlowExp`.  EVERY other line is identical — the whole
      Grönwall / bridge / opNorm assembly used only `‖v‖ < uniformFlowRadius` and tube confinement, never
      `expRho`.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HbaseJ2Assembly
import QIQTH.UniformFlowExpContDiffFourUniform

open Filter Set
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.GeodesicGronwall
open QIQTH.HbaseJ2Gronwall QIQTH.JacobiCLMExposure QIQTH.SecondVariationModulus
open QIQTH.HbaseJ2Assembly
open scoped Topology NNReal

namespace QIQTH.Flow3RegularityUniform

variable {n : ℕ}

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 6

/-! ###############################################################################
    ### ★ THE VELOCITY-SLOT HALF OF `hFwd2`, `expRho`-FREE.
    ############################################################################### -/

/-- **★ `forward2_velocitySlot'` — the velocity-slot half of `hFwd2`, `expRho`-FREE.**  For a fixed base
    `z ∈ K` and a velocity `v₀` with `‖v₀‖ < uniformFlowRadius g gi hC hK` (NO `expRho` guard), the
    forward-flow SECOND jet in the velocity slot
        `v ↦ fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z)) v`
    is `ContinuousAt` at `v₀`.  Exact mirror of `Flow3Regularity.forward2_velocitySlot`, but the C³
    forward map is a `.of_le (3 ≤ 4)` downgrade of the UNCONDITIONAL `ExpMap.contDiffAt4_uniformFlowExp`
    (Task M), NOT the `expRho`-gated `contDiffAt3_uniformFlowExp`.  NOT `a₁ = R/6`. -/
theorem forward2_velocitySlot' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (hz : z ∈ K) (v₀ : Point n)
    (hvuf : ‖v₀‖ < uniformFlowRadius g gi hC hK) :
    ContinuousAt
      (fun v : Point n => fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z)) v) v₀ := by
  have hc3 : ContDiffAt ℝ 3 (uniformFlowExp g gi hC hK z) v₀ :=
    (contDiffAt4_uniformFlowExp g gi hC hK z hz v₀ hvuf).of_le (by norm_num)
  exact (((hc3.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
    (by norm_num))).continuousAt

/-! ###############################################################################
    ### ★★ hbaseJ2 (uniform interior), `expRho`-FREE.
    ############################################################################### -/

/-- **★★ `uniformFlowExp_fderiv2_base_modulus'` — hbaseJ2 (uniform interior), `expRho`-FREE.**  A single
    uniform `Λ₂ ≥ 0` over the compact `K` with
      `‖fderiv²(uniformFlowExp … q) v − fderiv²(uniformFlowExp … q') v‖ ≤ Λ₂·‖q − q'‖`
    for `q, q' ∈ K` and `v` with `‖v‖ < uniformFlowRadius g gi hC hK` (NO `expRho` guards).  Line-for-line
    mirror of `HbaseJ2Assembly.uniformFlowExp_fderiv2_base_modulus`, with the two forward-map
    `C²`-differentiability facts (`hf2q`, `hf2q'`) re-anchored on the UNCONDITIONAL
    `ExpMap.contDiffAt4_uniformFlowExp` (Task M) instead of the `expRho`-gated
    `contDiffAt3_uniformFlowExp`.  Every other line is identical.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_fderiv2_base_modulus' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ Λ₂ : ℝ, 0 ≤ Λ₂ ∧ ∀ q ∈ K, ∀ q' ∈ K, ∀ v : Point n,
      ‖v‖ < uniformFlowRadius g gi hC hK →
        ‖fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q)) v
            - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q')) v‖
          ≤ Λ₂ * ‖q - q'‖ := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- `K ⊆ closedBall 0 M`; the common confinement ball `S`.
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : Point n)
  set S : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) (M + C₀ * ρ) with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  -- global differentiability of the first jet (for the `D¹F` MVT).
  have hdiffglob : Differentiable ℝ (fderiv ℝ (geodesicField g gi)) :=
    ((contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top).differentiable (by simp)
  -- the `M₂` (C²) sup bound on `S`.
  obtain ⟨M₂, hM₂0, hM₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · refine ⟨0, le_refl _, fun z hz => ?_⟩
      rw [hSe] at hz; exact absurd hz (by simp)
    · have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
        (((contDiff_geodesicField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
          (by simp)).norm
      obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn hSne hcontr.continuousOn
      exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖,
        norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x),
        fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  -- the `M₃` (C³) two-point `D²F` separation on `S`.
  obtain ⟨M₃, hM₃0, hM₃sep⟩ := geodesicField_fderiv2_diff_bound g gi hC hScompact hSconv
  -- the field bound `Kf` on `S`.
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  -- the base-tube separation `Lsep` (uniform over `K`).
  obtain ⟨Lsep, hLsep0, hsep⟩ := uniformTube_twopoint_diff_bound g gi hC hK
  set Λ₂ : ℝ := 3 * M₂ ^ 2 * Real.exp Lsep * (Real.exp Kf) ^ 4
      + M₃ * Real.exp Lsep * (Real.exp Kf) ^ 3 with hΛ₂def
  have hΛ₂0 : 0 ≤ Λ₂ := by
    rw [hΛ₂def]
    have h1 : 0 ≤ 3 * M₂ ^ 2 * Real.exp Lsep * (Real.exp Kf) ^ 4 := by positivity
    have h2 : 0 ≤ M₃ * Real.exp Lsep * (Real.exp Kf) ^ 3 :=
      mul_nonneg (mul_nonneg hM₃0 (Real.exp_pos _).le) (by positivity)
    linarith
  refine ⟨Λ₂, hΛ₂0, ?_⟩
  intro q hq q' hq' v hvuf
  have hvρ : ‖v‖ ≤ ρ := hvuf.le
  -- both tubes live in `S`.
  have hmemtube : ∀ z ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      uniformFlowTube g gi hC hK z v τ ∈ S := by
    intro z hz τ hτ
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]
    have hconf : ‖uniformFlowTube g gi hC hK z v τ - ((z, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ :=
      uniformFlowTube_spec_conf g gi hC hK z hz v hvρ τ hτ
    have hzn : ‖((z, 0) : Point n × Point n)‖ ≤ M := by
      rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
      have := hM hz; rwa [Metric.mem_closedBall, dist_zero_right] at this
    calc ‖uniformFlowTube g gi hC hK z v τ‖
        ≤ ‖((z, 0) : Point n × Point n)‖
            + ‖uniformFlowTube g gi hC hK z v τ - ((z, 0) : Point n × Point n)‖ := by
          have := norm_add_le ((z, 0) : Point n × Point n)
            (uniformFlowTube g gi hC hK z v τ - ((z, 0) : Point n × Point n))
          simpa using this
      _ ≤ M + C₀ * ‖v‖ := add_le_add hzn hconf
      _ ≤ M + C₀ * ρ := by
          have : C₀ * ‖v‖ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ hC₀nn
          linarith
  -- `C²` differentiability of both forward maps at `v` (for the second-jet bridge) — re-anchored on the
  -- UNCONDITIONAL C⁴ (Task M), NO `expRho`.
  have hc3q : ContDiffAt ℝ 3 (uniformFlowExp g gi hC hK q) v :=
    (contDiffAt4_uniformFlowExp g gi hC hK q hq v hvuf).of_le (by norm_num)
  have hc3q' : ContDiffAt ℝ 3 (uniformFlowExp g gi hC hK q') v :=
    (contDiffAt4_uniformFlowExp g gi hC hK q' hq' v hvuf).of_le (by norm_num)
  have hf2q : DifferentiableAt ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q)) v :=
    ((hc3q.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hf2q' : DifferentiableAt ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q')) v :=
    ((hc3q'.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  -- field bounds along both tubes.
  have hKbq : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ)‖ ≤ Kf :=
    fun τ hτ => hKf _ (hmemtube q hq τ hτ)
  have hKbq' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q' v τ)‖ ≤ Kf :=
    fun τ hτ => hKf _ (hmemtube q' hq' τ hτ)
  -- C² bounds along both tubes.
  have hD2q : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q v τ)‖ ≤ M₂ :=
    fun τ hτ => hM₂ _ (hmemtube q hq τ hτ)
  have hD2q' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q' v τ)‖ ≤ M₂ :=
    fun τ hτ => hM₂ _ (hmemtube q' hq' τ hτ)
  set Dc : ℝ := M₂ * (‖q - q'‖ * Real.exp Lsep) with hDcdef
  set DD : ℝ := M₃ * (‖q - q'‖ * Real.exp Lsep) with hDDdef
  -- coefficient separation `Dc` (D¹F MVT × tube separation).
  have hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ)
          - fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q' v τ)‖ ≤ Dc := by
    intro τ hτ
    have hmvt := hSconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fderiv ℝ (geodesicField g gi)) (fun x _ => hdiffglob x) hM₂
      (hmemtube q' hq' τ hτ) (hmemtube q hq τ hτ)
    refine hmvt.trans ?_
    have hd := hsep q hq q' hq' v hvρ τ hτ
    simp only [dist_eq_norm] at hd
    have hexpτ : Real.exp (Lsep * τ) ≤ Real.exp Lsep := by
      apply Real.exp_le_exp.mpr
      calc Lsep * τ ≤ Lsep * 1 := mul_le_mul_of_nonneg_left hτ.2 hLsep0
        _ = Lsep := mul_one _
    rw [hDcdef]
    calc M₂ * ‖uniformFlowTube g gi hC hK q v τ - uniformFlowTube g gi hC hK q' v τ‖
        ≤ M₂ * (‖q - q'‖ * Real.exp (Lsep * τ)) := mul_le_mul_of_nonneg_left hd hM₂0
      _ ≤ M₂ * (‖q - q'‖ * Real.exp Lsep) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpτ (norm_nonneg _)) hM₂0
  -- `D²F` separation `DD` (M₃ two-point bound × tube separation).
  have hDD_bound : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q v τ)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q' v τ)‖ ≤ DD := by
    intro τ hτ
    refine (hM₃sep _ (hmemtube q hq τ hτ) _ (hmemtube q' hq' τ hτ)).trans ?_
    have hd := hsep q hq q' hq' v hvρ τ hτ
    simp only [dist_eq_norm] at hd
    have hexpτ : Real.exp (Lsep * τ) ≤ Real.exp Lsep := by
      apply Real.exp_le_exp.mpr
      calc Lsep * τ ≤ Lsep * 1 := mul_le_mul_of_nonneg_left hτ.2 hLsep0
        _ = Lsep := mul_one _
    rw [hDDdef]
    calc M₃ * ‖uniformFlowTube g gi hC hK q v τ - uniformFlowTube g gi hC hK q' v τ‖
        ≤ M₃ * (‖q - q'‖ * Real.exp (Lsep * τ)) := mul_le_mul_of_nonneg_left hd hM₃0
      _ ≤ M₃ * (‖q - q'‖ * Real.exp Lsep) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpτ (norm_nonneg _)) hM₃0
  -- THE PER-PAIR BOUND: for each `(δ, b')`, bridge to the per-seed core.
  have hper : ∀ δ b' : Point n,
      ‖(fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q)) v
          - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q')) v) δ b'‖
        ≤ Λ₂ * ‖q - q'‖ * ‖δ‖ * ‖b'‖ := by
    intro δ b'
    obtain ⟨Jf0q, Vfq, L₂q, hJf0q0, hJf0qode, hVfq0, hVfqode, hL₂q, hFDq⟩ :=
      uniformFlowExp_secondVar_spec g gi hC hK q hq v hvuf b'
    obtain ⟨Jf0q', Vfq', L₂q', hJf0q'0, hJf0q'ode, hVfq'0, hVfq'ode, hL₂q', hFDq'⟩ :=
      uniformFlowExp_secondVar_spec g gi hC hK q' hq' v hvuf b'
    have hbrq := fderiv2_apply_eq_of_hasFDerivAt hf2q hFDq
    have hbrq' := fderiv2_apply_eq_of_hasFDerivAt hf2q' hFDq'
    have hval : (fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q)) v
          - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q')) v) δ b'
        = (Vfq δ 1).2.1 - (Vfq' δ 1).2.1 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
          ← hbrq δ, ← hbrq' δ, hL₂q δ, hL₂q' δ]
    rw [hval]
    have hcore := secondVar_endpoint_seed_diff_bound g gi hC
      (Y₁ := uniformFlowTube g gi hC hK q v) (Y₂ := uniformFlowTube g gi hC hK q' v)
      (Jf1 := Jf0q) (Jf2 := Jf0q') (Vf1 := Vfq δ) (Vf2 := Vfq' δ) (b := b') (δ := δ)
      (Kf := Kf) (M₂ := M₂) (Dc := Dc) (DD := DD)
      hKf0 hM₂0 hJf0q0 hJf0q'0 hJf0qode hJf0q'ode (hVfq0 δ) (hVfq'0 δ) (hVfqode δ) (hVfq'ode δ)
      hKbq hKbq' hD2q hD2q' hAd hDD_bound
    calc ‖(Vfq δ 1).2.1 - (Vfq' δ 1).2.1‖
        = ‖((Vfq δ 1).2 - (Vfq' δ 1).2).1‖ := by rw [Prod.fst_sub]
      _ ≤ ‖(Vfq δ 1).2 - (Vfq' δ 1).2‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ (3 * Dc * M₂ * (Real.exp Kf) ^ 4 + DD * (Real.exp Kf) ^ 3) * ‖δ‖ * ‖b'‖ := hcore
      _ = Λ₂ * ‖q - q'‖ * ‖δ‖ * ‖b'‖ := by rw [hDcdef, hDDdef, hΛ₂def]; ring
  -- THE DOUBLE OPERATOR NORM.
  exact opNorm2_le_bound
    (fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q)) v
      - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q')) v)
    (mul_nonneg hΛ₂0 (norm_nonneg _)) hper

end QIQTH.Flow3RegularityUniform

section AxiomChecks
open QIQTH.Flow3RegularityUniform
#print axioms forward2_velocitySlot'
#print axioms uniformFlowExp_fderiv2_base_modulus'
end AxiomChecks
