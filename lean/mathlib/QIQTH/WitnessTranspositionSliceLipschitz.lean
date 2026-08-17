/-
  WitnessTranspositionSliceLipschitz — Task F (plan v3, `tranquil-stargazing-fox.md`): the ORIGIN-CHAIN
  assembly of the two-variable transposition bound from PER-SLICE (axis-aligned) regularity of `Φ`,
  materially weaker than the JOINT regularity `WitnessTranspositionGeneralBound` /
  `SecondFieldPartialContDiff` require.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  assembly brick of the `hCConv` transposition route.  No `sorry`, no `:= True`, no new axioms, no
  vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.  std-3 only.  No
  existing file is edited.  a₁ = R/6 remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ORIGIN-CHAIN (what this delivers, and why it is strictly more useful than the joint route).

  `WitnessTranspositionGeneralBound.general_transposition_sliver_of_lipschitzOnWith` (J4-823) bounds the
  transposition difference `|Φ(0,z) − Φ(z,0)| ≤ K·‖z‖` from a SINGLE JOINT `LipschitzOnWith K Φ S` on a
  neighbourhood of the swap pair.  `SecondFieldPartialContDiff.secondFieldPartial_transposition_sliver`
  supplies that joint fact from JOINT `ContDiffAt ℝ 3 H (0,0)` of the witness kernel.  The joint route is
  BLOCKED: the concrete `.choose`-built inverse chart of the live witness has no coherence across base
  points, so no joint continuity/differentiability of the second field-partial across the base slot is
  available (the `.choose`-incoherence firewall; JET4_TOWER_PLAN J4-836 / plan v3 §"v3 Context").

  ── THE WEAKER HYPOTHESIS THIS FILE USES.  Decompose the transposition difference through the ORIGIN
     `(0,0)`:
        `Φ(0,z) − Φ(z,0)  =  [Φ(0,z) − Φ(0,0)]  +  [Φ(0,0) − Φ(z,0)]`.
     * the SECOND bracket varies the FIELD coordinate `p` from `0` to `z` at FIXED base `q = 0` — the
       **p-slice** `p ↦ Φ(p,0)`;
     * the FIRST bracket varies the BASE coordinate `q` from `z` to `0` at FIXED field `p = 0` — the
       **q-slice** `q ↦ Φ(0,q)`.
     Each bracket is controlled by the mean-value / Lipschitz inequality along ITS OWN single-coordinate
     slice.  So the transposition bound follows from `LipschitzOnWith` (equivalently `ContDiffAt ℝ 1`)
     of the TWO one-dimensional slices SEPARATELY — never of the joint two-variable map.  This is the
     exact regularity register the `.choose`-incoherence firewall does NOT block on the p-slice: the
     p-slice `p ↦ Φ(p,0)` at the FIXED base `q = 0` is governed by the third FIELD-partial `∂³_p H` on
     the `q = 0` slice, which is UNCONDITIONAL (`WitnessThirdPartialUniformBound`, Task D; source
     `InverseChartFieldC3.witnessField_contDiffAt3_center`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (ns `QIQTH.HeatResidualBound`).

    * `general_transposition_diff_of_slice_lipschitzOnWith` — ★ the two-point origin-chain bound
        `|Φ(0,z) − Φ(z,0)| ≤ (Kp + Kq)·‖z‖`
      from `LipschitzOnWith Kp (p ↦ Φ(p,0))` on a set containing `{0, z}` (p-slice) and
      `LipschitzOnWith Kq (q ↦ Φ(0,q))` on a set containing `{0, z}` (q-slice).  Pure triangle +
      per-slice Lipschitz — NO joint Lipschitz, NO differentiability of the joint map.

    * `general_transposition_sliver_of_slice_lipschitzOnWith` — ★ sliver form: under `‖z‖ ≤ √ε`,
        `|Φ(0,z) − Φ(z,0)| ≤ (Kp + Kq)·√ε` — the O(√ε) rate the closed J4-817 sliver carries.

    * `general_transposition_sliver_of_slice_contDiffAt` — ★★ TERMINAL per-slice form: from PER-SLICE
      `ContDiffAt ℝ 1 (p ↦ Φ(p,0)) 0` and `ContDiffAt ℝ 1 (q ↦ Φ(0,q)) 0` — NOT joint `ContDiffAt` —
        `∃ K r>0, ∀ ‖z‖<r ∧ ‖z‖≤√ε,  |Φ(0,z) − Φ(z,0)| ≤ K·√ε`,
      the SAME output shape as `general_transposition_sliver_of_contDiffAt`, but with the joint-`C¹`
      hypothesis replaced by the two per-slice-`C¹` hypotheses.  This is the origin-chain reduction the
      plan (Task F) named, made rigorous and abstract.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## HONEST SCOPE — this does NOT close `hCConv`.

  This brick REDUCES the transposition sliver bound to TWO per-slice regularity inputs.  For the CONCRETE
  witness's second field-partial:
    * the p-slice input (`ContDiffAt ℝ 1 (p ↦ Φ(p,0)) 0` at fixed base `q = 0`) is UNCONDITIONAL — it is
      the field-`C³` slice `InverseChartFieldC3.witnessField_contDiffAt3_center` (Task D), one order above;
    * the q-slice input (`ContDiffAt ℝ 1 (q ↦ Φ(0,q)) 0` at fixed field `p = 0`) is the base-slot
      regularity of the second field-partial `∂_q ∂²_p H` — the MIXED base-slot regularity of the
      `.choose`-built inverse chart (Task E Part 2 / sub-brick 3b `ChartMixedThirdJetBasepoint`), whose
      weld to the concrete `uniformFlowExp` needs second-order base regularity of that flow, NOT in the
      tower.  Task E **Part 1** bounds `∂_q uniformFlowExp` (the flow endpoint, a ZEROTH-order field
      object) — the WRONG order for the q-slice, which differentiates the SECOND field-partial once more
      in `q`.  So the q-slice remains the SINGLE isolated remaining input.

  Additionally, the downstream weld `transposition ⟶ kPrime_opNorm_sliver_bound.hcomp` (the scalar
  per-component sliver `|∫∫ kPrime eⱼ|`) is a SEPARATE unbuilt chain (`SecondFieldPartialContDiff` itself
  records it does not wire into `hcomp`).  Neither this brick nor the joint route closes `hCConv`.

  No `sorry`, no new axioms, no `:= True`; every hypothesis satisfiable and non-vacuous; none equals the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature

open QIQTH.Curvature
open scoped Topology NNReal

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- **★ THE ORIGIN-CHAIN TWO-POINT TRANSPOSITION BOUND FROM PER-SLICE LIPSCHITZ.**
    For ANY `Φ : Point n × Point n → ℝ` whose p-slice `p ↦ Φ(p,0)` is `LipschitzOnWith Kp` on a set
    `Sp ∋ 0, z` and whose q-slice `q ↦ Φ(0,q)` is `LipschitzOnWith Kq` on a set `Sq ∋ 0, z`, the
    transposition difference obeys
        `|Φ(0,z) − Φ(z,0)| ≤ (Kp + Kq)·‖z‖`.
    Decomposition through the origin `(0,0)`:
        `Φ(0,z) − Φ(z,0) = [Φ(0,z) − Φ(0,0)] + [Φ(0,0) − Φ(z,0)]`,
    the first bracket bounded by the q-slice Lipschitz constant, the second by the p-slice constant —
    NO joint Lipschitz of the two-variable map is used.  NOT `a₁ = R/6`. -/
theorem general_transposition_diff_of_slice_lipschitzOnWith (Φ : Point n × Point n → ℝ)
    {Kp Kq : ℝ≥0} {Sp Sq : Set (Point n)}
    (hp : LipschitzOnWith Kp (fun p => Φ (p, (0 : Point n))) Sp)
    (hq : LipschitzOnWith Kq (fun q => Φ ((0 : Point n), q)) Sq)
    (z : Point n) (h0p : (0 : Point n) ∈ Sp) (hzp : z ∈ Sp)
    (h0q : (0 : Point n) ∈ Sq) (hzq : z ∈ Sq) :
    |Φ ((0 : Point n), z) - Φ (z, (0 : Point n))| ≤ ((Kp : ℝ) + Kq) * ‖z‖ := by
  -- q-slice control of the first bracket:  `|Φ(0,z) − Φ(0,0)| ≤ Kq·‖z‖`.
  have hqd := hq.dist_le_mul z hzq (0 : Point n) h0q
  -- p-slice control of the second bracket:  `|Φ(0,0) − Φ(z,0)| ≤ Kp·‖z‖`.
  have hpd := hp.dist_le_mul (0 : Point n) h0p z hzp
  rw [Real.dist_eq] at hqd hpd
  have hz1 : dist z (0 : Point n) = ‖z‖ := by rw [dist_eq_norm, sub_zero]
  have hz2 : dist (0 : Point n) z = ‖z‖ := by rw [dist_eq_norm, zero_sub, norm_neg]
  rw [hz1] at hqd
  rw [hz2] at hpd
  -- origin-chain split + triangle inequality.
  have hsplit : Φ ((0 : Point n), z) - Φ (z, (0 : Point n))
      = (Φ ((0 : Point n), z) - Φ ((0 : Point n), (0 : Point n)))
        + (Φ ((0 : Point n), (0 : Point n)) - Φ (z, (0 : Point n))) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  calc |Φ ((0 : Point n), z) - Φ ((0 : Point n), (0 : Point n))|
        + |Φ ((0 : Point n), (0 : Point n)) - Φ (z, (0 : Point n))|
      ≤ (Kq : ℝ) * ‖z‖ + (Kp : ℝ) * ‖z‖ := add_le_add hqd hpd
    _ = ((Kp : ℝ) + Kq) * ‖z‖ := by ring

/-- **★ SLIVER FORM.**  Under the sliver window `‖z‖ ≤ √ε`, the origin-chain per-slice transposition
    difference obeys `|Φ(0,z) − Φ(z,0)| ≤ (Kp + Kq)·√ε` — the O(√ε) rate the closed J4-817 sliver
    carries.  NOT `a₁ = R/6`. -/
theorem general_transposition_sliver_of_slice_lipschitzOnWith (Φ : Point n × Point n → ℝ)
    {Kp Kq : ℝ≥0} {ε : ℝ} {Sp Sq : Set (Point n)}
    (hp : LipschitzOnWith Kp (fun p => Φ (p, (0 : Point n))) Sp)
    (hq : LipschitzOnWith Kq (fun q => Φ ((0 : Point n), q)) Sq)
    (z : Point n) (h0p : (0 : Point n) ∈ Sp) (hzp : z ∈ Sp)
    (h0q : (0 : Point n) ∈ Sq) (hzq : z ∈ Sq) (hwin : ‖z‖ ≤ Real.sqrt ε) :
    |Φ ((0 : Point n), z) - Φ (z, (0 : Point n))| ≤ ((Kp : ℝ) + Kq) * Real.sqrt ε :=
  (general_transposition_diff_of_slice_lipschitzOnWith Φ hp hq z h0p hzp h0q hzq).trans
    (mul_le_mul_of_nonneg_left hwin (by positivity))

/-- **★★ TERMINAL — origin-chain transposition sliver bound from PER-SLICE `C¹`.**  If the p-slice
    `p ↦ Φ(p,0)` and the q-slice `q ↦ Φ(0,q)` are EACH `ContDiffAt ℝ 1` at `0` — NOT the joint
    two-variable map — then there are a constant `K` and a radius `r > 0` such that for every `z` with
    `‖z‖ < r` inside the sliver window `‖z‖ ≤ √ε`,
        `|Φ(0,z) − Φ(z,0)| ≤ K·√ε`.
    Same output shape as `general_transposition_sliver_of_contDiffAt`, with the joint-`C¹` hypothesis
    replaced by the two per-slice-`C¹` hypotheses.  Each per-slice `C¹` gives a local Lipschitz constant
    (`ContDiffAt.exists_lipschitzOnWith`) on a ball around `0`; the origin-chain bound then closes on the
    intersection.  This is the origin-chain reduction the plan (Task F) named.  NOT `a₁ = R/6`. -/
theorem general_transposition_sliver_of_slice_contDiffAt (Φ : Point n × Point n → ℝ)
    (hp : ContDiffAt ℝ 1 (fun p => Φ (p, (0 : Point n))) (0 : Point n))
    (hq : ContDiffAt ℝ 1 (fun q => Φ ((0 : Point n), q)) (0 : Point n)) :
    ∃ (K : ℝ≥0) (r : ℝ), 0 < r ∧ ∀ (z : Point n) (ε : ℝ), ‖z‖ < r → ‖z‖ ≤ Real.sqrt ε →
      |Φ ((0 : Point n), z) - Φ (z, (0 : Point n))| ≤ (K : ℝ) * Real.sqrt ε := by
  obtain ⟨Kp, tp, htp, hLipp⟩ := hp.exists_lipschitzOnWith
  obtain ⟨Kq, tq, htq, hLipq⟩ := hq.exists_lipschitzOnWith
  obtain ⟨rp, hrp, hballp⟩ := Metric.mem_nhds_iff.mp htp
  obtain ⟨rq, hrq, hballq⟩ := Metric.mem_nhds_iff.mp htq
  refine ⟨Kp + Kq, min rp rq, lt_min hrp hrq, fun z ε hzr hwin => ?_⟩
  have hz0 : dist z (0 : Point n) = ‖z‖ := by rw [dist_eq_norm, sub_zero]
  -- `z` and `0` land in both slice neighbourhoods.
  have hzrp : ‖z‖ < rp := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzrq : ‖z‖ < rq := lt_of_lt_of_le hzr (min_le_right _ _)
  have hz_tp : z ∈ tp := hballp (by rw [Metric.mem_ball, hz0]; exact hzrp)
  have h0_tp : (0 : Point n) ∈ tp := hballp (by rw [Metric.mem_ball, dist_self]; exact hrp)
  have hz_tq : z ∈ tq := hballq (by rw [Metric.mem_ball, hz0]; exact hzrq)
  have h0_tq : (0 : Point n) ∈ tq := hballq (by rw [Metric.mem_ball, dist_self]; exact hrq)
  have hbound := general_transposition_sliver_of_slice_lipschitzOnWith Φ hLipp hLipq z
    h0_tp hz_tp h0_tq hz_tq hwin
  -- `(Kp + Kq : ℝ≥0) : ℝ = (Kp : ℝ) + (Kq : ℝ)`.
  exact_mod_cast hbound

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms general_transposition_diff_of_slice_lipschitzOnWith
#print axioms general_transposition_sliver_of_slice_lipschitzOnWith
#print axioms general_transposition_sliver_of_slice_contDiffAt
end AxiomChecks
