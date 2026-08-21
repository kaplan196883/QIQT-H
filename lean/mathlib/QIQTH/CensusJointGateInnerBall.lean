/-
  CensusJointGateInnerBall — the JOINT-GATE INNER-BALL bridge closing concern **(b)** of the
  `hCensusBound` (`hCross`) CoV-junction re-audit:  the "`z ∈ K` half" of the gate-split integral
  restriction is FREE from the already-standing geometry `K ∈ 𝓝 0`, so concern (b) reduces to G2 ALONE.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure STRUCTURAL set-membership bridge brick sitting on top of the banked `censusTauDeriv_gateSplit`
  (J4-937).  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise
  hypothesis, no existing banked file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE CONCERN (b), AS FLAGGED BY J4-944/945.  The census integrand over the base point `z` (field
  point FIXED at `0`) is `deriv (fun u ↦ vanVleckGatedWitness … u 0 z) (a−s) · F s z 0`.  The gate is the
  gated-kernel predicate at the census slice `(p, q) = (0, z)`, which is **JOINT**:
      `z ∈ K  ∧  0 ∈ S z`   (`gatedKernel K S H τ p q = if q∈K then (if p∈S q then H … else 0) else 0`).
  J4-937's `censusTauDeriv_gateSplit` proves the EVERYWHERE identity
      `deriv (fun u ↦ vanVleckGatedWitness … u 0 z) τ
         = if (z ∈ K ∧ 0 ∈ S z) then [CoV two-term closed form] else 0`.
  To identify the census integrand ON the two-term inner ball `ball 0 r` with the CoV closed form one
  needs `ball 0 r ⊆ {z | z ∈ K ∧ 0 ∈ S z}`, which splits as
      • the "`z ∈ K` half":  `ball 0 r ⊆ K`, and
      • G2:  `ball 0 r ⊆ {z | 0 ∈ S z}`.
  The prior reports listed the "`z ∈ K` half" as a residual obligation to be threaded separately.

  ## THE RESOLUTION (gpt-5.6-sol high adversarially confirmed).  The `z ∈ K` half is **NOT** a genuine
  new independent carry parallel to G2 — it follows FOR FREE from the already-standing geometry
  `h0Kmem : K ∈ 𝓝 0` (`K` is a neighbourhood of the census centre `0`; used throughout the assembly, e.g.
  `baseVaryingIFTData_nonempty`, `commonWitness_image_subball`).  By `Metric.mem_nhds_iff` there is
  `rK > 0` with `ball 0 rK ⊆ K`; intersecting with G2's `ball 0 rS` (radius `min rK rS`) gives
  `ball 0 r ⊆ K ∩ {z | 0 ∈ S z} = {z | z ∈ K ∧ 0 ∈ S z}` — the joint gate — on which
  `censusTauDeriv_gateSplit`'s `if_pos` branch fires.  The ASYMMETRY is real and is the whole point:
  `K` is GIVEN as a neighbourhood of `0` (`h0Kmem`), whereas `S` is an ABSTRACT gate-set family with NO
  neighbourhood assumption (e.g. `S ≡ ∅` makes `{z | 0 ∈ S z} = ∅`), so G2 is genuinely carried while the
  `z ∈ K` half is discharged by standing geometry.  Hence concern (b) reduces to **G2 alone**.

  Sol's residual caveats (NOT claimed closed here, none in this file): the inclusion proved is
  `ball 0 r ⊆ jointGate` (identity of the integrand ON the ball), NOT `jointGate ⊆ ball 0 r`, so the
  off-ball residue `jointGate \ ball 0 r` still needs the Gaussian-envelope tail control = concern (c);
  measurability/integrability of the abstract-`S` gated integrand is separate; and CoV chart validity of
  `uniformInverseChart` only needs the ORIGINAL base point `z ∈ K` (one-sided gate at `q = z`), which is
  exactly what `ball 0 r ⊆ K` supplies (no path/image-in-`K` condition arises for this orientation).

  ## WHAT LANDS.
    • `jointGate_innerBall_of_nhds_and_gateBall` — ★★ the SET BRIDGE / bundled joint-gate carry:
        `K ∈ 𝓝 0` (standing) + G2 `∃ rS>0, ball 0 rS ⊆ {z|0∈S z}`  ⟹  `∃ r>0, ball 0 r ⊆ {z | z∈K ∧ 0∈S z}`.
        The `z ∈ K` conjunct is supplied by `h0Kmem`; only G2 is a genuine input.
    • `censusTauDeriv_eq_onGate_on_jointGate_ball` — ★★ THE PAYOFF: on any ball contained in the joint
        gate, the gate-split `if` collapses to the on-gate CoV two-term closed form, for every `z` in the
        ball and every `τ`.  So the two-term integrand identity holds on `ball 0 r` from G2 + standing
        geometry ALONE — the `z ∈ K` conjunct never appears as a separate hypothesis.
    • `censusTauDeriv_onGate_innerBall_of_geometry` — ★★ the COMBINED bridge: from standing `K ∈ 𝓝 0` and
        G2 alone, there is an inner ball on which the census `∂_τ` kernel equals the on-gate closed form.
    • `jointGate_innerBall_satisfiable` — non-vacuity with TEETH: a genuinely NON-`univ` gate
        (`S z := ball z 1`, so `{z | 0 ∈ S z} = ball 0 1 ≠ univ`, exercising G2 non-trivially) and a
        compact neighbourhood `K := closedBall 0 1`, jointly inhabiting `h0Kmem` and G2 and producing a
        nonempty inner ball.

  ## HONEST STATUS.  RESOLVES concern (b) by CLARIFICATION: the "`z ∈ K` half" is discharged by the
  standing `K ∈ 𝓝 0`, so concern (b) is a non-issue MODULO G2 (no separate `z ∈ K` input).  Does NOT
  close `hCensusBound`/`hCross`.  Remaining CoV-junction obligations: (c) off-ball Gaussian envelope +
  integrability (incl. `jointGate \ ball 0 r`), (d) final rate absorption; plus G2/G3.  NONE in this file.
  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusTauDerivGateSplit

open Classical
open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.CensusTauDerivGateSplit
open scoped Topology BigOperators

namespace QIQTH.CensusJointGateInnerBall

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the SET BRIDGE: `z ∈ K` is free from `K ∈ 𝓝 0`, so concern (b) = G2.
    ############################################################################### -/

/-- **★★ `jointGate_innerBall_of_nhds_and_gateBall` — the JOINT-GATE inner ball (the "`z ∈ K` half" is
    FREE).**  Given the standing geometry `h0Kmem : K ∈ 𝓝 0` and the G2 carry
    `∃ rS>0, ball 0 rS ⊆ {z | 0 ∈ S z}`, there is a radius `r > 0` with
    `ball 0 r ⊆ {z | z ∈ K ∧ 0 ∈ S z}` — the FULL joint census gate.  The `z ∈ K` conjunct is discharged
    by `Metric.mem_nhds_iff.mp h0Kmem` (a ball `ball 0 rK ⊆ K`); take `r = min rK rS`.  So concern (b)'s
    "`z ∈ K` half" is NOT a genuine new carry — only G2 is a real input.  NOT `a₁ = R/6`. -/
theorem jointGate_innerBall_of_nhds_and_gateBall
    {K : Set (Point n)} (h0Kmem : K ∈ 𝓝 (0 : Point n)) (S : Point n → Set (Point n))
    (hS : ∃ rS : ℝ, 0 < rS ∧
        Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ S z}) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (0 : Point n) r ⊆ {z | z ∈ K ∧ (0 : Point n) ∈ S z} := by
  obtain ⟨rK, hrK, hballK⟩ := Metric.mem_nhds_iff.mp h0Kmem
  obtain ⟨rS, hrS, hballS⟩ := hS
  refine ⟨min rK rS, lt_min hrK hrS, ?_⟩
  intro z hz
  have hzK : z ∈ Metric.ball (0 : Point n) rK :=
    Metric.ball_subset_ball (min_le_left _ _) hz
  have hzS : z ∈ Metric.ball (0 : Point n) rS :=
    Metric.ball_subset_ball (min_le_right _ _) hz
  exact ⟨hballK hzK, hballS hzS⟩

/-! ###############################################################################
    ### §B — THE PAYOFF: on a joint-gate ball the gate-split `if_pos` branch fires.
    ############################################################################### -/

/-- **★★ `censusTauDeriv_eq_onGate_on_jointGate_ball` — the ON-GATE closed form on the joint-gate ball.**
    On any ball `ball 0 r` contained in the joint gate `{z | z ∈ K ∧ 0 ∈ S z}`, the census-slice `∂_τ`
    kernel equals the on-gate CoV two-term closed form for EVERY `z` in the ball and EVERY `τ` — the
    `if_pos` branch of `censusTauDeriv_gateSplit` (J4-937).  The `z ∈ K` conjunct comes bundled inside the
    ball hypothesis (via §A, from standing `K ∈ 𝓝 0`), so it never appears as a separate carry.  NOT
    `a₁ = R/6`. -/
theorem censusTauDeriv_eq_onGate_on_jointGate_ball (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Point n) r ⊆ {z | z ∈ K ∧ (0 : Point n) ∈ S z})
    (z : Point n) (hz : z ∈ Metric.ball (0 : Point n) r) (τ : ℝ) :
    deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) τ
      = ((∑ i, ((uniformInverseChart g gi hC hK z 0 i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)))
            * gaussDdim τ (uniformInverseChart g gi hC hK z 0))
          * chartFieldAmp g gi hC hK a b τ z 0
        + gaussDdim τ (uniformInverseChart g gi hC hK z 0)
            * censusAmpTauDeriv g gi hC hK a b z := by
  have hgate : z ∈ K ∧ (0 : Point n) ∈ S z := hball hz
  rw [censusTauDeriv_gateSplit hn g gi hC hK S a b z τ, if_pos hgate]

/-! ###############################################################################
    ### §C — THE COMBINED BRIDGE (concern (b) discharged modulo G2, from geometry).
    ############################################################################### -/

/-- **★★ `censusTauDeriv_onGate_innerBall_of_geometry` — concern (b) discharged modulo G2.**  From the
    standing geometry `h0Kmem : K ∈ 𝓝 0` and the G2 carry alone, there is an inner ball `ball 0 r` on
    which (i) the joint gate `{z | z ∈ K ∧ 0 ∈ S z}` holds and (ii) the census `∂_τ` kernel equals the
    on-gate CoV two-term closed form (for every `z` in the ball and every `τ`).  This packages §A + §B:
    the `z ∈ K` conjunct of the gate-split integral restriction is supplied by standing geometry, so the
    two-term integrand identity on `ball 0 r` needs ONLY G2 as an input.  NOT `a₁ = R/6`. -/
theorem censusTauDeriv_onGate_innerBall_of_geometry (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (S : Point n → Set (Point n)) (a b : ℝ)
    (hS : ∃ rS : ℝ, 0 < rS ∧
        Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ S z}) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (0 : Point n) r ⊆ {z | z ∈ K ∧ (0 : Point n) ∈ S z} ∧
      ∀ z ∈ Metric.ball (0 : Point n) r, ∀ τ : ℝ,
        deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) τ
          = ((∑ i, ((uniformInverseChart g gi hC hK z 0 i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)))
                * gaussDdim τ (uniformInverseChart g gi hC hK z 0))
              * chartFieldAmp g gi hC hK a b τ z 0
            + gaussDdim τ (uniformInverseChart g gi hC hK z 0)
                * censusAmpTauDeriv g gi hC hK a b z := by
  obtain ⟨r, hr, hball⟩ := jointGate_innerBall_of_nhds_and_gateBall h0Kmem S hS
  refine ⟨r, hr, hball, ?_⟩
  intro z hz τ
  exact censusTauDeriv_eq_onGate_on_jointGate_ball hn g gi hC hK S a b hr hball z hz τ

/-! ###############################################################################
    ### §D — non-vacuity (TEETH: a genuinely non-`univ` gate `S`, compact nbhd `K`).
    ############################################################################### -/

/-- **Non-vacuity of the joint-gate inner ball — TEETH.**  The two antecedents of §A are jointly
    inhabitable with a genuinely NON-trivial gate: `K := closedBall 0 1` is a COMPACT neighbourhood of `0`
    (finite-dim `Point n = Fin n → ℝ` is proper), and `S z := ball z 1` gives `{z | 0 ∈ S z} = ball 0 1`,
    which is NOT `univ` (so G2 is exercised non-trivially, `S ≡ univ` would trivialise it — witnessed by
    the constant-`2` point, whose sup-norm distance to `0` is `≥ 1` when `n ≥ 1`).  The bridge then
    produces a nonempty inner ball inside the joint gate.  NOT `a₁ = R/6`. -/
theorem jointGate_innerBall_satisfiable (hn : 0 < n) :
    ∃ (K : Set (Point n)) (S : Point n → Set (Point n)),
      IsCompact K ∧ K ∈ 𝓝 (0 : Point n) ∧
      (∃ rS : ℝ, 0 < rS ∧ Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ S z}) ∧
      (∃ z : Point n, (0 : Point n) ∉ S z) ∧
      ∃ r : ℝ, 0 < r ∧
        Metric.ball (0 : Point n) r ⊆ {z | z ∈ K ∧ (0 : Point n) ∈ S z} := by
  classical
  -- G2 for the concrete gate `S z := ball z 1`: `ball 0 1 ⊆ {z | 0 ∈ ball z 1}`.
  have hS : ∃ rS : ℝ, 0 < rS ∧
      Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ Metric.ball z 1} := by
    refine ⟨1, one_pos, ?_⟩
    intro z hz
    show (0 : Point n) ∈ Metric.ball z 1
    rw [Metric.mem_ball, dist_comm]
    exact Metric.mem_ball.mp hz
  have h0Kmem : Metric.closedBall (0 : Point n) 1 ∈ 𝓝 (0 : Point n) :=
    Metric.closedBall_mem_nhds _ one_pos
  refine ⟨Metric.closedBall (0 : Point n) 1, fun z => Metric.ball z 1,
    isCompact_closedBall _ _, h0Kmem, hS, ?_, ?_⟩
  · -- TEETH: the constant-`2` point has `0 ∉ ball (2·) 1`, so `{z | 0 ∈ S z} ≠ univ` (`S ≢ univ`).
    refine ⟨fun _ => (2 : ℝ), ?_⟩
    show (0 : Point n) ∉ Metric.ball (fun _ => (2 : ℝ)) 1
    rw [Metric.mem_ball, dist_comm, not_lt]
    -- sup-norm lower bound: any coordinate value `‖2‖ = 2 ≤ ‖const 2‖ = dist (const 2) 0`.
    have hcoord : ‖(2 : ℝ)‖ ≤ ‖(fun _ => (2 : ℝ) : Point n)‖ :=
      norm_le_pi_norm (fun _ => (2 : ℝ)) ⟨0, hn⟩
    rw [dist_zero_right]
    have : (1 : ℝ) ≤ ‖(fun _ => (2 : ℝ) : Point n)‖ := by
      have h2 : ‖(2 : ℝ)‖ = 2 := by rw [Real.norm_eq_abs]; norm_num
      rw [h2] at hcoord; linarith
    exact this
  · -- the produced inner ball, via §A.
    exact jointGate_innerBall_of_nhds_and_gateBall h0Kmem (fun z => Metric.ball z 1) hS

end QIQTH.CensusJointGateInnerBall

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusJointGateInnerBall
#print axioms jointGate_innerBall_of_nhds_and_gateBall
#print axioms censusTauDeriv_eq_onGate_on_jointGate_ball
#print axioms censusTauDeriv_onGate_innerBall_of_geometry
#print axioms jointGate_innerBall_satisfiable
end AxiomChecks
