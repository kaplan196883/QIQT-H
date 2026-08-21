/-
  CensusHballrateModuloG2 — the FULL modulo-G2 assembly of the C1 on-ball trace-rate carry `hballrate`
  of the `hCross` census chain, from the D-parameterized transported-weight regularity
  (`census_transported_weights_forData`) + the CoV two-term Gaussian core.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  the `hballrate` slot MODULO the single G2 gate carry `∃ rS>0, ball 0 rS ⊆ {z | 0 ∈ S z}` (supplied as
  a hypothesis), by assembling ALREADY-banked bricks.  No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable / conclusion-in-disguise hypothesis (the whole antecedent bundle is jointly
  satisfiable — the census gate is genuinely inhabited), no existing banked file edited.

  ## THE ASSEMBLY (Sol-validated design, gpt-5.6-sol high 2026-08-21).
    Fix the ONE common-witness `D` (`baseVaryingIFTData_nonempty`).  Get the D-parameterized uniform
    transported weights `q₁ = (amp·F)/|det|`, `q₂ = (slope·F)/|det|` on `ball 0 σ` (bounded `M₁,M₂`,
    pairwise-Lipschitz `Lq₁,Lq₂`).  Choose the split radius `ρ := δ = min (image-subdomain radius)
    (joint-gate radius)` so that `ball 0 δ ⊆ jointGate` AND `Wbv '' (ball 0 δ) ⊆ ball 0 σ`, with an
    inner ball `ball 0 r ⊆ Wbv '' (ball 0 δ)`.  Then, for each `(s, a)` (τ = a−s ∈ (0, τ₀]):
      • on `ball 0 δ ⊆ jointGate` the census `∂_τ` kernel collapses to the two-term closed form
        (`censusTauDeriv_eq_onGate_on_jointGate_ball`), so the integrand is `gaussDdim τ (Wbv z)·B z`;
      • the base-slot Gaussian change of variables (`commonWitness_cov_subball`) transports it to
        `∫ w in Wbv''(ball 0 δ), gaussDdim τ w·(B(D.V w)/|det (fderiv Wbv (D.V w))|)`;
      • `commonWitness_weightMatch` turns `poly(Wbv(D.V w)) = poly(w)`, folding the image integrand to
        `poly(w)·gaussDdim τ w·q₁ w + gaussDdim τ w·q₂ w`;
      • `integral_add` splits it (two `integrableOn_gauss_mul_bddOn_ball` proofs on the finite-measure
        image ball);
      • truncating `q₁,q₂` to `ball 0 σ` (`aesm_indicator_of_ball_lipschitz` gives global measurability
        from the KEPT `q₂` Lipschitz) and noting `image ⊆ ball 0 σ`, the two-term census core
        `two_term_census_bound_uniform_combined` applies at `Ω := Wbv''(ball 0 δ) ⊇ ball 0 r`, giving
        `≤ Cpair/√τ = Cpair·(a−s)^{−1/2}`.

  ## HONEST STATUS (blunt; gpt-5.6-sol high final adversarial audit 2026-08-21 — SOUND).  Under the
  standing geometry + s-uniform `F`-regularity hypotheses and G2 (`hS`), `hballrate_moduloG2` PRODUCES
  `ρ > 0` and `Cpair ≥ 0` inhabiting EXACTLY the `hballrate` existential predicate of J4-954's
  `censusBound_of_geometry_gate_supp_F_ballRate_anyS_existRho` (verified by literal type-match) — the
  witness is INDEPENDENT of the capstone's `FixedFlowGateData`.  So the `hballrate` ARGUMENT SLOT (the
  existential sub-predicate) is closed MODULO G2.  It does NOT provide an INTEGRATED capstone
  application: the capstone's SIBLING premises `hF(ρ)`, `hΦint(ρ)`, `hSupp` must hold at the SAME `ρ`
  (not supplied here), and the full `hCensusBound`/`hCross` additionally need the J4-929 differentiation
  carries and G2 (`hS`) itself discharged from the concrete gate.  It discharges NONE of `{hballrate,
  hDuhamel, hDConv, hCConv}` as a top-level τ-carry.  Non-vacuity (`_carries_satisfiable`) witnesses the
  NEW `{hS, hFb, hFl, numeric}` carries jointly satisfiable RELATIVE to the standing geometry (the
  geometry carriers are the tower's standing abstract carriers, inhabited by any Riemannian metric).
  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}` (with `hCross`/`hCensusBound` an OPEN downstream carry — this brick
  removes the `hballrate` sub-obstruction MODULO G2), UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusTransportedWeightsForData
import QIQTH.CensusJointGateInnerBall
import QIQTH.CensusCovSubballMeasurable
import QIQTH.CensusImageSubballBridge
import QIQTH.GaussTauTraceChartTransported
import QIQTH.BoundaryAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatResidualBound
open QIQTH.CensusTauDerivGateSplit QIQTH.CensusAmpConcreteRegularity
open QIQTH.BaseVaryingIFTCommonWitness QIQTH.BaseSlotDetRegularity
open QIQTH.CensusJointGateInnerBall QIQTH.CensusCovSubballMeasurable
open QIQTH.CensusImageSubballBridge QIQTH.CensusTransportedWeightsForData
open scoped Topology BigOperators ContDiff

namespace QIQTH.CensusHballrateModuloG2

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-- **★★★ `hballrate_moduloG2` — the FULL modulo-G2 `hballrate` (C1 on-ball trace rate).**  For the
    concrete gated van-Vleck witness, given the standing geometry, the s-uniform `F`-regularity carries,
    and the SINGLE G2 gate carry `hS : ∃ rS>0, ball 0 rS ⊆ {z | 0 ∈ S z}`, there is a geometry-
    determined split radius `ρ > 0` and a single pair-constant `Cpair ≥ 0` such that for EVERY
    `s ∈ Ioo (u−ε) u` and EVERY `a ∈ Icc u (u+h)`,
      `|∫ z in ball 0 ρ, deriv (fun r => vanVleckGatedWitness … r 0 z) (a−s) · F s z 0|
         ≤ Cpair · (a−s)^{−1/2}` .
    The produced `(ρ, Cpair)` inhabit EXACTLY the `hballrate` existential predicate of
    `censusBound_of_geometry_gate_supp_F_ballRate_anyS_existRho` (J4-954) — the caller instantiates the
    capstone's caller-chosen `ρ, Cpair` with these; the sibling premises `hF(ρ)/hΦint(ρ)/hSupp` at that
    same `ρ` remain the caller's.  The `hballrate` ARGUMENT SLOT is thus closed MODULO G2.
    NOT `a₁ = R/6`. -/
theorem hballrate_moduloG2 (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F : ℝ → Point n → Point n → ℝ) (u ε h τ₀ : ℝ)
    (hε : 0 < ε) (hτ₀ : 0 < τ₀) (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀)
    (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMF : 0 ≤ M_F) (hLF : 0 ≤ L_F)
    (hFb : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F)
    (hFl : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF →
      |F s z 0 - F s w 0| ≤ L_F * dist z w)
    (hS : ∃ rS : ℝ, 0 < rS ∧ Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ S z}) :
    ∃ (ρ Cpair : ℝ), 0 < ρ ∧ 0 ≤ Cpair ∧
      ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        |∫ z in Metric.ball (0 : Point n) ρ,
            deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
          ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2) := by
  classical
  -- ═══ the ONE common witness `D`. ═══
  obtain ⟨D⟩ := baseVaryingIFTData_nonempty g gi hC hK h0Kmem
  -- ═══ D-parameterized uniform transported weights (bounds + BOTH Lipschitz). ═══
  obtain ⟨σ, M₁, M₂, Lq₁, Lq₂, hσ0, hM₁, hM₂, hLq₁, hLq₂, hreg⟩ :=
    census_transported_weights_forData g gi hC hK D cutA cutB τ₀ hτ₀ h0Kmem hg hg0 hu
      F u ε rF M_F L_F hrF hMF hLF hFb hFl
  -- ═══ joint-gate inner ball (from G2 + standing geometry). ═══
  obtain ⟨r_j, hr_j, hjoint⟩ := jointGate_innerBall_of_nhds_and_gateBall h0Kmem S hS
  -- ═══ upper image containment: `Wbv '' (ball 0 δ₀) ⊆ ball 0 σ`. ═══
  obtain ⟨δ₀, hδ₀, hδ₀ρ, hupper⟩ := commonWitness_image_subball D h0Kmem σ hσ0
  -- ═══ shrink to the joint gate: `δ := min δ₀ r_j`. ═══
  set δ : ℝ := min δ₀ r_j with hδdef
  have hδ0 : 0 < δ := lt_min hδ₀ hr_j
  have hδD : δ ≤ D.ρ := le_trans (min_le_left _ _) hδ₀ρ
  have hballjoint : Metric.ball (0 : Point n) δ ⊆ {z | z ∈ K ∧ (0 : Point n) ∈ S z} :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hjoint
  have himgσ : (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) δ)
      ⊆ Metric.ball (0 : Point n) σ :=
    (Set.image_mono (Metric.ball_subset_ball (min_le_left _ _))).trans hupper
  -- ═══ inner ball for the shrunk `δ`. ═══
  obtain ⟨r, hr, hlower⟩ := commonWitness_innerBall_of_subdomain D δ hδ0
  -- ═══ measurability of the CoV image. ═══
  have hΩmeas : MeasurableSet
      ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) δ)) :=
    commonWitness_image_measurable D δ hδD
  set Ω : Set (Point n) :=
    (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) δ) with hΩdef
  -- ═══ the pair constant. ═══
  set Cpair : ℝ :=
    Lq₁ * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1))
      + (3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * (4 * (2 * (n : ℝ) + 1) / r ^ 2)) + M₂)
          * Real.sqrt τ₀ with hCpairdef
  have hCpair0 : 0 ≤ Cpair := by
    rw [hCpairdef]
    refine add_nonneg (mul_nonneg hLq₁ (by positivity))
      (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by positivity) hM₁) (by positivity)) hM₂)
        (Real.sqrt_nonneg _))
  refine ⟨δ, Cpair, hδ0, hCpair0, ?_⟩
  intro s hs a ha
  set τ : ℝ := a - s with hτdef
  -- horizon facts.
  have hτpos : 0 < τ := by
    rw [hτdef]; have := hs.2; have := ha.1; linarith
  have hτT : τ ≤ τ₀ := by
    rw [hτdef]; have := hs.1; have := ha.2; linarith
  have h4τ2 : (0 : ℝ) < 4 * τ ^ 2 := mul_pos (by norm_num) (pow_pos hτpos 2)
  have h2τ : (0 : ℝ) < 2 * τ := mul_pos (by norm_num) hτpos
  -- extract the (s, τ) regularity.
  obtain ⟨hq1b, hq1l, hq2b, hq2l⟩ := hreg s hs τ hτpos hτT
  -- ═══ the transported weights (named). ═══
  set W₀ : Point n → Point n := fun z => uniformInverseChart g gi hC hK z 0 with hW₀def
  set detf : Point n → ℝ := fun z => (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det
    with hdetfdef
  set q₁ : Point n → ℝ :=
    fun w => chartFieldAmp g gi hC hK cutA cutB τ (D.V w) 0 * F s (D.V w) 0 / |detf (D.V w)|
    with hq₁def
  set q₂ : Point n → ℝ :=
    fun w => censusAmpTauDeriv g gi hC hK cutA cutB (D.V w) * F s (D.V w) 0 / |detf (D.V w)|
    with hq₂def
  set qt₁ : Point n → ℝ := Set.indicator (Metric.ball (0 : Point n) σ) q₁ with hqt₁def
  set qt₂ : Point n → ℝ := Set.indicator (Metric.ball (0 : Point n) σ) q₂ with hqt₂def
  -- global boundedness of the truncations.
  have hqt1bnd : ∀ z, |qt₁ z| ≤ M₁ := by
    intro z; rw [hqt₁def, Set.indicator_apply]
    by_cases hz : z ∈ Metric.ball (0 : Point n) σ
    · simp only [if_pos hz]; exact hq1b z hz
    · simp only [if_neg hz, abs_zero]; exact hM₁
  have hqt2bnd : ∀ z, |qt₂ z| ≤ M₂ := by
    intro z; rw [hqt₂def, Set.indicator_apply]
    by_cases hz : z ∈ Metric.ball (0 : Point n) σ
    · simp only [if_pos hz]; exact hq2b z hz
    · simp only [if_neg hz, abs_zero]; exact hM₂
  -- measurability of the truncations (from the KEPT Lipschitz data).
  have hqt1meas : AEStronglyMeasurable qt₁ volume :=
    aesm_indicator_of_ball_lipschitz σ Lq₁ hLq₁ q₁ hq1l
  have hqt2meas : AEStronglyMeasurable qt₂ volume :=
    aesm_indicator_of_ball_lipschitz σ Lq₂ hLq₂ q₂ hq2l
  -- center-Lipschitz of `qt₁` on `ball 0 r`.
  have hrσ : Metric.ball (0 : Point n) r ⊆ Metric.ball (0 : Point n) σ := hlower.trans himgσ
  have h0σ : (0 : Point n) ∈ Metric.ball (0 : Point n) σ := Metric.mem_ball_self hσ0
  have hqt1cl : ∀ z ∈ Metric.ball (0 : Point n) r, |qt₁ z - qt₁ 0| ≤ Lq₁ * ‖z‖ := by
    intro z hz
    have hzσ : z ∈ Metric.ball (0 : Point n) σ := hrσ hz
    rw [hqt₁def, Set.indicator_of_mem hzσ q₁, Set.indicator_of_mem h0σ q₁]
    have := hq1l z hzσ 0 h0σ
    rwa [dist_zero_right] at this
  -- ═══ the base weight `B`. ═══
  set B : Point n → ℝ :=
    fun z => (∑ i, ((uniformInverseChart g gi hC hK z 0 i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)))
        * chartFieldAmp g gi hC hK cutA cutB τ z 0 * F s z 0
      + censusAmpTauDeriv g gi hC hK cutA cutB z * F s z 0 with hBdef
  -- STEP A: rewrite the census integrand on `ball 0 δ` via the on-gate closed form.
  have hstepA : (∫ z in Metric.ball (0 : Point n) δ,
        deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ * F s z 0)
      = ∫ z in Metric.ball (0 : Point n) δ,
          gaussDdim τ (uniformInverseChart g gi hC hK z 0) * B z := by
    refine setIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
    rw [censusTauDeriv_eq_onGate_on_jointGate_ball hn g gi hC hK S cutA cutB hδ0 hballjoint z hz τ]
    simp only [hBdef]; ring
  -- term1, term2 (the two-term integrand shapes).
  -- STEP C: fold the image integrand via `commonWitness_weightMatch`.
  have hcongr : Set.EqOn
      (fun w => gaussDdim τ w * (B (D.V w) / |detf (D.V w)|))
      (fun w => (∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ w * qt₁ w
        + gaussDdim τ w * qt₂ w)
      Ω := by
    intro w hw
    have hwσ : w ∈ Metric.ball (0 : Point n) σ := himgσ hw
    have hwDρ : w ∈ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) D.ρ) :=
      Set.image_mono (Metric.ball_subset_ball hδD) hw
    have hmatch : uniformInverseChart g gi hC hK (D.V w) 0 = w :=
      commonWitness_weightMatch D w hwDρ
    have hqt1w : qt₁ w = q₁ w := by rw [hqt₁def, Set.indicator_of_mem hwσ q₁]
    have hqt2w : qt₂ w = q₂ w := by rw [hqt₂def, Set.indicator_of_mem hwσ q₂]
    simp only [hBdef, hq₁def, hq₂def, hqt1w, hqt2w, hmatch]
    ring
  -- integrability of the two image integrands (finite-measure ball, bounded weights).
  -- term2: `gaussDdim τ · qt₂` integrable on `ball 0 σ ⊇ Ω`.
  have hInt2ball : IntegrableOn (fun w => gaussDdim τ w * qt₂ w) (Metric.ball (0 : Point n) σ) volume :=
    integrableOn_gauss_mul_bddOn_ball τ hτpos qt₂ M₂ σ hqt2meas (fun z _ => hqt2bnd z)
  have hInt2 : IntegrableOn (fun w => gaussDdim τ w * qt₂ w) Ω volume :=
    hInt2ball.mono_set himgσ
  -- poly bound on `ball 0 σ`.
  set Cpoly : ℝ := (n : ℝ) * (σ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) with hCpolydef
  have hpolybnd : ∀ w ∈ Metric.ball (0 : Point n) σ,
      |∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| ≤ Cpoly := by
    intro w hw
    have hwσ : ‖w‖ < σ := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hw
    have hper : ∀ i : Fin n, |(w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)|
        ≤ σ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ) := by
      intro i
      have hwi : |w i| ≤ ‖w‖ := norm_le_pi_norm w i
      have hwi2 : (w i) ^ 2 ≤ σ ^ 2 := by
        have h1 : (w i) ^ 2 = |w i| ^ 2 := (sq_abs _).symm
        have h2 : |w i| ≤ σ := le_of_lt (lt_of_le_of_lt hwi hwσ)
        rw [h1]; nlinarith [abs_nonneg (w i), h2]
      have hA : (0 : ℝ) ≤ (w i) ^ 2 / (4 * τ ^ 2) := div_nonneg (sq_nonneg _) h4τ2.le
      have hB : (0 : ℝ) < 1 / (2 * τ) := div_pos one_pos h2τ
      have hAle : (w i) ^ 2 / (4 * τ ^ 2) ≤ σ ^ 2 / (4 * τ ^ 2) :=
        div_le_div_of_nonneg_right hwi2 h4τ2.le
      rw [abs_le]; constructor
      · linarith
      · linarith
    calc |∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))|
        ≤ ∑ i, |(w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (σ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) := Finset.sum_le_sum (fun i _ => hper i)
      _ = Cpoly := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hCpolydef, nsmul_eq_mul]
  -- term1: `poly · gaussDdim τ · qt₁` integrable on `ball 0 σ ⊇ Ω`.
  have hpolycont : Continuous (fun w : Point n => ∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).pow 2).div_const _ |>.sub continuous_const
  have hf1meas : AEStronglyMeasurable
      (fun w : Point n => (∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * qt₁ w) volume :=
    hpolycont.aestronglyMeasurable.mul hqt1meas
  have hf1bnd : ∀ z ∈ Metric.ball (0 : Point n) σ,
      |(∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * qt₁ z| ≤ Cpoly * M₁ := by
    intro z hz
    rw [abs_mul]
    have hCpoly0 : (0 : ℝ) ≤ Cpoly := by
      rw [hCpolydef]; refine mul_nonneg (Nat.cast_nonneg _) ?_
      have := h4τ2; have := h2τ; positivity
    exact mul_le_mul (hpolybnd z hz) (hqt1bnd z) (abs_nonneg _) hCpoly0
  have hInt1ball0 : IntegrableOn
      (fun w => gaussDdim τ w * ((∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * qt₁ w))
      (Metric.ball (0 : Point n) σ) volume :=
    integrableOn_gauss_mul_bddOn_ball τ hτpos
      (fun w => (∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * qt₁ w) (Cpoly * M₁) σ hf1meas hf1bnd
  have hterm1eq : (fun w => gaussDdim τ w * ((∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * qt₁ w))
      = fun w => (∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ w * qt₁ w := by
    funext w; ring
  have hInt1ball : IntegrableOn
      (fun w => (∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ w * qt₁ w)
      (Metric.ball (0 : Point n) σ) volume := by
    rw [hterm1eq] at hInt1ball0; exact hInt1ball0
  have hInt1 : IntegrableOn
      (fun w => (∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ w * qt₁ w) Ω volume :=
    hInt1ball.mono_set himgσ
  -- ═══ the chained equality census = ∫Ω term1 + ∫Ω term2. ═══
  have hchain : (∫ z in Metric.ball (0 : Point n) δ,
        deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ * F s z 0)
      = (∫ w in Ω, (∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ w * qt₁ w)
        + (∫ w in Ω, gaussDdim τ w * qt₂ w) := by
    rw [hstepA]
    rw [commonWitness_cov_subball D δ hδD τ B]
    rw [← hΩdef]
    rw [setIntegral_congr_fun hΩmeas hcongr]
    rw [integral_add hInt1 hInt2]
  -- ═══ the two-term census bound. ═══
  have htwoterm := two_term_census_bound_uniform_combined τ r τ₀ hτpos hτT hr qt₁ qt₂
    Lq₁ M₁ M₂ hLq₁ hM₁ hM₂ hqt1meas hqt2meas hqt1bnd hqt2bnd hqt1cl Ω hΩmeas hlower
  -- ═══ assemble. ═══
  have hrp : τ ^ (-(1 : ℝ) / 2) = (Real.sqrt τ)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hτpos.le]
    norm_num
  rw [hτdef] at hchain ⊢
  rw [show a - s = τ from hτdef.symm] at hchain ⊢
  rw [hchain]
  calc |(∫ w in Ω, (∑ i, ((w i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ w * qt₁ w)
          + (∫ w in Ω, gaussDdim τ w * qt₂ w)|
      ≤ Cpair / Real.sqrt τ := htwoterm
    _ = Cpair * τ ^ (-(1 : ℝ) / 2) := by rw [hrp, div_eq_mul_inv]

/-- **Non-vacuity (TEETH) of the data-carry bundle of `hballrate_moduloG2`.**  The NEW carries this
    brick introduces on top of the standing geometry — the G2 gate `hS`, the s-uniform `F`-regularity
    `{hFb, hFl}`, and the numeric window `{hε, hτ₀, hh, hcap, hrF, hMF, hLF}` — are JOINTLY satisfiable
    at a GENUINELY non-`univ` gate (`S z := ball z 1`, so `{z | 0 ∈ S z} = ball 0 1 ≠ univ`, exercising
    G2 non-trivially — witnessed by the constant-`2` point `0 ∉ ball (2·) 1`) with `F ≡ 0`,
    `M_F = L_F = 0`, window `ε = 1/2, h = 0, τ₀ = 1`.  Confirms the brick is NOT vacuously conditioned.
    (The geometry carriers `{hC, hg, hg0, hu, h0Kmem}` are the standing tower carriers, inhabited by any
    Riemannian metric, unchanged here.)  NOT `a₁ = R/6`. -/
theorem hballrate_moduloG2_carries_satisfiable (hn : 0 < n) :
    ∃ (S : Point n → Set (Point n)) (F : ℝ → Point n → Point n → ℝ) (u ε h τ₀ rF M_F L_F : ℝ),
      0 < ε ∧ 0 < τ₀ ∧ 0 ≤ h ∧ ε + h ≤ τ₀ ∧ 0 < rF ∧ 0 ≤ M_F ∧ 0 ≤ L_F ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF →
        |F s z 0 - F s w 0| ≤ L_F * dist z w) ∧
      (∃ rS : ℝ, 0 < rS ∧ Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ S z}) ∧
      (∃ z : Point n, (0 : Point n) ∉ S z) := by
  classical
  refine ⟨fun z => Metric.ball z 1, fun _ _ _ => 0, 0, 1 / 2, 0, 1, 1, 0, 0,
    by norm_num, one_pos, le_refl _, by norm_num, one_pos, le_refl _, le_refl _, ?_, ?_, ?_, ?_⟩
  · intro s _ z _; simp
  · intro s _ z w _ _; simp
  · -- G2 for `S z := ball z 1`: `ball 0 1 ⊆ {z | 0 ∈ ball z 1}`.
    refine ⟨1, one_pos, fun z hz => ?_⟩
    rw [Set.mem_setOf_eq, Metric.mem_ball, dist_comm]
    exact Metric.mem_ball.mp hz
  · -- TEETH: the constant-`2` point has `0 ∉ ball (2·) 1`, so the gate is NOT `univ`.
    refine ⟨fun _ => (2 : ℝ), ?_⟩
    rw [Metric.mem_ball, dist_comm, not_lt]
    have hcoord : ‖(2 : ℝ)‖ ≤ ‖(fun _ => (2 : ℝ) : Point n)‖ :=
      norm_le_pi_norm (fun _ => (2 : ℝ)) ⟨0, hn⟩
    rw [dist_zero_right]
    have h2 : ‖(2 : ℝ)‖ = 2 := by rw [Real.norm_eq_abs]; norm_num
    rw [h2] at hcoord; linarith

end QIQTH.CensusHballrateModuloG2

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusHballrateModuloG2
#print axioms hballrate_moduloG2
#print axioms hballrate_moduloG2_carries_satisfiable
end AxiomChecks
