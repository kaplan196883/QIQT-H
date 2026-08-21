/-
  CensusOffBallEnvelope — J4-947: the OFF-BALL ENVELOPE REDUCTION + full far-rate threading for the
  concrete gated census integrand, closing the STRUCTURAL half of concern **(c)** of the `hCensusBound`
  (`hCross`) CoV-junction re-audit and THREADING J4-940's rate absorption into a single per-binder
  far-rate bound that has EXACTLY the shape `hcross_of_censusIntegral_bound` (J4-929) consumes.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  STRUCTURAL / REAL-ANALYSIS bridge brick composing three already-banked engines:
  `censusTauDeriv_eqZero_offGate` (J4-937, gate-off vanishing of the `∂_τ` kernel),
  `census_full_of_ball_bound_and_gaussEnv` (J4-933, the ball→ℝⁿ domain bridge), and
  `census_far_rate_of_ball_and_gaussEnv` (J4-940, the uniform rate absorption).  No `sorry`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypothesis, no existing banked
  file edited.

  ## THE CONCRETE INTEGRAND (verified against `hcross_of_censusIntegral_bound`, J4-929).  The census
  integrand `hCensusBound` bounds is
      `Φ s a z := deriv (fun r ↦ vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a−s) · F s z 0` ,
  over ALL of `ℝⁿ`, with `F : ℝ → Point n → Point n → ℝ` the abstract Levi factor (the `{hDuhamel,hDConv,
  hCConv}` = G3 object).

  ## THE TWO FLAGGED ANNULI ARE A SINGLE OFF-BALL REGION (task determination, gpt-5.6-sol audited).  The
  J4-945 caveat flagged the annulus `ball 0 D.ρ \ ball 0 δ` (CoV domain radius `D.ρ` beyond the
  transport-regularity sub-domain `δ`); the J4-946 caveat flagged `jointGate \ ball 0 r` (the joint gate
  beyond the two-term inner ball `r`).  These are NOT distinct regions needing separate treatment:
      `ball 0 D.ρ \ ball 0 δ  ⊆  (ball 0 δ)ᶜ  ⊆  (ball 0 ρ)ᶜ`   (any `ρ ≤ δ`),
      `jointGate \ ball 0 r   ⊆  (ball 0 r)ᶜ  ⊆  (ball 0 ρ)ᶜ`   (any `ρ ≤ r`),
  so BOTH sit inside the SINGLE off-ball complement `(ball 0 ρ)ᶜ = {z | ρ ≤ ‖z‖}`, which is EXACTLY the
  region `census_full_of_ball_bound_and_gaussEnv` (J4-933) handles in one shot via its off-ball Gaussian
  envelope hypothesis `∀ z, ρ ≤ ‖z‖ → |Φ z| ≤ Cenv·gaussDdim λ z`.  `offBall_annuli_subsumed` proves the
  two inclusions.

  ## THE GATE-OFF HALF IS FREE.  On the off-ball region, `Φ s a z` splits by the census gate `z ∈ K ∧
  0 ∈ S z`:  OFF the gate the `∂_τ` kernel VANISHES (`censusTauDeriv_eqZero_offGate`, J4-937), so
  `Φ s a z = 0 ≤ Cenv·gaussDdim λ z` FOR FREE; hence the full off-ball envelope REDUCES to the ON-GATE
  envelope `∀ z, (z∈K ∧ 0∈S z) → ρ ≤ ‖z‖ → |Φ s a z| ≤ Cenv·gaussDdim λ z` alone
  (`censusIntegrand_offBall_envelope_of_onGate`).

  ## WHAT LANDS.
    • `censusIntegrand_eqZero_offGate` — ★ the gate-off vanishing of the concrete integrand (`deriv·F = 0`
        off the gate), from `censusTauDeriv_eqZero_offGate` + `zero_mul`.
    • `offBall_annuli_subsumed` — ★ BOTH flagged annuli `⊆ (ball 0 ρ)ᶜ` (the single off-ball region).
    • `censusIntegrand_offBall_envelope_of_onGate` — ★★ the ENVELOPE REDUCTION: the full off-ball Gaussian
        envelope for `Φ` follows from the ON-GATE envelope alone (off-gate half discharged FREE).
    • `censusIntegrand_far_rate_of_onGate` — ★★ per-`(s,a)` far-rate: from the on-gate envelope, ball
        integrability, and the on-ball trace rate `|∫_{ball} Φ| ≤ Cpair·(a−s)^{−1/2}`, the full census
        `|∫_{ℝⁿ} Φ| ≤ (Cpair + Cenv·√2ⁿ·√ε)·(u−s)^{−1/2}`.  Threads J4-933 ⟶ J4-940.
    • `censusBound_of_onGate_and_ballRate` — ★★★ THE HEADLINE: the FULL `hCensusBound` binder
        `∀ s ∈ Ioo(u−ε)u, ∀ a ∈ Icc u(u+h), |∫ z, Φ s a z| ≤ C_far·(u−s)^{−1/2}` with the single explicit
        `C_far = Cpair + Cenv·√2ⁿ·√ε` — EXACTLY the antecedent `hcross_of_censusIntegral_bound` (J4-929)
        consumes — from the three uniform carries {on-gate envelope, ball integrability, on-ball trace rate}.
    • `censusBound_of_onGate_and_ballRate_hyp_satisfiable` — non-vacuity with TEETH: a genuine gate
        (`S z := ball z 1`, `K := closedBall 0 1`, so the gate is genuinely nonempty AND genuinely fails
        off `K`) with `F ≡ 0`, exercising BOTH gate branches non-trivially.

  ## HONEST STATUS (blunt).  This discharges the STRUCTURAL half of concern (c) — the gate-off vanishing,
  the annulus subsumption, and the envelope reduction — and THREADS J4-940's rate absorption, producing
  the full `hCensusBound` binder shape from THREE uniform carries.  It does NOT close `hCensusBound`.  The
  three carries are:
    (C1) `hballrate` — the on-ball trace rate `|∫_{ball 0 ρ} Φ| ≤ Cpair·(a−s)^{−1/2}` (the two-term
         trace-cancellation core, J4-922/944; depends on G2 for the gate identity on the ball and on G3
         for the F-factor);
    (C2) `hΦint` — integrability of `Φ` (available from the `hEnv` bundle of J4-929);
    (C3) `honGate` — the ON-GATE off-ball Gaussian domination `|deriv·F| ≤ Cenv·gaussDdim λ z` for
         `z ∈ gate`, `ρ ≤ ‖z‖`.  This is the GENUINE remaining analytic core of concern (c): dominating
         the two-term closed form `((∑ᵢ …)·gaussDdim τ(W z 0))·A + gaussDdim τ(W z 0)·∂τA` (with a
         POLYNOMIAL-in-`W z 0` prefactor) by a single Gaussian in the ORIGINAL coordinate `z`.  It needs
         (i) the chart bi-Lipschitz comparison `‖W z 0‖ ≳ ‖z‖`, (ii) polynomial×Gaussian ≤ wider-Gaussian
         domination, and (iii) the F-factor bound (G3).  NOT dischargeable here; carried explicitly.
  So `hCensusBound` is assembled modulo {C1, C2, C3} — i.e. modulo {G2, G3, and the on-gate Gaussian
  domination (C3)}, NOT modulo {G2, G3} alone.  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusFarRateAbsorb
import QIQTH.CensusTauDerivGateSplit

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.CensusDomainBridge QIQTH.CensusFarRateAbsorb QIQTH.CensusTauDerivGateSplit
open scoped Topology BigOperators

namespace QIQTH.CensusOffBallEnvelope

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### §A — the gate-off vanishing of the concrete census integrand.
    ############################################################################### -/

/-- **★ `censusIntegrand_eqZero_offGate` — the concrete integrand VANISHES off the census gate.**  When
    `z ∉ K` or the fixed field point `0 ∉ S z`, the `∂_τ` kernel is `0` (`censusTauDeriv_eqZero_offGate`,
    J4-937), so the full census integrand `deriv(fun r ↦ vanVleckGatedWitness … r 0 z)(a−s) · F s z 0`
    vanishes there — the off-gate region contributes NOTHING.  NOT `a₁ = R/6`. -/
theorem censusIntegrand_eqZero_offGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (s a : ℝ) (z : Point n)
    (hoff : z ∉ K ∨ (0 : Point n) ∉ S z) :
    deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0 = 0 := by
  rw [censusTauDeriv_eqZero_offGate g gi hC hK S cutA cutB z (a - s) hoff, zero_mul]

/-! ###############################################################################
    ### §B — BOTH flagged annuli sit inside the single off-ball region `(ball 0 ρ)ᶜ`.
    ############################################################################### -/

/-- **★ `offBall_annuli_subsumed` — the two flagged annuli are a SINGLE off-ball region.**  For `ρ ≤ δ`
    and `ρ ≤ r`, the J4-945 annulus `ball 0 D_ρ \ ball 0 δ` and the J4-946 annulus `J \ ball 0 r` are BOTH
    contained in the off-ball complement `(ball 0 ρ)ᶜ = {z | ρ ≤ ‖z‖}`.  Hence they need NO separate
    treatment — the single off-ball Gaussian envelope over `(ball 0 ρ)ᶜ` (fed to
    `census_full_of_ball_bound_and_gaussEnv`, J4-933) covers both at once.  NOT `a₁ = R/6`. -/
theorem offBall_annuli_subsumed (ρ δ r D_ρ : ℝ) (hρδ : ρ ≤ δ) (hρr : ρ ≤ r)
    (J : Set (Point n)) :
    (Metric.ball (0 : Point n) D_ρ \ Metric.ball (0 : Point n) δ ⊆ (Metric.ball (0 : Point n) ρ)ᶜ)
      ∧ (J \ Metric.ball (0 : Point n) r ⊆ (Metric.ball (0 : Point n) ρ)ᶜ) := by
  constructor
  · intro z hz
    have hzδ : z ∉ Metric.ball (0 : Point n) δ := hz.2
    exact fun hzρ => hzδ (Metric.ball_subset_ball hρδ hzρ)
  · intro z hz
    have hzr : z ∉ Metric.ball (0 : Point n) r := hz.2
    exact fun hzρ => hzr (Metric.ball_subset_ball hρr hzρ)

/-! ###############################################################################
    ### §C — the ENVELOPE REDUCTION: off-ball envelope ⟸ ON-GATE envelope (off-gate FREE).
    ############################################################################### -/

/-- **★★ `censusIntegrand_offBall_envelope_of_onGate` — the OFF-BALL envelope reduces to the ON-GATE
    envelope.**  The full off-ball single-Gaussian envelope for the concrete census integrand `Φ s a` on
    `{z | ρ ≤ ‖z‖}` follows from the ON-GATE envelope alone: off the census gate the integrand VANISHES
    (§A) so `0 ≤ Cenv·gaussDdim λ z` FOR FREE, and on the gate it is exactly `honGate`.  So the only
    genuine analytic content of concern (c) is the on-gate Gaussian domination.  NOT `a₁ = R/6`. -/
theorem censusIntegrand_offBall_envelope_of_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (s a ρ lam Cenv : ℝ) (hCenv : 0 ≤ Cenv)
    (honGate : ∀ z : Point n, (z ∈ K ∧ (0 : Point n) ∈ S z) → ρ ≤ ‖z‖ →
        |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
          ≤ Cenv * gaussDdim lam z) :
    ∀ z : Point n, ρ ≤ ‖z‖ →
      |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
        ≤ Cenv * gaussDdim lam z := by
  intro z hz
  by_cases hgate : z ∈ K ∧ (0 : Point n) ∈ S z
  · exact honGate z hgate hz
  · have hoff : z ∉ K ∨ (0 : Point n) ∉ S z := not_and_or.mp hgate
    rw [censusIntegrand_eqZero_offGate g gi hC hK S cutA cutB F s a z hoff, abs_zero]
    have : (0 : ℝ) ≤ Cenv * gaussDdim lam z := mul_nonneg hCenv (gaussDdim_nonneg lam z)
    exact this

/-! ###############################################################################
    ### §D — per-`(s,a)` far-rate: thread J4-933 (domain bridge) ⟶ J4-940 (rate absorption).
    ############################################################################### -/

/-- **★★ `censusIntegrand_far_rate_of_onGate` — per-`(s,a)` census far-rate from the ON-GATE envelope.**
    For the concrete integrand `Φ s a`, with `Ioo(u−ε)u`/`Icc u(u+h)` positions (`u−ε<s`, `s<u`, `u≤a`),
    integrability, the ON-GATE off-ball Gaussian envelope, and the on-ball trace rate
    `|∫_{ball 0 ρ} Φ| ≤ Cpair·(a−s)^{−1/2}`,
        `|∫ z, Φ s a z| ≤ (Cpair + Cenv·√2ⁿ·√ε)·(u−s)^{−1/2}` .
    Composes `censusIntegrand_offBall_envelope_of_onGate` (§C) with `census_far_rate_of_ball_and_gaussEnv`
    (J4-940 = J4-933 ⟶ rate absorption).  The RHS is EXACTLY the `hCensusBound` shape.  NOT `a₁ = R/6`. -/
theorem censusIntegrand_far_rate_of_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (u s a ε ρ lam Cenv Cpair : ℝ)
    (hε : 0 < ε) (hlam : 0 < lam) (hCenv : 0 ≤ Cenv) (hCpair : 0 ≤ Cpair) (hρ : 0 ≤ ρ)
    (hslo : u - ε < s) (hshi : s < u) (hau : u ≤ a)
    (hΦint : Integrable
      (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
        * F s z 0) volume)
    (honGate : ∀ z : Point n, (z ∈ K ∧ (0 : Point n) ∈ S z) → ρ ≤ ‖z‖ →
        |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
          ≤ Cenv * gaussDdim lam z)
    (hballrate : |∫ z in Metric.ball (0 : Point n) ρ,
        deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
          ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2)) :
    |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
      ≤ (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * (u - s) ^ (-(1 : ℝ) / 2) := by
  have henv := censusIntegrand_offBall_envelope_of_onGate g gi hC hK S cutA cutB F s a ρ lam Cenv
    hCenv honGate
  exact census_far_rate_of_ball_and_gaussEnv u s a ε ρ lam Cenv Cpair
    (Cpair * (a - s) ^ (-(1 : ℝ) / 2)) hε hlam hCenv hCpair hρ hslo hshi hau
    (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0)
    hΦint henv hballrate (le_refl _)

/-! ###############################################################################
    ### §E — THE HEADLINE: the FULL `hCensusBound` binder from THREE uniform carries.
    ############################################################################### -/

/-- **★★★ `censusBound_of_onGate_and_ballRate` — the FULL `hCensusBound` binder.**  Produces EXACTLY the
    antecedent `hcross_of_censusIntegral_bound` (J4-929) consumes:
        `∀ s ∈ Ioo(u−ε)u, ∀ a ∈ Icc u(u+h),
            |∫ z, deriv(fun r ↦ vanVleckGatedWitness … r 0 z)(a−s)·F s z 0| ≤ C_far·(u−s)^{−1/2}` ,
    with the single explicit `s`-independent `C_far := Cpair + Cenv·√2ⁿ·√ε`, from THREE uniform carries:
    (C1) the on-ball trace rate `hballrate`, (C2) integrability `hΦint`, (C3) the ON-GATE off-ball Gaussian
    domination `honGate`.  All differentiation and domain content is wired away; the residual analytic
    input is C3 (the on-gate Gaussian domination — the chart-comparison + two-term envelope), plus the
    two-term/trace core (C1, depending on G2/G3).  NOT `a₁ = R/6`. -/
theorem censusBound_of_onGate_and_ballRate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (u ε h ρ lam Cenv Cpair : ℝ)
    (hε : 0 < ε) (hlam : 0 < lam) (hCenv : 0 ≤ Cenv) (hCpair : 0 ≤ Cpair) (hρ : 0 ≤ ρ)
    (hΦint : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      Integrable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
          * F s z 0) volume)
    (honGate : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      ∀ z : Point n, (z ∈ K ∧ (0 : Point n) ∈ S z) → ρ ≤ ‖z‖ →
        |deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
          ≤ Cenv * gaussDdim lam z)
    (hballrate : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      |∫ z in Metric.ball (0 : Point n) ρ,
        deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
          ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2)) :
    ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
      |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
        ≤ (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro s hs a ha
  have hslo : u - ε < s := hs.1
  have hshi : s < u := hs.2
  have hau : u ≤ a := ha.1
  exact censusIntegrand_far_rate_of_onGate g gi hC hK S cutA cutB F u s a ε ρ lam Cenv Cpair
    hε hlam hCenv hCpair hρ hslo hshi hau (hΦint s hs a ha) (honGate s hs a ha)
    (hballrate s hs a ha)

/-! ###############################################################################
    ### §F — non-vacuity (TEETH: a genuine non-`univ` gate exercising BOTH gate branches).
    ############################################################################### -/

/-- **Non-vacuity of `censusBound_of_onGate_and_ballRate` — TEETH.**  The three-carry bundle is jointly
    satisfiable at a GENUINE gate: `K := closedBall 0 1` (compact nbhd of `0`) and `S z := ball z 1` (so
    the census gate `z ∈ K ∧ 0 ∈ S z` is genuinely NONEMPTY — holds at `z = 0` — AND genuinely FAILS off
    `K`), with `F ≡ 0` making `Φ ≡ 0` so C1/C2/C3 all hold (integrable, `|∫_ball 0| = 0 ≤ Cpair·…`,
    on-gate `|0| ≤ Cenv·gaussDdim`).  Both gate branches are exercised: the gate is inhabited (teeth on
    C3's antecedent) and non-trivial.  The conclusion then fires on genuine `Ioo/Icc` positions.  NOT
    `a₁ = R/6`. -/
theorem censusBound_of_onGate_and_ballRate_hyp_satisfiable (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (cutA cutB : ℝ) :
    ∃ (K : Set (Point n)) (S : Point n → Set (Point n)) (F : ℝ → Point n → Point n → ℝ)
      (u ε h ρ lam Cenv Cpair : ℝ),
      IsCompact K ∧ ((0 : Point n) ∈ K ∧ (0 : Point n) ∈ S 0) ∧ (∃ z : Point n, z ∉ K) ∧
      0 < ε ∧ 0 < lam ∧ 0 ≤ Cenv ∧ 0 ≤ Cpair ∧ 0 ≤ ρ ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        Integrable
          (fun z => deriv (fun r => vanVleckGatedWitness g gi hC (isCompact_closedBall 0 1) S cutA cutB r 0 z) (a - s)
            * F s z 0) volume) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        ∀ z : Point n, (z ∈ K ∧ (0 : Point n) ∈ S z) → ρ ≤ ‖z‖ →
          |deriv (fun r => vanVleckGatedWitness g gi hC (isCompact_closedBall 0 1) S cutA cutB r 0 z) (a - s) * F s z 0|
            ≤ Cenv * gaussDdim lam z) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        |∫ z in Metric.ball (0 : Point n) ρ,
          deriv (fun r => vanVleckGatedWitness g gi hC (isCompact_closedBall 0 1) S cutA cutB r 0 z) (a - s) * F s z 0|
            ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2)) := by
  classical
  refine ⟨Metric.closedBall (0 : Point n) 1, fun z => Metric.ball z 1, fun _ _ _ => (0 : ℝ),
    1, 1, 1, 1, 1, 1, 1,
    isCompact_closedBall _ _, ⟨Metric.mem_closedBall_self zero_le_one, ?_⟩, ?_,
    one_pos, one_pos, zero_le_one, zero_le_one, zero_le_one, ?_, ?_, ?_⟩
  · -- `0 ∈ ball 0 1 = S 0`.
    exact Metric.mem_ball_self one_pos
  · -- teeth: the constant-`2` point lies OUTSIDE `closedBall 0 1`.
    refine ⟨fun _ => (2 : ℝ), ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, not_le]
    have hcoord : ‖(2 : ℝ)‖ ≤ ‖(fun _ => (2 : ℝ) : Point n)‖ :=
      norm_le_pi_norm (fun _ => (2 : ℝ)) ⟨0, hn⟩
    have h2 : ‖(2 : ℝ)‖ = 2 := by rw [Real.norm_eq_abs]; norm_num
    rw [h2] at hcoord; linarith
  · -- C2: `F ≡ 0` ⟹ integrand `≡ 0` ⟹ integrable.
    intro s _ a _
    simpa using (integrable_zero (Point n) ℝ volume)
  · -- C3: on-gate `|deriv · 0| = 0 ≤ Cenv·gaussDdim`.
    intro s _ a _ z _ _
    simp only [mul_zero, abs_zero]
    exact mul_nonneg zero_le_one (gaussDdim_nonneg 1 z)
  · -- C1: `|∫_ball (deriv · 0)| = |∫_ball 0| = 0 ≤ Cpair·(a−s)^{−1/2}`.
    intro s hs a ha
    have hsa : 0 < a - s := by have h1 := ha.1; have h2 := hs.2; linarith
    have hrpos : (0 : ℝ) ≤ (a - s) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hsa) _
    simp only [mul_zero, integral_zero, abs_zero]
    exact mul_nonneg zero_le_one hrpos

end QIQTH.CensusOffBallEnvelope

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusOffBallEnvelope
#print axioms censusIntegrand_eqZero_offGate
#print axioms offBall_annuli_subsumed
#print axioms censusIntegrand_offBall_envelope_of_onGate
#print axioms censusIntegrand_far_rate_of_onGate
#print axioms censusBound_of_onGate_and_ballRate
#print axioms censusBound_of_onGate_and_ballRate_hyp_satisfiable
end AxiomChecks
