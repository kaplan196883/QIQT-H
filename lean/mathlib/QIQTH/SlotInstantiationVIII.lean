/-
  SlotInstantiationVIII — J4-425 (Part B, tranche (a) phase 8): the S5b GLOBAL Gaussian-difference
  dominator that CLOSES the R1 `hdom_comp` carry OFF the collar.  Continues `SlotInstantiationI..VII`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  ⚠  a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.

  WHY PHASE 8 EXISTS.  Phase 7 recorded the EXACT off-collar failure of the pointwise ρ-route: at fixed
  `‖z‖ = r₀`, `τ → 0` makes `e^{|θ|}` diverge, so `|ρ − 1| ≤ Cρ‖z‖³/τ` (the on-collar R1 heart) does NOT
  extend to `collarᶜ`.  The phase-7 author's binding spec was the **S5b route**: use the ALGEBRAIC
  identity (no exp linearisation)
      `hessGaussFactor·(ρ − 1)·qc = (z_i² − 2τ)/(4τ²)·(G^chart − G_τ)·qc`,
  where `(ρ − 1)·G_τ = G^chart − G_τ` is EXACT (`gauss_ratio_rho`, `G^chart = gaussDdim τ (W z 0)`), and
  the banked S5b bound `gaussDdim_replace_bound`
      `|G^chart − G_τ| ≤ (L'‖z‖³/(4τ))·(√2)ⁿ·G_{2τ}`   GLOBALLY (no exponential blow-up),
  valid for ALL `z` under the near-isometry cubic error `|r²_{Wz} − r²_z| ≤ L'‖z‖³` and the coercivity
  `½·r²_z ≤ r²_{Wz}`.  This yields a width-`2τ` dominator whose moment is again `C/√τ`.

  POWER COUNT (written BEFORE the proof, per spec).  Pointwise (ALL of `collarᶜ`, indeed all `z`), with
  `|z_i² − 2τ| ≤ ‖z‖² + 2τ` and `|qc| ≤ Mqc`:
      ‖H·(ρ−1)·qc‖ = |(z_i²−2τ)/(4τ²)|·|G^chart − G_τ|·|qc|
                   ≤ (‖z‖²+2τ)/(4τ²)·(L'‖z‖³/(4τ)·(√2)ⁿ·G_{2τ})·Mqc
                   = (L'(√2)ⁿMqc/(16τ³))·(‖z‖⁵ + 2τ‖z‖³)·G_{2τ}  =: comparisonDom2.
  Moments of `G_{2τ}` scale as `(2τ)^{k/2}`, so with the width-`2τ` quintic/cubic moments
  (`∫‖z‖⁵G_{2τ} ≤ n·1600√2·(√2)⁵(√τ)⁵`, `∫‖z‖³G_{2τ} ≤ n·(64√2+1)·(√2)³(√τ)³`, i.e. κ = 2 in
  `pow_norm_mul_gauss_integral`):
      ∫comparisonDom2 = (L'(√2)ⁿMqc/(16τ³))·[∫‖z‖⁵G_{2τ} + 2τ·∫‖z‖³G_{2τ}]
                      ≤ (L'(√2)ⁿMqc·n/16)·[1600√2(√2)⁵ + 2(64√2+1)(√2)³]·τ^{5/2−3}
                      = Bcomp2 / √τ,   Bcomp2 = L'(√2)ⁿMqc·n·(1600√2(√2)⁵ + 2(64√2+1)(√2)³)/16.
  The `τ^{5/2}` cubic moment ÷ the `1/τ³` Hessian/ρ prefactor produces EXACTLY `τ^{−1/2} = 1/√τ` — the
  SAME EXACT scaling as the phase-6 `comparisonDom`; the numeric constant merely picks up the factors
  `(√2)⁵ = 4√2` and `(√2)³ = 2√2`, giving the simplified value
  `Bcomp2 = L'·(√2)ⁿ·Mqc·n·(3328 + √2)/4` per `√τ`.

  ⚠ n-DEPENDENCE NOTE (honest).  Unlike the phase-6 `Bcomp` (which carried `n` only linearly), `Bcomp2`
  carries the EXTRA factor `(√2)ⁿ` inherited from `gaussDdim_replace_bound`'s coercivity step
  (`G_τ(w) ≤ (√2)ⁿ·G_{2τ}` on `½r²_base ≤ r²_w`).  This is legitimate: `n` is FIXED for the witness, so
  `hcomp_collapsed`'s demanded shape `‖∫…‖ ≤ Bcomp/√τ` accepts any `n`-dependent constant `Bcomp2`.  The
  `(√2)ⁿ` lands entirely in the CONSTANT; the τ-scaling `1/√τ` is untouched.

  THE WIN.  With S5b the a.e. `hdom_comp` domination is DISCHARGED GLOBALLY on `collarᶜ` (in fact on all
  of `ℝⁿ`) from the near-isometry inputs `herr`/`hmin` + the amplitude sup `Mqc` — it is NO LONGER a
  standing carry (contrast phase 6/7, where `hdom_comp` was an assumed a.e. bound).  What remains of
  group (1) reduces to the ENUMERATED INPUT CARRIES (see PHASE 8 COVERAGE).

  NO `sorry`, no `:= True`, no new axioms; std-3.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import QIQTH.SlotInstantiationVII

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched
open QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII QIQTH.SlotInstantiationIII
open QIQTH.SlotInstantiationIV QIQTH.SlotInstantiationV QIQTH.SlotInstantiationVI
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.SlotInstantiationVIII

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the two banked n-D Gaussian moments specialised to WIDTH `2τ` (κ = 2).
    ############################################################################### -/

/-- **★ `normPow5_gauss_bound_twoTau`.**  The width-`2τ` quintic Gaussian moment
      `∫_z ‖z‖⁵·G_{2τ}(z) ≤ n·(1600√2)·(√2)⁵·(√τ)⁵`,
    from `pow_norm_mul_gauss_integral` at `k = 5, κ = 2, t = τ` fed the 1-D `oneD_absMoment5`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem normPow5_gauss_bound_twoTau (τ : ℝ) (hτ : 0 < τ) :
    (∫ z : Point n, ‖z‖ ^ 5 * gaussDdim (2 * τ) z)
      ≤ (n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * (Real.sqrt τ) ^ 5 := by
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  exact pow_norm_mul_gauss_integral (n := n) 5 (by norm_num) 2 (by norm_num) τ hτ
    (1600 * Real.sqrt 2) (by positivity) (oneD_absMoment5 (2 * τ) h2τ)

/-- **★ `normPow3_gauss_bound_twoTau`.**  The width-`2τ` cubic Gaussian moment
      `∫_z ‖z‖³·G_{2τ}(z) ≤ n·(64√2+1)·(√2)³·(√τ)³`,
    from `pow_norm_mul_gauss_integral` at `k = 3, κ = 2, t = τ` fed the 1-D `oneD_absMoment3`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem normPow3_gauss_bound_twoTau (τ : ℝ) (hτ : 0 < τ) :
    (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z)
      ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3 := by
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  exact pow_norm_mul_gauss_integral (n := n) 3 (by norm_num) 2 (by norm_num) τ hτ
    (64 * Real.sqrt 2 + 1) (by positivity) (oneD_absMoment3 (2 * τ) h2τ)

/-! ###############################################################################
    ### §2 — the S5b width-`2τ` dominator, its nonnegativity, integrability, and `C/√τ` moment.
    ############################################################################### -/

/-- **★ `comparisonDom2`.**  THE S5b GLOBAL (off-collar, in fact whole-space) dominator of the `hcomp`
    comparison integrand `H·(ρ−1)·qc`, from the algebraic identity + `gaussDdim_replace_bound`:
      `comparisonDom2 τ L' Mqc z := (L'·(√2)ⁿ·Mqc/(16τ³))·((‖z‖⁵ + 2τ‖z‖³)·G_{2τ}(z))`.
    Here `L'` is the ℓ² near-isometry cubic-error constant and `Mqc` the amplitude sup (`|qc| ≤ Mqc`).
    ⚠ NOT `a₁ = R/6`. -/
noncomputable def comparisonDom2 (τ L' Mqc : ℝ) (z : Point n) : ℝ :=
  L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3)
    * ((‖z‖ ^ 5 + 2 * τ * ‖z‖ ^ 3) * gaussDdim (2 * τ) z)

/-- **`comparisonDom2_nonneg`.**  The width-`2τ` dominator is nonnegative.  ⚠ NOT `a₁ = R/6`. -/
theorem comparisonDom2_nonneg (τ L' Mqc : ℝ) (hτ : 0 < τ) (hL' : 0 ≤ L') (hMqc : 0 ≤ Mqc)
    (z : Point n) : 0 ≤ comparisonDom2 τ L' Mqc z := by
  unfold comparisonDom2
  have hG : (0 : ℝ) ≤ gaussDdim (2 * τ) z := QIQTH.ResidueBound.gaussDdim_nonneg (2 * τ) z
  have hfac : (0 : ℝ) ≤ ‖z‖ ^ 5 + 2 * τ * ‖z‖ ^ 3 := by positivity
  have hcoef : (0 : ℝ) ≤ L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) := by positivity
  exact mul_nonneg hcoef (mul_nonneg hfac hG)

/-- **`comparisonDom2_integrable`.**  The width-`2τ` dominator is integrable (split into the quintic and
    cubic `‖z‖^k·G_{2τ}` pieces via `normPow_gauss_integrable`).  ⚠ NOT `a₁ = R/6`. -/
theorem comparisonDom2_integrable (τ L' Mqc : ℝ) (hτ : 0 < τ) :
    Integrable (comparisonDom2 (n := n) τ L' Mqc) volume := by
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  have hI1 : Integrable (fun z : Point n =>
      L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)) volume :=
    (normPow_gauss_integrable 5 (by norm_num) (2 * τ) h2τ).const_mul _
  have hI2 : Integrable (fun z : Point n =>
      L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) * (2 * τ) * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))
      volume :=
    (normPow_gauss_integrable 3 (by norm_num) (2 * τ) h2τ).const_mul _
  refine (hI1.add hI2).congr (ae_of_all _ (fun z => ?_))
  simp only [Pi.add_apply]; unfold comparisonDom2; ring

/-- **★★ `comparisonDom2_moment` — THE S5b MOMENT DISCHARGE.**  The full-space integral of the width-`2τ`
    dominator obeys the matched sliver bound
      `∫_z comparisonDom2 τ L' Mqc z ≤ Bcomp2/√τ`,
    `Bcomp2 = L'·(√2)ⁿ·Mqc·n·(1600√2(√2)⁵ + 2(64√2+1)(√2)³)/16`  (= `L'(√2)ⁿMqc·n·(3328+√2)/4`).
    The `τ^{5/2}` cubic moment ÷ the `1/τ³` prefactor yields EXACTLY `τ^{−1/2}` — the same scaling as
    `comparisonDom_moment`; the constant picks up `(√2)⁵, (√2)³` and the `(√2)ⁿ` carry.  ⚠ NOT
    `a₁ = R/6`. -/
theorem comparisonDom2_moment (τ L' Mqc : ℝ) (hτ : 0 < τ) (hL' : 0 ≤ L') (hMqc : 0 ≤ Mqc) :
    (∫ z : Point n, comparisonDom2 τ L' Mqc z)
      ≤ L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
          * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5 + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
          / 16 / Real.sqrt τ := by
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  have hc : (0 : ℝ) ≤ L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) := by positivity
  have hc2τ : (0 : ℝ) ≤ L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) * (2 * τ) := by positivity
  have hI1 : Integrable (fun z : Point n =>
      L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)) volume :=
    (normPow_gauss_integrable 5 (by norm_num) (2 * τ) h2τ).const_mul _
  have hI2 : Integrable (fun z : Point n =>
      L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) * (2 * τ) * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))
      volume :=
    (normPow_gauss_integrable 3 (by norm_num) (2 * τ) h2τ).const_mul _
  have hsplit : (fun z : Point n => comparisonDom2 τ L' Mqc z)
      = (fun z => L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) * (2 * τ)
              * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)) := by
    funext z; unfold comparisonDom2; ring
  rw [hsplit, integral_add hI1 hI2, integral_const_mul, integral_const_mul]
  calc L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) * (∫ z : Point n, ‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) * (2 * τ)
              * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z)
      ≤ L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3)
            * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * (Real.sqrt τ) ^ 5)
          + L' * (Real.sqrt 2) ^ n * Mqc / (16 * τ ^ 3) * (2 * τ)
              * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3) :=
        add_le_add (mul_le_mul_of_nonneg_left (normPow5_gauss_bound_twoTau τ hτ) hc)
          (mul_le_mul_of_nonneg_left (normPow3_gauss_bound_twoTau τ hτ) hc2τ)
    _ = L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
          * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5 + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
          / 16 / Real.sqrt τ := by
        have hs : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
        set s := Real.sqrt τ with hsdef
        have hτs : τ = s ^ 2 := by rw [hsdef]; exact (Real.sq_sqrt hτ.le).symm
        set A := (Real.sqrt 2) ^ n with hA
        rw [hτs]; field_simp

/-! ###############################################################################
    ### §3 — the S5b GLOBAL pointwise domination (`hdom_comp2`), via the algebraic identity.
    ############################################################################### -/

/-- **★★★ S5b — `hdom_comp2_ptwise`.**  THE GLOBAL POINTWISE DOMINATION, honest at EVERY `z` (no
    collar/exp budget).  Under the near-isometry cubic error `herr` (`|r²_{Wz} − r²_z| ≤ L'‖z‖³`), the
    coercivity `hmin` (`½r²_z ≤ r²_{Wz}`) — the two S5b inputs of `gaussDdim_replace_bound` — and the
    amplitude sup `hqcbdd` (`|qc| ≤ Mqc`),
      `‖hessGaussFactor·(ρ−1)·qc‖ ≤ comparisonDom2 τ L' Mqc z`   for ALL `z`.
    Route: `hessGaussFactor·(ρ−1) = (z_i²−2τ)/(4τ²)·(G^chart − G_τ)` (`gauss_ratio_rho`, EXACT), then
    `|(z_i²−2τ)/(4τ²)| ≤ (‖z‖²+2τ)/(4τ²)` (`|z i| ≤ ‖z‖`), the banked `gaussDdim_replace_bound` for
    `|G^chart − G_τ|`, and `|qc| ≤ Mqc`.  NO exponential linearisation ⟹ NO off-collar blow-up.  ⚠ NOT
    `a₁ = R/6`. -/
theorem hdom_comp2_ptwise (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (τ s : ℝ) (hτ : 0 < τ) (L' Mqc : ℝ)
    (hL' : 0 ≤ L') (hMqc : 0 ≤ Mqc)
    (herr : ∀ z, |rncRadialSq (uniformInverseChart g gi hC hK z 0) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
    (hmin : ∀ z, (1 / 2 : ℝ) * rncRadialSq z
      ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc) (z : Point n) :
    ‖hessGaussFactor i τ z
        * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
      ≤ comparisonDom2 τ L' Mqc z := by
  have h4τ2 : (0 : ℝ) < 4 * τ ^ 2 := by positivity
  have hgpos : (0 : ℝ) ≤ gaussDdim (2 * τ) z := QIQTH.ResidueBound.gaussDdim_nonneg (2 * τ) z
  -- EXACT ratio identity: `(ρ − 1)·G_τ = G^chart − G_τ`.
  have hratio : (rhoRatio g gi hC hK τ z - 1) * gaussDdim τ z
      = gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z := by
    have hg := gauss_ratio_rho g gi hC hK τ hτ z
    rw [hg]; ring
  -- the algebraic S5b identity.
  have hid : hessGaussFactor i τ z
        * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2)
          * (gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z)
          * (chartAmp g gi hC hK a b τ z 0 * F s z 0) := by
    unfold hessGaussFactor; rw [← hratio]; ring
  -- coordinate vs norm.
  have hcoord : |z i| ≤ ‖z‖ := by
    have h := norm_le_pi_norm z i; rwa [Real.norm_eq_abs] at h
  have hzi2 : z i ^ 2 ≤ ‖z‖ ^ 2 := by
    have h2 : |z i| ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hcoord 2
    rwa [sq_abs] at h2
  -- bound on the Hessian coefficient.
  have hnum : |z i ^ 2 - 2 * τ| ≤ ‖z‖ ^ 2 + 2 * τ := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · nlinarith [sq_nonneg (z i), pow_nonneg (norm_nonneg z) 2, hτ]
    · nlinarith [hzi2, hτ]
  have hbA : |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := by
    rw [abs_div, abs_of_pos h4τ2]
    gcongr
  -- the S5b kernel-replacement bound at `W z = uniformInverseChart g gi hC hK z 0`.
  have hbB : |gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z|
      ≤ L' * ‖z‖ ^ 3 / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
    gaussDdim_replace_bound τ hτ (fun w => uniformInverseChart g gi hC hK w 0) z L' hL'
      (herr z) (hmin z)
  -- nonnegativity of the two dominating factors.
  have hboundA_nn : (0 : ℝ) ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := by positivity
  have hboundB_nn : (0 : ℝ) ≤ L' * ‖z‖ ^ 3 / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by
    positivity
  -- assemble.
  rw [hid, Real.norm_eq_abs, abs_mul, abs_mul]
  calc |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)|
          * |gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z|
          * |chartAmp g gi hC hK a b τ z 0 * F s z 0|
      ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2)
            * (L' * ‖z‖ ^ 3 / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z) * Mqc :=
        mul_le_mul (mul_le_mul hbA hbB (abs_nonneg _) hboundA_nn) (hqcbdd z)
          (abs_nonneg _) (mul_nonneg hboundA_nn hboundB_nn)
    _ = comparisonDom2 τ L' Mqc z := by unfold comparisonDom2; ring

/-! ###############################################################################
    ### §4 — `hcomp_final2`: the comparison leg CLOSED off-collar, `hdom_comp` DISCHARGED.
    ############################################################################### -/

/-- **★★★ `hcomp_final2` — THE COMPARISON LEG, `hdom_comp` DISCHARGED via S5b.**  Instantiating
    `SlotInstantiationV.hcomp_collapsed` at `D := comparisonDom2` and `Bcomp := Bcomp2`, ALL of
    `hDint`/`hmom`/`hdom` are discharged HERE: `comparisonDom2_integrable`, `comparisonDom2_moment`
    (`+ setIntegral_le_integral`, `D ≥ 0`), and the GLOBAL a.e. domination from `hdom_comp2_ptwise`
    (`ae_of_all`).  The `hdom_comp` carry of phase 6/7 is GONE — replaced by the near-isometry inputs
    `herr`/`hmin` + the amplitude sup `Mqc`.  The remaining carries are exactly `hcompDiff_int` (R3,
    wiring), `hform` (R2, jet supply), and the enumerated input carries `herr`/`hmin`/`Mqc`.  Result:
      `‖∫_{collarᶜ} (IchartResidual − hessGaussFactor·qc)‖ ≤ Bcomp2/√τ`.
    ⚠ NOT `a₁ = R/6`. -/
theorem hcomp_final2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (L' Mqc : ℝ) (hL' : 0 ≤ L') (hMqc : 0 ≤ Mqc)
    (hcompDiff_int : IntegrableOn
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      (collar (c * Real.sqrt τ))ᶜ volume)
    (hform : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
      IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
        = hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
    (herr : ∀ z, |rncRadialSq (uniformInverseChart g gi hC hK z 0) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
    (hmin : ∀ z, (1 / 2 : ℝ) * rncRadialSq z
      ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc) :
    ‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
      ≤ L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
          * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5 + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
          / 16 / Real.sqrt τ :=
  hcomp_collapsed g gi hC hK S a b F i T τ₀ r₀ c data τ s
    (comparisonDom2 τ L' Mqc)
    (L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
      * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5 + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
      / 16)
    hcompDiff_int
    ((comparisonDom2_integrable τ L' Mqc hτ).integrableOn)
    hform
    (ae_of_all _ (fun z => hdom_comp2_ptwise g gi hC hK a b F i τ s hτ L' Mqc hL' hMqc
      herr hmin hqcbdd z))
    (by
      calc ∫ z in (collar (c * Real.sqrt τ))ᶜ, comparisonDom2 τ L' Mqc z
          ≤ ∫ z : Point n, comparisonDom2 τ L' Mqc z :=
            setIntegral_le_integral (comparisonDom2_integrable τ L' Mqc hτ)
              (ae_of_all _ (fun z => comparisonDom2_nonneg τ L' Mqc hτ hL' hMqc z))
        _ ≤ _ := comparisonDom2_moment τ L' Mqc hτ hL' hMqc)

/-! ###############################################################################
    ### PACKAGE — the phase-8 conjunction.
    ############################################################################### -/

/-- **★★★ `slotInstantiation_phase8`.**  THE PHASE-8 PACKAGE: the prior group-(1) carries (held as
    `Pphase7`) CONJOINED with `hcomp_final2` — the comparison leg with the `hdom_comp` domination now
    DISCHARGED GLOBALLY off-collar via S5b (`≤ Bcomp2/√τ`), MODULO the enumerated input carries
    `hcompDiff_int` (R3), `hform` (R2), and `herr`/`hmin`/`Mqc` (the near-isometry + amplitude-sup
    inputs).  With this, group (1) reduces to ENUMERATED INPUT CARRIES ONLY (see PHASE 8 COVERAGE).
    ⚠ NOT `a₁ = R/6`. -/
theorem slotInstantiation_phase8 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (L' Mqc : ℝ) (hL' : 0 ≤ L') (hMqc : 0 ≤ Mqc)
    (Pphase7 : Prop) (hphase7 : Pphase7)
    (hcompDiff_int : IntegrableOn
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      (collar (c * Real.sqrt τ))ᶜ volume)
    (hform : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
      IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
        = hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
    (herr : ∀ z, |rncRadialSq (uniformInverseChart g gi hC hK z 0) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
    (hmin : ∀ z, (1 / 2 : ℝ) * rncRadialSq z
      ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc) :
    Pphase7
    ∧ (‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
        ≤ L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
            * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5
                + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
            / 16 / Real.sqrt τ) :=
  ⟨hphase7,
   hcomp_final2 g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ L' Mqc hL' hMqc
     hcompDiff_int hform herr hmin hqcbdd⟩

end QIQTH.SlotInstantiationVIII

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SlotInstantiationVIII
#print axioms normPow5_gauss_bound_twoTau
#print axioms normPow3_gauss_bound_twoTau
#print axioms comparisonDom2_nonneg
#print axioms comparisonDom2_integrable
#print axioms comparisonDom2_moment
#print axioms hdom_comp2_ptwise
#print axioms hcomp_final2
#print axioms slotInstantiation_phase8
end AxiomChecks

/-! ###############################################################################
    ## PHASE 8 COVERAGE  (J4-425, Part B, tranche (a))
    ###############################################################################

  S5b — `hdom_comp` OFF-COLLAR CLOSURE.  OUTCOME: DISCHARGED GLOBALLY.  The phase-7 off-collar failure
  of the pointwise ρ-route (`e^{|θ|}` blow-up as `τ → 0` at fixed `‖z‖`) is bypassed by the ALGEBRAIC
  S5b identity `hessGaussFactor·(ρ−1)·qc = (z_i²−2τ)/(4τ²)·(G^chart − G_τ)·qc` (`gauss_ratio_rho`,
  EXACT) + the banked `gaussDdim_replace_bound` (`|G^chart − G_τ| ≤ (L'‖z‖³/4τ)·(√2)ⁿ·G_{2τ}`, GLOBAL,
  no exp).  This gives:
    • `comparisonDom2` — the width-`2τ` dominator `(L'(√2)ⁿMqc/(16τ³))·(‖z‖⁵+2τ‖z‖³)·G_{2τ}`.
    • `hdom_comp2_ptwise` — `‖H·(ρ−1)·qc‖ ≤ comparisonDom2` for ALL `z` (no collar restriction).
    • `comparisonDom2_moment` — `∫ comparisonDom2 ≤ Bcomp2/√τ`, EXACT `C/√τ` scaling (`τ^{5/2}÷τ³`).
    • `hcomp_final2` — `hcomp_collapsed` wired at `comparisonDom2`, with `hDint`/`hmom`/**`hdom`** ALL
      discharged internally (the last is the phase-6/7 carry, now GONE).

  THE HYPOTHESES `gaussDdim_replace_bound` FORCED US TO CARRY (exact enumeration).  The S5b bound is
  applied with `W z = uniformInverseChart g gi hC hK z 0`; its two hypotheses become STANDING inputs of
  `hdom_comp2_ptwise`/`hcomp_final2`/`slotInstantiation_phase8`:
    • `herr : ∀ z, |r²_{W z} − r²_z| ≤ L'·‖z‖³`   — the ℓ² near-isometry CUBIC-error input (`L'`).
    • `hmin : ∀ z, ½·r²_z ≤ r²_{W z}`             — the COERCIVITY input (source of the `(√2)ⁿ`).
  Plus `hqcbdd : ∀ z, |qc| ≤ Mqc` — the amplitude sup (R4).  These are GENUINE geometric/amplitude
  inputs (NOT smuggled vacuities): `herr`/`hmin` are chart near-isometry facts and `hqcbdd` a sup; all
  three are `∀ z` (whole-space), which is exactly what a GLOBAL off-collar bound legitimately requires.

  n-DEPENDENCE OF THE CONSTANT.  `Bcomp2` carries `(√2)ⁿ` (from the coercivity step of
  `gaussDdim_replace_bound`), on top of the linear `n`.  Since `n` is fixed for the witness,
  `hcomp_collapsed` accepts this `n`-dependent constant; the τ-scaling `1/√τ` is unaffected.  Simplified
  value: `Bcomp2 = L'·(√2)ⁿ·Mqc·n·(3328 + √2)/4`.

  DON'T-UNDERCREDIT FINDINGS.  The heavy lifting was ALREADY BANKED: `gaussDdim_replace_bound`
  (`QIQTH.HeatResidualBound`, GaussianMomentEnvelope.lean) supplies the GLOBAL `G_{2τ}` replacement with
  the `(√2)ⁿ` coercivity factor; `gauss_ratio_rho` (`QIQTH.AmplitudeDataOnCollar`) supplies the EXACT
  ratio; `pow_norm_mul_gauss_integral` already carries the `κ` (width) parameter, so the width-`2τ`
  moments are a κ = 2 instantiation (NO new moment tower needed).  Phase 8 is pure ASSEMBLY of banked
  bricks.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ★★★ UPDATED GROUP-(1) RESIDUE (after phases 1–8) = ENUMERATED INPUT CARRIES ONLY.  MILESTONE.
  The group-(1) slot-instantiation ALGEBRA is complete AND the off-collar `hdom_comp` closure — the one
  remaining analytic gap after phase 7 — is now DISCHARGED (S5b).  What stands is a FINITE list of
  GENUINE INPUT carries, with NO further identity / scaling / domination work open in group (1):
    (I1)  `herr` — the ℓ² near-isometry cubic-error bound (chart geometry input, constant `L'`).
    (I2)  `hmin` — the chart coercivity `½r²_z ≤ r²_{Wz}` (chart geometry input).
    (I3)  `hqcbdd`/`Mqc` (and the phase-6 `M`/`Sconst`) — the amplitude·Levi SUP carries (R4).
    (I4)  `hform` — the off-collar jet supply (R2; discharged pointwise by
          `ichartResidual_sub_hess_form` wherever chart jets hold at base `z`).
    (I5)  `hcompDiff_int` — off-collar integrability of the residual difference (R3, phase-3 wiring).
    (I6)  `hf2int`/`hf3int` — the `.choose`-heavy integrand measurability carries (R5, DEFEQ-lesson).
  NONE of these is an open identity or τ-scaling: they are chart-geometry inputs (I1/I2/I4),
  amplitude sups (I3), and measurability/integrability wiring (I5/I6).  GROUP (1) = ENUMERATED INPUT
  CARRIES ONLY.  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack;
  this brick closes only the group-(1) slot-instantiation off-collar dominator, NOT any physical `R/6`
  claim.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
