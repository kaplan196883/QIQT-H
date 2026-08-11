/-
  FrozenWire — J4-612: the frozen defect WIRED into the α = −1/2 Neumann engine, the α = −1/2
  per-step integrability family DISCHARGED, and the final-rate audit (Sol go/no-go 3).

  WHY.  J4-610 (FrozenDefect) banked the τ^{−1/2} one-step defect bound
      |∑ᵢⱼ (gⁱʲ(q+v) − gⁱʲ(q)) ∂ᵢ∂ⱼΓ_q(τ,v)| ≤ (C/√τ)·G_{2τ}(v)
  and J4-611 (AlphaLevi) opened the D2 Neumann engine at α = −1/2
  (`leviSeries_dominatedW_le_negHalf`), whose antecedents are the one-step bound in exactly that
  shape PLUS the per-step integrability family `IterConvIntegrableW E 2 (−1/2) C`.  This file
  closes the gap between them:

    ▸ `frozenDefectKernel K r` — the frozen defect as an ACTUAL two-point kernel
      `ℝ → Point n → Point n → ℝ` (`v := p − q`), gated to `0 < τ ≤ 1` and `q` in the `r`-ball
      (outside the gate the kernel is `0` — the honest domain of the J4-610 bound; the τ-gate
      doubles as the engine's `hEzero`).
    ▸ `frozenDefectKernel_bound` — the J4-610 bound transported to the kernel, now FULL-∀τ
      (`|E τ p q| ≤ (C/√τ)·G_{2τ}(p−q)` for ALL τ > 0: above the gate the kernel is `0`).
      Because the gate caps τ at 1, NO time-cap machinery is needed.
    ▸ THE α = −1/2 PER-STEP INTEGRABILITY (the J4-611 reported gap, DISCHARGED):
      • `rpow_mul_rpow_intervalIntegrable` — the Beta-integrand interval integrability
        `∫₀ᵗ (t−s)^a·s^b` for `a,b > −1` (split at `t/2`; each half = integrable-power ×
        bounded factor) — the ingredient absent at α = 0 (where `(t−s)^0 = 1`).
      • `modelZ_integrableW_alpha` / `modelS_intervalIntegrableW_alpha` — the model conjuncts
        (4)∧(5) of `IterConvIntegrableW E 2 α C` for ALL `α > −1` (mirrors of the α = 0
        `ModelIntegrableW` proofs; the per-step engine `iterKernelW_eq` was already α-general).
      • `iterConvIntegrableW_of_bound_baseMeas_alpha` — the α-PARAMETRIC replay of the
        α = 0 producer `iterConvIntegrableW_of_bound_baseMeas`: the residual conjuncts
        (1)(2)(3) are α-INDEPENDENT and the joint domination/integrability induction of
        `IterConvIntegrableFull` never used `α = 0` — CONFIRMED α-agnostic by this replay,
        which consumes the model conjuncts as an input.  Measurability carries reused verbatim
        (`iterE_zmeas`, `conv_meas` are α-free).
    ▸ `frozenDefectKernel_stronglyMeasurable` — the base joint measurability of the kernel
      (closed-form body: rational coefficients × exact `∂∂Γ` formula × frozen Gaussian;
      measurable everywhere, ⚠ NO continuity at τ = 0 is claimed — none is needed).
    ▸ ★ `frozenWire_leviSeries_dominated` — THE WIRE: for every `K ≤ 0`, `r ≥ 0` there are
      `C > 0`, `C_L ≥ 0` with the one-step bound AND
          |leviSeries (frozenDefectKernel K r) τ p q| ≤ (C_L/√τ)·G_{2τ}(p−q)   on 0 < τ ≤ 1.
    ▸ NON-VACUITY: `frozenDefectKernel_witness_ne_zero` — the wired kernel is GENUINELY NONZERO
      at curved data (K < 0, n ≥ 2): the J4-610 witness (q = 0, v = unit vector) lies INSIDE
      the gate, so the series bound is about a genuinely nonzero kernel.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ★ FINAL-RATE AUDIT (Sol go/no-go 3) — VERDICT: (ii), THE CENTER-COLUMN SHARPENING IS REQUIRED.

  The a₁ = R/6 extraction (`TrueKernelA1.trueKernel_diagonal_a1_eq_R6`) consumes the Levi series
  at TWO points: (A) SUMMABILITY of the residual Neumann series at fixed t (for the heat
  equation) — an INTEGRATED consumption, for which the α = −1/2 series bound SUFFICES; and
  (B) `hCorrHigher` — the diagonal correction `heatConv H (leviSeries E) t 0 0 = pref·(t²·cRem)`
  whose GENUINE content (per `CorrHigherReduction`) is the POINTWISE per-slice `O((t−s)+s)`
  bound, i.e. an `O(τ)`-at-the-diagonal remainder requirement, NOT an integrated one.  Under the
  series domination |leviSeries E (s,·,0)| ≤ C_L·s^α·G_{2s}, the k ≥ 2 tail of the center-column
  series is O(s^{2(α+1)−1}): at α = −1/2 this is O(1) — after ∫₀ᵗ ds it contributes O(t), which
  WOULD SHIFT a₁; at α = 0 it is O(s) — exactly the `O((t−s)+s)` slice shape.  VERDICT: the
  τ-integrated consumers admit α = −1/2 (GO for convergence/summability), but the diagonal-rate
  consumer REQUIRES the center-column α = 0 sharpening.  That sharpening is CHEAP and is landed
  here: `FrozenDefectCenterZero` + `frozenDefectCenterZero_spaceForm` — at the RNC center `q = 0`
  the space-form coefficient is PURELY QUADRATIC (`curvedRNCInv_diff_bound` at `r = 0` gives
  |gⁱʲ(v) − gⁱʲ(0)| ≤ (−K/3)·2‖v‖², the linear term dropping), so the center-column defect obeys
  the CLEAN α = 0 bound |E(τ,·,0)| ≤ C·G_{2τ} with NO τ^{−1/2} weight, all τ > 0.

  ⚠ HONEST SCOPE.  `a₁ = R/6` remains CONDITIONAL: the flat tower is non-vacuous and closed; the
  curved side still owes the per-q re-based producer re-assembly (consuming this wire), the
  center-column α = 0 series re-run + its splice into the diagonal-rate consumer, the fat-K
  hEmeas/hAdom/hcont piles, the capstone co-instantiation, and the prior piles.  This brick is
  wire + α = −1/2 IterConv discharge + rate audit (+ the audit-mandated center-zero bound).
  No axioms, no sorry.
-/
import Mathlib
import QIQTH.FrozenDefect
import QIQTH.AlphaLevi
import QIQTH.IterEMeasurable

open Finset Filter Topology MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianWidthTransfer QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.CurvedRNCGaugeBundle QIQTH.FrozenGauss QIQTH.FrozenDefect
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.AlphaLevi

namespace QIQTH.FrozenWire

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. The frozen-defect two-point kernel (closed form, gated). -/

/-- **The frozen-defect kernel** `E_frozen(τ,p,q)`: the J4-610 Levi defect
    `∑ᵢⱼ (gⁱʲ(p) − gⁱʲ(q))·∂ᵢ∂ⱼΓ_q(τ, p−q)` written via the EXACT `frozenGauss_pd_pd` closed
    form (so the kernel is globally defined and measurable), GATED to the honest domain of the
    J4-610 bound: `0 < τ ≤ 1` and `q` in the `r`-ball; `0` outside (in particular for `τ ≤ 0`,
    the engine's `hEzero`). -/
noncomputable def frozenDefectKernel (K r : ℝ) (τ : ℝ) (p q : Point n) : ℝ :=
  if 0 < τ ∧ τ ≤ 1 ∧ rncRadialSq q ≤ r ^ 2 then
    ∑ i, ∑ j, (curvedRNCInv K p i j - curvedRNCInv K q i j)
      * ((-(curvedRNCMetric K q i j) / (2 * τ)
          + (∑ k, curvedRNCMetric K q i k * ((fun a => p a - q a) k))
            * (∑ k, curvedRNCMetric K q j k * ((fun a => p a - q a) k)) / (4 * τ ^ 2))
        * frozenGauss (curvedRNCMetric K q) τ (fun a => p a - q a))
  else 0

/-- On the gate, the closed form IS the pd-form defect of J4-610 (via the exact
    `frozenGauss_pd_pd` calculus; needs `τ > 0` and the symmetry of the frozen metric). -/
theorem frozenDefectKernel_eq_pd (K r τ : ℝ) (p q : Point n)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hq : rncRadialSq q ≤ r ^ 2) :
    frozenDefectKernel K r τ p q
      = ∑ i, ∑ j, (curvedRNCInv K p i j - curvedRNCInv K q i j)
          * pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i
              (fun a => p a - q a) := by
  unfold frozenDefectKernel
  rw [if_pos ⟨hτ, hτ1, hq⟩]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [frozenGauss_pd_pd (curvedRNCMetric K q) (fun a b => curvedRNCMetric_symm K q a b) τ hτ
      (fun a => p a - q a) i j]

/-- `hEzero`: the kernel vanishes at nonpositive time. -/
theorem frozenDefectKernel_zero (K r : ℝ) (τ : ℝ) (hτ : τ ≤ 0) (p q : Point n) :
    frozenDefectKernel K r τ p q = 0 := by
  unfold frozenDefectKernel
  rw [if_neg]
  rintro ⟨h1, -, -⟩
  linarith

/-- **The FULL-∀τ α = −1/2 one-step bound** for the gated kernel: `∃ C > 0` with
    `|E_frozen(τ,p,q)| ≤ (C/√τ)·G_{2τ}(p−q)` for ALL `τ > 0` and ALL `p, q` — on the gate this
    is J4-610 (`frozenDefectBound_spaceForm`, `v := p − q`); off the gate the kernel is `0` and
    the RHS is nonnegative.  The τ ≤ 1 gate makes the bound global-in-τ, so NO time-cap is
    needed for the per-step integrability producer. -/
theorem frozenDefectKernel_bound (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (p q : Point n), 0 < τ →
      |frozenDefectKernel K r τ p q| ≤ C / Real.sqrt τ * gaussDdim (2 * τ) (p - q) := by
  obtain ⟨C, hC, hbd⟩ := frozenDefectBound_spaceForm (n := n) K hK r hr
  refine ⟨C, hC, fun τ p q hτ => ?_⟩
  have hG0 : 0 ≤ gaussDdim (2 * τ) (p - q) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  by_cases hgate : τ ≤ 1 ∧ rncRadialSq q ≤ r ^ 2
  · obtain ⟨hτ1, hq⟩ := hgate
    rw [frozenDefectKernel_eq_pd K r τ p q hτ hτ1 hq]
    have h := hbd τ hτ hτ1 q (fun a => p a - q a) hq
    have hqv : (fun a => q a + (fun a' => p a' - q a') a) = p := funext fun a => by simp
    have hpq : (fun a => p a - q a) = p - q := funext fun a => (Pi.sub_apply p q a).symm
    rw [hqv, hpq] at h
    rw [hpq]
    exact h
  · unfold frozenDefectKernel
    rw [if_neg (fun h => hgate ⟨h.2.1, h.2.2⟩), abs_zero]
    have : 0 ≤ C / Real.sqrt τ := le_of_lt (div_pos hC hst)
    exact mul_nonneg this hG0

/-! ### 2. Joint strong measurability of the kernel. -/

/-- The radial square is continuous. -/
theorem continuous_rncRadialSq : Continuous fun v : Point n => rncRadialSq v := by
  unfold rncRadialSq
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2

/-- Each frozen-metric entry is continuous in the base point (a polynomial). -/
theorem continuous_curvedRNCMetric_entry (K : ℝ) (i j : Fin n) :
    Continuous fun q : Point n => curvedRNCMetric K q i j := by
  unfold curvedRNCMetric
  exact continuous_const.sub (continuous_const.mul
    ((continuous_rncRadialSq.mul continuous_const).sub
      ((continuous_apply i).mul (continuous_apply j))))

/-- The frozen-metric determinant is continuous in the base point. -/
theorem continuous_curvedRNCMetric_det (K : ℝ) :
    Continuous fun q : Point n => Matrix.det (curvedRNCMetric K q) := by
  have h : Continuous fun q : Point n =>
      (Matrix.of fun i j => curvedRNCMetric K q i j : Matrix (Fin n) (Fin n) ℝ) :=
    continuous_matrix fun i j => continuous_curvedRNCMetric_entry K i j
  exact h.matrix_det

/-- Each inverse-metric entry is (jointly) measurable in the base point (rational function with a
    possibly-vanishing denominator for `K > 0`; measurability needs no sign condition). -/
theorem measurable_curvedRNCInv_entry (K : ℝ) (i j : Fin n) :
    Measurable fun q : Point n => curvedRNCInv K q i j := by
  have hr : Measurable fun q : Point n => rncRadialSq q := continuous_rncRadialSq.measurable
  unfold curvedRNCInv
  fun_prop

/-- **The base joint strong measurability of the frozen-defect kernel** (the `hEmeas` input of the
    per-step-integrability producer).  ⚠ HONEST: measurability only — the kernel is CONTINUOUS in
    `(τ,p,q)` only on `τ > 0`; at `τ = 0` no continuity is claimed (nor needed). -/
theorem frozenDefectKernel_stronglyMeasurable (K r : ℝ) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      frozenDefectKernel K r w.1 w.2.1 w.2.2) := by
  have hq2 : Measurable fun w : ℝ × Point n × Point n => w.2.2 :=
    measurable_snd.comp measurable_snd
  have hp2 : Measurable fun w : ℝ × Point n × Point n => w.2.1 :=
    measurable_fst.comp measurable_snd
  have hv : ∀ kk : Fin n, Measurable fun w : ℝ × Point n × Point n =>
      w.2.1 kk - w.2.2 kk := fun kk =>
    ((measurable_pi_apply kk).comp hp2).sub ((measurable_pi_apply kk).comp hq2)
  have hA : ∀ i j : Fin n, Measurable fun w : ℝ × Point n × Point n =>
      curvedRNCMetric K w.2.2 i j := fun i j =>
    (continuous_curvedRNCMetric_entry K i j).measurable.comp hq2
  have hrow : ∀ i : Fin n, Measurable fun w : ℝ × Point n × Point n =>
      ∑ k, curvedRNCMetric K w.2.2 i k * ((fun a => w.2.1 a - w.2.2 a) k) := fun i =>
    Finset.measurable_sum _ fun k _ => (hA i k).mul (hv k)
  have hquad : Measurable fun w : ℝ × Point n × Point n =>
      quadForm (curvedRNCMetric K w.2.2) (fun a => w.2.1 a - w.2.2 a) := by
    unfold quadForm
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      ((hA i j).mul (hv i)).mul (hv j)
  have hgauss : Measurable fun w : ℝ × Point n × Point n =>
      frozenGauss (curvedRNCMetric K w.2.2) w.1 (fun a => w.2.1 a - w.2.2 a) := by
    unfold frozenGauss
    exact ((Measurable.pow_const
        ((Real.continuous_sqrt.measurable.comp (measurable_fst.const_mul (4 * Real.pi))).inv)
        n).mul
      (Real.continuous_sqrt.measurable.comp
        ((continuous_curvedRNCMetric_det K).measurable.comp hq2))).mul
      (Real.measurable_exp.comp (hquad.neg.div (measurable_fst.const_mul 4)))
  have hbody : Measurable fun w : ℝ × Point n × Point n =>
      ∑ i, ∑ j, (curvedRNCInv K w.2.1 i j - curvedRNCInv K w.2.2 i j)
        * ((-(curvedRNCMetric K w.2.2 i j) / (2 * w.1)
            + (∑ k, curvedRNCMetric K w.2.2 i k * ((fun a => w.2.1 a - w.2.2 a) k))
              * (∑ k, curvedRNCMetric K w.2.2 j k * ((fun a => w.2.1 a - w.2.2 a) k))
              / (4 * w.1 ^ 2))
          * frozenGauss (curvedRNCMetric K w.2.2) w.1 (fun a => w.2.1 a - w.2.2 a)) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    refine (((measurable_curvedRNCInv_entry K i j).comp hp2).sub
      ((measurable_curvedRNCInv_entry K i j).comp hq2)).mul (Measurable.mul ?_ hgauss)
    exact (((hA i j).neg).div (measurable_fst.const_mul 2)).add
      (((hrow i).mul (hrow j)).div ((measurable_fst.pow_const 2).const_mul 4))
  have hgate : MeasurableSet {w : ℝ × Point n × Point n |
      0 < w.1 ∧ w.1 ≤ 1 ∧ rncRadialSq w.2.2 ≤ r ^ 2} := by
    have h1 : MeasurableSet {w : ℝ × Point n × Point n | 0 < w.1} :=
      measurableSet_lt measurable_const measurable_fst
    have h2 : MeasurableSet {w : ℝ × Point n × Point n | w.1 ≤ 1} :=
      measurableSet_le measurable_fst measurable_const
    have h3 : MeasurableSet {w : ℝ × Point n × Point n | rncRadialSq w.2.2 ≤ r ^ 2} :=
      measurableSet_le (continuous_rncRadialSq.measurable.comp hq2) measurable_const
    exact h1.inter (h2.inter h3)
  exact (Measurable.ite hgate hbody measurable_const).stronglyMeasurable

/-! ### 3. The α = −1/2 per-step integrability: the Beta interval integrability. -/

/-- **The Beta-integrand interval integrability**: for `a, b > −1` and `t > 0`,
    `s ↦ (t−s)^a · s^b` is interval-integrable on `[0,t]`.  Split at `t/2`: on each half one
    factor is an integrable power (`intervalIntegrable_rpow'`, transported by `s ↦ t − s` on the
    right half) and the other is bounded.  This is the ingredient the α = 0 model proofs never
    needed (`(t−s)^0 = 1`) and the α = −1/2 family does. -/
theorem rpow_mul_rpow_intervalIntegrable (a b t : ℝ) (ha : -1 < a) (hb : -1 < b) (ht : 0 < t) :
    IntervalIntegrable (fun s => (t - s) ^ a * s ^ b) volume 0 t := by
  have ht2 : 0 < t / 2 := by linarith
  have hmeas : Measurable fun s : ℝ => (t - s) ^ a * s ^ b := by
    have h1 : Measurable fun s : ℝ => t - s := measurable_const.sub measurable_id
    have h2 : Measurable fun s : ℝ => (t - s) ^ a := h1.pow measurable_const
    have h3 : Measurable fun s : ℝ => s ^ b := measurable_id.pow measurable_const
    exact h2.mul h3
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  have hsplit : Set.Ioc (0 : ℝ) (t / 2) ∪ Set.Ioc (t / 2) t = Set.Ioc (0 : ℝ) t :=
    Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  rw [← hsplit]
  refine IntegrableOn.union ?_ ?_
  · -- left half: `s^b` integrable, `(t−s)^a` bounded by `Ca`
    set Ca : ℝ := (t / 2) ^ a + t ^ a with hCadef
    have hCa0 : 0 ≤ Ca := by
      have h1 : (0 : ℝ) ≤ (t / 2) ^ a := Real.rpow_nonneg ht2.le a
      have h2 : (0 : ℝ) ≤ t ^ a := Real.rpow_nonneg ht.le a
      linarith
    have hg : IntegrableOn (fun s : ℝ => Ca * s ^ b) (Set.Ioc 0 (t / 2)) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht2.le]
      exact (intervalIntegral.intervalIntegrable_rpow' hb).const_mul Ca
    refine Integrable.mono' hg (hmeas.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => ?_)
    obtain ⟨hs0, hs2⟩ := hs
    have hts : 0 < t - s := by linarith
    have hbound : (t - s) ^ a ≤ Ca := by
      rcases le_or_gt 0 a with hage | halt
      · have h1 : (t - s) ^ a ≤ t ^ a :=
          Real.rpow_le_rpow hts.le (by linarith) hage
        have h2 : (0 : ℝ) ≤ (t / 2) ^ a := Real.rpow_nonneg ht2.le a
        rw [hCadef]; linarith
      · have h1 : (t - s) ^ a ≤ (t / 2) ^ a :=
          Real.rpow_le_rpow_of_nonpos ht2 (by linarith) halt.le
        have h2 : (0 : ℝ) ≤ t ^ a := Real.rpow_nonneg ht.le a
        rw [hCadef]; linarith
    have hsb : (0 : ℝ) ≤ s ^ b := Real.rpow_nonneg hs0.le b
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hts.le a) hsb)]
    exact mul_le_mul_of_nonneg_right hbound hsb
  · -- right half: `(t−s)^a` integrable (by `s ↦ t − s`), `s^b` bounded by `Cb`
    set Cb : ℝ := (t / 2) ^ b + t ^ b with hCbdef
    have hCb0 : 0 ≤ Cb := by
      have h1 : (0 : ℝ) ≤ (t / 2) ^ b := Real.rpow_nonneg ht2.le b
      have h2 : (0 : ℝ) ≤ t ^ b := Real.rpow_nonneg ht.le b
      linarith
    have hgII : IntervalIntegrable (fun s : ℝ => (t - s) ^ a) volume (t / 2) t := by
      have h0 : IntervalIntegrable (fun u : ℝ => u ^ a) volume 0 (t / 2) :=
        intervalIntegral.intervalIntegrable_rpow' ha
      have h1 := h0.comp_sub_left t
      rw [show t - t / 2 = t / 2 by ring, sub_zero] at h1
      exact h1.symm
    have hg : IntegrableOn (fun s : ℝ => Cb * (t - s) ^ a) (Set.Ioc (t / 2) t) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : t / 2 ≤ t)]
      exact hgII.const_mul Cb
    refine Integrable.mono' hg (hmeas.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => ?_)
    obtain ⟨hs2, hst⟩ := hs
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hts0 : 0 ≤ t - s := by linarith
    have hbound : s ^ b ≤ Cb := by
      rcases le_or_gt 0 b with hbge | hblt
      · have h1 : s ^ b ≤ t ^ b := Real.rpow_le_rpow hs0.le hst hbge
        have h2 : (0 : ℝ) ≤ (t / 2) ^ b := Real.rpow_nonneg ht2.le b
        rw [hCbdef]; linarith
      · have h1 : s ^ b ≤ (t / 2) ^ b :=
          Real.rpow_le_rpow_of_nonpos ht2 hs2.le hblt.le
        have h2 : (0 : ℝ) ≤ t ^ b := Real.rpow_nonneg ht.le b
        rw [hCbdef]; linarith
    have hta : (0 : ℝ) ≤ (t - s) ^ a := Real.rpow_nonneg hts0 a
    rw [Real.norm_of_nonneg (mul_nonneg hta (Real.rpow_nonneg hs0.le b))]
    calc (t - s) ^ a * s ^ b ≤ (t - s) ^ a * Cb := mul_le_mul_of_nonneg_left hbound hta
      _ = Cb * (t - s) ^ a := mul_comm _ _

/-! ### 4. The model conjuncts (4)∧(5) of `IterConvIntegrableW E 2 α C` for `α > −1`. -/

/-- **Model conjunct (4) at general `α > −1`** (the `z`-integrand is integrable for every `s`):
    mirror of the α = 0 `modelZ_integrableW`; the extra `(t−s)^α` factor is a `z`-constant. -/
theorem modelZ_integrableW_alpha (α C : ℝ) (hα : -1 < α) (k : ℕ) (hk : 1 ≤ k)
    (t : ℝ) (_ht : 0 < t) (x y : Point n) (s : ℝ) :
    Integrable
      (fun z => C * baseKernelW (2 : ℝ) α (t - s) x z
        * (C ^ k * iterKernelW (2 : ℝ) α k s z y)) volume := by
  by_cases hs : 0 < s ∧ s < t
  · obtain ⟨hs0, hst⟩ := hs
    have hform : (fun z => C * baseKernelW (2 : ℝ) α (t - s) x z
          * (C ^ k * iterKernelW (2 : ℝ) α k s z y))
        = fun z => (C * C ^ k
              * (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
              * (t - s) ^ α * s ^ ((k : ℝ) * (α + 1) - 1))
            * (gaussDdim (2 * (t - s)) (x - z) * gaussDdim (2 * s) (z - y)) := by
      funext z
      rw [iterKernelW_eq 2 α (by norm_num) hα s hs0 z y hk]
      simp only [baseKernelW]
      ring
    rw [hform]
    exact (gaussDdim_mul_integrable (2 * (t - s)) (2 * s) x y).const_mul _
  · rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      exact Integrable.of_finite
    · have hzero : (fun z => C * baseKernelW (2 : ℝ) α (t - s) x z
            * (C ^ k * iterKernelW (2 : ℝ) α k s z y))
          = fun _ => (0 : ℝ) := by
        funext z
        rcases not_and_or.mp hs with h | h
        · push_neg at h
          rw [iterKernelW_of_nonpos_time 2 α (by norm_num) hn1 k hk s h z y,
              mul_zero, mul_zero]
        · push_neg at h
          simp only [baseKernelW]
          rw [gaussDdim_eq_zero_of_nonpos hn1 (by nlinarith : 2 * (t - s) ≤ 0) (x - z),
              mul_zero, mul_zero, zero_mul]
      rw [hzero]; exact integrable_zero _ _ _

/-- **Model conjunct (5) at general `α > −1`** (the `s ↦ ∫ z (…)` map is interval-integrable on
    `[0,t]`): mirror of the α = 0 `modelS_intervalIntegrableW`, the dominating shape now the
    genuine Beta integrand `(t−s)^α·s^{k(α+1)−1}` (via `rpow_mul_rpow_intervalIntegrable`). -/
theorem modelS_intervalIntegrableW_alpha (α C : ℝ) (hα : -1 < α) (k : ℕ) (hk : 1 ≤ k)
    (t : ℝ) (ht : 0 < t) (x y : Point n) :
    IntervalIntegrable
      (fun s => ∫ z, C * baseKernelW (2 : ℝ) α (t - s) x z
        * (C ^ k * iterKernelW (2 : ℝ) α k s z y)) volume 0 t := by
  have he1 : (-1 : ℝ) < (k : ℝ) * (α + 1) - 1 := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hg_ii : IntervalIntegrable
      (fun s => (C * C ^ k * (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
                  * gaussDdim (2 * t) (x - y))
                * ((t - s) ^ α * s ^ ((k : ℝ) * (α + 1) - 1))) volume 0 t :=
    (rpow_mul_rpow_intervalIntegrable α ((k : ℝ) * (α + 1) - 1) t hα he1 ht).const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  have hg : IntegrableOn
      (fun s => (C * C ^ k * (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
                  * gaussDdim (2 * t) (x - y))
                * ((t - s) ^ α * s ^ ((k : ℝ) * (α + 1) - 1))) (Set.Ioc 0 t) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]; exact hg_ii
  refine hg.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
  intro hmem
  obtain ⟨hs0, hsle⟩ := hmem
  have hsne : s ≠ t := by simpa using hst
  have hst2 : s < t := lt_of_le_of_ne hsle hsne
  have hts : 0 < t - s := by linarith
  have hform : (fun z => C * baseKernelW (2 : ℝ) α (t - s) x z
        * (C ^ k * iterKernelW (2 : ℝ) α k s z y))
      = fun z => (C * C ^ k
            * (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
            * ((t - s) ^ α * s ^ ((k : ℝ) * (α + 1) - 1)))
          * (gaussDdim (2 * (t - s)) (x - z) * gaussDdim (2 * s) (z - y)) := by
    funext z
    rw [iterKernelW_eq 2 α (by norm_num) hα s hs0 z y hk]
    simp only [baseKernelW]
    ring
  show (C * C ^ k * (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
          * gaussDdim (2 * t) (x - y))
        * ((t - s) ^ α * s ^ ((k : ℝ) * (α + 1) - 1))
      = ∫ z, C * baseKernelW (2 : ℝ) α (t - s) x z * (C ^ k * iterKernelW (2 : ℝ) α k s z y)
  rw [hform, integral_const_mul,
      QIQTH.GaussianConvolution.gaussDdim_conv (2 * (t - s)) (2 * s)
        (by linarith) (by linarith) x y,
      show 2 * (t - s) + 2 * s = 2 * t from by ring]
  ring

/-- The packaged model conjuncts (4)∧(5) at general `α > −1` (the exact shape they occupy in
    `IterConvIntegrableW E 2 α C`). -/
theorem iterConvIntegrableW_model_alpha (α C : ℝ) (hα : -1 < α) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
      (∀ s, Integrable
        (fun z => C * baseKernelW (2 : ℝ) α (t - s) x z
          * (C ^ k * iterKernelW (2 : ℝ) α k s z y))) ∧
      IntervalIntegrable
        (fun s => ∫ z, C * baseKernelW (2 : ℝ) α (t - s) x z
          * (C ^ k * iterKernelW (2 : ℝ) α k s z y)) volume 0 t :=
  fun k hk t ht x y =>
    ⟨fun s => modelZ_integrableW_alpha α C hα k hk t ht x y s,
     modelS_intervalIntegrableW_alpha α C hα k hk t ht x y⟩

/-! ### 5. The α-parametric per-step-integrability producer (the α = 0 replay, confirmed
    α-agnostic). -/

/-- **★ THE α-PARAMETRIC PER-STEP INTEGRABILITY PRODUCER** — the replay of
    `iterConvIntegrableW_of_bound_baseMeas` at general `α > −1`: from the FULL-∀τ width-2
    order-`α` one-step bound, the vanishing at nonpositive time, and the single base joint
    measurability, the full family `IterConvIntegrableW E 2 α C` holds.  The joint
    domination/integrability induction of `IterConvIntegrableFull` is α-AGNOSTIC (this replay
    is the certificate); the model conjuncts are supplied by `iterConvIntegrableW_model_alpha`
    and the measurability carries by the α-free `iterE_zmeas` / `conv_meas`. -/
theorem iterConvIntegrableW_of_bound_baseMeas_alpha
    (E : ℝ → Point n → Point n → ℝ) (α C : ℝ) (hα : -1 < α)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) α τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n => E w.1 w.2.1 w.2.2)) :
    IterConvIntegrableW E (2 : ℝ) α C := by
  -- the three measurability carries, α-free, from the single base measurability
  have hE_zmeas : ∀ (τ : ℝ) (p : Point n),
      AEStronglyMeasurable (fun z : Point n => E τ p z) volume := fun τ p =>
    (hEmeas.comp_measurable
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have hIterE_zmeas := iterE_zmeas E hEmeas
  have hConv_meas := conv_meas E hEmeas
  -- The iterated residual vanishes at nonpositive time (from `hEzero`).
  have iterE_nonpos : ∀ (k : ℕ), 1 ≤ k → ∀ (s : ℝ), s ≤ 0 → ∀ (z y : Point n),
      iterE E k s z y = 0 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro s hs z y; rw [iterE_one]; exact hEzero s hs z y
    | succ m hm ih =>
        intro s hs z y
        rw [iterE_succ E hm, heatConvK_apply]
        simp only [heatConv]
        refine (intervalIntegral.integral_congr (fun s' hs' => ?_)).trans
          intervalIntegral.integral_zero
        have hmem : s' ∈ Set.Icc s 0 := by rwa [Set.uIcc_of_ge hs] at hs'
        have hzero : (fun w => E (s - s') z w * iterE E m s' w y) = fun _ => (0 : ℝ) := by
          funext w; rw [ih s' hmem.2 w y, mul_zero]
        show (∫ w, E (s - s') z w * iterE E m s' w y) = 0
        rw [hzero, integral_zero]
  -- The five conjuncts at level `k`, GIVEN the level-`k` domination.
  have mkI : ∀ (k : ℕ), 1 ≤ k →
      (∀ τ, 0 < τ → ∀ p q, |iterE E k τ p q| ≤ C ^ k * iterKernelW (2:ℝ) α k τ p q) →
      ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
        IntervalIntegrable (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t ∧
        IntervalIntegrable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t ∧
        (∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|)) ∧
        (∀ s, Integrable
          (fun z => C * baseKernelW (2:ℝ) α (t - s) x z
            * (C ^ k * iterKernelW (2:ℝ) α k s z y))) ∧
        IntervalIntegrable
          (fun s => ∫ z, C * baseKernelW (2:ℝ) α (t - s) x z
            * (C ^ k * iterKernelW (2:ℝ) α k s z y)) volume 0 t := by
    intro k hk domk t ht x y
    obtain ⟨hmodZ, hmodS⟩ := iterConvIntegrableW_model_alpha α C hα k hk t ht x y
    -- Conjunct (3): per-`s` `z`-integrability of the actual product.
    have c3 : ∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|) := by
      intro s
      by_cases hs : 0 < s ∧ s < t
      · obtain ⟨hs0, hst⟩ := hs
        have hts : 0 < t - s := by linarith
        have hmeas : AEStronglyMeasurable
            (fun z => |E (t - s) x z| * |iterE E k s z y|) volume :=
          (continuous_abs.comp_aestronglyMeasurable (hE_zmeas (t - s) x)).mul
            (continuous_abs.comp_aestronglyMeasurable (hIterE_zmeas k hk s y))
        refine Integrable.mono' (hmodZ s) hmeas (ae_of_all _ (fun z => ?_))
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
        have hE := hEbound (t - s) x z hts
        have hIt := domk s hs0 z y
        calc |E (t - s) x z| * |iterE E k s z y|
            ≤ (C * baseKernelW (2:ℝ) α (t - s) x z)
                * (C ^ k * iterKernelW (2:ℝ) α k s z y) :=
              mul_le_mul hE hIt (abs_nonneg _) (le_trans (abs_nonneg _) hE)
          _ = C * baseKernelW (2:ℝ) α (t - s) x z
                * (C ^ k * iterKernelW (2:ℝ) α k s z y) := by ring
      · have hz : (fun z => |E (t - s) x z| * |iterE E k s z y|) = fun _ => (0 : ℝ) := by
          funext z
          rcases not_and_or.mp hs with h | h
          · push_neg at h
            rw [iterE_nonpos k hk s h z y, abs_zero, mul_zero]
          · push_neg at h
            rw [hEzero (t - s) (by linarith) x z, abs_zero, zero_mul]
        rw [hz]; exact integrable_zero _ _ _
    -- Joint / slice measurability of the actual `s`-integrands on `Ioc 0 t`.
    have hjoint := hConv_meas k hk t ht x y
    have hsig : AEStronglyMeasurable (fun s => ∫ z, E (t - s) x z * iterE E k s z y)
        (volume.restrict (Set.Ioc 0 t)) := by
      simpa only [Function.uncurry_apply_pair] using hjoint.integral_prod_right'
    have habs : AEStronglyMeasurable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|)
        (volume.restrict (Set.Ioc 0 t)) := by
      have hju : AEStronglyMeasurable
          (Function.uncurry (fun (s : ℝ) (z : Point n) => |E (t - s) x z| * |iterE E k s z y|))
          ((volume.restrict (Set.Ioc 0 t)).prod volume) := by
        have heqf :
            (Function.uncurry (fun (s : ℝ) (z : Point n) => |E (t - s) x z| * |iterE E k s z y|))
              = fun p =>
                |Function.uncurry
                  (fun (s : ℝ) (z : Point n) => E (t - s) x z * iterE E k s z y) p| := by
          funext p
          obtain ⟨s, z⟩ := p
          simp only [Function.uncurry_apply_pair]
          rw [abs_mul]
        rw [heqf]
        exact continuous_abs.comp_aestronglyMeasurable hjoint
      simpa only [Function.uncurry_apply_pair] using hju.integral_prod_right'
    -- The model `s`-integrand is integrable on `Ioc 0 t`.
    have hh : Integrable
        (fun s => ∫ z, C * baseKernelW (2:ℝ) α (t - s) x z
          * (C ^ k * iterKernelW (2:ℝ) α k s z y)) (volume.restrict (Set.Ioc 0 t)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hmodS
    -- The pointwise integrand domination on the interior `0 < s < t`.
    have hptdom : ∀ s, 0 < s → s < t → ∀ z,
        |E (t - s) x z| * |iterE E k s z y|
          ≤ C * baseKernelW (2:ℝ) α (t - s) x z
              * (C ^ k * iterKernelW (2:ℝ) α k s z y) := by
      intro s hs0 hst z
      have hts : 0 < t - s := by linarith
      have hE := hEbound (t - s) x z hts
      have hIt := domk s hs0 z y
      calc |E (t - s) x z| * |iterE E k s z y|
          ≤ (C * baseKernelW (2:ℝ) α (t - s) x z)
              * (C ^ k * iterKernelW (2:ℝ) α k s z y) :=
            mul_le_mul hE hIt (abs_nonneg _) (le_trans (abs_nonneg _) hE)
        _ = C * baseKernelW (2:ℝ) α (t - s) x z
              * (C ^ k * iterKernelW (2:ℝ) α k s z y) := by ring
    -- Conjunct (2): interval-integrability of `s ↦ ∫ z |E|·|iterE|`.
    have c2 : IntervalIntegrable
        (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
      refine Integrable.mono' hh habs ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
      intro hmem
      obtain ⟨hs0, hsle⟩ := hmem
      have hsne : s ≠ t := by simpa using hst
      have hst2 : s < t := lt_of_le_of_ne hsle hsne
      rw [Real.norm_of_nonneg
            (integral_nonneg (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _)))]
      exact integral_mono (c3 s) (hmodZ s) (fun z => hptdom s hs0 hst2 z)
    -- Conjunct (1): interval-integrability of `s ↦ ‖∫ z E·iterE‖`.
    have c1 : IntervalIntegrable
        (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
      refine Integrable.mono' hh hsig.norm ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
      intro hmem
      obtain ⟨hs0, hsle⟩ := hmem
      have hsne : s ≠ t := by simpa using hst
      have hst2 : s < t := lt_of_le_of_ne hsle hsne
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      calc ‖∫ z, E (t - s) x z * iterE E k s z y‖
          ≤ ∫ z, ‖E (t - s) x z * iterE E k s z y‖ := norm_integral_le_integral_norm _
        _ = ∫ z, |E (t - s) x z| * |iterE E k s z y| := by
              refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
              simp only [Real.norm_eq_abs, abs_mul]
        _ ≤ ∫ z, C * baseKernelW (2:ℝ) α (t - s) x z
                * (C ^ k * iterKernelW (2:ℝ) α k s z y) :=
              integral_mono (c3 s) (hmodZ s) (fun z => hptdom s hs0 hst2 z)
    exact ⟨c1, c2, c3, hmodZ, hmodS⟩
  -- The iterated-residual domination, by induction (the step consumes `mkI`).
  have Dall : ∀ (k : ℕ), 1 ≤ k → ∀ τ, 0 < τ → ∀ p q,
      |iterE E k τ p q| ≤ C ^ k * iterKernelW (2:ℝ) α k τ p q := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        intro τ hτ p q
        rw [iterE_one, pow_one, iterKernelW_one]
        exact hEbound τ p q hτ
    | succ m hm ih =>
        intro τ hτ p q
        obtain ⟨hI1, hI2, hIf, hIg, hIsg⟩ := mkI m hm ih τ hτ p q
        rw [iterE_succ E hm, iterKernelW_succ (2:ℝ) α hm]
        simp only [heatConvK_apply]
        have hbound := heatConv_le_of_abs_le_pos E (iterE E m)
          (fun τ' p' q' => C * baseKernelW (2:ℝ) α τ' p' q')
          (fun τ' p' q' => C ^ m * iterKernelW (2:ℝ) α m τ' p' q')
          τ p q hτ
          (fun τ' p' q' hτ' => hEbound τ' p' q' hτ')
          (fun τ' p' q' hτ' => ih τ' hτ' p' q')
          hI1 hI2 hIf hIg hIsg
        calc |heatConv E (iterE E m) τ p q|
            ≤ heatConv (fun τ' p' q' => C * baseKernelW (2:ℝ) α τ' p' q')
                (fun τ' p' q' => C ^ m * iterKernelW (2:ℝ) α m τ' p' q') τ p q := hbound
          _ = C ^ (m + 1)
                * heatConv (baseKernelW (2:ℝ) α) (iterKernelW (2:ℝ) α m) τ p q := by
              rw [heatConv_smul_left C (baseKernelW (2:ℝ) α)
                    (fun τ' p' q' => C ^ m * iterKernelW (2:ℝ) α m τ' p' q'),
                  heatConv_smul_right (C ^ m) (baseKernelW (2:ℝ) α)
                    (iterKernelW (2:ℝ) α m), pow_succ]
              ring
  exact fun k hk t ht x y => mkI k hk (Dall k hk) t ht x y

/-! ### 6. ★ THE WIRE: the frozen defect through the α = −1/2 Neumann engine. -/

/-- **★★ J4-612 — THE WIRED α = −1/2 LEVI-SERIES BOUND FOR THE FROZEN DEFECT.**  For every
    `K ≤ 0`, `r ≥ 0` there are `C > 0` (the J4-610 one-step constant) and `C_L ≥ 0` with:
      (i)  the FULL one-step bound `|E_frozen(τ,p,q)| ≤ (C/√τ)·G_{2τ}(p−q)` (all `τ > 0`), and
      (ii) the SERIES bound `|leviSeries E_frozen (τ,p,q)| ≤ (C_L/√τ)·G_{2τ}(p−q)` on `0 < τ ≤ 1`.
    The per-step integrability `IterConvIntegrableW E_frozen 2 (−1/2) C` is DISCHARGED here
    (producer `iterConvIntegrableW_of_bound_baseMeas_alpha` + the kernel's measurability/zero/
    bound facts) — it is no longer a carried pile for THIS kernel.
    ⚠ HONEST WEIGHT: the series bound inherits the irreducible `τ^{−1/2}` (see
    `AlphaLevi.negHalf_weight_unbounded`); NOT `a₁ = R/6`. -/
theorem frozenWire_leviSeries_dominated (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r) :
    ∃ C C_L : ℝ, 0 < C ∧ 0 ≤ C_L ∧
      (∀ (τ : ℝ) (p q : Point n), 0 < τ →
        |frozenDefectKernel K r τ p q| ≤ C / Real.sqrt τ * gaussDdim (2 * τ) (p - q)) ∧
      (∀ (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ 1 →
        |leviSeries (frozenDefectKernel K r) τ p q|
          ≤ C_L / Real.sqrt τ * gaussDdim (2 * τ) (p - q)) := by
  obtain ⟨C, hC, hbd⟩ := frozenDefectKernel_bound (n := n) K r hK hr
  -- the one-step bound in the engine's `baseKernelW` shape
  have hEboundW : ∀ (τ : ℝ) (p q : Point n), 0 < τ →
      |frozenDefectKernel K r τ p q| ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q := by
    intro τ p q hτ
    rw [baseKernelW_negHalf_apply τ hτ]
    calc |frozenDefectKernel K r τ p q|
        ≤ C / Real.sqrt τ * gaussDdim (2 * τ) (p - q) := hbd τ p q hτ
      _ = C * (gaussDdim (2 * τ) (p - q) / Real.sqrt τ) := by ring
  -- the α = −1/2 per-step integrability, DISCHARGED
  have hInt : IterConvIntegrableW (frozenDefectKernel K r) (2 : ℝ) (-(1 / 2) : ℝ) C :=
    iterConvIntegrableW_of_bound_baseMeas_alpha (frozenDefectKernel K r) (-(1 / 2)) C
      (by norm_num) hEboundW
      (fun τ hτ p q => frozenDefectKernel_zero K r τ hτ p q)
      (frozenDefectKernel_stronglyMeasurable K r)
  -- the α = −1/2 Neumann engine (J4-611), at `T = 1`
  obtain ⟨C_L, hC_L, hser⟩ := leviSeries_dominatedW_le_negHalf (frozenDefectKernel K r) C 1
    hC.le one_pos (fun τ p q hτ _ => hbd τ p q hτ) hInt
  exact ⟨C, C_L, hC, hC_L, hbd, fun τ p q hτ hτ1 => hser τ p q hτ hτ1⟩

/-! ### 7. Non-vacuity: the wired kernel is genuinely nonzero at curved data. -/

/-- **NON-VACUITY (adversarial).**  For `K < 0`, `n ≥ 2`, ANY `r` and ANY `0 < τ ≤ 1` the wired
    kernel is NONZERO at some `(p,q)` — the J4-610 witness (`q = 0` is in every ball, `v` = unit
    vector, `p = q + v`) lies INSIDE the gate, so the series bound of
    `frozenWire_leviSeries_dominated` is about a GENUINE nonzero curved kernel. -/
theorem frozenDefectKernel_witness_ne_zero (K r : ℝ) (hKlt : K < 0) (hn : 2 ≤ n)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ p q : Point n, frozenDefectKernel K r τ p q ≠ 0 := by
  obtain ⟨q, v, hq, hne⟩ := frozenDefect_witness_ne_zero K hKlt hn r τ hτ
  refine ⟨fun a => q a + v a, q, ?_⟩
  rw [frozenDefectKernel_eq_pd K r τ (fun a => q a + v a) q hτ hτ1 hq]
  have hv : (fun a => (fun a' => q a' + v a') a - q a) = v := funext fun a => by simp
  rw [hv]
  exact hne

/-! ### 8. ★ THE FINAL-RATE AUDIT'S CONSTRUCTIVE HALF: the center-column α = 0 sharpening. -/

/-- **`FrozenDefectCenterZero`** — the center-column (`q = 0`) CLEAN α = 0 defect bound: at the
    RNC center the coefficient `gⁱʲ(v) − gⁱʲ(0)` is purely QUADRATIC (`∂g⁻¹(0) = 0` for the
    space form), so the defect obeys `|·| ≤ C·G_{λτ}(v)` with NO `τ^{−1/2}` weight, ALL `τ > 0`.
    This is the sharpening the final-rate audit shows the DIAGONAL consumer (`hCorrHigher`'s
    per-slice `O((t−s)+s)` bound) requires — verdict (ii) of go/no-go 3. -/
def FrozenDefectCenterZero (n : ℕ) (K C lam : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ v : Point n,
    |∑ i, ∑ j, (curvedRNCInv K v i j - curvedRNCInv K (0 : Point n) i j)
        * pd (fun y => pd (fun z =>
            frozenGauss (curvedRNCMetric K (0 : Point n)) τ z) j y) i v|
      ≤ C * gaussDdim (lam * τ) v

/-- **★ THE CENTER-COLUMN α = 0 BOUND, PROVED (`FrozenDefectCenterZero` inhabited at width 2).**
    Ingredients: `curvedRNCInv_diff_bound` at `r = 0` (the linear term DROPS:
    `|gⁱʲ(v) − gⁱʲ(0)| ≤ (−K/3)·2‖v‖²`), the banked second-partial and determinant bounds at
    `q = 0` (`M = 1`), and the width-2 absorptions `x·G_τ, x²·G_τ ≤ C·G_{2τ}` (`x = ‖v‖²/τ`) —
    the quadratic coefficient exactly cancels the `1/τ`, leaving NO `τ^{−1/2}`.  Valid for ALL
    `τ > 0` (no `τ ≤ 1` ceiling). -/
theorem frozenDefectCenterZero_spaceForm (K : ℝ) (hK : K ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ FrozenDefectCenterZero n K C 2 := by
  obtain ⟨C₁, hC₁, hb₁⟩ := gaussDdim_absorb_one (n := n) (η := 0) (lam := 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂, hb₂⟩ := gaussDdim_absorb_two (n := n) (η := 0) (lam := 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hk0 : (0 : ℝ) ≤ -K / 3 := by linarith
  have hq0 : rncRadialSq (0 : Point n) ≤ (0 : ℝ) ^ 2 := by simp
  set D : ℝ := Real.sqrt ((Nat.factorial n : ℝ) * (1 + -K / 3 * (0 : ℝ) ^ 2) ^ n) with hDdef
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hM1 : (1 : ℝ) + -K / 3 * (0 : ℝ) ^ 2 = 1 := by ring
  refine ⟨(n : ℝ) ^ 2 * D * (-K / 3 * (C₁ + (n : ℝ) ^ 2 / 2 * C₂)) + 1, ?_, ?_⟩
  · have h0 : 0 ≤ (n : ℝ) ^ 2 * D * (-K / 3 * (C₁ + (n : ℝ) ^ 2 / 2 * C₂)) := by
      apply mul_nonneg (mul_nonneg (sq_nonneg _) hD0)
      apply mul_nonneg hk0
      have h1 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 2 * C₂ :=
        mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) hC₂.le
      linarith
    linarith
  · intro τ hτ v
    have hG0 : 0 ≤ gaussDdim τ v := QIQTH.ResidueBound.gaussDdim_nonneg _ _
    have hG20 : 0 ≤ gaussDdim (2 * τ) v := QIQTH.ResidueBound.gaussDdim_nonneg _ _
    have hgate : (1 - 0) * rncRadialSq v ≤ rncRadialSq v := by norm_num
    have hrv0 := rncRadialSq_nonneg v
    -- (i) the quadratic coefficient bound (linear term drops at q = 0)
    have hcoeff : ∀ i j : Fin n,
        |curvedRNCInv K v i j - curvedRNCInv K (0 : Point n) i j|
          ≤ -K / 3 * (2 * rncRadialSq v) := by
      intro i j
      have h := curvedRNCInv_diff_bound K hK 0 le_rfl (0 : Point n) v hq0 i j
      have h0v : (fun a => (0 : Point n) a + v a) = v := funext fun a => by simp
      rw [h0v] at h
      calc |curvedRNCInv K v i j - curvedRNCInv K (0 : Point n) i j|
          ≤ -K / 3 * (4 * 0 * Real.sqrt (rncRadialSq v) + 2 * rncRadialSq v) := h
        _ = -K / 3 * (2 * rncRadialSq v) := by ring
    -- (ii) the second-partial and determinant bounds at q = 0 (M = 1)
    have hcoef0 : (0 : ℝ)
        ≤ 1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2) := by
      apply add_nonneg (by positivity)
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (by norm_num)) hrv0
    have hpd : ∀ i j : Fin n,
        |pd (fun y => pd (fun z =>
            frozenGauss (curvedRNCMetric K (0 : Point n)) τ z) j y) i v|
          ≤ (1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2))
            * (D * gaussDdim τ v) := by
      intro i j
      have h1 := frozenGauss_pd_pd_abs_le K hK 0 (0 : Point n) hq0 τ hτ v i j
      rw [hM1] at h1
      have h2 := frozenGauss_le_detBound_mul_gauss K hK 0 (0 : Point n) hq0 τ hτ v
      rw [hM1] at h2
      calc |pd (fun y => pd (fun z =>
              frozenGauss (curvedRNCMetric K (0 : Point n)) τ z) j y) i v|
          ≤ (1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2))
            * frozenGauss (curvedRNCMetric K (0 : Point n)) τ v := h1
        _ ≤ (1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2))
            * (Real.sqrt ((Nat.factorial n : ℝ) * 1 ^ n) * gaussDdim τ v) :=
            mul_le_mul_of_nonneg_left h2 hcoef0
        _ = (1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2))
            * (D * gaussDdim τ v) := by rw [hDdef, hM1]
    have hB0 : (0 : ℝ) ≤ -K / 3 * (2 * rncRadialSq v) :=
      mul_nonneg hk0 (by linarith)
    -- per-term bound
    have hterm : ∀ i j : Fin n,
        |(curvedRNCInv K v i j - curvedRNCInv K (0 : Point n) i j)
          * pd (fun y => pd (fun z =>
              frozenGauss (curvedRNCMetric K (0 : Point n)) τ z) j y) i v|
        ≤ (-K / 3 * (2 * rncRadialSq v))
          * ((1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2))
              * (D * gaussDdim τ v)) := by
      intro i j
      rw [abs_mul]
      exact mul_le_mul (hcoeff i j) (hpd i j) (abs_nonneg _) hB0
    -- sum bound
    have hsum : |∑ i, ∑ j, (curvedRNCInv K v i j - curvedRNCInv K (0 : Point n) i j)
          * pd (fun y => pd (fun z =>
              frozenGauss (curvedRNCMetric K (0 : Point n)) τ z) j y) i v|
        ≤ (n : ℝ) ^ 2 * ((-K / 3 * (2 * rncRadialSq v))
            * ((1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2))
                * (D * gaussDdim τ v))) := by
      calc |∑ i, ∑ j, (curvedRNCInv K v i j - curvedRNCInv K (0 : Point n) i j)
            * pd (fun y => pd (fun z =>
                frozenGauss (curvedRNCMetric K (0 : Point n)) τ z) j y) i v|
          ≤ ∑ i, |∑ j, (curvedRNCInv K v i j - curvedRNCInv K (0 : Point n) i j)
              * pd (fun y => pd (fun z =>
                  frozenGauss (curvedRNCMetric K (0 : Point n)) τ z) j y) i v| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ∑ j : Fin n,
              |(curvedRNCInv K v i j - curvedRNCInv K (0 : Point n) i j)
                * pd (fun y => pd (fun z =>
                    frozenGauss (curvedRNCMetric K (0 : Point n)) τ z) j y) i v| :=
            Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (-K / 3 * (2 * rncRadialSq v))
              * ((1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2))
                  * (D * gaussDdim τ v)) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
        _ = (n : ℝ) ^ 2 * ((-K / 3 * (2 * rncRadialSq v))
              * ((1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2))
                  * (D * gaussDdim τ v))) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
    -- (iii) the CLEAN fold: the quadratic coefficient cancels the 1/τ exactly — NO 1/√τ
    have hfold : (-K / 3 * (2 * rncRadialSq v))
          * (1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2))
        = -K / 3 * ((rncRadialSq v / τ)
            + (n : ℝ) ^ 2 / 2 * (rncRadialSq v / τ) ^ 2) := by
      field_simp
      ring
    -- absorption at width 2
    have habs : (rncRadialSq v / τ) * gaussDdim τ v
          + (n : ℝ) ^ 2 / 2 * ((rncRadialSq v / τ) ^ 2 * gaussDdim τ v)
        ≤ (C₁ + (n : ℝ) ^ 2 / 2 * C₂) * gaussDdim (2 * τ) v := by
      have h1 := hb₁ τ hτ v v hgate
      have h2 := hb₂ τ hτ v v hgate
      have h2' : (n : ℝ) ^ 2 / 2 * ((rncRadialSq v / τ) ^ 2 * gaussDdim τ v)
          ≤ (n : ℝ) ^ 2 / 2 * (C₂ * gaussDdim (2 * τ) v) :=
        mul_le_mul_of_nonneg_left h2 (div_nonneg (sq_nonneg _) (by norm_num))
      calc (rncRadialSq v / τ) * gaussDdim τ v
            + (n : ℝ) ^ 2 / 2 * ((rncRadialSq v / τ) ^ 2 * gaussDdim τ v)
          ≤ C₁ * gaussDdim (2 * τ) v + (n : ℝ) ^ 2 / 2 * (C₂ * gaussDdim (2 * τ) v) :=
            add_le_add h1 h2'
        _ = (C₁ + (n : ℝ) ^ 2 / 2 * C₂) * gaussDdim (2 * τ) v := by ring
    -- final assembly
    calc |∑ i, ∑ j, (curvedRNCInv K v i j - curvedRNCInv K (0 : Point n) i j)
          * pd (fun y => pd (fun z =>
              frozenGauss (curvedRNCMetric K (0 : Point n)) τ z) j y) i v|
        ≤ (n : ℝ) ^ 2 * ((-K / 3 * (2 * rncRadialSq v))
            * ((1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2))
                * (D * gaussDdim τ v))) := hsum
      _ = (n : ℝ) ^ 2 * D * (((-K / 3 * (2 * rncRadialSq v))
            * (1 / (2 * τ) + (n : ℝ) ^ 2 * 1 ^ 2 * rncRadialSq v / (4 * τ ^ 2)))
              * gaussDdim τ v) := by ring
      _ = (n : ℝ) ^ 2 * D * ((-K / 3 * ((rncRadialSq v / τ)
            + (n : ℝ) ^ 2 / 2 * (rncRadialSq v / τ) ^ 2)) * gaussDdim τ v) := by
          rw [hfold]
      _ = (n : ℝ) ^ 2 * D * (-K / 3
            * ((rncRadialSq v / τ) * gaussDdim τ v
                + (n : ℝ) ^ 2 / 2 * ((rncRadialSq v / τ) ^ 2 * gaussDdim τ v))) := by
          ring
      _ ≤ (n : ℝ) ^ 2 * D * (-K / 3
            * ((C₁ + (n : ℝ) ^ 2 / 2 * C₂) * gaussDdim (2 * τ) v)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) hD0)
          exact mul_le_mul_of_nonneg_left habs hk0
      _ = (n : ℝ) ^ 2 * D * (-K / 3 * (C₁ + (n : ℝ) ^ 2 / 2 * C₂))
            * gaussDdim (2 * τ) v := by ring
      _ ≤ ((n : ℝ) ^ 2 * D * (-K / 3 * (C₁ + (n : ℝ) ^ 2 / 2 * C₂)) + 1)
            * gaussDdim (2 * τ) v := by
          apply mul_le_mul_of_nonneg_right _ hG20
          linarith

end QIQTH.FrozenWire
