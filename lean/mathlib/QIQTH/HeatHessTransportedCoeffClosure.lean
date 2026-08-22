/-
  HeatHessTransportedCoeffClosure — the transported bilinear Hessian-COEFFICIENT closure brick: the
  precise real-analysis lemma (gpt-5.6-sol high, 2026-08-22 GO) that isolates EXACTLY which factor of
  `hCConv`'s `hcomp` transported coefficient is supplied by the hCross census machinery and which factor
  is the remaining `JointSecondOrderRNCRegularity` opaque-chart wall — and feeds the result directly into
  the J4-998 heat-kernel Hessian moment-cancellation payoff `integral_heatHessMult_mul_lipschitz`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  real-analysis infrastructure brick — a bounded/Lipschitz-at-origin product-closure calculus for the
  transported second-order coefficient, decoupled from the opaque chart and from `hcomp` itself.  It does
  **NOT** discharge `hcomp`: the vector factors below (`a = (P_i∘V)ₐ`, `b = (P_j∘V)_b`, the transported
  CHART FIRST JETS) still require the `JointSecondOrderRNCRegularity` chart-jet regularity, which the
  concrete `Classical.choose`-built `uniformInverseChart` does not (yet) supply.  No `sorry`, no new
  axioms, no `:= True`, no vacuous hypothesis (satisfiability EXHIBITED, `cos ‖·‖`), none equal to the
  conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE (gpt-5.6-sol high GO-audit, 2026-08-22).  A GO/NO-GO consult established that the
  hCross transported-weight machinery (`census_transported_weights_uniform`, J4-959) does **NOT**
  mechanically transfer to close `hcomp`:

    • hCross's `hballrate` is FIRST-order (∂_τ / trace).  After the base-slot change of variables its
      integrand collapses to `poly(w)·Gᵧ(w)·q₁ w + Gᵧ(w)·q₂ w` where `q₁ = (amp·F)/|det(fderiv Wbv)|∘V`,
      `q₂ = (slope·F)/|det|∘V`, and `poly(w)` is a pure GAUSSIAN MOMENT polynomial.  NO chart jets appear
      as weight factors.  Census proves `q₁, q₂` bounded + pairwise-Lipschitz uniformly from CONCRETE
      inputs (amp/slope regularity, the Levi `F`-carry, the determinant bundle `|det|≥½`+Lipschitz, and
      the IFT common-witness `V` Lipschitz).  It uses NO full field-slot chart-jet regularity — only the
      chart MAP `V` as a Lipschitz map plus the scalar Jacobian determinant.

    • `hcomp` is SECOND-order (a field Hessian).  By the chain rule
      `∂ᵢ∂ⱼ[Gᵧ(W_z(x))] = G''ᵧ[∂ᵢW, ∂ⱼW] + G'ᵧ·∂ᵢ∂ⱼW`, so the FIRST jets `P = ∂W` (contracted into the
      Gaussian-Hessian bilinear directions) and the SECOND jet `Q = ∂²W` enter as WEIGHT factors that
      vary with the integrated base `z`.  After transport the coefficient of `heatHessMult τ eₐ e_b` is
      therefore `q₁(w)·(P_i(Vw))ₐ·(P_j(Vw))_b`, i.e. census's `q₁` TIMES the transported chart-jet
      components — whose uniform boundedness + Lipschitz-at-origin is EXACTLY
      `JointSecondOrderRNCRegularity`, the recurring opaque-chart wall census never needed.

  So `integral_heatHessMult_mul_lipschitz`'s single `L`-hypothesis DECOMPOSES as a product:
  census-`q₁` part (available, concrete) × chart-jet part (the named wall).  This file supplies the
  DECOMPOSITION calculus (Sol's recommended "transported Hessian coefficient closure lemma, in bilinear
  form"), turning the vague "uniform Lipschitzness of the whole transported coefficient" into the exact
  product of named factor-moduli, and wiring it into the moment-cancellation payoff.

  ## WHAT LANDS.
    • `lipAtZero_bdd_mul` — the 2-factor closure: bounded (`Ma`,`Mb`) + Lipschitz-at-origin (`La`,`Lb`)
      scalars multiply to a bounded (`Ma·Mb`) + Lipschitz-at-origin (`Ma·Lb + Mb·La`) scalar.  The
      product identity `ab − a₀b₀ = a(b−b₀) + b₀(a−a₀)` with `|b₀| ≤ Mb`.
    • `lipAtZero_bdd_mul3` — the 3-factor closure `f = q·a·b`: bounded `Mq·Ma·Mb`, Lipschitz-at-origin
      `Mq·Ma·Lb + Mq·Mb·La + Ma·Mb·Lq`.  This is EXACTLY the transported-coefficient modulus in terms of
      the census scalar (`q`) and the two transported chart-jet components (`a`,`b`).
    • `integral_heatHessMult_mul_transportedCoeff` — ★★★ THE PAYOFF: the J4-998 moment-cancellation
      bound `|∫ v, heatHessMult τ p q_dir v · (q v·a v·b v)| ≤ Lf·n³‖p‖‖q_dir‖(16√2+1)/√τ` with `Lf` the
      explicit 3-factor modulus, obtained by feeding `lipAtZero_bdd_mul3` into
      `HeatHessMoment.integral_heatHessMult_mul_lipschitz`.  The `τ^{−1/2}` sliver rate for the FULL
      transported second-order coefficient, once its factor-moduli are supplied.
    • `integral_heatHessMult_mul_transportedCoeff_hyp_satisfiable` — NON-VACUITY: the whole factor bundle
      is jointly satisfiable by a genuine NONCONSTANT weight (`q = a = b = cos‖·‖`, all `M = L = 1`), so
      the payoff fires on a real bounded-Lipschitz coefficient, not an empty one.

  ## HONEST STATUS (blunt).  This brick supplies the decomposition + the moment-cancellation payoff for
  the transported second-order coefficient, and PROVES the census scalar factor is NOT the analytic wall.
  It does **NOT** discharge `hcomp`: (i) the vector factors `a = (P_i∘V)ₐ`, `b = (P_j∘V)_b` need the
  chart-jet regularity `JointSecondOrderRNCRegularity` (the concrete `uniformInverseChart` opaque-chart
  wall), NOT supplied by census; (ii) census's `q₁` is Lipschitz only LOCALLY (on `ball 0 σ`) whereas the
  moment-cancellation integral is over all of `Point n`, so a truncation/global step (part of R2) still
  intervenes; (iii) the full `hcomp` additionally needs the second-order chain rule, base-slot CoV,
  integrability/measurability, and coordinate summation.  `hCConv` NOT closed.  `hDuhamel`/`hDConv`
  unaffected.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HeatHessianMomentCancellation

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatHessMoment
open scoped Topology BigOperators

namespace QIQTH.HeatHessCoeffClosure

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. The bounded / Lipschitz-at-origin product closure. -/

/-- **`lipAtZero_bdd_mul` — the 2-factor closure.**  If `a, b : Point n → ℝ` are each bounded (`|a| ≤ Ma`,
    `|b| ≤ Mb`) and Lipschitz at the origin (`|a v − a 0| ≤ La‖v‖`, `|b v − b 0| ≤ Lb‖v‖`), then the
    product `a·b` is bounded by `Ma·Mb` and Lipschitz at the origin with modulus `Ma·Lb + Mb·La`.  The
    identity `a v·b v − a 0·b 0 = a v·(b v − b 0) + b 0·(a v − a 0)`, with `|b 0| ≤ Mb`.  NOT `a₁ = R/6`. -/
theorem lipAtZero_bdd_mul (a b : Point n → ℝ) (Ma La Mb Lb : ℝ)
    (hMa : 0 ≤ Ma) (hMb : 0 ≤ Mb)
    (hab : ∀ v, |a v| ≤ Ma) (haL : ∀ v, |a v - a 0| ≤ La * ‖v‖)
    (hbb : ∀ v, |b v| ≤ Mb) (hbL : ∀ v, |b v - b 0| ≤ Lb * ‖v‖) :
    (∀ v, |a v * b v| ≤ Ma * Mb) ∧
    (∀ v, |a v * b v - a 0 * b 0| ≤ (Ma * Lb + Mb * La) * ‖v‖) := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [abs_mul]; exact mul_le_mul (hab v) (hbb v) (abs_nonneg _) hMa
  · have hkey : a v * b v - a 0 * b 0
        = a v * (b v - b 0) + b 0 * (a v - a 0) := by ring
    rw [hkey]
    calc |a v * (b v - b 0) + b 0 * (a v - a 0)|
        ≤ |a v * (b v - b 0)| + |b 0 * (a v - a 0)| := abs_add_le _ _
      _ = |a v| * |b v - b 0| + |b 0| * |a v - a 0| := by rw [abs_mul, abs_mul]
      _ ≤ Ma * (Lb * ‖v‖) + Mb * (La * ‖v‖) := by
          apply add_le_add
          · exact mul_le_mul (hab v) (hbL v) (abs_nonneg _) hMa
          · exact mul_le_mul (hbb 0) (haL v) (abs_nonneg _) hMb
      _ = (Ma * Lb + Mb * La) * ‖v‖ := by ring

/-- **`lipAtZero_bdd_mul3` — the 3-factor closure `f = q·a·b`.**  If `q, a, b : Point n → ℝ` are each
    bounded (`Mq, Ma, Mb`) and Lipschitz at the origin (`Lq, La, Lb`), then `v ↦ q v·a v·b v` is bounded
    by `Mq·Ma·Mb` and Lipschitz at the origin with modulus `Mq·Ma·Lb + Mq·Mb·La + Ma·Mb·Lq`.  Proved by
    applying `lipAtZero_bdd_mul` to `(a,b)` then to `(q, a·b)`.  This is EXACTLY the transported second-
    order coefficient modulus with `q` the census scalar `(amp·F)/|det|∘V` and `a`,`b` the transported
    chart-jet components `(P_i∘V)ₐ`, `(P_j∘V)_b`.  NOT `a₁ = R/6`. -/
theorem lipAtZero_bdd_mul3 (q a b : Point n → ℝ) (Mq Lq Ma La Mb Lb : ℝ)
    (hMq : 0 ≤ Mq) (hMa : 0 ≤ Ma) (hMb : 0 ≤ Mb)
    (hqb : ∀ v, |q v| ≤ Mq) (hqL : ∀ v, |q v - q 0| ≤ Lq * ‖v‖)
    (hab : ∀ v, |a v| ≤ Ma) (haL : ∀ v, |a v - a 0| ≤ La * ‖v‖)
    (hbb : ∀ v, |b v| ≤ Mb) (hbL : ∀ v, |b v - b 0| ≤ Lb * ‖v‖) :
    (∀ v, |q v * a v * b v| ≤ Mq * Ma * Mb) ∧
    (∀ v, |q v * a v * b v - q 0 * a 0 * b 0|
        ≤ (Mq * Ma * Lb + Mq * Mb * La + Ma * Mb * Lq) * ‖v‖) := by
  -- inner product `a·b`.
  obtain ⟨hABb, hABL⟩ := lipAtZero_bdd_mul a b Ma La Mb Lb hMa hMb hab haL hbb hbL
  -- outer product `q·(a·b)`.
  obtain ⟨hQABb, hQABL⟩ :=
    lipAtZero_bdd_mul q (fun v => a v * b v) Mq Lq (Ma * Mb) (Ma * Lb + Mb * La)
      hMq (mul_nonneg hMa hMb) hqb hqL hABb hABL
  constructor
  · intro v; have := hQABb v; simpa [mul_assoc] using this
  · intro v
    have := hQABL v
    -- rewrite associativity and the modulus into the stated form
    have hmod : Mq * (Ma * Lb + Mb * La) + Ma * Mb * Lq
        = Mq * Ma * Lb + Mq * Mb * La + Ma * Mb * Lq := by ring
    calc |q v * a v * b v - q 0 * a 0 * b 0|
        = |q v * (a v * b v) - q 0 * (a 0 * b 0)| := by rw [mul_assoc, mul_assoc]
      _ ≤ (Mq * (Ma * Lb + Mb * La) + Ma * Mb * Lq) * ‖v‖ := this
      _ = (Mq * Ma * Lb + Mq * Mb * La + Ma * Mb * Lq) * ‖v‖ := by rw [hmod]

/-! ### 2. The moment-cancellation payoff for the transported second-order coefficient. -/

/-- **★★★ `integral_heatHessMult_mul_transportedCoeff` — THE PAYOFF.**  For `τ > 0`, Gaussian-Hessian
    directions `p, q_dir`, and a transported second-order coefficient `f v = q v · a v · b v` built from
    three bounded (`Mq, Ma, Mb`) + Lipschitz-at-origin (`Lq, La, Lb`) AE-strongly-measurable factors,
        `|∫ v, heatHessMult τ p q_dir v · (q v · a v · b v)|
            ≤ Lf · n³ · ‖p‖ · ‖q_dir‖ · (16√2 + 1) / √τ`,
    where `Lf := Mq·Ma·Lb + Mq·Mb·La + Ma·Mb·Lq` is the explicit 3-factor Lipschitz-at-origin modulus.
    The constant `f 0`-mode CANCELS (`integral_heatHessMult_eq_zero`, J4-998) and the remainder collapses
    to `τ^{−1/2}` — the exact `hcomp` sliver rate for the FULL transported coefficient, once its factor-
    moduli are supplied.  With `q` the census scalar (available, concrete) and `a`,`b` the transported
    chart-jet components (the `JointSecondOrderRNCRegularity` wall), this exhibits the census factor as
    NOT the analytic obstruction.  Does NOT discharge `hcomp`.  NOT `a₁ = R/6`. -/
theorem integral_heatHessMult_mul_transportedCoeff (τ : ℝ) (hτ : 0 < τ)
    (p q_dir : Point n) (q a b : Point n → ℝ) (Mq Lq Ma La Mb Lb : ℝ)
    (hMq : 0 ≤ Mq) (hLq : 0 ≤ Lq) (hMa : 0 ≤ Ma) (hLa : 0 ≤ La) (hMb : 0 ≤ Mb) (hLb : 0 ≤ Lb)
    (hqm : AEStronglyMeasurable q volume) (ham : AEStronglyMeasurable a volume)
    (hbm : AEStronglyMeasurable b volume)
    (hqb : ∀ v, |q v| ≤ Mq) (hqL : ∀ v, |q v - q 0| ≤ Lq * ‖v‖)
    (hab : ∀ v, |a v| ≤ Ma) (haL : ∀ v, |a v - a 0| ≤ La * ‖v‖)
    (hbb : ∀ v, |b v| ≤ Mb) (hbL : ∀ v, |b v - b 0| ≤ Lb * ‖v‖) :
    |∫ v : Point n, heatHessMult τ p q_dir v * (q v * a v * b v)|
      ≤ (Mq * Ma * Lb + Mq * Mb * La + Ma * Mb * Lq)
          * (n : ℝ) ^ 3 * ‖p‖ * ‖q_dir‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ := by
  set Lf : ℝ := Mq * Ma * Lb + Mq * Mb * La + Ma * Mb * Lq with hLfdef
  have hLf : 0 ≤ Lf := by rw [hLfdef]; positivity
  set f : Point n → ℝ := fun v => q v * a v * b v with hfdef
  have hfmeas : AEStronglyMeasurable f volume := (hqm.mul ham).mul hbm
  have hflip : ∀ v : Point n, |f v - f 0| ≤ Lf * ‖v‖ :=
    (lipAtZero_bdd_mul3 q a b Mq Lq Ma La Mb Lb hMq hMa hMb hqb hqL hab haL hbb hbL).2
  simpa [hfdef, hLfdef] using
    integral_heatHessMult_mul_lipschitz τ hτ p q_dir Lf hLf f hfmeas hflip

/-! ### 3. Non-vacuity — the factor bundle is inhabited by a genuine nonconstant coefficient. -/

/-- **Non-vacuity witness.**  The full factor bundle of `integral_heatHessMult_mul_transportedCoeff` is
    jointly satisfiable by a genuine NONCONSTANT coefficient: `q = a = b := (cos ‖·‖ : Point n → ℝ)`, each
    bounded by `1` (`Real.abs_cos_le_one`) and Lipschitz-at-origin with `L = 1`
    (`Real.lipschitzWith_cos`, `cos ‖0‖ = cos 0 = 1`).  So the payoff fires on a real bounded-Lipschitz
    weight, not an empty/unsatisfiable one.  NOT `a₁ = R/6`. -/
theorem integral_heatHessMult_mul_transportedCoeff_hyp_satisfiable :
    ∃ (q a b : Point n → ℝ) (Mq Lq Ma La Mb Lb : ℝ),
      0 ≤ Mq ∧ 0 ≤ Lq ∧ 0 ≤ Ma ∧ 0 ≤ La ∧ 0 ≤ Mb ∧ 0 ≤ Lb ∧
      AEStronglyMeasurable q volume ∧ AEStronglyMeasurable a volume ∧
      AEStronglyMeasurable b volume ∧
      (∀ v, |q v| ≤ Mq) ∧ (∀ v, |q v - q 0| ≤ Lq * ‖v‖) ∧
      (∀ v, |a v| ≤ Ma) ∧ (∀ v, |a v - a 0| ≤ La * ‖v‖) ∧
      (∀ v, |b v| ≤ Mb) ∧ (∀ v, |b v - b 0| ≤ Lb * ‖v‖) := by
  refine ⟨fun v => Real.cos ‖v‖, fun v => Real.cos ‖v‖, fun v => Real.cos ‖v‖,
    1, 1, 1, 1, 1, 1, zero_le_one, zero_le_one, zero_le_one, zero_le_one, zero_le_one, zero_le_one,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.continuous_cos.comp continuous_norm).aestronglyMeasurable
  · exact (Real.continuous_cos.comp continuous_norm).aestronglyMeasurable
  · exact (Real.continuous_cos.comp continuous_norm).aestronglyMeasurable
  all_goals first
    | (intro v; exact Real.abs_cos_le_one _)
    | (intro v
       have hlip := Real.lipschitzWith_cos.dist_le_mul ‖v‖ ‖(0 : Point n)‖
       simp only [Real.dist_eq, norm_zero, Real.cos_zero, NNReal.coe_one, one_mul,
         sub_zero, abs_norm] at hlip ⊢
       exact hlip)

end QIQTH.HeatHessCoeffClosure

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HeatHessCoeffClosure
#print axioms lipAtZero_bdd_mul
#print axioms lipAtZero_bdd_mul3
#print axioms integral_heatHessMult_mul_transportedCoeff
#print axioms integral_heatHessMult_mul_transportedCoeff_hyp_satisfiable
end AxiomChecks
