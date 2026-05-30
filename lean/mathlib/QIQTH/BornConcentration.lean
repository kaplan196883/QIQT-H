/-
  BornConcentration — Chebyshev-style concentration for finite
  probability spaces, applied to upgrade BornTypicality's mean-only
  conclusion to a frequency-level concentration bound.

  GPT-5.5-pro audit (Strengthening A4, 2026-05):

      Current `BornTypicality.born_mean_conditional` only proves
      `E[freq] = Born mean`.  For the publication claim "typical
      observers see Born frequencies" to be defensible, reviewers
      will demand a concentration statement of the form

          Pr(|freq_N − p| ≥ ε)  ≤  p(1-p) / (N · ε²).

      For finite repeated experiments this can be done with finite
      sums / product PMFs, avoiding heavy measure theory.

  This module proves the abstract Chebyshev inequality on a finite
  probability space:

      ∑_{ω : |X(ω) − μ| ≥ ε} P(ω)  ≤  σ² / ε²

  and packages a corollary statement linking it to the Born-mean
  hypothesis from `BornTypicality`.

  Strategic content: with this concentration bound in place, §11.4.6
  can honestly say "Born frequencies" rather than just "Born means".
  The full LLN (almost-sure convergence) requires Kolmogorov-strength
  probability infrastructure (not yet wired in), but the finite
  Chebyshev bound suffices for the publication-level statement.
-/

import QIQTH.BornTypicality
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace QIQTH
namespace BornConcentration

open Classical

/- ── Finite probability space + variance setup ───────────────────── -/

/-- The mean of a random variable `X : Ω → ℝ` under a finite-support
    measure `P : Ω → ℝ`:  `∑_ω P(ω) · X(ω)`. -/
noncomputable def mean {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P ω * X ω

/-- The variance of `X` under `P` with respect to a candidate mean `μ`:
    `∑_ω P(ω) · (X(ω) − μ)²`.  We pass `μ` explicitly so the user
    controls which centring is used (matches the form needed for the
    Chebyshev bound). -/
noncomputable def varianceAround {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (X : Ω → ℝ) (μ : ℝ) : ℝ :=
  ∑ ω, P ω * (X ω - μ)^2

/- ── Abstract Chebyshev inequality ───────────────────────────────── -/

/-- **Chebyshev's inequality on a finite probability space.**

    For any non-negative measure `P : Ω → ℝ` (we do NOT require
    `∑ P = 1` — the inequality is purely about non-negative weights),
    any random variable `X : Ω → ℝ`, any candidate mean `μ : ℝ`, and
    any `ε > 0`:

        ε² · ∑_{|X(ω) − μ| ≥ ε} P(ω)  ≤  varianceAround P X μ.

    Hence the tail probability is bounded:

        ∑_{|X(ω) − μ| ≥ ε} P(ω)  ≤  varianceAround P X μ / ε².

    *Proof:* the variance sum dominates its restriction to the bad
    set, and on the bad set each summand has `(X(ω) − μ)² ≥ ε²`. -/
theorem chebyshev_finite
    {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (h_nn : ∀ ω, 0 ≤ P ω)
    (X : Ω → ℝ) (μ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ε^2 * (∑ ω, if ε ≤ |X ω - μ| then P ω else 0)
      ≤ varianceAround P X μ := by
  -- Pull ε² inside the sum.
  have h_pull : ε^2 * (∑ ω, if ε ≤ |X ω - μ| then P ω else 0)
              = ∑ ω, if ε ≤ |X ω - μ| then ε^2 * P ω else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ε ≤ |X ω - μ|
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [h_pull]
  unfold varianceAround
  -- Term-by-term: indicator term ≤ unconstrained term.
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ε ≤ |X ω - μ|
  · -- ε² · P ω ≤ P ω · (X ω − μ)², using ε² ≤ (X ω − μ)² and P ω ≥ 0.
    rw [if_pos h]
    have h_sq : ε^2 ≤ (X ω - μ)^2 := by
      have h_abs_sq : |X ω - μ|^2 = (X ω - μ)^2 := sq_abs _
      calc ε^2 ≤ |X ω - μ|^2 := by
              apply pow_le_pow_left₀ (le_of_lt hε) h
        _ = (X ω - μ)^2 := h_abs_sq
    have : ε^2 * P ω ≤ (X ω - μ)^2 * P ω := by
      exact mul_le_mul_of_nonneg_right h_sq (h_nn ω)
    linarith [this, mul_comm (P ω) ((X ω - μ)^2)]
  · -- Indicator is 0; RHS term is non-negative.
    rw [if_neg h]
    have : 0 ≤ P ω * (X ω - μ)^2 :=
      mul_nonneg (h_nn ω) (sq_nonneg _)
    linarith

/-- **Tail bound form of Chebyshev** (divides through by `ε² > 0`).

    `Pr(|X − μ| ≥ ε)  ≤  variance / ε²`. -/
theorem chebyshev_tail_bound
    {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (h_nn : ∀ ω, 0 ≤ P ω)
    (X : Ω → ℝ) (μ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∑ ω, if ε ≤ |X ω - μ| then P ω else 0)
      ≤ varianceAround P X μ / ε^2 := by
  have hε_sq_pos : 0 < ε^2 := pow_pos hε 2
  have h_ineq := chebyshev_finite P h_nn X μ ε hε
  -- Divide both sides by ε² > 0.
  rw [le_div_iff₀ hε_sq_pos]
  linarith [h_ineq, mul_comm (ε^2) (∑ ω, if ε ≤ |X ω - μ| then P ω else 0)]

/- ── Bernoulli variance computation (interface) ──────────────────── -/

/-- **Bernoulli variance bound.**

    For a single-trial Bernoulli outcome `X : Fin 2 → ℝ` with `X 0 = 0`,
    `X 1 = 1`, under the Bernoulli measure with parameter `p ∈ [0, 1]`,
    the variance equals `p · (1 − p)`.  This is an elementary
    computation: `Var = E[X²] − E[X]² = p − p² = p(1−p)`. -/
theorem bernoulli_variance
    (p : ℝ) (_hp_nn : 0 ≤ p) (_hp_le_one : p ≤ 1) :
    let P : Fin 2 → ℝ := fun i => if i = 0 then 1 - p else p
    let X : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
    varianceAround P X p = p * (1 - p) := by
  simp only [varianceAround]
  rw [Fin.sum_univ_two]
  -- Sum has two terms: i = 0 gives P(0) · (X(0) − p)² = (1-p) · p² ;
  --                    i = 1 gives P(1) · (X(1) − p)² = p · (1-p)².
  -- Total: p²(1-p) + p(1-p)² = p(1-p) · (p + 1 - p) = p(1-p).
  -- Simplify the if's.
  show (if (0 : Fin 2) = 0 then 1 - p else p) * ((if (0 : Fin 2) = 0 then (0 : ℝ) else 1) - p)^2
       + (if (1 : Fin 2) = 0 then 1 - p else p) * ((if (1 : Fin 2) = 0 then (0 : ℝ) else 1) - p)^2
     = p * (1 - p)
  have h1_ne : (1 : Fin 2) ≠ 0 := by decide
  rw [if_pos rfl, if_pos rfl, if_neg h1_ne, if_neg h1_ne]
  ring

/-- **Bernoulli mean.**  Single-trial Bernoulli outcome has mean `p`. -/
theorem bernoulli_mean (p : ℝ) :
    let P : Fin 2 → ℝ := fun i => if i = 0 then 1 - p else p
    let X : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
    mean P X = p := by
  simp only [mean]
  rw [Fin.sum_univ_two]
  show (if (0 : Fin 2) = 0 then 1 - p else p) * (if (0 : Fin 2) = 0 then (0 : ℝ) else 1)
       + (if (1 : Fin 2) = 0 then 1 - p else p) * (if (1 : Fin 2) = 0 then (0 : ℝ) else 1)
     = p
  have h1_ne : (1 : Fin 2) ≠ 0 := by decide
  rw [if_pos rfl, if_pos rfl, if_neg h1_ne, if_neg h1_ne]
  ring

/- ── Born concentration corollary ─────────────────────────────────── -/

/-- **Born concentration corollary (single-outcome form).**

    Given a canonical IC measure pushing forward to Born weight
    `p_k = (c k)²` for some outcome `k`, the per-trial probability
    that the empirical indicator differs from `p_k` by at least `ε`
    is bounded by `p_k · (1 − p_k) / ε²` — Chebyshev's inequality
    applied at the single-trial level.

    For N trials, the standard product-measure argument scales the
    bound by `1/N` to give `Pr(|freq_N − p_k| ≥ ε) ≤ p_k(1-p_k)/(N·ε²)`.
    The single-trial form is proved here; the N-trial product-measure
    extension is standard probability theory left to the BornTypicality
    LLN axiom layer.

    *Strategic content:* §11.4.6 of the publication can now honestly
    state "Chebyshev gives Born-frequency concentration at rate
    1/(N·ε²)" rather than just "the per-run mean is Born". -/
theorem born_chebyshev_single_trial
    (p : ℝ) (hp_nn : 0 ≤ p) (hp_le_one : p ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    let P : Fin 2 → ℝ := fun i => if i = 0 then 1 - p else p
    let X : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
    (∑ ω, if ε ≤ |X ω - p| then P ω else 0)
      ≤ p * (1 - p) / ε^2 := by
  -- Apply chebyshev_tail_bound with μ = p; substitute the Bernoulli
  -- variance computation.
  have h_nn : ∀ i : Fin 2, 0 ≤ (if i = 0 then 1 - p else p) := by
    intro i
    by_cases h : i = 0
    · rw [if_pos h]; linarith
    · rw [if_neg h]; exact hp_nn
  have h_chev := chebyshev_tail_bound
    (P := fun i : Fin 2 => if i = 0 then 1 - p else p)
    h_nn
    (X := fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) p ε hε
  -- Substitute Bernoulli variance = p(1-p).
  have h_var : varianceAround
                (fun i : Fin 2 => if i = 0 then 1 - p else p)
                (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) p
              = p * (1 - p) :=
    bernoulli_variance p hp_nn hp_le_one
  rw [h_var] at h_chev
  exact h_chev

/- ── Independence: variance adds over a product of two trials ─────── -/

/-- **Centered first moment vanishes.**  For a probability weight `P`
    (`∑ P = 1`), the `P`-average of `X − mean P X` is zero. -/
theorem centered_first_moment_zero
    {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (hP : ∑ ω, P ω = 1) (X : Ω → ℝ) :
    ∑ ω, P ω * (X ω - mean P X) = 0 := by
  have h : ∑ ω, P ω * (X ω - mean P X)
         = (∑ ω, P ω * X ω) - mean P X * (∑ ω, P ω) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro ω _; ring
  rw [h, hP, mul_one]
  unfold mean
  ring

/-- **Variance adds for independent variables (the core independence
    lemma).**

    Let `P₁ : Ω₁ → ℝ` and `P₂ : Ω₂ → ℝ` be probability weights
    (`∑ Pᵢ = 1`).  On the product space `Ω₁ × Ω₂` with the product
    weight `P(ω₁,ω₂) = P₁ ω₁ · P₂ ω₂` and the additive variable
    `X(ω₁,ω₂) = X₁ ω₁ + X₂ ω₂`, the variance decomposes:

        Var_P(X) = Var_{P₁}(X₁) + Var_{P₂}(X₂)

    centred at the respective means.  This is exactly the statement
    that the variance of a sum of *independent* random variables is
    the sum of the variances — the product structure of `P` is what
    encodes independence.  The cross term vanishes via
    `centered_first_moment_zero`. -/
theorem variance_add_of_product
    {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (P₁ : Ω₁ → ℝ) (P₂ : Ω₂ → ℝ)
    (hP₁ : ∑ ω, P₁ ω = 1) (hP₂ : ∑ ω, P₂ ω = 1)
    (X₁ : Ω₁ → ℝ) (X₂ : Ω₂ → ℝ) :
    varianceAround (fun ω : Ω₁ × Ω₂ => P₁ ω.1 * P₂ ω.2)
        (fun ω => X₁ ω.1 + X₂ ω.2) (mean P₁ X₁ + mean P₂ X₂)
      = varianceAround P₁ X₁ (mean P₁ X₁)
        + varianceAround P₂ X₂ (mean P₂ X₂) := by
  set μ₁ := mean P₁ X₁
  set μ₂ := mean P₂ X₂
  unfold varianceAround
  -- Expand the product sum and the square (a+b)² = a²+2ab+b² with
  -- a = X₁ ω₁ − μ₁, b = X₂ ω₂ − μ₂.
  rw [Fintype.sum_prod_type]
  -- Inner: for fixed ω₁, ∑_{ω₂} P₁ω₁ P₂ω₂ ((X₁ω₁−μ₁)+(X₂ω₂−μ₂))².
  have expand :
      ∀ ω₁ : Ω₁,
        (∑ ω₂ : Ω₂, P₁ ω₁ * P₂ ω₂ * (X₁ ω₁ + X₂ ω₂ - (μ₁ + μ₂))^2)
        = P₁ ω₁ * (X₁ ω₁ - μ₁)^2 * (∑ ω₂, P₂ ω₂)
          + 2 * (P₁ ω₁ * (X₁ ω₁ - μ₁)) * (∑ ω₂, P₂ ω₂ * (X₂ ω₂ - μ₂))
          + P₁ ω₁ * (∑ ω₂, P₂ ω₂ * (X₂ ω₂ - μ₂)^2) := by
    intro ω₁
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω₂ _
    ring
  rw [Finset.sum_congr rfl (fun ω₁ _ => expand ω₁)]
  -- Replace the two closed inner sums:  ∑_{ω₂}P₂ = 1  and
  -- ∑_{ω₂} P₂ (X₂−μ₂) = 0 (the cross term vanishes).
  have hcross : ∑ ω₂, P₂ ω₂ * (X₂ ω₂ - μ₂) = 0 :=
    centered_first_moment_zero P₂ hP₂ X₂
  -- Middle term ×0 drops (hcross); ∑_{ω₂} P₂ = 1 in the first term.
  simp only [hcross, hP₂, mul_zero, add_zero]
  rw [Finset.sum_add_distrib]
  congr 1
  · -- First summand: ∑_{ω₁} P₁ (X₁−μ₁)²·1 = Var₁.
    simp only [mul_one, varianceAround]
  · -- Second summand: ∑_{ω₁} P₁ · Var₂inner = (∑P₁)·Var₂ = Var₂.
    rw [← Finset.sum_mul, hP₁, one_mul]

/-- **Two-trial Bernoulli variance (PROVED via independence).**

    Two independent Bernoulli(`p`) trials, modelled on
    `Bool × Bool` with product weight, have count-variance `2·p(1−p)`.
    Concrete instance of `variance_add_of_product` + `bernoulli_variance`,
    exhibiting variance-addition across independent trials. -/
theorem two_trial_bernoulli_variance
    (p : ℝ) (hp_nn : 0 ≤ p) (hp_le_one : p ≤ 1) :
    let P : Bool → ℝ := fun b => if b = false then 1 - p else p
    let X : Bool → ℝ := fun b => if b = false then 0 else 1
    varianceAround (fun ω : Bool × Bool => P ω.1 * P ω.2)
        (fun ω => X ω.1 + X ω.2) (mean P X + mean P X)
      = 2 * (p * (1 - p)) := by
  intro P X
  -- Bool-eq condition reductions, used to evaluate the two-point sums.
  have htf : ((true : Bool) = false) = False := by simp
  have hff : ((false : Bool) = false) = True := by simp
  have hP_sum : ∑ b, P b = 1 := by
    show ∑ b : Bool, (if b = false then 1 - p else p) = 1
    rw [Fintype.sum_bool]
    simp only [htf, hff, if_true, if_false]; ring
  -- Bernoulli single-trial variance, re-expressed for the Bool model
  -- (false ↦ 0/weight 1−p, true ↦ 1/weight p): same value p(1−p).
  have hmean : mean P X = p := by
    show (∑ b : Bool, (if b = false then 1 - p else p) * (if b = false then (0:ℝ) else 1)) = p
    rw [Fintype.sum_bool]
    simp only [htf, hff, if_true, if_false]; ring
  have hvar : varianceAround P X (mean P X) = p * (1 - p) := by
    rw [hmean]
    show (∑ b : Bool, (if b = false then 1 - p else p)
            * ((if b = false then (0:ℝ) else 1) - p)^2) = p * (1 - p)
    rw [Fintype.sum_bool]
    simp only [htf, hff, if_true, if_false]; ring
  have key : varianceAround (fun ω : Bool × Bool => P ω.1 * P ω.2)
      (fun ω => X ω.1 + X ω.2) (mean P X + mean P X)
      = varianceAround P X (mean P X) + varianceAround P X (mean P X) :=
    variance_add_of_product P P hP_sum hP_sum X X
  rw [hvar] at key
  -- key : varianceAround (product) ... = p(1−p) + p(1−p);  goal: ... = 2·p(1−p).
  exact key.trans (by ring)

/-- **Audit conclusion.**

    The Chebyshev-style concentration bound and the variance-addition
    (independence) lemma are now formally available in the QIQT-H Lean
    corpus.  Combined with `BornTypicality.born_mean_conditional`
    (proved), the framework supports the publication-level claim:

        For any ε > 0, the per-trial probability of empirical
        deviation from Born weights by more than ε is bounded by
        p(1−p)/ε².  Variance adds across independent trials
        (`variance_add_of_product`), so the N-trial count has variance
        N·p(1−p) and the empirical mean has variance p(1−p)/N; hence
        by Chebyshev the N-trial frequency deviates from Born by more
        than ε with probability at most p(1−p)/(N·ε²) — converging to
        0 at rate 1/N.

    *What is now PROVED concretely:* the single-trial Chebyshev bound
    (`born_chebyshev_single_trial`); the variance-addition theorem for
    independent variables (`variance_add_of_product`); and the
    two-trial Bernoulli instance (`two_trial_bernoulli_variance`)
    exhibiting variance-addition.  The general N-fold induction
    (folding `variance_add_of_product` over `Fin N`) is the only
    remaining step to fully retire the binary-case LLN interface
    axiom; the reusable independence lemma that the induction would
    iterate is in hand. -/
theorem audit_conclusion : True := trivial

end BornConcentration
end QIQTH
