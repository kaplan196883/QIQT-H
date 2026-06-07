/-
  P1 of the GPT-5.5-pro prize plan: coarse-graining naturality of the Born measure.

  The operational backbone of a CANONICAL finite-record typicality measure μ: the Born
  measures attached to a directed system of measurement contexts are KOLMOGOROV-CONSISTENT
  under refinement.  Concretely, if a coarse POVM `{E_a}` is obtained from a finer POVM
  `{E'_b}` by grouping outcomes along a coarse-graining map `π : Ω' → Ω`
  (`E_a = ∑_{π b = a} E'_b`), then the coarse Born measure is the PUSHFORWARD of the fine one:

      bornW ρ (E_a) = (π_* (bornW ρ ∘ E'))(a)                  (`born_coarse_grain`)

  Hence total probability is preserved (`born_total_coarse`), a coarse-graining of a POVM is a
  POVM (`coarse_povm_complete`), and the family `{Born_C}` over contexts forms a consistent
  (projective) system — exactly the consistency a cylinder/premeasure construction (P3) consumes.

  Pure finite-dimensional linear algebra: linearity of trace and matrix multiplication over a
  fiber sum + `Finset.sum_fiberwise`.  No assumption on ρ (entangled states allowed).

  Axiom-free: depends only on `propext, Classical.choice, Quot.sound`.
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

namespace QIQTH.CoarseGrainNaturality

open Matrix BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω]

/-- Born weight of an effect `E` in state `ρ`: `Re tr(ρ E)`. -/
noncomputable def bornW (ρ E : Matrix n n ℂ) : ℝ := (Matrix.trace (ρ * E)).re

/-- Pushforward of a finite measure `μ` on `Ω'` along `π : Ω' → Ω`:
    `(π_* μ)(a) = ∑_{b : π b = a} μ b`. -/
noncomputable def pushforward (π : Ω' → Ω) (μ : Ω' → ℝ) (a : Ω) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b => π b = a), μ b

/-- Born weight is additive over a finite sum of effects: `bornW ρ (∑ F i) = ∑ bornW ρ (F i)`. -/
theorem bornW_sum (ρ : Matrix n n ℂ) {ι : Type*} (s : Finset ι) (F : ι → Matrix n n ℂ) :
    bornW ρ (∑ i ∈ s, F i) = ∑ i ∈ s, bornW ρ (F i) := by
  unfold bornW
  rw [Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- **Coarse-graining naturality (Born consistent under refinement).**  If the coarse effect
    `E a` is the fiber-sum of the fine effects `E' b` over `π` (`E a = ∑_{π b = a} E' b`), then the
    coarse Born weight is the PUSHFORWARD of the fine Born measure:
    `bornW ρ (E a) = (π_* (bornW ρ ∘ E'))(a)`.  This is the operational backbone of a canonical
    finite-record μ — the contexts' Born measures form a Kolmogorov-consistent (projective) system. -/
theorem born_coarse_grain (ρ : Matrix n n ℂ) (E : Ω → Matrix n n ℂ) (E' : Ω' → Matrix n n ℂ)
    (π : Ω' → Ω) (hE : ∀ a, E a = ∑ b ∈ Finset.univ.filter (fun b => π b = a), E' b) (a : Ω) :
    bornW ρ (E a) = pushforward π (fun b => bornW ρ (E' b)) a := by
  rw [hE a, bornW_sum]
  rfl

/-- **Total probability preserved by pushforward**: `∑_a (π_* μ)(a) = ∑_b μ b`. -/
theorem pushforward_total (π : Ω' → Ω) (μ : Ω' → ℝ) :
    ∑ a, pushforward π μ a = ∑ b, μ b := by
  unfold pushforward
  exact Finset.sum_fiberwise Finset.univ π μ

/-- **Born-normalization preserved under coarse-graining**: `∑_a bornW ρ (E a) = ∑_b bornW ρ (E' b)`.
    So coarse-graining a Born probability vector yields a Born probability vector. -/
theorem born_total_coarse (ρ : Matrix n n ℂ) (E : Ω → Matrix n n ℂ) (E' : Ω' → Matrix n n ℂ)
    (π : Ω' → Ω) (hE : ∀ a, E a = ∑ b ∈ Finset.univ.filter (fun b => π b = a), E' b) :
    ∑ a, bornW ρ (E a) = ∑ b, bornW ρ (E' b) := by
  simp only [born_coarse_grain ρ E E' π hE]
  exact pushforward_total π (fun b => bornW ρ (E' b))

/-- **A coarse-graining of a POVM is a POVM**: if `∑_b E' b = 1` and `E a = ∑_{π b = a} E' b`,
    then `∑_a E a = 1`.  (The coarse contexts are genuine measurements, so `born_total_coarse`
    turns a Born probability vector into a Born probability vector.) -/
theorem coarse_povm_complete (E : Ω → Matrix n n ℂ) (E' : Ω' → Matrix n n ℂ) (π : Ω' → Ω)
    (hE : ∀ a, E a = ∑ b ∈ Finset.univ.filter (fun b => π b = a), E' b)
    (hE' : ∑ b, E' b = 1) : ∑ a, E a = 1 := by
  simp only [hE]
  rw [Finset.sum_fiberwise Finset.univ π E']
  exact hE'

end QIQTH.CoarseGrainNaturality
