/-
  General bipartite no-signaling for an ARBITRARY (possibly entangled) state.

  Strengthens the product-state no-signaling of `FreeFieldNet`/`LorentzSelection`
  (which a foundations reader rightly discounts as "toy no-signaling") to the
  operationally honest statement: for ANY finite-dimensional bipartite density
  matrix `ρ` on `H₁ ⊗ H₂` — entangled or not — a local outcome's marginal
  probability does NOT depend on which remote POVM `{F_b}` is performed.

  This is the genuine no-signaling content: with a local effect `E` on `H₁` and a
  remote POVM `{F_b}` on `H₂` summing to `1`,

      ∑_b tr(ρ · (E ⊗ F_b)) = tr(ρ · (E ⊗ 1))                 (`bipartite_no_signaling`)

  so the local marginal is the SAME for two different remote POVMs
  (`local_marginal_indep_remote`).  Pure finite-dimensional linear algebra:
  Kronecker bilinearity (`E ⊗ (∑_b F_b) = ∑_b E ⊗ F_b`) + linearity of trace and
  matrix multiplication + POVM completeness `∑_b F_b = 1`.  No product/separability
  assumption on `ρ`.

  Axiom-free: depends only on `propext, Classical.choice, Quot.sound`.
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace QIQTH.NoSignalingGeneral

open Matrix BigOperators
open scoped Kronecker

variable {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
variable {β : Type*} [Fintype β]

/-- Kronecker is additive over a finite sum in the right factor:
    `E ⊗ (∑_b F_b) = ∑_b (E ⊗ F_b)`. -/
theorem kronecker_sum_right (E : Matrix d₁ d₁ ℂ) (F : β → Matrix d₂ d₂ ℂ) (s : Finset β) :
    ∑ b ∈ s, (E ⊗ₖ F b) = E ⊗ₖ (∑ b ∈ s, F b) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, kronecker_add, ih]

/-- **General bipartite no-signaling (arbitrary state).**  For ANY bipartite density
    matrix `ρ` on `H₁ ⊗ H₂` (entangled or not), any local effect `E` on `H₁`, and any
    remote POVM `{F_b}` on `H₂` with `∑_b F_b = 1`:

        ∑_b tr(ρ · (E ⊗ F_b)) = tr(ρ · (E ⊗ 1)).

    The local outcome's marginal probability is computed from `E` alone — it does not
    see the remote POVM at all.  No separability assumption on `ρ`. -/
theorem bipartite_no_signaling
    (ρ : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (E : Matrix d₁ d₁ ℂ) (F : β → Matrix d₂ d₂ ℂ)
    (hF : ∑ b, F b = 1) :
    ∑ b, Matrix.trace (ρ * (E ⊗ₖ F b)) = Matrix.trace (ρ * (E ⊗ₖ (1 : Matrix d₂ d₂ ℂ))) := by
  rw [← Matrix.trace_sum, ← Finset.mul_sum, kronecker_sum_right E F Finset.univ, hF]

/-- **No-signaling, operational form.**  Two different remote POVMs `{F_b}` and `{F'_c}`
    (each summing to `1`) yield the SAME local marginal for every local effect `E` and
    every (possibly entangled) bipartite state `ρ`.  Hence no choice of remote
    measurement can change the local statistics — Bob cannot signal to Alice. -/
theorem local_marginal_indep_remote
    {γ : Type*} [Fintype γ]
    (ρ : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (E : Matrix d₁ d₁ ℂ)
    (F : β → Matrix d₂ d₂ ℂ) (F' : γ → Matrix d₂ d₂ ℂ)
    (hF : ∑ b, F b = 1) (hF' : ∑ c, F' c = 1) :
    ∑ b, Matrix.trace (ρ * (E ⊗ₖ F b)) = ∑ c, Matrix.trace (ρ * (E ⊗ₖ F' c)) := by
  rw [bipartite_no_signaling ρ E F hF, bipartite_no_signaling ρ E F' hF']

/-- **Real-valued probability form.**  The local marginal probability
    `∑_b Re tr(ρ (E ⊗ F_b))` equals `Re tr(ρ (E ⊗ 1))`, independent of the remote POVM.
    (For a state `ρ` and effect `E ⊗ F_b` the Born weight is the real part of the trace;
    this packages `bipartite_no_signaling` for the typicality/probability layer.) -/
theorem bipartite_no_signaling_re
    (ρ : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (E : Matrix d₁ d₁ ℂ) (F : β → Matrix d₂ d₂ ℂ)
    (hF : ∑ b, F b = 1) :
    ∑ b, (Matrix.trace (ρ * (E ⊗ₖ F b))).re
      = (Matrix.trace (ρ * (E ⊗ₖ (1 : Matrix d₂ d₂ ℂ)))).re := by
  rw [← Complex.re_sum, bipartite_no_signaling ρ E F hF]

end QIQTH.NoSignalingGeneral
