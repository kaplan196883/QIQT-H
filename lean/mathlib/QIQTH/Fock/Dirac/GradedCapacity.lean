/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E7 — graded regional capacity (the charge/parity block decomposition)

For the electron, the regional observable algebra is **graded** by the superselected charge/parity:
the even / U(1)-invariant regional algebra decomposes into sectors, `𝒜_R ≃ ⊕_q M_{n_q}(ℂ)` (per
ELECTRON_FIELD_PLAN §7 and GPT-5.5-pro's block form).  A state on such an algebra is a probability
distribution `p_q` over the sectors together with a within-sector state `w_q` of each block, and its von
Neumann / record entropy decomposes as the **chain rule**
```
   S(ρ_R)  =  H(p)  +  Σ_q  p_q · S(w_q),
```
the **mixing entropy of the sector distribution** plus the **average within-sector entropy**.  This
module formalizes that decomposition (`gradedShannon_chain_rule`) and the resulting **graded capacity
bound** (`gradedShannon_capacity_le`): each block contributes at most `log n_q` (its own capacity, from
the per-sector `shannon_le_log_card` / the CAR `S ≤ log dim` of E3), so
```
   S(ρ_R)  ≤  H(p)  +  Σ_q  p_q · log n_q.
```
So the finite-capacity bound passes to the charge/parity-graded regional algebra — the algebra to which,
per §0, the electron's records and capacity attach (`QIQTH/Fock/Dirac/EvenObservables.lean`).

Built on `Real.negMulLog_mul` (the entropy chain identity `negMulLog(xy) = y·negMulLog x + x·negMulLog y`)
and the project's `RecordContract.shannon_le_log_card`.  Axiom-free (standard
`propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.

HONEST scope (§7): this lands the chain-rule decomposition and the per-block-summed bound
`≤ H(p) + Σ_q p_q log n_q`.  The further collapse to a single `log(Σ_q n_q) = log dim(⊕_q M_{n_q})`
(maximally-mixed over the whole graded algebra) needs a Jensen/log-sum step over the sector weights and
is the next E7 sub-item.  Free Dirac only.
-/
import QIQTH.RecordContract

namespace QIQTH.Fock.Dirac

open Real
open scoped BigOperators

variable {Q : Type*} [Fintype Q] {I : Q → Type*} [∀ q, Fintype (I q)]

/-- **The graded entropy chain rule.**  For a sector distribution `p` over `Q` and a within-sector state
`w q` on each sector `I q` (each normalized, `∑_i w q i = 1`), the joint record entropy decomposes as
the sector mixing entropy plus the average within-sector entropy:
`Σ_q Σ_i negMulLog(p_q · w_{q,i}) = Σ_q negMulLog(p_q) + Σ_q p_q · (Σ_i negMulLog(w_{q,i}))`,
i.e. `S = H(p) + Σ_q p_q S(w_q)`. -/
theorem gradedShannon_chain_rule (p : Q → ℝ) (w : ∀ q, I q → ℝ) (hw : ∀ q, ∑ i, w q i = 1) :
    ∑ q, ∑ i, Real.negMulLog (p q * w q i)
      = (∑ q, Real.negMulLog (p q)) + ∑ q, p q * ∑ i, Real.negMulLog (w q i) := by
  have step : ∀ q, ∑ i, Real.negMulLog (p q * w q i)
      = Real.negMulLog (p q) + p q * ∑ i, Real.negMulLog (w q i) := by
    intro q
    calc ∑ i, Real.negMulLog (p q * w q i)
        = ∑ i, (w q i * Real.negMulLog (p q) + p q * Real.negMulLog (w q i)) := by
          simp_rw [Real.negMulLog_mul]
      _ = (∑ i, w q i) * Real.negMulLog (p q) + p q * ∑ i, Real.negMulLog (w q i) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ = Real.negMulLog (p q) + p q * ∑ i, Real.negMulLog (w q i) := by
          rw [hw q, one_mul]
  rw [Finset.sum_congr rfl (fun q _ => step q), Finset.sum_add_distrib]

/-- **The graded capacity bound.**  Each sector contributes at most `log n_q` (its own capacity, the
per-block `shannon_le_log_card`), so the graded regional record entropy is bounded by the mixing entropy
plus the average sector log-capacity: `S(ρ_R) ≤ H(p) + Σ_q p_q · log n_q`.  The finite-capacity bound
passes to the charge/parity-graded regional algebra `⊕_q M_{n_q}`. -/
theorem gradedShannon_capacity_le (p : Q → ℝ) (w : ∀ q, I q → ℝ)
    (hp : ∀ q, 0 ≤ p q) (hw0 : ∀ q i, 0 ≤ w q i) (hw : ∀ q, ∑ i, w q i = 1) :
    ∑ q, ∑ i, Real.negMulLog (p q * w q i)
      ≤ (∑ q, Real.negMulLog (p q)) + ∑ q, p q * Real.log (Fintype.card (I q)) := by
  rw [gradedShannon_chain_rule p w hw, add_le_add_iff_left]
  apply Finset.sum_le_sum
  intro q _
  refine mul_le_mul_of_nonneg_left ?_ (hp q)
  rw [← QIQTH.RecordContract.shannon_eq_sum_negMulLog]
  exact QIQTH.RecordContract.shannon_le_log_card (w q) (hw0 q) (hw q)

end QIQTH.Fock.Dirac
