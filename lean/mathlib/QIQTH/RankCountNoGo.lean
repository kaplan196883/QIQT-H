/-
RankCountNoGo.lean — the rank-count no-go (GPT-5.5 consult, 2026-06-13).

The Born residual is "the Born-agnostic microstate multiplicity of branch k is ∝ w_k". We asked whether any
decoherence / einselection / quantum-Darwinism mechanism delivers that from the dynamics. The verdict was a
clean impossibility:

  The einselected record multiplicity of outcome k is the dimension / rank of the orthogonal environment
  record subspace it occupies. That rank is fixed by the interaction, bath size and coarse-graining — it is
  AMPLITUDE-INDEPENDENT: scaling a branch by a nonzero scalar c_k changes its norm/trace but NOT the support
  rank. So multiplicity is discrete and state-independent, while the Born weight ‖P_kψ‖² is continuous and
  state-dependent. They cannot be proportional on any open set of states.

We machine-check exactly this. A record-multiplicity rule assigns probabilities `n_k / Σ n_j` from counts
`n : K → ℕ` fixed by the dynamics; it does not see the amplitudes. Born assigns `w_k / Σ w_j`. The no-go:
no multiplicity rule equals Born, because the former is state-independent and the latter is not.

Consequence (the honest one): Path A — deriving the weight-encoding from decoherence dynamics — is closed.
Born requires an irreducible Hilbert-typicality axiom (`μ(k)=⟨Ψ|P_k|Ψ⟩`), the thinnest no-collapse posit,
which Gleason then makes essentially unique. This is the Path-B guardrail.

HONEST SCOPE: finite; no `sorry`, no project axioms.
-/
import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace QIQTH.RankCountNoGo

variable {K : Type*} [Fintype K]

/-- A **record-multiplicity rule**: the probability of outcome `k` from the (amplitude-independent) count
`n k` of orthogonal environment record-microstates carrying `k` — `p_k = n_k / Σ_j n_j`. It is a function of
the dynamics-fixed record counts only; it does **not** depend on the branch amplitudes. -/
noncomputable def multRule (n : K → ℕ) (k : K) : ℝ := (n k : ℝ) / ∑ j, (n j : ℝ)

/-- The **Born rule** from amplitude weights `w_k = ‖P_k ψ‖²`: `p_k = w_k / Σ_j w_j`. -/
noncomputable def bornW (w : K → ℝ) (k : K) : ℝ := w k / ∑ j, w j

/-- **The core obstruction (state-independence vs state-dependence).** A multiplicity rule takes no amplitude
argument, so its value at `k` is one fixed number; it therefore cannot agree with Born at `k` for two states
`w, w'` whose Born values at `k` differ. (Pro's rank-vs-amplitude obstruction, in its essential form.) -/
theorem multRule_ne_born_of_differs (n : K → ℕ) (w w' : K → ℝ) (k : K)
    (h : bornW w k ≠ bornW w' k) :
    multRule n k ≠ bornW w k ∨ multRule n k ≠ bornW w' k := by
  by_contra hcon
  simp only [not_or, ne_eq, not_not] at hcon
  exact h (hcon.1.symm.trans hcon.2)

/-- Two two-outcome amplitude profiles whose Born distributions differ at outcome `0`:
equal weights give `1/2`, the `(1,2)` profile gives `1/3`. -/
theorem bornW_differs_two : bornW (fun _ : Fin 2 => (1 : ℝ)) 0 ≠ bornW ![(1 : ℝ), 2] 0 := by
  simp only [bornW, Fin.sum_univ_two]
  norm_num

/-- **Rank-count no-go.** No amplitude-independent record-multiplicity rule equals the Born rule: for every
choice of record counts `n`, there is a pair of states on which the multiplicity rule disagrees with Born.
Multiplicity is state-independent; Born is state-dependent. Hence decoherence cannot turn amplitude into
count, and Born needs an irreducible Hilbert-typicality axiom. -/
theorem no_multiplicity_rule_is_born :
    ¬ ∃ n : Fin 2 → ℕ, ∀ (w : Fin 2 → ℝ) (k : Fin 2), multRule n k = bornW w k := by
  rintro ⟨n, hn⟩
  exact bornW_differs_two ((hn (fun _ => 1) 0).symm.trans (hn ![1, 2] 0))

end QIQTH.RankCountNoGo
