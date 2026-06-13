/-
Envariance.lean — Zurek's envariance as the "equal amplitudes ⇒ equal probabilities" half of Born.

The Born derivation has two halves. `SelectionDynamics.born_from_uniform` handles UNEQUAL amplitudes by
fine-graining outcome `k` into `M·w_k` equal sub-records over a Born-agnostic uniform measure. The missing
companion is the EQUAL-amplitude case: why two branches of equal weight get equal probability. Zurek's
**envariance** answers it with a pure symmetry argument: if a system swap `a ↔ b` is *undone* by a remote
(environment) action that leaves the local readout's typicality measure invariant, then the two outcomes
must carry equal selection probability — with NO appeal to Born.

We machine-check exactly this: a μ-preserving bijection `σ` of microstates that implements the `a ↔ b`
label swap on the readout forces `marg μ sel a = marg μ sel b`. This is the no-signaling/equivariance
machinery (`SelectorRefinement.equivariant_marg_invariant`) specialised to a swap — the envariance core.
Composing the two halves gives Born on the rational grid from a Born-agnostic measure, axiom-free.

HONEST SCOPE: finite; no `sorry`, no project axioms. The residual is unchanged: that the actual `(Φ,λ)`
dynamics furnishes such a μ-preserving swap for genuinely equal-amplitude branches (the envariance
symmetry of the global state) — established physically by Zurek, not derived here.
-/
import QIQTH.SelectorRefinement

open scoped BigOperators

namespace QIQTH.Envariance

open QIQTH.SelectorRefinement

variable {Ω K : Type*} [Fintype Ω] [DecidableEq K]

/-- **Envariance ⇒ equal marginals (Zurek's equal-amplitude Born).** If a bijection `σ` of the microstate
space preserves the typicality measure `μ` and implements the `a ↔ b` swap on the local readout
(`sel (σ ω) = swap a b (sel ω)`), then outcomes `a` and `b` receive equal selection probability:
`marg μ sel a = marg μ sel b`. A system swap undone by a μ-preserving remote action cannot change the
local marginal — so equal-amplitude (swap-symmetric) branches are equiprobable, with no Born assumption. -/
theorem envariance_equal_marg
    (μ : Ω → ℝ) (sel : Ω → K) (σ : Ω ≃ Ω) (a b : K)
    (hμ : ∀ ω, μ (σ ω) = μ ω)
    (hswap : ∀ ω, sel (σ ω) = Equiv.swap a b (sel ω)) :
    marg μ sel a = marg μ sel b := by
  simp only [marg]
  rw [← Equiv.sum_comp σ (fun ω => if sel ω = a then μ ω else 0)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [hswap ω, hμ ω]
  simp only [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

/-- **Envariance forces the uniform measure.** If the typicality measure `μ` is invariant under *every*
transposition of the (equal-amplitude) microstates — total envariance — then it is constant:
`μ a = μ b` for all `a, b`. This is the missing justification for `SelectionDynamics.born_from_uniform`,
which had to *assume* a uniform Born-agnostic measure: here uniformity is *derived* from the swap-symmetry
of equal-amplitude branches. (Specialise `envariance_equal_marg` to the readout `id` and the swap `σ = (a b)`,
where `marg μ id a = μ a`.) -/
theorem envariance_forces_uniform [DecidableEq Ω] (μ : Ω → ℝ)
    (hsym : ∀ a b : Ω, ∀ ω, μ (Equiv.swap a b ω) = μ ω) (a b : Ω) :
    μ a = μ b := by
  have key : ∀ c : Ω, marg μ (id : Ω → Ω) c = μ c := by
    intro c
    simp only [marg, id_eq]
    exact (Finset.sum_ite_eq' Finset.univ c μ).trans (if_pos (Finset.mem_univ c))
  have h := envariance_equal_marg μ (id : Ω → Ω) (Equiv.swap a b) a b (hsym a b) (fun _ => rfl)
  rwa [key a, key b] at h

end QIQTH.Envariance
