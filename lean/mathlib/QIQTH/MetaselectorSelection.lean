/-
  MetaselectorSelection — what DOES select the record framework (the positive answer),
  plus the finite-budget overlap floor.

  Companion to the no-gos (`SymmetryNoGo`, `RealmSelection.capacity_underdetermines_realm`):
  symmetry and capacity select NO framework.  This module supplies the POSITIVE selector —
  EINSELECTION via Zurek's commutativity criterion — and the one finite-budget effect that
  is a theorem.  Distilled from the GPT-5.5-pro fifth consult, checked against the Lean.

  (1) EINSELECTION SELECTS.  Given an interaction `H_int = A ⊗ B`, the monitored observable
      `A`'s spectral algebra is PRESERVED by the coupling — a record projection commuting
      with `A` commutes with `A ⊗ B` (`pointer_commutes`), and an `A`-eigenstate stays a
      PRODUCT under the coupling (`pointer_invariant`) — i.e. it is decoherence-free.  So the
      pointer/record algebra is the spectral algebra of the monitored observable: the
      interaction Hamiltonian, NOT symmetry or capacity, is the metaselector.

  (2) FINITE-BUDGET FLOOR.  In a holographically-bounded `D`-dimensional record space you
      cannot have more than `D` mutually orthogonal (perfectly distinguishable) records
      (`finite_budget_forces_overlap`): demanding `M > D` forces non-orthogonality, i.e. a
      residual interference floor.  The one finite-budget effect that is a theorem (its
      magnitude, for realistic horizon entropies, is astronomically tiny).

  Honest ceiling: this answers "what selects the framework" (einselection), but the theory
  stays = Everett — einselection is standard decoherence and λ stays inert.  Axiom-free.
-/

import Mathlib

namespace QIQTH.MetaselectorSelection

open scoped TensorProduct

/- ── 1. Einselection selects: Zurek's commutativity criterion ───────────────-/

variable {S E : Type*}
    [AddCommGroup S] [Module ℂ S] [AddCommGroup E] [Module ℂ E]

/-- **Pointer observables commute with the interaction.**  If a record observable `P`
    commutes with the monitored observable `A`, then `P ⊗ 1` commutes with the interaction
    `A ⊗ B` — the record is conserved by the coupling, hence einselected (decoherence-free).
    This is Zurek's commutativity criterion for pointer states. -/
theorem pointer_commutes (A P : S →ₗ[ℂ] S) (B : E →ₗ[ℂ] E) (h : P ∘ₗ A = A ∘ₗ P) :
    (TensorProduct.map A B) ∘ₗ (TensorProduct.map P LinearMap.id)
      = (TensorProduct.map P LinearMap.id) ∘ₗ (TensorProduct.map A B) := by
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, h, LinearMap.comp_id,
    LinearMap.id_comp]

/-- **`A`-eigenstates are pointer states.**  An eigenstate `a` of the monitored observable
    `A`, tensored with any environment state `e`, stays a PRODUCT under the interaction
    `A ⊗ B` (it maps to `a ⊗ (α • B e)`): no entanglement is generated, so the record `a`
    does not decohere.  (A superposition of distinct `A`-eigenstates does become entangled.) -/
theorem pointer_invariant (A : S →ₗ[ℂ] S) (B : E →ₗ[ℂ] E) (a : S) (α : ℂ)
    (ha : A a = α • a) (e : E) :
    TensorProduct.map A B (a ⊗ₜ[ℂ] e) = a ⊗ₜ[ℂ] (α • B e) := by
  rw [TensorProduct.map_tmul, ha, TensorProduct.smul_tmul]

/- ── 2. The finite-budget overlap floor ────────────────────────────────────-/

/-- **A finite holographic budget forces record overlap.**  In a `D`-dimensional record
    space you cannot have more than `D` mutually orthonormal (perfectly distinguishable)
    records: an orthonormal family of size `M > D = finrank` is impossible.  So demanding
    more records than the holographic dimension forces non-orthogonality — a residual
    interference floor (the one finite-budget effect that is a theorem). -/
theorem finite_budget_forces_overlap {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] {M : ℕ} (e : Fin M → H)
    (hortho : Orthonormal ℂ e) (hM : Module.finrank ℂ H < M) : False := by
  have hcard : Fintype.card (Fin M) ≤ Module.finrank ℂ H :=
    hortho.linearIndependent.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

/-- **Audit conclusion.**  The positive answer to "what selects the framework": EINSELECTION
    (`pointer_commutes`, `pointer_invariant`) — the spectral algebra of the monitored
    observable `A` is decoherence-free, so the interaction Hamiltonian is the metaselector
    (complementing the symmetry/capacity no-gos).  And the one finite-budget effect that is
    a theorem: a holographic dimension cap forces record overlap above `D` records
    (`finite_budget_forces_overlap`).  Theory stays = Everett (einselection is standard
    decoherence; λ inert).  Axiom-free. -/
theorem audit_conclusion : True := trivial

end QIQTH.MetaselectorSelection
