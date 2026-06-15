/-
  ContinuumLambdaField — the continuum λ-persistence at the GENUINE FREE-FIELD
  level (the payoff of the Stage-4 Γ-capstone).

  With `Γ(Δ^{it}) = secondQuantModCLM` now a unitary one-parameter group of bounded
  operators on the Fock Hilbert space (`SecondQuantCLM.lean`: `_mul`, `_zero`,
  `_adjoint`), the `ContinuumLambda` `Ad(Δ^{it})` machinery replays verbatim at the
  field level:

    * `modAutFock S t A = Γ(Δ^{it}) A Γ(Δ^{it})⋆` — the FREE-FIELD modular
      automorphism `σ_t = Ad(Γ(Δ^{it}))`, a one-parameter group of unital
      ⋆-automorphisms (`modAutFock_zero/_add/_one/_mul/_star`).
    * `modAutFock_fixes_iff_commute` — the **field-level Takesaki criterion**.
    * `dephaseFock_modAutFock_commute` — **field-level persistence**: the
      decoherence map `E(A)=Σ Pₐ A Pₐ` commutes with the second-quantized modular
      flow `σ_t` for every `t`.  A dephased free-field record state stays dephased
      under the genuine free-field modular dynamics.

  This carries the continuum λ-persistence from the one-particle `Δ^{it}` all the
  way to the second-quantized free field.  Axiom-free.
-/

import QIQTH.Fock.SecondQuantCLM

namespace QIQTH.Fock

open QIQTH.StandardSubspaceModular

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- ── The unitary group as a two-sided inverse / star pair ───────────────────-/

theorem secondQuantModCLM_mul_neg (S : StandardSubspace H) (t : ℝ) :
    secondQuantModCLM S t * secondQuantModCLM S (-t) = 1 := by
  rw [secondQuantModCLM_mul, add_neg_cancel, secondQuantModCLM_zero]

theorem secondQuantModCLM_neg_mul (S : StandardSubspace H) (t : ℝ) :
    secondQuantModCLM S (-t) * secondQuantModCLM S t = 1 := by
  rw [secondQuantModCLM_mul, neg_add_cancel, secondQuantModCLM_zero]

theorem secondQuantModCLM_star (S : StandardSubspace H) (t : ℝ) :
    star (secondQuantModCLM S t) = secondQuantModCLM S (-t) := by
  rw [ContinuousLinearMap.star_eq_adjoint, secondQuantModCLM_adjoint]

/- ── The free-field modular automorphism σ_t = Ad(Γ(Δ^{it})) ────────────────-/

/-- The free-field modular automorphism `σ_t(A) = Γ(Δ^{it}) A Γ(Δ^{it})⋆`. -/
noncomputable def modAutFock (S : StandardSubspace H) (t : ℝ)
    (A : Fock H →L[ℂ] Fock H) : Fock H →L[ℂ] Fock H :=
  secondQuantModCLM S t * A * secondQuantModCLM S (-t)

@[simp] theorem modAutFock_zero (S : StandardSubspace H) (A : Fock H →L[ℂ] Fock H) :
    modAutFock S 0 A = A := by
  simp only [modAutFock, neg_zero, secondQuantModCLM_zero, one_mul, mul_one]

/-- One-parameter group law `σ_s ∘ σ_t = σ_{s+t}`. -/
theorem modAutFock_add (S : StandardSubspace H) (s t : ℝ) (A : Fock H →L[ℂ] Fock H) :
    modAutFock S s (modAutFock S t A) = modAutFock S (s + t) A := by
  unfold modAutFock
  rw [show secondQuantModCLM S s * (secondQuantModCLM S t * A * secondQuantModCLM S (-t))
          * secondQuantModCLM S (-s)
        = (secondQuantModCLM S s * secondQuantModCLM S t) * A
          * (secondQuantModCLM S (-t) * secondQuantModCLM S (-s)) by noncomm_ring,
      secondQuantModCLM_mul, secondQuantModCLM_mul, show -t + -s = -(s + t) by ring]

theorem modAutFock_one (S : StandardSubspace H) (t : ℝ) :
    modAutFock S t 1 = 1 := by
  rw [modAutFock, mul_one, secondQuantModCLM_mul_neg]

/-- `σ_t` is multiplicative. -/
theorem modAutFock_mul (S : StandardSubspace H) (t : ℝ) (A B : Fock H →L[ℂ] Fock H) :
    modAutFock S t (A * B) = modAutFock S t A * modAutFock S t B := by
  unfold modAutFock
  rw [show secondQuantModCLM S t * A * secondQuantModCLM S (-t)
          * (secondQuantModCLM S t * B * secondQuantModCLM S (-t))
        = secondQuantModCLM S t * A * (secondQuantModCLM S (-t) * secondQuantModCLM S t)
          * B * secondQuantModCLM S (-t) by noncomm_ring,
      secondQuantModCLM_neg_mul, mul_one]
  noncomm_ring

/-- `σ_t` preserves the adjoint: a one-parameter group of ⋆-automorphisms. -/
theorem modAutFock_star (S : StandardSubspace H) (t : ℝ) (A : Fock H →L[ℂ] Fock H) :
    star (modAutFock S t A) = modAutFock S t (star A) := by
  unfold modAutFock
  rw [star_mul, star_mul, secondQuantModCLM_star, secondQuantModCLM_star, neg_neg]
  noncomm_ring

/- ── Field-level Takesaki criterion + persistence ──────────────────────────-/

/-- **Field-level Takesaki criterion.**  `σ_t(A) = A` iff `A` commutes with the
    free-field modular unitary `Γ(Δ^{it})`. -/
theorem modAutFock_fixes_iff_commute (S : StandardSubspace H) (t : ℝ)
    (A : Fock H →L[ℂ] Fock H) :
    modAutFock S t A = A ↔ secondQuantModCLM S t * A = A * secondQuantModCLM S t := by
  unfold modAutFock
  constructor
  · intro h
    have h2 : secondQuantModCLM S t * A * secondQuantModCLM S (-t) * secondQuantModCLM S t
        = A * secondQuantModCLM S t := by rw [h]
    rwa [mul_assoc (secondQuantModCLM S t * A), secondQuantModCLM_neg_mul, mul_one] at h2
  · intro h
    rw [h, mul_assoc, secondQuantModCLM_mul_neg, mul_one]

theorem commute_secondQuantModCLM_neg (S : StandardSubspace H) (t : ℝ)
    {P : Fock H →L[ℂ] Fock H}
    (h : secondQuantModCLM S t * P = P * secondQuantModCLM S t) :
    secondQuantModCLM S (-t) * P = P * secondQuantModCLM S (-t) := by
  calc secondQuantModCLM S (-t) * P
      = secondQuantModCLM S (-t) * P * (secondQuantModCLM S t * secondQuantModCLM S (-t)) := by
        rw [secondQuantModCLM_mul_neg, mul_one]
    _ = secondQuantModCLM S (-t) * (P * secondQuantModCLM S t) * secondQuantModCLM S (-t) := by
        noncomm_ring
    _ = secondQuantModCLM S (-t) * (secondQuantModCLM S t * P) * secondQuantModCLM S (-t) := by rw [h]
    _ = (secondQuantModCLM S (-t) * secondQuantModCLM S t) * P * secondQuantModCLM S (-t) := by
        noncomm_ring
    _ = P * secondQuantModCLM S (-t) := by rw [secondQuantModCLM_neg_mul, one_mul]

/-- The free-field decoherence / dephasing map `E(A) = Σ Pₐ A Pₐ`. -/
noncomputable def dephaseFock {ι : Type*} [Fintype ι]
    (P : ι → (Fock H →L[ℂ] Fock H)) (A : Fock H →L[ℂ] Fock H) : Fock H →L[ℂ] Fock H :=
  ∑ i, P i * A * P i

/-- **Field-level persistence.**  When the pointer family commutes with the
    free-field modular unitary `Γ(Δ^{it})`, the decoherence map `E` commutes with
    the second-quantized modular flow `σ_t = Ad(Γ(Δ^{it}))` for every `t`:
    `E ∘ σ_t = σ_t ∘ E`.  The continuum λ-persistence at the genuine free-field
    level — a dephased free-field record state stays dephased under the
    second-quantized modular dynamics. -/
theorem dephaseFock_modAutFock_commute (S : StandardSubspace H) (t : ℝ) {ι : Type*}
    [Fintype ι] (P : ι → (Fock H →L[ℂ] Fock H))
    (hcomm : ∀ i, secondQuantModCLM S t * P i = P i * secondQuantModCLM S t)
    (A : Fock H →L[ℂ] Fock H) :
    dephaseFock P (modAutFock S t A) = modAutFock S t (dephaseFock P A) := by
  unfold dephaseFock modAutFock
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hinv := commute_secondQuantModCLM_neg S t (hcomm i)
  rw [show P i * (secondQuantModCLM S t * A * secondQuantModCLM S (-t)) * P i
        = (P i * secondQuantModCLM S t) * A * (secondQuantModCLM S (-t) * P i) by noncomm_ring,
      ← hcomm i, hinv,
      show secondQuantModCLM S t * P i * A * (P i * secondQuantModCLM S (-t))
        = secondQuantModCLM S t * (P i * A * P i) * secondQuantModCLM S (-t) by noncomm_ring]

/-- **Audit conclusion.**  The continuum λ-persistence carried to the genuine
    free-field level: the modular automorphism `σ_t = Ad(Γ(Δ^{it}))` (a
    one-parameter ⋆-automorphism group), the field-level Takesaki criterion, and
    field-level persistence (`E ∘ σ_t = σ_t ∘ E`) — all on the second-quantized
    free-field modular flow, NO project axioms.  The Γ-capstone is complete. -/
theorem continuumLambdaField_audit : True := trivial

end QIQTH.Fock
