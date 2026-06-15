/-
  ContinuumLambda — Stage 1 of CONTINUUM_LAMBDA_ROADMAP.md.

  Lifts the finite (Type I) λ-law of `LambdaPointer.lean` to the GENUINE CONTINUUM
  modular flow `Δ^{it} = modUnitary` already built axiom-free in
  `StandardSubspaceModularFlow.lean` (the Rieffel–Van Daele bounded modular
  unitary group of a standard subspace).  This is the Type-III-native continuum
  λ-law: it rides the modular automorphism `σ_t = Ad(Δ^{it})`, NOT the retired
  crossed product.

  Built here (axiom-free):
    * `modAutOp` — the modular automorphism `σ_t(A) = Δ^{it} A Δ^{-it}` on
      `H →L[ℂ] H`; a one-parameter group of unital ⋆-automorphisms
      (`modAutOp_zero/_add/_one/_mul/_star`).
    * `modAutOp_fixes_iff_commute` — the CONTINUUM TAKESAKI CRITERION:
      `σ_t(A) = A ⟺ A` commutes with `Δ^{it}`.
    * `modAutOp_fixes_specProj` — a spectral projection of the modular generator
      `R` is fixed by the flow for every `t` (continuum exact-decoherence ⇒ the
      flow fixes the pointer), via `modUnitary_commute_specProj`.
    * `dephaseOp_modAutOp_commute` / `dephaseOp_specProj_commute` — CONTINUUM
      PERSISTENCE: the decoherence map `E(A)=Σ Pₐ A Pₐ` commutes with the
      continuum modular flow `σ_t` for every `t` (unconditional for spectral
      pointer projections).  A dephased, records-definite state stays dephased
      under the genuine continuum modular dynamics.

  Honest scope: this is the free-field / standard-subspace (one-particle) modular
  flow.  The local algebra's Type III₁-ness (Buchholz–Wichmann) is cited; the
  second-quantized `Γ(Δ^{it})` flow exists (`Fock/SecondQuantModularFlow`).
-/

import QIQTH.StandardSubspaceModularFlow

namespace QIQTH.ContinuumLambda

open QIQTH.StandardSubspaceModular QIQTH.SpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- ── 0. The modular unitary as a two-sided inverse pair ─────────────────────-/

theorem modUnitary_mul_neg (S : StandardSubspace H) (t : ℝ) :
    modUnitary S t * modUnitary S (-t) = 1 := by
  rw [← modUnitary_add, add_neg_cancel, modUnitary_zero]

theorem modUnitary_neg_mul (S : StandardSubspace H) (t : ℝ) :
    modUnitary S (-t) * modUnitary S t = 1 := by
  rw [← modUnitary_add, neg_add_cancel, modUnitary_zero]

theorem modUnitary_star (S : StandardSubspace H) (t : ℝ) :
    star (modUnitary S t) = modUnitary S (-t) := by
  rw [ContinuousLinearMap.star_eq_adjoint, modUnitary_adjoint]

/- ── 1. The modular automorphism σ_t = Ad(Δ^{it}) ──────────────────────────-/

/-- The continuum modular automorphism `σ_t(A) = Δ^{it} A Δ^{-it}`. -/
noncomputable def modAutOp (S : StandardSubspace H) (t : ℝ) (A : H →L[ℂ] H) :
    H →L[ℂ] H :=
  modUnitary S t * A * modUnitary S (-t)

/-- `σ_0 = id`. -/
@[simp] theorem modAutOp_zero (S : StandardSubspace H) (A : H →L[ℂ] H) :
    modAutOp S 0 A = A := by
  simp only [modAutOp, neg_zero, modUnitary_zero, one_mul, mul_one]

/-- **One-parameter group law** `σ_s ∘ σ_t = σ_{s+t}`. -/
theorem modAutOp_add (S : StandardSubspace H) (s t : ℝ) (A : H →L[ℂ] H) :
    modAutOp S s (modAutOp S t A) = modAutOp S (s + t) A := by
  unfold modAutOp
  rw [show modUnitary S s * (modUnitary S t * A * modUnitary S (-t)) * modUnitary S (-s)
        = (modUnitary S s * modUnitary S t) * A * (modUnitary S (-t) * modUnitary S (-s))
      by noncomm_ring, ← modUnitary_add, ← modUnitary_add, show -t + -s = -(s + t) by ring]

/-- `σ_t` is unital. -/
theorem modAutOp_one (S : StandardSubspace H) (t : ℝ) :
    modAutOp S t 1 = 1 := by
  rw [modAutOp, mul_one, modUnitary_mul_neg]

/-- `σ_t` is multiplicative: a ⋆-algebra endomorphism (the `Δ^{-it}Δ^{it}=1` in
    the middle cancels). -/
theorem modAutOp_mul (S : StandardSubspace H) (t : ℝ) (A B : H →L[ℂ] H) :
    modAutOp S t (A * B) = modAutOp S t A * modAutOp S t B := by
  unfold modAutOp
  rw [show modUnitary S t * A * modUnitary S (-t) * (modUnitary S t * B * modUnitary S (-t))
        = modUnitary S t * A * (modUnitary S (-t) * modUnitary S t) * B * modUnitary S (-t)
      by noncomm_ring, modUnitary_neg_mul, mul_one]
  noncomm_ring

/-- `σ_t` preserves the adjoint: a one-parameter group of ⋆-automorphisms. -/
theorem modAutOp_star (S : StandardSubspace H) (t : ℝ) (A : H →L[ℂ] H) :
    star (modAutOp S t A) = modAutOp S t (star A) := by
  unfold modAutOp
  rw [star_mul, star_mul, modUnitary_star, modUnitary_star, neg_neg]
  noncomm_ring

/- ── 2. The continuum Takesaki criterion + fixed pointer projections ───────-/

/-- **Continuum Takesaki criterion.**  `σ_t(A) = A` iff `A` commutes with the
    modular unitary `Δ^{it}`.  The continuum analogue of
    `LambdaPointer.modAut_fixes_iff_commute`. -/
theorem modAutOp_fixes_iff_commute (S : StandardSubspace H) (t : ℝ)
    (A : H →L[ℂ] H) :
    modAutOp S t A = A ↔ modUnitary S t * A = A * modUnitary S t := by
  unfold modAutOp
  constructor
  · intro h
    have h2 : modUnitary S t * A * modUnitary S (-t) * modUnitary S t
        = A * modUnitary S t := by rw [h]
    rwa [mul_assoc (modUnitary S t * A), modUnitary_neg_mul, mul_one] at h2
  · intro h
    rw [h, mul_assoc, modUnitary_mul_neg, mul_one]

/-- **The pointer projections are fixed by the flow.**  A spectral projection of
    the modular generator `R` is fixed by the modular automorphism for every `t`
    — the continuum statement of "exact decoherence ⇒ the modular flow fixes the
    pointer", via `modUnitary_commute_specProj`. -/
theorem modAutOp_fixes_specProj (S : StandardSubspace H) (t : ℝ)
    {s : Set (spectrum ℝ (rvdRC S))} (hs : MeasurableSet s) :
    modAutOp S t ((PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).E s)
      = (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).E s := by
  rw [modAutOp_fixes_iff_commute]
  exact modUnitary_commute_specProj S t hs

/- ── 3. Continuum persistence ──────────────────────────────────────────────-/

/-- If `P` commutes with `Δ^{it}`, so does its inverse `Δ^{-it}`. -/
theorem commute_modUnitary_neg (S : StandardSubspace H) (t : ℝ) {P : H →L[ℂ] H}
    (h : modUnitary S t * P = P * modUnitary S t) :
    modUnitary S (-t) * P = P * modUnitary S (-t) := by
  calc modUnitary S (-t) * P
      = modUnitary S (-t) * P * (modUnitary S t * modUnitary S (-t)) := by
        rw [modUnitary_mul_neg, mul_one]
    _ = modUnitary S (-t) * (P * modUnitary S t) * modUnitary S (-t) := by noncomm_ring
    _ = modUnitary S (-t) * (modUnitary S t * P) * modUnitary S (-t) := by rw [h]
    _ = (modUnitary S (-t) * modUnitary S t) * P * modUnitary S (-t) := by noncomm_ring
    _ = P * modUnitary S (-t) := by rw [modUnitary_neg_mul, one_mul]

/-- The decoherence / dephasing map onto a pointer family `P`:
    `E(A) = Σ Pₐ A Pₐ`. -/
noncomputable def dephaseOp {ι : Type*} [Fintype ι] (P : ι → (H →L[ℂ] H))
    (A : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i, P i * A * P i

/-- **Continuum persistence.**  When the pointer family commutes with the modular
    unitary `Δ^{it}` (the Takesaki criterion), the decoherence map `E` commutes
    with the continuum modular flow `σ_t = Ad(Δ^{it})`: `E ∘ σ_t = σ_t ∘ E`.  The
    continuum lift of `LambdaPointer.dephase_modAut_commute` — a dephased state
    stays dephased under the genuine continuum modular dynamics. -/
theorem dephaseOp_modAutOp_commute (S : StandardSubspace H) (t : ℝ) {ι : Type*}
    [Fintype ι] (P : ι → (H →L[ℂ] H))
    (hcomm : ∀ i, modUnitary S t * P i = P i * modUnitary S t) (A : H →L[ℂ] H) :
    dephaseOp P (modAutOp S t A) = modAutOp S t (dephaseOp P A) := by
  unfold dephaseOp modAutOp
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hinv := commute_modUnitary_neg S t (hcomm i)
  rw [show P i * (modUnitary S t * A * modUnitary S (-t)) * P i
        = (P i * modUnitary S t) * A * (modUnitary S (-t) * P i) by noncomm_ring,
      ← hcomm i, hinv,
      show modUnitary S t * P i * A * (P i * modUnitary S (-t))
        = modUnitary S t * (P i * A * P i) * modUnitary S (-t) by noncomm_ring]

/-- **Unconditional continuum persistence for spectral pointers.**  For a finite
    family of spectral projections of the modular generator `R`, the decoherence
    map commutes with the modular flow `σ_t` for every `t`, with no extra
    hypothesis (the commutation is automatic, `modUnitary_commute_specProj`). -/
theorem dephaseOp_specProj_commute (S : StandardSubspace H) (t : ℝ) {ι : Type*}
    [Fintype ι] (sset : ι → Set (spectrum ℝ (rvdRC S)))
    (hmeas : ∀ i, MeasurableSet (sset i)) (A : H →L[ℂ] H) :
    dephaseOp (fun i => (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).E (sset i))
        (modAutOp S t A)
      = modAutOp S t (dephaseOp
        (fun i => (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).E (sset i)) A) := by
  apply dephaseOp_modAutOp_commute
  intro i
  exact modUnitary_commute_specProj S t (hmeas i)

/-- **Audit conclusion (Stage 1).**  The continuum modular automorphism, Takesaki
    criterion, and persistence — the Type-III-native continuum lift of the finite
    λ-law — proved on the bounded RvD modular flow, NO project axioms.  The seed
    /Born/selection-event layers (Stages 2–3) and the Type III₁ classification
    (cited) are the remaining roadmap items. -/
theorem audit_conclusion : True := trivial

end QIQTH.ContinuumLambda
