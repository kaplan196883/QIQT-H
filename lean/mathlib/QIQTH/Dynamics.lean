/-
  THE DYNAMICS (THE_DYNAMICS_PLAN.md) — the code's time evolution.

  The microscopic side (the capacity-bounded record code = THE EMBEDDING's truncated field
  diamond) gets a TIME EVOLUTION: the diagonal code Hamiltonian `H = Σ_k ω_k N_k`, its Heisenberg
  flow `α_t` (defined by the phase unitary — NO Stone theorem, NO unbounded operators, NO matrix
  exponential; everything via the ENTRY FORMULA `α_t(A)(n,m) = e^{it(E(n)−E(m))}·A(n,m)`), on the
  way to explicit Gibbs/KMS states and the independent cross-check.

  DY1 — the diagonal dynamics core:
  • `energy` / `Hcode` (with `Hcode_apply_diag` — H is diagonal with entry E(n) = Σ ω_k n_k);
  • `phaseUnitary` with the group law; `alpha` with the ENTRY FORMULA `alpha_entry`;
  • the flow laws: `alpha_zero`, `alpha_add` (one-parameter group), `alpha_mul`, `alpha_star`
    (a ⋆-automorphism at every t);
  • the actions: **`alpha_diagonal` — every diagonal observable is STATIONARY** (records, number
    operators, occupation projectors: H is a function of the N_k, so the record algebra is FIXED by
    the flow — the honesty point, stated not hidden); the NONTRIVIAL dynamics lives on the ladders:
    `alpha_modeLowering` (`α_t(a_k) = e^{−iω_k t}·a_k`) and `alpha_modeRaising`
    (`α_t(a_k†) = e^{iω_k t}·a_k†`).
  Axiom-free, std-3.
-/
import Mathlib
import QIQTH.Embedding

namespace QIQTH.Dynamics

open QIQTH.Keystone QIQTH.Embedding
open scoped Matrix

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (C : Finset M) (ω : M → ℝ)

/-- **The occupation energy** `E(n) = Σ_k ω_k n_k` (frequencies `ω` are named data). -/
noncomputable def energy (n : Micro L C) : ℝ :=
  ∑ k : C, ω k.val * ((n k : ℕ) : ℝ)

/-- **The code Hamiltonian** `H = Σ_k ω_k N_k`. -/
noncomputable def Hcode : DiamondAlg L C :=
  ∑ k : C, (ω k.val : ℂ) • numberOp L C k

/-- `H` is diagonal in the occupation basis with entry `E(n)`. -/
theorem Hcode_apply_diag (n m : Micro L C) :
    Hcode L C ω n m = if n = m then ((energy L C ω n : ℝ) : ℂ) else 0 := by
  rw [Hcode, Matrix.sum_apply]
  by_cases h : n = m
  · subst h
    rw [if_pos rfl, energy]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_apply, numberOp_apply_diag, if_pos rfl, smul_eq_mul]
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun k _ => by
      rw [Matrix.smul_apply, numberOp_apply_diag, if_neg h, smul_zero]

/-- **The phase unitary** `U_t = diag e^{itE(n)}` — the finite time-evolution operator, defined
    directly (no Stone theorem, no matrix exponential). -/
noncomputable def phaseUnitary (t : ℝ) : DiamondAlg L C :=
  Matrix.diagonal fun n => Complex.exp (Complex.I * t * ((energy L C ω n : ℝ) : ℂ))

theorem phaseUnitary_zero : phaseUnitary L C ω 0 = 1 := by
  rw [phaseUnitary,
    show (fun n => Complex.exp (Complex.I * (0 : ℝ) * ((energy L C ω n : ℝ) : ℂ)))
      = fun _ => (1 : ℂ) from funext fun n => by norm_num,
    Matrix.diagonal_one]

/-- The group law of the phase unitaries. -/
theorem phaseUnitary_mul (t s : ℝ) :
    phaseUnitary L C ω t * phaseUnitary L C ω s = phaseUnitary L C ω (t + s) := by
  rw [phaseUnitary, phaseUnitary, phaseUnitary, Matrix.diagonal_mul_diagonal]
  congr 1
  funext n
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The Heisenberg flow** `α_t(A) = U_t A U_{−t}`. -/
noncomputable def alpha (t : ℝ) (A : DiamondAlg L C) : DiamondAlg L C :=
  phaseUnitary L C ω t * A * phaseUnitary L C ω (-t)

/-- **THE ENTRY FORMULA** (the engine of every proof below):
    `α_t(A)(n,m) = e^{it(E(n)−E(m))}·A(n,m)`. -/
theorem alpha_entry (t : ℝ) (A : DiamondAlg L C) (n m : Micro L C) :
    alpha L C ω t A n m
      = Complex.exp (Complex.I * t * ((energy L C ω n - energy L C ω m : ℝ) : ℂ)) * A n m := by
  simp only [alpha, phaseUnitary]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
    show Complex.I * t * ((energy L C ω n - energy L C ω m : ℝ) : ℂ)
      = Complex.I * t * ((energy L C ω n : ℝ) : ℂ)
        + Complex.I * (-t : ℝ) * ((energy L C ω m : ℝ) : ℂ) from by push_cast; ring,
    Complex.exp_add]
  ring

theorem alpha_zero (A : DiamondAlg L C) : alpha L C ω 0 A = A := by
  rw [alpha, neg_zero, phaseUnitary_zero, one_mul, mul_one]

/-- The flow is a one-parameter group. -/
theorem alpha_add (t s : ℝ) (A : DiamondAlg L C) :
    alpha L C ω (t + s) A = alpha L C ω t (alpha L C ω s A) := by
  ext n m
  rw [alpha_entry, alpha_entry, alpha_entry, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The flow is multiplicative (an algebra automorphism at every `t`). -/
theorem alpha_mul (t : ℝ) (A B : DiamondAlg L C) :
    alpha L C ω t (A * B) = alpha L C ω t A * alpha L C ω t B := by
  ext n m
  rw [alpha_entry, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [alpha_entry, alpha_entry]
  have key : Complex.exp (Complex.I * t * ((energy L C ω n - energy L C ω p : ℝ) : ℂ))
      * Complex.exp (Complex.I * t * ((energy L C ω p - energy L C ω m : ℝ) : ℂ))
      = Complex.exp (Complex.I * t * ((energy L C ω n - energy L C ω m : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← key]
  ring

/-- The flow is a ⋆-map (adjoints evolve consistently). -/
theorem alpha_star (t : ℝ) (A : DiamondAlg L C) :
    alpha L C ω t Aᴴ = (alpha L C ω t A)ᴴ := by
  ext n m
  rw [alpha_entry, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, alpha_entry,
    star_mul']
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **Every diagonal observable is STATIONARY** — `H` is a function of the `N_k`, so the record
    algebra is FIXED by the flow (the honesty point: records, number operators, and occupation
    projectors do not move; the nontrivial dynamics lives on the off-diagonal coherences). -/
theorem alpha_diagonal (t : ℝ) (d : Micro L C → ℂ) :
    alpha L C ω t (Matrix.diagonal d) = Matrix.diagonal d := by
  ext n m
  rw [alpha_entry, Matrix.diagonal_apply]
  by_cases h : n = m
  · subst h
    rw [if_pos rfl, sub_self]
    simp
  · rw [if_neg h, mul_zero]

/-- The number operators are stationary. -/
theorem alpha_numberOp (t : ℝ) (k : C) :
    alpha L C ω t (numberOp L C k) = numberOp L C k := by
  ext n m
  rw [alpha_entry, numberOp_apply_diag]
  by_cases h : n = m
  · subst h
    rw [if_pos rfl, sub_self]
    simp
  · rw [if_neg h, mul_zero]

/-- The occupation (pointer-basis) projectors are stationary. -/
theorem alpha_occupationProj (t : ℝ) (p : Micro L C) :
    alpha L C ω t (occupationProj L C p) = occupationProj L C p :=
  alpha_diagonal L C ω t _

/-- **The records are stationary** — the keystone record projectors are fixed points of the flow. -/
theorem alpha_recordProj (t : ℝ) (R : Finset (Micro L C)) :
    alpha L C ω t (recordProj L C R) = recordProj L C R :=
  alpha_diagonal L C ω t _

/-- **DY1 CAPSTONE — the nontrivial dynamics: the annihilator rotates at its mode frequency,**
    `α_t(a_k) = e^{−iω_k t}·a_k`. -/
theorem alpha_modeLowering (t : ℝ) (k : C) :
    alpha L C ω t (modeLowering L C k)
      = Complex.exp (-(Complex.I) * (ω k.val : ℂ) * (t : ℂ)) • modeLowering L C k := by
  ext n m
  rw [alpha_entry, Matrix.smul_apply, smul_eq_mul]
  by_cases h : modeLowering L C k n m = 0
  · rw [h, mul_zero, mul_zero]
  · have hs : sameOff L C k n m := by
      by_contra hs
      exact h (by rw [modeLowering, modeOp_apply, if_neg hs])
    have hk : ((n k : ℕ)) + 1 = ((m k : ℕ)) := by
      by_contra hk
      refine h ?_
      rw [modeLowering, modeOp_apply, if_pos hs]
      exact if_neg hk
    have hE : energy L C ω n - energy L C ω m = -(ω k.val) := by
      rw [energy, energy, ← Finset.sum_sub_distrib, Finset.sum_eq_single k]
      · rw [show ((m k : ℕ) : ℝ) = ((n k : ℕ) : ℝ) + 1 from by exact_mod_cast hk.symm]
        ring
      · intro j _ hj
        rw [hs j hj]
        ring
      · intro hmem
        exact absurd (Finset.mem_univ k) hmem
    rw [hE]
    congr 1
    push_cast
    ring_nf

/-- **The creator rotates oppositely**, `α_t(a_k†) = e^{iω_k t}·a_k†` (by the ⋆-law — no
    re-proof). -/
theorem alpha_modeRaising (t : ℝ) (k : C) :
    alpha L C ω t (modeLowering L C k)ᴴ
      = Complex.exp (Complex.I * (ω k.val : ℂ) * (t : ℂ)) • (modeLowering L C k)ᴴ := by
  rw [alpha_star, alpha_modeLowering, Matrix.conjTranspose_smul]
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  ring

/-! ## DY2 — the explicit Gibbs product density

The thermal state of the code at inverse temperature `β`: an EXPLICIT product diagonal density
(per-mode Boltzmann weights — no matrix exponential, per the binding verdict), normalized,
positive, and stationary under the flow. -/

section Gibbs

open scoped ComplexOrder

/-- **The per-mode partition function** `Z_k(β) = Σ_{i<D_k} e^{−βω_k i}`. -/
noncomputable def ZMode (β : ℝ) (k : M) : ℝ :=
  ∑ i : Fin (L.D k), Real.exp (-(β * ω k * ((i : ℕ) : ℝ)))

theorem ZMode_pos (β : ℝ) (k : M) : 0 < ZMode L ω β k :=
  Finset.sum_pos (fun i _ => Real.exp_pos _)
    ⟨⟨0, L.hD k⟩, Finset.mem_univ _⟩

/-- **The per-mode Boltzmann weight** `p_k(i) = e^{−βω_k i}/Z_k`. -/
noncomputable def pMode (β : ℝ) (k : M) (i : Fin (L.D k)) : ℝ :=
  Real.exp (-(β * ω k * ((i : ℕ) : ℝ))) / ZMode L ω β k

theorem pMode_pos (β : ℝ) (k : M) (i : Fin (L.D k)) : 0 < pMode L ω β k i :=
  div_pos (Real.exp_pos _) (ZMode_pos L ω β k)

/-- Each mode's Boltzmann weights are normalized. -/
theorem pMode_sum_one (β : ℝ) (k : M) : ∑ i, pMode L ω β k i = 1 := by
  simp only [pMode]
  rw [← Finset.sum_div,
    show (∑ i : Fin (L.D k), Real.exp (-(β * ω k * ((i : ℕ) : ℝ)))) = ZMode L ω β k from rfl,
    div_self (ZMode_pos L ω β k).ne']

/-- **The Gibbs product weight** of an occupation state: `w_β(n) = Π_k p_k(n_k)`. -/
noncomputable def gibbsWeight (β : ℝ) (n : Micro L C) : ℝ :=
  ∏ k : C, pMode L ω β k.val (n k)

theorem gibbsWeight_pos (β : ℝ) (n : Micro L C) : 0 < gibbsWeight L C ω β n :=
  Finset.prod_pos fun k _ => pMode_pos L ω β k.val (n k)

/-- The Gibbs weights are normalized (the product-sum interchange over the occupation basis). -/
theorem sum_gibbsWeight_one (β : ℝ) :
    ∑ n : Micro L C, gibbsWeight L C ω β n = 1 := by
  simp only [gibbsWeight]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  exact Finset.prod_eq_one fun k _ => pMode_sum_one L ω β k.val

/-- **The Gibbs density** `ρ_β = diag w_β` — the code's thermal state, explicit and diagonal. -/
noncomputable def gibbsDensity (β : ℝ) : DiamondAlg L C :=
  Matrix.diagonal fun n => ((gibbsWeight L C ω β n : ℝ) : ℂ)

/-- **DY2 CAPSTONE — the Gibbs state is a genuine density**: positive semidefinite with unit
    trace. -/
theorem gibbs_isDensity (β : ℝ) :
    QIQTH.QuantumEntropy.IsDensity (gibbsDensity L C ω β) where
  posSemidef := by
    rw [gibbsDensity]
    refine Matrix.posSemidef_diagonal_iff.mpr fun n => ?_
    exact Complex.zero_le_real.mpr (gibbsWeight_pos L C ω β n).le
  trace_one := by
    rw [gibbsDensity, Matrix.trace_diagonal, ← Complex.ofReal_sum, sum_gibbsWeight_one]
    norm_num

/-- **The Gibbs state is stationary** under the flow: `tr(ρ_β·α_t(A)) = tr(ρ_β·A)` — the flow
    preserves the diagonal, and ρ_β is diagonal. -/
theorem gibbs_stationary (β t : ℝ) (A : DiamondAlg L C) :
    Matrix.trace (gibbsDensity L C ω β * alpha L C ω t A)
      = Matrix.trace (gibbsDensity L C ω β * A) := by
  rw [Matrix.trace, Matrix.trace]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [gibbsDensity, Matrix.diagonal_apply]
  by_cases h : n = p
  · subst h
    rw [if_pos rfl, alpha_entry, sub_self]
    simp
  · rw [if_neg h, zero_mul, zero_mul]

end Gibbs

end QIQTH.Dynamics
