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
import QIQTH.FiniteModularTheory

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

/-! ## DY3 — the finite KMS bridge

The Gibbs state's MODULAR flow is the RESCALED physical flow — `σ_s^{ρ_β} = α_{−βs}` — so the held
finite Tomita–Takesaki KMS condition certifies ρ_β as the KMS state of the code dynamics at inverse
temperature β (the flow is never DEFINED by modAut, per the binding verdict: the bridge runs the
other way). At β = 0 the Gibbs state IS the keystone's maximally mixed counting state (the tracial
case). -/

section KMSBridge

open QIQTH.FiniteModularTheory

/-- The entry formula for the diagonal modular flow at a positive weight. -/
theorem sigmaDiag_entry (p : Micro L C → ℝ) (hp : ∀ n, 0 < p n) (s : ℝ)
    (x : DiamondAlg L C) (n m : Micro L C) :
    sigmaDiag p s x n m
      = Complex.exp (Complex.I * s * ((Real.log (p n) - Real.log (p m) : ℝ) : ℂ)) * x n m := by
  rw [sigmaDiag, diagPow, diagPow, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (hp n).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (hp m).ne'),
    ← Complex.ofReal_log (hp n).le, ← Complex.ofReal_log (hp m).le]
  rw [show Complex.I * s * ((Real.log (p n) - Real.log (p m) : ℝ) : ℂ)
      = ((Real.log (p n) : ℝ) : ℂ) * (Complex.I * s)
        + ((Real.log (p m) : ℝ) : ℂ) * (Complex.I * (-s : ℝ)) from by push_cast; ring,
    Complex.exp_add]
  ring

/-- The log of the Gibbs weight: `log w_β(n) = −βE(n) − Σ_k log Z_k`. -/
theorem log_gibbsWeight (β : ℝ) (n : Micro L C) :
    Real.log (gibbsWeight L C ω β n)
      = -(β * energy L C ω n) - ∑ k : C, Real.log (ZMode L ω β k.val) := by
  rw [gibbsWeight, Real.log_prod]
  · have hterm : ∀ k : C, Real.log (pMode L ω β k.val (n k))
        = -(β * (ω k.val * ((n k : ℕ) : ℝ))) - Real.log (ZMode L ω β k.val) := fun k => by
      rw [pMode, Real.log_div (Real.exp_ne_zero _) (ZMode_pos L ω β k.val).ne', Real.log_exp]
      ring
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib]
    congr 1
    rw [energy, Finset.mul_sum, ← Finset.sum_neg_distrib]
  · exact fun k _ => (pMode_pos L ω β k.val (n k)).ne'

/-- **DY3 CAPSTONE — the KMS bridge:** the Gibbs state's modular flow IS the rescaled physical
    flow, `σ_s^{ρ_β} = α_{−βs}` (the partition-function part of the weight cancels between the two
    diagonal conjugations; only the energy differences survive). -/
theorem sigmaDiag_gibbs_eq_alpha_rescale (β s : ℝ) (x : DiamondAlg L C) :
    sigmaDiag (fun n => gibbsWeight L C ω β n) s x = alpha L C ω (-(β * s)) x := by
  ext n m
  rw [sigmaDiag_entry L C (fun n => gibbsWeight L C ω β n)
      (fun n => gibbsWeight_pos L C ω β n) s x n m, alpha_entry]
  congr 2
  rw [log_gibbsWeight, log_gibbsWeight]
  push_cast
  ring

/-- The Gibbs inverse (explicit diagonal). -/
noncomputable def gibbsInv (β : ℝ) : DiamondAlg L C :=
  Matrix.diagonal fun n => (((gibbsWeight L C ω β n)⁻¹ : ℝ) : ℂ)

noncomputable instance gibbsInvertible (β : ℝ) : Invertible (gibbsDensity L C ω β) := by
  refine ⟨gibbsInv L C ω β, ?_, ?_⟩
  · rw [gibbsInv, gibbsDensity, Matrix.diagonal_mul_diagonal,
      show (fun i => (((gibbsWeight L C ω β i)⁻¹ : ℝ) : ℂ) * ((gibbsWeight L C ω β i : ℝ) : ℂ))
          = fun _ => (1 : ℂ) from funext fun i => by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (gibbsWeight_pos L C ω β i).ne',
          Complex.ofReal_one]]
    exact Matrix.diagonal_one
  · rw [gibbsInv, gibbsDensity, Matrix.diagonal_mul_diagonal,
      show (fun i => ((gibbsWeight L C ω β i : ℝ) : ℂ) * (((gibbsWeight L C ω β i)⁻¹ : ℝ) : ℂ))
          = fun _ => (1 : ℂ) from funext fun i => by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ (gibbsWeight_pos L C ω β i).ne',
          Complex.ofReal_one]]
    exact Matrix.diagonal_one

/-- **The Gibbs state satisfies the finite KMS condition** (the held Tomita–Takesaki applied to the
    explicit density): `ω_β(x·y) = ω_β(y·σ(x))` — with `σ` the modular conjugation whose real flow
    is `α_{−βs}` by the bridge above. -/
theorem gibbs_kms_condition (β : ℝ) (x y : DiamondAlg L C) :
    stateOf (gibbsDensity L C ω β) (x * y)
      = stateOf (gibbsDensity L C ω β) (y * modAut (gibbsDensity L C ω β) x) :=
  kms_condition (gibbsDensity L C ω β) x y

/-- **The tracial β = 0 case: the Gibbs state IS the keystone's maximally mixed counting state**
    (KMS at β = 0 is trace cyclicity; the thermal tower and the counting tower share their
    ground floor). -/
theorem gibbsDensity_zero_eq_maxMixed :
    gibbsDensity L C ω 0 = maxMixed (Micro L C) := by
  rw [gibbsDensity, maxMixed, card_micro]
  ext n m
  rw [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : n = m
  · rw [if_pos h, if_pos h, smul_eq_mul, mul_one, gibbsWeight]
    have hp : ∀ k : C, pMode L ω 0 k.val (n k) = ((L.D k.val : ℝ))⁻¹ := fun k => by
      rw [pMode, ZMode,
        show (∑ i : Fin (L.D k.val), Real.exp (-((0 : ℝ) * ω k.val * ((i : ℕ) : ℝ))))
          = ∑ _i : Fin (L.D k.val), (1 : ℝ) from Finset.sum_congr rfl fun i _ => by norm_num,
        Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]
      norm_num
    rw [Finset.prod_congr rfl fun k _ => hp k, Finset.prod_inv_distrib]
    push_cast
    congr 1
    rw [NC]
    push_cast
    exact Finset.prod_coe_sort C fun e => ((L.D e : ℕ) : ℂ)
  · rw [if_neg h, if_neg h, smul_zero]

end KMSBridge

end QIQTH.Dynamics
