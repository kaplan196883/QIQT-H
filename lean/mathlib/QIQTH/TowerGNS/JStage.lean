/-
  THE MODULAR CONJUGATION J1 (THE_MODULAR_CONJUGATION_PLAN.md) — the finite J layer:
  `jStage C a := √ρ·aᴴ·√ρ⁻¹`, the modular conjugation at stage level, and
  `deltaHalfStage C a := √ρ·a·√ρ⁻¹`, the stage-level half-power action.

  Deliverables:
  • `jStage_single` ★ — THE VERIFIED SCALAR: `J(E_{nm}c) = √(w_m/w_n) • E_{mn}(conj c)` —
    indices FLIPPED, scalar CONJUGATED (the anti-linear eigenbasis action);
  • `deltaHalfStage_single` — `Δ^{1/2}(E_{nm}c) = √(w_n/w_m) • E_{nm}c` (indices NOT
    flipped, scalar NOT conjugated — same basis, half the modAut eigenvalue);
  • the algebraic pack — `jStage_involutive` (J² = 1), `jStage_one` (JΩ = Ω free),
    `jStage_anti_mul`, the conjugate-linear `jStage_smul`, additive laws;
  • `jStage_deltaHalfStage = ᴴ` (the S̄-core: J∘Δ^{1/2} is the ⋆), `deltaHalfStage_jStage
    = modAut ρ ∘ ᴴ` (the F-core: Δ^{1/2}∘J — NOT S̄; the order guard), `deltaHalfStage_sq
    = modAut ρ` (Δ's core action);
  • `gnsInner_jStage` ★ — the single-stage ANTI-ISOMETRY `⟪Jx, Jy⟫_C = ⟪y, x⟫_C`
    (trace-cycling with ρ = S·S);
  • `rightConj_jStage = ᴴ` — the J2 feed: THE ENGINE E1 at `b := jStage a` gives the
    cross-stage law from this identity.

  HONEST SCOPE: finite-stage matrix identities only. NO global anti-unitary J is
  constructed here (that is J3–J4); no polar decomposition on the core (J5); no unbounded
  Δ^{1/2}; no Tomita II claim. Everything is diagonal-times-single entrywise calculus over
  the RightMul.lean √ρ toolkit. Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.RightMul
import QIQTH.TowerGNS.ModularEigenbasis

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The stage-level modular conjugation and half-power -/

/-- **The stage-level modular conjugation** `J_C a := √ρ·aᴴ·√ρ⁻¹` — the finite matrix
    closed form of the modular conjugation (conjugate-linear in `a` through the ᴴ). -/
noncomputable def jStage (C : Finset M) (a : DiamondAlg L C) : DiamondAlg L C :=
  sqrtGibbs L ω β C * aᴴ * sqrtInvGibbs L ω β C

/-- **The stage-level half-power action** `Δ^{1/2}_C a := √ρ·a·√ρ⁻¹` — the finite matrix
    closed form of the modular half-power on the algebra (ℂ-linear, no ᴴ). -/
noncomputable def deltaHalfStage (C : Finset M) (a : DiamondAlg L C) : DiamondAlg L C :=
  sqrtGibbs L ω β C * a * sqrtInvGibbs L ω β C

/-! ### The √ρ toolkit extensions (diagonal bookkeeping) -/

omit [DecidableEq M] in
/-- `(S⁻¹)ᴴ = S⁻¹` — the inverse square root is self-adjoint (real diagonal). -/
theorem sqrtInvGibbs_conjTranspose (C : Finset M) :
    (sqrtInvGibbs L ω β C)ᴴ = sqrtInvGibbs L ω β C := by
  rw [sqrtInvGibbs, Matrix.diagonal_conjTranspose]
  congr 1
  funext m
  simp [Complex.conj_ofReal]

/-- `S⁻¹ · S⁻¹ = ρ⁻¹` — the inverse square root squares to the explicit inverse density. -/
theorem sqrtInvGibbs_mul_self (C : Finset M) :
    sqrtInvGibbs L ω β C * sqrtInvGibbs L ω β C = gibbsInv L C ω β := by
  rw [sqrtInvGibbs, gibbsInv, Matrix.diagonal_mul_diagonal]
  congr 1
  funext m
  rw [← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (gibbsWeight_pos L C ω β m).le]

/-- Head cancellation `S·(S⁻¹·z) = z` (the rw-friendly ∀-form for right-associated
    products). -/
theorem sqrtGibbs_sqrtInvGibbs_cancel (C : Finset M) (z : DiamondAlg L C) :
    sqrtGibbs L ω β C * (sqrtInvGibbs L ω β C * z) = z := by
  rw [← Matrix.mul_assoc, sqrtGibbs_mul_sqrtInvGibbs, one_mul]

/-- Head cancellation `S⁻¹·(S·z) = z`. -/
theorem sqrtInvGibbs_sqrtGibbs_cancel (C : Finset M) (z : DiamondAlg L C) :
    sqrtInvGibbs L ω β C * (sqrtGibbs L ω β C * z) = z := by
  rw [← Matrix.mul_assoc, sqrtInvGibbs_mul_sqrtGibbs, one_mul]

/-- Head recombination `S·(S·z) = ρ·z`. -/
theorem sqrtGibbs_sqrtGibbs_head (C : Finset M) (z : DiamondAlg L C) :
    sqrtGibbs L ω β C * (sqrtGibbs L ω β C * z) = gibbsDensity L C ω β * z := by
  rw [← Matrix.mul_assoc, sqrtGibbs_mul_self]

/-- The conjugate transpose of `jStage`: `(J a)ᴴ = √ρ⁻¹·a·√ρ` (both diagonals are real,
    hence self-adjoint). -/
theorem jStage_conjTranspose (C : Finset M) (a : DiamondAlg L C) :
    (jStage L ω β C a)ᴴ = sqrtInvGibbs L ω β C * a * sqrtGibbs L ω β C := by
  rw [jStage, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, sqrtGibbs_conjTranspose,
    sqrtInvGibbs_conjTranspose, Matrix.mul_assoc]

/-! ### ★ The eigenbasis action — THE VERIFIED SCALAR -/

/-- **★ THE J SCALAR**: on the matrix-unit basis the stage conjugation acts as
    `J(E_{nm} c) = √(w_m/w_n) • E_{mn} (conj c)` — indices FLIPPED, scalar CONJUGATED,
    weight ratio square-rooted (the COLUMN weight `w_m` on top: `‖E_{nm}c‖² = w_m|c|²`,
    and `(w_m/w_n)·w_n = w_m` is the isometry check). -/
theorem jStage_single (C : Finset M) (n m : Micro L C) (c : ℂ) :
    jStage L ω β C (Matrix.single n m c)
      = ((Real.sqrt (gibbsWeight L C ω β m / gibbsWeight L C ω β n) : ℝ) : ℂ)
        • Matrix.single m n (starRingEnd ℂ c) := by
  rw [jStage, Matrix.conjTranspose_single, starRingEnd_apply, sqrtGibbs, sqrtInvGibbs]
  ext p q
  simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : m = p ∧ n = q
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Matrix.single_apply_same, smul_eq_mul]
    rw [Real.sqrt_div (gibbsWeight_pos L C ω β m).le]
    push_cast
    ring
  · rw [Matrix.single_apply_of_ne m n (star c) p q h, mul_zero, zero_mul, smul_zero]

/-- **The Δ^{1/2} scalar**: `Δ^{1/2}(E_{nm} c) = √(w_n/w_m) • E_{nm} c` — indices NOT
    flipped, scalar NOT conjugated: the matrix units are eigenvectors of the half-power
    with the square root of the `modAut` eigenvalue `w_n/w_m`
    (`modAut_gibbsDensity_single`). -/
theorem deltaHalfStage_single (C : Finset M) (n m : Micro L C) (c : ℂ) :
    deltaHalfStage L ω β C (Matrix.single n m c)
      = ((Real.sqrt (gibbsWeight L C ω β n / gibbsWeight L C ω β m) : ℝ) : ℂ)
        • Matrix.single n m c := by
  rw [deltaHalfStage, sqrtGibbs, sqrtInvGibbs]
  ext p q
  simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : n = p ∧ m = q
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Matrix.single_apply_same, smul_eq_mul]
    rw [Real.sqrt_div (gibbsWeight_pos L C ω β n).le]
    push_cast
    ring
  · rw [Matrix.single_apply_of_ne n m c p q h, mul_zero, zero_mul, smul_zero]

/-! ### The algebraic pack — the anti-⋆-homomorphism laws -/

/-- `J` is additive. -/
theorem jStage_add (C : Finset M) (a b : DiamondAlg L C) :
    jStage L ω β C (a + b) = jStage L ω β C a + jStage L ω β C b := by
  simp only [jStage, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

/-- `J` sends `0` to `0`. -/
theorem jStage_zero (C : Finset M) : jStage L ω β C 0 = 0 := by
  simp [jStage]

/-- **The conjugate-linear twist**: `J(c • a) = conj c • J a` — the stage conjugation is
    ANTI-linear (through the ᴴ). -/
theorem jStage_smul (C : Finset M) (c : ℂ) (a : DiamondAlg L C) :
    jStage L ω β C (c • a) = starRingEnd ℂ c • jStage L ω β C a := by
  simp only [jStage, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    starRingEnd_apply]

/-- `J 1 = 1` — the cyclic-vector fixed point at stage level (`JΩ = Ω` comes free in J4). -/
theorem jStage_one (C : Finset M) : jStage L ω β C 1 = 1 := by
  rw [jStage, Matrix.conjTranspose_one, mul_one, sqrtGibbs_mul_sqrtInvGibbs]

/-- **`J² = 1`** — the stage conjugation is involutive. -/
theorem jStage_involutive (C : Finset M) (a : DiamondAlg L C) :
    jStage L ω β C (jStage L ω β C a) = a := by
  rw [jStage, jStage_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [sqrtGibbs_mul_sqrtInvGibbs, mul_one, sqrtGibbs_sqrtInvGibbs_cancel]

/-- **The anti-multiplicativity**: `J(a·b) = J(b)·J(a)` — the conjugation reverses
    products (the commutant-side signature). -/
theorem jStage_anti_mul (C : Finset M) (a b : DiamondAlg L C) :
    jStage L ω β C (a * b) = jStage L ω β C b * jStage L ω β C a := by
  simp only [jStage, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [sqrtInvGibbs_sqrtGibbs_cancel]

/-! ### The polar-core identities — the order guard made theorems -/

/-- **The S̄-core**: `J ∘ Δ^{1/2} = ᴴ` — composing the half-power with the conjugation
    recovers the ⋆ (this is the S̄ = J∘Δ^{1/2} side of the polar decomposition, at stage
    level; J5 transports it to the GNS core). -/
theorem jStage_deltaHalfStage (C : Finset M) (a : DiamondAlg L C) :
    jStage L ω β C (deltaHalfStage L ω β C a) = aᴴ := by
  rw [jStage, deltaHalfStage, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    sqrtGibbs_conjTranspose, sqrtInvGibbs_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [sqrtGibbs_mul_sqrtInvGibbs, mul_one, sqrtGibbs_sqrtInvGibbs_cancel]

/-- **The F-core (ORDER GUARD)**: `Δ^{1/2} ∘ J = modAut ρ ∘ ᴴ` — the OTHER composition is
    NOT the ⋆ but the ⋆ twisted by the full modular automorphism: `Δ^{1/2}(J a) = ρ·aᴴ·ρ⁻¹`
    (this is F = Δ^{1/2}∘J, matching `rightConj_sq_conjTranspose_eq_modAut`). -/
theorem deltaHalfStage_jStage (C : Finset M) (a : DiamondAlg L C) :
    deltaHalfStage L ω β C (jStage L ω β C a) = modAut (gibbsDensity L C ω β) aᴴ := by
  rw [deltaHalfStage, jStage, modAut, invOf_gibbsDensity, ← sqrtGibbs_mul_self,
    ← sqrtInvGibbs_mul_self]
  simp only [Matrix.mul_assoc]

/-- **`(Δ^{1/2})² = Δ`-core**: the half-power squares to the finite modular automorphism —
    `Δ^{1/2}(Δ^{1/2} a) = modAut ρ a` (the two √ρ-conjugations compose into the full
    ρ-conjugation). -/
theorem deltaHalfStage_sq (C : Finset M) (a : DiamondAlg L C) :
    deltaHalfStage L ω β C (deltaHalfStage L ω β C a) = modAut (gibbsDensity L C ω β) a := by
  simp only [deltaHalfStage]
  rw [modAut, invOf_gibbsDensity, ← sqrtGibbs_mul_self, ← sqrtInvGibbs_mul_self]
  simp only [Matrix.mul_assoc]

/-- `Δ^{1/2}` is additive. -/
theorem deltaHalfStage_add (C : Finset M) (a b : DiamondAlg L C) :
    deltaHalfStage L ω β C (a + b)
      = deltaHalfStage L ω β C a + deltaHalfStage L ω β C b := by
  simp only [deltaHalfStage, Matrix.mul_add, Matrix.add_mul]

/-- `Δ^{1/2}` is ℂ-linear (NO conjugation twist — the half-power is genuinely linear,
    unlike `jStage`). -/
theorem deltaHalfStage_smul (C : Finset M) (c : ℂ) (a : DiamondAlg L C) :
    deltaHalfStage L ω β C (c • a) = c • deltaHalfStage L ω β C a := by
  simp only [deltaHalfStage, Matrix.mul_smul, Matrix.smul_mul]

/-! ### ★ The single-stage anti-isometry -/

/-- **★ THE ANTI-ISOMETRY**: `⟪J x, J y⟫_C = ⟪y, x⟫_C` — the stage conjugation flips the
    GNS form (anti-unitary signature). Trace-cycling with `ρ = S·S`:
    `tr(ρ·(S⁻¹xS)·(SyᴴS⁻¹)) = tr(S·x·ρ·yᴴ·S⁻¹) = tr(x·ρ·yᴴ) = tr(ρ·yᴴ·x) = ⟪y, x⟫`. -/
theorem gnsInner_jStage (C : Finset M) (x y : DiamondAlg L C) :
    gnsInner L ω β C (jStage L ω β C x) (jStage L ω β C y) = gnsInner L ω β C y x := by
  rw [gnsInner_def, gnsInner_def, jStage_conjTranspose, jStage, ← sqrtGibbs_mul_self]
  simp only [Matrix.mul_assoc]
  -- LHS: tr(S·(S·(S⁻¹·(x·(S·(S·(yᴴ·S⁻¹))))))); RHS: tr(S·(S·(yᴴ·x)))
  rw [sqrtGibbs_sqrtInvGibbs_cancel, sqrtGibbs_sqrtGibbs_head, sqrtGibbs_sqrtGibbs_head]
  -- LHS: tr(S·(x·(ρ·(yᴴ·S⁻¹)))); RHS: tr(ρ·(yᴴ·x))
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  -- LHS: tr(x·(ρ·(yᴴ·(S⁻¹·S))))
  rw [sqrtInvGibbs_mul_sqrtGibbs, mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-! ### The J2 feed — rightConj undoes the conjugation -/

/-- **The J2 feed**: `rightConj (J a) = aᴴ` — the √ρ-conjugation of RightMul.lean exactly
    undoes the stage conjugation's sandwich: `S⁻¹·(S·aᴴ·S⁻¹)·S = aᴴ`. THE ENGINE E1
    (`cornerEmbed_mul_sqrtGibbs`) at `b := jStage a` then gives the cross-stage law of J2
    from this identity. -/
theorem rightConj_jStage (C : Finset M) (a : DiamondAlg L C) :
    rightConj L ω β C (jStage L ω β C a) = aᴴ := by
  rw [rightConj, jStage]
  simp only [Matrix.mul_assoc]
  rw [sqrtInvGibbs_mul_sqrtGibbs, mul_one, sqrtInvGibbs_sqrtGibbs_cancel]

end QIQTH.TowerGNS
