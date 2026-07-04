/-
  ID1 (THE_IDENTIFICATION_PLAN.md) — THE FINITE MODULAR EIGENBASIS: matrix units are
  `modAut` eigenvectors with eigenvalue `w_n/w_m`; ρ is diagonal BY CONSTRUCTION.

  The Gibbs density is `Matrix.diagonal (gibbsWeight …)` by definition (Dynamics.lean), its
  explicit inverse `gibbsInv` is the diagonal of inverse weights, and the finite modular
  automorphism `modAut ρ x = ρ·x·⅟ρ` (FiniteModularTheory.lean) therefore acts on the
  matrix-unit basis as a PURE weight-ratio scaling:

      modAut ρ_β (E_{nm} c) = (w_n / w_m) • (E_{nm} c).

  No spectral theorem is needed anywhere — everything is diagonal-times-single entrywise
  calculus. This is the one genuinely NEW finite lemma of THE IDENTIFICATION campaign:
  together with `cornerFlow_single` (Generator.lean — the physical flow is a pure phase
  `exp(i·t·(log w_n − log w_m))` on the SAME basis) and `towerModularOp_of`
  (ModularOp.lean — Δ acts as `modAut ρ` on the pure-component core), all three operators
  (σ_t, Δ, U_t) share the matrix-unit eigenbasis, which ID2–ID4 transport to the GNS
  completion to identify `towerFlow t = Δ^{it}` on a dense span — WITHOUT exponential
  recovery.

  Deliverables:
  • `invOf_gibbsDensity` — `⅟ρ_β = gibbsInv` (the abstract `⅟` of the `gibbsInvertible`
    instance pinned to the explicit diagonal via `invOf_eq_right_inv`);
  • `modAut_gibbsDensity_single` ★ — the eigenvector equation above;
  • `gibbsWeight_div_pos` — the eigenvalue `w_n/w_m` is strictly positive (the downstream
    positivity handle for the ID2 resolvent transport);
  • `towerFlow_of_eq_sum_single` — the coerced orbit decomposition of the transported flow
    (the horbit identity inside `hasDerivAt_towerFlow_of`, extracted standalone for ID4).

  HONEST SCOPE (binding): finite-stage statements only. No Δ-eigenvector claim is made here
  (that is ID2); no identification `towerFlow = Δ^{it}` is claimed (that is ID4). Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.Generator

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped Matrix DirectSum

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The explicit inverse of the Gibbs density -/

/-- **The abstract `⅟` is the explicit diagonal**: `⅟(gibbsDensity) = gibbsInv` — the
    inverse supplied by the `gibbsInvertible` instance is pinned to the explicit diagonal of
    inverse weights via `invOf_eq_right_inv` (the right-multiplication identity is the
    entrywise `w·w⁻¹ = 1` cancellation, weights strictly positive). Every downstream
    `modAut` computation can now replace the abstract `⅟ρ_β` by a concrete diagonal. -/
theorem invOf_gibbsDensity (C : Finset M) :
    ⅟(gibbsDensity L C ω β) = gibbsInv L C ω β := by
  refine invOf_eq_right_inv ?_
  rw [gibbsInv, gibbsDensity, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ (gibbsWeight_pos L C ω β i).ne',
    Complex.ofReal_one]

/-! ### The eigenvalue positivity handle -/

/-- **The modular eigenvalue is strictly positive**: `0 < w_n / w_m` — the downstream
    positivity handle (ID2 needs `0 < δ` for the resolvent eigenvector transport). -/
theorem gibbsWeight_div_pos (C : Finset M) (n m : Micro L C) :
    0 < gibbsWeight L C ω β n / gibbsWeight L C ω β m :=
  div_pos (gibbsWeight_pos L C ω β n) (gibbsWeight_pos L C ω β m)

/-! ### ★ The finite modular eigenbasis -/

/-- **★ THE FINITE MODULAR EIGENBASIS**: the matrix units are eigenvectors of the finite
    modular automorphism with eigenvalue the Gibbs weight ratio —
    `modAut ρ_β (E_{nm} c) = (w_n / w_m) • (E_{nm} c)`. Entrywise: conjugating a
    single-entry matrix by the diagonal density picks up `w_n` from the left and `w_m⁻¹`
    from the right at the `(n,m)` entry, `0` elsewhere. This is the σ₋ᵢ-side of the shared
    eigenbasis; `cornerFlow_single` is the σ_t-side (pure phase, same basis, same sign
    convention `n`-minus-`m`). -/
theorem modAut_gibbsDensity_single (C : Finset M) (n m : Micro L C) (c : ℂ) :
    modAut (gibbsDensity L C ω β) (Matrix.single n m c)
      = ((gibbsWeight L C ω β n / gibbsWeight L C ω β m : ℝ) : ℂ)
        • Matrix.single n m c := by
  rw [modAut, invOf_gibbsDensity, gibbsDensity, gibbsInv]
  ext p q
  simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : n = p ∧ m = q
  · obtain ⟨rfl, rfl⟩ := h
    rw [Matrix.single_apply_same, smul_eq_mul]
    push_cast
    ring
  · rw [Matrix.single_apply_of_ne n m c p q h, mul_zero, zero_mul, smul_zero]

/-! ### The coerced orbit decomposition, standalone -/

/-- **The coerced orbit decomposition of the transported flow** (the horbit identity inside
    `hasDerivAt_towerFlow_of`, extracted standalone for ID4): the flowed coerced pure
    component is the finite sum of its phase-rotated coerced matrix-unit components —
    `U_t ↑(of C a) = Σ_{n,m} exp(i·t·(log w_n − log w_m)) • ↑(of C (E_{nm} (a n m)))`.
    Route: `towerFlow_coe` + `flowRaw_of` to land on the corner, `cornerFlow_eq_sum_single`
    to decompose, `towerOf_sum_single_smul_coe` to push the sum back through the coercion. -/
theorem towerFlow_of_eq_sum_single (t : ℝ) (C : Finset M) (a : DiamondAlg L C) :
    towerFlow L ω β t ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β)
      = ∑ n : Micro L C, ∑ m : Micro L C,
          Complex.exp (Complex.I * t * ((Real.log (gibbsWeight L C ω β n)
              - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ))
            • ((towerOf L ω β C (Matrix.single n m (a n m)) : TowerPre L ω β) :
                TowerGNS L ω β) := by
  rw [towerFlow_coe]
  have h1 : flowPre L ω β t (towerOf L ω β C a)
      = towerOf L ω β C (cornerFlow L ω β C t a) := flowRaw_of L ω β t C a
  rw [h1]
  conv_lhs => rw [cornerFlow_eq_sum_single L ω β C t a]
  exact towerOf_sum_single_smul_coe L ω β C a _

end QIQTH.TowerGNS
