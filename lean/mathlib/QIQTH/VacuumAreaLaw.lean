/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# VACAREA-1 — the regulated finite harmonic chain and its vacuum Gaussian data

The MECHANICAL §3-A foundation of the VACUUM AREA-LAW campaign (`VACUUM_AREA_LAW_PLAN.md`,
Route 1, lemma-group A).  It sets up, on a finite 1-D periodic lattice `Fin n`, the regulated free
scalar and the Gaussian data whose reduced entropy the campaign later shows scales with the
geometric boundary — *here nothing about area is claimed*.

What lands (all axiom-free, std-3):

* **The regulated coupling** `K_ε = m² − Δ_ε` (`couplingK`) as a real symmetric matrix, built as
  `(m²)·1 + Dᵀ_ε D_ε` with `D_ε` the (periodic) forward-difference operator scaled by `ε⁻¹`, so
  `Dᵀ_ε D_ε = −Δ_ε` is the discrete negative Laplacian.  The `DᵀD` form makes the Laplacian
  positive-semidefinite for free.
* **Positive-definiteness** `couplingK_posDef` for `m > 0` (`(m²)·1` positive-definite +
  `−Δ_ε` positive-semidefinite).
* **The vacuum covariances** `X = ½ K^{−1/2}` (`Xcov`), `P = ½ K^{1/2}` (`Pcov`) via the Mathlib
  matrix continuous functional calculus `CFC.sqrt`; each is positive-definite (`Xcov_posDef`,
  `Pcov_posDef`).
* **The canonical-commutation product** `X · P = ¼·1` (`Xcov_mul_Pcov`, and its mirror
  `Pcov_mul_Xcov`): the vacuum saturates Heisenberg globally — the *global* state is pure (all
  global symplectic eigenvalues `= ½`).
* **The reduced Gaussian state on a site subset** `s : Finset (Fin n)`: the reduced covariances
  `redX = X_Ω`, `redP = P_Ω` (submatrices, still positive-definite), the **symmetrized product**
  `redSymM = √X_Ω · P_Ω · √X_Ω` (positive-semidefinite, Hermitian — the symmetric conjugate of the
  non-symmetric `X_Ω P_Ω`), its **symplectic spectrum** `redSympEig j = √(eigenvalue_j(redSymM))`
  (`= spec √(X_Ω P_Ω)`), and the **entanglement entropy** `redEntropy = Σ_j gaussModeEntropy(ν_j)`
  built with the EXISTING per-mode Srednicki entropy `QIQTH.GaussianStateEntropy.gaussModeEntropy`.
* **Nonnegativity** `redEntropy_nonneg`, conditional on the Heisenberg floor `∀ j, ½ ≤ ν_j`
  (carried as a hypothesis here — see the WALL note below).

## HONEST SCOPE
This is finite-dimensional Gaussian **infrastructure**, NOT the area law.  Nothing here claims
`S ∝ A_geom`; the entropy machinery is area/volume-blind (`BoundaryGaussianAreaLaw` /
`bulk_entropy_volume_law` already show finite Gaussian modes give either an area OR a volume law
depending on where the modes localize).

**TODO (the analysis WALLs, per plan §3 B/C/D — NOT attempted here):**
  * the Heisenberg floor `∀ j, ½ ≤ redSympEig j` for a *reduced* Gaussian state (the reduced
    covariance is a valid physical covariance) — supplied as a hypothesis `hfloor`, not derived;
  * dimension-UNIFORM Gaussian-entropy estimates (§3-B);
  * fractional lattice Green-function decay of `K^{±1/2}(x,y)` (§3-C);
  * the planar surface entropy density and its IR integrability (§3-D) — the coefficient source;
  * localization to the geometric boundary and the noncommuting limits (§3-E/G).

Axiom-free.
-/
import Mathlib
import QIQTH.GaussianStateEntropy

namespace QIQTH.VacuumAreaLaw

open Matrix
open scoped MatrixOrder

/-! ## §0 — eigenvalue lower bounds from the Loewner order (a small reusable lemma) -/

/-- **A Loewner lower bound `c·1 ⪯ A` forces every eigenvalue of `A` above `c`.**  For a Hermitian
    real matrix `A`, if `A − c·1` is positive-semidefinite then each eigenvalue is `≥ c`.  Proof:
    test the PSD matrix `A − c·1` against a unit eigenvector `v` of `A` (eigenvalue `λ`), giving
    `0 ≤ (λ − c)·‖v‖² = λ − c`. -/
theorem eigenvalue_lb {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) {c : ℝ} (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) (j : ι) :
    c ≤ hA.eigenvalues j := by
  have hmv : (A - c • (1 : Matrix ι ι ℝ)) *ᵥ (⇑(hA.eigenvectorBasis j))
      = (hA.eigenvalues j - c) • (⇑(hA.eigenvectorBasis j)) := by
    rw [Matrix.sub_mulVec, hA.mulVec_eigenvectorBasis j, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_smul]
  have hnn := h.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis j))
  rw [hmv, dotProduct_smul, smul_eq_mul] at hnn
  have hnorm : star (⇑(hA.eigenvectorBasis j) : ι → ℝ) ⬝ᵥ (⇑(hA.eigenvectorBasis j)) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      real_inner_self_eq_norm_sq, hA.eigenvectorBasis.orthonormal.1 j, one_pow]
  rw [hnorm, mul_one] at hnn
  linarith

/-! ## §3-A.1 — the regulated coupling `K_ε = m² − Δ_ε` on a periodic chain -/

/-- The (periodic) forward-difference operator scaled by `ε⁻¹`:
    `(D_ε)_{i j} = ε⁻¹·(δ_{j, i+1} − δ_{j, i})`, with `i+1` taken cyclically in `Fin n`
    (periodic boundary conditions).  `Dᵀ_ε D_ε` is the discrete negative Laplacian `−Δ_ε`. -/
noncomputable def diffOp (ε : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ε⁻¹ * (if j.val = (i.val + 1) % n then 1 else if j = i then -1 else 0)

/-- The discrete **negative Laplacian** `−Δ_ε := Dᵀ_ε D_ε` (a graph Laplacian of the cycle,
    diagonal `2ε⁻²`, nearest-neighbour `−ε⁻²`).  As `AᵀA` it is manifestly symmetric and
    positive-semidefinite. -/
noncomputable def negLapε (ε : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (diffOp ε n)ᵀ * diffOp ε n

/-- `−Δ_ε` is positive-semidefinite (it is `AᵀA`). -/
theorem negLapε_posSemidef (ε : ℝ) (n : ℕ) : (negLapε ε n).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (diffOp ε n)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- **The regulated coupling `K_ε = m² − Δ_ε`**: `(m²)·1 + Dᵀ_ε D_ε`, a real symmetric matrix. -/
noncomputable def couplingK (ε m : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (m ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) + negLapε ε n

/-- **The regulated coupling is positive-definite for `m > 0`.**  `(m²)·1` is positive-definite
    (mass gap) and `−Δ_ε` is positive-semidefinite, so the sum is positive-definite.  This is the
    finite-volume, massive positivity of the free-scalar coupling. -/
theorem couplingK_posDef (ε m : ℝ) (n : ℕ) (hm : 0 < m) : (couplingK ε m n).PosDef := by
  have h1 : ((m ^ 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    (Matrix.PosDef.one).smul (by positivity)
  exact h1.add_posSemidef (negLapε_posSemidef ε n)

/-! ## §3-A.2 — the vacuum covariances `X = ½ K^{−1/2}`, `P = ½ K^{1/2}` -/

/-- The positive-definite square root `K^{1/2}` of the coupling (via the Mathlib matrix CFC). -/
noncomputable def sqrtK (ε m : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt (couplingK ε m n)

/-- `K^{1/2} · K^{1/2} = K`. -/
theorem sqrtK_mul_self (ε m : ℝ) (n : ℕ) (hm : 0 < m) :
    sqrtK ε m n * sqrtK ε m n = couplingK ε m n := by
  unfold sqrtK
  exact CFC.sqrt_mul_sqrt_self _ (couplingK_posDef ε m n hm).posSemidef.nonneg

/-- `K^{1/2}` has invertible determinant (`(det K^{1/2})² = det K ≠ 0`). -/
theorem sqrtK_isUnit_det (ε m : ℝ) (n : ℕ) (hm : 0 < m) : IsUnit (sqrtK ε m n).det := by
  have hKunit : IsUnit (couplingK ε m n).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (couplingK_posDef ε m n hm).isUnit
  apply isUnit_of_mul_isUnit_left (y := (sqrtK ε m n).det)
  rw [← Matrix.det_mul, sqrtK_mul_self ε m n hm]; exact hKunit

/-- `K^{1/2}` is positive-definite (nonnegative square root with nonzero determinant). -/
theorem sqrtK_posDef (ε m : ℝ) (n : ℕ) (hm : 0 < m) : (sqrtK ε m n).PosDef := by
  have hpsd : (sqrtK ε m n).PosSemidef := by
    unfold sqrtK; exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  exact hpsd.posDef_iff_det_ne_zero.mpr (sqrtK_isUnit_det ε m n hm).ne_zero

/-- The vacuum **position** covariance `X = ½ K^{−1/2}`. -/
noncomputable def Xcov (ε m : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (sqrtK ε m n)⁻¹

/-- The vacuum **momentum** covariance `P = ½ K^{1/2}`. -/
noncomputable def Pcov (ε m : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • sqrtK ε m n

/-- `X = ½ K^{−1/2}` is positive-definite. -/
theorem Xcov_posDef (ε m : ℝ) (n : ℕ) (hm : 0 < m) : (Xcov ε m n).PosDef :=
  ((sqrtK_posDef ε m n hm).inv).smul (by norm_num : (0 : ℝ) < 1 / 2)

/-- `P = ½ K^{1/2}` is positive-definite. -/
theorem Pcov_posDef (ε m : ℝ) (n : ℕ) (hm : 0 < m) : (Pcov ε m n).PosDef :=
  (sqrtK_posDef ε m n hm).smul (by norm_num : (0 : ℝ) < 1 / 2)

/-- **The canonical-commutation product `X · P = ¼·1`.**  `(½ K^{−1/2})(½ K^{1/2}) = ¼·1`: the
    global vacuum saturates the uncertainty product, so its symplectic eigenvalues are all `½` and
    the global state is pure (zero entanglement entropy).  This is the sanity anchor for the reduced
    (entangled) states below. -/
theorem Xcov_mul_Pcov (ε m : ℝ) (n : ℕ) (hm : 0 < m) :
    Xcov ε m n * Pcov ε m n = (1 / 4 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hinv : (sqrtK ε m n)⁻¹ * sqrtK ε m n = 1 :=
    Matrix.nonsing_inv_mul _ (sqrtK_isUnit_det ε m n hm)
  simp only [Xcov, Pcov, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hinv]
  norm_num

/-- The mirror product `P · X = ¼·1` (`X`, `P` are functions of the same `K`, hence commute). -/
theorem Pcov_mul_Xcov (ε m : ℝ) (n : ℕ) (hm : 0 < m) :
    Pcov ε m n * Xcov ε m n = (1 / 4 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hinv : sqrtK ε m n * (sqrtK ε m n)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (sqrtK_isUnit_det ε m n hm)
  simp only [Xcov, Pcov, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hinv]
  norm_num

/-- **The momentum covariance is `¼` of the inverse position covariance**, `P = ¼·X⁻¹`.  Immediate
    from the saturated product `X·P = ¼·1` and invertibility of `X`.  This is the algebraic pivot for
    the reduced Heisenberg floor: it recasts the reduced-state uncertainty as a statement purely about
    principal submatrices of `X` and `X⁻¹`. -/
theorem Pcov_eq (ε m : ℝ) (n : ℕ) (hm : 0 < m) :
    Pcov ε m n = (1 / 4 : ℝ) • (Xcov ε m n)⁻¹ := by
  have hdet : IsUnit (Xcov ε m n).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Xcov_posDef ε m n hm).isUnit
  have h : (Xcov ε m n)⁻¹ * (Xcov ε m n * Pcov ε m n)
      = (Xcov ε m n)⁻¹ * ((1 / 4 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    rw [Xcov_mul_Pcov ε m n hm]
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one] at h

/-! ## §3-A.3 — the reduced Gaussian state on a site subset and its symplectic spectrum

For a region `s : Finset (Fin n)` (index type `{x // x ∈ s}`), the reduced covariances are the
submatrices `X_Ω`, `P_Ω`.  The symplectic eigenvalues are the eigenvalues of `√(X_Ω P_Ω)`.  Since
the product `X_Ω P_Ω` is *not* symmetric, we take the symmetric conjugate
`redSymM := √X_Ω · P_Ω · √X_Ω` (which has the same spectrum, is Hermitian and positive-semidefinite),
read off its eigenvalues, and set `ν_j = √(eigenvalue_j)`.  The entropy is `Σ_j gaussModeEntropy ν_j`. -/

section Region

variable (ε m : ℝ) (n : ℕ) (s : Finset (Fin n))

/-- The reduced **position** covariance `X_Ω` — the submatrix of `X` on the region `s`. -/
noncomputable def redX : Matrix {x // x ∈ s} {x // x ∈ s} ℝ :=
  (Xcov ε m n).submatrix Subtype.val Subtype.val

/-- The reduced **momentum** covariance `P_Ω` — the submatrix of `P` on the region `s`. -/
noncomputable def redP : Matrix {x // x ∈ s} {x // x ∈ s} ℝ :=
  (Pcov ε m n).submatrix Subtype.val Subtype.val

/-- The reduced position covariance is positive-definite (a principal submatrix of a PD matrix). -/
theorem redX_posDef (hm : 0 < m) : (redX ε m n s).PosDef :=
  (Xcov_posDef ε m n hm).submatrix Subtype.coe_injective

/-- The reduced momentum covariance is positive-definite. -/
theorem redP_posDef (hm : 0 < m) : (redP ε m n s).PosDef :=
  (Pcov_posDef ε m n hm).submatrix Subtype.coe_injective

/-- **The symmetrized reduced product** `√X_Ω · P_Ω · √X_Ω`.  This is the symmetric conjugate of the
    (non-symmetric) `X_Ω P_Ω`; it is Hermitian and positive-semidefinite with the same spectrum, so
    its eigenvalues are `ν_j²` — the squared symplectic eigenvalues of the reduced state. -/
noncomputable def redSymM : Matrix {x // x ∈ s} {x // x ∈ s} ℝ :=
  CFC.sqrt (redX ε m n s) * redP ε m n s * CFC.sqrt (redX ε m n s)

/-- The symmetrized reduced product is positive-semidefinite (`Bᴴ A B` with `A = P_Ω` PD and
    `B = √X_Ω` Hermitian). -/
theorem redSymM_posSemidef (hm : 0 < m) : (redSymM ε m n s).PosSemidef := by
  have hR : (CFC.sqrt (redX ε m n s))ᴴ = CFC.sqrt (redX ε m n s) :=
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian).eq
  have h := (redP_posDef ε m n s hm).posSemidef.conjTranspose_mul_mul_same (CFC.sqrt (redX ε m n s))
  rwa [hR] at h

/-- The symmetrized reduced product is Hermitian, so its eigenvalues are well-defined. -/
theorem redSymM_isHermitian (hm : 0 < m) : (redSymM ε m n s).IsHermitian :=
  (redSymM_posSemidef ε m n s hm).1

/-- **The reduced symplectic spectrum** `ν_j = √(eigenvalue_j(√X_Ω P_Ω √X_Ω)) = spec √(X_Ω P_Ω)`.
    These are the symplectic eigenvalues of the reduced Gaussian state, the input the per-mode
    Srednicki entropy `gaussModeEntropy` consumes. -/
noncomputable def redSympEig (hm : 0 < m) (j : {x // x ∈ s}) : ℝ :=
  Real.sqrt ((redSymM_isHermitian ε m n s hm).eigenvalues j)

/-- The reduced symplectic eigenvalues are nonnegative (they are square roots). -/
theorem redSympEig_nonneg (hm : 0 < m) (j : {x // x ∈ s}) : 0 ≤ redSympEig ε m n s hm j :=
  Real.sqrt_nonneg _

/-- **The reduced entanglement entropy** `S(ρ_Ω) = Σ_j gaussModeEntropy(ν_j)` — the Williamson/
    Srednicki sum over the reduced symplectic spectrum, built with the EXISTING per-mode entropy
    `QIQTH.GaussianStateEntropy.gaussModeEntropy`.  (No claim of area scaling — see file scope.) -/
noncomputable def redEntropy (hm : 0 < m) : ℝ :=
  ∑ j, QIQTH.GaussianStateEntropy.gaussModeEntropy (redSympEig ε m n s hm j)

/-- **The reduced entanglement entropy is nonnegative**, given the Heisenberg floor `∀ j, ½ ≤ ν_j`
    on the reduced symplectic spectrum (carried as a hypothesis — the reduced covariance being a
    valid physical covariance is the §3-B WALL, not derived here).  Entanglement is never negative. -/
theorem redEntropy_nonneg (hm : 0 < m) (hfloor : ∀ j, (1 : ℝ) / 2 ≤ redSympEig ε m n s hm j) :
    0 ≤ redEntropy ε m n s hm :=
  Finset.sum_nonneg fun j _ =>
    QIQTH.GaussianStateEntropy.gaussModeEntropy_nonneg (hfloor j)

/-! ## §3-B — the reduced Heisenberg floor `ν_j ≥ ½` (VACAREA-2)

The reduced covariance of a *pure* global Gaussian state is a *physical* (mixed) covariance, so its
symplectic eigenvalues respect the pure-state floor `ν ≥ ½`.  We prove this by Sol's twice-Schur
argument, which collapses the whole statement to the classic inequality
`(X_Ω)⁻¹ ⪯ (X⁻¹)_Ω` (principal submatrix of the inverse dominates the inverse of the submatrix). -/

/-- `P_Ω = ¼·(X⁻¹)_Ω`: the reduced momentum covariance is `¼` of the principal submatrix of the
    inverse position covariance (from the global `P = ¼·X⁻¹`). -/
theorem redP_eq (hm : 0 < m) :
    redP ε m n s = (1 / 4 : ℝ) • ((Xcov ε m n)⁻¹).submatrix Subtype.val Subtype.val := by
  unfold redP
  rw [Pcov_eq ε m n hm]
  rfl

/-- **The reduced Heisenberg floor at the covariance level:** `√X_Ω · P_Ω · √X_Ω ⪰ ¼·1`.

Sol's twice-Schur route.  The vacuum saturates `X·P = ¼·1`, so `P = ¼·X⁻¹` and the block matrix
`[[X, 1],[1, X⁻¹]]` is positive-semidefinite (its Schur complement over `X` is `X⁻¹ − X⁻¹ = 0`).  A
principal submatrix of a PSD matrix is PSD, so `[[X_Ω, 1],[1, (X⁻¹)_Ω]] ⪰ 0`, whose Schur complement
over `X_Ω` is `(X⁻¹)_Ω − (X_Ω)⁻¹ ⪰ 0`, i.e. `(X_Ω)⁻¹ ⪯ (X⁻¹)_Ω`.  Since `P_Ω = ¼·(X⁻¹)_Ω` this gives
`¼·(X_Ω)⁻¹ ⪯ P_Ω`; conjugating by the self-adjoint `√X_Ω` yields
`¼·1 = √X_Ω·(¼·(X_Ω)⁻¹)·√X_Ω ⪯ √X_Ω·P_Ω·√X_Ω = redSymM`. -/
theorem redSymM_ge_quarter (hm : 0 < m) :
    ((1 / 4 : ℝ) • (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ)) ≤ redSymM ε m n s := by
  classical
  have hX : (Xcov ε m n).PosDef := Xcov_posDef ε m n hm
  have hRX : (redX ε m n s).PosDef := redX_posDef ε m n s hm
  letI iX : Invertible (Xcov ε m n) :=
    (Xcov ε m n).invertibleOfIsUnitDet ((Matrix.isUnit_iff_isUnit_det _).mp hX.isUnit)
  letI iRX : Invertible (redX ε m n s) :=
    (redX ε m n s).invertibleOfIsUnitDet ((Matrix.isUnit_iff_isUnit_det _).mp hRX.isUnit)
  -- (1) the global PSD block matrix `[[X, 1],[1, X⁻¹]]`
  have hblockG :
      (Matrix.fromBlocks (Xcov ε m n) 1 (1 : Matrix (Fin n) (Fin n) ℝ)ᴴ (Xcov ε m n)⁻¹).PosSemidef := by
    rw [hX.fromBlocks₁₁ 1 (Xcov ε m n)⁻¹]
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, sub_self]
    exact Matrix.PosSemidef.zero
  -- (2) restrict to the region and identify the reduced block matrix
  have hEq :
      (Matrix.fromBlocks (Xcov ε m n) 1 (1 : Matrix (Fin n) (Fin n) ℝ)ᴴ (Xcov ε m n)⁻¹).submatrix
          (Sum.map Subtype.val Subtype.val) (Sum.map Subtype.val Subtype.val)
        = Matrix.fromBlocks (redX ε m n s) (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ)
            (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ)ᴴ
            (((Xcov ε m n)⁻¹).submatrix Subtype.val Subtype.val) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.submatrix_apply, redX, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
  have hblockR :
      (Matrix.fromBlocks (redX ε m n s) (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ)
          (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ)ᴴ
          (((Xcov ε m n)⁻¹).submatrix Subtype.val Subtype.val)).PosSemidef := by
    rw [← hEq]; exact hblockG.submatrix _
  -- (3) the Schur complement over `redX`: `(X⁻¹)_Ω − (redX)⁻¹ ⪰ 0`
  have hstep :
      (((Xcov ε m n)⁻¹).submatrix Subtype.val Subtype.val - (redX ε m n s)⁻¹).PosSemidef := by
    have h := (hRX.fromBlocks₁₁ (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ)
      (((Xcov ε m n)⁻¹).submatrix Subtype.val Subtype.val)).1 hblockR
    simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using h
  -- (4) `¼·(redX)⁻¹ ⪯ redP`
  have hP_ge : ((1 / 4 : ℝ) • (redX ε m n s)⁻¹) ≤ redP ε m n s := by
    rw [redP_eq ε m n s hm, Matrix.le_iff, ← smul_sub]
    exact hstep.smul (by norm_num : (0 : ℝ) ≤ 1 / 4)
  -- (5) conjugate by the self-adjoint `√redX`
  have hRR : CFC.sqrt (redX ε m n s) * CFC.sqrt (redX ε m n s) = redX ε m n s :=
    CFC.sqrt_mul_sqrt_self _ (redX_posDef ε m n s hm).posSemidef.nonneg
  have hRunit : IsUnit (CFC.sqrt (redX ε m n s)).det := by
    apply isUnit_of_mul_isUnit_left (y := (CFC.sqrt (redX ε m n s)).det)
    rw [← Matrix.det_mul, hRR]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hRX.isUnit
  have hinvR : (redX ε m n s)⁻¹
      = (CFC.sqrt (redX ε m n s))⁻¹ * (CFC.sqrt (redX ε m n s))⁻¹ := by
    rw [← Matrix.mul_inv_rev, hRR]
  have h1 : CFC.sqrt (redX ε m n s) * (CFC.sqrt (redX ε m n s))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hRunit
  have h2 : (CFC.sqrt (redX ε m n s))⁻¹ * CFC.sqrt (redX ε m n s) = 1 :=
    Matrix.nonsing_inv_mul _ hRunit
  have hcancel : CFC.sqrt (redX ε m n s) * (redX ε m n s)⁻¹ * CFC.sqrt (redX ε m n s) = 1 := by
    rw [hinvR, mul_assoc, mul_assoc, h2, mul_one, h1]
  have hLHS :
      CFC.sqrt (redX ε m n s) * ((1 / 4 : ℝ) • (redX ε m n s)⁻¹) * CFC.sqrt (redX ε m n s)
        = (1 / 4 : ℝ) • (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hcancel]
  have hconj :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (redX ε m n s))).conjugate_le_conjugate hP_ge
  rw [hLHS] at hconj
  exact hconj

/-- **The reduced symplectic eigenvalues obey the Heisenberg floor `ν_j ≥ ½` (VACAREA-2).**  A
    subsystem of a pure Gaussian state is a physical (mixed) Gaussian state, so every symplectic
    eigenvalue of the reduced covariance sits at or above the pure-state floor.  This discharges the
    `hfloor` hypothesis carried in `redEntropy_nonneg`. -/
theorem redSympEig_ge_half (hm : 0 < m) (j : {x // x ∈ s}) :
    (1 : ℝ) / 2 ≤ redSympEig ε m n s hm j := by
  have heig : (1 / 4 : ℝ) ≤ (redSymM_isHermitian ε m n s hm).eigenvalues j :=
    eigenvalue_lb (redSymM_isHermitian ε m n s hm)
      (Matrix.le_iff.mp (redSymM_ge_quarter ε m n s hm)) j
  rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt heig

/-- **The reduced entanglement entropy is unconditionally nonnegative** — the carried `hfloor`
    hypothesis of `redEntropy_nonneg` is now discharged by `redSympEig_ge_half`.  Entanglement is
    never negative, for the *actual* reduced vacuum Gaussian state. -/
theorem redEntropy_nonneg' (hm : 0 < m) : 0 ≤ redEntropy ε m n s hm :=
  redEntropy_nonneg ε m n s hm (fun j => redSympEig_ge_half ε m n s hm j)

end Region

end QIQTH.VacuumAreaLaw
