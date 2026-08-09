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

/-! ## §3-C (VACAREA-3) — the massive gapped Loewner spectral window `m²·1 ⪯ K_ε ⪯ (m²+4/ε²)·1`

**Sol's verdict + a discovered Mathlib wall (this session).**  Sol (`gpt-5.6-sol`) confirmed the
*area coefficient* is a multi-session Mathlib wall (dimension-uniform quasi-local Green-function
decay `|K^{−1/2}(x,y)| ≤ C e^{−c|x−y|}`, periodic-distance boundary summation, Schatten control of
the symplectic defect — none packaged in Mathlib).  Its recommended green single-session rung was the
uniform symplectic CAP `½ ≤ ν_j ≤ ν_max(ε,m)` via the gapped window + covariance Loewner bounds.

**Discovered wall (checkpoint here).**  The CAP needs *operator monotonicity of `CFC.sqrt`*
(`√(m²·1) ⪯ √K`) and *operator inverse antitonicity* (`K^{1/2} ⪰ m·1 ⟹ K^{−1/2} ⪯ m⁻¹·1`).  In
Mathlib both are proved only over **complex** C⋆-algebras: `NonUnitalCStarAlgebra`/`CStarAlgebra`
*extend* `NormedSpace ℂ` (`Mathlib/Analysis/CStarAlgebra/Classes.lean`), so they do **not** apply to
`Matrix (Fin n) (Fin n) ℝ` (a real algebra).  The eigenvalue-level fallback (`A` Hermitian with
`∀j, c ≤ eig_j A ⟹ c·1 ⪯ A`, and `eig_j(√A) = √(eig_j A)`) is also absent from Mathlib and would
require a spectral-theorem development — i.e. genuinely multi-session.  **The covariance bounds, the
symplectic cap, and the per-site entropy bound are therefore CHECKPOINTED, not forced.**

What lands here (all axiom-free, std-3, finite-dimensional, gapped `m>0`, `n≥2`; **no area claim**):
* `eigenvalue_ub` — dual of `eigenvalue_lb`: `A ⪯ c·1 ⟹ eig_j(A) ≤ c`.
* `smul_le_smul_left`, `submatrix_le` — reusable Loewner-order helpers (scaling; principal-submatrix
  restriction), staged for the eventual cap sub-campaign.
* `shiftMat` (the cyclic permutation matrix `= finRotate`), `shiftMat_transpose_mul` (`Sᵀ S = 1`),
  `diffOp_eq_shift` (`D_ε = ε⁻¹(S − 1)` for `n ≥ 2`).
* **`negLapε_upper`** — the operator-norm-free Laplacian upper bound
  `(4/ε²)·1 − (−Δ_ε) = (ε⁻¹(S+1))ᵀ(ε⁻¹(S+1)) ⪰ 0` (spectrum of `−Δ_ε` in `[0, 4/ε²]`).
* **`couplingK_ge` / `couplingK_le`** — the gapped spectral WINDOW `m²·1 ⪯ K_ε ⪯ (m²+4/ε²)·1`.
* `gaussModeEntropy_mono` — the per-mode entropy is monotone on `[½,∞)` (reusable; the entropy input
  the future volume/area bound will consume). -/

/-- **Dual of `eigenvalue_lb`.**  A Loewner upper bound `A ⪯ c·1` forces every eigenvalue `≤ c`. -/
theorem eigenvalue_ub {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) {c : ℝ} (h : (c • (1 : Matrix ι ι ℝ) - A).PosSemidef) (j : ι) :
    hA.eigenvalues j ≤ c := by
  have hmv : (c • (1 : Matrix ι ι ℝ) - A) *ᵥ (⇑(hA.eigenvectorBasis j))
      = (c - hA.eigenvalues j) • (⇑(hA.eigenvectorBasis j)) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hA.mulVec_eigenvectorBasis j,
      sub_smul]
  have hnn := h.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis j))
  rw [hmv, dotProduct_smul, smul_eq_mul] at hnn
  have hnorm : star (⇑(hA.eigenvectorBasis j) : ι → ℝ) ⬝ᵥ (⇑(hA.eigenvectorBasis j)) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      real_inner_self_eq_norm_sq, hA.eigenvectorBasis.orthonormal.1 j, one_pow]
  rw [hnorm, mul_one] at hnn
  linarith

/-- Scaling a Loewner inequality by a nonnegative scalar. -/
theorem smul_le_smul_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) : c • A ≤ c • B := by
  rw [Matrix.le_iff] at h ⊢
  rw [← smul_sub]
  exact h.smul hc

/-- Restricting a Loewner inequality to a principal submatrix on a region `s`. -/
theorem submatrix_le {n : ℕ} (s : Finset (Fin n)) {A B : Matrix (Fin n) (Fin n) ℝ} (h : A ≤ B) :
    A.submatrix (Subtype.val : {x // x ∈ s} → Fin n) (Subtype.val : {x // x ∈ s} → Fin n)
      ≤ B.submatrix (Subtype.val : {x // x ∈ s} → Fin n) (Subtype.val : {x // x ∈ s} → Fin n) := by
  rw [Matrix.le_iff] at h ⊢
  have key := h.submatrix (Subtype.val : {x // x ∈ s} → Fin n)
  rwa [Matrix.submatrix_sub] at key

/-! ### The cyclic shift matrix and the Laplacian upper bound -/

/-- The cyclic **shift matrix** `S` (`= finRotate` as a permutation matrix): `S_{i j} = [j = i+1]`
    with `i+1` taken cyclically.  As a permutation matrix it is orthogonal (`Sᵀ S = 1`). -/
noncomputable def shiftMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := (finRotate n).permMatrix ℝ

theorem shiftMat_apply (n : ℕ) (i j : Fin n) :
    shiftMat n i j = if j = finRotate n i then 1 else 0 := by
  show (Equiv.toPEquiv (finRotate n)).toMatrix i j = _
  rw [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp only [Option.mem_some_iff]
  exact if_congr eq_comm rfl rfl

/-- `Sᵀ S = 1`: the shift matrix is orthogonal (it is a permutation matrix). -/
theorem shiftMat_transpose_mul (n : ℕ) : (shiftMat n)ᵀ * shiftMat n = 1 := by
  unfold shiftMat
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

/-- `(finRotate n i).val = (i.val + 1) % n` for `n ≥ 2` (the cyclic successor). -/
theorem finRotate_val {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (finRotate n i).val = (i.val + 1) % n := by
  haveI : NeZero n := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n by omega)]

/-- **`D_ε = ε⁻¹(S − 1)`** for `n ≥ 2`: the forward-difference operator is `ε⁻¹` times
    (shift − identity).  (For `n ≥ 2` the `j = i+1` and `j = i` cases are disjoint.) -/
theorem diffOp_eq_shift {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) : diffOp ε n = ε⁻¹ • (shiftMat n - 1) := by
  haveI : NeZero n := ⟨by omega⟩
  ext i j
  have hji : (j = finRotate n i) ↔ (j.val = (i.val + 1) % n) := by
    rw [Fin.ext_iff, finRotate_val hn i]
  have hne : (i.val + 1) % n ≠ i.val := by
    rcases lt_or_ge (i.val + 1) n with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · have h1 : i.val + 1 = n := le_antisymm (by omega) h
      rw [h1, Nat.mod_self]; omega
  simp only [diffOp, Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, shiftMat_apply,
    Matrix.one_apply, smul_eq_mul]
  congr 1
  by_cases h1 : j.val = (i.val + 1) % n
  · have hj_ne_i : ¬ (i = j) := by
      intro h; rw [← h] at h1; exact hne h1.symm
    rw [if_pos h1, if_pos (hji.mpr h1), if_neg hj_ne_i]; ring
  · rw [if_neg h1, if_neg (fun h => h1 (hji.mp h))]
    by_cases h2 : j = i
    · rw [if_pos h2, if_pos h2.symm]; ring
    · rw [if_neg h2, if_neg (fun h => h2 h.symm)]; ring

/-- **The Laplacian upper bound** `(4/ε²)·1 − (−Δ_ε) ⪰ 0`, i.e. `−Δ_ε ⪯ (4/ε²)·1`.  Proved by the
    operator-norm-free factorization `(4/ε²)·1 − (−Δ_ε) = (ε⁻¹(S+1))ᵀ(ε⁻¹(S+1))` (using `Sᵀ S = 1`
    and `−Δ_ε = (ε⁻¹(S−1))ᵀ(ε⁻¹(S−1))`).  The spectrum of `−Δ_ε` sits in `[0, 4/ε²]`. -/
theorem negLapε_upper {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (_hε : ε ≠ 0) :
    ((4 / ε ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) - negLapε ε n).PosSemidef := by
  have hSS : (shiftMat n)ᵀ * shiftMat n = 1 := shiftMat_transpose_mul n
  have hE : (4 / ε ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) - negLapε ε n
      = (ε⁻¹ • (shiftMat n + 1))ᵀ * (ε⁻¹ • (shiftMat n + 1)) := by
    unfold negLapε
    rw [diffOp_eq_shift hn ε]
    simp only [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_add,
      Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_one, Matrix.one_mul, hSS]
    module
  rw [hE]
  have := Matrix.posSemidef_conjTranspose_mul_self (ε⁻¹ • (shiftMat n + 1))
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- **The gapped spectral window (lower):** `m²·1 ⪯ K_ε` (the mass gap). -/
theorem couplingK_ge (ε m : ℝ) (n : ℕ) :
    (m ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ couplingK ε m n := by
  rw [Matrix.le_iff]
  have hcancel : couplingK ε m n - (m ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) = negLapε ε n := by
    unfold couplingK; abel
  rw [hcancel]; exact negLapε_posSemidef ε n

/-- The gapped upper cutoff `b_ε := m² + 4/ε²`. -/
noncomputable def bcap (ε m : ℝ) : ℝ := m ^ 2 + 4 / ε ^ 2

/-- **The gapped spectral window (upper):** `K_ε ⪯ (m²+4/ε²)·1`. -/
theorem couplingK_le {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : ε ≠ 0) (m : ℝ) :
    couplingK ε m n ≤ (bcap ε m) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [Matrix.le_iff]
  have hkey : (bcap ε m) • (1 : Matrix (Fin n) (Fin n) ℝ) - couplingK ε m n
      = (4 / ε ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) - negLapε ε n := by
    unfold bcap couplingK; rw [add_smul]; abel
  rw [hkey]; exact negLapε_upper hn hε

/-- **`gaussModeEntropy` is monotone on `[½, ∞)`** (a reusable local lemma; the per-mode entropy is
    increasing above the Heisenberg floor because its derivative `log((ν+½)/(ν−½)) > 0` there). -/
theorem gaussModeEntropy_mono {a b : ℝ} (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    QIQTH.GaussianStateEntropy.gaussModeEntropy a ≤ QIQTH.GaussianStateEntropy.gaussModeEntropy b := by
  have hmono : MonotoneOn QIQTH.GaussianStateEntropy.gaussModeEntropy (Set.Icc (1 / 2) b) := by
    have hdiff : DifferentiableOn ℝ QIQTH.GaussianStateEntropy.gaussModeEntropy
        (interior (Set.Icc (1 / 2) b)) := by
      intro x hx
      rw [interior_Icc] at hx
      exact (QIQTH.GaussianStateEntropy.gaussModeEntropy_hasDerivAt
        hx.1).differentiableAt.differentiableWithinAt
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      QIQTH.GaussianStateEntropy.gaussModeEntropy_continuous.continuousOn hdiff
    intro x hx
    rw [interior_Icc] at hx
    rw [(QIQTH.GaussianStateEntropy.gaussModeEntropy_hasDerivAt hx.1).deriv]
    exact (QIQTH.GaussianStateEntropy.gaussModeEntropy_deriv_pos hx.1).le
  exact hmono ⟨ha, hab⟩ ⟨ha.trans hab, le_refl b⟩ hab

/-! ## §3-C.1 (VACAREA-4) — the real-Hermitian spectral-order layer

The Mathlib-gap fill VACAREA-3 flagged: over `Matrix (Fin n) (Fin n) ℝ` (a *real* algebra), Mathlib's
operator-monotonicity of `CFC.sqrt` is available only over complex C⋆-algebras.  We supply the
eigenvalue-level bridge instead, via `Matrix.IsHermitian.spectral_theorem`:

* **`loewner_of_eigenvalues_ge` / `loewner_of_eigenvalues_le`** — the *converses* of the existing
  `eigenvalue_lb` / `eigenvalue_ub`: for a real Hermitian `A`, `(∀ j, c ≤ eig_j A) ↔ c·1 ⪯ A` and
  dually `(∀ j, eig_j A ≤ C) ↔ A ⪯ C·1` (Loewner order ↔ eigenvalue bounds).  Proved by conjugating
  the diagonal `diagonal (eig − c)` (PSD) by the eigenvector unitary of the spectral theorem.
* **`eigenvalues_sqrt`** — the square-root spectral identity `eig_j (CFC.sqrt A) = √(eig_j A)` for
  `A` PosSemidef, aligning the SORTED eigenvalue indices via the charpoly-root/`mergeSort` uniqueness
  the library uses for `sort_roots_charpoly_eq_eigenvalues₀` (√ monotone preserves the antitone
  order), then transferring `eigenvalues₀ → eigenvalues` through the shared reindexing. -/

/-- **Converse of `eigenvalue_lb`.**  If every eigenvalue of a real Hermitian `A` is `≥ c`, then
    `c·1 ⪯ A`.  Proof: `A − c·1 = U · diagonal(eig − c) · Uᴴ` by the spectral theorem, and
    `diagonal(eig − c)` is PSD, so its unitary conjugate is PSD. -/
theorem loewner_of_eigenvalues_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {c : ℝ} (h : ∀ j, c ≤ hA.eigenvalues j) :
    c • (1 : Matrix ι ι ℝ) ≤ A := by
  classical
  rw [Matrix.le_iff]
  have hspec : A = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hA.eigenvectorUnitary
      (diagonal hA.eigenvalues) := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hA.spectral_theorem
  have hdiag : (diagonal (fun j => hA.eigenvalues j - c)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => sub_nonneg.mpr (h j))
  have hdd : diagonal (fun j => hA.eigenvalues j - c)
      = diagonal hA.eigenvalues - c • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_ne hij]
  have hEq : A - c • (1 : Matrix ι ι ℝ)
      = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hA.eigenvectorUnitary
          (diagonal (fun j => hA.eigenvalues j - c)) := by
    rw [hdd, map_sub, map_smul, map_one, ← hspec]
  rw [hEq, Unitary.conjStarAlgAut_apply]
  exact hdiag.mul_mul_conjTranspose_same _

/-- **Converse of `eigenvalue_ub`.**  If every eigenvalue of a real Hermitian `A` is `≤ C`, then
    `A ⪯ C·1`. -/
theorem loewner_of_eigenvalues_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {C : ℝ} (h : ∀ j, hA.eigenvalues j ≤ C) :
    A ≤ C • (1 : Matrix ι ι ℝ) := by
  classical
  rw [Matrix.le_iff]
  have hspec : A = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hA.eigenvectorUnitary
      (diagonal hA.eigenvalues) := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hA.spectral_theorem
  have hdiag : (diagonal (fun j => C - hA.eigenvalues j)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => sub_nonneg.mpr (h j))
  have hdd : diagonal (fun j => C - hA.eigenvalues j)
      = C • (1 : Matrix ι ι ℝ) - diagonal hA.eigenvalues := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_ne hij]
  have hEq : C • (1 : Matrix ι ι ℝ) - A
      = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hA.eigenvectorUnitary
          (diagonal (fun j => C - hA.eigenvalues j)) := by
    rw [hdd, map_sub, map_smul, map_one, ← hspec]
  rw [hEq, Unitary.conjStarAlgAut_apply]
  exact hdiag.mul_mul_conjTranspose_same _

open Polynomial in
/-- **The square-root spectral identity** `eig_j (CFC.sqrt A) = √(eig_j A)` for `A` PosSemidef real
    Hermitian.  The SORTED eigenvalue indices align because `Real.sqrt` is monotone, so it preserves
    the antitone order that `Matrix.IsHermitian.eigenvalues₀` is defined by; we reuse the library's
    charpoly-root `mergeSort` uniqueness (`sort_roots_charpoly_eq_eigenvalues₀`). -/
theorem eigenvalues_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (hSqrt : (CFC.sqrt A).IsHermitian) (j : ι) :
    hSqrt.eigenvalues j = Real.sqrt (hA.1.eigenvalues j) := by
  classical
  have hmono : Monotone Real.sqrt := fun _ _ hxy => Real.sqrt_le_sqrt hxy
  have hre : ∀ x : ℝ, RCLike.re x = x := fun x => RCLike.ofReal_re x
  -- `CFC.sqrt A = cfc g A` with `g x = √(x.toNNReal)`, and its charpoly `= ∏ (X − C √eig_i)`.
  have hcfc : CFC.sqrt A = _root_.cfc (fun x : ℝ => (NNReal.sqrt x.toNNReal : ℝ)) A := by
    rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A hA.nonneg]
  have hcp : (CFC.sqrt A).charpoly
      = ∏ i, (X - C (Real.sqrt (hA.1.eigenvalues i) : ℝ)) := by
    rw [hcfc, hA.1.charpoly_cfc_eq]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hg : (NNReal.sqrt (hA.1.eigenvalues i).toNNReal : ℝ)
        = Real.sqrt (hA.1.eigenvalues i) := by
      rw [Real.coe_sqrt, Real.coe_toNNReal _ (hA.eigenvalues_nonneg i)]
    simp only [hg, RCLike.ofReal_real_eq_id, id_eq]
  -- Roots (real parts) of the two charpolys, as explicit multisets.
  have hRA : A.charpoly.roots.map RCLike.re = Multiset.map hA.1.eigenvalues Finset.univ.val := by
    rw [hA.1.roots_charpoly_eq_eigenvalues, Multiset.map_map]
    exact Multiset.map_congr rfl (fun x _ => by simp [Function.comp, hre])
  have hRS : (CFC.sqrt A).charpoly.roots.map RCLike.re
      = Multiset.map (Real.sqrt ∘ hA.1.eigenvalues) Finset.univ.val := by
    rw [hcp, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map]
      exact Multiset.map_congr rfl (fun x _ => by simp [Function.comp, hre])
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  -- `A`'s eigenvalue multiset equals the sorted list `ofFn eigenvalues₀`.
  have hMA : A.charpoly.roots.map RCLike.re = (↑(List.ofFn hA.1.eigenvalues₀) : Multiset ℝ) := by
    rw [← hA.1.sort_roots_charpoly_eq_eigenvalues₀]
    exact (Multiset.sort_eq _ _).symm
  have hEO : Multiset.map hA.1.eigenvalues Finset.univ.val
      = (↑(List.ofFn hA.1.eigenvalues₀) : Multiset ℝ) := by
    rw [← hRA]; exact hMA
  -- Reduce the goal to the antitone `eigenvalues₀` level; then to sorted-list uniqueness.
  suffices h0 : hSqrt.eigenvalues₀ = Real.sqrt ∘ hA.1.eigenvalues₀ by
    have hj := congrFun h0 ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)
    simpa only [Matrix.IsHermitian.eigenvalues, Function.comp_apply] using hj
  rw [← List.ofFn_inj, ← hSqrt.sort_roots_charpoly_eq_eigenvalues₀, hRS,
    show Multiset.map (Real.sqrt ∘ hA.1.eigenvalues) Finset.univ.val
        = (↑(List.ofFn (Real.sqrt ∘ hA.1.eigenvalues₀)) : Multiset ℝ) by
      rw [← Multiset.map_map, hEO, Multiset.map_coe, List.map_ofFn],
    Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact (hmono.comp_antitone (Matrix.IsHermitian.eigenvalues₀_antitone hA.1)).sortedGE_ofFn

/-! ## §3-C.2 (VACAREA-4) — the two sqrt Loewner bounds unblocked by the spectral-order layer

These are the first two lemmas of the symplectic-cap chain VACAREA-3 removed; they follow directly
from the gapped spectral window (`couplingK_ge` / `couplingK_le`) via the eigenvalue converses and
the square-root spectral identity.  (The remaining chain — `Xcov_le`, `Pcov_le`, `redX_le`,
`redP_le`, `redSymM_le`, `redSympEig_le`, `redEntropy_le` — is landed in §3-C.3 (VACAREA-5) via the
*inverse Loewner bound* `loewner_inv_le` (`m·1 ⪯ A ⟹ A⁻¹ ⪯ m⁻¹·1`, proved directly at the
eigenvector level, bypassing the sorted inverse-eigenvalue identity which is false under the
order-reversing `x⁻¹`).  No area claim.) -/

/-- **The sqrt Loewner lower bound** `m·1 ⪯ K^{1/2}`.  From the mass gap `m²·1 ⪯ K_ε` via the
    real-Hermitian spectral-order layer: `eig_j(K^{1/2}) = √(eig_j K) ≥ √(m²) = m`. -/
theorem m_le_sqrtK (ε : ℝ) {m : ℝ} {n : ℕ} (hm : 0 < m) :
    m • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ sqrtK ε m n := by
  have hKpsd : (couplingK ε m n).PosSemidef := (couplingK_posDef ε m n hm).posSemidef
  have hsqrtH : (CFC.sqrt (couplingK ε m n)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).1
  have hbound : ∀ j, m ≤ hsqrtH.eigenvalues j := by
    intro j
    rw [eigenvalues_sqrt hKpsd hsqrtH j]
    have hlb : m ^ 2 ≤ hKpsd.1.eigenvalues j :=
      eigenvalue_lb hKpsd.1 (Matrix.le_iff.mp (couplingK_ge ε m n)) j
    calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm.le).symm
      _ ≤ Real.sqrt (hKpsd.1.eigenvalues j) := Real.sqrt_le_sqrt hlb
  exact loewner_of_eigenvalues_ge hsqrtH hbound

/-- **The sqrt Loewner upper bound** `K^{1/2} ⪯ √(m²+4/ε²)·1`.  From the gapped window
    `K_ε ⪯ (m²+4/ε²)·1` via `eig_j(K^{1/2}) = √(eig_j K) ≤ √(m²+4/ε²)`. -/
theorem sqrtK_le {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : ε ≠ 0) {m : ℝ} (hm : 0 < m) :
    sqrtK ε m n ≤ Real.sqrt (bcap ε m) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hKpsd : (couplingK ε m n).PosSemidef := (couplingK_posDef ε m n hm).posSemidef
  have hsqrtH : (CFC.sqrt (couplingK ε m n)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).1
  have hbound : ∀ j, hsqrtH.eigenvalues j ≤ Real.sqrt (bcap ε m) := by
    intro j
    rw [eigenvalues_sqrt hKpsd hsqrtH j]
    exact Real.sqrt_le_sqrt (eigenvalue_ub hKpsd.1 (Matrix.le_iff.mp (couplingK_le hn hε m)) j)
  exact loewner_of_eigenvalues_le hsqrtH hbound

/-! ## §3-C.3 (VACAREA-5) — the inverse Loewner bound and the per-site (VOLUME) entropy cap

The tail VACAREA-4 checkpointed.  The one genuinely new Mathlib-gap fill is the **inverse Loewner
bound** `loewner_inv_le`: for PosDef real Hermitian `A`, `c·1 ⪯ A ⟹ A⁻¹ ⪯ c⁻¹·1`.  This is the
inverse analogue of the sqrt bounds, but — because `x ↦ x⁻¹` is *antitone* (it REVERSES the sorted
eigenvalue order that `eigenvalues₀` is defined by, unlike the monotone `√`) — the pointwise
sorted-index identity `eig_j(A⁻¹) = (eig_j A)⁻¹` is FALSE at the reindexed `eigenvalues` level.  We
therefore bypass the sorted identity entirely and prove the Loewner bound directly at the eigenvector
level: for each eigenvector `v` of `A⁻¹` with eigenvalue `μ`, `A v = μ⁻¹ v`, and testing the PSD
matrix `A − c·1` against `v` gives `c ≤ μ⁻¹`, i.e. `μ ≤ c⁻¹`; then `loewner_of_eigenvalues_le`.

The rest of the chain is mechanical Loewner algebra on top of VACAREA-4's `m_le_sqrtK` / `sqrtK_le`:
`Xcov_le` (via `loewner_inv_le`), `Pcov_le`, their submatrix restrictions `redX_le` / `redP_le`, the
conjugated `redSymM_le` (`√X_Ω·redP·√X_Ω ⪯ P_max·redX ⪯ P_max·X_max·1`), the symplectic cap
`redSympEig_le`, and finally the **per-site VOLUME entropy bound** `redEntropy_le`:
`S(ρ_Ω) ≤ |Ω|·h(ν_max)`.

**⚠ HONEST SCOPE.**  `redEntropy_le` is the VOLUME-compatible UPPER bound — it caps the entropy by
the number of sites `|Ω| = s.card`.  It is **NOT** the area law and **NOT** an area lower bound.  The
AREA coefficient (the `S ∝ A_geom` surface density) is the flagged multi-session wall (`VACUUM_AREA_
LAW_PLAN.md` §3-C/D: dimension-uniform quasi-local Green-function decay, boundary summation, Schatten
control — none packaged in Mathlib).  This brick closes the *physicality cap*, not the area scaling. -/

/-- **The inverse Loewner bound** `c·1 ⪯ A ⟹ A⁻¹ ⪯ c⁻¹·1` for PosDef real Hermitian `A` (`c > 0`).
    The inverse analogue of the sqrt Loewner bounds, but proved directly at the eigenvector level
    (not via a sorted eigenvalue identity, which is false here because `x⁻¹` reverses the sorted
    order): each eigenvector `v` of `A⁻¹` with eigenvalue `μ` satisfies `A v = μ⁻¹ v`, and testing
    `A − c·1 ⪰ 0` against `v` gives `c ≤ μ⁻¹`, i.e. `μ ≤ c⁻¹`; conclude via `loewner_of_eigenvalues_le`. -/
theorem loewner_inv_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) {c : ℝ} (hc : 0 < c)
    (h : c • (1 : Matrix ι ι ℝ) ≤ A) : A⁻¹ ≤ c⁻¹ • (1 : Matrix ι ι ℝ) := by
  have hAinv : (A⁻¹).PosDef := hA.inv
  have hHerm : (A⁻¹).IsHermitian := hAinv.1
  have hUnit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hPSD : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef := Matrix.le_iff.mp h
  refine loewner_of_eigenvalues_le hHerm (fun j => ?_)
  have hμpos : 0 < hHerm.eigenvalues j := hAinv.eigenvalues_pos j
  have hAv : A⁻¹ *ᵥ ⇑(hHerm.eigenvectorBasis j)
      = hHerm.eigenvalues j • ⇑(hHerm.eigenvectorBasis j) := hHerm.mulVec_eigenvectorBasis j
  have hAmul : A *ᵥ ⇑(hHerm.eigenvectorBasis j)
      = (hHerm.eigenvalues j)⁻¹ • ⇑(hHerm.eigenvectorBasis j) := by
    have h1 : A *ᵥ (A⁻¹ *ᵥ ⇑(hHerm.eigenvectorBasis j))
        = hHerm.eigenvalues j • (A *ᵥ ⇑(hHerm.eigenvectorBasis j)) := by
      rw [hAv, Matrix.mulVec_smul]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hUnit, Matrix.one_mulVec] at h1
    have h2 : (hHerm.eigenvalues j)⁻¹ • ⇑(hHerm.eigenvectorBasis j)
        = (hHerm.eigenvalues j)⁻¹ • (hHerm.eigenvalues j • (A *ᵥ ⇑(hHerm.eigenvectorBasis j))) :=
      congrArg (fun w => (hHerm.eigenvalues j)⁻¹ • w) h1
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hμpos), one_smul] at h2
    exact h2.symm
  have hmv : (A - c • (1 : Matrix ι ι ℝ)) *ᵥ ⇑(hHerm.eigenvectorBasis j)
      = ((hHerm.eigenvalues j)⁻¹ - c) • ⇑(hHerm.eigenvectorBasis j) := by
    rw [Matrix.sub_mulVec, hAmul, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  have hnn := hPSD.dotProduct_mulVec_nonneg (⇑(hHerm.eigenvectorBasis j))
  rw [hmv, dotProduct_smul, smul_eq_mul] at hnn
  have hnorm : star (⇑(hHerm.eigenvectorBasis j) : ι → ℝ) ⬝ᵥ (⇑(hHerm.eigenvectorBasis j)) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      real_inner_self_eq_norm_sq, hHerm.eigenvectorBasis.orthonormal.1 j, one_pow]
  rw [hnorm, mul_one] at hnn
  have hcle : c ≤ (hHerm.eigenvalues j)⁻¹ := by linarith
  have hfin := inv_anti₀ hc hcle
  rwa [inv_inv] at hfin

/-- **The position covariance upper bound** `X = ½K^{−1/2} ⪯ (1/2·m⁻¹)·1`.  From the sqrt lower bound
    `m·1 ⪯ K^{1/2}` (`m_le_sqrtK`) via the inverse Loewner bound `K^{−1/2} ⪯ m⁻¹·1`. -/
theorem Xcov_le (ε : ℝ) {m : ℝ} {n : ℕ} (hm : 0 < m) :
    Xcov ε m n ≤ (1 / 2 * m⁻¹) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hinv : (sqrtK ε m n)⁻¹ ≤ m⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) :=
    loewner_inv_le (sqrtK_posDef ε m n hm) hm (m_le_sqrtK ε hm)
  calc Xcov ε m n = (1 / 2 : ℝ) • (sqrtK ε m n)⁻¹ := rfl
    _ ≤ (1 / 2 : ℝ) • (m⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) :=
        smul_le_smul_left hinv (by norm_num)
    _ = (1 / 2 * m⁻¹) • (1 : Matrix (Fin n) (Fin n) ℝ) := by rw [smul_smul]

/-- **The momentum covariance upper bound** `P = ½K^{1/2} ⪯ (1/2·√(m²+4/ε²))·1`.  From the sqrt
    upper bound `K^{1/2} ⪯ √(m²+4/ε²)·1` (`sqrtK_le`). -/
theorem Pcov_le (ε : ℝ) {m : ℝ} {n : ℕ} (hn : 2 ≤ n) (hε : ε ≠ 0) (hm : 0 < m) :
    Pcov ε m n ≤ (1 / 2 * Real.sqrt (bcap ε m)) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  calc Pcov ε m n = (1 / 2 : ℝ) • sqrtK ε m n := rfl
    _ ≤ (1 / 2 : ℝ) • (Real.sqrt (bcap ε m) • (1 : Matrix (Fin n) (Fin n) ℝ)) :=
        smul_le_smul_left (sqrtK_le hn hε hm) (by norm_num)
    _ = (1 / 2 * Real.sqrt (bcap ε m)) • (1 : Matrix (Fin n) (Fin n) ℝ) := by rw [smul_smul]

/-- **The reduced position covariance upper bound** `X_Ω ⪯ (1/2·m⁻¹)·1` (principal submatrix of
    `Xcov_le`). -/
theorem redX_le (ε : ℝ) {m : ℝ} {n : ℕ} (s : Finset (Fin n)) (hm : 0 < m) :
    redX ε m n s ≤ (1 / 2 * m⁻¹) • (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ) := by
  classical
  have h := submatrix_le s (Xcov_le ε hm)
  have hEq : ((1 / 2 * m⁻¹) • (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix
        (Subtype.val : {x // x ∈ s} → Fin n) Subtype.val
      = (1 / 2 * m⁻¹) • (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    · have hv : (i : Fin n) ≠ (j : Fin n) := fun hh => hij (Subtype.ext hh)
      simp [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
        Matrix.one_apply_ne hv]
  rw [hEq] at h
  exact h

/-- **The reduced momentum covariance upper bound** `P_Ω ⪯ (1/2·√(m²+4/ε²))·1` (principal submatrix
    of `Pcov_le`). -/
theorem redP_le (ε : ℝ) {m : ℝ} {n : ℕ} (s : Finset (Fin n))
    (hn : 2 ≤ n) (hε : ε ≠ 0) (hm : 0 < m) :
    redP ε m n s ≤ (1 / 2 * Real.sqrt (bcap ε m)) • (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ) := by
  classical
  have h := submatrix_le s (Pcov_le ε hn hε hm)
  have hEq : ((1 / 2 * Real.sqrt (bcap ε m)) • (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix
        (Subtype.val : {x // x ∈ s} → Fin n) Subtype.val
      = (1 / 2 * Real.sqrt (bcap ε m)) • (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    · have hv : (i : Fin n) ≠ (j : Fin n) := fun hh => hij (Subtype.ext hh)
      simp [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
        Matrix.one_apply_ne hv]
  rw [hEq] at h
  exact h

/-- **The symmetrized reduced product upper bound** `√X_Ω·P_Ω·√X_Ω ⪯ (P_max·X_max)·1`, with
    `P_max = ½√(m²+4/ε²)`, `X_max = ½m⁻¹`.  Conjugate `redP_le` by the self-adjoint `√X_Ω`
    (`√X_Ω·(P_max·1)·√X_Ω = P_max·X_Ω`), then dominate `X_Ω` by `redX_le`. -/
theorem redSymM_le (ε : ℝ) {m : ℝ} {n : ℕ} (s : Finset (Fin n))
    (hn : 2 ≤ n) (hε : ε ≠ 0) (hm : 0 < m) :
    redSymM ε m n s
      ≤ ((1 / 2 * Real.sqrt (bcap ε m)) * (1 / 2 * m⁻¹))
          • (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ) := by
  have hsa : IsSelfAdjoint (CFC.sqrt (redX ε m n s)) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hconj := hsa.conjugate_le_conjugate (redP_le ε s hn hε hm)
  have hRR : CFC.sqrt (redX ε m n s) * CFC.sqrt (redX ε m n s) = redX ε m n s :=
    CFC.sqrt_mul_sqrt_self _ (redX_posDef ε m n s hm).posSemidef.nonneg
  have hR1 : CFC.sqrt (redX ε m n s)
      * ((1 / 2 * Real.sqrt (bcap ε m)) • (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ))
      * CFC.sqrt (redX ε m n s) = (1 / 2 * Real.sqrt (bcap ε m)) • redX ε m n s := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hRR]
  calc redSymM ε m n s
      = CFC.sqrt (redX ε m n s) * redP ε m n s * CFC.sqrt (redX ε m n s) := rfl
    _ ≤ (1 / 2 * Real.sqrt (bcap ε m)) • redX ε m n s := by rw [← hR1]; exact hconj
    _ ≤ (1 / 2 * Real.sqrt (bcap ε m)) • ((1 / 2 * m⁻¹) • (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ)) :=
        smul_le_smul_left (redX_le ε s hm) (by positivity)
    _ = ((1 / 2 * Real.sqrt (bcap ε m)) * (1 / 2 * m⁻¹))
          • (1 : Matrix {x // x ∈ s} {x // x ∈ s} ℝ) := by rw [smul_smul]

/-- The uniform symplectic-eigenvalue **cap** `ν_max = √(P_max·X_max) = √(½√(m²+4/ε²)·½m⁻¹)`. -/
noncomputable def sympCap (ε m : ℝ) : ℝ :=
  Real.sqrt ((1 / 2 * Real.sqrt (bcap ε m)) * (1 / 2 * m⁻¹))

/-- **The reduced symplectic eigenvalues are capped** `ν_j ≤ ν_max` — the upper companion of the
    Heisenberg floor `redSympEig_ge_half`.  Via `eigenvalue_ub` on `redSymM_le`, then `Real.sqrt`. -/
theorem redSympEig_le (ε : ℝ) {m : ℝ} {n : ℕ} (s : Finset (Fin n))
    (hn : 2 ≤ n) (hε : ε ≠ 0) (hm : 0 < m) (j : {x // x ∈ s}) :
    redSympEig ε m n s hm j ≤ sympCap ε m := by
  unfold redSympEig sympCap
  exact Real.sqrt_le_sqrt
    (eigenvalue_ub (redSymM_isHermitian ε m n s hm) (Matrix.le_iff.mp (redSymM_le ε s hn hε hm)) j)

/-- **The per-site (VOLUME) entanglement-entropy upper bound** `S(ρ_Ω) ≤ |Ω|·h(ν_max)`.  Each mode
    entropy `h(ν_j)` is squeezed between the floor `ν_j ≥ ½` (`redSympEig_ge_half`) and the cap
    `ν_j ≤ ν_max` (`redSympEig_le`); `gaussModeEntropy` is monotone there (`gaussModeEntropy_mono`),
    so `h(ν_j) ≤ h(ν_max)`, and summing over the `|Ω| = s.card` sites gives the bound.

    **⚠ This is the VOLUME-compatible physicality cap, NOT the area law** — it caps entropy by the
    NUMBER OF SITES, not the boundary area.  The area coefficient `S ∝ A_geom` is the flagged
    multi-session Mathlib wall (`VACUUM_AREA_LAW_PLAN.md` §3-C/D). -/
theorem redEntropy_le (ε : ℝ) {m : ℝ} {n : ℕ} (s : Finset (Fin n))
    (hn : 2 ≤ n) (hε : ε ≠ 0) (hm : 0 < m) :
    redEntropy ε m n s hm
      ≤ (s.card : ℝ) * QIQTH.GaussianStateEntropy.gaussModeEntropy (sympCap ε m) := by
  unfold redEntropy
  calc ∑ j, QIQTH.GaussianStateEntropy.gaussModeEntropy (redSympEig ε m n s hm j)
      ≤ ∑ _j : {x // x ∈ s}, QIQTH.GaussianStateEntropy.gaussModeEntropy (sympCap ε m) := by
        apply Finset.sum_le_sum
        intro j _
        exact gaussModeEntropy_mono (redSympEig_ge_half ε m n s hm j)
          (redSympEig_le ε s hn hε hm j)
    _ = (s.card : ℝ) * QIQTH.GaussianStateEntropy.gaussModeEntropy (sympCap ε m) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

end QIQTH.VacuumAreaLaw
