/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Williamson normal form — W1–W5: decomposition structure, symplectic algebra, carried Youla, sqrt entry point, entropy connection

Williamson's theorem states that a real symmetric positive-definite `2n × 2n` matrix `M` can be
brought to the block-diagonal form `Sᵀ M S = D ⊕ D` (with `D = diagonal ν` the *symplectic
eigenvalues*) by a symplectic `S` (`Sᵀ J S = J`).  The symplectic spectrum `ν` is the entropy /
holography input consumed by `QIQTH.GaussianStateEntropy.gaussStateEntropy`.

This file supplies **W1** and **W2** of the Williamson campaign:

* **W1 (guaranteed green):** the `WilliamsonDecomp` data structure (a symplectic `S` congruence-
  diagonalizing `M` to `D ⊕ D`), the symplectic-form algebra (`one`/`mul` closure, `J` membership),
  and the two determinant lemmas — `(det S)² = 1` for symplectic `S` (Mathlib only proves
  `IsUnit (det S)`; `det = 1` is a Mathlib TODO, so we derive `(det S)² = 1` locally), and the
  determinant of the Williamson block form `= (∏ νᵢ)²`.
* **W2 (the carried hypothesis):** the `YoulaDecomp` structure — the real **antisymmetric block
  normal form** `Oᵀ A O = [[0, D], [-D, 0]]` for an orthogonal `O`.  This is **CARRIED** (a
  structure whose proof of existence is assumed, never a Lean axiom): the Youla decomposition of a
  real antisymmetric matrix is **absent from Mathlib** (0 hits) and is the genuine analytic
  frontier of this campaign — the `haug` analogue.

* **W3 (the matrix-square-root entry point + the honest reduction):** `williamsonAux_antisymm` —
  the genuine `CFC.sqrt`-usability lemma proving the Williamson auxiliary `A := M^{1/2} J M^{1/2}`
  is antisymmetric (over `ℝ`, using `PosSemidef.isHermitian` + `Jᵀ = -J`); together with the honest
  reduction theorems `williamsonDecomp_of_construction` (the structure constructor exposed as an
  interface) and `williamson_of_construction_exists` (Williamson inhabited *given the existence of
  the constructed symplectic congruence*).  The block-matrix construction of that congruence
  `S = M^{-1/2} O (block-√ν)` — proving `S ∈ symplecticGroup` and `Sᵀ M S = D ⊕ D` — is the heavy
  algebra and remains **CARRIED** here (packaged as the `hconstr` hypothesis, never faked).

* **W4–W5 (the entropy connection — the QG payoff, landing on the structure directly):** the
  Gaussian entanglement entropy `WilliamsonDecomp.entropy := ∑ᵢ gaussModeEntropy (νᵢ)` read off the
  symplectic spectrum of a Williamson decomposition (summed over the mode index `l`), its
  nonnegativity `WilliamsonDecomp.entropy_nonneg` given the Heisenberg floor `∀ i, ½ ≤ νᵢ` (the
  hypothesis `gaussModeEntropy_nonneg` requires), the identification
  `williamson_entropy_eq_gaussStateEntropy` with the repo's `gaussStateEntropy` when `l = Fin n`
  (definitional), and the `n = 1` consistency `oneMode_entropy_consistency` — a single-mode
  (`l = Unit`) Williamson decomposition whose eigenvalue is `oneModeSympEig a b c = √(ab − c²)` has
  entropy `gaussModeEntropy (√(ab − c²)) ≥ 0`, wiring the repo's `oneModeSympEig` into the general
  structure through the Heisenberg-floor bound `oneModeSympEig_ge_half`.

**Honest scope.**  W1–W2 are scaffolding + one carried hypothesis; W3 adds the real square-root
entry point and packages the still-carried block construction; W4–W5 land the entropy bridge on the
`WilliamsonDecomp` structure directly (it does *not* need the carried construction — it consumes the
symplectic spectrum `ν` a decomposition already carries).  Williamson is *not yet* proved
unconditionally — it is proved **conditional on Youla** (and, at W3, on the constructed-`S`
existence).  The decomposition itself carries Youla + the S-construction; the entropy is a genuine
function of its spectrum.  Nothing here unlocks the area-law `S ∝ A` scaling (the entropy machinery
is area/volume-blind).  Axiom-free.
-/
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Matrix.Order
import QIQTH.GaussianStateEntropy

namespace QIQTH.Williamson

open Matrix
open scoped MatrixOrder

variable {l : Type*} [DecidableEq l] [Fintype l]

/-! ### W1 — the `WilliamsonDecomp` structure and symplectic algebra -/

/-- **A Williamson decomposition of a real symmetric matrix `M`.**  Bundles a symplectic congruence
    `S` (`S ∈ symplecticGroup`, i.e. `Sᵀ J S = J`) together with the nonnegative symplectic
    eigenvalues `ν` that bring `M` to the block-diagonal Williamson normal form
    `Sᵀ M S = diagonal ν ⊕ diagonal ν`. -/
structure WilliamsonDecomp (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) where
  /-- The symplectic transformation diagonalizing `M`. -/
  S : Matrix (l ⊕ l) (l ⊕ l) ℝ
  /-- `S` is symplectic: `Sᵀ J S = J` (equivalently `S J Sᵀ = J`). -/
  hSymp : S ∈ symplecticGroup l ℝ
  /-- The symplectic eigenvalues. -/
  ν : l → ℝ
  /-- The symplectic eigenvalues are nonnegative. -/
  hν : ∀ i, 0 ≤ ν i
  /-- `S` brings `M` to the Williamson block-diagonal normal form. -/
  hDiag : Sᵀ * M * S = Matrix.fromBlocks (Matrix.diagonal ν) 0 0 (Matrix.diagonal ν)

/-- The **symplectic spectrum** carried by a Williamson decomposition — the entropy/holography input
    consumed by `QIQTH.GaussianStateEntropy.gaussStateEntropy`. -/
def WilliamsonDecomp.sympSpec {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (W : WilliamsonDecomp M) : l → ℝ :=
  W.ν

/-- The identity is symplectic (`Submonoid.one_mem`). -/
theorem symplectic_one_mem : (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) ∈ symplecticGroup l ℝ :=
  (symplecticGroup l ℝ).one_mem

/-- The symplectic matrices are closed under multiplication (`Submonoid.mul_mem`). -/
theorem symplectic_mul_mem {A B : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplecticGroup l ℝ)
    (hB : B ∈ symplecticGroup l ℝ) : A * B ∈ symplecticGroup l ℝ :=
  (symplecticGroup l ℝ).mul_mem hA hB

/-- The canonical skew form `J` is itself symplectic (`SymplecticGroup.J_mem`). -/
theorem symplectic_J_mem : Matrix.J l ℝ ∈ symplecticGroup l ℝ :=
  SymplecticGroup.J_mem l ℝ

/-- **The determinant of a symplectic matrix squares to one.**  Mathlib only records
    `IsUnit (det S)` (`SymplecticGroup.symplectic_det`); the sharper `det S = 1` is a Mathlib TODO.
    We derive the weaker-but-sufficient `(det S)² = 1` here: taking determinants of `Sᵀ J S = J`
    gives `(det S)² · det J = det J`, and `det J ≠ 0` (from `det J · det J = 1`) cancels. -/
theorem symplectic_det_sq {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : S ∈ symplecticGroup l ℝ) :
    (S.det) ^ 2 = 1 := by
  rw [SymplecticGroup.mem_iff'] at hS
  -- take determinants of `Sᵀ * J * S = J`
  have hdet : (Sᵀ * Matrix.J l ℝ * S).det = (Matrix.J l ℝ).det := by rw [hS]
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  -- `hdet : S.det * (J l ℝ).det * S.det = (J l ℝ).det`
  have hJ : (Matrix.J l ℝ).det ≠ 0 := fun h => by
    have hjj := Matrix.J_det_mul_J_det l ℝ
    rw [h, mul_zero] at hjj
    exact zero_ne_one hjj
  have key : S.det * S.det * (Matrix.J l ℝ).det = 1 * (Matrix.J l ℝ).det := by
    rw [one_mul]
    calc S.det * S.det * (Matrix.J l ℝ).det
        = S.det * (Matrix.J l ℝ).det * S.det := by ring
      _ = (Matrix.J l ℝ).det := hdet
  have h2 : S.det * S.det = 1 := mul_right_cancel₀ hJ key
  rw [pow_two]; exact h2

/-- **The determinant of the Williamson block form `diagonal ν ⊕ diagonal ν` is `(∏ νᵢ)²`.**  Via the
    block-triangular determinant (`det_fromBlocks_zero₁₂`) and `det_diagonal`. -/
theorem det_williamson_block (ν : l → ℝ) :
    (Matrix.fromBlocks (Matrix.diagonal ν) 0 0 (Matrix.diagonal ν)).det = (∏ i, ν i) ^ 2 := by
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_diagonal, pow_two]

/-! ### W2 — the carried Youla real antisymmetric normal form

`YoulaDecomp` bundles the real **antisymmetric block normal form** of a real antisymmetric matrix
`A`: an orthogonal `O` with `Oᵀ A O = [[0, D], [-D, 0]]`, `D = diagonal ν`, `ν ≥ 0`.  This is the
skew analogue of the spectral theorem.

**CARRIED — the analytic frontier.**  The Youla decomposition of a real antisymmetric matrix is
**absent from Mathlib** (0 hits) and is the genuine unproved input of this campaign (the `haug`
analogue in the max-flow=min-cut campaign).  It is packaged as a *structure* whose inhabitant is
assumed by the caller — **never** a Lean axiom.  W3 (`williamson_of_youla`, a later increment) will
construct the Williamson `S` *given* an inhabitant of this structure, making Williamson conditional
on Youla, not unconditional. -/

/-- **A Youla (real antisymmetric block normal form) decomposition of `A`.**  An orthogonal `O`
    reducing `A` to the block-antisymmetric form `[[0, diagonal ν], [-(diagonal ν), 0]]` with
    `ν ≥ 0`.  **Carried** (see the section docstring): existence is assumed by the caller, never
    postulated as a Lean axiom. -/
structure YoulaDecomp (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) where
  /-- The orthogonalizing transformation. -/
  O : Matrix (l ⊕ l) (l ⊕ l) ℝ
  /-- `O` is orthogonal: `Oᵀ O = 1`. -/
  hOrth : O ∈ Matrix.orthogonalGroup (l ⊕ l) ℝ
  /-- The (nonnegative) skew normal-form eigenvalues. -/
  ν : l → ℝ
  /-- Nonnegativity of the skew eigenvalues. -/
  hν : ∀ i, 0 ≤ ν i
  /-- `O` brings `A` to the real antisymmetric block normal form. -/
  hNormal : Oᵀ * A * O = Matrix.fromBlocks 0 (Matrix.diagonal ν) (-(Matrix.diagonal ν)) 0

/-- The Youla skew eigenvalues are nonnegative (a trivial projection of the carried datum). -/
theorem YoulaDecomp.sympEig_nonneg {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (Y : YoulaDecomp A) :
    ∀ i, 0 ≤ Y.ν i :=
  Y.hν

/-! ### W3 — toward `williamson_of_youla`: the matrix-square-root entry point and the honest reduction

The Williamson construction hangs on the antisymmetric matrix `A := M^{1/2} J M^{1/2}`, whose Youla
real-skew normal form (carried) supplies the orthogonal `O` and the symplectic eigenvalues.  The
*first* genuine content — the entry point that proves `CFC.sqrt` is usable in this real-matrix
setting — is that `A` is indeed antisymmetric.  This is `williamsonAux_antisymm` below, derived from
`Jᵀ = -J` (`Matrix.J_transpose`) and the self-adjointness of the positive-semidefinite square root
(the `ArakiEntropy` precedent, here over `ℝ` where `conjTranspose = transpose`).

The heavy content — actually **constructing** the symplectic `S = M^{-1/2} O (block-√ν scaling)` and
proving both `S ∈ symplecticGroup` and `Sᵀ M S = D ⊕ D` — is the block-matrix algebra that remains
**carried** here (see `williamson_of_construction_exists`): we package it honestly as an existence
hypothesis on the constructed data, exactly as the max-flow campaign carried its `haug` augmenting
input, rather than fake it. -/

/-- **The Williamson auxiliary matrix `A := M^{1/2} J M^{1/2}` is antisymmetric.**  This is the
    genuine `CFC.sqrt`-usability lemma for the Williamson construction: over `ℝ` the positive-
    semidefinite square root `M^{1/2}` is symmetric (`(M^{1/2})ᵀ = M^{1/2}`, from the
    `PosSemidef.isHermitian` fact and `conjTranspose = transpose` over the trivially-starred `ℝ`),
    and `Jᵀ = -J` (`Matrix.J_transpose`), so `(M^{1/2} J M^{1/2})ᵀ = M^{1/2}(-J)M^{1/2}
    = -(M^{1/2} J M^{1/2})`. -/
theorem williamsonAux_antisymm (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hM : M.PosDef) :
    (CFC.sqrt M * Matrix.J l ℝ * CFC.sqrt M)ᵀ
      = -(CFC.sqrt M * Matrix.J l ℝ * CFC.sqrt M) := by
  -- the square root is symmetric over ℝ (self-adjoint + trivial star)
  have hsT : (CFC.sqrt M)ᵀ = CFC.sqrt M := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian).eq
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hsT, Matrix.J_transpose,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

/-! #### The honest reduction theorems (packaging the carried block-diagonalization) -/

/-- **The `WilliamsonDecomp` constructor, exposed as a reduction.**  Given a symplectic `S` and
    nonnegative `ν` that congruence-diagonalize `M` to the Williamson normal form, a
    `WilliamsonDecomp M` exists.  This is *packaging only* (it merely applies the structure
    constructor) — it names the interface the real construction must hit. -/
def williamsonDecomp_of_construction (M : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) (ν : l → ℝ) (hSymp : S ∈ symplecticGroup l ℝ)
    (hν : ∀ i, 0 ≤ ν i)
    (hDiag : Sᵀ * M * S = Matrix.fromBlocks (Matrix.diagonal ν) 0 0 (Matrix.diagonal ν)) :
    WilliamsonDecomp M :=
  ⟨S, hSymp, ν, hν, hDiag⟩

/-- **The honest Williamson reduction: conditional on the constructed symplectic data.**  Williamson's
    theorem for a real symmetric positive-definite `M` reduces to the *existence* of the constructed
    symplectic congruence `S` (with nonnegative symplectic eigenvalues `ν`) bringing `M` to block-
    diagonal form.  That existence is the block-matrix algebra `S = M^{-1/2} O (block-√ν)` fed by the
    carried Youla datum — the genuine analytic/algebraic frontier, carried here as the hypothesis
    `hconstr` rather than faked.  Given it, `WilliamsonDecomp M` is inhabited. -/
theorem williamson_of_construction_exists (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hM : M.PosDef)
    (hconstr : ∃ (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) (ν : l → ℝ),
      S ∈ symplecticGroup l ℝ ∧ (∀ i, 0 ≤ ν i) ∧
      Sᵀ * M * S = Matrix.fromBlocks (Matrix.diagonal ν) 0 0 (Matrix.diagonal ν)) :
    Nonempty (WilliamsonDecomp M) := by
  obtain ⟨S, ν, hSymp, hν, hDiag⟩ := hconstr
  exact ⟨⟨S, hSymp, ν, hν, hDiag⟩⟩

/-! ### W5 — the entropy connection (the QG payoff)

The symplectic spectrum `ν` a `WilliamsonDecomp` carries is exactly the input the Gaussian
entanglement entropy consumes.  We define the entropy of a decomposition as the sum, over the mode
index `l`, of the per-mode Srednicki entropy `gaussModeEntropy`, matching the shape of the repo's
`QIQTH.GaussianStateEntropy.gaussStateEntropy` (which sums over `Fin n`) but stated over the general
index `l`.  This lands on the structure directly — it does *not* invoke the carried block
construction (W3): it is a genuine function of the spectrum any decomposition already carries. -/

/-- **The Gaussian entanglement entropy of a Williamson decomposition.**  The sum, over the mode
    index `l`, of the per-mode Srednicki entropy `gaussModeEntropy` evaluated at the symplectic
    eigenvalues `ν` — the entropy the symplectic spectrum feeds (see
    `QIQTH.GaussianStateEntropy.gaussStateEntropy`, the `Fin n` version of the same sum). -/
noncomputable def WilliamsonDecomp.entropy {M : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (W : WilliamsonDecomp M) : ℝ :=
  ∑ i, QIQTH.GaussianStateEntropy.gaussModeEntropy (W.ν i)

/-- **The Gaussian entanglement entropy of a Williamson decomposition is nonnegative**, given the
    Heisenberg floor `∀ i, ½ ≤ νᵢ` on the symplectic spectrum (the uncertainty-principle bound
    `gaussModeEntropy_nonneg` requires).  Entanglement is never negative. -/
theorem WilliamsonDecomp.entropy_nonneg {M : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (W : WilliamsonDecomp M) (hfloor : ∀ i, (1 : ℝ) / 2 ≤ W.ν i) : 0 ≤ W.entropy :=
  Finset.sum_nonneg fun i _ => QIQTH.GaussianStateEntropy.gaussModeEntropy_nonneg (hfloor i)

/-- **The decomposition entropy is the repo's `gaussStateEntropy` when the mode index is `Fin n`.**
    Both are the same sum `∑ᵢ gaussModeEntropy (νᵢ)` over `Fin n`, so this is definitional — it
    identifies the structure-level entropy with the standalone Gaussian-state entropy function. -/
theorem williamson_entropy_eq_gaussStateEntropy {n : ℕ}
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (W : WilliamsonDecomp M) :
    W.entropy = QIQTH.GaussianStateEntropy.gaussStateEntropy W.ν :=
  rfl

/-! ### W4 — the `n = 1` consistency: `oneModeSympEig` wired into the structure

For a single mode (`l = Unit`) the symplectic eigenvalue is the repo's
`oneModeSympEig a b c = √(ab − c²)` read off the `2×2` covariance `[[a,c],[c,b]]`.  A one-mode
`WilliamsonDecomp` whose eigenvalue is that value has entropy `gaussModeEntropy (√(ab − c²))`, which
the Heisenberg bound `det ≥ ¼` makes nonnegative (through `oneModeSympEig_ge_half`).  This wires the
repo's single-mode symplectic eigenvalue into the general `WilliamsonDecomp.entropy` at `n = 1`. -/

/-- **The `n = 1` entropy consistency.**  For a single-mode (`l = Unit`) Williamson decomposition
    whose symplectic eigenvalue is the repo's `oneModeSympEig a b c = √(ab − c²)`, the
    decomposition entropy is exactly `gaussModeEntropy (√(ab − c²))`, and — under the Heisenberg
    uncertainty bound `¼ ≤ ab − c²` — it is nonnegative.  This grounds the structure-level entropy
    in physical single-mode covariance data, recovering the repo's `oneModeSympEig`. -/
theorem oneMode_entropy_consistency {M : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ}
    (W : WilliamsonDecomp M) {a b c : ℝ}
    (hν : W.ν () = QIQTH.GaussianStateEntropy.oneModeSympEig a b c)
    (h : (1 : ℝ) / 4 ≤ a * b - c ^ 2) :
    W.entropy
        = QIQTH.GaussianStateEntropy.gaussModeEntropy
          (QIQTH.GaussianStateEntropy.oneModeSympEig a b c)
      ∧ 0 ≤ W.entropy := by
  have hsum : W.entropy
      = QIQTH.GaussianStateEntropy.gaussModeEntropy (W.ν ()) := by
    rw [WilliamsonDecomp.entropy, Fintype.sum_unique]
  refine ⟨by rw [hsum, hν], ?_⟩
  rw [hsum, hν]
  exact QIQTH.GaussianStateEntropy.gaussModeEntropy_nonneg
    (QIQTH.GaussianStateEntropy.oneModeSympEig_ge_half h)

end QIQTH.Williamson
