/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Williamson normal form — W1–W6: decomposition structure, symplectic algebra, carried Youla, sqrt entry point, entropy connection, and the DERIVED S-construction

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
  algebra; **W6 (`williamson_of_youla`) DERIVES it** (see below), so the `hconstr` packaging is now
  a legacy interface, not the live carry.

* **W6 (the block-matrix S-construction — DERIVED, no longer carried):** `williamson_of_youla` —
  given `M.PosDef` and a `YoulaDecomp` of the antisymmetric auxiliary `A = M^{1/2} J M^{1/2}`, it
  **constructs** the symplectic congruence `S = M^{-1/2} O E` (with `E = [[0,√D],[√D,0]]` the
  *block-swapped* root of the Youla spectrum) and proves *both* Williamson conditions —
  `S ∈ symplecticGroup` (`S J Sᵀ = J`, via `E J E = Oᵀ A O`, `O Oᵀ = 1`, and `Ri A Ri = J`) and
  `Sᵀ M S = D ⊕ D` (via `Ri M Ri = 1` and `Oᵀ O = 1`).  The block swap is the sign reconciliation
  between Mathlib's `J = [[0,-1],[1,0]]` and Youla's orientation `[[0,D],[-D,0]]`.  This replaces
  W3's fully-carried construction: Williamson is now conditional **only** on Youla, not additionally
  on the constructed-`S` existence.

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
entry point and the legacy `hconstr` packaging; W4–W5 land the entropy bridge on the
`WilliamsonDecomp` structure directly (it does *not* need the construction — it consumes the
symplectic spectrum `ν` a decomposition already carries); **W6 DERIVES the block-matrix
S-construction** (`williamson_of_youla`), retiring W3's carry.  Williamson is *not yet* proved
unconditionally — it is proved **conditional on Youla alone** (`YoulaDecomp`, the real-antisymmetric
normal form absent from Mathlib).  The single remaining carry is Youla; the S-construction and the
entropy are genuine derivations.  Nothing here unlocks the area-law `S ∝ A` scaling (the entropy
machinery is area/volume-blind).  Axiom-free.
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

/-! ### W6 — `williamson_of_youla`: the block-matrix S-construction, DERIVED

This lands the block-matrix construction that W3 packaged as the carried `hconstr` hypothesis.
Given `M.PosDef` and a Youla decomposition `Y` of the antisymmetric auxiliary
`A := M^{1/2} J M^{1/2}` (`williamsonAux_antisymm`), we **construct** the symplectic congruence
`S := M^{-1/2} O E` and prove *both* Williamson conditions — no longer carried.

Here `R := M^{1/2} = CFC.sqrt M` (symmetric PD), `Ri := R⁻¹` (symmetric, `Ri R = R Ri = 1`,
`Ri M Ri = 1`), and `E := [[0, √D], [√D, 0]]` is the **block-swapped** square root of the Youla
spectrum `D = diagonal ν` (with `√D = diagonal (√νᵢ)`).  The block swap is the sign reconciliation
between Mathlib's `J = [[0,-1],[1,0]]` and Youla's orientation `Oᵀ A O = [[0,D],[-D,0]]`: it is
symmetric, still squares to `E * E = D ⊕ D` (so the diagonalization is unaffected), but flips
`E J E = [[0,D],[-D,0]] = Oᵀ A O` (the *diagonal* `√D ⊕ √D` would give the opposite sign and fail
the symplectic condition).

* **Diagonalize** `Sᵀ M S = D ⊕ D`: `Sᵀ M S = E Oᵀ (Ri M Ri) O E = E (Oᵀ O) E = E E = D ⊕ D`,
  using `Ri M Ri = 1` and `Oᵀ O = 1`.
* **Symplectic** `S J Sᵀ = J`: `S J Sᵀ = Ri O (E J E) Oᵀ Ri = Ri O (Oᵀ A O) Oᵀ Ri = Ri A Ri = J`,
  using `E J E = Oᵀ A O` (Youla), `O Oᵀ = 1`, and `Ri A Ri = Ri R J R Ri = J`.

This is **DERIVED**, replacing W3's fully-carried construction — Williamson is now conditional only
on Youla (`YoulaDecomp`), not additionally on the constructed-`S` existence.  Axiom-free. -/

/-- **The block-swapped root conjugates `J` to the Youla orientation.**  For `E = [[0,D],[D,0]]`
    (block-swapped diagonal), `E J E = [[0, D²], [-D², 0]]`, matching the sign of Youla's
    `Oᵀ A O = [[0, ν], [-ν, 0]]` (the *unswapped* `[[D,0],[0,D]]` would give the opposite sign).
    Extracted as a standalone lemma so the `J`-unfolding rewrite does not trip over the `J` hidden
    in the Youla datum's type. -/
private theorem blockSwapRoot_conj_J (d : l → ℝ) :
    (Matrix.fromBlocks 0 (Matrix.diagonal d) (Matrix.diagonal d) 0) * Matrix.J l ℝ
        * (Matrix.fromBlocks 0 (Matrix.diagonal d) (Matrix.diagonal d) 0)
      = Matrix.fromBlocks 0 (Matrix.diagonal (fun i => d i * d i))
          (-(Matrix.diagonal (fun i => d i * d i))) 0 := by
  rw [show Matrix.J l ℝ = Matrix.fromBlocks 0 (-1) 1 0 from rfl,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul, mul_one, Matrix.diagonal_mul_diagonal]

/-- **The Williamson S-construction, derived from Youla.**  Given `M.PosDef` and a Youla
    decomposition `Y` of the antisymmetric auxiliary `A = M^{1/2} J M^{1/2}`, the block matrix
    `S = M^{-1/2} O E` (with `E = [[0,√D],[√D,0]]` the block-swapped root of the Youla spectrum) is
    symplectic and congruence-diagonalizes `M` to the Williamson normal form.  This constructs the
    `WilliamsonDecomp M` that W3 carried as a hypothesis. -/
noncomputable def williamson_of_youla (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hM : M.PosDef)
    (Y : YoulaDecomp (CFC.sqrt M * Matrix.J l ℝ * CFC.sqrt M)) : WilliamsonDecomp M := by
  -- the symmetric positive-definite square root `R = M^{1/2}` and its inverse `Ri`
  set R : Matrix (l ⊕ l) (l ⊕ l) ℝ := CFC.sqrt M with hR
  have hM0 : (0 : Matrix (l ⊕ l) (l ⊕ l) ℝ) ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM0
  have hRsymm : Rᵀ = R := by
    rw [hR, ← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian).eq
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hRdet : IsUnit R.det := by
    apply isUnit_of_mul_isUnit_left (y := R.det)
    rw [← Matrix.det_mul, hRR]; exact hMdet
  set Ri : Matrix (l ⊕ l) (l ⊕ l) ℝ := R⁻¹ with hRi
  have hRiR : Ri * R = 1 := Matrix.nonsing_inv_mul R hRdet
  have hRRi : R * Ri = 1 := Matrix.mul_nonsing_inv R hRdet
  have hRisymm : Riᵀ = Ri := by rw [hRi, Matrix.transpose_nonsing_inv, hRsymm]
  have hRiMRi : Ri * M * Ri = 1 := by
    have e : Ri * M * Ri = (Ri * R) * (R * Ri) := by rw [← hRR]; simp only [Matrix.mul_assoc]
    rw [e, hRiR, hRRi, Matrix.one_mul]
  -- the block-swapped root `E` of the Youla spectrum
  have hdd : Matrix.diagonal (fun i => Real.sqrt (Y.ν i))
        * Matrix.diagonal (fun i => Real.sqrt (Y.ν i)) = Matrix.diagonal Y.ν := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (Y.hν i)
  set E : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
    Matrix.fromBlocks 0 (Matrix.diagonal (fun i => Real.sqrt (Y.ν i)))
      (Matrix.diagonal (fun i => Real.sqrt (Y.ν i))) 0 with hE
  have hEsymm : Eᵀ = E := by
    rw [hE, Matrix.fromBlocks_transpose]
    simp only [Matrix.transpose_zero, Matrix.diagonal_transpose]
  have hEE : E * E = Matrix.fromBlocks (Matrix.diagonal Y.ν) 0 0 (Matrix.diagonal Y.ν) := by
    rw [hE, Matrix.fromBlocks_multiply]
    simp only [mul_zero, zero_mul, add_zero, zero_add, hdd]
  have hsq : (fun i => Real.sqrt (Y.ν i) * Real.sqrt (Y.ν i)) = Y.ν := by
    funext i; exact Real.mul_self_sqrt (Y.hν i)
  have hEJE : E * Matrix.J l ℝ * E
      = Matrix.fromBlocks 0 (Matrix.diagonal Y.ν) (-(Matrix.diagonal Y.ν)) 0 := by
    rw [hE, blockSwapRoot_conj_J, hsq]
  -- the symplectic congruence `S = Ri O E`
  set S : Matrix (l ⊕ l) (l ⊕ l) ℝ := Ri * Y.O * E with hS
  have hOO : Y.Oᵀ * Y.O = 1 := (Matrix.mem_orthogonalGroup_iff' (l ⊕ l) ℝ).mp Y.hOrth
  have hOOt : Y.O * Y.Oᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (l ⊕ l) ℝ).mp Y.hOrth
  have hSt : Sᵀ = E * (Y.Oᵀ * Ri) := by
    rw [hS, Matrix.transpose_mul, Matrix.transpose_mul, hRisymm, hEsymm]
  -- diagonalization
  have hDiagEq : Sᵀ * M * S = Matrix.fromBlocks (Matrix.diagonal Y.ν) 0 0 (Matrix.diagonal Y.ν) := by
    have hk : Sᵀ * M * S = E * (Y.Oᵀ * (Ri * M * Ri) * Y.O) * E := by
      rw [hSt, hS]; simp only [Matrix.mul_assoc]
    rw [hk, hRiMRi, mul_one, hOO, mul_one, hEE]
  -- symplectic
  have hSympForm : S * Matrix.J l ℝ * Sᵀ = Matrix.J l ℝ := by
    have hk : S * Matrix.J l ℝ * Sᵀ = Ri * Y.O * (E * Matrix.J l ℝ * E) * Y.Oᵀ * Ri := by
      rw [hSt, hS]; simp only [Matrix.mul_assoc]
    rw [hk, hEJE, ← Y.hNormal]
    have hfin : Ri * Y.O * (Y.Oᵀ * (R * Matrix.J l ℝ * R) * Y.O) * Y.Oᵀ * Ri
        = Ri * ((Y.O * Y.Oᵀ) * (R * Matrix.J l ℝ * R) * (Y.O * Y.Oᵀ)) * Ri := by
      simp only [Matrix.mul_assoc]
    rw [hfin]
    simp only [hOOt, Matrix.one_mul, Matrix.mul_one]
    have hRiARi : Ri * (R * Matrix.J l ℝ * R) * Ri = Matrix.J l ℝ := by
      have e : Ri * (R * Matrix.J l ℝ * R) * Ri = (Ri * R) * Matrix.J l ℝ * (R * Ri) := by
        simp only [Matrix.mul_assoc]
      rw [e, hRiR, hRRi, Matrix.one_mul, Matrix.mul_one]
    exact hRiARi
  exact ⟨S, SymplecticGroup.mem_iff.mpr hSympForm, Y.ν, Y.hν, hDiagEq⟩

end QIQTH.Williamson
