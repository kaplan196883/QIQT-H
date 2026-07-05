/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Williamson normal form — W1–W8: decomposition structure, symplectic algebra, carried Youla, sqrt entry point, entropy connection, the DERIVED S-construction, the Youla complex spectral entry point (W7), and the REAL (A²) route per-block geometry (W8)

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

* **W7 (the Youla spectral entry point — real derived content toward discharging the carry):** the
  route to the still-carried `YoulaDecomp` (the real antisymmetric normal form absent from Mathlib)
  goes through the complexification.  `iA_isHermitian` proves that for a real antisymmetric `A`
  (`Aᵀ = -A`) the matrix `iA_ℂ := Complex.I • (A.map Complex.ofReal)` is **Hermitian** over `ℂ`, so
  the complex spectral theorem (`Matrix.IsHermitian.spectral_theorem`) applies and diagonalizes it
  with real eigenvalues.  `iA_conj_antifixed` proves `conj(iA_ℂ) = -iA_ℂ` — the algebraic **seed of
  the `± ν` eigenvalue pairing** (conjugating an eigenvector sends `λ ↦ -λ`, so the spectrum is
  symmetric about `0`).  Both are axiom-free derived lemmas.  **The remaining wall (pinned, NOT
  discharged):** the complex spectral theorem delivers a *complex* eigenvector unitary and real
  eigenvalues over the **flat** index `l ⊕ l`; producing the split-index nonnegative spectrum
  `ν : l → ℝ` (the positive members of the `± ν` pairs) and the **real** orthogonal `O` with
  `Oᵀ A O = fromBlocks 0 (diag ν) (-(diag ν)) 0` requires (a) a multiplicity argument pairing the
  symmetric eigenvalue multiset across the `Sum` split and (b) the real-Schur extraction
  `O = [Re(colₖ), Im(colₖ)]` from conjugate eigenvector pairs.  Neither has any Mathlib support; this
  is the genuine research-grade real-antisymmetric-normal-form gap.  A scratch probe confirmed the
  spectral entry point compiles and the stall is exactly this flat-complex → real-block assembly.

**Honest scope.**  W1–W2 are scaffolding + one carried hypothesis; W3 adds the real square-root
entry point and the legacy `hconstr` packaging; W4–W5 land the entropy bridge on the
`WilliamsonDecomp` structure directly (it does *not* need the construction — it consumes the
symplectic spectrum `ν` a decomposition already carries); **W6 DERIVES the block-matrix
S-construction** (`williamson_of_youla`), retiring W3's carry.  Williamson is *not yet* proved
unconditionally — it is proved **conditional on Youla alone** (`YoulaDecomp`, the real-antisymmetric
normal form absent from Mathlib).  The single remaining carry is Youla; the S-construction and the
entropy are genuine derivations.  W7 lands the *spectral entry point* toward discharging the Youla
carry (`iA_isHermitian`, `iA_conj_antifixed`) and pins the exact remaining obstruction (the
flat-complex → real-block assembly) honestly — Youla itself is **still carried**.  **W8 attacks the
same carry from the REAL side** (`T := A*A`, no complexification): it derives the *entire*
per-eigenspace geometry — `T` symmetric + negative semidefinite, `A`-commuting, the `⟨Ax,x⟩ = 0`
antisymmetry, and — the core — `antisymm_invariant_block` (the closed `2×2` rotation block
`Ae = f, Af = -ν² e` on each `T`-eigenspace) plus the `ν = 0` kernel block — and pins the *one*
remaining obstruction (the abstract→concrete assembly of per-block frames into a single `l ⊕ l`
orthogonal `O`) honestly.  Youla is **still carried**; the real route discharges everything up to the
`O`-assembly.  Nothing here unlocks the area-law `S ∝ A` scaling (the entropy machinery is
area/volume-blind).  Axiom-free.
-/
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.InnerProductSpace.Orthogonal
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

/-! ### W7 — toward `youlaDecomp_of_antisymm`: the complex-Hermitian entry point

The Youla real antisymmetric normal form (the single remaining carry, `YoulaDecomp`) is the real
Schur / real-skew normal form absent from Mathlib.  The spectral route to it goes through the
*complexification*: for a real antisymmetric `A` (`Aᵀ = -A`), the matrix `iA_ℂ := I • (A.map ℝ→ℂ)`
is **Hermitian** over `ℂ`, so the complex spectral theorem applies and diagonalizes it with real
eigenvalues.  The `± ν` pairing of those eigenvalues (from `A` real, hence `A_ℂ = conj A_ℂ`) and the
assembly of conjugate eigenvectors into real `2×2` rotation blocks is the genuine research-grade
wall.  This increment lands the **entry point** — the Hermitian fact that makes the complex spectral
theorem available — as real derived content, and pins the remaining obstruction honestly. -/

/-- **The complexified antisymmetric matrix `iA_ℂ = I • (A.map ℝ→ℂ)` is Hermitian.**  For a real
    antisymmetric `A` (`Aᵀ = -A`), `A_ℂ := A.map Complex.ofReal` satisfies `(A_ℂ)ᴴ = (A_ℂ)ᵀ = -A_ℂ`
    (the conjugate transpose is the transpose because the entries are real, and the transpose is `-A`
    by antisymmetry).  Then `(I • A_ℂ)ᴴ = star I • (A_ℂ)ᴴ = (-I) • (-A_ℂ) = I • A_ℂ`, so `iA_ℂ` is
    Hermitian.  This is the entry point that makes the complex spectral theorem applicable to the
    Youla construction — real derived content, not carried. -/
theorem iA_isHermitian (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hA : Aᵀ = -A) :
    (Complex.I • A.map (Complex.ofReal)).IsHermitian := by
  -- the complexified matrix has conjugate transpose equal to `-A_ℂ`
  have hAc : (A.map (Complex.ofReal))ᴴ = -(A.map (Complex.ofReal)) := by
    rw [← Matrix.conjTranspose_map Complex.ofReal (fun a => by simp),
        Matrix.conjTranspose_eq_transpose_of_trivial, hA]
    ext i j
    simp
  -- assemble the Hermitian condition
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hAc, Complex.star_def, Complex.conj_I, neg_smul, smul_neg,
      neg_neg]

/-- **The complexified matrix `iA_ℂ` is anti-fixed by entrywise conjugation: `conj(iA_ℂ) = -iA_ℂ`.**
    Because `A` is real, `A_ℂ = A.map ofReal` is fixed by conjugation, while `conj I = -I`; hence
    `map conj (I • A_ℂ) = -I • A_ℂ = -(I • A_ℂ)`.  This is the **algebraic seed of the `± ν`
    eigenvalue pairing**: if `v` is an eigenvector of the Hermitian `iA_ℂ` with (real) eigenvalue `λ`,
    then `conj v` is an eigenvector of `conj(iA_ℂ) = -iA_ℂ` with eigenvalue `λ`, i.e. an eigenvector
    of `iA_ℂ` with eigenvalue `-λ`, so the spectrum is symmetric about `0`.  Real derived content. -/
theorem iA_conj_antifixed (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    (Complex.I • A.map (Complex.ofReal)).map (starRingEnd ℂ)
      = -(Complex.I • A.map (Complex.ofReal)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, map_mul,
    Complex.conj_I, Complex.conj_ofReal]
  ring

/-! ### W8 — the REAL (`A²`) route toward Youla: `T := A*A` structure + the invariant-block core

A **complexification-free** route to the Youla real antisymmetric normal form.  For a real
antisymmetric `A` (`Aᵀ = -A`), the real symmetric matrix `T := A * A` is **negative semidefinite**
(`⟨Tx,x⟩ = -‖Ax‖² ≤ 0`); it `A`-commutes, so each of its (real) spectral eigenspaces `T e = -ν² e`
is `A`-invariant, and on the `ν > 0` eigenspace `A` acts as the `2×2` rotation block
`ν·[[0,-1],[1,0]]` in the orthonormal frame `{e, Ae/ν}` (the Youla block); the `ν = 0` (kernel)
eigenspace is exactly the `A`-kernel (`Ae = 0`).  This section lands that route's **derived
structural core** as clean matrix / dot-product content — **no `Complex.I`, no spectral
complexification**:

* `antisymm_sq_isHermitian` — `T := A*A` is symmetric (Hermitian over `ℝ`);
* `antisymm_neg_sq_posSemidef` — `-(A*A)` is positive semidefinite (`T` negative semidefinite);
* `antisymm_comm_sq` — `A` commutes with `T` (the eigenspace-invariance seed);
* `antisymm_dotProduct_self` — `⟨Ax, x⟩ = 0` (antisymmetry in inner-product form);
* `antisymm_normSq_mulVec` — `⟨Ax, Ax⟩ = -⟨A²x, x⟩` (the `-‖Ax‖²` Rayleigh identity);
* `antisymm_sq_dotProduct_nonpos` — `⟨Tx, x⟩ ≤ 0` (negative semidefiniteness, vector form);
* `antisymm_invariant_block` — **the core**: on the `T`-eigenspace `(A*A) e = -ν² e`, with
  `f := A e`, one has `e ⊥ f`, `‖f‖² = ν²‖e‖²`, and `A f = -ν² e` — i.e. `A e = f`, `A f = -ν² e`,
  the closed `2×2` rotation block;
* `antisymm_kernel_of_sq_kernel` — the `ν = 0` block: `(A*A) e = 0 ⟹ A e = 0`.

**The remaining wall (pinned, NOT discharged).**  What is *derived* here is the entire per-eigenspace
geometry — the real algebraic content of the theorem.  What is *not* discharged is the
**abstract→concrete assembly**: taking the real spectral decomposition of the symmetric `T`
(Mathlib's `Matrix.IsHermitian.spectral_theorem` applies since `T` is `IsHermitian`), grouping its
eigenvalues into `ν = 0` and `-νₖ²` (`νₖ > 0`) blocks, extracting per-block orthonormal frames
`{e, Ae/ν}` via `antisymm_invariant_block`, and **assembling them into ONE concrete orthogonal
`O : Matrix (l ⊕ l) (l ⊕ l) ℝ`** with the exact `l ⊕ l` sum-indexing so that
`Oᵀ A O = fromBlocks 0 (diagonal ν) (-(diagonal ν)) 0` holds entrywise.  This block-assembly /
`finrank`-induction step (mapping the flat spectral basis to the split `l ⊕ l` index) has no Mathlib
support and is the genuine research-grade gap — the same wall the complex W7 route hit, reached now
from the real side with the full per-block geometry in hand.  `youlaDecomp_of_antisymm` therefore
remains **carried**; the real route discharges everything *up to* the concrete `O`-assembly.  All
lemmas below are axiom-free (std-3). -/

section RealRoute

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`T := A*A` is Hermitian (symmetric over `ℝ`) for antisymmetric `A`.**  `(A*A)ᵀ = Aᵀ Aᵀ =
    (-A)(-A) = A*A`, and over `ℝ` the conjugate transpose is the transpose.  This makes Mathlib's
    real spectral theorem (`Matrix.IsHermitian.spectral_theorem`) applicable to `T` — the entry point
    of the real route. -/
theorem antisymm_sq_isHermitian (A : Matrix n n ℝ) (hA : Aᵀ = -A) : (A * A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hA, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg]

/-- **`-(A*A)` is positive semidefinite** (equivalently `T := A*A` is negative semidefinite) for
    antisymmetric `A`.  `-(A*A) = (-A)*A = Aᵀ*A = Aᴴ*A`, positive semidefinite by
    `Matrix.posSemidef_conjTranspose_mul_self`.  Hence the eigenvalues of `T` are `≤ 0`, i.e. of the
    form `μₖ = -νₖ²` with `νₖ ≥ 0` — the Youla skew eigenvalues. -/
theorem antisymm_neg_sq_posSemidef (A : Matrix n n ℝ) (hA : Aᵀ = -A) : (-(A * A)).PosSemidef := by
  have hAc : Aᴴ = -A := by rw [Matrix.conjTranspose_eq_transpose_of_trivial, hA]
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rwa [hAc, Matrix.neg_mul] at h

/-- **`A` commutes with `T := A*A`.**  Immediate from associativity, but it is the structural seed of
    the eigenspace-invariance step: since `A T = T A`, `A` preserves every eigenspace of `T`. -/
theorem antisymm_comm_sq (A : Matrix n n ℝ) : A * (A * A) = (A * A) * A := by
  rw [Matrix.mul_assoc]

/-- **Antisymmetric ⟹ `⟨Ax, x⟩ = 0`.**  `⟨Ax,x⟩ = ⟨x, Aᵀx⟩ = ⟨x, -Ax⟩ = -⟨Ax,x⟩`, so it vanishes
    (`⟨·,·⟩` is the real dot product, symmetric over `ℝ`).  This is the orthogonality `Ae ⊥ e` that
    makes `{e, Ae}` an orthogonal pair inside each block. -/
theorem antisymm_dotProduct_self (A : Matrix n n ℝ) (hA : Aᵀ = -A) (x : n → ℝ) :
    (A *ᵥ x) ⬝ᵥ x = 0 := by
  have h : (A *ᵥ x) ⬝ᵥ x = -((A *ᵥ x) ⬝ᵥ x) :=
    calc (A *ᵥ x) ⬝ᵥ x = x ⬝ᵥ (A *ᵥ x) := dotProduct_comm _ _
      _ = (x ᵥ* A) ⬝ᵥ x := Matrix.dotProduct_mulVec _ _ _
      _ = (Aᵀ *ᵥ x) ⬝ᵥ x := by rw [Matrix.mulVec_transpose]
      _ = ((-A) *ᵥ x) ⬝ᵥ x := by rw [hA]
      _ = -((A *ᵥ x) ⬝ᵥ x) := by rw [Matrix.neg_mulVec, neg_dotProduct]
  linarith

/-- **Antisymmetric ⟹ `⟨Ax, Ax⟩ = -⟨A²x, x⟩`** (the `-‖Ax‖²` Rayleigh identity).  Via `Aᵀ = -A`:
    `⟨A²x,x⟩ = ⟨Ax, Aᵀ... ⟩ = -⟨Ax, Ax⟩`.  This drives both negative semidefiniteness of `T = A*A`
    and, on a `T`-eigenspace, the `‖Ae‖² = ν²‖e‖²` normalization. -/
theorem antisymm_normSq_mulVec (A : Matrix n n ℝ) (hA : Aᵀ = -A) (x : n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = -(((A * A) *ᵥ x) ⬝ᵥ x) := by
  have hkey : ((A * A) *ᵥ x) ⬝ᵥ x = -((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) :=
    calc ((A * A) *ᵥ x) ⬝ᵥ x
        = (A *ᵥ (A *ᵥ x)) ⬝ᵥ x := by rw [← Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ (A *ᵥ (A *ᵥ x)) := dotProduct_comm _ _
      _ = (x ᵥ* A) ⬝ᵥ (A *ᵥ x) := Matrix.dotProduct_mulVec _ _ _
      _ = (Aᵀ *ᵥ x) ⬝ᵥ (A *ᵥ x) := by rw [Matrix.mulVec_transpose]
      _ = ((-A) *ᵥ x) ⬝ᵥ (A *ᵥ x) := by rw [hA]
      _ = -((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by rw [Matrix.neg_mulVec, neg_dotProduct]
  rw [hkey, neg_neg]

/-- **`T := A*A` is negative semidefinite in vector form: `⟨Tx, x⟩ ≤ 0`.**  Directly from
    `antisymm_normSq_mulVec` (`⟨Tx,x⟩ = -‖Ax‖²`) and `‖Ax‖² ≥ 0`. -/
theorem antisymm_sq_dotProduct_nonpos (A : Matrix n n ℝ) (hA : Aᵀ = -A) (x : n → ℝ) :
    ((A * A) *ᵥ x) ⬝ᵥ x ≤ 0 := by
  have h := antisymm_normSq_mulVec A hA x
  have hnn : 0 ≤ (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
    simpa using dotProduct_self_star_nonneg (A *ᵥ x)
  linarith

/-- **The `2×2` `A`-invariant block on a `T`-eigenspace — the real-route core.**  If `e` lies in the
    `T = A*A` eigenspace with eigenvalue `-ν²` (`(A*A) *ᵥ e = -(ν^2) • e`), then with `f := A *ᵥ e`:
    (i) `e ⬝ᵥ f = 0` (`f ⊥ e`); (ii) `f ⬝ᵥ f = ν² • (e ⬝ᵥ e)` (so `‖Ae‖ = |ν|·‖e‖`); (iii)
    `A *ᵥ f = -(ν^2) • e`.  Together `A e = f` and `A f = -ν² e`: in the orthonormal frame
    `{e, f/ν}` (for `ν > 0`) `A` acts as the rotation block `ν·[[0,-1],[1,0]]` — the Youla `2×2`
    block.  This closes the per-block geometry the assembly consumes. -/
theorem antisymm_invariant_block (A : Matrix n n ℝ) (hA : Aᵀ = -A) (ν : ℝ) (e : n → ℝ)
    (he : (A * A) *ᵥ e = -(ν ^ 2) • e) :
    e ⬝ᵥ (A *ᵥ e) = 0 ∧
      (A *ᵥ e) ⬝ᵥ (A *ᵥ e) = (ν ^ 2) • (e ⬝ᵥ e) ∧
      A *ᵥ (A *ᵥ e) = -(ν ^ 2) • e := by
  refine ⟨?_, ?_, ?_⟩
  · rw [dotProduct_comm]; exact antisymm_dotProduct_self A hA e
  · rw [antisymm_normSq_mulVec A hA e, he]
    simp only [smul_dotProduct, smul_eq_mul]
    ring
  · rw [Matrix.mulVec_mulVec, he]

/-- **The `T := A*A` kernel is the `A`-kernel** (the `ν = 0` Youla block, `Ae = 0`).  If
    `(A*A) *ᵥ e = 0` then `A *ᵥ e = 0`: `⟨Ae,Ae⟩ = -⟨A²e,e⟩ = 0` forces `Ae = 0` over `ℝ`.  This is
    the degenerate `ν = 0` block, where `A` restricts to zero. -/
theorem antisymm_kernel_of_sq_kernel (A : Matrix n n ℝ) (hA : Aᵀ = -A) (e : n → ℝ)
    (he : (A * A) *ᵥ e = 0) : A *ᵥ e = 0 := by
  have h : (A *ᵥ e) ⬝ᵥ (A *ᵥ e) = 0 := by
    rw [antisymm_normSq_mulVec A hA e, he, zero_dotProduct, neg_zero]
  exact dotProduct_self_eq_zero.mp h

end RealRoute

/-! ### W9 — the real-root pairing: `A`-invariance of `T`-eigenspaces, the complex structure, and
even-dimensionality

Two structural stepping stones toward the Youla `l ⊕ l` assembly, working at the **operator** level
(`Module.End` eigenspaces of `T := A*A`, viewed via `Matrix.mulVecLin`) — neither prior attempt
tried these.  For a real antisymmetric `A` (`Aᵀ = -A`), on the eigenspace
`W := ker(T + ν²·1) = Module.End.eigenspace (mulVecLin (A*A)) (-ν²)`:

* **(a) `A`-invariance** (`antisymm_eigenspace_invariant`): `A` maps `W` into itself, because `A`
  commutes with `T = A*A` (from `antisymm_comm_sq`/`mul_assoc`): if `T x = -ν² x` then
  `T (A x) = A (T x) = -ν² (A x)`.  This is the `MapsTo` that lets `A` restrict to `W`.
* **(b) the restricted square** (`antisymm_sq_eq_smul_on_eigenspace`): on `W`, `A ∘ A = -ν²·id`
  (the eigenvalue equation `(A*A) x = -ν² x` read through `mulVec_mulVec`).  So for `ν > 0`,
  `J := A/ν` restricted to `W` satisfies `J² = -id`: `W` carries a **complex structure**.
* **(c) even-dimensionality** (`antisymm_eigenspace_even`): the crux — `Even (finrank ℝ W)` for the
  `ν > 0` eigenspaces.  DERIVED here via the determinant of the restricted operator
  `A_W := (mulVecLin A).restrict`: from (b), `A_W ∘ A_W = -ν²·id`, so
  `(det A_W)² = det(A_W ∘ A_W) = (-ν²)^{finrank W}` (`LinearMap.det_comp` + `det_smul` + `det_id`).
  The left side is a real square, hence `≥ 0`; with `ν > 0` the right side has sign `(-1)^{finrank W}`,
  forcing `finrank W` even.  This is the `{e, Je}` pairing that enables the `l ⊕ l` split-indexing.

Piece 2 (`antisymm_negSqEigenvalues` + `_nonneg`) exposes the real spectral data the assembly
consumes: the eigenvalues of the PosSemidef `-(A*A)` (from `antisymm_neg_sq_posSemidef`) are `≥ 0`
— these are the `νₖ²`, so `T = A*A` has spectrum `-νₖ² ≤ 0`, the Youla skew eigenvalues squared.

**The remaining wall (pinned, NOT discharged — unchanged from W7/W8).**  Even-dimensionality of each
`ν > 0` eigenspace is exactly the multiplicity fact that makes an `l ⊕ l` split *possible*, but the
**flat-basis → `l ⊕ l` split-index assembly** — choosing, per positive eigenvalue, a real orthonormal
`{eₖ}` with its `A`-partner `{A eₖ / ν}`, and threading all blocks (plus the kernel) into ONE concrete
orthogonal `O : Matrix (l ⊕ l) (l ⊕ l) ℝ` with `Oᵀ A O = fromBlocks 0 (diag ν) (-(diag ν)) 0`
entrywise — still has no Mathlib support (no `finrank`-indexed real-normal-form induction).
`youlaDecomp_of_antisymm` therefore remains **carried**; W9 discharges the complex-structure /
even-multiplicity ingredient the assembly *needs* but not the concrete `O`-surgery itself.  All lemmas
below are axiom-free (std-3). -/

section RealRootPairing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **(a) `A`-invariance of each `T := A*A` eigenspace.**  For antisymmetric `A`, `A` maps the
    eigenspace `W = ker(T + ν²·1) = Module.End.eigenspace (mulVecLin (A*A)) (-ν²)` into itself.  From
    `A T = T A` (associativity): if `T x = -ν² x` then `T (A x) = A (T x) = A (-ν² x) = -ν² (A x)`,
    so `A x ∈ W`.  This is the `MapsTo` that lets `A` restrict to `W` (the seed of the complex
    structure). -/
theorem antisymm_eigenspace_invariant (A : Matrix n n ℝ) (ν : ℝ) :
    ∀ x ∈ Module.End.eigenspace (Matrix.mulVecLin (A * A)) (-(ν ^ 2)),
      Matrix.mulVecLin A x ∈ Module.End.eigenspace (Matrix.mulVecLin (A * A)) (-(ν ^ 2)) := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hx
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, mul_assoc, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]

/-- **(b) On the `T`-eigenspace, `A ∘ A` acts as `-ν²·id`.**  The eigenvalue equation
    `(A*A) *ᵥ x = -ν² • x` read through `mulVec_mulVec`.  For `ν > 0`, this says `J := A/ν` restricted
    to the eigenspace satisfies `J² = -id` — the eigenspace carries a complex structure. -/
theorem antisymm_sq_eq_smul_on_eigenspace (A : Matrix n n ℝ) (ν : ℝ) (x : n → ℝ)
    (hx : x ∈ Module.End.eigenspace (Matrix.mulVecLin (A * A)) (-(ν ^ 2))) :
    Matrix.mulVecLin A (Matrix.mulVecLin A x) = -(ν ^ 2) • x := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hx
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hx]

/-- **(c) Even-dimensionality of the `ν > 0` eigenspaces — the complex-structure crux.**  For
    antisymmetric `A` and `ν > 0`, the `T := A*A` eigenspace `W = ker(T + ν²·1)` has **even** real
    dimension.  DERIVED from the restricted operator `A_W := (mulVecLin A).restrict` (well-defined by
    the `A`-invariance (a)): by (b), `A_W ∘ A_W = -ν²·id`, so
    `(det A_W)² = det(A_W ∘ A_W) = (-ν²)^{finrank W}` (`LinearMap.det_comp`, `det_smul`, `det_id`).
    The left side is a real square (`≥ 0`); for `ν > 0` the right side equals
    `(-1)^{finrank W} · (ν²)^{finrank W}` with `(ν²)^{finrank W} > 0`, so `(-1)^{finrank W} ≥ 0`,
    forcing `finrank W` even.  This is the `{e, Ae/ν}` pairing (a complex structure `J² = -id`) that
    underlies the `l ⊕ l` split-indexing of the Youla normal form.  (The antisymmetry of `A` is not
    needed for *this* step: on the `-ν²` eigenspace `A_W² = -ν²·id` is a genuine complex structure for
    any real `A`; antisymmetry is what makes the eigenvalues of `A*A` be exactly the `-ν²` in the first
    place — `antisymm_neg_sq_posSemidef`.) -/
theorem antisymm_eigenspace_even (A : Matrix n n ℝ) {ν : ℝ} (hν : 0 < ν) :
    Even (Module.finrank ℝ (Module.End.eigenspace (Matrix.mulVecLin (A * A)) (-(ν ^ 2)))) := by
  set W := Module.End.eigenspace (Matrix.mulVecLin (A * A)) (-(ν ^ 2)) with hW
  -- `A` restricts to an endomorphism `A_W` of `W` (by the invariance (a))
  have hinv : ∀ x ∈ W, Matrix.mulVecLin A x ∈ W := antisymm_eigenspace_invariant A ν
  set AW := (Matrix.mulVecLin A).restrict hinv with hAW
  -- `A_W ∘ A_W = -ν²·id` on `W` (the complex structure, from (b))
  have hcomp : AW.comp AW = (-(ν ^ 2)) • (LinearMap.id : W →ₗ[ℝ] W) := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    have hx : Matrix.mulVecLin A (Matrix.mulVecLin A (x : n → ℝ)) = -(ν ^ 2) • (x : n → ℝ) :=
      antisymm_sq_eq_smul_on_eigenspace A ν x x.2
    simpa only [LinearMap.comp_apply, LinearMap.coe_restrict_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, SetLike.val_smul] using hx
  -- take determinants: `(det A_W)² = (-ν²)^{finrank W}`
  have hdet : LinearMap.det AW * LinearMap.det AW = (-(ν ^ 2)) ^ Module.finrank ℝ W := by
    rw [← LinearMap.det_comp, hcomp, LinearMap.det_smul, LinearMap.det_id, mul_one]
  -- the left side is a real square, so the right side is `≥ 0`
  have hnn : (0 : ℝ) ≤ (-(ν ^ 2)) ^ Module.finrank ℝ W := hdet ▸ mul_self_nonneg _
  rcases Nat.even_or_odd (Module.finrank ℝ W) with he | ho
  · exact he
  · exfalso
    rw [ho.neg_pow] at hnn
    have hpos : (0 : ℝ) < (ν ^ 2) ^ Module.finrank ℝ W := pow_pos (pow_pos hν 2) _
    linarith

/-- **Piece 2 — the real spectral data (the eigenvalues of the PosSemidef `-(A*A)`).**  The
    eigenvalues of `-(A*A)` (Hermitian and PosSemidef by `antisymm_neg_sq_posSemidef`), read off by
    the real spectral theorem (`Matrix.IsHermitian.eigenvalues`).  These are the `νₖ²`; so
    `T = A*A` has spectrum `-νₖ² ≤ 0`, the Youla skew eigenvalues squared — the data the still-carried
    `l ⊕ l` assembly consumes. -/
noncomputable def antisymm_negSqEigenvalues (A : Matrix n n ℝ) (hA : Aᵀ = -A) : n → ℝ :=
  (antisymm_neg_sq_posSemidef A hA).1.eigenvalues

/-- **The `-(A*A)` eigenvalues are nonnegative** (`Matrix.PosSemidef.eigenvalues_nonneg` applied to
    `antisymm_neg_sq_posSemidef`).  Equivalently the eigenvalues of `T = A*A` are `≤ 0` — the
    negative-semidefiniteness of `T` at the spectral level, the `-νₖ²` list. -/
theorem antisymm_negSqEigenvalues_nonneg (A : Matrix n n ℝ) (hA : Aᵀ = -A) (i : n) :
    0 ≤ antisymm_negSqEigenvalues A hA i :=
  (antisymm_neg_sq_posSemidef A hA).eigenvalues_nonneg i

end RealRootPairing

/-! ### W10 — the abstract recursion toward `youlaDecomp_of_antisymm`: the skew-adjoint plane/complement
step, the nonsingular-skew even backbone, and the **honest concrete stall**

A genuine, determined attempt to *close* `youlaDecomp_of_antisymm` (the Youla real antisymmetric block
normal form, the last carry) via the classical **dimension-halving induction**, worked at the abstract
inner-product-space (`OrthonormalBasis` / `Submodule`) level where the induction naturally lives.  Two
genuinely new axiom-free lemmas are landed as the load-bearing recursion primitives:

* `antisymm_card_even` — **a nonsingular real antisymmetric matrix has an even-cardinality index**
  (`Bᵀ = -B`, `IsUnit B.det ⟹ Even (card m)`), by the determinant sign trick
  `det B = det Bᵀ = det (-B) = (-1)^{card} det B`.  This is the *even-multiplicity backbone*: applied to
  the operator `a` restricted to `(ker a)ᗮ` (where it is nonsingular skew), it forces `Even (finrank (ker a))`,
  which is exactly what makes the `ν = 0` kernel block of the induction *pairable* (a nonzero kernel has
  `≥ 2` dimensions, so a second orthonormal kernel vector always exists).
* `skewAdjoint_orthogonal_invariant` — **for a skew-adjoint operator (`⟪a x, y⟫ = -⟪x, a y⟫`), the
  orthogonal complement of an invariant subspace is invariant** (`⟪a y, x⟫ = 0 ∧ ⟪a y, x⟫ = -⟪y, a x⟫ ⟹
  ⟪y, a x⟫ = 0`).  This is the step that lets the induction **recurse on `Pᗮ`** after splitting off a
  `2×2` block `P = span{u, a u}`, with `a` still skew-adjoint on `Pᗮ` — the engine of dimension halving.
  (Mathlib only has `LinearMap.IsSymmetric.invariant_orthogonalComplement_eigenspace`, for *symmetric*
  operators and *eigenspaces*; this skew-adjoint / arbitrary-invariant-subspace form is new.)

**Mathlib landscape — CORRECTED from W7–W9.**  The earlier checkpoints claimed the flat-basis → `l ⊕ l`
assembly has "NO Mathlib support."  That is now **corrected**: Mathlib *does* supply the gluing
primitives — `OrthonormalBasis.prod` (an `OrthonormalBasis (ι₁ ⊕ ι₂)` of `WithLp 2 (E × F)` from ON
bases of the factors) and `Submodule.orthogonalDecomposition` (`E ≃ₗᵢ WithLp 2 (K × Kᗮ)`), together with
`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` (an eigenvector of the symmetric
`T := a ∘ a` on any nontrivial finite-dim `E`) and `DirectSum.IsInternal.subordinateOrthonormalBasis`.
The abstract induction below **type-checks end-to-end** through the eigenvector extraction, the `μ ≤ 0 /
ν = √(−μ)` normalization, the `a u = 0` vs `ν > 0` case split, the `2×2` invariant plane
`P = span{u, a u}`, the complement invariance (via `skewAdjoint_orthogonal_invariant`), the restricted
operator `aC := (a.domRestrict Pᗮ).codRestrict Pᗮ`, and the **recursive `IH` call on `Pᗮ`** (dropping
`finrank` by `2`).

**THE HONEST CONCRETE STALL.**  What is *not* discharged is the final **basis-gluing + index-reindexing +
`a`-action verification**.  At the recursion point, with the `2×2` block data `‖u‖ = ‖w‖ = 1`, `u ⊥ w`,
`a u = ν • w`, `a w = -ν • u` in hand and the induction hypothesis furnishing
`bC : OrthonormalBasis (κ' ⊕ κ') ℝ Pᗮ` with `νC` realizing the pairing on `Pᗮ`, the remaining goal
(captured verbatim via `extract_goal`) is:

```
⊢ ∃ (κ : Type) (_ : Fintype κ) (b : OrthonormalBasis (κ ⊕ κ) ℝ E) (ν : κ → ℝ),
    (∀ k, a (b (Sum.inl k)) = -ν k • b (Sum.inr k)) ∧
    (∀ k, a (b (Sum.inr k)) =  ν k • b (Sum.inl k))
```

The move that would close it — take `κ := Unit ⊕ κ'`, build `b` by mapping
`(OrthonormalBasis.prod (stdOrthonormalBasis of P) bC)` through `(Submodule.orthogonalDecomposition P).symm`,
reindexing `Fin 2 ⊕ (κ' ⊕ κ')` into `(Unit ⊕ κ') ⊕ (Unit ⊕ κ')`, and verifying the three `a`-action
equations through the isometry — has **all its primitives present in Mathlib** but is a large, purely
mechanical index/coercion assembly (threading the skew `a` through `orthogonalDecomposition.symm ∘ prod`
and matching the `κ ⊕ κ` pairing layout).  It is a **formalization-labor wall, not a missing-lemma wall**
— the honest correction to the W7–W9 "no support" framing.  `youlaDecomp_of_antisymm` therefore **remains
carried**; W10 lands the two recursion primitives the assembly runs on and pins the exact residual goal.
All lemmas below are axiom-free (std-3). -/

section RealYoulaRecursion

open scoped RealInnerProductSpace

/-- **A nonsingular real antisymmetric matrix has even index cardinality.**  `Bᵀ = -B` gives
    `det B = det Bᵀ = det (-B) = (-1)^{card m} · det B`; if `card m` were odd this forces
    `det B = -det B`, i.e. `det B = 0`, contradicting `IsUnit B.det`.  The even-multiplicity backbone
    of the Youla induction: applied to `a` restricted to `(ker a)ᗮ` (nonsingular skew there), it forces
    `Even (finrank (ker a))`, so the `ν = 0` kernel block is pairable. -/
theorem antisymm_card_even {m : Type*} [Fintype m] [DecidableEq m] (B : Matrix m m ℝ)
    (hB : Bᵀ = -B) (hdet : IsUnit B.det) : Even (Fintype.card m) := by
  by_contra h
  rw [Nat.not_even_iff_odd] at h
  have hdd : B.det = -B.det := by
    calc B.det = Bᵀ.det := (Matrix.det_transpose B).symm
      _ = (-B).det := by rw [hB]
      _ = (-1) ^ Fintype.card m * B.det := Matrix.det_neg B
      _ = -B.det := by rw [h.neg_one_pow]; ring
  have hz : B.det = 0 := by linarith
  exact hdet.ne_zero hz

/-- **Skew-adjoint operator: the orthogonal complement of an invariant subspace is invariant.**  For
    `a` skew-adjoint (`⟪a x, y⟫ = -⟪x, a y⟫`) and `P` closed under `a`, if `x ∈ Pᗮ` then for every
    `y ∈ P` one has `a y ∈ P`, so `⟪a y, x⟫ = 0`; combined with `⟪a y, x⟫ = -⟪y, a x⟫` this yields
    `⟪y, a x⟫ = 0` for all `y ∈ P`, i.e. `a x ∈ Pᗮ`.  This is the recursion engine of the Youla
    dimension-halving induction: after splitting a `2×2` block `P = span{u, a u}`, `a` restricts to a
    skew-adjoint operator on `Pᗮ`, on which the induction recurses. -/
theorem skewAdjoint_orthogonal_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a : E →ₗ[ℝ] E)
    (hskew : ∀ x y, ⟪a x, y⟫ = -⟪x, a y⟫)
    (P : Submodule ℝ E) (hP : ∀ x ∈ P, a x ∈ P) :
    ∀ x ∈ Pᗮ, a x ∈ Pᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro y hy
  have h0 : ⟪a y, x⟫ = 0 := (Submodule.mem_orthogonal P x).mp hx (a y) (hP y hy)
  have hsk := hskew y x
  rw [h0] at hsk
  linarith [hsk]

end RealYoulaRecursion

/-! ### W11 — the ABSTRACT operator Youla pairing: `youla_pairing`, FULLY PROVED (no carry)

The operator-level heart of the Youla real antisymmetric normal form, proved **unconditionally** by
the classical dimension-halving strong induction on `finrank ℝ E`.  For a finite-dimensional real
inner product space `E` and a skew-adjoint operator `a` (`⟪a x, y⟫ = -⟪x, a y⟫`) with `Even
(finrank ℝ E)`, there is an orthonormal basis indexed by `κ ⊕ κ` that block-pairs `a` into
`ν`-rotation `2×2` blocks: `a (b (inl k)) = -ν k • b (inr k)`, `a (b (inr k)) = ν k • b (inl k)`,
with `ν ≥ 0`.

**The engine.**  Each recursion step peels a single `2×2` block `P = span{p, q}`:

* If `a ≠ 0`: `T := a ∘ₗ a` is symmetric and negative semidefinite; its **minimal** eigenvalue
  `μ₀ = ⨅ Rayleigh < 0` (the infimum is `< 0` because `a ≠ 0`, via a `BddBelow`/`ciInf_le`
  operator-norm bound), giving a unit `T`-eigenvector `u` with `a u ≠ 0`; then `w := a u / ν`
  (`ν := ‖a u‖ = √(-μ₀) > 0`) closes the rotation block `a u = ν • w`, `a w = -ν • u`, `u ⊥ w`.
* If `a = 0`: any two orthonormal vectors form a `ν = 0` block.

The complement `Pᗮ` is `a`-invariant (`skewAdjoint_orthogonal_invariant`), has even dimension
`finrank E - 2`, and carries the restricted skew-adjoint `aC := a.restrict`; the **induction
hypothesis** furnishes its Youla basis, which is glued to the block frame `{p, q}` by an explicit
`Sum.elim` family whose orthonormality (`P ⊥ Pᗮ`) and cardinality (`= finrank E`) upgrade it to an
`OrthonormalBasis` via `OrthonormalBasis.mk`.  The `a`-action is verified index-by-index through the
inclusion `↑(aC x) = a ↑x`.  **Fully axiom-free (std-3); this is the abstract core discharging the
Youla carry at the operator level.**  (The concrete `Matrix (l⊕l)(l⊕l) → YoulaDecomp` bridge —
`E := EuclideanSpace ℝ (l⊕l)`, `a := toEuclideanLin A`, ON basis → orthogonal `O` via
`OrthonormalBasis.toMatrix` → `fromBlocks` — is the NEXT increment, not done here.) -/

section AbstractYoulaPairing

open Module
open scoped InnerProductSpace

/-- **The abstract Youla pairing (finrank-indexed strong-induction form).**  For each `n`, every
    `n`-dimensional real inner product space with a skew-adjoint operator and `Even n` admits the
    block-pairing orthonormal basis.  Proved by strong induction on `n` (peel a `2×2` block, recurse
    on the even-dimensional invariant complement). -/
theorem youla_pairing_aux : ∀ (n : ℕ) {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E →ₗ[ℝ] E),
    (∀ x y, ⟪a x, y⟫_ℝ = -⟪x, a y⟫_ℝ) → finrank ℝ E = n → Even n →
    ∃ (κ : Type) (_ : Fintype κ) (b : OrthonormalBasis (κ ⊕ κ) ℝ E) (ν : κ → ℝ),
      (∀ k, 0 ≤ ν k) ∧
      (∀ k, a (b (Sum.inl k)) = -ν k • b (Sum.inr k)) ∧
      (∀ k, a (b (Sum.inr k)) = ν k • b (Sum.inl k)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro E _ _ _ a ha hn hEven
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- base case: `finrank E = 0`, empty basis, everything vacuous
      refine ⟨Empty, inferInstance,
        OrthonormalBasis.mk (v := fun k => isEmptyElim k) (Orthonormal.of_isEmpty (𝕜 := ℝ) _) ?_,
        fun k => k.elim, fun k => k.elim, fun k => k.elim, fun k => k.elim⟩
      have hcard : Fintype.card (Empty ⊕ Empty) = finrank ℝ E := by rw [hn, hn0]; simp
      exact (linearIndependent_empty_type.span_eq_top_of_card_eq_finrank' hcard).ge
    · -- inductive step: `n = 2·t ≥ 2`
      obtain ⟨t, ht⟩ := hEven
      have hn2 : 2 ≤ n := by omega
      -- STEP 1: extract a single `2×2` block `(p, q, ν)` with `a p = -ν•q`, `a q = ν•p`
      obtain ⟨p, q, ν, hp1, hq1, hpq, hν0, hap, haq⟩ :
          ∃ (p q : E) (ν : ℝ), ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ ⟪p, q⟫_ℝ = 0 ∧ 0 ≤ ν ∧
            a p = -ν • q ∧ a q = ν • p := by
        by_cases hazero : a = 0
        · -- `a = 0`: any orthonormal pair is a `ν = 0` block
          haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (show 0 < finrank ℝ E by rw [hn]; exact hnpos)
          obtain ⟨x, hx⟩ := exists_ne (0 : E)
          have hxne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
          set u := (‖x‖⁻¹ : ℝ) • x with hudef
          have hu1 : ‖u‖ = 1 := by
            rw [hudef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hx),
              inv_mul_cancel₀ hxne]
          have huneq : u ≠ 0 := by rw [hudef]; exact smul_ne_zero (inv_ne_zero hxne) hx
          have hdimperp : 0 < finrank ℝ (ℝ ∙ u)ᗮ := by
            have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u)
            rw [finrank_span_singleton huneq] at h1
            omega
          haveI : Nontrivial ↥((ℝ ∙ u)ᗮ) := Module.nontrivial_of_finrank_pos hdimperp
          obtain ⟨y', hy'⟩ := exists_ne (0 : ↥((ℝ ∙ u)ᗮ))
          have hyne : (y' : E) ≠ 0 := by simpa only [ne_eq, Submodule.coe_eq_zero] using hy'
          have hynorm : ‖(y' : E)‖ ≠ 0 := norm_ne_zero_iff.mpr hyne
          set w := (‖(y' : E)‖⁻¹ : ℝ) • (y' : E) with hwdef
          have hw1 : ‖w‖ = 1 := by
            rw [hwdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hyne),
              inv_mul_cancel₀ hynorm]
          have huw : ⟪u, w⟫_ℝ = 0 := by
            rw [hwdef, real_inner_smul_right,
              Submodule.mem_orthogonal_singleton_iff_inner_right.mp y'.2, mul_zero]
          exact ⟨u, w, 0, hu1, hw1, huw, le_refl 0, by simp [hazero], by simp [hazero]⟩
        · -- `a ≠ 0`: minimal eigenvector of `T := a ∘ₗ a` gives a genuine `ν > 0` block
          haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (show 0 < finrank ℝ E by rw [hn]; exact hnpos)
          obtain ⟨v₀, hv₀ne⟩ := DFunLike.ne_iff.mp hazero
          rw [LinearMap.zero_apply] at hv₀ne
          have hv₀0 : v₀ ≠ 0 := fun h => hv₀ne (by rw [h, map_zero])
          have hTsymm : (a ∘ₗ a).IsSymmetric := by
            intro x y
            simp only [LinearMap.comp_apply]
            rw [ha (a x) y, ha x (a y), neg_neg]
          set μ₀ : ℝ :=
            ⨅ z : {z : E // z ≠ 0}, RCLike.re ⟪(a ∘ₗ a) (z : E), (z : E)⟫_ℝ / ‖(z : E)‖ ^ 2 with hμ₀
          have hev : Module.End.HasEigenvalue (a ∘ₗ a) μ₀ :=
            hTsymm.hasEigenvalue_iInf_of_finiteDimensional
          have hbdd : BddBelow (Set.range fun z : {z : E // z ≠ 0} =>
              RCLike.re ⟪(a ∘ₗ a) (z : E), (z : E)⟫_ℝ / ‖(z : E)‖ ^ 2) := by
            refine ⟨-‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ ^ 2, ?_⟩
            rintro _ ⟨⟨z, hz⟩, rfl⟩
            show -‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ ^ 2
              ≤ RCLike.re ⟪(a ∘ₗ a) z, z⟫_ℝ / ‖z‖ ^ 2
            have hz2 : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
            have hnum : RCLike.re ⟪(a ∘ₗ a) (z : E), (z : E)⟫_ℝ = -‖a z‖ ^ 2 := by
              rw [RCLike.re_to_real]; simp only [LinearMap.comp_apply]
              rw [ha (a z) z, real_inner_self_eq_norm_sq]
            rw [hnum, neg_div, neg_le_neg_iff, div_le_iff₀ hz2]
            have hle : ‖a z‖ ≤ ‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ * ‖z‖ := by
              have h := (a.toContinuousLinearMap).le_opNorm z
              rwa [LinearMap.coe_toContinuousLinearMap'] at h
            calc ‖a z‖ ^ 2 = ‖a z‖ * ‖a z‖ := pow_two _
              _ ≤ (‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ * ‖z‖)
                    * (‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ * ‖z‖) :=
                  mul_self_le_mul_self (norm_nonneg _) hle
              _ = ‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ ^ 2 * ‖z‖ ^ 2 := by ring
          have hfv₀ : RCLike.re ⟪(a ∘ₗ a) v₀, v₀⟫_ℝ / ‖v₀‖ ^ 2 < 0 := by
            have hnum : RCLike.re ⟪(a ∘ₗ a) v₀, v₀⟫_ℝ = -‖a v₀‖ ^ 2 := by
              rw [RCLike.re_to_real]; simp only [LinearMap.comp_apply]
              rw [ha (a v₀) v₀, real_inner_self_eq_norm_sq]
            rw [hnum]
            exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (pow_pos (norm_pos_iff.mpr hv₀ne) 2))
              (pow_pos (norm_pos_iff.mpr hv₀0) 2)
          have hμ₀neg : μ₀ < 0 := by
            rw [hμ₀]; exact lt_of_le_of_lt (ciInf_le hbdd ⟨v₀, hv₀0⟩) hfv₀
          obtain ⟨u₀, hu₀ev⟩ := hev.exists_hasEigenvector
          have hu₀0 : u₀ ≠ 0 := hu₀ev.2
          have hTu₀ : (a ∘ₗ a) u₀ = μ₀ • u₀ := hu₀ev.apply_eq_smul
          have hu₀norm : ‖u₀‖ ≠ 0 := norm_ne_zero_iff.mpr hu₀0
          set u := (‖u₀‖⁻¹ : ℝ) • u₀ with hudef
          have hu1 : ‖u‖ = 1 := by
            rw [hudef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hu₀0),
              inv_mul_cancel₀ hu₀norm]
          have hTu : (a ∘ₗ a) u = μ₀ • u := by rw [hudef, map_smul, hTu₀, smul_comm]
          have hau_ne : a u ≠ 0 := by
            intro h
            have h1 : ⟪(a ∘ₗ a) u, u⟫_ℝ = μ₀ := by
              rw [hTu, real_inner_smul_left, real_inner_self_eq_norm_sq, hu1]; norm_num
            have h2 : ⟪(a ∘ₗ a) u, u⟫_ℝ = 0 := by
              simp only [LinearMap.comp_apply, h, map_zero, inner_zero_left]
            rw [h2] at h1; linarith
          set ν := ‖a u‖ with hνdef
          have hνpos : 0 < ν := by rw [hνdef]; exact norm_pos_iff.mpr hau_ne
          have hνne : ν ≠ 0 := hνpos.ne'
          have hνsq : ν ^ 2 = -μ₀ := by
            have h3 : ⟪(a ∘ₗ a) u, u⟫_ℝ = -‖a u‖ ^ 2 := by
              simp only [LinearMap.comp_apply]; rw [ha (a u) u, real_inner_self_eq_norm_sq]
            have h4 : ⟪(a ∘ₗ a) u, u⟫_ℝ = μ₀ := by
              rw [hTu, real_inner_smul_left, real_inner_self_eq_norm_sq, hu1]; norm_num
            rw [hνdef]; linarith
          set w := (ν⁻¹ : ℝ) • a u with hwdef
          have hw1 : ‖w‖ = 1 := by
            rw [hwdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hνpos, ← hνdef,
              inv_mul_cancel₀ hνne]
          have hawu : ν • w = a u := by
            rw [hwdef, smul_smul, mul_inv_cancel₀ hνne, one_smul]
          have hscalar : ν⁻¹ * μ₀ = -ν := by
            have hμ : μ₀ = -ν ^ 2 := by rw [hνsq]; ring
            rw [hμ, mul_neg, pow_two, ← mul_assoc, inv_mul_cancel₀ hνne, one_mul]
          have haw : a w = -ν • u := by
            rw [hwdef, map_smul, ← LinearMap.comp_apply, hTu, smul_smul, hscalar]
          have huw : ⟪u, w⟫_ℝ = 0 := by
            rw [hwdef, real_inner_smul_right]
            have h5 := ha u u
            have h5' := real_inner_comm u (a u)
            have h6 : ⟪u, a u⟫_ℝ = 0 := by linarith [h5, h5']
            rw [h6, mul_zero]
          exact ⟨w, u, ν, hw1, hu1, by rw [real_inner_comm]; exact huw, hνpos.le, haw, hawu.symm⟩
      -- STEP 2: the `2×2` block subspace `P = span {p, q}` and its `a`-invariant complement `Pᗮ`
      set P : Submodule ℝ E := Submodule.span ℝ (Set.range ![p, q]) with hPdef
      have hon_pq : Orthonormal ℝ ![p, q] := by
        rw [orthonormal_vecCons_iff]
        refine ⟨hp1, ?_, ?_⟩
        · intro i
          fin_cases i
          show ⟪p, q⟫_ℝ = 0
          exact hpq
        · rw [orthonormal_vecCons_iff]
          exact ⟨hq1, fun i => i.elim0, Orthonormal.of_isEmpty (𝕜 := ℝ) _⟩
      have hpP : p ∈ P := Submodule.subset_span ⟨0, by simp⟩
      have hqP : q ∈ P := Submodule.subset_span ⟨1, by simp⟩
      have hfinP : finrank ℝ P = 2 := by
        rw [hPdef, finrank_span_eq_card hon_pq.linearIndependent]; simp
      have hinv : ∀ x ∈ P, a x ∈ P := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem z hz =>
            obtain ⟨i, rfl⟩ := hz
            fin_cases i
            · show a p ∈ P
              rw [hap]; exact P.smul_mem _ hqP
            · show a q ∈ P
              rw [haq]; exact P.smul_mem _ hpP
        | zero => simpa using P.zero_mem
        | add x y _ _ ihx ihy => rw [map_add]; exact P.add_mem ihx ihy
        | smul c x _ ihx => rw [map_smul]; exact P.smul_mem c ihx
      have hinvC : ∀ x ∈ Pᗮ, a x ∈ Pᗮ := skewAdjoint_orthogonal_invariant a ha P hinv
      set aC : ↥(Pᗮ) →ₗ[ℝ] ↥(Pᗮ) := a.restrict hinvC with haCdef
      have haC_coe : ∀ x : ↥(Pᗮ), ((aC x : ↥(Pᗮ)) : E) = a (x : E) := by
        intro x; rw [haCdef]; rfl
      have haC : ∀ x y : ↥(Pᗮ), ⟪aC x, y⟫_ℝ = -⟪x, aC y⟫_ℝ := by
        intro x y
        rw [Submodule.coe_inner, Submodule.coe_inner, haC_coe, haC_coe]
        exact ha x y
      have hsum := Submodule.finrank_add_finrank_orthogonal P
      rw [hfinP, hn] at hsum
      have hlt : finrank ℝ Pᗮ < n := by omega
      have hEvenPerp : Even (finrank ℝ Pᗮ) := ⟨t - 1, by omega⟩
      -- STEP 3: recurse on the even-dimensional complement
      obtain ⟨κ', instκ', bC, νC, hνC, hCinl, hCinr⟩ :=
        IH (finrank ℝ Pᗮ) hlt aC haC rfl hEvenPerp
      letI : Fintype κ' := instκ'
      letI : DecidableEq κ' := Classical.decEq κ'
      -- STEP 4: glue the block frame `{p, q}` to the recursive basis `bC`
      set vv : (Unit ⊕ κ') ⊕ (Unit ⊕ κ') → E :=
        Sum.elim (Sum.elim (fun _ => p) (fun k => (bC (Sum.inl k) : E)))
                 (Sum.elim (fun _ => q) (fun k => (bC (Sum.inr k) : E))) with hvvdef
      set νfull : Unit ⊕ κ' → ℝ := Sum.elim (fun _ => ν) νC with hνfulldef
      have hbb : ∀ z z' : κ' ⊕ κ',
          ⟪(bC z : E), (bC z' : E)⟫_ℝ = if z = z' then (1 : ℝ) else 0 := by
        intro z z'; rw [← Submodule.coe_inner]; exact orthonormal_iff_ite.mp bC.orthonormal z z'
      have hPbot : ∀ z : κ' ⊕ κ', ∀ x ∈ P, ⟪x, (bC z : E)⟫_ℝ = 0 :=
        fun z x hx => Submodule.inner_right_of_mem_orthogonal hx (bC z).2
      have hon : Orthonormal ℝ vv := by
        rw [orthonormal_iff_ite]
        have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp1]; norm_num
        have hqq : ⟪q, q⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hq1]; norm_num
        have hqp : ⟪q, p⟫_ℝ = 0 := by rw [real_inner_comm]; exact hpq
        have hpbC : ∀ z, ⟪p, (bC z : E)⟫_ℝ = 0 := fun z => hPbot z p hpP
        have hqbC : ∀ z, ⟪q, (bC z : E)⟫_ℝ = 0 := fun z => hPbot z q hqP
        have hbCp : ∀ z, ⟪(bC z : E), p⟫_ℝ = 0 := fun z => by rw [real_inner_comm]; exact hpbC z
        have hbCq : ∀ z, ⟪(bC z : E), q⟫_ℝ = 0 := fun z => by rw [real_inner_comm]; exact hqbC z
        rintro ((⟨⟩ | k) | (⟨⟩ | k)) ((⟨⟩ | l) | (⟨⟩ | l)) <;>
          simp [hvvdef, hp1, hq1, hpp, hqq, hpq, hqp, hpbC, hqbC, hbCp, hbCq, hbb]
      have hcardC : finrank ℝ Pᗮ = Fintype.card (κ' ⊕ κ') := finrank_eq_card_basis bC.toBasis
      have hcard : Fintype.card ((Unit ⊕ κ') ⊕ (Unit ⊕ κ')) = finrank ℝ E := by
        simp only [Fintype.card_sum, Fintype.card_unit] at hcardC ⊢
        omega
      have hspan : ⊤ ≤ Submodule.span ℝ (Set.range vv) :=
        (hon.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge
      set b : OrthonormalBasis ((Unit ⊕ κ') ⊕ (Unit ⊕ κ')) ℝ E :=
        OrthonormalBasis.mk hon hspan with hbdef
      have hbcoe : ⇑b = vv := OrthonormalBasis.coe_mk hon hspan
      refine ⟨Unit ⊕ κ', inferInstance, b, νfull, ?_, ?_, ?_⟩
      · intro k
        rcases k with ⟨⟩ | k'
        · simpa only [hνfulldef, Sum.elim_inl] using hν0
        · simpa only [hνfulldef, Sum.elim_inr] using hνC k'
      · intro k
        rw [hbcoe]
        rcases k with ⟨⟩ | k'
        · simp only [hvvdef, hνfulldef, Sum.elim_inl, Sum.elim_inr]; exact hap
        · simp only [hvvdef, hνfulldef, Sum.elim_inl, Sum.elim_inr]
          rw [← haC_coe, hCinl k', Submodule.coe_smul]
      · intro k
        rw [hbcoe]
        rcases k with ⟨⟩ | k'
        · simp only [hvvdef, hνfulldef, Sum.elim_inl, Sum.elim_inr]; exact haq
        · simp only [hvvdef, hνfulldef, Sum.elim_inl, Sum.elim_inr]
          rw [← haC_coe, hCinr k', Submodule.coe_smul]

/-- **The abstract operator Youla pairing.**  For a finite-dimensional real inner product space `E`
    and a skew-adjoint operator `a` (`⟪a x, y⟫ = -⟪x, a y⟫`) with `Even (finrank ℝ E)`, there is an
    orthonormal basis indexed by `κ ⊕ κ` block-pairing `a` into `ν`-rotation `2×2` blocks
    (`a (b (inl k)) = -ν k • b (inr k)`, `a (b (inr k)) = ν k • b (inl k)`), with `ν ≥ 0`.  This is
    the coordinate-free heart of the Youla real antisymmetric normal form, **proved unconditionally**
    (no carry). -/
theorem youla_pairing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a : E →ₗ[ℝ] E)
    (ha : ∀ x y, ⟪a x, y⟫_ℝ = -⟪x, a y⟫_ℝ) (hdim : Even (finrank ℝ E)) :
    ∃ (κ : Type) (_ : Fintype κ) (b : OrthonormalBasis (κ ⊕ κ) ℝ E) (ν : κ → ℝ),
      (∀ k, 0 ≤ ν k) ∧
      (∀ k, a (b (Sum.inl k)) = -ν k • b (Sum.inr k)) ∧
      (∀ k, a (b (Sum.inr k)) = ν k • b (Sum.inl k)) :=
  youla_pairing_aux (finrank ℝ E) a ha rfl hdim

end AbstractYoulaPairing

end QIQTH.Williamson
