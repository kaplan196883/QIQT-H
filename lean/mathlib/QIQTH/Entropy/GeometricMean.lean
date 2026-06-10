/-
  The operator geometric mean `A # B` and its **joint concavity** (Carlen §3.3–3.5).

  For positive-definite `A` and positive-semidefinite `B`,
  `gmean A B = A^{1/2} (A^{-1/2} B A^{-1/2})^{1/2} A^{1/2}`.
  It is characterised variationally as the **largest** Hermitian `X` with `[[A, X],[X, B]] ⪰ 0`
  (Ando):
  * `gmean_fromBlocks_posSemidef` (achievability): the block at `X = A # B` is PSD, via the
    Schur complement with `(A#B) A⁻¹ (A#B) = B`;
  * `le_gmean_of_fromBlocks_posSemidef` (maximality): any Hermitian `X` making the block PSD satisfies
    `X ≤ A # B`, via the reduction `Z² ≤ C ⟹ Z ≤ √C` (`matrix_le_sqrt_of_sq_le`) after conjugating by
    `A^{-1/2}`.
  Summing the achievability blocks and applying maximality gives **superadditivity = joint concavity**:
  `A₀ # B₀ + A₁ # B₁ ≤ (A₀+A₁) # (B₀+B₁)`.  This is the operator-mean input to Lieb's concavity.
-/
import QIQTH.Entropy.MatrixOperatorMonotone
import QIQTH.Entropy.OperatorConvex

namespace QIQTH.Entropy

open Matrix CStarMatrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The operator geometric mean `A # B = A^{1/2} (A^{-1/2} B A^{-1/2})^{1/2} A^{1/2}`. -/
noncomputable def gmean (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt A * CFC.sqrt ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) * CFC.sqrt A

/-! ### `√A` algebra for positive-definite `A` -/

/-- `√A` is Hermitian. -/
lemma sqrt_isHermitian (A : Matrix n n ℂ) : (CFC.sqrt A).IsHermitian :=
  (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian

/-- `(√A)ᴴ = √A` (simp form, matching any argument association). -/
@[local simp] lemma sqrt_conjTranspose (A : Matrix n n ℂ) : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
  (sqrt_isHermitian A).eq

/-- `(√A)⁻¹` is Hermitian. -/
lemma sqrt_inv_isHermitian (A : Matrix n n ℂ) : ((CFC.sqrt A)⁻¹).IsHermitian :=
  (sqrt_isHermitian A).inv

/-- `det (√A)` is a unit, for `A` positive definite (`√A · √A = A` and `det A` is a unit). -/
lemma sqrt_isUnit_det {A : Matrix n n ℂ} (hA : A.PosDef) : IsUnit (CFC.sqrt A).det := by
  have hss : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  rw [← hss, Matrix.det_mul] at hAdet
  exact isUnit_of_mul_isUnit_left hAdet

lemma sqrt_mul_inv {A : Matrix n n ℂ} (hA : A.PosDef) : CFC.sqrt A * (CFC.sqrt A)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (sqrt_isUnit_det hA)

lemma sqrt_inv_mul {A : Matrix n n ℂ} (hA : A.PosDef) : (CFC.sqrt A)⁻¹ * CFC.sqrt A = 1 :=
  Matrix.nonsing_inv_mul _ (sqrt_isUnit_det hA)

/-- `(√A)⁻¹ (√A)⁻¹ = A⁻¹`. -/
lemma sqrt_inv_mul_sqrt_inv {A : Matrix n n ℂ} (hA : A.PosDef) :
    (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ = A⁻¹ := by
  rw [Matrix.PosSemidef.inv_sqrt hA.posSemidef]
  exact CFC.sqrt_mul_sqrt_self _ hA.inv.posSemidef.nonneg

/-- `√A · A⁻¹ · √A = 1`. -/
lemma sqrt_mul_inv_mul_sqrt {A : Matrix n n ℂ} (hA : A.PosDef) :
    CFC.sqrt A * A⁻¹ * CFC.sqrt A = 1 := by
  have e : CFC.sqrt A * A⁻¹ * CFC.sqrt A
      = (CFC.sqrt A * (CFC.sqrt A)⁻¹) * ((CFC.sqrt A)⁻¹ * CFC.sqrt A) := by
    rw [← sqrt_inv_mul_sqrt_inv hA]; simp only [Matrix.mul_assoc]
  rw [e, sqrt_mul_inv hA, sqrt_inv_mul hA, Matrix.one_mul]

/-- The inner conjugate `(√A)⁻¹ B (√A)⁻¹` is positive semidefinite for `0 ≤ B`. -/
lemma inner_conj_posSemidef {A B : Matrix n n ℂ} (hB : 0 ≤ B) :
    (0 : Matrix n n ℂ) ≤ (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹ := by
  have h := (nonneg_iff_posSemidef.mp hB).conjTranspose_mul_mul_same (CFC.sqrt A)⁻¹
  rw [(sqrt_inv_isHermitian A).eq] at h
  exact nonneg_iff_posSemidef.mpr h

/-! ### Achievability and the defining identity -/

/-- `gmean` is Hermitian. -/
lemma gmean_isHermitian (A B : Matrix n n ℂ) : (gmean A B).IsHermitian := by
  show (gmean A B)ᴴ = gmean A B
  unfold gmean
  simp only [Matrix.conjTranspose_mul, sqrt_conjTranspose, Matrix.mul_assoc]

/-- **Defining identity** `(A # B) A⁻¹ (A # B) = B` for `A` positive definite, `0 ≤ B`. -/
lemma gmean_mul_inv_mul_gmean {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : 0 ≤ B) :
    gmean A B * A⁻¹ * gmean A B = B := by
  have htt : CFC.sqrt ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹)
      * CFC.sqrt ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) = (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹ :=
    CFC.sqrt_mul_sqrt_self _ (inner_conj_posSemidef hB)
  have key : CFC.sqrt A * A⁻¹ * CFC.sqrt A = 1 := sqrt_mul_inv_mul_sqrt hA
  have hsr : CFC.sqrt A * (CFC.sqrt A)⁻¹ = 1 := sqrt_mul_inv hA
  have hsl : (CFC.sqrt A)⁻¹ * CFC.sqrt A = 1 := sqrt_inv_mul hA
  unfold gmean
  set s := CFC.sqrt A
  set t := CFC.sqrt (s⁻¹ * B * s⁻¹)
  calc s * t * s * A⁻¹ * (s * t * s)
      = s * t * (s * A⁻¹ * s) * (t * s) := by simp only [Matrix.mul_assoc]
    _ = s * t * 1 * (t * s) := by rw [key]
    _ = s * (t * t) * s := by rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = s * (s⁻¹ * B * s⁻¹) * s := by rw [htt]
    _ = (s * s⁻¹) * B * (s⁻¹ * s) := by simp only [Matrix.mul_assoc]
    _ = B := by rw [hsr, hsl, Matrix.one_mul, Matrix.mul_one]

/-- **Achievability** (Ando): the block `[[A, A#B],[A#B, B]]` is positive semidefinite. -/
lemma gmean_fromBlocks_posSemidef {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : 0 ≤ B) :
    (Matrix.fromBlocks A (gmean A B) (gmean A B) B).PosSemidef := by
  haveI : Invertible A := hA.isUnit.invertible
  have h := fromBlocks_star_inv_posSemidef hA (gmean A B)
  rw [(gmean_isHermitian A B).eq, gmean_mul_inv_mul_gmean hA hB] at h
  exact h

/-! ### Maximality -/

/-- **Maximality** (Ando): any Hermitian `X` making `[[A, X],[X, B]]` positive semidefinite satisfies
    `X ≤ A # B`. -/
lemma le_gmean_of_fromBlocks_posSemidef {A B X : Matrix n n ℂ} (hA : A.PosDef) (hB : 0 ≤ B)
    (hX : X.IsHermitian) (h : (Matrix.fromBlocks A X X B).PosSemidef) : X ≤ gmean A B := by
  haveI : Invertible A := hA.isUnit.invertible
  -- Schur: X A⁻¹ X ≤ B
  have hschur : X * A⁻¹ * X ≤ B := by
    have hh : (Matrix.fromBlocks A X Xᴴ B).PosSemidef := by rwa [hX.eq]
    have := star_inv_le_of_fromBlocks_posSemidef hA hh
    rwa [hX.eq] at this
  have hsr : CFC.sqrt A * (CFC.sqrt A)⁻¹ = 1 := sqrt_mul_inv hA
  have hsl : (CFC.sqrt A)⁻¹ * CFC.sqrt A = 1 := sqrt_inv_mul hA
  have hAinv : (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ = A⁻¹ := sqrt_inv_mul_sqrt_inv hA
  -- Z := (√A)⁻¹ X (√A)⁻¹ is Hermitian, C := (√A)⁻¹ B (√A)⁻¹ ⪰ 0
  have hZherm : ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹).IsHermitian := by
    show ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹)ᴴ = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, (sqrt_inv_isHermitian A).eq, hX.eq,
      Matrix.mul_assoc]
  have hCnonneg : (0 : Matrix n n ℂ) ≤ (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹ := inner_conj_posSemidef hB
  -- conjugate hschur by (√A)⁻¹ : Z*Z ≤ C
  have hZZ : ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹) * ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹)
      ≤ (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹ := by
    have hconj := conjTranspose_mul_mul_le hschur (CFC.sqrt A)⁻¹
    rw [(sqrt_inv_isHermitian A).eq] at hconj
    have eL : (CFC.sqrt A)⁻¹ * (X * A⁻¹ * X) * (CFC.sqrt A)⁻¹
        = ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹) * ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹) := by
      rw [← hAinv]; simp only [Matrix.mul_assoc]
    rwa [eL] at hconj
  -- Z ≤ √C
  have hZt := matrix_le_sqrt_of_sq_le hZherm hCnonneg hZZ
  -- conjugate by √A : X ≤ gmean
  have hconj2 := conjTranspose_mul_mul_le hZt (CFC.sqrt A)
  rw [(sqrt_isHermitian A).eq] at hconj2
  have eX : CFC.sqrt A * ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹) * CFC.sqrt A = X := by
    calc CFC.sqrt A * ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹) * CFC.sqrt A
        = (CFC.sqrt A * (CFC.sqrt A)⁻¹) * X * ((CFC.sqrt A)⁻¹ * CFC.sqrt A) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [hsr, hsl, Matrix.one_mul, Matrix.mul_one]
  rw [eX] at hconj2
  exact hconj2

/-! ### Joint concavity -/

/-- **Joint concavity (superadditivity) of the operator geometric mean** (Carlen §3.5):
    `A₀ # B₀ + A₁ # B₁ ≤ (A₀+A₁) # (B₀+B₁)` for positive-definite `Aᵢ` and `0 ≤ Bᵢ`. -/
theorem gmean_superadditive {A₀ A₁ B₀ B₁ : Matrix n n ℂ}
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) :
    gmean A₀ B₀ + gmean A₁ B₁ ≤ gmean (A₀ + A₁) (B₀ + B₁) := by
  have hblock : (Matrix.fromBlocks (A₀ + A₁) (gmean A₀ B₀ + gmean A₁ B₁)
      (gmean A₀ B₀ + gmean A₁ B₁) (B₀ + B₁)).PosSemidef := by
    have hsum := (gmean_fromBlocks_posSemidef hA₀ hB₀).add (gmean_fromBlocks_posSemidef hA₁ hB₁)
    rwa [Matrix.fromBlocks_add] at hsum
  exact le_gmean_of_fromBlocks_posSemidef (hA₀.add hA₁) (add_nonneg hB₀ hB₁)
    ((gmean_isHermitian A₀ B₀).add (gmean_isHermitian A₁ B₁)) hblock

/-! ### Congruence covariance (transformer invariance) -/

/-- The conjugation of a 2×2 block by the block-diagonal `diag(M,M)`:
    `diag(M,M) · [[X,W],[W,Y]] · diag(M,M)ᴴ = [[MXMᴴ, MWMᴴ],[MWMᴴ, MYMᴴ]]`. -/
lemma fromBlocks_conj (M X W Y : Matrix n n ℂ) :
    Matrix.fromBlocks M 0 0 M * Matrix.fromBlocks X W W Y * (Matrix.fromBlocks M 0 0 M)ᴴ
      = Matrix.fromBlocks (M * X * Mᴴ) (M * W * Mᴴ) (M * W * Mᴴ) (M * Y * Mᴴ) := by
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_assoc]

/-- **Congruence covariance** of the operator geometric mean (Ando): for invertible `M`,
    `(M X Mᴴ) # (M Y Mᴴ) = M (X # Y) Mᴴ`.  This is the geodesic/transformer invariance underlying the
    weight-midpoint identity `(A#ₛB) #½ (A#ₜB) = A#_{(s+t)/2}B`, hence the dense dyadic weights. -/
theorem gmean_congr {X Y M : Matrix n n ℂ} (hX : X.PosDef) (hY : 0 ≤ Y) (hM : IsUnit M.det) :
    gmean (M * X * Mᴴ) (M * Y * Mᴴ) = M * gmean X Y * Mᴴ := by
  have hMstar : (star M : Matrix n n ℂ) = Mᴴ := Matrix.star_eq_conjTranspose M
  have hMX : (M * X * Mᴴ).PosDef := by
    rw [← hMstar]; exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
      ((Matrix.isUnit_iff_isUnit_det M).mpr hM)).mpr hX
  have hMY : (0 : Matrix n n ℂ) ≤ M * Y * Mᴴ := by
    have := (nonneg_iff_posSemidef.mp hY).mul_mul_conjTranspose_same M
    exact nonneg_iff_posSemidef.mpr this
  have hMmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hMmul' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  -- forward: M (X#Y) Mᴴ ≤ gmean(MXMᴴ)(MYMᴴ)
  have hgHerm : (M * gmean X Y * Mᴴ).IsHermitian := by
    show (M * gmean X Y * Mᴴ)ᴴ = M * gmean X Y * Mᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (gmean_isHermitian X Y).eq, Matrix.mul_assoc]
  have hfwd : M * gmean X Y * Mᴴ ≤ gmean (M * X * Mᴴ) (M * Y * Mᴴ) := by
    have hblk := (gmean_fromBlocks_posSemidef hX hY).mul_mul_conjTranspose_same
      (Matrix.fromBlocks M 0 0 M)
    rw [fromBlocks_conj] at hblk
    exact le_gmean_of_fromBlocks_posSemidef hMX hMY hgHerm hblk
  -- reverse: gmean(MXMᴴ)(MYMᴴ) ≤ M (X#Y) Mᴴ
  have hrev : gmean (M * X * Mᴴ) (M * Y * Mᴴ) ≤ M * gmean X Y * Mᴴ := by
    set G := gmean (M * X * Mᴴ) (M * Y * Mᴴ) with hG
    have hGh : G.IsHermitian := gmean_isHermitian _ _
    -- conjugate achievability block of (MXMᴴ,MYMᴴ) by diag(M⁻¹,M⁻¹) to land on (X,Y)
    have hblk := (gmean_fromBlocks_posSemidef hMX hMY).mul_mul_conjTranspose_same
      (Matrix.fromBlocks M⁻¹ 0 0 M⁻¹)
    rw [fromBlocks_conj] at hblk
    have hXeq : M⁻¹ * (M * X * Mᴴ) * (M⁻¹)ᴴ = X := by
      have hr : M⁻¹ * (M * X * Mᴴ) * (M⁻¹)ᴴ = (M⁻¹ * M) * X * (Mᴴ * (M⁻¹)ᴴ) := by
        simp only [Matrix.mul_assoc]
      rw [hr, hMmul', ← Matrix.conjTranspose_mul, hMmul', Matrix.conjTranspose_one,
        Matrix.one_mul, Matrix.mul_one]
    have hYeq : M⁻¹ * (M * Y * Mᴴ) * (M⁻¹)ᴴ = Y := by
      have hr : M⁻¹ * (M * Y * Mᴴ) * (M⁻¹)ᴴ = (M⁻¹ * M) * Y * (Mᴴ * (M⁻¹)ᴴ) := by
        simp only [Matrix.mul_assoc]
      rw [hr, hMmul', ← Matrix.conjTranspose_mul, hMmul', Matrix.conjTranspose_one,
        Matrix.one_mul, Matrix.mul_one]
    rw [hXeq, hYeq] at hblk
    have hGHerm : (M⁻¹ * G * (M⁻¹)ᴴ).IsHermitian := by
      show (M⁻¹ * G * (M⁻¹)ᴴ)ᴴ = M⁻¹ * G * (M⁻¹)ᴴ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hGh.eq, Matrix.mul_assoc]
    have hle := le_gmean_of_fromBlocks_posSemidef hX hY hGHerm hblk
    -- conjugate back by M: G = M (M⁻¹ G (M⁻¹)ᴴ) Mᴴ ≤ M (X#Y) Mᴴ
    have hmono := mul_mul_conjTranspose_le hle M
    have hGeq : M * (M⁻¹ * G * (M⁻¹)ᴴ) * Mᴴ = G := by
      have hr : M * (M⁻¹ * G * (M⁻¹)ᴴ) * Mᴴ = (M * M⁻¹) * G * ((M⁻¹)ᴴ * Mᴴ) := by
        simp only [Matrix.mul_assoc]
      rw [hr, hMmul, ← Matrix.conjTranspose_mul, hMmul, Matrix.conjTranspose_one,
        Matrix.one_mul, Matrix.mul_one]
    rw [hGeq] at hmono
    exact hmono
  exact le_antisymm hrev hfwd

/-! ### Monotonicity and the dyadic ladder toward the general `A #ₜ B` family -/

/-- `A # B` is positive semidefinite (a congruence of the positive `√(√A⁻¹ B √A⁻¹)`). -/
lemma gmean_nonneg {A B : Matrix n n ℂ} (hB : 0 ≤ B) : 0 ≤ gmean A B := by
  have h := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹))
    ).mul_mul_conjTranspose_same (CFC.sqrt A)
  rw [(sqrt_isHermitian A).eq] at h
  exact nonneg_iff_posSemidef.mpr h

/-- **Monotonicity in the second argument**: `B ≤ B' ⟹ A # B ≤ A # B'`.  Via conjugation
    monotonicity and operator monotonicity of `√` — the ingredient that drives the dyadic ladder. -/
theorem gmean_le_gmean_right {A B B' : Matrix n n ℂ} (hB : 0 ≤ B) (hBB' : B ≤ B') :
    gmean A B ≤ gmean A B' := by
  have hin : (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹ ≤ (CFC.sqrt A)⁻¹ * B' * (CFC.sqrt A)⁻¹ := by
    have := conjTranspose_mul_mul_le hBB' (CFC.sqrt A)⁻¹
    rwa [(sqrt_inv_isHermitian A).eq] at this
  have hsq := matrix_sqrt_le_sqrt (inner_conj_posSemidef hB) hin
  have hconj := conjTranspose_mul_mul_le hsq (CFC.sqrt A)
  rw [(sqrt_isHermitian A).eq] at hconj
  exact hconj

/-- **`t = 1/4` weighted geometric mean concavity** (one rung up the dyadic ladder).
    `A #_{1/4} B = A # (A # B)` (composition identity), and its joint concavity follows from the
    superadditivity of `#` (twice) and monotonicity in the second argument:
    `A₀#(A₀#B₀) + A₁#(A₁#B₁) ≤ (A₀+A₁)#((A₀+A₁)#(B₀+B₁))`.
    Iterating gives every dyadic weight, and continuity the full `A #ₜ B` (hence `A^{1-t} ⊗ B^t`)
    family that feeds Lieb's concavity. -/
theorem gmean_nested_superadditive {A₀ A₁ B₀ B₁ : Matrix n n ℂ}
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) :
    gmean A₀ (gmean A₀ B₀) + gmean A₁ (gmean A₁ B₁)
      ≤ gmean (A₀ + A₁) (gmean (A₀ + A₁) (B₀ + B₁)) := by
  have h1 := gmean_superadditive hA₀ hA₁ (gmean_nonneg (A := A₀) hB₀) (gmean_nonneg (A := A₁) hB₁)
  have h2 := gmean_superadditive hA₀ hA₁ hB₀ hB₁
  have h3 := gmean_le_gmean_right (A := A₀ + A₁)
    (add_nonneg (gmean_nonneg (A := A₀) hB₀) (gmean_nonneg (A := A₁) hB₁)) h2
  exact h1.trans h3

/-- The `k`-fold nested geometric mean `nestGmean k A B = A #_{1/2ᵏ} B` (using the composition identity
    `A # (A #ₜ B) = A #_{t/2} B`): `nestGmean 0 A B = B`, `nestGmean (k+1) A B = A # (nestGmean k A B)`. -/
noncomputable def nestGmean : ℕ → Matrix n n ℂ → Matrix n n ℂ → Matrix n n ℂ
  | 0, _, B => B
  | (k + 1), A, B => gmean A (nestGmean k A B)

/-- `0 ≤ nestGmean k A B`. -/
lemma nestGmean_nonneg (k : ℕ) {A B : Matrix n n ℂ} (hB : 0 ≤ B) : 0 ≤ nestGmean k A B := by
  induction k with
  | zero => exact hB
  | succ m ih => exact gmean_nonneg (A := A) ih

/-- **Joint concavity of the weighted geometric mean at every dyadic weight `t = 1/2ᵏ`**: the nested
    mean is superadditive,
    `nestGmean k A₀ B₀ + nestGmean k A₁ B₁ ≤ nestGmean k (A₀+A₁) (B₀+B₁)`.
    Proof by induction on `k`: each rung uses superadditivity of `#` and monotonicity in the second
    argument (`gmean_le_gmean_right`), exactly as in the `k=2` (`t=1/4`) case.  Continuity in the weight
    then yields the full `A #ₜ B` family — equivalently the joint concavity of `A^{1-t} ⊗ B^t` feeding
    Lieb's concavity theorem. -/
theorem nestGmean_superadditive (k : ℕ) {A₀ A₁ B₀ B₁ : Matrix n n ℂ}
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) :
    nestGmean k A₀ B₀ + nestGmean k A₁ B₁ ≤ nestGmean k (A₀ + A₁) (B₀ + B₁) := by
  induction k with
  | zero => exact le_refl _
  | succ m ih =>
    have h1 := gmean_superadditive hA₀ hA₁ (nestGmean_nonneg m (A := A₀) hB₀)
      (nestGmean_nonneg m (A := A₁) hB₁)
    have h3 := gmean_le_gmean_right (A := A₀ + A₁)
      (add_nonneg (nestGmean_nonneg m (A := A₀) hB₀) (nestGmean_nonneg m (A := A₁) hB₁)) ih
    exact h1.trans h3

end QIQTH.Entropy
