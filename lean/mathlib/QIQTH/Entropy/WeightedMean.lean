/-
  The weighted operator geometric mean `A #ₜ B`, `t ∈ [0,1]` (Kubo–Ando), via matrix `rpow`:
  `A #ₜ B = A^{1/2} (A^{-1/2} B A^{-1/2})^t A^{1/2}`.

  It interpolates the endpoints (`A #_0 B = A`, `A #_1 B = B`) and recovers the geometric mean at the
  midpoint (`A #_{1/2} B = A # B`, `wgmean_half`).  The weight-midpoint identity
  `(A#ₛB) #½ (A#ₜB) = A #_{(s+t)/2} B` (next step, from `gmean_congr`) then bisects `{0,1}` to all
  dyadic weights, which `matrix_le_of_tendsto` lifts to all `t` — the continuity route to Lieb.
-/
import QIQTH.Entropy.GeometricMean
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace QIQTH.Entropy

open Matrix CStarMatrix
open scoped MatrixOrder ComplexOrder Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The weighted operator geometric mean `A #ₜ B = A^{1/2} (A^{-1/2} B A^{-1/2})^t A^{1/2}`. -/
noncomputable def wgmean (t : ℝ) (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt A * (((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) ^ t) * CFC.sqrt A

/-- `A #ₜ B` is positive semidefinite (a congruence of the positive `(A^{-1/2}BA^{-1/2})^t`). -/
lemma wgmean_nonneg (t : ℝ) {A B : Matrix n n ℂ} : 0 ≤ wgmean t A B := by
  have h := (nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) (y := t))
    ).mul_mul_conjTranspose_same (CFC.sqrt A)
  rw [(sqrt_isHermitian A).eq] at h
  exact nonneg_iff_posSemidef.mpr h

/-- **Midpoint = geometric mean**: `A #_{1/2} B = A # B`. -/
lemma wgmean_half (A B : Matrix n n ℂ) : wgmean (1 / 2) A B = gmean A B := by
  unfold wgmean gmean
  rw [← CFC.sqrt_eq_rpow]

/-- **Left endpoint**: `A #_0 B = A`. -/
lemma wgmean_zero {A B : Matrix n n ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) : wgmean 0 A B = A := by
  unfold wgmean
  rw [CFC.rpow_zero _ (inner_conj_posSemidef hB), Matrix.mul_one, CFC.sqrt_mul_sqrt_self A hA]

/-- **Right endpoint**: `A #_1 B = B`. -/
lemma wgmean_one {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : 0 ≤ B) : wgmean 1 A B = B := by
  unfold wgmean
  rw [CFC.rpow_one _ (inner_conj_posSemidef hB),
    show CFC.sqrt A * ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) * CFC.sqrt A
        = (CFC.sqrt A * (CFC.sqrt A)⁻¹) * B * ((CFC.sqrt A)⁻¹ * CFC.sqrt A) by
      simp only [Matrix.mul_assoc],
    sqrt_mul_inv hA, sqrt_inv_mul hA, Matrix.one_mul, Matrix.mul_one]

/-- `A #ₜ B` is positive **definite** when `A, B` are — so the geometric-mean lemmas (which need a
    positive-definite first argument) apply to weighted-mean values. -/
lemma wgmean_posDef {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    (wgmean t A B).PosDef := by
  have hsqAU : IsUnit (CFC.sqrt A) := (Matrix.isUnit_iff_isUnit_det _).mpr (sqrt_isUnit_det hA)
  have hsqAinvU : IsUnit ((CFC.sqrt A)⁻¹) := Matrix.isUnit_nonsing_inv_iff.mpr hsqAU
  have hCpd : ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹).PosDef := by
    have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := B) hsqAinvU).mpr hB
    rwa [Matrix.star_eq_conjTranspose, (sqrt_inv_isHermitian A).eq] at h
  have hCtpd : (((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) ^ t).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp
      (IsStrictlyPositive.rpow _ t (Matrix.isStrictlyPositive_iff_posDef.mpr hCpd))
  have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff
    (x := ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) ^ t) hsqAU).mpr hCtpd
  rw [Matrix.star_eq_conjTranspose, (sqrt_isHermitian A).eq] at h
  exact h

/-! ### The commuting rpow identity and the weight-midpoint identity -/

/-- `√(Cˣ) = C^{x/2}` for positive-definite `C` and any real `x`. -/
lemma sqrt_rpow {C : Matrix n n ℂ} (hC : C.PosDef) (x : ℝ) :
    CFC.sqrt (C ^ x) = C ^ (x / 2) := by
  have hCn : (0 : Matrix n n ℂ) ≤ C := hC.posSemidef.nonneg
  rcases eq_or_ne x 0 with h | h
  · subst h
    rw [CFC.rpow_zero C hCn, CFC.sqrt_one, show (0 : ℝ) / 2 = 0 by norm_num, CFC.rpow_zero C hCn]
  · rw [CFC.sqrt_eq_rpow, CFC.rpow_rpow C x (1 / 2) h (Matrix.isStrictlyPositive_iff_posDef.mpr hC),
      show x * (1 / 2) = x / 2 by ring]

/-- **Commuting weighted-mean identity**: `(Cˢ) # (Cᵗ) = C^{(s+t)/2}` for positive-definite `C`.
    All factors are powers of the single `C`, so the geometric mean collapses by `rpow_add`. -/
lemma gmean_rpow {C : Matrix n n ℂ} (hC : C.PosDef) (s t : ℝ) :
    gmean (C ^ s) (C ^ t) = C ^ ((s + t) / 2) := by
  have hCu : IsUnit C := hC.isUnit
  have hCn : (0 : Matrix n n ℂ) ≤ C := hC.posSemidef.nonneg
  have hinv : (C ^ (s / 2 : ℝ))⁻¹ = C ^ (-(s / 2) : ℝ) := by
    apply Matrix.inv_eq_right_inv
    rw [← CFC.rpow_add hCu, add_neg_cancel, CFC.rpow_zero C hCn]
  unfold gmean
  rw [sqrt_rpow hC s, hinv, ← CFC.rpow_add hCu, ← CFC.rpow_add hCu, sqrt_rpow hC,
    ← CFC.rpow_add hCu, ← CFC.rpow_add hCu]
  congr 1
  ring

/-- **The weight-midpoint identity** (Ando): `(A #ₛ B) #½ (A #ₜ B) = A #_{(s+t)/2} B` for
    positive-definite `A, B`.  Direct from congruence-covariance (`gmean_congr` with `M = √A`) and the
    commuting identity `gmean(Cˢ)(Cᵗ) = C^{(s+t)/2}`.  Bisecting `{0,1}` with this gives joint concavity
    at every dyadic weight `k/2ⁿ` (dense), which `matrix_le_of_tendsto` lifts to all `t ∈ [0,1]`. -/
theorem wgmean_midpoint {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (s t : ℝ) :
    gmean (wgmean s A B) (wgmean t A B) = wgmean ((s + t) / 2) A B := by
  have hsqAU : IsUnit (CFC.sqrt A) := (Matrix.isUnit_iff_isUnit_det _).mpr (sqrt_isUnit_det hA)
  have hsqAinvU : IsUnit ((CFC.sqrt A)⁻¹) := Matrix.isUnit_nonsing_inv_iff.mpr hsqAU
  -- C := (√A)⁻¹ B (√A)⁻¹ is positive definite
  have hCpd : ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹).PosDef := by
    have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := B) hsqAinvU).mpr hB
    rwa [Matrix.star_eq_conjTranspose, (sqrt_inv_isHermitian A).eq] at h
  have hCspd : (((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) ^ s).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp
      (IsStrictlyPositive.rpow _ s (Matrix.isStrictlyPositive_iff_posDef.mpr hCpd))
  -- wgmean r A B = √A · Cʳ · (√A)ᴴ
  have hwg : ∀ r : ℝ, wgmean r A B
      = CFC.sqrt A * (((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) ^ r) * (CFC.sqrt A)ᴴ := by
    intro r; unfold wgmean; rw [(sqrt_isHermitian A).eq]
  rw [hwg s, hwg t, gmean_congr hCspd CFC.rpow_nonneg (sqrt_isUnit_det hA), gmean_rpow hCpd s t,
    hwg ((s + t) / 2)]

/-! ### Exponent continuity (the analysis lemma) -/

/-- **Continuity of the matrix power in the exponent**: `t ↦ A^t` is continuous for positive-definite
    `A`.  Via the spectral formula `A^t = V · diag(λᵢ^t) · Vᴴ`, this reduces to scalar continuity of
    `t ↦ λᵢ^t` (each `λᵢ > 0`).  (Mathlib has continuity of `rpow` only in the base, not the exponent.) -/
lemma continuous_matrix_rpow {A : Matrix n n ℂ} (hA : A.PosDef) :
    Continuous (fun t : ℝ => A ^ t) := by
  have hHerm := hA.isHermitian
  have key : (fun t : ℝ => A ^ t)
      = fun t => (hHerm.eigenvectorUnitary : Matrix n n ℂ)
          * Matrix.diagonal (fun i => (RCLike.ofReal (hHerm.eigenvalues i ^ t) : ℂ))
          * (hHerm.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    funext t
    rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg, Matrix.IsHermitian.cfc_eq hHerm,
      Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rfl
  rw [key]
  refine Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_) continuous_const
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  exact RCLike.continuous_ofReal.comp (Real.continuous_const_rpow (ne_of_gt (hA.eigenvalues_pos i)))

/-- The inner conjugate `(√A)⁻¹ B (√A)⁻¹` is positive definite for positive-definite `A, B`. -/
lemma inner_conj_posDef {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹).PosDef := by
  have hsqAU : IsUnit (CFC.sqrt A) := (Matrix.isUnit_iff_isUnit_det _).mpr (sqrt_isUnit_det hA)
  have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := B)
    (Matrix.isUnit_nonsing_inv_iff.mpr hsqAU)).mpr hB
  rwa [Matrix.star_eq_conjTranspose, (sqrt_inv_isHermitian A).eq] at h

/-- **Continuity of the weighted mean in its weight**: `t ↦ A #ₜ B` is continuous (for PosDef `A,B`).
    From `continuous_matrix_rpow` applied to `(√A)⁻¹ B (√A)⁻¹` and continuity of matrix multiplication. -/
lemma continuous_wgmean {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    Continuous (fun t : ℝ => wgmean t A B) :=
  (continuous_const.matrix_mul (continuous_matrix_rpow (inner_conj_posDef hA hB))).matrix_mul
    continuous_const

/-! ### Joint concavity at all dyadic weights, by bisection -/

/-- `A #ₜ B` is jointly superadditive (concave) at the weight `t` — the two-point inequality on
    positive-definite arguments. -/
def WgSuperadd (t : ℝ) : Prop :=
  ∀ {A₀ A₁ B₀ B₁ : Matrix n n ℂ}, A₀.PosDef → A₁.PosDef → B₀.PosDef → B₁.PosDef →
    wgmean t A₀ B₀ + wgmean t A₁ B₁ ≤ wgmean t (A₀ + A₁) (B₀ + B₁)

/-- Concavity at the left endpoint `t = 0` (where `A #_0 B = A`). -/
theorem wgSuperadd_zero : WgSuperadd (n := n) 0 := by
  intro A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁
  rw [wgmean_zero hA₀.posSemidef.nonneg hB₀.posSemidef.nonneg,
    wgmean_zero hA₁.posSemidef.nonneg hB₁.posSemidef.nonneg,
    wgmean_zero (hA₀.add hA₁).posSemidef.nonneg (hB₀.add hB₁).posSemidef.nonneg]

/-- Concavity at the right endpoint `t = 1` (where `A #_1 B = B`). -/
theorem wgSuperadd_one : WgSuperadd (n := n) 1 := by
  intro A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁
  rw [wgmean_one hA₀ hB₀.posSemidef.nonneg, wgmean_one hA₁ hB₁.posSemidef.nonneg,
    wgmean_one (hA₀.add hA₁) (hB₀.add hB₁).posSemidef.nonneg]

/-- **Bisection step**: concavity at `s` and `t` gives concavity at the midpoint `(s+t)/2`.  Via the
    weight-midpoint identity `A#_{(s+t)/2}B = (A#ₛB)#½(A#ₜB)`, the superadditivity of `#`, and joint
    monotonicity of `#`. -/
theorem wgSuperadd_midpoint {s t : ℝ} (hs : WgSuperadd (n := n) s) (ht : WgSuperadd (n := n) t) :
    WgSuperadd (n := n) ((s + t) / 2) := by
  intro A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁
  rw [← wgmean_midpoint hA₀ hB₀, ← wgmean_midpoint hA₁ hB₁,
    ← wgmean_midpoint (hA₀.add hA₁) (hB₀.add hB₁)]
  refine (gmean_superadditive (wgmean_posDef hA₀ hB₀ s) (wgmean_posDef hA₁ hB₁ s)
    (wgmean_nonneg t) (wgmean_nonneg t)).trans ?_
  exact gmean_mono ((wgmean_posDef hA₀ hB₀ s).add (wgmean_posDef hA₁ hB₁ s))
    (wgmean_posDef (hA₀.add hA₁) (hB₀.add hB₁) s)
    (add_nonneg (wgmean_nonneg t) (wgmean_nonneg t))
    (hs hA₀ hA₁ hB₀ hB₁) (ht hA₀ hA₁ hB₀ hB₁)

end QIQTH.Entropy
