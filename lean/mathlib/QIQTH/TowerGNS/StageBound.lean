/-
  THE REPRESENTATION R5 (THE_REPRESENTATION_PLAN.md) — THE GNS BOUNDEDNESS INEQUALITY.

  For a corner element `a` at stage `C`, left multiplication by the embedded `ι a` on the
  stage-`K` GNS form is BOUNDED with the explicit FROBENIUS constant
  `c(a) = frobNormSq a = tr(aᴴa) = Σ‖a i j‖²`:

      ⟪ιa·x, ιa·x⟫_K ≤ c(a) · ⟪x, x⟫_K.

  HONEST SCOPE: `c(a)` is the FROBENIUS (Hilbert–Schmidt) norm squared, NOT the C*-norm —
  the GNS representation is proved BOUNDED here, never claimed contractive; the sharp
  `‖a‖²`-bound (‖π(a)‖ ≤ ‖a‖) is not needed for R6's continuous extension and is not stated.

  The engine is the matrix inequality `frobBound`: `c(a)•1 − aᴴa` is PSD (a rowwise squared
  Cauchy–Schwarz on `star v ⬝ᵥ (aᴴa *ᵥ v) = ‖a *ᵥ v‖²`), transported through the corner
  embedding by `cornerEmbed_posSemidef` (the `star B * B` decomposition of a PSD matrix, via
  the scoped `MatrixOrder` C*-order) and sandwiched by `xᴴ·_·x`; positivity of the Gibbs
  state on PSD matrices then yields the capstone `gnsInner_leftMul_le`.
-/
import Mathlib
import QIQTH.TowerGNS.PreSpace

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The Frobenius constant -/

/-- **The Frobenius constant** `c(a) = tr(aᴴa)` — the Hilbert–Schmidt norm squared of the
    corner element `a` (NOT the C*-norm; the boundedness constant of R5, never claimed
    sharp). -/
noncomputable def frobNormSq (C : Finset M) (a : DiamondAlg L C) : ℝ :=
  RCLike.re (Matrix.trace (aᴴ * a))

/-- `star v ⬝ᵥ v` is the (real, nonnegative) sum of the squared entry norms — the reduction
    of the complex-order dot-product positivity to a REAL sum. -/
theorem star_dotProduct_self_eq {n : Type*} [Fintype n] (v : n → ℂ) :
    star v ⬝ᵥ v = ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul,
    Complex.ofReal_sum, Complex.ofReal_pow]
  norm_cast

/-- The trace of `aᴴ * a` is the (real) double sum of the squared entry norms. -/
theorem trace_conjTranspose_mul_self_eq (C : Finset M) (a : DiamondAlg L C) :
    Matrix.trace (aᴴ * a) = ((∑ i, ∑ j, ‖a i j‖ ^ 2 : ℝ) : ℂ) := by
  have hdiag : ∀ j, (aᴴ * a) j j = ((∑ i, ‖a i j‖ ^ 2 : ℝ) : ℂ) := fun j => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
      RCLike.conj_mul, Complex.ofReal_sum, Complex.ofReal_pow]
    norm_cast
  calc Matrix.trace (aᴴ * a) = ∑ j, ((∑ i, ‖a i j‖ ^ 2 : ℝ) : ℂ) := by
        simp only [Matrix.trace, Matrix.diag_apply]
        exact Finset.sum_congr rfl fun j _ => hdiag j
    _ = ((∑ j, ∑ i, ‖a i j‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.ofReal_sum]
    _ = ((∑ i, ∑ j, ‖a i j‖ ^ 2 : ℝ) : ℂ) := by rw [Finset.sum_comm]

/-- The Frobenius constant is the double sum of the squared entry norms. -/
theorem frobNormSq_eq_sum (C : Finset M) (a : DiamondAlg L C) :
    frobNormSq L C a = ∑ i, ∑ j, ‖a i j‖ ^ 2 := by
  rw [frobNormSq, trace_conjTranspose_mul_self_eq, RCLike.re_to_complex, Complex.ofReal_re]

/-- The Frobenius constant is nonnegative. -/
theorem frobNormSq_nonneg (C : Finset M) (a : DiamondAlg L C) : 0 ≤ frobNormSq L C a := by
  rw [frobNormSq_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-! ### The Frobenius matrix inequality -/

/-- **The Frobenius bound**: `c(a)•1 − aᴴa` is positive semidefinite — rowwise squared
    Cauchy–Schwarz (`‖(a *ᵥ v) i‖ ≤ Σⱼ ‖a i j‖·‖v j‖`, then
    `Finset.sum_mul_sq_le_sq_mul_sq`), with the complex-order positivity reduced to the
    real inequality through `star_dotProduct_self_eq`. -/
theorem frobBound (C : Finset M) (a : DiamondAlg L C) :
    ((frobNormSq L C a : ℂ) • (1 : DiamondAlg L C) - aᴴ * a).PosSemidef := by
  have hsa : IsSelfAdjoint (frobNormSq L C a : ℂ) := by
    rw [isSelfAdjoint_iff]
    exact Complex.conj_ofReal _
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_one.smul hsa).sub (Matrix.isHermitian_conjTranspose_mul_self a))
    fun v => ?_
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star, star_dotProduct_self_eq,
    star_dotProduct_self_eq, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.zero_le_real, sub_nonneg, frobNormSq_eq_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have hrow : ‖(a *ᵥ v) i‖ ≤ ∑ j, ‖a i j‖ * ‖v j‖ := by
    have hmv : (a *ᵥ v) i = ∑ j, a i j * v j := by
      simp only [Matrix.mulVec, dotProduct]
    rw [hmv]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => norm_mul _ _
  calc ‖(a *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖a i j‖ * ‖v j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hrow 2
    _ ≤ (∑ j, ‖a i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-! ### PSD transport along the corner embedding -/

section PosSemidefTransport

open scoped MatrixOrder

/-- **PSD transport**: the corner embedding preserves positive semidefiniteness — decompose
    `q = star B * B` (the scoped `MatrixOrder` C*-order) and push the decomposition through
    the ⋆-algebra laws of the embedding. -/
theorem cornerEmbed_posSemidef {C K : Finset M} (h : C ⊆ K) {q : DiamondAlg L C}
    (hq : q.PosSemidef) : (cornerEmbed L C K h q).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hq.nonneg
  rw [hB, Matrix.star_eq_conjTranspose, cornerEmbed_mul, cornerEmbed_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end PosSemidefTransport

/-! ### The R5 capstone — GNS boundedness -/

/-- **R5 CAPSTONE — the GNS boundedness inequality**: left multiplication by the embedded
    corner element `ι a` is bounded on the stage-`K` GNS form with the Frobenius constant:
    `⟪ιa·x, ιa·x⟫_K ≤ frobNormSq a · ⟪x, x⟫_K`. (Frobenius bound, NOT the C*-norm — π is
    bounded, never claimed contractive.) -/
theorem gnsInner_leftMul_le (C K : Finset M) (h : C ⊆ K) (a : DiamondAlg L C)
    (x : DiamondAlg L K) :
    RCLike.re (gnsInner L ω β K (cornerEmbed L C K h a * x) (cornerEmbed L C K h a * x))
      ≤ frobNormSq L C a * RCLike.re (gnsInner L ω β K x x) := by
  -- the embedded gap matrix `c•1 − ι(aᴴa)` is PSD
  have hgap : ((frobNormSq L C a : ℂ) • (1 : DiamondAlg L K)
      - cornerEmbed L C K h (aᴴ * a)).PosSemidef := by
    have h1 := cornerEmbed_posSemidef L h (frobBound L C a)
    rwa [cornerEmbed_sub, cornerEmbed_smul, cornerEmbed_one] at h1
  -- the sandwich `xᴴ(gap)x` is PSD, so the Gibbs state is nonnegative on it
  have h0 := stateOf_posSemidef_nonneg L ω β K (hgap.conjTranspose_mul_mul_same x)
  -- rewrite the sandwich as `c•(xᴴx) − (ιa·x)ᴴ(ιa·x)`
  have hkey : (cornerEmbed L C K h a * x)ᴴ * (cornerEmbed L C K h a * x)
      = xᴴ * cornerEmbed L C K h (aᴴ * a) * x := by
    rw [Matrix.conjTranspose_mul, cornerEmbed_mul, cornerEmbed_star]
    simp only [Matrix.mul_assoc]
  have hexpand : xᴴ * ((frobNormSq L C a : ℂ) • (1 : DiamondAlg L K)
        - cornerEmbed L C K h (aᴴ * a)) * x
      = (frobNormSq L C a : ℂ) • (xᴴ * x)
        - (cornerEmbed L C K h a * x)ᴴ * (cornerEmbed L C K h a * x) := by
    rw [hkey, Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one]
  rw [hexpand] at h0
  -- expand the state linearly and pass to real parts
  rw [stateOf, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul] at h0
  have hre := (Complex.le_def.mp h0).1
  rw [Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul] at hre
  rw [gnsInner_def, gnsInner_def, RCLike.re_to_complex, RCLike.re_to_complex]
  linarith

end QIQTH.TowerGNS
