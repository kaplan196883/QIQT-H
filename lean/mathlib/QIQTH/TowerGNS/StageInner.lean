/-
  THE REPRESENTATION R2 (THE_REPRESENTATION_PLAN.md) — the per-stage GNS form.

  For each finite corner K, the Gibbs state defines the GNS sesquilinear form
  `gnsInner K x y := φ_K(xᴴ y) = tr(ρ_K xᴴ y)` — conjugate-linear in the FIRST slot (Mathlib's
  Core convention). Proved here: conjugate symmetry (trace of the conjugate transpose + the
  diagonal-real density + the trace cycle), POSITIVITY (`tr(ρ xᴴx) = tr(x ρ xᴴ) ≥ 0` — the
  A4 recipe: `trace_mul_cycle` + `PosSemidef.mul_mul_conjTranspose_same` + `trace_nonneg`),
  additivity/homogeneity in each slot, and positivity of the state on PSD matrices.

  Plus THE STABILIZED PAIRING `pairInner C C' a b` (the R3 pre-space inner product between
  components at stages C and C', evaluated at the common stage C ⊔ C') with its STABILITY
  lemma `pairInner_embed`: the pairing computed at ANY common upper stage K agrees — R1's
  functoriality + the ⋆/mul laws + T7's state compatibility. No DirectSum, no completion here.
-/
import Mathlib
import QIQTH.TowerGNS.EmbedTrans

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-- **The per-stage GNS form**: `⟪x, y⟫_K = φ_K(xᴴ y)` — conjugate-linear in the first slot. -/
noncomputable def gnsInner (K : Finset M) (x y : DiamondAlg L K) : ℂ :=
  stateOf (gibbsDensity L K ω β) (xᴴ * y)

theorem gnsInner_def (K : Finset M) (x y : DiamondAlg L K) :
    gnsInner L ω β K x y = Matrix.trace (gibbsDensity L K ω β * (xᴴ * y)) := rfl

/-- The state is nonnegative on positive semidefinite matrices (`ρ` PSD ⟹ `tr(ρ q) =
    tr(√q ρ √qᴴ)`-type positivity; here directly via the diagonal weights). -/
theorem stateOf_posSemidef_nonneg (K : Finset M) {q : DiamondAlg L K}
    (hq : q.PosSemidef) : 0 ≤ stateOf (gibbsDensity L K ω β) q := by
  rw [stateOf, gibbsDensity, QIQTH.Tower.trace_diagonal_mul]
  refine Finset.sum_nonneg fun n _ => ?_
  have h1 : (0 : ℂ) ≤ ((gibbsWeight L K ω β n : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (gibbsWeight_pos L K ω β n).le
  have h2 : (0 : ℂ) ≤ q n n := hq.diag_nonneg
  exact mul_nonneg h1 h2

/-- **Positivity of the form**: `0 ≤ ⟪x, x⟫_K` (in the complex order — real and nonnegative).
    The A4 recipe: cycle the trace to `tr(x ρ xᴴ)`, which is the trace of a PSD matrix. -/
theorem gnsInner_self_nonneg (K : Finset M) (x : DiamondAlg L K) :
    0 ≤ gnsInner L ω β K x x := by
  have hcycle : gnsInner L ω β K x x
      = Matrix.trace (x * gibbsDensity L K ω β * xᴴ) := by
    rw [gnsInner_def, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [hcycle]
  exact ((gibbs_isDensity L K ω β).posSemidef.mul_mul_conjTranspose_same x).trace_nonneg

/-- Conjugate symmetry: `conj ⟪y, x⟫ = ⟪x, y⟫` (the Core field orientation). -/
theorem gnsInner_conj_symm (K : Finset M) (x y : DiamondAlg L K) :
    starRingEnd ℂ (gnsInner L ω β K y x) = gnsInner L ω β K x y := by
  have hstar : (gibbsDensity L K ω β * (yᴴ * x))ᴴ
      = xᴴ * y * gibbsDensity L K ω β := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    have hρ : (gibbsDensity L K ω β)ᴴ = gibbsDensity L K ω β := by
      rw [gibbsDensity, Matrix.diagonal_conjTranspose]
      congr 1
      funext n
      simp [Complex.conj_ofReal]
    rw [hρ, Matrix.mul_assoc]
  calc starRingEnd ℂ (gnsInner L ω β K y x)
      = star (Matrix.trace (gibbsDensity L K ω β * (yᴴ * x))) := rfl
    _ = Matrix.trace ((gibbsDensity L K ω β * (yᴴ * x))ᴴ) :=
        (Matrix.trace_conjTranspose _).symm
    _ = Matrix.trace (xᴴ * y * gibbsDensity L K ω β) := by rw [hstar]
    _ = gnsInner L ω β K x y := by
        rw [gnsInner_def, Matrix.trace_mul_comm]

/-- Additivity in the second slot. -/
theorem gnsInner_add_right (K : Finset M) (x y z : DiamondAlg L K) :
    gnsInner L ω β K x (y + z) = gnsInner L ω β K x y + gnsInner L ω β K x z := by
  simp only [gnsInner, stateOf, Matrix.mul_add, Matrix.trace_add]

/-- Additivity in the first slot. -/
theorem gnsInner_add_left (K : Finset M) (x y z : DiamondAlg L K) :
    gnsInner L ω β K (x + y) z = gnsInner L ω β K x z + gnsInner L ω β K y z := by
  simp only [gnsInner, stateOf, Matrix.conjTranspose_add, Matrix.add_mul,
    Matrix.mul_add, Matrix.trace_add]

/-- ℂ-homogeneity in the second slot. -/
theorem gnsInner_smul_right (K : Finset M) (c : ℂ) (x y : DiamondAlg L K) :
    gnsInner L ω β K x (c • y) = c * gnsInner L ω β K x y := by
  simp only [gnsInner, stateOf, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- Conjugate homogeneity in the first slot (the Core `smul_left` orientation). -/
theorem gnsInner_smul_left (K : Finset M) (c : ℂ) (x y : DiamondAlg L K) :
    gnsInner L ω β K (c • x) y = starRingEnd ℂ c * gnsInner L ω β K x y := by
  simp only [gnsInner, stateOf, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rfl

/-- **The stabilized pairing** — the inner product between tower components at stages `C` and
    `C'`, evaluated at the common stage `C ⊔ C'` (the R3 pre-space form). -/
noncomputable def pairInner (C C' : Finset M) (a : DiamondAlg L C) (b : DiamondAlg L C') : ℂ :=
  gnsInner L ω β (C ⊔ C')
    (cornerEmbed L C (C ⊔ C') Finset.subset_union_left a)
    (cornerEmbed L C' (C ⊔ C') Finset.subset_union_right b)

/-- **R2 CAPSTONE — stability of the pairing**: the pairing computed at ANY common upper stage
    agrees with `pairInner` — R1's functoriality composes the embeddings, the ⋆/mul laws push
    them through the form, and T7's state compatibility collapses the stage. -/
theorem pairInner_embed (C C' K : Finset M) (hC : C ⊆ K) (hC' : C' ⊆ K)
    (a : DiamondAlg L C) (b : DiamondAlg L C') :
    pairInner L ω β C C' a b
      = gnsInner L ω β K (cornerEmbed L C K hC a) (cornerEmbed L C' K hC' b) := by
  have hsub : C ⊔ C' ⊆ K := Finset.union_subset hC hC'
  have key : ∀ X Y : DiamondAlg L (C ⊔ C'),
      gnsInner L ω β K (cornerEmbed L (C ⊔ C') K hsub X) (cornerEmbed L (C ⊔ C') K hsub Y)
        = gnsInner L ω β (C ⊔ C') X Y := by
    intro X Y
    rw [gnsInner, gnsInner, ← cornerEmbed_star, ← cornerEmbed_mul, cornerEmbed_stateOf]
  have ha : cornerEmbed L C K hC a
      = cornerEmbed L (C ⊔ C') K hsub (cornerEmbed L C (C ⊔ C') Finset.subset_union_left a) := by
    rw [cornerEmbed_trans]
  have hb : cornerEmbed L C' K hC' b
      = cornerEmbed L (C ⊔ C') K hsub (cornerEmbed L C' (C ⊔ C') Finset.subset_union_right b) := by
    rw [cornerEmbed_trans]
  rw [ha, hb, key]
  rfl

end QIQTH.TowerGNS
