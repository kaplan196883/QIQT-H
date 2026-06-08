/-
  F2c — the symmetric (bosonic) Fock space, pre-Hilbert structure.

  Builds on the keystone `ExpKernel.expKernel_posSemidef'` (Phase F2, `FOCK_CCR_FOUNDATION_PLAN.md`;
  Parthasarathy §19).  The **exponential vectors** `e(f)` (one per `f` in the one-particle space `H`)
  span a pre-inner-product space with `⟪e(f), e(g)⟫ = exp⟪f,g⟫`.  Positive-definiteness of that inner
  product is exactly the keystone, so this assembles a genuine `PreInnerProductSpace.Core ℂ` — the
  pre-Hilbert symmetric Fock space.  Its completion is the Fock space proper (next increment).

  `FockPre H` is a dedicated wrapper around `H →₀ ℂ` (formal finite ℂ-combinations of exponential
  vectors `e(f) = single f 1`), so the Fock inner product does not pollute the default `Finsupp`
  instances.  Axiom-free.
-/
import QIQTH.Fock.ExpKernel
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace QIQTH.Fock

open Complex Matrix
open scoped ComplexOrder InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The exponential inner product on formal combinations of exponential vectors:
    `⟪∑ aᵢ e(fᵢ), ∑ bⱼ e(gⱼ)⟫ = ∑ conj(aᵢ)·bⱼ·exp⟪fᵢ,gⱼ⟫`. -/
noncomputable def fockInner (φ ψ : H →₀ ℂ) : ℂ :=
  φ.sum fun g a => ψ.sum fun h b => star a * Complex.exp ⟪g, h⟫_ℂ * b

/-- The Fock inner product of an exponential vector with itself is nonnegative — this is the keystone
    `expKernel_posSemidef'` (positive-definiteness of `exp⟪f,g⟫`). -/
theorem fockInner_self_nonneg (φ : H →₀ ℂ) : 0 ≤ fockInner φ φ := by
  have h := (ExpKernel.expKernel_posSemidef' (id : H → H)).2 φ
  simpa only [fockInner, ExpKernel.expKernel_apply, id_eq] using h

/-- The Fock inner product is Hermitian. -/
theorem fockInner_conj (φ ψ : H →₀ ℂ) : conj (fockInner ψ φ) = fockInner φ ψ := by
  unfold fockInner
  simp only [map_finsuppSum, map_mul, RCLike.star_def, Complex.conj_conj, ← Complex.exp_conj,
    inner_conj_symm]
  rw [Finsupp.sum_comm]
  exact Finsupp.sum_congr fun g _ => Finsupp.sum_congr fun h _ => by ring

/-- The Fock inner product is additive in the first argument. -/
theorem fockInner_add_left (φ ψ χ : H →₀ ℂ) :
    fockInner (φ + ψ) χ = fockInner φ χ + fockInner ψ χ := by
  unfold fockInner
  rw [Finsupp.sum_add_index'] <;> simp [← Finsupp.sum_add, add_mul, star_add]

/-- The Fock inner product is conjugate-linear in the first argument. -/
theorem fockInner_smul_left (r : ℂ) (φ ψ : H →₀ ℂ) :
    fockInner (r • φ) ψ = conj r * fockInner φ ψ := by
  unfold fockInner
  rw [Finsupp.sum_smul_index (by intro i; simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun h _ => ?_
  rw [star_mul, RCLike.star_def]
  ring

/-- Pre-Fock space: formal finite ℂ-combinations of exponential vectors, carrying the Fock inner
    product (kept on a wrapper type so it does not pollute the default `Finsupp` instances). -/
def FockPre (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Type _ := H →₀ ℂ

namespace FockPre

noncomputable instance : AddCommGroup (FockPre H) := inferInstanceAs (AddCommGroup (H →₀ ℂ))
noncomputable instance : Module ℂ (FockPre H) := inferInstanceAs (Module ℂ (H →₀ ℂ))

/-- The **exponential vector** `e(f)` in the pre-Fock space. -/
noncomputable def expVec (f : H) : FockPre H := (Finsupp.single f 1 : H →₀ ℂ)

/-- The pre-inner-product (positive-semidefinite, Hermitian) structure of the symmetric Fock space. -/
noncomputable instance instCore : PreInnerProductSpace.Core ℂ (FockPre H) where
  inner φ ψ := fockInner (φ : H →₀ ℂ) (ψ : H →₀ ℂ)
  conj_inner_symm φ ψ := fockInner_conj φ ψ
  re_inner_nonneg φ := (Complex.nonneg_iff.mp (fockInner_self_nonneg φ)).1
  add_left φ ψ χ := fockInner_add_left φ ψ χ
  smul_left φ ψ r := fockInner_smul_left r φ ψ

/-- **The defining inner-product identity:** `⟪e(f), e(g)⟫ = exp⟪f,g⟫`.  This is what makes the
    exponential vectors the coherent states of the bosonic Fock space. -/
theorem inner_expVec (f g : H) :
    fockInner (expVec f : H →₀ ℂ) (expVec g : H →₀ ℂ) = Complex.exp ⟪f, g⟫_ℂ := by
  simp only [fockInner, expVec, Finsupp.sum_single_index, star_one, one_mul, mul_one,
    mul_zero, zero_mul, star_zero]

end FockPre

end QIQTH.Fock
