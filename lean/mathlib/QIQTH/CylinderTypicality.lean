/-
  P3 of the GPT-5.5-pro prize plan: the cylinder typicality (pre)measure on a directed
  projective system of finite measurement contexts — a CANONICAL finite-record covariant μ
  that BYPASSES all three operator-algebra Mathlib walls (no spectral sqrt, no unbounded
  Tomita, no continuum KMS).

  A `BornProjSystem` is a finite-dim state `ρ` together with a directed family of finite POVM
  measurement contexts and coarse-graining (refinement) maps `π` making coarse effects fiber-sums
  of fine ones.  The Born measures `μ_i(a) = Re tr(ρ E^i_a)` then form a KOLMOGOROV-CONSISTENT
  (projective) family — `μ_i = (π)_* μ_j` (`consistent`, from P1) — each a probability measure
  (`μ_total`, `μ_nonneg`), and the induced CYLINDER measure is well-defined independently of the
  stage at which an event is described (`cylinder_refine`, `cylinder_common_refine`) and covariant
  under a unitary symmetry of the system (`μ_covariant`, from P2).

  This is the honest finite/operational core of the covariant typicality measure: the premeasure on
  cylinder events is canonical and consistent.  The genuinely XL continuum step that remains is the
  Carathéodory/Kolmogorov extension to a σ-additive measure on the projective LIMIT of a continuum
  net (and pinning the net to a relativistic QFT) — explicitly NOT done here.

  Axiom-free: depends only on `propext, Classical.choice, Quot.sound`.
-/
import QIQTH.CoarseGrainNaturality
import QIQTH.BornTypicalityQuantum
import Mathlib.Order.Directed
import Mathlib.Tactic

namespace QIQTH.CylinderTypicality

open Matrix BigOperators
open scoped ComplexOrder
open QIQTH.CoarseGrainNaturality

/-- A directed projective system of finite measurement contexts on a finite-dimensional state `ρ`,
    with coarse-graining (refinement) maps `π`.  The Born measures form a Kolmogorov-consistent
    probability family (see the theorems below). -/
structure BornProjSystem where
  /-- Hilbert-space dimension. -/
  dim : ℕ
  /-- the (finite-dim) state. -/
  ρ : Matrix (Fin dim) (Fin dim) ℂ
  hρ : ρ.PosSemidef
  trρ : ρ.trace = 1
  /-- directed index of measurement stages (refinement order). -/
  Idx : Type
  [idxPre : Preorder Idx]
  [idxDir : IsDirected Idx (· ≤ ·)]
  /-- outcome set of each stage. -/
  Out : Idx → Type
  [outFin : ∀ i, Fintype (Out i)]
  [outDec : ∀ i, DecidableEq (Out i)]
  /-- the POVM effects at each stage. -/
  E : ∀ i, Out i → Matrix (Fin dim) (Fin dim) ℂ
  hE_psd : ∀ i a, (E i a).PosSemidef
  hE_povm : ∀ i, ∑ a, E i a = 1
  /-- coarse-graining map from a finer stage `j` to a coarser stage `i ≤ j`. -/
  π : ∀ ⦃i j⦄, i ≤ j → Out j → Out i
  /-- compatibility: a coarse effect is the fiber-sum of the fine effects over `π`. -/
  coarse : ∀ ⦃i j⦄ (h : i ≤ j) (a : Out i),
    E i a = ∑ b ∈ Finset.univ.filter (fun b => π h b = a), E j b

attribute [instance] BornProjSystem.idxPre BornProjSystem.idxDir BornProjSystem.outFin
  BornProjSystem.outDec

namespace BornProjSystem

variable (S : BornProjSystem)

/-- The Born measure at stage `i`: `μ_i(a) = Re tr(ρ E^i_a)`. -/
noncomputable def μ (i : S.Idx) (a : S.Out i) : ℝ := bornW S.ρ (S.E i a)

/-- **Kolmogorov consistency (projective system).**  The coarse Born measure is the pushforward of
    the fine one: `μ_i = (π)_* μ_j` for `i ≤ j`.  (Directly from P1 `born_coarse_grain`.) -/
theorem consistent {i j : S.Idx} (h : i ≤ j) (a : S.Out i) :
    S.μ i a = pushforward (S.π h) (S.μ j) a :=
  born_coarse_grain S.ρ (S.E i) (S.E j) (S.π h) (S.coarse h) a

/-- Each stage's Born measure is normalized: `∑_a μ_i(a) = 1` (uses `tr ρ = 1`). -/
theorem μ_total (i : S.Idx) : ∑ a, S.μ i a = 1 := by
  unfold μ bornW
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, S.hE_povm i, Matrix.mul_one, S.trρ,
    Complex.one_re]

/-- Each stage's Born measure is nonnegative (PSD state + PSD effects). -/
theorem μ_nonneg (i : S.Idx) (a : S.Out i) : 0 ≤ S.μ i a := by
  unfold μ bornW
  have h := QIQTH.BornTypicalityQuantum.trace_mul_nonneg S.hρ (S.hE_psd i a)
  simpa using (Complex.le_def.mp h).1

/-- The cylinder measure of an event `A ⊆ Out i` (a proposition decided at stage `i`). -/
noncomputable def cylinder (i : S.Idx) (A : Finset (S.Out i)) : ℝ := ∑ a ∈ A, S.μ i a

/-- **Cylinder measure is refinement-consistent (well-defined across stages).**  Refining stage `i`
    to a finer stage `j ≥ i` and replacing the event `A` by its preimage `π⁻¹(A)` gives the SAME
    measure — the premeasure consistency that makes the typicality measure on cylinders independent
    of the stage at which the event is described. -/
theorem cylinder_refine {i j : S.Idx} (h : i ≤ j) (A : Finset (S.Out i)) :
    S.cylinder i A = S.cylinder j (Finset.univ.filter (fun b => S.π h b ∈ A)) := by
  unfold cylinder
  simp only [S.consistent h]
  exact sum_pushforward_eq (S.π h) (S.μ j) A

/-- The whole space has cylinder measure `1` (total probability). -/
theorem cylinder_univ (i : S.Idx) : S.cylinder i Finset.univ = 1 := by
  unfold cylinder; exact S.μ_total i

/-- Cylinder measure is nonnegative. -/
theorem cylinder_nonneg (i : S.Idx) (A : Finset (S.Out i)) : 0 ≤ S.cylinder i A :=
  Finset.sum_nonneg fun a _ => S.μ_nonneg i a

/-- **Global well-definedness via directedness.**  Two cylinder events described at stages `i`, `i'`
    that have the SAME description at a common refinement `k` (which exists by `IsDirected`) carry
    the SAME measure.  Hence the typicality measure on cylinders is globally consistent, not merely
    pairwise. -/
theorem cylinder_common_refine {i i' : S.Idx} (A : Finset (S.Out i)) (A' : Finset (S.Out i'))
    {k : S.Idx} (hk : i ≤ k) (hk' : i' ≤ k)
    (hAA' : (Finset.univ.filter (fun b => S.π hk b ∈ A))
          = (Finset.univ.filter (fun b => S.π hk' b ∈ A'))) :
    S.cylinder i A = S.cylinder i' A' := by
  rw [S.cylinder_refine hk A, S.cylinder_refine hk' A', hAA']

/-- **Covariance of the typicality measure under a unitary symmetry (P2).**  If a unitary `U` fixes
    the state (`U ρ Uᴴ = ρ`) and permutes a stage's effects via an outcome bijection `σ`
    (`E^i_{σ a} = U E^i_a Uᴴ`), then the Born measure is `σ`-invariant: `μ_i(σ a) = μ_i(a)`.  This is
    the equivariance of the canonical typicality measure under the symmetries of the system. -/
theorem μ_covariant (U : Matrix (Fin S.dim) (Fin S.dim) ℂ) (hU : Uᴴ * U = 1)
    (hfix : U * S.ρ * Uᴴ = S.ρ) (i : S.Idx) (σ : S.Out i → S.Out i)
    (hσ : ∀ a, S.E i (σ a) = U * S.E i a * Uᴴ) (a : S.Out i) :
    S.μ i (σ a) = S.μ i a := by
  unfold μ
  rw [hσ a]
  have h : bornW S.ρ (U * S.E i a * Uᴴ) = bornW (U * S.ρ * Uᴴ) (U * S.E i a * Uᴴ) := by rw [hfix]
  rw [h, bornW_unitary_invariant U S.ρ (S.E i a) hU]

end BornProjSystem

end QIQTH.CylinderTypicality
