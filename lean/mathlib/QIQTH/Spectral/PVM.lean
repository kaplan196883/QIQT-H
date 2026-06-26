/-
  Phase 1 of the Tomita–Takesaki roadmap (TOMITA_TAKESAKI_ROADMAP.md):
  the KEYSTONE — projection-valued measures (PVM), scalar spectral measures,
  the simple-function spectral integral, and the *named* analytic targets
  (bounded-Borel functional calculus + the spectral theorem).

  REVISED after GPT-5.5-pro consultation, which caught a real correctness flaw
  in the first scaffold: finite additivity + multiplicativity does NOT imply
  countable additivity (counterexample: a nonprincipal ultrafilter on ℕ gives a
  {0,1}-valued finitely-additive projection-valued set function with E{n}=0 for
  every singleton yet E univ=1).  So a *finitely*-additive object is a
  projection-valued CONTENT, not a measure, and "the scalar μ_x extends to a
  genuine Measure" is FALSE from finite additivity alone.  Two layers, then:

  • `PVContent` — the finitely-additive projection-valued content (all sets).
    The clean algebraic lemmas (`inner_E_self`, `E_compl`, the scalar set
    function `mu`, the simple integral) live here and are PROVED axiom-free.

  • `ProjectionValuedMeasure` — the GENUINE PVM: laws on a `MeasurableSpace`'s
    measurable sets, with **strong-operator** countable additivity
    (`HasSum (fun n => E (A n) x) (E (⋃ n, A n) x)`, NOT operator-norm — the
    latter is false, e.g. partial sums of rank-one projections onto an ONB do
    not converge to `1` in norm).  This is the object on which the Phase-1
    analytic targets (T1–T3) are sound.

  General operator-algebra material intended for upstreaming to Mathlib; adds
  NO project axioms.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

namespace QIQTH
namespace Spectral

open scoped BigOperators ENNReal

variable {Ω : Type*} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- ── Projection-valued CONTENT (finitely additive) ────────────────────────-/

/-- A **projection-valued content**: a map `E` from subsets to bounded
    operators, each value an orthogonal projection (`IsSelfAdjoint` +
    `IsIdempotentElem`), with `E ∅ = 0`, `E univ = 1`, multiplicativity
    `E (s ∩ t) = E s * E t`, and FINITE additivity on disjoint sets.

    NB (GPT-5.5-pro): finite additivity is strictly weaker than the σ-additivity
    a measure needs — see `ProjectionValuedMeasure` below.  This `PVContent` is a
    genuine stepping stone (its algebraic lemmas are reused), not the final
    object. -/
structure PVContent (Ω H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  E : Set Ω → (H →L[ℂ] H)
  isSA : ∀ s, IsSelfAdjoint (E s)
  isIdem : ∀ s, IsIdempotentElem (E s)
  E_empty : E ∅ = 0
  E_univ : E Set.univ = 1
  E_inter : ∀ s t, E (s ∩ t) = E s * E t
  E_add : ∀ s t, Disjoint s t → E (s ∪ t) = E s + E t

namespace PVContent

variable (P : PVContent Ω H)

theorem mul_self (s : Set Ω) : P.E s * P.E s = P.E s := P.isIdem s

theorem adjoint_eq (s : Set Ω) : ContinuousLinearMap.adjoint (P.E s) = P.E s := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact P.isSA s

theorem E_apply_idem (s : Set Ω) (x : H) : P.E s (P.E s x) = P.E s x := by
  rw [← ContinuousLinearMap.mul_apply, P.mul_self]

/-- **Key projection identity:** `⟪x, E s x⟫ = ‖E s x‖²`. -/
theorem inner_E_self (s : Set Ω) (x : H) :
    inner ℂ x (P.E s x) = (‖P.E s x‖ : ℂ) ^ 2 := by
  have key : inner ℂ x (ContinuousLinearMap.adjoint (P.E s) (P.E s x))
      = inner ℂ (P.E s x) (P.E s x) :=
    ContinuousLinearMap.adjoint_inner_right (P.E s) x (P.E s x)
  rw [P.adjoint_eq, P.E_apply_idem] at key
  rw [key]; exact inner_self_eq_norm_sq_to_K _

/-- **Complementation:** `E sᶜ = 1 - E s`. -/
theorem E_compl (s : Set Ω) : P.E sᶜ = 1 - P.E s := by
  have h := P.E_add s sᶜ disjoint_compl_right
  rw [Set.union_compl_self, P.E_univ] at h
  rw [h]; abel

/-- Each `E s` is a **positive** operator (`0 ≤ E s` in the Loewner order): a
    self-adjoint idempotent is positive. -/
theorem E_nonneg (s : Set Ω) : 0 ≤ P.E s :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    ((ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
        (p := P.E s) (P.isIdem s)).mpr (P.isSA s))

/-- Each `E s` is a **subprojection of the identity** (`E s ≤ 1`): from
    `1 - E s = E sᶜ ≥ 0`. -/
theorem E_le_one (s : Set Ω) : P.E s ≤ 1 :=
  (ContinuousLinearMap.le_def _ _).mpr (by
    rw [← P.E_compl s]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp (P.E_nonneg sᶜ))

/-- The scalar set function `μ_x(s) = ‖E s x‖²` (finitely additive; a genuine
    `Measure` only on the σ-additive `ProjectionValuedMeasure`). -/
noncomputable def mu (x : H) (s : Set Ω) : ℝ := ‖P.E s x‖ ^ 2

theorem mu_nonneg (x : H) (s : Set Ω) : 0 ≤ P.mu x s := sq_nonneg _

theorem mu_empty (x : H) : P.mu x ∅ = 0 := by simp [mu, P.E_empty]

theorem mu_univ (x : H) : P.mu x Set.univ = ‖x‖ ^ 2 := by
  simp [mu, P.E_univ, ContinuousLinearMap.one_apply]

theorem mu_eq_inner (x : H) (s : Set Ω) :
    (P.mu x s : ℂ) = inner ℂ x (P.E s x) := by
  show ((‖P.E s x‖ ^ 2 : ℝ) : ℂ) = inner ℂ x (P.E s x)
  rw [P.inner_E_self]; push_cast; ring

/-- **Spectral integral of a SIMPLE function** `∑ᵢ cᵢ 𝟙_{sᵢ}`: `∑ᵢ cᵢ · E(sᵢ)`.
    The constructive core of the Borel functional calculus.  (Phase-1 refinement:
    re-home to `MeasureTheory.SimpleFunc`-style canonical partitions
    `∑_{z ∈ range f} z · E(f⁻¹{z})`, per the consultation.) -/
noncomputable def integralSimple {ι : Type*} (t : Finset ι)
    (c : ι → ℂ) (sets : ι → Set Ω) : H →L[ℂ] H :=
  ∑ i ∈ t, c i • P.E (sets i)

theorem integralSimple_union {ι : Type*} [DecidableEq ι] (t₁ t₂ : Finset ι)
    (h : Disjoint t₁ t₂) (c : ι → ℂ) (sets : ι → Set Ω) :
    P.integralSimple (t₁ ∪ t₂) c sets
      = P.integralSimple t₁ c sets + P.integralSimple t₂ c sets := by
  simp only [integralSimple, Finset.sum_union h]

/-- **The functional calculus respects the adjoint** (`∫ f̄ dE = (∫ f dE)†`), on
    simple functions: `(∑ᵢ cᵢ E sᵢ)† = ∑ᵢ c̄ᵢ E sᵢ` (each `E sᵢ` self-adjoint). -/
theorem integralSimple_adjoint {ι : Type*} (t : Finset ι) (c : ι → ℂ)
    (sets : ι → Set Ω) :
    ContinuousLinearMap.adjoint (P.integralSimple t c sets)
      = P.integralSimple t (fun i => star (c i)) sets := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  simp only [integralSimple, star_sum, star_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show star (P.E (sets i)) = P.E (sets i) from P.isSA (sets i)]

/-- **The functional calculus is multiplicative** on simple functions over a
    pairwise-disjoint family: `(∑ᵢ cᵢ E sᵢ)(∑ⱼ dⱼ E sⱼ) = ∑ᵢ cᵢdᵢ E sᵢ`.  This is
    the heart of "`f ↦ ∫ f dE` is a `*`-homomorphism": the cross terms vanish via
    `E sᵢ · E sⱼ = E(sᵢ∩sⱼ) = E ∅ = 0` for `i ≠ j`, and the diagonal collapses by
    idempotence — exactly `∫ f dE · ∫ g dE = ∫ (fg) dE` for simple `f, g`. -/
theorem integralSimple_mul {ι : Type*} (t : Finset ι) (c d : ι → ℂ)
    (sets : ι → Set Ω)
    (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (sets i) (sets j)) :
    P.integralSimple t c sets * P.integralSimple t d sets
      = P.integralSimple t (fun i => c i * d i) sets := by
  simp only [integralSimple]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mul_sum]
  have hoff : ∀ j ∈ t, j ≠ i →
      (c i • P.E (sets i)) * (d j • P.E (sets j)) = 0 := by
    intro j hj hji
    rw [smul_mul_smul, ← P.E_inter,
      (hdisj i hi j hj (Ne.symm hji)).inter_eq, P.E_empty, smul_zero]
  rw [Finset.sum_eq_single_of_mem i hi hoff, smul_mul_smul, P.mul_self]

/-- **`(∫f dE)⋆ (∫f dE) = ∫|f|² dE`** on a disjoint family — the positive
    operator `T⋆T` of a simple FC element is again a simple FC element with
    nonnegative coefficients `star(cᵢ)·cᵢ = ‖cᵢ‖²`.  Immediate from the adjoint and
    multiplicativity laws; the key step toward the norm bound `‖∫f dE‖ ≤ ‖f‖∞`. -/
theorem integralSimple_star_mul_self {ι : Type*} (t : Finset ι) (c : ι → ℂ)
    (sets : ι → Set Ω)
    (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (sets i) (sets j)) :
    star (P.integralSimple t c sets) * P.integralSimple t c sets
      = P.integralSimple t (fun i => star (c i) * c i) sets := by
  rw [ContinuousLinearMap.star_eq_adjoint, P.integralSimple_adjoint,
    P.integralSimple_mul t (fun i => star (c i)) c sets hdisj]

/-- **Finite additivity over a `Finset`:** for a pairwise-disjoint family,
    `∑ᵢ E sᵢ = E(⋃ᵢ sᵢ)`.  By induction on the index set from `E_add`.  Needed for
    the norm bound `‖∫f dE‖ ≤ ‖f‖∞` (the `∑ E sᵢ ≤ 1` step) and for `∫1 dE = 1`. -/
theorem sum_E_biUnion {ι : Type*} [DecidableEq ι] (t : Finset ι) (sets : ι → Set Ω)
    (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (sets i) (sets j)) :
    ∑ i ∈ t, P.E (sets i) = P.E (⋃ i ∈ t, sets i) := by
  classical
  revert hdisj
  induction t using Finset.induction with
  | empty => intro _; simp [P.E_empty]
  | @insert a s ha ih =>
    intro hdisj
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    have hd : Disjoint (sets a) (⋃ i ∈ s, sets i) := by
      simp only [Set.disjoint_iUnion_right]
      intro i hi
      exact hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (by rintro rfl; exact ha hi)
    rw [P.E_add _ _ hd, ih (fun i hi j hj hne =>
      hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hne)]

/-- **Unitality of the FC:** `∫ 1 dE = 1` over a covering partition
    (`⋃ᵢ sᵢ = univ`, pairwise disjoint).  `∑ᵢ 1·E sᵢ = ∑ᵢ E sᵢ = E(⋃ᵢ sᵢ) =
    E univ = 1`. -/
theorem integralSimple_one {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (sets : ι → Set Ω)
    (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (sets i) (sets j))
    (hcover : ⋃ i ∈ t, sets i = Set.univ) :
    P.integralSimple t (fun _ => 1) sets = 1 := by
  simp only [integralSimple, one_smul]
  rw [P.sum_E_biUnion t sets hdisj, hcover, P.E_univ]

/- ── Norm bound for the simple spectral integral ──────────────────────────-/

/-- **Finite Pythagoras** for a pairwise-orthogonal family of vectors:
    `‖∑ᵢ gᵢ‖² = ∑ᵢ ‖gᵢ‖²`.  (General inner-product fact, used to control the
    norm of `∑ᵢ cᵢ E sᵢ x` on a disjoint family.) -/
theorem norm_sum_sq_of_orthogonal {ι : Type*} (t : Finset ι) (g : ι → H)
    (h : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → inner ℂ (g i) (g j) = (0 : ℂ)) :
    ‖∑ i ∈ t, g i‖ ^ 2 = ∑ i ∈ t, ‖g i‖ ^ 2 := by
  have key : inner ℂ (∑ i ∈ t, g i) (∑ i ∈ t, g i)
      = ∑ i ∈ t, inner ℂ (g i) (g i) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [inner_sum, Finset.sum_eq_single i]
    · intro j hj hji; exact h i hi j hj (Ne.symm hji)
    · intro hni; exact absurd hi hni
  simp only [inner_self_eq_norm_sq_to_K] at key
  exact_mod_cast key

/-- **Two-term Pythagoras** for orthogonal vectors: `‖a+b‖² = ‖a‖²+‖b‖²`. -/
theorem norm_add_sq_orthogonal (a b : H) (h : inner ℂ a b = (0 : ℂ)) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have hba : inner ℂ b a = (0 : ℂ) := by rw [← inner_conj_symm, h, map_zero]
  have key : inner ℂ (a + b) (a + b) = inner ℂ a a + inner ℂ b b := by
    rw [inner_add_left, inner_add_right, inner_add_right, h, hba]; ring
  have e1 : inner ℂ (a + b) (a + b) = (‖a + b‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  have e2 : inner ℂ a a = (‖a‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  have e3 : inner ℂ b b = (‖b‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  have hC : (‖a + b‖ : ℂ) ^ 2 = (‖a‖ : ℂ) ^ 2 + (‖b‖ : ℂ) ^ 2 := by
    rw [← e1, key, e2, e3]
  exact_mod_cast hC

/-- For **disjoint** `s, t`, the ranges of `E s` and `E t` are orthogonal:
    `⟪E s x, E t x⟫ = 0` (since `E s · E t = E (s∩t) = E ∅ = 0`). -/
theorem E_apply_orthogonal {s t : Set Ω} (hd : Disjoint s t) (x : H) :
    inner ℂ (P.E s x) (P.E t x) = (0 : ℂ) := by
  rw [← ContinuousLinearMap.adjoint_inner_right (P.E s) x (P.E t x), P.adjoint_eq,
    ← ContinuousLinearMap.mul_apply, ← P.E_inter, hd.inter_eq, P.E_empty]
  simp

/-- Each projection is a **contraction**: `‖E s x‖ ≤ ‖x‖`.  From the orthogonal
    decomposition `x = E s x + E sᶜ x` and Pythagoras. -/
theorem norm_E_apply_le (s : Set Ω) (x : H) : ‖P.E s x‖ ≤ ‖x‖ := by
  have hx : P.E s x + P.E sᶜ x = x := by
    rw [P.E_compl]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    abel
  have h := norm_add_sq_orthogonal (P.E s x) (P.E sᶜ x)
    (P.E_apply_orthogonal disjoint_compl_right x)
  rw [hx] at h
  have hle : ‖P.E s x‖ ^ 2 ≤ ‖x‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ‖P.E sᶜ x‖]
  calc ‖P.E s x‖ = Real.sqrt (‖P.E s x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Norm bound for the simple FC** (the C\*-bound `‖∫f dE‖ ≤ ‖f‖∞`): for a
    pairwise-disjoint family with `‖cᵢ‖ ≤ M`, `‖∑ᵢ cᵢ E sᵢ‖ ≤ M`.  Proof: the
    pointwise estimate `‖T x‖² = ∑ᵢ ‖cᵢ‖² ‖E sᵢ x‖² ≤ M² ∑ᵢ ‖E sᵢ x‖²
    = M² ‖E(⋃ᵢ sᵢ) x‖² ≤ M² ‖x‖²`, both Pythagoras steps using disjointness. -/
theorem integralSimple_opNorm_le {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (c : ι → ℂ) (sets : ι → Set Ω) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ i ∈ t, ‖c i‖ ≤ M)
    (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (sets i) (sets j)) :
    ‖P.integralSimple t c sets‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM (fun x => ?_)
  have hTx : P.integralSimple t c sets x = ∑ i ∈ t, c i • (P.E (sets i) x) := by
    simp only [integralSimple, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply]
  set g : ι → H := fun i => c i • (P.E (sets i) x) with hg
  have hgorth : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → inner ℂ (g i) (g j) = (0 : ℂ) := by
    intro i hi j hj hij
    simp only [hg, inner_smul_left, inner_smul_right,
      P.E_apply_orthogonal (hdisj i hi j hj hij) x, mul_zero]
  have hpyth : ‖P.integralSimple t c sets x‖ ^ 2 = ∑ i ∈ t, ‖g i‖ ^ 2 := by
    rw [hTx]; exact norm_sum_sq_of_orthogonal t g hgorth
  have hbound : ∑ i ∈ t, ‖g i‖ ^ 2 ≤ M ^ 2 * ∑ i ∈ t, ‖P.E (sets i) x‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hgi : ‖g i‖ ^ 2 = ‖c i‖ ^ 2 * ‖P.E (sets i) x‖ ^ 2 := by
      simp [hg, norm_smul, mul_pow]
    rw [hgi]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc i hi) 2)
      (sq_nonneg _)
  have hEorth : ∀ i ∈ t, ∀ j ∈ t, i ≠ j →
      inner ℂ (P.E (sets i) x) (P.E (sets j) x) = (0 : ℂ) :=
    fun i hi j hj hij => P.E_apply_orthogonal (hdisj i hi j hj hij) x
  have hEpyth : ∑ i ∈ t, ‖P.E (sets i) x‖ ^ 2 = ‖∑ i ∈ t, P.E (sets i) x‖ ^ 2 :=
    (norm_sum_sq_of_orthogonal t (fun i => P.E (sets i) x) hEorth).symm
  have hsumE : ∑ i ∈ t, P.E (sets i) x = P.E (⋃ i ∈ t, sets i) x := by
    rw [← P.sum_E_biUnion t sets hdisj, ContinuousLinearMap.sum_apply]
  have hfin : ‖P.integralSimple t c sets x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [hpyth, mul_pow]
    refine le_trans hbound ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg M)
    rw [hEpyth, hsumE]
    exact pow_le_pow_left₀ (norm_nonneg _) (P.norm_E_apply_le _ x) 2
  have h1 : 0 ≤ M * ‖x‖ := mul_nonneg hM (norm_nonneg _)
  calc ‖P.integralSimple t c sets x‖
      = Real.sqrt (‖P.integralSimple t c sets x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((M * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hfin
    _ = M * ‖x‖ := Real.sqrt_sq h1

end PVContent

/- ── Projection-valued MEASURE (the genuine object) ───────────────────────-/

/-- A **projection-valued measure** on a measurable space `Ω` acting on `H`:
    laws on *measurable* sets, with **strong-operator** countable additivity.
    This is the corrected primitive (cf. `PVContent`): on it the scalar measures
    `μ_x` are genuine finite measures and the Phase-1 analytic targets are sound.

    `hasSum_iUnion` states σ-additivity vectorwise/strongly — `HasSum` in `H`,
    not in `H →L[ℂ] H` (operator-norm σ-additivity is false). -/
structure ProjectionValuedMeasure (Ω H : Type*) [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  E : Set Ω → (H →L[ℂ] H)
  isSA : ∀ ⦃s⦄, MeasurableSet s → IsSelfAdjoint (E s)
  isIdem : ∀ ⦃s⦄, MeasurableSet s → IsIdempotentElem (E s)
  E_empty : E ∅ = 0
  E_univ : E Set.univ = 1
  E_inter : ∀ ⦃s t⦄, MeasurableSet s → MeasurableSet t → E (s ∩ t) = E s * E t
  /-- strong-operator countable additivity over pairwise-disjoint measurable sets -/
  hasSum_iUnion : ∀ {A : ℕ → Set Ω}, (∀ n, MeasurableSet (A n)) →
    (Pairwise fun m n => Disjoint (A m) (A n)) →
    ∀ x : H, HasSum (fun n => E (A n) x) (E (⋃ n, A n) x)

namespace ProjectionValuedMeasure

variable [MeasurableSpace Ω] (P : ProjectionValuedMeasure Ω H)

theorem adjoint_eq {s : Set Ω} (hs : MeasurableSet s) :
    ContinuousLinearMap.adjoint (P.E s) = P.E s := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact P.isSA hs

theorem E_apply_idem {s : Set Ω} (hs : MeasurableSet s) (x : H) :
    P.E s (P.E s x) = P.E s x := by
  rw [← ContinuousLinearMap.mul_apply, P.isIdem hs]

/-- **The spectral projections of a PVM commute:** `E s * E t = E t * E s` for measurable `s, t` (both equal
    `E (s ∩ t)`). A fundamental property of any projection-valued measure — the observable is a commutative
    family of projections; applies in particular to the position and momentum PVMs. -/
theorem E_comm {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P.E s * P.E t = P.E t * P.E s := by
  rw [← P.E_inter hs ht, ← P.E_inter ht hs, Set.inter_comm]

/-- `⟪x, E s x⟫ = ‖E s x‖²` for measurable `s`. -/
theorem inner_E_self {s : Set Ω} (hs : MeasurableSet s) (x : H) :
    inner ℂ x (P.E s x) = (‖P.E s x‖ : ℂ) ^ 2 := by
  have key : inner ℂ x (ContinuousLinearMap.adjoint (P.E s) (P.E s x))
      = inner ℂ (P.E s x) (P.E s x) :=
    ContinuousLinearMap.adjoint_inner_right (P.E s) x (P.E s x)
  rw [P.adjoint_eq hs, P.E_apply_idem hs] at key
  rw [key]; exact inner_self_eq_norm_sq_to_K _

/-- Real form: `Re ⟪x, E s x⟫ = ‖E s x‖²`. -/
theorem re_inner_E {s : Set Ω} (hs : MeasurableSet s) (x : H) :
    (inner ℂ x (P.E s x)).re = ‖P.E s x‖ ^ 2 := by
  rw [P.inner_E_self hs]; norm_cast

/-- **The scalar spectral measure** `μ_x` — now a genuine
    `MeasureTheory.Measure Ω` (this is Phase-1 target T1, PROVED): the strong-
    operator σ-additivity of `E` (`hasSum_iUnion`) pushed through the bounded
    linear functional `⟪x,·⟫` gives σ-additivity of `s ↦ ‖E s x‖²`. -/
noncomputable def scalarMeasure (x : H) : MeasureTheory.Measure Ω :=
  MeasureTheory.Measure.ofMeasurable
    (fun s _ => ENNReal.ofReal (‖P.E s x‖ ^ 2))
    (by simp [P.E_empty])
    (fun f hf hd => by
      show ENNReal.ofReal (‖P.E (⋃ i, f i) x‖ ^ 2)
        = ∑' n, ENNReal.ofReal (‖P.E (f n) x‖ ^ 2)
      have hUm : MeasurableSet (⋃ i, f i) := MeasurableSet.iUnion hf
      have hsum := P.hasSum_iUnion hf hd x
      have hC := ContinuousLinearMap.hasSum (innerSL ℂ x) hsum
      have hRe := ContinuousLinearMap.hasSum Complex.reCLM hC
      have hR : HasSum (fun n => ‖P.E (f n) x‖ ^ 2) (‖P.E (⋃ i, f i) x‖ ^ 2) := by
        have hfun : (fun n => Complex.reCLM (innerSL ℂ x (P.E (f n) x)))
            = (fun n => ‖P.E (f n) x‖ ^ 2) := by
          funext n
          simp only [Complex.reCLM_apply]
          exact P.re_inner_E (hf n) x
        have htar : Complex.reCLM (innerSL ℂ x (P.E (⋃ i, f i) x))
            = ‖P.E (⋃ i, f i) x‖ ^ 2 := by
          simp only [Complex.reCLM_apply]; exact P.re_inner_E hUm x
        rw [hfun, htar] at hRe; exact hRe
      rw [show ‖P.E (⋃ i, f i) x‖ ^ 2 = ∑' n, ‖P.E (f n) x‖ ^ 2 from hR.tsum_eq.symm]
      exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hR.summable)

/-- Value of the scalar spectral measure on a measurable set. -/
theorem scalarMeasure_apply (x : H) {s : Set Ω} (hs : MeasurableSet s) :
    P.scalarMeasure x s = ENNReal.ofReal (‖P.E s x‖ ^ 2) :=
  MeasureTheory.Measure.ofMeasurable_apply s hs

/-- **Total mass `‖x‖²`** — `μ_x` is a finite measure summing the resolution of
    identity. -/
theorem scalarMeasure_univ (x : H) :
    P.scalarMeasure x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [P.scalarMeasure_apply x MeasurableSet.univ, P.E_univ,
    ContinuousLinearMap.one_apply]

/- ── Simple integral and the integral-against-`μ_x` bridge (T2) ────────────-/

/-- **Spectral integral of a simple function** on the genuine PVM:
    `∫(∑ᵢ cᵢ 𝟙_{sᵢ}) dE = ∑ᵢ cᵢ E sᵢ`. -/
noncomputable def integralSimple {ι : Type*} (t : Finset ι)
    (c : ι → ℂ) (sets : ι → Set Ω) : H →L[ℂ] H :=
  ∑ i ∈ t, c i • P.E (sets i)

/-- **Sesquilinear form of the simple integral** (pure linearity, no measurability
    needed): `⟪x, (∫f dE) y⟫ = ∑ᵢ cᵢ ⟪x, E sᵢ y⟫`.  This is the bilinear datum
    whose diagonal is `∫ f dμ_x` and whose polarization gives the complex measures
    `μ_{x,y}`. -/
theorem inner_integralSimple_left {ι : Type*} (t : Finset ι) (c : ι → ℂ)
    (sets : ι → Set Ω) (x y : H) :
    inner ℂ x ((P.integralSimple t c sets) y)
      = ∑ i ∈ t, c i * inner ℂ x (P.E (sets i) y) := by
  simp only [integralSimple, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inner_sum, inner_smul_right]

/-- **Diagonal real form**: for real coefficients,
    `Re ⟪x, (∫f dE) x⟫ = ∑ᵢ aᵢ ‖E sᵢ x‖²` — the μ_x-weighted sum. -/
theorem re_inner_integralSimple_self {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (sets : ι → Set Ω) (x : H) (hm : ∀ i ∈ t, MeasurableSet (sets i)) :
    (inner ℂ x ((P.integralSimple t (fun i => (a i : ℂ)) sets) x)).re
      = ∑ i ∈ t, a i * ‖P.E (sets i) x‖ ^ 2 := by
  have h : inner ℂ x ((P.integralSimple t (fun i => (a i : ℂ)) sets) x)
      = ((∑ i ∈ t, a i * ‖P.E (sets i) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [P.inner_integralSimple_left, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [P.inner_E_self (hm i hi)]; push_cast; ring
  rw [h, Complex.ofReal_re]

/-- **The simple FC integrates against `μ_x`** (genuine Lebesgue integral):
    `∫⁻ (∑ᵢ aᵢ 𝟙_{sᵢ}) dμ_x = ENNReal.ofReal (∑ᵢ aᵢ ‖E sᵢ x‖²)` for nonneg `aᵢ`. -/
theorem lintegral_indicatorSum_eq {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (sets : ι → Set Ω) (x : H) (hm : ∀ i ∈ t, MeasurableSet (sets i))
    (ha : ∀ i ∈ t, 0 ≤ a i) :
    ∫⁻ ω, (∑ i ∈ t, (sets i).indicator (fun _ => ENNReal.ofReal (a i)) ω)
        ∂(P.scalarMeasure x)
      = ENNReal.ofReal (∑ i ∈ t, a i * ‖P.E (sets i) x‖ ^ 2) := by
  have hmeas : ∀ i ∈ t,
      Measurable ((sets i).indicator (fun _ => ENNReal.ofReal (a i))) :=
    fun i hi => measurable_const.indicator (hm i hi)
  rw [MeasureTheory.lintegral_finsetSum t hmeas,
    ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [MeasureTheory.lintegral_indicator_const (hm i hi),
    P.scalarMeasure_apply x (hm i hi), ← ENNReal.ofReal_mul (ha i hi)]

/-- **`⟪x,(∫f dE)x⟫ = ∫ f dμ_x`** for a nonneg real simple function
    `f = ∑ᵢ aᵢ 𝟙_{sᵢ}` (the Phase-1 T2 quadratic-form bridge, on the *genuine*
    scalar spectral measure): the expectation of the simple effect in state `x`
    equals the Lebesgue integral of `f` against `μ_x`. -/
theorem re_inner_integralSimple_eq_lintegral {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (sets : ι → Set Ω) (x : H) (hm : ∀ i ∈ t, MeasurableSet (sets i))
    (ha : ∀ i ∈ t, 0 ≤ a i) :
    (inner ℂ x ((P.integralSimple t (fun i => (a i : ℂ)) sets) x)).re
      = (∫⁻ ω, (∑ i ∈ t, (sets i).indicator (fun _ => ENNReal.ofReal (a i)) ω)
          ∂(P.scalarMeasure x)).toReal := by
  rw [P.lintegral_indicatorSum_eq t a sets x hm ha,
    P.re_inner_integralSimple_self t a sets x hm,
    ENNReal.toReal_ofReal
      (Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)))]

/- ── Polarization: the off-diagonal complex weights `μ_{x,y}` ──────────────-/

/-- The real value of `μ_x` on a measurable set: `(μ_x s).toReal = ‖E s x‖²`. -/
theorem scalarMeasure_toReal (x : H) {s : Set Ω} (hs : MeasurableSet s) :
    (P.scalarMeasure x s).toReal = ‖P.E s x‖ ^ 2 := by
  rw [P.scalarMeasure_apply x hs, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- **Polarization of the sesquilinear form** `⟪x, E s y⟫` into diagonal quadratic
    forms `⟪z, E s z⟫`.  (No self-adjointness or measurability needed — pure
    sesquilinearity, exactly Mathlib's `inner_map_polarization` technique.) -/
theorem inner_E_polarization (s : Set Ω) (x y : H) :
    inner ℂ x (P.E s y) =
      (inner ℂ (x + y) (P.E s (x + y)) - inner ℂ (x - y) (P.E s (x - y))
        - Complex.I * inner ℂ (x + Complex.I • y) (P.E s (x + Complex.I • y))
        + Complex.I * inner ℂ (x - Complex.I • y) (P.E s (x - Complex.I • y))) / 4 := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I, ← pow_two, Complex.I_sq, mul_add, mul_sub, ← mul_assoc,
    mul_neg, neg_neg, one_mul, neg_one_mul, sub_sub]
  ring

/-- **The off-diagonal weight `μ_{x,y}(s) := ⟪x, E s y⟫` is a ℂ-combination of the
    four GENUINE scalar measures** `μ_{x±y}`, `μ_{x±iy}` (polarization).  This is
    what makes `μ_{x,y}` a complex measure: it inherits countable additivity from
    the (already-proved) `MeasureTheory.Measure`s `scalarMeasure z`. -/
theorem inner_E_eq_polarization_measures (s : Set Ω) (hs : MeasurableSet s)
    (x y : H) :
    inner ℂ x (P.E s y) =
      (((P.scalarMeasure (x + y) s).toReal : ℂ)
        - ((P.scalarMeasure (x - y) s).toReal : ℂ)
        - Complex.I * ((P.scalarMeasure (x + Complex.I • y) s).toReal : ℂ)
        + Complex.I * ((P.scalarMeasure (x - Complex.I • y) s).toReal : ℂ)) / 4 := by
  rw [P.inner_E_polarization s x y, P.inner_E_self hs, P.inner_E_self hs,
    P.inner_E_self hs, P.inner_E_self hs, P.scalarMeasure_toReal _ hs,
    P.scalarMeasure_toReal _ hs, P.scalarMeasure_toReal _ hs,
    P.scalarMeasure_toReal _ hs]
  push_cast
  ring

/-- **Capstone: the simple-integral sesquilinear form expressed entirely via the
    genuine scalar measures** (no operator inner products remain).  This realizes
    `⟪x,(∫f dE)y⟫ = ∫ f dμ_{x,y}` for simple `f` with `μ_{x,y}` the polarization
    complex measure — the off-diagonal companion of `re_inner_integralSimple_eq_lintegral`. -/
theorem inner_integralSimple_eq_polarization {ι : Type*} (t : Finset ι) (c : ι → ℂ)
    (sets : ι → Set Ω) (x y : H) (hm : ∀ i ∈ t, MeasurableSet (sets i)) :
    inner ℂ x ((P.integralSimple t c sets) y) =
      ∑ i ∈ t, c i *
        ((((P.scalarMeasure (x + y) (sets i)).toReal : ℂ)
          - ((P.scalarMeasure (x - y) (sets i)).toReal : ℂ)
          - Complex.I * ((P.scalarMeasure (x + Complex.I • y) (sets i)).toReal : ℂ)
          + Complex.I * ((P.scalarMeasure (x - Complex.I • y) (sets i)).toReal : ℂ)) / 4) := by
  rw [P.inner_integralSimple_left]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [P.inner_E_eq_polarization_measures (sets i) (hm i hi)]

/- ── Foundations for the simple→bounded-Borel extension (Route A, Riesz) ───-/

/-- `μ_x` is a **finite** measure (total mass `‖x‖²`) — so every bounded
    measurable function is Bochner-integrable against it.  Prerequisite for the
    integral functional `f ↦ ∫ f dμ_x` of the bounded-Borel FC. -/
instance instIsFiniteMeasure_scalarMeasure (x : H) :
    MeasureTheory.IsFiniteMeasure (P.scalarMeasure x) :=
  ⟨by rw [P.scalarMeasure_univ x]; exact ENNReal.ofReal_lt_top⟩

/-- **Parallelogram identity for the scalar measures** (real form):
    `(μ_{x+y} + μ_{x−y})(s) = 2 μ_x(s) + 2 μ_y(s)`.  This is the seed of the
    sesquilinearity of the form `(x,y) ↦ ∫ f dμ_{x,y}` underlying the
    bounded-Borel functional calculus (Route A): integrating it against a
    bounded `f` gives the parallelogram law for the diagonal functional
    `D_f(x) := ∫ f dμ_x`, whence its polarization is sesquilinear. -/
theorem scalarMeasure_toReal_parallelogram (x y : H) {s : Set Ω}
    (hs : MeasurableSet s) :
    (P.scalarMeasure (x + y) s).toReal + (P.scalarMeasure (x - y) s).toReal
      = 2 * (P.scalarMeasure x s).toReal + 2 * (P.scalarMeasure y s).toReal := by
  rw [P.scalarMeasure_toReal _ hs, P.scalarMeasure_toReal _ hs,
    P.scalarMeasure_toReal _ hs, P.scalarMeasure_toReal _ hs, map_add, map_sub]
  have h := parallelogram_law_with_norm (𝕜 := ℂ) (P.E s x) (P.E s y)
  linarith [h]

/-- **Scaling at the measure level:** `μ_{c·x} = ‖c‖² · μ_x`.  (`E s (c•x) = c•E s x`
    so `‖E s (c•x)‖² = ‖c‖²‖E s x‖²`.) -/
theorem scalarMeasure_smul (c : ℂ) (x : H) :
    P.scalarMeasure (c • x) = ENNReal.ofReal (‖c‖ ^ 2) • P.scalarMeasure x := by
  refine MeasureTheory.Measure.ext (fun s hs => ?_)
  rw [MeasureTheory.Measure.smul_apply, smul_eq_mul, P.scalarMeasure_apply _ hs,
    P.scalarMeasure_apply _ hs, map_smul, norm_smul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]

/-- **Parallelogram at the measure level:** `μ_{x+y} + μ_{x−y} = 2·μ_x + 2·μ_y`. -/
theorem scalarMeasure_parallelogram_measure (x y : H) :
    P.scalarMeasure (x + y) + P.scalarMeasure (x - y)
      = (2 : ℝ≥0∞) • P.scalarMeasure x + (2 : ℝ≥0∞) • P.scalarMeasure y := by
  refine MeasureTheory.Measure.ext (fun s hs => ?_)
  have hreal : ‖P.E s (x + y)‖ ^ 2 + ‖P.E s (x - y)‖ ^ 2
      = (‖P.E s x‖ ^ 2 + ‖P.E s x‖ ^ 2) + (‖P.E s y‖ ^ 2 + ‖P.E s y‖ ^ 2) := by
    rw [map_add, map_sub]
    have h := parallelogram_law_with_norm (𝕜 := ℂ) (P.E s x) (P.E s y)
    linarith [h]
  simp only [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply, smul_eq_mul]
  rw [P.scalarMeasure_apply _ hs, P.scalarMeasure_apply _ hs,
    P.scalarMeasure_apply _ hs, P.scalarMeasure_apply _ hs, two_mul, two_mul,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity), hreal]

/-- A bounded measurable function is **Bochner-integrable** against the finite
    measure `μ_x`. -/
theorem integrable_boundedMeasurable {f : Ω → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x : H) :
    MeasureTheory.Integrable f (P.scalarMeasure x) :=
  (MeasureTheory.integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-- **The diagonal functional** `D_f(x) := ∫ f dμ_x` (E2a of the bounded-Borel FC
    sub-plan).  Its homogeneity `D_f(c·x) = ‖c‖² D_f(x)` and parallelogram law are
    what make the polarized form `B_f(x,y)` sesquilinear. -/
noncomputable def diagInt (f : Ω → ℂ) (x : H) : ℂ :=
  ∫ ω, f ω ∂(P.scalarMeasure x)

/-- **Homogeneity** of the diagonal functional: `D_f(c·x) = ‖c‖² D_f(x)`. -/
theorem diagInt_smul (f : Ω → ℂ) (c : ℂ) (x : H) :
    P.diagInt f (c • x) = ((‖c‖ ^ 2 : ℝ) : ℂ) * P.diagInt f x := by
  simp only [diagInt]
  rw [P.scalarMeasure_smul, MeasureTheory.integral_smul_measure,
    ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]

/-- **Parallelogram law** for the diagonal functional:
    `D_f(x+y) + D_f(x−y) = 2 D_f(x) + 2 D_f(y)`. -/
theorem diagInt_parallelogram {f : Ω → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x y : H) :
    P.diagInt f (x + y) + P.diagInt f (x - y)
      = 2 * P.diagInt f x + 2 * P.diagInt f y := by
  have hint : ∀ z, MeasureTheory.Integrable f (P.scalarMeasure z) :=
    fun z => P.integrable_boundedMeasurable hf hC z
  simp only [diagInt]
  rw [← MeasureTheory.integral_add_measure (hint (x + y)) (hint (x - y)),
    P.scalarMeasure_parallelogram_measure x y,
    MeasureTheory.integral_add_measure
      ((hint x).smul_measure (by norm_num)) ((hint y).smul_measure (by norm_num)),
    MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]

/-- **E2b — the polarized sesquilinear form** `B_f(x,y)`, mirroring Mathlib's
    Fréchet–von Neumann–Jordan `inner_` but with the quadratic functional
    `D_f = diagInt f` in place of `‖·‖²`.  Its diagonal is `D_f` and (once shown
    sesquilinear + bounded) it represents `∫ f dE` via `continuousLinearMapOfBilin`. -/
noncomputable def bilinDiag (f : Ω → ℂ) (x y : H) : ℂ :=
  4⁻¹ * (P.diagInt f (x + y) - P.diagInt f (x - y)
    + Complex.I * P.diagInt f (Complex.I • x + y)
    - Complex.I * P.diagInt f (Complex.I • x - y))

/-- **Additivity in the first slot** of `B_f` — the Jordan–von Neumann core,
    ported from `InnerProductSpace.OfNorm.add_left` (no `algebraMap` casting needed
    since `D_f` is already ℂ-valued), using `diagInt_parallelogram`. -/
theorem bilinDiag_add_left {f : Ω → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x y z : H) :
    P.bilinDiag f (x + y) z = P.bilinDiag f x z + P.bilinDiag f y z := by
  simp only [bilinDiag]
  have h1 := P.diagInt_parallelogram hf hC (x + y + z) (x - z)
  have h2 := P.diagInt_parallelogram hf hC (x + y - z) (x + z)
  have h3 := P.diagInt_parallelogram hf hC (y + z) z
  have h4 := P.diagInt_parallelogram hf hC (y - z) z
  have h5 := P.diagInt_parallelogram hf hC (Complex.I • (x + y) + z) (Complex.I • x - z)
  have h6 := P.diagInt_parallelogram hf hC (Complex.I • (x + y) - z) (Complex.I • x + z)
  have h7 := P.diagInt_parallelogram hf hC (Complex.I • y + z) z
  have h8 := P.diagInt_parallelogram hf hC (Complex.I • y - z) z
  simp only [smul_add] at *
  abel_nf at *
  linear_combination (-h1 + h2 + h3 - h4 + Complex.I * (-h5 + h6 + h7 - h8)) / 8

/-- `D_f` is invariant under **unit-modulus scaling**: `D_f(c·x) = D_f(x)` when
    `‖c‖ = 1` (special case of `diagInt_smul`). -/
theorem diagInt_unit_smul (f : Ω → ℂ) {c : ℂ} (hc : ‖c‖ = 1) (x : H) :
    P.diagInt f (c • x) = P.diagInt f x := by
  rw [P.diagInt_smul, hc, one_pow, Complex.ofReal_one, one_mul]

/-- `D_f` is **even**: `D_f(-x) = D_f(x)`. -/
theorem diagInt_neg (f : Ω → ℂ) (x : H) : P.diagInt f (-x) = P.diagInt f x := by
  rw [← neg_one_smul ℂ x]; exact P.diagInt_unit_smul f (by simp) x

/-- **Conjugation** passes through `D_f`: `conj (D_f x) = D_{f̄}(x)` (the scalar
    measure `μ_x` is real, so `conj ∫ f = ∫ conj f`). -/
theorem diagInt_conj (f : Ω → ℂ) (x : H) :
    (starRingEnd ℂ) (P.diagInt f x) = P.diagInt (fun ω => (starRingEnd ℂ) (f ω)) x := by
  simp only [diagInt]; exact integral_conj.symm

/-- `D_f(i·y + x) = D_f(i·x − y)` (unit-scaling invariance + evenness; used to
    establish the conjugate-symmetry of `B_f`). -/
theorem diagInt_I_left (f : Ω → ℂ) (x y : H) :
    P.diagInt f (Complex.I • y + x) = P.diagInt f (Complex.I • x - y) := by
  have hv : Complex.I • y + x = Complex.I • (y - Complex.I • x) := by
    rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]; abel
  have hu : P.diagInt f (Complex.I • (y - Complex.I • x)) = P.diagInt f (y - Complex.I • x) :=
    P.diagInt_unit_smul f Complex.norm_I _
  have hn : y - Complex.I • x = -(Complex.I • x - y) := by abel
  rw [hv, hu, hn, P.diagInt_neg]

/-- `D_f(i·y − x) = D_f(i·x + y)` (companion of `diagInt_I_left`). -/
theorem diagInt_I_right (f : Ω → ℂ) (x y : H) :
    P.diagInt f (Complex.I • y - x) = P.diagInt f (Complex.I • x + y) := by
  have hv : Complex.I • y - x = Complex.I • (y + Complex.I • x) := by
    rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]; abel
  have hu : P.diagInt f (Complex.I • (y + Complex.I • x)) = P.diagInt f (y + Complex.I • x) :=
    P.diagInt_unit_smul f Complex.norm_I _
  have hc2 : y + Complex.I • x = Complex.I • x + y := by abel
  rw [hv, hu, hc2]

/-- **Conjugate-symmetry of the polarized form** for complex `f`:
    `conj (B_f(y,x)) = B_{f̄}(x,y)` where `f̄ = conj ∘ f`.  (For real `f` this is the
    usual `⟪x,y⟫ = conj⟪y,x⟫`.)  This transfers slot-1 additivity to slot 2. -/
theorem bilinDiag_conj_symm (f : Ω → ℂ) (x y : H) :
    (starRingEnd ℂ) (P.bilinDiag f y x)
      = P.bilinDiag (fun ω => (starRingEnd ℂ) (f ω)) x y := by
  simp only [bilinDiag, map_mul, map_sub, map_add, map_inv₀, map_ofNat, Complex.conj_I,
    P.diagInt_conj]
  rw [show y + x = x + y from add_comm y x, show y - x = -(x - y) from by abel,
    P.diagInt_neg, P.diagInt_I_left (fun ω => (starRingEnd ℂ) (f ω)) x y,
    P.diagInt_I_right (fun ω => (starRingEnd ℂ) (f ω)) x y]
  ring

/-- **Additivity in the second slot** of `B_f`, from slot-1 additivity (of `f̄`)
    through `bilinDiag_conj_symm`. -/
theorem bilinDiag_add_right {f : Ω → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x y z : H) :
    P.bilinDiag f x (y + z) = P.bilinDiag f x y + P.bilinDiag f x z := by
  have hfc : Measurable (fun ω => (starRingEnd ℂ) (f ω)) :=
    RCLike.continuous_conj.measurable.comp hf
  have hCc : ∀ ω, ‖(starRingEnd ℂ) (f ω)‖ ≤ C := fun ω => by
    rw [RCLike.norm_conj]; exact hC ω
  have key : ∀ w : H, P.bilinDiag f x w
      = (starRingEnd ℂ) (P.bilinDiag (fun ω => (starRingEnd ℂ) (f ω)) w x) := by
    intro w
    rw [P.bilinDiag_conj_symm]
    simp only [Complex.conj_conj]
  rw [key (y + z), key y, key z, P.bilinDiag_add_left hfc hCc y z x, map_add]

/-- **`i`-scaling in the first slot** (the `I_prop` of Jordan–von Neumann, pure
    algebra via `i² = −1` and evenness of `D_f`): `B_f(i·x, y) = conj(i)·B_f(x,y)`. -/
theorem bilinDiag_I_smul_left (f : Ω → ℂ) (x y : H) :
    P.bilinDiag f (Complex.I • x) y
      = (starRingEnd ℂ) Complex.I * P.bilinDiag f x y := by
  simp only [bilinDiag, Complex.conj_I, smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [show -x + y = -(x - y) from by abel, show -x - y = -(x + y) from by abel,
    P.diagInt_neg, P.diagInt_neg]
  linear_combination (P.diagInt f (Complex.I • x + y)
    - P.diagInt f (Complex.I • x - y)) / 4 * Complex.I_sq

/-- **Odd measure identity** (the continuity-free key to real homogeneity): for
    `r ≥ 0`, `μ_{r·x+y} + r·μ_{x−y} = μ_{r·x−y} + r·μ_{x+y}` (both sides equal
    `r²‖Ex‖² + ‖Ey‖² + r‖Ex‖² + r‖Ey‖²` at each set; all positive measures, no
    signed-measure machinery). -/
theorem scalarMeasure_odd_measure (x y : H) {r : ℝ} (hr : 0 ≤ r) :
    P.scalarMeasure ((r : ℂ) • x + y) + ENNReal.ofReal r • P.scalarMeasure (x - y)
      = P.scalarMeasure ((r : ℂ) • x - y) + ENNReal.ofReal r • P.scalarMeasure (x + y) := by
  refine MeasureTheory.Measure.ext (fun s hs => ?_)
  have hreal : ‖P.E s ((r : ℂ) • x + y)‖ ^ 2 + r * ‖P.E s (x - y)‖ ^ 2
      = ‖P.E s ((r : ℂ) • x - y)‖ ^ 2 + r * ‖P.E s (x + y)‖ ^ 2 := by
    have e : ∀ u : H, ((‖u‖ ^ 2 : ℝ) : ℂ) = inner ℂ u u := fun u => by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have key : ((‖P.E s ((r : ℂ) • x + y)‖ ^ 2 + r * ‖P.E s (x - y)‖ ^ 2 : ℝ) : ℂ)
        = ((‖P.E s ((r : ℂ) • x - y)‖ ^ 2 + r * ‖P.E s (x + y)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_add, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul,
        e (P.E s ((r : ℂ) • x + y)), e (P.E s (x - y)), e (P.E s ((r : ℂ) • x - y)),
        e (P.E s (x + y))]
      simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
        inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
      ring
    exact_mod_cast key
  simp only [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply, smul_eq_mul]
  rw [P.scalarMeasure_apply _ hs, P.scalarMeasure_apply _ hs, P.scalarMeasure_apply _ hs,
    P.scalarMeasure_apply _ hs, ← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_mul hr,
    ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hr (sq_nonneg _)),
    ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hr (sq_nonneg _)), hreal]

/-- **Odd functional identity:** `D_f(r·x+y) − D_f(r·x−y) = r(D_f(x+y) − D_f(x−y))`
    (here as `D_f(r·x+y) + r·D_f(x−y) = D_f(r·x−y) + r·D_f(x+y)`), `r ≥ 0`.
    Integrates `scalarMeasure_odd_measure`; the seed of real homogeneity of `B_f`. -/
theorem diagInt_odd {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C)
    (x y : H) {r : ℝ} (hr : 0 ≤ r) :
    P.diagInt f ((r : ℂ) • x + y) + (r : ℂ) * P.diagInt f (x - y)
      = P.diagInt f ((r : ℂ) • x - y) + (r : ℂ) * P.diagInt f (x + y) := by
  have hint : ∀ z, MeasureTheory.Integrable f (P.scalarMeasure z) :=
    fun z => P.integrable_boundedMeasurable hf hC z
  simp only [diagInt]
  have hsmul : ∀ w : H, (r : ℂ) * ∫ ω, f ω ∂(P.scalarMeasure w)
      = ∫ ω, f ω ∂(ENNReal.ofReal r • P.scalarMeasure w) := fun w => by
    rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hr, Complex.real_smul]
  rw [hsmul (x - y), hsmul (x + y),
    ← MeasureTheory.integral_add_measure (hint _) ((hint _).smul_measure (by simp)),
    ← MeasureTheory.integral_add_measure (hint _) ((hint _).smul_measure (by simp)),
    P.scalarMeasure_odd_measure x y hr]

/-- **Real homogeneity in the first slot, `r ≥ 0`:** `B_f(r·x, y) = r·B_f(x,y)`.
    Both the `x` and the `i·x` odd identities feed in; no continuity used. -/
theorem bilinDiag_real_smul_left_nonneg {f : Ω → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x y : H) {r : ℝ} (hr : 0 ≤ r) :
    P.bilinDiag f ((r : ℂ) • x) y = (r : ℂ) * P.bilinDiag f x y := by
  have hodd1 := P.diagInt_odd hf hC x y hr
  have hodd2 := P.diagInt_odd hf hC (Complex.I • x) y hr
  have hsc : Complex.I • ((r : ℂ) • x) = (r : ℂ) • (Complex.I • x) := smul_comm _ _ _
  simp only [bilinDiag, hsc]
  linear_combination (hodd1 + Complex.I * hodd2) / 4

/-- `B_f(0, y) = 0`. -/
theorem bilinDiag_zero_left (f : Ω → ℂ) (y : H) : P.bilinDiag f 0 y = 0 := by
  simp only [bilinDiag, zero_add, zero_sub, smul_zero, P.diagInt_neg]
  ring

/-- `B_f(-x, y) = -B_f(x, y)` (from additivity in the first slot). -/
theorem bilinDiag_neg_left {f : Ω → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x y : H) :
    P.bilinDiag f (-x) y = -P.bilinDiag f x y := by
  have h := P.bilinDiag_add_left hf hC x (-x) y
  rw [add_neg_cancel, P.bilinDiag_zero_left] at h
  linear_combination -h

/-- **Real homogeneity in the first slot (all `r : ℝ`):** `B_f(r·x,y) = r·B_f(x,y)`. -/
theorem bilinDiag_real_smul_left {f : Ω → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x y : H) (r : ℝ) :
    P.bilinDiag f ((r : ℂ) • x) y = (r : ℂ) * P.bilinDiag f x y := by
  rcases le_total 0 r with hr | hr
  · exact P.bilinDiag_real_smul_left_nonneg hf hC x y hr
  · have hnr : (0 : ℝ) ≤ -r := by linarith
    have h := P.bilinDiag_real_smul_left_nonneg hf hC x y hnr
    have hcoe : (r : ℂ) • x = -(((-r : ℝ) : ℂ) • x) := by
      push_cast; rw [neg_smul, neg_neg]
    rw [hcoe, P.bilinDiag_neg_left hf hC, h]; push_cast; ring

/-- **Conjugate-linearity in the first slot (full `ℂ`):**
    `B_f(c·x, y) = conj(c)·B_f(x,y)` — combines real homogeneity, `i`-scaling and
    additivity via `c = c.re + c.im·i`.  This is the sesquilinear half (with
    `bilinDiag_conj_symm` giving linearity in the second slot). -/
theorem bilinDiag_smul_left {f : Ω → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) (c : ℂ) (x y : H) :
    P.bilinDiag f (c • x) y = (starRingEnd ℂ) c * P.bilinDiag f x y := by
  have hdecomp : c • x = (c.re : ℂ) • x + (c.im : ℂ) • (Complex.I • x) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  have hconj : (starRingEnd ℂ) c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hdecomp, P.bilinDiag_add_left hf hC, P.bilinDiag_real_smul_left hf hC,
    P.bilinDiag_real_smul_left hf hC, P.bilinDiag_I_smul_left, Complex.conj_I, hconj]
  ring

/-- **Diagonal bound** `‖D_f x‖ ≤ C‖x‖²` from `‖f‖ ≤ C` and `μ_x(univ) = ‖x‖²`. -/
theorem diagInt_norm_le {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x : H) : ‖P.diagInt f x‖ ≤ C * ‖x‖ ^ 2 := by
  have hint : MeasureTheory.Integrable f (P.scalarMeasure x) :=
    P.integrable_boundedMeasurable hf hC x
  calc ‖P.diagInt f x‖
      ≤ ∫ ω, ‖f ω‖ ∂(P.scalarMeasure x) := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ _ω, C ∂(P.scalarMeasure x) :=
        MeasureTheory.integral_mono hint.norm (MeasureTheory.integrable_const C)
          (fun ω => hC ω)
    _ = C * ‖x‖ ^ 2 := by
        rw [MeasureTheory.integral_const, MeasureTheory.measureReal_def, P.scalarMeasure_univ,
          ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_comm]

/-- **Linearity in the second slot:** `B_f(x, c·y) = c·B_f(x,y)` (from
    conjugate-symmetry + first-slot conjugate-linearity of `f̄`). -/
theorem bilinDiag_smul_right {f : Ω → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) (c : ℂ) (x y : H) :
    P.bilinDiag f x (c • y) = c * P.bilinDiag f x y := by
  have hfc : Measurable (fun ω => (starRingEnd ℂ) (f ω)) :=
    RCLike.continuous_conj.measurable.comp hf
  have hCc : ∀ ω, ‖(starRingEnd ℂ) (f ω)‖ ≤ C := fun ω => by rw [RCLike.norm_conj]; exact hC ω
  have key : ∀ w : H, P.bilinDiag f x w
      = (starRingEnd ℂ) (P.bilinDiag (fun ω => (starRingEnd ℂ) (f ω)) w x) := by
    intro w; rw [P.bilinDiag_conj_symm]; simp only [Complex.conj_conj]
  rw [key (c • y), P.bilinDiag_smul_left hfc hCc c y x, map_mul, Complex.conj_conj, key y]

/-- `B_f(x, 0) = 0`. -/
theorem bilinDiag_zero_right (f : Ω → ℂ) (x : H) : P.bilinDiag f x 0 = 0 := by
  simp only [bilinDiag, add_zero, sub_zero]; ring

/-- **Quadratic bound** `‖B_f(x,y)‖ ≤ C(‖x‖²+‖y‖²)` (polarization + diagonal bound
    + two parallelogram laws). -/
theorem bilinDiag_norm_le_add {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x y : H) :
    ‖P.bilinDiag f x y‖ ≤ C * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hb : ∀ z, ‖P.diagInt f z‖ ≤ C * ‖z‖ ^ 2 := fun z => P.diagInt_norm_le hf hC0 hC z
  have hpar1 : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
    parallelogram_law_with_norm (𝕜 := ℂ) x y
  have hpar2 : ‖Complex.I • x + y‖ ^ 2 + ‖Complex.I • x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    rw [parallelogram_law_with_norm (𝕜 := ℂ) (Complex.I • x) y, norm_smul, Complex.norm_I, one_mul]
  set a := P.diagInt f (x + y)
  set b := P.diagInt f (x - y)
  set c := P.diagInt f (Complex.I • x + y)
  set d := P.diagInt f (Complex.I • x - y)
  have htri : ‖a - b + Complex.I * c - Complex.I * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc ‖a - b + Complex.I * c - Complex.I * d‖
        ≤ ‖a - b + Complex.I * c‖ + ‖Complex.I * d‖ := norm_sub_le _ _
      _ ≤ ‖a - b‖ + ‖Complex.I * c‖ + ‖Complex.I * d‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖Complex.I * c‖ + ‖Complex.I * d‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
  rw [bilinDiag, norm_mul, show ‖(4 : ℂ)⁻¹‖ = 4⁻¹ from by norm_num]
  have hsum : ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ ≤ C * (4 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by
    have := hb (x + y); have := hb (x - y); have := hb (Complex.I • x + y)
    have := hb (Complex.I • x - y)
    nlinarith [hb (x + y), hb (x - y), hb (Complex.I • x + y), hb (Complex.I • x - y),
      hpar1, hpar2]
  calc 4⁻¹ * ‖a - b + Complex.I * c - Complex.I * d‖
      ≤ 4⁻¹ * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by gcongr
    _ ≤ 4⁻¹ * (C * (4 * (‖x‖ ^ 2 + ‖y‖ ^ 2))) := by gcongr
    _ = C * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by ring

/-- **Product (bilinear) bound** `‖B_f(x,y)‖ ≤ 2C·‖x‖·‖y‖` — the bound feeding
    `LinearMap.mkContinuous₂`.  Proof: normalize to unit vectors and apply the
    quadratic bound (giving `‖u‖²+‖v‖² = 2`). -/
theorem bilinDiag_norm_le {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x y : H) :
    ‖P.bilinDiag f x y‖ ≤ 2 * C * ‖x‖ * ‖y‖ := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx, P.bilinDiag_zero_left]
  rcases eq_or_ne y 0 with hy | hy
  · simp [hy, P.bilinDiag_zero_right]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set u := (‖x‖⁻¹ : ℂ) • x with hu
  set v := (‖y‖⁻¹ : ℂ) • y with hv
  have hxu : x = (‖x‖ : ℂ) • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hxpos.ne'), one_smul]
  have hyv : y = (‖y‖ : ℂ) • v := by
    rw [hv, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hypos.ne'), one_smul]
  have hofr : ∀ z : H, ‖(‖z‖ : ℂ)‖ = ‖z‖ := fun z => by simp
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, hofr, inv_mul_cancel₀ hxpos.ne']
  have hnv : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, hofr, inv_mul_cancel₀ hypos.ne']
  have hdecomp : P.bilinDiag f x y = (‖x‖ : ℂ) * ((‖y‖ : ℂ) * P.bilinDiag f u v) := by
    conv_lhs => rw [hxu, hyv]
    rw [P.bilinDiag_smul_left hf hC, P.bilinDiag_smul_right hf hC, Complex.conj_ofReal]
  rw [hdecomp, norm_mul, norm_mul, hofr, hofr]
  have hquad : ‖P.bilinDiag f u v‖ ≤ C * (‖u‖ ^ 2 + ‖v‖ ^ 2) :=
    P.bilinDiag_norm_le_add hf hC0 hC u v
  rw [hnu, hnv] at hquad
  have hq2 : ‖P.bilinDiag f u v‖ ≤ 2 * C := by nlinarith [hquad]
  calc ‖x‖ * (‖y‖ * ‖P.bilinDiag f u v‖)
      ≤ ‖x‖ * (‖y‖ * (2 * C)) := by gcongr
    _ = 2 * C * ‖x‖ * ‖y‖ := by ring

/-- The polarized form as a **bundled sesquilinear `LinearMap`** `H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ`
    (conjugate-linear in the first slot, linear in the second), mirroring `innerₛₗ`. -/
noncomputable def bilinDiagₗ {f : Ω → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => P.bilinDiag f x y)
    (fun x₁ x₂ y => P.bilinDiag_add_left hf hC x₁ x₂ y)
    (fun c x y => by rw [smul_eq_mul]; exact P.bilinDiag_smul_left hf hC c x y)
    (fun x y₁ y₂ => P.bilinDiag_add_right hf hC x y₁ y₂)
    (fun c x y => by rw [RingHom.id_apply, smul_eq_mul]; exact P.bilinDiag_smul_right hf hC c x y)

/-- **The bounded-Borel functional calculus `∫ f dE`** (E2c), defined via the Riesz
    representation `continuousLinearMapOfBilin` of the bounded sesquilinear form
    `B_f`.  Requires `0 ≤ C` and `‖f‖ ≤ C`. -/
noncomputable def intBorel {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin
    (LinearMap.mkContinuous₂ (P.bilinDiagₗ hf hC) (2 * C)
      (fun x y => P.bilinDiag_norm_le hf hC0 hC x y))

/-- **Defining property of `∫ f dE`:** `⟪(∫f dE) x, y⟫ = B_f(x,y)` — the
    sesquilinear form `B_f(x,y) = ∫ f dμ_{x,y}` is realized by the operator. -/
theorem inner_intBorel {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x y : H) :
    inner ℂ ((P.intBorel hf hC0 hC) x) y = P.bilinDiag f x y := by
  rw [intBorel, InnerProductSpace.continuousLinearMapOfBilin_apply,
    LinearMap.mkContinuous₂_apply]
  rfl

/-- **Operator norm bound:** `‖∫f dE‖ ≤ 2C`.  From `‖T x‖² = Re B_f(x, T x) ≤
    ‖B_f(x, T x)‖ ≤ 2C‖x‖‖T x‖`. -/
theorem intBorel_norm_le {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) : ‖P.intBorel hf hC0 hC‖ ≤ 2 * C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun x => ?_)
  set T := P.intBorel hf hC0 hC with hT
  have hkey : ‖T x‖ ^ 2 ≤ 2 * C * ‖x‖ * ‖T x‖ := by
    have h1 : (P.bilinDiag f x (T x)).re = ‖T x‖ ^ 2 := by
      rw [hT, ← P.inner_intBorel hf hC0 hC x, inner_self_eq_norm_sq_to_K]; norm_cast
    rw [← h1]
    calc (P.bilinDiag f x (T x)).re ≤ ‖P.bilinDiag f x (T x)‖ := Complex.re_le_norm _
      _ ≤ 2 * C * ‖x‖ * ‖T x‖ := P.bilinDiag_norm_le hf hC0 hC x (T x)
  rcases (norm_nonneg (T x)).eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg (mul_nonneg (by norm_num) hC0) (norm_nonneg x)
  · rw [pow_two] at hkey
    exact le_of_mul_le_mul_right hkey h0

/- ── Orientation check + correctly-oriented FC (E2c follow-up) ─────────────-/

/-- `D_f` of a CONSTANT function: `∫ c dμ_z = ‖z‖²·c`. -/
theorem diagInt_const (c : ℂ) (z : H) :
    P.diagInt (fun _ => c) z = (‖z‖ : ℂ) ^ 2 * c := by
  rw [diagInt, MeasureTheory.integral_const, MeasureTheory.measureReal_def,
    P.scalarMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  push_cast; ring

/-- `B_f` of a CONSTANT function is `c·⟪x,y⟫` (polarization of `‖·‖²` = `⟪x,y⟫`).
    Note this is conjugate-linear in `x` — confirming that the Riesz operator
    `intBorel` is the *conjugated* calculus (see `intBorel_const`). -/
theorem bilinDiag_const (c : ℂ) (x y : H) :
    P.bilinDiag (fun _ => c) x y = c * inner ℂ x y := by
  have e : ∀ u : H, (‖u‖ : ℂ) ^ 2 = inner ℂ u u :=
    fun u => (inner_self_eq_norm_sq_to_K u).symm
  have hbr : (‖x + y‖ : ℂ) ^ 2 - (‖x - y‖ : ℂ) ^ 2
      + Complex.I * (‖Complex.I • x + y‖ : ℂ) ^ 2
      - Complex.I * (‖Complex.I • x - y‖ : ℂ) ^ 2 = 4 * inner ℂ x y := by
    rw [e, e, e, e]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, Complex.conj_I]
    linear_combination (2 * (inner ℂ y x - inner ℂ x y)) * Complex.I_sq
  rw [bilinDiag, P.diagInt_const, P.diagInt_const, P.diagInt_const, P.diagInt_const]
  linear_combination (4⁻¹ * c) * hbr

/-- **Orientation diagnosis (GPT-5.5-pro check):** the Riesz operator satisfies
    `intBorel (const c) = conj(c)·1`, NOT `c·1` — because `⟪(intBorel) x, y⟫ = B_f(x,y)`
    puts the operator on the *first* (conjugate-linear) inner slot.  Hence the
    correctly-oriented bounded-Borel calculus is the ADJOINT, `boundedFC` below. -/
theorem intBorel_const (c : ℂ) :
    P.intBorel (f := fun _ => c) measurable_const (norm_nonneg c) (fun _ => le_rfl)
      = (starRingEnd ℂ) c • (1 : H →L[ℂ] H) := by
  refine ContinuousLinearMap.ext (fun y => ?_)
  refine ext_inner_right ℂ (fun x => ?_)
  rw [P.inner_intBorel, P.bilinDiag_const, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, inner_smul_left, starRingEnd_self_apply]

/-- **The correctly-oriented bounded-Borel functional calculus** `Φ(f) := (∫f dE)*`
    (the adjoint of the Riesz operator), so that `⟪x, Φ(f) y⟫ = B_f(x,y) = ∫ f dμ_{x,y}`
    with the operator on the SECOND slot — the standard convention. -/
noncomputable def boundedFC {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint (P.intBorel hf hC0 hC)

/-- Defining property of the oriented FC: `⟪x, Φ(f) y⟫ = B_f(x,y)`. -/
theorem inner_boundedFC {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) (x y : H) :
    inner ℂ x ((P.boundedFC hf hC0 hC) y) = P.bilinDiag f x y := by
  rw [boundedFC, ContinuousLinearMap.adjoint_inner_right, P.inner_intBorel]

/-- **Unitality / constant rule:** `Φ(const c) = c·1`.  In particular `Φ(1) = 1`,
    so the oriented calculus is unital (a genuine functional calculus). -/
theorem boundedFC_const (c : ℂ) :
    P.boundedFC (f := fun _ => c) measurable_const (norm_nonneg c) (fun _ => le_rfl)
      = c • (1 : H →L[ℂ] H) := by
  refine ContinuousLinearMap.ext (fun y => ?_)
  refine ext_inner_left ℂ (fun x => ?_)
  rw [P.inner_boundedFC, P.bilinDiag_const, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, inner_smul_right]

/-- Additivity of the diagonal functional in `f`: `D_{f+g} = D_f + D_g`. -/
theorem diagInt_add {f g : Ω → ℂ} (hf : Measurable f) (hg : Measurable g)
    {Cf Cg : ℝ} (hCf : ∀ ω, ‖f ω‖ ≤ Cf) (hCg : ∀ ω, ‖g ω‖ ≤ Cg) (z : H) :
    P.diagInt (fun ω => f ω + g ω) z = P.diagInt f z + P.diagInt g z := by
  simp only [diagInt]
  exact MeasureTheory.integral_add (P.integrable_boundedMeasurable hf hCf z)
    (P.integrable_boundedMeasurable hg hCg z)

/-- Linearity of the diagonal functional over finite sums:
    `D_{∑ᵢ Fᵢ} = ∑ᵢ D_{Fᵢ}` (each `Fᵢ` integrable against `μ_z`).  Bound-free. -/
theorem diagInt_finsetSum {ι : Type*} (t : Finset ι) (F : ι → Ω → ℂ) (z : H)
    (hF : ∀ i ∈ t, MeasureTheory.Integrable (F i) (P.scalarMeasure z)) :
    P.diagInt (fun ω => ∑ i ∈ t, F i ω) z = ∑ i ∈ t, P.diagInt (F i) z := by
  simp only [diagInt]
  exact MeasureTheory.integral_finsetSum t hF

/-- Additivity of the polarized sesquilinear form in `f`: `B_{f+g} = B_f + B_g`. -/
theorem bilinDiag_add_f {f g : Ω → ℂ} (hf : Measurable f) (hg : Measurable g)
    {Cf Cg : ℝ} (hCf : ∀ ω, ‖f ω‖ ≤ Cf) (hCg : ∀ ω, ‖g ω‖ ≤ Cg) (x y : H) :
    P.bilinDiag (fun ω => f ω + g ω) x y = P.bilinDiag f x y + P.bilinDiag g x y := by
  simp only [bilinDiag]
  rw [P.diagInt_add hf hg hCf hCg, P.diagInt_add hf hg hCf hCg,
      P.diagInt_add hf hg hCf hCg, P.diagInt_add hf hg hCf hCg]
  ring

/-- Linearity of the polarized form over finite sums: `B_{∑ᵢ Fᵢ} = ∑ᵢ B_{Fᵢ}`. -/
theorem bilinDiag_finsetSum {ι : Type*} (t : Finset ι) (F : ι → Ω → ℂ)
    (hF : ∀ z : H, ∀ i ∈ t, MeasureTheory.Integrable (F i) (P.scalarMeasure z))
    (x y : H) :
    P.bilinDiag (fun ω => ∑ i ∈ t, F i ω) x y = ∑ i ∈ t, P.bilinDiag (F i) x y := by
  simp only [bilinDiag]
  rw [P.diagInt_finsetSum t F _ (hF _), P.diagInt_finsetSum t F _ (hF _),
      P.diagInt_finsetSum t F _ (hF _), P.diagInt_finsetSum t F _ (hF _)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

/-- **Additivity of the bounded-Borel FC in `f`:** `Φ(f+g) = Φ(f) + Φ(g)`. -/
theorem boundedFC_add {f g : Ω → ℂ} (hf : Measurable f) (hg : Measurable g)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ ω, ‖f ω‖ ≤ Cf) (hCg : ∀ ω, ‖g ω‖ ≤ Cg) :
    P.boundedFC (hf.add hg) (add_nonneg hCf0 hCg0)
        (fun ω => (norm_add_le _ _).trans (add_le_add (hCf ω) (hCg ω)))
      = P.boundedFC hf hCf0 hCf + P.boundedFC hg hCg0 hCg := by
  refine ContinuousLinearMap.ext (fun y => ?_)
  refine ext_inner_left ℂ (fun x => ?_)
  rw [P.inner_boundedFC, ContinuousLinearMap.add_apply, inner_add_right,
      P.inner_boundedFC, P.inner_boundedFC]
  exact P.bilinDiag_add_f hf hg hCf hCg x y

/-- Scalar-homogeneity of the diagonal functional in `f`: `D_{c·f} = c·D_f`. -/
theorem diagInt_smul_f (c : ℂ) (f : Ω → ℂ) (z : H) :
    P.diagInt (fun ω => c * f ω) z = c * P.diagInt f z := by
  simp only [diagInt]
  exact MeasureTheory.integral_const_mul c f

/-- Scalar-homogeneity of the polarized form in `f`: `B_{c·f} = c·B_f`. -/
theorem bilinDiag_smul_f (c : ℂ) (f : Ω → ℂ) (x y : H) :
    P.bilinDiag (fun ω => c * f ω) x y = c * P.bilinDiag f x y := by
  simp only [bilinDiag]
  rw [P.diagInt_smul_f, P.diagInt_smul_f, P.diagInt_smul_f, P.diagInt_smul_f]
  ring

/-- **ℂ-homogeneity of the bounded-Borel FC in `f`:** `Φ(c·f) = c·Φ(f)`. -/
theorem boundedFC_smul (c : ℂ) {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) :
    P.boundedFC (hf.const_mul c) (mul_nonneg (norm_nonneg c) hC0)
        (fun ω => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC ω) (norm_nonneg c))
      = c • P.boundedFC hf hC0 hC := by
  refine ContinuousLinearMap.ext (fun y => ?_)
  refine ext_inner_left ℂ (fun x => ?_)
  rw [P.inner_boundedFC, ContinuousLinearMap.smul_apply, inner_smul_right, P.inner_boundedFC]
  exact P.bilinDiag_smul_f c f x y

/-- **Operator-norm bound for the bounded-Borel FC:** `‖Φ(f)‖ ≤ 2C` for `‖f‖∞ ≤ C`.
    (`Φ(f)` is the adjoint of the Riesz operator `intBorel f`, and the adjoint is a
    linear isometry.)  This is the estimate that makes the simple→bounded-Borel
    extension converge in OPERATOR NORM — the route to multiplicativity `Φ(fg)=Φ(f)Φ(g)`
    that weak-operator convergence cannot deliver. -/
theorem boundedFC_norm_le {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) : ‖P.boundedFC hf hC0 hC‖ ≤ 2 * C := by
  rw [boundedFC, LinearIsometryEquiv.norm_map]
  exact P.intBorel_norm_le hf hC0 hC

/-- **`Φ(f)` depends only on `f`, not on the bound:** equal functions give equal
    operators (the value is `⟪x,Φ(f)y⟫ = B_f(x,y)`, independent of the bound proof).
    Lets us rewrite `f` to any pointwise-equal form (e.g. reindex a product). -/
theorem boundedFC_congr {f f' : Ω → ℂ} {Cf Cf' : ℝ}
    (hf : Measurable f) (hCf0 : 0 ≤ Cf) (hCf : ∀ ω, ‖f ω‖ ≤ Cf)
    (hf' : Measurable f') (hCf0' : 0 ≤ Cf') (hCf' : ∀ ω, ‖f' ω‖ ≤ Cf')
    (h : f = f') :
    P.boundedFC hf hCf0 hCf = P.boundedFC hf' hCf0' hCf' := by
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [P.inner_boundedFC, P.inner_boundedFC, h]

/- ── The indicator bridge: `Φ(𝟙_s) = E s` and multiplicativity on projections ─-/

/-- The complex indicator `𝟙_s` is bounded by `1`. -/
theorem norm_indicatorOne_le (s : Set Ω) (ω : Ω) :
    ‖(s.indicator (fun _ => (1 : ℂ))) ω‖ ≤ 1 := by
  by_cases hω : ω ∈ s
  · rw [Set.indicator_of_mem hω]; simp
  · rw [Set.indicator_of_notMem hω]; simp

/-- `D_{𝟙_s}(z) = μ_z(s)` — the diagonal functional of an indicator is the scalar
    spectral mass. -/
theorem diagInt_indicator {s : Set Ω} (hs : MeasurableSet s) (z : H) :
    P.diagInt (s.indicator (fun _ => (1 : ℂ))) z = ((P.scalarMeasure z s).toReal : ℂ) := by
  rw [diagInt, MeasureTheory.integral_indicator_const (1 : ℂ) hs, Complex.real_smul, mul_one,
    MeasureTheory.measureReal_def]

/-- `D_{𝟙_s}(z) = ⟪z, E s z⟫` — the diagonal of the indicator's form is the
    projection's quadratic form. -/
theorem diagInt_indicator_eq_inner {s : Set Ω} (hs : MeasurableSet s) (z : H) :
    P.diagInt (s.indicator (fun _ => (1 : ℂ))) z = inner ℂ z (P.E s z) := by
  rw [P.diagInt_indicator hs, P.scalarMeasure_toReal z hs, P.inner_E_self hs]
  push_cast; ring

/-- **Indicator bridge (polarized):** the bounded-Borel sesquilinear form of an
    indicator is the spectral projection's form, `B_{𝟙_s}(x,y) = ⟪x, E s y⟫`.
    Proved by reducing the four polarization points to `⟪z, E s z⟫` and expanding
    by sesquilinearity (the same Jordan–von Neumann computation as
    `inner_E_polarization`, with the `I•x ± y` convention of `bilinDiag`). -/
theorem bilinDiag_indicator {s : Set Ω} (hs : MeasurableSet s) (x y : H) :
    P.bilinDiag (s.indicator (fun _ => (1 : ℂ))) x y = inner ℂ x (P.E s y) := by
  rw [bilinDiag, P.diagInt_indicator_eq_inner hs, P.diagInt_indicator_eq_inner hs,
    P.diagInt_indicator_eq_inner hs, P.diagInt_indicator_eq_inner hs]
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I, ← pow_two, Complex.I_sq, mul_add, mul_sub, ← mul_assoc,
    mul_neg, neg_neg, one_mul, neg_one_mul, sub_sub]
  ring

/-- **The bounded-Borel FC of an indicator is the spectral projection:** `Φ(𝟙_s) = E s`.
    This anchors the abstract Borel functional calculus to the PVM it came from. -/
theorem boundedFC_indicator {s : Set Ω} (hs : MeasurableSet s) :
    P.boundedFC (f := s.indicator (fun _ => (1 : ℂ)))
        (measurable_const.indicator hs) zero_le_one (norm_indicatorOne_le s)
      = P.E s := by
  refine ContinuousLinearMap.ext (fun y => ?_)
  refine ext_inner_left ℂ (fun x => ?_)
  rw [P.inner_boundedFC, P.bilinDiag_indicator hs]

/-- **Multiplicativity of the FC on indicators** (the projection `*`-relation):
    since `𝟙_s · 𝟙_t = 𝟙_{s∩t}` pointwise, `Φ(𝟙_{s∩t}) = E s · E t`.  This is the
    multiplicative law `Φ(f·g) = Φ(f)·Φ(g)` verified on the indicator algebra — the
    generating subalgebra of the bounded-Borel functions. -/
theorem boundedFC_indicator_mul {s t : Set Ω} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    P.boundedFC (f := (s ∩ t).indicator (fun _ => (1 : ℂ)))
        (measurable_const.indicator (hs.inter ht)) zero_le_one
        (norm_indicatorOne_le _)
      = P.E s * P.E t := by
  rw [P.boundedFC_indicator (hs.inter ht), P.E_inter hs ht]

/-- **The bounded-Borel FC of a simple function is its spectral integral:**
    `Φ(∑ᵢ cᵢ 𝟙_{sᵢ}) = ∑ᵢ cᵢ E sᵢ = integralSimple`.  Proved at the sesquilinear-form
    level: `B_{∑cᵢ𝟙_{sᵢ}} = ∑ cᵢ B_{𝟙_{sᵢ}} = ∑ cᵢ ⟪x, E sᵢ y⟫` (finset linearity +
    smul-in-`f` + the indicator bridge). -/
theorem boundedFC_eq_integralSimple {ι : Type*} (t : Finset ι) (c : ι → ℂ)
    (sets : ι → Set Ω) (hm : ∀ i ∈ t, MeasurableSet (sets i)) :
    P.boundedFC
        (f := fun ω => ∑ i ∈ t, c i * (sets i).indicator (fun _ => (1 : ℂ)) ω)
        (Finset.measurable_sum t fun i hi =>
          (measurable_const.indicator (hm i hi)).const_mul (c i))
        (Finset.sum_nonneg fun i _ => norm_nonneg (c i))
        (fun ω => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_left (norm_indicatorOne_le _ ω)
            (norm_nonneg _)).trans_eq (mul_one _)))
      = P.integralSimple t c sets := by
  refine ContinuousLinearMap.ext (fun y => ?_)
  refine ext_inner_left ℂ (fun x => ?_)
  rw [P.inner_boundedFC, P.inner_integralSimple_left,
      P.bilinDiag_finsetSum t (fun i ω => c i * (sets i).indicator (fun _ => (1 : ℂ)) ω)
        (fun z i hi => P.integrable_boundedMeasurable
          ((measurable_const.indicator (hm i hi)).const_mul (c i))
          (fun ω => by
            rw [norm_mul]
            exact (mul_le_mul_of_nonneg_left (norm_indicatorOne_le _ ω)
              (norm_nonneg _)).trans_eq (mul_one _)) z) x y]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [P.bilinDiag_smul_f (c i) ((sets i).indicator (fun _ => (1 : ℂ))) x y,
      P.bilinDiag_indicator (hm i hi)]

/-- **Operator product of two simple integrals** (the algebraic core of
    multiplicativity `Φ(fg)=Φ(f)Φ(g)` for simple `f,g`): cross terms collapse by
    `E Aᵢ · E Bⱼ = E(Aᵢ ∩ Bⱼ)`. -/
theorem integralSimple_mul_eq {ι κ : Type*} (t : Finset ι) (s : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (A : ι → Set Ω) (B : κ → Set Ω)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (hB : ∀ j ∈ s, MeasurableSet (B j)) :
    P.integralSimple t a A * P.integralSimple s b B
      = ∑ i ∈ t, ∑ j ∈ s, (a i * b j) • P.E (A i ∩ B j) := by
  simp only [integralSimple]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [smul_mul_smul, ← P.E_inter (hA i hi) (hB j hj)]

/-- The simple integral over the **product index** `t ×ˢ s` (weights `aᵢbⱼ`, sets
    `Aᵢ ∩ Bⱼ`) equals the product of the two simple integrals.  Pure operator algebra
    (`integralSimple_mul_eq` + `Finset.sum_product`). -/
theorem integralSimple_product_eq {ι κ : Type*} (t : Finset ι) (s : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (A : ι → Set Ω) (B : κ → Set Ω)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (hB : ∀ j ∈ s, MeasurableSet (B j)) :
    P.integralSimple (t ×ˢ s) (fun p => a p.1 * b p.2) (fun p => A p.1 ∩ B p.2)
      = P.integralSimple t a A * P.integralSimple s b B := by
  rw [P.integralSimple_mul_eq t s a b A B hA hB, integralSimple, Finset.sum_product]

/-- **Multiplicativity on simple functions:** `Φ(f·g) = Φ(f)·Φ(g)` for simple
    `f = ∑ᵢ aᵢ 𝟙_{Aᵢ}`, `g = ∑ⱼ bⱼ 𝟙_{Bⱼ}`.  Stated with `Φ(f), Φ(g)` as the simple
    integrals (`= Φ(f), Φ(g)` by `boundedFC_eq_integralSimple`).  Proof: the product
    `f·g` reindexes pointwise to the `t ×ˢ s` simple function (`boundedFC_congr` +
    `Finset.sum_mul_sum` + the indicator product `𝟙_A·𝟙_B = 𝟙_{A∩B}`), whose FC is
    `integralSimple (t ×ˢ s) = (integralSimple t)·(integralSimple s)`. -/
theorem boundedFC_simple_mul {ι κ : Type*} (t : Finset ι) (s : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (A : ι → Set Ω) (B : κ → Set Ω)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (hB : ∀ j ∈ s, MeasurableSet (B j)) :
    P.boundedFC
        (f := fun ω => (∑ i ∈ t, a i * (A i).indicator (fun _ => (1 : ℂ)) ω)
                      * (∑ j ∈ s, b j * (B j).indicator (fun _ => (1 : ℂ)) ω))
        (C := (∑ i ∈ t, ‖a i‖) * ∑ j ∈ s, ‖b j‖)
        ((Finset.measurable_sum t fun i hi =>
            (measurable_const.indicator (hA i hi)).const_mul (a i)).mul
          (Finset.measurable_sum s fun j hj =>
            (measurable_const.indicator (hB j hj)).const_mul (b j)))
        (mul_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg (a i))
          (Finset.sum_nonneg fun j _ => norm_nonneg (b j)))
        (fun ω => by
          rw [norm_mul]
          refine mul_le_mul ?_ ?_ (norm_nonneg _)
            (Finset.sum_nonneg fun i _ => norm_nonneg (a i))
          · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
              rw [norm_mul]
              exact (mul_le_mul_of_nonneg_left (norm_indicatorOne_le _ ω)
                (norm_nonneg _)).trans_eq (mul_one _))
          · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
              rw [norm_mul]
              exact (mul_le_mul_of_nonneg_left (norm_indicatorOne_le _ ω)
                (norm_nonneg _)).trans_eq (mul_one _)))
      = P.integralSimple t a A * P.integralSimple s b B := by
  rw [← P.integralSimple_product_eq t s a b A B hA hB,
      ← P.boundedFC_eq_integralSimple (t ×ˢ s) (fun p => a p.1 * b p.2)
        (fun p => A p.1 ∩ B p.2)
        (fun p hp => (hA p.1 (Finset.mem_product.mp hp).1).inter
          (hB p.2 (Finset.mem_product.mp hp).2))]
  refine P.boundedFC_congr _ _ _ _ _ _ ?_
  funext ω
  rw [Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [mul_mul_mul_comm]
  congr 1
  rw [← Set.inter_indicator_mul]
  simp

/-- **`SimpleFunc` as a sum of scaled indicators** (the bridge from Mathlib's
    `SimpleFunc`, produced by `approxOn`, to the `∑ cᵢ 𝟙_{sᵢ}` form of our FC lemmas):
    `φ a = ∑_{y ∈ φ.range} y · 𝟙_{φ⁻¹{y}}(a)`.  Exactly one range term is nonzero. -/
theorem simpleFunc_eq_sum (φ : MeasureTheory.SimpleFunc Ω ℂ) (a : Ω) :
    φ a = ∑ y ∈ φ.range, y * (φ ⁻¹' {y}).indicator (fun _ => (1 : ℂ)) a := by
  rw [Finset.sum_eq_single (φ a)]
  · rw [Set.indicator_of_mem (by simp), mul_one]
  · intro y _ hne
    rw [Set.indicator_of_notMem
      (by simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact fun h => hne h.symm),
      mul_zero]
  · intro h
    exact absurd (φ.mem_range_self a) h

/-- **The FC of a `SimpleFunc`** equals the spectral integral over its range:
    `Φ(⇑φ) = ∑_{y ∈ φ.range} y · E(φ⁻¹{y})`. -/
theorem boundedFC_simpleFunc (φ : MeasureTheory.SimpleFunc Ω ℂ) {C : ℝ}
    (hf : Measurable (⇑φ)) (hC0 : 0 ≤ C) (hC : ∀ ω, ‖φ ω‖ ≤ C) :
    P.boundedFC hf hC0 hC = P.integralSimple φ.range id (fun y => φ ⁻¹' {y}) := by
  rw [← P.boundedFC_eq_integralSimple φ.range id (fun y => φ ⁻¹' {y})
        (fun y _ => φ.measurableSet_fiber y)]
  exact P.boundedFC_congr _ _ _ _ _ _ (funext fun a => simpleFunc_eq_sum φ a)

/-- **Multiplicativity on `SimpleFunc`s:** `Φ(⇑φ · ⇑ψ) = Φ(⇑φ)·Φ(⇑ψ)`.  Reduces to
    `boundedFC_simple_mul` over the ranges of `φ, ψ` via `simpleFunc_eq_sum`. -/
theorem boundedFC_simpleFunc_mul (φ ψ : MeasureTheory.SimpleFunc Ω ℂ) {Cφ Cψ Cp : ℝ}
    (hfφ : Measurable (⇑φ)) (hC0φ : 0 ≤ Cφ) (hCφ : ∀ ω, ‖φ ω‖ ≤ Cφ)
    (hfψ : Measurable (⇑ψ)) (hC0ψ : 0 ≤ Cψ) (hCψ : ∀ ω, ‖ψ ω‖ ≤ Cψ)
    (hfp : Measurable (fun ω => φ ω * ψ ω)) (hC0p : 0 ≤ Cp)
    (hCp : ∀ ω, ‖φ ω * ψ ω‖ ≤ Cp) :
    P.boundedFC hfp hC0p hCp
      = P.boundedFC hfφ hC0φ hCφ * P.boundedFC hfψ hC0ψ hCψ := by
  rw [P.boundedFC_simpleFunc φ hfφ hC0φ hCφ, P.boundedFC_simpleFunc ψ hfψ hC0ψ hCψ,
      ← P.boundedFC_simple_mul φ.range ψ.range id id (fun y => φ ⁻¹' {y})
        (fun y => ψ ⁻¹' {y}) (fun y _ => φ.measurableSet_fiber y)
        (fun y _ => ψ.measurableSet_fiber y)]
  exact P.boundedFC_congr _ _ _ _ _ _
    (funext fun ω => by simp only [simpleFunc_eq_sum φ ω, simpleFunc_eq_sum ψ ω, id_eq])

/- ── Bounded-convergence ("normality") continuity of the FC ─────────────────-/

/-- **Dominated/bounded convergence for the diagonal functional:** if `fₙ → f`
    pointwise with a common bound `C`, then `D_{fₙ}(z) → D_f(z)`.  (DCT against the
    finite measure `μ_z`.)  The engine for extending FC identities from simple to
    all bounded Borel functions. -/
theorem tendsto_diagInt_of_dominated {f : ℕ → Ω → ℂ} {g : Ω → ℂ} {C : ℝ}
    (hf : ∀ n, Measurable (f n)) (hfb : ∀ n ω, ‖f n ω‖ ≤ C)
    (hlim : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (nhds (g ω))) (z : H) :
    Filter.Tendsto (fun n => P.diagInt (f n) z) Filter.atTop (nhds (P.diagInt g z)) := by
  simp only [diagInt]
  exact MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hf n).aestronglyMeasurable)
    (MeasureTheory.integrable_const C)
    (fun n => Filter.Eventually.of_forall (fun ω => hfb n ω))
    (Filter.Eventually.of_forall hlim)

/-- **Bounded-convergence continuity of the bounded-Borel FC** (weak-operator
    "normality"): if `fₙ → f` pointwise with a common bound `C`, then
    `⟪x, Φ(fₙ) y⟫ → ⟪x, Φ(f) y⟫`.  This is the limit principle that lets the
    indicator/simple identities (e.g. multiplicativity) extend to all bounded
    Borel `f`. -/
theorem tendsto_inner_boundedFC_of_dominated {f : ℕ → Ω → ℂ} {g : Ω → ℂ} {C : ℝ}
    (hC0 : 0 ≤ C) (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hfb : ∀ n ω, ‖f n ω‖ ≤ C) (hgb : ∀ ω, ‖g ω‖ ≤ C)
    (hlim : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (nhds (g ω))) (x y : H) :
    Filter.Tendsto (fun n => inner ℂ x ((P.boundedFC (hf n) hC0 (hfb n)) y))
      Filter.atTop (nhds (inner ℂ x ((P.boundedFC hg hC0 hgb) y))) := by
  simp only [P.inner_boundedFC, bilinDiag]
  have h1 := P.tendsto_diagInt_of_dominated hf hfb hlim (x + y)
  have h2 := P.tendsto_diagInt_of_dominated hf hfb hlim (x - y)
  have h3 := P.tendsto_diagInt_of_dominated hf hfb hlim (Complex.I • x + y)
  have h4 := P.tendsto_diagInt_of_dominated hf hfb hlim (Complex.I • x - y)
  exact (((h1.sub h2).add (h3.const_mul Complex.I)).sub
    (h4.const_mul Complex.I)).const_mul (4⁻¹ : ℂ)

/-- Bound-free form of the normality engine: `B_{fₙ}(x,y) → B_f(x,y)` under bounded
    pointwise convergence (the limit `f` needs no bound — `bilinDiag` carries none).
    This is the workhorse for the simple→bounded-Borel multiplicativity extension. -/
theorem tendsto_bilinDiag_of_dominated {f : ℕ → Ω → ℂ} {g : Ω → ℂ} {C : ℝ}
    (hf : ∀ n, Measurable (f n)) (hfb : ∀ n ω, ‖f n ω‖ ≤ C)
    (hlim : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (nhds (g ω))) (x y : H) :
    Filter.Tendsto (fun n => P.bilinDiag (f n) x y) Filter.atTop (nhds (P.bilinDiag g x y)) := by
  simp only [bilinDiag]
  have h1 := P.tendsto_diagInt_of_dominated hf hfb hlim (x + y)
  have h2 := P.tendsto_diagInt_of_dominated hf hfb hlim (x - y)
  have h3 := P.tendsto_diagInt_of_dominated hf hfb hlim (Complex.I • x + y)
  have h4 := P.tendsto_diagInt_of_dominated hf hfb hlim (Complex.I • x - y)
  exact (((h1.sub h2).add (h3.const_mul Complex.I)).sub
    (h4.const_mul Complex.I)).const_mul (4⁻¹ : ℂ)

/- ── The bounded-Borel approximating sequence (via `approxOn`) ───────────────-/

/-- The `approxOn` simple-function sequence for a bounded measurable `f` (base point
    `0`, set `univ`): `approxSeq f hf n` is a `SimpleFunc`, `→ f` pointwise, with
    `‖approxSeq f hf n ω‖ ≤ 2‖f ω‖`. -/
noncomputable def approxSeq (f : Ω → ℂ) (hf : Measurable f) (n : ℕ) :
    MeasureTheory.SimpleFunc Ω ℂ :=
  MeasureTheory.SimpleFunc.approxOn f hf Set.univ 0 (Set.mem_univ 0) n

theorem approxSeq_tendsto {f : Ω → ℂ} (hf : Measurable f) (ω : Ω) :
    Filter.Tendsto (fun n => approxSeq f hf n ω) Filter.atTop (nhds (f ω)) :=
  MeasureTheory.SimpleFunc.tendsto_approxOn hf (Set.mem_univ 0)
    (by simp)

theorem approxSeq_norm_le {f : Ω → ℂ} (hf : Measurable f) (n : ℕ) (ω : Ω) :
    ‖approxSeq f hf n ω‖ ≤ ‖f ω‖ + ‖f ω‖ :=
  MeasureTheory.SimpleFunc.norm_approxOn_zero_le hf (Set.mem_univ 0) ω n

theorem approxSeq_measurable {f : Ω → ℂ} (hf : Measurable f) (n : ℕ) :
    Measurable (⇑(approxSeq f hf n)) :=
  (approxSeq f hf n).measurable

/- ── Multiplicativity capstone: `Φ(f·g) = Φ(f)·Φ(g)` for bounded Borel `f,g` ──-/

/-- **Stage 1 (left simple):** `Φ(⇑φ · g) = Φ(⇑φ)·Φ(g)` for a `SimpleFunc φ` and a
    bounded measurable `g`.  Approximate `g` by `SimpleFunc`s `gₘ → g` and pass to the
    weak limit: `⟪x, Φ(φ·gₘ)y⟫ = ⟪Φ(φ)†x, Φ(gₘ)y⟫` (by `boundedFC_simpleFunc_mul`),
    both sides converge (`tendsto_bilinDiag`), so the limits agree. -/
theorem boundedFC_mul_simpleFunc_left (φ : MeasureTheory.SimpleFunc Ω ℂ)
    {g : Ω → ℂ} {Cφ Cg Cp : ℝ}
    (hfφ : Measurable (⇑φ)) (hC0φ : 0 ≤ Cφ) (hCφ : ∀ ω, ‖φ ω‖ ≤ Cφ)
    (hg : Measurable g) (hC0g : 0 ≤ Cg) (hCg : ∀ ω, ‖g ω‖ ≤ Cg)
    (hfp : Measurable (fun ω => φ ω * g ω)) (hC0p : 0 ≤ Cp)
    (hCp : ∀ ω, ‖φ ω * g ω‖ ≤ Cp) :
    P.boundedFC hfp hC0p hCp = P.boundedFC hfφ hC0φ hCφ * P.boundedFC hg hC0g hCg := by
  -- abbreviations for the approximating SimpleFuncs gₘ → g and their bounds
  have hgm_meas : ∀ m, Measurable (⇑(approxSeq g hg m)) := fun m => approxSeq_measurable hg m
  have hgm_bd : ∀ m ω, ‖approxSeq g hg m ω‖ ≤ Cg + Cg := fun m ω =>
    (approxSeq_norm_le hg m ω).trans (add_le_add (hCg ω) (hCg ω))
  have hgm_lim : ∀ ω, Filter.Tendsto (fun m => approxSeq g hg m ω) Filter.atTop (nhds (g ω)) :=
    fun ω => approxSeq_tendsto hg ω
  have hpm_meas : ∀ m, Measurable (fun ω => φ ω * approxSeq g hg m ω) :=
    fun m => hfφ.mul (hgm_meas m)
  have hpm_bd : ∀ m ω, ‖φ ω * approxSeq g hg m ω‖ ≤ Cφ * (Cg + Cg) := fun m ω => by
    rw [norm_mul]; exact mul_le_mul (hCφ ω) (hgm_bd m ω) (norm_nonneg _) hC0φ
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [P.inner_boundedFC, ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.adjoint_inner_left, P.inner_boundedFC]
  -- goal: bilinDiag (φ·g) x y = bilinDiag g (Φ(φ)†x) y
  -- per-m identity: bilinDiag (φ·gₘ) x y = bilinDiag gₘ (Φ(φ)†x) y
  have hpm : ∀ m, P.bilinDiag (fun ω => φ ω * approxSeq g hg m ω) x y
      = P.bilinDiag (⇑(approxSeq g hg m))
          (ContinuousLinearMap.adjoint (P.boundedFC hfφ hC0φ hCφ) x) y := fun m => by
    rw [← P.inner_boundedFC (hpm_meas m) (mul_nonneg hC0φ (add_nonneg hC0g hC0g)) (hpm_bd m),
        P.boundedFC_simpleFunc_mul φ (approxSeq g hg m) hfφ hC0φ hCφ
          (hgm_meas m) (add_nonneg hC0g hC0g) (hgm_bd m)
          (hpm_meas m) (mul_nonneg hC0φ (add_nonneg hC0g hC0g)) (hpm_bd m),
        ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left,
        P.inner_boundedFC]
  -- two weak limits, joined by uniqueness
  have tA := P.tendsto_bilinDiag_of_dominated (C := Cφ * (Cg + Cg)) hpm_meas hpm_bd
    (fun ω => (hgm_lim ω).const_mul (φ ω)) x y
  have tB := P.tendsto_bilinDiag_of_dominated (C := Cg + Cg) hgm_meas hgm_bd hgm_lim
    (ContinuousLinearMap.adjoint (P.boundedFC hfφ hC0φ hCφ) x) y
  exact tendsto_nhds_unique (tA.congr hpm) tB

/-- **MULTIPLICATIVITY OF THE BOUNDED-BOREL FUNCTIONAL CALCULUS** (the keystone):
    `Φ(f·g) = Φ(f)·Φ(g)` for all bounded measurable `f, g`.  Approximate `f` by
    `SimpleFunc`s `fₙ → f` and pass to the weak limit, using Stage 1 (left-simple
    multiplicativity) for each `fₙ`: `⟪x, Φ(fₙ·g)y⟫ = ⟪x, Φ(fₙ)(Φ(g)y)⟫`, both sides
    converge (`tendsto_bilinDiag`), so the limits agree.  Together with `boundedFC_add`,
    `boundedFC_smul` and `boundedFC_const`, the FC `Φ : Bᵇ(Ω) → (H →L[ℂ] H)` is a
    unital `*`-algebra homomorphism. -/
theorem boundedFC_mul {f g : Ω → ℂ} {Cf Cg Cp : ℝ}
    (hf : Measurable f) (hC0f : 0 ≤ Cf) (hCf : ∀ ω, ‖f ω‖ ≤ Cf)
    (hg : Measurable g) (hC0g : 0 ≤ Cg) (hCg : ∀ ω, ‖g ω‖ ≤ Cg)
    (hfp : Measurable (fun ω => f ω * g ω)) (hC0p : 0 ≤ Cp)
    (hCp : ∀ ω, ‖f ω * g ω‖ ≤ Cp) :
    P.boundedFC hfp hC0p hCp = P.boundedFC hf hC0f hCf * P.boundedFC hg hC0g hCg := by
  have hfn_meas : ∀ n, Measurable (⇑(approxSeq f hf n)) := fun n => approxSeq_measurable hf n
  have hfn_bd : ∀ n ω, ‖approxSeq f hf n ω‖ ≤ Cf + Cf := fun n ω =>
    (approxSeq_norm_le hf n ω).trans (add_le_add (hCf ω) (hCf ω))
  have hfn_lim : ∀ ω, Filter.Tendsto (fun n => approxSeq f hf n ω) Filter.atTop (nhds (f ω)) :=
    fun ω => approxSeq_tendsto hf ω
  have hpn_meas : ∀ n, Measurable (fun ω => approxSeq f hf n ω * g ω) :=
    fun n => (hfn_meas n).mul hg
  have hpn_bd : ∀ n ω, ‖approxSeq f hf n ω * g ω‖ ≤ (Cf + Cf) * Cg := fun n ω => by
    rw [norm_mul]; exact mul_le_mul (hfn_bd n ω) (hCg ω) (norm_nonneg _) (add_nonneg hC0f hC0f)
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [P.inner_boundedFC, ContinuousLinearMap.mul_apply, P.inner_boundedFC]
  -- goal: bilinDiag (f·g) x y = bilinDiag f x (Φ(g) y)
  have hpn : ∀ n, P.bilinDiag (fun ω => approxSeq f hf n ω * g ω) x y
      = P.bilinDiag (⇑(approxSeq f hf n)) x (P.boundedFC hg hC0g hCg y) := fun n => by
    rw [← P.inner_boundedFC (hpn_meas n) (mul_nonneg (add_nonneg hC0f hC0f) hC0g) (hpn_bd n),
        P.boundedFC_mul_simpleFunc_left (approxSeq f hf n) (hfn_meas n) (add_nonneg hC0f hC0f)
          (hfn_bd n) hg hC0g hCg (hpn_meas n) (mul_nonneg (add_nonneg hC0f hC0f) hC0g) (hpn_bd n),
        ContinuousLinearMap.mul_apply, P.inner_boundedFC]
  have tA := P.tendsto_bilinDiag_of_dominated (C := (Cf + Cf) * Cg) hpn_meas hpn_bd
    (fun ω => (hfn_lim ω).mul_const (g ω)) x y
  have tB := P.tendsto_bilinDiag_of_dominated (C := Cf + Cf) hfn_meas hfn_bd hfn_lim
    x (P.boundedFC hg hC0g hCg y)
  exact tendsto_nhds_unique (tA.congr hpn) tB

end ProjectionValuedMeasure

/- ── Phase-1 analytic TARGETS (named, sound on `ProjectionValuedMeasure`) ──

    Recorded precisely (not as opaque axioms — the module stays axiom-free):

    (T1) SCALAR MEASURES.  ✅ PROVED — `ProjectionValuedMeasure.scalarMeasure x`
         is a genuine finite `MeasureTheory.Measure Ω` with
         `scalarMeasure_apply : μ_x s = ENNReal.ofReal (‖E s x‖²)` (measurable `s`)
         and `scalarMeasure_univ : μ_x univ = ENNReal.ofReal (‖x‖²)`.  Proof:
         strong σ-additivity `hasSum_iUnion` pushed through the bounded linear
         functional `⟪x,·⟫` (then `Re`) gives σ-additivity of `‖E(·)x‖²`, fed to
         `Measure.ofMeasurable`.  (FALSE for a mere `PVContent` — see the
         ultrafilter remark above.)

    (T2) BOUNDED-BOREL FUNCTIONAL CALCULUS.  `f ↦ ∫ f dE` from bounded measurable
         functions to `H →L[ℂ] H`, a `*`-homomorphism with `‖∫f dE‖ ≤ ‖f‖∞`,
         `∫f̄ dE = (∫f dE)†`, `∫(fg)dE = (∫f dE)(∫g dE)`, and
         `⟪x,(∫f dE)y⟫ = ∫ f dμ_{x,y}` (μ via polarization of the `μ_x`).
         ◧ STARTED — the `*`-HOMOMORPHISM CORE on simple functions is PROVED
         (axiom-free): `integralSimple_adjoint` (adjoint law `∫f̄ = (∫f)†`, each
         `E s` self-adjoint) and `integralSimple_mul` (multiplicativity
         `∫f·∫g = ∫(fg)` over a pairwise-disjoint family — cross terms vanish via
         `E sᵢ·E sⱼ = E(sᵢ∩sⱼ) = E ∅ = 0`, diagonal collapses by idempotence).
         Also PROVED: `integralSimple_star_mul_self` (`(∫f)⋆(∫f) = ∫|f|²`, the
         positive operator `T⋆T`).
         ★ THE NORM BOUND `‖∫f dE‖ ≤ ‖f‖∞` IS NOW PROVED axiom-free
         (`integralSimple_opNorm_le`).  The C\*-order route via
         `CStarAlgebra.norm_le_norm_of_nonneg_of_le` is BLOCKED in Mathlib: the
         partial order on `H →L[ℂ] H` is the Loewner order (`instLoewnerPartialOrder`)
         but there is no `StarOrderedRing (H →L[ℂ] H)` instance (upstream TODO), so
         that lemma does not fire.  Instead the bound is proved by the elementary
         POINTWISE PYTHAGORAS estimate: with `sᵢ` pairwise disjoint the vectors
         `cᵢ E sᵢ x` are orthogonal (`E_apply_orthogonal`), so
         `‖T x‖² = ∑ᵢ ‖cᵢ‖² ‖E sᵢ x‖² ≤ M² ∑ᵢ ‖E sᵢ x‖² = M² ‖E(⋃ᵢ sᵢ) x‖²
         ≤ M² ‖x‖²` (`norm_sum_sq_of_orthogonal` twice; `sum_E_biUnion` for the
         middle equality; `norm_E_apply_le`, i.e. `E ≤ 1` ⟹ contraction, for the
         last), then `opNorm_le_bound`.  Supporting order facts also PROVED:
         `E_nonneg` (`0 ≤ E s`) and `E_le_one` (`E s ≤ 1`), and
         `integralSimple_one` (`∫1 dE = 1` over a covering partition).
         ★ THE SESQUILINEAR / QUADRATIC-FORM BRIDGE IS NOW PROVED on the genuine
         `ProjectionValuedMeasure` (axiom-free): `inner_integralSimple_left`
         (`⟪x,(∫f)y⟫ = ∑ᵢ cᵢ⟪x,E sᵢ y⟫`, the bilinear datum), its diagonal
         `re_inner_integralSimple_self` (`Re⟪x,(∫f)x⟫ = ∑ᵢ aᵢ‖E sᵢ x‖²`), and the
         genuine Lebesgue-integral identity `re_inner_integralSimple_eq_lintegral`
         (`Re⟪x,(∫f dE)x⟫ = ∫ f dμ_x` for a nonneg real simple `f`, with `μ_x` the
         T1 scalar spectral measure), via `lintegral_indicatorSum_eq`.
         ★ THE OFF-DIAGONAL POLARIZATION IS NOW PROVED axiom-free:
         `inner_E_polarization` (`⟪x,E s y⟫` as a ℂ-combination of diagonal forms
         `⟪z,E s z⟫`) and `inner_E_eq_polarization_measures`
         (`μ_{x,y}(s) = ¼(μ_{x+y}(s) − μ_{x−y}(s) − i μ_{x+iy}(s) + i μ_{x−iy}(s))`,
         exhibiting the complex weight as a combination of the four GENUINE
         scalar measures — so `μ_{x,y}` inherits countable additivity), with the
         capstone `inner_integralSimple_eq_polarization` writing the simple
         sesquilinear form `⟪x,(∫f)y⟫` purely via the genuine measures.
         REMAINING for T2: only the simple→bounded-Borel EXTENSION lifting these
         from simple `f` to all bounded Borel `f`.  ROUTE CHOSEN (scoped, see
         TOMITA_TAKESAKI_ROADMAP.md "T2 extension sub-plan"): **A, Riesz form** via
         `InnerProductSpace.continuousLinearMapOfBilin` (`B♯` with `⟪B♯v,w⟫=B v w`),
         building `∫f dE := (B_f)♯` from the bounded sesquilinear form
         `B_f(x,y) = ∫ f dμ_{x,y}` — no operator-topology limit needed for
         existence.  FOUNDATIONS PROVED here: `instIsFiniteMeasure_scalarMeasure`
         (bounded `f` Bochner-integrable against `μ_x`) and
         `scalarMeasure_toReal_parallelogram` (seeds the form's sesquilinearity).
         The deepest residual is multiplicativity `∫(fg) = ∫f ∘ ∫g` for bounded
         `f,g` (needs a monotone-class / dominated-convergence step).

    (T3) SPECTRAL THEOREM.  Every bounded self-adjoint `T` admits a unique PVM on
         `ℝ` (supported on `spectrum`) with `⟪x, T x⟫ = ∫ id dμ_x`.  Recommended
         route (per consultation): extend Mathlib's CONTINUOUS functional
         calculus `π : C(spec T) →⋆ₐ B(H)` to a normal representation of bounded
         Borel functions via `x ↦ ⟪x, π(·) x⟫` + Riesz–Markov, then `E(B):=Φ(1_B)`.
         AVOID the bidual / universal-W*-representation route in Lean for now.

    Note the modular target needs Δ^{it} where `Δ ≥ 0` may have `0` in its
    continuous spectrum, so `λ ↦ λ^{it}` is bounded BOREL but not continuous —
    continuous FC is insufficient; T2/T3 (Borel FC) are genuinely required, and
    the modular group is STRONGLY (not norm-) continuous.  See Phase 2. -/

end Spectral
end QIQTH
