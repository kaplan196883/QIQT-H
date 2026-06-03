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
