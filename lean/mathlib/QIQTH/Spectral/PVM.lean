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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

namespace QIQTH
namespace Spectral

open scoped BigOperators

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
         `⟪x,(∫f dE)y⟫ = ∫ f dμ_{x,y}` (μ via polarization of the `μ_x`).  The
         hard step is the continuous→Borel multiplicativity extension
         (monotone-class) + SOT bounded-convergence, NOT uniqueness.

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
