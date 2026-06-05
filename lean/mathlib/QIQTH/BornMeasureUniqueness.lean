/-
  λ-identification: the canonical product-history Born measure is FORCED.

  This is the conceptual bridge the finite Born-typicality development was missing.
  The QIQT-H selector λ (CoreNoCollapse) assigns, to an event `S` of `n`-trial
  measurement histories `ω : Fin n → Fin m`, the weight

      λ_{ρ,E,n}(S) = tr( ρ^⊗ⁿ · ∑_{ω ∈ S} ⊗ₜ E(ωₜ) ) .

  We show this λ is UNIQUELY pinned down: ANY finitely-additive measure `μ` on
  history events whose single-history weights are the product Born weights
  `∏ₜ tr(ρ E_{ωₜ})` must coincide with the trace functional `tr(ρ^⊗ⁿ · F_S)`.

  Two ingredients, both proved here, axiom-free:

    • `eventEffect_univ`  the product-history effects `F_ω = ⊗ₜ E(ωₜ)` are a genuine
                          POVM on the big space: `∑_ω F_ω = 1` (from `∑ₖ Eₖ = 1`,
                          via the SAME product/sum interchange behind `sum_w_eq_one`);

    • `measure_unique_of_additive`  two finitely-additive measures agreeing on
                          singletons are equal (the determination backbone).

  Composed (`product_born_measure_unique`), they give the λ-identification: the
  product Born measure is the unique additive history measure with the Born product
  marginals, and it EQUALS the trace functional.  The single-history marginals
  `tr(ρ E_k)` are themselves the unique Gleason/effect measure on the single-trial
  POVM (`EffectGleason.finite_effect_gleason_unique`); so once the single-trial Born
  rule is forced by Gleason, the whole n-trial product measure is forced by
  additivity — no extra postulate.

  NOTE on honest scope: the hypothesis `μ {ω} = ∏ₜ tr(ρ E_{ωₜ})` encodes BOTH the
  single-trial Born values AND their independent (product) combination across trials.
  The product factorization is the i.i.d. preparation `ρ^⊗ⁿ`; tensor-multiplicativity
  of Born under independent experiments is treated separately (RecordGleason).  What
  is established here is the measure-theoretic uniqueness GIVEN those marginals.
-/

import QIQTH.BornTypicalityQuantum
import QIQTH.BornTypicalityFinite

namespace QIQTH
namespace BornMeasureUniqueness

open Finset Matrix BornTypicalityQuantum
open scoped ComplexOrder

variable {n d m : ℕ}

/-- The canonical product-history Born measure: `λ(S) = ∑_{ω ∈ S} ∏ₜ tr(ρ E_{ωₜ})`.
    (Equal to the trace functional `tr(ρ^⊗ⁿ · F_S)` — see `bornMeasure_eq_trace`.) -/
noncomputable def bornMeasure (ρ : Matrix (Fin d) (Fin d) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (S : Finset (Fin n → Fin m)) : ℝ :=
  ∑ ω ∈ S, BornTypicalityFinite.w (bornProb ρ E) ω

variable (ρ : Matrix (Fin d) (Fin d) ℂ) (E : Fin m → Matrix (Fin d) (Fin d) ℂ)

@[simp] theorem bornMeasure_empty :
    bornMeasure ρ E (∅ : Finset (Fin n → Fin m)) = 0 := by
  rw [bornMeasure, Finset.sum_empty]

theorem bornMeasure_singleton (ω : Fin n → Fin m) :
    bornMeasure ρ E {ω} = BornTypicalityFinite.w (bornProb ρ E) ω := by
  rw [bornMeasure, Finset.sum_singleton]

/-- **Finite additivity** of the product Born measure on disjoint (insert) events. -/
theorem bornMeasure_insert (a : Fin n → Fin m) (S : Finset (Fin n → Fin m)) (ha : a ∉ S) :
    bornMeasure ρ E (insert a S) = bornMeasure ρ E {a} + bornMeasure ρ E S := by
  rw [bornMeasure, bornMeasure, bornMeasure, Finset.sum_insert ha, Finset.sum_singleton]

/-- **Normalization:** `λ(Ω) = 1` (the single-history weights sum to one, from
    `∑ₖ tr(ρ Eₖ) = 1`). -/
theorem bornMeasure_univ (hp1 : ∑ k, bornProb ρ E k = 1) :
    bornMeasure ρ E (univ : Finset (Fin n → Fin m)) = 1 :=
  BornTypicalityFinite.sum_w_eq_one (bornProb ρ E) hp1

/-- **λ equals the trace functional** `tr(ρ^⊗ⁿ · F_S)` for a Hermitian state and
    Hermitian effects (Born weights real). -/
theorem bornMeasure_eq_trace (hρ : ρ.IsHermitian) (hE : ∀ k, (E k).IsHermitian)
    (S : Finset (Fin n → Fin m)) :
    bornMeasure ρ E S
      = (kronN (fun _ : Fin n => ρ) * eventEffect E S).trace.re := by
  rw [trace_eventEffect_eq_sum,
    Finset.sum_congr rfl (fun ω _ => quantumWeight_eq_w ρ E hρ hE ω),
    ← Complex.ofReal_sum, Complex.ofReal_re]
  rfl

/-- **The product-history effects form a POVM:** `∑_ω ⊗ₜ E(ωₜ) = 1` on the n-fold
    product space, from completeness `∑ₖ Eₖ = 1` of the single-trial POVM.  (Same
    product/sum interchange — `Finset.prod_univ_sum` — that makes the product weights
    a probability distribution.) -/
theorem eventEffect_univ (hEsum : ∑ k, E k = 1) :
    eventEffect E (univ : Finset (Fin n → Fin m))
      = (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) := by
  ext x y
  rw [eventEffect, Matrix.sum_apply]
  simp only [kronN]
  rw [show (univ : Finset (Fin n → Fin m))
        = Fintype.piFinset (fun _ : Fin n => (univ : Finset (Fin m))) from
      (Fintype.piFinset_univ).symm,
    ← Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset (Fin m)))
      (fun t k => E k (x t) (y t))]
  have hentry : ∀ t : Fin n,
      (∑ k, E k (x t) (y t)) = (1 : Matrix (Fin d) (Fin d) ℂ) (x t) (y t) := by
    intro t
    have h := congrFun (congrFun hEsum (x t)) (y t)
    rwa [Matrix.sum_apply] at h
  rw [Finset.prod_congr rfl (fun t _ => hentry t)]
  simp only [Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    obtain ⟨t0, ht0⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (mem_univ t0) (if_neg ht0)

/-- **Determination backbone.**  Two finitely-additive real measures on history
    events that agree on every singleton are equal.  (Induction on the event.) -/
theorem measure_unique_of_additive (μ ν : Finset (Fin n → Fin m) → ℝ)
    (hμ0 : μ ∅ = 0) (hν0 : ν ∅ = 0)
    (hμins : ∀ a (S : Finset (Fin n → Fin m)), a ∉ S → μ (insert a S) = μ {a} + μ S)
    (hνins : ∀ a (S : Finset (Fin n → Fin m)), a ∉ S → ν (insert a S) = ν {a} + ν S)
    (hpt : ∀ a, μ {a} = ν {a}) :
    ∀ S, μ S = ν S := by
  intro S
  induction S using Finset.induction with
  | empty => rw [hμ0, hν0]
  | insert a S ha ih => rw [hμins a S ha, hνins a S ha, hpt a, ih]

/-- **λ-identification (the conceptual prize).**  For a genuine density matrix `ρ`
    (PSD, unit trace) and a POVM `E` (PSD effects, `∑ Eₖ = 1`), ANY finitely-additive
    measure `μ` on `n`-history events whose single-history weights are the product
    Born weights `∏ₜ tr(ρ E_{ωₜ})` MUST equal the trace functional `tr(ρ^⊗ⁿ · F_S)`.

    Thus the QIQT-H selector measure on product histories is not a free choice: it is
    the unique additive measure carrying the Born marginals, and it is exactly the
    Born/trace functional on the product-history POVM (`eventEffect_univ`: `∑_ω F_ω = 1`).
    Combined with single-trial Gleason uniqueness, the entire n-trial Born measure is
    forced once the single-trial Born rule is. -/
theorem product_born_measure_unique
    (hρ : ρ.PosSemidef) (hE : ∀ k, (E k).PosSemidef)
    (μ : Finset (Fin n → Fin m) → ℝ)
    (hμ0 : μ ∅ = 0)
    (hμins : ∀ a (S : Finset (Fin n → Fin m)), a ∉ S → μ (insert a S) = μ {a} + μ S)
    (hpt : ∀ ω, μ {ω} = ∏ t, bornProb ρ E (ω t)) :
    ∀ S, μ S = (kronN (fun _ : Fin n => ρ) * eventEffect E S).trace.re := by
  have hμ : ∀ S, μ S = bornMeasure ρ E S := by
    refine measure_unique_of_additive μ (bornMeasure ρ E) hμ0
      (bornMeasure_empty ρ E) hμins
      (fun a S ha => bornMeasure_insert ρ E a S ha) ?_
    intro a
    rw [hpt a, bornMeasure_singleton]
    rfl
  intro S
  rw [hμ S]
  exact bornMeasure_eq_trace ρ E hρ.1 (fun k => (hE k).1) S

/-- **Non-vacuity witness.**  The product Born measure ITSELF satisfies the
    hypotheses of `product_born_measure_unique` (additivity + Born product marginals),
    so that uniqueness theorem is inhabited, not vacuously true.  (Guards the
    "trivially-satisfiable hypothesis" soundness shape.) -/
theorem bornMeasure_satisfies_hyps :
    bornMeasure ρ E (∅ : Finset (Fin n → Fin m)) = 0
      ∧ (∀ a (S : Finset (Fin n → Fin m)), a ∉ S →
          bornMeasure ρ E (insert a S) = bornMeasure ρ E {a} + bornMeasure ρ E S)
      ∧ (∀ ω : Fin n → Fin m, bornMeasure ρ E {ω} = ∏ t, bornProb ρ E (ω t)) :=
  ⟨bornMeasure_empty ρ E, fun a S ha => bornMeasure_insert ρ E a S ha,
    fun ω => bornMeasure_singleton ρ E ω⟩

end BornMeasureUniqueness
end QIQTH
