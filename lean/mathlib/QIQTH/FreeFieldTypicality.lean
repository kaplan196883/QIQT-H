/-
  Toward the prize — the FREE-FIELD (finite-mode) covariant typicality measure.

  The continuum relativistic prize needs Fock space / CCR / quasifree states (a multi-year build;
  Mathlib has none).  This module delivers the genuine FINITE-MODE (Type I) free-field instance of the
  proven covariant-μ machinery: outcomes are occupation **sectors** `m → Bool` over a finite set `m`
  of modes (= `FreeFieldRecord.Sector`), the state is any boost-invariant per-region measure `ν`, and
  the **boost** (mode permutation `e : m ≃ m`, the finite-mode shadow of a Lorentz boost,
  `FreeFieldRecord.boost`) acts on histories.

  Results (axiom-free): `freeFieldMeasure` — the σ-additive i.i.d. free-field history typicality measure
  via Mathlib's Kolmogorov extension; `freeFieldMeasure_marginal` (Born marginal at every finite set of
  regions); and **`freeFieldMeasure_boost_invariant`** — the typicality measure is INVARIANT under the
  (geometry-moving) boost when the per-region state is boost-invariant, i.e. genuine covariance of μ∞
  under a real symmetry, instantiated by field structure.

  HONEST SCOPE: this is the finite-mode (Type I) free field — a legitimate physical model, NOT the
  continuum (Type III₁) prize, which requires the Fock/CCR/quasifree infrastructure as a separate
  multi-year program.  What is demonstrated is the covariant-μ pipeline running on genuine free-field
  occupation sectors with a real boost symmetry.  Axiom-free.
-/
import QIQTH.FiniteMarginals
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace QIQTH.FreeFieldTypicality

open MeasureTheory
open QIQTH.HistoryMeasure

variable {m : Type*} [Fintype m] [DecidableEq m] {ν : Measure (m → Bool)} [IsProbabilityMeasure ν]

/-- The **boost** acting on an occupation sector by permuting modes: `(boostMap e s) i = s (e i)`
    (= `FreeFieldRecord.boost`).  A measurable bijection of the sector space. -/
def boostMap (e : m ≃ m) (s : m → Bool) : m → Bool := fun i => s (e i)

theorem measurable_boostMap (e : m ≃ m) : Measurable (boostMap e) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (e i)

/-- The diagonal boost on the history space (apply the boost in every region). -/
def diagBoost (e : m ≃ m) (h : ℕ → (m → Bool)) : ℕ → (m → Bool) := fun t => boostMap e (h t)

theorem measurable_diagBoost (e : m ≃ m) : Measurable (diagBoost e) :=
  measurable_pi_lambda _ fun t => (measurable_boostMap e).comp (measurable_pi_apply t)

/-- **The free-field (finite-mode) typicality measure**: the σ-additive i.i.d. history measure with a
    boost-invariant per-region state `ν` on occupation sectors `m → Bool`. -/
noncomputable def freeFieldMeasure (ν : Measure (m → Bool)) [IsProbabilityMeasure ν] :
    Measure (ℕ → (m → Bool)) :=
  Measure.infinitePi (fun _ : ℕ => ν)

instance : IsProbabilityMeasure (freeFieldMeasure ν) := by
  unfold freeFieldMeasure; infer_instance

/-- The free-field measure restricts to the product Born marginal at every finite set of regions. -/
theorem freeFieldMeasure_marginal (J : Finset ℕ) :
    (freeFieldMeasure ν).map J.restrict = Measure.pi (fun _ : J => ν) :=
  Measure.infinitePi_map_restrict _

/-- **Boost-covariance of the typicality measure.**  If the per-region state is invariant under the
    boost (`ν.map (boostMap e) = ν`), then the free-field typicality measure μ∞ is invariant under the
    diagonal boost: `μ∞.map (diagBoost e) = μ∞`.  Covariance of the typicality measure under a genuine
    geometry-moving symmetry, instantiated by the free-field mode-permutation boost. -/
theorem freeFieldMeasure_boost_invariant (e : m ≃ m) (hν : ν.map (boostMap e) = ν) :
    (freeFieldMeasure ν).map (diagBoost e) = freeFieldMeasure ν := by
  refine isLimit_map_eq (productMarginals_isProjectiveLimit (fun _ : ℕ => ν)) ?_
  intro J
  show ((freeFieldMeasure ν).map (diagBoost e)).map J.restrict = Measure.pi (fun _ : J => ν)
  have hcoordB : Measurable (fun g : (∀ j : J, m → Bool) => fun j => boostMap e (g j)) :=
    measurable_pi_lambda _ fun j => (measurable_boostMap e).comp (measurable_pi_apply j)
  haveI : ∀ _ : J, SigmaFinite (ν.map (boostMap e)) := fun _ => by rw [hν]; infer_instance
  rw [Measure.map_map (Finset.measurable_restrict J) (measurable_diagBoost e),
    show J.restrict ∘ diagBoost e
        = (fun g : (∀ j : J, m → Bool) => fun j => boostMap e (g j)) ∘ J.restrict from rfl,
    ← Measure.map_map hcoordB (Finset.measurable_restrict J),
    show (freeFieldMeasure ν).map J.restrict = Measure.pi (fun _ : J => ν) from
      freeFieldMeasure_marginal J,
    Measure.pi_map_pi (fun _ : J => (measurable_boostMap e).aemeasurable), hν]

end QIQTH.FreeFieldTypicality
