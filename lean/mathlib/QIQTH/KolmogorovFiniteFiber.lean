/-
  XL-step Phase A, **A2b** — the general (correlated/entangled) Kolmogorov extension for
  FINITE-FIBER projective families.  This closes the one remaining crux: a Kolmogorov-consistent
  family of finite-stage probability measures on FINITE discrete outcome spaces extends to a genuine
  σ-additive probability measure μ∞ on the full history space (the projective limit), WITHOUT any
  independence/product assumption — so it covers correlated/entangled histories.

  The single analytic input is `projectiveFamilyContent_tendsto_zero`: an antitone sequence of
  measurable cylinders with empty intersection has content → 0.  For finite discrete fibers the full
  product `∀ i, α i` is COMPACT (Tychonoff) and each measurable cylinder is CLOSED (discrete fibers ⇒
  every base set is clopen, pulled back along the continuous restriction), so by the finite-
  intersection property an antitone sequence of cylinders with empty intersection is EVENTUALLY EMPTY,
  whence the content is eventually `0`.  This is the finite-fiber analog of Mathlib's
  `piContent_tendsto_zero` for the product case, but with no product/independence assumption.

  Feeding this through Mathlib's `addContent_iUnion_eq_sum_of_tendsto_zero` →
  `isSigmaSubadditive_of_addContent_iUnion_eq_tsum` → `AddContent.measure` yields `kolmogorovMeasure`,
  and `kolmogorovMeasure_isProjectiveLimit` proves it is the projective limit.  The headline
  `FiniteMarginals.exists_isLimit` then gives EXISTENCE of the typicality measure μ∞ for ANY finite-
  fiber `FiniteMarginals` family (combined with `limit_unique`: unique).

  Axiom-free: depends only on `propext, Classical.choice, Quot.sound`.
-/
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import QIQTH.FiniteMarginals
import Mathlib.Tactic

namespace QIQTH.KolmogorovFiniteFiber

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)]
  [∀ i, Finite (α i)]
  {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

/-- With discrete fibers, every measurable cylinder is topologically closed (its base is clopen and
    restriction is continuous). -/
theorem isClosed_of_mem_measurableCylinders {t : Set (∀ i, α i)}
    (ht : t ∈ measurableCylinders α) : IsClosed t := by
  obtain ⟨I, S, _, rfl⟩ := (mem_measurableCylinders t).mp ht
  rw [cylinder]
  exact (isClosed_discrete S).preimage (Finset.continuous_restrict I)

/-- In a compact space, an antitone sequence of closed sets with empty intersection is eventually
    empty (finite-intersection property). -/
theorem exists_eq_empty_of_antitone_isClosed_iInter_empty {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {t : ℕ → Set X} (htd : ∀ i, t (i + 1) ⊆ t i) (htcl : ∀ i, IsClosed (t i))
    (hempty : ⋂ i, t i = ∅) : ∃ N, t N = ∅ := by
  by_contra h
  push_neg at h
  have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    t htd h (htcl 0).isCompact htcl
  rw [hempty] at hne
  exact Set.not_nonempty_empty hne

/-- **The analytic crux (A2b).**  An antitone sequence of measurable cylinders with empty
    intersection has projective-family content tending to `0` — proved from compactness of the
    finite-fiber product (no independence assumption). -/
theorem projectiveFamilyContent_tendsto_zero [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) {s : ℕ → Set (∀ i, α i)}
    (hs : ∀ n, s n ∈ measurableCylinders α) (hanti : Antitone s) (hempty : ⋂ n, s n = ∅) :
    Tendsto (fun n => projectiveFamilyContent hP (s n)) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_eq_empty_of_antitone_isClosed_iInter_empty
    (fun i => hanti (Nat.le_succ i)) (fun i => isClosed_of_mem_measurableCylinders (hs i)) hempty
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Set.subset_eq_empty (hanti hn) hN, addContent_empty]

/-- The projective-family content of a finite-fiber projective family is σ-subadditive. -/
theorem isSigmaSubadditive_projectiveFamilyContent [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    (projectiveFamilyContent hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum isSetRing_measurableCylinders
    (fun f hf hUf hdisj => ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders _
    (fun _ _ => projectiveFamilyContent_ne_top hP)
    (fun _ hs hanti hempty => projectiveFamilyContent_tendsto_zero hP hs hanti hempty)
    hf hUf hdisj

/-- **The Kolmogorov-extension measure** of a finite-fiber projective family: the σ-additive measure
    on the full history space `∀ i, α i` extending the cylinder content. -/
noncomputable def kolmogorovMeasure [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P) :
    Measure (∀ i, α i) :=
  (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.symm.le (isSigmaSubadditive_projectiveFamilyContent hP)

/-- The Kolmogorov measure agrees with the content (hence with `P I`) on cylinders. -/
theorem kolmogorovMeasure_cylinder [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P)
    {I : Finset ι} {S : Set (∀ i : I, α i)} (hS : MeasurableSet S) :
    kolmogorovMeasure hP (cylinder I S) = projectiveFamilyContent hP (cylinder I S) :=
  AddContent.measure_eq _ isSetSemiring_measurableCylinders generateFrom_measurableCylinders.symm
    (isSigmaSubadditive_projectiveFamilyContent hP) (cylinder_mem_measurableCylinders I S hS)

/-- **A2b — EXISTENCE: the Kolmogorov measure is the projective limit.**  For a finite-fiber
    projective family (any consistency, no product assumption), `kolmogorovMeasure` restricts to `P I`
    at every finite context. -/
theorem kolmogorovMeasure_isProjectiveLimit [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) : IsProjectiveLimit (kolmogorovMeasure hP) P := by
  intro I
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply (Finset.measurable_restrict I) hS]
  show kolmogorovMeasure hP (cylinder I S) = P I S
  rw [kolmogorovMeasure_cylinder hP hS, projectiveFamilyContent_cylinder hP hS]

/-- **A2b headline: existence of the continuum typicality measure for any finite-fiber family.**
    Every finite-fiber `FiniteMarginals` family has a (unique, by `limit_unique`) σ-additive
    probability measure μ∞ on the history space realizing it as the projective limit — the
    correlated/entangled case, with NO independence assumption. -/
theorem exists_isLimit (F : QIQTH.HistoryMeasure.FiniteMarginals α) :
    ∃ μ : Measure (∀ i, α i), IsProbabilityMeasure μ ∧ F.IsLimit μ := by
  haveI : ∀ J, IsProbabilityMeasure (F.μ J) := F.isProb
  haveI : ∀ J, IsFiniteMeasure (F.μ J) := fun J => inferInstance
  exact ⟨kolmogorovMeasure F.proj,
    (kolmogorovMeasure_isProjectiveLimit F.proj).isProbabilityMeasure,
    kolmogorovMeasure_isProjectiveLimit F.proj⟩

end QIQTH.KolmogorovFiniteFiber
