/-
  RNCGaugeExp — grounding the abstract RNC-gauge core in the exp map's ACTUAL value-3-jet.

  RNCGauge builds the symmetrized normal-coordinate gauge `GaugeJet (rncDΓ Γ dΓ1)` for an ABSTRACT
  Christoffel array `Γ` and first-derivative array `dΓ1`.  Its honest gap (see the `rncGaugeJet`
  docstring) was: it did NOT yet connect the raw coefficient array `a3rawArr` to the exp map's genuine
  value-3-jet cubic `a₃` from `QIQTH.ExpMap.expMap_value_three_jet`.

  This file discharges exactly that connection (fact B).  `a3rawArr_contract_eq_a3` proves that
  `a3rawArr`, specialized to the true Christoffel jet
    `Γ i j k := christoffel g gi i j k p`,   `dΓ1 l i j k := pd (christoffel g gi i j k) l p`,
  contracts (over the lower triple against `v`) to EXACTLY the inlined cubic coefficient `a₃(v)_i` of
  `expMap_value_three_jet`.  This is pure `Finset` algebra (index reindexing + commutativity); it needs
  no Christoffel symmetry.

  With this, `exp_rncGaugeJet` records that `rncGaugeJet` now concerns the GENUINE exp-derived formal
  Christoffel jet, not merely an abstract array.

  HONEST scope: this grounds `rncDΓ` in the exp map's value-3-jet `a₃`.  It does NOT reach κ = 1/6 for
  the pullback metric — that needs the bridge `rncDΓ = pd(christoffel g̃)(0)` together with
  `ContDiff exp_p` to define g̃ (the cited smooth-dependence frontier), and it is NOT numerical-`G`.
-/
import Mathlib
import QIQTH.RNCGauge
import QIQTH.ExpMap

namespace QIQTH.RNCGaugeExp

open QIQTH.RNCGauge QIQTH.Curvature
open scoped BigOperators

variable {n : ℕ}

/-- **christSqA reindex.**  The `christSqA`-block contraction reindexes to the `a₃` term A shape.
    Pure `Finset` reordering: `l,j,k,a ↦ a,k,l,j`. -/
private lemma reindex_A (C : Fin n → Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (∑ l, ∑ j, ∑ k, (∑ a, C i a k * C a l j) * v l * v j * v k)
      = ∑ j, ∑ k, C i j k * (∑ a, ∑ b, C j a b * v a * v b) * v k := by
  have hL : (∑ l, ∑ j, ∑ k, (∑ a, C i a k * C a l j) * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, ∑ a, C i a k * C a l j * v l * v j * v k := by
    simp only [Finset.sum_mul]
  have hR : (∑ j, ∑ k, C i j k * (∑ a, ∑ b, C j a b * v a * v b) * v k)
      = ∑ j, ∑ k, ∑ a, ∑ b, C i j k * C j a b * v a * v b * v k := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hL, hR]
  calc (∑ l, ∑ j, ∑ k, ∑ a, C i a k * C a l j * v l * v j * v k)
      = ∑ l, ∑ j, ∑ a, ∑ k, C i a k * C a l j * v l * v j * v k :=
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ j, ∑ k, C i a k * C a l j * v l * v j * v k :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ a, ∑ l, ∑ j, ∑ k, C i a k * C a l j * v l * v j * v k := Finset.sum_comm
    _ = ∑ a, ∑ l, ∑ k, ∑ j, C i a k * C a l j * v l * v j * v k :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ a, ∑ k, ∑ l, ∑ j, C i a k * C a l j * v l * v j * v k :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ a, ∑ b, C i j k * C j a b * v a * v b * v k := rfl

/-- **christSqB reindex.**  The `christSqB`-block contraction reindexes to the `a₃` term B shape.
    Pure `Finset` reordering: `l,j,k,a ↦ j,a,l,k`. -/
private lemma reindex_B (C : Fin n → Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (∑ l, ∑ j, ∑ k, (∑ a, C i j a * C a l k) * v l * v j * v k)
      = ∑ j, ∑ k, C i j k * v j * (∑ a, ∑ b, C k a b * v a * v b) := by
  have hL : (∑ l, ∑ j, ∑ k, (∑ a, C i j a * C a l k) * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, ∑ a, C i j a * C a l k * v l * v j * v k := by
    simp only [Finset.sum_mul]
  have hR : (∑ j, ∑ k, C i j k * v j * (∑ a, ∑ b, C k a b * v a * v b))
      = ∑ j, ∑ k, ∑ a, ∑ b, C i j k * C k a b * v a * v j * v b := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hL, hR]
  calc (∑ l, ∑ j, ∑ k, ∑ a, C i j a * C a l k * v l * v j * v k)
      = ∑ j, ∑ l, ∑ k, ∑ a, C i j a * C a l k * v l * v j * v k := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ a, ∑ k, C i j a * C a l k * v l * v j * v k :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ l, ∑ k, C i j a * C a l k * v l * v j * v k :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ a, ∑ b, C i j k * C k a b * v a * v j * v b := rfl

/-- **Fact B: `a3rawArr` grounds the exp map's value-3-jet cubic `a₃`.**

    The abstract raw cubic coefficient `a3rawArr`, specialized to the TRUE Christoffel jet
    `Γ i j k := christoffel g gi i j k p` and `dΓ1 l i j k := pd (christoffel g gi i j k) l p`,
    contracts (over the lower triple `l,j,k` against `v`) to EXACTLY the inlined cubic coefficient
    `a₃(v)_i` appearing in `QIQTH.ExpMap.expMap_value_three_jet` (the `(1/6) • …` term).

    Pure `Finset` algebra: the `∂Γ` block reindexes by `sum_comm`; the two `ΓΓ` blocks reindex to the
    `a₃` term-A / term-B shapes (`reindex_A`, `reindex_B`).  No Christoffel symmetry is used. -/
theorem a3rawArr_contract_eq_a3 (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (v : Point n)
    (i : Fin n) :
    (∑ l, ∑ j, ∑ k,
        a3rawArr (fun i j k => christoffel g gi i j k p)
                 (fun l i j k => pd (fun z => christoffel g gi i j k z) l p) i l j k
          * v l * v j * v k)
      = -(∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l)
        + (∑ j, ∑ k, christoffel g gi i j k p
              * (∑ a, ∑ b, christoffel g gi j a b p * v a * v b) * v k)
        + (∑ j, ∑ k, christoffel g gi i j k p
              * v j * (∑ a, ∑ b, christoffel g gi k a b p * v a * v b)) := by
  -- Pointwise split of the raw coefficient into ∂Γ, ΓΓ-A, ΓΓ-B pieces.
  have hpt : ∀ l j k : Fin n,
      a3rawArr (fun i j k => christoffel g gi i j k p)
               (fun l i j k => pd (fun z => christoffel g gi i j k z) l p) i l j k
        * v l * v j * v k
      = -(pd (fun z => christoffel g gi i j k z) l p) * v l * v j * v k
        + (∑ a, christoffel g gi i a k p * christoffel g gi a l j p) * v l * v j * v k
        + (∑ a, christoffel g gi i j a p * christoffel g gi a l k p) * v l * v j * v k := by
    intro l j k
    simp only [a3rawArr, christSqA, christSqB]
    ring
  simp only [hpt, Finset.sum_add_distrib]
  -- ∂Γ block: reorder + factor out the negation.
  have hDelta : (∑ l, ∑ j, ∑ k, -(pd (fun z => christoffel g gi i j k z) l p) * v l * v j * v k)
      = -(∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l) := by
    have hcomm : (∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l)
        = ∑ l, ∑ j, ∑ k, pd (fun z => christoffel g gi i j k z) l p * v l * v j * v k := by
      rw [show (∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l)
            = ∑ j, ∑ l, ∑ k, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l from
          Finset.sum_congr rfl fun j _ => Finset.sum_comm]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => by ring
    rw [hcomm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- ΓΓ blocks: reindex via the two helper lemmas (beta-reduce the specialization first).
  have hA := reindex_A (fun x y z => christoffel g gi x y z p) v i
  have hB := reindex_B (fun x y z => christoffel g gi x y z p) v i
  simp only [] at hA hB
  rw [hDelta, hA, hB]

/-- **The grounded capstone.**  The formal RNC-Christoffel linear jet `rncDΓ`, built from the exp map's
    ACTUAL value-3-jet data (Christoffel values `christoffel g gi · · · p` and their first derivatives
    `pd (christoffel g gi · · ·) · p`), satisfies the symmetrized normal-coordinate gauge `GaugeJet`.

    This is `rncGaugeJet` specialized to the genuine exp-derived jet.  Together with
    `a3rawArr_contract_eq_a3` — which grounds `a3rawArr` in the exp map's honest cubic `a₃` from
    `expMap_value_three_jet` — the gauge statement now concerns the real exp-map 3-jet, not an abstract
    array.

    HONEST scope: this does NOT reach κ = 1/6 for the pullback metric (that requires the bridge
    `rncDΓ = pd(christoffel g̃)(0)` plus `ContDiff exp_p` to define g̃ — the cited smooth-dependence
    frontier), and it is NOT numerical-`G`. -/
theorem exp_rncGaugeJet (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) :
    GaugeJet (rncDΓ (fun i j k => christoffel g gi i j k p)
                    (fun l i j k => pd (fun z => christoffel g gi i j k z) l p)) :=
  rncGaugeJet _ _

end QIQTH.RNCGaugeExp
