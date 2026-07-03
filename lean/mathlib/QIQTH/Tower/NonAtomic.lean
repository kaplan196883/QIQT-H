/-
  THE TOWER T6 (THE_TOWER_PLAN.md) — non-atomicity: the quantum reading of the limit is FALSE.

  Under a uniform frequency bound `0 ≤ x_k ≤ b` and cutoffs `D_k ≥ 2`, EVERY singleton of the
  infinite-mode Gibbs measure has measure ZERO (the cylinder squeeze: every configuration is
  contained in cylinders of mass ≤ c^N with c = 1/(1+e^{−b}) < 1). Hence the measure has NO atoms —
  and therefore NO diagonal-density ("diagState") reading of the limit exists: the quantum reading
  of the T5 limit object is FALSE (binding verdict), not deferred.

  ⚠ THE VACUUM-ATOM DICHOTOMY (cited, not proved): the uniform bound is LOAD-BEARING. If the
  frequencies grow so fast that ∑_k e^{−x_k} < ∞, the product measure DOES have an atom — the
  vacuum configuration carries mass ∏_k Z_k⁻¹ > 0 (a Kakutani-type product dichotomy; cf.
  Kakutani 1948, Araki–Woods 1968 §types I). No claim about that regime is made here; only the
  bounded-frequency non-atomicity is proved.
-/
import Mathlib
import QIQTH.Tower.GibbsLimit

namespace QIQTH.Tower

open MeasureTheory QIQTH.Decoupling
open scoped ENNReal

/-- With at least two levels the partition function dominates the first two terms: `1 + q ≤ Z`. -/
theorem one_add_le_Zgeom {D : ℕ} (hD : 2 ≤ D) {q : ℝ} (h0 : 0 ≤ q) :
    1 + q ≤ Zgeom D q := by
  rw [Zgeom]
  have hsub : Finset.range 2 ⊆ Finset.range D := by
    intro y hy
    rw [Finset.mem_range] at *
    omega
  have h2 : ∑ n ∈ Finset.range 2, q ^ n = 1 + q := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
  rw [← h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => pow_nonneg h0 n

/-- **The uniform eigenvalue ceiling**: with `D ≥ 2` levels and frequency `0 ≤ x ≤ b`, every
    Gibbs eigenvalue is at most `1/(1+e^{−b}) < 1` — the mass can never concentrate on one level. -/
theorem gibbsEigen_le_ceiling {D : ℕ} (hD : 2 ≤ D) {x b : ℝ} (hx0 : 0 ≤ x) (hxb : x ≤ b)
    (i : Fin D) :
    gibbsEigen D x i ≤ 1 / (1 + Real.exp (-b)) := by
  have hZpos : (0 : ℝ) < Zgeom D (Real.exp (-x)) := Zgeom_pos (by omega) (Real.exp_pos _).le
  have hbpos : (0 : ℝ) < 1 + Real.exp (-b) := by positivity
  rw [gibbsEigen, div_le_div_iff₀ hZpos hbpos]
  have hnum : Real.exp (-(x * i)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ x * i := mul_nonneg hx0 (Nat.cast_nonneg _)
    linarith
  have hexp : Real.exp (-b) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  have hZ : 1 + Real.exp (-b) ≤ Zgeom D (Real.exp (-x)) :=
    le_trans (by linarith) (one_add_le_Zgeom hD (Real.exp_pos _).le)
  nlinarith [Real.exp_pos (-(x * i)), Real.exp_pos (-b)]

/-- The ceiling is strictly below one. -/
theorem ceiling_lt_one (b : ℝ) : 1 / (1 + Real.exp (-b)) < 1 := by
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos (-b)]

/-- **T6 CAPSTONE — NON-ATOMICITY (the cylinder squeeze)**: under the uniform frequency bound
    `0 ≤ x_k ≤ b` and cutoffs `D_k ≥ 2`, EVERY singleton configuration of the infinite-mode Gibbs
    measure has measure ZERO — each configuration lies in the depth-`N` cylinder of mass
    `≤ (1/(1+e^{−b}))^N → 0`. Hence NO diagonal-density reading of the T5 limit exists: the
    quantum ("diagState") reading of the limit measure is FALSE (binding verdict), not deferred. -/
theorem gibbsLimitMeasure_singleton_eq_zero {D : ℕ → ℕ} [∀ k, NeZero (D k)] {x : ℕ → ℝ}
    {b : ℝ} (hD : ∀ k, 2 ≤ D k) (hx0 : ∀ k, 0 ≤ x k) (hxb : ∀ k, x k ≤ b)
    (n : ∀ k, Fin (D k)) :
    gibbsLimitMeasure D x {n} = 0 := by
  classical
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 + Real.exp (-b))) with hc
  have hc1 : c < 1 := by
    rw [hc, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff one_pos |>.mpr (ceiling_lt_one b)
  have hbound : ∀ N : ℕ, gibbsLimitMeasure D x {n} ≤ c ^ N := by
    intro N
    set J : Finset ℕ := Finset.range N with hJ
    have hmeas : Measurable (J.restrict (π := fun k => Fin (D k))) :=
      measurable_pi_lambda _ fun j => measurable_pi_apply _
    have hset : ({J.restrict n} : Set (∀ j : J, Fin (D j)))
        = Set.pi Set.univ (fun j : J => ({n j.val} : Set (Fin (D j.val)))) := by
      ext m
      simp [funext_iff, Set.mem_pi, Finset.restrict]
    have hsingle : MeasurableSet ({J.restrict n} : Set (∀ j : J, Fin (D j))) := by
      rw [hset]
      exact MeasurableSet.pi Set.countable_univ fun j _ => measurableSet_singleton _
    have hsub : ({n} : Set (∀ k, Fin (D k))) ⊆ J.restrict ⁻¹' {J.restrict n} := by
      intro m hm
      rw [Set.mem_singleton_iff] at hm
      subst hm
      exact rfl
    calc gibbsLimitMeasure D x {n}
        ≤ gibbsLimitMeasure D x (J.restrict ⁻¹' {J.restrict n}) := measure_mono hsub
      _ = (gibbsLimitMeasure D x).map J.restrict {J.restrict n} :=
          (Measure.map_apply hmeas hsingle).symm
      _ = (QIQTH.HistoryMeasure.productMarginals
            (fun k => boltzMeasure (D k) (x k))).μ J {J.restrict n} := by
          rw [gibbsLimitMeasure_isProjectiveLimit D x J]
      _ = ∏ j : J, ENNReal.ofReal (gibbsEigen (D j.val) (x j.val) (n j.val)) := by
          rw [show (QIQTH.HistoryMeasure.productMarginals
                (fun k => boltzMeasure (D k) (x k))).μ J
              = Measure.pi (fun j : J => boltzMeasure (D j) (x j)) from rfl,
            hset, Measure.pi_pi]
          exact Finset.prod_congr rfl fun j _ =>
            boltzMeasure_singleton (D j.val) (x j.val) (n j.val)
      _ ≤ ∏ _j : J, c :=
          Finset.prod_le_prod' fun j _ => ENNReal.ofReal_le_ofReal
            (gibbsEigen_le_ceiling (hD j.val) (hx0 j.val) (hxb j.val) (n j.val))
      _ = c ^ N := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, hJ, Finset.card_range]
  have hpow : Filter.Tendsto (fun N : ℕ => c ^ N) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc1
  have hle : gibbsLimitMeasure D x {n} ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hpow hbound
  exact le_zero_iff.mp hle

/-- **The measure has NO atoms** (the bundled Mathlib `NoAtoms` reading of the capstone): under
    the uniform frequency bound the infinite-mode Gibbs measure is non-atomic — no configuration
    carries positive mass, so no atomic/diagonal-state decomposition of the limit exists. -/
theorem gibbsLimitMeasure_noAtoms {D : ℕ → ℕ} [∀ k, NeZero (D k)] {x : ℕ → ℝ} {b : ℝ}
    (hD : ∀ k, 2 ≤ D k) (hx0 : ∀ k, 0 ≤ x k) (hxb : ∀ k, x k ≤ b) :
    NoAtoms (gibbsLimitMeasure D x) :=
  ⟨fun n => gibbsLimitMeasure_singleton_eq_zero hD hx0 hxb n⟩

end QIQTH.Tower
