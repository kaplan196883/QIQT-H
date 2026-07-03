/-
  THE TOWER T5 (THE_TOWER_PLAN.md) — the state limit: the σ-additive infinite-mode Gibbs measure.

  The classical (diagonal) limit object of the code tower: the single-mode Boltzmann measures
  assemble — through the HELD product/Kolmogorov infrastructure (`Measure.infinitePi`,
  `productMarginals`, `FiniteMarginals.limit_unique`) — into the unique σ-additive probability
  measure on the infinite occupation-configuration space whose finite marginals ARE the code's
  own DY Gibbs weights (the T5 capstone adapter: singleton marginal = `ENNReal.ofReal gibbsWeight`).

  ⚠ HONEST SCOPE (binding verdict): this is the CLASSICAL measure on occupation configurations —
  the correct limit object. NO quantum state on the infinite system is constructed (T6 proves the
  measure is non-atomic under a frequency bound, so no diagonal density/diagState reading exists —
  that reading is FALSE, not deferred; the GNS/ITPFI quantum limit is cited Phase-B material).
-/
import Mathlib
import QIQTH.Tower.AWFingerprint
import QIQTH.FiniteMarginals
import QIQTH.Dynamics

namespace QIQTH.Tower

open MeasureTheory QIQTH.Decoupling

variable {M : Type*}

/-- **The single-mode Boltzmann probability measure** on `Fin D` with weights `gibbsEigen`. -/
noncomputable def boltzMeasure (D : ℕ) (x : ℝ) : Measure (Fin D) :=
  ∑ i, ENNReal.ofReal (gibbsEigen D x i) • Measure.dirac i

theorem boltzMeasure_singleton (D : ℕ) (x : ℝ) (i : Fin D) :
    boltzMeasure D x {i} = ENNReal.ofReal (gibbsEigen D x i) := by
  classical
  rw [boltzMeasure, Measure.finset_sum_apply]
  rw [Finset.sum_eq_single i ?h0 ?h1]
  · rw [Measure.smul_apply, Measure.dirac_apply' i (measurableSet_singleton i)]
    simp
  case h0 =>
    intro j _ hj
    rw [Measure.smul_apply, Measure.dirac_apply' j (measurableSet_singleton i)]
    simp [Set.indicator, hj]
  case h1 =>
    intro h
    exact absurd (Finset.mem_univ i) h

instance boltzMeasure_isProb (D : ℕ) [NeZero D] (x : ℝ) :
    IsProbabilityMeasure (boltzMeasure D x) := by
  constructor
  rw [boltzMeasure, Measure.finset_sum_apply]
  have hD : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  calc ∑ i : Fin D, (ENNReal.ofReal (gibbsEigen D x i) • Measure.dirac i) Set.univ
      = ∑ i : Fin D, ENNReal.ofReal (gibbsEigen D x i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    _ = ENNReal.ofReal (∑ i : Fin D, gibbsEigen D x i) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => (gibbsEigen_pos hD x i).le).symm
    _ = 1 := by rw [sum_gibbsEigen hD x, ENNReal.ofReal_one]

/-- **THE INFINITE-MODE GIBBS MEASURE**: the σ-additive probability measure on the occupation
    configuration space `∀ k, Fin (D_k)`, via the held `Measure.infinitePi`. -/
noncomputable def gibbsLimitMeasure (Dv : M → ℕ) [∀ k, NeZero (Dv k)] (x : M → ℝ) :
    Measure (∀ k, Fin (Dv k)) :=
  Measure.infinitePi (fun k => boltzMeasure (Dv k) (x k))

/-- The limit realizes the product marginal family (the held Kolmogorov/product machinery). -/
theorem gibbsLimitMeasure_isProjectiveLimit (Dv : M → ℕ) [∀ k, NeZero (Dv k)] (x : M → ℝ) :
    (QIQTH.HistoryMeasure.productMarginals
        (fun k => boltzMeasure (Dv k) (x k))).IsLimit (gibbsLimitMeasure Dv x) :=
  QIQTH.HistoryMeasure.productMarginals_isProjectiveLimit _

/-- **Uniqueness**: any measure realizing the Gibbs marginal family IS the limit measure. -/
theorem gibbsLimitMeasure_unique (Dv : M → ℕ) [∀ k, NeZero (Dv k)] (x : M → ℝ)
    {μ : Measure (∀ k, Fin (Dv k))}
    (hμ : (QIQTH.HistoryMeasure.productMarginals
      (fun k => boltzMeasure (Dv k) (x k))).IsLimit μ) :
    μ = gibbsLimitMeasure Dv x :=
  QIQTH.HistoryMeasure.FiniteMarginals.limit_unique _ hμ
    (gibbsLimitMeasure_isProjectiveLimit Dv x)

instance (Dv : M → ℕ) [∀ k, NeZero (Dv k)] (x : M → ℝ) :
    IsProbabilityMeasure (gibbsLimitMeasure Dv x) :=
  QIQTH.HistoryMeasure.productMarginals_isProbabilityMeasure _

/-- **The DY bridge**: the code's per-mode Boltzmann weight IS the tower eigenvalue list at
    `x = βω` (the DS2 partition-function bridge closes the parametrizations). -/
theorem pMode_eq_gibbsEigen (L : QIQTH.Keystone.LinkDims M) (ω : M → ℝ) (β : ℝ) (k : M)
    (i : Fin (L.D k)) :
    QIQTH.Dynamics.pMode L ω β k i = gibbsEigen (L.D k) (β * ω k) i := by
  rw [QIQTH.Dynamics.pMode, gibbsEigen, QIQTH.Decoupling.ZMode_eq_Zgeom]

/-- **T5 CAPSTONE — the finite marginals of the infinite-mode Gibbs measure ARE the code's own
    Gibbs weights**: the singleton marginal at every occupation `n` of every finite mode set `C`
    equals `ENNReal.ofReal (gibbsWeight n)` — the σ-additive limit object restricts to exactly the
    held DY2/DY4 thermal data (DY4's marginal consistency is what makes the family projective). -/
theorem gibbsLimit_marginal_singleton [DecidableEq M] (L : QIQTH.Keystone.LinkDims M)
    [∀ k, NeZero (L.D k)] (ω : M → ℝ) (β : ℝ) (C : Finset M)
    (n : QIQTH.Keystone.Micro L C) :
    (QIQTH.HistoryMeasure.productMarginals
        (fun k => boltzMeasure (L.D k) (β * ω k))).μ C {n}
      = ENNReal.ofReal (QIQTH.Dynamics.gibbsWeight L C ω β n) := by
  classical
  have hset : ({n} : Set (∀ j : C, Fin (L.D j))) = Set.pi Set.univ (fun j => {n j}) := by
    ext m
    simp [funext_iff, Set.mem_pi]
  rw [show (QIQTH.HistoryMeasure.productMarginals
        (fun k => boltzMeasure (L.D k) (β * ω k))).μ C
      = Measure.pi (fun j : C => boltzMeasure (L.D j) (β * ω j)) from rfl,
    hset, Measure.pi_pi]
  rw [Finset.prod_congr rfl fun j _ => boltzMeasure_singleton (L.D j.val) (β * ω j.val) (n j)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    (gibbsEigen_pos (Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)) _ _).le)]
  congr 1
  rw [QIQTH.Dynamics.gibbsWeight]
  exact Finset.prod_congr rfl fun j _ => (pMode_eq_gibbsEigen L ω β j.val (n j)).symm

end QIQTH.Tower
