import Mathlib

/-!
# Finite replica n→1 analytic continuation (brick G2 = input #2 of the DY7 conjecture)

## Scope firewall (honest, binding)

This file discharges **input #2 of the DY7 conjecture's five cited physical inputs
AT THE FINITE LEVEL**: the real-analytic replica / Rényi calculus underlying the
heuristic `S = −∂ₙ log Zₙ |ₙ₌₁`.

* **FINITE full-support probability spectrum only** (`p : ι → ℝ`, `∀ i, 0 < p i`,
  `∑ p = 1` — the record code's finite mode occupation). This is the finite
  spectral calculus AFTER one already has `Zₙ = Tr ρⁿ = ∑ pᵢⁿ`.
* It does **NOT** justify the physics load-bearing step: that the INTEGER-`n`
  geometric / orbifold replica path integrals pick out THIS analytic family
  (integer values alone do not determine a unique continuation — that
  identification stays CITED).
* Real-analytic finite calculus; **NOT** the conjecture; **NOT** the strong
  holographic principle; **NOT** quantum gravity. No axioms, no `sorry`.

Here `pᵢⁿ` is realized as `Real.exp (n * Real.log (p i))` (smoother than
fighting `Real.rpow`); on the full-support spectrum this equals the true power.

## Main results
* `replicaW_one` : `log Z₁ = 0` (normalization).
* `replicaW_hasDerivAt_one` : the replica free energy's slope at `n=1` is `∑ pᵢ log pᵢ`.
* `replica_entropy_hasDerivAt` / `entropy_eq_neg_deriv` : `S = −∂ₙ log Zₙ |ₙ₌₁`.
* `renyi_tendsto_shannon` : the Rényi `n→1` limit is the Shannon entropy.
* `finite_replica_continuation` : the capstone conjunction.
-/

open Filter Topology

namespace QIQTH.ReplicaContinuation

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The replica partition function `Zₙ = ∑ pᵢⁿ`, with `pᵢⁿ := exp(n·log pᵢ)`. -/
noncomputable def replicaZ (p : ι → ℝ) (n : ℝ) : ℝ := ∑ i, Real.exp (n * Real.log (p i))

/-- The replica free energy `Wₙ = log Zₙ`. -/
noncomputable def replicaW (p : ι → ℝ) (n : ℝ) : ℝ := Real.log (replicaZ p n)

/-- The Shannon entropy `S = −∑ pᵢ log pᵢ`. -/
noncomputable def shannon (p : ι → ℝ) : ℝ := - ∑ i, p i * Real.log (p i)

/-- The Rényi entropy `Sₙ = Wₙ / (1 − n)`. -/
noncomputable def renyi (p : ι → ℝ) (n : ℝ) : ℝ := replicaW p n / (1 - n)

section basic

variable {p : ι → ℝ}

/-- `replicaZ p n > 0`: a nonempty finite sum of positive exponentials. -/
theorem replicaZ_pos (n : ℝ) : 0 < replicaZ p n := by
  unfold replicaZ
  apply Finset.sum_pos
  · intro i _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

omit [Nonempty ι] in
/-- `replicaZ` is smooth in `n`: a finite sum of `n ↦ exp(n·log pᵢ)`. -/
theorem replicaZ_contDiff : ContDiff ℝ ⊤ (replicaZ p) := by
  show ContDiff ℝ ⊤ (fun n => ∑ i, Real.exp (n * Real.log (p i)))
  apply ContDiff.sum
  intro i _
  exact ((contDiff_id.mul contDiff_const).exp)

/-- `replicaW = log ∘ replicaZ` is smooth (positivity of `replicaZ`). -/
theorem replicaW_contDiff : ContDiff ℝ ⊤ (replicaW p) := by
  show ContDiff ℝ ⊤ (fun n => Real.log (replicaZ p n))
  rw [contDiff_iff_contDiffAt]
  intro n
  exact (Real.contDiffAt_log.2 (replicaZ_pos n).ne').comp n replicaZ_contDiff.contDiffAt

omit [Nonempty ι] in
/-- Normalization: `Z₁ = ∑ pᵢ = 1`. -/
theorem replicaZ_one (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) : replicaZ p 1 = 1 := by
  unfold replicaZ
  rw [show (∑ i, Real.exp (1 * Real.log (p i))) = ∑ i, p i from
    Finset.sum_congr rfl fun i _ => by rw [one_mul, Real.exp_log (hp i)], hsum]

omit [Nonempty ι] in
/-- Normalization: `W₁ = log Z₁ = 0`. -/
theorem replicaW_one (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) : replicaW p 1 = 0 := by
  rw [replicaW, replicaZ_one hp hsum, Real.log_one]

omit [Nonempty ι] in
/-- `replicaZ` has derivative `∑ pᵢⁿ · log pᵢ` at each `n`; at `n=1` this is `∑ pᵢ log pᵢ`. -/
theorem replicaZ_hasDerivAt_one (hp : ∀ i, 0 < p i) :
    HasDerivAt (replicaZ p) (∑ i, p i * Real.log (p i)) 1 := by
  show HasDerivAt (fun n => ∑ i, Real.exp (n * Real.log (p i))) _ 1
  have hval : (∑ i, Real.exp (1 * Real.log (p i)) * Real.log (p i))
      = ∑ i, p i * Real.log (p i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [one_mul, Real.exp_log (hp i)]
  rw [← hval]
  rw [show (fun n : ℝ => ∑ i, Real.exp (n * Real.log (p i)))
      = ∑ i : ι, (fun n : ℝ => Real.exp (n * Real.log (p i))) from by
    funext n; rw [Finset.sum_apply]]
  apply HasDerivAt.sum
  intro i _
  have h1 : HasDerivAt (fun n : ℝ => n * Real.log (p i)) (Real.log (p i)) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (Real.log (p i))
  simpa using h1.exp

/-- **The headline slope**: the replica free energy `Wₙ = log Zₙ` has derivative
`∑ pᵢ log pᵢ` at `n = 1`. -/
theorem replicaW_hasDerivAt_one (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    HasDerivAt (replicaW p) (∑ i, p i * Real.log (p i)) 1 := by
  have hZ := replicaZ_hasDerivAt_one hp
  have hne : replicaZ p 1 ≠ 0 := (replicaZ_pos 1).ne'
  have := hZ.log hne
  rw [replicaZ_one hp hsum, div_one] at this
  exact this

/-- **`S = −∂ₙ log Zₙ |ₙ₌₁`**: `n ↦ −Wₙ` has derivative the Shannon entropy at `n = 1`. -/
theorem replica_entropy_hasDerivAt (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    HasDerivAt (fun n : ℝ => - replicaW p n) (shannon p) 1 := by
  have := (replicaW_hasDerivAt_one hp hsum).neg
  rw [shannon]
  exact this

/-- The Shannon entropy is minus the slope of the replica free energy at `n = 1`. -/
theorem entropy_eq_neg_deriv (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    - deriv (replicaW p) 1 = shannon p := by
  rw [(replicaW_hasDerivAt_one hp hsum).deriv, shannon]

/-- **The Rényi `n→1` limit is the Shannon entropy** (no L'Hôpital: uses the slope
characterization of the derivative). -/
theorem renyi_tendsto_shannon (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    Filter.Tendsto (renyi p) (nhdsWithin 1 {(1:ℝ)}ᶜ) (nhds (shannon p)) := by
  -- slope of replicaW at 1 tends to the derivative ∑ pᵢ log pᵢ
  have hslope : Filter.Tendsto (slope (replicaW p) 1)
      (nhdsWithin 1 {(1:ℝ)}ᶜ) (nhds (∑ i, p i * Real.log (p i))) :=
    (hasDerivAt_iff_tendsto_slope.1 (replicaW_hasDerivAt_one hp hsum))
  -- renyi p n = - slope (replicaW p) 1 n  (for all n; both sides are 0/0-junk at n=1)
  have heq : ∀ n : ℝ, renyi p n = - slope (replicaW p) 1 n := by
    intro n
    rw [renyi, slope_def_field, replicaW_one hp hsum, sub_zero, ← div_neg, neg_sub]
  have : Filter.Tendsto (renyi p) (nhdsWithin 1 {(1:ℝ)}ᶜ)
      (nhds (- ∑ i, p i * Real.log (p i))) :=
    (hslope.neg).congr (fun n => (heq n).symm)
  simpa [shannon] using this

/-- **Capstone**: normalization, the entropy-as-slope law, and the Rényi limit together. -/
theorem finite_replica_continuation (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    replicaW p 1 = 0 ∧ HasDerivAt (fun n : ℝ => - replicaW p n) (shannon p) 1 ∧
      Filter.Tendsto (renyi p) (nhdsWithin 1 {(1:ℝ)}ᶜ) (nhds (shannon p)) :=
  ⟨replicaW_one hp hsum, replica_entropy_hasDerivAt hp hsum, renyi_tendsto_shannon hp hsum⟩

end basic

end QIQTH.ReplicaContinuation
