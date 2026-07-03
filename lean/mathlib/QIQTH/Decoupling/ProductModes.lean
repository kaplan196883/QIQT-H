/-
  THE DECOUPLING SHADOW DS4 (THE_DECOUPLING_SHADOW_PLAN.md) — the finite-product lifts.

  The single-mode decoupling limits lifted to FINITE mode sets by `Finset` limit algebra: along
  any cutoff schedule in which every mode's cutoff grows,
  • the product thermal entropy converges to the finite-mode free-field value
    `Σ_k s_Planck(βω_k)`;
  • the total truncation-defect expectation dies;
  • the Gibbs weight of every FIXED occupation pattern converges to the free-field Boltzmann
    weight `Π_k q_k^{n_k}(1−q_k)`.

  ⚠ HONEST SCOPE (binding verdict): FINITE mode sets only — no continuum Riemann sums, no
  Type III limit; fixed positive temperatures (the saturation regime is the DS3 guard). Forces
  neither the screen geometry nor G. NOT a full decoupling derivation.
-/
import Mathlib
import QIQTH.Decoupling.EntropyRegimes

namespace QIQTH.Decoupling

open Filter

/-- **The free (Planck) mode entropy** `s_Planck(x) = −log(1−e^{−x}) + x·e^{−x}/(1−e^{−x})`. -/
noncomputable def planckEntropy (x : ℝ) : ℝ :=
  -Real.log (1 - Real.exp (-x)) + x * (Real.exp (-x) / (1 - Real.exp (-x)))

/-- **The product thermal entropy** of a finite mode set at cutoff assignment `Dv`. -/
noncomputable def productEntropy {K : Type*} (S : Finset K) (Dv : K → ℕ) (ω : K → ℝ)
    (β : ℝ) : ℝ :=
  ∑ k ∈ S, thermalEntropy (Dv k) (β * ω k)

/-- **DS4 CAPSTONE — the product thermal entropy converges to the finite-mode free-field
    value** along any cutoff schedule growing at every mode:
    `Σ_k S_{D_j(k)}(βω_k) → Σ_k s_Planck(βω_k)`. -/
theorem tendsto_productEntropy {K : Type*} (S : Finset K) (ω : K → ℝ) (β : ℝ)
    (hβω : ∀ k ∈ S, 0 < β * ω k) (Dv : ℕ → K → ℕ)
    (hD : ∀ k ∈ S, Tendsto (fun j : ℕ => Dv j k) atTop atTop) :
    Tendsto (fun j : ℕ => productEntropy S (Dv j) ω β) atTop
      (nhds (∑ k ∈ S, planckEntropy (β * ω k))) := by
  refine tendsto_finset_sum S fun k hk => ?_
  exact (tendsto_thermalEntropy_planck (hβω k hk)).comp (hD k hk)

/-- **The total defect expectation dies** along growing cutoffs: `Σ_k ⟨D·P_top⟩_k → 0`. -/
theorem tendsto_totalDefect {K : Type*} (S : Finset K) (ω : K → ℝ) (β : ℝ)
    (hβω : ∀ k ∈ S, 0 < β * ω k) (Dv : ℕ → K → ℕ)
    (hD : ∀ k ∈ S, Tendsto (fun j : ℕ => Dv j k) atTop atTop) :
    Tendsto (fun j : ℕ => ∑ k ∈ S, defectExpect (Dv j k) (Real.exp (-(β * ω k)))) atTop
      (nhds 0) := by
  have h := tendsto_finset_sum S (f := fun k j =>
      defectExpect (Dv j k) (Real.exp (-(β * ω k)))) (a := fun _ => (0 : ℝ)) fun k hk => by
    have h0 : (0 : ℝ) ≤ Real.exp (-(β * ω k)) := (Real.exp_pos _).le
    have h1 : Real.exp (-(β * ω k)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith [hβω k hk]
    exact (tendsto_defectExpect h0 h1).comp (hD k hk)
  simpa using h

/-- **The Gibbs weight of every FIXED occupation pattern converges to the free-field Boltzmann
    weight**: `Π_k q_k^{n_k}/Z_{D_j(k)} → Π_k q_k^{n_k}·(1−q_k)` — the state-level product
    decoupling (the truncated thermal state's finite-dimensional marginals converge to the
    free-field ones, occupation by occupation). -/
theorem tendsto_gibbsWeight_fixedOccupation {K : Type*} (S : Finset K) (ω : K → ℝ) (β : ℝ)
    (hβω : ∀ k ∈ S, 0 < β * ω k) (n : K → ℕ) (Dv : ℕ → K → ℕ)
    (hD : ∀ k ∈ S, Tendsto (fun j : ℕ => Dv j k) atTop atTop) :
    Tendsto (fun j : ℕ => ∏ k ∈ S,
        Real.exp (-(β * ω k)) ^ (n k) / Zgeom (Dv j k) (Real.exp (-(β * ω k)))) atTop
      (nhds (∏ k ∈ S, Real.exp (-(β * ω k)) ^ (n k) * (1 - Real.exp (-(β * ω k))))) := by
  refine tendsto_finset_prod S fun k hk => ?_
  have h0 : (0 : ℝ) ≤ Real.exp (-(β * ω k)) := (Real.exp_pos _).le
  have h1 : Real.exp (-(β * ω k)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith [hβω k hk]
  have hZ : Tendsto (fun j : ℕ => Zgeom (Dv j k) (Real.exp (-(β * ω k)))) atTop
      (nhds (1 - Real.exp (-(β * ω k)))⁻¹) :=
    (tendsto_Zgeom h0 h1).comp (hD k hk)
  have hne : ((1 - Real.exp (-(β * ω k)))⁻¹ : ℝ) ≠ 0 := inv_ne_zero (by linarith)
  have hconst : Tendsto (fun _ : ℕ => Real.exp (-(β * ω k)) ^ (n k)) atTop
      (nhds (Real.exp (-(β * ω k)) ^ (n k))) := tendsto_const_nhds
  have hlim := hconst.div hZ hne
  rw [show Real.exp (-(β * ω k)) ^ (n k) * (1 - Real.exp (-(β * ω k)))
      = Real.exp (-(β * ω k)) ^ (n k) / (1 - Real.exp (-(β * ω k)))⁻¹ from by
    rw [div_eq_mul_inv, inv_inv]]
  exact hlim

end QIQTH.Decoupling
