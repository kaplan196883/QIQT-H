/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E3 — quasi-free fermionic entropy and the CAR capacity bound

The von Neumann entropy of a *quasi-free* (Gaussian) state of a free fermion (the electron) is a SUM
over the eigenvalues `c ∈ [0,1]` of the one-particle correlation matrix `C` (`0 ≤ C ≤ 1`) of a single
"binary" entropy term
```
   S = − Tr[C log C + (1−C) log(1−C)] = Σ over eigenvalues c of  H₂(c),
   H₂(c) = − c log c − (1−c) log(1−c) = negMulLog c + negMulLog (1−c).
```
This is the fermionic mirror of `QIQTH.GaussianStateEntropy.gaussModeEntropy` (the bosonic per-mode
entropy) and of `QIQTH.BranchLedger.Shannon` / `shannon_le_log_card` (the record/Shannon bound).

The headline is the **CAR capacity bound**: each mode contributes at most `log 2` (a single fermionic
mode is a qubit), so the total entropy of a region with one-particle space `h_R` of dimension `n` is
bounded by `n · log 2 = log (2ⁿ) = log dim(⋀ h_R)` — the dimension of the antisymmetric (CAR) Fock
space over `h_R`.  This is the fermionic analogue of `S_vN ≤ log N_R`: the finite-capacity bound
survives the bosons → fermions transition, on the chosen regional algebra.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound` only).  No `sorry`.

HONEST scope (per ELECTRON_FIELD_PLAN §0,§5): `c : ι → ℝ` here are the eigenvalues of the correlation
matrix — the spectral reduction of `C` to its eigenvalues is taken as the granularity (exactly as the
bosonic `gaussModeEntropy` is stated per symplectic mode).  Which *regional algebra* the capacity
attaches to (full graded field algebra vs. even / U(1)-invariant observable algebra) is the E7 question;
here the bound is the per-spectrum kernel that E7 consumes.
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace QIQTH.Fock.Dirac

open Real
open scoped BigOperators

/-- The single-mode (binary) fermionic entropy `H₂(c) = −c·log c − (1−c)·log(1−c)`, written via
`Real.negMulLog`.  For a single fermionic mode with occupation `c ∈ [0,1]` this is the entropy of the
reduced state (a qubit). -/
noncomputable def binaryEntropy (c : ℝ) : ℝ :=
  Real.negMulLog c + Real.negMulLog (1 - c)

/-- A pure/empty mode (`c = 0`) carries no entropy. -/
@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, Real.negMulLog_zero, Real.negMulLog_one]

/-- A full mode (`c = 1`) carries no entropy. -/
@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy, Real.negMulLog_zero, Real.negMulLog_one]

/-- `negMulLog` evaluated at `1/2` is `(1/2)·log 2` — the half that the concavity bound lands on. -/
private theorem negMulLog_half : Real.negMulLog (1 / 2 : ℝ) = (1 / 2) * Real.log 2 := by
  have hlog : Real.log (1 / 2 : ℝ) = - Real.log 2 := by rw [one_div, Real.log_inv]
  simp only [Real.negMulLog_def, hlog]
  ring

/-- The maximally-mixed mode (`c = 1/2`) carries exactly `log 2` — the qubit capacity. -/
theorem binaryEntropy_half : binaryEntropy (1 / 2) = Real.log 2 := by
  have h2 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  unfold binaryEntropy
  rw [h2, negMulLog_half]
  ring

/-- **The single-mode capacity bound**: a fermionic mode carries at most `log 2`.  Proof = concavity of
`negMulLog` (Jensen at the two points `c`, `1−c` with equal weights), maximized at `c = 1/2`. -/
theorem binaryEntropy_le_log_two {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    binaryEntropy c ≤ Real.log 2 := by
  have hxc : c ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hc0
  have hyc : (1 - c) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  -- Jensen for the concave `negMulLog` at `c` and `1−c`, weights `1/2, 1/2`.
  have hjensen :=
    Real.concaveOn_negMulLog.2 hxc hyc
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (1:ℝ) / 2 + 1 / 2 = 1)
  -- The midpoint is `1/2`.
  have hmid : (1 / 2 : ℝ) • c + (1 / 2 : ℝ) • (1 - c) = 1 / 2 := by
    simp only [smul_eq_mul]; ring
  rw [hmid, negMulLog_half] at hjensen
  simp only [smul_eq_mul] at hjensen
  -- hjensen : (1/2)·negMulLog c + (1/2)·negMulLog (1−c) ≤ (1/2)·log 2
  unfold binaryEntropy
  linarith

/-- A fermionic mode entropy is nonnegative on `[0,1]` (`negMulLog ≥ 0` on `[0,1]`). -/
theorem binaryEntropy_nonneg {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : 0 ≤ binaryEntropy c := by
  have h1 : 0 ≤ Real.negMulLog c := Real.negMulLog_nonneg hc0 hc1
  have h2 : 0 ≤ Real.negMulLog (1 - c) := Real.negMulLog_nonneg (by linarith) (by linarith)
  unfold binaryEntropy; linarith

/-- The von Neumann entropy of a quasi-free (Gaussian) fermionic state, as a sum over the eigenvalues
`c i ∈ [0,1]` of its one-particle correlation matrix.  Equals `−Tr[C log C + (1−C) log(1−C)]`. -/
noncomputable def fermionicGaussianEntropy {ι : Type*} [Fintype ι] (c : ι → ℝ) : ℝ :=
  ∑ i, binaryEntropy (c i)

/-- A quasi-free fermionic entropy is nonnegative. -/
theorem fermionicGaussianEntropy_nonneg {ι : Type*} [Fintype ι] {c : ι → ℝ}
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) : 0 ≤ fermionicGaussianEntropy c :=
  Finset.sum_nonneg (fun i _ => binaryEntropy_nonneg (hc0 i) (hc1 i))

/-- **The CAR capacity bound** (fermionic mirror of `shannon_le_log_card`): the entropy of a quasi-free
state on a region with `n = card ι` fermionic modes is at most `n · log 2`.  Each mode is a qubit. -/
theorem fermionicGaussianEntropy_le_card_log_two {ι : Type*} [Fintype ι] {c : ι → ℝ}
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) :
    fermionicGaussianEntropy c ≤ (Fintype.card ι : ℝ) * Real.log 2 := by
  have hsum : fermionicGaussianEntropy c ≤ ∑ _i : ι, Real.log 2 :=
    Finset.sum_le_sum (fun i _ => binaryEntropy_le_log_two (hc0 i) (hc1 i))
  rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum

/-- **Capacity bound in manifest holographic form**: `S ≤ log (2ⁿ) = log dim(⋀ h_R)`, the logarithm of
the dimension of the antisymmetric (CAR) Fock space over an `n`-mode region.  This is the fermionic
`S_vN ≤ log N_R` with `N_R = 2ⁿ`. -/
theorem fermionicGaussianEntropy_le_log_dim {ι : Type*} [Fintype ι] {c : ι → ℝ}
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) :
    fermionicGaussianEntropy c ≤ Real.log (2 ^ (Fintype.card ι)) := by
  rw [Real.log_pow]
  exact fermionicGaussianEntropy_le_card_log_two hc0 hc1

/-! ### The fermionic (CAR / Araki) relative entropy

The relative entropy of two quasi-free fermionic states, in terms of their one-particle correlation
spectra `c, d ∈ (0,1)`, is the sum over modes of the **binary relative entropy** (KL divergence)
`D(c‖d) = c·log(c/d) + (1−c)·log((1−c)/(1−d))`.  Its **nonnegativity** is the fermionic mirror of
Klein's inequality (`QuantumRelativeEntropy.relEntropy_nonneg`) — the CAR/Araki relative entropy at the
mode level.  Relative entropy (not the bare von Neumann entropy) is the quantity that controls the
modular / entanglement-first-law side of the area law, so this is the fermionic input to that route. -/

/-- The single-mode (binary) fermionic relative entropy / KL divergence
`D(c‖d) = c·log(c/d) + (1−c)·log((1−c)/(1−d))`. -/
noncomputable def fermionicBinaryRelEntropy (c d : ℝ) : ℝ :=
  c * Real.log (c / d) + (1 - c) * Real.log ((1 - c) / (1 - d))

/-- **Binary relative-entropy positivity (Gibbs' inequality):** `0 ≤ D(c‖d)` for occupations
`c, d ∈ (0,1)`.  Proof = `log x ≤ x − 1` per term.  The fermionic mirror of Klein's inequality. -/
theorem fermionicBinaryRelEntropy_nonneg {c d : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hd0 : 0 < d) (hd1 : d < 1) : 0 ≤ fermionicBinaryRelEntropy c d := by
  have hlog1 : Real.log (c / d) = - Real.log (d / c) := by
    rw [Real.log_div hc0.ne' hd0.ne', Real.log_div hd0.ne' hc0.ne']; ring
  have hlog2 : Real.log ((1 - c) / (1 - d)) = - Real.log ((1 - d) / (1 - c)) := by
    rw [Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith)]; ring
  have t1 : c * Real.log (d / c) ≤ d - c := by
    have hcne : c ≠ 0 := hc0.ne'
    calc c * Real.log (d / c) ≤ c * (d / c - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hd0 hc0)) hc0.le
      _ = d - c := by field_simp
  have t2 : (1 - c) * Real.log ((1 - d) / (1 - c)) ≤ c - d := by
    have h1cne : (1 : ℝ) - c ≠ 0 := by linarith
    calc (1 - c) * Real.log ((1 - d) / (1 - c))
          ≤ (1 - c) * ((1 - d) / (1 - c) - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith)))
            (by linarith)
      _ = c - d := by field_simp; ring
  unfold fermionicBinaryRelEntropy
  rw [hlog1, hlog2, mul_neg, mul_neg]
  linarith [t1, t2]

/-- The **fermionic (CAR/Araki) relative entropy** of two quasi-free states, summed over the mode
spectra `c, d`. -/
noncomputable def fermionicGaussianRelEntropy {ι : Type*} [Fintype ι] (c d : ι → ℝ) : ℝ :=
  ∑ i, fermionicBinaryRelEntropy (c i) (d i)

/-- **CAR relative-entropy positivity** `S(ρ_C ‖ ρ_D) ≥ 0` — the fermionic Araki/Klein inequality. -/
theorem fermionicGaussianRelEntropy_nonneg {ι : Type*} [Fintype ι] {c d : ι → ℝ}
    (hc0 : ∀ i, 0 < c i) (hc1 : ∀ i, c i < 1) (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1) :
    0 ≤ fermionicGaussianRelEntropy c d :=
  Finset.sum_nonneg (fun i _ => fermionicBinaryRelEntropy_nonneg (hc0 i) (hc1 i) (hd0 i) (hd1 i))

/-- **Faithfulness (binary):** `D(c‖c) = 0` — the relative entropy of a state with itself vanishes.
With `fermionicBinaryRelEntropy_nonneg` (≥ 0, with equality iff equal), this is the second defining
property of relative entropy; it is exactly what makes the first law `δS = δ⟨K⟩` the statement that the
relative entropy `D(n ‖ n_KMS)` is *minimized* (= 0) at the KMS occupation. -/
@[simp] theorem fermionicBinaryRelEntropy_self (c : ℝ) : fermionicBinaryRelEntropy c c = 0 := by
  unfold fermionicBinaryRelEntropy
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; simp
  · rcases eq_or_ne (1 - c) 0 with hc1 | hc1
    · rw [hc1, div_self hc]; simp
    · rw [div_self hc, div_self hc1, Real.log_one]; ring

/-- **Faithfulness (CAR/Araki):** `S(ρ ‖ ρ) = 0` — the fermionic relative entropy of a quasi-free state
with itself vanishes. -/
@[simp] theorem fermionicGaussianRelEntropy_self {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    fermionicGaussianRelEntropy c c = 0 := by
  simp [fermionicGaussianRelEntropy]

end QIQTH.Fock.Dirac
