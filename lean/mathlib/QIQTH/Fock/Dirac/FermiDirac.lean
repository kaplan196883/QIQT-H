/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E6 — Fermi–Dirac occupation: the CAR `+1` (vs Bose `−1`) Unruh signature

For a Rindler mode `b_ω` of the free Dirac field, the vacuum restricted to the wedge is boost-KMS at
inverse temperature `β = 2π` (the Unruh temperature — the SAME as for the scalar; ELECTRON_FIELD_PLAN
§0).  The fermionic difference is the OCCUPATION: combining the KMS thermal condition
`⟨b_ω† b_ω⟩ = e^{−βω} ⟨b_ω b_ω†⟩` with the **CAR** anticommutator `{b_ω, b_ω†} = 1`
(`b_ω b_ω† = 1 − b_ω† b_ω`) gives the balance
```
   n = e^{−βω} (1 − n)        ⟹        n = 1 / (e^{βω} + 1)        (Fermi–Dirac).
```
The bosonic case uses the CCR commutator `[a, a†] = 1` (`a a† = 1 + a† a`), giving
`n = e^{−βω}(1 + n) ⟹ n = 1/(e^{βω} − 1)` (Bose–Einstein).  So the Unruh temperature is identical; only
the sign in the denominator flips — `+1` for the electron (CAR) vs `−1` for the scalar (CCR).  This is
the spin–statistics signature at the level of the thermal occupation.

This module formalizes that real-analysis content: the Fermi–Dirac function, the KMS+CAR balance it
satisfies, its UNIQUENESS as the solution of that balance, that it is a valid occupation `0 < n < 1`,
the Bose contrast, and the Rindler/Unruh specialization `β = 2π`.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.

HONEST scope (ELECTRON_FIELD_PLAN §0): the *balance relation* `n = e^{−βω}(1 − n)` is the KMS+CAR input
(it presupposes the modular/KMS state, the cited operator-algebra machinery — E5).  What is derived here
is that, GIVEN the balance, the occupation is uniquely Fermi–Dirac, valid, and sign-distinguished from
Bose.  Free Dirac only.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace QIQTH.Fock.Dirac

open Real

/-- The **Fermi–Dirac occupation** `n(β,ω) = 1/(e^{βω} + 1)` — the `+1` (CAR) thermal occupation. -/
noncomputable def fermiDirac (β ω : ℝ) : ℝ := 1 / (Real.exp (β * ω) + 1)

/-- The **Bose–Einstein occupation** `1/(e^{βω} − 1)` — the `−1` (CCR) thermal occupation, kept for the
explicit spin–statistics contrast. -/
noncomputable def boseEinstein (β ω : ℝ) : ℝ := 1 / (Real.exp (β * ω) - 1)

/-- Fermi–Dirac occupation is positive. -/
theorem fermiDirac_pos (β ω : ℝ) : 0 < fermiDirac β ω := by
  unfold fermiDirac; positivity

/-- Fermi–Dirac occupation is below 1 (an electron mode is at most singly occupied — Pauli). -/
theorem fermiDirac_lt_one (β ω : ℝ) : fermiDirac β ω < 1 := by
  unfold fermiDirac
  rw [div_lt_one (by positivity)]
  have := Real.exp_pos (β * ω); linarith

/-- Fermi–Dirac occupation is a valid occupation number: `0 < n < 1`. -/
theorem fermiDirac_mem_Ioo (β ω : ℝ) : fermiDirac β ω ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨fermiDirac_pos β ω, fermiDirac_lt_one β ω⟩

/-- **The KMS + CAR balance.**  `n = e^{−βω}(1 − n)`: the Fermi–Dirac occupation satisfies the detailed
balance coming from the KMS thermal condition together with the CAR anticommutator
`b b† = 1 − b† b`. -/
theorem fermiDirac_kms_balance (β ω : ℝ) :
    fermiDirac β ω = Real.exp (-(β * ω)) * (1 - fermiDirac β ω) := by
  unfold fermiDirac
  rw [Real.exp_neg]
  have hne : Real.exp (β * ω) + 1 ≠ 0 := by positivity
  have he : Real.exp (β * ω) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

/-- **Uniqueness.**  Any `n` solving the KMS+CAR balance `n = e^{−βω}(1 − n)` equals the Fermi–Dirac
occupation.  So `1/(e^{βω}+1)` is THE occupation of a fermionic Rindler mode. -/
theorem fermiDirac_unique {β ω n : ℝ} (h : n = Real.exp (-(β * ω)) * (1 - n)) :
    n = fermiDirac β ω := by
  have he : Real.exp (β * ω) ≠ 0 := (Real.exp_pos _).ne'
  have hne : Real.exp (β * ω) + 1 ≠ 0 := by positivity
  rw [Real.exp_neg] at h
  unfold fermiDirac
  field_simp at h ⊢
  linear_combination h

/-- **The Bose contrast.**  With the CCR sign (`a a† = 1 + a† a`) the balance becomes
`n = e^{−βω}(1 + n)`, solved by the Bose–Einstein occupation `1/(e^{βω} − 1)`.  Same Unruh temperature;
denominator sign `−1` instead of the Fermi–Dirac `+1` — the spin–statistics signature.  (Requires
`e^{βω} ≠ 1`, i.e. `βω ≠ 0`, for the bosonic occupation to be defined.) -/
theorem boseEinstein_kms_balance {β ω : ℝ} (h : Real.exp (β * ω) ≠ 1) :
    boseEinstein β ω = Real.exp (-(β * ω)) * (1 + boseEinstein β ω) := by
  unfold boseEinstein
  rw [Real.exp_neg]
  have hne : Real.exp (β * ω) - 1 ≠ 0 := sub_ne_zero.mpr h
  have he : Real.exp (β * ω) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

/-- The **Rindler/Unruh occupation** of a fermionic mode: the Fermi–Dirac occupation at the Unruh
inverse temperature `β = 2π`, `n_ω = 1/(e^{2πω} + 1)`. -/
noncomputable def rindlerOccupationFermi (ω : ℝ) : ℝ := fermiDirac (2 * Real.pi) ω

/-- The Rindler/Unruh fermionic occupation is `1/(e^{2πω}+1)` and satisfies the KMS+CAR balance at
`β = 2π`. -/
theorem rindlerOccupationFermi_balance (ω : ℝ) :
    rindlerOccupationFermi ω = Real.exp (-(2 * Real.pi * ω)) * (1 - rindlerOccupationFermi ω) :=
  fermiDirac_kms_balance (2 * Real.pi) ω

end QIQTH.Fock.Dirac
