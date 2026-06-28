/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# PHOTON_FIELD_PLAN P4 — the Bose–Einstein (photon) Unruh occupation

The photon is bosonic (CCR), so its Rindler/Unruh thermal occupation is **Bose–Einstein**
`n_ω = 1/(e^{βω} − 1)` — the `−1` denominator (vs the electron's Fermi–Dirac `+1`,
`QIQTH/Fock/Dirac/FermiDirac.lean`).  The `boseEinstein` definition and the CCR KMS balance
`n = e^{−βω}(1 + n)` (the `+ n` from `a a† = 1 + a† a`) already live in `FermiDirac.lean` as the explicit
spin–statistics contrast; this module completes the bosonic cluster parallel to the fermionic one:
positivity (for `βω > 0`), uniqueness of the KMS solution, the strict **`n_BE > n_FD`** ordering (the
bosonic occupation exceeds the fermionic — no Pauli ceiling, the occupation-level shadow of the photon's
*unbounded* regional capacity, `PHOTON_FIELD_PLAN` P2/P3), and the Rindler/Unruh occupation at the
Bisognano–Wichmann temperature `β = 2π`.

Honest scope: this is the distribution-level (single-mode) Unruh occupation, the bosonic mirror of the
electron's `rindlerOccupationFermi` / `electron_unruh_occupation`.  The full photon Unruh *state*
expectation rides the bosonic second-quantized modular flow `secondQuantModFlow` (reused, P5).  The
bosonic occupation requires `βω ≠ 0` (`e^{βω} ≠ 1`) to be defined — the `ω = 0` zero-mode is part of the
gauge/IR frontier (P10), not formalized here.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Maxwell only.
-/
import QIQTH.Fock.Dirac.FermiDirac

namespace QIQTH.Fock.Photon

open QIQTH.Fock.Dirac

/-- **The Bose–Einstein occupation is positive** for `βω > 0`: `0 < 1/(e^{βω} − 1)`, since `e^{βω} > 1`.
The photon's Rindler occupation is a genuine (positive) occupation number above the zero-mode. -/
theorem boseEinstein_pos {β ω : ℝ} (h : 0 < β * ω) : 0 < boseEinstein β ω := by
  unfold boseEinstein
  have h1 : Real.exp 0 < Real.exp (β * ω) := Real.exp_lt_exp.mpr h
  rw [Real.exp_zero] at h1
  apply div_pos one_pos
  linarith

/-- **Uniqueness of the bosonic Unruh occupation.**  Any `n` solving the KMS + CCR balance
`n = e^{−βω}(1 + n)` equals the Bose–Einstein occupation `1/(e^{βω} − 1)` (for `e^{βω} ≠ 1`).  So
`1/(e^{βω}−1)` is THE occupation of a bosonic Rindler/photon mode — the bosonic mirror of
`fermiDirac_unique`. -/
theorem boseEinstein_unique {β ω n : ℝ} (hβω : Real.exp (β * ω) ≠ 1)
    (h : n = Real.exp (-(β * ω)) * (1 + n)) : n = boseEinstein β ω := by
  have he : Real.exp (β * ω) ≠ 0 := (Real.exp_pos _).ne'
  have hne : Real.exp (β * ω) - 1 ≠ 0 := sub_ne_zero.mpr hβω
  rw [Real.exp_neg] at h
  unfold boseEinstein
  field_simp at h ⊢
  linear_combination h

/-- **The bosonic occupation exceeds the fermionic** (`βω > 0`): `n_FD < n_BE`, i.e.
`1/(e^{βω}+1) < 1/(e^{βω}−1)`.  At the same Unruh temperature the photon mode is MORE occupied than the
electron mode — and, crucially, the bosonic occupation has **no Pauli ceiling** (`n_FD < 1` but `n_BE`
is unbounded as `βω → 0⁺`): the occupation-level reason the photon's regional capacity needs a number
cutoff (`PHOTON_FIELD_PLAN` P2/P3 `truncFockDim_*`) while the electron's CAR capacity is intrinsically
finite. -/
theorem boseEinstein_gt_fermiDirac {β ω : ℝ} (h : 0 < β * ω) :
    fermiDirac β ω < boseEinstein β ω := by
  unfold fermiDirac boseEinstein
  have h1 : Real.exp 0 < Real.exp (β * ω) := Real.exp_lt_exp.mpr h
  rw [Real.exp_zero] at h1
  have hpos : (0 : ℝ) < Real.exp (β * ω) - 1 := by linarith
  have hpos2 : (0 : ℝ) < Real.exp (β * ω) + 1 := by linarith
  rw [div_lt_div_iff_of_pos_left one_pos hpos2 hpos]
  linarith

/-- The **Rindler/Unruh occupation** of a bosonic (photon) mode: the Bose–Einstein occupation at the Unruh
inverse temperature `β = 2π`, `n_ω = 1/(e^{2πω} − 1)`. -/
noncomputable def rindlerOccupationBose (ω : ℝ) : ℝ := boseEinstein (2 * Real.pi) ω

/-- The Rindler/Unruh bosonic occupation satisfies the KMS + CCR balance at `β = 2π` (requires
`e^{2πω} ≠ 1`, i.e. `ω ≠ 0` — the photon zero-mode is the gauge/IR frontier). -/
theorem rindlerOccupationBose_balance {ω : ℝ} (h : Real.exp (2 * Real.pi * ω) ≠ 1) :
    rindlerOccupationBose ω
      = Real.exp (-(2 * Real.pi * ω)) * (1 + rindlerOccupationBose ω) :=
  boseEinstein_kms_balance h

/-- **The photon Unruh occupation is positive** (`ω > 0`): `0 < n_ω = 1/(e^{2πω} − 1)`.  The Bose–Einstein
occupation of a positive-energy photon mode seen by the Rindler/Unruh observer at the Bisognano–Wichmann
temperature `β = 2π`. -/
theorem rindlerOccupationBose_pos {ω : ℝ} (h : 0 < ω) : 0 < rindlerOccupationBose ω :=
  boseEinstein_pos (by positivity)

end QIQTH.Fock.Photon
