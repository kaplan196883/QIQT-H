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
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

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

/-- **The bosonic partition function is `n + 1`**: `(n + 1)(1 − e^{−βω}) = 1`, i.e. `n + 1 = 1/(1 − e^{−βω})
= Z_bose` (for `e^{βω} ≠ 1`).  The `(n+1)` enhancement factor IS the single-mode bosonic partition function
`Z_bose = ∑_k e^{−βωk} = 1/(1 − e^{−βω})` — the geometric-series sum over the number states.  (Contrast the
fermionic 2-state `Z_fermi = 1 + e^{−βω}`, `electron_gibbs_weight_*`: the bosonic geometric `1/(1−x)` vs the
fermionic two-level `1+x` partition function — the spin–statistics signature at the partition level.) -/
theorem boseEinstein_add_one_mul {β ω : ℝ} (h : Real.exp (β * ω) ≠ 1) :
    (1 + boseEinstein β ω) * (1 - Real.exp (-(β * ω))) = 1 := by
  unfold boseEinstein
  rw [Real.exp_neg]
  have he : Real.exp (β * ω) ≠ 0 := (Real.exp_pos _).ne'
  have hsub : Real.exp (β * ω) - 1 ≠ 0 := sub_ne_zero.mpr h
  field_simp
  ring

/-- **The bosonic Gibbs form of the occupation** `n = e^{−βω}/(1 − e^{−βω})` (for `e^{βω} ≠ 1`).  The
Bose–Einstein occupation is the **mean of the geometric (Bose) distribution** `p_k = (1−x)x^k` over the
number states `k = 0,1,2,…`, with Boltzmann factor `x = e^{−βω}` and single-mode partition function
`Z = 1/(1−x)` — i.e. `n = x/(1−x) = x·Z`.  (Contrast the fermionic 2-state `n = x/(1+x)`: the bosonic
`1−x` denominator vs the fermionic `1+x` is the geometric-vs-two-level spin–statistics signature.) -/
theorem boseEinstein_gibbs_form {β ω : ℝ} (h : Real.exp (β * ω) ≠ 1) :
    boseEinstein β ω = Real.exp (-(β * ω)) / (1 - Real.exp (-(β * ω))) := by
  have hfrac : 1 - Real.exp (-(β * ω)) = (Real.exp (β * ω) - 1) / Real.exp (β * ω) := by
    rw [Real.exp_neg, eq_div_iff (Real.exp_pos _).ne', sub_mul, one_mul,
        inv_mul_cancel₀ (Real.exp_pos _).ne']
  unfold boseEinstein
  rw [hfrac, Real.exp_neg, div_div_eq_mul_div, inv_mul_cancel₀ (Real.exp_pos _).ne']

/-- **The bosonic enhancement factor `1 + n = e^{βω}·n`** (for `e^{βω} ≠ 1`).  The `(n+1)` of bosonic
emission (spontaneous `1` + stimulated `n`) equals `e^{βω}` times the occupation — the multiplicative
form of the CCR/KMS balance `n = e^{−βω}(1+n)` (`boseEinstein_kms_balance`), and the source of the
Bose–Einstein distribution.  (Contrast the fermionic `1 − n = e^{βω}·n`, `fermiDirac`'s `+1` denominator:
the bosonic `+n` vs fermionic `−n` is the spin–statistics signature.) -/
theorem boseEinstein_one_add {β ω : ℝ} (h : Real.exp (β * ω) ≠ 1) :
    1 + boseEinstein β ω = Real.exp (β * ω) * boseEinstein β ω := by
  unfold boseEinstein
  have hsub : Real.exp (β * ω) - 1 ≠ 0 := sub_ne_zero.mpr h
  field_simp
  ring

/-- **The Bose–Einstein occupation decreases with mode energy**: for `0 < βω₁ ≤ βω₂`,
`n(βω₂) ≤ n(βω₁)`.  Higher-energy photon modes are (thermally) less occupied — the Bose occupation
`1/(e^{βω}−1)` is antitone in `βω` (since `e^{βω}−1` is increasing and positive).  The expected monotone
falloff of the thermal/Unruh photon spectrum with energy. -/
theorem boseEinstein_le_of_le {β ω₁ ω₂ : ℝ} (h1 : 0 < β * ω₁) (h : β * ω₁ ≤ β * ω₂) :
    boseEinstein β ω₂ ≤ boseEinstein β ω₁ := by
  unfold boseEinstein
  have he1 : 1 < Real.exp (β * ω₁) := by
    have h2 := Real.exp_lt_exp.mpr h1; rwa [Real.exp_zero] at h2
  have hpos : (0 : ℝ) < Real.exp (β * ω₁) - 1 := by linarith
  have hle : Real.exp (β * ω₁) - 1 ≤ Real.exp (β * ω₂) - 1 := by
    have := Real.exp_le_exp.mpr h; linarith
  exact one_div_le_one_div_of_le hpos hle

/-- **The photon Unruh occupation in Gibbs form** (`β = 2π`): `n_ω = e^{−2πω}/(1 − e^{−2πω})`.  The
Rindler/Unruh photon occupation at the Bisognano–Wichmann temperature is the mean of the geometric (Bose)
distribution with Boltzmann factor `e^{−2πω}` — the `β = 2π` specialization of `boseEinstein_gibbs_form`. -/
theorem rindlerOccupationBose_gibbs_form {ω : ℝ} (h : Real.exp (2 * Real.pi * ω) ≠ 1) :
    rindlerOccupationBose ω
      = Real.exp (-(2 * Real.pi * ω)) / (1 - Real.exp (-(2 * Real.pi * ω))) :=
  boseEinstein_gibbs_form h

/-- The single bosonic-mode (photon) thermal entropy `S_BE(n) = (1+n)log(1+n) − n log n` — the von Neumann
entropy of a thermal harmonic oscillator at occupation `n` (the bosonic mirror of the electron's
`binaryEntropy`). -/
noncomputable def boseEntropy (n : ℝ) : ℝ := (1 + n) * Real.log (1 + n) - n * Real.log n

/-- **The photon Unruh thermal entropy** `S_BE = log Z + βω·n` (for `βω > 0`).  For a bosonic (photon) mode
with Bose–Einstein occupation `n = 1/(e^{βω}−1)`, the mode entropy equals the log partition function
`log Z = −log(1 − e^{−βω})` plus `βω` times the occupation (`= β⟨E⟩`):
`(1+n)log(1+n) − n log n = −log(1 − e^{−βω}) + βω·n`.  The bosonic mirror of the electron's
`electron_mode_entropy` (`S = log Z + β⟨E⟩`) — but with **no `log 2` ceiling**: as `βω → 0⁺` the occupation
`n → ∞` and `S_BE → ∞`, the *unbounded* photon mode entropy (the entropy-level reason the photon needs a
number cutoff, `PHOTON_FIELD_PLAN` P2/P3), in sharp contrast with the electron's Pauli ceiling
`S ≤ log 2`. -/
theorem photon_mode_entropy {β ω : ℝ} (h : 0 < β * ω) :
    boseEntropy (boseEinstein β ω)
      = -Real.log (1 - Real.exp (-(β * ω))) + (β * ω) * boseEinstein β ω := by
  have hexp1 : 1 < Real.exp (β * ω) := by
    have h2 := Real.exp_lt_exp.mpr h; rwa [Real.exp_zero] at h2
  have hsub : (0 : ℝ) < Real.exp (β * ω) - 1 := by linarith
  have hsubne : Real.exp (β * ω) - 1 ≠ 0 := ne_of_gt hsub
  set n := boseEinstein β ω with hn
  have hnpos : 0 < n := boseEinstein_pos h
  have h1n : Real.exp (β * ω) * n = 1 + n := by
    have hb1 : n * (Real.exp (β * ω) - 1) = 1 := by
      rw [hn]; unfold boseEinstein; exact one_div_mul_cancel hsubne
    linear_combination hb1
  have hlog1n : Real.log (1 + n) = β * ω + Real.log n := by
    rw [← h1n, Real.log_mul (Real.exp_pos _).ne' hnpos.ne', Real.log_exp]
  have hlogn : Real.log n = -Real.log (Real.exp (β * ω) - 1) := by
    rw [hn]; unfold boseEinstein; rw [one_div, Real.log_inv]
  have hfrac : 1 - Real.exp (-(β * ω)) = (Real.exp (β * ω) - 1) / Real.exp (β * ω) := by
    rw [Real.exp_neg, eq_div_iff (Real.exp_pos _).ne', sub_mul, one_mul,
        inv_mul_cancel₀ (Real.exp_pos _).ne']
  have hlogZ : -Real.log (1 - Real.exp (-(β * ω))) = β * ω - Real.log (Real.exp (β * ω) - 1) := by
    rw [hfrac, Real.log_div hsubne (Real.exp_pos _).ne', Real.log_exp]; ring
  rw [boseEntropy, hlog1n, hlogn, hlogZ]; ring

/-- **The bosonic logit at the Unruh occupation**: `log((1+n)/n) = βω` at `n = boseEinstein β ω`
(`βω > 0`).  Since `(1+n)/n = e^{βω}` for the Bose–Einstein occupation, the bosonic "modular energy"
recovered from the occupation is `βω` — the CCR analog of `fermiDirac_logit` (`log((1−n)/n) = βω`). -/
theorem boseEinstein_logit {β ω : ℝ} (h : 0 < β * ω) :
    Real.log ((1 + boseEinstein β ω) / boseEinstein β ω) = β * ω := by
  have hexp1 : 1 < Real.exp (β * ω) := by
    have h2 := Real.exp_lt_exp.mpr h; rwa [Real.exp_zero] at h2
  have hsubne : Real.exp (β * ω) - 1 ≠ 0 := by
    have : (0 : ℝ) < Real.exp (β * ω) - 1 := by linarith
    exact ne_of_gt this
  have hnpos : 0 < boseEinstein β ω := boseEinstein_pos h
  have h1n : Real.exp (β * ω) * boseEinstein β ω = 1 + boseEinstein β ω := by
    have hb1 : boseEinstein β ω * (Real.exp (β * ω) - 1) = 1 := by
      unfold boseEinstein; exact one_div_mul_cancel hsubne
    linear_combination hb1
  have hfrac : (1 + boseEinstein β ω) / boseEinstein β ω = Real.exp (β * ω) := by
    rw [← h1n, mul_div_assoc, div_self hnpos.ne', mul_one]
  rw [hfrac, Real.log_exp]

/-- **`d/dn S_BE = log((1+n)/n)`** — the bosonic mode entropy's derivative with respect to occupation.
Writing `S_BE(n) = (1+n)log(1+n) − n log n = negMulLog(n) − negMulLog(1+n)`, the derivative is
`log(1+n) − log n = log((1+n)/n)` (the bosonic modular energy). -/
theorem hasDerivAt_boseEntropy {n : ℝ} (hn0 : 0 < n) :
    HasDerivAt boseEntropy (Real.log ((1 + n) / n)) n := by
  have hnne : n ≠ 0 := hn0.ne'
  have h1nne : (1 : ℝ) + n ≠ 0 := by positivity
  have hinner : HasDerivAt (fun m : ℝ => 1 + m) 1 n := (hasDerivAt_id n).const_add 1
  have h2 : HasDerivAt (fun m => Real.negMulLog (1 + m)) (-Real.log (1 + n) - 1) n := by
    have h := (Real.hasDerivAt_negMulLog h1nne).comp n hinner
    simpa using h
  have key : HasDerivAt (fun m => Real.negMulLog m - Real.negMulLog (1 + m))
      (Real.log ((1 + n) / n)) n := by
    have h := (Real.hasDerivAt_negMulLog hnne).sub h2
    convert h using 1
    rw [Real.log_div h1nne hnne]; ring
  have hbe : boseEntropy = fun m => Real.negMulLog m - Real.negMulLog (1 + m) := by
    funext m; simp only [boseEntropy, Real.negMulLog_def]; ring
  rw [hbe]; exact key

/-- **The photon entanglement first law `δS = δ⟨K⟩`** (`βω > 0`): at the Bose–Einstein/Unruh occupation the
bosonic mode entropy's derivative IS the modular energy `βω` — `HasDerivAt boseEntropy (βω) (boseEinstein β ω)`.
The bosonic mirror of `electron_firstLaw`: the first law `δS = δ⟨K⟩` (modular energy `βω`, `= 2πω` at the
Bisognano–Wichmann temperature) that drives the area law, now realized for the photon mode. -/
theorem photon_firstLaw {β ω : ℝ} (h : 0 < β * ω) :
    HasDerivAt boseEntropy (β * ω) (boseEinstein β ω) := by
  have hd := hasDerivAt_boseEntropy (boseEinstein_pos h)
  rwa [boseEinstein_logit h] at hd

end QIQTH.Fock.Photon
