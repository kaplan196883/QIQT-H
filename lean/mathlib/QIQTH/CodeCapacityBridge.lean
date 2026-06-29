/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# CODE–CAPACITY BRIDGE — the free field meets QIQT-H's finite microstates

This module connects the **free-field substrate** (CAR `⋀h` / truncated symmetric Fock, records) to the
finite-microstate / holographic-capacity layer `log dim 𝓗_R ≤ A(∂R)/4ℓ_P²` — a real machine-checked link, not a
slogan.  See `CODE_CAPACITY_BRIDGE_PLAN.md`.

HONEST SCOPE (§0 of the plan): **capacity is a CONSTRAINT, not a generator.**  The finite-microstate postulate
does NOT determine Dirac-vs-Maxwell, spin, mass, gauge group, or the gamma matrices — it only bounds the
admissible *code dimension*.  The arrow is `capacity ⟹ upper bound on code dim`, never `capacity ⟹
electron/photon`.  The one genuine "reverse" statement with teeth is the **CAR/CCR finite-capacity dichotomy**
(this file, `no_finiteDim_CCR`): exact finite CCR is impossible, so the photon's bosonic mode cannot live in a
finite-capacity sector without a cutoff — whereas the CAR fermion's `⋀h` is finite and fits exactly.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.InnerProductSpace.PiL2
import QIQTH.FQBoundMicro
import QIQTH.BornEquiprobable

namespace QIQTH.CodeCapacityBridge

open Matrix

section CodeFits

variable {C 𝓗 : Type*}
  [NormedAddCommGroup C] [InnerProductSpace ℂ C] [Module.Finite ℂ C]
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [Module.Finite ℂ 𝓗]

/-- **★ M1 — the code-fitting bound (necessary condition).**  If the field's regional **code space** `C` admits
a (record- and inner-product-preserving) encoding `V : C ↪ 𝓗` into the **microstate space** `𝓗` — a
`LinearIsometry`, hence injective — then its dimension fits: `finrank C ≤ finrank 𝓗`.  This is the substantive
"fits holographically" direction: an encodable field sector cannot have more dimensions than the microstate
space allows.  It chains into the area bound (M4): `S_vN ≤ log finrank C ≤ log finrank 𝓗 ≤ A/4ℓ_P²`.

(The converse — `finrank C ≤ finrank 𝓗 ⟹ such an isometry exists` — holds by orthonormal-basis extension; it is
the labelled follow-on, fiddly `OrthonormalBasis` index-injection bookkeeping, not needed for the bridge's
payoff which takes `V` as a hypothesis.) -/
theorem finrank_le_of_codeIsometry (V : C →ₗᵢ[ℂ] 𝓗) :
    Module.finrank ℂ C ≤ Module.finrank ℂ 𝓗 :=
  V.toLinearMap.finrank_le_finrank_of_injective V.injective

end CodeFits

section Encoding

variable {dC d𝓗 : Type*} [Fintype dC] [DecidableEq dC] [Fintype d𝓗] [DecidableEq d𝓗]

/-- **★ M2 — the encoding preserves record expectations.**  A code encoding into the microstate space is a
matrix isometry `V : d𝓗 × dC` with `Vᴴ V = 1` (columns orthonormal — a Stiefel/partial-isometry encoding).
For any field state `ρ` and any **record** observable `O` on the code space, the encoded expectation equals the
bare one:  `Tr_{𝓗}((VρVᴴ)(VOVᴴ)) = Tr_{C}(ρ O)` (since `VᴴV = 1` collapses the middle: `VρVᴴ·VOVᴴ = Vρ·O·Vᴴ`,
then `Tr` cycles `Vᴴ` to the front).  So encoding the field sector into the holographic microstate space changes
**no record statistic** — the records of the electron/photon are faithfully carried into the microstate
description. -/
theorem encoded_record_expectation (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1) (ρ O : Matrix dC dC ℂ) :
    (V * ρ * Vᴴ * (V * O * Vᴴ)).trace = (ρ * O).trace := by
  have key : V * ρ * Vᴴ * (V * O * Vᴴ) = V * (ρ * O) * Vᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V (O * Vᴴ), hV, Matrix.one_mul]
  rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

/-- The encoded state `VρVᴴ` has unit trace when `ρ` does (`Tr(VρVᴴ) = Tr ρ`) — the encoding maps states to
states (`VᴴV = 1`), a special case of `encoded_record_expectation` with `O = 1`. -/
theorem encoded_trace (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1) (ρ : Matrix dC dC ℂ) :
    (V * ρ * Vᴴ).trace = ρ.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

end Encoding

section AreaBound

open QIQTH.QuantumEntropy

/-- **★★★ M4 — the chained code→capacity area bound (the payoff).**  The field's regional density `ρ` lives on
its own **code space** `dC`, kept SEPARATE from the **microstate space** `𝓗` (= `𝓗_R`); they are connected only
by the *fitting condition* `card dC ≤ card 𝓗` (M1: the field sector encodes into the microstate space).  Then,
under the finite-microstate / holographic postulate `HolographicCapacityBound 𝓗 areaTerm` (`log|𝓗_R| ≤
areaTerm = A/4ℓ_P²`):

  `S_vN(ρ) ≤ log(card dC) ≤ log(card 𝓗) ≤ A/4ℓ_P²`.

So the **free field's regional entropy obeys the holographic area floor once its code sector fits the microstate
space** — the genuine machine-checked link between the electron/photon and QIQT-H's finite microstates.  Note
this does NOT identify the field state space with the microstate space (that would be the slogan): the field
lives on `dC`, the microstates on `𝓗`, and capacity bounds the field only *through the fitting inequality*.
(Contrast `FQBoundMicro.area_floor_vonNeumann`, which puts `ρ` directly on `𝓗`.) -/
theorem encoded_field_entropy_le_area {dC 𝓗 : Type*}
    [Fintype dC] [DecidableEq dC] [Nonempty dC] [Fintype 𝓗] {areaTerm : ℝ}
    [hcap : HolographicCapacityBound 𝓗 areaTerm]
    (hfit : Fintype.card dC ≤ Fintype.card 𝓗)
    {ρ : Matrix dC dC ℂ} (h : IsDensity ρ) :
    vonNeumannEntropy h ≤ areaTerm :=
  calc vonNeumannEntropy h
      ≤ Real.log (Fintype.card dC) := vonNeumannEntropy_le_log_card h
    _ ≤ Real.log (Fintype.card 𝓗) :=
        Real.log_le_log (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast hfit)
    _ ≤ areaTerm := hcap.bound

/-- **★ M5 (electron) — the CAR-Fock instantiation.**  The electron's regional code space is the CAR (exterior)
Fock of `n` one-particle modes, of dimension `2^n` (`Fock/Dirac/CAR.finrank_CARFock`: `dim ⋀h = 2^{finrank h}`),
here realized as `Fin (2^n)`.  If it fits the microstate space (`2^n ≤ |𝓗_R|`), its regional von Neumann entropy
obeys the holographic area floor: `S_vN(ρ) ≤ A/4ℓ_P²`. -/
theorem electron_entropy_le_area {n : ℕ} {𝓗 : Type*} [Fintype 𝓗] {areaTerm : ℝ}
    [HolographicCapacityBound 𝓗 areaTerm] (hfit : 2 ^ n ≤ Fintype.card 𝓗)
    {ρ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (h : IsDensity ρ) :
    vonNeumannEntropy h ≤ areaTerm := by
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  exact encoded_field_entropy_le_area (by simpa using hfit) h

/-- **★ M5 (photon) — the truncated-symmetric-Fock instantiation.**  The photon's regional code space is the
number-cutoff symmetric Fock `Γ_s^{≤N}(h_γ)` of dimension `C(d+N,N)` (`Fock/Photon/PhotonFock.truncFockDim_eq_
choose`), here realized as `Fin (C(d+N,N))`.  If it fits the microstate space (`C(d+N,N) ≤ |𝓗_R|`), its regional
von Neumann entropy obeys the holographic area floor `S_vN(ρ) ≤ A/4ℓ_P²`.  (Without the cutoff `N` the bosonic
Fock is infinite-dimensional — `no_finiteDim_CCR` — so it cannot fit any finite microstate sector.) -/
theorem photon_entropy_le_area {d N : ℕ} {𝓗 : Type*} [Fintype 𝓗] {areaTerm : ℝ}
    [HolographicCapacityBound 𝓗 areaTerm] (hfit : (d + N).choose N ≤ Fintype.card 𝓗)
    {ρ : Matrix (Fin ((d + N).choose N)) (Fin ((d + N).choose N)) ℂ} (h : IsDensity ρ) :
    vonNeumannEntropy h ≤ areaTerm := by
  haveI : NeZero ((d + N).choose N) := ⟨(Nat.choose_pos (Nat.le_add_left N d)).ne'⟩
  exact encoded_field_entropy_le_area (by simpa using hfit) h

end AreaBound

section RecordCapacity

/-- **★ M6 — record capacity ≤ code dimension.**  A family of *perfectly distinguishable* records is an
orthonormal family `e : I → C` of record states (orthonormal ⟹ linearly independent), so their count is bounded
by the code dimension: `|I| ≤ finrank C`.  ("How many distinguishable records the field's regional sector can
carry" is its dimension.) -/
theorem record_card_le_finrank {C : Type*}
    [NormedAddCommGroup C] [InnerProductSpace ℂ C] [Module.Finite ℂ C]
    {I : Type*} [Fintype I] {e : I → C} (he : Orthonormal ℂ e) :
    Fintype.card I ≤ Module.finrank ℂ C :=
  he.linearIndependent.fintype_card_le_finrank

/-- **★★★ M7 — the record→area capstone (Theorem D).**  Combining M6 with the chained area bound: a family of
perfectly distinguishable records `e : I → ℂ^{dC}` in the field's code space, when the code fits the microstate
space (`card dC ≤ |𝓗_R|`) under the holographic postulate, has its **log record count** bounded by the area:

  `log |I| ≤ log(card dC) ≤ log|𝓗_R| ≤ A/4ℓ_P²`.

So the number of macroscopically distinguishable records the electron/photon can carry in a region is
holographically bounded — `log(#records) ≤ A/4ℓ_P²` — once the code sector fits the finite microstate space.
This is the honest culmination of the bridge (capacity bounds the field's records THROUGH the fitting
inequality; it does not generate them). -/
theorem record_log_card_le_area {dC : Type*} [Fintype dC] [DecidableEq dC]
    {𝓗 : Type*} [Fintype 𝓗] {areaTerm : ℝ} [HolographicCapacityBound 𝓗 areaTerm]
    (hfit : Fintype.card dC ≤ Fintype.card 𝓗)
    {I : Type*} [Fintype I] [Nonempty I] {e : I → EuclideanSpace ℂ dC} (he : Orthonormal ℂ e) :
    Real.log (Fintype.card I) ≤ areaTerm := by
  have h1 : Fintype.card I ≤ Module.finrank ℂ (EuclideanSpace ℂ dC) :=
    he.linearIndependent.fintype_card_le_finrank
  rw [finrank_euclideanSpace] at h1
  have hIpos : 0 < Fintype.card I := Fintype.card_pos
  calc Real.log (Fintype.card I)
      ≤ Real.log (Fintype.card dC) :=
        Real.log_le_log (by exact_mod_cast hIpos) (by exact_mod_cast h1)
    _ ≤ Real.log (Fintype.card 𝓗) :=
        Real.log_le_log (by exact_mod_cast lt_of_lt_of_le hIpos h1) (by exact_mod_cast hfit)
    _ ≤ areaTerm := HolographicCapacityBound.bound

end RecordCapacity

section Unification

open QIQTH.BornEquiprobable QIQTH.BornTypicality QIQTH.NoBornFromNothing

/-- **★★★★ The unifying theorem — Born weights AND the area capacity, from ONE microstate fine-graining.**
Take the regional field sector as a finite **equal-amplitude orthonormal fine-graining** `f : I → 𝓗_R` (the
microstate atoms in `𝓗_R = ℂ^{d𝓗}`) with an outcome/record readout `sec : I → K`.  Then the *same* atom set
`I` does **double duty**:

* **(Born, typicality)** — the uniform (equiprobable) measure over the atoms has outcome-marginal *exactly* the
  squared amplitude, `outcomeMarginal sec (1/|I|) k = (sectorAmp f sec k)² = |c_k|²` (the Zurek amplitude→count
  bridge, `uniform_marginal_eq_sectorAmp_sq` — axiom-free; the *canonicity* of this equiprobable measure is the
  named P5 premise);
* **(Capacity, holography)** — under `HolographicCapacityBound 𝓗 areaTerm`, the atom count is area-bounded,
  `log|I| ≤ A/4ℓ_P²` (`record_log_card_le_area`), and hence so is the number of distinguishable records (`|K|`
  realized values, each occupying ≥ 1 atom).

So the **electron's (or photon's) regional records are Born-weighted *and* holographically capacity-bounded by one
and the same microstate count** — capacity is the *ceiling* on the count `|I|`, Born is the *partition* of it into
sector fractions.  This is the honest point of contact between the code–capacity bridge and Born-from-typicality:
the finite microstate fine-graining is simultaneously the capacity bookkeeping and the probability-measure
carrier.  (It remains a statement about the field's *records/states*: it does **not** construct the field, derive
`G`, or remove the P5 / `HolographicCapacityBound` premises.)  Instantiates for the electron (CAR Fock, `|I|≤2^n`)
and the photon (truncated symmetric Fock, `|I|≤C(d+N,N)`). -/
theorem records_born_and_area_bounded
    {d𝓗 : Type*} [Fintype d𝓗] [DecidableEq d𝓗] {areaTerm : ℝ} [HolographicCapacityBound d𝓗 areaTerm]
    {I K : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq K]
    (f : I → EuclideanSpace ℂ d𝓗) (hf : Orthonormal ℂ f) (sec : I → K) :
    (∀ k, outcomeMarginal sec (fun _ => 1 / (Fintype.card I : ℝ)) k = (sectorAmp f sec k) ^ 2)
      ∧ Real.log (Fintype.card I) ≤ areaTerm :=
  ⟨fun k => uniform_marginal_eq_sectorAmp_sq hf sec k,
   record_log_card_le_area (𝓗 := d𝓗) (le_refl _) hf⟩

end Unification

/-- **★ M0 — Exact finite-dimensional CCR is impossible** (the photon needs a cutoff).  On a *nonzero*
finite-dimensional space there are no operators `a, a†` satisfying the canonical commutation relation
`[a, a†] = a a† − a† a = 1`: the trace of any commutator is `0` (`trace(ab) = trace(ba)`), but `trace 1 =
dim H ≠ 0`.

This is the precise, honest sense in which **finite holographic capacity "touches" the photon**: a bosonic
oscillator mode (CCR) **cannot** be realized in a finite-microstate sector — it requires a number/energy cutoff
(the truncated symmetric Fock of the photon plan) or the Type-II renormalized route.  Contrast the **fermion**:
the CAR algebra is finite-dimensional (`⋀h ≅ M_{2ⁿ}`), so it fits a finite-capacity sector exactly.  The single
genuine "reverse" content of the capacity postulate — and it stops here: spin-statistics PROPER needs
locality/Poincaré/positive-energy, NOT capacity. -/
theorem no_finiteDim_CCR {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (a b : Matrix n n ℂ) : a * b - b * a ≠ 1 := by
  intro h
  have htr : (a * b - b * a).trace = 0 := by
    rw [trace_sub, trace_mul_comm a b, sub_self]
  rw [h, trace_one] at htr
  have hcard : (Fintype.card n : ℂ) = 0 := htr
  have : Fintype.card n = 0 := by exact_mod_cast hcard
  exact (Fintype.card_ne_zero) this

end QIQTH.CodeCapacityBridge
