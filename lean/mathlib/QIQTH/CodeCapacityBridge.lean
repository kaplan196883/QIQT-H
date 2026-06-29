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
import QIQTH.FQBoundMicro

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

end AreaBound

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
