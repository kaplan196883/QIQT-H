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

namespace QIQTH.CodeCapacityBridge

open Matrix

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
