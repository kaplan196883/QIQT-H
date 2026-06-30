/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Falsification gate B — the finite Poincaré trace no-go

GPT-5.5-pro QG audit (2026-06-30): a *universal* "finite capacity forbids approximate Lorentz invariance" is
**false** (critical spin chains / QCAs are low-energy counterexamples), so any kill must be **branch-specific**.
This file is gate **B** of the QG campaign (`QG_CAMPAIGN_PLAN.md`): on a *finite-dimensional* Hilbert space there
is **no exact boost generator carrying a genuine (positive) Hamiltonian**.

The boost–translation Poincaré relation `[K, P] = i·H` — a boost generator `K`, a translation generator `P`, the
Hamiltonian `H` — cannot hold in finite dimensions with `H` a nonzero positive(-semidefinite) operator: the trace
of a commutator vanishes, forcing `tr H = 0`, and a positive-semidefinite matrix of trace `0` is `0`. So a finite
matter region carrying an *exact* Poincaré algebra has a **trivial** Hamiltonian — finite capacity can realize
boost covariance only **approximately** (the low-energy / EFT regime), never exactly.

This honestly bounds QIQT-H's finite modular/spectral claims: they are finite-time / low-energy approximations of
the continuum boost flow, not exact realizations. Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

namespace QIQTH.QG

set_option linter.unusedSectionVars false

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The trace of a commutator vanishes:** `tr(KP − PK) = 0`. -/
theorem trace_commutator (K P : Matrix n n ℂ) : (K * P - P * K).trace = 0 := by
  rw [trace_sub, trace_mul_comm K P, sub_self]

/-- **The boost–translation relation forces a traceless Hamiltonian.** If `[K,P] = i·H` on a
finite-dimensional space, then `tr H = 0` — a commutator cannot have nonzero trace, and `i ≠ 0`. -/
theorem trace_eq_zero_of_boost_relation (K P H : Matrix n n ℂ)
    (hrel : K * P - P * K = Complex.I • H) : H.trace = 0 := by
  have h0 : (Complex.I • H).trace = 0 := by rw [← hrel]; exact trace_commutator K P
  rw [trace_smul, smul_eq_mul] at h0
  exact (mul_eq_zero.mp h0).resolve_left Complex.I_ne_zero

/-- **★ Falsification gate B — no exact finite boost generator with a positive Hamiltonian.**
If the boost–translation relation `[K,P] = i·H` holds in finite dimensions with `H` **positive semidefinite**,
then `H = 0`. An exact finite-region Poincaré algebra forces a trivial Hamiltonian; a finite-capacity region
carries boost covariance only approximately. -/
theorem no_exact_finite_boost (K P H : Matrix n n ℂ)
    (hrel : K * P - P * K = Complex.I • H) (hpos : H.PosSemidef) : H = 0 :=
  hpos.trace_eq_zero_iff.mp (trace_eq_zero_of_boost_relation K P H hrel)

/-- **Contrapositive:** a *nonzero* positive-semidefinite Hamiltonian admits **no** exact finite boost generator —
the relation `[K,P] = i·H` is unsatisfiable in finite dimensions. This is the operational form of the no-go:
finite capacity + a genuine (positive, nonzero-energy) Hamiltonian ⟹ boosts cannot be exactly unitary. -/
theorem no_boost_of_pos_ne_zero (H : Matrix n n ℂ) (hpos : H.PosSemidef) (hne : H ≠ 0)
    (K P : Matrix n n ℂ) : K * P - P * K ≠ Complex.I • H :=
  fun hrel => hne (no_exact_finite_boost K P H hrel hpos)

end QIQTH.QG
