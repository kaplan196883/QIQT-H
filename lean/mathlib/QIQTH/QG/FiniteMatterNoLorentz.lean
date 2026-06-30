/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# D2 — Fork B no-go: literal finite MATTER capacity is incompatible with exact Lorentz + nontrivial dynamics

Phase of `FINITE_MATTER_OR_ENTROPY_PLAN.md` (D2). The red-team forced a fork: does QIQT-H assert finite *matter*
capacity (a literal finite-dimensional regional Hilbert space — Fork B) or only finite *renormalized entropy*
over covariant Type III₁ matter (Fork A)? D1 (`scripts/qg/D1_fork_audit.md`) found QIQT-H's load-bearing
postulate is Fork A (an entropy bound), with Fork B only a heuristic gloss + finite-dim Lean proxy. This file
**confirms Fork B is untenable for exact Lorentz** — strengthening I1 (`FinitePoincareNoGo.no_exact_finite_boost`:
on finite dim, `[K,P]=i·H`, `H⪰0 ⟹ H=0`) to the full (1+1) Poincaré boost–energy–momentum algebra.

**Result.** A finite-dimensional representation of `[K,P]=i·H`, `[K,H]=i·P` with a positive-semidefinite
Hamiltonian `H` forces **`H = 0` AND `P = 0`** — no energy, no momentum, completely trivial dynamics. So a literal
finite-dim matter Hilbert space cannot carry exact Lorentz boosts together with any nonzero positive energy. This
is the rep-theoretic shadow of "non-compact Lorentz has no non-trivial finite-dimensional unitary representation":
finite-dim matter + exact boosts ⟹ no physics. QIQT-H therefore must be **Fork A** (finite entropy/records over a
covariant Type III₁ matter algebra), NOT Fork B. Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).
-/
import QIQTH.QG.FinitePoincareNoGo

namespace QIQTH.QG

set_option linter.unusedSectionVars false

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite-dimensional representation of the `(1+1)` Poincaré boost–energy–momentum relations on a matter
Hilbert space `ℂⁿ`: a boost generator `K`, Hamiltonian `H`, momentum `P`, with `[K,P] = i·H`, `[K,H] = i·P`, and
the Hamiltonian **positive-semidefinite** (`H ⪰ 0` — the spectral condition of a physical energy). -/
structure FinitePoincareRep (n : Type*) [Fintype n] [DecidableEq n] where
  /-- boost generator -/
  K : Matrix n n ℂ
  /-- momentum -/
  P : Matrix n n ℂ
  /-- Hamiltonian -/
  H : Matrix n n ℂ
  /-- `[K,P] = i·H` (the boost of momentum generates energy) -/
  boost_P : K * P - P * K = Complex.I • H
  /-- `[K,H] = i·P` (the boost of energy generates momentum) -/
  boost_H : K * H - H * K = Complex.I • P
  /-- the Hamiltonian is positive-semidefinite -/
  energy_pos : H.PosSemidef

/-- **★ D2 — Fork B no-go.** Any finite-dimensional representation of the boost–energy–momentum relations with a
positive-semidefinite Hamiltonian forces **`H = 0` and `P = 0`** — completely trivial energy and momentum. So a
literal finite-dim matter Hilbert space (Fork B) cannot carry exact Lorentz boosts together with any nonzero
positive energy: the only finite-dim "matter with exact boosts" has no dynamics at all. (`H = 0` is I1's
commutator-trace no-go; then `[K,H] = i·P` with `H = 0` forces `P = 0`.) -/
theorem finitePoincare_trivial (rep : FinitePoincareRep n) : rep.H = 0 ∧ rep.P = 0 := by
  have hH : rep.H = 0 := no_exact_finite_boost rep.K rep.P rep.H rep.boost_P rep.energy_pos
  refine ⟨hH, ?_⟩
  have hb := rep.boost_H
  rw [hH, mul_zero, zero_mul, sub_zero] at hb
  exact (smul_eq_zero.mp hb.symm).resolve_left Complex.I_ne_zero

/-- **Contrapositive — Fork B is unsatisfiable for nontrivial energy.** A nonzero (positive-semidefinite)
Hamiltonian on a finite-dimensional matter space admits **no** consistent exact boost: no `K, P` complete it to a
finite Poincaré representation. Finite matter + exact Lorentz ⟹ the energy is zero. -/
theorem no_finitePoincareRep_of_nontrivial_energy {H : Matrix n n ℂ} (hne : H ≠ 0) :
    ¬ ∃ rep : FinitePoincareRep n, rep.H = H := by
  rintro ⟨rep, rfl⟩
  exact hne (finitePoincare_trivial rep).1

end QIQTH.QG
