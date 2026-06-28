/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN — PhysLean bridge (the CAR operator-layer dependency)

The remaining frontier of the electron substrate (E2-full creation/annihilation operators, E5 second
quantization) needs the fermionic **CAR field-operator algebra**, which is already formalized in
**PhysLean** (HEPLean): `FieldStatistic` (bosonic/fermionic), `CreateAnnihilate`, `CrAnFieldOp`,
`WickAlgebra`, `SuperCommute` (the graded commutator).  Rather than rebuild that layer, QIQT-H now
depends on PhysLean (pinned to commit `d0ee4af`, whose Mathlib pin `c5ea00351c28 @ v4.30.0` matches
QIQT-H's exactly — no Mathlib bump).

This module is the **bridge**: it imports PhysLean and identifies PhysLean's `ℤ₂` `FieldStatistic` group
with the QIQT-H electron substrate's parity grading `Γ = (−1)^F` / the Clifford `evenOdd` grading
(`QIQTH/Fock/Dirac/DiracGamma.lean`, `Parity.lean`).  Concretely: the electron is `fermionic`; two
fermions combine to `bosonic` (PhysLean) ↔ a product of two odd one-particle generators is even
(`isEven_ι_mul_ι`); and `statParity : FieldStatistic →* ℤ₂` is the grading homomorphism shared by both
sides.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  This establishes the
dependency is live and the statistics align; building the CAR creation/annihilation operators on
PhysLean's `WickAlgebra` is the follow-on E2-full/E5 work.
-/
import Physlib.QFT.PerturbationTheory.FieldStatistics.Basic
import QIQTH.Fock.Dirac.DiracGamma

namespace QIQTH.Fock.Dirac

open FieldStatistic

/-- The electron is a **fermion** (its PhysLean field statistic). -/
def electronStatistic : FieldStatistic := FieldStatistic.fermionic

/-- **Two electrons combine to bosonic statistics**: `fermionic · fermionic = bosonic`.  The
`FieldStatistic`-level mirror of `isEven_ι_mul_ι` (a product of two odd one-particle generators is
even) and of the Clifford fact `diracGamma_mul_mem_even` — identifying PhysLean's `ℤ₂` `FieldStatistic`
group with the CAR parity grading `Γ = (−1)^F`. -/
theorem electron_pair_bosonic : electronStatistic * electronStatistic = FieldStatistic.bosonic :=
  FieldStatistic.fermionic_mul_fermionic

/-- The **ℤ₂ grade** of a field statistic: `bosonic ↦ 0` (even), `fermionic ↦ 1` (odd).  This is the
grading shared by PhysLean's `FieldStatistic` and the QIQT-H substrate's parity / Clifford `evenOdd`
gradings (`diracGamma_mem_odd : γ ∈ evenOdd 1`, `diracGamma_mul_mem_even : γγ ∈ evenOdd 0`). -/
def statParity : FieldStatistic → ZMod 2
  | .bosonic => 0
  | .fermionic => 1

/-- `statParity` is a grading homomorphism: `statParity (a · b) = statParity a + statParity b` — the
`ℤ₂` group structure of `FieldStatistic` is exactly the additive grading the electron substrate uses. -/
@[simp] theorem statParity_mul (a b : FieldStatistic) :
    statParity (a * b) = statParity a + statParity b := by
  cases a <;> cases b <;> decide

/-- The electron carries odd grade `1` — consistent with `diracGamma_mem_odd` (a one-particle gamma is
odd) and with the CAR parity `Γ` acting as `−1` on one-particle states. -/
theorem electron_statParity : statParity electronStatistic = 1 := rfl

end QIQTH.Fock.Dirac
