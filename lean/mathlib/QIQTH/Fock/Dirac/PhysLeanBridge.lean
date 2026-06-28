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
import Physlib.QFT.PerturbationTheory.FieldStatistics.ExchangeSign
import Physlib.QFT.PerturbationTheory.FieldSpecification.Basic
import Physlib.QFT.PerturbationTheory.WickAlgebra.SuperCommute
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

/-- **The electron exchange sign is `−1`**: `𝓢(fermionic, fermionic) = −1` (PhysLean
`exchangeSign`).  This is exactly the graded-commutation sign `(−1)^{|F₁||F₂|}` of the
ELECTRON_FIELD crux `F₁F₂ = (−1)^{|F₁||F₂|} F₂F₁` for two fermions — the same `−1` that appears in the
substrate's one-particle anticommutation `ι_mul_ι_swap : ι a · ι b = −(ι b · ι a)`.  So PhysLean's
exchange-sign machinery and the QIQT-H CAR anticommutation carry the identical Pauli sign. -/
theorem electron_exchangeSign :
    FieldStatistic.exchangeSign electronStatistic electronStatistic = -1 := by
  rw [FieldStatistic.exchangeSign_eq_if]
  simp [electronStatistic]

/-- **The electron field specification** in PhysLean's framework: a single field, **fermionic**, with
trivial position/asymptotic labels (the minimal free-Dirac content).  This is the `FieldSpecification`
on which PhysLean's `CrAnFieldOp` / `WickAlgebra` / `superCommute` (the CAR creation/annihilation
operator layer) are built — the entry point to the QIQT-H E2-full / E5 operator tier. -/
def electronFieldSpec : FieldSpecification where
  Field := Unit
  PositionLabel := fun _ => Unit
  AsymptoticLabel := fun _ => Unit
  statistic := fun _ => FieldStatistic.fermionic

/-- The electron field is **fermionic** (its statistic in the PhysLean field specification) — matching
`electronStatistic` and the substrate's odd/CAR grading. -/
@[simp] theorem electronFieldSpec_statistic (f : electronFieldSpec.Field) :
    electronFieldSpec.statistic f = FieldStatistic.fermionic := rfl

/-! ### CAR relations for the electron (via PhysLean's `superCommute`)

For the fermionic electron the **super-commutator `[·,·]ₛ` IS the anticommutator** (the graded commutator
with exchange sign `−1`, `electron_exchangeSign`).  PhysLean's `WickAlgebra.superCommute` then yields the
canonical anticommutation (CAR) relations for the electron's creation/annihilation operators — the
E2-full/E5 operator content. -/

open FieldSpecification FieldSpecification.WickAlgebra in
/-- **Pauli exclusion `{a†, a†} = 0`**: the super-commutator (= anticommutator) of two electron
*creation* operators vanishes — two electrons cannot be created in the same mode. -/
theorem electron_create_create_zero {φ φ' : electronFieldSpec.CrAnFieldOp}
    (h : (electronFieldSpec |>ᶜ φ) = .create) (h' : (electronFieldSpec |>ᶜ φ') = .create) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ = 0 :=
  superCommute_create_create h h'

open FieldSpecification FieldSpecification.WickAlgebra in
/-- **`{a, a} = 0`**: the super-commutator (= anticommutator) of two electron *annihilation* operators
vanishes — the Pauli relation for annihilation operators. -/
theorem electron_annihilate_annihilate_zero {φ φ' : electronFieldSpec.CrAnFieldOp}
    (h : (electronFieldSpec |>ᶜ φ) = .annihilate) (h' : (electronFieldSpec |>ᶜ φ') = .annihilate) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ = 0 :=
  superCommute_annihilate_annihilate h h'

open FieldSpecification FieldSpecification.WickAlgebra in
/-- **The anticommutator is a c-number**: the super-commutator of any two electron creation/annihilation
operators lies in the centre of the algebra — the defining CAR property that `{a, a†}` is a scalar (the
one-particle inner product), not an operator. -/
theorem electron_superCommute_mem_center (φ φ' : electronFieldSpec.CrAnFieldOp) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ ∈ Subalgebra.center ℂ (WickAlgebra electronFieldSpec) :=
  superCommute_ofCrAnOp_ofCrAnOp_mem_center φ φ'

open FieldSpecification FieldSpecification.WickAlgebra in
/-- **The CAR anticommutator `{a, a†}` for the electron.**  Because the electron is fermionic (exchange
sign `−1`, `electron_exchangeSign`), PhysLean's super-commutator of the **annihilation** part `anPart φ`
(`a`) and the **creation** part `crPart φ'` (`a†`) of two field operators is literally the
*anticommutator* (the `+` sign):
`[anPart φ, crPart φ']ₛ = anPart φ · crPart φ' + crPart φ' · anPart φ`.
This is the defining nonzero CAR relation `{a(φ), a†(φ')}` — the kinematic heart of the electron's
second quantization. -/
theorem electron_anPart_crPart_anticomm (φ φ' : electronFieldSpec.FieldOp) :
    [anPart φ, crPart φ']ₛ = anPart φ * crPart φ' + crPart φ' * anPart φ := by
  rw [superCommute_anPart_crPart]
  have hs : FieldStatistic.exchangeSign (electronFieldSpec |>ₛ φ) (electronFieldSpec |>ₛ φ') = -1 := by
    rw [show (electronFieldSpec |>ₛ φ) = FieldStatistic.fermionic from rfl,
        show (electronFieldSpec |>ₛ φ') = FieldStatistic.fermionic from rfl,
        FieldStatistic.exchangeSign_eq_if]
    simp
  rw [hs, neg_one_smul, neg_mul, sub_neg_eq_add]

end QIQTH.Fock.Dirac
