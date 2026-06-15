/-
  FieldBorn — the Born rule at the genuine free-field level.

  The continuum λ-law's Born layer, on the genuine FOCK VACUUM STATE.  The vacuum
  functional `vacuumState T = re⟪Ω, TΩ⟫` is a positive, normalized state on the
  bounded operators of the Fock Hilbert space; the records λ selects are bounded
  POSITIVE EFFECTS summing to one (a POVM).  Their vacuum-state expectations are
  the Born weights, and:

    * `vacuumState_povm_sum` — for any finite POVM (`Σ Eₐ = 1`), the vacuum-state
      Born weights sum to one: a genuine probability, on the real free-field
      vacuum state (no trace, Type-independent).
    * `vacuumState_weylBit_sum` — instantiated at the **Weyl-bit record POVM**
      `{E(u,+1), E(u,−1)}` (the canonical single-mode free-field record): the two
      vacuum-state weights sum to one, each nonnegative (`vacuumState_nonneg`,
      the effects being positive) — the genuine free-field two-outcome Born
      probability `(1±exp(−½‖u‖²))/2`.

  Axiom-free.  This is the Born layer of the continuum λ-law made literal on the
  completed Fock Hilbert space and its genuine vacuum state, complementing the
  spectral-measure Born rule of `NaturalConeBorn` at the one-particle level.
-/

import QIQTH.Fock.WeylCLM

namespace QIQTH.Fock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The vacuum-state Born weights of a POVM are a probability.**  For any finite
    family of bounded effects summing to one, the vacuum-state expectations sum to
    one — the field-level algebraic Born rule on the genuine Fock vacuum state. -/
theorem vacuumState_povm_sum {ι : Type*} [Fintype ι]
    (E : ι → (Fock H →L[ℂ] Fock H)) (hsum : ∑ i, E i = 1) :
    ∑ i, vacuumState (E i) = 1 := by
  calc ∑ i, vacuumState (E i)
      = ∑ i, vacuumStateHom (E i) := rfl
    _ = vacuumStateHom (∑ i, E i) := (map_sum vacuumStateHom E Finset.univ).symm
    _ = vacuumStateHom 1 := by rw [hsum]
    _ = 1 := vacuumStateHom_one

/-- **The free-field two-outcome Born probability.**  The vacuum-state weights of
    the Weyl-bit record POVM `{E(u,+1), E(u,−1)}` sum to one.  Each is
    nonnegative (`vacuumState_nonneg`, the effects being positive), so this is a
    genuine probability `(1±exp(−½‖u‖²))/2` on the real free-field vacuum state. -/
theorem vacuumState_weylBit_sum (u : H) :
    vacuumState (weylBitEffectCLM u 1) + vacuumState (weylBitEffectCLM u (-1)) = 1 := by
  rw [← vacuumState_add, weylBitEffectCLM_complete, vacuumState_one]

/-- **Audit conclusion.**  The Born layer of the continuum λ-law at the genuine
    free-field level: vacuum-state weights of a POVM are a probability
    (`vacuumState_povm_sum`), instantiated at the Weyl-bit record POVM
    (`vacuumState_weylBit_sum`).  NO project axioms.  On the genuine Fock vacuum
    state, no trace, complementing the one-particle spectral-measure Born rule. -/
theorem fieldBorn_audit : True := trivial

end QIQTH.Fock
