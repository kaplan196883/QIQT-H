/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The min-cut record bound in ENTROPY form — S_vN ≤ log(min-cut area)

The §2.2 record bound (`RecordMincut.lean`) is a RANK statement: distinguishable records across a cut
`≤` the cut's bond capacity (a zero-error / Schmidt-rank bound).  This file connects it to the
von Neumann ENTROPY area law, via QIQT-H's existing Jensen/Gibbs bound
`QIQTH.vonNeumannEntropy_le_log_card` (`S(ρ) ≤ log(dim 𝓗)`).

Specialized to the **cut channel** `CutAssignments D C` (the finite index type whose cardinality IS
the cut bond capacity `∏_{e∈C} D e`), it reads:

    S_vN(ρ)  ≤  log (cutBondCapacity D C)     (`vonNeumannEntropy_cut_le_log_capacity`)

for ANY density `ρ` on the cut channel — the ENTROPY form of the record bound, with the "area" being
the min-cut bond capacity.  Together with the rank saturation (`distinguishableRecords_id_cutSpace`,
achieved by the maximally-mixed state), this shows the record (rank) bound and the entropy bound are
the *same* min-cut/area bound, seen through `S ≤ log(rank) ≤ log(area)`.

## Scope firewall (HONEST)

This bridges two EXISTING axiom-free QIQT-H results (the min-cut record machinery and the Gibbs
entropy bound); it introduces no new physics.  It is NOT a claim that the physical world is
holographic (min-cut = geometric AREA is Tier-3/OPEN), NOT a continuum limit, NOT emergent spacetime,
NOT QG, NOT numerical-`G`.  The density `ρ` on the cut channel is a carried object; the "area" is the
combinatorial bond capacity, not a geometric area.
-/
import QIQTH.RecordMincut
import QIQTH.FQBoundMicro

namespace QIQTH.RecordMincutEntropy

open QIQTH.RecordMincut

variable {Edge : Type*} [DecidableEq Edge]

/-- **The min-cut record bound in entropy form.**  For any density matrix `ρ` on the cut channel
`CutAssignments D C`, the von Neumann entropy is bounded by the log of the cut's bond capacity:
`S_vN(ρ) ≤ log(∏_{e∈C} D e)`.  This is `QIQTH.vonNeumannEntropy_le_log_card` specialized to the cut
channel (`Fintype.card (CutAssignments D C) = cutBondCapacity D C`), i.e. the ENTROPY form of the
§2.2 record bound. -/
theorem vonNeumannEntropy_cut_le_log_capacity (D : Edge → ℕ) (C : Finset Edge)
    {ρ : Matrix (CutAssignments D C) (CutAssignments D C) ℂ}
    (h : QIQTH.QuantumEntropy.IsDensity ρ) :
    QIQTH.QuantumEntropy.vonNeumannEntropy h ≤ Real.log (cutBondCapacity D C) := by
  have hb := QIQTH.vonNeumannEntropy_le_log_card h
  rwa [cutAssignments_card] at hb

end QIQTH.RecordMincutEntropy
