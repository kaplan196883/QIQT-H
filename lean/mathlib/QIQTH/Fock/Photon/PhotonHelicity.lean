/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# PHOTON_FIELD_PLAN P1 — the transverse helicity-±1 one-particle space (2 physical polarizations)

The physical photon one-particle space is **transverse**: a massless spin-1 particle has exactly **two**
physical polarizations, the helicities `±1` (`PHOTON_FIELD_PLAN` §0 — build on the positive physical
transverse space, NOT the 4-component indefinite-metric `A_μ`).  Model it as the direct sum of the two
helicity sectors, `h_γ = h_{+1} ⊕ h_{−1}` (here the product type `Hplus × Hminus`).  This module pins the
"2 polarizations" count and feeds it into the photon capacity (P2/P3):

* `photon_helicity_finrank` — `dim h_γ = dim h_{+1} + dim h_{−1}` (the transverse one-particle dimension
  splits over the two helicities).
* `photon_two_polarizations` — for a single momentum mode (one ℂ per helicity) `dim h_γ = 2`: a photon has
  exactly **two** transverse polarizations per momentum (vs the 4 components of `A_μ`, two of which are the
  unphysical gauge/longitudinal modes removed by working on the physical space).
* `photon_capacity_helicity` — the number-cutoff bosonic capacity in terms of the two helicity dimensions:
  `dim Γ_s^{≤N}(h_γ) = C(dim h_{+1} + dim h_{−1} + N, N)` (`truncFockDim` on the helicity-split space).

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Maxwell only.
-/
import QIQTH.Fock.Photon.PhotonFock
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace QIQTH.Fock.Photon

variable (Hplus Hminus : Type*)
  [AddCommGroup Hplus] [Module ℂ Hplus] [Module.Finite ℂ Hplus]
  [AddCommGroup Hminus] [Module ℂ Hminus] [Module.Finite ℂ Hminus]

/-- **The transverse one-particle dimension splits over the two helicities**:
`dim h_γ = dim h_{+1} + dim h_{−1}` for `h_γ = h_{+1} ⊕ h_{−1}`. -/
theorem photon_helicity_finrank :
    Module.finrank ℂ (Hplus × Hminus) = Module.finrank ℂ Hplus + Module.finrank ℂ Hminus :=
  Module.finrank_prod

/-- **A photon has exactly two transverse polarizations per momentum**: `dim (ℂ × ℂ) = 2`.  For a single
momentum mode each helicity contributes one complex dimension, so the physical photon one-particle space
has dimension `2` — the two helicities `±1` (vs the 4 components of `A_μ`, the extra two being the
unphysical gauge/longitudinal modes excluded by working on the positive physical space). -/
theorem photon_two_polarizations : Module.finrank ℂ (ℂ × ℂ) = 2 := by
  rw [Module.finrank_prod, Module.finrank_self]

/-- **The photon capacity over the two helicities**: `dim Γ_s^{≤N}(h_γ) = C(dim h_{+1} + dim h_{−1} + N, N)`.
The number-cutoff bosonic Fock dimension (P2's `truncFockDim_eq_choose`) on the transverse helicity-split
one-particle space — the photon's finite regional capacity counts the two physical polarizations. -/
theorem photon_capacity_helicity (N : ℕ) :
    truncFockDim (Module.finrank ℂ (Hplus × Hminus)) N
      = (Module.finrank ℂ Hplus + Module.finrank ℂ Hminus + N).choose N := by
  rw [truncFockDim_eq_choose, Module.finrank_prod]

end QIQTH.Fock.Photon
