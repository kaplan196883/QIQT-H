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

/-- **The photon helicity operator** `Λ = (+1) on h_{+1}, (−1) on h_{−1}` — the spin projection along the
momentum, `+1` on the positive-helicity sector and `−1` on the negative.  (Massless spin-1: helicity is
`±1`, never `0`.) -/
def helicityOp : (Hplus × Hminus) →ₗ[ℂ] (Hplus × Hminus) :=
  LinearMap.prodMap LinearMap.id (-LinearMap.id)

/-- **The photon helicity squares to the identity: `Λ² = 1` (eigenvalues `±1`).**  The photon is a massless
spin-1 particle with exactly two helicities `±1`; the helicity operator has `Λ² = 1`, its eigenvalues being
`±1` — the spin-1 (vs the would-be longitudinal helicity `0` of a *massive* vector, absent here). -/
theorem helicityOp_sq :
    (helicityOp Hplus Hminus).comp (helicityOp Hplus Hminus) = LinearMap.id := by
  ext p <;> simp [helicityOp]

/-- The **positive-helicity projection** `P_{+1}` onto `h_{+1}` (the `Λ = +1` eigenspace): `(x, y) ↦
(x, 0)`. -/
def helicityProjPlus : (Hplus × Hminus) →ₗ[ℂ] (Hplus × Hminus) :=
  LinearMap.prodMap LinearMap.id 0

/-- The **negative-helicity projection** `P_{−1}` onto `h_{−1}` (the `Λ = −1` eigenspace): `(x, y) ↦
(0, y)`. -/
def helicityProjMinus : (Hplus × Hminus) →ₗ[ℂ] (Hplus × Hminus) :=
  LinearMap.prodMap 0 LinearMap.id

/-- **Helicity `+1` on the positive sector**: `Λ(x, 0) = +1·(x, 0)` — a positive-helicity photon is a
`Λ = +1` eigenvector. -/
@[simp] theorem helicityOp_plus (x : Hplus) :
    helicityOp Hplus Hminus (x, 0) = (x, 0) := by simp [helicityOp]

/-- **Helicity `−1` on the negative sector**: `Λ(0, y) = −1·(0, y) = (0, −y)` — a negative-helicity photon
is a `Λ = −1` eigenvector.  (The two eigenvalues `±1` are the photon's two transverse helicities.) -/
@[simp] theorem helicityOp_minus (y : Hminus) :
    helicityOp Hplus Hminus (0, y) = (0, -y) := by simp [helicityOp]

/-- **The two polarizations resolve the identity: `P_{+1} + P_{−1} = 1`.**  The two transverse helicity
projections sum to the identity on the physical one-particle space `h_γ = h_{+1} ⊕ h_{−1}` — the photon's
**two physical polarizations form a complete set** (no third, longitudinal mode: a resolution of the
identity by exactly the two transverse helicities). -/
theorem helicityProj_complete :
    helicityProjPlus Hplus Hminus + helicityProjMinus Hplus Hminus = LinearMap.id := by
  ext p <;> simp [helicityProjPlus, helicityProjMinus]

/-- The positive-helicity projection is **idempotent** `P_{+1}² = P_{+1}` (a genuine projection). -/
theorem helicityProjPlus_idem :
    (helicityProjPlus Hplus Hminus).comp (helicityProjPlus Hplus Hminus)
      = helicityProjPlus Hplus Hminus := by
  ext p <;> simp [helicityProjPlus]

/-- **The spectral decomposition of the helicity: `Λ = (+1)·P_{+1} + (−1)·P_{−1}`**, i.e.
`Λ = P_{+1} − P_{−1}`.  The helicity operator is its two eigen-projections weighted by the eigenvalues
`±1` — the spectral (eigen-)decomposition of the photon helicity. -/
theorem helicityOp_eq_proj :
    helicityOp Hplus Hminus = helicityProjPlus Hplus Hminus - helicityProjMinus Hplus Hminus := by
  ext p <;> simp [helicityOp, helicityProjPlus, helicityProjMinus]

/-- **The helicity projections are orthogonal: `P_{+1}·P_{−1} = 0`.**  The positive- and negative-helicity
sectors are orthogonal (a photon has a *definite* helicity `+1` or `−1`) — together with completeness
`P_{+1}+P_{−1}=1` and idempotence, the `P_{±1}` form a complete orthogonal system of projections. -/
theorem helicityProj_orthogonal :
    (helicityProjPlus Hplus Hminus).comp (helicityProjMinus Hplus Hminus) = 0 := by
  ext p <;> simp [helicityProjPlus, helicityProjMinus]

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

/-- **For `d` spatial modes per helicity the photon capacity is `C(2d + N, N)`** — the two transverse
polarizations doubling the mode count, the explicit parity-symmetric (`d_{+1} = d_{−1} = d`) form. -/
theorem photon_capacity_two_helicity (d N : ℕ) :
    truncFockDim (2 * d) N = (2 * d + N).choose N :=
  truncFockDim_eq_choose (2 * d) N

/-- **The second polarization enlarges the capacity**: the two-helicity (`2d`-mode) photon Fock has at
least as many states as a single-helicity (`d`-mode) one, `truncFockDim d N ≤ truncFockDim (2d) N`.  Both
transverse polarizations contribute to the photon's regional capacity — it carries *more* information than
a single-component (scalar-like) field of the same per-helicity mode count.  (Via `Nat.choose_le_choose`,
`d + N ≤ 2d + N`.) -/
theorem photon_capacity_helicity_ge (d N : ℕ) :
    truncFockDim d N ≤ truncFockDim (2 * d) N := by
  rw [truncFockDim_eq_choose, truncFockDim_eq_choose]
  exact Nat.choose_le_choose N (by omega)

end QIQTH.Fock.Photon
