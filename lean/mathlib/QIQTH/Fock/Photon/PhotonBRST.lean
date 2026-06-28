/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# PHOTON_FIELD_PLAN P10 (foothold) — abstract BRST cohomology `H_Q = ker Q ⧸ im Q`

The covariant (Gupta–Bleuler/BRST) quantization of the photon handles the gauge redundancy + the
indefinite-metric unphysical (longitudinal/temporal/ghost) modes via a **nilpotent BRST charge** `Q`
(`Q² = 0`); the **physical states are the BRST cohomology** `H_Q = ker Q ⧸ im Q` (closed modulo exact), on
which the indefinite metric descends to a positive (physical) inner product.  This module builds the
**algebraic backbone** of that — entirely axiom-free, no indefinite-metric/positivity input:

* `exactToClosed` — `im Q ⊆ ker Q` (`Q² = 0`): every **exact** state (BRST-trivial, a pure gauge/ghost
  shift) is **closed** (BRST-invariant).
* `cohomology Q hQ = ker Q ⧸ im Q` — the BRST cohomology, the home of the **physical photon states** (the
  closed-mod-exact quotient: the two transverse polarizations, with the unphysical modes quotiented out).

This is the single-nilpotent-operator (BRST) formulation, complementing the de Rham two-term
`F = dA` / `d²=0` cohomology of `QIQTH/Fock/Photon/PhotonFieldStrength.lean`.

HONEST scope (PHOTON_FIELD_PLAN §0 / P10): this is the *algebraic* cohomology quotient.  The full
Gupta–Bleuler/BRST construction — the indefinite-metric Krein space, the descent of the metric to a
*positive* form on `H_Q`, the ghost number grading, the no-ghost theorem — is the deferred continuum
frontier (P10), as is the Maxwell `F`-net CCR and the Kabat contact term.  Axiom-free (standard
`propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Maxwell only.
-/
import Mathlib.LinearAlgebra.Quotient.Basic

namespace QIQTH.Fock.Photon.BRST

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- The **closed** (BRST-invariant) states: `ker Q`. -/
def closed (Q : V →ₗ[R] V) : Submodule R V := LinearMap.ker Q

/-- The **exact** (BRST-trivial) states: `im Q`. -/
def exact (Q : V →ₗ[R] V) : Submodule R V := LinearMap.range Q

/-- **Exact ⊆ closed: every exact (BRST-trivial) state is closed (BRST-invariant)**, from the nilpotency
`Q² = 0`.  A pure-gauge/ghost shift `Q ψ` is automatically BRST-invariant. -/
theorem exact_le_closed {Q : V →ₗ[R] V} (hQ : Q.comp Q = 0) : exact Q ≤ closed Q := by
  rintro y ⟨x, rfl⟩
  show Q (Q x) = 0
  have := LinearMap.congr_fun hQ x
  simpa using this

/-- `Q`, corestricted to land in `ker Q` (using `Q² = 0`) — the map whose range is the exact submodule
*viewed inside* the closed states `ker Q`. -/
def exactToClosed (Q : V →ₗ[R] V) (hQ : Q.comp Q = 0) : V →ₗ[R] closed Q :=
  Q.codRestrict (closed Q) (fun v => by
    show Q (Q v) = 0
    have := LinearMap.congr_fun hQ v
    simpa using this)

/-- The exact states as a submodule of the closed states `ker Q` (the image of `exactToClosed`). -/
def exactInClosed (Q : V →ₗ[R] V) (hQ : Q.comp Q = 0) : Submodule R (closed Q) :=
  LinearMap.range (exactToClosed Q hQ)

/-- **The BRST cohomology `H_Q = ker Q ⧸ im Q`** — the physical photon states (closed modulo exact: the
two transverse polarizations, the unphysical longitudinal/temporal/ghost modes quotiented out). -/
abbrev cohomology (Q : V →ₗ[R] V) (hQ : Q.comp Q = 0) : Type _ :=
  closed Q ⧸ exactInClosed Q hQ

/-- **Trivial cohomology ⟺ every closed state is exact** (`ker Q = im Q`).  When the BRST cohomology
vanishes (`exactInClosed = ⊤`) there are no nontrivial physical states beyond the exact ones; nontrivial
`H_Q` is exactly the space of genuine physical (transverse) photon states. -/
theorem cohomology_trivial_iff (Q : V →ₗ[R] V) (hQ : Q.comp Q = 0) :
    exactInClosed Q hQ = ⊤ ↔ ∀ v ∈ closed Q, v ∈ exact Q := by
  constructor
  · intro h v hv
    have : (⟨v, hv⟩ : closed Q) ∈ exactInClosed Q hQ := h ▸ Submodule.mem_top
    obtain ⟨x, hx⟩ := this
    exact ⟨x, congrArg Subtype.val hx⟩
  · intro h
    rw [eq_top_iff]
    rintro ⟨v, hv⟩ -
    obtain ⟨x, hx⟩ := h v hv
    exact ⟨x, Subtype.ext hx⟩

/-- **A BRST-invariant observable preserves the closed (physical) states.**  If `O` commutes with the
BRST charge `Q` (`O∘Q = Q∘O`, i.e. `O` is BRST-invariant / `[O,Q]=0`), then `O` maps `ker Q` into `ker Q`:
a physical (BRST-closed) state stays physical under `O`.  So the **BRST-invariant observables act on the
physical photon states** — `Q(Ov) = O(Qv) = 0`. -/
theorem closed_mem_of_comm {Q O : V →ₗ[R] V} (hO : O.comp Q = Q.comp O) {v : V}
    (hv : v ∈ closed Q) : O v ∈ closed Q := by
  rw [closed, LinearMap.mem_ker] at hv ⊢
  rw [show Q (O v) = O (Q v) by rw [← LinearMap.comp_apply, ← hO, LinearMap.comp_apply], hv, map_zero]

/-- **A BRST-invariant observable preserves the exact (BRST-trivial) states.**  If `O∘Q = Q∘O`, then `O`
maps `im Q` into `im Q` (`O(Qx) = Q(Ox)`): a BRST-trivial state stays BRST-trivial.  Together with
`closed_mem_of_comm`, a BRST-invariant `O` therefore **descends to a well-defined operator on the
cohomology `H_Q`** — the physical observables act on the physical (cohomology) states. -/
theorem exact_mem_of_comm {Q O : V →ₗ[R] V} (hO : O.comp Q = Q.comp O) {v : V}
    (hv : v ∈ exact Q) : O v ∈ exact Q := by
  obtain ⟨x, rfl⟩ := hv
  exact ⟨O x, by rw [← LinearMap.comp_apply, ← hO, LinearMap.comp_apply]⟩

end QIQTH.Fock.Photon.BRST
