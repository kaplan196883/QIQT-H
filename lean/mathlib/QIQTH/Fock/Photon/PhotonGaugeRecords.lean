/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# PHOTON_FIELD_PLAN P6/P7 — the gauge-invariant observable algebra (the photon's records)

Per the PHOTON_FIELD_PLAN crux (§0, GPT-5.5-pro): for the photon, **records and capacity attach to the
GAUGE-INVARIANT observable subalgebra**, not to the raw potential `A_μ`.  The physical records are the
gauge-invariant observables — the field strength `F_μν = ∂_μ A_ν − ∂_ν A_μ`, the stress tensor `T_μν`, the
energy/helicity, Wilson loops — *not* the gauge-variant `A_μ` (which is why one builds on the **positive
physical** Hilbert space `F = dA` / the transverse helicity-±1 modes, never the indefinite-metric `A_μ`).

This is the photon analogue of the electron's **even** (parity-fixed) observable subalgebra
(`QIQTH/Fock/Dirac/EvenObservables.lean`): there records are the `Γ = (−1)^F`-fixed points; here records
are the **gauge-fixed points** — the elements fixed by *every* gauge transformation `gaugeAct Λ`
(the algebra-automorphism lift of `A_μ ↦ A_μ + ∂_μ Λ`).  Same categorical object: the fixed-point
subalgebra of a family of algebra automorphisms.

* **P6** — `IsGaugeInvariant` (a record is fixed by every gauge transformation) and the
  `gaugeInvariantSubalgebra` (closed under `+`, `*`, scalars; the records algebra).  On the physical
  transverse space the gauge action is trivial, so every physical observable IS a record
  (`isGaugeInvariant_of_trivial`) — exactly the point of building on the positive physical Hilbert space.
* **P7** — `isGaugeInvariant_map_of_comm`: any algebra map (e.g. the modular flow `Δ_γ^{it}`,
  `QIQTH/Fock/Photon/PhotonModularFlow.lean`) that **commutes with the gauge action** preserves the
  gauge-invariant records — the photon analogue of `fermiSecondQuantModFlow_isEven` (the modular flow
  keeps records as records).

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Maxwell only.  (The
gauge group's nontrivial action on the unphysical longitudinal/temporal modes — Gupta–Bleuler indefinite
metric — and the boundary-flux *center* / edge modes are the deferred frontier P8–P10.)
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic

namespace QIQTH.Fock.Photon

variable {𝕜 : Type*} [CommSemiring 𝕜] {A : Type*} [Semiring A] [Algebra 𝕜 A]
  {Λ : Type*} (gaugeAct : Λ → A →ₐ[𝕜] A)

/-- An observable is a **gauge-invariant record** iff *every* gauge transformation `gaugeAct Λ` fixes it.
These are the photon's physical records — the field strength `F_μν`, stress tensor `T_μν`, energy/helicity
— per PHOTON_FIELD_PLAN §0.  (The photon analogue of the electron's `IsEven`.) -/
def IsGaugeInvariant (a : A) : Prop := ∀ lam, gaugeAct lam a = a

variable {gaugeAct}

/-- `1` (the vacuum/identity observable) is a gauge-invariant record. -/
theorem isGaugeInvariant_one : IsGaugeInvariant gaugeAct (1 : A) := fun _ => map_one _

/-- `0` is a gauge-invariant record. -/
theorem isGaugeInvariant_zero : IsGaugeInvariant gaugeAct (0 : A) := fun _ => map_zero _

/-- Gauge-invariant records are closed under addition. -/
theorem isGaugeInvariant_add {a b : A} (ha : IsGaugeInvariant gaugeAct a)
    (hb : IsGaugeInvariant gaugeAct b) : IsGaugeInvariant gaugeAct (a + b) :=
  fun lam => by rw [map_add, ha lam, hb lam]

/-- Gauge-invariant records are closed under multiplication (gauge-invariant · gauge-invariant is
gauge-invariant). -/
theorem isGaugeInvariant_mul {a b : A} (ha : IsGaugeInvariant gaugeAct a)
    (hb : IsGaugeInvariant gaugeAct b) : IsGaugeInvariant gaugeAct (a * b) :=
  fun lam => by rw [map_mul, ha lam, hb lam]

/-- Gauge-invariant records are closed under `𝕜`-scaling. -/
theorem isGaugeInvariant_smul (c : 𝕜) {a : A} (ha : IsGaugeInvariant gaugeAct a) :
    IsGaugeInvariant gaugeAct (c • a) :=
  fun lam => by rw [map_smul, ha lam]

/-- Scalars (the image of `algebraMap`) are gauge-invariant records. -/
theorem isGaugeInvariant_algebraMap (c : 𝕜) : IsGaugeInvariant gaugeAct (algebraMap 𝕜 A c) :=
  fun _ => AlgHom.commutes _ _

/-- **The gauge-invariant observable subalgebra** — the gauge-fixed points of the photon field algebra.
This is the algebra to which (per PHOTON_FIELD_PLAN §0) the photon's records and the regional capacity
bound (P2/P3) attach.  Closed under `+`, `*`, contains the scalars.  The photon analogue of the electron's
`evenSubalgebra`. -/
def gaugeInvariantSubalgebra (gaugeAct : Λ → A →ₐ[𝕜] A) : Subalgebra 𝕜 A where
  carrier := {a | IsGaugeInvariant gaugeAct a}
  mul_mem' ha hb := isGaugeInvariant_mul ha hb
  one_mem' := isGaugeInvariant_one
  add_mem' ha hb := isGaugeInvariant_add ha hb
  zero_mem' := isGaugeInvariant_zero
  algebraMap_mem' := isGaugeInvariant_algebraMap

@[simp] theorem mem_gaugeInvariantSubalgebra {a : A} :
    a ∈ gaugeInvariantSubalgebra gaugeAct ↔ IsGaugeInvariant gaugeAct a := Iff.rfl

/-- **On the physical transverse space, every observable is a record.**  If the gauge action is trivial
(`gaugeAct Λ = id` for all `Λ`) — as it is on the *positive physical* (transverse / helicity-±1) Hilbert
space, where the gauge redundancy is already quotiented out — then every observable is gauge-invariant.
This is exactly why one builds the photon substrate on the physical space (`F = dA`), never the
indefinite-metric `A_μ`: there the physical observables are manifestly records. -/
theorem isGaugeInvariant_of_trivial (htriv : ∀ lam, gaugeAct lam = AlgHom.id 𝕜 A) (a : A) :
    IsGaugeInvariant gaugeAct a :=
  fun lam => by rw [htriv lam, AlgHom.id_apply]

/-- **P7 — an algebra map commuting with the gauge action preserves records.**  If `σ : A →ₐ A` commutes
with every gauge transformation (`σ ∘ gaugeAct Λ = gaugeAct Λ ∘ σ`), then `σ` carries gauge-invariant
records to gauge-invariant records.  Applied to the photon modular flow `Δ_γ^{it}` (`photonModFlow`),
which is gauge-blind on the physical space (it commutes with the gauge action — trivially so on the
transverse space): **the modular dynamics keeps records as records**, the photon analogue of the
electron's `fermiSecondQuantModFlow_isEven`.  So the photon's gauge-invariant records (`F_μν`, `T_μν`) are
conserved by the boost/modular flow `σ_t`. -/
theorem isGaugeInvariant_map_of_comm (σ : A →ₐ[𝕜] A)
    (hcomm : ∀ lam, σ.comp (gaugeAct lam) = (gaugeAct lam).comp σ)
    {a : A} (ha : IsGaugeInvariant gaugeAct a) : IsGaugeInvariant gaugeAct (σ a) := by
  intro lam
  have h := AlgHom.congr_fun (hcomm lam) a
  simp only [AlgHom.comp_apply] at h
  rw [ha lam] at h
  exact h.symm

end QIQTH.Fock.Photon
