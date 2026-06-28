/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# PHOTON_FIELD_PLAN P6/P10 (bridge) — the field strength `F = dA` is gauge-invariant, and `dF = 0`

The photon's records are the **gauge-invariant** observables, the canonical one being the field strength
`F = dA` (PHOTON_FIELD_PLAN §0; P6 `PhotonGaugeRecords` built this abstractly as the gauge-fixed
subalgebra).  This module pins down the *concrete reason* `F = dA` is gauge-invariant: it is purely the
**`d² = 0`** (cochain / closedness) condition of the exterior derivative.

Model the differential structure as ℂ-linear maps `d_gauge : Λ →ₗ A` (a gauge parameter `Λ` produces the
**pure-gauge** potential `dΛ`) and `d_F : A →ₗ F` (the potential `A` produces the field strength `F = dA`),
with the cochain condition `d_F ∘ d_gauge = 0` (`d² = 0`).  Then:

* `fieldStrength_gauge_invariant` — `F = dA` is **gauge-invariant**: `d_F(A + d_gauge Λ) = d_F A`, because
  the pure-gauge shift `d_gauge Λ` lands in `ker d_F` (the `d² = 0` condition).  This is the concrete
  realization of "records = `F_μν`, not `A_μ`": the potential `A` shifts under gauge, but `F = dA` does not.
* `bianchi_identity` — `d_next(F) = 0` for `F = dA` (with the *next* cochain map `d_next ∘ d_F = 0`): the
  **homogeneous Maxwell equations** `dF = 0` (the Bianchi identity), again a pure `d² = 0` consequence.

So both the gauge-invariance of the photon's field-strength record AND the Bianchi identity are the two
faces of the single cochain condition `d² = 0` — the algebraic backbone of the gauge-invariant observable
structure (the genuine, concrete P6 content; the full continuum Maxwell `F`-net CCR from de Rham test
2-forms is the deferred P10 frontier).

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Maxwell only.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

namespace QIQTH.Fock.Photon

variable {Λ A F G : Type*}
  [AddCommGroup Λ] [AddCommGroup A] [AddCommGroup F] [AddCommGroup G]
  [Module ℂ Λ] [Module ℂ A] [Module ℂ F] [Module ℂ G]

/-- **The field strength `F = dA` is gauge-invariant.**  For the exterior derivative `d_F : A →ₗ F`
(`F = dA`) and the gauge map `d_gauge : Λ →ₗ A` (`Λ ↦ dΛ`, the pure-gauge potentials) satisfying the
cochain condition `d_F ∘ d_gauge = 0` (`d² = 0`), the field strength is unchanged by a gauge transformation
`A ↦ A + d_gauge Λ`: `d_F (a + d_gauge lam) = d_F a`.  The concrete reason the photon's records are the
gauge-invariant `F_μν`, not the gauge-variant potential `A_μ` (PHOTON_FIELD_PLAN §0 / P6). -/
theorem fieldStrength_gauge_invariant (dGauge : Λ →ₗ[ℂ] A) (dF : A →ₗ[ℂ] F)
    (hdd : dF ∘ₗ dGauge = 0) (a : A) (lam : Λ) :
    dF (a + dGauge lam) = dF a := by
  have hker : dF (dGauge lam) = 0 := by
    have h := LinearMap.congr_fun hdd lam
    simpa using h
  rw [map_add, hker, add_zero]

/-- **The Bianchi identity `dF = 0`** (the homogeneous Maxwell equations).  For `F = dA` (`dF : A →ₗ F`)
and the next cochain map `dNext : F →ₗ G` with `dNext ∘ dF = 0` (`d² = 0`), the field strength is closed:
`dNext (dF a) = 0`, i.e. `dF = 0`.  Together with `fieldStrength_gauge_invariant` this exhibits both the
gauge-invariance of `F = dA` and its closedness as the two faces of the single condition `d² = 0`. -/
theorem bianchi_identity (dF : A →ₗ[ℂ] F) (dNext : F →ₗ[ℂ] G)
    (hdd : dNext ∘ₗ dF = 0) (a : A) :
    dNext (dF a) = 0 := by
  have h := LinearMap.congr_fun hdd a
  simpa using h

/-- **The field strength descends to the gauge quotient** — the physical configuration space.  Since the
pure-gauge potentials `range d_gauge` lie in `ker d_F` (the `d²=0` condition), the field strength `F = dA`
factors through the quotient `A ⧸ range d_gauge`: there is a well-defined `F̄ : (A ⧸ range d_gauge) →ₗ F`
with `F̄ ∘ mkQ = d_F` (`Submodule.liftQ`).  So the photon's physical observable (the field strength) is a
genuine function of the **gauge-equivalence class** `[A]`, not of the gauge representative `A` — the
clean statement that the photon's records live on the physical (gauge-quotient) configuration space, the
"records = gauge-invariant" thesis (§0/P6) in its sharpest form. -/
theorem fieldStrength_descends_to_quotient (dGauge : Λ →ₗ[ℂ] A) (dF : A →ₗ[ℂ] F)
    (hdd : dF ∘ₗ dGauge = 0) :
    ((LinearMap.range dGauge).liftQ dF (by
      rw [LinearMap.range_le_ker_iff]; exact hdd)).comp
        (LinearMap.range dGauge).mkQ = dF :=
  (LinearMap.range dGauge).liftQ_mkQ dF _

/-- **The field-strength fibers are `ker d_F` cosets**: two potentials give the same field strength iff
they differ by a **closed** element, `d_F a = d_F a' ↔ a − a' ∈ ker d_F`.  So the configurations with a
given `F` form an affine coset of `ker d_F`. -/
theorem fieldStrength_eq_iff_sub_mem_ker (dF : A →ₗ[ℂ] F) (a a' : A) :
    dF a = dF a' ↔ a - a' ∈ LinearMap.ker dF := by
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- **Closed ⊇ exact: `range d_gauge ≤ ker d_F`** — the `d² = 0` cochain condition as a submodule
inclusion.  The **pure-gauge** (exact) configurations `range d_gauge` are all **closed** (`ker d_F`): a
gauge shift never changes the field strength.  The quotient `ker d_F ⧸ range d_gauge` is the first
cohomology — the **topological / boundary-flux sectors** (the `closed`-but-not-`exact` configurations),
i.e. the algebraic home of the photon's edge-mode center (`PhotonFluxSectors`, P9): nontrivial cohomology
= nontrivial boundary flux.  (For a contractible region the cohomology is trivial — the regional algebra is
a factor, no center; the §0 honest caveat.) -/
theorem pureGauge_le_ker (dGauge : Λ →ₗ[ℂ] A) (dF : A →ₗ[ℂ] F) (hdd : dF ∘ₗ dGauge = 0) :
    LinearMap.range dGauge ≤ LinearMap.ker dF :=
  LinearMap.range_le_ker_iff.mpr hdd

/-- **Trivial cohomology ⟹ `F` determines `A` up to gauge.**  When the first cohomology is trivial — every
**closed** configuration is **exact**, `ker d_F = range d_gauge` (a *contractible* region: no topological
flux sectors, the regional algebra is a *factor*) — two potentials have the same field strength **iff they
are gauge-equivalent**: `d_F a = d_F a' ↔ a − a' ∈ range d_gauge`.  So for a contractible region the
gauge-invariant record `F = dA` is a *complete* invariant of the physical (gauge) configuration — the
honest §0/P9 caveat that the boundary-flux center is present only when the cohomology (the
closed-mod-exact quotient) is nontrivial. -/
theorem fieldStrength_eq_iff_gauge_of_trivial_cohomology (dGauge : Λ →ₗ[ℂ] A) (dF : A →ₗ[ℂ] F)
    (h : LinearMap.ker dF = LinearMap.range dGauge) (a a' : A) :
    dF a = dF a' ↔ a - a' ∈ LinearMap.range dGauge := by
  rw [fieldStrength_eq_iff_sub_mem_ker, h]

end QIQTH.Fock.Photon
