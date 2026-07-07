/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The entanglement-entropy AREA LAW for an explicit boundary-local Gaussian model

This file turns the previously-CARRIED assumption `S ∝ A` (the load-bearing input behind the QIQT-H
induced-Newton-constant derivation `1/G = N·Λ_s²`, see `THE_STRONG_G_PLAN.md` steps SG2/SG3/SG5) into a
THEOREM for an EXPLICIT boundary-local Gaussian capacity model, reusing the per-mode Srednicki entropy
`gaussModeEntropy` from `QIQTH.GaussianStateEntropy`.

Model (SG3): the boundary of an `L×L×L` cube is a lattice of `6 L²` plaquettes; each plaquette carries the
SAME `m` normal modes with a boundary-INDEPENDENT symplectic-eigenvalue profile `ν₀ : Fin m → ℝ`.  This
homogeneity IS the boundary-locality hypothesis — carried EXPLICITLY as the choice of index type, NOT an
axiom.  The total boundary entropy sums the per-site `gaussStateEntropy` over all boundary sites, and
factorizes as `(A/a₀²)·(per-site entropy)`: entropy `∝ area`.

## HONEST SCOPE
Proves `S ∝ A` for THIS explicit boundary-local Gaussian model only.  Does **NOT** prove Srednicki's
free-scalar vacuum area law, **NOT** that the actual QIQT-H vacuum realizes this boundary-local model (that
is the remaining physical postulate — sharply isolated by the volume-law guard `bulk_entropy_volume_law`,
which shows finite Gaussian modes give a VOLUME law `∝ L³` unless boundary-localized), **NOT** `Λ_s`,
**NOT** the numerical value of `G`.  Axiom-free.
-/
import Mathlib
import QIQTH.GaussianStateEntropy

namespace QIQTH.BoundaryGaussianAreaLaw

open QIQTH.GaussianStateEntropy

variable {n : ℕ}

/-! ## SG2 — boundary plaquette combinatorics

The boundary of an `L×L×L` cube is `6` faces, each an `L×L` grid of plaquettes: `6 L²` sites. -/

/-- The boundary lattice of an `L×L×L` cube: `6` faces × an `L×L` grid of plaquettes. -/
abbrev CubeBoundary (L : ℕ) := Fin 6 × Fin L × Fin L

/-- **The boundary carries exactly `6 L²` plaquettes** — the discrete area of the cube surface. -/
theorem card_cubeBoundary (L : ℕ) : Fintype.card (CubeBoundary L) = 6 * L ^ 2 := by
  simp [CubeBoundary, Fintype.card_prod, Fintype.card_fin]; ring

/-- The physical (dimensionful) boundary area: number of plaquettes times the lattice cell area `a₀²`. -/
noncomputable def latticeArea (L : ℕ) (a₀ : ℝ) : ℝ := (Fintype.card (CubeBoundary L) : ℝ) * a₀ ^ 2

/-- **Srednicki-adjacent angular-degeneracy identity:** the number of angular modes up to level `L`
    (the odd-integer degeneracies `2l+1`) sums to a perfect square `(L+1)²` — the combinatorial seed of the
    per-shell mode count in the radial-lattice entropy computation. -/
theorem sum_odd_eq_sq (L : ℕ) : (∑ l ∈ Finset.range (L + 1), (2 * l + 1)) = (L + 1) ^ 2 := by
  induction L with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-! ## SG3 — THE boundary-channel AREA-LAW theorem (the core deliverable) -/

/-- The total boundary entanglement entropy: the per-site `gaussStateEntropy ν₀` summed over every boundary
    site `b : B`.  Homogeneity (every site carries the same profile `ν₀`) IS the boundary-locality
    hypothesis, carried explicitly. -/
noncomputable def boundaryEntropy (B : Type*) [Fintype B] {m : ℕ} (ν₀ : Fin m → ℝ) : ℝ :=
  ∑ _b : B, gaussStateEntropy ν₀

/-- The boundary entropy factorizes as `(#sites)·(per-site entropy)`. -/
theorem boundary_entropy_factorizes (B : Type*) [Fintype B] {m : ℕ} (ν₀ : Fin m → ℝ) :
    boundaryEntropy B ν₀ = (Fintype.card B : ℝ) * gaussStateEntropy ν₀ := by
  simp [boundaryEntropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **THE AREA LAW.**  For the boundary-local Gaussian model on an `L×L×L` cube, the total entanglement
    entropy equals `(A/a₀²)·(per-site entropy)`, where `A = latticeArea L a₀ = (#plaquettes)·a₀²` is the
    boundary area.  So `S = (gaussStateEntropy ν₀ / a₀²) · A`: entropy is strictly PROPORTIONAL to area,
    with proportionality constant `gaussStateEntropy ν₀ / a₀²` (per unit area).  The previously-carried
    assumption `S ∝ A` is now a theorem — for this explicit boundary-local model.

    HONEST SCOPE: does not prove that the QIQT-H vacuum realizes this boundary-local model (the remaining
    physical postulate); the volume-law guard `bulk_entropy_volume_law` shows that hypothesis is
    load-bearing (a bulk-local model scales as `L³`, not `L²`). -/
theorem boundary_entropy_area_law (L : ℕ) {m : ℕ} (ν₀ : Fin m → ℝ) (a₀ : ℝ) (ha₀ : a₀ ≠ 0) :
    boundaryEntropy (CubeBoundary L) ν₀ = (latticeArea L a₀ / a₀ ^ 2) * gaussStateEntropy ν₀ := by
  rw [boundary_entropy_factorizes, latticeArea]
  rw [mul_div_assoc, div_self (pow_ne_zero 2 ha₀), mul_one]

/-! ## SG5 — VOLUME-LAW GUARD (vacuity check)

Finite Gaussian modes do NOT automatically give an area law.  A BULK-local model — the SAME per-site
entropy, but summed over the `L³` interior sites instead of the `6 L²` boundary plaquettes — scales as
VOLUME (`L³`).  The contrast `L³` vs `6 L²` proves the boundary-LOCALITY hypothesis in `boundary_entropy_area_law`
is genuinely load-bearing (mirrors the regulator-rigidity guard): it is what turns a would-be volume law
into an area law. -/

/-- The bulk lattice of an `L×L×L` cube: the full `L×L×L` grid of interior sites. -/
abbrev CubeBulk (L : ℕ) := Fin L × Fin L × Fin L

/-- The bulk carries `L³` sites (contrast the boundary's `6 L²`). -/
theorem card_cubeBulk (L : ℕ) : Fintype.card (CubeBulk L) = L ^ 3 := by
  simp [CubeBulk, Fintype.card_prod, Fintype.card_fin]; ring

/-- The bulk entanglement entropy: the same per-site `gaussStateEntropy` summed over the bulk sites. -/
noncomputable def bulkEntropy (B : Type*) [Fintype B] {m : ℕ} (ν₀ : Fin m → ℝ) : ℝ :=
  ∑ _x : B, gaussStateEntropy ν₀

/-- **THE VOLUME-LAW GUARD.**  A bulk-local Gaussian model — identical per-site entropy, summed over the
    interior instead of the boundary — scales as `L³` (VOLUME), not `L²` (area).  This shows that finite
    Gaussian modes do NOT automatically yield an area law: the boundary-LOCALITY hypothesis of
    `boundary_entropy_area_law` is genuinely load-bearing. -/
theorem bulk_entropy_volume_law (L : ℕ) {m : ℕ} (ν₀ : Fin m → ℝ) :
    bulkEntropy (CubeBulk L) ν₀ = (L ^ 3 : ℝ) * gaussStateEntropy ν₀ := by
  rw [bulkEntropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cubeBulk]
  push_cast
  ring

end QIQTH.BoundaryGaussianAreaLaw
