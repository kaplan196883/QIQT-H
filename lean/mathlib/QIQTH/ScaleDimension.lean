/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# SCALE AS DIMENSION — the RG-scale radial rung (duality campaign, brick D5a)

The held single-scale entanglement→distance reconstruction (`QIQTH.EmergentSpacetime`,
`weightedCutDist` + `IsApproxPseudometric`) is **spatial** and lives at ONE refinement scale.
This file adds the **radial / RG-scale direction** (Maldacena's `U` = RG scale): the QIQT-H
refinement tower's *forced log-additive* invariant canonically supplies a radial LINE, and the
held cut metric extends to a **bulk pseudometric on `X × ℕ`** (boundary site × refinement scale)
whose SLICES are the boundary metric and whose FIBERS are additive RG-depth geodesics.

## MANDATORY FIREWALL (binding scope)

* D5a is a **KINEMATIC radial coordinate**: the forced log-additive refinement invariant canonically
  supplies a radial LINE, and the held cut metric extends to a bulk PSEUDOMETRIC on `X × ℕ` whose
  slices are the boundary metric and whose fibers are additive RG-depth geodesics.
* It does **NOT** establish AdS curvature, a warp factor, the Einstein equations, RT/HRT surfaces,
  causal/Lorentzian structure, or dynamics. The `L¹` product is a **CHOSEN no-warp extension** (not a
  derived warp factor); `forcedWeight` is carried as a nonneg parameter (the tower's `κ·log(ratio)`
  invariant is the intended instance). **Pseudometric (not metric)** — no separation is claimed.
* Finite/kinematic. NOT the conjecture, NOT the strong holographic principle, NOT QG.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`). No `sorry`.
-/
import QIQTH.EmergentSpacetime

namespace QIQTH.ScaleDimension

open QIQTH.EmergentSpacetime

/-!
## PART A — THE RADIAL LINE (the RG-depth coordinate)

The tower's per-stage forced weight (the QIQT-H refinement tower's `κ·log(ratio)` invariant) is
carried here as a nonnegative parameter `forcedWeight : ℕ → ℝ`.  Accumulating it gives the radial
RG depth, and `|Λ k − Λ l|` is the 1-D radial-line distance.
-/

/-- The accumulated RG depth `Λ(k) = ∑_{n<k} forcedWeight n` (log-additive along the tower). -/
def radialDepth (forcedWeight : ℕ → ℝ) (k : ℕ) : ℝ := ∑ n ∈ Finset.range k, forcedWeight n

/-- The radial-line distance `|Λ k − Λ l|`. -/
def radialDist (Λ : ℕ → ℝ) (k l : ℕ) : ℝ := |Λ k - Λ l|

theorem radialDist_nonneg (Λ : ℕ → ℝ) (k l : ℕ) : 0 ≤ radialDist Λ k l := abs_nonneg _

theorem radialDist_self (Λ : ℕ → ℝ) (k : ℕ) : radialDist Λ k k = 0 := by simp [radialDist]

theorem radialDist_symm (Λ : ℕ → ℝ) (k l : ℕ) : radialDist Λ k l = radialDist Λ l k := by
  simp [radialDist, abs_sub_comm]

theorem radialDist_triangle (Λ : ℕ → ℝ) (i j k : ℕ) :
    radialDist Λ i k ≤ radialDist Λ i j + radialDist Λ j k := by
  unfold radialDist
  have h : Λ i - Λ k = (Λ i - Λ j) + (Λ j - Λ k) := by ring
  calc |Λ i - Λ k| = |(Λ i - Λ j) + (Λ j - Λ k)| := by rw [h]
    _ ≤ |Λ i - Λ j| + |Λ j - Λ k| := abs_add_le _ _

/-- `radialDepth` is monotone (forced weights are nonneg) — needed for ordered radial additivity. -/
theorem radialDepth_monotone (forcedWeight : ℕ → ℝ) (hfw : ∀ n, 0 ≤ forcedWeight n) :
    Monotone (radialDepth forcedWeight) := by
  intro k l hkl
  unfold radialDepth
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl) ?_
  intro n _ _; exact hfw n

/-- **★ ORDERED RADIAL ADDITIVITY.**  Along the (monotone) RG-depth coordinate, radial length is the
*accumulated* RG content between scales — the radial geodesic depth adds along `k ≤ l ≤ m`. -/
theorem radialDist_add_of_monotone (Λ : ℕ → ℝ) (hΛ : Monotone Λ) {k l m : ℕ}
    (hkl : k ≤ l) (hlm : l ≤ m) :
    radialDist Λ k m = radialDist Λ k l + radialDist Λ l m := by
  have hkl' : Λ k ≤ Λ l := hΛ hkl
  have hlm' : Λ l ≤ Λ m := hΛ hlm
  have hkm' : Λ k ≤ Λ m := le_trans hkl' hlm'
  unfold radialDist
  rw [abs_of_nonpos (sub_nonpos.mpr hkm'), abs_of_nonpos (sub_nonpos.mpr hkl'),
    abs_of_nonpos (sub_nonpos.mpr hlm')]
  ring

/-!
## PART B — THE BULK PRODUCT PSEUDOMETRIC (spatial ⊕ radial, `L¹`)

The bulk distance on `X × ℕ` (boundary site × refinement scale) is the `L¹` sum of the held spatial
cut metric `dX` and the radial RG line `radialDist Λ`.  This is a **chosen no-warp extension** — no
warp factor is derived (see firewall).
-/

/-- The bulk distance on `X × ℕ`: spatial cut metric `dX` plus radial RG line `radialDist Λ`. -/
def scaleProdDist {X : Type*} (dX : X → X → ℝ) (Λ : ℕ → ℝ) : X × ℕ → X × ℕ → ℝ :=
  fun p q => dX p.1 q.1 + radialDist Λ p.2 q.2

/-- **★★ The bulk product is a genuine (exact) pseudometric**, given the held spatial one. -/
theorem scaleProd_isPseudometric {X : Type*} (dX : X → X → ℝ) (Λ : ℕ → ℝ)
    (hX : IsApproxPseudometric 0 dX) :
    IsApproxPseudometric 0 (scaleProdDist dX Λ) where
  nonneg := fun p q => add_nonneg (hX.nonneg _ _) (radialDist_nonneg Λ _ _)
  self := fun p => by simp [scaleProdDist, hX.self, radialDist_self]
  symm := fun p q => by rw [scaleProdDist, scaleProdDist, hX.symm, radialDist_symm Λ p.2 q.2]
  triangle := fun p q r => by
    have h1 := hX.triangle p.1 q.1 r.1
    have h2 := radialDist_triangle Λ p.2 q.2 r.2
    simp only [scaleProdDist]
    linarith

@[simp] theorem scaleProd_slice {X : Type*} (dX : X → X → ℝ) (Λ : ℕ → ℝ) (x y : X) (k : ℕ) :
    scaleProdDist dX Λ (x, k) (y, k) = dX x y := by
  simp [scaleProdDist, radialDist_self]

@[simp] theorem scaleProd_fiber {X : Type*} (dX : X → X → ℝ) (Λ : ℕ → ℝ)
    (hself : ∀ x, dX x x = 0) (x : X) (k l : ℕ) :
    scaleProdDist dX Λ (x, k) (x, l) = radialDist Λ k l := by
  simp [scaleProdDist, hself]

/-!
## PART C — THE D5a CAPSTONE

Grounded in the held `weightedCutDist`: the single-scale cut metric extends to a bulk pseudometric on
`X × ℕ` whose slices recover the boundary metric and whose fibers are additive RG-depth geodesics.
-/

/-- **★★ SCALE AS DIMENSION (D5a).**  The held single-scale cut metric `weightedCutDist ω χ` extends
to a bulk pseudometric on `X × ℕ` (boundary site × refinement scale) whose

* **slices** (fixed scale `k`) are exactly the boundary metric, and
* **fibers** (fixed site `x`) are the radial RG-depth line, which is **additive** along `k ≤ l ≤ m`.

The radial coordinate is the accumulated forced-weight invariant `radialDepth forcedWeight`.

Note (binder deviation): the ordered-additivity conjunct uses **explicit** binders
`∀ x (k l m : ℕ)` (rather than the implicit `∀ x {k l m}` sketched in the design) to avoid a
`let`+`∀`+implicit-binder interaction; the mathematical content is identical. -/
theorem scaleAsDimension {I X : Type*} [Fintype I] (ω : I → ℝ) (χ : I → X → ℝ)
    (hω : ∀ i, 0 ≤ ω i) (forcedWeight : ℕ → ℝ) (hfw : ∀ n, 0 ≤ forcedWeight n) :
    let Λ := radialDepth forcedWeight
    IsApproxPseudometric 0 (scaleProdDist (weightedCutDist ω χ) Λ)
    ∧ (∀ k x y, scaleProdDist (weightedCutDist ω χ) Λ (x, k) (y, k) = weightedCutDist ω χ x y)
    ∧ (∀ x k l, scaleProdDist (weightedCutDist ω χ) Λ (x, k) (x, l) = radialDist Λ k l)
    ∧ (∀ x (k l m : ℕ), k ≤ l → l ≤ m →
        scaleProdDist (weightedCutDist ω χ) Λ (x, k) (x, m)
          = scaleProdDist (weightedCutDist ω χ) Λ (x, k) (x, l)
            + scaleProdDist (weightedCutDist ω χ) Λ (x, l) (x, m)) := by
  intro Λ
  have hself : ∀ x, weightedCutDist ω χ x x = 0 := weightedCutDist_self ω χ
  have hmono : Monotone Λ := radialDepth_monotone forcedWeight hfw
  refine ⟨scaleProd_isPseudometric _ _ (weightedCutDist_isPseudometric hω), ?_, ?_, ?_⟩
  · intro k x y; exact scaleProd_slice _ _ x y k
  · intro x k l; exact scaleProd_fiber _ _ hself x k l
  · intro x k l m hkl hlm
    rw [scaleProd_fiber _ _ hself x k m, scaleProd_fiber _ _ hself x k l,
      scaleProd_fiber _ _ hself x l m]
    exact radialDist_add_of_monotone Λ hmono hkl hlm

end QIQTH.ScaleDimension
