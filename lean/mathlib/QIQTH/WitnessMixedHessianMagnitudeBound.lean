/-
  WitnessMixedHessianMagnitudeBound — J4-862: the MIXED-INDEX (`∂ᵢ∂ⱼ`, `i ≠ j`) pointwise GATE ENVELOPE
  — the off-diagonal companion of `SecondDerivEnvelope.witnessFieldDeriv2_gate_abs_le` (the diagonal E2
  bound), applied to the already-banked mixed value formula `ChartJetHessianMixed.witnessMixed_gate_eq`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  triangle-inequality envelope brick: a MECHANICAL mirror of the diagonal
  `SecondDerivEnvelope.witnessFieldDeriv2_gate_abs_le` proof pattern, applied to the off-diagonal mixed
  on-gate value formula `ChartJetHessianMixed.witnessMixed_gate_eq`.  No `sorry`, no new axioms, no
  vacuous / unsatisfiable hypotheses, no conclusion-in-disguise.

  ── WHAT THE DIAGONAL BOUND DID (`witnessFieldDeriv2_gate_abs_le`, `SecondDerivEnvelope.lean`).  From the
  3-term diagonal formula `∂ᵢ∂ᵢH = G·hs·A + 2·(G·gr)·∂ᵢA + G·∂ᵢ∂ᵢA` and the carried factor sup-bounds
  `|hs|≤Bs2`, `|gr|≤Bs1`, `|A|≤Ba`, `|∂ᵢA|≤Bd`, `|∂ᵢ∂ᵢA|≤Bdd`, pure triangle inequality on the 3 terms
  (with `abs_of_nonneg` on `G := gaussDdim τ (W z p) ≥ 0`) gives `|∂ᵢ∂ᵢH| ≤ G·(Bs2·Ba + 2·Bs1·Bd + Bdd)`.

  ── WHAT THIS FILE DOES (the MIXED analogue, `i ≠ j`).  The banked mixed formula
  `ChartJetHessianMixed.witnessMixed_gate_eq` reads
    `∂ᵢ∂ⱼH = G·hsM·A + (G·grⱼ)·∂ᵢA + (G·grᵢ)·∂ⱼA + G·∂ᵢ∂ⱼA`,
  `hsM := ⟨V,Pi⟩·⟨V,Pj⟩/(4τ²) − (⟨Pi,Pj⟩+⟨V,Q⟩)/(2τ)`, `grⱼ := −⟨V,Pj⟩/(2τ)`, `grᵢ := −⟨V,Pi⟩/(2τ)`.
  The ONE structural difference from the diagonal is that the two gradient terms are now DISTINCT (the
  diagonal `2·(G·gr)·∂ᵢA` splits into `(G·grⱼ)·∂ᵢA + (G·grᵢ)·∂ⱼA`), so the triangle inequality has FOUR
  summands rather than three and carries two independent gradient-scalar / amplitude-gradient sup-bounds.
  From `|hsM|≤Bs2`, `|grⱼ|≤Bsj`, `|grᵢ|≤Bsi`, `|A|≤Ba`, `|∂ᵢA|≤Bdi`, `|∂ⱼA|≤Bdj`, `|∂ᵢ∂ⱼA|≤Bdd` the
  SAME `abs_add_le` / `abs_mul` / `mul_le_mul` combination (one extra summand) delivers
    `|∂ᵢ∂ⱼH| ≤ G·(Bs2·Ba + Bsj·Bdi + Bsi·Bdj + Bdd)`.
  The `1/τ²` / `1/τ` Hessian / gradient singular powers live INSIDE the carried scalar bounds `Bs2`,
  `Bsj`, `Bsi` exactly as in the diagonal case — this brick is purely the magnitude combinator, NOT the
  integrability verdict (which the diagonal `SecondDerivEnvelope §C` supplies one order up).

  ── WHAT THIS FEEDS.  The per-component pointwise magnitude bound `∀ i j, |∂ᵢ∂ⱼH| ≤ G·(…)` is the
  scalar-entry input a downstream combinator (b2) assembles into a full CLM operator-norm bound on the
  mixed field-Hessian `kPrime`, closing the `MixedDirectionsFieldHessianEnvelope` (J4-843) wall that
  `hcomp`'s far-domination leg still carries.  This file supplies ONLY the per-entry scalar bound (b1);
  the CLM assembly (b2) is a separate increment.

  NON-VACUITY.  The hypotheses are exactly those of the already-banked `witnessMixed_gate_eq` (the
  concrete curved gate data whose joint satisfiability is witnessed by the banked mixed-measurability
  chain — genuine first/second field jets and `PdiffAt`s at a gate-interior field point) PLUS seven
  upper-bound side-conditions, which are ALWAYS satisfiable (take each constant equal to the
  corresponding absolute value).  The `witnessMixed_gate_abs_le_tight` corollary makes this explicit:
  instantiating the seven constants at the tightest abs-values needs NOTHING beyond `witnessMixed_gate_eq`'s
  own hypotheses, so the full antecedent set is inhabited exactly when the (non-vacuous) gate data is.
  No conclusion-in-disguise; no J4-548-style unsatisfiable antecedent.  All mains std-3.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetHessianMixed

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open QIQTH.ChartJetHessianMixed
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.WitnessMixedHessianMagnitudeBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ `witnessMixed_gate_abs_le` — THE MIXED (OFF-DIAGONAL) ORDER-2 GATE ENVELOPE.**  From the on-gate
    4-term mixed order-2 formula (`ChartJetHessianMixed.witnessMixed_gate_eq`) and the carried factor
    sup-bounds
      `|hsMixed| ≤ Bs2`, `|grⱼ| ≤ Bsj`, `|grᵢ| ≤ Bsi`, `|A| ≤ Ba`, `|∂ᵢA| ≤ Bdi`, `|∂ⱼA| ≤ Bdj`,
      `|∂ᵢ∂ⱼA| ≤ Bdd`,
    where `hsMixed := ⟨V,Pi⟩·⟨V,Pj⟩/(4τ²) − (⟨Pi,Pj⟩+⟨V,Q⟩)/(2τ)`, `grⱼ := −⟨V,Pj⟩/(2τ)`,
    `grᵢ := −⟨V,Pi⟩/(2τ)`, `V := uniformInverseChart … z p`, the off-diagonal second field-`pd` of the
    gated `N = 1` van-Vleck witness obeys the Gaussian-envelope pointwise bound
      `|∂ᵢ∂ⱼH| ≤ G_τ(W z p)·(Bs2·Ba + Bsj·Bdi + Bsi·Bdj + Bdd)`.
    Pure triangle inequality on the mixed on-gate formula (the E2 pattern, off-diagonal) — the exact
    mirror of `SecondDerivEnvelope.witnessFieldDeriv2_gate_abs_le`, one extra summand from the split
    gradient terms.  The `1/τ²`/`1/τ` singular powers sit INSIDE the carried scalar bounds
    `Bs2`/`Bsj`/`Bsi`.  NOT `a₁ = R/6`. -/
theorem witnessMixed_gate_abs_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pi Pj : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetVi : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (Pi x k) (x i))
    (hJetVj : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x j s) k) (Pj x k) (x j))
    (hJetQ : ∀ k, HasDerivAt
      (fun s : ℝ => Pj (Function.update p i s) k) (Q k) (p i))
    (hAmpj1 : ∀ x, PdiffAt (chartFieldAmp g gi hC hK a b τ z) j x)
    (hAmpi1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) j y) i p)
    (Bs2 Bsj Bsi Ba Bdi Bdj Bdd : ℝ)
    (hSc2 : |(∑ k, uniformInverseChart g gi hC hK z p k * Pi p k)
                * (∑ k, uniformInverseChart g gi hC hK z p k * Pj p k) / (4 * τ ^ 2)
              - ((∑ k, Pi p k * Pj p k)
                  + (∑ k, uniformInverseChart g gi hC hK z p k * Q k)) / (2 * τ)| ≤ Bs2)
    (hScj : |(-(∑ k, uniformInverseChart g gi hC hK z p k * Pj p k) / (2 * τ))| ≤ Bsj)
    (hSci : |(-(∑ k, uniformInverseChart g gi hC hK z p k * Pi p k) / (2 * τ))| ≤ Bsi)
    (hBa : |chartFieldAmp g gi hC hK a b τ z p| ≤ Ba)
    (hBdi : |pd (chartFieldAmp g gi hC hK a b τ z) i p| ≤ Bdi)
    (hBdj : |pd (chartFieldAmp g gi hC hK a b τ z) j p| ≤ Bdj)
    (hBdd : |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) j y) i p| ≤ Bdd) :
    |pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) j y) i p|
      ≤ gaussDdim τ (uniformInverseChart g gi hC hK z p)
          * (Bs2 * Ba + Bsj * Bdi + Bsi * Bdj + Bdd) := by
  rw [witnessMixed_gate_eq g gi hC hK S a b i j τ hτ z hz hSopen p hp Pi Pj Q
      hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2]
  set G := gaussDdim τ (uniformInverseChart g gi hC hK z p) with hGdef
  set hs := (∑ k, uniformInverseChart g gi hC hK z p k * Pi p k)
                * (∑ k, uniformInverseChart g gi hC hK z p k * Pj p k) / (4 * τ ^ 2)
              - ((∑ k, Pi p k * Pj p k)
                  + (∑ k, uniformInverseChart g gi hC hK z p k * Q k)) / (2 * τ) with hsdef
  set grj := -(∑ k, uniformInverseChart g gi hC hK z p k * Pj p k) / (2 * τ) with grjdef
  set gri := -(∑ k, uniformInverseChart g gi hC hK z p k * Pi p k) / (2 * τ) with gridef
  set A := chartFieldAmp g gi hC hK a b τ z p with hAdef
  set dAi := pd (chartFieldAmp g gi hC hK a b τ z) i p with hdAidef
  set dAj := pd (chartFieldAmp g gi hC hK a b τ z) j p with hdAjdef
  set ddA := pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) j y) i p with hddAdef
  have hGnn : 0 ≤ G := gaussDdim_nonneg _ _
  have hBs2nn : 0 ≤ Bs2 := le_trans (abs_nonneg _) hSc2
  have hBsjnn : 0 ≤ Bsj := le_trans (abs_nonneg _) hScj
  have hBsinn : 0 ≤ Bsi := le_trans (abs_nonneg _) hSci
  calc |G * hs * A + (G * grj) * dAi + (G * gri) * dAj + G * ddA|
      ≤ |G * hs * A| + |(G * grj) * dAi| + |(G * gri) * dAj| + |G * ddA| := by
        have h1 := abs_add_le (G * hs * A + (G * grj) * dAi + (G * gri) * dAj) (G * ddA)
        have h2 := abs_add_le (G * hs * A + (G * grj) * dAi) ((G * gri) * dAj)
        have h3 := abs_add_le (G * hs * A) ((G * grj) * dAi)
        linarith
    _ = G * |hs| * |A| + (G * |grj|) * |dAi| + (G * |gri|) * |dAj| + G * |ddA| := by
        simp only [abs_mul, abs_of_nonneg hGnn]
    _ ≤ G * Bs2 * Ba + (G * Bsj) * Bdi + (G * Bsi) * Bdj + G * Bdd := by
        refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hSc2 hGnn) hBa (abs_nonneg _)
            (mul_nonneg hGnn hBs2nn)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hScj hGnn) hBdi (abs_nonneg _)
            (mul_nonneg hGnn hBsjnn)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hSci hGnn) hBdj (abs_nonneg _)
            (mul_nonneg hGnn hBsinn)
        · exact mul_le_mul_of_nonneg_left hBdd hGnn
    _ = G * (Bs2 * Ba + Bsj * Bdi + Bsi * Bdj + Bdd) := by ring

/-- **★ `witnessMixed_gate_abs_le_tight` — NON-VACUITY WITNESS.**  Instantiating the seven sup-bound
    constants of `witnessMixed_gate_abs_le` at their TIGHTEST values (each equal to the corresponding
    absolute value, so every side-condition is `le_refl`) needs NOTHING beyond `witnessMixed_gate_eq`'s
    own hypotheses.  This exhibits the full antecedent set of `witnessMixed_gate_abs_le` as inhabited
    precisely when the (already-banked, non-vacuous) concrete curved gate data holds — no J4-548-style
    unsatisfiable antecedent.  NOT `a₁ = R/6`. -/
theorem witnessMixed_gate_abs_le_tight (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pi Pj : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetVi : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (Pi x k) (x i))
    (hJetVj : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x j s) k) (Pj x k) (x j))
    (hJetQ : ∀ k, HasDerivAt
      (fun s : ℝ => Pj (Function.update p i s) k) (Q k) (p i))
    (hAmpj1 : ∀ x, PdiffAt (chartFieldAmp g gi hC hK a b τ z) j x)
    (hAmpi1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) j y) i p) :
    |pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) j y) i p|
      ≤ gaussDdim τ (uniformInverseChart g gi hC hK z p)
          * (|(∑ k, uniformInverseChart g gi hC hK z p k * Pi p k)
                  * (∑ k, uniformInverseChart g gi hC hK z p k * Pj p k) / (4 * τ ^ 2)
                - ((∑ k, Pi p k * Pj p k)
                    + (∑ k, uniformInverseChart g gi hC hK z p k * Q k)) / (2 * τ)|
              * |chartFieldAmp g gi hC hK a b τ z p|
            + |(-(∑ k, uniformInverseChart g gi hC hK z p k * Pj p k) / (2 * τ))|
              * |pd (chartFieldAmp g gi hC hK a b τ z) i p|
            + |(-(∑ k, uniformInverseChart g gi hC hK z p k * Pi p k) / (2 * τ))|
              * |pd (chartFieldAmp g gi hC hK a b τ z) j p|
            + |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) j y) i p|) :=
  witnessMixed_gate_abs_le g gi hC hK S a b i j τ hτ z hz hSopen p hp Pi Pj Q
    hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2 _ _ _ _ _ _ _
    (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _)

end QIQTH.WitnessMixedHessianMagnitudeBound

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WitnessMixedHessianMagnitudeBound
#print axioms witnessMixed_gate_abs_le
#print axioms witnessMixed_gate_abs_le_tight
end AxiomChecks
