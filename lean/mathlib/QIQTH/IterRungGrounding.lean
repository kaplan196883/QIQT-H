/-
  IterRungGrounding — J4-474: GROUND THE `htermBox` RUNG CARRIES `hIterBase` + `hIterStep`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  continues the box-census surface reduction: J4-473 (`BoxAtomsGrounding`) reduced the census
  `htermBox` atom to the two x-slot RUNG carries of `IterEContinuity.iterE_jointContinuousOn` —
  `hIterBase` (the k=0 rung, `E = iterE E 1` itself on the box) and `hIterStep` (the per-level
  Duhamel-convolution step).  This brick grounds those two rung carries ONE LEVEL DOWN, onto their
  honest lower-level suppliers, at the transport granularity of the individual carries.

  ── `hIterBase` (THE BASE RUNG).  ⚠ SLOT RE-AUDIT (dont-undercredit) — THE GATE.  The census base is
       the **x-slot** heat operator `p ↦ E p.1 p.2 0 = heatOp g gi Wit p.1 p.2 0` (varying spatial
       variable `p.2` in the FIRST slot, `y` frozen at `0`).  Unfolding `heatOp` at `(x := p.2, y := 0)`:
          `heatOp g gi Wit p.1 p.2 0
             = deriv (fun u => Wit u p.2 0) p.1 − laplaceBeltrami g gi (fun q => Wit p.1 q 0) p.2`,
       so the Laplacian's BASE POINT is `p.2` (VARYING).  The banked N2 supplier
       `NonLeviBoxContinuity.heatOp_slice_continuousOn_box_of_parts` is the OTHER (z-slot) orientation
       `heatOp g gi Wit p.1 0 p.2` — its Laplacian base is the FIXED `0` (which makes the metric /
       Christoffel factors CONSTANTS, cf. N3).  So N2 does **NOT** transport to the x-slot base: the
       base-point differs (`0` fixed vs `p.2` varying) — exactly the base-keying mismatch the J4-473
       `hpd2diag` transparency re-audit flagged.  What DOES transport is N2's ROUTE, re-oriented:
       `heatOp` unfold + `ContinuousOn.sub` reduces the x-slot base to two x-slot part carries
       (`hDerivX` = the `∂_τ` x-slot slice; `hLapX` = the varying-base Laplacian x-slot slice).
       Genuine reduction; the two parts are honest carries, neither the conclusion.

  ── `hIterStep` (THE CONVOLUTION RUNG).  GENUINE WIRE — THE GATE.  The step is the per-level implication
       `ContinuousOn (iterE E (k+1)) box → ContinuousOn (iterE E (k+2)) box`.  Since `iterE E (k+2)
       = heatConv E (iterE E (k+1))`, the banked OUTER engine
       `IterEContinuity.iterE_succ_jointContinuousOn_of_dominated` PRODUCES the succ rung outright from
       the per-rung fixed-domain (`Ioc 0 1`) Gaussian domination data (`hmeas/hbound/hbnd_int/hcont` at
       `A = E`, `B = iterE E (k+1)`).  ⚠ DOMINATION GATE (dont-undercredit): the banked census
       dominations (`CensusDominations` D2 heat-kernel Gaussian `hAdomHeat`, the `leviSeries`-pairing
       s-slice bounds) are NOT in this per-rung `heatConv`-outer-engine shape (the `∫ w, E·iterE E k`
       inner integral over `Ioc 0 1`); they are the honest R-dom residual named by `IterEContinuity`.
       So the per-rung dominations are CARRIED, and the step is produced from them per rung.

  ── WHAT LANDS.
    • `hIterBase_grounded`   — ★★★ the census `hIterBase` rung, PRODUCED from the two x-slot part carries
        (`hDerivX` + `hLapX`) via the N2 route re-oriented to the x-slot.  Honest reduction.
    • `hIterStep_grounded`   — ★★★ the census `hIterStep` rung, PRODUCED from the per-rung Gaussian
        domination data via the banked `iterE_succ_jointContinuousOn_of_dominated`.  Genuine wire.
    • `htermBox_chain_final` — ★★★ THE END-TO-END CHAIN: from the deepest x-slot carries + per-rung
        dominations, the ENTIRE census `htermBox` family (`∀ k`) via `BoxAtomsGrounding.htermBox_grounded`.
    • `rung_residuals` (+ intro) — the enumerated surviving surface after the two rung groundings.

  NO `sorry`, NO `:= True`, NO new axioms; std-3 only.  No existing file edited.
  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.BoxAtomsGrounding
import QIQTH.NonLeviBoxContinuity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.IterEContinuity QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LaplaceBeltrami
open scoped Topology Interval BigOperators

namespace QIQTH.IterRungGrounding

variable {n : ℕ}

/-! ###############################################################################
    ### ★★★ `hIterBase_grounded` — the census BASE rung, from x-slot `∂_τ` + Laplacian parts.
    ############################################################################### -/

/-- **★★★ `hIterBase_grounded`.**  THE `hIterBase` RUNG DISCHARGE (the BASE rung, HONEST x-slot
    REDUCTION).  ⚠ THE SLOT GATE: the census base is the **x-slot** heat operator
    `p ↦ heatOp g gi Wit p.1 p.2 0` (`= E p.1 p.2 0` at `E := heatOp g gi Wit`), whose Laplacian base
    point is `p.2` (VARYING).  The banked N2 `heatOp_slice_continuousOn_box_of_parts` is the z-slot
    orientation `heatOp g gi Wit p.1 0 p.2` (Laplacian base `0` FIXED) — a base-keying mismatch that does
    NOT transport (exactly like the J4-473 `hpd2diag` re-audit).  What transports is N2's ROUTE
    re-oriented: `heatOp` unfold (`deriv (∂_τ) − laplaceBeltrami (Δ_x)`) + `ContinuousOn.sub` reduces the
    x-slot base, at each `(τ₀,R)`, to the two `∀`-quantified x-slot part carries `hDerivX` (the `∂_τ`
    slice `p ↦ deriv (fun u => Wit u p.2 0) p.1`) and `hLapX` (the varying-base Laplacian slice
    `p ↦ laplaceBeltrami g gi (fun q => Wit p.1 q 0) p.2`).  Both parts are honest carries; neither is
    the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hIterBase_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hDerivX : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u p.2 0) p.1)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hLapX : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          laplaceBeltrami g gi
            (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro τ₀ hτ₀ R
  have hEq :
      (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 p.2 0)
      = fun p : ℝ × Point n =>
          deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u p.2 0) p.1
            - laplaceBeltrami g gi
                (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) p.2 := by
    funext p; simp only [heatOp]
  rw [hEq]
  exact (hDerivX τ₀ hτ₀ R).sub (hLapX τ₀ hτ₀ R)

/-! ###############################################################################
    ### ★★★ `hIterStep_grounded` — the census STEP rung, from per-rung Gaussian domination.
    ############################################################################### -/

/-- **★★★ `hIterStep_grounded`.**  THE `hIterStep` RUNG DISCHARGE (the CONVOLUTION rung, GENUINE WIRE).
    The census step is the per-level implication `ContinuousOn (iterE E (k+1)) box → ContinuousOn
    (iterE E (k+2)) box`.  Since `iterE E (k+2) = heatConv E (iterE E (k+1))`, the banked OUTER engine
    `IterEContinuity.iterE_succ_jointContinuousOn_of_dominated` PRODUCES the succ rung from the per-rung
    fixed-domain (`Ioc 0 1`) Gaussian domination data at `A = E`, `B = iterE E (k+1)` — the antecedent IH
    is not needed (the engine works directly from domination, a strictly stronger step).  ⚠ DOMINATION
    GATE: the banked census dominations are NOT in this per-rung `heatConv`-outer shape (they are the
    honest R-dom residual named by `IterEContinuity`), so the `hmeas/hbound/hbnd_int/hcont` are CARRIED
    per rung.  Generic in `E`; none of the carries is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hIterStep_grounded (E : ℝ → Point n → Point n → ℝ) (T : ℝ) (bnd : ℕ → ℝ → ℝ)
    (hmeas : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ∀ p ∈ Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R,
        AEStronglyMeasurable
          (fun u => ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E (k + 1) (p.1 * u) w 0)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hbound : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ∀ p ∈ Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R,
        ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
          ‖∫ w, E (p.1 - p.1 * u) p.2 w * iterE E (k + 1) (p.1 * u) w 0‖ ≤ bnd k u)
    (hbnd_int : ∀ k : ℕ, Integrable (bnd k) (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hcont : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        ContinuousOn
          (fun p : ℝ × Point n =>
            ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E (k + 1) (p.1 * u) w 0)
          (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)
      → ContinuousOn (fun p : ℝ × Point n => iterE E (k + 2) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro τ₀ hτ₀ R k _
  exact iterE_succ_jointContinuousOn_of_dominated E (k := k + 1) (by omega) (τ₀ / 2) T R (bnd k)
    (hmeas τ₀ hτ₀ R k) (hbound τ₀ hτ₀ R k) (hbnd_int k) (hcont τ₀ hτ₀ R k)

/-! ###############################################################################
    ### ★★★ `htermBox_chain_final` — the END-TO-END `htermBox` chain from the deepest carries.
    ############################################################################### -/

/-- **★★★ `htermBox_chain_final`.**  THE END-TO-END `htermBox` CHAIN.  From the deepest x-slot part
    carries (`hDerivX` + `hLapX`, for the base) and the per-rung Gaussian domination data (`hmeas/
    hbound/hbnd_int/hcont`, for the step), the ENTIRE census termwise box family
      `∀ τ₀∈Ioc 0 T, ∀ R, ∀ k, ContinuousOn (fun p ↦ iterE (heatOp g gi Wit) (k+1) p.1 p.2 0) box`
    is PRODUCED, by feeding `hIterBase_grounded` + `hIterStep_grounded` into the banked x-slot induction
    `BoxAtomsGrounding.htermBox_grounded` (`= IterEContinuity.iterE_jointContinuousOn` per box).  This
    is the census `htermBox` atom of `BoxCensusGrounding.v2Census_phase12`, now standing on x-slot
    `∂_τ`/Laplacian parts + per-rung dominations only.  ⚠ NOT `a₁ = R/6`. -/
theorem htermBox_chain_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hDerivX : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u p.2 0) p.1)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hLapX : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          laplaceBeltrami g gi
            (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (bnd : ℕ → ℝ → ℝ)
    (hmeas : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ∀ p ∈ Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R,
        AEStronglyMeasurable
          (fun u => ∫ w, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (p.1 - p.1 * u) p.2 w
            * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) (p.1 * u) w 0)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hbound : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ∀ p ∈ Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R,
        ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
          ‖∫ w, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (p.1 - p.1 * u) p.2 w
            * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) (p.1 * u) w 0‖
            ≤ bnd k u)
    (hbnd_int : ∀ k : ℕ, Integrable (bnd k) (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hcont : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        ContinuousOn
          (fun p : ℝ × Point n =>
            ∫ w, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (p.1 - p.1 * u) p.2 w
              * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) (p.1 * u) w 0)
          (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
  QIQTH.BoxAtomsGrounding.htermBox_grounded
    (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) T
    (hIterBase_grounded g gi hChr hK S a b T hDerivX hLapX)
    (hIterStep_grounded (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) T bnd
      hmeas hbound hbnd_int hcont)

/-! ###############################################################################
    ### THE RUNG LEDGER — the surviving surface after the two rung groundings.
    ############################################################################### -/

/-- **`rung_residuals`.**  THE ENUMERATED SURVIVING SURFACE after the J4-474 rung groundings.  A genuine
    conjunction (non-vacuous plumbing witness); each conjunct SATISFIABLE, none the conclusion.

    THE RUNG LEDGER (what remains carried in place of the two `htermBox` rung carries `hIterBase` /
    `hIterStep` of `BoxAtomsGrounding.box_atoms_residuals`):
      1. `hDerivX` — the x-slot `∂_τ` slice `p ↦ deriv (fun u => Wit u p.2 0) p.1` box family (one part
         of the re-oriented base rung; the `∂_τ` leg of the x-slot heat operator);
      2. `hLapX`   — the x-slot VARYING-BASE Laplacian slice `p ↦ laplaceBeltrami g gi (fun q => Wit p.1
         q 0) p.2` box family (the other base part; the metric/Christoffel factors are at the VARYING
         `p.2`, so N3's fixed-`0`-constant route does NOT collapse them — genuinely harder than N3);
      3. `hDom`    — the per-rung fixed-domain (`Ioc 0 1`) Gaussian domination bundle (`hmeas/hbound/
         hbnd_int/hcont` at `A = E`, `B = iterE E (k+1)`) feeding the OUTER-engine step at each rung;
      4. `hRestBox`— the UNCHANGED `BoxAtomsGrounding` residual (the `hPd2Full` diagonal-partial host +
         the phase-12 body carries `hRest`).

    DISCHARGED (NOT in this ledger): `hIterBase` — re-oriented onto `hDerivX`+`hLapX` via the N2 route in
    the x-slot; `hIterStep` — produced from `hDom` via `iterE_succ_jointContinuousOn_of_dominated`; and
    hence (via `htermBox_chain_final`) the WHOLE `htermBox` census family.  ⚠ SLOT/DOMINATION RE-AUDIT:
    the banked N2 (z-slot, fixed-`0` base) does NOT discharge the x-slot base, and the banked census
    dominations are not in the per-rung `heatConv`-outer shape — both stay honest carries.  ⚠ NOT
    `a₁ = R/6`; CONDITIONAL on exactly this surface. -/
def rung_residuals (hDerivX hLapX hDom hRestBox : Prop) : Prop :=
  hDerivX ∧ hLapX ∧ hDom ∧ hRestBox

/-- The rung ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem rung_residuals_intro {hDerivX hLapX hDom hRestBox : Prop}
    (h1 : hDerivX) (h2 : hLapX) (h3 : hDom) (h4 : hRestBox) :
    rung_residuals hDerivX hLapX hDom hRestBox :=
  ⟨h1, h2, h3, h4⟩

end QIQTH.IterRungGrounding

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.IterRungGrounding.hIterBase_grounded
#print axioms QIQTH.IterRungGrounding.hIterStep_grounded
#print axioms QIQTH.IterRungGrounding.htermBox_chain_final
#print axioms QIQTH.IterRungGrounding.rung_residuals_intro
