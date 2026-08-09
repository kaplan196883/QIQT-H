/-
  BoxAtomsGrounding — J4-473: GROUND THE TWO NAMED BOX ATOMS `hpd2diag` + `htermBox`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  continues the box-census surface reduction begun by `BoxCensusGrounding` (J4-469), which reduced
  the two positive-time-compact box FAMILIES (`hSecBoxes`, `hBBoxes`) to two named ATOMS —
  `hpd2diag` (the gated-witness second-spatial-partial box carry, keyed at the FIXED RNC center `0`)
  and `htermBox` (the per-`k` termwise box continuity of the Levi iterate `iterE E (k+1)`).  This
  brick grounds those two atoms ONE LEVEL DOWN, onto their honest lower-level suppliers, at the
  transport granularity of the individual carries (NEVER re-applying the ~85-binder phase-12 Π).

  ── `htermBox` (the LEVI ITERATE ATOM).  GENUINE WIRE.  THE INDUCTION MATCH.  The census atom
       `∀ τ₀∈Ioc 0 T, ∀ R, ∀ k, ContinuousOn (fun p ↦ iterE E (k+1) p.1 p.2 0)
          (Icc (τ₀/2) T ×ˢ closedBall 0 R)`
     is the **x-slot** orientation (varying spatial variable `p.2` in the FIRST slot, `y` frozen at
     `0`).  ⚠ SLOT RE-AUDIT (dont-undercredit).  J4-394's `LeviIterBoxInduction.iterE_z_continuousOn_
     box_family` supplies the OTHER (z-slot, middle-frozen) orientation `iterE E (k+1) p.1 0 p.2` and
     does NOT transport here.  The CORRECT supplier is the banked x-slot induction
     `IterEContinuity.iterE_jointContinuousOn` (exactly as `LeviMTest`'s M0 slot-orientation note
     records: the consumer's Levi factor `leviSeries E s z 0` freezes the LAST slot, so the termwise
     carry needed is the x-slot family).  So `htermBox` REDUCES, at each `(τ₀,R)`, to the strictly
     lower-level BASE (`iterE E 1 = E` x-slot joint continuity) + STEP carries via that banked
     induction.  Genuine reduction of the whole `∀ k` family onto base+step.

  ── `hpd2diag` (the WITNESS SECOND-PARTIAL ATOM).  HONEST NAMED RESIDUE.  THE TRANSPARENCY RE-AUDIT.
     The atom is the DIAGONAL `(i,i)` second spatial partial of the GATED witness
     `vanVleckGatedWitness = gatedKernel K S (globalCutoffParametrixWitnessN 1 …)`, keyed at the FIXED
     base `0`.  The J4-469 mismatch claim vs the ungated `ChartComposedHeatOp.chartComposed_pd_pd_
     jointContinuousOn` is CONFIRMED, and the "positive-time transparency" hypothesis is REFUTED on
     two independent counts:
       (T1) THE GATE IS `τ`-INDEPENDENT.  `gatedKernel K S H τ p q = if q∈K then (if p∈S q then H τ p q
            else 0) else 0` carries NO `τ`-dependence (a HARD spatial gate, by design — the point of
            `gatedKernel_apply_of_mem`).  So there is NO `τ`-gate to be "transparent" for `τ ≥ τ₀/2 > 0`;
            the J4-443 τ-transparency pattern is a category error here.  Any transparency would be
            SPATIAL — it would require `z = p.2 ∈ K` AND `0 ∈ interior (S z)` to hold IDENTICALLY over
            the box `closedBall 0 R`, which does NOT hold (the ball is not `⊆ K`, nor is `0` interior to
            `S z` for all `z`).
       (T2) BASE-KEYING MISMATCH.  `chartComposed_pd_pd_jointContinuousOn` keys its second partial at
            the VARYING base `p.2`; the census atom keys at the FIXED base `0`.  Different base slot.
     ⟹ the ungated chart-composed supplier does NOT transport.  `hpd2diag` stays an HONEST carry.  What
     IS available is a consolidation onto the CANONICAL atom `NonLeviBoxContinuity.hpd2` (the mixed
     second-spatial-partial box carry over ALL `(i,j)`): the census only needs the DIAGONAL `j = i`, so
     `hpd2diag` follows from that fuller canonical atom by specialization + quantifier reorder.  NO
     discharge — the atom is merely NAMED at its canonical home.

  ── WHAT LANDS.
    • `htermBox_grounded`  — ★★★ the census `htermBox` atom, PRODUCED from the x-slot base+step carries
        via the banked `IterEContinuity.iterE_jointContinuousOn` (per box).
    • `hpd2diag_grounded`  — ★★★ the census `hpd2diag` atom, CONSOLIDATED (specialization + reorder)
        onto the canonical mixed second-partial atom `NonLeviBoxContinuity.hpd2` shape.  Honest residue.
    • `box_atoms_residuals` (+ intro) — the enumerated surviving surface after the two atom groundings.

  NO `sorry`, NO `:= True`, NO new axioms; std-3 only.  No existing file edited.
  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.BoxCensusGrounding
import QIQTH.IterEContinuity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.IterEContinuity QIQTH.HeatResidualBound
open scoped Topology Interval BigOperators

namespace QIQTH.BoxAtomsGrounding

variable {n : ℕ}

/-! ###############################################################################
    ### ★★★ `htermBox_grounded` — the census `htermBox` atom, from x-slot base+step (banked induction).
    ############################################################################### -/

/-- **★★★ `htermBox_grounded`.**  THE `htermBox` DISCHARGE (the LEVI ITERATE side, GENUINE WIRE).  The
    census per-`k` termwise box continuity family — `∀ τ₀∈Ioc 0 T, ∀ R, ∀ k, ContinuousOn (fun p ↦
    iterE E (k+1) p.1 p.2 0) (Icc (τ₀/2) T ×ˢ closedBall 0 R)` — is the **x-slot** orientation
    (varying `p.2` in the FIRST spatial slot, `y` frozen at `0`).  It is PRODUCED, at each `(τ₀, R)`,
    by the banked x-slot induction `IterEContinuity.iterE_jointContinuousOn` (t₁ := τ₀/2, t₂ := T),
    fed the `∀`-quantified base carry `hbase` (`iterE E 1 = E` x-slot joint continuity) and per-level
    step carry `hstep`.  ⚠ SLOT RE-AUDIT: J4-394's `iterE_z_continuousOn_box_family` is the WRONG
    (z-slot, middle-frozen) orientation and does NOT transport — the x-slot induction is the correct
    supplier (per `LeviMTest`'s M0 note).  Generic in `E`; at the census `E := heatOp g gi
    (vanVleckGatedWitness …)`.  ⚠ NOT `a₁ = R/6`. -/
theorem htermBox_grounded (E : ℝ → Point n → Point n → ℝ) (T : ℝ)
    (hbase : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn (fun p : ℝ × Point n => E p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hstep : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)
      → ContinuousOn (fun p : ℝ × Point n => iterE E (k + 2) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro τ₀ hτ₀ R k
  exact iterE_jointContinuousOn E (τ₀ / 2) T R (hbase τ₀ hτ₀ R) (hstep τ₀ hτ₀ R) k

/-! ###############################################################################
    ### ★★★ `hpd2diag_grounded` — the census `hpd2diag` atom, consolidated onto the canonical `hpd2`.
    ############################################################################### -/

/-- **★★★ `hpd2diag_grounded`.**  THE `hpd2diag` CONSOLIDATION (the WITNESS side, HONEST NAMED RESIDUE).
    THE TRANSPARENCY RE-AUDIT: no discharge exists.  The gate `gatedKernel K S H` is `τ`-INDEPENDENT
    (a hard SPATIAL gate), so the positive-time (`τ ≥ τ₀/2 > 0`) transparency pattern does NOT apply;
    and `ChartComposedHeatOp.chartComposed_pd_pd_jointContinuousOn` keys the second partial at the
    VARYING base `p.2`, whereas the census atom keys at the FIXED base `0` — a base-slot mismatch.  So
    the ungated chart-composed supplier does NOT transport.  What IS available: the census atom needs
    only the DIAGONAL `(i,i)` second partial, so it follows from the CANONICAL mixed second-spatial-
    partial box atom `hpd2full` (the `NonLeviBoxContinuity.hpd2` shape, over ALL `(i,j)`) by
    specialization `j := i` and quantifier reorder.  This merely NAMES the atom at its canonical home;
    it closes NOTHING deeper.  ⚠ NOT `a₁ = R/6`. -/
theorem hpd2diag_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hpd2full : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ i j : Fin n,
      ContinuousOn
        (fun p : ℝ × Point n =>
          pd (fun y : Point n =>
              pd (fun x : Point n =>
                vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) j y) i (0 : Point n))
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          pd (fun x : Point n =>
              pd (fun x' : Point n =>
                vanVleckGatedWitness g gi hChr hK S a b p.1 x' p.2) i x) i (0 : Point n))
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro i τ₀ hτ₀ R
  exact hpd2full τ₀ hτ₀ R i i

/-! ###############################################################################
    ### THE BOX ATOMS LEDGER — the surviving surface after the two atom groundings.
    ############################################################################### -/

/-- **`box_atoms_residuals`.**  THE ENUMERATED SURVIVING SURFACE after the J4-473 atom groundings.
    A genuine conjunction (non-vacuous plumbing witness), machine-checkable; each conjunct
    SATISFIABLE, none the conclusion.

    THE BOX ATOMS LEDGER (what remains carried in place of the two named box atoms `hpd2diag` /
    `htermBox` of `BoxCensusGrounding.v2Census_phase12`):
      1. `hIterBase` — the x-slot BASE carry `p ↦ E p.1 p.2 0` (the `iterE E 1 = E` residual, one heat
         operator past the banked witness-kernel continuity) that, WITH `hIterStep`, now REPLACES the
         whole termwise box atom `htermBox` (via the banked x-slot induction);
      2. `hIterStep` — the per-level x-slot convolution STEP carry that, WITH `hIterBase`, completes
         the `htermBox` reduction;
      3. `hPd2Full`  — the CANONICAL mixed second-spatial-partial box atom (`NonLeviBoxContinuity.hpd2`
         shape, over ALL `(i,j)`) that now HOSTS the diagonal `hpd2diag` (specialization + reorder);
      4. `hRest`     — the UNCHANGED phase-12 body carries.

    DISCHARGED (NOT in this ledger): `htermBox` — VERBATIM-reduced to `hIterBase`+`hIterStep` via
    `IterEContinuity.iterE_jointContinuousOn` (x-slot orientation).  CONSOLIDATED (NOT discharged):
    `hpd2diag` — hosted on `hPd2Full`.  ⚠ THE TRANSPARENCY RE-AUDIT: no banked supplier discharges the
    witness second-partial atom (the `τ`-independent spatial gate + base-`0` keying both block the
    ungated `chartComposed_pd_pd_jointContinuousOn` wire); it stays an honest carry.  ⚠ NOT `a₁ = R/6`;
    CONDITIONAL on exactly this surface. -/
def box_atoms_residuals (hIterBase hIterStep hPd2Full hRest : Prop) : Prop :=
  hIterBase ∧ hIterStep ∧ hPd2Full ∧ hRest

/-- The box atoms ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem box_atoms_residuals_intro {hIterBase hIterStep hPd2Full hRest : Prop}
    (h1 : hIterBase) (h2 : hIterStep) (h3 : hPd2Full) (h4 : hRest) :
    box_atoms_residuals hIterBase hIterStep hPd2Full hRest :=
  ⟨h1, h2, h3, h4⟩

end QIQTH.BoxAtomsGrounding

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.BoxAtomsGrounding.htermBox_grounded
#print axioms QIQTH.BoxAtomsGrounding.hpd2diag_grounded
#print axioms QIQTH.BoxAtomsGrounding.box_atoms_residuals_intro
