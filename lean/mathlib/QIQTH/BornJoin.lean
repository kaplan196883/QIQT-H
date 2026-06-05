/-
# The join: capacity-selected actual histories obey the Born law (prize C3+C4)

This is the JOIN GPT-5.5-pro identified as THE prize — connecting the no-collapse core (A:
exactly one actual pointer value per trial, `ValueSelection.existsUnique_actualValue`) with
the Born layer (B: finite typicality, `BornTypicalityFinite`).

Model (`ActualEnsemble`): a finite ensemble of worlds with a probability mass `P`; in each
world, each of `n` trials runs a capacity-limited `ValueSelection` whose unique actual
pointer value (C1) is the experienced outcome.  Two NAMED physical inputs (not smuggled):
  • `oneSite` — single-trial calibration: the world-mass of "trial `t`'s actual value is `a`"
    is the Born weight `p a` (supplied by the one-site bridge `OneSiteBorn`, `p = bornVec`);
  • `indep` — trials are independent: the mass of a full actual history factorizes.

From these we DERIVE:
  • `pushforward_eq_w` — the world-mass realizing history `h` is the product Born weight
    `∏ₜ p(hₜ) = w p h` (the Born PRODUCT law — not assumed, derived from oneSite+indep);
  • `actualHistory_typical` — the total world-mass of histories with `ε`-atypical frequency
    of outcome `k` is `≤ p k(1−p k)/(n·ε²) → 0` (finite Chebyshev LLN, `BornTypicalityFinite`).

No collapse map appears.  Capacity gives the unique actual value; calibration+independence
give the Born product law; typicality follows.  Axiom-free (standard three only). -/
import QIQTH.ValueSelection
import QIQTH.BornTypicalityFinite
import Mathlib.Tactic

namespace QIQTH.BornJoin

open CoreNoCollapse PointerValue BornTypicalityFinite Finset

/-- A finite probability mass on a finite type of worlds. -/
structure ProbMass (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  sum_one : ∑ ω, mass ω = 1

/-- Mass of a finite set of worlds. -/
noncomputable def ProbMass.massSet {Ω : Type*} [Fintype Ω] (P : ProbMass Ω)
    (A : Finset Ω) : ℝ := ∑ ω ∈ A, P.mass ω

variable {m n : ℕ}

/-- **The join model.**  A finite ensemble of worlds; in each world every trial runs a
    capacity-limited value selection; the single-trial Born law `p` calibrates the one-site
    mass (`oneSite`); trials are independent (`indep`). -/
structure ActualEnsemble (m n : ℕ) where
  Ω : Type
  [finΩ : Fintype Ω]
  [decΩ : DecidableEq Ω]
  P : ProbMass Ω
  /-- per world, per trial: a capacity-limited run with a unique actual pointer value -/
  V : Ω → Fin n → ValueSelection (Fin m)
  /-- the single-trial Born law (e.g. `OneSiteBorn.bornVec ψ`) -/
  p : Fin m → ℝ
  p_nonneg : ∀ k, 0 ≤ p k
  p_sum : ∑ k, p k = 1
  /-- single-trial calibration: world-mass of "trial t's actual value is a" = Born weight -/
  oneSite : ∀ (t : Fin n) (a : Fin m),
    P.massSet (univ.filter (fun ω => (V ω t).actualValue = a)) = p a
  /-- independence of trials: the mass of a full actual history factorizes -/
  indep : ∀ h : Fin n → Fin m,
    P.massSet (univ.filter (fun ω => (fun t => (V ω t).actualValue) = h))
      = ∏ t, P.massSet (univ.filter (fun ω => (V ω t).actualValue = h t))

attribute [instance] ActualEnsemble.finΩ ActualEnsemble.decΩ

namespace ActualEnsemble

variable (E : ActualEnsemble m n)

/-- The actual pointer-value history realized in world `ω` (unique per trial by C1). -/
noncomputable def actualHist (ω : E.Ω) : Fin n → Fin m := fun t => (E.V ω t).actualValue

/-- **Pushforward = Born product law.**  The world-mass of the worlds realizing history `h`
    equals the product Born weight `∏ₜ p(hₜ) = w p h`.  DERIVED from single-trial calibration
    + independence — the product law is a consequence, not an assumption. -/
theorem pushforward_eq_w (h : Fin n → Fin m) :
    E.P.massSet (univ.filter (fun ω => E.actualHist ω = h)) = w E.p h := by
  show E.P.massSet (univ.filter (fun ω => (fun t => (E.V ω t).actualValue) = h)) = w E.p h
  rw [E.indep h]
  exact Finset.prod_congr rfl (fun t _ => E.oneSite t (h t))

/-- **Born typicality of capacity-selected actual histories (the prize statement).**  The
    total world-mass of histories whose empirical frequency of outcome `k` deviates from the
    Born weight `p k` by `ε` is `≤ p k(1−p k)/(n·ε²) → 0`.  Derived: pushforward = Born product
    law, then the finite Chebyshev weak law.  No collapse postulate is used. -/
theorem actualHistory_typical (k : Fin m) {ε : ℝ} (hε : 0 < ε) (hn : 0 < n) :
    (∑ h ∈ (univ : Finset (Fin n → Fin m)).filter
        (fun h => ((n : ℝ) * ε) ^ 2 ≤ (count k h - (n : ℝ) * E.p k) ^ 2),
        E.P.massSet (univ.filter (fun ω => E.actualHist ω = h)))
      ≤ E.p k * (1 - E.p k) / ((n : ℝ) * ε ^ 2) := by
  rw [Finset.sum_congr rfl (fun h _ => E.pushforward_eq_w h)]
  exact chebyshev_freq E.p E.p_nonneg E.p_sum k hε hn

/-- **Born typicality, world-mass form.**  The mass of WORLDS whose actual history has
    `ε`-atypical frequency of outcome `k` is `≤ p k(1−p k)/(n·ε²)`.  (Same bound as
    `actualHistory_typical`, repackaged as a single probability via the fiberwise partition
    of the bad worlds by their history.) -/
theorem actualHistory_typical_world (k : Fin m) {ε : ℝ} (hε : 0 < ε) (hn : 0 < n) :
    E.P.massSet (univ.filter
        (fun ω => ((n : ℝ) * ε) ^ 2 ≤ (count k (E.actualHist ω) - (n : ℝ) * E.p k) ^ 2))
      ≤ E.p k * (1 - E.p k) / ((n : ℝ) * ε ^ 2) := by
  classical
  set bad : (Fin n → Fin m) → Prop :=
    fun h => ((n : ℝ) * ε) ^ 2 ≤ (count k h - (n : ℝ) * E.p k) ^ 2 with hbad
  have hmaps : ∀ ω ∈ univ.filter (fun ω => bad (E.actualHist ω)),
      E.actualHist ω ∈ (univ : Finset (Fin n → Fin m)).filter bad := by
    intro ω hω
    rw [mem_filter] at hω ⊢
    exact ⟨mem_univ _, hω.2⟩
  have hpart :
      E.P.massSet (univ.filter (fun ω => bad (E.actualHist ω)))
        = ∑ h ∈ (univ : Finset (Fin n → Fin m)).filter bad,
            E.P.massSet (univ.filter (fun ω => E.actualHist ω = h)) := by
    rw [ProbMass.massSet, ← Finset.sum_fiberwise_of_maps_to hmaps E.P.mass]
    refine Finset.sum_congr rfl (fun h hh => ?_)
    rw [ProbMass.massSet]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext ω
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun hω => hω.2
    · intro heq
      rw [mem_filter] at hh
      exact ⟨by rw [heq]; exact hh.2, heq⟩
  rw [hpart]
  exact E.actualHistory_typical k hε hn

/-- **Finite no-collapse Born representation theorem (the prize).**  In any capacity-limited
    measurement ensemble: (i) every world has a UNIQUE actual pointer-value history (capacity
    + selector, no collapse); (ii) the world-mass realizing each history is exactly the Born
    PRODUCT weight `∏ₜ p(hₜ)` (DERIVED from single-trial calibration + independence, not
    assumed); (iii) histories with `ε`-atypical frequency carry `≤ p k(1−p k)/(n·ε²) → 0`
    total world-mass.  No collapse postulate appears. -/
theorem finite_noCollapseBornRepresentation (k : Fin m) {ε : ℝ} (hε : 0 < ε) (hn : 0 < n) :
    (∀ ω : E.Ω, ∃! h : Fin n → Fin m,
        ∀ t, ∃ r ∈ (E.V ω t).config.active, (E.V ω t).ctx.valueOf r = h t)
    ∧ (∀ h : Fin n → Fin m,
        E.P.massSet (univ.filter (fun ω => E.actualHist ω = h)) = w E.p h)
    ∧ E.P.massSet (univ.filter
        (fun ω => ((n : ℝ) * ε) ^ 2 ≤ (count k (E.actualHist ω) - (n : ℝ) * E.p k) ^ 2))
        ≤ E.p k * (1 - E.p k) / ((n : ℝ) * ε ^ 2) :=
  ⟨fun ω => existsUnique_actualHistory (E.V ω), E.pushforward_eq_w,
    E.actualHistory_typical_world k hε hn⟩

end ActualEnsemble
end QIQTH.BornJoin
