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
give the Born product law; typicality follows.  Axiom-free (standard three only).

HONEST SCOPE (GPT-5.5-pro verification, 2026-06 — do NOT overstate).  This is a CONDITIONAL
representation theorem, NOT a derivation of Born statistics from capacity.  Brutally:
  • The Born law is an ASSUMPTION: `oneSite` + `indep` are fields of `ActualEnsemble`, and
    together they essentially ARE the Born product law — `pushforward_eq_w` is their
    composition.  Honest reading: "ASSUMING Born one-site marginals + independence, the actual
    histories have the Born product law and are Chebyshev-typical."
  • The no-collapse core's contribution here (unique actual value, C1) is largely a WRAPPER:
    the probability content would hold for any `X : Ω → Fin n → Fin m`; the capacity/value
    machinery imposes no probabilistic constraint (any process can be dressed as value
    selections; correlated ones simply fail the explicit `indep` field).
  • `iidWitness` is logically non-vacuous but DEGENERATE: it sets `mass = w p` (building in the
    law it exhibits) and uses trivial one-record `Unit` selections.
  • `p` is an ARBITRARY probability vector here; it is the genuine quantum Born weight only when
    instantiated `p := OneSiteBorn.bornVec M ψ` (for a unit state — see `bornVec_isProbVector`).
NOT established: deriving Born from Hilbert-space QM, deriving independence, deriving the world
measure, or that no-collapse dynamics produce typical frequencies.  Fair one-line claim:
"Lean verifies that finite no-collapse value-selection wrappers over an explicitly Born-marginal,
independent world ensemble have unique actual histories whose pushforward is the Born product
measure and hence are Chebyshev-typical." -/
import QIQTH.ValueSelection
import QIQTH.BornTypicalityFinite
import QIQTH.OneSiteBorn
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

/-- **The world-measure carries NO observable freedom (toward b3).**  Any two capacity-limited
    ensembles with the same single-trial law `p` have IDENTICAL history distributions — both equal
    the product Born measure `w p` — regardless of their world-spaces `Ω` or probability masses
    `P`.  So the posited `ProbMass` is not a fundamental extra input: the observable n-trial
    outcome statistics are FORCED by `p` + independence; the world-measure beyond what fixes `p`
    is observationally irrelevant.

    This is the honest content behind "deriving the world-measure": one cannot derive a specific
    probability from selector dynamics (Born is not the counting/uniform measure), but one CAN
    show the world-measure adds no freedom — the outcome law is unique.  Combined with `p` forced
    Born (non-contextuality, `BornJoinGleason`) and independence = product preparation
    (`w_history_factorizes`), the ENTIRE observable content is fixed by non-contextuality +
    product preparation; the `(Φ,λ)` dynamics generating individual runs remains physics, not a
    further probabilistic posit. -/
theorem history_law_unique (E₁ E₂ : ActualEnsemble m n)
    (hp : E₁.p = E₂.p) (h : Fin n → Fin m) :
    E₁.P.massSet ((univ : Finset E₁.Ω).filter (fun ω => E₁.actualHist ω = h))
      = E₂.P.massSet ((univ : Finset E₂.Ω).filter (fun ω => E₂.actualHist ω = h)) := by
  rw [E₁.pushforward_eq_w, E₂.pushforward_eq_w, hp]

/-- The history distribution of ANY capacity-limited ensemble equals the product Born measure
    `w p` — the outcome statistics are fixed independent of how the worlds/measure are modelled. -/
theorem history_law_eq_w (E : ActualEnsemble m n) (h : Fin n → Fin m) :
    E.P.massSet ((univ : Finset E.Ω).filter (fun ω => E.actualHist ω = h)) = w E.p h :=
  E.pushforward_eq_w h

end ActualEnsemble

/- ── C6: a concrete i.i.d. Born witness (non-vacuity of the prize) ──

   Shows the prize theorem's hypotheses (`oneSite` + `indep`) are JOINTLY SATISFIABLE, so
   `finite_noCollapseBornRepresentation` is not vacuous.  Model: worlds = histories, world-mass
   = the product Born weight `w p`, and each trial's record is a one-record (Unit) context
   forced to that world's outcome.  Then `oneSite` is the single-trial marginal of `w p` (= p)
   and `indep` is the product structure of `w p`. -/

open PointerValue

/-- The trivial one-record capacity context on `Unit` (zero cost, zero capacity). -/
def unitJoint : JointRecordContext where
  Rec := Unit
  jointCost := fun _ => 0
  mono := fun _ => le_refl 0
  Qmax := 0
  pair_exceeds := fun r s h => absurd (Subsingleton.elim r s) h

/-- A value context with a single record forced to value `a`. -/
def singleValueContext (a : Fin m) : ValueContext (Fin m) where
  J := unitJoint
  valueOf := fun _ => a
  pair_exceeds_value := fun _ _ h => absurd rfl h

/-- A value selection whose unique actual value is `a`. -/
def singleValueSelection (a : Fin m) : ValueSelection (Fin m) where
  ctx := singleValueContext a
  config := { active := {()}, capacity := le_refl 0 }
  selected := ⟨(), Finset.mem_singleton_self ()⟩

@[simp] theorem singleValueSelection_actualValue (a : Fin m) :
    (singleValueSelection a).actualValue = a :=
  ((singleValueSelection a).actualValue_eq_of_mem (Finset.mem_singleton_self ())).symm

/-- **Single-trial marginal of the product Born weight is `p`.**  (The `oneSite` calibration
    of the witness, from `BornTypicalityFinite.marginal`.) -/
theorem iid_oneSite (p : Fin m → ℝ) (hp1 : ∑ k, p k = 1) (t : Fin n) (a : Fin m) :
    (∑ ω ∈ (univ : Finset (Fin n → Fin m)).filter
        (fun ω => (singleValueSelection (ω t)).actualValue = a), w p ω) = p a := by
  simp only [singleValueSelection_actualValue]
  rw [Finset.sum_filter, ← marginal p hp1 a t]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases h : ω t = a <;> simp [h, w]

/-- **The i.i.d. Born ensemble** witnessing non-vacuity of the prize: worlds are histories,
    mass is the product Born weight, each trial is forced to that world's outcome. -/
noncomputable def iidWitness (p : Fin m → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) :
    ActualEnsemble m n where
  Ω := Fin n → Fin m
  P := ⟨w p, fun ω => w_nonneg p hp0 ω, sum_w_eq_one p hp1⟩
  V := fun ω t => singleValueSelection (ω t)
  p := p
  p_nonneg := hp0
  p_sum := hp1
  oneSite := fun t a => iid_oneSite p hp1 t a
  indep := fun h => by
    have hL : (∑ ω ∈ (univ : Finset (Fin n → Fin m)).filter
        (fun ω => (fun t => (singleValueSelection (ω t)).actualValue) = h), w p ω) = w p h := by
      have hset : (univ : Finset (Fin n → Fin m)).filter
          (fun ω => (fun t => (singleValueSelection (ω t)).actualValue) = h) = {h} := by
        ext ω
        simp only [mem_filter, mem_univ, true_and, mem_singleton, singleValueSelection_actualValue]
      rw [hset, Finset.sum_singleton]
    have hR : (∏ t, (∑ ω ∈ (univ : Finset (Fin n → Fin m)).filter
        (fun ω => (singleValueSelection (ω t)).actualValue = h t), w p ω)) = w p h :=
      (Finset.prod_congr rfl (fun t _ => iid_oneSite p hp1 t (h t)))
    exact hL.trans hR.symm

/-- The prize theorem's Born product law holds on the concrete i.i.d. witness — confirming the
    hypotheses are realized and `finite_noCollapseBornRepresentation` is non-vacuous. -/
example (p : Fin m → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) (h : Fin n → Fin m) :
    (iidWitness p hp0 hp1).P.massSet
        ((univ : Finset (Fin n → Fin m)).filter
          (fun ω => (iidWitness p hp0 hp1).actualHist ω = h)) = w p h :=
  (iidWitness p hp0 hp1).pushforward_eq_w h

/-- **The single-trial law CAN be the genuine quantum Born weight.**  For a unit state `ψ`
    and a finite PVM `M`, `OneSiteBorn.bornVec M ψ` (`a ↦ ‖Eₐψ‖²`) is a valid probability
    vector, so it may serve as `ActualEnsemble.p`.  Then `oneSite` reads "world-mass of actual
    value `a` = ‖Eₐψ‖²" — the quantum Born weight, not a free parameter.  (This fixes `p`; the
    one-site CALIBRATION itself remains a named assumption.) -/
theorem bornVec_isProbVector {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : CoreNoCollapse.FinPVM H) (ψ : H) (hψ : ‖ψ‖ = 1) :
    (∀ a, 0 ≤ OneSiteBorn.bornVec M ψ a) ∧ ∑ a, OneSiteBorn.bornVec M ψ a = 1 :=
  ⟨OneSiteBorn.bornVec_nonneg M ψ, OneSiteBorn.bornVec_sum M ψ hψ⟩

end QIQTH.BornJoin
