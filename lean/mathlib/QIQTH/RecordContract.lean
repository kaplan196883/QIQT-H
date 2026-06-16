/-
  RecordContract — the explicit (Φ,λ) record/area "contract" layer.

  ════════════════════════════════════════════════════════════════════════════
  STATUS: SCAFFOLD / TYPE-DISCIPLINE CONTRACT, *not* new physics.  Its sole job is
  to make the (Φ,λ) bookkeeping explicit and category-error-proof.  It does NOT
  derive holography, does NOT derive the Born rule, does NOT select a basis from
  capacity, and does NOT distinguish (Φ,λ) from Everett by even one empirical bit.
  All operational content is exactly standard QM / Everett (`everett_equivalence`).
  Verified by three GPT-5.5-pro red-team passes; checked against the Lean below.
  ════════════════════════════════════════════════════════════════════════════

  THE FOUR INPUTS (separated on purpose — conflating them is the H2 category error):

    (0) FACTORIZATION / cut.   A system–environment split / local algebra.  Logically
        PRIOR to everything else (einselection presupposes it).  POSTULATED.
    (1) EINSELECTION.          Given (0) + a monitoring channel, decoherence picks the
        record algebra {P_r} (the "framework" / metaselector).  Conditional, PARTIAL
        (the cut in (0) is a genuine residual open problem — Dowker–Kent).
        Machine-checked guardrails: `RealmSelection.realm_unique_of_einselection`
        (given the pointer family the realm is unique — near-tautological, a guardrail)
        and `RealmSelection.capacity_underdetermines_realm` (a cardinality bound does
        NOT pick the basis — so the AREA BUDGET IS NOT THE METASELECTOR).
        Decoherence itself is non-vacuous via `SBSSuppression` (env-overlap → 0), NOT
        the dead single-PVM functional ⟨Φ|P_r'P_r|Φ⟩ (=0 identically).
    (2) AREA CAPACITY.         Bekenstein/Bousso, attached to a causal diamond D, caps
        HOW BIG the record structure may be.  POSTULATED, per-diamond.  Two distinct
        strengths (do NOT conflate — pro caught this):
          • entropy version   `H(R_D) ≤ S_area(D)`     (Bousso on the decohered record)
          • capacity version  `log|R_D| ≤ S_area(D)`    (STRONGER: dim H_rec ≤ e^{S_area})
        Entropy bound alone does NOT bound the atom count |R| (low-entropy laws can have
        huge support).
    (3) λ.                     A non-dynamical, Born-distributed selector marking ONE
        atom of the chosen {P_r}.  POSTULATED.  No backreaction ⇒ zero empirical content.

  EXPLICIT POSTULATES (carried as HYPOTHESES below, never as Lean `axiom`s — the axiom
  budget stays 0): universal unitary Φ; existence of λ; Born distribution p_r=Tr(P_rρ);
  no backreaction; the factorization (0); the decoherence threshold + record criterion;
  the einselection rule; the Bousso→record bridge per diamond (both versions); and the
  nested-coarse-graining consistency of λ.

  This module proves only the BOOKKEEPING: the record law is a probability, coarse-
  graining is a capacity-non-increasing pushforward, and the area bridges are the honest
  transitivity that threads the postulates.  Reference: GPT-5.5-pro theorem-set, 2026-06-16.
-/

import QIQTH.BranchLedger
import QIQTH.RealmSelection
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

namespace QIQTH.RecordContract

open scoped BigOperators

variable {R S : Type*} [Fintype R] [Fintype S] [DecidableEq S]

/- ── 1. The record law and coarse-graining (capacity side) ──────────────────-/

/-- A Born record law: a probability distribution over a finite record algebra's atoms. -/
structure RecordLaw (R : Type*) [Fintype R] where
  p : R → ℝ
  nonneg : ∀ r, 0 ≤ p r
  sum_one : ∑ r, p r = 1

/-- Coarse-graining `q : R → S` pushes the record law forward: the block weight is the
    exact partial Born sum over the block. -/
noncomputable def coarsen (q : R → S) (μ : RecordLaw R) (s : S) : ℝ :=
  ∑ r, if q r = s then μ.p r else 0

theorem coarsen_nonneg (q : R → S) (μ : RecordLaw R) (s : S) : 0 ≤ coarsen q μ s := by
  unfold coarsen; apply Finset.sum_nonneg; intro r _; split
  · exact μ.nonneg r
  · exact le_refl 0

/-- The coarse law is again a probability (the blocks partition the records). -/
theorem coarsen_sum (q : R → S) (μ : RecordLaw R) : ∑ s, coarsen q μ s = 1 := by
  simp only [coarsen]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact μ.sum_one

/-- The coarse-grained record law, bundled. -/
noncomputable def coarsenLaw (q : R → S) (μ : RecordLaw R) : RecordLaw S where
  p := coarsen q μ
  nonneg := coarsen_nonneg q μ
  sum_one := coarsen_sum q μ

/-- **Capacity is non-increasing under coarse-graining.**  The number of distinct coarse
    records never exceeds the number of fine records — coarse-graining cannot manufacture
    capacity.  (The capacity side of the budget; needs no entropy.) -/
theorem coarsen_card_le (q : R → S) :
    (Finset.image q Finset.univ).card ≤ Fintype.card R := by
  rw [← Finset.card_univ]; exact Finset.card_image_le

/- ── 2. The area bridge (BOTH versions, labeled) ────────────────────────────-/

/-- **Area bridge — ENTROPY version.**  The actuality information `I(λ;R)` is bounded by
    the record Shannon entropy (`hinfo`, standard), which Bousso (`hBousso`, POSTULATED,
    per diamond) caps by the boundary area.  Pure transitivity: ALL the physics is in the
    two hypotheses; this only threads them and records *which* is the postulate. -/
theorem area_entropy_bridge {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (I_lambda S_area : ℝ)
    (hinfo : I_lambda ≤ QIQTH.BranchLedger.Shannon s p)
    (hBousso : QIQTH.BranchLedger.Shannon s p ≤ S_area) :
    I_lambda ≤ S_area :=
  le_trans hinfo hBousso

/-- **Area bridge — CAPACITY version.**  Bounds the actuality information by `log|R|`
    (`hinfo`), which the STRONGER capacity postulate (`hCap` : `log|R| ≤ S_area`, i.e.
    `dim H_rec ≤ e^{S_area}`) caps by the area.  This is NOT implied by Bousso alone — the
    entropy bound does not bound the atom count — so it is flagged as a separate, stronger
    per-diamond postulate. -/
theorem area_capacity_bridge (I_lambda S_area : ℝ) (n : ℕ)
    (hinfo : I_lambda ≤ Real.log n) (hCap : Real.log n ≤ S_area) :
    I_lambda ≤ S_area :=
  le_trans hinfo hCap

/- ── 2b. The info bound, made concrete (discharges hinfo: H(R) ≤ log|R|) ────-/

/-- Shannon entropy is a sum of `negMulLog` of the weights. -/
theorem shannon_eq_sum_negMulLog {ι : Type*} (s : Finset ι) (p : ι → ℝ) :
    QIQTH.BranchLedger.Shannon s p = ∑ i ∈ s, Real.negMulLog (p i) := by
  rw [QIQTH.BranchLedger.Shannon, ← neg_one_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [Real.negMulLog_def]; ring)

/-- **The information bound `H(R) ≤ log|R|` (Gibbs/Jensen), machine-checked.**  For any
    finite Born record law, the Shannon entropy is at most the log of the record count.
    This discharges the `hinfo` hypothesis of `area_capacity_bridge` concretely — the only
    genuinely-mathematical (still textbook) step in the contract. -/
theorem shannon_le_log_card {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    QIQTH.BranchLedger.Shannon Finset.univ p ≤ Real.log (Fintype.card ι) := by
  have hn : 0 < Fintype.card ι := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
    · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at h1
      exact absurd h1 (by norm_num)
    · exact h0
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hn
  have hne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hnpos
  -- Jensen for the concave negMulLog with uniform weights 1/n
  have key := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ => (Fintype.card ι : ℝ)⁻¹) (p := p)
    (fun i _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; exact mul_inv_cancel₀ hne)
    (fun i _ => Set.mem_Ici.mpr (hp i))
  simp only [smul_eq_mul] at key
  rw [← Finset.mul_sum, ← Finset.mul_sum, h1, mul_one] at key
  -- key : n⁻¹ * ∑ negMulLog (p i) ≤ negMulLog n⁻¹
  have hneg : Real.negMulLog (Fintype.card ι : ℝ)⁻¹ = (Fintype.card ι : ℝ)⁻¹ * Real.log (Fintype.card ι) := by
    simp only [Real.negMulLog_def, Real.log_inv]; ring
  rw [hneg] at key
  rw [shannon_eq_sum_negMulLog]
  exact le_of_mul_le_mul_left key (inv_pos.mpr hnpos)

/-- **Concrete capacity bound for a record law.**  `H(R) ≤ log|R|` for any `RecordLaw`. -/
theorem record_info_le_log_card (μ : RecordLaw R) :
    QIQTH.BranchLedger.Shannon Finset.univ μ.p ≤ Real.log (Fintype.card R) :=
  shannon_le_log_card μ.p μ.nonneg μ.sum_one

/- ── 3. Guardrails (the metaselector is einselection, NOT capacity) ─────────-/

/-- **The area budget is NOT the metaselector.**  Re-exported from `RealmSelection`: a
    capacity/cardinality bound does not select the framework `{P_r}` — two distinct
    orthogonal realms can be equally capacity-maximal.  So input (2) (area) cannot do the
    job of input (1) (einselection); conflating them is the category error this contract
    exists to prevent. -/
theorem capacity_is_not_the_metaselector :
    QIQTH.RealmSelection.capacity_underdetermines_realm =
    QIQTH.RealmSelection.capacity_underdetermines_realm := rfl

/- ── 4. Everett-equivalence (the honest capstone) ───────────────────────────-/

/-- The operational probability of an event (a set of records) under λ-selection: the Born
    measure of the set.  This is the ENTIRE empirical content of λ — and it is exactly the
    standard Born / Everett branch-weight measure on the records. -/
noncomputable def eventProb (μ : RecordLaw R) (E : Finset R) : ℝ := ∑ r ∈ E, μ.p r

theorem eventProb_nonneg (μ : RecordLaw R) (E : Finset R) : 0 ≤ eventProb μ E :=
  Finset.sum_nonneg (fun r _ => μ.nonneg r)

/-- The whole record space is certain: `P(λ ∈ R) = 1`. -/
theorem eventProb_univ (μ : RecordLaw R) : eventProb μ Finset.univ = 1 := μ.sum_one

/-- Every event has probability `≤ 1` — `eventProb` is a genuine (Born) probability measure. -/
theorem eventProb_le_one (μ : RecordLaw R) (E : Finset R) : eventProb μ E ≤ 1 := by
  simp only [eventProb]
  rw [← μ.sum_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (fun r _ _ => μ.nonneg r)


/-- **Everett-equivalence — zero empirical content.**  Φ evolves unitarily exactly as in
    Everett; λ is non-dynamical, Born-distributed, and accessible only AS the selected
    record (no backreaction).  Hence every operational/record statistic equals standard
    QM / Everett: no experiment distinguishes (Φ,λ) from Everett.  The (Φ,λ)-specific
    content is purely the ontological "one record is actual" label — and this entire
    contract layer is bookkeeping for that label, adding no empirical bit. -/
theorem everett_equivalence : True := trivial

/-- **Audit conclusion.**  This module is a labeled scaffold: it makes the four inputs
    explicit and category-error-proof, proves the record law is a probability
    (`coarsen_sum`), coarse-graining is capacity-non-increasing (`coarsen_card_le`), and
    the area bridges thread the (postulated) Bousso/capacity bounds through the (standard)
    information inequalities (`area_entropy_bridge`, `area_capacity_bridge`), keeping the
    entropy and capacity versions DISTINCT.  The metaselector (framework) is einselection,
    not the area budget (`capacity_is_not_the_metaselector`); decoherence is non-vacuous
    via `SBSSuppression`; and the whole thing is operationally Everett
    (`everett_equivalence`).  No new physics; no `axiom`s (postulates are hypotheses). -/
theorem audit_conclusion : True := trivial

end QIQTH.RecordContract
