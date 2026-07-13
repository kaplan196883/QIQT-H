/-
  BULK AUTONOMY — the AUTONOMOUS bulk-only equation of motion (duality campaign, brick D4c).
  Closes the gap D4b explicitly left open.

  D4b (`QIQTH/BulkGeneration.lean`) proved the GENERATION half: a boundary Markov generator `Q`
  moves the ledger `p`, and the induced bulk metric velocity is
  `reconstruct'(areaOfLedger(Q·p(s)))` — the LINEAR decoder pushforward of the ledger velocity.
  But that velocity depends on the boundary ledger `p(s)`, NOT on the metric `h(s) = D(p(s))`
  alone (`D := reconstruct' ∘ areaOfLedger`, the composite linear decoder).  D4b's firewall noted
  exactly this: an autonomous bulk-only law would additionally require `ker D` to be
  `Q`-invariant.  D4c closes precisely that gap.

  ⚠ MANDATORY FIREWALL (verifier-binding, honest).
  • D4c closes D4b's gap: the bulk metric evolution is AUTONOMOUS (velocity a function of the
    metric `h(s)` alone) EXACTLY WHEN `ker D` is `Q`-invariant / the intertwiner
    `D ∘ Q = Qbar ∘ D` holds — carried as a HYPOTHESIS (structure/argument, NEVER an axiom).
    The `no_descend_of_bad_kernel` no-go shows the condition is NECESSARY, not decorative: if
    `ker D` is not `Q`-invariant, NO descended velocity field on the metric exists.
  • This is the KINEMATIC autonomy of the induced metric flow (the velocity descends through the
    linear decoder); it is NOT the Einstein equation, NOT an AdS/curved dynamical law, NOT
    backreaction — those are the heat-kernel-gated warp/curvature content (D5/D6), separate and
    deferred.  Finite-dimensional, linearized decoder.  NOT the conjecture, NOT the strong
    holographic principle, NOT quantum gravity.
  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.BulkGeneration

namespace QIQTH.BulkAutonomy

/-! ## Part A — the abstract autonomous-descent package (self-contained, load-bearing) -/

section Abstract

variable {P H : Type*}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- `ker D` is `Q`-invariant. -/
def KerInvariant (D : P →L[ℝ] H) (Q : P →L[ℝ] P) : Prop :=
  ∀ k : P, D k = 0 → D (Q k) = 0

/-- `ker D` is `Q`-invariant iff `Q` respects the fibres of `D` (the geometric meaning: `Q`
    descends to a well-defined map on `im D`). -/
theorem kerInvariant_iff_fiber_congr (D : P →L[ℝ] H) (Q : P →L[ℝ] P) :
    KerInvariant D Q ↔ ∀ x y : P, D x = D y → D (Q x) = D (Q y) := by
  constructor
  · intro h x y hxy
    have hk : D (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hq : D (Q (x - y)) = 0 := h (x - y) hk
    have hsub : D (Q x) - D (Q y) = 0 := by simpa [map_sub] using hq
    exact sub_eq_zero.mp hsub
  · intro h k hk
    simpa using h k 0 (by simpa using hk)

/-- **★★ minimal autonomous descent.**  `V` need only agree with `D ∘ Q` on the image of `D`;
    given the boundary rate equation `p' = Q·p`, the metric trajectory `D ∘ p` obeys the
    AUTONOMOUS law `h'(s) = V(h(s))` — velocity a function of the metric alone. -/
theorem autonomous_descend_at (D : P →L[ℝ] H) (Q : P →L[ℝ] P) (V : H → H)
    (hdesc : ∀ x : P, D (Q x) = V (D x)) {p : ℝ → P} {s : ℝ}
    (hp : HasDerivAt p (Q (p s)) s) :
    HasDerivAt (fun t : ℝ => D (p t)) (V (D (p s))) s := by
  have hlin : HasDerivAt (fun t : ℝ => D (p t)) (D (Q (p s))) s := by
    have hD : HasFDerivAt (fun x : P => D x) D (p s) := D.hasFDerivAt
    simpa only [Function.comp_apply] using hD.comp_hasDerivAt s hp
  simpa [hdesc (p s)] using hlin

/-- **★★ the clean intertwiner version.**  If `D ∘ Q = Qbar ∘ D` (the decoder intertwines the
    boundary generator `Q` with a BULK generator `Qbar`), then the metric trajectory is
    autonomous with velocity `Qbar(h(s))`. -/
theorem autonomous_descend_at_clm (D : P →L[ℝ] H) (Q : P →L[ℝ] P) (Qbar : H →L[ℝ] H)
    (hcomm : D.comp Q = Qbar.comp D) {p : ℝ → P} {s : ℝ}
    (hp : HasDerivAt p (Q (p s)) s) :
    HasDerivAt (fun t : ℝ => D (p t)) (Qbar (D (p s))) s := by
  refine autonomous_descend_at D Q (fun y => Qbar y) ?_ hp
  intro x
  simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L : P →L[ℝ] H => L x) hcomm

/-- **The autonomous bulk law, globally.**  If `p' = Q·p` holds for all times and the intertwiner
    `D ∘ Q = Qbar ∘ D` holds, the metric trajectory `h(t) = D(p t)` obeys `h'(s) = Qbar(h(s))`
    for all `s`. -/
theorem autonomous_descend_global_clm (D : P →L[ℝ] H) (Q : P →L[ℝ] P) (Qbar : H →L[ℝ] H)
    (hcomm : D.comp Q = Qbar.comp D) {p : ℝ → P} (hp : ∀ s : ℝ, HasDerivAt p (Q (p s)) s) :
    ∀ s : ℝ, HasDerivAt (fun t : ℝ => D (p t)) (Qbar ((fun t : ℝ => D (p t)) s)) s :=
  fun s => by simpa using autonomous_descend_at_clm D Q Qbar hcomm (hp s)

/-- **★ THE NO-GO.**  If `ker D` is NOT `Q`-invariant, NO descended velocity field exists: two
    ledgers with the same metric would give different metric velocities.  Autonomy genuinely
    REQUIRES the kernel-invariance condition — it is necessary, not decorative. -/
theorem no_descend_of_bad_kernel (D : P →L[ℝ] H) (Q : P →L[ℝ] P)
    (hbad : ∃ k : P, D k = 0 ∧ D (Q k) ≠ 0) :
    ¬ ∃ V : H → H, ∀ x : P, D (Q x) = V (D x) := by
  rintro ⟨V, hdesc⟩
  rcases hbad with ⟨k, hk, hkQ⟩
  have h1 : D (Q k) = V 0 := by simpa [hk] using hdesc k
  have h0 : V 0 = 0 := by simpa using (hdesc 0).symm
  exact hkQ (by simp [h1, h0])

end Abstract

/-! ## Part B — grounding in the D4b bulk setting (the metric vocabulary)

  We state the autonomous law in the actual bulk-metric types `Ledger ι` and `Metric` from
  `QIQTH.BulkGeneration`.  The `Metric` codomain `Matrix (Fin 4) (Fin 4) ℝ` is made a genuine
  normed space by the same Frobenius convention `BulkGeneration` fixes (`open scoped
  Matrix.Norms.Frobenius`), so the continuous-linear-map statement is well-formed and matches
  D4b's ambient norm EXACTLY.

  We take the composite decoder `D` and the promoted Markov generator `Q` as given CLMs (a
  bundling `BulkGeneration` performs internally in `bulk_chain`), and the bulk generator `Qbar` as
  the intertwiner witness.  This is a thin specialization of `autonomous_descend_at_clm`; the
  POINT is to phrase the closed gap in the bulk-metric vocabulary. -/

section Grounded

open QIQTH.BulkGeneration
open scoped Matrix.Norms.Frobenius

/-- **★★ THE AUTONOMOUS BULK METRIC LAW (D4c, in the D4b vocabulary).**  Let
    `D : Ledger ι →L[ℝ] Metric` be the composite linear area decoder
    (`reconstruct' ∘ areaOfLedger`, bundled as a CLM), `Q : Ledger ι →L[ℝ] Ledger ι` the boundary
    Markov generator promoted to a CLM, and suppose the decoder INTERTWINES `Q` with a bulk
    generator `Qbar : Metric →L[ℝ] Metric` (`D ∘ Q = Qbar ∘ D`, equivalently — by
    `kerInvariant_iff_fiber_congr` — `ker D` is `Q`-invariant).  Then along any boundary rate
    solution `p' = Q·p`, the induced bulk metric trajectory `h(t) = D(p t)` obeys the AUTONOMOUS
    bulk-only law `h'(s) = Qbar(h(s))`: the velocity is a function of the metric `h(s)` alone,
    closing the gap D4b left open. -/
theorem bulk_metric_autonomous {ι : Type*} [Fintype ι]
    (D : Ledger ι →L[ℝ] Metric) (Q : Ledger ι →L[ℝ] Ledger ι) (Qbar : Metric →L[ℝ] Metric)
    (hcomm : D.comp Q = Qbar.comp D) {p : ℝ → Ledger ι} {s : ℝ}
    (hp : HasDerivAt p (Q (p s)) s) :
    HasDerivAt (fun t : ℝ => D (p t)) (Qbar (D (p s))) s :=
  autonomous_descend_at_clm D Q Qbar hcomm hp

/-- **The bulk metric law, globally**, in the bulk vocabulary: along a global boundary rate
    solution the metric obeys `h'(s) = Qbar(h(s))` for every `s`. -/
theorem bulk_metric_autonomous_global {ι : Type*} [Fintype ι]
    (D : Ledger ι →L[ℝ] Metric) (Q : Ledger ι →L[ℝ] Ledger ι) (Qbar : Metric →L[ℝ] Metric)
    (hcomm : D.comp Q = Qbar.comp D) {p : ℝ → Ledger ι} (hp : ∀ s : ℝ, HasDerivAt p (Q (p s)) s) :
    ∀ s : ℝ, HasDerivAt (fun t : ℝ => D (p t)) (Qbar ((fun t : ℝ => D (p t)) s)) s :=
  autonomous_descend_global_clm D Q Qbar hcomm hp

end Grounded

end QIQTH.BulkAutonomy
