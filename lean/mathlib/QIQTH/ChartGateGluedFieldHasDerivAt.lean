/-
  ChartGateGluedFieldHasDerivAt — J4-1137: dispatch 15 of the "inverse-branch overlap-uniqueness
  bridge" sub-campaign (greenlit J4-1122, …, abstract fiber-gate lemmas J4-1135, concrete gate
  `S := ⋂ k, fiberGate (G k)` J4-1136, redirected target `GatedRepSFix.tripleHEmeas_concrete_v4`
  per the decisive audit J4-1134, per `gpt-5.6-sol` high consult 2026-08-24 x15).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does (and does NOT do).

  J4-1136's own "next dispatch" note (echoed in this dispatch's task): fix a coordinate `k`, glue
  the finite family `{Pfield z₀ 0 k}_{z₀ ∈ t k}` (from J4-1132's compatible family, restricted to
  J4-1136's diagonal-cover finite index `t k`) via `exists_measurable_glue_finset_field` (J4-1131)
  into a SINGLE globally-`Measurable` `Pglued_k`, then combine with J4-1136's membership-unfolding
  bridge (`mem_S_iff`) to derive the literal on-gate `HasDerivAt` conjunct that
  `GatedRepSFix.tripleHEmeas_concrete_v4`'s `hcarField` consumes — for ONE fixed coordinate `k`,
  and for the SHARED gate `S` produced by `chartGate_concrete_S_construction`.

  ## The construction (fifteenth Sol consult, BEFORE any Lean).

  Sol flagged one genuine Lean-level design choice: `exists_measurable_glue_finset_field` requires
  its measurability / pairwise-agreement hypotheses for EVERY index of `ι`, but J4-1132's family
  spec only supplies them for ADMISSIBLE seeds (`z₀ ∈ interior K`, `‖v₀‖ < r₀`); a generic
  `z₀ : Point n` is not admissible. Two options: (A) junk-fill (`if z₀ ∈ t k then … else ∅`), or
  (B) index by the SUBTYPE `↥(t k)`, whose every element is admissible (`t k ⊆ K₀ ⊆ interior K`,
  `v₀ = 0`, `‖0‖ = 0 < r₀`), eliminating all junk / empty-intersection casework. Sol confirmed (B)
  is cleaner and pitfall-free (`FinsetCoe.fintype` gives `Finset.univ : Finset ↥(t k)`; the final
  glue lookup is `hPgluedEq i (Finset.mem_univ i)`). Adopted here.

  Derivation at a covered point: from `p ∈ S q`, `mem_S_iff` gives (at the fixed `k`) a seed
  `z₀ ∈ t k` with `(q,p) ∈ U z₀ 0 k`; the family spec's derivative clause at `ξ := (q,p)` gives
  `HasDerivAt … (Pfield z₀ 0 k q p jj) (p k)`; the glue `Set.EqOn` on `U z₀ 0 k` rewrites the
  coefficient to `Pglued_k q p jj`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. No `sorry`, no new axioms, no vacuous/unsatisfiable
  hypotheses, no existing file edited (NEW FILE). This dispatch builds ONLY the single-coordinate
  glued `Pglued_k` + its measurability + the on-gate `HasDerivAt` conjunct at coordinate `k`, for
  the shared `S`. It does NOT yet: package the `∀ k` universal (each `k` gets its own `Pglued_k`,
  but they are not yet collected into `hcarField`'s `∀ k, ∃ Pfield, …` shape); build the
  `hcarField2` / second-derivative (`Pifield`/`Pjfield`/`Qfield`) analogue; discharge
  `PdiffAt (chartFieldAmp …)` (an unrelated amplitude/geometric obligation, never touched by this
  sub-campaign); discharge `hOffS`/`hOffS2` (the radialCutoff-support off-`S` vanishing — Sol
  flagged HARDER post-intersection-shrinkage); or produce any actual `tripleHEmeas_concrete_v4` /
  `a1_R6_assembled_v7` invocation. Non-vacuity of the `HasDerivAt` clause is conditional on
  `K₀.Nonempty` (diagonal inclusion then fires at `(q,q)` for `q ∈ K₀`); the theorem does not
  assume `K₀.Nonempty`, so the clause is stated as a genuine (non-vacuous-when-inhabited)
  conditional. `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ChartGateConcreteInstantiation
import QIQTH.MeasurableGlueFinset

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **★★★ `chartGate_glued_pfield_onGate_hasDerivAt_single_coord`** — dispatch 15 payoff. For a
    FIXED coordinate `k`, glues the diagonal-cover finite family `{Pfield z₀ 0 k}_{z₀ ∈ t k}` (from
    J4-1132's compatible family, at J4-1136's finite index `t k`) into a single globally-`Measurable`
    `Pglued`, and derives the literal on-gate `HasDerivAt` conjunct of
    `GatedRepSFix.tripleHEmeas_concrete_v4`'s `hcarField` (at coordinate `k`), for the SHARED gate
    `S := ⋂ k, fiberGate (G k)` from `chartGate_concrete_S_construction` (J4-1136). Carries `S`'s
    openness, the `hKSmeas`-shaped joint measurability, and diagonal inclusion on `K₀`. Does NOT
    package the `∀ k` universal nor the `hcarField2` second-order analogue (later dispatches). -/
theorem chartGate_glued_pfield_onGate_hasDerivAt_single_coord (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {K₀ : Set (Point n)} (hK₀ : IsCompact K₀) (hK₀sub : K₀ ⊆ interior K) (k : Fin n) :
    ∃ (S : Point n → Set (Point n)) (Pglued : Point n → Point n → Fin n → ℝ),
      (∀ q, IsOpen (S q)) ∧
      MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} ∧
      (∀ q ∈ K₀, q ∈ S q) ∧
      (∀ jj, Measurable (fun ξ : Point n × Point n => Pglued ξ.1 ξ.2 jj)) ∧
      (∀ q p : Point n, p ∈ S q → ∀ jj : Fin n,
        HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK q (Function.update p k s) jj)
          (Pglued q p jj) (p k)) := by
  classical
  obtain ⟨r₀, hr₀pos, Pfield, U, t, G, S, hall, hagreeFam, htsub, htcov, hGdef, hSdef,
    hmemS, hSopen, hKSmeas, hdiag⟩ :=
    chartGate_concrete_S_construction hn g gi hC hK hK₀ hK₀sub
  have h0lt : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀pos
  -- admissibility of a seed in `t k`
  have hadm : ∀ z₀ ∈ t k, z₀ ∈ interior K := by
    intro z₀ hz₀
    exact hK₀sub (htsub k (Finset.mem_coe.mpr hz₀))
  -- (B) index the glue by the subtype `↥(t k)` — every element admissible, no junk-fill.
  set U' : ↥(t k) → Set (Point n × Point n) := fun i => U i.1 0 k with hU'def
  set P' : ↥(t k) → Point n → Point n → Fin n → ℝ := fun i => Pfield i.1 0 k with hP'def
  have hU'meas : ∀ i : ↥(t k), MeasurableSet (U' i) := by
    intro i
    exact (hall i.1 0 k (hadm i.1 i.2) h0lt).2.1
  have hP'meas : ∀ (i : ↥(t k)) (jj : Fin n),
      Measurable (fun ξ : Point n × Point n => P' i ξ.1 ξ.2 jj) := by
    intro i jj
    exact (hall i.1 0 k (hadm i.1 i.2) h0lt).2.2.2.1 jj
  have hP'agree : ∀ (i j : ↥(t k)) (jj : Fin n),
      Set.EqOn (fun ξ : Point n × Point n => P' i ξ.1 ξ.2 jj)
        (fun ξ : Point n × Point n => P' j ξ.1 ξ.2 jj) (U' i ∩ U' j) := by
    intro i j jj ξ hξ
    exact hagreeFam i.1 0 k j.1 0 (hadm i.1 i.2) h0lt (hadm j.1 j.2) h0lt ξ hξ jj
  obtain ⟨Pglued, hPgluedMeas, hPgluedEq⟩ :=
    exists_measurable_glue_finset_field (Finset.univ : Finset ↥(t k)) U' P'
      hU'meas hP'meas hP'agree
  refine ⟨S, Pglued, hSopen, hKSmeas, hdiag, hPgluedMeas, ?_⟩
  intro q p hpS jj
  -- membership bridge → covering seed at the fixed `k`
  obtain ⟨z₀, hz₀t, hqpU⟩ := (hmemS q p).mp hpS k
  -- the compatible family's derivative clause at `ξ := (q, p)`
  have hHD := (hall z₀ 0 k (hadm z₀ hz₀t) h0lt).2.2.2.2 (q, p) hqpU jj
  -- the glued field agrees with `Pfield z₀ 0 k` on `U z₀ 0 k` at `(q, p)`
  have hEq : Pglued q p jj = Pfield z₀ 0 k q p jj := by
    have hmem' : ((q, p) : Point n × Point n) ∈ U' (⟨z₀, hz₀t⟩ : ↥(t k)) := hqpU
    have := hPgluedEq (⟨z₀, hz₀t⟩ : ↥(t k)) (Finset.mem_univ _) jj hmem'
    simpa [P', hP'def] using this
  rw [hEq]
  simpa using hHD

end QIQTH.ExpMap

/-! ## Axiom checks — the public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ExpMap
#print axioms chartGate_glued_pfield_onGate_hasDerivAt_single_coord
end AxiomChecks
