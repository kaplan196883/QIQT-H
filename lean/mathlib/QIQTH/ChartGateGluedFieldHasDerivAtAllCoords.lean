/-
  ChartGateGluedFieldHasDerivAtAllCoords — J4-1138: dispatch 16 of the "inverse-branch
  overlap-uniqueness bridge" sub-campaign (greenlit J4-1122, …, single-coordinate glued field
  J4-1137, per `gpt-5.6-sol` high consult 2026-08-24 x16).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does (and does NOT do).

  J4-1137's `chartGate_glued_pfield_onGate_hasDerivAt_single_coord` takes a FREE coordinate
  parameter `k : Fin n` and, internally, calls `chartGate_concrete_S_construction` to obtain its
  gate `S`. Applying that theorem separately for two different `k`s invokes
  `chartGate_concrete_S_construction` TWICE, yielding two a-priori DIFFERENT (opaque
  `Classical.choice`-selected) gates `S`, `S'` — there is no Lean-provable reason they coincide.
  But `GatedRepSFix.tripleHEmeas_concrete_v4`'s target signature needs a SINGLE outer `S`
  (an explicit theorem parameter, shared simultaneously by `hcarField`, `hcarField2`, `hcarTau`),
  with `hcarField`'s job being only "for each `k`, produce a `Pfield` satisfying the on-gate
  conjuncts against THAT fixed `S`". J4-1137's dispatch-16 plan ("just `choose`/collect
  `Pglued_k` over `k`") is therefore broken as literally stated: collecting witnesses from `n`
  separate top-level calls to J4-1137 does NOT produce a shared `S`.

  Per the sixteenth `gpt-5.6-sol` (high) consult: this is a low-cost PACKAGING defect, not a new
  mathematical obstruction — `chartGate_concrete_S_construction` ALREADY builds one shared
  `S := ⋂ k, fiberGate (G k)` from ONE application (its own internal `choose` already ranges over
  `k : Fin n` to build the per-coordinate diagonal covers `t`/`G` BEFORE assembling `S`; see
  `ChartGateConcreteInstantiation.lean` step 1). The fix is to invoke
  `chartGate_concrete_S_construction` EXACTLY ONCE at the top of a NEW capstone, retain the single
  resulting `S` (and its supporting `Pfield`/`U`/`t`/`hall`/`hagreeFam` data) in scope, and THEN,
  under that one fixed `S`, prove `∀ k, ∃ Pglued, …` by repeating (inside a `∀ k` binder, not via
  `n` separate top-level applications) exactly the single-coordinate gluing argument J4-1137 already
  proved. This file does that: it is J4-1137's proof body, generalized to close under `∀ k` off ONE
  shared `obtain`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. No `sorry`, no new axioms, no vacuous/unsatisfiable
  hypotheses, no existing file edited (NEW FILE). This dispatch fixes the shared-`S`
  packaging defect and delivers the genuine `∀ k, ∃ Pglued, …` universal `GatedRepSFix.
  tripleHEmeas_concrete_v4`'s `hcarField`'s FIRST FOUR conjuncts need (measurability of the raw
  chart map is supplied separately by existing lemmas; the second/third/fourth conjuncts of
  `hcarField` — `chartFieldAmp` measurability, `pd (chartFieldAmp …)` measurability, and the
  `IsOpen (S w.2.2)`/`PdiffAt (chartFieldAmp …) k w.2.1` on-gate conjuncts — are NOT addressed
  here, since they concern the amplitude `chartFieldAmp`, textually unrelated to the
  `uniformInverseChart` chart-derivative machinery this sub-campaign builds). It does NOT: touch
  `hcarField2` (second-derivative analogue); discharge `PdiffAt (chartFieldAmp …)` (an unrelated
  amplitude/geometric obligation, never touched by this sub-campaign); discharge `hOffS`/`hOffS2`
  (the radialCutoff-support off-`S` vanishing — flagged by Sol as the single highest-risk
  remaining piece, needing an as-yet-unestablished containment of the cutoff's support inside
  every per-coordinate fiber gate); or produce any actual `tripleHEmeas_concrete_v4` /
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

/-- **★★★ `chartGate_glued_pfield_onGate_hasDerivAt_all_coords`** — dispatch 16 payoff, fixing
    the shared-`S` packaging defect flagged after J4-1137. Invokes
    `chartGate_concrete_S_construction` EXACTLY ONCE (producing a SINGLE shared gate `S` and
    supporting compatible-family data), then, under that one fixed `S`, produces for EVERY
    coordinate `k` a globally-`Measurable` glued field `Pglued k` witnessing the literal on-gate
    `HasDerivAt` conjunct of `GatedRepSFix.tripleHEmeas_concrete_v4`'s `hcarField k` at that `k` —
    all against the SAME `S`, unlike n separate applications of J4-1137's single-coordinate
    theorem. -/
theorem chartGate_glued_pfield_onGate_hasDerivAt_all_coords (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {K₀ : Set (Point n)} (hK₀ : IsCompact K₀) (hK₀sub : K₀ ⊆ interior K) :
    ∃ (S : Point n → Set (Point n)) (Pglued : Fin n → Point n → Point n → Fin n → ℝ),
      (∀ q, IsOpen (S q)) ∧
      MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} ∧
      (∀ q ∈ K₀, q ∈ S q) ∧
      (∀ k jj, Measurable (fun ξ : Point n × Point n => Pglued k ξ.1 ξ.2 jj)) ∧
      (∀ k : Fin n, ∀ q p : Point n, p ∈ S q → ∀ jj : Fin n,
        HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK q (Function.update p k s) jj)
          (Pglued k q p jj) (p k)) := by
  classical
  -- Invoke the concrete-gate construction EXACTLY ONCE: `S` (and the supporting family data)
  -- is fixed here, shared by every `k` below — NOT re-derived per coordinate.
  obtain ⟨r₀, hr₀pos, Pfield, U, t, G, S, hall, hagreeFam, htsub, htcov, hGdef, hSdef,
    hmemS, hSopen, hKSmeas, hdiag⟩ :=
    chartGate_concrete_S_construction hn g gi hC hK hK₀ hK₀sub
  have h0lt : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀pos
  -- For EACH coordinate `k`, glue the finite family `{Pfield z₀ 0 k}_{z₀ ∈ t k}` off the SAME
  -- `t`, `U`, `hall`, `hagreeFam` fixed above — repeating J4-1137's single-coordinate argument
  -- inside a `∀ k` binder rather than via separate top-level theorem applications.
  have hper : ∀ k : Fin n, ∃ Pglued : Point n → Point n → Fin n → ℝ,
      (∀ jj, Measurable (fun ξ : Point n × Point n => Pglued ξ.1 ξ.2 jj)) ∧
      (∀ q p : Point n, p ∈ S q → ∀ jj : Fin n,
        HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK q (Function.update p k s) jj)
          (Pglued q p jj) (p k)) := by
    intro k
    have hadm : ∀ z₀ ∈ t k, z₀ ∈ interior K := by
      intro z₀ hz₀
      exact hK₀sub (htsub k (Finset.mem_coe.mpr hz₀))
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
    refine ⟨Pglued, hPgluedMeas, ?_⟩
    intro q p hpS jj
    obtain ⟨z₀, hz₀t, hqpU⟩ := (hmemS q p).mp hpS k
    have hHD := (hall z₀ 0 k (hadm z₀ hz₀t) h0lt).2.2.2.2 (q, p) hqpU jj
    have hEq : Pglued q p jj = Pfield z₀ 0 k q p jj := by
      have hmem' : ((q, p) : Point n × Point n) ∈ U' (⟨z₀, hz₀t⟩ : ↥(t k)) := hqpU
      have := hPgluedEq (⟨z₀, hz₀t⟩ : ↥(t k)) (Finset.mem_univ _) jj hmem'
      simpa [P', hP'def] using this
    rw [hEq]
    simpa using hHD
  choose Pglued hPgluedMeas hPgluedHD using hper
  exact ⟨S, Pglued, hSopen, hKSmeas, hdiag, hPgluedMeas, hPgluedHD⟩

end QIQTH.ExpMap

/-! ## Axiom checks — the public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ExpMap
#print axioms chartGate_glued_pfield_onGate_hasDerivAt_all_coords
end AxiomChecks
