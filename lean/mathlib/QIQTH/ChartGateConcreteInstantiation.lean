/-
  ChartGateConcreteInstantiation — J4-1136: dispatch 13 of the "inverse-branch overlap-uniqueness
  bridge" sub-campaign (greenlit J4-1122, ..., abstract fiber-gate lemmas J4-1135, redirected
  target `GatedRepSFix.tripleHEmeas_concrete_v4` per the decisive audit J4-1134, per `gpt-5.6-sol`
  high consult 2026-08-24 x14).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does (and does NOT do).

  J4-1135's "next dispatch" note specified instantiating `fiberGate` (J4-1135) at the ACTUAL
  diagonal-cover chart data (`ChartCoherentPFieldCompatibleFamily.lean`, J4-1132; `ChartCoherent-
  PFieldDiagonalFiniteCover.lean`, J4-1133) to build the concrete gate `S` for `GatedRepSFix.
  tripleHEmeas_concrete_v4`. A fourteenth Sol consult (2026-08-24, BEFORE any Lean) reviewed the
  precise plan and flagged one genuine Lean-level subtlety NOT visible from the ledger prose alone:
  `chartCoherent_pfield_diagonal_finite_cover` (J4-1133) internally re-invokes `exists_chart-
  Coherent_pfield_compatible_family` (J4-1132) FRESH for every call, so calling it separately for
  two different coordinates `k₁ ≠ k₂` gives NO Lean-provable guarantee that the extracted `(r₀,
  Pfield, U)` triples coincide (opaque `Classical.choice` witnesses from two independent existential
  eliminations are not automatically equal) — yet `tripleHEmeas_concrete_v4`'s `S` must be built
  from a SINGLE shared family across every `k : Fin n` simultaneously (`hcarField`'s `∀k` all use
  the SAME outer `S`). Sol's fix, adopted here: extract the compatible family (J4-1132) EXACTLY
  ONCE, then re-derive the Heine–Borel diagonal-cover ARGUMENT (J4-1133's technique) as a fresh,
  GENERIC lemma parameterized directly over an already-fixed family spec `hall`, rather than
  re-invoking the family existential per coordinate. This makes `(r₀, Pfield, U)` genuinely shared
  when the per-coordinate covers `t k` are then collected via `choose` over the finite index `Fin
  n`.

  ## The construction.

  (1) `finite_diag_cover_of_open_family` — a purely TOPOLOGICAL Heine–Borel lemma, decoupled from
      any chart-specific family spec (Sol's recommended abstraction): given a compact `K₀`, a
      family `V : Point n → Set (Point n × Point n)` open at every `z ∈ K₀`, and diagonal
      membership `(z,z) ∈ V z` for every `z ∈ K₀`, extracts a finite `t ⊆ K₀` whose `V`-images
      cover the compact diagonal `Δ K₀`. (Mirrors J4-1133's proof body verbatim, generalized off
      any chart content.)
  (2) `finite_diag_cover_of_family` — the chart-specific wrapper: given an ALREADY-FIXED compatible
      family (`r₀`, `Pfield`, `U`, `hall` — NOT re-derived), instantiates (1) at `V z := U z 0 k`
      for a given coordinate `k`, using `hall`'s openness/diagonal-membership clauses plus
      `uniformFlowExp_zero`.
  (3) `chartGate_concrete_S_construction` — the payoff: fixes the compatible family ONCE, collects
      `t : Fin n → Finset (Point n)` via `choose` applied to (2) at every `k` (genuinely shared
      `r₀`/`Pfield`/`U`), defines `G k := ⋃ z₀ ∈ t k, U z₀ 0 k` and `S q := ⋂ k, fiberGate (G k)
      q` (the FINITE INTERSECTION `tripleHEmeas_concrete_v4`'s `S` needs, per J4-1135's decisive
      correction — NOT a per-`k` union), and proves: `S q` is open for every `q` (via `fiberGate_
      iInter_isOpen`, J4-1135); the literal `hKSmeas`-shaped set `{w | w.2.2∈K ∧ w.2.1∈S w.2.2}` is
      `MeasurableSet` (via `fiberGate_gate_measurableSet`, J4-1135, applied per coordinate and
      combined with `MeasurableSet.iInter` over the nonempty finite index `Fin n`, `hn : 0 < n`);
      and diagonal inclusion `∀ q ∈ K₀, q ∈ S q` (every coordinate's cover places `(q,q)` in `G k`).
      Also banks the elementary membership-unfolding bridge `mem_S_iff` Sol flagged as needed by
      the NEXT dispatch's derivative-transfer step, so dispatch 14 does not have to re-derive it.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. No `sorry`, no new axioms, no vacuous/unsatisfiable
  hypotheses, no existing file edited (NEW FILE). This dispatch builds ONLY the concrete `S`
  construction plus its openness, `hKSmeas`-shaped measurability, and diagonal inclusion — it does
  NOT yet: glue the finite `Pfield` families via `exists_measurable_glue_finset_field` (J4-1131)
  into a single `Pglued_k`; transfer the on-gate `HasDerivAt` conjunct of `hcarField`/`hcarField2`
  through that gluing; discharge `PdiffAt (chartFieldAmp …)` (an unrelated amplitude/geometric
  obligation, never touched by this sub-campaign); discharge `hOffS`/`hOffS2` (the radialCutoff-
  support off-`S` vanishing — Sol flagged this HARDER once `S` is intersection-shrunk, an
  obligation this file does not address); or produce any actual `tripleHEmeas_concrete_v4`/
  `a1_R6_assembled_v7` invocation. Also note: `q ∈ S q` for `q ∈ K₀` is DIAGONAL INCLUSION, not
  nonemptiness of `S q` beyond that one point unless `K₀` is separately known nonempty (per Sol's
  terminology caution). `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.
-/
import QIQTH.ChartGateFiberProductMeasurable
import QIQTH.ChartCoherentPFieldDiagonalFiniteCover

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **`finite_diag_cover_of_open_family`** — purely topological Heine–Borel diagonal-cover lemma,
    decoupled from any chart-specific compatible-family spec (Sol's recommended abstraction,
    fourteenth consult). Mirrors `chartCoherent_pfield_diagonal_finite_cover`'s (J4-1133) proof body
    verbatim, generalized off any chart content: given `K₀` compact and a family `V` open and
    diagonal-membership-carrying at every `z ∈ K₀`, extracts a finite `t ⊆ K₀` whose `V`-images
    already cover the compact diagonal `Δ K₀ := {(q,q) : q ∈ K₀}`. -/
theorem finite_diag_cover_of_open_family {K₀ : Set (Point n)} (hK₀ : IsCompact K₀)
    (V : Point n → Set (Point n × Point n))
    (hVopen : ∀ z ∈ K₀, IsOpen (V z))
    (hdiag : ∀ z ∈ K₀, ((z, z) : Point n × Point n) ∈ V z) :
    ∃ t : Finset (Point n), ↑t ⊆ K₀ ∧
      (fun q => ((q, q) : Point n × Point n)) '' K₀ ⊆ ⋃ z ∈ t, V z := by
  set s : Set (Point n × Point n) := (fun q => ((q, q) : Point n × Point n)) '' K₀ with hsdef
  have hscompact : IsCompact s := hK₀.image (by fun_prop)
  have hc₂ : s ⊆ ⋃ i ∈ K₀, V i := by
    rintro x ⟨q, hq, rfl⟩
    exact Set.mem_biUnion hq (hdiag q hq)
  obtain ⟨b', hb'sub, hb'fin, hb'cov⟩ :=
    IsCompact.elim_finite_subcover_image hscompact hVopen hc₂
  refine ⟨hb'fin.toFinset, ?_, ?_⟩
  · rw [hb'fin.coe_toFinset]; exact hb'sub
  · rw [show (⋃ z₀ ∈ hb'fin.toFinset, V z₀) = ⋃ z₀ ∈ b', V z₀ by simp [hb'fin.coe_toFinset]]
    exact hb'cov

/-- **`finite_diag_cover_of_family`** — chart-specific instantiation of (1) at an ALREADY-FIXED
    compatible family `(r₀, Pfield, U, hall)` (NOT re-derived per coordinate — the fix for the
    "separately-extracted witnesses may not coincide" issue Sol flagged). For a fixed `hall`
    (any compatible-family spec of `exists_chartCoherent_pfield_compatible_family`'s shape) and
    coordinate `k`, extracts the finite diagonal cover of `K₀` by `{U z₀ 0 k}`. -/
theorem finite_diag_cover_of_family
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (Pfield : Point n → Point n → Fin n → Point n → Point n → Fin n → ℝ)
    (U : Point n → Point n → Fin n → Set (Point n × Point n))
    (hall : ∀ z₀ v₀ (k : Fin n), z₀ ∈ interior K → ‖v₀‖ < r₀ →
      IsOpen (U z₀ v₀ k) ∧
      MeasurableSet (U z₀ v₀ k) ∧
      ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈ U z₀ v₀ k ∧
      (∀ jj : Fin n, Measurable (fun ξ : Point n × Point n => Pfield z₀ v₀ k ξ.1 ξ.2 jj)) ∧
      (∀ ξ ∈ U z₀ v₀ k, ∀ jj : Fin n,
        HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k s) jj)
          (Pfield z₀ v₀ k ξ.1 ξ.2 jj) (ξ.2 k)))
    {K₀ : Set (Point n)} (hK₀ : IsCompact K₀) (hK₀sub : K₀ ⊆ interior K) (k : Fin n) :
    ∃ t : Finset (Point n), ↑t ⊆ K₀ ∧
      (fun q => ((q, q) : Point n × Point n)) '' K₀ ⊆ ⋃ z₀ ∈ t, U z₀ 0 k := by
  apply finite_diag_cover_of_open_family hK₀ (fun z => U z 0 k)
  · intro z hz
    have hzint := hK₀sub hz
    have h0lt : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀
    exact (hall z 0 k hzint h0lt).1
  · intro z hz
    have hzint := hK₀sub hz
    have h0lt : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀
    have hmem := (hall z 0 k hzint h0lt).2.2.1
    have hzK : z ∈ K := interior_subset hzint
    have hz0 : uniformFlowExp g gi hC hK z 0 = z := uniformFlowExp_zero g gi hC hK z hzK
    rwa [hz0] at hmem

/-- **★★★ `chartGate_concrete_S_construction`** — dispatch 13 payoff: the CONCRETE `S := ⋂ k,
    fiberGate (G k)` gate (`G k` built from J4-1132's compatible family + J4-1133-style diagonal
    covers, SHARED across every coordinate `k` per the fourteenth-consult fix), together with its
    openness, `hKSmeas`-shaped joint measurability, and diagonal inclusion on `K₀`. Also exposes
    the elementary membership-unfolding bridge `p ∈ S q ↔ ∀ k, ∃ z₀ ∈ t k, (q,p) ∈ U z₀ 0 k`
    Sol flagged as needed by the next dispatch's `HasDerivAt`-transfer step. Does NOT yet build any
    derivative-clause witness (`Pfield`/`hcarField`'s on-gate branch) — that is dispatch 14. -/
theorem chartGate_concrete_S_construction (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {K₀ : Set (Point n)} (hK₀ : IsCompact K₀) (hK₀sub : K₀ ⊆ interior K) :
    ∃ (r₀ : ℝ) (_ : 0 < r₀)
      (Pfield : Point n → Point n → Fin n → Point n → Point n → Fin n → ℝ)
      (U : Point n → Point n → Fin n → Set (Point n × Point n))
      (t : Fin n → Finset (Point n))
      (G : Fin n → Set (Point n × Point n))
      (S : Point n → Set (Point n)),
      (∀ z₀ v₀ (k : Fin n), z₀ ∈ interior K → ‖v₀‖ < r₀ →
        IsOpen (U z₀ v₀ k) ∧
        MeasurableSet (U z₀ v₀ k) ∧
        ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈ U z₀ v₀ k ∧
        (∀ jj : Fin n, Measurable (fun ξ : Point n × Point n => Pfield z₀ v₀ k ξ.1 ξ.2 jj)) ∧
        (∀ ξ ∈ U z₀ v₀ k, ∀ jj : Fin n,
          HasDerivAt
            (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k s) jj)
            (Pfield z₀ v₀ k ξ.1 ξ.2 jj) (ξ.2 k))) ∧
      (∀ z₀ v₀ (k : Fin n) z₀' v₀',
        z₀ ∈ interior K → ‖v₀‖ < r₀ → z₀' ∈ interior K → ‖v₀'‖ < r₀ →
        ∀ ξ ∈ U z₀ v₀ k ∩ U z₀' v₀' k, ∀ jj : Fin n,
          Pfield z₀ v₀ k ξ.1 ξ.2 jj = Pfield z₀' v₀' k ξ.1 ξ.2 jj) ∧
      (∀ k, ↑(t k) ⊆ K₀) ∧
      (∀ k, (fun q => ((q, q) : Point n × Point n)) '' K₀ ⊆ ⋃ z₀ ∈ t k, U z₀ 0 k) ∧
      (∀ k, G k = ⋃ z₀ ∈ t k, U z₀ 0 k) ∧
      (∀ q, S q = ⋂ k, fiberGate (G k) q) ∧
      (∀ q p : Point n, p ∈ S q ↔ ∀ k, ∃ z₀ ∈ t k, ((q, p) : Point n × Point n) ∈ U z₀ 0 k) ∧
      (∀ q, IsOpen (S q)) ∧
      MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} ∧
      (∀ q ∈ K₀, q ∈ S q) := by
  classical
  -- (Step 0) Fix the compatible family EXACTLY ONCE.
  obtain ⟨r₀, hr₀pos, Pfield, U, hall, hagree⟩ :=
    exists_chartCoherent_pfield_compatible_family g gi hC hK
  -- (Step 1) Collect the per-coordinate diagonal covers off the SAME shared family.
  have hcover_exists : ∀ k : Fin n, ∃ t : Finset (Point n), ↑t ⊆ K₀ ∧
      (fun q => ((q, q) : Point n × Point n)) '' K₀ ⊆ ⋃ z₀ ∈ t, U z₀ 0 k := fun k =>
    finite_diag_cover_of_family g gi hC hK hr₀pos Pfield U hall hK₀ hK₀sub k
  choose t htsub htcov using hcover_exists
  -- (Step 2) Define the per-coordinate gate `G k` and the SHARED gate `S := ⋂ k, fiberGate (G k)`.
  set G : Fin n → Set (Point n × Point n) := fun k => ⋃ z₀ ∈ t k, U z₀ 0 k with hGdef
  set S : Point n → Set (Point n) := fun q => ⋂ k, fiberGate (G k) q with hSdef
  refine ⟨r₀, hr₀pos, Pfield, U, t, G, S, hall, hagree, htsub, htcov, fun k => rfl, fun q => rfl,
    ?_, ?_, ?_, ?_⟩
  · -- membership-unfolding bridge
    intro q p
    simp only [hSdef, Set.mem_iInter, mem_fiberGate, hGdef, Set.mem_iUnion₂, exists_prop]
  · -- openness of every `S q`
    intro q
    have hGopen : ∀ k, IsOpen (G k) := by
      intro k
      rw [hGdef]
      exact isOpen_biUnion (fun z₀ hz₀ =>
        (hall z₀ 0 k (hK₀sub (htsub k hz₀))
          (by rw [norm_zero]; exact hr₀pos)).1)
    rw [hSdef]
    exact isOpen_iInter_of_finite (fun k => fiberGate_isOpen (hGopen k) q)
  · -- `hKSmeas`-shaped joint measurability of `{w | w.2.2∈K ∧ w.2.1∈S w.2.2}`
    have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
    have hGmeas : ∀ k, MeasurableSet (G k) := by
      intro k
      have hGopen : IsOpen (G k) := by
        rw [hGdef]
        exact isOpen_biUnion (fun z₀ hz₀ =>
          (hall z₀ 0 k (hK₀sub (htsub k hz₀))
            (by rw [norm_zero]; exact hr₀pos)).1)
      exact hGopen.measurableSet
    have hAk : ∀ k : Fin n, MeasurableSet
        {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ fiberGate (G k) w.2.2} :=
      fun k => fiberGate_gate_measurableSet (hGmeas k) hKmeas
    have hk₀ : Fin n := ⟨0, hn⟩
    have hEq : {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
        = ⋂ k, {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ fiberGate (G k) w.2.2} := by
      ext w
      simp only [hSdef, Set.mem_iInter, mem_fiberGate, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hwK, hall'⟩
        exact fun k => ⟨hwK, hall' k⟩
      · intro hall'
        exact ⟨(hall' hk₀).1, fun k => (hall' k).2⟩
    rw [hEq]
    exact MeasurableSet.iInter hAk
  · -- diagonal inclusion `∀ q ∈ K₀, q ∈ S q`
    intro q hq
    rw [hSdef]
    simp only [Set.mem_iInter, mem_fiberGate]
    intro k
    have hmem := htcov k (Set.mem_image_of_mem _ hq)
    simpa [hGdef] using hmem

end QIQTH.ExpMap

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ExpMap
#print axioms finite_diag_cover_of_open_family
#print axioms finite_diag_cover_of_family
#print axioms chartGate_concrete_S_construction
end AxiomChecks
