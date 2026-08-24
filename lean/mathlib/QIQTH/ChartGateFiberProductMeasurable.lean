/-
  ChartGateFiberProductMeasurable — J4-1135: dispatch 12 of the "inverse-branch overlap-uniqueness
  bridge" sub-campaign (greenlit J4-1122, ... , seed-indexed pairwise-compatible `Pfield` family
  J4-1132, diagonal finite-subcover coverage J4-1133, DECISIVE REDIRECT AUDIT J4-1134 — the target
  consumer is `GatedRepSFix.tripleHEmeas_concrete_v4`'s conditional `S`-carrier, NOT the unreachable
  literal `hcarField`/`hcarField2` of `ChartJointBorel.lean` — per `gpt-5.6-sol` high consult
  2026-08-24 x13).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does (and does NOT do).

  J4-1134 redirected the sub-campaign toward `GatedRepSFix.tripleHEmeas_concrete_v4`, whose
  `S`-carrier hypotheses are all SATISFIABLE (S-membership is a HYPOTHESIS, not a forced
  conclusion). A thirteenth Sol consult (2026-08-24, BEFORE any Lean this dispatch) worked out the
  concrete wiring: for a fixed coordinate `k`, the diagonal-cover family of `ChartCoherentPField-
  DiagonalFiniteCover.lean` (J4-1133) yields an open "gate" `G_k := ⋃_{z₀∈t_k} U z₀ 0 k ⊆ Point n ×
  Point n`, and the natural candidate `S_k q := {p | (q,p) ∈ G_k}` (the "fiber" of `G_k` at base
  point `q`) is open, contains `q` itself for every `q` in the diagonal-cover's compact target
  `K₀`, and — crucially — any `p ∈ S_k q` places `(q,p)` inside SOME seed's `U z₀ 0 k`, where the
  glued representative literally witnesses the needed `HasDerivAt`. Sol's decisive correction: the
  outer `S` of `tripleHEmeas_concrete_v4` is SHARED across `∀ k, ∃ Pfield` (`hcarField`) and
  `∀ i j, ∃ Pifield Pjfield Qfield` (`hcarField2`) — so a per-`k` union `⋃ k, S_k` is WRONG (a
  point `p` landing in `S_k q` for only ONE `k` does not license the `k'`-derivative clause for a
  DIFFERENT `k'`); the correct combination is a FINITE INTERSECTION `S q := ⋂ k, S_k q` (over
  `k : Fin n`, a `Fintype`), so that `p ∈ S q` licenses EVERY coordinate's on-gate clause
  simultaneously. This file builds the generic, CHART-AGNOSTIC piece Sol identified as the smallest
  useful first brick underlying that combination: "fiber gates" of a product-space open/measurable
  set, their openness, their diagonal-membership transfer, and — the genuinely new content beyond
  `MeasurableGlueFinset.lean` — the JOINT measurability of the induced `{w | w.2.2 ∈ K ∧ w.2.1 ∈
  fiberGate G w.2.2}` incidence set consumed directly by `hKSmeas`. Finite-intersection openness
  (`Fin n` being `Finite`) and the fiber-of-an-intersection identity are included so the eventual
  `S := ⋂ k, S_k` combination is a direct instantiation, not a fresh argument.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. No `sorry`, no new axioms, no vacuous/unsatisfiable
  hypotheses, no existing file edited (NEW FILE). This file is PURELY ABSTRACT (arbitrary
  topological/measurable types `X`, `Y`, `Z`; no reference to `uniformInverseChart`, `chartCoherent`,
  `K`, `interior K`, seeds, or any chart/geometry object) — mirroring `MeasurableGlueFinset.lean`'s
  scope discipline. It does NOT yet: instantiate `G` with the actual diagonal-cover family `⋃_{z₀∈t}
  U z₀ 0 k`; define the chart-specific `S_k`/`S := ⋂ k, S_k`; glue the finite `Pfield`/`Pifield`/
  `Pjfield`/`Qfield` families via `exists_measurable_glue_finset_field`; discharge the
  `PdiffAt (chartFieldAmp …)` conjuncts (an unrelated amplitude/geometric obligation, never
  touched by this sub-campaign); discharge `hOffS`/`hOffS2` (the radialCutoff-support facts —
  Sol flagged these as HARDER once `S` is intersection-shrunk, since a smaller `S` makes the
  off-`S` region LARGER, an obligation this file does not address); or produce any actual
  `tripleHEmeas_concrete_v4`/`a1_R6_assembled_v7` invocation. `a₁ = R/6` remains STRICTLY
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import Mathlib

open MeasureTheory

namespace QIQTH.ExpMap

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- **`fiberGate` — the fiber of a product-space set `G ⊆ X × Y` at a base point `q : X`.**
    `fiberGate G q = {p | (q,p) ∈ G}`.  Chart-agnostic; `X`/`Y` will later be instantiated at
    `Point n` (base point / field point respectively) and `G` at the chart-cover union. -/
def fiberGate (G : Set (X × Y)) (q : X) : Set Y := {p | (q, p) ∈ G}

@[simp] theorem mem_fiberGate {G : Set (X × Y)} {q : X} {p : Y} :
    p ∈ fiberGate G q ↔ (q, p) ∈ G := Iff.rfl

/-- **★ `fiberGate_isOpen`.**  The fiber of an open product-space set is open, via continuity of
    the partial-application map `p ↦ (q,p)`. -/
theorem fiberGate_isOpen {G : Set (X × Y)} (hG : IsOpen G) (q : X) :
    IsOpen (fiberGate G q) := by
  have hcont : Continuous (fun p : Y => (q, p)) := continuous_const.prodMk continuous_id
  have heq : fiberGate G q = (fun p : Y => (q, p)) ⁻¹' G := rfl
  rw [heq]
  exact hG.preimage hcont

/-- **`fiberGate_diag_mem`.**  If `(q,q) ∈ G` (the diagonal case, `X = Y`), then `q ∈ fiberGate G
    q` — the transfer used to certify nonvacuity of `S q` from diagonal-cover membership. -/
theorem fiberGate_diag_mem {G : Set (X × X)} {q : X} (h : (q, q) ∈ G) :
    q ∈ fiberGate G q := h

/-- **★★ `fiberGate_gate_measurableSet` — THE PAYLOAD: joint measurability of the gated incidence
    set `{w | w.2.2 ∈ K ∧ w.2.1 ∈ fiberGate G w.2.2}` consumed directly by `hKSmeas` in
    `GatedRepSFix.tripleHEmeas_concrete_v4` (with `Z := ℝ`, `X := Y := Point n`, `w.2.2` the base
    point, `w.2.1` the field point).  From `G` measurable (e.g. `hG.measurableSet` for `G` open, in
    the presence of `[OpensMeasurableSpace (X × Y)]`) and `K` measurable, via the algebraic identity
    `{w | w.2.2∈K ∧ w.2.1∈fiberGate G w.2.2} = (Prod.snd∘Prod.snd)⁻¹'K ∩ (fun w↦(w.2.2,w.2.1))⁻¹'G`
    and measurability of the coordinate-projection / swap maps. -/
theorem fiberGate_gate_measurableSet {G : Set (X × Y)} {K : Set X}
    (hG : MeasurableSet G) (hK : MeasurableSet K) :
    MeasurableSet {w : Z × Y × X | w.2.2 ∈ K ∧ w.2.1 ∈ fiberGate G w.2.2} := by
  have hsnd2 : Measurable (fun w : Z × Y × X => w.2.2) := measurable_snd.comp measurable_snd
  have hfst2 : Measurable (fun w : Z × Y × X => w.2.1) := measurable_fst.comp measurable_snd
  have hswap : Measurable (fun w : Z × Y × X => ((w.2.2, w.2.1) : X × Y)) :=
    hsnd2.prodMk hfst2
  have heq : {w : Z × Y × X | w.2.2 ∈ K ∧ w.2.1 ∈ fiberGate G w.2.2}
      = (fun w : Z × Y × X => w.2.2) ⁻¹' K ∩ (fun w : Z × Y × X => ((w.2.2, w.2.1) : X × Y)) ⁻¹' G := by
    ext w
    simp
  rw [heq]
  exact (hK.preimage hsnd2).inter (hG.preimage hswap)

/-- **`fiberGate_iInter` — the fiber of a finite intersection is the intersection of fibers.**
    `fiberGate (⋂ i, G i) q = ⋂ i, fiberGate (G i) q`, so combining per-coordinate gates
    `G k` (`k : ι`, `Fintype ι`) into the SHARED gate `⋂ k, G k` transfers directly to `S`. -/
theorem fiberGate_iInter {ι : Type*} (G : ι → Set (X × Y)) (q : X) :
    fiberGate (⋂ i, G i) q = ⋂ i, fiberGate (G i) q := by
  ext p
  simp [fiberGate]

/-- **★ `fiberGate_iInter_isOpen` — openness survives the FINITE intersection.**  For `ι` finite
    (e.g. `ι = Fin n`), the shared gate `⋂ i, G i` is open whenever each `G i` is, and hence so is
    every fiber `fiberGate (⋂ i, G i) q` — the exact fact needed for `S := ⋂ k, S_k` to satisfy the
    `IsOpen (S w.2.2)` conjunct of `hcarField`/`hcarField2` simultaneously for every coordinate. -/
theorem fiberGate_iInter_isOpen {ι : Type*} [Finite ι] {G : ι → Set (X × Y)}
    (hG : ∀ i, IsOpen (G i)) (q : X) :
    IsOpen (fiberGate (⋂ i, G i) q) := by
  rw [fiberGate_iInter]
  exact isOpen_iInter_of_finite (fun i => fiberGate_isOpen (hG i) q)

end QIQTH.ExpMap

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ExpMap
#print axioms fiberGate_isOpen
#print axioms fiberGate_diag_mem
#print axioms fiberGate_gate_measurableSet
#print axioms fiberGate_iInter
#print axioms fiberGate_iInter_isOpen
end AxiomChecks
