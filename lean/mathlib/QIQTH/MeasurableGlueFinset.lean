/-
  MeasurableGlueFinset — J4-1131: dispatch 9 of the "inverse-branch overlap-uniqueness bridge"
  sub-campaign (greenlit J4-1122, hub lemma J4-1123, two-seed `Set.EqOn` corollary J4-1124,
  open-overlap germ compatibility J4-1125, target-facing value/`fderiv`/carrier consumer triple
  J4-1126, literal coordinate-line `HasDerivAt` transfer J4-1127, first-order coefficient-field
  agreement J4-1128, second-order (`Qfield`) agreement J4-1129, concrete single-seed `fderiv`-built
  representative J4-1130, per `gpt-5.6-sol` high consult 2026-08-24 x9).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  J4-1130's own "Next dispatch" note flags the piecewise/global gluing across MANY seeds as the
  genuinely harder, compactness/patching-flavoured remaining task. Per Sol's ninth consult, the
  FULL chart-specific gluing (covering `hcarField`'s `∀ w, w.2.2 ∈ K → …` over all of `K`) is
  DEFERRED to a later dispatch for two independent reasons Sol identified:

    (a) the SEED space `{(z,v) : z ∈ interior K, ‖v‖ < c}` is generally only OPEN, not compact
        (`interior K` alone gives no finite subcover); a genuine finite-subcover argument needs a
        COMPACT `K₀ ⊆ interior K` together with a STRICT gate-radius inequality `c < r₀` — neither
        of which this sub-campaign has established yet (this is a NEW obligation, not yet
        discharged anywhere in the tower);
    (b) even granting (a), extracting the actual finite chart family from J4-1130's construction
        (pulling back the seed-indexed open pieces through the flow-exp map `Φ(z,v) := (z, exp_z
        v)` and invoking compactness) is itself nontrivial plumbing.

  Per Sol's explicit recommendation ("recommended dispatch order: (1) prove the abstract finite
  `Set.piecewise` gluing lemma... (2) optionally add a coordinatewise-field corollary... (3)
  separately resolve the compact target issue... (4) only then extract the finite chart family"),
  THIS dispatch builds ONLY step (1): a wholly chart-agnostic, topology-free, general-purpose
  lemma — glue finitely many pairwise-overlap-agreeing `Measurable` functions (indexed by an
  arbitrary `Finset`, over arbitrary measurable spaces) into a SINGLE global `Measurable` function
  that agrees with each input on its own domain — via iterated `Set.piecewise`
  (`Finset.induction_on` + `Measurable.piecewise`), NOT a `Nat.find`-style selector (Sol: "do not
  build a measurable selector explicitly"). No compactness, no charts, no `K`, no seeds — purely
  the abstract combinatorial/measure-theoretic gluing brick steps (3)/(4) will consume later.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. No `sorry`, no new axioms, no vacuous/unsatisfiable
  hypotheses, no existing file edited. This file is PURELY ABSTRACT (no reference to
  `uniformInverseChart`, `chartCoherent`, `K`, or any chart/geometry object) — it does NOT yet
  instantiate the chart-specific gluing, does NOT establish the compact-seed-space obligation
  (b) flagged above (a genuinely NEW, not-yet-discharged prerequisite: a compact `K₀ ⊆ interior K`
  together with `c < r₀`), and does NOT yet extract a finite chart family from J4-1130's
  single-seed construction. `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv,
  hCConv}`, UNCHANGED.
-/
import Mathlib
import QIQTH.Curvature

open MeasureTheory

namespace QIQTH.ExpMap

open QIQTH.Curvature (Point)

/-! ###############################################################################
    ## The abstract finite measurable-gluing lemma (chart-agnostic, topology-free).
    ############################################################################### -/

/-- **★★ J4-1131 — `exists_measurable_glue_finset`: glue finitely many pairwise-overlap-agreeing
    `Measurable` functions into a single global `Measurable` function.** Given a `Finset` index set
    `I`, a family of `MeasurableSet`s `U i`, a family of `Measurable` functions `f i` (each defined
    on the WHOLE space, but only intended to be authoritative on its own `U i`), a `Measurable`
    `fallback` for points outside every `U i`, and PAIRWISE agreement of `f i`/`f j` on the overlap
    `U i ∩ U j` for every `i j ∈ I` (the exact shape J4-1128's `chartCoherent_field_agree_at_overlap_
    two_seeds`, instantiated with two chart-specific representatives, supplies) — there is a single
    `g : X → Y`, `Measurable`, agreeing with `f i` throughout `U i` for every `i ∈ I`. Built by
    `Finset.induction_on` + iterated `Set.piecewise`, prioritising the most-recently-inserted index
    on the overlap of its own set with earlier ones; pairwise agreement (used for the FRESH index
    against the ALREADY-GLUED function, at any point lying in both) shows this prioritisation is
    invisible in the final `EqOn` conclusion — the glued function agrees with EVERY `f i` on ALL of
    `U i`, not merely the highest-priority one. -/
theorem exists_measurable_glue_finset {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (I : Finset ι) (U : ι → Set X) (f : ι → X → Y) (fallback : X → Y)
    (hU : ∀ i, MeasurableSet (U i)) (hf : ∀ i, Measurable (f i))
    (hfallback : Measurable fallback)
    (hagree : ∀ i j, Set.EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ g : X → Y, Measurable g ∧ ∀ i ∈ I, Set.EqOn g (f i) (U i) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨fallback, hfallback, by simp⟩
  | insert a I ha ih =>
      obtain ⟨g, hg, hglue⟩ := ih
      refine ⟨(U a).piecewise (f a) g, Measurable.piecewise (hU a) (hf a) hg, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hiI
      · intro x hxa
        simp [Set.piecewise, hxa]
      · intro x hxi
        by_cases hxa : x ∈ U a
        · have := hagree a i ⟨hxa, hxi⟩
          simpa [Set.piecewise, hxa] using this
        · simpa [Set.piecewise, hxa] using hglue i hiI hxi

/-- **Corollary — the coordinatewise-field specialization.** For a family of candidate coefficient
    fields `Pfield_i : Point n → Point n → Fin n → ℝ` (matching J4-1130's output shape), each
    `Measurable` (per output component `jj`) throughout the whole space and pairwise-agreeing on
    the raw-set overlaps `U i ∩ U j`, there is a single glued field `Pfield`, `Measurable` per
    component, agreeing with every `Pfield i` throughout `U i` — the exact well-definedness shape
    the eventual chart-specific gluing will instantiate this with, one output component `jj` at a
    time, via `exists_measurable_glue_finset` applied to `X := Point n × Point n`, `Y := ℝ`. -/
theorem exists_measurable_glue_finset_field {n : ℕ} {ι : Type*} (I : Finset ι)
    (U : ι → Set (Point n × Point n)) (Pfield : ι → Point n → Point n → Fin n → ℝ)
    (hU : ∀ i, MeasurableSet (U i))
    (hPfield : ∀ i jj, Measurable (fun ξ : Point n × Point n => Pfield i ξ.1 ξ.2 jj))
    (hagree : ∀ i j jj, Set.EqOn (fun ξ : Point n × Point n => Pfield i ξ.1 ξ.2 jj)
      (fun ξ : Point n × Point n => Pfield j ξ.1 ξ.2 jj) (U i ∩ U j)) :
    ∃ Pglued : Point n → Point n → Fin n → ℝ,
      (∀ jj, Measurable (fun ξ : Point n × Point n => Pglued ξ.1 ξ.2 jj)) ∧
      ∀ i ∈ I, ∀ jj, Set.EqOn (fun ξ : Point n × Point n => Pglued ξ.1 ξ.2 jj)
        (fun ξ : Point n × Point n => Pfield i ξ.1 ξ.2 jj) (U i) := by
  classical
  choose g hg hglue using fun jj =>
    exists_measurable_glue_finset I U (fun i => fun ξ : Point n × Point n => Pfield i ξ.1 ξ.2 jj)
      (fun _ => 0) hU (hPfield · jj) measurable_const (hagree · · jj)
  refine ⟨fun q p jj => g jj (q, p), ?_, ?_⟩
  · intro jj
    exact hg jj
  · intro i hi jj ξ hξ
    exact hglue jj i hi hξ

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms exists_measurable_glue_finset
#print axioms exists_measurable_glue_finset_field
end AxiomChecks
