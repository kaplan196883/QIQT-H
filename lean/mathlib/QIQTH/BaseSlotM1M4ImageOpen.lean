/-
  BaseSlotM1M4ImageOpen — J4-1022: `IsOpen (W '' S')` for a genuine open domain `S'` carrying the
  FULL M1–M4 package (`BaseSlotM1M4Assembly`, J4-1008), closing the ONE precisely-named remaining
  gap flagged by J4-1021 (`HCompNearCarryTerm1AmpWeightedTail`): "gap (II)"'s ball-containment
  retargeting (J4-1020's Brick B, `S'` z-space → `W''S'` w-space) needs `IsOpen (W''S')`, which
  `BaseSlotM1M4Assembly`'s public existential does NOT expose (it hides the underlying
  `OpenPartialHomeomorph` structure entirely — only `S'`, `V`, `InjOn`, the left-inverse, M1, and M4
  are surfaced).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROUTE (Sol `gpt-5.6-sol`, high, 2026-08-23, consulted before Lean; confirmed sound).

  Sol confirmed: rather than re-deriving `BaseSlotM1M4Assembly`'s ENTIRE ~60-line construction
  (Steps B–E: the diagonal-tube joint-C² slice `Uslice`, and the units-openness `Uinv`) just to keep
  the internal `OpenPartialHomeomorph` `e` in scope, the CHEAPER and more ROBUST route is:
    1. Call the ALREADY-BANKED, PUBLIC `uniformInverseChart_baseSlot_M1M4_generalK`
       (`BaseSlotM1M4Assembly`, J4-1008) as an OPAQUE black box, obtaining its witness set `T` with
       the full M1–M4 package.
    2. SEPARATELY reconstruct the `OpenPartialHomeomorph` `e := hstrict.toOpenPartialHomeomorph W`
       from the ALREADY-BANKED, PUBLIC `uniformInverseChart_baseSlot_hasStrictFDerivAt_CLE_generalK`
       (`BaseSlotIFTLocalHomeomorph`, J4-1007) — the SAME strict-derivative fact that
       `BaseSlotM1M4Assembly` itself is built on (transitively, via its call to
       `uniformInverseChart_baseSlot_localOpenHomeomorph_generalK`), but this time keeping `e` itself
       (not just its opaque `.source`) in hand.
    3. Define the NEW witness `S' := T ∩ e.source`. Since `S' ⊆ T`, ALL of the M1–M4 package
       restricts from `T` to `S'` for free (`Set.InjOn.mono`, pointwise restriction for the
       left-inverse/M4, `HasFDerivWithinAt.mono` for M1) — no need to know `T = e.source` on the
       nose, only `S' ⊆ T` and `S' ⊆ e.source`.
    4. `S' ⊆ e.source` is exactly what Mathlib's `OpenPartialHomeomorph.isOpen_image_of_subset_source`
       needs: `IsOpen (e '' S')`. Since `(e : Point n → Point n) = W` GLOBALLY (`toOpenPartialHomeomorph
       _coe`, not just on `e.source`), `e '' S' = W '' S'` by a bare rewrite — no pointwise
       image-congruence argument needed.
  This produces a SINGLE open set `S'` (a genuine, generally-SMALLER, subset of
  `BaseSlotM1M4Assembly`'s original witness — this is fine: any subsequent consumer just uses THIS
  file's `S'` as the operative near-carry domain, and every M1–M4 fact restricts) on which M1–M4
  hold AND `W '' S'` is open, for the FIRST time in this campaign.

  ## WHAT THIS FILE DOES **NOT** DO (honest scope; do NOT over-claim).
    (a) It does NOT attempt the full domain-restricted Amp-weighted term1 payoff (composing J4-1019's
        Lipschitz bound, J4-1020's ball-tail bounds, J4-1021's Amp-weighted tails, and THIS file's
        `IsOpen (W''S')` into a single explicit bound on `nb`'s actual domain) — that composition is
        a separate, substantial undertaking (matching up the literal `S'` used here against
        `HCompNearCarryChartSurfaceWired`'s literal `kPrime`/domain shape) and is NOT attempted here.
    (b) It does NOT wire into `HCompNearCarryChartSurfaceWired`'s literal `kPrime` shape or
        `VanVleckGatedSpatialSymmetry.hcomp`.  `nb`/`hcomp`/`hCConv` remain OPEN.
    (c) `Bfac`'s OTHER THREE terms are entirely untouched here; the far-carry `fb` remains SEPARATELY
        open regardless of anything in this file.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT
  `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none
  equal to the conclusion, no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.BaseSlotM1M4Assembly
import QIQTH.BaseSlotIFTLocalHomeomorph

open Filter Set MeasureTheory
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.HerrHminGeneralQ0GeneralK
open scoped Topology

namespace QIQTH.BaseSlotM1M4ImageOpen

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★★ `uniformInverseChart_baseSlot_M1M4_image_open_generalK`.**  THE PAYOFF: a single open set
`S' ∋ q₀` carrying `BaseSlotM1M4Assembly`'s FULL M1–M4 package (`InjOn`, a left inverse `V`, M1
`HasFDerivWithinAt` throughout `S'`, and M4 `0 < |det|` throughout `S'`) for the base-slot map
`W p := uniformInverseChart g gi hC hK p q₀`, PLUS the genuinely new fact that the CoV IMAGE `W '' S'`
is itself OPEN — closing the exact gap J4-1021 flagged as blocking the near-carry `nb`'s ball-
containment retargeting from `S'` (z-space) to `W''S'` (w-space).  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_M1M4_image_open_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ (S' : Set (Point n)) (V : Point n → Point n),
      IsOpen S' ∧ q₀ ∈ S' ∧
      Set.InjOn (fun p => uniformInverseChart g gi hC hK p q₀) S' ∧
      (∀ p ∈ S', V (uniformInverseChart g gi hC hK p q₀) = p) ∧
      (∀ z ∈ S', HasFDerivWithinAt (fun p => uniformInverseChart g gi hC hK p q₀)
          (fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) z) S' z) ∧
      (∀ z ∈ S', 0 < |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) z).det|) ∧
      IsOpen ((fun p => uniformInverseChart g gi hC hK p q₀) '' S') := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p q₀ with hWdef
  -- Step A: the banked M1–M4 package (J4-1008), used opaquely — its witness set `T`.
  obtain ⟨T, V, hTopen, hq0T, hinj, hV, hfd, hJpos⟩ :=
    QIQTH.BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_generalK g gi hC hK hq₀
  -- Step B: rebuild the `OpenPartialHomeomorph` `e` from the SAME underlying strict-derivative fact
  -- (J4-1007), this time keeping `e` (not just its opaque `.source`) in hand.
  have hstrict := QIQTH.BaseSlotIFTLocalHomeomorph.uniformInverseChart_baseSlot_hasStrictFDerivAt_CLE_generalK
    g gi hC hK hq₀
  set e := hstrict.toOpenPartialHomeomorph W with hedef
  have hcoe : (e : Point n → Point n) = W := hstrict.toOpenPartialHomeomorph_coe
  have hq0e : q₀ ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  -- Step C: the NEW witness `S' := T ∩ e.source` — every M1–M4 fact restricts from `T` for free.
  set S' : Set (Point n) := T ∩ e.source with hS'def
  have hS'open : IsOpen S' := hTopen.inter e.open_source
  have hS'subT : S' ⊆ T := Set.inter_subset_left
  have hS'sube : S' ⊆ e.source := Set.inter_subset_right
  refine ⟨S', V, hS'open, ⟨hq0T, hq0e⟩, hinj.mono hS'subT, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hV p (hS'subT hp)
  · intro z hz
    exact (hfd z (hS'subT hz)).mono hS'subT
  · intro z hz
    exact hJpos z (hS'subT hz)
  · -- Step D: the payoff — `S' ⊆ e.source` feeds Mathlib's own `isOpen_image_of_subset_source`.
    have himg : IsOpen (e '' S') := e.isOpen_image_of_subset_source hS'open hS'sube
    rwa [hcoe] at himg

end QIQTH.BaseSlotM1M4ImageOpen

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.BaseSlotM1M4ImageOpen
#print axioms uniformInverseChart_baseSlot_M1M4_image_open_generalK
end AxiomChecks
