/-
  HDmeasGFromFieldSliceTimeDeriv — J4-1116: the TIME-DERIVATIVE analogue of J4-973's
  `HFmeasGFromFieldSlice.hFmeasG_of_field_slice`, discharging J4-1115's remaining `hDmeas` carrier of
  `HDConvBoundDHpardiffAnySConstGateHFzeroDischarge.hDConv_boundD_hpardiff_anyS_constGate_hfzero_wired`
  by the SAME product-splitter route, peeling the witness τ-DERIVATIVE factor onto a NEW witness-side
  lever (the τ-independence of the gate condition lets `deriv` commute with the outer gate `if`), leaving
  the honest F-side residue `hFslice` (shared with `hAmeas`'s own reduction).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE / carrier-reduction brick.  No `sorry`, no new axioms, no `:= True`, no vacuous
  / unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT J4-973 COVERED, AND WHAT IT DID NOT.  `HFmeasGFromFieldSlice.hFmeasG_of_field_slice` reduces
  the PLAIN witness·F product measurability (`hAmeas`'s shape) to `{hKm, hSm0, hIn, hFslice}` via the
  BANKED `WitnessMeasDeriv.vanVleckGatedWitness_slice_aestronglyMeasurable`.  That lemma (and every other
  banked "Deriv"-measurability lemma in the tower — `WitnessMeasDeriv.lean`, `WitnessDerivMeasurability
  .lean`) is about the SPATIAL first-derivative kernel `witnessFieldDeriv` (a `Point n`-coordinate
  derivative), NOT the τ-derivative `deriv (fun r => vanVleckGatedWitness … r p z) τ` that `hDmeas`
  actually needs.  No banked lemma covers this object; THIS FILE supplies it.

  ## THE NEW LEVER (genuinely new, but small and structural).  `gatedKernel K S H τ p q := if q∈K then
  (if p∈Sq then H τ p q else 0) else 0` — the gate condition `q∈K ∧ p∈Sq` does NOT mention `τ` at all.
  So, AS A FUNCTION OF `τ`, `fun τ => gatedKernel K S H τ p q` is LITERALLY one of the two branches
  `(fun τ => H τ p q)` / `(fun _ => 0)` (a `funext` + `by_cases` case split on the τ-INDEPENDENT
  condition, not a "deriv of an `ite`" pointwise fact) — hence
      `deriv (fun τ => gatedKernel K S H τ p q) r
        = if q ∈ K then (if p ∈ S q then deriv (fun τ => H τ p q) r else 0) else 0`
  UNCONDITIONALLY (no differentiability hypothesis of any kind).  `gpt-5.6-sol` (high) confirmed this
  route 2026-08-24: no `Function.update`/`deriv_ite` subtlety, pure case-split function-equality.  The
  resulting RHS is itself `gatedKernel K S (fun τ p q => deriv (fun r => H r p q) τ) τ p q` — i.e. the
  τ-derivative of a gated kernel is the SAME gate applied to the derivative of the base kernel — so the
  EXISTING gated-indicator measurability lever (`WitnessMeasDeriv.gatedKernel_slice_aestronglyMeasurable`)
  applies VERBATIM to it, with the base kernel `H` replaced by its τ-derivative `fun τ p q ↦ deriv (fun
  r ↦ H r p q) τ`.

  ## HONEST STATUS OF THE NEW CARRY `hInDeriv`.  `gpt-5.6-sol` (high) audited this precisely: `hInDeriv`
  is NOT a logical weakening of `hDmeas` (e.g. it is not implied by `hDmeas` on an empty gate or `F ≡ 0`),
  nor is it implied by `hIn` alone (fixed-time slice measurability does not control the measurability of
  Mathlib's totalized `deriv` at points of possible non-differentiability) — it is a genuinely SEPARATE,
  strictly LIGHTER (ungated, F-free) carry, exactly parallel in spirit to `hIn` (which plays the same role
  for the un-differentiated witness).  This is an honest carrier FACTORIZATION (relocating the analytic
  content onto the ungated inner kernel), not a discharge of that content — `hInDeriv` remains carried,
  satisfiable, non-vacuous, never the conclusion.  Verdict: GO, build today (Sol, 2026-08-24).

  ## WHAT THIS DOES — AND DOES NOT — DO.  Reduces `hDmeas` (product) → `{hKm, hSm0, hInDeriv, hFslice}`,
  mirroring J4-973's `hFmeasG` (`hAmeas`) reduction to `{hKm, hSm0, hIn, hFslice}` — `hKm`/`hSm0`/`hFslice`
  are SHARED between the two reductions, so together `{hAmeas, hDmeas}` (2 entangled product carries)
  reduce to `{hKm, hSm0, hIn, hInDeriv, hFslice}` (5 honest, lighter, non-entangled carries — 3 new beyond
  J4-973's own residue).  Does NOT discharge `hFdom`/`hbase`, nor touch `hDuhamel`/`hDConv`/`hCConv`.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WitnessMeasDeriv
import QIQTH.HFmeasGFromFieldSlice

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.WitnessMeasDeriv QIQTH.HFmeasGFromFieldSlice
open scoped Interval Topology BigOperators

namespace QIQTH.HDmeasGFromFieldSliceTimeDeriv

variable {n : ℕ}

/-! ###############################################################################
    ### §A — the STRUCTURAL LEVER: `deriv` commutes with a τ-INDEPENDENT gate.
    ############################################################################### -/

/-- **★ `deriv_gatedKernel_time` — THE STRUCTURAL IDENTITY.**  For any base kernel `H`, since the gate
    condition `q ∈ K ∧ p ∈ S q` does not mention the time argument, `fun τ ↦ gatedKernel K S H τ p q` is
    literally one of the two branches `(fun τ ↦ H τ p q)` / `(fun _ ↦ 0)` — a pure `funext`+`by_cases`
    case split, NO differentiability hypothesis needed.  Hence the τ-derivative of a gated kernel IS the
    (identically) gated τ-derivative of the base kernel.  NOT `a₁ = R/6`. -/
theorem deriv_gatedKernel_time (K : Set (Point n)) (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) (r : ℝ) (p q : Point n) :
    deriv (fun τ => gatedKernel K S H τ p q) r
      = gatedKernel K S (fun τ p q => deriv (fun r' => H r' p q) τ) r p q := by
  classical
  by_cases hq : q ∈ K
  · by_cases hp : p ∈ S q
    · have h1 : (fun τ => gatedKernel K S H τ p q) = (fun τ => H τ p q) := by
        funext τ; exact gatedKernel_apply_of_mem K S H τ hq hp
      have h2 : gatedKernel K S (fun τ p q => deriv (fun r' => H r' p q) τ) r p q
          = deriv (fun r' => H r' p q) r := gatedKernel_apply_of_mem K S _ r hq hp
      rw [h1, h2]
    · have h1 : (fun τ => gatedKernel K S H τ p q) = (fun _ : ℝ => (0 : ℝ)) := by
        funext τ; exact gatedKernel_apply_of_notMem K S H τ p q (Or.inr hp)
      have h2 : gatedKernel K S (fun τ p q => deriv (fun r' => H r' p q) τ) r p q = 0 :=
        gatedKernel_apply_of_notMem K S _ r p q (Or.inr hp)
      rw [h1, h2, deriv_const]
  · have h1 : (fun τ => gatedKernel K S H τ p q) = (fun _ : ℝ => (0 : ℝ)) := by
      funext τ; exact gatedKernel_apply_of_notMem K S H τ p q (Or.inl hq)
    have h2 : gatedKernel K S (fun τ p q => deriv (fun r' => H r' p q) τ) r p q = 0 :=
      gatedKernel_apply_of_notMem K S _ r p q (Or.inl hq)
    rw [h1, h2, deriv_const]

/-! ###############################################################################
    ### §B — the τ-derivative gated-slice measurability lever (reuses §A + the banked non-deriv lever).
    ############################################################################### -/

/-- **★★ `gatedKernelDeriv_slice_aestronglyMeasurable`.**  The τ-DERIVATIVE analogue of
    `WitnessMeasDeriv.gatedKernel_slice_aestronglyMeasurable`: for a fixed time `τ` and field point `p`,
    if `K` is measurable, the field-gate preimage `{z | p ∈ S z}` is measurable, and the INNER kernel's
    τ-derivative slice `z ↦ deriv (fun r ↦ H r p z) τ` is `AEStronglyMeasurable`, then the gated
    τ-derivative slice `z ↦ deriv (fun r ↦ gatedKernel K S H r p z) τ` is `AEStronglyMeasurable`.  Route:
    rewrite via `deriv_gatedKernel_time` to `gatedKernel K S (τ-deriv of H) τ p z`, then apply the
    BANKED non-deriv lever to the τ-derivative kernel.  NOT `a₁ = R/6`. -/
theorem gatedKernelDeriv_slice_aestronglyMeasurable (K : Set (Point n)) (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p : Point n) (ν : Measure (Point n))
    (hKm : MeasurableSet K) (hSm : MeasurableSet {z : Point n | p ∈ S z})
    (hDm : AEStronglyMeasurable (fun z => deriv (fun r => H r p z) τ) ν) :
    AEStronglyMeasurable (fun z => deriv (fun r => gatedKernel K S H r p z) τ) ν := by
  have hrw : (fun z => deriv (fun r => gatedKernel K S H r p z) τ)
      = (fun z => gatedKernel K S (fun τ' p' q' => deriv (fun r' => H r' p' q') τ') τ p z) := by
    funext z; exact deriv_gatedKernel_time K S H τ p z
  rw [hrw]
  exact gatedKernel_slice_aestronglyMeasurable K S _ τ p ν hKm hSm hDm

/-- **`vanVleckGatedWitnessDeriv_slice_aestronglyMeasurable`** — the concrete wrapper of the τ-derivative
    lever for the `N = 1` gated van-Vleck witness `H_G`.  The witness τ-derivative slice
    `z ↦ deriv (fun r ↦ H_G r p z) τ` is `AEStronglyMeasurable` from {`K` measurable, `{z | p ∈ S z}`
    measurable, inner order-1 parametrix τ-derivative slice z-ae-measurable}.  NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitnessDeriv_slice_aestronglyMeasurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (p : Point n)
    (hKm : MeasurableSet K) (hSm : MeasurableSet {z : Point n | p ∈ S z})
    (hInDeriv : AEStronglyMeasurable
      (fun z => deriv (fun r => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) r p z) τ)
      (volume : Measure (Point n))) :
    AEStronglyMeasurable
      (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r p z) τ)
      (volume : Measure (Point n)) := by
  unfold vanVleckGatedWitness
  exact gatedKernelDeriv_slice_aestronglyMeasurable K S _ τ p volume hKm hSm hInDeriv

/-! ###############################################################################
    ### §C — THE CONCRETE REDUCTION: `hDmeas` from banked witness-side infra + pure F-slice carry.
    ############################################################################### -/

/-- **★★★ `hDmeasG_of_field_slice` — the `hDmeas` product-measurability carrier REDUCED to a pure F-slice
    carry.**  The TIME-DERIVATIVE analogue of `HFmeasGFromFieldSlice.hFmeasG_of_field_slice`.  For the
    concrete gated van-Vleck witness `A := vanVleckGatedWitness g gi hC hK S cutA cutB` and free field `F`,
    GIVEN the WITNESS-SIDE carries `{hKm, hSm0, hInDeriv}` (the τ-derivative analogue of `hIn`) and the
    PURE F-side carry `hFslice : ∀ s, AEStronglyMeasurable (fun z ↦ F s z 0) volume`, the product
    slice-measurability `hDmeas`'s literal shape holds:
        `∀ s c, AEStronglyMeasurable (fun z ↦ deriv (fun r ↦ A r 0 z) (c−s) · F s z 0) volume`.
    Route: `vanVleckGatedWitnessDeriv_slice_aestronglyMeasurable` discharges the witness τ-derivative
    factor from `{hKm, hSm0, hInDeriv}`; `.mul` with `hFslice` gives the product.  NOT `a₁ = R/6`. -/
theorem hDmeasG_of_field_slice
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hInDeriv : ∀ τ : ℝ, AEStronglyMeasurable
      (fun z => deriv (fun r => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) cutA cutB
        (uniformInverseChart g gi hC hK) r (0 : Point n) z) τ)
      (volume : Measure (Point n)))
    (hFslice : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z 0) (volume : Measure (Point n))) :
    ∀ s c : ℝ, AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s)
          * F s z 0) volume := by
  intro s c
  refine aesm_mul_of_slices ?_ (hFslice s)
  exact vanVleckGatedWitnessDeriv_slice_aestronglyMeasurable g gi hC hK S cutA cutB (c - s)
    (0 : Point n) hKm hSm0 (hInDeriv (c - s))

/-! ###############################################################################
    ### §D — NON-VACUITY (TEETH).  §A's identity is genuinely active (not a `0=0` collapse).
    ############################################################################### -/

/-- **Non-vacuity (TEETH) of `deriv_gatedKernel_time`.**  On the gate (`q ∈ K`, `p ∈ S q`), with a
    genuinely τ-differentiable base kernel `H τ p q := τ` (so `deriv (fun τ ↦ H τ p q) r = 1 ≠ 0`), the
    gated τ-derivative EQUALS the same nonzero value `1` — the identity is ACTIVE, not a `0 = 0`
    degeneracy. -/
theorem deriv_gatedKernel_time_hyp_satisfiable :
    ∃ (K : Set (Point n)) (S : Point n → Set (Point n)) (p q : Point n),
      q ∈ K ∧ p ∈ S q ∧
      deriv (fun τ : ℝ => gatedKernel K S (fun τ' _ _ => τ') τ p q) (0 : ℝ) = 1 := by
  classical
  refine ⟨Set.univ, (fun _ => Set.univ), 0, 0, Set.mem_univ _, Set.mem_univ _, ?_⟩
  have h1 : (fun τ : ℝ => gatedKernel Set.univ (fun _ => Set.univ) (fun τ' _ _ => τ') τ
      (0 : Point n) (0 : Point n)) = (fun τ : ℝ => τ) := by
    funext τ
    exact gatedKernel_apply_of_mem Set.univ (fun _ => Set.univ) (fun τ' _ _ => τ') τ
      (Set.mem_univ _) (Set.mem_univ _)
  rw [h1]
  simpa using (hasDerivAt_id (0 : ℝ)).deriv

end QIQTH.HDmeasGFromFieldSliceTimeDeriv

section AxiomChecks
open QIQTH.HDmeasGFromFieldSliceTimeDeriv
#print axioms deriv_gatedKernel_time
#print axioms gatedKernelDeriv_slice_aestronglyMeasurable
#print axioms vanVleckGatedWitnessDeriv_slice_aestronglyMeasurable
#print axioms hDmeasG_of_field_slice
#print axioms deriv_gatedKernel_time_hyp_satisfiable
end AxiomChecks
