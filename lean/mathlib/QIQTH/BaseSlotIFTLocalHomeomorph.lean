/-
  BaseSlotIFTLocalHomeomorph — J4-1007: the FIRST genuine local-diffeomorphism package for
  `uniformInverseChart`'s BASE slot, obtained by invoking Mathlib's actual Inverse Function Theorem
  (`HasStrictFDerivAt.toOpenPartialHomeomorph`), fed by J4-1006's general interior-`q₀`, general-`K`
  base-slot derivative data.  This is item (i) of `ChartGaussianChangeVar`'s (J4-269) own "missing-fact
  list" (M1)–(M4) for the CONCRETE change-of-variables instantiation, and (per the `HCompNearCarry
  ChartSurfaceWired`/`HCompNearCarryFullyClosed` firewalls) the residual item (ii) of the near-carry
  `nb`'s "base↔field change of variables".

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS ROUTE (Sol `gpt-5.6-sol`, high, 2026-08-22, qualified GO, consulted before Lean).

  Two earlier NO-GO diagnostics (cp882/883/884) ruled out building the base↔field CoV from the
  QUADRATIC ANTISYMMETRY-DEFECT bricks (J4-1002/1003) — those bound the RAW CHART MAP's antisymmetry,
  a DIFFERENT object from what a genuine change-of-variables needs (a two-sided C¹ local inverse with
  a controlled Jacobian).  Sol's redirect (cp882) named the correct route: "joint-C² CoV/Jacobian ->
  quantitative T(v) vs v control -> …".  This file supplies the FIRST half of that redirect — NOT via
  hand-assembling the change-of-variables data from the coercivity bounds (`herr_gate`/`hmin_gate`,
  J4-1006), which Sol confirmed do NOT by themselves give injectivity or a Jacobian bound (a coercive
  bound `‖W p‖² ≳ ‖p−q₀‖²` says nothing about `W p₁ − W p₂` for `p₁ ≠ p₂`) — but via Mathlib's OWN
  Inverse Function Theorem machinery, applied directly to the ALREADY-BANKED base-slot derivative fact
  `uniformInverseChart_baseSlot_fderiv_neg_id_generalK` (J4-1006) upgraded, using the ALREADY-BANKED
  joint `ContDiffAt ℝ 2` (`uniformInverseChart_jointContDiffAt_diag_generalK`, J4-884), to a
  `HasStrictFDerivAt` with an INVERTIBLE (self-inverse) derivative `−Id`.

  ## WHAT LANDS.
    • `negCLE` — the negation continuous linear equivalence on `Point n` (`(LinearEquiv.neg ℝ).to
      ContinuousLinearEquiv`), with `negCLE_coe` identifying its coercion with `−Id`.
    • `uniformInverseChart_baseSlot_contDiffAt_generalK` — the base-slot restriction `p ↦
      uniformInverseChart p q₀` is `ContDiffAt ℝ 2` at `q₀`, by composing the joint `ContDiffAt ℝ 2`
      (`uniformInverseChart_jointContDiffAt_diag_generalK`) with the smooth embedding `p ↦ (p, q₀)`.
    • `uniformInverseChart_baseSlot_hasStrictFDerivAt_generalK` — ★★ upgrades the (F4)-style base-slot
      `HasFDerivAt … (−Id) q₀` (J4-1006) to `HasStrictFDerivAt`, via `ContDiffAt.hasStrictFDerivAt`
      (order `≥ 1`) plus uniqueness of the Fréchet derivative to identify `fderiv ℝ W q₀` with `−Id`.
    • `uniformInverseChart_baseSlot_hasStrictFDerivAt_CLE_generalK` — the same fact re-packaged with
      the derivative typed as `negCLE`'s coercion, ready for Mathlib's IFT.
    • `uniformInverseChart_baseSlot_localOpenHomeomorph_generalK` — ★★★ THE PAYOFF: applying `HasStrict
      FDerivAt.toOpenPartialHomeomorph`, there is an OPEN set `S ∋ q₀` on which the base-slot map
      `p ↦ uniformInverseChart p q₀` is INJECTIVE, with an explicit LEFT INVERSE `V` (`V (W p) = p` for
      `p ∈ S`) — discharging M2 (`InjOn`) and M3 (the left inverse `V`) of `ChartGaussianChangeVar`'s
      missing-fact list, for the FIRST time in this campaign, directly from Mathlib's own IFT rather
      than any hand-built construction.

  ## WHAT THIS FILE DOES **NOT** DO (honest scope; do NOT over-claim).
    (a) It does NOT discharge M1 (`HasFDerivWithinAt W (f' z) S z` for EVERY `z ∈ S`, only AT `q₀`
        itself) — that needs `fderiv` to be shown differentiable/continuous THROUGHOUT `S` (available
        in principle from the same `ContDiffAt ℝ 2` shrunk to a `ContDiffOn` neighbourhood, NOT
        attempted here).
    (b) It does NOT discharge M4 (`0 < |det (f' z)|` uniformly on `S`) — this needs the openness of the
        invertible/unit elements of the endomorphism ring `Point n →L[ℝ] Point n` (Mathlib has
        `Units.isOpen` for complete normed rings) composed with continuity of `fderiv` and the
        `IsUnit ↔ det ≠ 0` bridge (`ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap` +
        `LinearMap.isUnit_iff_isUnit_det`) — all three pieces are confirmed to EXIST in this Mathlib
        checkout (grepped, not attempted/wired) but NOT assembled here.
    (c) It does NOT instantiate `ChartGaussianChangeVar.chart_gaussian_change_variables` (that needs
        M1+M4 too, per (a)/(b)).
    (d) It does NOT wire into `HCompNearCarryChartSurfaceWired`'s literal `kPrime` shape or `VanVleck
        GatedSpatialSymmetry.hcomp`.  `nb`/`hcomp`/`hCConv` remain OPEN.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HerrHminGeneralQ0GeneralK

open Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.HerrHminGeneralQ0GeneralK
open scoped Topology

namespace QIQTH.BaseSlotIFTLocalHomeomorph

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the negation continuous linear equivalence on `Point n`.
    ############################################################################### -/

/-- **`negCLE`.**  Negation `x ↦ −x` as a continuous linear EQUIVALENCE on `Point n` (finite-dimensional
    over `ℝ`, so any linear equivalence is automatically continuous). NOT `a₁ = R/6`. -/
noncomputable def negCLE (n : ℕ) : Point n ≃L[ℝ] Point n :=
  (LinearEquiv.neg ℝ : Point n ≃ₗ[ℝ] Point n).toContinuousLinearEquiv

/-- **`negCLE_coe`.**  The coercion of `negCLE` to a continuous linear MAP is exactly `−Id`. NOT
    `a₁ = R/6`. -/
theorem negCLE_coe :
    ((negCLE n : Point n ≃L[ℝ] Point n) : Point n →L[ℝ] Point n)
      = -(ContinuousLinearMap.id ℝ (Point n)) := by
  ext x
  simp [negCLE, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.neg_apply]

/-! ###############################################################################
    ### §2 — base-slot `ContDiffAt ℝ 2`, by restricting the banked joint fact.
    ############################################################################### -/

/-- **`uniformInverseChart_baseSlot_contDiffAt_generalK`.**  The base-slot restriction `p ↦
    uniformInverseChart g gi hC hK p q₀` (eval point `q₀` FIXED) is `ContDiffAt ℝ 2` at `q₀`, obtained
    by composing the banked joint `ContDiffAt ℝ 2` fact (`uniformInverseChart_jointContDiffAt_diag_
    generalK`, J4-884) with the smooth (`C^∞`) embedding `p ↦ (p, q₀)`. NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_contDiffAt_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ContDiffAt ℝ 2 (fun p => uniformInverseChart g gi hC hK p q₀) q₀ := by
  have hjoint := uniformInverseChart_jointContDiffAt_diag_generalK g gi hC hK q₀ hq₀
  have hmk : ContDiffAt ℝ 2 (fun p : Point n => ((p, q₀) : Point n × Point n)) q₀ :=
    ContDiffAt.prodMk contDiffAt_id contDiffAt_const
  have hcomp := ContDiffAt.comp (g := fun ξ : Point n × Point n =>
      uniformInverseChart g gi hC hK ξ.1 ξ.2)
    (f := fun p : Point n => ((p, q₀) : Point n × Point n)) q₀ hjoint hmk
  simpa using hcomp

/-! ###############################################################################
    ### §3 — upgrading the (F4)-style base-slot `HasFDerivAt (−Id)` to `HasStrictFDerivAt`.
    ############################################################################### -/

/-- **★★ `uniformInverseChart_baseSlot_hasStrictFDerivAt_generalK`.**  The base-slot map `p ↦
    uniformInverseChart g gi hC hK p q₀` has STRICT Fréchet derivative `−Id` at `q₀` — the upgrade of
    J4-1006's `HasFDerivAt` fact (`uniformInverseChart_baseSlot_fderiv_neg_id_generalK`) needed to feed
    Mathlib's Inverse Function Theorem.  Route: `ContDiffAt.hasStrictFDerivAt` (order `2 ≠ 0`) gives
    `HasStrictFDerivAt W (fderiv ℝ W q₀) q₀`; uniqueness of the Fréchet derivative
    (`HasFDerivAt.unique`) identifies `fderiv ℝ W q₀` with the banked `−Id`. NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_hasStrictFDerivAt_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    HasStrictFDerivAt (fun p => uniformInverseChart g gi hC hK p q₀)
      (-(ContinuousLinearMap.id ℝ (Point n))) q₀ := by
  have hcd := uniformInverseChart_baseSlot_contDiffAt_generalK g gi hC hK hq₀
  have hstrict := hcd.hasStrictFDerivAt (by norm_num)
  have hfd := uniformInverseChart_baseSlot_fderiv_neg_id_generalK g gi hC hK hq₀
  have hfderiv_eq : fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) q₀
      = -(ContinuousLinearMap.id ℝ (Point n)) := hfd.fderiv
  rwa [hfderiv_eq] at hstrict

/-- **`uniformInverseChart_baseSlot_hasStrictFDerivAt_CLE_generalK`.**  The same strict-derivative fact,
    re-typed with the derivative as the coercion of `negCLE` (a genuine `ContinuousLinearEquiv`),
    exactly the shape `HasStrictFDerivAt.toOpenPartialHomeomorph` needs. NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_hasStrictFDerivAt_CLE_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    HasStrictFDerivAt (fun p => uniformInverseChart g gi hC hK p q₀)
      ((negCLE n : Point n ≃L[ℝ] Point n) : Point n →L[ℝ] Point n) q₀ := by
  rw [negCLE_coe]
  exact uniformInverseChart_baseSlot_hasStrictFDerivAt_generalK g gi hC hK hq₀

/-! ###############################################################################
    ### §4 — THE PAYOFF: the genuine local open homeomorphism via Mathlib's IFT.
    ############################################################################### -/

/-- **★★★ `uniformInverseChart_baseSlot_localOpenHomeomorph_generalK`.**  THE PAYOFF: Mathlib's Inverse
    Function Theorem, invoked directly on the base-slot map `W p := uniformInverseChart g gi hC hK p q₀`
    at `q₀` (strict derivative `−Id`, a genuine `ContinuousLinearEquiv`), produces an OPEN set `S` with
    `q₀ ∈ S` on which `W` is INJECTIVE, together with an explicit LEFT INVERSE `V` (`∀ p ∈ S, V (W p) =
    p`) — discharging M2 (`InjOn`) and M3 (the left inverse) of `ChartGaussianChangeVar`'s missing-fact
    list, for the base-slot map, for the FIRST time in this campaign, directly from Mathlib's own IFT
    machinery (`HasStrictFDerivAt.toOpenPartialHomeomorph`) rather than a hand-built construction.
    M1 (`HasFDerivWithinAt` throughout `S`) and M4 (Jacobian lower bound throughout `S`) are NOT
    discharged here (see file docstring). NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_localOpenHomeomorph_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ S : Set (Point n), IsOpen S ∧ q₀ ∈ S ∧
      Set.InjOn (fun p => uniformInverseChart g gi hC hK p q₀) S ∧
      ∃ V : Point n → Point n, ∀ p ∈ S,
        V (uniformInverseChart g gi hC hK p q₀) = p := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p q₀ with hWdef
  have hstrict := uniformInverseChart_baseSlot_hasStrictFDerivAt_CLE_generalK g gi hC hK hq₀
  set e := hstrict.toOpenPartialHomeomorph W with hedef
  refine ⟨e.source, e.open_source, hstrict.mem_toOpenPartialHomeomorph_source, ?_, e.symm, ?_⟩
  · have hinj : Set.InjOn e e.source := e.injOn
    have hcoe : (e : Point n → Point n) = W := hstrict.toOpenPartialHomeomorph_coe
    rwa [hcoe] at hinj
  · intro p hp
    have hleft : e.symm (e p) = p := e.left_inv hp
    have hcoe : (e : Point n → Point n) = W := hstrict.toOpenPartialHomeomorph_coe
    rwa [hcoe] at hleft

end QIQTH.BaseSlotIFTLocalHomeomorph

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.BaseSlotIFTLocalHomeomorph
#print axioms negCLE_coe
#print axioms uniformInverseChart_baseSlot_contDiffAt_generalK
#print axioms uniformInverseChart_baseSlot_hasStrictFDerivAt_generalK
#print axioms uniformInverseChart_baseSlot_hasStrictFDerivAt_CLE_generalK
#print axioms uniformInverseChart_baseSlot_localOpenHomeomorph_generalK
end AxiomChecks
