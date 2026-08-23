/-
  HBFpeakInteriorNullFrontierBypass — J4-1089: the `hBFpeak` census carry of `hzmass_capped_window_closed`
  / `MixedEnvelopeAssembly` REDUCED off the PROVEN-DEAD chart-C²+in-gate boundary cover `W` (J4-892/1088),
  via the SAME AEStronglyMeasurable/null-frontier bypass technique J4-904→907 used for `hbint`, applied
  here to the `hBFpeak` peak-DOMINATION carry instead of to a continuity carry.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}; hCConv is NOT closed here.  No `sorry`,
  no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT (J4-1088's decisive negative + the un-pursued angle it flagged).

  J4-1088 proved that the literal chart-`C²`+in-gate open cover `W` that `HBFpeakReducedToChartC2Cover`
  (J4-1087) uses to bound the field-Hessian peak `BF s z := ⨆ x', ‖fderiv … x'‖` by a `z`-UNIFORM
  `sSup` over the COMPACT set `(K ×ˢ concreteKx) ∩ jointCore` is PROVEN IMPOSSIBLE at any boundary point
  of a genuine compact `K` (`BTubeCompactnessAssembly`, J4-892) — `IsCompact.bddAbove_image` there needs
  continuity reaching all the way to `∂K`, which the open-cover base-projection argument forbids.

  `hbint` dodged the analogous continuity-at-`∂K` wall (J4-904→907) by observing its consumer only needs
  `AEStronglyMeasurable`/`Integrable`, which TOLERATES the null discontinuity locus `∂K`. This file checks
  and confirms — first via a direct read of the ONLY consumer of `hBFpeak`
  (`HZMassLeviBaseEnvelope.hzmass_of_peak_BF_gaussian2s_BL`), then via `gpt-5.6-sol`(high) consult — that
  the SAME move is available for `hBFpeak`: the consumer builds a pointwise domination `henv : ∀ z, …`
  purely to feed Mathlib's `integral_mono`, which has an a.e. sibling `integral_mono_ae` requiring only
  `f ≤ᵐ[μ] g`. So `hBFpeak`'s literal `∀ z : Point n` is NOT actually needed by its consumer — `∀ᵐ z`
  suffices, mechanically, with no other change to the algebra.

  ## WHAT THIS BUYS (Sol-confirmed: a genuine, if narrow, strict weakening — NOT a re-labelling of `hbnd`).

  Given a peak bound ONLY on the OPEN `interior K` (`hBFint`, avoiding the dead boundary cover entirely)
  plus the ALREADY-BANKED off-`K` vanishing (`hBFoff`) plus the null-frontier fact (already discharged
  for the live ball, `HbintMeasurabilityNullFrontier.volume_frontier_closedBall_eq_zero`), the a.e.-`z`
  gluing lemma `ae_le_of_le_on_interior_of_eq_zero_off_of_null_frontier` produces EXACTLY the relaxed
  `hBFpeak` shape the AE consumer needs — WITHOUT ever invoking the dead cover `W`.

  This is a strict weakening of the OLD `hBFpeak`, not a solve: a function bounded on `interior K`,
  zero off `K`, but with ARBITRARY / possibly-unbounded values exactly ON the null set `∂K` satisfies
  the NEW hypothesis but not the old one — so this genuinely removes an unnecessary obligation, per
  `gpt-5.6-sol`'s worked counterexample-style argument (the mass integral cannot see the null boundary).

  ## THE HONEST RESIDUE (Sol-confirmed, NOT closed here — do not overclaim).

  `hBFint : ∀ z ∈ interior K, BF s z ≤ Ppk s` (z-UNIFORM over the OPEN interior, `Ppk` an `s`-only
  function) remains a NAMED, UNDISCHARGED carry — structurally analogous to (but NOT literally identical
  to; it bounds `BF` alone, not the product `BL·BF`) `hbint`'s own still-open `hbnd` carry. Sol's explicit
  counter-check: continuity/local-boundedness on an open set does NOT imply a single uniform bound (the
  standard counterexample `F(z) = 1/(R − ‖z−c‖)` on an open ball is continuous, locally bounded at every
  interior point, yet globally UNBOUNDED approaching the boundary — and this failure mode is NOT excluded
  by nullity of `∂K` alone, since positive-measure shells arbitrarily close to `∂K` remain in `interior K`).
  So `IsCompact.bddAbove_image`-style closure arguments do NOT transfer to `interior K` for free; no
  Mathlib route was found (or is expected) to discharge `hBFint` from continuity alone. `hBFint` is left
  as an explicit, honestly-open hypothesis — NOT force-derived, NOT `sorry`'d.

  ## WHAT LANDS (ns `QIQTH.HBFpeakInteriorNullFrontierBypass`).
    • `ae_le_of_le_on_interior_of_eq_zero_off_of_null_frontier` — ★★ the GENERAL gluing lemma: interior
      bound + off-K vanishing + null frontier ⟹ a.e. bound (mirrors `hbint`'s
      `aestronglyMeasurable_of_interiorContinuous_nullFrontier`, but for a DOMINATION carry, not a
      continuity/measurability carry).
    • `hBFpeak_ae_of_interior_and_offK` — ★★ the a.e.-`s` literal `hBFpeak`-shape wrapper.
    • `hzmass_of_peak_BF_gaussian2s_BL_ae` — ★★★ the AE-`z` sibling of
      `HZMassLeviBaseEnvelope.hzmass_of_peak_BF_gaussian2s_BL`, via `integral_mono_ae` in place of
      `integral_mono` — CONFIRMS the consumer genuinely tolerates a.e.-`z` domination.
    • `hzmass_capped_window_closed_ae` — ★★★ the AE-`z` sibling of
      `HZMassCappedWindowClosed.hzmass_capped_window_closed`.
    • `hzmass_via_interior_peak_null_frontier` — ★★★ THE COMPOSITE: `hzmass`'s FULL closure (on the
      capped window) from `{hBFint (NAMED, open), hBFoff (banked shape), null-frontier (banked for the
      live ball), the elementary window/Levi carries}` — with NO reference to the dead boundary cover `W`
      anywhere in the hypothesis list.
    • Non-vacuity witnesses (empty base `K := ∅`; live ball `K := closedBall 0 r`).
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HZMassCappedWindowClosed
import QIQTH.HbintMeasurabilityNullFrontier

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.FlatHeatEquation QIQTH.ResidueBound
open QIQTH.RadialDistance
open QIQTH.HZMassCappedWindowClosed QIQTH.HZMassLeviBaseEnvelope
open QIQTH.HbintMeasurabilityNullFrontier
open scoped Topology BigOperators

namespace QIQTH.HBFpeakInteriorNullFrontierBypass

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §0 — the general gluing lemma: interior bound + off-K vanishing + null frontier ⟹ a.e. bound.
    ############################################################################### -/

/-- **★★ §0 — `ae_le_of_le_on_interior_of_eq_zero_off_of_null_frontier`.** For CLOSED `K` with
    `volume (frontier K) = 0`: a function bounded by `P` on the OPEN `interior K`, vanishing off `K`, and
    `P ≥ 0`, is bounded by `P` ALMOST EVERYWHERE (the only points that could fail are exactly `frontier
    K`, which is null). Mirrors `HbintMeasurabilityNullFrontier.aestronglyMeasurable_of_
    interiorContinuous_nullFrontier`'s co-null decomposition `interior K ∪ Kᶜ`, but for a DOMINATION
    (not continuity/measurability) carry — no continuity hypothesis anywhere, so no dead cover is ever
    needed. NOT `a₁ = R/6`. -/
theorem ae_le_of_le_on_interior_of_eq_zero_off_of_null_frontier
    {K : Set (Point n)} (hKcl : IsClosed K) (hnull : volume (frontier K) = 0)
    (F : Point n → ℝ) (P : ℝ) (hP : 0 ≤ P)
    (hint : ∀ z ∈ interior K, F z ≤ P)
    (hoff : ∀ z, z ∉ K → F z = 0) :
    ∀ᵐ z ∂volume, F z ≤ P := by
  have hae : ∀ᵐ z ∂volume, z ∉ frontier K := by
    rw [ae_iff]
    simpa using hnull
  filter_upwards [hae] with z hz
  by_cases hzK : z ∈ K
  · have hfe : frontier K = K \ interior K := hKcl.frontier_eq
    have hzi : z ∈ interior K := by
      by_contra hci
      exact hz (hfe ▸ ⟨hzK, hci⟩)
    exact hint z hzi
  · rw [hoff z hzK]
    exact hP

/-! ###############################################################################
    ### §1 — the a.e.-`s` literal `hBFpeak` shape, from an interior-only peak bound.
    ############################################################################### -/

/-- **★★ §1 — `hBFpeak_ae_of_interior_and_offK`.** The a.e.-`s` `∀ᵐ z` version of the `hBFpeak` census
    carry, built from a peak bound restricted to the OPEN `interior K` (`hBFint`, avoiding the dead
    boundary cover entirely) plus off-`K` vanishing (`hBFoff`) plus the null-frontier fact. `hBFint`
    remains an honest, NAMED, undischarged hypothesis — this brick only removes the (unnecessary, per
    the consumer trace) dependence on boundary values. NOT `a₁ = R/6`. -/
theorem hBFpeak_ae_of_interior_and_offK
    {K : Set (Point n)} (hKcl : IsClosed K) (hnull : volume (frontier K) = 0)
    (BF : ℝ → Point n → ℝ) (Ppk : ℝ → ℝ) (t : ℝ) (m : ℕ)
    (hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 ≤ Ppk s)
    (hBFint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z ∈ interior K, BF s z ≤ Ppk s)
    (hBFoff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ z, z ∉ K → BF s z = 0) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, BF s z ≤ Ppk s := by
  filter_upwards [hPpknn, hBFint, hBFoff] with s hpn hbi hbo hsU
  exact ae_le_of_le_on_interior_of_eq_zero_off_of_null_frontier hKcl hnull (BF s) (Ppk s)
    (hpn hsU) (hbi hsU) (hbo hsU)

/-! ###############################################################################
    ### §2 — the AE-`z` sibling of `hzmass_of_peak_BF_gaussian2s_BL`, via `integral_mono_ae`.
    ############################################################################### -/

/-- **★★★ §2 — `hzmass_of_peak_BF_gaussian2s_BL_ae`.** The AE-`z` sibling of
    `HZMassLeviBaseEnvelope.hzmass_of_peak_BF_gaussian2s_BL` — IDENTICAL statement and proof shape,
    except `hBFpeak` is `∀ᵐ z` (not `∀ z`) and the final domination step uses `integral_mono_ae`
    (not `integral_mono`). Directly CONFIRMS the consumer tolerates a.e.-`z` domination: no other
    hypothesis or algebraic step changes. NOT `a₁ = R/6`. -/
theorem hzmass_of_peak_BF_gaussian2s_BL_ae
    (t : ℝ) (m : ℕ) (C : ℝ) (BL BF : ℝ → Point n → ℝ) (Ppk CB : ℝ → ℝ)
    (hCnn : 0 ≤ C)
    (hspos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < s)
    (hpos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < t - s)
    (hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z * BF s z) volume)
    (hBFpeakAE : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, BF s z ≤ Ppk s)
    (hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, 0 ≤ BL s z)
    (hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BL s z ≤ CB s * gaussDdim (2 * s) z)
    (hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        0 ≤ Ppk s)
    (hpow : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Ppk s * CB s ≤ C * (t - s)⁻¹) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ z, BL s z * BF s z) ≤ C * (t - s)⁻¹ := by
  filter_upwards [hspos, hpos, hint, hBFpeakAE, hBLnn, hBLgauss, hPpknn, hpow]
    with s hsp hpp hii hpkAE hbn hbg hpn hpw hs
  have hs2 : 0 < 2 * s := by have := hsp hs; linarith
  have hii := hii hs
  have hpkz := hpkAE hs
  -- pointwise-a.e. product envelope `BL·BF ≤ᵐ (Ppk·CB)·gaussDdim (2s)`.
  have henv : (fun z => BL s z * BF s z) ≤ᵐ[volume]
      (fun z => (Ppk s * CB s) * gaussDdim (2 * s) z) := by
    filter_upwards [hpkz] with z hpks
    have hbns := hbn hs z
    have hbgs := hbg hs z
    have hpns := hpn hs
    have step1 : BL s z * BF s z ≤ BL s z * Ppk s :=
      mul_le_mul_of_nonneg_left hpks hbns
    have step2 : BL s z * Ppk s ≤ (CB s * gaussDdim (2 * s) z) * Ppk s :=
      mul_le_mul_of_nonneg_right hbgs hpns
    have step3 : (CB s * gaussDdim (2 * s) z) * Ppk s
        = (Ppk s * CB s) * gaussDdim (2 * s) z := by ring
    calc BL s z * BF s z
        ≤ BL s z * Ppk s := step1
      _ ≤ (CB s * gaussDdim (2 * s) z) * Ppk s := step2
      _ = (Ppk s * CB s) * gaussDdim (2 * s) z := step3
  -- integrate the envelope; the Gaussian has total mass `1` at width `2s`.
  have hgint : Integrable (fun z : Point n => gaussDdim (2 * s) z) volume :=
    gaussDdim_integrable' (2 * s) hs2
  have henvint : Integrable (fun z : Point n => (Ppk s * CB s) * gaussDdim (2 * s) z) volume :=
    hgint.const_mul (Ppk s * CB s)
  have hmono : (∫ z, BL s z * BF s z)
      ≤ ∫ z : Point n, (Ppk s * CB s) * gaussDdim (2 * s) z :=
    integral_mono_ae hii henvint henv
  have hval : (∫ z : Point n, (Ppk s * CB s) * gaussDdim (2 * s) z) = Ppk s * CB s := by
    rw [integral_const_mul, gaussDdim_mass_one (2 * s) hs2, mul_one]
  rw [hval] at hmono
  exact le_trans hmono (hpw hs)

/-! ###############################################################################
    ### §3 — the AE-`z` sibling of `hzmass_capped_window_closed`.
    ############################################################################### -/

/-- **★★★ §3 — `hzmass_capped_window_closed_ae`.** The AE-`z` sibling of
    `HZMassCappedWindowClosed.hzmass_capped_window_closed`, feeding `hpow_capped` (unchanged) into
    `hzmass_of_peak_BF_gaussian2s_BL_ae` in place of the literal-`∀z` original. NOT `a₁ = R/6`. -/
theorem hzmass_capped_window_closed_ae
    (t : ℝ) (m : ℕ) (M : ℝ) (BL BF : ℝ → Point n → ℝ) (Ppk CB : ℝ → ℝ)
    (hMnn : 0 ≤ M) (hepspos : 0 < t - epsSeq m)
    (hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z * BF s z) volume)
    (hBFpeakAE : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, BF s z ≤ Ppk s)
    (hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, 0 ≤ BL s z)
    (hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BL s z ≤ CB s * gaussDdim (2 * s) z)
    (hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        0 ≤ Ppk s)
    (hPCbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → Ppk s * CB s ≤ M) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ z, BL s z * BF s z) ≤ (M * t) * (t - s)⁻¹ := by
  have htpos : 0 < t := QIQTH.HZMassCappedWindowClosed.t_pos_of_epspos hepspos
  have hspos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < s := by
    refine ae_of_all _ (fun s hs => (QIQTH.HZMassCappedWindowClosed.window_gap hepspos hs).1)
  have hpos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < t - s := by
    refine ae_of_all _ (fun s hs => ?_)
    exact lt_of_lt_of_le (epsSeq_pos m)
      (QIQTH.HZMassCappedWindowClosed.window_gap hepspos hs).2
  have hpow := QIQTH.HZMassCappedWindowClosed.hpow_capped t m M Ppk CB hMnn hepspos hPCbound
  exact hzmass_of_peak_BF_gaussian2s_BL_ae (n := n) t m (M * t) BL BF Ppk CB
    (mul_nonneg hMnn (le_of_lt htpos)) hspos hpos hint hBFpeakAE hBLnn hBLgauss hPpknn hpow

/-! ###############################################################################
    ### §4 — THE COMPOSITE: `hzmass` closed WITHOUT the dead boundary cover `W`.
    ############################################################################### -/

/-- **★★★ §4 — `hzmass_via_interior_peak_null_frontier`.** THE COMPOSITE result: the FULL `hzmass`
    field of `MixedDirectionsFieldHessianEnvelope`, on the capped window, from a carry list with NO
    reference anywhere to the dead chart-C²+in-gate boundary cover `W` (J4-892/1088). Replaces the OLD
    `hBFpeak : ∀ z` carry by the strictly-weaker `hBFint : ∀ z ∈ interior K` (still an honest, NAMED,
    undischarged carry — the residue Sol confirmed is NOT reachable from continuity/local-boundedness
    alone) plus the banked off-`K` vanishing shape `hBFoff` plus the null-frontier fact. NOT `a₁ = R/6`. -/
theorem hzmass_via_interior_peak_null_frontier
    {K : Set (Point n)} (hKcl : IsClosed K) (hnull : volume (frontier K) = 0)
    (t : ℝ) (m : ℕ) (M : ℝ) (BL BF : ℝ → Point n → ℝ) (Ppk CB : ℝ → ℝ)
    (hMnn : 0 ≤ M) (hepspos : 0 < t - epsSeq m)
    (hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z * BF s z) volume)
    (hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 ≤ Ppk s)
    (hBFint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z ∈ interior K, BF s z ≤ Ppk s)
    (hBFoff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ z, z ∉ K → BF s z = 0)
    (hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, 0 ≤ BL s z)
    (hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BL s z ≤ CB s * gaussDdim (2 * s) z)
    (hPCbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → Ppk s * CB s ≤ M) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ z, BL s z * BF s z) ≤ (M * t) * (t - s)⁻¹ := by
  have hBFpeakAE := hBFpeak_ae_of_interior_and_offK hKcl hnull BF Ppk t m hPpknn hBFint hBFoff
  exact hzmass_capped_window_closed_ae t m M BL BF Ppk CB
    hMnn hepspos hint hBFpeakAE hBLnn hBLgauss hPpknn hPCbound

/-! ###############################################################################
    ### §5 — NON-VACUITY.
    ############################################################################### -/

/-- **Non-vacuity at the DEGENERATE empty base `K := ∅`.** Every carry holds trivially with zero
    envelopes; `interior ∅ = ∅` so `hBFint` is vacuously true, `hBFoff` holds since every `z ∉ ∅`.
    No J4-548/847-style unsatisfiable antecedent. -/
theorem hzmass_via_interior_peak_null_frontier_nonvacuous_empty {n : ℕ}
    (t : ℝ) (m : ℕ) (hepspos : 0 < t - epsSeq m) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ _z : Point n, (0 : ℝ) * 0) ≤ ((0 : ℝ) * t) * (t - s)⁻¹ := by
  have hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z : Point n =>
        (fun _ _ => (0 : ℝ)) s z * (fun _ _ => (0 : ℝ)) s z) volume := by
    refine ae_of_all _ (fun s _ => ?_)
    simp only [mul_zero]
    exact integrable_zero _ _ _
  have hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → (0:ℝ) ≤ (fun _ => (0 : ℝ)) s :=
    ae_of_all _ (fun s _ => le_refl 0)
  have hBFint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z ∈ interior (∅ : Set (Point n)), (fun _ _ => (0 : ℝ)) s z ≤ (fun _ => (0 : ℝ)) s :=
    ae_of_all _ (fun s _ z hz => (Set.notMem_empty z (interior_subset hz)).elim)
  have hBFoff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z, z ∉ (∅ : Set (Point n)) → (fun _ _ => (0 : ℝ)) s z = 0 :=
    ae_of_all _ (fun s _ z _ => rfl)
  have hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, 0 ≤ (fun _ _ => (0 : ℝ)) s z :=
    ae_of_all _ (fun s _ z => le_refl 0)
  have hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, (fun _ _ => (0 : ℝ)) s z
        ≤ (fun _ => (0 : ℝ)) s * gaussDdim (2 * s) z := by
    refine ae_of_all _ (fun s _ z => ?_)
    simp
  have hPCbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      (fun _ => (0 : ℝ)) s * (fun _ => (0 : ℝ)) s ≤ (0 : ℝ) :=
    ae_of_all _ (fun s _ => by simp)
  exact hzmass_via_interior_peak_null_frontier (n := n) (K := (∅ : Set (Point n)))
    isClosed_empty (by simp) t m 0 (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    (le_refl 0) hepspos hint hPpknn hBFint hBFoff hBLnn hBLgauss hPCbound

/-- **Non-vacuity at the LIVE ball `K := closedBall 0 r` (`n ≥ 1`, `r ≠ 0`).** The null-frontier fact is
    the SAME banked `volume_frontier_closedBall_eq_zero` (J4-904) `hbint` already relies on; every other
    carry holds with zero envelopes. This is the genuine live-geometry instantiation, not just the
    degenerate empty-base sanity check. -/
theorem hzmass_via_interior_peak_null_frontier_nonvacuous_ball
    (hn : 0 < n) (r : ℝ) (hr : r ≠ 0) (t : ℝ) (m : ℕ) (hepspos : 0 < t - epsSeq m) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ _z : Point n, (0 : ℝ) * 0) ≤ ((0 : ℝ) * t) * (t - s)⁻¹ := by
  have hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z : Point n =>
        (fun _ _ => (0 : ℝ)) s z * (fun _ _ => (0 : ℝ)) s z) volume := by
    refine ae_of_all _ (fun s _ => ?_)
    simp only [mul_zero]
    exact integrable_zero _ _ _
  have hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → (0:ℝ) ≤ (fun _ => (0 : ℝ)) s :=
    ae_of_all _ (fun s _ => le_refl 0)
  have hBFint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z ∈ interior (Metric.closedBall (0 : Point n) r),
        (fun _ _ => (0 : ℝ)) s z ≤ (fun _ => (0 : ℝ)) s :=
    ae_of_all _ (fun s _ z _ => le_refl 0)
  have hBFoff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z, z ∉ Metric.closedBall (0 : Point n) r → (fun _ _ => (0 : ℝ)) s z = 0 :=
    ae_of_all _ (fun s _ z _ => rfl)
  have hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, 0 ≤ (fun _ _ => (0 : ℝ)) s z :=
    ae_of_all _ (fun s _ z => le_refl 0)
  have hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, (fun _ _ => (0 : ℝ)) s z
        ≤ (fun _ => (0 : ℝ)) s * gaussDdim (2 * s) z := by
    refine ae_of_all _ (fun s _ z => ?_)
    simp
  have hPCbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      (fun _ => (0 : ℝ)) s * (fun _ => (0 : ℝ)) s ≤ (0 : ℝ) :=
    ae_of_all _ (fun s _ => by simp)
  exact hzmass_via_interior_peak_null_frontier (n := n) (K := Metric.closedBall (0 : Point n) r)
    (Metric.isClosed_closedBall) (volume_frontier_closedBall_eq_zero hn r hr)
    t m 0 (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    (le_refl 0) hepspos hint hPpknn hBFint hBFoff hBLnn hBLgauss hPCbound

end QIQTH.HBFpeakInteriorNullFrontierBypass

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HBFpeakInteriorNullFrontierBypass
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms ae_le_of_le_on_interior_of_eq_zero_off_of_null_frontier
#print axioms hBFpeak_ae_of_interior_and_offK
#print axioms hzmass_of_peak_BF_gaussian2s_BL_ae
#print axioms hzmass_capped_window_closed_ae
#print axioms hzmass_via_interior_peak_null_frontier
#print axioms hzmass_via_interior_peak_null_frontier_nonvacuous_empty
#print axioms hzmass_via_interior_peak_null_frontier_nonvacuous_ball
end AxiomChecks
