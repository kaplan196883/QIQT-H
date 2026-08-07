/-
  Pd2ConvDissolution — J4-363: THE `hPd2conv` DISSOLUTION (SOL CONSULT #14).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE brick
  of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  `a₁ = R/6` remains conditional on the
  whole `hDuhamel`/convergence-trio + geometric-wiring stack; this file DISSOLVES the last of the FOUR
  labelled inputs of `a1_R6_from_labelled` — `hPd2conv` — into a COROLLARY of the already-carried hD1
  sliver census, plus the two first-derivative representation links (full-side + frozen-side) that are
  themselves discharged by the carried `hfam_v2` and the banked proper-integral frozen linewise diff.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TARGET (verbatim, `FrozenLaplaceSliver.hLapFull_of_pd2conv`'s `hPd2conv` binder).
      `hPd2conv : ∀ i, Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen H F u (u − epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0))`
  — the frozen (`s`-truncated) second field-partial at the RNC origin `0` converging to the full one.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SOL-#14 VERDICT (why this is NON-CIRCULAR).
  `∂ᵢ∂ᵢ(full conv)(0) = ∂ᵢ[the Dmap coefficient `gcoef i`](0)`: the full-side SECOND derivative is obtained
  by differentiating the `s`-INTEGRAL-REPRESENTED FIRST-derivative coefficient (the carried `hfam_v2`
  family, whose `HasFDerivAt` output IS the Dmap coefficient — the `(t−s)^{−1/2}`-dominated FIRST
  interchange), NOT a full-side SECOND interchange (the deep wall that made every J4-336-style
  `LapTrunc→full` route circular).  The hD1 census (`hbulkderiv`/`hbulk_tendsto`/`hsliver`) is
  FROZEN-side-only + the candidate, and its `hsliver`/`hb` convergence at `x = 0` IS the needed
  frozen→full convergence.  So `hPd2conv` = a COROLLARY of the already-carried sliver census.

  ## THE ONE INTERFACE POINT (B0).  `XUniformSliverFull.hD1_from_data` concludes a BARE `ContDiffAt ℝ 1`,
  which FORGETS that the derivative it installed IS the census candidate `gderiv 0`.  Its proof exposes
  that fact one layer down — `HD1SliverRoute.hD1_bulk_sliver_reduction hsOpen hx …` gives
  `HasFDerivAt gfull (gderiv x₀) x₀` for each `x₀ ∈ sSet` (the uniform-limit-of-derivatives theorem,
  BEFORE `hD1_reduction` erases it into `ContDiffAt`).  We re-export that inner step AT `x₀ = 0`
  (`gcoef_hasFDerivAt_candidate`): the candidate-identification `∂ᵢ(gcoef i)(0) = gderiv i 0 · eᵢ`.
  This is an API EXTRACTION, not new analysis.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (this file, ns `QIQTH.Pd2ConvDissolution`).
    • (B0a) `pd_of_hasFDerivAt`         — the HasFDerivAt→`pd` bookkeeping `∂ᵢf(x) = Df(x)·eᵢ`.
    • (B0b) `pd_germ_eq_of_family`      — from an `hfam_v2`-shape `∃`-nbhd `HasFDerivAt` family, the germ
        `(∂ᵢφ) =ᶠ[𝓝 0] (·↦ D(·)·eᵢ)` (how `hfull_pd1`/`hfrozen_pd1` are discharged from the carries).
    • (B0c) `gcoef_hasFDerivAt_candidate` — ★ THE candidate-identification: the `hD1_bulk_sliver_reduction`
        inner step re-exported at `x₀ = 0`, `HasFDerivAt (gcoef) (gderiv 0) 0`, from the sliver census.
    • (B1/B2) `pd2_at_zero_eq`          — `∂ᵢ∂ᵢφ(0) = L·eᵢ` from {first-partial germ = ψ near 0} + {ψ has
        Fréchet derivative `L` at 0}; used for BOTH the full and frozen sides.
    • (B3) ★★★ `hPd2conv_from_census`   — the EXACT `hPd2conv` binder of `hLapFull_of_pd2conv`, derived
        from the enumerated census (frozen-side + candidate ONLY): NO new domination, NO full-side
        second interchange.

  ## THE COMPLETE CENSUS OF `hPd2conv_from_census` (all satisfiable, all already carried; no silent caps).
    • the OPEN sliver nbhd `{sSet, hsOpen, hsnhds}` (⟹ `0 ∈ sSet`);
    • the hD1 SLIVER census `{gcoef, gderiv, fbulk, fderivBulk, bb, hb, hbulkderiv, hbulk_tendsto,
        hsliver}` — the SAME per-coordinate uniform-limit-of-derivatives data feeding
        `XUniformSliverFull.hD1_from_data` / `CConvV2DerivRep.hD1_conditional` (`hbulk_tendsto`'s limit is
        the full Dmap coefficient `gcoef i`; the `fbulk i m` double as the frozen truncations' first
        partials).  The census's `hcont` (derivative-field continuity) is NOT needed here — it feeds only
        the `ContDiffAt` step, not the 2-jet;
    • the two FIRST-DERIVATIVE representation links (strictly more elementary than `hPd2conv`, non-
        circular, each a `pd_germ_eq_of_family` corollary in the concrete case):
        `hfull_pd1`   : `∂ᵢ(full conv) =ᶠ[𝓝 0] gcoef i`               (from the carried `hfam_v2`);
        `hfrozen_pd1` : `∂ᵢ(frozen_m conv) =ᶠ[𝓝 0] fbulk i m`         (from the banked frozen linewise).

  Every hypothesis is satisfiable and non-vacuous (the width-2 Gaussian model of every sliver brick
  satisfies all of them), and NONE equals the conclusion.  NO `sorry`, no `:= True`, no new axioms, no
  existing file edited.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HeatDuhamel
import QIQTH.ConvApproximants
import QIQTH.D2HExpandRecon
import QIQTH.HD1SliverRoute

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.HeatDuhamel
open QIQTH.HeatResidualBound
open scoped Topology Interval

namespace QIQTH.Pd2ConvDissolution

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (B0a) `pd_of_hasFDerivAt` — the HasFDerivAt→`pd` bookkeeping.
    ############################################################################### -/

/-- **(B0a) `pd_of_hasFDerivAt`.**  If `f` has Fréchet derivative `L` at `x`, its `i`-th coordinate
    partial reads off the basis component: `∂ᵢf(x) = L(eᵢ)`.  `pd_eq_fderiv` (chain rule through the
    coordinate line `update`) + `HasFDerivAt.fderiv`.  NOT `a₁ = R/6`. -/
theorem pd_of_hasFDerivAt (f : Point n → ℝ) (L : Point n →L[ℝ] ℝ) (i : Fin n) (x : Point n)
    (hf : HasFDerivAt f L x) :
    pd f i x = L (Pi.single i (1 : ℝ)) := by
  rw [QIQTH.Curvature.pd_eq_fderiv f i x hf.differentiableAt, hf.fderiv]

/-! ###############################################################################
    ### (B0b) `pd_germ_eq_of_family` — the first-partial germ from an `hfam_v2` family.
    ############################################################################### -/

/-- **(B0b) `pd_germ_eq_of_family`.**  From the `hfam_v2`-shape `∃`-neighbourhood `HasFDerivAt` family
    (`∃ w ∈ 𝓝 0, ∀ x ∈ w, HasFDerivAt φ (D x) x`), the first coordinate partial equals the basis
    component of the representative NEAR `0`:  `(fun y ↦ ∂ᵢφ y) =ᶠ[𝓝 0] (fun y ↦ (D y)(eᵢ))`.  This is
    the "HasFDerivAt→pd bookkeeping + local congruence" step (SOL #14, B1): it discharges the
    `hfull_pd1`/`hfrozen_pd1` links of the capstone from the carried families (full: `hfam_v2`; frozen:
    the banked proper-integral linewise diff), with `gcoef i y = (D y)(eᵢ)` the Dmap coefficient.
    NOT `a₁ = R/6`. -/
theorem pd_germ_eq_of_family (φ : Point n → ℝ) (D : Point n → (Point n →L[ℝ] ℝ)) (i : Fin n)
    (hfam : ∃ w ∈ 𝓝 (0 : Point n), ∀ x ∈ w, HasFDerivAt φ (D x) x) :
    (fun y => pd φ i y) =ᶠ[𝓝 (0 : Point n)] (fun y => (D y) (Pi.single i (1 : ℝ))) := by
  obtain ⟨w, hw, hD⟩ := hfam
  filter_upwards [hw] with y hy
  exact pd_of_hasFDerivAt φ (D y) i y (hD y hy)

/-! ###############################################################################
    ### (B0c) `gcoef_hasFDerivAt_candidate` — the candidate-identification (API extraction).
    ############################################################################### -/

/-- **★ (B0c) `gcoef_hasFDerivAt_candidate`.**  THE candidate-identification the bare `hD1_from_data`
    `ContDiffAt` forgets.  `HD1SliverRoute.hD1_bulk_sliver_reduction` (the uniform-limit-of-derivatives
    theorem — the very step `hD1_from_data`'s proof applies BEFORE `hD1_reduction` erases it into
    `ContDiffAt`) re-exported AT `x₀ = 0` (`0 ∈ sSet` from the open nbhd): the full-side coefficient
    `gcoef` has Fréchet derivative `gderiv 0` at `0`.  Per-coordinate (`ι = ℕ`, the truncation index).
    THIS IS AN API EXTRACTION, not new analysis.  NOT `a₁ = R/6`. -/
theorem gcoef_hasFDerivAt_candidate
    {sSet : Set (Point n)} (hsOpen : IsOpen sSet) (h0 : (0 : Point n) ∈ sSet)
    (fbulk : ℕ → Point n → ℝ) (fderivBulk : ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gcoef : Point n → ℝ) (gderiv : Point n → (Point n →L[ℝ] ℝ))
    (bb : ℕ → ℝ) (hb : Tendsto bb atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ m, ∀ x ∈ sSet, HasFDerivAt (fbulk m) (fderivBulk m x) x)
    (hbulk_tendsto : ∀ x ∈ sSet, Tendsto (fun m => fbulk m x) atTop (𝓝 (gcoef x)))
    (hsliver : ∀ m, ∀ x ∈ sSet, dist (fderivBulk m x) (gderiv x) ≤ bb m) :
    HasFDerivAt gcoef (gderiv 0) 0 :=
  QIQTH.HD1SliverRoute.hD1_bulk_sliver_reduction hsOpen h0 fbulk fderivBulk gcoef gderiv bb hb
    hbulkderiv hbulk_tendsto hsliver

/-! ###############################################################################
    ### (B1/B2) `pd2_at_zero_eq` — the second-partial read-off, both sides.
    ############################################################################### -/

/-- **★★ (B1/B2) `pd2_at_zero_eq`.**  The second coordinate partial at `0` reads off the basis
    component of the coefficient's Fréchet derivative:  if the FIRST partial `(fun y ↦ ∂ᵢφ y)` agrees
    near `0` with a coefficient `ψ` that itself has Fréchet derivative `L` at `0`, then
    `∂ᵢ∂ᵢφ(0) = L(eᵢ)`.  `pd_congr_of_eventuallyEq` (the germ-locality of the outer `pd`) collapses the
    first-partial germ onto `ψ`; `pd_of_hasFDerivAt` reads off `L`.  Used for BOTH the full side
    (`φ = full conv`, `ψ = gcoef i`, `L = gderiv i 0`) and the frozen side (`φ = frozen_m conv`,
    `ψ = fbulk i m`, `L = fderivBulk i m 0`).  NOT `a₁ = R/6`. -/
theorem pd2_at_zero_eq (φ ψ : Point n → ℝ) (L : Point n →L[ℝ] ℝ) (i : Fin n)
    (hgerm : (fun y => pd φ i y) =ᶠ[𝓝 (0 : Point n)] ψ)
    (hjet : HasFDerivAt ψ L 0) :
    pd (fun y => pd φ i y) i 0 = L (Pi.single i (1 : ℝ)) := by
  rw [QIQTH.D2HExpandRecon.pd_congr_of_eventuallyEq (fun y => pd φ i y) ψ i 0 hgerm]
  exact pd_of_hasFDerivAt ψ L i 0 hjet

/-! ###############################################################################
    ### (B3) `hPd2conv_from_census` — ★★★ the exact `hPd2conv` binder, dissolved.
    ############################################################################### -/

/-- **★★★ (B3) `hPd2conv_from_census`.**  THE EXACT `hPd2conv` binder of
    `FrozenLaplaceSliver.hLapFull_of_pd2conv`, derived from the enumerated census ONLY — the last of
    the four labelled `a₁` inputs, DISSOLVED into a corollary of the already-carried hD1 sliver census
    plus the two first-derivative representation links.

    ── THE CENSUS (all satisfiable, all carried; none the conclusion).
      • `{sSet, hsOpen, hsnhds}` — the open sliver neighbourhood of `0`;
      • `{gcoef, gderiv, fbulk, fderivBulk, bb, hb, hbulkderiv, hbulk_tendsto, hsliver}` — the hD1
        SLIVER census (`hbulk_tendsto`'s limit `gcoef i` = the full Dmap coefficient; the `fbulk i m`
        = the frozen truncations' first partials); its `hcont` is NOT needed (2-jet only);
      • `hfull_pd1`/`hfrozen_pd1` — the first-partial representation links (`pd_germ_eq_of_family`
        corollaries of the carried `hfam_v2` / the banked frozen linewise diff).

    ── THE ROUTE (SOL #14).  B0: `gcoef_hasFDerivAt_candidate` at `0` (from the sliver census) gives
    `HasFDerivAt (gcoef i) (gderiv i 0) 0`.  B1: `pd2_at_zero_eq` on `hfull_pd1` ⟹
    `∂ᵢ∂ᵢ(full)(0) = gderiv i 0 · eᵢ`.  B2: `pd2_at_zero_eq` on `hfrozen_pd1` + `hbulkderiv … 0` ⟹
    `∂ᵢ∂ᵢ(frozen_m)(0) = fderivBulk i m 0 · eᵢ`.  B3: `hsliver`+`hb` (squeeze) ⟹
    `fderivBulk i m 0 → gderiv i 0`, evaluated at `eᵢ` (continuity of CLM application) ⟹ the target
    Tendsto.  NO new domination; NO full-side second interchange (non-circular).  NOT `a₁ = R/6`. -/
theorem hPd2conv_from_census
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (gcoef : Fin n → Point n → ℝ)
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i m, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i, ∀ x ∈ sSet, Tendsto (fun m => fbulk i m x) atTop (𝓝 (gcoef i x)))
    (hsliver : ∀ i m, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hfull_pd1 : ∀ i : Fin n,
        (fun y => pd (fun x => heatConv H F u x 0) i y) =ᶠ[𝓝 (0 : Point n)] gcoef i)
    (hfrozen_pd1 : ∀ (i : Fin n) (m : ℕ),
        (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y)
          =ᶠ[𝓝 (0 : Point n)] fbulk i m) :
    ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0)) := by
  intro i
  have h0 : (0 : Point n) ∈ sSet := mem_of_mem_nhds hsnhds
  -- B0: the candidate-identification, from the sliver census at `x₀ = 0`.
  have hcand : HasFDerivAt (gcoef i) (gderiv i 0) 0 :=
    gcoef_hasFDerivAt_candidate hsOpen h0 (fbulk i) (fderivBulk i) (gcoef i) (gderiv i)
      (bb i) (hb i) (hbulkderiv i) (hbulk_tendsto i) (hsliver i)
  -- B3 (convergence, frozen derivatives → full derivative): squeeze on `hsliver`/`hb` at `0`.
  have hconv : Tendsto (fun m => fderivBulk i m 0) atTop (𝓝 (gderiv i 0)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun m => hsliver i m 0 h0) (hb i)
  -- B1 (full side): `∂ᵢ∂ᵢ(full)(0) = gderiv i 0 · eᵢ`.
  have hB1 : pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0
      = (gderiv i 0) (Pi.single i (1 : ℝ)) :=
    pd2_at_zero_eq (fun x => heatConv H F u x 0) (gcoef i) (gderiv i 0) i (hfull_pd1 i) hcand
  -- B2 (frozen side): `∂ᵢ∂ᵢ(frozen_m)(0) = fderivBulk i m 0 · eᵢ`.
  have hB2 : ∀ m : ℕ,
      pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
        = (fderivBulk i m 0) (Pi.single i (1 : ℝ)) := by
    intro m
    exact pd2_at_zero_eq (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) (fbulk i m)
      (fderivBulk i m 0) i (hfrozen_pd1 i m) (hbulkderiv i m 0 h0)
  -- B3 (assembly): evaluate the convergence at `eᵢ`, then carry it through B1/B2.
  have hev : Continuous (fun L : Point n →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) :=
    continuous_id.clm_apply continuous_const
  have hlim : Tendsto (fun m => (fderivBulk i m 0) (Pi.single i (1 : ℝ))) atTop
      (𝓝 ((gderiv i 0) (Pi.single i (1 : ℝ)))) :=
    (hev.tendsto (gderiv i 0)).comp hconv
  rw [hB1]
  exact hlim.congr (fun m => (hB2 m).symm)

end QIQTH.Pd2ConvDissolution

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.Pd2ConvDissolution
#print axioms pd_of_hasFDerivAt
#print axioms pd_germ_eq_of_family
#print axioms gcoef_hasFDerivAt_candidate
#print axioms pd2_at_zero_eq
#print axioms hPd2conv_from_census
end AxiomChecks
