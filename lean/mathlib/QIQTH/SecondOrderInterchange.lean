/-
  SecondOrderInterchange — J4-141: THE `hInterchange` DISCHARGE — second-order coordinate
  differentiation under the double space-time integral at the finite gap, the riskiest INTERCHANGE
  carry of the freshly-banked conditional `hDuhamel_semifinal` (J4-140, `SliverSumPlumbing`).

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and proves NOTHING about
  `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET (the `hInterchange` hypothesis carried by `LapTruncAssembly` / `SliverSumPlumbing`).
      `∀ (m : ℕ) (i : Fin n),
         pd (fun y => pd (fun x => heatConvFrozen H F u (u − epsSeq m) x 0) i y) i 0
           = ∫ s in (0)..(u − epsSeq m), ∫ z, pdpdH i (u − s) z · F s z 0`.
  The map differentiated is the FROZEN convolution `x ↦ ∫₀^b ∫_z H (u−s) x z · F s z 0`
  (`heatConvFrozen H F u b x 0`, `b := u − epsSeq m`); `pdpdH i` is the second field-`x`-partial at
  the center `x = 0`.  The finite gap `u − s ≥ epsSeq m > 0` for `s ∈ [0, b]` keeps every inner time
  strictly positive, so `H (u−s) · z` is REGULAR and the parametric derivative-under-the-integral
  machinery fires with Gaussian-type dominations (all satisfiable via C4b + the gap).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (this file, ns `QIQTH.HeatResidualBound`).

    (E)  `innerZ_line_hasDerivAt` — THE INNER (`∫z`) NESTING.  For fixed time `s` and base
         line-point `p`, differentiating `w ↦ ∫ z, K (u−s) (update y i w) z · F s z 0` in the
         coordinate line passes under the Lebesgue `z`-integral:
           `HasDerivAt (fun w => ∫ z, K (u−s) (update y i w) z · F s z 0)
                       (∫ z, dK (u−s) (update y i p) z · F s z 0) p`.
         Direct `.2` of `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (mirrors
         `HeatConvRegularity.heatConvInner_hasDerivAt`, but the differentiation variable enters
         through the SPACE slot via the coordinate line `update y i ·`, not the time slot).  This is
         the tool that discharges the `hdiff` carry of the core (E-outer) below.

    (Eout) `line_pd_double_integral` — THE CORE = THE OUTER (`∫s`) NESTING + `pd`-UNFOLDING.  With
         the `∫z`-derivative family `hdiff` (each instance an `innerZ_line_hasDerivAt`), the second
         (`∫s`) differentiation passes under the interval-integral and the whole thing unfolds through
         `pd f i y = deriv (fun t => f (update y i t)) (y i)`:
           `pd (fun x => ∫₀^b ∫_z K (u−s) x z · F s z 0) i y
              = ∫₀^b ∫_z dK (u−s) y z · F s z 0`.
         Route: `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`.2`) + `.deriv`
         + `Function.update_eq_self` (the base line-point `update y i (y i) = y`).

    (Q1) `pd_heatConvFrozen_interchange` — FIRST-ORDER under the double integral: `line_pd_double_-
         integral` specialised to `K := H`, `dK := dH` (`heatConvFrozen H F u b · 0`'s field `pd`).

    (Q2) ★★ `pd_pd_heatConvFrozen_interchange` — SECOND-ORDER: the first-order interchange `hQ1` holds
         on an open field neighborhood `V ∋ 0`, so germ-congruence of `pd` (`pd_congr_of_eventuallyEq`)
         rewrites the inner `pd` to the `∫∫ dH`-form, then `line_pd_double_integral` fires AGAIN
         (`K := dH`, `dK := dHH`, base `0`), giving
           `pd (fun y => pd (fun x => heatConvFrozen H F u b x 0) i y) i 0
              = ∫₀^b ∫_z dHH (u−s) 0 z · F s z 0`.

    ★★★ `hInterchange_discharge` — THE VERBATIM SHAPE: `Q2` at every `m` with `b := u − epsSeq m` and
         `pdpdH i τ z := dHH τ 0 z`, producing exactly the `hInterchange` carried by `LapTruncAssembly`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FIREWALL — the carries (each a genuine differentiation-under-∫ fact, NONE the conclusion,
  none vacuous, all satisfiable via the C4b Gaussian-derivative bounds and the strictly-positive gap).

    NEIGHBORHOODS   `snb ∈ 𝓝 (y i)` (real-line coordinate nbhd), `V` open `∋ 0` (field nbhd on which
                    the first-order interchange holds) — the domains of the local dominations.
    Z-DOMINATION    (`innerZ`) `hmeas`/`hint`/`h'meas` (measurability + base integrability of the
                    `z`-integrand and its field-derivative), `bnd`/`hbnd`/`hbound` (integrable
                    `z`-dominator of the derivative integrand, uniform over the line-nbhd), `hdiff`
                    (the pointwise `HasDerivAt` family of `K (u−s) (update y i ·) z · F`).
    S-DOMINATION    (`line_pd_double_integral`) `hFmeas`/`hFint`/`hF'meas` (measurability + base
                    interval-integrability of the `∫z`-object and its derivative), `bound`/`hbdd`/
                    `hbound` (interval-integrable `s`-dominator, uniform over the line-nbhd), `hdiff`
                    (the `∫z`-derivative family = the E-inner conclusion at each `s`).
    FIRST-ORDER     (`Q2`) `hQ1` — the first-order interchange on `V` (= `Q1`'s conclusion at each
                    `y ∈ V`); genuine, dischargeable by `pd_heatConvFrozen_interchange`, NOT the
                    (second-order) conclusion.
    IDENTIFICATION  (`hInterchange_discharge`) `hpdpdH` — `pdpdH i (u−s) z = dHH (u−s) 0 z` (the
                    parameter `pdpdH` IS the concrete second field-partial at `0`); definitional, not
                    vacuous.

    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.LapTruncAssembly
import QIQTH.HeatConvRegularity

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatDuhamel
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### E — the inner (`∫z`) coordinate-line differentiation.
    ############################################################################### -/

/-- **★ E — `innerZ_line_hasDerivAt`.**  THE INNER (`∫z`) NESTING.  For a fixed time `s`, a base
    line-point `p`, and a coordinate direction `i`, the map
      `w ↦ ∫ z, K (u−s) (update y i w) z · F s z 0`
    (`w` moving along the `i`-th coordinate line through `y`) is differentiable at `p`, with the
    derivative obtained by moving `∂_w` under the Lebesgue `z`-integral:
      `HasDerivAt (fun w => ∫ z, K (u−s) (update y i w) z · F s z 0)
                  (∫ z, dK (u−s) (update y i p) z · F s z 0) p`.
    Direct `.2` of `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.  Mirrors
    `HeatConvRegularity.heatConvInner_hasDerivAt`, but the differentiation variable enters through the
    SPACE slot via the coordinate line, not the time slot.  Carries the genuine `z`-level
    differentiation-under-∫ inputs (measurability, base integrability, uniform integrable derivative
    bound, pointwise `HasDerivAt` family); none is the conclusion. -/
theorem innerZ_line_hasDerivAt (K dK F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (i : Fin n) (y : Point n) (p : ℝ)
    (znb : Set ℝ) (hznb : znb ∈ 𝓝 p)
    (hmeas : ∀ w, AEStronglyMeasurable
      (fun z => K (u - s) (Function.update y i w) z * F s z 0) volume)
    (hint : Integrable
      (fun z => K (u - s) (Function.update y i p) z * F s z 0) volume)
    (h'meas : AEStronglyMeasurable
      (fun z => dK (u - s) (Function.update y i p) z * F s z 0) volume)
    (bnd : Point n → ℝ) (hbnd : Integrable bnd volume)
    (hbound : ∀ᵐ z ∂volume, ∀ w ∈ znb,
      ‖dK (u - s) (Function.update y i w) z * F s z 0‖ ≤ bnd z)
    (hdiff : ∀ᵐ z ∂volume, ∀ w ∈ znb,
      HasDerivAt (fun w => K (u - s) (Function.update y i w) z * F s z 0)
        (dK (u - s) (Function.update y i w) z * F s z 0) w) :
    HasDerivAt (fun w => ∫ z, K (u - s) (Function.update y i w) z * F s z 0)
      (∫ z, dK (u - s) (Function.update y i p) z * F s z 0) p :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le hznb
    (Filter.Eventually.of_forall hmeas) hint h'meas hbound hbnd hdiff).2

/-! ###############################################################################
    ### Eout — the core: the outer (`∫s`) nesting + `pd`-unfolding.
    ############################################################################### -/

/-- **★★ Eout — `line_pd_double_integral`.**  THE CORE.  With the `∫z`-derivative family `hdiff`
    (each instance an `innerZ_line_hasDerivAt`) plus the outer `s`-level dominations, the coordinate
    partial `pd … i y` of the frozen double integral passes under BOTH integrals:
      `pd (fun x => ∫ s in (0)..b, ∫ z, K (u−s) x z · F s z 0) i y
         = ∫ s in (0)..b, ∫ z, dK (u−s) y z · F s z 0`.
    Route: unfold `pd f i y = deriv (fun t => f (update y i t)) (y i)`, apply
    `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`.2`) to the coordinate line,
    take `.deriv`, and collapse the base line-point `update y i (y i) = y` (`Function.update_eq_self`).
    The `hdiff` carry is exactly the `∫z`-derivative family; the base integrabilities/measurabilities
    are stated at `y` and fed to the engine (which expects `update y i (y i)`) via `update_eq_self`. -/
theorem line_pd_double_integral (K dK F : ℝ → Point n → Point n → ℝ)
    (u b : ℝ) (i : Fin n) (y : Point n)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (y i))
    (hFmeas : ∀ w, AEStronglyMeasurable
      (fun s => ∫ z, K (u - s) (Function.update y i w) z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, K (u - s) y z * F s z 0) volume 0 b)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, dK (u - s) y z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 b)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      ‖∫ z, dK (u - s) (Function.update y i w) z * F s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, K (u - s) (Function.update y i w) z * F s z 0)
        (∫ z, dK (u - s) (Function.update y i w) z * F s z 0) w) :
    pd (fun x => ∫ s in (0)..b, ∫ z, K (u - s) x z * F s z 0) i y
      = ∫ s in (0)..b, ∫ z, dK (u - s) y z * F s z 0 := by
  have hy : Function.update y i (y i) = y := Function.update_eq_self i y
  have hFint' : IntervalIntegrable
      (fun s => ∫ z, K (u - s) (Function.update y i (y i)) z * F s z 0) volume 0 b := by
    rw [hy]; exact hFint
  have hF'meas' : AEStronglyMeasurable
      (fun s => ∫ z, dK (u - s) (Function.update y i (y i)) z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)) := by
    rw [hy]; exact hF'meas
  have hHD := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := 0) (b := b) (x₀ := y i) (s := snb) (bound := bound)
      (F := fun w s => ∫ z, K (u - s) (Function.update y i w) z * F s z 0)
      (F' := fun w s => ∫ z, dK (u - s) (Function.update y i w) z * F s z 0)
      hsnb (Filter.Eventually.of_forall hFmeas) hFint' hF'meas' hbound hbdd hdiff
  have hpd : pd (fun x => ∫ s in (0)..b, ∫ z, K (u - s) x z * F s z 0) i y
      = deriv (fun t => ∫ s in (0)..b, ∫ z, K (u - s) (Function.update y i t) z * F s z 0)
          (y i) := rfl
  -- assign the engine's derivative to its explicit (beta-reduced) type so `update_eq_self` fires
  have hh : deriv (fun t => ∫ s in (0)..b, ∫ z, K (u - s) (Function.update y i t) z * F s z 0) (y i)
      = ∫ s in (0)..b, ∫ z, dK (u - s) (Function.update y i (y i)) z * F s z 0 := hHD.2.deriv
  rw [hpd, hh, hy]

/-! ###############################################################################
    ### Q1 — first-order under the double integral.
    ############################################################################### -/

/-- **★ Q1 — `pd_heatConvFrozen_interchange`.**  FIRST-ORDER under the double integral.
    `line_pd_double_integral` specialised to `K := H` (so the frozen double integral is exactly
    `heatConvFrozen H F u b x 0`) with the field-derivative kernel `dH`:
      `pd (fun x => heatConvFrozen H F u b x 0) i y = ∫ s in (0)..b, ∫ z, dH (u−s) y z · F s z 0`.
    Carries the same `∫z`/`∫s` dominations as the core, at the concrete kernel `H`. -/
theorem pd_heatConvFrozen_interchange (H dH F : ℝ → Point n → Point n → ℝ)
    (u b : ℝ) (i : Fin n) (y : Point n)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (y i))
    (hFmeas : ∀ w, AEStronglyMeasurable
      (fun s => ∫ z, H (u - s) (Function.update y i w) z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, H (u - s) y z * F s z 0) volume 0 b)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, dH (u - s) y z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 b)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      ‖∫ z, dH (u - s) (Function.update y i w) z * F s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, H (u - s) (Function.update y i w) z * F s z 0)
        (∫ z, dH (u - s) (Function.update y i w) z * F s z 0) w) :
    pd (fun x => heatConvFrozen H F u b x 0) i y
      = ∫ s in (0)..b, ∫ z, dH (u - s) y z * F s z 0 := by
  have h := line_pd_double_integral H dH F u b i y snb hsnb hFmeas hFint hF'meas
    bound hbdd hbound hdiff
  simpa only [heatConvFrozen] using h

/-! ###############################################################################
    ### Q2 — second-order under the double integral (THE PRIZE).
    ############################################################################### -/

/-- **★★ Q2 — `pd_pd_heatConvFrozen_interchange`.**  SECOND-ORDER under the double integral.  With
    the first-order interchange `hQ1` holding on an open field neighborhood `V ∋ 0` (each instance =
    `pd_heatConvFrozen_interchange`), germ-congruence of `pd` (`pd_congr_of_eventuallyEq`) rewrites the
    inner `pd` to its `∫∫ dH`-form; then `line_pd_double_integral` fires AGAIN (`K := dH`, `dK := dHH`,
    base `0`) to give
      `pd (fun y => pd (fun x => heatConvFrozen H F u b x 0) i y) i 0
         = ∫ s in (0)..b, ∫ z, dHH (u−s) 0 z · F s z 0`.
    The exact `hInterchange` body at general `b`; `dHH` is the second field-`x`-partial kernel.  NOT
    `a₁ = R/6`. -/
theorem pd_pd_heatConvFrozen_interchange (H dH dHH F : ℝ → Point n → Point n → ℝ)
    (u b : ℝ) (i : Fin n)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (hQ1 : ∀ y ∈ V, pd (fun x => heatConvFrozen H F u b x 0) i y
      = ∫ s in (0)..b, ∫ z, dH (u - s) y z * F s z 0)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 ((0 : Point n) i))
    (hFmeas : ∀ w, AEStronglyMeasurable
      (fun s => ∫ z, dH (u - s) (Function.update (0 : Point n) i w) z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, dH (u - s) (0 : Point n) z * F s z 0) volume 0 b)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, dHH (u - s) (0 : Point n) z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 b)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      ‖∫ z, dHH (u - s) (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, dH (u - s) (Function.update (0 : Point n) i w) z * F s z 0)
        (∫ z, dHH (u - s) (Function.update (0 : Point n) i w) z * F s z 0) w) :
    pd (fun y => pd (fun x => heatConvFrozen H F u b x 0) i y) i 0
      = ∫ s in (0)..b, ∫ z, dHH (u - s) 0 z * F s z 0 := by
  -- Rewrite the inner `pd` to its `∫∫ dH`-form on the germ at `0` (via `hQ1` on the open `V`).
  have hcong : pd (fun y => pd (fun x => heatConvFrozen H F u b x 0) i y) i 0
      = pd (fun y => ∫ s in (0)..b, ∫ z, dH (u - s) y z * F s z 0) i 0 := by
    apply pd_congr_of_eventuallyEq
    filter_upwards [hVopen.mem_nhds hV0] with y hy using hQ1 y hy
  rw [hcong]
  -- Second application of the core with `K := dH`, `dK := dHH`, base `0`.
  exact line_pd_double_integral dH dHH F u b i 0 snb hsnb hFmeas hFint hF'meas
    bound hbdd hbound hdiff

/-! ###############################################################################
    ### ★★★ hInterchange_discharge — the VERBATIM carried shape.
    ############################################################################### -/

/-- **★★★ `hInterchange_discharge`.**  The verbatim `hInterchange` hypothesis carried by
    `LapTruncAssembly.hDuhamel_assembled` / `SliverSumPlumbing.hDuhamel_semifinal`, discharged: for
    every `m` (gap `b := u − epsSeq m > 0`) and coordinate `i`, the second-order interchange
      `pd (fun y => pd (fun x => heatConvFrozen H F u (u − epsSeq m) x 0) i y) i 0
         = ∫ s in (0)..(u − epsSeq m), ∫ z, pdpdH i (u − s) z · F s z 0`
    holds, with `pdpdH i τ z := dHH τ 0 z` (the concrete second field-`x`-partial at the center).
    Pure threading: `pd_pd_heatConvFrozen_interchange` at each `(m, i)` with the per-`(m,i)` carries
    (`hQ1`/`hFmeas`/`hFint`/`hF'meas`/`hbdd`/`hbound`/`hdiff` at gap `u − epsSeq m`), then the
    identification `hpdpdH`.  Every hypothesis is a genuine differentiation-under-∫ carry; NONE is the
    (second-order) conclusion.  NOT `a₁ = R/6`. -/
theorem hInterchange_discharge (H dH dHH F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hpdpdH : ∀ i τ z, pdpdH i τ z = dHH τ 0 z)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ y ∈ V,
      pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y
        = ∫ s in (0)..(u - epsSeq m), ∫ z, dH (u - s) y z * F s z 0)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    -- (`snb` is a real-line nbhd of `0`; reused per `i` since `(0 : Point n) i = 0` for every `i`.)
    (hFmeas : ∀ (m : ℕ) (i : Fin n) (w : ℝ), AEStronglyMeasurable
      (fun s => ∫ z, dH (u - s) (Function.update (0 : Point n) i w) z * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), IntervalIntegrable
      (fun s => ∫ z, dH (u - s) (0 : Point n) z * F s z 0) volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), AEStronglyMeasurable
      (fun s => ∫ z, dHH (u - s) (0 : Point n) z * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bound : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), IntervalIntegrable (bound m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
      ‖∫ z, dHH (u - s) (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bound m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, dH (u - s) (Function.update (0 : Point n) i w) z * F s z 0)
        (∫ z, dHH (u - s) (Function.update (0 : Point n) i w) z * F s z 0) w) :
    ∀ (m : ℕ) (i : Fin n),
      pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
        = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
  intro m i
  have hz : ((0 : Point n) i) = (0 : ℝ) := by simp
  have hQ2 := pd_pd_heatConvFrozen_interchange H dH dHH F u (u - epsSeq m) i
    V hVopen hV0 (hQ1 m i) snb (by rw [hz]; exact hsnb)
    (hFmeas m i) (hFint m i) (hF'meas m i) (bound m i) (hbdd m i) (hbound m i) (hdiff m i)
  rw [hQ2]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [hpdpdH]

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.innerZ_line_hasDerivAt
#print axioms QIQTH.HeatResidualBound.line_pd_double_integral
#print axioms QIQTH.HeatResidualBound.pd_heatConvFrozen_interchange
#print axioms QIQTH.HeatResidualBound.pd_pd_heatConvFrozen_interchange
#print axioms QIQTH.HeatResidualBound.hInterchange_discharge
