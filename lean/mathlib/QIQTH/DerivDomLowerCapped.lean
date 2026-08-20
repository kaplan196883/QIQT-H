/-
  DerivDomLowerCapped — J4-911: the C3ε PARAMETER-DERIVATIVE DOMINATOR (`boundD`) reduced to a
  named crude time-derivative Gaussian envelope, via the lower-capped Gaussian pairing.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick.  It supplies the previously-DATA-still `boundD` / `hbdd_d` /
  `hbound_d` census triple (the differentiation-under-the-integral dominator for the frozen convolution's
  parameter derivative — shared by the `hDuhamel` and `hDConv` legs) as a CONSTANT dominator, GIVEN a
  crude time-derivative Gaussian envelope on the derivative field `A τ 0 z := deriv (fun r => Wit r 0 z) τ`
  (the honest geometric residue, of the SAME `C·τ⁻¹·gaussDdim` class as the already-accepted
  `WideAmplitudeData.second_domination` second-`x`-derivative envelope) + the banked width-`2` Levi source
  bound + the Levi vanishing `hFzero`.  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, none equal to (or trivially yielding) the conclusion, no existing
  file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE CONSUMER SHAPE (the LIVE census binder, `HDuhamelLiveGateWired` / `HDConvLiveGateWired`).
      `(boundD : ℕ → ℝ → ℝ → ℝ)`
      `(hbdd_d  : ∀ m, ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u − epsSeq m))`
      `(hbound_d: ∀ m, ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u − epsSeq m) → ∀ c ∈ nb m u,`
      `            ‖∫ z, deriv (fun r => Wit r 0 z) (c − s) · F s z 0‖ ≤ boundD m u s)`
  with the neighborhood binder `(nb : ℕ → ℝ → Set ℝ)`, `(hnb : ∀ m, ∀ u ∈ U, nb m u ∈ 𝓝 u)`.

  ## THE REDUCTION (generic in `A`, `F`).
    •  `derivDomNb m u := Metric.ball u (epsSeq m / 2)` — the CONCRETE shared neighborhood (so the same
       `nb` feeds `hbound_d` here AND the companion `hpardiff` later, with no existential-packaging
       mismatch).  `derivDomNb_mem_nhds` supplies `hnb`.
    •  `derivDom_boundD_of_crude` — the CONSTANT dominator + both `hbdd_d` / `hbound_d`.  Route: on the
       pairing interval `s ∈ (0, u−εₘ]` with `c ∈ ball u (εₘ/2)`, the derivative time `τ := c − s`
       satisfies `εₘ/2 < τ < u + εₘ =: Tc` and `0 < s ≤ Tc`, so:
         ·  the crude `|A τ 0 z| ≤ Ccr·τ⁻¹·gaussDdim (wL·τ)(0−z)` (valid on `(0,Tc]`) LOWER-CAPS to the
            genuine Gaussian bound `(Ccr·(εₘ/2)⁻¹)·gaussDdim (wL·τ)(0−z)` via `τ⁻¹ ≤ (εₘ/2)⁻¹`;
         ·  paired against the width-`2` Levi bound `|F s z 0| ≤ CF·gaussDdim (wF·s) z` and integrated in
            `z` (Gaussian product `∫ G_{wL·τ}·G_{wF·s} = G_{wL·τ+wF·s}(0)`, `gaussDdim_pairing_integral`);
         ·  since `wL·τ + wF·s ≥ (min wL wF)·(τ+s) = (min wL wF)·c ≥ (min wL wF)·(u − εₘ/2) > 0`, the
            centred-Gaussian peak antitonicity `gaussDdim_zero_antitone` bounds it by the `s,c`-UNIFORM
            CONSTANT `M m u := (Ccr·(εₘ/2)⁻¹)·CF·gaussDdim ((min wL wF)·(u − εₘ/2)) 0`.
       `hbound_d` is proved DETERMINISTICALLY for every `s` and every `c ∈ nb m u` (the `s ≤ 0` branch is
       zero by `hFzero`), then wrapped in `∀ᵐ` — sidestepping the illegal `∀ c, ∀ᵐ s` order.  `hbdd_d` is
       `intervalIntegrable_const`.

  ⚠  STILL NOT `a₁ = R/6`.  The one carried residue `hAcrude` (the crude time-derivative envelope) is a
  genuine geometric input; it is satisfiable at the concrete gated witness (`GatedTauDerivRep`'s exact
  `∂_τ` closed form `(∑ᵢ((Wz)ᵢ²/4τ² − 1/2τ))·gaussDdim τ(Wz)·A + gaussDdim τ(Wz)·∂_τA` absorbs into the
  `τ⁻¹·gaussDdim(wider)` class via the polynomial-Gaussian absorption bank), NOT discharged here.
-/
import Mathlib
import QIQTH.EveryCeilingFamilies

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing
open scoped Interval Topology BigOperators

namespace QIQTH.DerivDomLowerCapped

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **The concrete shared neighborhood.**  `derivDomNb m u := Metric.ball u (epsSeq m / 2)`.  The
    half-gap radius keeps the derivative time `c − s` bounded below by `epsSeq m / 2 > 0` on the pairing
    interval, so a crude `τ⁻¹` envelope lower-caps to a genuine Gaussian bound.  Exposed CONCRETELY so
    the same `nb` binder feeds both this dominator and the companion parametric-`HasDerivAt` slot. -/
noncomputable def derivDomNb (m : ℕ) (u : ℝ) : Set ℝ := Metric.ball u (epsSeq m / 2)

/-- `derivDomNb m u ∈ 𝓝 u` — the `hnb` supply. -/
theorem derivDomNb_mem_nhds (m : ℕ) (u : ℝ) : derivDomNb m u ∈ 𝓝 u := by
  apply Metric.ball_mem_nhds
  have := epsSeq_pos m; linarith

/-- **★★★ J4-911 — `derivDom_boundD_of_crude`.**  THE C3ε PARAMETER-DERIVATIVE DOMINATOR.  For a
    derivative field `A` carrying the crude time-derivative Gaussian envelope `hAcrude`
    (`|A τ 0 z| ≤ Ccr m u · τ⁻¹ · gaussDdim (wL m u · τ)(0−z)` on `(0, u+εₘ]`) and a Levi source `F`
    carrying the width-`2` bound `hFdom` + the vanishing `hFzero`, the census `boundD` / `hbdd_d` /
    `hbound_d` triple holds at the CONCRETE neighborhood `derivDomNb`, with the CONSTANT dominator
    `boundD m u := fun _ => (Ccr m u·(εₘ/2)⁻¹)·CF m u·gaussDdim ((min (wL m u)(wF m u))·(u−εₘ/2)) 0`.
    ⚠ NOT `a₁ = R/6`; the crude envelope `hAcrude` is a carried geometric residue. -/
theorem derivDom_boundD_of_crude
    (A F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (Ccr wL CF wF : ℕ → ℝ → ℝ)
    (hCcr : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ Ccr m u) (hwL : ∀ (m : ℕ), ∀ u ∈ U, 0 < wL m u)
    (hCF : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ CF m u) (hwF : ∀ (m : ℕ), ∀ u ∈ U, 0 < wF m u)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, F s z 0 = 0)
    (hAcrude : ∀ (m : ℕ), ∀ u ∈ U, ∀ τ : ℝ, 0 < τ → τ ≤ u + epsSeq m → ∀ z : Point n,
        |A τ 0 z| ≤ Ccr m u * τ⁻¹ * gaussDdim (wL m u * τ) (0 - z))
    (hFdom : ∀ (m : ℕ), ∀ u ∈ U, ∀ s : ℝ, 0 < s → s ≤ u + epsSeq m → ∀ z : Point n,
        |F s z 0| ≤ CF m u * gaussDdim (wF m u * s) z) :
    ∃ boundD : ℕ → ℝ → ℝ → ℝ,
      (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m)) ∧
      (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ derivDomNb m u,
        ‖∫ z, A (c - s) 0 z * F s z 0‖ ≤ boundD m u s) := by
  -- the CONSTANT dominator.
  set M : ℕ → ℝ → ℝ := fun m u =>
    (Ccr m u * (epsSeq m / 2)⁻¹) * CF m u
      * gaussDdim (min (wL m u) (wF m u) * (u - epsSeq m / 2)) (0 : Point n) with hMdef
  refine ⟨fun m u _ => M m u, ?_, ?_⟩
  · -- `hbdd_d`: a constant is interval-integrable.
    intro m u _hu; exact intervalIntegrable_const
  · -- `hbound_d`: DETERMINISTIC over `s` and `c`, then wrapped in `∀ᵐ`.
    intro m u hu
    refine ae_of_all _ (fun s hsmem c hc => ?_)
    have he : 0 < epsSeq m := epsSeq_pos m
    -- nonnegativity of the constant.
    have hMnn : 0 ≤ M m u := by
      rw [hMdef]
      exact mul_nonneg (mul_nonneg (mul_nonneg (hCcr m u hu)
        (by positivity)) (hCF m u hu)) (gaussDdim_nonneg _ _)
    -- unpack the interval membership.
    have hub : s ∈ Set.Ioc (min 0 (u - epsSeq m)) (max 0 (u - epsSeq m)) := hsmem
    have hsmax : s ≤ max 0 (u - epsSeq m) := hub.2
    -- the ball membership `|c − u| < εₘ/2`.
    have hcball : dist c u < epsSeq m / 2 := hc
    have hcu : |c - u| < epsSeq m / 2 := by rwa [Real.dist_eq] at hcball
    have hcuL : u - epsSeq m / 2 < c := by have := (abs_lt.mp hcu).1; linarith
    have hcuU : c < u + epsSeq m / 2 := by have := (abs_lt.mp hcu).2; linarith
    rcases le_or_gt s 0 with hs0 | hs0
    · -- `s ≤ 0`: the Levi factor vanishes, the integral is `0`.
      have hz : (fun z => A (c - s) 0 z * F s z 0) = fun _ => (0 : ℝ) := by
        funext z; rw [hFzero s hs0 z, mul_zero]
      rw [hz, integral_zero, norm_zero]; exact hMnn
    · -- `s > 0`: the genuine Gaussian pairing branch.
      -- from `s ≤ max 0 (u−εₘ)` and `s > 0` extract `0 < s ≤ u − εₘ` (hence `u > εₘ`).
      have hue : 0 < u - epsSeq m := by
        by_contra h
        push_neg at h
        rw [max_eq_left h] at hsmax
        exact absurd (lt_of_lt_of_le hs0 hsmax) (lt_irrefl 0)
      have hsue : s ≤ u - epsSeq m := by rwa [max_eq_right hue.le] at hsmax
      -- the derivative time `τ = c − s` window: `εₘ/2 < c − s < u + εₘ`, `0 < s ≤ u + εₘ`.
      have hτlo : epsSeq m / 2 < c - s := by linarith
      have hτpos : 0 < c - s := by linarith
      have hτTc : c - s ≤ u + epsSeq m := by linarith
      have hsTc : s ≤ u + epsSeq m := by linarith
      -- lower-capped first-factor Gaussian bound.
      have hCA0 : 0 ≤ Ccr m u * (epsSeq m / 2)⁻¹ := mul_nonneg (hCcr m u hu) (by positivity)
      have hAcap : ∀ z : Point n,
          |A (c - s) 0 z|
            ≤ (Ccr m u * (epsSeq m / 2)⁻¹) * gaussDdim (wL m u * (c - s)) (0 - z) := by
        intro z
        refine le_trans (hAcrude m u hu (c - s) hτpos hτTc z) ?_
        have hinv : (c - s)⁻¹ ≤ (epsSeq m / 2)⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div]
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinv (hCcr m u hu)) (gaussDdim_nonneg _ _)
      -- the width-2 Levi bound.
      have hFcap : ∀ z : Point n, |F s z 0| ≤ CF m u * gaussDdim (wF m u * s) z :=
        hFdom m u hu s hs0 hsTc
      -- the `z`-integrable dominator.
      set Dz : Point n → ℝ := fun z =>
        (Ccr m u * (epsSeq m / 2)⁻¹ * CF m u)
          * (gaussDdim (wL m u * (c - s)) z * gaussDdim (wF m u * s) z) with hDzdef
      have hDz_int : Integrable Dz volume := by
        rw [hDzdef]
        exact (gaussDdim_pair_integrable (wL m u * (c - s)) (wF m u * s)).const_mul _
      have hpt : ∀ z : Point n, ‖A (c - s) 0 z * F s z 0‖ ≤ Dz z := by
        intro z
        rw [Real.norm_eq_abs, abs_mul]
        have hAz := hAcap z
        rw [gaussDdim_zero_sub] at hAz
        have hFz := hFcap z
        rw [hDzdef]
        calc |A (c - s) 0 z| * |F s z 0|
            ≤ (Ccr m u * (epsSeq m / 2)⁻¹ * gaussDdim (wL m u * (c - s)) z)
                * (CF m u * gaussDdim (wF m u * s) z) :=
              mul_le_mul hAz hFz (abs_nonneg _) (mul_nonneg hCA0 (gaussDdim_nonneg _ _))
          _ = (Ccr m u * (epsSeq m / 2)⁻¹ * CF m u)
                * (gaussDdim (wL m u * (c - s)) z * gaussDdim (wF m u * s) z) := by ring
      -- pairing integral value and the `s,c`-uniform peak bound.
      have hmin0 : 0 < min (wL m u) (wF m u) := lt_min (hwL m u hu) (hwF m u hu)
      have hlowbase : 0 < min (wL m u) (wF m u) * (u - epsSeq m / 2) :=
        mul_pos hmin0 (by linarith)
      have hcomb : min (wL m u) (wF m u) * (u - epsSeq m / 2)
          ≤ wL m u * (c - s) + wF m u * s := by
        have h1 : min (wL m u) (wF m u) ≤ wL m u := min_le_left _ _
        have h2 : min (wL m u) (wF m u) ≤ wF m u := min_le_right _ _
        have hcs : (0:ℝ) ≤ c - s := hτpos.le
        have hsnn : (0:ℝ) ≤ s := hs0.le
        nlinarith [mul_le_mul_of_nonneg_right h1 hcs, mul_le_mul_of_nonneg_right h2 hsnn]
      have hval : (∫ z, Dz z)
          = (Ccr m u * (epsSeq m / 2)⁻¹ * CF m u)
              * gaussDdim (wL m u * (c - s) + wF m u * s) (0 : Point n) := by
        rw [hDzdef, integral_const_mul,
          gaussDdim_pairing_integral (wL m u * (c - s)) (wF m u * s)
            (mul_pos (hwL m u hu) hτpos) (mul_pos (hwF m u hu) hs0)]
      have hpeak : gaussDdim (wL m u * (c - s) + wF m u * s) (0 : Point n)
          ≤ gaussDdim (min (wL m u) (wF m u) * (u - epsSeq m / 2)) (0 : Point n) :=
        gaussDdim_zero_antitone (min (wL m u) (wF m u) * (u - epsSeq m / 2))
          (wL m u * (c - s) + wF m u * s) hlowbase hcomb
      -- assemble.
      calc ‖∫ z, A (c - s) 0 z * F s z 0‖
          ≤ ∫ z, ‖A (c - s) 0 z * F s z 0‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ z, Dz z :=
            integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hDz_int
              (ae_of_all _ hpt)
        _ = (Ccr m u * (epsSeq m / 2)⁻¹ * CF m u)
              * gaussDdim (wL m u * (c - s) + wF m u * s) (0 : Point n) := hval
        _ ≤ (Ccr m u * (epsSeq m / 2)⁻¹ * CF m u)
              * gaussDdim (min (wL m u) (wF m u) * (u - epsSeq m / 2)) (0 : Point n) :=
            mul_le_mul_of_nonneg_left hpeak
              (mul_nonneg (mul_nonneg (hCcr m u hu) (by positivity)) (hCF m u hu))
        _ = M m u := by simp only [hMdef]

end QIQTH.DerivDomLowerCapped

section AxiomChecks
open QIQTH.DerivDomLowerCapped
#print axioms derivDomNb_mem_nhds
#print axioms derivDom_boundD_of_crude
end AxiomChecks
