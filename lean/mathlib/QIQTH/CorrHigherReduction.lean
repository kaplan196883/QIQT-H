/-
  CorrHigherReduction — J4-503: the HONEST bounded-remainder form of `hCorrHigher`, reducing the
  Levi/Duhamel correction-order carry of `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` to the SINGLE
  still-open per-slice `O(a+s)` transport estimate.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  No `sorry`, no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypothesis, no result equal to (or trivially yielding) `a₁=R/6`,
  no existing file edited, nothing committed.  std-3 only.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE CARRY BEING REDUCED.  The capstone `trueKernel_diagonal_a1_eq_R6` carries
      `hCorrHigher : heatConv H (leviSeries E) t 0 0 = pref·(t²·cRem)`
  at a SINGLE fixed `t > 0`.  ⚠ AT A SINGLE `t` THIS EQUALITY IS TRIVIALLY SATISFIABLE (take
  `cRem := heatConv … / (pref·t²)`, `pref ≠ 0`, `t ≠ 0`) — which is exactly the COSMETIC discharge in
  `TrueKernelA1Reduced.corrHigher_witness`.  The GENUINE `O(t²)` content — that `cRem` stays BOUNDED
  as `t → 0⁺`, so the folded correction does NOT shift the `t¹` coefficient `a₁` — is NOT captured by
  the bare single-`t` equality.  It is a statement about the FAMILY `cRem(t)`, i.e. a `∀τ` bound
      `‖heatConv H (leviSeries E) τ 0 0‖ ≤ K·τ²`.

  ## WHAT THIS FILE LANDS (the honest reduction).  By the DEFINITION of the space-time convolution
  (`HeatDuhamel.heatConv A B t x y = ∫ s in 0..t, ∫ z, A (t−s) x z · B s z y` — the J4-499 τ/s
  resolution is DEFINITIONAL), the traced correction is `∫₀^t r (t−s) s ds` with the traced residual
  slice `r a s := ∫ z, H a 0 z · F s z 0` at parametrix-age `a = t − s`.  Assembling the banked
  Duhamel-simplex step `DuhamelAssembly.duhamel_simplex_quadratic_bound` (`(∀s, ‖r(t−s) s‖ ≤
  K·((t−s)+s)) → ‖∫₀^t r(t−s) s‖ ≤ K·t²`, using that `(t−s)+s = t` is CONSTANT on the Duhamel path)
  gives the `O(t²)` BOUND, and dividing out `pref·t²` yields the `hCorrHigher` EQUALITY shape TOGETHER
  WITH the BOUND `|cRem| ≤ K/|pref|` — the boundedness the cosmetic discharge lacks.

    ★  `corrHigher_bounded_of_slice` — from a carried per-slice `O(a+s)` bound on the traced residual,
       the `hCorrHigher` equality holds with the CONCRETE witness `cRem = heatConv…/(pref·t²)` AND the
       genuine bound `|cRem| ≤ K/|pref|`.  This ISOLATES the remaining gap to the per-slice estimate.
    ★  `slice_bound_inhabited` — SATISFIABILITY: the carried per-slice `O(a+s)` hypothesis is INHABITED
       (the flat / vanishing-source case `F ≡ 0`), so the reduction is NOT vacuous.

  ## ⚠ WHAT REMAINS OPEN (the isolated carried input).  The per-slice `O(a+s)` bound
      `‖∫ z, H (t−s) 0 z · F s z 0‖ ≤ K·((t−s)+s)`
  is NOT proved here.  The currently-banked pieces are (i) the crude ABSOLUTE slice bound `O(1/a)`
  (`ConcreteRemainderOrder.concreteRemainder_order`, LOG-DIVERGENT under `∫₀^t ds`), (ii) the SIGNED
  slice upgrade `O(1/a) → O(1)` (`SliceBoundO1.hessGauss_signed_slice_O1`: const/linear moments cancel,
  only the amplitude Hessian survives), and (iii) the van-Vleck amplitude 2-jet
  `D²u₀(0) = (1/6)Ric` (`VanVleckTwoJet.invSqrt_trace_hessian_scal`).  The MISSING estimate is the
  TRANSPORT CANCELLATION upgrading the surviving `O(1)` amplitude-Hessian transport coefficient to
  `O(a+s)` — the parametrix `u₀ + t·u₁` transport-equation identity that annihilates it — which is NOT
  banked as an operational per-slice identity for the concrete `chartAmp·F`.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HeatDuhamel
import QIQTH.DuhamelSimplexAssembly

open MeasureTheory
open scoped Interval

namespace QIQTH.CorrHigherReduction

open QIQTH.Curvature QIQTH.HeatDuhamel

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **★ `corrHigher_bounded_of_slice` — the honest bounded-remainder reduction of `hCorrHigher`.**
    Fix `t > 0`, a nonzero heat prefactor `pref`, and `K ≥ 0`.  IF the traced residual slice
    `r a s := ∫ z, H a 0 z · F s z 0` (parametrix-age `a`, source-time `s`) satisfies the
    post-cancellation `O(a+s)` bound
        `‖∫ z, H (t−s) 0 z · F s z 0‖ ≤ K·((t−s)+s)`   on `s ∈ Ι 0 t`,
    THEN the correction `heatConv H F t 0 0` has the `hCorrHigher` EQUALITY shape with the CONCRETE
    remainder witness `cRem = heatConv H F t 0 0 / (pref·t²)` AND — crucially — the genuine BOUND
        `|cRem| ≤ K / |pref|`.
    The equality alone is trivially satisfiable at a single `t`; the BOUND is the real `O(t²)` content
    (as `t → 0⁺` the remainder stays bounded, so `a₁` is not shifted).  Assembles the definitional τ/s
    resolution of `heatConv` with the banked `DuhamelAssembly.duhamel_simplex_quadratic_bound`
    (`(t−s)+s = t` constant on the Duhamel path).  ⚠ NOT `a₁ = R/6`; the per-slice `O(a+s)` hypothesis
    is the still-open transport estimate. -/
theorem corrHigher_bounded_of_slice
    (H F : ℝ → Point n → Point n → ℝ) (pref K t : ℝ)
    (ht : 0 < t) (hpref : pref ≠ 0) (hK : 0 ≤ K)
    (hslice : ∀ s ∈ Ι (0 : ℝ) t, ‖∫ z, H (t - s) 0 z * F s z 0‖ ≤ K * ((t - s) + s)) :
    heatConv H F t 0 0 = pref * (t ^ 2 * (heatConv H F t 0 0 / (pref * t ^ 2)))
      ∧ |heatConv H F t 0 0 / (pref * t ^ 2)| ≤ K / |pref| := by
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hpt2 : pref * t ^ 2 ≠ 0 := mul_ne_zero hpref (ne_of_gt ht2)
  -- The `O(t²)` BOUND via the banked Duhamel-simplex assembly (`heatConv` unfolds definitionally to
  -- `∫ s in 0..t, ∫ z, H (t−s) 0 z · F s z 0 = ∫ s in 0..t, (fun a s' => ∫ z, H a 0 z · F s' z 0) (t−s) s`).
  have hbound : ‖heatConv H F t 0 0‖ ≤ K * t ^ 2 :=
    QIQTH.DuhamelAssembly.duhamel_simplex_quadratic_bound
      (fun a s' => ∫ z, H a 0 z * F s' z 0) K t ht.le hslice
  rw [Real.norm_eq_abs] at hbound
  refine ⟨?_, ?_⟩
  · field_simp
  · rw [abs_div, abs_mul, abs_of_pos ht2]
    have hpref_pos : (0 : ℝ) < |pref| := abs_pos.mpr hpref
    have hrw : K / |pref| = (K * t ^ 2) / (|pref| * t ^ 2) := by
      field_simp
    rw [hrw]
    gcongr

/-- **★ `slice_bound_inhabited` — SATISFIABILITY of the carried per-slice `O(a+s)` hypothesis.**  For
    the flat / vanishing-source case `F ≡ 0`, the traced residual slice `∫ z, H (t−s) 0 z · 0 = 0`, so
    the `O(a+s)` bound holds for every `K ≥ 0` and `t ≥ 0`.  Hence the hypothesis of
    `corrHigher_bounded_of_slice` is INHABITED and the reduction is NOT vacuous / does not close by
    contradiction. -/
theorem slice_bound_inhabited (H : ℝ → Point n → Point n → ℝ) (K t : ℝ) (hK : 0 ≤ K) (ht : 0 ≤ t) :
    ∀ s ∈ Ι (0 : ℝ) t,
      ‖∫ z, H (t - s) 0 z * (fun (_ : ℝ) (_ _ : Point n) => (0 : ℝ)) s z 0‖
        ≤ K * ((t - s) + s) := by
  intro s _
  simp only [mul_zero, MeasureTheory.integral_zero, norm_zero]
  have : (t - s) + s = t := by ring
  rw [this]
  positivity

/-- **★ `corrHigher_bounded_flat` — the reduction is NON-VACUOUSLY inhabited end-to-end.**  Feeding the
    flat witness `slice_bound_inhabited` into `corrHigher_bounded_of_slice` produces a genuine bounded
    remainder (here `cRem = 0`), certifying the whole reduction is satisfiable (not a proof-by-empty). -/
theorem corrHigher_bounded_flat (H : ℝ → Point n → Point n → ℝ) (pref t : ℝ)
    (ht : 0 < t) (hpref : pref ≠ 0) :
    heatConv H (fun (_ : ℝ) (_ _ : Point n) => (0 : ℝ)) t 0 0
        = pref * (t ^ 2 * (heatConv H (fun (_ : ℝ) (_ _ : Point n) => (0 : ℝ)) t 0 0 / (pref * t ^ 2)))
      ∧ |heatConv H (fun (_ : ℝ) (_ _ : Point n) => (0 : ℝ)) t 0 0 / (pref * t ^ 2)|
          ≤ (0 : ℝ) / |pref| :=
  corrHigher_bounded_of_slice H (fun _ _ _ => 0) pref 0 t ht hpref le_rfl
    (slice_bound_inhabited H 0 t le_rfl ht.le)

end QIQTH.CorrHigherReduction

section AxiomChecks
open QIQTH.CorrHigherReduction
#print axioms corrHigher_bounded_of_slice
#print axioms slice_bound_inhabited
#print axioms corrHigher_bounded_flat
end AxiomChecks
