/-
  HCompNearCarryTerm1AmpSliverBound — J4-1047: the amplitude-weighted generalization of J4-1016's
  sliver bound Sol identified as the ONE genuinely tractable new lemma toward `r6`'s composition,
  after a plan-review confirmed the base-slot (J4-1046/J4-1023) vs eval-slot (J4-1012/J4-1013)
  coordinate systems are NOT bridgeable today without an unbuilt "coordinate bridge" lemma.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## PLAN-REVIEW (gpt-5.6-sol, high, before any Lean).  Consulted on cp1008's "r6 4-lemma composition"
  using J4-1046's literal `hxmem`/`hd`-free `kPrime` CoV identity (base-slot, `W z := uniformInverseChart
  z x`) together with J4-1012 (`evalSlot_terminalVel_weighted_CoV`, EVAL-slot `U x z`), J4-1013
  (`reversal_link_ball_integral`), J4-1014/1020/1022/1023 (base-slot domain-containment/tail-bound
  chain), and J4-1016 (`terminalVelAt_chartReplace_sliver_bound_unconditional`).  VERDICT: (1) J4-1012/
  1013 operate in the EVAL-slot chart image (`w_e := U x z`) while J4-1046/1023 operate in the BASE-slot
  chart image (`w_b := U z x`) — these are two DIFFERENT `w`-coordinates for the same `z`, and
  `reversal_link_ball_integral` only bridges the two GAUSSIAN VALUES while still in `z`-space; it does
  NOT identify the two image sets, inverse maps, Jacobians, or transported amplitudes.  Composing
  J4-1046's base-slot CoV weight `Bfac(V w_b)/|det f'_b(V w_b)|` with J4-1016's bare `‖z‖^k`-weighted
  sliver comparison is therefore NOT valid as stated — it needs either a base-vs-eval coordinate-
  transition lemma (unbuilt) or a fully eval-slot-only parallel package (also unbuilt: J4-1014/1020/
  1022/1023's containment/tail machinery is base-slot only).  (2) There is no way to apply J4-1016's
  bound directly on `z`-space domains without first performing the eval-slot CoV (`w = U x z`) — the
  sliver bound is stated in flat chart/tangent coordinates centred at `0`, not in `z`-space centred at
  `x`.  (3) The ONE piece buildable RIGHT NOW from what's banked, with NO new coordinate bridge, is a
  weighted/restricted generalization of J4-1016 itself: replacing its bare `‖z‖^k` weight by an
  ARBITRARY amplitude `a(s,z)` dominated by `C·‖z‖^k`, and its full ball `ball 0 R'` by an arbitrary
  measurable sub-region.  This file builds exactly that generalization (on the FULL discharged ball, to
  keep the domain-restriction question — which needs the still-missing bridge — separate).  It is a
  genuine new composition (triangle inequality + pointwise domination + `chartReplace_sliver_uniform_
  bound`'s existing per-`τ` bound, none of which had been assembled together before), not a restatement.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`. No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited (NEW FILE).

  ── WHAT THIS FILE DOES.  Generalizes J4-1016's `terminalVelAt_chartReplace_sliver_bound_unconditional`
  from the bare integrand `‖z‖^k · |G_{t-s}(T_{x₀}z) − G_{t-s}(z)|` to the SIGNED, amplitude-weighted
  integrand `(G_{t-s}(T_{x₀}z) − G_{t-s}(z)) · a(s,z)`, for ANY globally continuous `a : ℝ → Point n → ℝ`
  dominated by `|a s z| ≤ C·‖z‖^k` (`C ≥ 0`), giving the SAME rate `O(√ε^{k+3})` scaled by `C`, on the
  SAME discharged ball `ball 0 R'`.  UNCONDITIONAL modulo the standing geometry `(g, gi, hC, hK, x₀ ∈ K)`.
  Proof: triangle inequality (`norm_integral_le_integral_norm`, `intervalIntegral.norm_integral_le_of_
  norm_le_const_ae`) + pointwise domination of the signed amplitude-weighted integrand's norm by
  `C · ‖z‖^k · |G_{t-s}(T_{x₀}z) − G_{t-s}(z)|` (`setIntegral_mono_on`, `Integrable.mono'` for the needed
  integrability side, via the SAME continuity/domination recipe J4-1016 uses) + J4-1016's own per-`τ`
  bound (`chartReplace_sliver_uniform_bound`).

  ── WHAT THIS DOES **NOT** DO.  It does NOT bridge the base-slot/eval-slot coordinate mismatch Sol
  identified — the amplitude `a` here is still evaluated in the SAME flat `z`-coordinate as J4-1016's
  bare weight, not the base-slot-CoV-transported weight `Bfac(V w_b)/|det f'_b(V w_b)|` that J4-1046/
  1023's actual machinery produces. It does NOT compose with J4-1012, J4-1013, or J4-1046 into any
  bound on `nb`'s actual literal `term1`. It does NOT discharge `r6`, `nb`, `hCConv`, or any part of
  `hcomp`. `Bfac`'s other 3 summands and `fb` remain untouched. `a₁ = R/6` remains STRICTLY CONDITIONAL
  on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HWintFullBallDischarge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.FlatHeatEquation
open QIQTH.ExpMap QIQTH.ChartThirdJet QIQTH.RadialDistance
open QIQTH.GeodesicReversalRouteAtPoint
open QIQTH.HCompNearCarryConcreteDischarge
open QIQTH.GaussianAbsMomentGeneral
open QIQTH.HCompNearCarryAssembly
open QIQTH.HWintFullBallDischarge
open scoped Topology Interval

namespace QIQTH.HCompNearCarryTerm1AmpSliverBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `terminalVelAt_chartReplace_sliver_amp_bound_unconditional`.**  The amplitude-weighted
    generalization of J4-1016's near-sliver rate: for ANY globally continuous `a : ℝ → Point n → ℝ`
    dominated by `C · ‖z‖^k`, the SIGNED chart-replacement cancellation integral weighted by `a` obeys
    the SAME `O(√ε^{k+3})` rate, scaled by `C`, on the discharged ball `ball 0 R'`.  UNCONDITIONAL
    modulo the standing geometry. NOT `a₁ = R/6`. -/
theorem terminalVelAt_chartReplace_sliver_amp_bound_unconditional
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (t : ℝ)
    (a : ℝ → Point n → ℝ) (ha_cont : ∀ s : ℝ, Continuous (a s))
    (C : ℝ) (hC0 : 0 ≤ C) (ha_bound : ∀ s z, |a s z| ≤ C * ‖z‖ ^ k) :
    ∃ R' > (0 : ℝ), ∃ L' ≥ (0 : ℝ),
      ‖∫ s in (t - ε)..t,
          ∫ z in Metric.ball (0 : Point n) R',
            (gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖
        ≤ C * ((L' / 4 * (Real.sqrt 2) ^ n
                * ((n : ℝ) * absMomentConst (k + 3) * (Real.sqrt 2) ^ (k + 3)))
              * (Real.sqrt ε) ^ (k + 3)) := by
  obtain ⟨R, hR, L', hL', herr, hmin⟩ := terminalVelAt_nearIsometry_data g gi hC hK hx₀K
  set ρ0 : ℝ := min (expRho g gi hC x₀) (uniformFlowRadius g gi hC hK) with hρ0def
  have hρ0pos : 0 < ρ0 := lt_min (expRho_pos g gi hC x₀) (uniformFlowRadius_pos g gi hC hK)
  set R' : ℝ := min R ρ0 with hR'def
  have hR'pos : 0 < R' := lt_min hR hρ0pos
  have hR'leR : R' ≤ R := min_le_left _ _
  have hsubρ0 : Metric.ball (0 : Point n) R' ⊆ Metric.ball (0 : Point n) ρ0 :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hsubR : Metric.ball (0 : Point n) R' ⊆ Metric.ball (0 : Point n) R :=
    Metric.ball_subset_ball hR'leR
  have hcontOn : ContinuousOn (terminalVelAt g gi hC hK x₀) (Metric.ball (0 : Point n) R') :=
    (terminalVelAt_continuousOn_ball g gi hC hK hx₀K).mono hsubρ0
  have herr' : ∀ z ∈ Metric.ball (0 : Point n) R', |rncRadialSq (terminalVelAt g gi hC hK x₀ z) -
      rncRadialSq z| ≤ L' * ‖z‖ ^ 3 := fun z hz => herr z (hsubR hz)
  have hmin' : ∀ z ∈ Metric.ball (0 : Point n) R',
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (terminalVelAt g gi hC hK x₀ z) :=
    fun z hz => hmin z (hsubR hz)
  refine ⟨R', hR'pos, L', hL', ?_⟩
  set ck3 : ℝ := absMomentConst (k + 3) with hck3def
  have hck3nn : 0 ≤ ck3 := absMomentConst_nonneg (k + 3)
  -- `hWint` on `ball 0 R'`, for every `τ ∈ (0, ε]` (same recipe as J4-1016 §2).
  have hWint : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
      IntegrableOn (fun z : Point n =>
          ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|)
        (Metric.ball 0 R') volume := by
    intro τ hτ0 _hτε
    have hcont1 : ContinuousOn (fun z => gaussDdim τ (terminalVelAt g gi hC hK x₀ z))
        (Metric.ball (0 : Point n) R') := (gaussDdim_cont τ).comp_continuousOn hcontOn
    have hcont2 : ContinuousOn (fun z : Point n => gaussDdim τ z) (Metric.ball (0 : Point n) R') :=
      (gaussDdim_cont τ).continuousOn
    have hcontI : ContinuousOn
        (fun z : Point n => ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|)
        (Metric.ball (0 : Point n) R') :=
      (continuous_norm.pow k).continuousOn.mul
        (_root_.continuous_abs.comp_continuousOn (hcont1.sub hcont2))
    have hmeas : AEStronglyMeasurable
        (fun z : Point n => ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|)
        (volume.restrict (Metric.ball (0 : Point n) R')) :=
      hcontI.aestronglyMeasurable measurableSet_ball
    set M0 : ℝ := gaussDdim τ (0 : Point n) with hM0def
    have hCbound : IntegrableOn (fun _ : Point n => R' ^ k * M0)
        (Metric.ball (0 : Point n) R') volume := integrableOn_const (by finiteness)
    refine Integrable.mono' hCbound hmeas ?_
    rw [ae_restrict_iff' measurableSet_ball]
    refine ae_of_all _ (fun z hz => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hz
    have haM : gaussDdim τ (terminalVelAt g gi hC hK x₀ z) ≤ M0 := gaussDdim_le_diagonal hτ0 _
    have hbM : gaussDdim τ z ≤ M0 := gaussDdim_le_diagonal hτ0 z
    have haa : 0 ≤ gaussDdim τ (terminalVelAt g gi hC hK x₀ z) := gaussDdim_nonneg τ _
    have hbb : 0 ≤ gaussDdim τ z := gaussDdim_nonneg τ z
    have habs : |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z| ≤ M0 := by
      rw [abs_le]; constructor <;> linarith
    have hzk : ‖z‖ ^ k ≤ R' ^ k := pow_le_pow_left₀ (norm_nonneg z) hz.le _
    have hval : ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|
        ≤ R' ^ k * M0 := mul_le_mul hzk habs (abs_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hval
  have hmom := terminalVel_sliver_hmom k ε
  set Cshape : ℝ := L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3))
    with hCshapedef
  have hCshape_nn : 0 ≤ Cshape := by rw [hCshapedef]; positivity
  set M : ℝ := Cshape * (Real.sqrt ε) ^ (k + 1) with hMdef
  have hle : t - ε ≤ t := by linarith
  have hae : ∀ᵐ s : ℝ ∂volume, s ∈ Set.uIoc (t - ε) t →
      ‖∫ z in Metric.ball (0 : Point n) R',
          (gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖
        ≤ C * M := by
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [hne] with s hsne hmem
    rw [Set.uIoc_of_le hle] at hmem
    obtain ⟨hs1, hs2⟩ := hmem
    have hs2' : s < t := lt_of_le_of_ne hs2 hsne
    have hτpos : 0 < t - s := by linarith
    have hτε : t - s ≤ ε := by linarith
    -- Continuity of the signed base difference and its product with `a s` on `ball 0 R'`.
    have hcontGdiff : ContinuousOn
        (fun z => gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z)
        (Metric.ball (0 : Point n) R') := by
      have hc1 : ContinuousOn (fun z => gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z))
          (Metric.ball (0 : Point n) R') := (gaussDdim_cont (t - s)).comp_continuousOn hcontOn
      have hc2 : ContinuousOn (fun z : Point n => gaussDdim (t - s) z)
          (Metric.ball (0 : Point n) R') := (gaussDdim_cont (t - s)).continuousOn
      exact hc1.sub hc2
    have hcontProd : ContinuousOn
        (fun z => (gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z)
        (Metric.ball (0 : Point n) R') :=
      hcontGdiff.mul (ha_cont s).continuousOn
    have hmeasProd : AEStronglyMeasurable
        (fun z => (gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z)
        (volume.restrict (Metric.ball (0 : Point n) R')) :=
      hcontProd.aestronglyMeasurable measurableSet_ball
    have hmeasNorm : AEStronglyMeasurable
        (fun z => ‖(gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖)
        (volume.restrict (Metric.ball (0 : Point n) R')) := hmeasProd.norm
    -- Pointwise domination of the signed-amplitude norm by `C·‖z‖^k·|Gdiff|`.
    have hptwise : ∀ z ∈ Metric.ball (0 : Point n) R',
        ‖(gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖
          ≤ C * ‖z‖ ^ k
              * |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z| := by
      intro z _hz
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |a s z| ≤ C * ‖z‖ ^ k := ha_bound s z
      calc |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z| * |a s z|
          ≤ |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z| * (C * ‖z‖ ^ k) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = C * ‖z‖ ^ k
              * |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z| := by ring
    have hWintτ := hWint (t - s) hτpos hτε
    have hdomInt : IntegrableOn (fun z : Point n => C * ‖z‖ ^ k *
        |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z|)
        (Metric.ball 0 R') volume := by
      have hscaled := hWintτ.const_mul C
      simpa [mul_assoc] using hscaled
    have habAE : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : Point n) R')),
        ‖(gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖
          ≤ C * ‖z‖ ^ k
              * |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z| := by
      rw [ae_restrict_iff' measurableSet_ball]
      exact ae_of_all _ hptwise
    have hprodInt : IntegrableOn
        (fun z => (gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z)
        (Metric.ball 0 R') volume := Integrable.mono' hdomInt hmeasProd habAE
    have hnormInt : IntegrableOn
        (fun z => ‖(gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖)
        (Metric.ball 0 R') volume := hprodInt.norm
    have hmono : ∫ z in Metric.ball (0 : Point n) R',
          ‖(gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖
        ≤ ∫ z in Metric.ball (0 : Point n) R', C * ‖z‖ ^ k *
              |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z| :=
      setIntegral_mono_on hnormInt hdomInt measurableSet_ball hptwise
    have hstep3 : ∫ z in Metric.ball (0 : Point n) R', C * ‖z‖ ^ k *
          |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z|
        = C * ∫ z in Metric.ball (0 : Point n) R', ‖z‖ ^ k *
              |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z| := by
      rw [← integral_const_mul]
      congr 1
      ext z
      ring
    have hboundτ := chartReplace_sliver_uniform_bound k R' ε hε
      (terminalVelAt g gi hC hK x₀) L' hL' herr' hmin' ck3 hck3nn hWint hmom hτpos hτε
    have hstep1 : ‖∫ z in Metric.ball (0 : Point n) R',
          (gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖
        ≤ ∫ z in Metric.ball (0 : Point n) R',
            ‖(gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖ :=
      norm_integral_le_integral_norm _
    calc ‖∫ z in Metric.ball (0 : Point n) R',
              (gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖
        ≤ ∫ z in Metric.ball (0 : Point n) R',
              ‖(gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖ :=
          hstep1
      _ ≤ ∫ z in Metric.ball (0 : Point n) R', C * ‖z‖ ^ k *
              |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z| := hmono
      _ = C * ∫ z in Metric.ball (0 : Point n) R', ‖z‖ ^ k *
              |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z| := hstep3
      _ ≤ C * M := mul_le_mul_of_nonneg_left hboundτ hC0
  calc ‖∫ s in (t - ε)..t,
          ∫ z in Metric.ball (0 : Point n) R',
            (gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z) * a s z‖
      ≤ C * M * |t - (t - ε)| := intervalIntegral.norm_integral_le_of_norm_le_const_ae hae
    _ = C * M * ε := by rw [show t - (t - ε) = ε by ring, abs_of_pos hε]
    _ = C * (Cshape * (Real.sqrt ε) ^ (k + 3)) := by
        rw [hMdef]
        have hpow : (Real.sqrt ε) ^ (k + 3) = (Real.sqrt ε) ^ (k + 1) * ε := by
          rw [show k + 3 = (k + 1) + 2 from by ring, pow_add, Real.sq_sqrt hε.le]
        rw [hpow]; ring

end QIQTH.HCompNearCarryTerm1AmpSliverBound

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryTerm1AmpSliverBound
#print axioms terminalVelAt_chartReplace_sliver_amp_bound_unconditional
end AxiomChecks
