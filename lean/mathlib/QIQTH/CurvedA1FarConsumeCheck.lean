/-
  CurvedA1FarConsumeCheck — J4-582: a SOUNDNESS PIN on the J4-581 hFar coercivity discharge.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This file records — as std-3 theorems — the ADVERSARIAL
  finding of the J4-582 soundness investigation into whether J4-581's discharge of the hFar
  coercivity (`CurvedA1FintHFarCoercivity.curved_hFar_coercivity_frameK_at_gate`) SOUNDLY consumes
  into the fully-wired curved capstone `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`.

  ── THE MECHANISM J4-581 RELIES ON.  Both J4-581's discharge and the capstone carry the SAME frame
  hypothesis `hframeK : ∀ q ∈ K, curvedRNCMetric κ q = δ` over the SAME chart base set `K` (the set
  the gated kernel `gatedKernel K S H τ p q = if q∈K then (if p∈S q then H τ p q else 0) else 0` gates
  the SOURCE slot `q` by).  For the genuinely-curved witness (`κ ≠ 0`, `n ≥ 2`), `hframeK` forces
  `K ⊆ {0}` (`curvedRNCMetric_frame_forces_origin`); together with the capstone's `hK0 : 0 ∈ K` this
  forces `K = {0}` (`frameK_forces_singleton`).

  ── THE FINDING (why the discharge is NOT a benign "empty annulus").  Collapsing `K = {0}` does not
  merely empty the far-field annulus — it collapses the ENTIRE witness's SOURCE support to the single
  point `{0}` (Lebesgue-null in `Point n = Fin n → ℝ`, `n ≥ 1`), because the gated kernel VANISHES for
  every source point `z ∉ K`.  Hence EVERY base integral `∫ z, H τ 0 z ∂volume` of the witness is
  ZERO (`witness_baseIntegral_zero`).  But the capstone `curved_a1_R6_fully_wired` ALSO carries the
  normalization hypothesis `hmassone : ∫ z, H (εₘ) 0 z → 1`.  A sequence that is identically `0` cannot
  converge to `1`, so `hmassone` is UNSATISFIABLE whenever `hframeK`+`hK0` hold at the curved witness
  (`hmassone_unsatisfiable`).  Therefore the capstone's antecedent bundle `{hframeK, hK0, hmassone}` is
  JOINTLY UNSATISFIABLE for `κ ≠ 0`, `n ≥ 2` — the capstone is VACUOUS exactly at the genuinely-curved
  witness it advertises.  The `_curved_satisfiable` gate only checks the CONCLUSION COEFFICIENT
  (`Ric(0) ≠ 0`), NOT antecedent inhabitation — the axiom-budget blind spot.

  ── VERDICT.  J4-581's `curved_hFar_coercivity_frameK_at_gate` is a CORRECT standalone std-3 lemma,
  and the `K` binders it and the capstone's `hframeK` range over are the SAME (NOT a `constGate`-support
  conflation).  But (i) the discharge is NOT actually consumed by the capstone (the `CurvedA1FintH*`
  hFar chain is not imported by `CurvedA1FullyWiredCapstone`; the capstone carries Gaussian-domination
  binders directly), and (ii) the very `K = {0}` collapse the discharge invokes makes the capstone's
  own normalization hypothesis unsatisfiable at the curved witness.  So J4-581's doc claim that "the a₁
  content is carried by the ∫z Gaussian over ℝⁿ with the constGate(c) witness support" is FALSE when
  `K = {0}`: that ∫z is identically zero.  a₁ = R/6 stays CONDITIONAL — and, at this witness with the
  frame hypothesis, VACUOUSLY so.  ⚠ NOT `a₁ = R/6`.
-/
import QIQTH.CurvedA1FintHFarCoercivity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.A1R6CoreAtGate QIQTH.HeatResidualBound QIQTH.CurvedA1FintHFarCoercivity
open scoped Topology BigOperators ContDiff

namespace QIQTH.CurvedA1FarConsumeCheck

variable {n : ℕ}

/-- **★★★ J4-582 — `frameK_forces_singleton`.**  The capstone's own hypotheses `hK0 : 0 ∈ K` and
    `hframeK : ∀ q ∈ K, curvedRNCMetric κ q = δ` force `K = {0}` at the genuinely-curved witness
    (`κ ≠ 0`, `n ≥ 2`), via `curvedRNCMetric_frame_forces_origin`.  ⚠ NOT `a₁ = R/6`. -/
theorem frameK_forces_singleton (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n)
    {K : Set (Point n)} (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0)) :
    K = {(0 : Point n)} :=
  Set.eq_singleton_iff_unique_mem.mpr
    ⟨hK0, fun q hq => curvedRNCMetric_frame_forces_origin κ hκ hn (hframeK q hq)⟩

/-- **★★★ J4-582 — `witness_baseIntegral_zero`.**  Under the capstone's frame hypotheses at the
    genuinely-curved witness (`κ ≠ 0`, `n ≥ 2`), the base integral of the gated van-Vleck witness
    vanishes IDENTICALLY: `∫ z, H τ 0 z ∂volume = 0`, for every time `τ`.  Because `K = {0}` collapses
    the witness's SOURCE support to the Lebesgue-null singleton `{0}` (the gated kernel vanishes for
    `z ∉ K`).  This is the exact ∫z-over-ℝⁿ integral the a₁ content would have to live in — and it is
    zero.  ⚠ NOT `a₁ = R/6`. -/
theorem witness_baseIntegral_zero (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0))
    (a b c τ : ℝ) :
    (∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z) = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hKeq : K = {(0 : Point n)} := frameK_forces_singleton κ hκ hn hK0 hframeK
  -- off the (collapsed) base set, the gated witness vanishes.
  have hzero : ∀ z : Point n, z ≠ 0 →
      vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z = 0 := by
    intro z hzne
    have hzK : z ∉ K := by rw [hKeq]; simpa using hzne
    simp only [vanVleckGatedWitness]
    exact gatedKernel_apply_of_notMem K _ _ τ (0 : Point n) z (Or.inl hzK)
  -- so the integrand is supported on the null singleton `{0}` and integrates to `0`.
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  have hsub : {z : Point n | vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z ≠ 0}
      ⊆ {(0 : Point n)} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [Set.mem_singleton_iff]
    by_contra hzne
    exact hz (hzero z hzne)
  have hnull : (volume : Measure (Point n)) {z : Point n |
        vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z ≠ 0} = 0 :=
    measure_mono_null hsub (MeasureTheory.measure_singleton (0 : Point n))
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  simpa using hnull

/-- **★★★ J4-582 — `hmassone_unsatisfiable` — THE VACUITY PIN.**  Under the capstone's own frame
    hypotheses at the genuinely-curved witness (`κ ≠ 0`, `n ≥ 2`), the capstone's normalization
    hypothesis `hmassone : ∫ z, H (εₘ) 0 z → 1` is UNSATISFIABLE — the base integrals are identically
    `0` (`witness_baseIntegral_zero`), and a constant-`0` sequence cannot converge to `1`.  Hence the
    antecedent bundle `{hframeK, hK0, hmassone}` of `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`
    is JOINTLY UNSATISFIABLE for `κ ≠ 0`, `n ≥ 2`: the capstone is VACUOUS at the genuinely-curved
    witness.  ⚠ NOT `a₁ = R/6`. -/
theorem hmassone_unsatisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0))
    (a b c : ℝ) :
    ¬ Filter.Tendsto
        (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (epsSeq m) (0 : Point n) z)
        Filter.atTop (𝓝 (1 : ℝ)) := by
  intro htend
  have hfun : (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (epsSeq m) (0 : Point n) z)
      = (fun _ : ℕ => (0 : ℝ)) := by
    funext m
    exact witness_baseIntegral_zero κ hκ hn hChr hK hK0 hframeK a b c (epsSeq m)
  rw [hfun] at htend
  have h0 : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique htend h0)

end QIQTH.CurvedA1FarConsumeCheck

section AxiomChecks
open QIQTH.CurvedA1FarConsumeCheck
#print axioms frameK_forces_singleton
#print axioms witness_baseIntegral_zero
#print axioms hmassone_unsatisfiable
end AxiomChecks
