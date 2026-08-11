/-
  CurvedA1ReBase — J4-602: (A) the DEGENERACY AUDIT of the J4-592→601 `hInnerCont` chain under the
  `K = {0}` singleton pin, sharpened to PROVED collapse lemmas; (B) the START of the RE-BASE of the
  `hInnerCont` carrier at a NON-collapsed base compact `K := Metric.closedBall 0 r` (`r > 0`) for the
  genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; this proves NOTHING about the coefficient.  `a₁ = R/6`
  remains CONDITIONAL — and this brick EXPANDS the honest residual: the re-based `hInnerCont` (and
  with it re-based `hBdom`/`hAdom`/`hmeas`/`hcont` instantiations at the fat base compact) are OWED,
  not banked.  Recording that expansion is the point.

  ── PART A: THE AUDIT (proved, std-3), sharpening J4-601's `curved_innerPairing_zero` pin.
  The J4-592→601 chain (`CurvedA1HInnerCont`/`HContDom`/`HBdom`/`HEmeas`/`ReachAlign`/`HAdom`/`Hmeas`)
  drains the capstone's `hInnerCont` carrier.  The CAPSTONE
  (`CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center`) quantifies over a GENERAL compact `K`
  with only `hK0 : 0 ∈ K` — it is NOT pinned to `{0}`; and its MASS side (J4-591,
  `CurvedA1HmassoneFinal.curved_hmassone_final_at_gate`) carries `hKball : Metric.ball 0 rS ⊆ K`
  (`rS > 0`) — a NON-collapsed `K`.  The J4-592 reduction (`curved_hInnerCont_at_gate`) and the
  J4-596 builder (`curved_hContDom_at_gate` / `ContDomWindow.hContDom_discharged`) are likewise
  GENERAL-`K` engines.  The `{0}` pin enters at J4-597 (`CurvedA1HBdom.curved_hBdom_at_gate`) and is
  inherited by J4-598/599/600/601.  Hence the J4-597→601 closures are DEGENERATE INSTANTIATIONS of
  general binders — inconsistent with the `hKball` mass side (no single `K` can serve both, since the
  mass side forbids `K = {0}` — `CurvedA1FarConsumeCheck` J4-582).  What we PROVE here (all generic in
  the gate `S` and inner kernel `H`, so they classify the chain at once):
    • `singleton_gatedKernel_offOrigin_zero` — at `K = {0}` the gated kernel kills every source
      `q ≠ 0` (restatement of the gate mechanism at all `p`, not just `p = 0`).
    • `singleton_heatOp_offOrigin_zero` — hence the DEFECT kernel `E = heatOp g gi W` also vanishes
      at every source `q ≠ 0` (`heatOp` is inert in `q`; both germs are identically 0).
    • `singleton_heatConvK_zero` — a Duhamel convolution whose LEFT factor vanishes off the null
      source `{0}` is IDENTICALLY 0 (inner `z`-integral of an a.e.-zero integrand, `n ≥ 1`).
    • `singleton_iterE_ge_two_zero` — so ALL Levi/Neumann iterates `E^{*k}`, `k ≥ 2`, vanish.
    • `singleton_leviSeries_eq_negE` — ★★ THE COLLAPSE PIN: at `K = {0}` the "Levi series" is
      LITERALLY `−E` — a single defect term; the Neumann/Volterra tail is ABSENT.  So the J4-597/599
      `hBdom` conclusion (`|leviSeries …| ≤ C_L·gaussDdim`) is at this witness a bound on ONE
      first-order defect kernel, NOT on a genuine series; and
    • `singleton_leviSeries_offSlice_zero` — off the `y = 0` slice it is a bound on the CONSTANT 0.
  AUDIT TABLE (documented verdicts; the lemmas above are the proofs):
    J4-592 `curved_hInnerCont_at_gate`      — GENERIC ENGINE (general `K`); retains full value.
    J4-596 `curved_hContDom_at_gate` /
           `curved_hInnerCont_of_dominations` — GENERIC ENGINE (general `K`); the BUILDER retains
           value; its `hContDom` conclusion INSTANTIATED at `{0}` is dominated-continuity of an
           a.e.-0 integrand (degenerate instance of a live engine).
    J4-597 `curved_hBdom_at_gate`           — {0}-PINNED.  Conclusion = Gaussian bound on
           `leviSeries = −E` (single defect term, `y=0` slice only; ≡0 off it): PARTIAL content
           (first-order defect bound survives; series content ABSENT).
    J4-598 `curved_hEmeas_at_gate`          — {0}-PINNED.  Triple measurability of a kernel that is
           nontrivial ONLY on the `q = 0` slice: weak content; the REQUANT quantifier architecture
           (`∃δ₀` before `∀a,b`; `ReachRequant`) is generic and retains value.
    J4-599 `curved_hBdom_unconditional`     — {0}-PINNED; same classification as J4-597; the
           prescribed-ceiling joint-production pattern is generic and retains value.
    J4-600 `curved_hAdom_hBdom_at_gate`     — {0}-PINNED.  `hAdom` (`|W τ p q| ≤ Gauss`) is
           trivially true off `q = 0`; content only on the frozen-source `q = 0` slice.
    J4-601 `curved_hInnerCont_closed`       — {0}-PINNED; DEGENERATE (continuity of the constant-0
           pairing; already pinned by `curved_innerPairing_zero`).
  LOAD-BEARING VERDICT: the capstone binder is GENERAL-`K`; J4-592's chain instantiated it
  degenerately.  The RE-BASE (this file, part B) — not a capstone repair — is the real work.

  ── PART B: THE RE-BASE START (proved, std-3), at `K := Metric.closedBall 0 r`, `r > 0`.
    • `rebased_ball_subset` / `rebased_base_pos_measure` — the CO-INSTANTIATION CERTIFICATE: the fat
      base compact contains `Metric.ball 0 r` (so J4-591's `hKball` is satisfiable at `rS := r` for
      the SAME `K` — mass side and `hInnerCont` side can finally share one `K`), and it has POSITIVE
      Lebesgue measure (`n ≥ 1`) — the a.e.-source-kill mechanism of the audit CANNOT apply.
    • `rebased_gate_source_open` — the structural non-collapse: on the whole ball the `q`-gate is
      OPEN (the gated witness agrees with the ungated parametrix wherever the spatial gate holds);
      the collapse mechanism is confined to the complement of `K`.
    • `rebased_hmeas_at_gate` — ★★ THE FIRST RE-BASED CARRIER: the `hmeas` z-slice eventual
      measurability of the inner pairing `z ↦ W(u−s) 0 z · L s z 0` at the FAT base compact, from
      the banked reach-conditional witness-slice supplier `CurvedRNCChartReach.curvedRNC_hWmeas_carryFree`
      (produces `ρ` then `δ₀` with the gate radius `c < δ₀` — the J4-599/600 prescribed-ceiling
      production shape) times the Levi z-slice supplier `CurvedA1ClassBMeas7.leviSlice_meas` (single
      labelled carry `hLcont`, spatial continuity of the Levi slice), composed by
      `AEStronglyMeasurable.mul`.  Conditional on TWO honest inputs: the geometric REACH of the
      origin from the ball (`ExpRhoReachability`-family genuine input) and `hLcont`.  At THIS `K`
      the pairing is NOT forced to vanish — the carrier is analytic again.
  SCOPE OF REMAINDER (honest): re-based `hcont`, `hAdom`/`hBdom` (now GENUINE Gaussian dominations of
  a witness/Levi series with fat source support — the real analytic wall), `hContDom` assembly, and
  the co-instantiated capstone application at `K = closedBall 0 r` are NOT here.  They are the owed
  re-based residual, deliberately recorded as OPEN.

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedent (each hypothesis is
  satisfiable and none is the conclusion), no existing file edited except the `QIQTH.lean` /
  `AxiomAudit.lean` wiring, nothing committed.
-/
import Mathlib
import QIQTH.CurvedA1Hmeas
import QIQTH.CurvedRNCChartReach
import QIQTH.CurvedA1ClassBMeas7

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.ExpMap
open scoped Topology

namespace QIQTH.CurvedA1ReBase

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### PART A — the proved degeneracy audit of the `K = {0}` pin.  Generic in `S`, `H`. -/

/-- **A1 — the singleton gate kills every off-origin source, at EVERY `p`.**  (J4-601 proved this at
    `p = 0`; the audit needs all `p` to classify the width-2 `hBdom`/`hAdom` conclusions.)  NOT
    `a₁ = R/6`. -/
theorem singleton_gatedKernel_offOrigin_zero (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p : Point n) {q : Point n} (hq : q ≠ 0) :
    gatedKernel ({(0 : Point n)} : Set (Point n)) S H τ p q = 0 :=
  gatedKernel_apply_of_notMem _ _ _ τ p q (Or.inl (by simpa using hq))

/-- **A2 — the DEFECT kernel of the singleton-gated witness vanishes at every off-origin source.**
    `heatOp` differentiates only in `(τ, p)`; at `q ≠ 0` both germs of the gated kernel are
    identically `0`, so `E τ p q = 0`.  NOT `a₁ = R/6`. -/
theorem singleton_heatOp_offOrigin_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (τ : ℝ) (p : Point n) {q : Point n} (hq : q ≠ 0) :
    heatOp g gi (gatedKernel ({(0 : Point n)} : Set (Point n)) S H) τ p q = 0 := by
  refine heatOp_eq_zero_of_locally_zero g gi _ τ p q ?_ ?_
  · exact Filter.Eventually.of_forall
      (fun t => singleton_gatedKernel_offOrigin_zero S H t p hq)
  · exact Filter.Eventually.of_forall
      (fun p' => singleton_gatedKernel_offOrigin_zero S H τ p' hq)

/-- **A3 — a Duhamel convolution with an off-origin-dead LEFT factor is IDENTICALLY zero** (`n ≥ 1`:
    the source support `{0}` is Lebesgue-null, so the inner `z`-integral dies, hence the outer
    `s`-integral).  NOT `a₁ = R/6`. -/
theorem singleton_heatConvK_zero (hn : 1 ≤ n) (E F : ℝ → Point n → Point n → ℝ)
    (hE : ∀ (τ : ℝ) (p : Point n) {q : Point n}, q ≠ 0 → E τ p q = 0)
    (t : ℝ) (x y : Point n) :
    heatConvK E F t x y = 0 := by
  rw [heatConvK_apply]
  unfold heatConv
  have hinner : ∀ s : ℝ, (∫ z, E (t - s) x z * F s z y) = 0 := by
    intro s
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    filter_upwards [QIQTH.CurvedA1Hmeas.offOrigin_ae hn] with z hz
    rw [hE (t - s) x hz, zero_mul]
    rfl
  simp only [hinner, intervalIntegral.integral_zero]

/-- **A4 — all Levi/Neumann iterates of order `≥ 2` vanish at the singleton pin.**  NOT
    `a₁ = R/6`. -/
theorem singleton_iterE_ge_two_zero (hn : 1 ≤ n) (E : ℝ → Point n → Point n → ℝ)
    (hE : ∀ (τ : ℝ) (p : Point n) {q : Point n}, q ≠ 0 → E τ p q = 0)
    (m : ℕ) (t : ℝ) (x y : Point n) :
    iterE E (m + 2) t x y = 0 := by
  have hstep : (iterE E (m + 2) : ℝ → Point n → Point n → ℝ)
      = heatConvK E (iterE E (m + 1)) :=
    iterE_succ E (k := m + 1) (by omega)
  rw [hstep]
  exact singleton_heatConvK_zero hn E (iterE E (m + 1)) hE t x y

/-- **★★ A5 — THE LEVI-SERIES COLLAPSE PIN.**  At the singleton pin the "Levi series" is LITERALLY
    minus the single defect kernel: `leviSeries E = −E` pointwise.  The Neumann/Volterra tail (every
    iterate of order ≥ 2, and with it all series/summability content) is ABSENT.  Consequence for the
    audit: the J4-597/599 `hBdom` conclusion (`|leviSeries …| ≤ C_L·gaussDdim`) is, at the `K = {0}`
    witness, a Gaussian bound on ONE first-order defect term — partial content, NOT a series bound.
    NOT `a₁ = R/6`. -/
theorem singleton_leviSeries_eq_negE (hn : 1 ≤ n) (E : ℝ → Point n → Point n → ℝ)
    (hE : ∀ (τ : ℝ) (p : Point n) {q : Point n}, q ≠ 0 → E τ p q = 0)
    (t : ℝ) (x y : Point n) :
    leviSeries E t x y = -E t x y := by
  unfold leviSeries
  rw [tsum_eq_single 0 (fun k hk => ?_)]
  · simp [iterE_one]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [singleton_iterE_ge_two_zero hn E hE m t x y, mul_zero]

/-- **A6 — off the `y = 0` slice the singleton-pinned Levi series is the CONSTANT 0** (so there the
    J4-597/599 width-2 domination bounds the constant-0 function).  NOT `a₁ = R/6`. -/
theorem singleton_leviSeries_offSlice_zero (hn : 1 ≤ n) (E : ℝ → Point n → Point n → ℝ)
    (hE : ∀ (τ : ℝ) (p : Point n) {q : Point n}, q ≠ 0 → E τ p q = 0)
    (t : ℝ) (x : Point n) {y : Point n} (hy : y ≠ 0) :
    leviSeries E t x y = 0 := by
  rw [singleton_leviSeries_eq_negE hn E hE t x y, hE t x hy, neg_zero]

/-- **A7 — the audit instantiated at the CONCRETE J4-597→601 witness**: the defect kernel of the
    singleton-gated curved van-Vleck witness dies at every off-origin source, so A5/A6 apply verbatim
    to the chain's `leviSeries (heatOp g^K gi^K W)`.  NOT `a₁ = R/6`. -/
theorem curved_singleton_defect_offOrigin_zero (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (a b c : ℝ) (τ : ℝ) (p : Point n) {q : Point n} (hq : q ≠ 0) :
    heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)
      τ p q = 0 := by
  simp only [vanVleckGatedWitness]
  exact singleton_heatOp_offOrigin_zero (curvedRNCMetric κ) (curvedRNCInv κ) _ _ τ p hq

/-! ### PART B — the re-base at the NON-collapsed base compact `K := Metric.closedBall 0 r`. -/

/-- **B1 — the co-instantiation certificate, ball side.**  `Metric.ball 0 r ⊆ Metric.closedBall 0 r`:
    J4-591's mass-side gate-activation carrier `hKball : ball 0 rS ⊆ K` is satisfiable at `rS := r`
    for the SAME re-based `K` — the mass side and the `hInnerCont` side can finally share one base
    compact (impossible at `K = {0}`).  NOT `a₁ = R/6`. -/
theorem rebased_ball_subset (r : ℝ) :
    Metric.ball (0 : Point n) r ⊆ Metric.closedBall (0 : Point n) r :=
  Metric.ball_subset_closedBall

/-- **B2 — the co-instantiation certificate, measure side.**  The re-based base compact has POSITIVE
    Lebesgue measure (`n ≥ 1`, `r > 0`): the a.e.-source-kill mechanism of the audit (support in a
    null set) CANNOT apply at this `K`.  NOT `a₁ = R/6`. -/
theorem rebased_base_pos_measure (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    0 < (volume : Measure (Point n)) (Metric.closedBall (0 : Point n) r) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : Point n) hr)
    (measure_mono Metric.ball_subset_closedBall)

open Classical in
/-- **B3 — the structural non-collapse of the `q`-gate.**  On the WHOLE re-based ball the `q`-gate is
    OPEN: for every source `z ∈ closedBall 0 r` the gated kernel agrees with the spatially-gated
    ungated kernel (`if p ∈ S z then H τ p z else 0`) — the off-origin kill mechanism of the audit is
    confined to the complement of `K`.  Stated for the abstract `gatedKernel`, hence for the concrete
    witness by `simp only [vanVleckGatedWitness]`.  NOT `a₁ = R/6`. -/
theorem rebased_gate_source_open (r : ℝ) (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p : Point n)
    {z : Point n} (hz : z ∈ Metric.closedBall (0 : Point n) r) :
    gatedKernel (Metric.closedBall (0 : Point n) r) S H τ p z
      = if p ∈ S z then H τ p z else 0 := by
  simp only [gatedKernel, if_pos hz]

/-- **★★ B4 — `rebased_hmeas_at_gate` — THE FIRST RE-BASED `hInnerCont` CARRIER.**  The `hmeas`
    z-slice eventual measurability of the inner pairing `z ↦ W(u−s) 0 z · L s z 0` at the
    NON-collapsed base compact `K := Metric.closedBall 0 r` (`r > 0`) for the genuinely-curved
    witness `g^K = curvedRNCMetric κ` (`κ < 0`) — the EXACT `hmeas` binder shape of the J4-596
    general-`K` builder (`CurvedA1HContDom.curved_hContDom_at_gate`), instantiated at the fat `K`
    where (by B1/B2) the pairing is NOT forced to vanish.

    Production shape (the J4-599/600 prescribed-ceiling lesson): the banked reach-conditional
    supplier `CurvedRNCChartReach.curvedRNC_hWmeas_carryFree` produces `ρ` FIRST; GIVEN the genuine
    geometric reach input (origin reachable from every `z ∈ closedBall 0 r` with velocity `< ρ` —
    the `ExpRhoReachability`-family input), it produces a uniform gate reach `δ₀` valid for every
    gate radius `0 < c < δ₀`; at each such `c`, GIVEN the single labelled Levi-slice continuity carry
    `hLcont`, the pairing slice is `AEStronglyMeasurable` for every `u ∈ U`, `s₀ ∈ Ioo 0 u`,
    eventually (in fact everywhere) in `s`: witness slice (supplier) × Levi slice
    (`CurvedA1ClassBMeas7.leviSlice_meas`) via `AEStronglyMeasurable.mul`.

    ⚠ CONDITIONAL on {reach, `hLcont`} — both genuine, neither the conclusion, neither vacuous
    (the reach is satisfiable geometry; `hLcont` is the honest Levi-regularity wall).  NOT
    `a₁ = R/6`. -/
theorem rebased_hmeas_at_gate (κ r : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (a b : ℝ) (U : Set ℝ) :
    ∃ ρ > (0 : ℝ),
      (∀ z ∈ Metric.closedBall (0 : Point n) r, ∃ v : Point n, ‖v‖ < ρ ∧
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          (isCompact_closedBall (0 : Point n) r) z v = 0) →
      ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
        (∀ u' : ℝ, Continuous
          (fun z => leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_closedBall (0 : Point n) r)
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_closedBall (0 : Point n) r) c) a b)) u' z (0 : Point n))) →
        ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
          AEStronglyMeasurable
            (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_closedBall (0 : Point n) r)
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  (isCompact_closedBall (0 : Point n) r) c) a b (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                  (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                    (isCompact_closedBall (0 : Point n) r)
                    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                      (isCompact_closedBall (0 : Point n) r) c) a b)) s z 0)
            (volume : Measure (Point n)) := by
  obtain ⟨ρ, hρ, himpl⟩ :=
    QIQTH.CurvedRNCChartReach.curvedRNC_hWmeas_carryFree κ hκ hChr
      (isCompact_closedBall (0 : Point n) r) a b
  refine ⟨ρ, hρ, fun hReach => ?_⟩
  obtain ⟨δ₀, hδ₀, hWslice⟩ := himpl hReach
  refine ⟨δ₀, hδ₀, fun c hc hcδ hLcont => ?_⟩
  intro u _ s₀ _
  refine Filter.Eventually.of_forall (fun s => ?_)
  exact (hWslice c hc hcδ (u - s)).mul
    (QIQTH.CurvedA1ClassBMeas7.leviSlice_meas (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      (isCompact_closedBall (0 : Point n) r)
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        (isCompact_closedBall (0 : Point n) r) c) a b hLcont s)

/-- **★ B5 — the usual curvature gate**: the re-based witness metric is GENUINELY curved for
    `κ < 0`, `n ≥ 2` (`∃ w, 1 < det g^K w`) — the re-base changes the BASE COMPACT, not the metric.
    Re-exports the banked certificate.  NOT `a₁ = R/6`. -/
theorem rebased_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  QIQTH.CurvedA1Hmeas.curved_hmeas_satisfiable κ hκ hn

end QIQTH.CurvedA1ReBase

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1ReBase

#print axioms singleton_gatedKernel_offOrigin_zero
#print axioms singleton_heatOp_offOrigin_zero
#print axioms singleton_heatConvK_zero
#print axioms singleton_iterE_ge_two_zero
#print axioms singleton_leviSeries_eq_negE
#print axioms singleton_leviSeries_offSlice_zero
#print axioms curved_singleton_defect_offOrigin_zero
#print axioms rebased_ball_subset
#print axioms rebased_base_pos_measure
#print axioms rebased_gate_source_open
#print axioms rebased_hmeas_at_gate
#print axioms rebased_satisfiable

end AxiomChecks
