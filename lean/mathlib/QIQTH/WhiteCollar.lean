/-
  WhiteCollar — J4-630: THE WHITENED COLLAR — `hOffS` DISCHARGED (and the `hOffS2` shape
  pre-discharged) at the concrete flow-ball gates, making the J4-629 `hP1` slot UNCONDITIONAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still
  owes: S1-b (the `hP2` second field-`pd` slot) + S1-c (the E3d assembly at the whitened witness)
  + `hlam8` (`lam ≤ 8`, opaque `C₀`) + `K1TransportBudget` + the fat-`K` carrier piles + the
  capstone co-instantiation at the whitened witness + the prior analytic piles.  This brick is the
  COLLAR only: it removes the single carried `hOffS` input of `white_hP1_concrete`.

  ── THE MECHANISM VERDICT (the J4-630 question answered): the whitened collar is **FREE from the
     banked CONTRACTION** — NO whitening-frame operator-norm estimate is needed.  The J4-629
     docstring anticipated "a uniform-on-`K` norm bound for the whitening frame `E_q`"; the actual
     discharge needs only the banked κ≤0 radial contraction, applied at the inverse velocity:
       • the cutoff reads `V̂ = whiteInvChart_q x = E_q⁻¹ v` (with `v = uniformInverseChart_q x`
         the RAW chart velocity, `x = φ_q v` on the gate);
       • `χ_{a,b}(V̂) ≠ 0 ⟹ rncRadialSq V̂ < b²` (`radialCutoff_eq_zero`);
       • THE ONE EXTRA STEP vs the as-built collar (`OffSVanishing`, J4-235):
           `rncRadialSq v = rncRadialSq (E_q (E_q⁻¹ v)) ≤ rncRadialSq (E_q⁻¹ v) = rncRadialSq V̂`
         via the banked contraction `whiteVel_radialSq_le` (κ ≤ 0: `E_q` radially contracts) at
         `whiteVel_whiteUnvel` (`E_q ∘ E_q⁻¹ = id`, banked J4-626/WhiteAnnulus) — EXACTLY the
         J4-626 frontier-leg expansion trick, reused at the support ball instead of the frontier;
       • hence `‖v‖ < b < c ⟹ x ∈ φ_q '' ball 0 b`, whose CLOSURE sits inside the gate
         `S q = φ_q '' ball 0 c` (the banked `huniformChart` closed-map conjunct at radius `b`) —
         so every `p ∉ S q` lies in the OPEN complement of that closure, on which the gated
         witness is IDENTICALLY `0` (gate kills off-`S`, cutoff kills the collar).
     Local vanishing ⟹ all field-`pd`s vanish (`pd_congr_of_eventuallyEq` + `pd_const`; iterate
     via `eventually_eventually_nhds` for the second — line-for-line the J4-235 template).

  ── DELIVERED:
       ▸ `whiteCut_locally_zero_offGate` — the collar lemma: for `q ∈ K`, `p ∉ S q` (concrete
         flow-ball gate, radii `0 < a < b < c < δ₀`), the whitened gated witness's field slot is
         `≡ 0` on a NEIGHBOURHOOD of `p` (every `τ`, including `τ ≤ 0`).
       ▸ ★ `white_hOffS_discharged` — the EXACT `hOffS` shape of `white_hP1_concrete`
         (first field-`pd` vanishes off-gate) as a THEOREM.
       ▸ ★ `white_hOffS2_discharged` — the mixed-second-`pd` analogue (the `hOffS2` shape the
         S1-b/`hP2` successor will consume), same mechanism one level up.
       ▸ ★★ `white_hP1_unconditional` — J4-629's `white_hP1_concrete` with `hOffS` DISCHARGED:
         the `hP1` E3d slot at the concrete flow-ball gates with NO carried measurability-side
         input (radii `0 < a < b < c < δ₀` carried honestly, as in the as-built J4-235).
       ▸ non-vacuity gates §4 (radius-window satisfiability at any `δ₀`, expansion-direction pin,
         inhabited gate + nonzero measured object re-exports).

  ── RADII, carried HONESTLY: `0 < a < b < c < δ₀` with `δ₀` the banked uniform chart radius
     (`uniformInverseChart_huniformChart`) — the same discipline as the as-built collar; the
     window `(b, δ₀)` is nonempty exactly when `b < δ₀` (the radii are free parameters chosen at
     assembly time; §4 gate 1 certifies the constraint system is satisfiable for EVERY `δ₀ > 0`).

  No `sorry`, no `admit`, no new axioms, no `:= True`; no existing file edited except the
  `QIQTH.lean` / `AxiomAudit.lean` wiring.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteS1P1
import QIQTH.WhiteAnnulus

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.RNCDecay
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.EquivProbe
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteS1
open QIQTH.WhiteS1P1 QIQTH.WhiteAnnulus
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace QIQTH.WhiteCollar

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ###############################################################################
    ### §1 — the collar lemma: local vanishing of the whitened gated witness off-gate.
    ############################################################################### -/

/-- **The whitened collar** (`whiteCut_locally_zero_offGate`) — at the concrete flow-ball gate
    `S q = uniformFlowExp_q '' ball 0 c` (radii `0 < a < b < c < δ₀`), for every `q ∈ K` and
    every field point `p ∉ S q`, the field slot of the whitened GATED witness is identically `0`
    on a NEIGHBOURHOOD of `p`, for every `τ`.

    The J4-235 support-closure argument with ONE extra whitening step: on the gate, `x = φ_q v`
    with `W_q x = v` (banked germ left-inverse) and the cutoff reads `V̂ = E_q⁻¹ v`; if
    `χ_{a,b}(V̂) ≠ 0` then `rncRadialSq V̂ < b²`, and the banked κ≤0 CONTRACTION
    `whiteVel_radialSq_le` at `E_q(E_q⁻¹ v) = v` (`whiteVel_whiteUnvel`) gives
    `rncRadialSq v ≤ rncRadialSq V̂ < b²`, hence `‖v‖ < b` — so the support sits inside
    `φ_q '' ball 0 b`, whose closure `⊆ S q` (banked `huniformChart` closed-map conjunct).
    Every `p ∉ S q` therefore lies in the open complement of that closure, where the gate kills
    the off-`S` part and the cutoff kills the collar.  NO whitening-frame norm bound is needed.
    NOT `a₁ = R/6`. -/
theorem whiteCut_locally_zero_offGate (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) →
        ∀ (τ : ℝ) (q : Point n), q ∈ Kset → ∀ p : Point n, p ∉ S q →
          (fun x => whiteGatedWitness κ hκ hKc S a b τ x q) =ᶠ[nhds p] (fun _ => 0) := by
  obtain ⟨δ₀, hδ₀pos, hspec⟩ := uniformInverseChart_huniformChart (curvedRNCMetric κ)
    (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ S hSeq τ q hq p hpS
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  have hbδ : b < δ₀ := lt_trans hbc hcδ
  -- per-`q` chart data.
  obtain ⟨hgerm, hball⟩ := hspec q hq
  obtain ⟨_hOpenb, hclosb⟩ := hball b hb0 hbδ
  -- `S q = φ_q '' ball 0 c`.
  have hSq : S q = uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) c := by rw [hSeq]
  -- closure of the `b`-support-ball image `⊆ S q`.
  have hsub : closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) b) ⊆ S q := by
    rw [hSq]
    exact hclosb.trans (Set.image_mono (Metric.closedBall_subset_ball hbc))
  -- `p` is in the OPEN complement of that closure.
  set U := (closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) b))ᶜ with hUdef
  have hUopen : IsOpen U := isOpen_compl_iff.mpr isClosed_closure
  have hpU : p ∈ U := fun h => hpS (hsub h)
  refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) ?_
  intro x hxU
  -- `x ∉ φ_q '' ball 0 b`.
  have hxNotBall : x ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q '' Metric.ball (0 : Point n) b :=
    fun h => hxU (subset_closure h)
  -- compute the witness value.
  show whiteGatedWitness κ hκ hKc S a b τ x q = 0
  show gatedKernel Kset S (whiteCutKernel κ hκ hKc a b) τ x q = 0
  by_cases hxS : x ∈ S q
  · -- on the gate: the radial cutoff kills the value, via the CONTRACTION.
    rw [gatedKernel_apply_of_mem Kset S _ τ hq hxS]
    rw [hSq] at hxS
    obtain ⟨v, hv, hvx⟩ := hxS
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    -- germ left-inverse: `W_q x = v`.
    have hWqv : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q v) = v := by
      have hh := ((hgerm v (lt_trans hvc hcδ)).1).eq_of_nhds
      simpa using hh
    have hWqx : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q x = v := by rw [← hvx]; exact hWqv
    -- the whitened chart value at `x` is `E_q⁻¹ v`.
    have hval : whiteInvChart κ hκ hKc q x = whiteUnvel κ q v := by
      show whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q x) = whiteUnvel κ q v
      rw [hWqx]
    -- the cutoff at `E_q⁻¹ v` vanishes (else `x ∈ φ_q '' ball 0 b`, by the contraction).
    have hcut0 : radialCutoff a b (whiteUnvel κ q v) = 0 := by
      by_contra hne
      have hlt : rncRadialSq (whiteUnvel κ q v) < b ^ 2 := by
        by_contra hge
        exact hne (radialCutoff_eq_zero ha hab (not_lt.mp hge))
      -- ⚠ THE CONTRACTION STEP (direction VERIFIED, not assumed):
      -- `rncRadialSq v = rncRadialSq (E_q (E_q⁻¹ v)) ≤ rncRadialSq (E_q⁻¹ v)` for κ ≤ 0.
      have hcontr : rncRadialSq v ≤ rncRadialSq (whiteUnvel κ q v) := by
        have h4 := whiteVel_radialSq_le κ hκ q (whiteUnvel κ q v)
        rwa [whiteVel_whiteUnvel κ hκ q v] at h4
      have hvb2 : rncRadialSq v < b ^ 2 := lt_of_le_of_lt hcontr hlt
      have hsqle : ‖v‖ * ‖v‖ ≤ rncRadial v * rncRadial v :=
        mul_le_mul (norm_le_rncRadial v) (norm_le_rncRadial v) (norm_nonneg v)
          (rncRadial_nonneg v)
      have hnv2 : ‖v‖ ^ 2 < b ^ 2 := by
        have hsq := rncRadial_sq v
        nlinarith [hsqle, hvb2, hsq]
      have hnvb : ‖v‖ < b := lt_of_pow_lt_pow_left₀ 2 hb0.le hnv2
      exact hxNotBall ⟨v, mem_ball_zero_iff.mpr hnvb, hvx⟩
    simp only [whiteCutKernel, hval, hcut0, zero_mul]
  · -- off the gate: the `S`-gate kills the value.
    exact gatedKernel_apply_of_notMem Kset S _ τ x q (Or.inr hxS)

/-! ###############################################################################
    ### §2 — the `hOffS` / `hOffS2` discharges (exact `white_hP1_concrete` binder shapes).
    ############################################################################### -/

/-- **★ `white_hOffS_discharged`** — the EXACT `hOffS` binder shape of J4-629's
    `white_hP1_concrete` as a THEOREM: at the concrete flow-ball gate (radii
    `0 < a < b < c < δ₀`), for every direction `k` and every `w` with `w.2.2 ∈ K`, `0 < w.1`,
    `w.2.1 ∉ S w.2.2`, the raw first field-`pd` of the whitened gated witness vanishes.  From the
    collar via `pd_congr_of_eventuallyEq` + `pd_const` (the J4-235 `hOffS_concrete` template).
    NOT `a₁ = R/6`. -/
theorem white_hOffS_discharged (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (ha : 0 < a) (hab : a < b) (k : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 →
        w.2.1 ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
        pd (fun x : Point n => whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          w.1 x w.2.2) k w.2.1 = 0 := by
  obtain ⟨δ₀, hδ₀pos, hcollar⟩ := whiteCut_locally_zero_offGate κ hκ hKc a b ha hab
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ w hzK _hτ hpS
  have hEq := hcollar c hbc hcδ
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) rfl
    w.1 w.2.2 hzK w.2.1 hpS
  rw [pd_congr_of_eventuallyEq _ _ k w.2.1 hEq]
  exact pd_const 0 k w.2.1

/-- **★ `white_hOffS2_discharged`** — the MIXED SECOND field-`pd` analogue (the `hOffS2` shape
    the S1-b/`hP2` successor will consume): at the concrete flow-ball gate, for every `i j` and
    every off-gate `w`, `pd_i (pd_j (whitened gated witness)) = 0` — the collar one level up
    (`eventually_eventually_nhds` + `pd_congr_of_eventuallyEq` twice + `pd_const`; the J4-235
    `hOffS2_concrete` template).  NOT `a₁ = R/6`. -/
theorem white_hOffS2_discharged (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (ha : 0 < a) (hab : a < b) (i j : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → 0 < w.1 →
        w.2.1 ∉ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c →
        pd (fun y : Point n => pd (fun x : Point n => whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          w.1 x w.2.2) j y) i w.2.1 = 0 := by
  obtain ⟨δ₀, hδ₀pos, hcollar⟩ := whiteCut_locally_zero_offGate κ hκ hKc a b ha hab
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ w hzK _hτ hpS
  have hEq := hcollar c hbc hcδ
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) rfl
    w.1 w.2.2 hzK w.2.1 hpS
  -- one level up: the first `pd` is `0` on a neighbourhood of `w.2.1`.
  have hEq2 : (fun y : Point n => pd (fun x : Point n => whiteGatedWitness κ hκ hKc
      (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
      w.1 x w.2.2) j y) =ᶠ[nhds w.2.1] (fun _ => 0) := by
    have hnest := (eventually_eventually_nhds (p := fun x =>
      (fun x : Point n => whiteGatedWitness κ hκ hKc
        (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
        w.1 x w.2.2) x = (fun _ => (0 : ℝ)) x)).mpr hEq
    filter_upwards [hnest] with y hy
    rw [pd_congr_of_eventuallyEq _ _ j y hy]
    exact pd_const 0 j y
  rw [pd_congr_of_eventuallyEq _ _ i w.2.1 hEq2]
  exact pd_const 0 i w.2.1

/-! ###############################################################################
    ### §3 — ★★ the unconditional `hP1` slot.
    ############################################################################### -/

/-- **★★ `white_hP1_unconditional` — the J4-629 `hP1` slot with `hOffS` DISCHARGED.**  At the
    concrete flow-ball gates (radii `0 < a < b < c < δ₀`), the whitened gated witness's first
    field-`pd` derivative field is jointly strongly measurable — the exact `hP1` antecedent of
    `HEmeasBorelAudit.triple_hEmeas_of_borel_deriv_fields` at `G := whiteGatedWitness`, with NO
    carried measurability-side input: chart rep, gate measurability, gate openness, on-gate `pd`
    representative (all J4-629) AND the off-`S` collar (this file) are all discharged from
    geometry.  Radii carried honestly (`b < c < δ₀` here vs `0 < c < δ₀` in J4-629 — the collar
    needs the support radius `b` strictly inside the gate radius `c`).  NOT `a₁ = R/6`. -/
theorem white_hP1_unconditional (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (ha : 0 < a) (hab : a < b) (k : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        pd (fun x : Point n => whiteGatedWitness κ hκ hKc
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc z '' Metric.ball (0 : Point n) c) a b
          w.1 x w.2.2) k w.2.1) := by
  obtain ⟨δ₁, hδ₁, hP1⟩ := white_hP1_concrete hn κ hκ hKc a b k
  obtain ⟨δ₂, hδ₂, hOff⟩ := white_hOffS_discharged κ hκ hKc a b ha hab k
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro c hbc hcδ
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  exact hP1 c hc0 (lt_of_lt_of_le hcδ (min_le_left _ _))
    (hOff c hbc (lt_of_lt_of_le hcδ (min_le_right _ _)))

/-! ###############################################################################
    ### §4 — Non-vacuity / adversarial gates (cp466 discipline).
    ############################################################################### -/

/-- **Gate 1 — the radius window is SATISFIABLE at every chart radius**: for EVERY `δ₀ > 0` there
    exist radii `0 < a < b < c < δ₀` — the collar's constraint system is never contradictory (the
    radii are free parameters chosen at assembly time AFTER the chart radius is known; the banked
    chart radius is strictly positive, `uniformInverseChart_huniformChart`).  ⚠ HONEST: for a
    FIXED `(a,b)` chosen before the chart radius, `b < δ₀` is not provable (`δ₀` opaque) — the
    same carried discipline as the as-built J4-235 collar. -/
theorem white_collar_radii_satisfiable :
    ∀ δ₀ : ℝ, 0 < δ₀ → ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧ c < δ₀ :=
  fun δ₀ hδ₀ => ⟨δ₀ / 8, δ₀ / 4, δ₀ / 2, by linarith, by linarith, by linarith, by linarith⟩

/-- **Gate 2 — the expansion-direction pin** (the NO-FALSE-CLAIM check on the contraction step):
    the direction actually consumed by the collar is
        `rncRadialSq v ≤ rncRadialSq (E_q⁻¹ v)`   (κ ≤ 0, all `q`, all `v`)
    — the whitening INVERSE radially EXPANDS (equivalently: `E_q` contracts, applied at
    `E_q(E_q⁻¹ v) = v`).  Stated and proved standalone so the direction is pinned as a theorem,
    not an assumption inside a larger proof.  NOT `a₁ = R/6`. -/
theorem white_collar_expansion_pin (κ : ℝ) (hκ : κ ≤ 0) (q v : Point n) :
    rncRadialSq v ≤ rncRadialSq (whiteUnvel κ q v) := by
  have h := whiteVel_radialSq_le κ hκ q (whiteUnvel κ q v)
  rwa [whiteVel_whiteUnvel κ hκ q v] at h

/-- **Gate 3 — the discharged `hOffS` is about a NONZERO object**: re-export of the J4-628/J4-629
    object gate — at the genuinely curved fat witness (`n = 2`, `κ = −1`, `K = closedBall 0 2`,
    concrete flow-ball gate, cutoff `1 < 2`) the whitened gated witness is strictly positive on
    the origin diagonal for every `τ > 0`; the collar kills the kernel OFF the gate, not the
    kernel.  NOT `a₁ = R/6`. -/
theorem white_collar_underlying_nonzero :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ →
      0 < whiteGatedWitness (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2)
        (fun z => uniformFlowExp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
          (curvedRNC_hChr (-1 : ℝ) (by norm_num))
          (isCompact_closedBall (0 : Point 2) 2) z '' Metric.ball (0 : Point 2) c)
        1 2 τ 0 0 :=
  QIQTH.WhiteS1P1.white_hP1_underlying_nonzero

/-- **Gate 4 — the full gate stays INHABITED at the unconditional slot** (the strong-measurability
    conclusion is not about an indicator over `∅`): re-export of the J4-628 gate at the concrete
    flow-ball gates.  NOT `a₁ = R/6`. -/
theorem white_collar_gate_nonempty (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) {q : Point n} (hq : q ∈ Kset) (c : ℝ) (hc : 0 < c) (τ : ℝ) :
    (τ, uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q 0, q)
      ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ Kset ∧
          w.2.1 ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w.2.2 '' Metric.ball (0 : Point n) c} :=
  QIQTH.WhiteS1P1.white_hP1_gate_nonempty κ hκ hKc hq c hc τ

end QIQTH.WhiteCollar

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteCollar
#print axioms QIQTH.WhiteCollar.whiteCut_locally_zero_offGate
#print axioms QIQTH.WhiteCollar.white_hOffS_discharged
#print axioms QIQTH.WhiteCollar.white_hOffS2_discharged
#print axioms QIQTH.WhiteCollar.white_hP1_unconditional
#print axioms QIQTH.WhiteCollar.white_collar_radii_satisfiable
#print axioms QIQTH.WhiteCollar.white_collar_expansion_pin
#print axioms QIQTH.WhiteCollar.white_collar_underlying_nonzero
#print axioms QIQTH.WhiteCollar.white_collar_gate_nonempty
end AxiomChecks
