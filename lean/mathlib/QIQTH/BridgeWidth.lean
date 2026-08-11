/-
  BridgeWidth — J4-619: (i) the WIDTH-GENERAL bridge tail engine (width 2 → general `w`), phrased
  so it consumes the capstone's OWN carried domination shapes (general width `wA`, τ-CAPPED — the
  `hAdomHeat`/`hpkgBound` binder family); (ii) the START of the `hEuni` supplier — the honest
  LANDSCAPE of the uniform all-rows Gaussian domination of the transport defect
  `E = heatOp g^κ gi^κ (vanVleckGatedWitness …)`, with the cheap parts PROVED and the hard part
  honestly mapped.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ★ (i) WIDTH GENERALIZATION.  The J4-618 engine (`BridgeDefect`) was width-2-pinned in exactly
  three places: the mixed-model integrability pair (`FrozenColumn.mixedColZ_integrable` /
  `mixedColS_intervalIntegrable`), the ladder instantiations of the Beta/C–K step (the step lemma
  `gaussTimePow_conv_beta_scaled` itself was ALREADY width-generic), and the final widening
  arithmetic.  This file replays all three at general width `w`:
    ▸ `mixedColZW_integrable` / `mixedColSW_intervalIntegrable` — the `(a,b)` mixed-model pair at
      width `w > 0` (Gaussian product integrability + the scaled semigroup `G_{w·} ∗ G_{w·}`).
    ▸ `heatConv_le_of_abs_le_pos_right_capped` — the domination step with BOTH pointwise bounds
      demanded only on `(0, t)` (τ-CAPPED): the capstone's carried dominations are `τ ≤ T`-gated,
      so the engine must not demand all-τ bounds.  (The banked `_right` variant demanded all τ.)
    ▸ `iterE_column_bound_w` / `leviSeries_column_k3_bound_w` — the mixed ladder and the k ≥ 3
      sub-tail at width `w`, `s ∈ (0,1]`, from τ-capped one-step bounds.
    ▸ ★ `bridgeGenericK2_O_s_w` — k = 2 is O(s)·G_{ws} under the τ-capped uniform O(1) width-`w`
      domination (the Beta step at `(0,0)` is width-agnostic).
    ▸ ★ `bridgeGeneric_tail_O_s_w` — the FULL k ≥ 2 tail is `O(s)·G_{ws}` at ANY `w > 0`;
      ★ `bridgeGeneric_tail_O_s_w_G8` — for `w ∈ [2, 8]` one widening (`G_{ws} ≤ 2ⁿ·G_{8s}`,
      needing `ws ≤ 8s ≤ 4ws`) lands the banked bridge shape `O(s)·G_{8s}`.  HONEST RANGE: the
      single-step widening covers `w ∈ [2,8]`; `w < 2` or `w > 8` would need a chained widening
      (not built here — the capstone's concrete producer is at `wA = 2`, well inside).
    ▸ ★★ `frozenTransportBridge_of_dominations_w` + the capstone-pinned
      `transport_bridge_of_dominations_w` / `transport_corrHigher_of_dominations_w` — the J4-618
      reduction, now consuming width-`w` (`w ∈ [2,8]`), τ-capped dominations.

  ★★ (ii) THE hEuni LANDSCAPE — the finding of this brick.
  1. `hEuni` IS NOT A NEW PILE MEMBER: the capstone's OWN carried Section-C binder `hpkgBound`
     (`∀ t' τ p q, 0 < τ → τ ≤ t' → |E| ≤ C(1+t')·baseKernelW 2 0 τ p q`) is ALREADY an all-rows
     width-2 O(1)-in-τ Gaussian domination; capped at `t' = 1` it yields the engine's τ-capped
     `hEuni` with `C_U = 2C` (`hEuni_of_hpkgBound`).  Hence `transport_bridge_of_pkgBound` /
     `transport_corrHigher_of_pkgBound`: the bridge + bounded-cRem O(t²) API hold under
     {the capstone's own `hpkgBound` carry, the α = −1/2 bound `hEbound`, per-step
     integrability `hInt`} — the all-rows uniform domination is ELIMINATED as a separate
     supplier (it rides on a hypothesis the capstone already carries).  J4-618's "STRICTLY
     STRONGER than hAdomHeat" caveat is thereby RETIRED: hEuni is exactly the `t' = 1` slice of
     `hpkgBound`, not an extra demand.
  2. THE {0}-GATE SUPPLY IS BANKED BUT DEGENERATE: `curvedRNC_heatOp_dom_pkg` (J4-536) proves
     `hpkgBound` — hence `hEuni` (`transport_hEuni_singleton_banked`) — for the genuinely-curved
     witness, but ONLY at base seed `Kset = {0}` (its route runs through the CONST producer's
     `hframeK`, which at `κ ≠ 0` forces the seed to `{0}`: `const_route_frame_forces_singleton`,
     re-pinning J4-582/J4-603).  And at `{0}` the supply is CONTENT-FREE for the bridge: the
     defect vanishes at every off-origin source (`capstoneDefect_singleton_offOrigin_zero`), all
     Levi iterates k ≥ 2 die, the k ≥ 2 transport tail is IDENTICALLY ZERO
     (`transport_tail_singleton_zero`), and the bridge Prop holds OUTRIGHT
     (`frozenTransportBridge_singleton_degenerate`) — a degeneracy pin, NOT progress on fat K.
     Composite: `const_route_fatK_tail_collapse` — ANY attempt to feed the engine through the
     CONST route's `hframeK` at a base containing 0 collapses the transport tail to 0.
  3. THE FAT-K VERDICT (honest obstruction, documented not theorem-ized): at fat `K` the ONLY
     banked all-rows producer is the CONST chain, unavailable by (2).  The center-gauge replay
     (J4-604→607) delivers at layer 4 only `(C₀ + Cεu·ε₀/τ)·G` — NOT O(1)-uniform as `τ ↓ 0` at
     fixed gate — and J4-608's Sol-confirmed diagonal witness (`tr g⁻¹(q) − n ≠ 0`) shows the
     `ε₀/τ` floor is GENUINE for the FLAT-GAUSSIAN (frozen-shape) parametrix defect.  The open
     mathematical question that decides the wall's height: whether the TRANSPORT (van-Vleck)
     parametrix defect — built to cancel the leading singularity — obeys a genuinely better
     per-q bound (classically it is `O(τ⁰)·G`-smooth for N = 1).  Nothing banked proves this:
     the fat-K `hpkgBound`/`hEuni` supplier therefore needs a per-q analysis of the TRANSPORT
     amplitude (a frozen-style J4-609→616 replay for the van-Vleck amplitude with per-q
     recentring), i.e. it is in the SAME difficulty class as the original (hbound-fat) wall —
     no shortcut exists via the banked CONST/center-gauge machinery.  This file's reduction
     narrows the wall to: {`hpkgBound` at fat K (already a capstone carrier), `hEbound`, `hInt`,
     `K1TransportBudget`} — with NO all-rows demand beyond the capstone's own.
     SOL VERDICT (gpt-5.6-sol, consulted with these findings): (α) the accounting in (1) is
     sound — not circular unless `hpkgBound`'s eventual proof invoked this tail engine (it
     does not); (β) exponent bookkeeping confirmed — for the N = 1 (single van-Vleck term)
     parametrix the classical Levi residual is `O(τ⁰)·G` in NORMALIZED-Gaussian form
     (`t^m·(4πt)^{−n/2}e^{−d²/ct}` = `t^m·G_{ct}`, one `t^{−n/2}` only, no dimension penalty),
     PROVIDED the phase is the per-q/geodesic one — and the witness here IS per-q recentered
     (`globalCutoffParametrixWitnessN` evaluates `heatParametrix` at `V_q p`, the per-q inverse
     exp chart — NOT the fixed flat `|p−q|²` phase, which would make fat-K `hpkgBound` FALSE by
     the same `tr g⁻¹(q) − n ≠ 0` diagonal witness).  So fat-K `hpkgBound` is plausibly TRUE
     for this witness; (γ) row-0 + smoothness + compactness does NOT give it (q-derivatives
     carry negative τ-powers); the ONE candidate shortcut at constant curvature is ISOMETRY
     EQUIVARIANCE (hyperbolic space homogeneous; if parametrix/cutoff/gate are equivariant, an
     isometry `q ↦ 0` transfers the banked row-0 analysis to all rows + a uniform metric
     comparison converts to the fixed-coordinate Gaussian) — new work, not banked, but
     potentially far cheaper than the full per-q replay.  Recommended J4-620 probe.

  NON-VACUITY: `bridgeWidth_witness_w2` — the width-general path is JOINTLY inhabited at `w = 2`
  by the banked nonzero `bridgeWitnessKernel` (all antecedents discharged, genuinely curved
  frozen data κ = −1, r = 1/2); `bridgeWitnessKernel_uni_w4` / `bridgeWitnessKernel_bound_w4` —
  the `w ≠ 2` hypothesis slots are individually inhabited at the same nonzero kernel (`w = 4`
  via one widening).  ⚠ The `w ≠ 2` per-step-integrability PRODUCER (the width-`w` analogue of
  `iterConvIntegrableW_of_bound_baseMeas_alpha`) is NOT built — hInt at `w ≠ 2` is a carried
  hypothesis (scoped follow-on); note the engine consumes ONLY the E-side conjuncts (1)–(3) of
  `IterConvIntegrableW`, which are width-free facts about `E` itself.

  ⚠ HONEST FRAMING.  `a₁ = R/6` remains CONDITIONAL: the flat tower is closed and non-vacuous;
  the curved side owes the transport dominations at fat K (`hpkgBound`-at-fat-K — this brick
  maps its true difficulty as (hbound-fat)-class — plus `hEbound`/`hInt` at the transport
  kernel), the k = 1 `K1TransportBudget`, the fat-K carrier piles of the capstone, the full
  capstone co-instantiation, and the prior piles.  Nothing here proves anything about the
  coefficient.  No axioms, no sorry, no `:= True`.
-/
import Mathlib
import QIQTH.BridgeDefect
import QIQTH.CurvedA1ReBase
import QIQTH.CurvedA1FarConsumeCheck
import QIQTH.CurvedRNCHeatOpDomPkg

open Finset Filter Topology MeasureTheory
open scoped Interval
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianWidthTransfer QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.CurvedRNCGaugeBundle QIQTH.FrozenGauss QIQTH.FrozenDefect
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.AlphaLevi QIQTH.FrozenWire QIQTH.FrozenColumn
open QIQTH.FrozenK2 QIQTH.FrozenK2Sharp QIQTH.CoInstSmoke QIQTH.BridgeDefect
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixAnsatz QIQTH.A1R6CoreAtGate

namespace QIQTH.BridgeWidth

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 0. The τ-CAPPED domination step — bounds demanded only on `(0, t)`. -/

/-- **The τ-capped right-column `heatConv` domination step.**  Verbatim
    `FrozenColumn.heatConv_le_of_abs_le_pos_right`, but with BOTH pointwise dominations demanded
    only at times in `(0, t)` — the pointwise step only ever evaluates the bounds at
    `t − s, s ∈ (0, t)`.  This is what lets the engine consume the capstone's τ-CAPPED carried
    dominations (`hAdomHeat`/`hpkgBound` are `τ ≤ T`-gated). -/
theorem heatConv_le_of_abs_le_pos_right_capped
    (A B A' B' : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n) (ht : 0 < t)
    (hA : ∀ τ p q, 0 < τ → τ < t → |A τ p q| ≤ A' τ p q)
    (hB : ∀ τ p, 0 < τ → τ < t → |B τ p y| ≤ B' τ p y)
    (hI1 : IntervalIntegrable (fun s => ‖∫ z, A (t - s) x z * B s z y‖) volume 0 t)
    (hI2 : IntervalIntegrable (fun s => ∫ z, |A (t - s) x z| * |B s z y|) volume 0 t)
    (hIf : ∀ s, Integrable (fun z => |A (t - s) x z| * |B s z y|))
    (hIg : ∀ s, Integrable (fun z => A' (t - s) x z * B' s z y))
    (hIsg : IntervalIntegrable (fun s => ∫ z, A' (t - s) x z * B' s z y) volume 0 t) :
    |heatConv A B t x y| ≤ heatConv A' B' t x y := by
  refine le_trans (heatConv_abs_le A B t x y ht.le hI1 hI2) ?_
  simp only [heatConv]
  refine intervalIntegral.integral_mono_on_of_le_Ioo ht.le hI2 hIsg (fun s hs => ?_)
  obtain ⟨hs0, hst⟩ := hs
  have hts : 0 < t - s := by linarith
  have htslt : t - s < t := by linarith
  refine integral_mono (hIf s) (hIg s) (fun z => ?_)
  have hAz := hA (t - s) x z hts htslt
  have hBz := hB s z hs0 hst
  exact mul_le_mul hAz hBz (abs_nonneg _) (le_trans (abs_nonneg _) hAz)

/-! ### 1. The width-`w` mixed-model `(a, b)` integrability pair. -/

/-- **Width-`w` mixed-model `z`-integrability** — `FrozenColumn.mixedColZ_integrable` at general
    width `w > 0`. -/
theorem mixedColZW_integrable (w a b C₁ C₂ : ℝ) (hw : 0 < w) (t s : ℝ) (x y : Point n) :
    Integrable
      (fun z => C₁ * baseKernelW w a (t - s) x z
        * (C₂ * baseKernelW w b s z y)) volume := by
  by_cases hs : 0 < s ∧ s < t
  · obtain ⟨hs0, hst⟩ := hs
    have hform : (fun z => C₁ * baseKernelW w a (t - s) x z
          * (C₂ * baseKernelW w b s z y))
        = fun z => (C₁ * C₂ * ((t - s) ^ a * s ^ b))
            * (gaussDdim (w * (t - s)) (x - z) * gaussDdim (w * s) (z - y)) := by
      funext z
      simp only [baseKernelW]
      ring
    rw [hform]
    exact (gaussDdim_mul_integrable (w * (t - s)) (w * s) x y).const_mul _
  · rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      exact Integrable.of_finite
    · have hzero : (fun z => C₁ * baseKernelW w a (t - s) x z
            * (C₂ * baseKernelW w b s z y))
          = fun _ => (0 : ℝ) := by
        funext z
        rcases not_and_or.mp hs with h | h
        · push_neg at h
          simp only [baseKernelW]
          rw [gaussDdim_eq_zero_of_nonpos hn1
            (mul_nonpos_of_nonneg_of_nonpos hw.le h) (z - y)]
          ring
        · push_neg at h
          simp only [baseKernelW]
          rw [gaussDdim_eq_zero_of_nonpos hn1
            (mul_nonpos_of_nonneg_of_nonpos hw.le (by linarith)) (x - z)]
          ring
      rw [hzero]
      exact integrable_zero _ _ _

/-- **Width-`w` mixed-model `s`-interval-integrability** (`a, b > −1`) —
    `FrozenColumn.mixedColS_intervalIntegrable` at general width `w > 0`, via the scaled
    Gaussian semigroup `gaussDdim_conv_scaled`. -/
theorem mixedColSW_intervalIntegrable (w a b C₁ C₂ : ℝ) (hw : 0 < w)
    (ha : -1 < a) (hb : -1 < b) (t : ℝ) (ht : 0 < t) (x y : Point n) :
    IntervalIntegrable
      (fun s => ∫ z, C₁ * baseKernelW w a (t - s) x z
        * (C₂ * baseKernelW w b s z y)) volume 0 t := by
  have hg_ii : IntervalIntegrable
      (fun s => (C₁ * C₂ * gaussDdim (w * t) (x - y)) * ((t - s) ^ a * s ^ b)) volume 0 t :=
    (rpow_mul_rpow_intervalIntegrable a b t ha hb ht).const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  have hg : IntegrableOn
      (fun s => (C₁ * C₂ * gaussDdim (w * t) (x - y)) * ((t - s) ^ a * s ^ b))
      (Set.Ioc 0 t) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]; exact hg_ii
  refine hg.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
  intro hmem
  obtain ⟨hs0, hsle⟩ := hmem
  have hsne : s ≠ t := by simpa using hst
  have hst2 : s < t := lt_of_le_of_ne hsle hsne
  have hts : 0 < t - s := by linarith
  have hform : (fun z => C₁ * baseKernelW w a (t - s) x z
        * (C₂ * baseKernelW w b s z y))
      = fun z => (C₁ * C₂ * ((t - s) ^ a * s ^ b))
          * (gaussDdim (w * (t - s)) (x - z) * gaussDdim (w * s) (z - y)) := by
    funext z
    simp only [baseKernelW]
    ring
  show (C₁ * C₂ * gaussDdim (w * t) (x - y)) * ((t - s) ^ a * s ^ b)
      = ∫ z, C₁ * baseKernelW w a (t - s) x z * (C₂ * baseKernelW w b s z y)
  rw [hform, integral_const_mul,
      gaussDdim_conv_scaled w (t - s) s hw hts hs0 x y,
      show (t - s) + s = t from by ring]
  ring

/-! ### 2. The width-`w` mixed ladder — τ-capped one-step bounds, `s ∈ (0,1]`. -/

/-- **The width-`w` τ-capped mixed center-column ladder** — `FrozenColumn.iterE_column_bound`
    at general width `w > 0`, with the one-step bounds demanded only on `(0, 1]` (the
    capstone's carried-domination gate shape); the conclusion is restricted to `s ∈ (0, 1]`
    accordingly (every internal evaluation happens at times `< s ≤ 1`).
    ⚠ Only the E-side conjuncts (1)–(3) of `hInt` are consumed (the model conjuncts are
    width-free facts, unused). -/
theorem iterE_column_bound_w (E : ℝ → Point n → Point n → ℝ) (w C C₀ : ℝ)
    (hw : 0 < w) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ 1 → |E τ p q| ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p q)
    (hEcol : ∀ (τ : ℝ) (p : Point n), 0 < τ → τ ≤ 1 →
      |E τ p 0| ≤ C₀ * gaussDdim (w * τ) (p - 0))
    (hInt : IterConvIntegrableW E w (-(1 / 2) : ℝ) C) :
    ∀ (m : ℕ) (s : ℝ), 0 < s → s ≤ 1 → ∀ p : Point n,
      |iterE E (m + 1) s p 0|
        ≤ colC C C₀ m * s ^ ((m : ℝ) / 2) * gaussDdim (w * s) (p - 0) := by
  intro m
  induction m with
  | zero =>
      intro s hs hs1 p
      rw [show (0 : ℕ) + 1 = 1 from rfl, iterE_one, colC_zero,
          show ((0 : ℕ) : ℝ) / 2 = (0 : ℝ) from by norm_num, Real.rpow_zero, mul_one]
      exact hEcol s p hs hs1
  | succ m ih =>
      intro s hs hs1 p
      have hm1 : 1 ≤ m + 1 := by omega
      obtain ⟨hI1, hI2, hIf, -, -⟩ := hInt (m + 1) hm1 s hs p 0
      -- the τ-capped right-column bound for the inner iterate, in `baseKernelW` shape
      have hB : ∀ (τ : ℝ) (z : Point n), 0 < τ → τ < s →
          |iterE E (m + 1) τ z 0|
            ≤ colC C C₀ m * baseKernelW w ((m : ℝ) / 2) τ z 0 := by
        intro τ z hτ hτs
        have hτ1 : τ ≤ 1 := le_of_lt (lt_of_lt_of_le hτs hs1)
        calc |iterE E (m + 1) τ z 0|
            ≤ colC C C₀ m * τ ^ ((m : ℝ) / 2) * gaussDdim (w * τ) (z - 0) :=
              ih τ hτ hτ1 z
          _ = colC C C₀ m * baseKernelW w ((m : ℝ) / 2) τ z 0 := by
              simp only [baseKernelW]; ring
      have hA : ∀ (τ : ℝ) (p' q' : Point n), 0 < τ → τ < s →
          |E τ p' q'| ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p' q' := by
        intro τ p' q' hτ hτs
        exact hEbound τ p' q' hτ (le_of_lt (lt_of_lt_of_le hτs hs1))
      have hIg : ∀ σ, Integrable
          (fun z => C * baseKernelW w (-(1 / 2) : ℝ) (s - σ) p z
            * (colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z 0)) :=
        fun σ => mixedColZW_integrable w (-(1 / 2)) ((m : ℝ) / 2) C (colC C C₀ m) hw s σ p 0
      have hbge : (-1 : ℝ) < (m : ℝ) / 2 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hIsg : IntervalIntegrable
          (fun σ => ∫ z, C * baseKernelW w (-(1 / 2) : ℝ) (s - σ) p z
            * (colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z 0)) volume 0 s :=
        mixedColSW_intervalIntegrable w (-(1 / 2)) ((m : ℝ) / 2) C (colC C C₀ m) hw
          (by norm_num) hbge s hs p 0
      rw [iterE_succ E hm1]
      simp only [heatConvK_apply]
      have hdom := heatConv_le_of_abs_le_pos_right_capped E (iterE E (m + 1))
        (fun τ p' q' => C * baseKernelW w (-(1 / 2) : ℝ) τ p' q')
        (fun σ z' q' => colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z' q')
        s p 0 hs hA hB hI1 hI2 hIf hIg hIsg
      have hRHS : heatConv
            (fun τ p' q' => C * baseKernelW w (-(1 / 2) : ℝ) τ p' q')
            (fun σ z' q' => colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z' q') s p 0
          = C * colC C C₀ m
              * (s ^ (((m : ℝ) + 1) / 2)
                * (Real.Gamma (1 / 2) * Real.Gamma ((m : ℝ) / 2 + 1)
                    / Real.Gamma ((m : ℝ) / 2 + 3 / 2))
                * gaussDdim (w * s) (p - 0)) := by
        rw [heatConv_smul_left C (baseKernelW w (-(1 / 2)))
              (fun σ z' q' => colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z' q') s p 0,
            heatConv_smul_right (colC C C₀ m) (baseKernelW w (-(1 / 2)))
              (baseKernelW w ((m : ℝ) / 2)) s p 0]
        unfold baseKernelW
        rw [gaussTimePow_conv_beta_scaled w (-(1 / 2)) ((m : ℝ) / 2) hw
              (by norm_num) hbge s hs p 0,
            show (-(1 / 2 : ℝ) + (m : ℝ) / 2 + 1) = ((m : ℝ) + 1) / 2 from by ring,
            show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) from by norm_num,
            show (-(1 / 2 : ℝ) + (m : ℝ) / 2 + 2) = (m : ℝ) / 2 + 3 / 2 from by ring]
        ring
      calc |heatConv E (iterE E (m + 1)) s p 0|
          ≤ heatConv
              (fun τ p' q' => C * baseKernelW w (-(1 / 2) : ℝ) τ p' q')
              (fun σ z' q' => colC C C₀ m * baseKernelW w ((m : ℝ) / 2) σ z' q')
              s p 0 := hdom
        _ = C * colC C C₀ m
              * (s ^ (((m : ℝ) + 1) / 2)
                * (Real.Gamma (1 / 2) * Real.Gamma ((m : ℝ) / 2 + 1)
                    / Real.Gamma ((m : ℝ) / 2 + 3 / 2))
                * gaussDdim (w * s) (p - 0)) := hRHS
        _ = colC C C₀ (m + 1) * s ^ (((m + 1 : ℕ) : ℝ) / 2) * gaussDdim (w * s) (p - 0) := by
            rw [show (((m + 1 : ℕ) : ℝ) / 2) = ((m : ℝ) + 1) / 2 from by push_cast; ring,
                ← colC_succ C C₀ m]
            ring

/-- **The width-`w` k ≥ 3 sub-tail is O(s)** — `FrozenColumn.leviSeries_column_k3_bound` at
    general width `w > 0` with τ-capped one-step bounds. -/
theorem leviSeries_column_k3_bound_w (E : ℝ → Point n → Point n → ℝ) (w C C₀ : ℝ)
    (hw : 0 < w) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ 1 → |E τ p q| ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p q)
    (hEcol : ∀ (τ : ℝ) (p : Point n), 0 < τ → τ ≤ 1 →
      |E τ p 0| ≤ C₀ * gaussDdim (w * τ) (p - 0))
    (hInt : IterConvIntegrableW E w (-(1 / 2) : ℝ) C) :
    ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ p : Point n,
      |leviSeries E s p 0 + E s p 0 - iterE E 2 s p 0|
        ≤ (∑' m : ℕ, colC C C₀ (m + 2)) * (s * gaussDdim (w * s) (p - 0)) := by
  intro s hs hs1 p
  have hG0 : 0 ≤ gaussDdim (w * s) (p - 0) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hterm := iterE_column_bound_w E w C C₀ hw hC hC₀ hEbound hEcol hInt
  have hterm4 : ∀ m : ℕ, |iterE E (m + 1 + 1 + 1) s p 0|
      ≤ colC C C₀ (m + 2) * (s * gaussDdim (w * s) (p - 0)) := by
    intro m
    have hD0 := colC_nonneg C C₀ hC hC₀ (m + 2)
    have hpow : s ^ (((m + 2 : ℕ) : ℝ) / 2) ≤ s := by
      have hexp : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) / 2 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        push_cast
        linarith
      calc s ^ (((m + 2 : ℕ) : ℝ) / 2) ≤ s ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hs hs1 hexp
        _ = s := Real.rpow_one s
    calc |iterE E (m + 1 + 1 + 1) s p 0|
        ≤ colC C C₀ (m + 2) * s ^ (((m + 2 : ℕ) : ℝ) / 2) * gaussDdim (w * s) (p - 0) :=
          hterm (m + 2) s hs hs1 p
      _ ≤ colC C C₀ (m + 2) * s * gaussDdim (w * s) (p - 0) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hD0) hG0
      _ = colC C C₀ (m + 2) * (s * gaussDdim (w * s) (p - 0)) := by ring
  have hterm2 : ∀ m : ℕ, |iterE E (m + 1) s p 0|
      ≤ colC C C₀ m * gaussDdim (w * s) (p - 0) := by
    intro m
    have hpow : s ^ ((m : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one hs.le hs1 (by positivity)
    calc |iterE E (m + 1) s p 0|
        ≤ colC C C₀ m * s ^ ((m : ℝ) / 2) * gaussDdim (w * s) (p - 0) :=
          hterm m s hs hs1 p
      _ ≤ colC C C₀ m * 1 * gaussDdim (w * s) (p - 0) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (colC_nonneg C C₀ hC hC₀ m)) hG0
      _ = colC C C₀ m * gaussDdim (w * s) (p - 0) := by ring
  have hSumCG : Summable (fun m : ℕ => colC C C₀ m * gaussDdim (w * s) (p - 0)) :=
    (colC_summable C C₀ hC hC₀).mul_right _
  have hAbsSum : Summable (fun m : ℕ => |iterE E (m + 1) s p 0|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hterm2 hSumCG
  have hnormeq : (fun m : ℕ => ‖(-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p 0‖)
      = fun m : ℕ => |iterE E (m + 1) s p 0| := by
    funext m
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  have hfSum : Summable (fun m : ℕ => (-1 : ℝ) ^ (m + 1) * iterE E (m + 1) s p 0) :=
    Summable.of_norm (by rw [hnormeq]; exact hAbsSum)
  have hsplit1 : leviSeries E s p 0
      = (-1 : ℝ) ^ (0 + 1) * iterE E (0 + 1) s p 0
        + ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0 := by
    simp only [leviSeries]
    exact hfSum.tsum_eq_zero_add
  have hfSum1 : Summable
      (fun m : ℕ => (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0) :=
    (summable_nat_add_iff 1).mpr hfSum
  have hsplit2 : (∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1) * iterE E (m + 1 + 1) s p 0)
      = (-1 : ℝ) ^ (0 + 1 + 1) * iterE E (0 + 1 + 1) s p 0
        + ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0 :=
    hfSum1.tsum_eq_zero_add
  have hf0 : (-1 : ℝ) ^ (0 + 1) * iterE E (0 + 1) s p 0 = -(E s p 0) := by
    rw [show (0 : ℕ) + 1 = 1 from rfl, iterE_one]
    ring
  have hf1 : (-1 : ℝ) ^ (0 + 1 + 1) * iterE E (0 + 1 + 1) s p 0 = iterE E 2 s p 0 := by
    norm_num
  have htaileq : leviSeries E s p 0 + E s p 0 - iterE E 2 s p 0
      = ∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0 := by
    rw [hsplit1, hsplit2, hf0, hf1]; ring
  have hAbsSum3 : Summable (fun m : ℕ => |iterE E (m + 1 + 1 + 1) s p 0|) := by
    have := (summable_nat_add_iff 2).mpr hAbsSum
    exact this.congr (fun m => by norm_num)
  have hColSum2 : Summable (fun m : ℕ => colC C C₀ (m + 2)) := by
    have := (summable_nat_add_iff 2).mpr (colC_summable C C₀ hC hC₀)
    exact this.congr (fun m => by norm_num)
  have hSumK3 : Summable
      (fun m : ℕ => colC C C₀ (m + 2) * (s * gaussDdim (w * s) (p - 0))) :=
    hColSum2.mul_right _
  have hnormeq3 : (fun m : ℕ => ‖(-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0‖)
      = fun m : ℕ => |iterE E (m + 1 + 1 + 1) s p 0| := by
    funext m
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  calc |leviSeries E s p 0 + E s p 0 - iterE E 2 s p 0|
      = |∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0| := by
        rw [htaileq]
    _ ≤ ∑' m : ℕ, |iterE E (m + 1 + 1 + 1) s p 0| := by
        rw [← Real.norm_eq_abs]
        calc ‖∑' m : ℕ, (-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0‖
            ≤ ∑' m : ℕ, ‖(-1 : ℝ) ^ (m + 1 + 1 + 1) * iterE E (m + 1 + 1 + 1) s p 0‖ :=
              norm_tsum_le_tsum_norm (by rw [hnormeq3]; exact hAbsSum3)
          _ = ∑' m : ℕ, |iterE E (m + 1 + 1 + 1) s p 0| := by rw [hnormeq3]
    _ ≤ ∑' m : ℕ, colC C C₀ (m + 2) * (s * gaussDdim (w * s) (p - 0)) :=
        hAbsSum3.tsum_le_tsum hterm4 hSumK3
    _ = (∑' m : ℕ, colC C C₀ (m + 2)) * (s * gaussDdim (w * s) (p - 0)) := tsum_mul_right

/-! ### 3. ★ The width-`w` k = 2 O(s) bound and the full k ≥ 2 tail. -/

/-- **★ `bridgeGenericK2_O_s_w` — k = 2 is O(s)·G_{ws} under the τ-capped uniform O(1)
    width-`w` domination.**  The Beta step at exponents `(0,0)` is width-agnostic
    (`∫₀ˢ dσ = s`, `G_{w(s−σ)} ∗ G_{wσ} = G_{ws}`).  Width-general, τ-capped replay of
    `BridgeDefect.bridgeGenericK2_O_s` (which was width-2-pinned and demanded all-τ bounds). -/
theorem bridgeGenericK2_O_s_w (E : ℝ → Point n → Point n → ℝ) (w C C_U : ℝ) (hw : 0 < w)
    (hEuni : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C_U * gaussDdim (w * τ) (p - q))
    (hInt : IterConvIntegrableW E w (-(1 / 2) : ℝ) C) :
    ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ p : Point n,
      |iterE E 2 s p 0| ≤ C_U ^ 2 * (s * gaussDdim (w * s) (p - 0)) := by
  intro s hs hs1 p
  obtain ⟨hI1, hI2, hIf, -, -⟩ := hInt 1 le_rfl s hs p 0
  have huniW : ∀ τ (p' q' : Point n), 0 < τ → τ < s →
      |E τ p' q'| ≤ C_U * baseKernelW w (0 : ℝ) τ p' q' := by
    intro τ p' q' hτ hτs
    have hbw : baseKernelW w (0 : ℝ) τ p' q' = gaussDdim (w * τ) (p' - q') := by
      simp only [baseKernelW, Real.rpow_zero, one_mul]
    rw [hbw]
    exact hEuni τ p' q' hτ (le_of_lt (lt_of_lt_of_le hτs hs1))
  have hB : ∀ (τ : ℝ) (z : Point n), 0 < τ → τ < s →
      |iterE E 1 τ z 0| ≤ C_U * baseKernelW w (0 : ℝ) τ z 0 := by
    intro τ z hτ hτs
    rw [iterE_one]
    exact huniW τ z 0 hτ hτs
  have hIg : ∀ σ, Integrable (fun z => C_U * baseKernelW w (0 : ℝ) (s - σ) p z
      * (C_U * baseKernelW w (0 : ℝ) σ z 0)) :=
    fun σ => mixedColZW_integrable w (0 : ℝ) (0 : ℝ) C_U C_U hw s σ p 0
  have hIsg : IntervalIntegrable (fun σ => ∫ z, C_U * baseKernelW w (0 : ℝ) (s - σ) p z
      * (C_U * baseKernelW w (0 : ℝ) σ z 0)) volume 0 s :=
    mixedColSW_intervalIntegrable w (0 : ℝ) (0 : ℝ) C_U C_U hw (by norm_num) (by norm_num)
      s hs p 0
  rw [show (2 : ℕ) = 1 + 1 from rfl, iterE_succ E le_rfl]
  simp only [heatConvK_apply]
  have hdom := heatConv_le_of_abs_le_pos_right_capped E (iterE E 1)
    (fun τ p' q' => C_U * baseKernelW w (0 : ℝ) τ p' q')
    (fun σ z' q' => C_U * baseKernelW w (0 : ℝ) σ z' q')
    s p 0 hs huniW hB hI1 hI2 hIf hIg hIsg
  have hRHS : heatConv (fun τ p' q' => C_U * baseKernelW w (0 : ℝ) τ p' q')
      (fun σ z' q' => C_U * baseKernelW w (0 : ℝ) σ z' q') s p 0
      = C_U ^ 2 * (s * gaussDdim (w * s) (p - 0)) := by
    rw [heatConv_smul_left C_U (baseKernelW w (0 : ℝ))
          (fun σ z' q' => C_U * baseKernelW w (0 : ℝ) σ z' q') s p 0,
        heatConv_smul_right C_U (baseKernelW w (0 : ℝ))
          (baseKernelW w (0 : ℝ)) s p 0]
    unfold baseKernelW
    rw [gaussTimePow_conv_beta_scaled w 0 0 hw (by norm_num) (by norm_num) s hs p 0,
        show ((0 : ℝ) + 0 + 1) = (1 : ℝ) from by norm_num,
        show ((0 : ℝ) + 0 + 2) = (2 : ℝ) from by norm_num,
        show ((0 : ℝ) + 1) = (1 : ℝ) from by norm_num,
        Real.rpow_one, Real.Gamma_one, Real.Gamma_two]
    ring
  calc |heatConv E (iterE E 1) s p 0|
      ≤ heatConv (fun τ p' q' => C_U * baseKernelW w (0 : ℝ) τ p' q')
          (fun σ z' q' => C_U * baseKernelW w (0 : ℝ) σ z' q') s p 0 := hdom
    _ = C_U ^ 2 * (s * gaussDdim (w * s) (p - 0)) := hRHS

/-- **★ `bridgeGeneric_tail_O_s_w` — the FULL k ≥ 2 tail is O(s)·G_{ws} at ANY width
    `w > 0`**, under the τ-capped width-`w` domination pile (α = −1/2 bound + uniform O(1)
    bound + per-step integrability).  The width-general, τ-capped replay of
    `BridgeDefect.bridgeGeneric_tail_O_s` BEFORE the final widening.  ⚠ NOT `a₁ = R/6`. -/
theorem bridgeGeneric_tail_O_s_w (E : ℝ → Point n → Point n → ℝ) (w C C_U : ℝ)
    (hw : 0 < w) (hC : 0 ≤ C) (hCU : 0 ≤ C_U)
    (hEbound : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C_U * gaussDdim (w * τ) (p - q))
    (hInt : IterConvIntegrableW E w (-(1 / 2) : ℝ) C) :
    ∃ C_os : ℝ, 0 ≤ C_os ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |leviSeries E s p 0 + E s p 0| ≤ C_os * (s * gaussDdim (w * s) (p - 0)) := by
  have hEcol : ∀ (τ : ℝ) (p : Point n), 0 < τ → τ ≤ 1 →
      |E τ p 0| ≤ C_U * gaussDdim (w * τ) (p - 0) := fun τ p hτ hτ1 => hEuni τ p 0 hτ hτ1
  have hk3 := leviSeries_column_k3_bound_w E w C C_U hw hC hCU hEbound hEcol hInt
  have hk2 := bridgeGenericK2_O_s_w E w C C_U hw hEuni hInt
  have hsum_nn : 0 ≤ (∑' m : ℕ, colC C C_U (m + 2)) :=
    tsum_nonneg (fun m => colC_nonneg C C_U hC hCU (m + 2))
  refine ⟨(∑' m : ℕ, colC C C_U (m + 2)) + C_U ^ 2,
    add_nonneg hsum_nn (by positivity), fun s p hs hs1 => ?_⟩
  calc |leviSeries E s p 0 + E s p 0|
      = |(leviSeries E s p 0 + E s p 0 - iterE E 2 s p 0) + iterE E 2 s p 0| := by ring_nf
    _ ≤ |leviSeries E s p 0 + E s p 0 - iterE E 2 s p 0| + |iterE E 2 s p 0| := abs_add_le _ _
    _ ≤ (∑' m : ℕ, colC C C_U (m + 2)) * (s * gaussDdim (w * s) (p - 0))
          + C_U ^ 2 * (s * gaussDdim (w * s) (p - 0)) :=
        add_le_add (hk3 s hs hs1 p) (hk2 s hs hs1 p)
    _ = ((∑' m : ℕ, colC C C_U (m + 2)) + C_U ^ 2) * (s * gaussDdim (w * s) (p - 0)) := by
        ring

/-- **★ `bridgeGeneric_tail_O_s_w_G8` — the width-`w` tail in the banked `G_{8s}` bridge
    shape, for `w ∈ [2, 8]`.**  One widening `G_{ws} ≤ 2ⁿ·G_{8s}` (valid iff `ws ≤ 8s ≤ 4ws`,
    i.e. `2 ≤ w ≤ 8` — the HONEST single-step range; the capstone's concrete producer is at
    `wA = 2`, well inside).  ⚠ NOT `a₁ = R/6`. -/
theorem bridgeGeneric_tail_O_s_w_G8 (E : ℝ → Point n → Point n → ℝ) (w C C_U : ℝ)
    (hw2 : 2 ≤ w) (hw8 : w ≤ 8) (hC : 0 ≤ C) (hCU : 0 ≤ C_U)
    (hEbound : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C_U * gaussDdim (w * τ) (p - q))
    (hInt : IterConvIntegrableW E w (-(1 / 2) : ℝ) C) :
    ∃ C_os : ℝ, 0 ≤ C_os ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |leviSeries E s p 0 + E s p 0| ≤ C_os * (s * gaussDdim (8 * s) (p - 0)) := by
  have hw : 0 < w := lt_of_lt_of_le two_pos hw2
  obtain ⟨C_os, hCos, htail⟩ :=
    bridgeGeneric_tail_O_s_w E w C C_U hw hC hCU hEbound hEuni hInt
  refine ⟨C_os * 2 ^ n, by positivity, fun s p hs hs1 => ?_⟩
  have hG8 : 0 ≤ gaussDdim (8 * s) (p - 0) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hwide : gaussDdim (w * s) (p - 0) ≤ 2 ^ n * gaussDdim (8 * s) (p - 0) :=
    gaussDdim_widen_le (w * s) (8 * s) (by positivity)
      (by nlinarith) (by nlinarith) _
  calc |leviSeries E s p 0 + E s p 0|
      ≤ C_os * (s * gaussDdim (w * s) (p - 0)) := htail s p hs hs1
    _ ≤ C_os * (s * (2 ^ n * gaussDdim (8 * s) (p - 0))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwide hs.le) hCos
    _ = (C_os * 2 ^ n) * (s * gaussDdim (8 * s) (p - 0)) := by ring

/-! ### 4. ★★ The width-`w` bridge reduction and its capstone-pinned instantiations. -/

/-- **★★ `frozenTransportBridge_of_dominations_w` — the J4-618 reduction at general width
    `w ∈ [2, 8]`, with τ-CAPPED dominations.**  The owed bridge Prop holds for ANY defect
    kernel under the width-`w` hAdom-family pile — this is the shape the capstone's own
    binders (`hAdomHeat` at width `wA`, `hpkgBound`) actually carry (τ-gated, general width),
    which the width-2 all-τ J4-618 engine could not consume.  ⚠ CONDITIONAL on the carried
    dominations; NOT `a₁ = R/6`. -/
theorem frozenTransportBridge_of_dominations_w (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r)
    (E : ℝ → Point n → Point n → ℝ) (w C C_U : ℝ) (hw2 : 2 ≤ w) (hw8 : w ≤ 8)
    (hC : 0 ≤ C) (hCU : 0 ≤ C_U)
    (hEbound : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C_U * gaussDdim (w * τ) (p - q))
    (hInt : IterConvIntegrableW E w (-(1 / 2) : ℝ) C) :
    FrozenTransportBridge E (frozenDefectKernel K r) := by
  obtain ⟨C_os, hCos, htail⟩ :=
    bridgeGeneric_tail_O_s_w_G8 E w C C_U hw2 hw8 hC hCU hEbound hEuni hInt
  exact QIQTH.BridgeDefect.frozenTransportBridge_of_tail_O_s K r hK hr E C_os hCos htail

/-- **★★ `transport_bridge_of_dominations_w` — the width-`w` bridge at the capstone's OWN
    defect kernel** (`capstoneDefect = heatOp g^κ gi^κ (vanVleckGatedWitness …)`), under
    CARRIED, LABELLED τ-capped width-`w` transport dominations.  ⚠ These remain the owed
    transport-side analytic pile; NOT `a₁ = R/6`. -/
theorem transport_bridge_of_dominations_w (P : FatFrozenPackage n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric P.κ) (curvedRNCInv P.κ) a b c y))
    {Kc : Set (Point n)} (hKc : IsCompact Kc) (S : Point n → Set (Point n)) (a b : ℝ)
    (w C C_U : ℝ) (hw2 : 2 ≤ w) (hw8 : w ≤ 8) (hC : 0 ≤ C) (hCU : 0 ≤ C_U)
    -- ⚠ CARRIED (labelled): the τ-capped width-`w` transport-defect domination pile.
    (hEbound : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |capstoneDefect P.κ hChr hKc S a b τ p q|
        ≤ C * baseKernelW w (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |capstoneDefect P.κ hChr hKc S a b τ p q| ≤ C_U * gaussDdim (w * τ) (p - q))
    (hInt : IterConvIntegrableW (capstoneDefect P.κ hChr hKc S a b)
      w (-(1 / 2) : ℝ) C) :
    FrozenTransportBridge (capstoneDefect P.κ hChr hKc S a b)
      (frozenDefectKernel P.κ P.rS) :=
  frozenTransportBridge_of_dominations_w P.κ P.rS P.hκ.le P.hrS.le
    (capstoneDefect P.κ hChr hKc S a b) w C C_U hw2 hw8 hC hCU hEbound hEuni hInt

/-! ### 5. ★★ THE hEuni SUPPLIER, PART 1 — hEuni RIDES ON the capstone's own `hpkgBound`. -/

/-- **★★ `hEuni_of_hpkgBound` — the uniform all-rows O(1) domination is NOT a new pile
    member.**  The capstone's OWN carried Section-C binder `hpkgBound`
    (`∀ t' τ p q, 0 < τ → τ ≤ t' → |E τ p q| ≤ C(1+t')·baseKernelW 2 0 τ p q`) yields, at the
    slice `t' = 1`, EXACTLY the engine's τ-capped width-2 `hEuni` with `C_U = 2C`.  This
    RETIRES J4-618's "hEuni is STRICTLY STRONGER than the carried hAdomHeat" caveat: the
    all-rows uniform bound rides on a hypothesis the capstone already carries. -/
theorem hEuni_of_hpkgBound (E : ℝ → Point n → Point n → ℝ) (C : ℝ)
    (hpkg : ∀ t' : ℝ, ∀ τ (p q : Point n), 0 < τ → τ ≤ t' →
      |E τ p q| ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ (2 * C) * gaussDdim (2 * τ) (p - q) := by
  intro τ p q hτ hτ1
  have h := hpkg 1 τ p q hτ hτ1
  rw [baseKernelW_zero_apply] at h
  calc |E τ p q| ≤ (C * (1 + 1)) * gaussDdim (2 * τ) (p - q) := h
    _ = (2 * C) * gaussDdim (2 * τ) (p - q) := by ring

/-- **★★ `transport_bridge_of_pkgBound` — the bridge from {the capstone's own `hpkgBound`
    carry, `hEbound`, `hInt`}: hEuni ELIMINATED as a separate supplier.**  The remaining owed
    transport-side pile is exactly {`hpkgBound` (already a capstone carrier — banked at the
    `{0}` seed by J4-536, owed at fat K), the α = −1/2 `hEbound`, per-step integrability
    `hInt`} + the separate `K1TransportBudget`.  ⚠ NOT `a₁ = R/6`. -/
theorem transport_bridge_of_pkgBound (P : FatFrozenPackage n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric P.κ) (curvedRNCInv P.κ) a b c y))
    {Kc : Set (Point n)} (hKc : IsCompact Kc) (S : Point n → Set (Point n)) (a b : ℝ)
    (C_p C_b : ℝ) (hCp : 0 ≤ C_p) (hCb : 0 ≤ C_b)
    -- ⚠ the capstone's OWN Section-C carry shape (`hpkgBound`), verbatim:
    (hpkg : ∀ t' : ℝ, ∀ τ (p q : Point n), 0 < τ → τ ≤ t' →
      |capstoneDefect P.κ hChr hKc S a b τ p q|
        ≤ (C_p * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    -- ⚠ CARRIED (labelled): the α = −1/2 transport bound + per-step integrability.
    (hEbound : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |capstoneDefect P.κ hChr hKc S a b τ p q|
        ≤ C_b * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q)
    (hInt : IterConvIntegrableW (capstoneDefect P.κ hChr hKc S a b)
      (2 : ℝ) (-(1 / 2) : ℝ) C_b) :
    FrozenTransportBridge (capstoneDefect P.κ hChr hKc S a b)
      (frozenDefectKernel P.κ P.rS) :=
  transport_bridge_of_dominations_w P hChr hKc S a b 2 C_b (2 * C_p)
    le_rfl (by norm_num) hCb (by linarith)
    hEbound (hEuni_of_hpkgBound _ C_p hpkg) hInt

/-- **★★ `transport_corrHigher_of_pkgBound` — the capstone-shaped bounded-cRem O(t²) API for
    the transport k ≥ 2 tail, from {`hpkgBound` carry, `hEbound`, `hInt`}** — chained through
    the certified `smoke_bridge_verdict` transfer.  Together with `leviSeries_split`, the
    capstone's `leviSeries E` slot is covered modulo exactly `K1TransportBudget`.
    ⚠ NOT `a₁ = R/6`. -/
theorem transport_corrHigher_of_pkgBound (P : FatFrozenPackage n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric P.κ) (curvedRNCInv P.κ) a b c y))
    {Kc : Set (Point n)} (hKc : IsCompact Kc) (S : Point n → Set (Point n)) (a b : ℝ)
    (C_p C_b : ℝ) (hCp : 0 ≤ C_p) (hCb : 0 ≤ C_b)
    (hpkg : ∀ t' : ℝ, ∀ τ (p q : Point n), 0 < τ → τ ≤ t' →
      |capstoneDefect P.κ hChr hKc S a b τ p q|
        ≤ (C_p * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEbound : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
      |capstoneDefect P.κ hChr hKc S a b τ p q|
        ≤ C_b * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q)
    (hInt : IterConvIntegrableW (capstoneDefect P.κ hChr hKc S a b)
      (2 : ℝ) (-(1 / 2) : ℝ) C_b) :
    ∃ C_t : ℝ, 0 ≤ C_t ∧
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a' : ℝ) (ζ : Point n), 0 < a' →
          |H a' 0 ζ| ≤ C_H * gaussDdim (2 * a') ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        ∀ (pref t : ℝ), 0 < t → t ≤ 1 → pref ≠ 0 →
          (heatConv H (fun σ p q => leviSeries (capstoneDefect P.κ hChr hKc S a b) σ p q
                + capstoneDefect P.κ hChr hKc S a b σ p q) t 0 0
            = pref * (t ^ 2
                * (heatConv H (fun σ p q => leviSeries (capstoneDefect P.κ hChr hKc S a b) σ p q
                      + capstoneDefect P.κ hChr hKc S a b σ p q) t 0 0
                    / (pref * t ^ 2))))
          ∧ |heatConv H (fun σ p q => leviSeries (capstoneDefect P.κ hChr hKc S a b) σ p q
                + capstoneDefect P.κ hChr hKc S a b σ p q) t 0 0|
            ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) * t ^ 2
          ∧ |heatConv H (fun σ p q => leviSeries (capstoneDefect P.κ hChr hKc S a b) σ p q
                + capstoneDefect P.κ hChr hKc S a b σ p q) t 0 0 / (pref * t ^ 2)|
            ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) / |pref| :=
  smoke_bridge_verdict P (capstoneDefect P.κ hChr hKc S a b)
    (transport_bridge_of_pkgBound P hChr hKc S a b C_p C_b hCp hCb hpkg hEbound hInt)

/-! ### 6. ★★ THE hEuni SUPPLIER, PART 2 — the `{0}`-gate supply is BANKED but DEGENERATE. -/

/-- **The transport defect at the singleton seed dies at every off-origin source** — the
    J4-602 collapse mechanism instantiated at `capstoneDefect` with a GENERIC gate `S`.
    NOT `a₁ = R/6`. -/
theorem capstoneDefect_singleton_offOrigin_zero (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (S : Point n → Set (Point n)) (a b τ : ℝ) (p : Point n) {q : Point n} (hq : q ≠ 0) :
    capstoneDefect κ hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b τ p q = 0 := by
  simp only [capstoneDefect, vanVleckGatedWitness]
  exact QIQTH.CurvedA1ReBase.singleton_heatOp_offOrigin_zero
    (curvedRNCMetric κ) (curvedRNCInv κ) _ _ τ p hq

/-- **★ `transport_tail_singleton_zero` — at `K = {0}` the transport k ≥ 2 tail is
    IDENTICALLY ZERO** (`leviSeries E = −E` by the J4-602 collapse pin), so the `{0}`-gate
    `hEuni` supply of J4-536, while a genuine all-rows bound, bounds a kernel whose entire
    Levi tail is absent — the bridge content at `{0}` is empty.  NOT `a₁ = R/6`. -/
theorem transport_tail_singleton_zero (hn : 1 ≤ n) (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (S : Point n → Set (Point n)) (a b s : ℝ) (x y : Point n) :
    leviSeries (capstoneDefect κ hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b) s x y
      + capstoneDefect κ hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b s x y
      = 0 := by
  rw [QIQTH.CurvedA1ReBase.singleton_leviSeries_eq_negE hn _
    (fun τ p {q} hq => capstoneDefect_singleton_offOrigin_zero κ hChr S a b τ p hq) s x y]
  ring

/-- **★ `frozenTransportBridge_singleton_degenerate` — THE DEGENERACY PIN: at the `{0}` seed
    the bridge Prop holds OUTRIGHT** (the transport tail is 0, and the frozen tail alone has
    the banked O(s)·G_{8s} bound).  This is NOT progress on the capstone (which at `{0}` is
    non-co-instantiable with the mass side, J4-582): it pins that the ONLY currently-banked
    `hEuni`/`hpkgBound` supply lands in a regime where the bridge carries no content.
    NOT `a₁ = R/6`. -/
theorem frozenTransportBridge_singleton_degenerate (hn : 1 ≤ n)
    (κf r : ℝ) (hκf : κf ≤ 0) (hr : 0 ≤ r) (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (S : Point n → Set (Point n)) (a b : ℝ) :
    FrozenTransportBridge
      (capstoneDefect κ hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b)
      (frozenDefectKernel κf r) := by
  obtain ⟨C_f, hCf, hf⟩ := frozenColumn_tail_O_s (n := n) κf r hκf hr
  refine ⟨C_f, hCf, fun s p hs hs1 => ?_⟩
  rw [transport_tail_singleton_zero hn κ hChr S a b s p 0, zero_sub, abs_neg]
  exact hf s p hs hs1

/-- **`transport_hEuni_singleton_banked` — the `{0}`-gate hEuni IS banked** (the honest
    supply pin): J4-536's `curvedRNC_heatOp_dom_pkg` delivers the all-rows width-2 uniform
    bound `|E τ p q| ≤ C(1+T)·G_{2τ}(p−q)` on `(0, T]` for the genuinely-curved witness at
    seed `Kset = {0}` — a TRUE, PROVED `hEuni`-shaped statement whose kernel is nonetheless
    degenerate (supported on the `q = 0` column; tail ≡ 0, see above).  NOT `a₁ = R/6`. -/
theorem transport_hEuni_singleton_banked (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hwv : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (T : ℝ) :
    ∃ a b C c : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧
      ∀ (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ T →
        |capstoneDefect κ hChr
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b τ p q|
          ≤ (C * (1 + T)) * gaussDdim (2 * τ) (p - q) := by
  obtain ⟨a, b, C, c, ha, hab, hC, hbc, hpkg, -⟩ :=
    QIQTH.CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg κ hκ hChr hwv T
  refine ⟨a, b, C, c, ha, hab, hC, hbc, fun τ p q hτ hτT => ?_⟩
  simp only [capstoneDefect]
  have h := hpkg T τ p q hτ hτT
  rwa [baseKernelW_zero_apply] at h

/-! ### 7. ★ THE FAT-K OBSTRUCTION PINS — why the banked producer cannot reach fat `K`. -/

/-- **★ `const_route_frame_forces_singleton` — the CONST producer's route to
    `hpkgBound`/`hEuni` is `{0}`-only at the curved witness.**  The banked all-rows producer
    (`gatedWitnessN1_hEboundW_le_lin_CONST` → `curvedRNC_heatOp_dom_pkg`) requires the frame
    hypothesis `hframeK` on its seed compact; at `κ ≠ 0`, `n ≥ 2` (with `0 ∈ K`) that forces
    `K = {0}` — the J4-582/J4-603 finding, re-pinned here as the supply-side obstruction:
    NO fat-K instantiation of the banked `hEuni` route exists.  NOT `a₁ = R/6`. -/
theorem const_route_frame_forces_singleton (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n)
    {K : Set (Point n)} (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j,
      curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0)) :
    K = {(0 : Point n)} :=
  QIQTH.CurvedA1FarConsumeCheck.frameK_forces_singleton κ hκ hn hK0 hframeK

/-- **★ `const_route_fatK_tail_collapse` — the composite obstruction: ANY attempt to feed the
    bridge engine through the CONST route's frame hypothesis collapses the transport tail to
    zero.**  If the seed compact satisfies `hframeK` (the banked producer's demand) and
    contains the center, then at the curved witness (`κ ≠ 0`, `n ≥ 2`) the k ≥ 2 transport
    tail is identically 0 — the bridge obtained this way is the degenerate one, never the
    fat-K bridge the capstone needs.  Hence the fat-K `hEuni`/`hpkgBound` supplier genuinely
    requires a per-q analysis of the TRANSPORT amplitude (the (hbound-fat)-class wall — see
    the header verdict).  NOT `a₁ = R/6`. -/
theorem const_route_fatK_tail_collapse (κ : ℝ) (hκ : κ ≠ 0) (hn2 : 2 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j,
      curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0))
    (S : Point n → Set (Point n)) (a b s : ℝ) (x y : Point n) :
    leviSeries (capstoneDefect κ hChr hK S a b) s x y
      + capstoneDefect κ hChr hK S a b s x y = 0 := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hKeq : K = {(0 : Point n)} :=
    const_route_frame_forces_singleton κ hκ hn2 hK0 hframeK
  subst hKeq
  exact transport_tail_singleton_zero hn1 κ hChr S a b s x y

/-! ### 8. NON-VACUITY — the width-general path is jointly inhabited. -/

/-- **`bridgeWidth_witness_w2` — the width-general reduction is JOINTLY inhabited at
    `w = 2`.**  The banked genuinely-nonzero `bridgeWitnessKernel` discharges ALL antecedents
    of `frozenTransportBridge_of_dominations_w` (τ-capping only WEAKENS the banked all-τ
    proofs), at genuinely curved frozen data `κ = −1`, `r = 1/2` — the width-general
    hypothesis pile is not vacuous.  (⚠ The witness is NOT the transport defect.) -/
theorem bridgeWidth_witness_w2 :
    FrozenTransportBridge (bridgeWitnessKernel (n := n))
      (frozenDefectKernel (-1) (1 / 2)) :=
  frozenTransportBridge_of_dominations_w (-1) (1 / 2) (by norm_num) (by norm_num)
    (bridgeWitnessKernel (n := n)) 2 1 1 le_rfl (by norm_num) zero_le_one zero_le_one
    (fun τ p q hτ _ => bridgeWitnessKernel_bound τ p q hτ)
    (fun τ p q hτ _ => bridgeWitnessKernel_uni τ p q hτ)
    bridgeWitnessKernel_iterConvIntegrable

/-- **The `w ≠ 2` uniform-domination slot is individually inhabited at a nonzero kernel**
    (`w = 4` via one widening `G_{2τ} ≤ 2ⁿ·G_{4τ}`).  ⚠ The width-4 per-step-integrability
    PRODUCER is not built (the banked producer is width-2-pinned), so no full `w = 4` joint
    witness is claimed — honest partial gate. -/
theorem bridgeWitnessKernel_uni_w4 : ∀ τ (p q : Point n), 0 < τ → τ ≤ 1 →
    |bridgeWitnessKernel τ p q| ≤ (2 ^ n : ℝ) * gaussDdim (4 * τ) (p - q) := by
  intro τ p q hτ _
  calc |bridgeWitnessKernel τ p q|
      ≤ 1 * gaussDdim (2 * τ) (p - q) := bridgeWitnessKernel_uni τ p q hτ
    _ = gaussDdim (2 * τ) (p - q) := one_mul _
    _ ≤ 2 ^ n * gaussDdim (4 * τ) (p - q) :=
        gaussDdim_widen_le (2 * τ) (4 * τ) (by linarith) (by linarith) (by linarith) _

end QIQTH.BridgeWidth

-- std-3 verification (chk): READ these outputs — no sorryAx, no extra axioms.
#print axioms QIQTH.BridgeWidth.heatConv_le_of_abs_le_pos_right_capped
#print axioms QIQTH.BridgeWidth.mixedColZW_integrable
#print axioms QIQTH.BridgeWidth.mixedColSW_intervalIntegrable
#print axioms QIQTH.BridgeWidth.iterE_column_bound_w
#print axioms QIQTH.BridgeWidth.leviSeries_column_k3_bound_w
#print axioms QIQTH.BridgeWidth.bridgeGenericK2_O_s_w
#print axioms QIQTH.BridgeWidth.bridgeGeneric_tail_O_s_w
#print axioms QIQTH.BridgeWidth.bridgeGeneric_tail_O_s_w_G8
#print axioms QIQTH.BridgeWidth.frozenTransportBridge_of_dominations_w
#print axioms QIQTH.BridgeWidth.transport_bridge_of_dominations_w
#print axioms QIQTH.BridgeWidth.hEuni_of_hpkgBound
#print axioms QIQTH.BridgeWidth.transport_bridge_of_pkgBound
#print axioms QIQTH.BridgeWidth.transport_corrHigher_of_pkgBound
#print axioms QIQTH.BridgeWidth.capstoneDefect_singleton_offOrigin_zero
#print axioms QIQTH.BridgeWidth.transport_tail_singleton_zero
#print axioms QIQTH.BridgeWidth.frozenTransportBridge_singleton_degenerate
#print axioms QIQTH.BridgeWidth.transport_hEuni_singleton_banked
#print axioms QIQTH.BridgeWidth.const_route_frame_forces_singleton
#print axioms QIQTH.BridgeWidth.const_route_fatK_tail_collapse
#print axioms QIQTH.BridgeWidth.bridgeWidth_witness_w2
#print axioms QIQTH.BridgeWidth.bridgeWitnessKernel_uni_w4
