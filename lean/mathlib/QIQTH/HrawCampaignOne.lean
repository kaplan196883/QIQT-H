/-
  HrawCampaignOne — J4-359: the OPENER of the `hraw` labelled-input campaign (Sol consult #10, wall
  (c); ledger `docs/qg_roadmap/JET4_TOWER_PLAN.md` §§ J4-333/337/358).  The width/target verdict plus
  the first legs toward `GlobalRawBoundFacade.GlobalGatedRawBound`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  RECON + first-legs brick for the LABELLED input `hraw`.  No `sorry` (header prose excepted), no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.  `hraw` remains a NAMED,
  SATISFIABLE labelled residue and `a₁ = R/6` stays CONDITIONAL on the whole convergence / geometric-
  wiring stack AND on `hraw`/`hD2Hexpand`/`hPd2conv`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (H0) — THE THREE RECON VERDICTS.

  Fix the endgame gate `H_G := vanVleckGatedWitness g gi hC hK S a b = gatedKernel K S (…)` and the
  consumer target
      `GlobalGatedRawBound g gi H P : ∀ τ>0, ∀ p q, |heatOp g gi H τ p q| ≤ P·((r²/τ+1)·G_τ(p−q))`,
  `r² = rncRadialSq (p−q)`, `G_c(τ,·) = gaussDdim (c·τ) ·` (width `4c·τ`).  Its consumer is
  `DaLimHardTranche.hEdom_of_gaussPoly_residual` (the BANKED bridge to the width-3/2 residual
  `hEdom`, `E₀ = 13·P`, `E₁ = 0`).

  ── (Q1) THE WIDTH QUESTION — VERDICT: **NO trivial collapse; `hraw` stays the correct entry.** ──────
  The banked in-chart per-base engine `WidthMarginEngine.globalWitness_residual_bound_inChart_final_
  narrow` delivers, UNIFORMLY over `q ∈ K`, a POLYNOMIAL-FREE bound at width EXACTLY `3/2` — but in the
  CHART coordinate `v`:
      `|heatOp g gi H_w τ (φ_q v) q| ≤ B · gaussDdim (3/2·τ) v`   (`‖v‖ < r₀`).
  The consumer `hEdom` wants width `3/2` in the AMBIENT difference `p − q`.  These do NOT collapse: the
  chart→ambient step (`globalWitness_residual_bound_chartGaussian`) needs the near-isometry width budget
  `hdisp : (3/2)·r²_{φv−q} ≤ 2·r²_v` and lands at width `2` (`gaussDdim (2·τ) (p−q)`), STRICTLY WIDER
  than the `3/2` target.  A width-2 upper bound CANNOT be narrowed to width-3/2 pointwise
  (`e^{−r²/8τ}` decays slower than `e^{−r²/6τ}`), so the polynomial-free width-3/2 ambient bound is NOT
  available and `hEdom`-per-base is NOT the engine's ambient output.  The width-1-with-polynomial
  ambient `hraw` remains the DESIGNED entry: (i) it is the natural PRE-COLLAPSE `N=1` shape (one
  derivative hit ⟹ one `r²/τ`); (ii) it feeds the BANKED bridge (→ width-3/2 `hEdom`); (iii)
  chart-transferring the width-1 Gaussian under the near-isometry (`r²_{p−q} ≤ (4/3)·r²_v`) lands at
  ambient width `4/3 < 3/2`, so the design closes exactly where the polynomial-free width-3/2 route
  does not.  `hraw` KEPT LABELLED (matches Sol #10 (c)).  Below, `hEdom_of_polyfree_width` makes the
  general "polynomial-free width `w₀ ≤ 3/2` ⟹ `hEdom`-shape (`E₁=0`)" observation CONCRETE — it is the
  honest reason the collapse would work IF such a narrow ambient bound existed; it does not, so the
  width-1 `hraw` route is the one that actually closes.

  ── (Q2) THE UNIFORMIZATION QUESTION — VERDICT: **the constant is ALREADY uniform over `K`.** ─────────
  In `globalWitness_residual_bound_inChart_final_narrow` the `∃ a b B` binder sits OUTSIDE the `∀ q ∈ K`
  quantifier: `∃ a b B, … ∀ τ q, q ∈ K → 0 < τ → ∃ r₀ > 0, ∀ v, ‖v‖ < r₀ → … ≤ B·gaussDdim(3/2·τ) v`.
  So the amplitude `B` is uniform over `K` BY CONSTRUCTION (it descends from global smooth data on the
  compact `K`, not per-base `.choose`).  No `IsCompact.elim_finite_subcover` extraction of the CONSTANT
  is needed.  The only per-`(τ,q)` existential is `r₀` — the chart-validity radius, a genuine but
  non-opaque near-diagonal neighbourhood radius.  Hence the uniformization is NOT the wall; the real
  infrastructure (per Sol #10 (c)) is the width-1 PRESERVATION through the chart transfer plus the
  ambient global assembly.

  ── (Q3) THE GATE-ASSEMBLY QUESTION — VERDICT: **support = the gate = near-diagonal; far region EMPTY.**
  The gated witness's heat operator VANISHES off the gate: `gatedKernel_heatOp_eq_zero_of_notMem` gives
  `heatOp g gi (gatedKernel K S H) τ p q = 0` whenever `q ∉ K` OR `p ∉ closure (S q)`.  So the global
  `hraw` bound `∀ τ p q, |heatOp| ≤ …` is TRIVIAL off the gate (`0 ≤ nonneg RHS`) and ON the gate
  (`q ∈ K`, `p ∈ closure (S q)`) reduces — via `gatedKernel_heatOp_eq_of_mem_nhds` — to the ungated
  in-chart bound with `p = uniformFlowExp q v` in a `v`-ball.  The support is CONFINED to the gate =
  the near-diagonal flow-ball; the far-off-diagonal region is EMPTY on the support.  The assembly is the
  near-diagonal cover ONLY, plus the trivial off-gate vanishing.  `gatedRawBound_of_onGate` below IS
  this assembly reduction (the global gated target ⟸ the on-gate near-diagonal bound).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (H1) — THE FIRST LEGS.

  •  `gaussDdim_width_mono` — the general width-monotonicity comparison: `gaussDdim (w₀·τ) v ≤
     √(w₁/w₀)ⁿ · gaussDdim (w₁·τ) v` for `0 < w₀ ≤ w₁` (the narrower Gaussian ≤ a bounded multiple of
     the wider one).  Thin diagonal specialization (`v = w`) of the banked chart transfer
     `gaussDdim_le_gaussDdim_chart`.

  •  `hEdom_of_polyfree_width` — the width-parametric `hEdom` entry: from a POLYNOMIAL-FREE ambient
     bound at any width `w₀ ≤ 3/2` (`|heatOp| ≤ P·gaussDdim (w₀·τ) (p−q)`) produce the exact width-3/2
     `hEdom` ∃-shape with `E₁ = 0`.  This is the concrete form of the (Q1) collapse observation.

  •  `gatedWitness_heatOp_eq_zero_offSupport` — the SUPPORT CONFINEMENT: the gated witness's heat
     operator is `0` off the gate (`q ∉ K ∨ p ∉ closure (S q)`).

  •  `gatedRawBound_of_onGate` — the GATE ASSEMBLY reduction: `GlobalGatedRawBound` for the gated
     witness follows from the on-gate near-diagonal bound alone (off-gate handled by the confinement).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GlobalRawBoundFacade
import QIQTH.WidthMarginEngine
import QIQTH.GlobalHunifAssembly

open Set Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.ResidueBound
open scoped Topology BigOperators

namespace QIQTH.HrawCampaignOne

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### (H1·1) — the general width-monotonicity comparison.
    ############################################################################### -/

/-- **★ (H1·1) — `gaussDdim_width_mono`.**  For `0 < w₀ ≤ w₁` and `τ > 0`, the narrower Gaussian is
    dominated by a bounded multiple of the wider one:
        `gaussDdim (w₀·τ) v ≤ √(w₁/w₀)ⁿ · gaussDdim (w₁·τ) v`.
    Thin diagonal (`v = w`) specialization of the banked chart transfer
    `HeatResidualBound.gaussDdim_le_gaussDdim_chart` (the width budget `w₀·r² ≤ w₁·r²` is immediate for
    `w₀ ≤ w₁`, `r² ≥ 0`).  This is the "widen the target Gaussian for free" fact underlying the (Q1)
    collapse analysis.  NOT `a₁ = R/6`. -/
theorem gaussDdim_width_mono {w₀ w₁ : ℝ} (hw₀ : 0 < w₀) (hle : w₀ ≤ w₁) {τ : ℝ} (hτ : 0 < τ)
    (v : Point n) :
    gaussDdim (w₀ * τ) v ≤ Real.sqrt (w₁ / w₀) ^ n * gaussDdim (w₁ * τ) v := by
  have hw₁ : 0 < w₁ := lt_of_lt_of_le hw₀ hle
  have hnorm : w₀ * rncRadialSq v ≤ w₁ * rncRadialSq v :=
    mul_le_mul_of_nonneg_right hle (rncRadialSq_nonneg v)
  exact QIQTH.HeatResidualBound.gaussDdim_le_gaussDdim_chart hw₀ hw₁ hτ hnorm

/-! ###############################################################################
    ### (H1·2) — the polynomial-free width-`w₀` entry into `hEdom`.
    ############################################################################### -/

/-- **★ (H1·2) — `hEdom_of_polyfree_width`.**  THE CONCRETE (Q1) OBSERVATION.  From a POLYNOMIAL-FREE
    ambient residual bound at ANY width `w₀ ≤ 3/2`,
        `hbound : ∀ τ>0, ∀ p q, |heatOp g gi H τ p q| ≤ P·gaussDdim (w₀·τ) (p−q)`   (`P ≥ 0`),
    the exact width-3/2 `hEdom` ∃-shape follows with `E₁ = 0`:
        `∃ E₀ E₁, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ>0, ∀ p q,
            |heatOp g gi H τ p q| ≤ (E₀ + E₁·τ)·√(3/2)ⁿ·gaussDdim (3/2·τ) (p−q)`,
    with `E₀ = P·√(3/2/w₀)ⁿ` (the `√(3/2)ⁿ` cofactor is absorbed via `√(3/2)ⁿ ≥ 1`).  Route: widen
    `gaussDdim (w₀·τ)` to `gaussDdim (3/2·τ)` by `gaussDdim_width_mono`.  This is the honest reason the
    width-collapse WOULD trivialize the campaign IF a polynomial-free ambient bound at width `≤ 3/2`
    existed — it does NOT (Q1 verdict: the chart transfer only delivers width 2), so the width-1
    `hraw` route is the one that actually closes.  NOT `a₁ = R/6`. -/
theorem hEdom_of_polyfree_width (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) {w₀ : ℝ} (hw₀ : 0 < w₀) (hw₀le : w₀ ≤ 3 / 2)
    (P : ℝ) (hP : 0 ≤ P)
    (hbound : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q| ≤ P * gaussDdim (w₀ * τ) (p - q)) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi H τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  refine ⟨P * Real.sqrt (3 / 2 / w₀) ^ n, 0, mul_nonneg hP (by positivity), le_rfl,
    fun τ hτ p q => ?_⟩
  have hcmp : gaussDdim (w₀ * τ) (p - q)
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * gaussDdim (3 / 2 * τ) (p - q) :=
    gaussDdim_width_mono hw₀ hw₀le hτ (p - q)
  have hG0 : 0 ≤ gaussDdim (3 / 2 * τ) (p - q) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hE0 : 0 ≤ P * Real.sqrt (3 / 2 / w₀) ^ n := mul_nonneg hP (by positivity)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (3 / 2) ^ n := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (3 / 2) := by
      have h2 := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      rwa [Real.sqrt_one] at h2
    calc (1 : ℝ) = 1 ^ n := (one_pow n).symm
      _ ≤ Real.sqrt (3 / 2) ^ n := pow_le_pow_left₀ (by norm_num) h1 n
  calc |heatOp g gi H τ p q|
      ≤ P * gaussDdim (w₀ * τ) (p - q) := hbound τ hτ p q
    _ ≤ P * (Real.sqrt (3 / 2 / w₀) ^ n * gaussDdim (3 / 2 * τ) (p - q)) :=
        mul_le_mul_of_nonneg_left hcmp hP
    _ = (P * Real.sqrt (3 / 2 / w₀) ^ n) * gaussDdim (3 / 2 * τ) (p - q) := by ring
    _ ≤ (P * Real.sqrt (3 / 2 / w₀) ^ n)
          * (Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hG0 hsqrt1) hE0
    _ = (P * Real.sqrt (3 / 2 / w₀) ^ n + 0 * τ) * Real.sqrt (3 / 2) ^ n
          * gaussDdim (3 / 2 * τ) (p - q) := by ring

/-! ###############################################################################
    ### (H1·3) — the support confinement of the gated witness.
    ############################################################################### -/

/-- **★ (H1·3) — `gatedWitness_heatOp_eq_zero_offSupport`.**  THE SUPPORT CONFINEMENT.  The heat
    operator of the gated kernel VANISHES off the gate: for `q ∉ K` OR `p ∉ closure (S q)`,
        `heatOp g gi (gatedKernel K S H) τ p q = 0`.
    The `q ∉ K` branch is the banked out-of-`K` vanishing; the `p ∉ closure (S q)` branch produces the
    neighbourhood `{p' | p' ∉ S q} ∈ 𝓝 p` (the open set `(closure (S q))ᶜ ⊆ (S q)ᶜ` contains `p`) and
    applies the banked out-of-gate vanishing `gatedKernel_heatOp_eq_zero_of_notMem`.  This confines the
    support to `{(p,q) | q ∈ K ∧ p ∈ closure (S q)}` = the gate = the near-diagonal flow-ball
    (the (Q3) verdict).  NOT `a₁ = R/6`. -/
theorem gatedWitness_heatOp_eq_zero_offSupport (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (τ : ℝ) (p q : Point n) (h : q ∉ K ∨ p ∉ closure (S q)) :
    heatOp g gi (gatedKernel K S H) τ p q = 0 := by
  rcases h with hq | hp
  · exact QIQTH.HeatResidualBound.gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inl hq)
  · refine QIQTH.HeatResidualBound.gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inr ?_)
    have hopen : IsOpen (closure (S q))ᶜ := isOpen_compl_iff.mpr isClosed_closure
    have hmem : p ∈ (closure (S q))ᶜ := hp
    have hsub : (closure (S q))ᶜ ⊆ {p' : Point n | p' ∉ S q} := by
      intro x hx
      show x ∉ S q
      exact fun hxS => hx (subset_closure hxS)
    exact Filter.mem_of_superset (hopen.mem_nhds hmem) hsub

/-! ###############################################################################
    ### (H1·4) — the gate-assembly reduction to the near diagonal.
    ############################################################################### -/

/-- **★ (H1·4) — `gatedRawBound_of_onGate`.**  THE GATE ASSEMBLY REDUCTION (the (Q3) skeleton): the
    global `GlobalGatedRawBound g gi (gatedKernel K S H) P` (`P ≥ 0`) follows from the ON-GATE
    near-diagonal bound alone,
        `hgate : ∀ τ>0, ∀ q ∈ K, ∀ p ∈ closure (S q),
            |heatOp g gi (gatedKernel K S H) τ p q| ≤ P·((r²/τ + 1)·gaussDdim τ (p−q))`,
    the off-gate region being discharged by `gatedWitness_heatOp_eq_zero_offSupport` (there the LHS is
    `0 ≤` the nonnegative RHS).  This is exactly the (Q3) verdict made a theorem: the `hraw` proof needs
    ONLY the near-diagonal cover; the far-off-diagonal is EMPTY on the support.  NOT `a₁ = R/6`. -/
theorem gatedRawBound_of_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (gatedKernel K S H) τ p q|
          ≤ P * ((rncRadialSq (p - q) / τ + 1) * gaussDdim τ (p - q))) :
    QIQTH.GlobalRawBoundFacade.GlobalGatedRawBound g gi (gatedKernel K S H) P := by
  intro τ hτ p q
  have hRHS : 0 ≤ P * ((rncRadialSq (p - q) / τ + 1) * gaussDdim τ (p - q)) :=
    mul_nonneg hP (mul_nonneg
      (add_nonneg (div_nonneg (rncRadialSq_nonneg _) hτ.le) zero_le_one)
      (QIQTH.ResidueBound.gaussDdim_nonneg _ _))
  by_cases hq : q ∈ K
  · by_cases hp : p ∈ closure (S q)
    · exact hgate τ hτ q hq p hp
    · rw [gatedWitness_heatOp_eq_zero_offSupport g gi K S H τ p q (Or.inr hp), abs_zero]
      exact hRHS
  · rw [gatedWitness_heatOp_eq_zero_offSupport g gi K S H τ p q (Or.inl hq), abs_zero]
    exact hRHS

end QIQTH.HrawCampaignOne

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HrawCampaignOne.gaussDdim_width_mono
#print axioms QIQTH.HrawCampaignOne.hEdom_of_polyfree_width
#print axioms QIQTH.HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport
#print axioms QIQTH.HrawCampaignOne.gatedRawBound_of_onGate
