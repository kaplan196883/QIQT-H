/-
  HunifTrichotomy — J4-98: DISCHARGING the geometric trichotomy `htri` of J4-97
  (`GlobalHunifAssembly.lean`) for the CONCRETE gated witness, closing the `hunif`/`hEboundW`
  reduction of the recenter capstone down to a single, isolated geometric containment.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What J4-97 left, and what this file delivers (ns `QIQTH.HeatResidualBound`; NO `sorry`).

  J4-97 reduced the width-2 residual primitive `hEboundW` (for the GATED kernel `gatedKernel K S H`)
  to a single geometric TRICHOTOMY `htri`: for `q ∈ K`, `τ > 0`, every `p`, either the gate `S q` is a
  neighborhood of `p` and the ungated bound holds at `p`, OR the gate is locally OFF `p`.  The header
  of J4-97 identified two missing pieces: (W1) chart-image openness and (W2) the cutoff-support ⊆
  transport-radius containment.

  This file delivers:

    * (T1) `basepointChart_exists_strong` — the CHART-IMAGE OPENNESS exposure (W1).  Re-derives the
      base-point IFT `OpenPartialHomeomorph e` of `φ_q = uniformFlowExp g gi hC hK q` (the same one
      whose `symm` J4-93 buried behind `basepointInverseChart`), but now EXPOSES the structured data:
      `e` (open source/target, injective-on-source, symm continuous on target, open-image API),
      `⇑e = φ_q` as a total function, and an explicit ball `ball 0 δ ⊆ e.source`.  Unconditional.

    * (T2) `gatedKernel_uniform_perBasePoint_of_cover` / `gatedKernel_hEboundW_of_cover` — the honest
      3-LEG COVER variant of J4-97's G3/G4.  J4-97's 2-leg trichotomy is provably too coarse at the
      gate FRONTIER (a point `p ∈ closure (S q) \ S q` satisfies neither leg).  The frontier is covered
      by a THIRD leg: the witness kernel `H(τ,·,q)` is LOCALLY ZERO near `p` (the cutoff collar), so the
      gated `heatOp` vanishes.  Given the 3-leg cover, the gated kernel obeys the FULL per-base-point
      width-2 family and the consumer-ready `hEboundW` shape.  Unconditional reduction.
      Helper: `gatedKernel_heatOp_eq_zero_of_kernel_locally_zero`.

    * (T3, reduction) `gatedWitness_cover_of_good` / `gatedWitness_hEboundW_of_good` — the CONCRETE gate
      `S q := φ_q '' (ball 0 c)` (open by T1) with the 3-leg cover DISCHARGED from ONE isolated
      geometric hypothesis `hgood` (below), using T1 for openness/frontier structure,
      `basepointInverseChart_spec` (J4-93) for collar continuity, and the J4-96 uniform bound for the
      in-gate leg.  Delivers the exact `hEboundW` primitive shape for the concrete witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## FIREWALL — the single isolated input `hgood` (binding, honest).

  `hgood` packages, per `q ∈ K`, ONE radius `c` with `b < c` on which BOTH (a) the τ-UNIFORM in-chart
  Gaussian bound holds (`∀ τ>0, ∀ ‖v‖<c, |heatOp H_w τ (φ_q v) q| ≤ B·gaussDdim (2τ)(φ_q v − q)`) AND
  (b) the base-point chart germ radius reaches `c`.  This is EXACTLY the residue flagged by J4-97's
  firewall as (W2): the cutoff support radius `b` (`GlobalResidualWitness` selects `b` from annulus
  suppliers) is not forced by the transport radius `r₀ = min ρ₀ (uniformFlowRadius)`, and J4-96 exposes
  `r₀` only INSIDE the `∀ τ` binder (a τ-free VALUE, but existentially bound per `(τ,q)`).  Closing
  `hgood` = a τ-uniform-radius restatement of the J4-96 chain PLUS the geometric radius ordering
  `b < r₀`.  T1 (chart openness) is discharged UNCONDITIONALLY here; only the radius containment `hgood`
  remains.  `hgood` is genuine, satisfiable (flat `g`: `φ_q v = q + v`, all radii `= +∞`), and strictly
  weaker than the (global, all-`p`) gated conclusion it feeds.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GlobalHunifAssembly
import QIQTH.UniformFlowLocalInverse
import QIQTH.CutoffAnnulusSupport

open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open QIQTH.RadialDistance QIQTH.RNCDecay
open Set Filter
open scoped BigOperators Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### (T1) Chart-image openness — the base-point IFT partial homeomorph, structured data exposed. -/

/-- **★ T1 (W1) — the STRONG base-point inverse chart: openness exposed.**  Building Mathlib's IFT
    `OpenPartialHomeomorph e` of `φ_q = uniformFlowExp g gi hC hK q` at the diagonal point `v = 0` gives a
    genuine local homeomorphism whose structured data is now EXPOSED (unlike `basepointChart_exists`,
    which hid `e` behind `.choose` and surfaced only the left-inverse germ + `C²`):
      * `⇑e = φ_q` as a TOTAL function (the IFT coe identity),
      * `e.source`/`e.target` OPEN, `e` injective on source, `e.symm` continuous on target, and the
        open-image API `isOpen_image_of_subset_source` — all inherited from `OpenPartialHomeomorph`,
      * an explicit ball `Metric.ball 0 δ ⊆ e.source`.
    This is the invariance-of-domain surrogate (`φ_q` is an OPEN map near `0`) that J4-97 flagged as the
    missing W1 for the in-gate `S q ∈ 𝓝 p` branch.  Hypotheses ONLY `hC` + `IsCompact K` (unconditional).
    Mirrors `basepointChart_exists`'s IFT construction but keeps `e` in the existential. -/
theorem basepointChart_exists_strong (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) :
    ∃ (e : OpenPartialHomeomorph (Point n) (Point n)) (δ : ℝ), 0 < δ ∧
      (⇑e = uniformFlowExp g gi hC hK q) ∧
      Metric.ball (0 : Point n) δ ⊆ e.source := by
  obtain ⟨ρ₀, hρ₀pos, hnondeg⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  have hRpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have h0R : ‖(0 : Point n)‖ < uniformFlowRadius g gi hC hK := by rw [norm_zero]; exact hRpos
  have h0ρ : ‖(0 : Point n)‖ < ρ₀ := by rw [norm_zero]; exact hρ₀pos
  have hf0 : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK q) 0 :=
    contDiffAt2_uniformFlowExp g gi hC hK q hq 0 h0R
  have hU0 : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) 0) := hnondeg q hq 0 h0ρ
  set fe0 : Point n ≃L[ℝ] Point n := ContinuousLinearEquiv.ofUnit hU0.unit with hfe0
  have hcoe0 : (fe0 : Point n →L[ℝ] Point n) = fderiv ℝ (uniformFlowExp g gi hC hK q) 0 := by
    apply ContinuousLinearMap.ext; intro x
    have h1 : (fe0 : Point n →L[ℝ] Point n) x = (hU0.unit : Point n →L[ℝ] Point n) x := rfl
    rw [h1, hU0.unit_spec]
  have hf'0 : HasFDerivAt (uniformFlowExp g gi hC hK q) (fe0 : Point n →L[ℝ] Point n) 0 := by
    rw [hcoe0]; exact (hf0.differentiableAt (by norm_num)).hasFDerivAt
  set e := hf0.toOpenPartialHomeomorph (uniformFlowExp g gi hC hK q) hf'0 hn2 with hedef
  have hcoee : (⇑e : Point n → Point n) = uniformFlowExp g gi hC hK q := by
    rw [hedef]; exact hf0.toOpenPartialHomeomorph_coe hf'0 hn2
  have h0src : (0 : Point n) ∈ e.source := by
    rw [hedef]; exact hf0.mem_toOpenPartialHomeomorph_source hf'0 hn2
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.isOpen_iff.mp e.open_source 0 h0src
  exact ⟨e, δ₁, hδ₁pos, hcoee, hδ₁sub⟩

/-! ### (T2) The 3-leg cover variant of J4-97's G3 — frontier covered by the cutoff-collar leg. -/

/-- **T2 (collar leg) — the gated `heatOp` vanishes where the base kernel is locally zero.**  If the
    witness kernel `H` is locally `0` in BOTH slots at `(τ,p)` (time germ at `τ`, space germ at `p`),
    then so is the gated kernel `gatedKernel K S H` (the set-gate can only zero things further), hence
    `heatOp g gi (gatedKernel K S H) τ p q = 0` by `heatOp_eq_zero_of_locally_zero` (J4-94).  This is the
    engine of the FRONTIER leg: on the cutoff collar `radialCutoff a b (W p') = 0` for `p'` near `p` and
    ALL times, so `H_w(·,·,q)` is locally zero in both slots there. -/
theorem gatedKernel_heatOp_eq_zero_of_kernel_locally_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (τ : ℝ) (p q : Point n)
    (htau : (fun t => H t p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ)))
    (hspace : (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ))) :
    heatOp g gi (gatedKernel K S H) τ p q = 0 := by
  refine heatOp_eq_zero_of_locally_zero g gi (gatedKernel K S H) τ p q ?_ ?_
  · -- time germ of the gated kernel at `p`.
    by_cases hq : q ∈ K
    · by_cases hp : p ∈ S q
      · filter_upwards [htau] with t ht
        rw [gatedKernel_apply_of_mem K S H t hq hp]; exact ht
      · exact Filter.Eventually.of_forall
          (fun t => gatedKernel_apply_of_notMem K S H t p q (Or.inr hp))
    · exact Filter.Eventually.of_forall
        (fun t => gatedKernel_apply_of_notMem K S H t p q (Or.inl hq))
  · -- space germ of the gated kernel near `p`.
    by_cases hq : q ∈ K
    · filter_upwards [hspace] with p' hp'
      by_cases hp'S : p' ∈ S q
      · rw [gatedKernel_apply_of_mem K S H τ hq hp'S]; exact hp'
      · exact gatedKernel_apply_of_notMem K S H τ p' q (Or.inr hp'S)
    · exact Filter.Eventually.of_forall
        (fun p' => gatedKernel_apply_of_notMem K S H τ p' q (Or.inl hq))

/-- **★★ T2 — the GATED per-base-point Gaussian family from the 3-LEG geometric COVER.**

    The honest replacement for J4-97's G3.  For each `q ∈ K`, `τ > 0`, `p`, ONE of THREE legs holds:
      (1) `S q ∈ 𝓝 p` and the UNgated bound holds at `p`  (in-gate),
      (2) `{p' | p' ∉ S q} ∈ 𝓝 p`  (off-gate),
      (3) `H(·,·,q)` is locally `0` in both slots at `(τ,p)`  (cutoff collar / frontier).
    Then the gated kernel obeys the FULL per-base-point width-2 family over ALL `q` (the `q ∉ K` zero
    leg included) and ALL `p`.  Leg (1) transfers by G2a, leg (2) vanishes by G2b, leg (3) vanishes by
    the collar lemma; `gaussDdim > 0` closes the zero cases.  The 3rd leg is what covers the gate
    FRONTIER, which J4-97's 2-leg trichotomy could not.  NOT `a₁ = R/6`. -/
theorem gatedKernel_uniform_perBasePoint_of_cover (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcover : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
        (S q ∈ nhds p ∧ |heatOp g gi H τ p q| ≤ C * gaussDdim (2 * τ) (p - q))
      ∨ ({p' : Point n | p' ∉ S q} ∈ nhds p)
      ∨ ((fun t => H t p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ))
          ∧ (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ)))) :
    ∀ q τ, 0 < τ → ∀ p,
      |heatOp g gi (gatedKernel K S H) τ p q| ≤ C * gaussDdim (2 * τ) (p - q) := by
  intro q τ hτ p
  have hgpos : (0 : ℝ) ≤ C * gaussDdim (2 * τ) (p - q) :=
    mul_nonneg hC (QIQTH.LeviSeries.gaussDdim_pos (2 * τ) (by positivity) (p - q)).le
  by_cases hq : q ∈ K
  · rcases hcover q hq τ hτ p with ⟨hS, hbd⟩ | hoff | ⟨ht, hs⟩
    · rw [gatedKernel_heatOp_eq_of_mem_nhds g gi K S H τ p q hq hS]; exact hbd
    · rw [gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inr hoff), abs_zero]
      exact hgpos
    · rw [gatedKernel_heatOp_eq_zero_of_kernel_locally_zero g gi K S H τ p q ht hs, abs_zero]
      exact hgpos
  · rw [gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inl hq), abs_zero]
    exact hgpos

/-- **★★ T2 — the CONSUMER-READY width-2 target for the gated witness, from the 3-LEG COVER.**
    Composes `gatedKernel_uniform_perBasePoint_of_cover` with `hEboundW_of_uniform_perBasePoint`
    (`RecenterReduction`) to deliver the EXACT `hEboundW` primitive shape consumed by
    `TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual`:
        `∀ τ p q, 0 < τ → |heatOp g gi (gatedKernel K S H) τ p q| ≤ C · baseKernelW 2 0 τ p q`.
    Conditional ONLY on the 3-leg geometric cover.  NOT `a₁ = R/6`. -/
theorem gatedKernel_hEboundW_of_cover (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcover : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
        (S q ∈ nhds p ∧ |heatOp g gi H τ p q| ≤ C * gaussDdim (2 * τ) (p - q))
      ∨ ({p' : Point n | p' ∉ S q} ∈ nhds p)
      ∨ ((fun t => H t p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ))
          ∧ (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ)))) :
    ∀ τ p q, 0 < τ →
      |heatOp g gi (gatedKernel K S H) τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  hEboundW_of_uniform_perBasePoint (heatOp g gi (gatedKernel K S H)) C
    (gatedKernel_uniform_perBasePoint_of_cover g gi K S H C hC hcover)

/-! ### (T3, W1 bridge) The concrete chart-image gate is open with controlled closure, from T1. -/

/-- **T3 (W1 bridge) — the chart-image ball gate is OPEN with a compact-image closure, from T1.**  For
    the base-point chart `e` of T1 (`⇑e = φ_q`, `ball 0 δ ⊆ e.source`), every sub-ball radius `0 < c < δ`
    gives an OPEN image `φ_q '' (ball 0 c)` (`isOpen_image_of_subset_source`) whose closure lands inside
    the COMPACT (hence closed) image `φ_q '' (closedBall 0 c)` (`closedBall` compact, `e` continuous on
    source ⊇ `closedBall 0 c`).  These are exactly the `Hopen`/`Hclos` geometric facts the concrete cover
    consumes — so T1 DISCHARGES the W1 part of `hgood` for `c < δ`; only the radius ordering `b < δ` and
    the W2 uniform bound remain. -/
theorem chartImage_ball_open_closure (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, 0 < c → c < δ →
      IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
      ∧ closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
          ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c := by
  obtain ⟨e, δ, hδ0, hcoe, hsub⟩ := basepointChart_exists_strong g gi hC hK q hq
  refine ⟨δ, hδ0, ?_⟩
  intro c hc0 hcδ
  have hballsub : Metric.ball (0 : Point n) c ⊆ e.source :=
    fun x hx => hsub (Metric.ball_subset_ball hcδ.le hx)
  have hcballsub : Metric.closedBall (0 : Point n) c ⊆ e.source := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx
    exact hsub (mem_ball_zero_iff.mpr (lt_of_le_of_lt hx hcδ))
  refine ⟨?_, ?_⟩
  · have hop := e.isOpen_image_of_subset_source Metric.isOpen_ball hballsub
    rwa [hcoe] at hop
  · have hcompact : IsCompact (e '' Metric.closedBall 0 c) :=
      (isCompact_closedBall (0 : Point n) c).image_of_continuousOn (e.continuousOn.mono hcballsub)
    have hcl := closure_minimal
      (Set.image_mono Metric.ball_subset_closedBall) hcompact.isClosed
    rwa [hcoe] at hcl

/-! ### (T3) The concrete gated witness — cover discharged from the isolated residue `hgood`. -/

/-- **★★ T3 CORE — `gatedWitness_hEboundW_of_good`: the `hEboundW` primitive for the CONCRETE gate.**

    For the concrete witness `H_w = globalCutoffParametrixWitness Θ u a b (basepointInverseChart …)` and
    the concrete spatial gate `S q := φ_q '' (ball 0 c)` (open by T1), the 3-leg cover of T2 is
    DISCHARGED from the single isolated residue `hgood`, giving the exact `hEboundW` shape
        `∀ τ p q, 0 < τ → |heatOp g gi (gatedKernel K S H_w) τ p q| ≤ B · baseKernelW 2 0 τ p q`.

    `hgood` supplies, per `q ∈ K`, ONE radius `c > b` on which: (bound) the τ-UNIFORM in-chart Gaussian
    estimate holds; (inv/cont) `basepointInverseChart` is the genuine continuous inverse of `φ_q` up to
    radius `c`; (open/clos) the chart-image ball is open with compact-image closure (the T1 facts,
    provided by `chartImage_ball_open_closure` for `c < δ`).  The cover legs: `p ∈ S q` ⇒ in-gate bound
    (leg 1); `p ∉ closure (S q)` ⇒ off-gate (leg 2); `p ∈ closure (S q) \ S q` (the FRONTIER, at
    `‖W_q p‖ = c > b`) ⇒ the cutoff COLLAR (`radialCutoff a b (W_q p') = 0` on a `W_q`-continuity
    neighborhood, since `rncRadialSq (W_q p') > b²`), so `H_w(·,·,q)` is locally zero — leg 3.  `hgood`
    is genuine, satisfiable, and strictly weaker than the (global, all-`p`) conclusion.  NOT `a₁ = R/6`. -/
theorem gatedWitness_hEboundW_of_good (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b B : ℝ) (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (hgood : ∀ q ∈ K, ∃ c : ℝ, b < c ∧
      (∀ τ, 0 < τ → ∀ v : Point n, ‖v‖ < c →
        |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ B * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        basepointInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        ContinuousAt (basepointInverseChart g gi hC hK q) (uniformFlowExp g gi hC hK q v)) ∧
      IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
      closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
        ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c) :
    ∃ S : Point n → Set (Point n), ∀ τ p q, 0 < τ →
      |heatOp g gi (gatedKernel K S
          (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK))) τ p q|
        ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  classical
  set H : ℝ → Point n → Point n → ℝ :=
    globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK) with hHdef
  set cf : Point n → ℝ := fun q => if hq : q ∈ K then (hgood q hq).choose else 0 with hcfdef
  refine ⟨fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q), ?_⟩
  refine gatedKernel_hEboundW_of_cover g gi K _ H B hB ?_
  intro q hq τ hτ p
  have hcfq : cf q = (hgood q hq).choose := dif_pos hq
  set c₀ : ℝ := (hgood q hq).choose with hc0def
  obtain ⟨hbc, hbnd, hinv, hcont, hopen, hclos⟩ := (hgood q hq).choose_spec
  -- the gate at `q` is `φ_q '' ball 0 c₀`.
  have hSqeq : uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)
      = uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀ := by rw [hcfq]
  rw [hSqeq]
  have hb0 : 0 < b := lt_trans ha hab
  by_cases hpS : p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀
  · -- LEG 1 (in-gate): transfer the uniform in-chart bound.
    refine Or.inl ⟨hopen.mem_nhds hpS, ?_⟩
    obtain ⟨w, hw, hwp⟩ := hpS
    rw [mem_ball_zero_iff] at hw
    have hb := hbnd τ hτ w hw
    rw [hwp] at hb
    exact hb
  · by_cases hpcl : p ∈ closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀)
    · -- LEG 3 (frontier collar): the cutoff of `W_q` vanishes near `p`.
      obtain ⟨w', hw', hw'p⟩ := hclos hpcl
      rw [mem_closedBall_zero_iff] at hw'
      have hnormeq : ‖w'‖ = c₀ := by
        rcases lt_or_eq_of_le hw' with hlt | heq
        · exact absurd (⟨w', mem_ball_zero_iff.mpr hlt, hw'p⟩ :
            p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀) hpS
        · exact heq
      have hWp : basepointInverseChart g gi hC hK q p = w' := by
        rw [← hw'p]; exact hinv w' hw'
      have hb2 : b ^ 2 < rncRadialSq (basepointInverseChart g gi hC hK q p) := by
        rw [hWp]
        have h1 : ‖w'‖ ^ 2 ≤ rncRadialSq w' := by
          have hle := norm_le_rncRadial w'
          have := rncRadial_sq w'
          nlinarith [norm_nonneg w', rncRadial_nonneg w', hle, this]
        nlinarith [h1, hnormeq, hb0, hbc]
      have hcontp : ContinuousAt (basepointInverseChart g gi hC hK q) p := by
        rw [← hw'p]; exact hcont w' hw'
      have hNnhds :
          (basepointInverseChart g gi hC hK q) ⁻¹' {w : Point n | b ^ 2 < rncRadialSq w} ∈ nhds p :=
        hcontp.preimage_mem_nhds ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hb2)
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · -- time germ: `H_w(t,p,q) = 0` for all `t`.
        refine Filter.Eventually.of_forall (fun t => ?_)
        simp only [hHdef, globalCutoffParametrixWitness]
        rw [radialCutoff_eq_zero ha hab (le_of_lt hb2), zero_mul]
      · -- space germ: `H_w(τ,p',q) = 0` for `p'` near `p`.
        filter_upwards [hNnhds] with p' hp'
        have hp'2 : b ^ 2 < rncRadialSq (basepointInverseChart g gi hC hK q p') := hp'
        simp only [hHdef, globalCutoffParametrixWitness]
        rw [radialCutoff_eq_zero ha hab (le_of_lt hp'2), zero_mul]
    · -- LEG 2 (off-gate): the complement of the closed closure is a neighborhood.
      refine Or.inr (Or.inl ?_)
      have hsub : (closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀))ᶜ
          ⊆ {p' : Point n | p' ∉ uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀} :=
        fun x hx hxS => hx (subset_closure hxS)
      exact Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hpcl) hsub

/-- **★★ T3 CAPSTONE — `gatedWitness_hEboundW`: the `hEboundW` primitive composed with J4-96.**

    Obtains the single `τ`-free `(a,b,B)` and the per-`(τ,q)` in-chart Gaussian bound from the J4-96
    capstone `globalWitness_residual_bound_chartGaussian_final` (all far-point + near-isometry inputs
    already discharged there), feeds them to `hgood`, and delivers, for the CONCRETE gated witness, the
    exact width-2 `hEboundW` primitive shape consumed by
    `TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual`:
        `∃ a b B S, … ∧ ∀ τ p q, 0 < τ → |heatOp g gi (gatedKernel K S H_w) τ p q| ≤ B · baseKernelW 2 0 τ p q`.

    Hypotheses are the genuine geometric/heat data (`hg`/`hC`/`hK`/`hgnd`/`hgsymm`/`hinvF`/`hframeK`/`Θ`/
    `u`/`hw0smooth`/`hw0flat`) PLUS the single isolated residue `hgood`: given the J4-96 per-`(τ,q)`
    bound, upgrade it (per `q ∈ K`) to a τ-UNIFORM radius `c > b` and supply the chart geometry (open
    image + compact-image closure + `basepointInverseChart` inverse/continuity up to `c`).  The geometry
    is discharged unconditionally by T1 (`chartImage_ball_open_closure`) and J4-93
    (`basepointInverseChart_spec`) for `c` below the chart radius; the sole irreducible content of
    `hgood` is the cutoff-support ⊆ transport-radius ordering `b < c` under the τ-uniform bound (J4-97's
    firewall W2).  NOT `a₁ = R/6`. -/
theorem gatedWitness_hEboundW (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hgood : ∀ (a b B : ℝ), 0 < a → a < b → 0 ≤ B →
        (∀ (τ : ℝ) (q : Point n), q ∈ K → 0 < τ →
          ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
            |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
                (uniformFlowExp g gi hC hK q v) q|
              ≤ B * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) →
        ∀ q ∈ K, ∃ c : ℝ, b < c ∧
          (∀ τ, 0 < τ → ∀ v : Point n, ‖v‖ < c →
            |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
                (uniformFlowExp g gi hC hK q v) q|
              ≤ B * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) ∧
          (∀ v : Point n, ‖v‖ ≤ c →
            basepointInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v) ∧
          (∀ v : Point n, ‖v‖ ≤ c →
            ContinuousAt (basepointInverseChart g gi hC hK q) (uniformFlowExp g gi hC hK q v)) ∧
          IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
          closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
            ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∃ S : Point n → Set (Point n),
      ∀ τ p q, 0 < τ →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK))) τ p q|
          ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  obtain ⟨a, b, B, ha, hab, hB, hb96⟩ :=
    globalWitness_residual_bound_chartGaussian_final g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u
      hw0smooth hw0flat
  refine ⟨a, b, B, ha, hab, hB, ?_⟩
  exact gatedWitness_hEboundW_of_good g gi hC hK Θ u a b B ha hab hB
    (hgood a b B ha hab hB hb96)

end QIQTH.HeatResidualBound
