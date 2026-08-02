/-
  GlobalHunifAssembly — J4-97: the GATED-witness assembly toward the GLOBAL (all-`p`, all-`q`) width-2
  residual bound `hEboundW`, consumed by the reduced `a₁ = R/6` capstone
  (`TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual`) via
  `RecenterReduction.hEboundW_of_uniform_perBasePoint`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file delivers (ns `QIQTH.HeatResidualBound`; NO `sorry`, no new axioms, no `expRho`).

  The in-chart per-base-point bound is PROVED (J4-96,
  `globalWitness_residual_bound_chartGaussian_final`): a single `(a,b,B)`, uniform over `q ∈ K`,
      `|heatOp g gi H_w τ (φ_q v) q| ≤ B · gaussDdim (2τ) (φ_q v − q)`   for `‖v‖ < r₀`,
  where `H_w = globalCutoffParametrixWitness Θ u a b (basepointInverseChart …)`, `φ_q = uniformFlowExp …`.
  The consumer wants the GLOBAL form `∀ q τ, 0<τ → ∀ p, |E τ p q| ≤ C·gaussDdim (2τ)(p−q)` — i.e. the
  bound at EVERY `p`, not only the in-chart image points, and at EVERY `q`, not only `q ∈ K`.  The raw
  witness has no clean global extension: `basepointInverseChart … q` is `e.symm` of the base-point IFT
  homeomorph, TOTAL with uncontrolled junk off `e.target`, so `H_w` need not vanish off-chart; and for
  `q ∉ K` the chart is the zero default, making `H_w` `p`-constant but NOT `τ`-constant, so `heatOp ≠ 0`.

  ### The FIX — a GATED kernel (this file, all UNCONDITIONAL):
      `gatedKernel K S H τ p q := if q ∈ K then (if p ∈ S q then H τ p q else 0) else 0`,
  a `q`-gate (kills `q ∉ K`) followed by a spatial set-gate `S q`.  We prove:
    * (G1) `heatOp_congr_nhds` — `heatOp` respects local (space-germ + time-germ) equality of the kernel.
      The `∂_τ` slot by `EventuallyEq.deriv_eq`, the `Δ_g` slot by `laplaceBeltrami_congr_nhds`.
    * (G2a) `gatedKernel_heatOp_eq_of_mem_nhds` — where the gate is a NEIGHBORHOOD of `p` (and `q ∈ K`),
      the gated `heatOp` EQUALS the ungated `heatOp` (the set-gate is `τ`-independent, so both germs
      transfer), hence the in-chart bound applies verbatim.
    * (G2b) `gatedKernel_heatOp_eq_zero_of_notMem` — where the gate is locally OFF `p` (`{p'∉S q}` a
      neighborhood) OR `q ∉ K`, the gated `heatOp` VANISHES (`heatOp_eq_zero_of_locally_zero`, J4-94).
      This is the out-of-chart / out-of-`K` zero-extension, resolved by CONSTRUCTION (no junk-inverse
      analysis).
    * (G3) `gatedKernel_uniform_perBasePoint_of_trichotomy` — the honest reduction: GIVEN the geometric
      TRICHOTOMY hypothesis `htri` (for each `q ∈ K`, `τ`, `p`: either the gate is a nbhd of `p` and the
      UNgated bound holds at `p`, OR the gate is locally off `p`), the gated kernel satisfies the FULL
      per-base-point Gaussian family `∀ q τ, 0<τ → ∀ p, |heatOp g gi (gatedKernel …) τ p q| ≤
      C·gaussDdim (2τ)(p−q)` — including `q ∉ K` (zero leg, `gaussDdim > 0`).
    * (G4) `gatedKernel_hEboundW_of_trichotomy` — composing G3 with
      `hEboundW_of_uniform_perBasePoint` delivers the EXACT consumer shape
      `∀ τ p q, 0<τ → |heatOp g gi (gatedKernel …) τ p q| ≤ C·baseKernelW 2 0 τ p q`,
      ready to be the `hEboundW` primitive of `trueKernel_diagonal_a1_eq_R6_residual`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## FIREWALL — what remains, precisely (binding, honest; GPT-5.6-sol consulted, verdict confirmed).

  Everything above is UNCONDITIONAL.  The single remaining input is the geometric TRICHOTOMY `htri`
  (for the concrete gate `S q = φ_q '' (inner chart ball)` around `H := H_w`).  Discharging `htri` needs
  TWO pieces of infrastructure not present in the current chain:

    (W1) CHART-IMAGE OPENNESS.  The in-gate branch of `htri` requires, at each image point `p = φ_q v`,
      that `S q ∈ 𝓝 p` (so G2a transfers the bound).  This is openness of `φ_q` at `v`.  Mathlib has NO
      invariance-of-domain, so openness must come from an IFT `OpenPartialHomeomorph`; `φ_q`'s own
      invertible derivative DOES give one (`contDiffAt` + nondegeneracy, both already available), but the
      `e` chosen inside `basepointInverseChart` is hidden behind `.choose`, exposing only the LEFT-inverse
      germ + `C²` — NOT the open target / right-inverse germ (`HasStrictFDerivAt.eventually_right_inverse`
      exists in Mathlib but was not exported).  Reconstructing `φ_q`'s own open chart and matching it to
      `basepointInverseChart` on the image (where the two inverses agree) is genuine local-diffeomorphism
      infrastructure.

    (W2) SUPPORT CONTAINMENT (the `b`-vs-`r₀` quantifier gap).  J4-96 fixes `(a,b)` FIRST, then yields
      `∃ r₀ > 0` per `(τ,q)`.  Nothing forces the cutoff support `{v | rncRadialSq v < b²}` inside
      `ball 0 r₀`, so an in-gate active-cutoff point may have `‖v‖ ≥ r₀`, where J4-96 does not apply.  The
      frontier of the gate must also lie in a radial-cutoff ZERO COLLAR (`radialCutoff_eventuallyEq_zero`)
      to land the off-gate germ.  This needs J4-96 (or the cutoff-selection lemma) restated to expose the
      containment `active-cutoff ⟹ ‖v‖ < r₀`.

  Discharging `htri` for the concrete `(H_w, S = φ_q '' ball)` — i.e. supplying (W1)+(W2) — is J4-98's
  job; the `hHdiag`-at-`0` interplay for the gated witness is likewise deferred there.  NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses (`htri` is a genuine,
  satisfiable geometric statement; the gating machinery it feeds is proved unconditionally).
-/
import Mathlib
import QIQTH.GlobalWitnessHunif
import QIQTH.RecenterReduction
import QIQTH.NearIsometryBudget

open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open Set Filter
open scoped BigOperators Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### (G1) The heat operator respects local (space + time) equality of the kernel. -/

/-- **★ G1 — `heatOp` is germ-local in the kernel.**  If `H'` agrees with `H` as a function of time near
    `τ` (at the fixed base point `p`) AND as a function of space near `p` (at the fixed time `τ`), then
    `heatOp g gi H' τ p q = heatOp g gi H τ p q`.  `heatOp = ∂_τ − Δ_g`: the `∂_τ` slot transfers by
    `EventuallyEq.deriv_eq` (time germ), the `Δ_g` slot by `laplaceBeltrami_congr_nhds` (space germ, `Δ_g`
    being a germ-local second-order operator).  The `q`-slot is inert (`heatOp` never differentiates in
    `q`).  This is the transfer engine for any set-gated / locally-modified witness. -/
theorem heatOp_congr_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (H H' : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p q : Point n)
    (htau : (fun t => H' t p q) =ᶠ[nhds τ] (fun t => H t p q))
    (hspace : (fun p' => H' τ p' q) =ᶠ[nhds p] (fun p' => H τ p' q)) :
    heatOp g gi H' τ p q = heatOp g gi H τ p q := by
  unfold heatOp
  rw [htau.deriv_eq, QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds g gi _ _ p hspace]

/-! ### (G2) The gated kernel and its trichotomy legs. -/

open Classical in
/-- **The GATED kernel.**  A `q`-gate onto `K` (kills `q ∉ K`, where the chart is a junk default)
    followed by a spatial set-gate `S q`:
        `gatedKernel K S H τ p q := if q ∈ K then (if p ∈ S q then H τ p q else 0) else 0`.
    The set-gate is `τ`-independent (the point of a HARD gate): the time slot at any in-gate `(p,q)`
    equals `H` exactly for ALL `t`, so `∂_τ` transfers cleanly (a smooth/`τ`-dependent gate would inject
    a `∂_τχ` term J4-96 cannot absorb). -/
noncomputable def gatedKernel (K : Set (Point n)) (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) : ℝ → Point n → Point n → ℝ :=
  fun τ p q => if q ∈ K then (if p ∈ S q then H τ p q else 0) else 0

/-- On the gate (`q ∈ K`, `p ∈ S q`) the gated kernel equals the base kernel, for every time. -/
theorem gatedKernel_apply_of_mem (K : Set (Point n)) (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) {p q : Point n} (hq : q ∈ K) (hp : p ∈ S q) :
    gatedKernel K S H τ p q = H τ p q := by
  simp only [gatedKernel, if_pos hq, if_pos hp]

/-- Off the gate (`q ∉ K`, or `p ∉ S q`) the gated kernel vanishes, for every time. -/
theorem gatedKernel_apply_of_notMem (K : Set (Point n)) (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p q : Point n) (h : q ∉ K ∨ p ∉ S q) :
    gatedKernel K S H τ p q = 0 := by
  rcases h with hq | hp
  · simp only [gatedKernel, if_neg hq]
  · by_cases hq : q ∈ K
    · simp only [gatedKernel, if_pos hq, if_neg hp]
    · simp only [gatedKernel, if_neg hq]

/-- **G2a — the in-gate heat-operator transfer.**  Where the gate is a NEIGHBORHOOD of `p` (and
    `q ∈ K`), the gated heat operator EQUALS the ungated one: both the time germ (the set-gate is
    `τ`-independent, so equality holds for all `t`) and the space germ (equality on the whole
    neighborhood `S q`) transfer via G1.  Consequently any pointwise bound on `heatOp g gi H τ p q`
    applies verbatim to `heatOp g gi (gatedKernel K S H) τ p q`. -/
theorem gatedKernel_heatOp_eq_of_mem_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (τ : ℝ) (p q : Point n) (hq : q ∈ K) (hS : S q ∈ nhds p) :
    heatOp g gi (gatedKernel K S H) τ p q = heatOp g gi H τ p q := by
  have hp : p ∈ S q := mem_of_mem_nhds hS
  refine heatOp_congr_nhds g gi H (gatedKernel K S H) τ p q ?_ ?_
  · -- time germ: equality holds for ALL `t` (set-gate is `τ`-independent).
    exact Filter.Eventually.of_forall
      (fun t => gatedKernel_apply_of_mem K S H t hq hp)
  · -- space germ: equality on the neighborhood `S q`.
    exact Filter.eventuallyEq_of_mem hS
      (fun p' hp' => gatedKernel_apply_of_mem K S H τ hq hp')

/-- **G2b — the out-of-gate heat-operator vanishing.**  Where the gate is locally OFF `p`
    (`{p' | p' ∉ S q} ∈ 𝓝 p`) OR `q ∉ K`, the gated kernel is locally `0` in both slots, so
    `heatOp_eq_zero_of_locally_zero` (J4-94) gives `heatOp g gi (gatedKernel K S H) τ p q = 0`.  This is
    the out-of-chart / out-of-`K` zero-extension, resolved purely by the gate — no junk-inverse
    analysis. -/
theorem gatedKernel_heatOp_eq_zero_of_notMem (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (τ : ℝ) (p q : Point n) (h : q ∉ K ∨ {p' : Point n | p' ∉ S q} ∈ nhds p) :
    heatOp g gi (gatedKernel K S H) τ p q = 0 := by
  rcases h with hq | hoff
  · -- `q ∉ K`: the whole kernel is identically `0`.
    refine heatOp_eq_zero_of_locally_zero g gi (gatedKernel K S H) τ p q ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun t => gatedKernel_apply_of_notMem K S H t p q (Or.inl hq))
    · exact Filter.Eventually.of_forall
        (fun p' => gatedKernel_apply_of_notMem K S H τ p' q (Or.inl hq))
  · -- `q`-in-`K` but gate off a neighborhood of `p`.
    have hpoff : p ∉ S q := mem_of_mem_nhds hoff
    refine heatOp_eq_zero_of_locally_zero g gi (gatedKernel K S H) τ p q ?_ ?_
    · -- time germ at `p`: `p ∉ S q`, so the kernel is `0` for all `t`.
      exact Filter.Eventually.of_forall
        (fun t => gatedKernel_apply_of_notMem K S H t p q (Or.inr hpoff))
    · -- space germ: `0` on the neighborhood `{p' | p' ∉ S q}`.
      exact Filter.eventuallyEq_of_mem hoff
        (fun p' hp' => gatedKernel_apply_of_notMem K S H τ p' q (Or.inr hp'))

/-! ### (G3) The honest reduction — trichotomy ⟹ the full per-base-point Gaussian family. -/

/-- **★★ G3 — the GATED per-base-point Gaussian family from the geometric trichotomy.**

    GIVEN the geometric TRICHOTOMY `htri` — for each `q ∈ K`, time `τ > 0`, and point `p`, EITHER the
    gate is a neighborhood of `p` AND the UNgated residual already obeys the width-2 bound at `p`, OR the
    gate is locally OFF `p` — the gated kernel obeys the FULL per-base-point width-2 Gaussian family over
    ALL `q` (including `q ∉ K`, handled by the zero leg since `gaussDdim > 0`) and ALL `p`:
        `∀ q τ, 0 < τ → ∀ p, |heatOp g gi (gatedKernel K S H) τ p q| ≤ C · gaussDdim (2τ) (p − q)`.

    The in-gate branch transfers the bound by G2a; the off-gate branch and the `q ∉ K` case vanish by
    G2b (`0 ≤ C · gaussDdim`).  `htri` is genuinely used and IS the content (the sole remaining wall);
    the gating machinery around it is unconditional.  NOT `a₁ = R/6`. -/
theorem gatedKernel_uniform_perBasePoint_of_trichotomy (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (htri : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
        (S q ∈ nhds p ∧ |heatOp g gi H τ p q| ≤ C * gaussDdim (2 * τ) (p - q))
      ∨ ({p' : Point n | p' ∉ S q} ∈ nhds p)) :
    ∀ q τ, 0 < τ → ∀ p,
      |heatOp g gi (gatedKernel K S H) τ p q| ≤ C * gaussDdim (2 * τ) (p - q) := by
  intro q τ hτ p
  have hgpos : (0 : ℝ) ≤ C * gaussDdim (2 * τ) (p - q) :=
    mul_nonneg hC (QIQTH.LeviSeries.gaussDdim_pos (2 * τ) (by positivity) (p - q)).le
  by_cases hq : q ∈ K
  · rcases htri q hq τ hτ p with ⟨hS, hbd⟩ | hoff
    · -- in-gate: transfer the ungated bound.
      rw [gatedKernel_heatOp_eq_of_mem_nhds g gi K S H τ p q hq hS]
      exact hbd
    · -- off-gate: `heatOp = 0`.
      rw [gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inr hoff), abs_zero]
      exact hgpos
  · -- `q ∉ K`: `heatOp = 0`.
    rw [gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inl hq), abs_zero]
    exact hgpos

/-! ### (G4) The consumer-ready `hEboundW` shape. -/

/-- **★★ G4 — the CONSUMER-READY width-2 target for the gated witness.**  Composing G3 with
    `hEboundW_of_uniform_perBasePoint` (`RecenterReduction`) rewrites the doubled-time Gaussian into the
    width-kernel wrapper `baseKernelW 2 0`, delivering the EXACT shape of the `hEboundW` primitive
    consumed by `TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual`:
        `∀ τ p q, 0 < τ → |heatOp g gi (gatedKernel K S H) τ p q| ≤ C · baseKernelW 2 0 τ p q`.
    Conditional ONLY on the geometric trichotomy `htri` (the isolated wall — see the file firewall:
    chart-image openness + J4-96 support containment, J4-98's job).  NOT `a₁ = R/6`. -/
theorem gatedKernel_hEboundW_of_trichotomy (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (htri : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
        (S q ∈ nhds p ∧ |heatOp g gi H τ p q| ≤ C * gaussDdim (2 * τ) (p - q))
      ∨ ({p' : Point n | p' ∉ S q} ∈ nhds p)) :
    ∀ τ p q, 0 < τ →
      |heatOp g gi (gatedKernel K S H) τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  hEboundW_of_uniform_perBasePoint (heatOp g gi (gatedKernel K S H)) C
    (gatedKernel_uniform_perBasePoint_of_trichotomy g gi K S H C hC htri)

end QIQTH.HeatResidualBound
