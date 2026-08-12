/-
  WhiteGauss — J4-637: `hGauss` AT THE WHITENED CHART, DISCHARGED.

  THE BRICK.  The J4-636 K1 budget `white_K1BudgetW_of_transport` (WhiteOrder1) is conditional on
  FIVE labelled transport inputs {hwsm, hGauss, h0, h1, hΔ}.  This file discharges `hGauss` — the
  inverse-metric radial compatibility (Gauss-lemma face)
      `∀ x, ‖x‖ < r₀ → ∀ i, ∑ⱼ (ĝ⁻¹(x)ᵢⱼ − δᵢⱼ)·xʲ = 0`
  at the whitened chart data — UNCONDITIONALLY (no labelled input; standard-3 axioms only).

  ── THE ASSESS (step 1 of the brick).  The raw radial identity IS banked end-to-end:
    • the per-point first-variation Gauss identity is a PROVED theorem
      (`GaussInteriorMVT.gauss_interior_identity` / `hgball_concrete` — the J4-347 closure of the
      hGauss campaign: interior-MVT constancy, curvature kill, Euler homogeneity), for a GENERAL
      base metric (no `g_p = δ` gauge), under ordinary geometry hypotheses only
      (`hsymm`/`hinv`/`hg` + smooth Christoffels) — all banked for `curvedRNCMetric`;
    • the coordinate contraction (`GaussLemmaAssembly.gauss_coordinate_contraction`) converts it to
          `∑ⱼ g̃(v)ᵢⱼ vʲ = ∑ⱼ g_p(i,j) vʲ`      (g̃ = expPullbackMetric; general base row `g_p`),
      i.e. THE RAW GAUSS LEMMA `g̃(v)·v = g(q)·v` — the radial vector is `g(q)`-preserved;
    • the weld `uniformFlowPullbackMetric_eq_expPullbackMetric_eventually` transports it to the
      repo's uniform-flow chart on a per-`q` ball.
  So the brick is pure banked-jet algebra, exactly as the J4-636 (g) recommendation hoped: NO new
  ODE work, NO labelled input one level down.

  ── THE CHAIN (per base row `q ∈ K`, `κ ≤ 0`).
    §1  `uniformFlow_gauss_radial`   — RAW: `∑ⱼ g̃_q(v)ᵢⱼ vʲ = ∑ⱼ g^κ(q)ᵢⱼ vʲ` on a ball
                                       (weld + banked coordinate Gauss lemma).
    §2  `whitePullbackMetric_gauss`  — WHITENED METRIC: `ĝ(w)·w = w` exactly:
            `ĝ(w)w = Eᵀ·g̃(Ew)·(Ew) = Eᵀ·g^κ(q)·(Ew) = (Eᵀ g^κ(q) E)·w = δ·w = w`
        (raw Gauss at `v = E_q w` + the banked all-`q` whitening identity
        `curvedRNC_whitening_all`).  ⟹ the whitened chart IS a true-Gauss-lemma chart.
    §3  ★ `whiteGauss_discharged`    — INVERSE: `ĝ⁻¹(x)·x = x` on the joint gate, via the banked
        Neumann unit package `whitePullbackMetric_neumann` + `sum_invMat_mul`
        (`ĝ⁻¹x = ĝ⁻¹(ĝx) = x`).  This is the EXACT `hGauss` shape of WhiteOrder1.
    §4  ★★ `white_K1BudgetW_of_transport_gaussFree` — the J4-636 K1 budget REWIRED with `hGauss`
        GONE: conditional on {hwsm, h0, h1, hΔ} only (gate radius below the discharged Gauss gate).
    §5  Non-vacuity gates (cp466): the discharged statement is exercised at the genuinely curved
        witness (`n = 2`, `κ = −1`, `q = (1,1)` in the fat ball, a NONZERO gate point).

  ⚠ HONEST SCOPE (binding).
    • The Gauss gate radius is PER-`q` (the weld/`expRho` ball is per-row); the rewired budget
      exposes it as `∃ rG > 0` with the budget for every gate radius `r₀ ≤ rG`.  Downstream
      co-instantiation must intersect gates as usual.
    • `a₁ = R/6` remains CONDITIONAL: the flat tower is closed and non-vacuous; the curved side
      still owes the discharge of the REMAINING K1 inputs {hwsm, h0, h1, hΔ} at the whitened
      chart data (h0 = the checkpointed k = 0 transport identity, h1 = the k = 1 equation, hΔ =
      transport-coefficient regularity, hwsm = coefficient smoothness) + the Duhamel-split
      integrability carry + the fat-`K` carrier piles + the capstone co-instantiation + the prior
      analytic piles.  This brick removes exactly ONE of the five: `hGauss`.
  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.WhiteOrder1
import QIQTH.GaussInteriorMVT

open Finset Filter Topology Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.HeatResidualBound QIQTH.HeatTransportRecursion
open QIQTH.ExpMap QIQTH.PullbackMetric
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.CurvedA1CenterAmp QIQTH.EquivProbe
open QIQTH.WhiteWitness QIQTH.WhiteReplay QIQTH.WhiteAmbient
open QIQTH.GaussLemmaAssembly QIQTH.GaussInteriorMVT
open QIQTH.WhiteCapstoneWire QIQTH.WhiteOrder1

namespace QIQTH.WhiteGauss

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §0. A reusable triple-contraction swap (pure `Finset` algebra). -/

/-- `∑ⱼ (AᵀMA)ᵢⱼ xʲ = ∑ₖ Aᵢₖ·(∑ₗ Mₖₗ·(Ax)ₗ)` — the congruence-transport of a radial contraction
    through a frame `A` (both `A`-slots row-indexed as in `whitePullbackMetric`). -/
theorem contract_swap (A M B : Fin n → Fin n → ℝ) (x : Point n) (i : Fin n) :
    (∑ j, (∑ k, ∑ l, A i k * M k l * B l j) * x j)
      = ∑ k, A i k * (∑ l, M k l * (∑ j, B l j * x j)) := by
  calc (∑ j, (∑ k, ∑ l, A i k * M k l * B l j) * x j)
      = ∑ j, ∑ k, ∑ l, A i k * M k l * B l j * x j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
    _ = ∑ k, ∑ j, ∑ l, A i k * M k l * B l j * x j := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ j, A i k * M k l * B l j * x j :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, A i k * (∑ l, M k l * (∑ j, B l j * x j)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun j _ => by ring

/-- `∑ⱼ δᵢⱼ·xʲ = xⁱ`. -/
theorem sum_delta_mul (x : Point n) (i : Fin n) :
    (∑ j, (if i = j then (1 : ℝ) else 0) * x j) = x i := by
  rw [Finset.sum_eq_single i (fun b _ hbi => by rw [if_neg (Ne.symm hbi), zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), if_pos rfl, one_mul]

/-! ### §1. The RAW radial identity at the uniform-flow chart — from the banked Gauss lemma. -/

/-- **★ The raw Gauss lemma at the flow chart** (general base row — NO `g(q) = δ` gauge).  On a
    per-`q` ball, the uniform-flow pullback metric of the curved RNC witness satisfies
        `∑ⱼ g̃_q(v)ᵢⱼ·vʲ = ∑ⱼ g^κ(q)ᵢⱼ·vʲ`
    — the radial vector is an eigenvector of the pullback metric "relative to `g^κ(q)`".
    Suppliers: the banked per-point first-variation Gauss identity (`hgball_concrete`, the J4-347
    analytic closure) + the coordinate contraction (`gauss_coordinate_contraction`) + the banked
    chart weld (`uniformFlowPullbackMetric_eq_expPullbackMetric_eventually`).  All geometry
    hypotheses are the banked `curvedRNCMetric` facts — NOTHING is labelled.  NOT `a₁ = R/6`. -/
theorem uniformFlow_gauss_radial (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    ∃ ρ > (0 : ℝ), ∀ v : Point n, ‖v‖ < ρ → ∀ i : Fin n,
      (∑ j, uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q v i j * v j)
        = ∑ j, curvedRNCMetric κ q i j * v j := by
  obtain ⟨ε, hε0, hweld⟩ := Metric.eventually_nhds_iff.mp
    (uniformFlowPullbackMetric_eq_expPullbackMetric_eventually (curvedRNCMetric κ)
      (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q hq)
  refine ⟨min ε (expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q),
    lt_min hε0 (expRho_pos (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q), ?_⟩
  intro v hv i
  have hvε : dist v (0 : Point n) < ε := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le hv (min_le_left _ _)
  have hvρ : ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q :=
    lt_of_lt_of_le hv (min_le_right _ _)
  have hw := hweld hvε
  -- the banked per-point first-variation Gauss identity at the `i`-th column
  have hg1 := hgball_concrete (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
    (fun y a b => curvedRNCMetric_symm κ y a b)
    (fun y a b => curvedRNCMetric_hinvF κ hκ y a b)
    (fun a b => curvedRNCMetric_contDiff κ a b) q v hvρ i
  -- the banked coordinate contraction (general base row)
  have hcontr := gauss_coordinate_contraction (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) q v hvρ i hg1
  calc (∑ j, uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q v i j * v j)
      = ∑ j, expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) q v i j * v j :=
        Finset.sum_congr rfl fun j _ => by rw [hw i j]
    _ = ∑ j, curvedRNCMetric κ q i j * v j := hcontr

/-! ### §2. The whitened chart is a TRUE-Gauss-lemma chart: `ĝ(w)·w = w`. -/

/-- **★ The whitened metric Gauss lemma** — `∑ⱼ ĝ_q(w)ᵢⱼ·wʲ = wⁱ` EXACTLY on a per-`q` gate:
        `ĝ(w)w = Eᵀ·g̃(Ew)·(Ew) = Eᵀ·g^κ(q)·(Ew) = (Eᵀ g^κ(q) E)·w = δ·w = w`
    (§1 raw Gauss at `v = E_q w`, confined by `whiteVel_norm_le`, closed by the banked whitening
    identity `curvedRNC_whitening_all`).  The whitened chart is exactly the "true-Gauss-lemma
    chart" of the J4-635 note — the eikonal layer vanishes identically.  NOT `a₁ = R/6`. -/
theorem whitePullbackMetric_gauss (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    ∃ r > (0 : ℝ), ∀ w : Point n, ‖w‖ < r → ∀ i : Fin n,
      (∑ j, whitePullbackMetric κ hκ hKc q w i j * w j) = w i := by
  obtain ⟨ρ, hρ0, hraw⟩ := uniformFlow_gauss_radial κ hκ hKc q hq
  have hs1 : (0 : ℝ) < Real.sqrt n + 1 := by positivity
  refine ⟨ρ / (Real.sqrt n + 1), by positivity, ?_⟩
  intro w hw i
  -- velocity confinement: `‖E_q w‖ < ρ`
  have hEw : ‖whiteVel κ q w‖ < ρ := by
    have h1 := whiteVel_norm_le κ hκ q w
    have h2 : Real.sqrt n * ‖w‖ ≤ (Real.sqrt n + 1) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg (n : ℝ)]) (norm_nonneg w)
    have h3 : (Real.sqrt n + 1) * ‖w‖ < (Real.sqrt n + 1) * (ρ / (Real.sqrt n + 1)) :=
      mul_lt_mul_of_pos_left hw hs1
    have h4 : (Real.sqrt n + 1) * (ρ / (Real.sqrt n + 1)) = ρ := by field_simp
    linarith
  have hrawE := hraw (whiteVel κ q w) hEw
  -- the two contraction swaps (raw metric at `Ew`, and the frozen base metric)
  have hswap1 := contract_swap (curvedWhitening κ q)
    (fun k l => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l)
    (curvedWhitening κ q) w i
  have hswap2 := contract_swap (curvedWhitening κ q)
    (fun k l => curvedRNCMetric κ q k l) (curvedWhitening κ q) w i
  -- the whitening identity contracts to `δ`
  have hδ : (∑ j, (∑ k, ∑ l, curvedWhitening κ q i k * curvedRNCMetric κ q k l
        * curvedWhitening κ q l j) * w j) = w i := by
    rw [Finset.sum_congr rfl fun j _ => by rw [curvedRNC_whitening_all κ hκ q i j]]
    exact sum_delta_mul w i
  -- the middle step: the raw Gauss lemma at `v = E_q w`, row by row
  have hmid : (∑ k, curvedWhitening κ q i k
        * (∑ l, uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l
          * (∑ j, curvedWhitening κ q l j * w j)))
      = ∑ k, curvedWhitening κ q i k
        * (∑ l, curvedRNCMetric κ q k l * (∑ j, curvedWhitening κ q l j * w j)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact hrawE k
  calc (∑ j, whitePullbackMetric κ hκ hKc q w i j * w j)
      = ∑ j, (∑ k, ∑ l, curvedWhitening κ q i k
          * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l
          * curvedWhitening κ q l j) * w j := by
        exact Finset.sum_congr rfl fun j _ => by
          rw [show whitePullbackMetric κ hκ hKc q w i j
              = ∑ k, ∑ l, curvedWhitening κ q i k
                  * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
                      (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l
                  * curvedWhitening κ q l j from rfl]
    _ = ∑ k, curvedWhitening κ q i k
          * (∑ l, uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l
            * (∑ j, curvedWhitening κ q l j * w j)) := hswap1
    _ = ∑ k, curvedWhitening κ q i k
          * (∑ l, curvedRNCMetric κ q k l * (∑ j, curvedWhitening κ q l j * w j)) := hmid
    _ = ∑ j, (∑ k, ∑ l, curvedWhitening κ q i k * curvedRNCMetric κ q k l
          * curvedWhitening κ q l j) * w j := hswap2.symm
    _ = w i := hδ

/-! ### §3. ★ The `hGauss` discharge: `ĝ⁻¹(x)·x = x` on the joint gate. -/

/-- **★★ `whiteGauss_discharged` — the WhiteOrder1 `hGauss` input, UNCONDITIONAL.**  For every
    `κ ≤ 0`, compact base `K`, row `q ∈ K`, there is a gate radius `r₀ > 0` with
        `∀ ‖x‖ < r₀, ∀ i, ∑ⱼ (ĝ⁻¹_q(x)ᵢⱼ − δᵢⱼ)·xʲ = 0`
    — the EXACT labelled `hGauss` of `white_K1BudgetW_of_transport` (via `whiteMetricInv = ĝ⁻¹`,
    definitional).  Mechanism: `ĝ(x)x = x` (§2) + the banked Neumann unit package
    (`whitePullbackMetric_neumann`) + the entrywise left inverse (`sum_invMat_mul`):
        `ĝ⁻¹x = ĝ⁻¹(ĝx) = (ĝ⁻¹ĝ)x = δx = x`.
    NO labelled input survives.  NOT `a₁ = R/6` — the other four K1 inputs remain owed. -/
theorem whiteGauss_discharged (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ → ∀ i : Fin n,
      (∑ j, (whitePullbackMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j)
        = 0 := by
  obtain ⟨r₁, hr₁0, hmet⟩ := whitePullbackMetric_gauss κ hκ hKc q hq
  obtain ⟨r₂, hr₂0, M, hM0, hpkg⟩ := whitePullbackMetric_neumann κ hκ hKc
  refine ⟨min r₁ r₂, lt_min hr₁0 hr₂0, ?_⟩
  intro x hx i
  have hx1 : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : ‖x‖ < r₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hU : IsUnit (matToCLM (fun a b => whitePullbackMetric κ hκ hKc q x a b)) :=
    (hpkg q hq x hx2).2.1
  -- `ĝ⁻¹(x)·x = x`
  have hinvrad : (∑ j, whitePullbackMetricInv κ hκ hKc q x i j * x j) = x i := by
    have hgx : ∀ j, x j = ∑ k, whitePullbackMetric κ hκ hKc q x j k * x k :=
      fun j => (hmet x hx1 j).symm
    calc (∑ j, whitePullbackMetricInv κ hκ hKc q x i j * x j)
        = ∑ j, whitePullbackMetricInv κ hκ hKc q x i j
            * (∑ k, whitePullbackMetric κ hκ hKc q x j k * x k) :=
          Finset.sum_congr rfl fun j _ => by rw [← hgx j]
      _ = ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
            * (whitePullbackMetric κ hκ hKc q x j k * x k) :=
          Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
      _ = ∑ k, (∑ j, whitePullbackMetricInv κ hκ hKc q x i j
            * whitePullbackMetric κ hκ hKc q x j k) * x k := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k, (if i = k then (1 : ℝ) else 0) * x k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          congr 1
          exact sum_invMat_mul (fun a b => whitePullbackMetric κ hκ hKc q x a b) hU i k
      _ = x i := sum_delta_mul x i
  calc (∑ j, (whitePullbackMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j)
      = (∑ j, whitePullbackMetricInv κ hκ hKc q x i j * x j)
        - ∑ j, (if i = j then (1 : ℝ) else 0) * x j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = x i - x i := by rw [hinvrad, sum_delta_mul x i]
    _ = 0 := sub_self _

/-! ### §4. ★★ The K1 budget REWIRED — `hGauss` gone. -/

/-- **★★ `white_K1BudgetW_of_transport_gaussFree` — the J4-636 K1 `t²` budget with the `hGauss`
    input DISCHARGED.**  Under the FOUR remaining labelled transport inputs {hwsm, h0, h1, hΔ}
    (+`w ≥ 2` and the `H`-side data), the budget `K1TransportBudgetW w H (whiteDefect1 … r₀)`
    holds for EVERY gate radius `r₀ ≤ rG`, where `rG > 0` is the discharged Gauss gate of §3.
    The K1 input list after this brick: `{hwsm, h0, h1, hΔ}` — `hGauss` is no longer carried.
    ⚠ CONDITIONAL on the four remaining labelled inputs; NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_of_transport_gaussFree (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (w C_Δ : ℝ)
    (hw2 : 2 ≤ w) (hCΔ : 0 ≤ C_Δ)
    (hwsm : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) k)) :
    ∃ rG > (0 : ℝ), ∀ r₀ : ℝ, r₀ ≤ rG →
      (∀ x : Point n, ‖x‖ < r₀ →
        totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0) →
      (∀ x : Point n, ‖x‖ < r₀ →
        totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0) →
      (∀ x : Point n, ‖x‖ < r₀ →
        |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ) →
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (ζ : Point n), 0 < a →
          |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        K1TransportBudgetW w H (whiteDefect1 κ hκ hKc q r₀) := by
  obtain ⟨rG, hrG0, hG⟩ := whiteGauss_discharged κ hκ hKc q hq
  refine ⟨rG, hrG0, ?_⟩
  intro r₀ hr₀ h0 h1 hΔ H C_H hCH hH hH0
  exact white_K1BudgetW_of_transport κ hκ hKc q r₀ w C_Δ hw2 hCΔ hwsm
    (fun x hx i => hG x (lt_of_lt_of_le hx hr₀) i) h0 h1 hΔ H C_H hCH hH hH0

/-! ### §5. Non-vacuity gates (cp466 discipline). -/

/-- **★ The witness gate** — the discharged `hGauss` is EXERCISED at the genuinely curved witness
    (`n = 2`, `κ = −1`, `q = (1,1)` inside the fat ball `closedBall 0 2` — the same row where the
    as-built chart provably fails the δ-frame, `white_vs_asBuilt_frame_gate`): the gate radius is
    positive AND a NONZERO gate point satisfies the discharged identity — the statement is not a
    `{0}`-collapse.  (`Ric(0) = (n−1)κ·δ ≠ 0` at `κ = −1`, `n = 2`:
    `curvedRNCMetric_ricci_trace_diag_ne` — the base geometry is NOT secretly flat.) -/
theorem whiteGauss_witness_gate :
    ∃ r₀ > (0 : ℝ), ∃ x : Point 2, x ≠ 0 ∧ ‖x‖ < r₀ ∧ ∀ i : Fin 2,
      (∑ j, (whitePullbackMetricInv (-1) (by norm_num)
          (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) x i j
        - (if i = j then (1 : ℝ) else 0)) * x j) = 0 := by
  have hq : ((fun _ => 1) : Point 2) ∈ Metric.closedBall (0 : Point 2) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => ?_) one_le_two
    simp
  obtain ⟨r₀, hr₀0, hG⟩ := whiteGauss_discharged (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) hq
  have hb : ‖(fun _ => r₀ / 2 : Point 2)‖ ≤ r₀ / 2 := by
    refine pi_norm_le_iff_of_nonneg (by linarith) |>.mpr fun i => ?_
    show ‖r₀ / 2‖ ≤ r₀ / 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r₀ / 2)]
  refine ⟨r₀, hr₀0, (fun _ => r₀ / 2), ?_, ?_, ?_⟩
  · intro hx0
    have h := congrFun hx0 (0 : Fin 2)
    rw [Pi.zero_apply] at h
    linarith
  · linarith
  · intro i
    exact hG _ (by linarith) i

end QIQTH.WhiteGauss

section AxiomChecks
open QIQTH.WhiteGauss
#print axioms QIQTH.WhiteGauss.contract_swap
#print axioms QIQTH.WhiteGauss.uniformFlow_gauss_radial
#print axioms QIQTH.WhiteGauss.whitePullbackMetric_gauss
#print axioms QIQTH.WhiteGauss.whiteGauss_discharged
#print axioms QIQTH.WhiteGauss.white_K1BudgetW_of_transport_gaussFree
#print axioms QIQTH.WhiteGauss.whiteGauss_witness_gate
end AxiomChecks
