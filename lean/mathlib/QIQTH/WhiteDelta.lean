/-
  WhiteDelta — J4-638: `hΔ` AT THE WHITENED CHART, DISCHARGED (conditional ONLY on `hwsm`).

  THE BRICK.  After J4-637 (WhiteGauss) the K1 `t²` budget `white_K1BudgetW_of_transport`
  (WhiteOrder1) carries FOUR labelled transport inputs {hwsm, h0, h1, hΔ}.  This file discharges
  `hΔ` — the gate-uniform remainder-amplitude bound
      `∀ x, ‖x‖ < r₀ → |Δ_{ĝ_q} w₁(x)| ≤ C_Δ`,   `w₁ = foldedCoeff Θ̂ û 1 = Θ̂^{−1/2}·û₁`
  (the order-1 folded transported coefficient; `Δ_ĝ` = the whitened coordinate Laplace–Beltrami)
  — as an EXISTENCE statement (`∃ rΔ > 0, ∃ C_Δ ≥ 0, …`), GIVEN only the coefficient-smoothness
  input `hwsm` at `k = 1`.  The linear-gain identity of WhiteOrder1 makes this bound the exact
  remainder amplitude of the k = 1 budget, so no numeric value of `C_Δ` is ever consumed
  downstream — existence is the full binder shape.

  ── THE MECHANISM (the J4-637 (g) route, executed).
    §1  `laplaceBeltrami_abs_le_of_entry_bounds` — THE OPERATOR DECOMPOSITION:
            `|Δ_g f(x)| ≤ Gb·Σᵢⱼ|∂ᵢ∂ⱼf(x)| + Gb·CΓ·n²·Σₖ|∂ₖf(x)|`
        from entrywise `|g⁻¹| ≤ Gb` and `|Γ| ≤ CΓ` — the `ĝ⁻¹`-contraction of second derivatives
        + the Christoffel-contraction of first derivatives, pure `Finset`/abs algebra.
    §2  `smooth_jet_bounds_on_closedBall` — THE COEFFICIENT-DERIVATIVE BOUNDS: for `C^∞` `f`,
        the first- and second-partial sum fields are continuous (`contDiff_pd`, twice), hence
        bounded on the compact closed gate ball (`IsCompact.exists_bound_of_continuousOn`) —
        the ray-integral regularity of `û₁ = radialTransportSolve …` is NOT re-derived here:
        it enters exactly through `hwsm` (`ContDiff ℝ ⊤` of the folded coefficient), the one
        remaining regularity input.
    §3  ★ `whiteDelta_discharged` — the hΔ EXISTENCE: the banked whitened suppliers
        `whiteInv_entry_bound` (`|ĝ⁻¹| ≤ Gb`, WhiteAnnulus, J4-622 dev + δ triangle) and
        `whiteChart_christoffel_linear_uniform` (`|Γ̂| ≤ CΓ·‖x‖`, WhiteOffDiag, J4-623 linear
        decay) feed §1; `hwsm 1` feeds §2; the gate is `rΔ = min r₁ rΓ` and
        `C_Δ = Gb·M₂ + Gb·(CΓ·rΔ)·n²·M₁`.
    §4  ★★ `white_K1BudgetW_of_transport_deltaGaussFree` — THE K1 BUDGET REWIRED with BOTH
        `hGauss` (J4-637) and `hΔ` (this brick) GONE: conditional on {hwsm, h0, h1} only,
        for every gate radius `r₀ ≤ min rG rΔ`.
        THE K1 INPUT LIST AFTER THIS BRICK: `{hwsm, h0, h1}`.
    §5  Non-vacuity gates (cp466 discipline):
        `whiteDelta_supplier_gate` — UNCONDITIONAL: at the genuinely curved witness (`n = 2`,
        `κ = −1`, `q = (1,1)` — the row where the as-built frame provably fails δ and
        `Ric(0) ≠ 0`), the supplier layer (`|ĝ⁻¹| ≤ Gb`, `|Γ̂| ≤ CΓ‖x‖`) is EXERCISED at a
        NONZERO gate point — the gate is not a `{0}`-collapse and does not depend on `hwsm`;
        `whiteDelta_witness_gate` — the full discharged `hΔ` instantiated at the same witness,
        GIVEN `hwsm` at `k = 1` (the honest antecedent record: ONLY `hwsm` blocks the
        unconditional instantiation — precisely the remaining input).

  ⚠ HONEST SCOPE (binding).
    • `C_Δ` is PER-ROW `q` (the compactness sup of §2 is at fixed `q`); gate-uniformity is in `x`
      over the gate ball, exactly the `hΔ` binder shape.  A `q`-uniform `C_Δ` (fat-`K` carrier)
      would need the uniform C² packet for `û₁` — NOT claimed here, and not needed by the binder.
    • The discharge is CONDITIONAL on `hwsm` (k = 1 suffices for `hΔ`; the budget still takes the
      all-`k` `hwsm`): the smoothness of the transported coefficient `û₁` (through
      `radialTransportSolve`'s ray integral) is the one genuine regularity input left standing.
    • `a₁ = R/6` remains CONDITIONAL: the flat tower is closed and non-vacuous; the curved side
      still owes the discharge of the REMAINING K1 inputs {hwsm, h0, h1} at the whitened chart
      data (hwsm = coefficient smoothness, h0 = the checkpointed k = 0 transport identity,
      h1 = the k = 1 equation) + the Duhamel-split integrability carry + the fat-`K` carrier
      piles + the capstone co-instantiation at the whitened witness + the prior analytic piles.
      This brick removes exactly ONE of the four: `hΔ`.
  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.WhiteGauss
import QIQTH.WhiteAnnulus
import QIQTH.ChristoffelSmooth

open Finset Filter Topology Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.HeatResidualBound QIQTH.HeatTransportRecursion
open QIQTH.ExpMap QIQTH.PullbackMetric
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.WhiteWitness QIQTH.WhiteReplay QIQTH.WhiteAmbient
open QIQTH.WhiteOffDiag QIQTH.WhiteAnnulus
open QIQTH.WhiteCapstoneWire QIQTH.WhiteOrder1 QIQTH.WhiteGauss

namespace QIQTH.WhiteDelta

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §1. The operator decomposition: `|Δ_g f| ≤ ĝ⁻¹-contraction of ∂∂f + Γ-contraction of ∂f`. -/

/-- **The pointwise Laplace–Beltrami amplitude bound from entry bounds** — the operator shape of
    the `hΔ` discharge: with `|g⁻¹(x)ᵢⱼ| ≤ Gb` and `|Γ(x)ᵏᵢⱼ| ≤ CΓ`,
        `|Δ_g f(x)| ≤ Gb·(Σᵢⱼ |∂ᵢ∂ⱼf(x)|) + Gb·CΓ·n²·(Σₖ |∂ₖf(x)|)`.
    Pure `Finset`/abs algebra — no regularity used. -/
theorem laplaceBeltrami_abs_le_of_entry_bounds (g gi : Point n → Fin n → Fin n → ℝ)
    (f : Point n → ℝ) (x : Point n) (Gb CΓ : ℝ) (hGb0 : 0 ≤ Gb) (_hCΓ0 : 0 ≤ CΓ)
    (hgi : ∀ i j : Fin n, |gi x i j| ≤ Gb)
    (hΓ : ∀ k i j : Fin n, |christoffel g gi k i j x| ≤ CΓ) :
    |laplaceBeltrami g gi f x|
      ≤ Gb * (∑ i, ∑ j, |pd (fun y => pd f j y) i x|)
        + Gb * CΓ * (n : ℝ) ^ 2 * ∑ k, |pd f k x| := by
  classical
  set S1 : ℝ := ∑ k, |pd f k x| with hS1def
  -- the entrywise bound.
  have hterm : ∀ i j : Fin n,
      |gi x i j * (pd (fun y => pd f j y) i x - ∑ k, christoffel g gi k i j x * pd f k x)|
        ≤ Gb * (|pd (fun y => pd f j y) i x| + CΓ * S1) := by
    intro i j
    have hB : |∑ k, christoffel g gi k i j x * pd f k x| ≤ CΓ * S1 := by
      calc |∑ k, christoffel g gi k i j x * pd f k x|
          ≤ ∑ k, |christoffel g gi k i j x * pd f k x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k, CΓ * |pd f k x| := Finset.sum_le_sum fun k _ => by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right (hΓ k i j) (abs_nonneg _)
        _ = CΓ * S1 := by rw [hS1def, Finset.mul_sum]
    have habs : |pd (fun y => pd f j y) i x - ∑ k, christoffel g gi k i j x * pd f k x|
        ≤ |pd (fun y => pd f j y) i x| + CΓ * S1 := by
      have h1 : |pd (fun y => pd f j y) i x - ∑ k, christoffel g gi k i j x * pd f k x|
          ≤ |pd (fun y => pd f j y) i x| + |∑ k, christoffel g gi k i j x * pd f k x| := by
        calc |pd (fun y => pd f j y) i x - ∑ k, christoffel g gi k i j x * pd f k x|
            = |pd (fun y => pd f j y) i x
                + -(∑ k, christoffel g gi k i j x * pd f k x)| := by rw [sub_eq_add_neg]
          _ ≤ |pd (fun y => pd f j y) i x|
                + |-(∑ k, christoffel g gi k i j x * pd f k x)| := abs_add_le _ _
          _ = |pd (fun y => pd f j y) i x|
                + |∑ k, christoffel g gi k i j x * pd f k x| := by rw [abs_neg]
      exact h1.trans (add_le_add le_rfl hB)
    calc |gi x i j * (pd (fun y => pd f j y) i x
            - ∑ k, christoffel g gi k i j x * pd f k x)|
        = |gi x i j| * |pd (fun y => pd f j y) i x
            - ∑ k, christoffel g gi k i j x * pd f k x| := abs_mul _ _
      _ ≤ Gb * (|pd (fun y => pd f j y) i x| + CΓ * S1) :=
          mul_le_mul (hgi i j) habs (abs_nonneg _) hGb0
  -- the double-sum triangle.
  have hsum : |laplaceBeltrami g gi f x|
      ≤ ∑ i, ∑ j, Gb * (|pd (fun y => pd f j y) i x| + CΓ * S1) := by
    calc |laplaceBeltrami g gi f x|
        = |∑ i, ∑ j, gi x i j * (pd (fun y => pd f j y) i x
            - ∑ k, christoffel g gi k i j x * pd f k x)| := rfl
      _ ≤ ∑ i, |∑ j, gi x i j * (pd (fun y => pd f j y) i x
            - ∑ k, christoffel g gi k i j x * pd f k x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |gi x i j * (pd (fun y => pd f j y) i x
            - ∑ k, christoffel g gi k i j x * pd f k x)| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, Gb * (|pd (fun y => pd f j y) i x| + CΓ * S1) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  -- the closed-form of the majorant.
  have halg : (∑ i : Fin n, ∑ j : Fin n, Gb * (|pd (fun y => pd f j y) i x| + CΓ * S1))
      = Gb * (∑ i, ∑ j, |pd (fun y => pd f j y) i x|) + Gb * CΓ * (n : ℝ) ^ 2 * S1 := by
    have hrow : ∀ i : Fin n,
        (∑ j : Fin n, Gb * (|pd (fun y => pd f j y) i x| + CΓ * S1))
          = Gb * (∑ j, |pd (fun y => pd f j y) i x|) + (n : ℝ) * (Gb * (CΓ * S1)) := by
      intro i
      calc (∑ j : Fin n, Gb * (|pd (fun y => pd f j y) i x| + CΓ * S1))
          = ∑ j : Fin n, (Gb * |pd (fun y => pd f j y) i x| + Gb * (CΓ * S1)) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = (∑ j, Gb * |pd (fun y => pd f j y) i x|)
              + ∑ _j : Fin n, Gb * (CΓ * S1) := Finset.sum_add_distrib
        _ = Gb * (∑ j, |pd (fun y => pd f j y) i x|) + (n : ℝ) * (Gb * (CΓ * S1)) := by
            rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
    calc (∑ i : Fin n, ∑ j : Fin n, Gb * (|pd (fun y => pd f j y) i x| + CΓ * S1))
        = ∑ i : Fin n, (Gb * (∑ j, |pd (fun y => pd f j y) i x|)
            + (n : ℝ) * (Gb * (CΓ * S1))) := Finset.sum_congr rfl fun i _ => hrow i
      _ = (∑ i : Fin n, Gb * (∑ j, |pd (fun y => pd f j y) i x|))
            + ∑ _i : Fin n, (n : ℝ) * (Gb * (CΓ * S1)) := Finset.sum_add_distrib
      _ = Gb * (∑ i, ∑ j, |pd (fun y => pd f j y) i x|)
            + (n : ℝ) * ((n : ℝ) * (Gb * (CΓ * S1))) := by
          rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ = Gb * (∑ i, ∑ j, |pd (fun y => pd f j y) i x|) + Gb * CΓ * (n : ℝ) ^ 2 * S1 := by
          ring
  calc |laplaceBeltrami g gi f x|
      ≤ ∑ i, ∑ j, Gb * (|pd (fun y => pd f j y) i x| + CΓ * S1) := hsum
    _ = Gb * (∑ i, ∑ j, |pd (fun y => pd f j y) i x|) + Gb * CΓ * (n : ℝ) ^ 2 * S1 := halg

/-! ### §2. The coefficient-derivative bounds: smooth ⟹ 1-jet/2-jet sums bounded on the gate. -/

/-- **First/second partial-sum bounds of a `C^∞` scalar on a closed ball** — the compactness leg
    of the `hΔ` discharge: `x ↦ Σₖ|∂ₖf|` and `x ↦ Σᵢⱼ|∂ᵢ∂ⱼf|` are continuous (`contDiff_pd`,
    once and twice), hence bounded on `closedBall 0 r`.  The ray-integral regularity of the
    transported coefficient is NOT re-derived: it enters through `hf` only. -/
theorem smooth_jet_bounds_on_closedBall (f : Point n → ℝ) (hf : ContDiff ℝ ⊤ f) (r : ℝ) :
    ∃ M1 M2 : ℝ, 0 ≤ M1 ∧ 0 ≤ M2 ∧ ∀ x : Point n, ‖x‖ ≤ r →
      (∑ k, |pd f k x|) ≤ M1 ∧ (∑ i, ∑ j, |pd (fun y => pd f j y) i x|) ≤ M2 := by
  classical
  have hc1 : Continuous fun x : Point n => ∑ k, |pd f k x| :=
    continuous_finsetSum _ fun k _ => (contDiff_pd f hf k).continuous.abs
  have hc2 : Continuous fun x : Point n => ∑ i, ∑ j, |pd (fun y => pd f j y) i x| :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (contDiff_pd (fun y => pd f j y) (contDiff_pd f hf j) i).continuous.abs
  obtain ⟨C1, hC1⟩ := (isCompact_closedBall (0 : Point n) r).exists_bound_of_continuousOn
    hc1.continuousOn
  obtain ⟨C2, hC2⟩ := (isCompact_closedBall (0 : Point n) r).exists_bound_of_continuousOn
    hc2.continuousOn
  refine ⟨max C1 0, max C2 0, le_max_right _ _, le_max_right _ _, fun x hx => ?_⟩
  have hmem : x ∈ Metric.closedBall (0 : Point n) r := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hx
  constructor
  · have h := hC1 x hmem
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_max_left _ _))
  · have h := hC2 x hmem
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_max_left _ _))

/-! ### §3. ★ The `hΔ` discharge at the whitened chart data. -/

/-- **★★ `whiteDelta_discharged` — the WhiteOrder1 `hΔ` input, GIVEN only `hwsm` at `k = 1`.**
    For every `κ ≤ 0`, compact base `K`, row `q ∈ K`, if the order-1 folded transported
    coefficient `w₁ = Θ̂^{−1/2}·û₁` is `C^∞` (the `hwsm 1` input — the transport-solution
    regularity, the ONE input consumed), then there are a gate radius `rΔ > 0` and a remainder
    amplitude `C_Δ ≥ 0` with
        `∀ ‖x‖ < rΔ, |Δ_{ĝ_q} w₁(x)| ≤ C_Δ`
    — the EXACT labelled `hΔ` of `white_K1BudgetW_of_transport`.  Mechanism: the banked
    whitened suppliers `whiteInv_entry_bound` (`|ĝ⁻¹| ≤ Gb`) and
    `whiteChart_christoffel_linear_uniform` (`|Γ̂| ≤ CΓ·‖x‖ ≤ CΓ·rΔ`) feed the §1 operator
    decomposition; §2 compactness feeds the jet sums.  `C_Δ` is per-row `q` (see header scope);
    NOT `a₁ = R/6` — the K1 inputs {hwsm, h0, h1} remain owed. -/
theorem whiteDelta_discharged (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (hwsm1 : ContDiff ℝ ⊤
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1)) :
    ∃ rΔ > (0 : ℝ), ∃ C_Δ : ℝ, 0 ≤ C_Δ ∧ ∀ x : Point n, ‖x‖ < rΔ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ := by
  classical
  obtain ⟨r₁, hr₁0, Gb, hGb0, hgib⟩ := whiteInv_entry_bound κ hκ hKc
  obtain ⟨rΓ, hrΓ0, CΓ, hCΓ0, hΓ⟩ := whiteChart_christoffel_linear_uniform κ hκ hKc
  set rΔ : ℝ := min r₁ rΓ with hrΔdef
  have hrΔ0 : 0 < rΔ := lt_min hr₁0 hrΓ0
  obtain ⟨M1, M2, hM10, hM20, hM⟩ := smooth_jet_bounds_on_closedBall
    (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) hwsm1 rΔ
  have hcoef0 : 0 ≤ Gb * (CΓ * rΔ) * (n : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg hGb0 (mul_nonneg hCΓ0 hrΔ0.le))
      (pow_nonneg (Nat.cast_nonneg n) 2)
  refine ⟨rΔ, hrΔ0, Gb * M2 + Gb * (CΓ * rΔ) * (n : ℝ) ^ 2 * M1,
    add_nonneg (mul_nonneg hGb0 hM20) (mul_nonneg hcoef0 hM10), ?_⟩
  intro x hx
  have hx1 : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxΓ : ‖x‖ < rΓ := lt_of_lt_of_le hx (min_le_right _ _)
  have hbound := laplaceBeltrami_abs_le_of_entry_bounds
    (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
    (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x
    Gb (CΓ * rΔ) hGb0 (mul_nonneg hCΓ0 hrΔ0.le)
    (fun i j => hgib q hq x hx1 i j)
    (fun k i j => (hΓ q hq x hxΓ k i j).trans
      (mul_le_mul_of_nonneg_left hx.le hCΓ0))
  obtain ⟨hS1le, hS2le⟩ := hM x hx.le
  calc |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x|
      ≤ Gb * (∑ i, ∑ j, |pd (fun y =>
            pd (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) j y) i x|)
          + Gb * (CΓ * rΔ) * (n : ℝ) ^ 2
            * ∑ k, |pd (foldedCoeff (whiteTheta κ hκ hKc q)
                (whiteCoeffs κ hκ hKc q) 1) k x| := hbound
    _ ≤ Gb * M2 + Gb * (CΓ * rΔ) * (n : ℝ) ^ 2 * M1 :=
        add_le_add (mul_le_mul_of_nonneg_left hS2le hGb0)
          (mul_le_mul_of_nonneg_left hS1le hcoef0)

/-! ### §4. ★★ The K1 budget REWIRED — `hΔ` gone (and `hGauss` already gone, J4-637). -/

/-- **★★ `white_K1BudgetW_of_transport_deltaGaussFree` — the K1 `t²` budget with BOTH `hGauss`
    (J4-637) and `hΔ` (this brick) DISCHARGED.**  Under the THREE remaining labelled transport
    inputs {hwsm, h0, h1} (+`w ≥ 2` and the `H`-side data), the budget
    `K1TransportBudgetW w H (whiteDefect1 … r₀)` holds for EVERY gate radius `r₀ ≤ rGΔ`, where
    `rGΔ > 0` is the joint Gauss/Delta gate.
    THE K1 INPUT LIST AFTER THIS BRICK: `{hwsm, h0, h1}` — `hΔ` is no longer carried.
    ⚠ CONDITIONAL on the three remaining labelled inputs; NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_of_transport_deltaGaussFree (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (w : ℝ) (hw2 : 2 ≤ w)
    (hwsm : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) k)) :
    ∃ rGΔ > (0 : ℝ), ∀ r₀ : ℝ, r₀ ≤ rGΔ →
      (∀ x : Point n, ‖x‖ < r₀ →
        totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0) →
      (∀ x : Point n, ‖x‖ < r₀ →
        totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0) →
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (ζ : Point n), 0 < a →
          |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        K1TransportBudgetW w H (whiteDefect1 κ hκ hKc q r₀) := by
  obtain ⟨rG, hrG0, hG⟩ := whiteGauss_discharged κ hκ hKc q hq
  obtain ⟨rΔ, hrΔ0, C_Δ, hCΔ0, hΔd⟩ := whiteDelta_discharged κ hκ hKc q hq (hwsm 1)
  refine ⟨min rG rΔ, lt_min hrG0 hrΔ0, ?_⟩
  intro r₀ hr₀ h0 h1 H C_H hCH hH hH0
  exact white_K1BudgetW_of_transport κ hκ hKc q r₀ w C_Δ hw2 hCΔ0 hwsm
    (fun x hx i => hG x (lt_of_lt_of_le hx (hr₀.trans (min_le_left _ _))) i)
    h0 h1
    (fun x hx => hΔd x (lt_of_lt_of_le hx (hr₀.trans (min_le_right _ _))))
    H C_H hCH hH hH0

/-! ### §5. Non-vacuity gates (cp466 discipline). -/

/-- **★ The supplier gate — UNCONDITIONAL.**  At the genuinely curved witness (`n = 2`,
    `κ = −1`, `q = (1,1)` inside the fat ball `closedBall 0 2` — the row where the as-built
    chart provably fails the δ-frame and `Ric(0) = (n−1)κ·δ ≠ 0`): the DELTA gate radius is
    positive and a NONZERO gate point carries both supplier bounds (`|ĝ⁻¹| ≤ Gb`,
    `|Γ̂| ≤ CΓ·‖x‖`) — the §3 antecedent geometry is inhabited independently of `hwsm`, and
    the gate is not a `{0}`-collapse. -/
theorem whiteDelta_supplier_gate :
    ∃ r₀ > (0 : ℝ), ∃ Gb CΓ : ℝ, 0 ≤ Gb ∧ 0 ≤ CΓ ∧ ∃ x : Point 2, x ≠ 0 ∧ ‖x‖ < r₀ ∧
      (∀ i j : Fin 2, |whitePullbackMetricInv (-1) (by norm_num)
          (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) x i j| ≤ Gb) ∧
      (∀ k i j : Fin 2, |christoffel
          (fun w => whitePullbackMetric (-1) (by norm_num)
            (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) w)
          (fun w => whitePullbackMetricInv (-1) (by norm_num)
            (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) w) k i j x|
        ≤ CΓ * ‖x‖) := by
  have hq : ((fun _ => 1) : Point 2) ∈ Metric.closedBall (0 : Point 2) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => ?_) one_le_two
    simp
  obtain ⟨r₁, hr₁0, Gb, hGb0, hgib⟩ := whiteInv_entry_bound (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2)
  obtain ⟨rΓ, hrΓ0, CΓ, hCΓ0, hΓ⟩ := whiteChart_christoffel_linear_uniform (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2)
  set r₀ : ℝ := min r₁ rΓ with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hr₁0 hrΓ0
  have hb : ‖(fun _ => r₀ / 2 : Point 2)‖ ≤ r₀ / 2 := by
    refine pi_norm_le_iff_of_nonneg (by linarith) |>.mpr fun i => ?_
    show ‖r₀ / 2‖ ≤ r₀ / 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r₀ / 2)]
  have hxlt : ‖(fun _ => r₀ / 2 : Point 2)‖ < r₀ := lt_of_le_of_lt hb (by linarith)
  refine ⟨r₀, hr₀0, Gb, CΓ, hGb0, hCΓ0, (fun _ => r₀ / 2), ?_, hxlt, ?_, ?_⟩
  · intro hx0
    have h := congrFun hx0 (0 : Fin 2)
    rw [Pi.zero_apply] at h
    linarith
  · intro i j
    exact hgib _ hq _ (lt_of_lt_of_le hxlt (min_le_left _ _)) i j
  · intro k i j
    exact hΓ _ hq _ (lt_of_lt_of_le hxlt (min_le_right _ _)) k i j

/-- **★ The witness gate — the full discharged `hΔ` at the curved witness, GIVEN `hwsm 1`.**
    The honest antecedent record: at the same genuinely curved witness, the §3 discharge
    instantiates to a positive gate with a NONZERO gate point carrying the `hΔ` bound —
    conditional on exactly the ONE remaining regularity input (`hwsm` at `k = 1`), nothing
    else.  (Unconditional instantiation is blocked precisely by `hwsm` — the cited frontier.) -/
theorem whiteDelta_witness_gate
    (hwsm1 : ContDiff ℝ ⊤ (foldedCoeff
      (whiteTheta (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
      (whiteCoeffs (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1)) 1)) :
    ∃ r₀ > (0 : ℝ), ∃ C_Δ : ℝ, 0 ≤ C_Δ ∧ ∃ x : Point 2, x ≠ 0 ∧ ‖x‖ < r₀ ∧
      |laplaceBeltrami
        (whiteMetric (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        (whiteMetricInv (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        (foldedCoeff
          (whiteTheta (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
          (whiteCoeffs (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
          1) x| ≤ C_Δ := by
  have hq : ((fun _ => 1) : Point 2) ∈ Metric.closedBall (0 : Point 2) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => ?_) one_le_two
    simp
  obtain ⟨r₀, hr₀0, C_Δ, hCΔ0, hΔd⟩ := whiteDelta_discharged (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) hq hwsm1
  have hb : ‖(fun _ => r₀ / 2 : Point 2)‖ ≤ r₀ / 2 := by
    refine pi_norm_le_iff_of_nonneg (by linarith) |>.mpr fun i => ?_
    show ‖r₀ / 2‖ ≤ r₀ / 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r₀ / 2)]
  have hxlt : ‖(fun _ => r₀ / 2 : Point 2)‖ < r₀ := lt_of_le_of_lt hb (by linarith)
  refine ⟨r₀, hr₀0, C_Δ, hCΔ0, (fun _ => r₀ / 2), ?_, hxlt, hΔd _ hxlt⟩
  intro hx0
  have h := congrFun hx0 (0 : Fin 2)
  rw [Pi.zero_apply] at h
  linarith

end QIQTH.WhiteDelta

section AxiomChecks
open QIQTH.WhiteDelta
#print axioms QIQTH.WhiteDelta.laplaceBeltrami_abs_le_of_entry_bounds
#print axioms QIQTH.WhiteDelta.smooth_jet_bounds_on_closedBall
#print axioms QIQTH.WhiteDelta.whiteDelta_discharged
#print axioms QIQTH.WhiteDelta.white_K1BudgetW_of_transport_deltaGaussFree
#print axioms QIQTH.WhiteDelta.whiteDelta_supplier_gate
#print axioms QIQTH.WhiteDelta.whiteDelta_witness_gate
end AxiomChecks
