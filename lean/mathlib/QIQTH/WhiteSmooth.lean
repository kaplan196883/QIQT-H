/-
  WhiteSmooth — J4-639: the `hwsm` rung — the C¹-vs-⊤ BINDER WALL read + the sanctioned
  C²-WEAKENED K1 budget variant.  ONE brick of the `a₁ = R/6` heat-kernel campaign.
  NOT `a₁ = R/6`; proves NOTHING about the coefficient value.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★ THE ORDER READ (the brick's first half — banked smoothness per layer, verified in-repo).
    • The WhiteOrder1/WhiteDelta `hwsm` binder demands `∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ̂ û k)`,
      and in this toolchain `(⊤ : WithTop ℕ∞) = ω` is the ANALYTIC level (the J4-174/J4-175
      structural finding).  So the binder as stated asks for ω-analyticity of ALL folded
      transported coefficients — GLOBALLY.
    • The banked `hu`/`hw` tower (HuInftyRebase, J4-175) closes the ENTIRE family at `∞`
      (`hu_infty_closed` + `hw_discharged_infty`), but ONLY GIVEN `ω`-smooth metric entries
      {hg, hgi} + `det g > 0`.  The ray-integral solve `radialTransportSolve` reaches every
      finite order and `∞` (`radialTransportSolve_contDiff_infty`) but NOT `ω` — the honest
      Mathlib gap.  So even with an analytic metric the literal `⊤`-binder is UNREACHABLE;
      with the `∞`-rebase it is reachable at `∞ ≥` any finite order.
    • At the WHITENED chart data the metric-smoothness input itself is the wall: the flow chart
      is banked at `ContDiffAt ℝ 4` per interior point (`uniformFlowExp_contDiffAt_four`,
      `contDiffAt3_uniformFlowExp`) and the pullback metric `g̃` only at the two-Fréchet-layer
      `IsC2At` level (`uniformFlowPullbackMetric_entry_isC2At`); NO global `ContDiff` of
      `whitePullbackMetric` (any order, let alone `ω`) is banked.  Hence the honest achievable
      GLOBAL order `k*` for `w₁ = Θ̂^{−1/2}·û₁` from the banked chain alone is: NONE banked
      unconditionally; `∞` conditionally on whitened-metric `ω`-smoothness (+ `det > 0`).
  ★ THE CONSUMER AUDIT (what the K1 chain ACTUALLY uses of `hwsm`).
    • The N = 1 residual layer regrouping and the cancellation: only FIRST partials of `w₀, w₁`
      (`pd`-splits) and, through the banked general-`N` engine, the `Δ_g(G·P)` Leibniz split —
      i.e. `C²` AT the evaluation point, for `k ≤ 1` ONLY (the `∀ k` is a binder artifact:
      `P = w₀ + t·w₁` never touches `k ≥ 2`).
    • The `hΔ` discharge (WhiteDelta §2): continuity of the 1-jet/2-jet sums on a compact gate
      ball — GLOBAL `C²` of `w₁` suffices (finite, not `⊤`).
  ⟹ THE SANCTIONED FALLBACK BUILT HERE: the C²-weakened variant of the ENTIRE K1 chain.
      §0  `pd`/`Δ_g`/`r∂_r` linearity of `f + h·t` at `ContDiffAt ℝ 2` (eventual-congr localization).
      §1  the N = 1 residual decomposition → absorbed → assembled-O1 → 4-layer regroup → the
          LINEAR-GAIN cancellation, all with hypotheses `ContDiffAt ℝ 2` of `w₀, w₁` AT the point
          (down from `∀ k, ContDiff ℝ ⊤` GLOBAL) — the finite-regularity replay in the proved
          R1/R3b (LaplaceBeltramiFiniteReg / ResidualN0FiniteReg) pattern, extended to N = 1.
      §2  `whiteDefect1_linear_gain_C2` + `white_K1BudgetW_of_transport_C2` — the J4-636 K1 `t²`
          budget consuming only the gate-local C² pair {hw0, hw1} (k ≤ 1!) instead of `hwsm`.
      §3  `contDiff_pd_one`/`continuous_pd_of_contDiff_one` (finite-order `pd` calculus) +
          `smooth_jet_bounds_on_closedBall_C2` + `whiteDelta_discharged_C2` — the J4-638 `hΔ`
          discharge re-based at GLOBAL `ContDiff ℝ 2` of `w₁` (down from `⊤`).
      §4  ★★ `white_K1BudgetW_C2_gaussDeltaFree` — the K1 budget with hGauss (J4-637) and hΔ
          (J4-638, re-proved at C²) discharged, conditional ONLY on {hw0C2, hw1C2, h0, h1}:
          THE K1 INPUT LIST AFTER THIS BRICK: `{hw0C2, hw1C2, h0, h1}` — the old `hwsm`
          (`∀ k`, global, `ω`) is REPLACED by global `C²` of the TWO coefficients `w₀, w₁`.
      §5  the achievable-order supplier: `white_foldedCoeff_contDiff_infty_of_metric_smooth`
          (`∞`-smoothness of ALL folded whitened coefficients GIVEN whitened-metric
          `ω`-smoothness + positivity, via the banked HuInftyRebase tower) + the downcast
          `white_hwsm2_of_metric_smooth` + ★ `white_K1BudgetW_of_metric_smooth` (K1 from
          {metric-smoothness, h0, h1}).
      §6  gates (cp466): the flat C² antecedent inhabitance + END-TO-END firing of the NEW C²
          cancellation chain (`flat_N1_residual_vanishes_C2`, unconditional); the monotonicity
          record `hwsm_top_implies_pair_C2` (the variant consumes a STRICTLY weaker input — no
          silent strengthening); the curved-witness gate for the C² `hΔ` discharge
          (`whiteSmooth_witness_gate`, conditional on exactly the C² pair).

  ⚠ HONEST SCOPE (binding).
    • The C² pair {hw0C2 = `ContDiff ℝ 2 w₀`, hw1C2 = `ContDiff ℝ 2 w₁`} at the whitened chart
      data is NOT discharged here: `w₀ = Θ̂^{−1/2}` needs global C² of the whitened van-Vleck
      determinant (the chart bank stops at per-point `IsC2At`/`ContDiffAt 4`), and `w₁` needs
      the ray-integral solve at a C¹ source — the scoped residue.  The §5 supplier reduces the
      pair to whitened-metric `ω`-smoothness — a strictly stronger but structurally banked-shaped
      input (the HuInftyRebase antecedent); its discharge at the whitened chart is the frontier.
    • `a₁ = R/6` remains CONDITIONAL: the flat tower is closed and non-vacuous; the curved side
      still owes the discharge of the K1 inputs — now `{hw0C2, hw1C2, h0, h1}` (this brick
      strictly weakened the regularity input from `∀ k` global `ω` to `k ≤ 1` global `C²`) —
      + the Duhamel-split integrability carry + the fat-`K` carrier piles + the capstone
      co-instantiation at the whitened witness + the prior analytic piles.
  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.WhiteDelta
import QIQTH.ResidualN0FiniteReg
import QIQTH.LaplaceBeltramiFiniteReg
import QIQTH.HuInftyRebase

open Finset Filter Topology Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.VanVleck QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.WhiteWitness QIQTH.WhiteReplay QIQTH.WhiteOffDiag QIQTH.WhiteAmbient
open QIQTH.WhiteAnnulus QIQTH.WidthFree QIQTH.WhiteCapstoneWire
open QIQTH.WhiteOrder1 QIQTH.WhiteGauss QIQTH.WhiteDelta
open scoped ContDiff

namespace QIQTH.WhiteSmooth

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §0. Linearity of `pd` / `Δ_g` / `r∂_r` on `f + h·t` at finite regularity. -/

/-- `∂ⱼ(f + h·t) = ∂ⱼf + (∂ⱼh)·t` at `C¹` (pointwise). -/
theorem pd_add_mul_const_C1 (f h : Point n → ℝ) (t : ℝ) (j : Fin n) (y : Point n)
    (hf : ContDiffAt ℝ 1 f y) (hh : ContDiffAt ℝ 1 h y) :
    pd (fun z => f z + h z * t) j y = pd f j y + pd h j y * t := by
  have hPf : PdiffAt f j y := PdiffAt_of_contDiffAt f j y hf
  have hPh : PdiffAt h j y := PdiffAt_of_contDiffAt h j y hh
  have hcomm : (fun z => f z + h z * t) = fun z => f z + t * h z :=
    funext fun z => by ring
  have hPth : PdiffAt (fun z => t * h z) j y := by
    simp only [PdiffAt] at hPh ⊢
    exact hPh.const_mul t
  rw [hcomm, pd_add f (fun z => t * h z) j y hPf hPth, pd_const_mul t h j y hPh]
  ring

/-- `∂ᵢ∂ⱼ(f + h·t) = ∂ᵢ∂ⱼf + (∂ᵢ∂ⱼh)·t` at `C²` (eventual-congr localization of the first
    partial, then the `pd` algebra one level up). -/
theorem pd_pd_add_mul_const_C2 (f h : Point n → ℝ) (t : ℝ) (i j : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x) :
    pd (fun y => pd (fun z => f z + h z * t) j y) i x
      = pd (fun y => pd f j y) i x + pd (fun y => pd h j y) i x * t := by
  have hev : ∀ᶠ y in nhds x,
      pd (fun z => f z + h z * t) j y = pd f j y + pd h j y * t := by
    filter_upwards [hf.eventually (by norm_num), hh.eventually (by norm_num)] with y hfy hhy
    exact pd_add_mul_const_C1 f h t j y (hfy.of_le (by norm_num)) (hhy.of_le (by norm_num))
  rw [pd_congr_nhds i x hev]
  have hPf : PdiffAt (fun y => pd f j y) i x := PdiffAt_pd_of_contDiffAt f j i x hf
  have hPh : PdiffAt (fun y => pd h j y) i x := PdiffAt_pd_of_contDiffAt h j i x hh
  have hcomm : (fun y => pd f j y + pd h j y * t)
      = fun y => pd f j y + t * pd h j y := funext fun y => by ring
  have hPth : PdiffAt (fun y => t * pd h j y) i x := by
    simp only [PdiffAt] at hPh ⊢
    exact hPh.const_mul t
  rw [hcomm, pd_add _ _ i x hPf hPth, pd_const_mul t _ i x hPh]
  ring

/-- `Δ_g(f + h·t) = Δ_g f + (Δ_g h)·t` at `C²` — the linearity the two-term parametrix
    polynomial needs (metric/Christoffel enter only as values). -/
theorem laplaceBeltrami_add_mul_const_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (f h : Point n → ℝ) (t : ℝ) (x : Point n)
    (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x) :
    laplaceBeltrami g gi (fun y => f y + h y * t) x
      = laplaceBeltrami g gi f x + laplaceBeltrami g gi h x * t := by
  simp only [laplaceBeltrami]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := pd_pd_add_mul_const_C2 f h t i j x hf hh
  have hΓ : (∑ k, christoffel g gi k i j x * pd (fun z => f z + h z * t) k x)
      = (∑ k, christoffel g gi k i j x * pd f k x)
        + (∑ k, christoffel g gi k i j x * pd h k x) * t := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_add_mul_const_C1 f h t k x (hf.of_le (by norm_num)) (hh.of_le (by norm_num))]
    ring
  rw [h2, hΓ]
  ring

/-- `r∂_r(f + h·t) = r∂_r f + (r∂_r h)·t` at `C¹`. -/
theorem radialDeriv_add_mul_const_C1 (f h : Point n → ℝ) (t : ℝ) (v : Point n)
    (hf : ContDiffAt ℝ 1 f v) (hh : ContDiffAt ℝ 1 h v) :
    radialDeriv (fun y => f y + h y * t) v = radialDeriv f v + radialDeriv h v * t := by
  simp only [radialDeriv]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_add_mul_const_C1 f h t i v hf hh]
  ring

/-! ### §1. The N = 1 residual chain at `ContDiffAt ℝ 2` (the finite-regularity replay). -/

/-- **`N = 1` off-diagonal residual decomposition at `C²`** — the finite-regularity analogue of
    `parametrixResidual_offdiag_decomp` at `N = 1`, in the proved R3b pattern
    (`parametrixResidual_offdiag_decomp_N0_C2`): the ONLY smoothness used is `ContDiffAt ℝ 2`
    of `w₀, w₁` AT `v` (down from `∀ k, ContDiff ℝ ⊤` GLOBAL). -/
theorem parametrixResidual_offdiag_decomp_N1_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v)
    (hw1 : ContDiffAt ℝ 2 (foldedCoeff Θ u 1) v) :
    parametrixResidualN 1 g gi Θ u t v
      = (deriv (fun s => gaussDdim s v) t - laplaceBeltrami g gi (gaussDdim t) v)
          * (∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
            * (∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
        - gaussDdim t v
            * (∑ k ∈ Finset.range (1 + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        - (∑ i, ∑ j, gi v i j
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
  have hPfun : (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k)
      = fun y => foldedCoeff Θ u 0 y + foldedCoeff Θ u 1 y * t := by
    funext y
    rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, mul_one]
  -- (A) the `t`-derivative of `H₁(·,v)` via the product rule
  have hgaussHD : HasDerivAt (fun s => gaussDdim s v)
      (deriv (fun s => gaussDdim s v) t) t := by
    have hFP := HasDerivAt.fun_finsetProd
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        heatKernel1D_hasDerivAt_t t (v i) ht)
    exact hFP.differentiableAt.hasDerivAt
  have hpoly : HasDerivAt
      (fun s => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * s ^ k)
      (∑ k ∈ Finset.range (1 + 1),
        foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1))) t := by
    have key : HasDerivAt
        (∑ k ∈ Finset.range (1 + 1), fun s : ℝ => foldedCoeff Θ u k v * s ^ k)
        (∑ k ∈ Finset.range (1 + 1),
          foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1))) t :=
      HasDerivAt.sum (fun k _ => (hasDerivAt_pow k t).const_mul (foldedCoeff Θ u k v))
    have hfun : (∑ k ∈ Finset.range (1 + 1), fun s : ℝ => foldedCoeff Θ u k v * s ^ k)
        = (fun s => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * s ^ k) := by
      funext s; simp only [Finset.sum_apply]
    rw [hfun] at key
    exact key
  have hderiv_fun : (fun s => heatParametrix 1 Θ u s v)
      = (fun s => gaussDdim s v
          * ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * s ^ k) :=
    funext (fun s => heatParametrix_folded 1 Θ u s v)
  have hderivval : deriv (fun s => heatParametrix 1 Θ u s v) t
      = deriv (fun s => gaussDdim s v) t
          * (∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
          * ∑ k ∈ Finset.range (1 + 1),
              foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)) := by
    rw [hderiv_fun]; exact (hgaussHD.mul hpoly).deriv
  -- (B) the `Δ_g` of `H₁(t,·)` via the un-symmetrised `C²` product rule
  have hHeq : heatParametrix 1 Θ u t
      = (fun y => gaussDdim t y * ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) :=
    funext (fun y => heatParametrix_folded 1 Θ u t y)
  have hCDg : ContDiffAt ℝ 2 (fun y => gaussDdim t y) v :=
    (gaussDdim_contDiff t).contDiffAt.of_le le_top
  have hCDP : ContDiffAt ℝ 2
      (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) v := by
    rw [hPfun]
    exact hw0.add (hw1.mul contDiffAt_const)
  have hΔsum : laplaceBeltrami g gi
        (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) v
      = ∑ k ∈ Finset.range (1 + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k := by
    rw [hPfun, laplaceBeltrami_add_mul_const_C2 g gi _ _ t v hw0 hw1,
      Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, mul_one]
  have hΔval : laplaceBeltrami g gi (heatParametrix 1 Θ u t) v
      = laplaceBeltrami g gi (gaussDdim t) v
          * (∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
          * (∑ k ∈ Finset.range (1 + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        + ∑ i, ∑ j, gi v i j
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) i v) := by
    rw [hHeq,
        laplaceBeltrami_mul_mixed_C2 g gi (fun y => gaussDdim t y)
          (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) v hCDg hCDP,
        hΔsum]
  unfold parametrixResidualN
  rw [hderivval, hΔval]
  ring

/-- **`N = 1` off-diagonal absorption identity at `C²`** — the flat cross-gradient is absorbed
    into the radial transport (`flatCrossTerm_eq`, no smoothness); decomposition from
    `parametrixResidual_offdiag_decomp_N1_C2`. -/
theorem parametrixResidual_offdiag_absorbed_N1_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v)
    (hw1 : ContDiffAt ℝ 2 (foldedCoeff Θ u 1) v) :
    parametrixResidualN 1 g gi Θ u t v
      = (deriv (fun s => gaussDdim s v) t - laplaceBeltrami g gi (gaussDdim t) v)
          * (∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
            * (∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
        + (1 / t) * gaussDdim t v
            * radialDeriv (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) v
        - gaussDdim t v
            * (∑ k ∈ Finset.range (1 + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        - (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
  have hsplit : (∑ i, ∑ j, gi v i j
        * (pd (fun y => gaussDdim t y) i v
              * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) j v
          + pd (fun y => gaussDdim t y) j v
              * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) i v))
      = (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
          * (pd (fun y => gaussDdim t y) i v
                * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) j v
            + pd (fun y => gaussDdim t y) j v
                * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) i v))
        + (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0)
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [parametrixResidual_offdiag_decomp_N1_C2 g gi Θ u t ht v hw0 hw1, hsplit,
      flatCrossTerm_eq t ht
        (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) v]
  ring

/-- **`N = 1` assembled `O(1/t)` residual at `C²`** — the finite-regularity analogue of the
    banked `parametrixResidual_offdiag_O1_total` at `N = 1` (statement shape VERBATIM); the
    three transform lemmas carry no `w`-smoothness, the radial split is `r∂_r`-linearity at
    `C¹`, and the absorption needs `C²` at `v` only. -/
theorem parametrixResidual_offdiag_O1_total_N1_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v)
    (hw1 : ContDiffAt ℝ 2 (foldedCoeff Θ u 1) v) :
    parametrixResidualN 1 g gi Θ u t v
      = ((1 / t) * gaussDdim t v
            * ((1 / 2) * (∑ i, (gi v i i - 1))
                - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k))
          + (1 / t ^ 2) * gaussDdim t v
            * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))))
          * (∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
            * (∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
        + ((1 / t) * gaussDdim t v * radialDeriv (foldedCoeff Θ u 0) v
            + gaussDdim t v
                * ∑ k ∈ Finset.range 1, radialDeriv (foldedCoeff Θ u (k + 1)) v * t ^ k)
        - gaussDdim t v
            * (∑ k ∈ Finset.range (1 + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        - (1 / t) * gaussDdim t v
            * ((-1 / 2) * ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
                * (v i * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) j v
                    + v j * pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
  have ht' : t ≠ 0 := ne_of_gt ht
  have hPfun : (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k)
      = fun y => foldedCoeff Θ u 0 y + foldedCoeff Θ u 1 y * t := by
    funext y
    rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, mul_one]
  have hRT : (1 / t) * gaussDdim t v
        * radialDeriv (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) v
      = (1 / t) * gaussDdim t v * radialDeriv (foldedCoeff Θ u 0) v
        + gaussDdim t v
            * ∑ k ∈ Finset.range 1, radialDeriv (foldedCoeff Θ u (k + 1)) v * t ^ k := by
    rw [hPfun, radialDeriv_add_mul_const_C1 _ _ t v
        (hw0.of_le (by norm_num)) (hw1.of_le (by norm_num)),
      Finset.sum_range_one, pow_zero, mul_one]
    field_simp
  rw [parametrixResidual_offdiag_absorbed_N1_C2 g gi Θ u t ht v hw0 hw1,
      flatCurvatureResidue_leading_parametrix 1 g gi Θ u t ht v, hRT,
      deviationCrossTerm_leading_parametrix 1 gi Θ u t ht v]

/-- **★ The N = 1 residual in exact `t`-layers at `C²`** — the finite-regularity analogue of
    `WhiteOrder1.parametrixResidual_N1_layers`: hypotheses `ContDiffAt ℝ 2` of `w₀, w₁` AT `v`
    (down from `∀ k, ContDiff ℝ ⊤`); identical conclusion. -/
theorem parametrixResidual_N1_layers_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v)
    (hw1 : ContDiffAt ℝ 2 (foldedCoeff Θ u 1) v) :
    parametrixResidualN 1 g gi Θ u t v
      = (1 / t ^ 2) * gaussDdim t v
          * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
          * foldedCoeff Θ u 0 v
        + (1 / t) * gaussDdim t v
          * (totalRadialO1_coeff g gi Θ u v
              + (-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))
                * foldedCoeff Θ u 1 v)
        + gaussDdim t v * totalRadialO1_coeff_level1 g gi Θ u v
        - t * gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 1) v := by
  have ht' : t ≠ 0 := ne_of_gt ht
  -- the pd-split of the two-term parametrix polynomial (now at `C¹` pointwise)
  have hP : ∀ j : Fin n,
      pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) j v
        = pd (foldedCoeff Θ u 0) j v + t * pd (foldedCoeff Θ u 1) j v := by
    intro j
    have hfun : (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k)
        = fun y => foldedCoeff Θ u 0 y + t * foldedCoeff Θ u 1 y := by
      funext y
      rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, mul_one]
      ring
    have hd0 : PdiffAt (foldedCoeff Θ u 0) j v :=
      PdiffAt_of_contDiffAt (foldedCoeff Θ u 0) j v (hw0.of_le (by norm_num))
    have hd1 : PdiffAt (foldedCoeff Θ u 1) j v :=
      PdiffAt_of_contDiffAt (foldedCoeff Θ u 1) j v (hw1.of_le (by norm_num))
    have hd1' : PdiffAt (fun y => t * foldedCoeff Θ u 1 y) j v := by
      simp only [PdiffAt] at hd1 ⊢
      exact hd1.const_mul t
    rw [hfun, pd_add _ _ j v hd0 hd1', pd_const_mul t (foldedCoeff Θ u 1) j v hd1]
  rw [parametrixResidual_offdiag_O1_total_N1_C2 g gi Θ u t ht v hw0 hw1]
  simp only [hP]
  -- split the deviation cross-sum into its w₀ and w₁ parts
  have hIV : (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * (pd (foldedCoeff Θ u 0) j v + t * pd (foldedCoeff Θ u 1) j v)
            + v j * (pd (foldedCoeff Θ u 0) i v + t * pd (foldedCoeff Θ u 1) i v)))
      = (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
          * (v i * pd (foldedCoeff Θ u 0) j v + v j * pd (foldedCoeff Θ u 0) i v))
        + t * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
          * (v i * pd (foldedCoeff Θ u 1) j v + v j * pd (foldedCoeff Θ u 1) i v)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hIV]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, mul_one, Nat.cast_zero, Nat.cast_one, Nat.sub_self,
    Nat.zero_sub, mul_zero, add_zero, zero_add]
  unfold totalRadialO1_coeff totalRadialO1_coeff_level1
  field_simp
  ring

/-- **★★ THE ORDER-1 CANCELLATION AT `C²`** — the finite-regularity linear-gain identity:
    given the radial compatibility, `K₀ = 0`, `K₁ = 0` and only `ContDiffAt ℝ 2` of `w₀, w₁`
    at `v`, the full N = 1 residual collapses to `−t·G·Δ_g w₁`.  Mirror of
    `WhiteOrder1.parametrixResidual_N1_linear_gain` with the `⊤` binder GONE. -/
theorem parametrixResidual_N1_linear_gain_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v)
    (hw1 : ContDiffAt ℝ 2 (foldedCoeff Θ u 1) v)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (h0 : totalRadialO1_coeff g gi Θ u v = 0)
    (h1 : totalRadialO1_coeff_level1 g gi Θ u v = 0) :
    parametrixResidualN 1 g gi Θ u t v
      = -(t * gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 1) v) := by
  have hB : (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hfac : (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))
        = v i * (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfac, hGauss i, mul_zero]
  rw [parametrixResidual_N1_layers_C2 g gi Θ u t ht v hw0 hw1, hB, h0, h1]
  ring

/-! ### §2. The C²-weakened linear-gain column bound and K1 budget at the whitened witness. -/

/-- **★ The linear-gain column bound at gate-local `C²`** — mirror of
    `WhiteOrder1.whiteDefect1_linear_gain` with `hwsm` (`∀ k`, global `⊤`) REPLACED by the
    gate-local C² pair `hwsm2` (`k ≤ 1` only, `ContDiffAt ℝ 2` at gate points). -/
theorem whiteDefect1_linear_gain_C2 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ w C_Δ : ℝ) (hw1 : 1 ≤ w) (hCΔ : 0 ≤ C_Δ)
    (hwsm2 : ∀ x : Point n, ‖x‖ < r₀ →
      ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0) x
      ∧ ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x)
    (hGauss : ∀ x : Point n, ‖x‖ < r₀ → ∀ i,
      (∑ j, (whiteMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (h0 : ∀ x : Point n, ‖x‖ < r₀ →
      totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0)
    (h1 : ∀ x : Point n, ‖x‖ < r₀ →
      totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0)
    (hΔ : ∀ x : Point n, ‖x‖ < r₀ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ) :
    ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |whiteDefect1 κ hκ hKc q r₀ s p 0|
        ≤ (Real.sqrt w ^ n * C_Δ) * (s * gaussDdim (w * s) (p - 0)) := by
  intro s p hs hs1
  rw [sub_zero]
  have hG0 : 0 ≤ gaussDdim (w * s) p := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  by_cases hp : ‖p‖ < r₀
  · have hval : whiteDefect1 κ hκ hKc q r₀ s p (0 : Point n)
        = parametrixResidualN 1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
            (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) s p := by
      unfold whiteDefect1
      rw [if_pos ⟨hs, hs1, hp⟩]
    rw [hval, parametrixResidual_N1_linear_gain_C2 _ _ _ _ s hs p
      (hwsm2 p hp).1 (hwsm2 p hp).2 (hGauss p hp) (h0 p hp) (h1 p hp), abs_neg]
    have hGs : 0 < gaussDdim s p := gaussDdim_pos s hs p
    have hwid : gaussDdim s p ≤ Real.sqrt w ^ n * gaussDdim (w * s) p := by
      have h := gaussDdim_le_of_width_le 1 w one_pos hw1 (τ := s) hs p
      rwa [one_mul, div_one] at h
    calc |s * gaussDdim s p
          * laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
              (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) p|
        = s * gaussDdim s p
          * |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
              (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) p| := by
          rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hGs]
      _ ≤ s * gaussDdim s p * C_Δ := by
          exact mul_le_mul_of_nonneg_left (hΔ p hp)
            (mul_nonneg hs.le hGs.le)
      _ ≤ s * (Real.sqrt w ^ n * gaussDdim (w * s) p) * C_Δ := by
          have := mul_le_mul_of_nonneg_left hwid hs.le
          exact mul_le_mul_of_nonneg_right this hCΔ
      _ = (Real.sqrt w ^ n * C_Δ) * (s * gaussDdim (w * s) p) := by ring
  · have hval : whiteDefect1 κ hκ hKc q r₀ s p (0 : Point n) = 0 := by
      unfold whiteDefect1
      rw [if_neg (fun h => hp h.2.2)]
    rw [hval, abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hCΔ)
      (mul_nonneg hs.le hG0)

/-- **★★ `white_K1BudgetW_of_transport_C2` — the J4-636 K1 `t²` budget with the `hwsm` binder
    WEAKENED to the gate-local C² pair** (the sanctioned fallback of the C¹-vs-⊤ wall): same
    conclusion `K1TransportBudgetW w H (whiteDefect1 …)`, inputs now
    {hwsm2 (k ≤ 1, `ContDiffAt ℝ 2` at gate points), hGauss, h0, h1, hΔ}.  NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_of_transport_C2 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ w C_Δ : ℝ) (hw2 : 2 ≤ w) (hCΔ : 0 ≤ C_Δ)
    (hwsm2 : ∀ x : Point n, ‖x‖ < r₀ →
      ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0) x
      ∧ ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x)
    (hGauss : ∀ x : Point n, ‖x‖ < r₀ → ∀ i,
      (∑ j, (whiteMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (h0 : ∀ x : Point n, ‖x‖ < r₀ →
      totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0)
    (h1 : ∀ x : Point n, ‖x‖ < r₀ →
      totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0)
    (hΔ : ∀ x : Point n, ‖x‖ < r₀ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ)
    (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ) (hCH : 0 ≤ C_H)
    (hH : ∀ (a : ℝ) (ζ : Point n), 0 < a →
      |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ))
    (hH0 : ∀ ζ : Point n, H 0 0 ζ = 0) :
    K1TransportBudgetW w H (whiteDefect1 κ hκ hKc q r₀) := by
  have hw1 : (1 : ℝ) ≤ w := le_trans one_le_two hw2
  exact k1BudgetW_of_pointwise_linear_gain w hw2 (whiteDefect1 κ hκ hKc q r₀)
    (Real.sqrt w ^ n * C_Δ)
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hCΔ)
    (whiteDefect1_linear_gain_C2 κ hκ hKc q r₀ w C_Δ hw1 hCΔ hwsm2 hGauss h0 h1 hΔ)
    H C_H hCH hH hH0

/-! ### §3. The finite-order `pd` calculus and the `hΔ` discharge at `C²`. -/

/-- `∂ᵢ` of a global `C²` scalar is globally `C¹`. -/
theorem contDiff_pd_one (f : Point n → ℝ) (hf : ContDiff ℝ 2 f) (i : Fin n) :
    ContDiff ℝ 1 (fun y => pd f i y) := by
  have heq : (fun y => pd f i y) = fun y => fderiv ℝ f y (Pi.single i (1 : ℝ)) := by
    funext y
    exact pd_eq_fderiv f i y ((hf.differentiable (by norm_num)).differentiableAt)
  rw [heq]
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- `∂ᵢ` of a global `C¹` scalar is continuous. -/
theorem continuous_pd_of_contDiff_one (f : Point n → ℝ) (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (fun y => pd f i y) := by
  have heq : (fun y => pd f i y) = fun y => fderiv ℝ f y (Pi.single i (1 : ℝ)) := by
    funext y
    exact pd_eq_fderiv f i y ((hf.differentiable (by norm_num)).differentiableAt)
  rw [heq]
  exact ((hf.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous

/-- **First/second partial-sum bounds of a GLOBAL `C²` scalar on a closed ball** — the
    finite-regularity analogue of `WhiteDelta.smooth_jet_bounds_on_closedBall` (`⊤` → `C²`). -/
theorem smooth_jet_bounds_on_closedBall_C2 (f : Point n → ℝ) (hf : ContDiff ℝ 2 f) (r : ℝ) :
    ∃ M1 M2 : ℝ, 0 ≤ M1 ∧ 0 ≤ M2 ∧ ∀ x : Point n, ‖x‖ ≤ r →
      (∑ k, |pd f k x|) ≤ M1 ∧ (∑ i, ∑ j, |pd (fun y => pd f j y) i x|) ≤ M2 := by
  classical
  have hc1 : Continuous fun x : Point n => ∑ k, |pd f k x| :=
    continuous_finsetSum _ fun k _ => ((contDiff_pd_one f hf k).continuous).abs
  have hc2 : Continuous fun x : Point n => ∑ i, ∑ j, |pd (fun y => pd f j y) i x| :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_pd_of_contDiff_one (fun y => pd f j y) (contDiff_pd_one f hf j) i).abs
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

/-- **★ `whiteDelta_discharged_C2` — the `hΔ` existence GIVEN only GLOBAL `C²` of `w₁`** —
    the J4-638 discharge re-based at finite regularity (`⊤` → `ContDiff ℝ 2`); mechanism
    identical (banked suppliers `whiteInv_entry_bound` + `whiteChart_christoffel_linear_uniform`
    feed the operator decomposition; C² compactness feeds the jet sums). -/
theorem whiteDelta_discharged_C2 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (hwsm1C2 : ContDiff ℝ 2
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1)) :
    ∃ rΔ > (0 : ℝ), ∃ C_Δ : ℝ, 0 ≤ C_Δ ∧ ∀ x : Point n, ‖x‖ < rΔ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ := by
  classical
  obtain ⟨r₁, hr₁0, Gb, hGb0, hgib⟩ := whiteInv_entry_bound κ hκ hKc
  obtain ⟨rΓ, hrΓ0, CΓ, hCΓ0, hΓ⟩ := whiteChart_christoffel_linear_uniform κ hκ hKc
  set rΔ : ℝ := min r₁ rΓ with hrΔdef
  have hrΔ0 : 0 < rΔ := lt_min hr₁0 hrΓ0
  obtain ⟨M1, M2, hM10, hM20, hM⟩ := smooth_jet_bounds_on_closedBall_C2
    (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) hwsm1C2 rΔ
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

/-! ### §4. ★★ The assembled C² K1 budget — hGauss and hΔ discharged, C² pair carried. -/

/-- **★★ `white_K1BudgetW_C2_gaussDeltaFree` — the K1 `t²` budget with `hGauss` (J4-637) and
    `hΔ` (re-proved at C², §3) DISCHARGED and the regularity input weakened to the GLOBAL C²
    pair {hw0C2, hw1C2} (`k ≤ 1` only).**
    THE K1 INPUT LIST AFTER THIS BRICK: `{hw0C2, hw1C2, h0, h1}` — strictly weaker than the
    previous `{hwsm (∀ k, global ω), h0, h1}`.  ⚠ CONDITIONAL; NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_C2_gaussDeltaFree (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (w : ℝ) (hw2 : 2 ≤ w)
    (hw0C2 : ContDiff ℝ 2
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0))
    (hw1C2 : ContDiff ℝ 2
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1)) :
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
  obtain ⟨rΔ, hrΔ0, C_Δ, hCΔ0, hΔd⟩ := whiteDelta_discharged_C2 κ hκ hKc q hq hw1C2
  refine ⟨min rG rΔ, lt_min hrG0 hrΔ0, ?_⟩
  intro r₀ hr₀ h0 h1 H C_H hCH hH hH0
  exact white_K1BudgetW_of_transport_C2 κ hκ hKc q r₀ w C_Δ hw2 hCΔ0
    (fun _x _ => ⟨hw0C2.contDiffAt, hw1C2.contDiffAt⟩)
    (fun x hx i => hG x (lt_of_lt_of_le hx (hr₀.trans (min_le_left _ _))) i)
    h0 h1
    (fun x hx => hΔd x (lt_of_lt_of_le hx (hr₀.trans (min_le_right _ _))))
    H C_H hCH hH hH0

/-! ### §5. The achievable-order supplier: metric smoothness ⟹ the C² pair (via the ∞ tower). -/

/-- **The achievable-order regularity of ALL whitened folded coefficients** — `ContDiff ℝ ∞`
    (every finite order; NOT `ω = ⊤`, the honest ray-integral wall), GIVEN `ω`-smooth whitened
    metric entries + positivity: the banked HuInftyRebase tower (`hu_infty_closed` +
    `hw_discharged_infty`) instantiated at the whitened chart data of row `q`.
    ⚠ The metric-smoothness antecedent is NOT banked for the whitened chart (only per-point
    `IsC2At`/`ContDiffAt 4` flow regularity is) — this is the scoped supplier reduction, not a
    discharge. -/
theorem white_foldedCoeff_contDiff_infty_of_metric_smooth (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun w => whiteMetric κ hκ hKc q w a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun w => whiteMetricInv κ hκ hKc q w a b))
    (hgpos : ∀ w : Point n, 0 < Matrix.det (whiteMetric κ hκ hKc q w)) :
    ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) k) := by
  have hu := QIQTH.HuInftyRebase.hu_infty_closed
    (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) hg hgi hgpos
  have hw := QIQTH.HuInftyRebase.hw_discharged_infty
    (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) hg hgpos hu
  exact hw

/-- The downcast `∞ → C²` of the supplier: metric smoothness delivers the EXACT C² pair the
    §4 budget consumes. -/
theorem white_hwsm2_of_metric_smooth (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun w => whiteMetric κ hκ hKc q w a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun w => whiteMetricInv κ hκ hKc q w a b))
    (hgpos : ∀ w : Point n, 0 < Matrix.det (whiteMetric κ hκ hKc q w)) :
    ContDiff ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0)
    ∧ ContDiff ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) := by
  have h := white_foldedCoeff_contDiff_infty_of_metric_smooth κ hκ hKc q hg hgi hgpos
  have hle : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h := (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)); simpa using h
  exact ⟨(h 0).of_le hle, (h 1).of_le hle⟩

/-- **★ `white_K1BudgetW_of_metric_smooth` — the K1 reduction capstone of this brick**: the
    K1 `t²` budget conditional on {whitened-metric `ω`-smoothness + positivity, h0, h1} — the
    regularity leg of the K1 input list reduced through the C² variant to the structural
    HuInftyRebase antecedent.  ⚠ CONDITIONAL; the metric-smoothness antecedent at the whitened
    chart is the cited frontier; NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_of_metric_smooth (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (w : ℝ) (hw2 : 2 ≤ w)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun w => whiteMetric κ hκ hKc q w a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun w => whiteMetricInv κ hκ hKc q w a b))
    (hgpos : ∀ w : Point n, 0 < Matrix.det (whiteMetric κ hκ hKc q w)) :
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
  obtain ⟨hw0C2, hw1C2⟩ := white_hwsm2_of_metric_smooth κ hκ hKc q hg hgi hgpos
  exact white_K1BudgetW_C2_gaussDeltaFree κ hκ hKc q hq w hw2 hw0C2 hw1C2

/-! ### §6. Non-vacuity gates (cp466 discipline). -/

/-- **★ Monotonicity record — NO silent strengthening**: the OLD `hwsm` binder
    (`∀ k, ContDiff ℝ ⊤`, global, all `k`) IMPLIES the NEW gate-local C² pair — the variant
    consumes a strictly weaker input (weakening certified, at every gate radius). -/
theorem hwsm_top_implies_pair_C2 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ : ℝ)
    (hwsm : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) k)) :
    ∀ x : Point n, ‖x‖ < r₀ →
      ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0) x
      ∧ ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x :=
  fun _x _ => ⟨((hwsm 0).of_le le_top).contDiffAt, ((hwsm 1).of_le le_top).contDiffAt⟩

/-- **★ END-TO-END firing of the NEW C² cancellation chain at the flat witness** — the flat
    data (`g = gi = δ`, `Θ ≡ 1`, `u = (1,0,…)`) satisfy the C² antecedents (constants), the
    C² chain applies, and the residual provably vanishes THROUGH
    `parametrixResidual_N1_linear_gain_C2` — the new finite-regularity theorems are
    non-degenerate end-to-end at an explicit witness (UNCONDITIONAL). -/
theorem flat_N1_residual_vanishes_C2 (t : ℝ) (ht : 0 < t) (v : Point n) :
    parametrixResidualN 1
      (fun _ : Point n => fun i j : Fin n => if i = j then (1 : ℝ) else 0)
      (fun _ : Point n => fun i j : Fin n => if i = j then (1 : ℝ) else 0)
      (fun _ : Point n => (1 : ℝ)) (fun k _ => if k = 0 then (1 : ℝ) else 0) t v = 0 := by
  obtain ⟨hw, hG, h0, h1⟩ := flat_order1_hyps_inhabited (n := n)
  have hw0 : ContDiffAt ℝ 2 (foldedCoeff (fun _ : Point n => (1 : ℝ))
      (fun k _ => if k = 0 then (1 : ℝ) else 0) 0) v := ((hw 0).of_le le_top).contDiffAt
  have hw1 : ContDiffAt ℝ 2 (foldedCoeff (fun _ : Point n => (1 : ℝ))
      (fun k _ => if k = 0 then (1 : ℝ) else 0) 1) v := ((hw 1).of_le le_top).contDiffAt
  rw [parametrixResidual_N1_linear_gain_C2 _ _ _ _ t ht v hw0 hw1 (hG v) (h0 v) (h1 v)]
  have hfold1 : foldedCoeff (fun _ : Point n => (1 : ℝ))
      (fun k _ => if k = 0 then (1 : ℝ) else 0) 1 = fun _ : Point n => (0 : ℝ) := by
    funext y
    simp [foldedCoeff]
  rw [hfold1, laplaceBeltrami_const]
  ring

/-- **★ The curved-witness gate for the C² `hΔ` discharge** — at the genuinely curved witness
    (`n = 2`, `κ = −1`, `q = (1,1)` in the fat ball), GIVEN exactly the GLOBAL C² of `w₁`
    (the new, strictly weaker antecedent — nothing else), the §3 discharge instantiates to a
    positive gate with a NONZERO gate point carrying the `hΔ` bound (no `{0}`-collapse).
    The honest antecedent record: ONLY the C² pair blocks unconditional instantiation. -/
theorem whiteSmooth_witness_gate
    (hw1C2 : ContDiff ℝ 2 (foldedCoeff
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
  obtain ⟨r₀, hr₀0, C_Δ, hCΔ0, hΔd⟩ := whiteDelta_discharged_C2 (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) hq hw1C2
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

end QIQTH.WhiteSmooth

section AxiomChecks
open QIQTH.WhiteSmooth
#print axioms QIQTH.WhiteSmooth.pd_add_mul_const_C1
#print axioms QIQTH.WhiteSmooth.pd_pd_add_mul_const_C2
#print axioms QIQTH.WhiteSmooth.laplaceBeltrami_add_mul_const_C2
#print axioms QIQTH.WhiteSmooth.radialDeriv_add_mul_const_C1
#print axioms QIQTH.WhiteSmooth.parametrixResidual_offdiag_decomp_N1_C2
#print axioms QIQTH.WhiteSmooth.parametrixResidual_offdiag_absorbed_N1_C2
#print axioms QIQTH.WhiteSmooth.parametrixResidual_offdiag_O1_total_N1_C2
#print axioms QIQTH.WhiteSmooth.parametrixResidual_N1_layers_C2
#print axioms QIQTH.WhiteSmooth.parametrixResidual_N1_linear_gain_C2
#print axioms QIQTH.WhiteSmooth.whiteDefect1_linear_gain_C2
#print axioms QIQTH.WhiteSmooth.white_K1BudgetW_of_transport_C2
#print axioms QIQTH.WhiteSmooth.contDiff_pd_one
#print axioms QIQTH.WhiteSmooth.continuous_pd_of_contDiff_one
#print axioms QIQTH.WhiteSmooth.smooth_jet_bounds_on_closedBall_C2
#print axioms QIQTH.WhiteSmooth.whiteDelta_discharged_C2
#print axioms QIQTH.WhiteSmooth.white_K1BudgetW_C2_gaussDeltaFree
#print axioms QIQTH.WhiteSmooth.white_foldedCoeff_contDiff_infty_of_metric_smooth
#print axioms QIQTH.WhiteSmooth.white_hwsm2_of_metric_smooth
#print axioms QIQTH.WhiteSmooth.white_K1BudgetW_of_metric_smooth
#print axioms QIQTH.WhiteSmooth.hwsm_top_implies_pair_C2
#print axioms QIQTH.WhiteSmooth.flat_N1_residual_vanishes_C2
#print axioms QIQTH.WhiteSmooth.whiteSmooth_witness_gate
end AxiomChecks
