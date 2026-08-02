/-
  ResidualN1GaussianBound — J4-103: the ORDER-`N = 1` residual Gaussian bound (the genuinely new
  brick of the order-`N` rebuild after J4-102's `OrderNResidual` firewall).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS BUILT HERE (the honest boundary — read it).

  J4-102 (`OrderNResidual`) built the `N`-generic PLUMBING (near packet consumer, `N`-parametric
  witness) + the `N = 1` DIAGONAL algebraic tail, and FIREWALLED the actual `N = 1` residual GAUSSIAN
  bound (the analogue of `residualN0_gaussian_bound_C3`).  This file discharges that firewall via the
  EXACT ALGEBRAIC SPLIT of the order-1 parametrix into two order-0 parametrices.

    • `foldedCoeff_shift` — the profile-shift identity (B1): `foldedCoeff Θ (fun j => u (j+1)) k =
      foldedCoeff Θ u (k+1)` (definitional — `rfl`).  So the shifted profile `u' := fun j => u (j+1)`
      has `foldedCoeff Θ u' 0 = w₁`, letting the `w₁` profile be handled by the SAME `N = 0` machinery.

    • `heatParametrix_one_split` — the algebraic split `H₁(s,x) = H₀[u](s,x) + s·H₀[u'](s,x)`, i.e.
      `gauss·(w₀ + s·w₁) = gauss·w₀ + s·gauss·w₁` (pure re-association of the folded ansatz).

    • `heatParametrix_differentiableAt_time` / `heatParametrix_contDiff_space` — the two regularity
      helpers (time-differentiability of `H_N(·,v)` for `t > 0`; spatial `C^∞` of `H_N(t,·)`).

    • `parametrixResidual_one_split` — ★ THE EXACT `N = 1` RESIDUAL SPLIT.  From the ansatz split, the
      product rule in `t`, and `Δ_g`-linearity,
        `parametrixResidualN 1 g gi Θ u t v
           = parametrixResidualN 0 g gi Θ u t v
             + heatParametrix 0 Θ u' t v
             + t · parametrixResidualN 0 g gi Θ u' t v` ,   `u' := fun j => u (j+1)` .
      The three summands: (i) the `N = 0` residual with `w₀`; (ii) the `gauss·w₁` middle term; (iii)
      `t` times the `N = 0` residual with the shifted profile `w₁`.  (Only `hw` and `ht`; the metric
      is arbitrary.)

    • `residualN1_gaussian_bound` — ★ THE FIXED-`t` `N = 1` RESIDUAL GAUSSIAN BOUND (B3).  Near the
      RNC centre,
        `|parametrixResidualN 1 g gi Θ u t v|
           ≤ ((1 + 32·n²·M·W₀ + L₀) + W₁ + t·(1 + 32·n²·M·W₁ + L₁)) · gaussDdimWide t v` ,
      assembling (i) via `residualN0_gaussian_bound` at the `w₀` data, (iii) via the SAME bound at the
      shifted `w₁` data (profile-shift), and (ii) via `|w₁| ≤ W₁` and `gaussDdim ≤ gaussDdimWide`.
      The constant is `(C₀ + W₁) + t·C₁` — the honest `C₀ + C₁·t` shape.

    • `residualN1_gaussianWide_ball` — the explicit-radius `hEnear` ball shape at `N = 1`, obtained by
      converting the `∀ᶠ` bound to an explicit `‖·‖`-ball (`Metric.eventually_nhds_iff`) and feeding
      `near_uncutResidual_gaussianWide_ball_from_packet_one` (J4-102).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  This is the FIXED-`t` `N = 1` bound (constant `C₀ + C₁·t` may depend on
  the fixed `t`).  It is NOT a `τ`-uniform `∀ τ > 0` bound against `baseKernelW 2 0`: the raw `N = 1`
  residual has a genuine `t·(…)` tail term that GROWS linearly in `τ` at the diagonal, so no `τ`-free
  `α = 0` constant exists (confirmed: the sharp `τ`-uniform shape needs the `α = 1` margin
  `baseKernelW 2 1` via the transport cancellation, or the coarse `(1+τ)` prefactor; and the Duhamel
  simplex only needs `τ ∈ (0,t]` anyway — the current capstone's `∀ τ` is stronger than the small-time
  `a₁ = R/6` theory requires).  Every hypothesis is genuine and load-bearing; the `w₁` jet data
  (`hw1flat`/`hw1hessRicci`/`hw1bd`/`hlap1`) has the SAME shape as `w₀`'s and is satisfiable by an
  actual second folded DeWitt coefficient.  NO `expRho`, NOT `a₁ = R/6`.  No `sorry`, no new axioms,
  no vacuous hypotheses.
-/
import Mathlib
import QIQTH.ParametrixResidualN0Bound
import QIQTH.HeatParametrixOrder
import QIQTH.OrderNResidual

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### #1 — the profile-shift identity (B1) and the algebraic ansatz split. -/

/-- **★ J4-103 (B1) — THE PROFILE-SHIFT IDENTITY.**  The folded coefficient of the shifted profile
    `u' = fun j => u (j+1)` at index `k` is the folded coefficient of `u` at index `k+1`:
        `foldedCoeff Θ (fun j => u (j+1)) k = foldedCoeff Θ u (k+1)` .
    Definitional (`rfl`), since `foldedCoeff Θ v k = fun y => Θ(y)^{−1/2}·v k y` reads `v` only through
    `v k`, and `(fun j => u (j+1)) k = u (k+1)`.  In particular `foldedCoeff Θ u' 0 = w₁`, so the `w₁`
    profile is handled by the SAME `N = 0` machinery at the shifted profile. -/
theorem foldedCoeff_shift (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (k : ℕ) :
    foldedCoeff Θ (fun j => u (j + 1)) k = foldedCoeff Θ u (k + 1) := rfl

/-- **★ J4-103 — THE ORDER-1 ANSATZ SPLIT.**  The order-1 folded parametrix is the order-0 parametrix
    of `u` plus `s` times the order-0 parametrix of the shifted profile `u' = fun j => u (j+1)`:
        `H₁(s,x) = H₀[u](s,x) + s·H₀[u'](s,x)` ,   i.e.  `gauss·(w₀ + s·w₁) = gauss·w₀ + s·gauss·w₁` .
    Pure re-association of the folded ansatz (`Finset.range 2 = {0,1}`). -/
theorem heatParametrix_one_split (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (s : ℝ) (x : Point n) :
    heatParametrix 1 Θ u s x
      = heatParametrix 0 Θ u s x + s * heatParametrix 0 Θ (fun j => u (j + 1)) s x := by
  simp only [heatParametrix, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

/-! ### #2 — the two regularity helpers. -/

/-- **Time-differentiability of the parametrix at a fixed point** (for `t > 0`).  `s ↦ H_N(s,v)` is
    differentiable at every `t > 0`, being the product of the smooth Gaussian factor `s ↦ gauss(s,v)`
    (finite product of `heatKernel1D`) and the polynomial `s ↦ Σ_k w_k(v)·s^k`. -/
theorem heatParametrix_differentiableAt_time (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (v : Point n) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun s => heatParametrix N Θ u s v) t := by
  have hderiv_fun : (fun s => heatParametrix N Θ u s v)
      = (fun s => gaussDdim s v * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * s ^ k) :=
    funext (fun s => heatParametrix_folded N Θ u s v)
  rw [hderiv_fun]
  have hgaussHD : HasDerivAt (fun s => gaussDdim s v) (deriv (fun s => gaussDdim s v) t) t := by
    have hFP := HasDerivAt.fun_finsetProd
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        heatKernel1D_hasDerivAt_t t (v i) ht)
    exact hFP.differentiableAt.hasDerivAt
  have hpoly : HasDerivAt (fun s => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * s ^ k)
      (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1))) t := by
    have key : HasDerivAt (∑ k ∈ Finset.range (N + 1), fun s : ℝ => foldedCoeff Θ u k v * s ^ k)
        (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1))) t :=
      HasDerivAt.sum (fun k _ => (hasDerivAt_pow k t).const_mul (foldedCoeff Θ u k v))
    have hfun : (∑ k ∈ Finset.range (N + 1), fun s : ℝ => foldedCoeff Θ u k v * s ^ k)
        = (fun s => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * s ^ k) := by
      funext s; simp only [Finset.sum_apply]
    rw [hfun] at key; exact key
  exact (hgaussHD.mul hpoly).differentiableAt

/-- **Spatial `C^∞` of the parametrix at a fixed time.**  `y ↦ H_N(t,y)` is `ContDiff ℝ ⊤`, being the
    product of the smooth Gaussian `gauss(t,·)` and the smooth folded polynomial `Σ_k w_k(·)·t^k`. -/
theorem heatParametrix_contDiff_space (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    ContDiff ℝ ⊤ (heatParametrix N Θ u t) := by
  have hHeq : heatParametrix N Θ u t
      = (fun y => gaussDdim t y * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) :=
    funext (fun y => heatParametrix_folded N Θ u t y)
  rw [hHeq]
  exact (gaussDdim_contDiff t).mul (ContDiff.sum fun k _ => (hw k).mul contDiff_const)

/-! ### #3 — the exact `N = 1` residual split. -/

/-- **★ J4-103 — THE EXACT `N = 1` RESIDUAL SPLIT.**  With the shifted profile `u' = fun j => u (j+1)`
    (so `foldedCoeff Θ u' 0 = w₁`), the heat-operator residual of the order-1 parametrix decomposes as
        `parametrixResidualN 1 g gi Θ u t v
           = parametrixResidualN 0 g gi Θ u t v
             + heatParametrix 0 Θ u' t v
             + t · parametrixResidualN 0 g gi Θ u' t v` .
    PROOF.  From the ansatz split `H₁ = H₀[u] + s·H₀[u']`: the time derivative uses the product rule
    `∂_s(s·H₀[u']) = H₀[u'] + s·∂_s H₀[u']`, and `Δ_g` is linear (`laplaceBeltrami_add`,
    `laplaceBeltrami_const_mul`).  Subtracting term-by-term regroups into the three summands.  (Only
    coefficient smoothness `hw` and `t > 0`; the metric is arbitrary.)  NOT `a₁ = R/6`. -/
theorem parametrixResidual_one_split (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    parametrixResidualN 1 g gi Θ u t v
      = parametrixResidualN 0 g gi Θ u t v
        + heatParametrix 0 Θ (fun j => u (j + 1)) t v
        + t * parametrixResidualN 0 g gi Θ (fun j => u (j + 1)) t v := by
  -- (A) the time-derivative split via the product rule.
  have hf : HasDerivAt (fun s => heatParametrix 0 Θ u s v)
      (deriv (fun s => heatParametrix 0 Θ u s v) t) t :=
    (heatParametrix_differentiableAt_time 0 Θ u v ht).hasDerivAt
  have hg' : HasDerivAt (fun s => heatParametrix 0 Θ (fun j => u (j + 1)) s v)
      (deriv (fun s => heatParametrix 0 Θ (fun j => u (j + 1)) s v) t) t :=
    (heatParametrix_differentiableAt_time 0 Θ (fun j => u (j + 1)) v ht).hasDerivAt
  have hidt : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h1 : HasDerivAt
      (fun s => heatParametrix 0 Θ u s v + s * heatParametrix 0 Θ (fun j => u (j + 1)) s v)
      (deriv (fun s => heatParametrix 0 Θ u s v) t
        + (1 * heatParametrix 0 Θ (fun j => u (j + 1)) t v
           + t * deriv (fun s => heatParametrix 0 Θ (fun j => u (j + 1)) s v) t)) t :=
    hf.add (hidt.mul hg')
  have hderiv : deriv (fun s => heatParametrix 1 Θ u s v) t
      = deriv (fun s => heatParametrix 0 Θ u s v) t
        + heatParametrix 0 Θ (fun j => u (j + 1)) t v
        + t * deriv (fun s => heatParametrix 0 Θ (fun j => u (j + 1)) s v) t := by
    have hsplit : (fun s => heatParametrix 1 Θ u s v)
        = (fun s => heatParametrix 0 Θ u s v + s * heatParametrix 0 Θ (fun j => u (j + 1)) s v) := by
      funext s; exact heatParametrix_one_split Θ u s v
    rw [hsplit, h1.deriv]; ring
  -- (B) the `Δ_g` split via linearity.
  have hlap : laplaceBeltrami g gi (heatParametrix 1 Θ u t) v
      = laplaceBeltrami g gi (heatParametrix 0 Θ u t) v
        + t * laplaceBeltrami g gi (heatParametrix 0 Θ (fun j => u (j + 1)) t) v := by
    have hHeq : heatParametrix 1 Θ u t
        = (fun y => heatParametrix 0 Θ u t y
            + (fun z => t * heatParametrix 0 Θ (fun j => u (j + 1)) t z) y) := by
      funext y
      show heatParametrix 1 Θ u t y
          = heatParametrix 0 Θ u t y + t * heatParametrix 0 Θ (fun j => u (j + 1)) t y
      exact heatParametrix_one_split Θ u t y
    rw [hHeq,
      laplaceBeltrami_add g gi (heatParametrix 0 Θ u t)
        (fun z => t * heatParametrix 0 Θ (fun j => u (j + 1)) t z) v
        (heatParametrix_contDiff_space 0 Θ u t hw)
        (contDiff_const.mul
          (heatParametrix_contDiff_space 0 Θ (fun j => u (j + 1)) t (fun k => hw (k + 1)))),
      laplaceBeltrami_const_mul g gi t (heatParametrix 0 Θ (fun j => u (j + 1)) t) v
        (heatParametrix_contDiff_space 0 Θ (fun j => u (j + 1)) t (fun k => hw (k + 1)))]
  -- (C) assemble.
  unfold parametrixResidualN
  rw [hderiv, hlap]; ring

/-! ### #4 — the fixed-`t` `N = 1` residual Gaussian bound (B3). -/

/-- **★ J4-103 (B3) — THE FIXED-`t` `N = 1` PARAMETRIX-RESIDUAL GAUSSIAN BOUND.**  Near the RNC centre,
        `|parametrixResidualN 1 g gi Θ u t v|
           ≤ ((1 + 32·n²·M·W₀ + L₀) + W₁ + t·(1 + 32·n²·M·W₁ + L₁)) · gaussDdimWide t v`   (∀ᶠ `v`).
    From `parametrixResidual_one_split` and the triangle inequality: (i) the `w₀` residual via
    `residualN0_gaussian_bound` (constant `C₀ = 1 + 32·n²·M·W₀ + L₀`); (iii) the shifted `w₁` residual
    times `t` via the SAME bound at the shifted profile `u' = fun j => u (j+1)` (constant
    `C₁ = 1 + 32·n²·M·W₁ + L₁`, profile-shift `foldedCoeff Θ u' 0 = w₁`); (ii) the middle term
    `gauss·w₁` via `|w₁| ≤ W₁` and `gaussDdim ≤ gaussDdimWide`.  The constant `(C₀ + W₁) + t·C₁` is the
    honest `C₀ + C₁·t` shape (fixed-`t`; the `t·(…)` tail forbids a `τ`-free `∀ τ` `α = 0` bound — see
    the module note).  The `w₁` jet data `hw1flat`/`hw1hessRicci`/`hw1bd`/`hlap1` mirrors `w₀`'s and is
    satisfiable.  NOT `a₁ = R/6`. -/
theorem residualN1_gaussian_bound
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hCd : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    -- `w₀` jet data:
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 0 0)
    -- `w₁` jet data (same shape as `w₀`'s, satisfiable by the second folded DeWitt coefficient):
    (hw1flat : ∀ e, pd (foldedCoeff Θ u 1) e (0 : Point n) = 0)
    (hw1hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 1) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 1) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 1 0)
    {t : ℝ} (ht : 0 < t) (M W₀ L₀ W₁ L₁ : ℝ) (hM : 0 ≤ M) (hW₀ : 0 ≤ W₀) (hW₁ : 0 ≤ W₁)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W₀)
    (hlap0 : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L₀)
    (hw1bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 1 v| ≤ W₁)
    (hlap1 : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 1) v| ≤ L₁) :
    ∀ᶠ v in nhds (0 : Point n),
      |parametrixResidualN 1 g gi Θ u t v|
        ≤ ((1 + 32 * (n : ℝ) ^ 2 * M * W₀ + L₀) + W₁
            + t * (1 + 32 * (n : ℝ) ^ 2 * M * W₁ + L₁)) * gaussDdimWide t v := by
  -- term (i): the `N = 0` residual with the `w₀` data.
  have hbound0 := residualN0_gaussian_bound g gi Θ u hg hgiC hCd hw hg0 hgi0 hdg0 hdgi0 hΓ0
    hsymm hinv hgauge hw0flat hw0hessRicci ht M W₀ L₀ hM hW₀ hdev hw0bd hlap0
  -- term (iii): the `N = 0` residual with the SHIFTED profile `u' = fun j => u (j+1)` (`w₁` data).
  have hbound1 := residualN0_gaussian_bound g gi Θ (fun j => u (j + 1)) hg hgiC hCd
    (fun k => hw (k + 1)) hg0 hgi0 hdg0 hdgi0 hΓ0 hsymm hinv hgauge hw1flat hw1hessRicci ht M W₁ L₁
    hM hW₁ hdev hw1bd hlap1
  -- term (ii): the middle term `gauss·w₁`.
  have hmid : ∀ᶠ v in nhds (0 : Point n),
      |heatParametrix 0 Θ (fun j => u (j + 1)) t v| ≤ W₁ * gaussDdimWide t v := by
    filter_upwards [hw1bd] with v hv
    have hfold : heatParametrix 0 Θ (fun j => u (j + 1)) t v
        = gaussDdim t v * foldedCoeff Θ (fun j => u (j + 1)) 0 v := by
      rw [heatParametrix_folded, Finset.sum_range_one, pow_zero, mul_one]
    rw [hfold, abs_mul, abs_of_nonneg (gaussDdim_nonneg t v)]
    have hv' : |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W₁ := hv
    calc gaussDdim t v * |foldedCoeff Θ (fun j => u (j + 1)) 0 v|
        ≤ gaussDdim t v * W₁ := mul_le_mul_of_nonneg_left hv' (gaussDdim_nonneg t v)
      _ ≤ gaussDdimWide t v * W₁ :=
          mul_le_mul_of_nonneg_right (gaussDdim_le_gaussDdimWide ht v) hW₁
      _ = W₁ * gaussDdimWide t v := by ring
  -- assemble via the residual split and the triangle inequality.
  filter_upwards [hbound0, hbound1, hmid] with v h0 h1 hm
  rw [parametrixResidual_one_split g gi Θ u t ht v hw]
  set Gw : ℝ := gaussDdimWide t v with hGw
  set A : ℝ := parametrixResidualN 0 g gi Θ u t v with hA
  set B : ℝ := heatParametrix 0 Θ (fun j => u (j + 1)) t v with hB
  set D : ℝ := parametrixResidualN 0 g gi Θ (fun j => u (j + 1)) t v with hD
  have htD : t * |D| ≤ t * ((1 + 32 * (n : ℝ) ^ 2 * M * W₁ + L₁) * Gw) :=
    mul_le_mul_of_nonneg_left h1 ht.le
  calc |A + B + t * D|
      ≤ |A + B| + |t * D| := abs_add_le _ _
    _ ≤ (|A| + |B|) + |t * D| := add_le_add (abs_add_le _ _) le_rfl
    _ = (|A| + |B|) + t * |D| := by rw [abs_mul, abs_of_pos ht]
    _ ≤ ((1 + 32 * (n : ℝ) ^ 2 * M * W₀ + L₀) * Gw + W₁ * Gw)
          + t * ((1 + 32 * (n : ℝ) ^ 2 * M * W₁ + L₁) * Gw) :=
        add_le_add (add_le_add h0 hm) htD
    _ = ((1 + 32 * (n : ℝ) ^ 2 * M * W₀ + L₀) + W₁
          + t * (1 + 32 * (n : ℝ) ^ 2 * M * W₁ + L₁)) * Gw := by ring

/-- **★ J4-103 — THE `N = 1` `hEnear` BALL SHAPE.**  The explicit-radius near-diagonal residual bound
    for the CONCRETE order-1 parametrix `H = heatParametrix 1 Θ u t`, obtained by converting the `∀ᶠ`
    bound `residualN1_gaussian_bound` to an explicit `‖·‖`-ball (`Metric.eventually_nhds_iff`) and
    feeding `near_uncutResidual_gaussianWide_ball_from_packet_one` (J4-102):
      `∃ b > 0, ∀ w, rncRadialSq w ≤ b² →
         |∂_t(heatParametrix 1 Θ u · t)(w) − Δ_g(heatParametrix 1 Θ u t)(w)| ≤ C · gaussDdimWide t w` ,
    with `C = (1 + 32·n²·M·W₀ + L₀) + W₁ + t·(1 + 32·n²·M·W₁ + L₁)`.  This is the `hEnear` carry at
    `N = 1` — the order-1 analogue of `near_uncutResidual_gaussianWide_ball_C3`.  NOT `a₁ = R/6`. -/
theorem residualN1_gaussianWide_ball
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hCd : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 0 0)
    (hw1flat : ∀ e, pd (foldedCoeff Θ u 1) e (0 : Point n) = 0)
    (hw1hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 1) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 1) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 1 0)
    {t : ℝ} (ht : 0 < t) (M W₀ L₀ W₁ L₁ : ℝ) (hM : 0 ≤ M) (hW₀ : 0 ≤ W₀) (hW₁ : 0 ≤ W₁)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W₀)
    (hlap0 : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L₀)
    (hw1bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 1 v| ≤ W₁)
    (hlap1 : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 1) v| ≤ L₁) :
    ∃ b : ℝ, 0 < b ∧
      ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |deriv (fun s => heatParametrix 1 Θ u s w) t
            - laplaceBeltrami g gi (heatParametrix 1 Θ u t) w|
          ≤ ((1 + 32 * (n : ℝ) ^ 2 * M * W₀ + L₀) + W₁
              + t * (1 + 32 * (n : ℝ) ^ 2 * M * W₁ + L₁)) * gaussDdimWide t w := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (residualN1_gaussian_bound g gi Θ u hg hgiC hCd hw hg0 hgi0 hdg0 hdgi0 hΓ0 hsymm hinv hgauge
      hw0flat hw0hessRicci hw1flat hw1hessRicci ht M W₀ L₀ W₁ L₁ hM hW₀ hW₁ hdev hw0bd hlap0 hw1bd
      hlap1)
  exact near_uncutResidual_gaussianWide_ball_from_packet_one g gi Θ u
    ((1 + 32 * (n : ℝ) ^ 2 * M * W₀ + L₀) + W₁ + t * (1 + 32 * (n : ℝ) ^ 2 * M * W₁ + L₁)) ε hε
    (fun v hv => hball (by rw [dist_eq_norm, sub_zero]; exact hv))

end QIQTH.HeatResidualBound
