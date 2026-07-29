/-
  ParametrixResidualN0Bound — M6 / C4d: the FULL `N=0` parametrix-residual Gaussian bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS BUILT HERE (the honest boundary — read it).

  The C4d input to the Levi/Duhamel parametrix convergence (`iterConv_bound`/`leviSeries_summable`,
  C5c) is a one-step residual bound `|E(t,v)| ≤ C · baseKernel(t,v)`.  At the leading van-Vleck order
  `N = 0` the residual (`parametrixResidual_N0_O1_isolated`) is the sum of THREE terms
      `(∂_t − Δ_g)H_0(t,v)`
        `= (1/t)·G·totalRadialO1_coeff(v)`                       -- (1) leading `1/t` singular,
        `+ (1/t²)·G·[−¼∑ᵢⱼ(gⁱʲ−δ)vⁱvʲ]·w₀(v)`                    -- (2) the `1/t²` residue,
        `− G·Δ_g w₀(v)` ,                                        -- (3) the `Δ_g w₀` regular driver,
  where `G = gaussDdim t v` is the flat `d`-dim Gaussian and `w₀ = foldedCoeff Θ u 0`.  This file
  ASSEMBLES all three into one clean Gaussian bound with a FIXED constant.

    • `residualQuadratic_gaussian_bound` — term (2) alone:  near the RNC centre, with the genuine
      `O(r²)` metric-deviation decay `|gⁱʲ−δ| ≤ M·r²` and coefficient boundedness `|w₀| ≤ W`,
          `|(1/t²)·G·[−¼∑(gⁱʲ−δ)vⁱvʲ]·w₀| ≤ 32·n²·M·W · gaussDdimWide t v` .
      Mechanism: `|∑ᵢⱼ(gⁱʲ−δ)vⁱvʲ| ≤ n²·M·r⁴` (deviation `O(r²)` × `|vⁱvʲ| ≤ r²`, `n²` terms), then
      the C4a `m=2` absorption `r⁴·G ≤ 128 t²·G_wide` (`rncRadialSq_pow_mul_gaussDdim_le 2`) cancels
      the `1/t²`.

    • `gaussDdim_le_gaussDdimWide` — the pointwise comparison `G ≤ G_wide` (`e^{−r²/4t} ≤ e^{−r²/8t}`),
      used to fold the (bounded) regular driver term (3) into the widened Gaussian.

    • `residualN0_gaussian_bound` — ★ THE FULL `N=0` BOUND.  Near the RNC centre,
          `|(∂_t − Δ_g)H_0(t,v)| ≤ (1 + 32·n²·M·W + L) · gaussDdimWide t v` ,
      assembling term (1) via `residualLeading_gaussian_bound` (M6-1, at `ε = 1`), term (2) via
      `residualQuadratic_gaussian_bound`, and term (3) via `|Δ_g w₀| ≤ L` + `G ≤ G_wide`, by the
      triangle inequality.  This is the one-step `|E| ≤ C·G_wide` residual bound feeding the
      Levi/Duhamel convergence toward the true heat kernel and `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  FLOOR LANDED = **F1** — the FULL `N=0` residual Gaussian bound
  `|E| ≤ C·G_wide` (all three terms), `∀ᶠ v in 𝓝 0` near the RNC centre.

  The three carried decay/boundedness hypotheses are GENUINE, load-bearing analytic facts, NOT
  vacuous:
    • `hdev : ∀ᶠ v, ∀ i j, |gⁱʲ(v) − δⁱʲ| ≤ M·r²`  — the `O(r²)` RNC metric-deviation decay (the same
      shape as `ResidueBound.residue_metricdev_bound`'s `hddecay`; true because RNC 2-jets vanish at 0).
    • `hw0bd : ∀ᶠ v, |w₀(v)| ≤ W`  — local boundedness of the leading coefficient (`w₀` continuous).
    • `hlap : ∀ᶠ v, |Δ_g w₀(v)| ≤ L`  — local boundedness of `Δ_g w₀` (`w₀` is `C²`, `Δ_g w₀`
      continuous ⟹ locally bounded).
  The M6-1 leading-term hypotheses (van-Vleck 2-jet + RNC gauge + smoothness) are inherited verbatim
  through `residualLeading_gaussian_bound`.

  What this is NOT:
    • NOT the general-`N` residual bound `|E| ≤ C·t^{N−d/2}·G_κ` — that lifts this `N=0` bound over `N`
      (the `Σ_{k}` transport/`Δ_g` polynomials), a further brick.
    • NOT yet WIRED into `iterConv_bound`/`leviSeries_summable`: those consume `|E τ p q| ≤ C·baseKernel`
      in the TWO-POINT `(p,q)` representation, whereas this bound is in the single RNC coordinate `v`
      with the widened Gaussian `gaussDdimWide`.  The `gaussDdimWide → baseKernel` identification and
      the `v → (p,q)` difference representation are the remaining convergence-wiring step.
    • NOT `a₁ = R/6` (M6 parametrix convergence C5/C6 remains; `a₁ = R/6` stays the carried G3 input).

  No `sorry`, no new axioms, no vacuous hypotheses.  Grounded in Rosenberg, *The Laplacian on a
  Riemannian Manifold*, §3.2.1, and the Grigor'yan-style Gaussian iterated-convolution program.
-/
import Mathlib
import QIQTH.ParametrixResidualGaussianBound
import QIQTH.ParametrixResidualO1Total
import QIQTH.GaussianPolyBound
import QIQTH.ResidueBound

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.HeatResidualBound

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### The pointwise Gaussian comparison `G ≤ G_wide`. -/

/-- **The narrow-to-wide Gaussian comparison** `gaussDdim t v ≤ gaussDdimWide t v`.  Both share the
    prefactor `(√(4πt))⁻ⁿ ≥ 0`; the widened exponent `−r²/(8t)` dominates the narrow `−r²/(4t)`
    (since `r² ≥ 0`, `t > 0`).  Used to fold the bounded regular driver `−G·Δ_g w₀` into `G_wide`. -/
theorem gaussDdim_le_gaussDdimWide {t : ℝ} (ht : 0 < t) (v : Point n) :
    gaussDdim t v ≤ gaussDdimWide t v := by
  rw [gaussDdim_eq_exp, gaussDdimWide]
  have hrr : 0 ≤ rncRadialSq v := rncRadialSq_nonneg v
  have hexp : -(rncRadialSq v) / (4 * t) ≤ -(rncRadialSq v) / (8 * t) := by
    have h1 : rncRadialSq v / (8 * t) ≤ rncRadialSq v / (4 * t) := by
      gcongr; linarith [ht.le, hrr]
    rw [neg_div, neg_div]
    linarith [h1]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)

/-! ### Term (2): the `1/t²` residue Gaussian bound. -/

/-- **THE `1/t²` RESIDUE GAUSSIAN BOUND (term (2), companion to M6-1).**  Near the RNC centre, with
    the genuine `O(r²)` metric-deviation decay `hdev : |gⁱʲ − δⁱʲ| ≤ M·r²` and coefficient
    boundedness `hw0bd : |w₀| ≤ W`, the `1/t²` residue of the `N=0` parametrix residual satisfies
        `|(1/t²)·G·[−¼∑ᵢⱼ(gⁱʲ−δ)vⁱvʲ]·w₀| ≤ 32·n²·M·W · gaussDdimWide t v`   (eventually in `v`).
    PROOF.  `|∑ᵢⱼ(gⁱʲ−δ)vⁱvʲ| ≤ n²·M·r⁴` (each of the `n²` summands is `≤ (M·r²)·r²`, using
    `|vⁱvʲ| ≤ r²` and the deviation decay), times `|w₀| ≤ W`; then the C4a `m=2` absorption
    `r⁴·G = (r²)²·G ≤ 128·t²·G_wide` (`rncRadialSq_pow_mul_gaussDdim_le 2`, `8²·2! = 128`) cancels the
    `1/t²`, leaving the `t`-free constant `128/4 · n²·M·W = 32·n²·M·W`.  NOT the full residual bound. -/
theorem residualQuadratic_gaussian_bound
    (_g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {t : ℝ} (ht : 0 < t) (M W : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W) :
    ∀ᶠ v in nhds (0 : Point n),
      |(1 / t ^ 2) * gaussDdim t v
          * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
          * foldedCoeff Θ u 0 v|
        ≤ 32 * (n : ℝ) ^ 2 * M * W * gaussDdimWide t v := by
  have htne : t ≠ 0 := ht.ne'
  filter_upwards [hdev, hw0bd] with v hdev_v hw_v
  -- Abbreviations.
  set S : ℝ := ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j) with hSdef
  set w : ℝ := foldedCoeff Θ u 0 v with hwdef
  -- `|S| ≤ n²·M·r⁴`.
  have hSabs : |S| ≤ (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 := by
    calc |S| ≤ ∑ i, ∑ j, |(gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, M * rncRadialSq v ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            have h1 : |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v := hdev_v i j
            have h2 : |v i * v j| ≤ rncRadialSq v := by
              rw [abs_mul]
              calc |v i| * |v j|
                  ≤ rncRadial v * rncRadial v :=
                    mul_le_mul (abs_coord_le_rncRadial v i) (abs_coord_le_rncRadial v j)
                      (abs_nonneg _) (rncRadial_nonneg v)
                _ = rncRadialSq v := by rw [← rncRadial_sq]; ring
            calc |gi v i j - (if i = j then (1 : ℝ) else 0)| * |v i * v j|
                ≤ (M * rncRadialSq v) * rncRadialSq v :=
                  mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hM (rncRadialSq_nonneg v))
              _ = M * rncRadialSq v ^ 2 := by ring
      _ = (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
  -- The `m = 2` polynomial-absorption bound `r⁴·G ≤ 128 t²·G_wide`.
  have hrr2G : rncRadialSq v ^ 2 * gaussDdim t v ≤ 128 * t ^ 2 * gaussDdimWide t v := by
    have h := rncRadialSq_pow_mul_gaussDdim_le 2 ht v
    have hc : (8 : ℝ) ^ 2 * ((2 : ℕ).factorial : ℝ) = 128 := by norm_num [Nat.factorial]
    rwa [hc] at h
  -- Nonnegativities.
  have hG : 0 ≤ gaussDdim t v := gaussDdim_nonneg t v
  have hn2Mrr : 0 ≤ (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hM) (sq_nonneg _)
  have hC0 : 0 ≤ (1 / t ^ 2) * (1 / 4) := by positivity
  have hK2 : 0 ≤ (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2) := by
    apply mul_nonneg
    · apply div_nonneg _ (by norm_num)
      exact mul_nonneg (mul_nonneg (sq_nonneg _) hM) hW
    · positivity
  -- The abs of term (2) in clean product form.
  have habs2 : |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * gaussDdim t v * (1 / 4) * |S| * |w| := by
    simp only [abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / t ^ 2 by positivity),
        abs_of_nonneg hG, show |(-1 / 4 : ℝ)| = 1 / 4 by norm_num]
    ring
  calc |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * (1 / 4) * gaussDdim t v * (|S| * |w|) := by rw [habs2]; ring
    _ ≤ (1 / t ^ 2) * (1 / 4) * gaussDdim t v
          * (((n : ℝ) ^ 2 * M * rncRadialSq v ^ 2) * W) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hSabs hw_v (abs_nonneg _) hn2Mrr)
            (mul_nonneg hC0 hG)
    _ = (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2) * (rncRadialSq v ^ 2 * gaussDdim t v) := by ring
    _ ≤ (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2) * (128 * t ^ 2 * gaussDdimWide t v) :=
          mul_le_mul_of_nonneg_left hrr2G hK2
    _ = 32 * (n : ℝ) ^ 2 * M * W * gaussDdimWide t v := by field_simp; ring

/-! ### The full `N=0` parametrix-residual Gaussian bound. -/

/-- **★ THE FULL `N=0` PARAMETRIX-RESIDUAL GAUSSIAN BOUND (F1).**  Near the RNC centre, the complete
    leading-order heat-operator residual is bounded by a fixed multiple of the widened Gaussian:
        `|(∂_t − Δ_g)H_0(t,v)| ≤ (1 + 32·n²·M·W + L) · gaussDdimWide t v`   (eventually in `v`).
    The three residual terms are absorbed separately and summed by the triangle inequality:
      • (1) `(1/t)·G·totalRadialO1_coeff` ≤ `1·G_wide`  via `residualLeading_gaussian_bound` at `ε = 1`
            (off-diagonal cancellation `coeff = o(r²)` absorbing the `1/t`),
      • (2) `(1/t²)·G·[−¼∑(gⁱʲ−δ)vⁱvʲ]·w₀` ≤ `32·n²·M·W·G_wide`  via `residualQuadratic_gaussian_bound`
            (deviation `O(r²)`, `m=2` absorption),
      • (3) `G·Δ_g w₀` ≤ `L·G_wide`  via `|Δ_g w₀| ≤ L` and `G ≤ G_wide` (`gaussDdim_le_gaussDdimWide`).
    The carried `hdev`/`hw0bd`/`hlap` are genuine `O(r²)`/boundedness facts (see header); the M6-1
    van-Vleck 2-jet + RNC gauge hypotheses are inherited.  This is the one-step `|E| ≤ C·G_wide`
    residual bound the Levi/Duhamel convergence consumes.  NOT the general-`N` bound, NOT yet wired
    into `iterConv_bound`, NOT `a₁ = R/6`. -/
theorem residualN0_gaussian_bound
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
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L) :
    ∀ᶠ v in nhds (0 : Point n),
      |parametrixResidualN 0 g gi Θ u t v|
        ≤ (1 + 32 * (n : ℝ) ^ 2 * M * W + L) * gaussDdimWide t v := by
  -- term (1): the leading `1/t` bound at `ε = 1`.
  have hlead := residualLeading_gaussian_bound g gi Θ u hg hgiC hCd (hw 0) hg0 hgi0 hdg0 hdgi0 hΓ0
    hsymm hinv hgauge hw0flat hw0hessRicci ht 1 (by norm_num)
  -- term (2): the `1/t²` residue bound.
  have hquad := residualQuadratic_gaussian_bound g gi Θ u ht M W hM hW hdev hw0bd
  filter_upwards [hlead, hquad, hlap] with v hA hB hlap_v
  -- rewrite the `N=0` residual into its three isolated terms.
  rw [parametrixResidual_N0_O1_isolated g gi Θ u t ht v hw]
  set Gw : ℝ := gaussDdimWide t v with hGw
  -- term (3): `|G·Δ_g w₀| ≤ L·G_wide`.
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) hlap_v
  have hD : |gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L * Gw := by
    rw [abs_mul, abs_of_nonneg (gaussDdim_nonneg t v)]
    calc gaussDdim t v * |laplaceBeltrami g gi (foldedCoeff Θ u 0) v|
        ≤ gaussDdim t v * L :=
          mul_le_mul_of_nonneg_left hlap_v (gaussDdim_nonneg t v)
      _ ≤ Gw * L := by
          rw [hGw]; exact mul_le_mul_of_nonneg_right (gaussDdim_le_gaussDdimWide ht v) hL0
      _ = L * Gw := by rw [hGw]; ring
  -- assemble by the triangle inequality.
  calc |(1 / t) * gaussDdim t v * totalRadialO1_coeff g gi Θ u v
          + (1 / t ^ 2) * gaussDdim t v
              * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
              * foldedCoeff Θ u 0 v
          - gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 0) v|
      = |((1 / t) * gaussDdim t v * totalRadialO1_coeff g gi Θ u v
          + (1 / t ^ 2) * gaussDdim t v
              * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
              * foldedCoeff Θ u 0 v)
          + (-(gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 0) v))| := by
        rw [sub_eq_add_neg]
    _ ≤ |(1 / t) * gaussDdim t v * totalRadialO1_coeff g gi Θ u v
          + (1 / t ^ 2) * gaussDdim t v
              * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
              * foldedCoeff Θ u 0 v|
          + |(-(gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 0) v))| := abs_add_le _ _
    _ = |(1 / t) * gaussDdim t v * totalRadialO1_coeff g gi Θ u v
          + (1 / t ^ 2) * gaussDdim t v
              * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
              * foldedCoeff Θ u 0 v|
          + |gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 0) v| := by rw [abs_neg]
    _ ≤ (|(1 / t) * gaussDdim t v * totalRadialO1_coeff g gi Θ u v|
          + |(1 / t ^ 2) * gaussDdim t v
              * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
              * foldedCoeff Θ u 0 v|)
          + |gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 0) v| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (1 * Gw + 32 * (n : ℝ) ^ 2 * M * W * Gw) + L * Gw :=
        add_le_add (add_le_add hA hB) hD
    _ = (1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Gw := by ring

end QIQTH.HeatResidualBound
