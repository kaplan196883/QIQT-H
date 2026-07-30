/-
  ResidualN0GaussianC3 — brick R3c-3 of the RECENTER campaign: the FINITE-REGULARITY
  (`ContDiffAt`) version of the FULL `N=0` parametrix-residual Gaussian bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS BUILT HERE (the honest boundary — read it).

  The `⊤`-versions live in `ParametrixResidualGaussianBound` (`residualLeading_gaussian_bound`, the
  leading `1/t` term) and `ParametrixResidualN0Bound` (`residualN0_gaussian_bound`, the full
  three-term assembly).  Both carry `ContDiff ℝ ⊤` on the metric `g`, inverse metric `gi`,
  Christoffel `Γ`, and the folded coefficients `w_k`.

  This file re-derives the SAME two conclusions with those smoothness hypotheses weakened to their
  TRUE MINIMAL finite order at the single base point `0` — exactly what R3c-2
  (`totalRadialO1_coeff_isLittleO_C3`, `OffDiagLittleOFiniteReg`) supplies:
    • `g`  : `ContDiffAt ℝ 2` at `0`,
    • `gi` : `ContDiffAt ℝ 2` at `0`,
    • `Γ`  : `ContDiffAt ℝ 2` at `0`,
    • `w₀` : `ContDiffAt ℝ 3` at `0`  (only the `k = 0` folded coefficient is used at `N = 0`).

    • `residualLeading_gaussian_bound_C3` — the leading `(1/t)·G·totalRadialO1_coeff` term's
      `ε`-Gaussian bound, obtained by swapping the internal `totalRadialO1_coeff_isLittleO` call for
      R3c-2's finite-regularity `totalRadialO1_coeff_isLittleO_C3`.  The Gaussian polynomial-absorption
      machinery (`rncRadialSq_mul_gaussDdim_le`, `filter_upwards`) is regularity-free — ported verbatim.

    • `residualN0_gaussian_bound_C3` — ★ THE FULL `N=0` BOUND at finite regularity.  Assembled exactly
      like `residualN0_gaussian_bound`: term (1) via `residualLeading_gaussian_bound_C3` at `ε = 1`,
      term (2) via `residualQuadratic_gaussian_bound` (already smoothness-free — reused verbatim),
      term (3) via `|Δ_g w₀| ≤ L` + `gaussDdim_le_gaussDdimWide`.  The residual is split into its three
      isolated terms by the finite-regularity `parametrixResidual_N0_O1_isolated_C2` (fed `w₀ ∈ C²`
      eventually near `0`, from `w₀ ∈ C³` at `0` via `ContDiffAt.eventually`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  FLOOR LANDED = the FULL `N=0` residual Gaussian bound
  `|E| ≤ C·G_wide` (all three terms), `∀ᶠ v in 𝓝 0` near the RNC centre, at FINITE regularity.

  All regularity hypotheses are genuinely used (each smoothness order is load-bearing in the R3c-2
  little-`o` chain / the `C²` residual isolation).  The carried `hdev`/`hw0bd`/`hlap` are the same
  genuine `O(r²)`/boundedness facts as the ⊤ version; the point-`0` van-Vleck 2-jet + RNC gauge
  hypotheses are inherited verbatim.  NOT the general-`N` bound, NOT yet wired into
  `iterConv_bound`/`leviSeries_summable`, NOT `a₁ = R/6`.

  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.ParametrixResidualN0Bound
import QIQTH.ParametrixResidualGaussianBound
import QIQTH.OffDiagLittleOFiniteReg
import QIQTH.ResidualN0FiniteReg

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.HeatResidualBound

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **THE M6 / C4d LEADING-RESIDUAL GAUSSIAN BOUND, FINITE REGULARITY (R3c-3).**  The finite-regularity
    twin of `residualLeading_gaussian_bound`: near the RNC centre, the most-singular piece of the `N=0`
    parametrix residual — `(1/t)·G·totalRadialO1_coeff` — is bounded by an arbitrarily small multiple
    of the widened Gaussian, for every `ε > 0`, eventually in `v`.
        `|(1/t)·gaussDdim t v · totalRadialO1_coeff g gi Θ u v| ≤ ε · gaussDdimWide t v` .
    The `ContDiff ⊤` metric/coefficient hypotheses of the ⊤ version are weakened to their true minimal
    finite order at `0` (`g, gi, Γ ∈ ContDiffAt ℝ 2`, `w₀ ∈ ContDiffAt ℝ 3`), swapping the internal
    off-diagonal cancellation `totalRadialO1_coeff_isLittleO` for R3c-2's finite-regularity
    `totalRadialO1_coeff_isLittleO_C3`.  Every remaining step (Gaussian polynomial absorption,
    sup-norm ≤ radial, `filter_upwards`) is regularity-free.  NOT `a₁ = R/6`. -/
theorem residualLeading_gaussian_bound_C3
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgiC : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hC : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
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
    {t : ℝ} (ht : 0 < t) :
    ∀ ε > 0, ∀ᶠ v in nhds (0 : Point n),
      |(1 / t) * gaussDdim t v * totalRadialO1_coeff g gi Θ u v| ≤ ε * gaussDdimWide t v := by
  -- The off-diagonal cancellation `totalRadialO1_coeff = o(‖v‖²)`, at FINITE regularity (R3c-2).
  have hlo := totalRadialO1_coeff_isLittleO_C3 g gi Θ u hg hgiC hC hw0 hg0 hgi0 hdg0 hdgi0 hΓ0
    hsymm hinv hgauge hw0flat hw0hessRicci
  intro ε hε
  have htne : t ≠ 0 := ht.ne'
  have hε8 : (0 : ℝ) < ε / 8 := by positivity
  filter_upwards [hlo.bound hε8] with v hbnd
  have hcb : |totalRadialO1_coeff g gi Θ u v| ≤ (ε / 8) * ‖v‖ ^ 2 := by
    rwa [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖v‖ ^ 2)] at hbnd
  have hnorm_le : ‖v‖ ≤ rncRadial v := by
    rw [pi_norm_le_iff_of_nonneg (rncRadial_nonneg v)]
    intro i
    rw [Real.norm_eq_abs]
    exact abs_coord_le_rncRadial v i
  have hsq : ‖v‖ ^ 2 ≤ (rncRadial v) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hnorm_le 2
  have hA0 : 0 ≤ (1 / t) * gaussDdim t v :=
    mul_nonneg (one_div_nonneg.mpr ht.le) (gaussDdim_nonneg t v)
  have hpre0 : 0 ≤ (ε / 8) * (1 / t) :=
    mul_nonneg hε8.le (one_div_nonneg.mpr ht.le)
  calc |(1 / t) * gaussDdim t v * totalRadialO1_coeff g gi Θ u v|
      = (1 / t) * gaussDdim t v * |totalRadialO1_coeff g gi Θ u v| := by
        rw [abs_mul, abs_of_nonneg hA0]
    _ ≤ (1 / t) * gaussDdim t v * ((ε / 8) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcb hA0
    _ = (ε / 8) * (1 / t) * (‖v‖ ^ 2 * gaussDdim t v) := by ring
    _ ≤ (ε / 8) * (1 / t) * ((rncRadial v) ^ 2 * gaussDdim t v) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsq (gaussDdim_nonneg t v)) hpre0
    _ ≤ (ε / 8) * (1 / t) * (8 * t * gaussDdimWide t v) :=
        mul_le_mul_of_nonneg_left (rncRadialSq_mul_gaussDdim_le ht v) hpre0
    _ = ε * gaussDdimWide t v := by field_simp

/-- **★ THE FULL `N=0` PARAMETRIX-RESIDUAL GAUSSIAN BOUND, FINITE REGULARITY (R3c-3).**  The
    finite-regularity twin of `residualN0_gaussian_bound`: near the RNC centre,
        `|(∂_t − Δ_g)H_0(t,v)| ≤ (1 + 32·n²·M·W + L) · gaussDdimWide t v`   (eventually in `v`).
    The `ContDiff ⊤` metric/coefficient hypotheses are weakened to their true minimal finite order at
    `0` (`g, gi, Γ ∈ ContDiffAt ℝ 2`, `w₀ ∈ ContDiffAt ℝ 3`); only the `k = 0` folded coefficient is
    used.  Assembled exactly as the ⊤ version: term (1) via `residualLeading_gaussian_bound_C3` at
    `ε = 1`, term (2) via `residualQuadratic_gaussian_bound` (smoothness-free — reused verbatim), term
    (3) via `|Δ_g w₀| ≤ L` and `gaussDdim_le_gaussDdimWide`, split by the finite-regularity
    `parametrixResidual_N0_O1_isolated_C2` (`w₀ ∈ C²` eventually near `0`, from `w₀ ∈ C³` at `0`).  The
    carried `hdev`/`hw0bd`/`hlap` are genuine `O(r²)`/boundedness facts; the van-Vleck 2-jet + RNC
    gauge hypotheses are inherited.  NOT the general-`N` bound, NOT yet wired into `iterConv_bound`,
    NOT `a₁ = R/6`. -/
theorem residualN0_gaussian_bound_C3
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgiC : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hCd : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
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
  -- term (1): the leading `1/t` bound at `ε = 1`, at finite regularity.
  have hlead := residualLeading_gaussian_bound_C3 g gi Θ u hg hgiC hCd hw0 hg0 hgi0 hdg0 hdgi0 hΓ0
    hsymm hinv hgauge hw0flat hw0hessRicci ht 1 (by norm_num)
  -- term (2): the `1/t²` residue bound (smoothness-free — reused verbatim).
  have hquad := residualQuadratic_gaussian_bound g gi Θ u ht M W hM hW hdev hw0bd
  -- `w₀ ∈ C²` eventually near `0`, from `w₀ ∈ C³` at `0` (for the `C²` residual isolation).
  have hw0ev : ∀ᶠ v in nhds (0 : Point n), ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v :=
    (hw0.of_le (by norm_num)).eventually (by norm_num)
  filter_upwards [hlead, hquad, hlap, hw0ev] with v hA hB hlap_v hw0_v
  -- rewrite the `N=0` residual into its three isolated terms (finite-regularity isolation).
  rw [parametrixResidual_N0_O1_isolated_C2 g gi Θ u t ht v hw0_v]
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
