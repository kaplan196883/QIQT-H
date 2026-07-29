/-
  ParametrixResidualGaussianBound — M6 / C4d: the LEADING-residual Gaussian bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS BUILT HERE (the honest boundary — read it).

  The C4d input to the Levi/Duhamel parametrix convergence (`CONVERGENCE_INFRASTRUCTURE_PLAN.md`)
  demands the parametrix residual `E = (∂_t − Δ_g)H_N` be cast into a clean Gaussian bound
      `|E(t,v)| ≤ C · t^{N−d/2} · G_κ(t,v)`
  so that the iterated-convolution Neumann series (`iterConv_bound`/`leviSeries_summable`, C5c) sums.
  At the leading van-Vleck order `N = 0` the residual (`parametrixResidual_N0_O1_isolated`) is
      `(∂_t − Δ_g)H_0(t,v) = (1/t)·G·totalRadialO1_coeff(v) + (1/t²)·G·[−¼∑(gⁱʲ−δ)vⁱvʲ]·w₀ − G·Δ_g w₀`,
  whose most-singular piece is the `(1/t)·G·coeff` term.  This file bounds EXACTLY that leading piece:

    • `residualLeading_gaussian_bound` — the FULL leading-term Gaussian bound.  Near the RNC centre,
      for every `ε > 0`, eventually in `v`,
          `|(1/t)·gaussDdim t v · totalRadialO1_coeff g gi Θ u v| ≤ ε · gaussDdimWide t v`,
      where `gaussDdimWide t v = (√(4πt))⁻ⁿ·exp(−r²/8t)` is the widened `d`-dim Gaussian.

  The mechanism is the OFF-DIAGONAL CANCELLATION `totalRadialO1_coeff = o(‖v‖²)`
  (`totalRadialO1_coeff_isLittleO`) fed into the Gaussian polynomial-absorption bound
  `rncRadialSq_mul_gaussDdim_le` (`r²·G ≤ 8t·G_wide`, itself C4a `gaussian_poly_absorb m=1`):
      `|coeff| ≤ (ε/8)·‖v‖²` eventually (`IsLittleO.bound`),  `‖v‖² ≤ (rncRadial v)²` (sup-norm ≤ radial),
      so `(1/t)·G·|coeff| ≤ (ε/8)·(1/t)·(r²·G) ≤ (ε/8)·(1/t)·8t·G_wide = ε·G_wide`.
  Because the cancellation makes the coefficient `o(r²)` (NOT merely `O(1)`), the `1/t` singularity is
  fully absorbed: the leading residual is `o(1)·Gaussian` — pointwise smaller than ANY fixed multiple
  of the Gaussian near the centre.  This is the C4d smallness the convergence machinery consumes.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  FLOOR LANDED = **F1** for the LEADING (`1/t`) term ONLY.

  What this IS:  the full `ε`-Gaussian bound on the `(1/t)·G·totalRadialO1_coeff` singular piece,
  uniform-eventually near the RNC centre, inheriting the van-Vleck 2-jet + RNC gauge through the
  little-`o` hypothesis chain.  All hypotheses are the genuine, load-bearing gauge/smoothness/van-Vleck
  data of `totalRadialO1_coeff_isLittleO` (none vacuous — the bound is FALSE without the cancellation).

  What this is NOT:
    • NOT the `(1/t²)·G·[−¼∑(gⁱʲ−δ)vⁱvʲ]·w₀` residue.  That is a SEPARATE next brick: `∑(gⁱʲ−δ)vⁱvʲ =
      O(r⁴)` (metric deviation `O(r²)` × `vⁱvʲ = O(r²)`), absorbed by `rncRadialSq_pow_mul_gaussDdim_le`
      with `m=2` (`r⁴·G ≤ 128 t²·G_wide`), leaving a `t⁰·G_wide` bound — reachable, but needs the
      concrete `O(r²)` metric-deviation decay hypothesis (residue-bound style), so it is its own lemma.
    • NOT the `−G·Δ_g w₀` regular driver (bounded, non-singular; a further brick).
    • NOT the FULL `E = (∂_t−Δ_g)H_N` bound `|E| ≤ C·t^{N−d/2}·G_κ` (C4d) — that assembles this leading
      bound + the `1/t²` residue + the regular driver over general `N`, then wires into `iterConv_bound`.
    • NOT `a₁ = R/6` (M6 parametrix convergence C4/C5/C6 remains; `a₁=R/6` stays the carried G3 input).

  No `sorry`, no new axioms, no vacuous hypotheses.  Grounded in Rosenberg, *The Laplacian on a
  Riemannian Manifold*, §3.2.1, and the Grigor'yan-style Gaussian iterated-convolution program.
-/
import Mathlib
import QIQTH.ParametrixOffDiagLittleO
import QIQTH.ParametrixResidualO1Total
import QIQTH.GaussianPolyBound
import QIQTH.ResidueBound

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.ResidueBound QIQTH.HeatResidualBound

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ THE M6 / C4d LEADING-RESIDUAL GAUSSIAN BOUND (F1 for the `1/t` term).**  Near the RNC centre,
    the most-singular piece of the `N=0` parametrix residual — `(1/t)·G·totalRadialO1_coeff` — is
    bounded by an arbitrarily small multiple of the widened Gaussian:  for every `ε > 0`, eventually
    in `v` (in `𝓝 0`),
        `|(1/t)·gaussDdim t v · totalRadialO1_coeff g gi Θ u v| ≤ ε · gaussDdimWide t v` .
    PROOF.  The off-diagonal cancellation `totalRadialO1_coeff = o(‖v‖²)` gives (via `IsLittleO.bound`
    at `c = ε/8`) `|coeff| ≤ (ε/8)·‖v‖²` eventually.  The sup-norm bound `‖v‖ ≤ rncRadial v`
    (`pi_norm_le_iff_of_nonneg` + `abs_coord_le_rncRadial`) upgrades this to `|coeff| ≤ (ε/8)·(rncRadial v)²`
    after multiplying by `G ≥ 0`, and the C4a polynomial-absorption bound `r²·G ≤ 8t·G_wide`
    (`rncRadialSq_mul_gaussDdim_le`) cancels the `1/t`:  `(ε/8)·(1/t)·8t·G_wide = ε·G_wide`.
    Inherits the van-Vleck 2-jet + RNC gauge through the little-`o` hypotheses.  NOT the `1/t²` residue,
    NOT the full `E`-bound, NOT `a₁ = R/6`. -/
theorem residualLeading_gaussian_bound
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw0 : ContDiff ℝ ⊤ (foldedCoeff Θ u 0))
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
  -- The off-diagonal cancellation: `totalRadialO1_coeff = o(‖v‖²)` near the RNC centre.
  have hlo := totalRadialO1_coeff_isLittleO g gi Θ u hg hgiC hC hw0 hg0 hgi0 hdg0 hdgi0 hΓ0
    hsymm hinv hgauge hw0flat hw0hessRicci
  intro ε hε
  have htne : t ≠ 0 := ht.ne'
  have hε8 : (0 : ℝ) < ε / 8 := by positivity
  -- eventual little-`o` bound at `c = ε/8`.
  filter_upwards [hlo.bound hε8] with v hbnd
  -- `|coeff v| ≤ (ε/8)·‖v‖²` (strip the real norms).
  have hcb : |totalRadialO1_coeff g gi Θ u v| ≤ (ε / 8) * ‖v‖ ^ 2 := by
    rwa [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖v‖ ^ 2)] at hbnd
  -- sup-norm ≤ radial: `‖v‖ ≤ rncRadial v`, hence `‖v‖² ≤ (rncRadial v)²`.
  have hnorm_le : ‖v‖ ≤ rncRadial v := by
    rw [pi_norm_le_iff_of_nonneg (rncRadial_nonneg v)]
    intro i
    rw [Real.norm_eq_abs]
    exact abs_coord_le_rncRadial v i
  have hsq : ‖v‖ ^ 2 ≤ (rncRadial v) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hnorm_le 2
  -- nonnegativity of the singular prefactor `(1/t)·G` and the coefficient `(ε/8)·(1/t)`.
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

end QIQTH.HeatResidualBound
