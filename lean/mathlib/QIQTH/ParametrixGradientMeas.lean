/-
  ParametrixGradientMeas — J4-189 (Sol endgame, toward F1): the GEOMETRY DISCHARGE of the last
  J4-188 factor carry `hDH`.  ErrorKernelJointMeas (J4-188) reduced the joint `(τ,v)`-measurability of
  the diagonal cutoff-error normal form `E = χ·(G_τ·A) − annulusTerms` to `{hg, hgi, hgpos}` PLUS the
  single genuine derivative-field carry `hDH` — the joint `(τ,v)`-measurability of the parametrix's own
  spatial gradient field `(τ,v) ↦ ∂ⱼ(heatParametrix N Θ u τ ·)(v)`.  THIS FILE DISCHARGES `hDH` from
  geometry, so that `E`'s normal form is jointly `(τ,v)`-measurable from `{hg, hgi, hgpos}` ALONE.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a
  measurable-algebra / product-rule reduction: it turns "the parametrix spatial-gradient field is
  jointly measurable" into "the metric is `C^∞` with `det g > 0`", by feeding the BANKED flat-Gaussian
  spatial-derivative identity (`HeatResidualBound.gaussDdim_pd_eq`, `∂ⱼG_τ(v) = (−vⱼ/2τ)·G_τ(v)`),
  the folded-coefficient smoothness (`hw_discharged_infty ∘ hu_infty_closed`), and the polynomial-gradient
  commutation (`ErrorKernelJointMeas.pd_polySum_eq`) through the τ>0 product rule, with the τ≤0 branch
  handled by the parametrix's identical vanishing (`heatParametrix_eq_zero_of_nonpos`, needs `0<n`).
  No new heat-kernel content, no `sorry`, no new axioms, no vacuous/unsatisfiable hypotheses, no
  conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file delivers (ns `QIQTH.ParametrixGradientMeas`).

    * `heatParametrix_pd_eq` — THE GRADIENT IDENTITY (for `τ>0`).  Via the folded form
      `H = G_τ·Σ_k w_k·τᵏ` and the Leibniz rule (`pd_mul`), the parametrix spatial partial is the
      explicit two-term product-rule expansion
        `∂ⱼH(τ,v) = (−vⱼ/(2τ)·G_τ(v))·(Σ_k w_k(v)·τᵏ) + G_τ(v)·(Σ_k (∂ⱼw_k)(v)·τᵏ)` ,
      using the banked Gaussian gradient `gaussDdim_pd_eq` and the polynomial-gradient commutation
      `pd_polySum_eq`.  (For `τ≤0` the parametrix is identically `0` in `v`, so `∂ⱼH = 0` — folded
      into the measurability discharge below via the `gaussDdim = 0` collapse of the same formula.)

    * ★ `heatParametrix_pd_measurable_of_folded` — THE `hDH` DISCHARGE (abstract).  For smooth folded
      coefficients (`hw`) and `0<n`, the parametrix spatial-gradient field
      `(τ,v) ↦ ∂ⱼ(heatParametrix N Θ u τ ·)(v)` is jointly `(τ,v)`-measurable.  The gradient EQUALS the
      explicit product-rule formula EVERYWHERE (τ>0 by `heatParametrix_pd_eq`; τ≤0 both sides `0`), and
      the formula is measurable factor-by-factor: `−vⱼ/(2τ)` (measurable division, `τ=0` junk), `G_τ(v)`
      globally Borel (`gaussDdim_uncurry_measurable`), the folded-coefficient sums and their partials
      continuous (`hw`, `contDiff_pd_inf`) × the measurable `τ`-powers.

    * `heatParametrix_pd_measurable_from_geometry` — THE `hDH` DISCHARGE (geometry).  Specializes the
      above to `Θ = vanVleck g`, `u = transportCoeff …`, with `hw` supplied by
      `hw_discharged_infty ∘ hu_infty_closed` — from `{hg, hgi, hgpos}` ALONE.  This is EXACTLY the
      `hDH` hypothesis of `ErrorKernelJointMeas.annulusTerms_measurable_from_geometry` /
      `…cutoffError_normalForm_measurable_from_geometry`.

    * ★ `cutoffError_normalForm_measurable_final` — THE F1 FEED (fully from geometry).  J4-188's
      `cutoffError_normalForm_measurable_from_geometry` with the `hDH` carry ELIMINATED (discharged by
      the theorem above): the diagonal cutoff-error normal form `χ·(G_τ·A) − annulusTerms` is jointly
      `(τ,v)`-measurable from `{hn, hg, hgi, hgpos}` — NO derivative-field carry remains.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE F1 ASSEMBLY VERDICT (honest, read it — this file closes ONE of the two orthogonal axes).

  The residue chain carries F1 as `hEmeas` (`ResidueThreading`), the TRIPLE `(τ,p,q)` strong
  measurability of the gated van-Vleck witness `E = heatOp g gi H_G`.  There are TWO ORTHOGONAL axes:

    (FACTOR / diagonal axis) — On the gate the triple collapses to the DIAGONAL single-base-point
      residual (J4-187 `cutoffErrorKernel`), whose joint `(τ,v)`-measurability is the FACTOR side.
      ★ WITH THIS FILE this axis is now FULLY DISCHARGED FROM GEOMETRY: every factor carry of J4-187,
      INCLUDING the last derivative-field `hDH`, reduces to `{hn, hg, hgi, hgpos}`
      (`cutoffError_normalForm_measurable_final`).  Nothing remains on the factor side.

    (FLOW / q-regularity axis) — `GatedWitnessEmeas` (J4-110) reduces the FULL triple `hEmeas` to
      `heatOp_stronglyMeasurable_of_jointContinuous`, whose irreducible inputs are:
        • (W1)  JOINT CONTINUITY of the gated kernel `H_G` in `(τ,p,q)` — the base-point `q` running
          through the `Classical.choose` geodesic flow `uniformFlowExp`, whose joint `(q,w)` structure
          is NOT exposed (per `BasepointSmoothDep`: "runs through opaque `Classical.choose` witnesses");
        • (W2)  JOINT CONTINUITY (indeed joint `C¹`) of each FIRST-order `pd` field of `H_G` — because
          `laplaceBeltrami` nests a second `pd`, and `measurable_deriv_with_param` upgrades to a
          measurable parameterized derivative ONLY from JOINT CONTINUITY of the family; measurability of
          the flow alone does not propagate through the two nested parameterized derivatives.

  These two axes are ORTHOGONAL: this file supplies the joint `(τ,v)`-measurability of the DIAGONAL
  (single-base-point) gradient field — it does NOT, and cannot, supply the `q`-CONTINUITY of the
  flow-dependent kernel `H_G(τ,p,q)` across the base point `q`.  The banked chart machinery (J4-168
  general-`p` Grönwall) gives chart CONTINUITY in the CHART variable `z`, not the `C¹` base-point (`q`)
  dependence of the opaque `Classical.choose` flow.  Hence:

    F1 (`hEmeas`) triple  ⟸  { `cutoffError_normalForm_measurable_final` [THIS FILE — factor axis, DONE]
                               , W1/W2 flow `q`-regularity of `uniformFlowExp` [HONEST WALL — the Sol
                                 route-(b) parameter-ODE joint measurability/`C¹`, a multi-week Lean
                                 ODE-smooth-dependence endeavour: closed integral-solution relation +
                                 Lusin–Souslin, or parameterized Picard + `ODE_solution_unique`] }.

  W1/W2 are NOT dischargeable with the banked diagonal/chart machinery — they are a genuinely distinct
  (ODE-smooth-dependence) wall, recorded here as the honest residue.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ErrorKernelJointMeas

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatResidualBound QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.HuInftyRebase
open QIQTH.InnerKernelJointMeas QIQTH.ErrorKernelFactorization QIQTH.ErrorKernelJointMeas
open QIQTH.HeatParametrixOrder
open scoped BigOperators ContDiff

namespace QIQTH.ParametrixGradientMeas

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ## 1.  The gradient identity (τ>0): the explicit product-rule expansion. -/

/-- **`heatParametrix_pd_eq` — the parametrix spatial gradient for `τ>0`.**  Via the folded form
    `H_N(τ,·) = G_τ·Σ_{k≤N} w_k·τᵏ` (`heatParametrix_folded`) and the Leibniz rule (`pd_mul`), the
    spatial partial factors into the two-term product-rule expansion
      `∂ⱼH_N(τ,v) = (−vⱼ/(2τ)·G_τ(v))·(Σ_{k≤N} w_k(v)·τᵏ) + G_τ(v)·(Σ_{k≤N} (∂ⱼw_k)(v)·τᵏ)`,
    using the BANKED Gaussian gradient `gaussDdim_pd_eq` (`∂ⱼG_τ(v) = (−vⱼ/2τ)·G_τ(v)`, `τ>0`) for the
    first factor and the polynomial-gradient commutation `pd_polySum_eq` for the second.  The folded
    coefficients `w_k = Θ^{−1/2}u_k` are carried `C^∞` (`hw`).  NOT `a₁ = R/6`. -/
theorem heatParametrix_pd_eq (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (j : Fin n) (v : Point n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    pd (heatParametrix N Θ u τ) j v
      = (-(v j) / (2 * τ) * gaussDdim τ v)
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * τ ^ k)
        + gaussDdim τ v
          * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j v * τ ^ k) := by
  have hfold : heatParametrix N Θ u τ
      = fun y => gaussDdim τ y * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * τ ^ k :=
    funext (fun y => heatParametrix_folded N Θ u τ y)
  rw [hfold]
  have hg_pd : PdiffAt (fun y => gaussDdim τ y) j v :=
    PdiffAt_of_contDiff _ (gaussDdim_contDiff τ) j v
  have hsum_pd : PdiffAt
      (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * τ ^ k) j v :=
    PdiffAt_sum (Finset.range (N + 1)) (fun k y => foldedCoeff Θ u k y * τ ^ k) j v
      (fun k _ => PdiffAt_of_contDiff_inf (fun y => foldedCoeff Θ u k y * τ ^ k)
        ((hw k).mul contDiff_const) j v)
  rw [pd_mul (fun y => gaussDdim τ y)
        (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * τ ^ k) j v hg_pd hsum_pd,
      gaussDdim_pd_eq τ hτ v j,
      pd_polySum_eq N Θ u τ j v hw]

/-! ## 2.  ★ The `hDH` discharge — joint `(τ,v)`-measurability of the gradient field. -/

/-- **★ `heatParametrix_pd_measurable_of_folded` — THE `hDH` DISCHARGE (abstract, J4-189).**  For
    smooth folded coefficients (`hw`) and `0 < n`, the parametrix spatial-gradient field
    `(τ,v) ↦ ∂ⱼ(heatParametrix N Θ u τ ·)(v)` is jointly `(τ,v)`-measurable.  MECHANISM: the gradient
    EQUALS the explicit product-rule formula EVERYWHERE — for `τ>0` by `heatParametrix_pd_eq`, and for
    `τ≤0` BOTH sides are `0` (the parametrix is identically `0` in `v`, `heatParametrix_eq_zero_of_nonpos`,
    so `∂ⱼ = pd_const 0`; the formula also collapses via `gaussDdim = 0`, `gaussDdim_eq_zero_of_nonpos` —
    both need `0<n`).  The formula is then measurable factor-by-factor: `−vⱼ/(2τ)` measurable (division,
    `τ=0` junk fine), `G_τ(v)` globally Borel (`gaussDdim_uncurry_measurable`), the folded-coefficient
    sums (`hw`.continuous) and their partials (`contDiff_pd_inf`.continuous) times the measurable
    `τ`-powers.  NOT `a₁ = R/6`. -/
theorem heatParametrix_pd_measurable_of_folded (N : ℕ) (hn : 0 < n) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) (j : Fin n) :
    Measurable (fun w : ℝ × Point n => pd (heatParametrix N Θ u w.1) j w.2) := by
  have hEq : (fun w : ℝ × Point n => pd (heatParametrix N Θ u w.1) j w.2)
      = (fun w : ℝ × Point n =>
          (-(w.2 j) / (2 * w.1) * gaussDdim w.1 w.2)
              * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k w.2 * w.1 ^ k)
            + gaussDdim w.1 w.2
              * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j w.2 * w.1 ^ k)) := by
    funext w
    rcases lt_or_ge 0 w.1 with hτ | hτ
    · -- τ > 0 : the explicit product-rule identity.
      exact heatParametrix_pd_eq N Θ u w.1 hτ j w.2 hw
    · -- τ ≤ 0 : the parametrix is identically 0 in `v`, so `∂ⱼ = 0`; the formula collapses via `G_τ = 0`.
      have hz : heatParametrix N Θ u w.1 = fun _ => (0 : ℝ) :=
        funext (fun x => heatParametrix_eq_zero_of_nonpos hn N Θ u w.1 x hτ)
      have hg0 : gaussDdim w.1 w.2 = 0 := gaussDdim_eq_zero_of_nonpos hn w.1 w.2 hτ
      rw [hz, pd_const, hg0]; ring
  rw [hEq]
  have hquot : Measurable (fun w : ℝ × Point n => -(w.2 j) / (2 * w.1)) :=
    (((measurable_pi_apply j).comp measurable_snd).neg).div (measurable_const.mul measurable_fst)
  have hgauss : Measurable (fun w : ℝ × Point n => gaussDdim w.1 w.2) :=
    gaussDdim_uncurry_measurable
  have hS1 : Measurable (fun w : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k w.2 * w.1 ^ k) :=
    Finset.measurable_sum _ (fun k _ =>
      (((hw k).continuous.comp continuous_snd).measurable).mul (measurable_fst.pow_const k))
  have hS2 : Measurable (fun w : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j w.2 * w.1 ^ k) :=
    Finset.measurable_sum _ (fun k _ =>
      (((contDiff_pd_inf (foldedCoeff Θ u k) (hw k) j).continuous.comp continuous_snd).measurable).mul
        (measurable_fst.pow_const k))
  exact ((hquot.mul hgauss).mul hS1).add (hgauss.mul hS2)

/-- **`heatParametrix_pd_measurable_from_geometry` — THE `hDH` DISCHARGE (geometry, J4-189).**  The
    concrete van-Vleck parametrix spatial-gradient field is jointly `(τ,v)`-measurable from
    `{hn, hg, hgi, hgpos}` ALONE: specialize `heatParametrix_pd_measurable_of_folded` to
    `Θ = vanVleck g`, `u = transportCoeff (transportOp (vanVleck g) g gi)`, with the folded-coefficient
    smoothness `hw` supplied by the `∞`-chain closure `hw_discharged_infty ∘ hu_infty_closed`.  This is
    EXACTLY the `hDH` hypothesis of `ErrorKernelJointMeas.annulusTerms_measurable_from_geometry` /
    `…cutoffError_normalForm_measurable_from_geometry`.  NOT `a₁ = R/6`. -/
theorem heatParametrix_pd_measurable_from_geometry (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (hn : 0 < n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ∀ j, Measurable (fun w : ℝ × Point n =>
      pd (heatParametrix N (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) w.1) j w.2) :=
  fun j => heatParametrix_pd_measurable_of_folded N hn (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi))
    (hw_discharged_infty g gi hg hgpos (hu_infty_closed g gi hg hgi hgpos)) j

/-! ## 3.  ★ The F1 feed, fully from geometry — the `hDH` carry ELIMINATED. -/

/-- **★ `cutoffError_normalForm_measurable_final` — THE F1 FEED (fully from geometry, J4-189).**  The
    full residual normal form
      `χ·(G_τ·A) − annulusTerms`
    (which, by `ErrorKernelFactorization.cutoffError_eq_cutoff_gauss_A_sub_annulus`, EQUALS the
    diagonal cutoff error kernel `E` on `{τ>0}`) is jointly `(τ,v)`-measurable from
    `{hn, hg, hgi, hgpos}` ALONE — NO derivative-field carry remains.  This is J4-188's
    `cutoffError_normalForm_measurable_from_geometry` with its single `hDH` hypothesis DISCHARGED by
    `heatParametrix_pd_measurable_from_geometry`.  The factor / diagonal axis of F1 is now fully
    reduced to geometry; the orthogonal flow `q`-regularity axis (W1/W2) is the honest residue (see the
    module-header verdict).  NOT `a₁ = R/6`. -/
theorem cutoffError_normalForm_measurable_final (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (a b : ℝ) (hn : 0 < n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    Measurable (fun w : ℝ × Point n =>
      radialCutoff a b w.2
          * (gaussDdim w.1 w.2 * residualCoeffA N g gi (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) w.1 w.2)
        - annulusTerms g gi a b
            (heatParametrix N (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) w.1) w.2) :=
  cutoffError_normalForm_measurable_from_geometry N g gi a b hg hgi hgpos
    (heatParametrix_pd_measurable_from_geometry N g gi hn hg hgi hgpos)

/-! ## Axiom checks — every main result is `std-3` (propext, Classical.choice, Quot.sound). -/

section AxiomChecks

#print axioms heatParametrix_pd_eq
#print axioms heatParametrix_pd_measurable_of_folded
#print axioms heatParametrix_pd_measurable_from_geometry
#print axioms cutoffError_normalForm_measurable_final

end AxiomChecks

end QIQTH.ParametrixGradientMeas
