/-
  CutoffResidualGlobalBound — the GLOBAL cutoff-parametrix residual bound (C4c far-field, diagonal
  chart), the PAYOFF brick assembling the cutoff-parametrix far-field construction toward the
  unconditional `a₁ = R/6` heat-kernel coefficient.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE DELIVERS (honest FLOOR = F1, diagonal chart).

  For the cutoff-parametrix `χ · H` (χ = `radialCutoff a b`, a smooth radial cutoff `≡ 1` on the
  near ball `rncRadialSq < a²` and `≡ 0` off the far ball `rncRadialSq > b²`), the heat-operator
  residual `(∂_t − Δ_g)(χ·H)` is GLOBALLY dominated by a constant times the WIDTH-2 Gaussian:

      `∃ B ≥ 0, ∀ v, |(∂_t − Δ_g)(χ·H) v| ≤ B · gaussDdimWide t v` .

  This is EXACTLY the width-2 shape (`hEboundW` / `gaussDdimWide`) that the Levi/Neumann engine
  (`neumann_summable_alpha0_width2`) consumes.  A corollary converts it to the base-kernel form
  `|…| ≤ (B·√2ⁿ) · baseKernelW 2 0 t v 0` via `gaussDdimWide_eq_scaled_baseKernelW`.

  THE `(∂_t − Δ_g)(χ·H)` OBJECT.  Because `χ` is TIME-INDEPENDENT, `∂_t(χ·H)(t,v) = χ(v)·∂_tH(t,v)`.
  We abstract the time slice by carrying the spatial field `H : Point n → ℝ` and its time-derivative
  `dtH : Point n → ℝ` (`= ∂_t H(t,·)`), so the residual value is

      `Rcut v := radialCutoff a b v · dtH v  −  Δ_g(χ·H) v` ,

  and the UNCUT residual is `E v := dtH v − Δ_g H v`.  The Laplace–Beltrami Leibniz split
  (`laplaceBeltrami_mul_inf`, the `C∞` version — see below) gives the exact region identity

      `Rcut v = χ(v)·E v  −  H v·Δ_gχ v  −  2·∑ᵢⱼ gⁱʲ (∂ᵢχ)(∂ⱼH)` .

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE `C∞`-SMOOTHNESS FIX (load-bearing, honest).  The radial cutoff is `ContDiff ℝ ∞` (smooth) but
  NOT `ContDiff ℝ ⊤` (analytic — `smoothTransition` is not analytic).  The library Leibniz rule
  `LaplaceBeltrami.laplaceBeltrami_mul` demands the ANALYTIC hypothesis `ContDiff ℝ ⊤`, which the
  cutoff does not satisfy.  So this file re-proves the regularity/Leibniz chain at the correct
  `C∞` smoothness level (`PdiffAt_of_contDiff_inf`, `contDiff_pd_inf`, `PdiffAt_pd_inf`,
  `pd_pd_mul_inf`, `laplaceBeltrami_mul_inf`) — the SAME proofs with `⊤` weakened to `∞`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS CARRIED (all GENUINE, load-bearing, NONE vacuous).  These hold for the CONCRETE cutoff
  parametrix `H = gaussDdim·(bounded smooth cofactor)` on the compact annulus `a² ≤ rncRadialSq ≤ b²`
  (with `b` below the injectivity radius), and deriving them from the concrete `H` is the SEPARATE
  follow-on brick:
    • `hH  : ContDiff ℝ ∞ H`                      (parametrix profile is smooth);
    • `hEnear` : the near/interior uncut-residual bound `|E v| ≤ C·gaussDdimWide t v` on the whole
      ball `rncRadialSq v ≤ b²` (the near part is PROVED — `residualN0_local_baseKernelW_slice`);
    • `hHann`/`hDHann` : concrete-parametrix annulus derivative bounds
      `|H v| ≤ M·gaussDdim`, `|∂ⱼH v| ≤ M·(1/t)·gaussDdim` on the annulus;
    • `hgibd`/`hDchi`/`hLapChi` : inverse-metric, cutoff-gradient, `Δ_gχ` bounds on the annulus
      (from continuity on the COMPACT annulus);
    • `hgisymm` : symmetry of the inverse metric (used only to symmetrise the cross term).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  PROOF BY REGION (case split on `rncRadialSq v` vs `a²`, `b²`):
    (a) `rncRadialSq v < a²` (near): `χ ≡ 1`, `∂χ = 0`, `Δ_gχ = 0`, so `Rcut = E`, bounded by `hEnear`.
    (b) `a² ≤ rncRadialSq v ≤ b²` (annulus): triangle inequality; each of `|χ·E|`, `|H·Δ_gχ|`,
        `|2 gⁱʲ ∂ᵢχ ∂ⱼH|` is `(poly in 1/t)·gaussDdim·(bounded)`, absorbed into `gaussDdimWide` via
        `gaussDdim ≤ gaussDdimWide` and the annulus brick `invTpow_gaussDdim_le_gaussDdimWide`.
    (c) `rncRadialSq v > b²` (far): `χ = 0`, `∂χ = 0`, `Δ_gχ = 0`, so `Rcut = 0`.

  This CLOSES the C4c far-field on the DIAGONAL chart (base point `0`): it discharges the
  Gaussian-cofactor global-boundedness hypothesis of
  `residual_global_baseKernelW_of_gaussianCofactor` in its width-2 form.  The remaining C4c walls are
  the OFF-DIAGONAL / all-base-point recentering and the deep near residual derivation from concrete
  `H`.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.LaplaceBeltramiLeibniz
import QIQTH.CutoffAnnulusSupport
import QIQTH.AnnulusGaussianBound
import QIQTH.ParametrixHEboundWiring
import QIQTH.C4cDecomposition

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### `C∞`-smoothness regularity (the cutoff is only `C∞`, not analytic `⊤`).

The library `PdiffAt_of_contDiff`, `contDiff_pd`, `PdiffAt_pd`, `pd_pd_mul`, `laplaceBeltrami_mul`
require `ContDiff ℝ ⊤` (analytic).  The radial cutoff is only `ContDiff ℝ ∞` (smooth), so we re-prove
the exact same statements with `⊤` weakened to `∞` — the proofs are unchanged. -/

/-- `C∞` version of `PdiffAt_of_contDiff`: a smooth field is partially differentiable everywhere. -/
theorem PdiffAt_of_contDiff_inf (f : Point n → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin n) (x : Point n) :
    PdiffAt f i x := by
  have hg : DifferentiableAt ℝ f ((Function.update x i) (x i)) := by
    rw [Function.update_eq_self]; exact (hf.differentiable (by simp)).differentiableAt
  exact hg.comp (x i) (hasDerivAt_update x i (x i)).differentiableAt

/-- `C∞` version of `contDiff_pd`: the partial derivative of a smooth field is smooth. -/
theorem contDiff_pd_inf (f : Point n → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ContDiff ℝ ∞ (fun y => pd f i y) := by
  have heq : (fun y => pd f i y) = fun y => fderiv ℝ f y (Pi.single i (1 : ℝ)) := by
    funext y
    exact pd_eq_fderiv f i y (hf.differentiable (by simp)).differentiableAt
  rw [heq]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- `C∞` version of `PdiffAt_pd`: `∂_d f` of a smooth field is partially differentiable. -/
theorem PdiffAt_pd_inf (f : Point n → ℝ) (hf : ContDiff ℝ ∞ f) (d e : Fin n) (z : Point n) :
    PdiffAt (fun y => pd f d y) e z :=
  PdiffAt_of_contDiff_inf (fun y => pd f d y) (contDiff_pd_inf f hf d) e z

/-- `C∞` version of `pd_pd_mul`: the second-order coordinate Leibniz rule. -/
theorem pd_pd_mul_inf (f h : Point n → ℝ) (i j : Fin n) (x : Point n)
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    pd (fun y => pd (fun z => f z * h z) j y) i x
      = pd (fun y => pd f j y) i x * h x + pd f j x * pd h i x
        + pd f i x * pd h j x + f x * pd (fun y => pd h j y) i x := by
  have hstep : (fun y => pd (fun z => f z * h z) j y)
      = (fun y => pd f j y * h y + f y * pd h j y) := by
    funext y
    exact pd_mul f h j y (PdiffAt_of_contDiff_inf f hf j y) (PdiffAt_of_contDiff_inf h hh j y)
  rw [hstep,
      pd_add (fun y => pd f j y * h y) (fun y => f y * pd h j y) i x
        ((PdiffAt_pd_inf f hf j i x).mul (PdiffAt_of_contDiff_inf h hh i x))
        ((PdiffAt_of_contDiff_inf f hf i x).mul (PdiffAt_pd_inf h hh j i x)),
      pd_mul (fun y => pd f j y) h i x (PdiffAt_pd_inf f hf j i x) (PdiffAt_of_contDiff_inf h hh i x),
      pd_mul f (fun y => pd h j y) i x (PdiffAt_of_contDiff_inf f hf i x) (PdiffAt_pd_inf h hh j i x)]
  ring

/-- `C∞` version of `laplaceBeltrami_mul`: the Laplace–Beltrami Leibniz product rule
    `Δ_g(f·h) = f·Δ_g h + h·Δ_g f + 2·gⁱʲ(∂ᵢf)(∂ⱼh)`, valid for merely SMOOTH `f, h`. -/
theorem laplaceBeltrami_mul_inf (g gi : Point n → Fin n → Fin n → ℝ) (f h : Point n → ℝ)
    (x : Point n) (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hgisymm : ∀ i j, gi x i j = gi x j i) :
    laplaceBeltrami g gi (fun y => f y * h y) x
      = f x * laplaceBeltrami g gi h x + h x * laplaceBeltrami g gi f x
        + 2 * ∑ i, ∑ j, gi x i j * (pd f i x) * (pd h j x) := by
  classical
  have hksum : ∀ i j : Fin n,
      (∑ k, christoffel g gi k i j x * pd (fun z => f z * h z) k x)
        = h x * (∑ k, christoffel g gi k i j x * pd f k x)
          + f x * (∑ k, christoffel g gi k i j x * pd h k x) := by
    intro i j
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_mul f h k x (PdiffAt_of_contDiff_inf f hf k x) (PdiffAt_of_contDiff_inf h hh k x)]
    ring
  have hterm : ∀ i j : Fin n,
      gi x i j * (pd (fun y => pd (fun z => f z * h z) j y) i x
          - ∑ k, christoffel g gi k i j x * pd (fun z => f z * h z) k x)
        = h x * (gi x i j * (pd (fun y => pd f j y) i x
              - ∑ k, christoffel g gi k i j x * pd f k x))
          + f x * (gi x i j * (pd (fun y => pd h j y) i x
              - ∑ k, christoffel g gi k i j x * pd h k x))
          + gi x i j * (pd f j x * pd h i x + pd f i x * pd h j x) := by
    intro i j
    rw [pd_pd_mul_inf f h i j x hf hh, hksum i j]; ring
  have hcross : (∑ i, ∑ j, gi x i j * (pd f j x * pd h i x + pd f i x * pd h j x))
      = 2 * ∑ i, ∑ j, gi x i j * pd f i x * pd h j x := by
    have hsplit : (∑ i, ∑ j, gi x i j * (pd f j x * pd h i x + pd f i x * pd h j x))
        = (∑ i, ∑ j, gi x i j * (pd f j x * pd h i x))
          + (∑ i, ∑ j, gi x i j * (pd f i x * pd h j x)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hfirst : (∑ i, ∑ j, gi x i j * (pd f j x * pd h i x))
        = ∑ i, ∑ j, gi x i j * pd f i x * pd h j x := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hgisymm j i]; ring
    have hsecond : (∑ i, ∑ j, gi x i j * (pd f i x * pd h j x))
        = ∑ i, ∑ j, gi x i j * pd f i x * pd h j x :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, hfirst, hsecond]; ring
  have eP : (∑ i, ∑ j, h x * (gi x i j * (pd (fun y => pd f j y) i x
        - ∑ k, christoffel g gi k i j x * pd f k x)))
      = h x * ∑ i, ∑ j, gi x i j * (pd (fun y => pd f j y) i x
        - ∑ k, christoffel g gi k i j x * pd f k x) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
  have eQ : (∑ i, ∑ j, f x * (gi x i j * (pd (fun y => pd h j y) i x
        - ∑ k, christoffel g gi k i j x * pd h k x)))
      = f x * ∑ i, ∑ j, gi x i j * (pd (fun y => pd h j y) i x
        - ∑ k, christoffel g gi k i j x * pd h k x) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
  simp only [laplaceBeltrami]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm i j]
  simp only [Finset.sum_add_distrib]
  rw [eP, eQ, hcross]
  ring

/-! ### `Δ_g χ = 0` off the annulus (all cutoff derivatives vanish there). -/

/-- On the open near ball `rncRadialSq v < a²` the cutoff's Laplace–Beltrami vanishes: all first and
    second partials of `χ` are `0` there, so every summand of `Δ_gχ` is `0`. -/
theorem laplaceBeltrami_radialCutoff_zero_near (g gi : Point n → Fin n → Fin n → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n} (hv : rncRadialSq v < a ^ 2) :
    laplaceBeltrami g gi (radialCutoff a b) v = 0 := by
  have hz : ∀ k, pd (radialCutoff a b) k v = 0 :=
    fun k => pd_radialCutoff_eq_zero_of_near ha hab hv k
  simp only [laplaceBeltrami]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [pd_pd_radialCutoff_eq_zero_of_near ha hab hv j i]
  simp [hz]

/-- On the open far region `b² < rncRadialSq v` the cutoff's Laplace–Beltrami vanishes. -/
theorem laplaceBeltrami_radialCutoff_zero_far (g gi : Point n → Fin n → Fin n → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n} (hv : b ^ 2 < rncRadialSq v) :
    laplaceBeltrami g gi (radialCutoff a b) v = 0 := by
  have hz : ∀ k, pd (radialCutoff a b) k v = 0 :=
    fun k => pd_radialCutoff_eq_zero_of_far ha hab hv k
  simp only [laplaceBeltrami]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [pd_pd_radialCutoff_eq_zero_of_far ha hab hv j i]
  simp [hz]

/-! ### ★ The global cutoff-parametrix residual bound (F1, diagonal chart). -/

/-- **★ THE GLOBAL CUTOFF-PARAMETRIX RESIDUAL BOUND (F1, diagonal chart).**  The heat-operator
    residual of the cutoff parametrix `χ·H` (`χ = radialCutoff a b`, time-independent, so
    `∂_t(χH) = χ·∂_tH`; `dtH` abstracts `∂_tH(t,·)`) is GLOBALLY dominated by a constant times the
    width-2 Gaussian:

      `∃ B ≥ 0, ∀ v, |χ(v)·dtH v − Δ_g(χ·H) v| ≤ B · gaussDdimWide t v` .

    This is the width-2 `hEboundW` shape the Levi/Neumann engine consumes.  All carried hypotheses
    are genuine and load-bearing (satisfied by the concrete cutoff parametrix; see the file header):
    `hEnear` (near/interior uncut residual bound on `rncRadialSq ≤ b²`), `hHann`/`hDHann` (concrete-`H`
    annulus derivative bounds), `hgibd`/`hDchi`/`hLapChi` (inverse-metric / cutoff-gradient / `Δ_gχ`
    bounds on the compact annulus), `hgisymm` (inverse-metric symmetry), `hH` (`H` smooth). -/
theorem cutoffResidual_global_gaussianWide_bound
    (g gi : Point n → Fin n → Fin n → ℝ) (H dtH : Point n → ℝ)
    (a b t : ℝ) (ha : 0 < a) (hab : a < b) (ht : 0 < t)
    (hH : ContDiff ℝ ∞ H)
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (C : ℝ) (hCnn : 0 ≤ C)
    (hEnear : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |dtH w - laplaceBeltrami g gi H w| ≤ C * gaussDdimWide t w)
    (M : ℝ) (hM : 0 ≤ M)
    (hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |H w| ≤ M * gaussDdim t w)
    (hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd H j w| ≤ M * (1 / t) * gaussDdim t w)
    (Kg Kc1 Kc2 : ℝ) (hKg : 0 ≤ Kg) (hKc1 : 0 ≤ Kc1) (hKc2 : 0 ≤ Kc2)
    (hgibd : ∀ (w : Point n) (i j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |gi w i j| ≤ Kg)
    (hDchi : ∀ (w : Point n) (i : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd (radialCutoff a b) i w| ≤ Kc1)
    (hLapChi : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |laplaceBeltrami g gi (radialCutoff a b) w| ≤ Kc2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Point n,
      |radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v|
        ≤ B * gaussDdimWide t v := by
  -- the three pieces of the constant `B`
  have hb2 : 0 ≤ M * Kc2 := mul_nonneg hM hKc2
  have hcoef : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M := by positivity
  have hb3 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2) := by positivity
  refine ⟨C + M * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2), by linarith, ?_⟩
  intro v
  have hgd : gaussDdim t v ≤ gaussDdimWide t v := gaussDdim_le_gaussDdimWide ht v
  have hWnn : 0 ≤ gaussDdimWide t v := gaussDdimWide_nonneg t v
  have ha2b2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  rcases lt_or_ge (rncRadialSq v) (a ^ 2) with hnear | ha2
  · -- (a) NEAR: rncRadialSq v < a²
    have hb : rncRadialSq v ≤ b ^ 2 := le_trans (le_of_lt hnear) ha2b2
    have hχ1 : radialCutoff a b v = 1 := radialCutoff_eq_one ha hab (le_of_lt hnear)
    have hlbmul := laplaceBeltrami_mul_inf g gi (radialCutoff a b) H v
      (radialCutoff_contDiff a b) hH (hgisymm v)
    have hlapχ : laplaceBeltrami g gi (radialCutoff a b) v = 0 :=
      laplaceBeltrami_radialCutoff_zero_near g gi ha hab hnear
    have hpdχ : ∀ i, pd (radialCutoff a b) i v = 0 :=
      fun i => pd_radialCutoff_eq_zero_of_near ha hab hnear i
    have hRcut : radialCutoff a b v * dtH v
        - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v
          = dtH v - laplaceBeltrami g gi H v := by
      rw [hlbmul, hχ1, hlapχ]
      simp [hpdχ]
    rw [hRcut]
    calc |dtH v - laplaceBeltrami g gi H v| ≤ C * gaussDdimWide t v := hEnear v hb
      _ ≤ (C + M * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v := by
          apply mul_le_mul_of_nonneg_right _ hWnn; linarith
  · rcases le_or_gt (rncRadialSq v) (b ^ 2) with hb | hfar
    · -- (b) ANNULUS: a² ≤ rncRadialSq v ≤ b²
      have hlbmul := laplaceBeltrami_mul_inf g gi (radialCutoff a b) H v
        (radialCutoff_contDiff a b) hH (hgisymm v)
      have hRcut : radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v
            = radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v)
              - H v * laplaceBeltrami g gi (radialCutoff a b) v
              - 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v := by
        rw [hlbmul]; ring
      rw [hRcut]
      -- triangle inequality `|A - B' - Cc| ≤ |A| + |B'| + |Cc|`
      have hsub2 : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
        rw [sub_eq_add_neg]; exact (abs_add_le x (-y)).trans_eq (by rw [abs_neg])
      set A := radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v) with hA
      set B' := H v * laplaceBeltrami g gi (radialCutoff a b) v with hB'
      set Cc := 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v with hCc
      have htri : |A - B' - Cc| ≤ |A| + |B'| + |Cc| :=
        (hsub2 (A - B') Cc).trans (by have := hsub2 A B'; linarith)
      -- |A| = |χ·E| ≤ C·W
      have hAbd : |A| ≤ C * gaussDdimWide t v := by
        rw [hA, abs_mul]
        have hχle : |radialCutoff a b v| ≤ 1 := by
          rw [abs_of_nonneg (radialCutoff_nonneg a b v)]; exact radialCutoff_le_one a b v
        calc |radialCutoff a b v| * |dtH v - laplaceBeltrami g gi H v|
            ≤ 1 * (C * gaussDdimWide t v) :=
              mul_le_mul hχle (hEnear v hb) (abs_nonneg _) (by norm_num)
          _ = C * gaussDdimWide t v := by ring
      -- |B'| = |H·Δ_gχ| ≤ (M·Kc2)·W
      have hBbd : |B'| ≤ (M * Kc2) * gaussDdimWide t v := by
        rw [hB', abs_mul]
        calc |H v| * |laplaceBeltrami g gi (radialCutoff a b) v|
            ≤ (M * gaussDdim t v) * Kc2 :=
              mul_le_mul (hHann v ha2 hb) (hLapChi v ha2 hb) (abs_nonneg _)
                (mul_nonneg hM (gaussDdim_nonneg t v))
          _ = (M * Kc2) * gaussDdim t v := by ring
          _ ≤ (M * Kc2) * gaussDdimWide t v := mul_le_mul_of_nonneg_left hgd hb2
      -- |Cc| = |2·∑∑ gⁱʲ ∂ᵢχ ∂ⱼH| ≤ (2 n² Kg Kc1 M (8/a²))·W
      have hSabs : |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      have hterm : ∀ i j : Fin n, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ Kg * Kc1 * (M * (1 / t) * gaussDdim t v) := by
        intro i j
        rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (hgibd v i j ha2 hb) (hDchi v i ha2 hb) (abs_nonneg _) hKg)
          (hDHann v j ha2 hb) (abs_nonneg _) (mul_nonneg hKg hKc1)
      have hsum2 : ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ ∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (M * (1 / t) * gaussDdim t v)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      have hconst : (∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (M * (1 / t) * gaussDdim t v)))
          = (n : ℝ) ^ 2 * (Kg * Kc1 * (M * (1 / t) * gaussDdim t v)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      have hinvT : (1 / t) * gaussDdim t v ≤ (8 / a ^ 2) * gaussDdimWide t v := by
        have h := invTpow_gaussDdim_le_gaussDdimWide 1 a ha ht ha2
        simpa [pow_one, Nat.factorial_one, Nat.cast_one] using h
      have h2pos : (0 : ℝ) < 2 := by norm_num
      have hCcbd : |Cc| ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v := by
        rw [hCc]
        calc |2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
            = 2 * |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v| := by
              rw [abs_mul, abs_of_pos h2pos]
          _ ≤ 2 * ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
              mul_le_mul_of_nonneg_left hSabs (by norm_num)
          _ ≤ 2 * ((n : ℝ) ^ 2 * (Kg * Kc1 * (M * (1 / t) * gaussDdim t v))) :=
              mul_le_mul_of_nonneg_left (hsum2.trans hconst.le) (by norm_num)
          _ = (2 * (n : ℝ) ^ 2 * Kg * Kc1 * M) * ((1 / t) * gaussDdim t v) := by ring
          _ ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * M) * ((8 / a ^ 2) * gaussDdimWide t v) :=
              mul_le_mul_of_nonneg_left hinvT hcoef
          _ = (2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v := by ring
      calc |A - B' - Cc|
          ≤ C * gaussDdimWide t v + (M * Kc2) * gaussDdimWide t v
              + (2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v :=
            htri.trans (add_le_add (add_le_add hAbd hBbd) hCcbd)
        _ = (C + M * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2)) * gaussDdimWide t v := by
            ring
    · -- (c) FAR: b² < rncRadialSq v
      have hχ0 : radialCutoff a b v = 0 := radialCutoff_eq_zero ha hab (le_of_lt hfar)
      have hlbmul := laplaceBeltrami_mul_inf g gi (radialCutoff a b) H v
        (radialCutoff_contDiff a b) hH (hgisymm v)
      have hlapχ : laplaceBeltrami g gi (radialCutoff a b) v = 0 :=
        laplaceBeltrami_radialCutoff_zero_far g gi ha hab hfar
      have hpdχ : ∀ i, pd (radialCutoff a b) i v = 0 :=
        fun i => pd_radialCutoff_eq_zero_of_far ha hab hfar i
      have hRcut : radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v = 0 := by
        rw [hlbmul, hχ0, hlapχ]
        simp [hpdχ]
      rw [hRcut, abs_zero]
      have : (0 : ℝ) ≤ C + M * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * M * (8 / a ^ 2) := by linarith
      exact mul_nonneg this hWnn

/-- **The base-kernel form (width-2 `hEboundW` shape).**  Rewriting the global cutoff residual bound
    through `gaussDdimWide t v = √2ⁿ · baseKernelW 2 0 t v 0` gives the doubled-time base-kernel bound
    `|(∂_t − Δ_g)(χ·H) v| ≤ (B·√2ⁿ) · baseKernelW 2 0 t v 0` — the exact object the Levi/Neumann
    engine's `residual_global_baseKernelW_of_gaussianCofactor` consumes on the diagonal chart. -/
theorem cutoffResidual_global_baseKernelW_bound
    (g gi : Point n → Fin n → Fin n → ℝ) (H dtH : Point n → ℝ)
    (a b t : ℝ) (ha : 0 < a) (hab : a < b) (ht : 0 < t)
    (hH : ContDiff ℝ ∞ H)
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (C : ℝ) (hCnn : 0 ≤ C)
    (hEnear : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |dtH w - laplaceBeltrami g gi H w| ≤ C * gaussDdimWide t w)
    (M : ℝ) (hM : 0 ≤ M)
    (hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |H w| ≤ M * gaussDdim t w)
    (hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd H j w| ≤ M * (1 / t) * gaussDdim t w)
    (Kg Kc1 Kc2 : ℝ) (hKg : 0 ≤ Kg) (hKc1 : 0 ≤ Kc1) (hKc2 : 0 ≤ Kc2)
    (hgibd : ∀ (w : Point n) (i j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |gi w i j| ≤ Kg)
    (hDchi : ∀ (w : Point n) (i : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd (radialCutoff a b) i w| ≤ Kc1)
    (hLapChi : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |laplaceBeltrami g gi (radialCutoff a b) w| ≤ Kc2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Point n,
      |radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v|
        ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by
  obtain ⟨B, hBnn, hBd⟩ := cutoffResidual_global_gaussianWide_bound g gi H dtH a b t ha hab ht hH
    hgisymm C hCnn hEnear M hM hHann hDHann Kg Kc1 Kc2 hKg hKc1 hKc2 hgibd hDchi hLapChi
  refine ⟨B * Real.sqrt 2 ^ n, by positivity, fun v => ?_⟩
  calc |radialCutoff a b v * dtH v
        - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v|
      ≤ B * gaussDdimWide t v := hBd v
    _ = B * (Real.sqrt 2 ^ n * baseKernelW (2 : ℝ) (0 : ℝ) t v 0) := by
        rw [gaussDdimWide_eq_scaled_baseKernelW ht v]
    _ = (B * Real.sqrt 2 ^ n) * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by ring

end QIQTH.HeatResidualBound
