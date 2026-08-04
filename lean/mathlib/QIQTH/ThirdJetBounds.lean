/-
  ThirdJetBounds — J4-193: the THIRD-JET / `∇E`-amplitude layer of the `a₁ = R/6` heat-kernel
  campaign.  Supplies the FIELD-GRADIENT bound of the residual amplitude `A = residualCoeffA` (the
  τ²-cleared, compact-box bound) and the pointwise product-rule skeleton the `∇(G·A)` assembly feeds
  through the J4-191 Gaussian-absorption levers.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE brick of
  the `a₁ = R/6` heat-kernel campaign — the `hEgrad` amplitude-gradient item.  The `∇E` bound consumed
  downstream needs the FIELD-slot derivative of the residual amplitude `A`; `A` carries the metric /
  Christoffel / Laplace–Beltrami coefficients through second jets, so `∂ⱼA` is a genuine THIRD-jet
  object.  This file delivers its τ²-cleared compact bound (the direct J4-190 mirror, at the gradient)
  plus the pointwise Leibniz skeleton.  No `sorry`, no new axioms, no vacuous/unsatisfiable hypotheses,
  no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file delivers (ns `QIQTH.ThirdJetBounds`).

    * `pd_slice_eq_fderiv` — THE PARAM/SLICE BRIDGE.  For a jointly differentiable `F : ℝ × Point n → ℝ`
      the field-slot partial equals the joint Fréchet derivative in the pure-field direction:
        `pd (fun w => F (t, w)) j v = fderiv ℝ F (t, v) (0, eⱼ)`  (chain rule through `update`, mirroring
      `Curvature.pd_eq_fderiv` one product-slot up).

    * `residualCoeffAWeighted_contDiff` — THE JOINT `C^∞` UPGRADE of the τ²-cleared amplitude
      `residualCoeffAWeighted` (J4-190): `(τ,v) ↦ residualCoeffAWeighted` is jointly `ContDiff ℝ ∞`.
      The `ContDiff` analogue of `CompactJetBounds.residualCoeffAWeighted_continuous`: every factor field
      is `ContDiff` (`christoffel_contDiff` / `laplaceBeltrami_contDiff` / `contDiff_pd_inf` / the radial
      sum), the poly-gradient reduces by `pd_poly_eq_sum`, and `ContDiff.{add,sub,mul,sum}` assemble it.
      This is what makes `fderiv` of the amplitude CONTINUOUS, hence bounded on the compact box.

    * ★ `residualCoeffA_grad_tau_weighted_bound` — THE τ²-WEIGHTED AMPLITUDE-GRADIENT BOUND.  On the box
      `(0,T] × closedBall 0 b`,
        `τ² · |pd (residualCoeffA N g gi Θ u τ ·) j v| ≤ C`   (NON-NEGATIVE `C`).
      The direct J4-190 mirror, at the GRADIENT: the pole-clearing `τ²·A = residualCoeffAWeighted`
      (`residualCoeffAWeighted_eq`) commutes with the FIELD `pd` (the τ-Laurent weight is a v-constant,
      pulled through `pd_const_mul`), so `τ²·pd A = pd residualCoeffAWeighted = fderiv F (τ,v)(0,eⱼ)`
      (the slice bridge), which is continuous hence bounded on the compact box.  The honest bounded form
      of the pole-carrying gradient `∂ⱼA` (which blows up as `τ↓0`) — the amplitude-gradient input the
      coming `∇(G·A)` step consumes.  NOT `a₁ = R/6`.

    * `gradGA_term_bound_skeleton` — THE POINTWISE LEIBNIZ SKELETON.  For `τ>0`,
        `|∂ᵢ(G·A)(v)| ≤ (|vᵢ|/(2τ))·G_τ(v)·|A(v)| + G_τ(v)·|∂ᵢA(v)|`,
      the exact triangle form the final `∇E` assembly feeds through the J4-191 absorption levers
      (`(|vᵢ|/τ)·G` and `G·(τ²-cleared ∂A)`).  Product rule (`pd_mul`) + the banked Gaussian gradient
      `gaussDdim_pd_eq` + triangle inequality.  The `PdiffAt A` hypothesis is genuine and satisfiable
      (dischargeable from `{hg,hgi,hw}` via the joint `ContDiff` above).  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  Diagonal-chart amplitude, single base point; the bound carries only the
  EXISTENCE of the sup-constant (uniform-over-base-point constants are the recognized residue).  NOT the
  `∇E` bound itself (the mixed-third-jet Gaussian-moment estimate is the downstream multi-brick layer);
  this file supplies its AMPLITUDE-gradient input and the assembly skeleton.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CompactJetBounds
import QIQTH.CutoffResidualGlobalBound
import QIQTH.OnGateFieldRegularity
import QIQTH.ChartThirdJet

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.TransportOpSmoothness QIQTH.RadialTransport
open QIQTH.ErrorKernelFactorization QIQTH.FlatHeatEquation QIQTH.CompactJetBounds
open QIQTH.HeatParametrixOrder QIQTH.ResidueBound
open QIQTH.VanVleck QIQTH.HeatParametrixAnsatz QIQTH.HeatTransportRecursion
open QIQTH.ParametrixFunction QIQTH.OnGateFieldRegularity QIQTH.ChartThirdJet
open scoped BigOperators ContDiff

namespace QIQTH.ThirdJetBounds

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ## 1.  The param/slice bridge:  field-slot `pd` = joint `fderiv` in the pure-field direction. -/

/-- **`pd_slice_eq_fderiv` — the param/slice bridge.**  For `F : ℝ × Point n → ℝ` differentiable at
    `(t,v)`, the field-slot partial of the `t`-slice equals the joint Fréchet derivative applied to the
    pure-field basis direction `(0, eⱼ)`:
      `pd (fun w => F (t, w)) j v = fderiv ℝ F (t, v) (0, Pi.single j 1)`.
    Chain rule through the coordinate line `s ↦ (t, update v j s)` (its derivative is `(0, eⱼ)`), the
    exact product-slot analogue of `Curvature.pd_eq_fderiv`. -/
theorem pd_slice_eq_fderiv (F : ℝ × Point n → ℝ) (t : ℝ) (v : Point n) (j : Fin n)
    (hF : DifferentiableAt ℝ F (t, v)) :
    pd (fun w => F (t, w)) j v = fderiv ℝ F (t, v) (0, Pi.single j (1 : ℝ)) := by
  have hu : HasDerivAt (fun s : ℝ => ((t, Function.update v j s) : ℝ × Point n))
      ((0 : ℝ), Pi.single j (1 : ℝ)) (v j) :=
    (hasDerivAt_const (v j) t).prodMk (hasDerivAt_update v j (v j))
  have hFf : HasFDerivAt F (fderiv ℝ F (t, v))
      ((fun s : ℝ => ((t, Function.update v j s) : ℝ × Point n)) (v j)) := by
    simp only [Function.update_eq_self]; exact hF.hasFDerivAt
  have h := (hFf.comp_hasDerivAt (v j) hu).deriv
  simpa only [pd, Function.comp] using h

/-! ## 2.  The joint `C^∞` upgrade of the τ²-cleared amplitude. -/

/-- **`residualCoeffAWeighted_contDiff` — joint `C^∞` upgrade.**  `(τ,v) ↦ residualCoeffAWeighted` is
    jointly `ContDiff ℝ ∞`.  The `ContDiff` analogue of `residualCoeffAWeighted_continuous`: each factor
    field is `ContDiff` (downcasting `christoffel_contDiff`/`laplaceBeltrami_contDiff` from `⊤`, the
    folded coefficients and their partials via `contDiff_pd_inf`, the radial sum), the internal
    poly-gradient is reduced by `pd_poly_eq_sum`, and `ContDiff.{add,sub,mul,sum}` assemble the whole.
    This is what makes `fderiv` of the amplitude continuous. -/
theorem residualCoeffAWeighted_contDiff (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ)
    (hg : ∀ a c, ContDiff ℝ ⊤ (fun y => g y a c))
    (hgi : ∀ a c, ContDiff ℝ ⊤ (fun y => gi y a c))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    ContDiff ℝ ∞ (fun p : ℝ × Point n => residualCoeffAWeighted N g gi Θ u p.1 p.2) := by
  have mv : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × Point n => p.2 i) :=
    fun i => ((contDiff_apply ℝ ℝ i : ContDiff ℝ ∞ (fun f : Point n => f i)).comp
      contDiff_snd)
  have mtk : ∀ k : ℕ, ContDiff ℝ ∞ (fun p : ℝ × Point n => p.1 ^ k) :=
    fun k => contDiff_fst.pow k
  have mt : ContDiff ℝ ∞ (fun p : ℝ × Point n => p.1) := contDiff_fst
  have mgi : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × Point n => gi p.2 i j) :=
    fun i j => ((hgi i j).of_le le_top).comp contDiff_snd
  have mchr : ∀ k i j, ContDiff ℝ ∞ (fun p : ℝ × Point n => christoffel g gi k i j p.2) :=
    fun k i j => ((christoffel_contDiff g gi hg hgi k i j).of_le le_top).comp contDiff_snd
  have mw : ∀ k, ContDiff ℝ ∞ (fun p : ℝ × Point n => foldedCoeff Θ u k p.2) :=
    fun k => ((hw k).of_le le_top).comp contDiff_snd
  have hradv : ∀ k, ContDiff ℝ ∞ (fun v : Point n => radialDeriv (foldedCoeff Θ u k) v) := by
    intro k
    simp only [radialDeriv]
    exact ContDiff.sum (fun i _ =>
      (contDiff_apply ℝ ℝ i : ContDiff ℝ ∞ (fun f : Point n => f i)).mul
        (contDiff_pd_inf (foldedCoeff Θ u k) ((hw k).of_le le_top) i))
  have mrad : ∀ k, ContDiff ℝ ∞ (fun p : ℝ × Point n => radialDeriv (foldedCoeff Θ u k) p.2) :=
    fun k => (hradv k).comp contDiff_snd
  have mlap : ∀ k, ContDiff ℝ ∞ (fun p : ℝ × Point n => laplaceBeltrami g gi (foldedCoeff Θ u k) p.2) :=
    fun k => ((laplaceBeltrami_contDiff g gi hg hgi (foldedCoeff Θ u k) (hw k)).of_le le_top).comp
      contDiff_snd
  have mpd : ∀ k j, ContDiff ℝ ∞ (fun p : ℝ × Point n => pd (foldedCoeff Θ u k) j p.2) :=
    fun k j => (contDiff_pd_inf (foldedCoeff Θ u k) ((hw k).of_le le_top) j).comp contDiff_snd
  have hpdP : ∀ j, ContDiff ℝ ∞ (fun p : ℝ × Point n =>
      pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * p.1 ^ k) j p.2) := by
    intro j
    have heq : (fun p : ℝ × Point n =>
        pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * p.1 ^ k) j p.2)
        = (fun p : ℝ × Point n =>
            ∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j p.2 * p.1 ^ k) := by
      funext p; exact pd_poly_eq_sum N Θ u p.1 j p.2 hw
    rw [heq]
    exact ContDiff.sum (fun k _ => (mpd k j).mul (mtk k))
  simp only [residualCoeffAWeighted]
  have hb1e : ContDiff ℝ ∞ (fun p : ℝ × Point n =>
      (1 / 2 : ℝ) * (∑ i, (gi p.2 i i - 1))
        - (1 / 2 : ℝ) * (∑ i, ∑ j, ∑ k, gi p.2 i j * christoffel g gi k i j p.2 * p.2 k)) :=
    (contDiff_const.mul (ContDiff.sum (fun i _ => (mgi i i).sub contDiff_const))).sub
      (contDiff_const.mul (ContDiff.sum (fun i _ =>
        ContDiff.sum (fun j _ =>
          ContDiff.sum (fun k _ => ((mgi i j).mul (mchr k i j)).mul (mv k))))))
  have hb2e : ContDiff ℝ ∞ (fun p : ℝ × Point n =>
      (-1 / 4 : ℝ) * (∑ i, ∑ j, (gi p.2 i j - (if i = j then (1 : ℝ) else 0)) * (p.2 i * p.2 j))) :=
    contDiff_const.mul (ContDiff.sum (fun i _ =>
      ContDiff.sum (fun j _ => ((mgi i j).sub contDiff_const).mul ((mv i).mul (mv j)))))
  have hP : ContDiff ℝ ∞ (fun p : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k p.2 * p.1 ^ k) :=
    ContDiff.sum (fun k _ => (mw k).mul (mtk k))
  have hS2 : ContDiff ℝ ∞ (fun p : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k p.2 * ((k : ℝ) * p.1 ^ (k - 1))) :=
    ContDiff.sum (fun k _ => (mw k).mul (contDiff_const.mul (mtk (k - 1))))
  have hRtail : ContDiff ℝ ∞ (fun p : ℝ × Point n =>
      ∑ k ∈ Finset.range N, radialDeriv (foldedCoeff Θ u (k + 1)) p.2 * p.1 ^ k) :=
    ContDiff.sum (fun k _ => (mrad (k + 1)).mul (mtk k))
  have hLap : ContDiff ℝ ∞ (fun p : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) p.2 * p.1 ^ k) :=
    ContDiff.sum (fun k _ => (mlap k).mul (mtk k))
  have hdevP : ContDiff ℝ ∞ (fun p : ℝ × Point n =>
      (-1 / 2 : ℝ) * ∑ i, ∑ j, (gi p.2 i j - (if i = j then (1 : ℝ) else 0))
          * (p.2 i * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * p.1 ^ k) j p.2
              + p.2 j * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * p.1 ^ k) i p.2)) :=
    contDiff_const.mul (ContDiff.sum (fun i _ =>
      ContDiff.sum (fun j _ => ((mgi i j).sub contDiff_const).mul
        (((mv i).mul (hpdP j)).add ((mv j).mul (hpdP i))))))
  exact ((((((mt.mul hb1e).add hb2e).mul hP).add ((mtk 2).mul hS2)).add
    ((mt.mul (mrad 0)).add ((mtk 2).mul hRtail))).sub ((mtk 2).mul hLap)).sub (mt.mul hdevP)

/-! ## 3.  ★ The τ²-weighted amplitude-gradient bound. -/

/-- **★ `residualCoeffA_grad_tau_weighted_bound` — the τ²-weighted amplitude-GRADIENT bound.**  On the
    box `(0,T] × closedBall 0 b`, the τ²-weighted field-gradient of the Laurent amplitude is bounded by a
    NON-NEGATIVE constant:
      `τ² · |pd (residualCoeffA N g gi Θ u τ ·) j v| ≤ C`   for all `0 < τ ≤ T`, `v ∈ closedBall 0 b`.
    The direct J4-190 mirror, at the gradient.  Pole-clearing / pd-commutation: `τ²·A =
    residualCoeffAWeighted` (`residualCoeffAWeighted_eq`, `τ ≠ 0`), and since the τ²-weight is a
    v-constant it passes THROUGH the field `pd` (`pd_const_mul`), so
      `τ²·pd A = pd residualCoeffAWeighted = fderiv F (τ,v)(0,eⱼ)`
    (the slice bridge `pd_slice_eq_fderiv`), where `F = residualCoeffAWeighted`.  `fderiv F` is
    CONTINUOUS (`residualCoeffAWeighted_contDiff` + `ContDiff.continuous_fderiv`), hence bounded on the
    compact box `Icc 0 T ×ˢ closedBall 0 b`.  The honest bounded form of the pole-carrying gradient
    `∂ⱼA`.  NOT `a₁ = R/6`. -/
theorem residualCoeffA_grad_tau_weighted_bound (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (T b : ℝ) (j : Fin n)
    (hg : ∀ a c, ContDiff ℝ ⊤ (fun y => g y a c))
    (hgi : ∀ a c, ContDiff ℝ ⊤ (fun y => gi y a c))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (v : Point n), 0 < t → t ≤ T →
      v ∈ Metric.closedBall (0 : Point n) b →
      t ^ 2 * |pd (fun w => residualCoeffA N g gi Θ u t w) j v| ≤ C := by
  set F : ℝ × Point n → ℝ :=
    fun p => residualCoeffAWeighted N g gi Θ u p.1 p.2 with hFdef
  have hFcd : ContDiff ℝ ∞ F := residualCoeffAWeighted_contDiff N g gi Θ u hg hgi hw
  have hcont : Continuous (fun p : ℝ × Point n => fderiv ℝ F p (0, Pi.single j (1 : ℝ))) :=
    (hFcd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hKcpt : IsCompact (Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : Point n) b) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : Point n) b)
  obtain ⟨C, hC⟩ := hKcpt.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t v ht htT hv => ?_⟩
  have htne : t ≠ 0 := ne_of_gt ht
  have hmem : (t, v) ∈ Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : Point n) b :=
    ⟨⟨ht.le, htT⟩, hv⟩
  have hbnd := hC (t, v) hmem
  rw [Real.norm_eq_abs] at hbnd
  -- residualCoeffA slice is `C^∞` (from `F`-slice via the pole-cleared identity), giving `PdiffAt`.
  have hslice : ContDiff ℝ ∞ (fun w : Point n => F (t, w)) :=
    hFcd.comp (contDiff_const.prodMk contDiff_id)
  have hAslice : ContDiff ℝ ∞ (fun w : Point n => residualCoeffA N g gi Θ u t w) := by
    have heqf : (fun w : Point n => residualCoeffA N g gi Θ u t w)
        = (fun w : Point n => (1 / t ^ 2) * F (t, w)) := by
      funext w
      simp only [hFdef]
      rw [← residualCoeffAWeighted_eq N g gi Θ u t htne w, ← mul_assoc, one_div,
        inv_mul_cancel₀ (pow_ne_zero 2 htne), one_mul]
    rw [heqf]
    exact contDiff_const.mul hslice
  have hPd : PdiffAt (fun w => residualCoeffA N g gi Θ u t w) j v :=
    PdiffAt_of_contDiff_inf _ hAslice j v
  -- pole-clearing + slice bridge:  `t²·pd A = fderiv F (t,v)(0,eⱼ)`.
  have hbridge : pd (fun w => F (t, w)) j v = fderiv ℝ F (t, v) (0, Pi.single j (1 : ℝ)) :=
    pd_slice_eq_fderiv F t v j (hFcd.differentiable (by simp)).differentiableAt
  have hAeq : (fun w : Point n => F (t, w))
      = (fun w : Point n => t ^ 2 * residualCoeffA N g gi Θ u t w) := by
    funext w; simp only [hFdef]
    exact (residualCoeffAWeighted_eq N g gi Θ u t htne w).symm
  have hkey : t ^ 2 * pd (fun w => residualCoeffA N g gi Θ u t w) j v
      = fderiv ℝ F (t, v) (0, Pi.single j (1 : ℝ)) := by
    rw [← hbridge, hAeq,
      pd_const_mul (t ^ 2) (fun w => residualCoeffA N g gi Θ u t w) j v hPd]
  have hfinal : t ^ 2 * |pd (fun w => residualCoeffA N g gi Θ u t w) j v|
      = |fderiv ℝ F (t, v) (0, Pi.single j (1 : ℝ))| := by
    rw [← hkey, abs_mul, abs_of_nonneg (sq_nonneg t)]
  rw [hfinal]
  exact le_trans hbnd (le_max_left _ _)

/-! ## 4.  The pointwise Leibniz skeleton for `∇(G·A)`. -/

/-- **`gradGA_term_bound_skeleton` — the pointwise `∇(G·A)` triangle skeleton.**  For `τ > 0`,
      `|∂ᵢ(G_τ·A)(v)| ≤ (|vᵢ|/(2τ))·G_τ(v)·|A(v)| + G_τ(v)·|∂ᵢA(v)|`,
    with `A = residualCoeffA N g gi Θ u τ`.  Product rule (`pd_mul`), the banked flat-Gaussian gradient
    `gaussDdim_pd_eq` (`∂ᵢG_τ = (−vᵢ/2τ)·G_τ`), and the triangle inequality; `G_τ ≥ 0` collapses the
    absolute value on the Gaussian.  The `PdiffAt A` hypothesis is genuine and satisfiable (discharge it
    from `{hg,hgi,hw}` via `residualCoeffAWeighted_contDiff` / `PdiffAt_of_contDiff_inf`).  This is the
    exact triangle the `∇E` assembly feeds through the J4-191 absorption levers.  NOT `a₁ = R/6`. -/
theorem gradGA_term_bound_skeleton (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (v : Point n)
    (hA : PdiffAt (fun w => residualCoeffA N g gi Θ u τ w) i v) :
    |pd (fun w => gaussDdim τ w * residualCoeffA N g gi Θ u τ w) i v|
      ≤ |v i| / (2 * τ) * gaussDdim τ v * |residualCoeffA N g gi Θ u τ v|
        + gaussDdim τ v * |pd (fun w => residualCoeffA N g gi Θ u τ w) i v| := by
  have hG : PdiffAt (fun w => gaussDdim τ w) i v :=
    PdiffAt_of_contDiff _ (gaussDdim_contDiff τ) i v
  have hGnn : (0 : ℝ) ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  rw [pd_mul (fun w => gaussDdim τ w) (fun w => residualCoeffA N g gi Θ u τ w) i v hG hA,
    gaussDdim_pd_eq τ hτ v i]
  calc |(-(v i) / (2 * τ) * gaussDdim τ v) * residualCoeffA N g gi Θ u τ v
          + gaussDdim τ v * pd (fun w => residualCoeffA N g gi Θ u τ w) i v|
      ≤ |(-(v i) / (2 * τ) * gaussDdim τ v) * residualCoeffA N g gi Θ u τ v|
          + |gaussDdim τ v * pd (fun w => residualCoeffA N g gi Θ u τ w) i v| := abs_add_le _ _
    _ = |v i| / (2 * τ) * gaussDdim τ v * |residualCoeffA N g gi Θ u τ v|
          + gaussDdim τ v * |pd (fun w => residualCoeffA N g gi Θ u τ w) i v| := by
        have e1 : |(-(v i) / (2 * τ) * gaussDdim τ v) * residualCoeffA N g gi Θ u τ v|
            = |v i| / (2 * τ) * gaussDdim τ v * |residualCoeffA N g gi Θ u τ v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hGnn, abs_div, abs_neg,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * τ)]
        have e2 : |gaussDdim τ v * pd (fun w => residualCoeffA N g gi Θ u τ w) i v|
            = gaussDdim τ v * |pd (fun w => residualCoeffA N g gi Θ u τ w) i v| := by
          rw [abs_mul, abs_of_nonneg hGnn]
        rw [e1, e2]

/-! ## 5.  The parametrix field-`C³` corollary (mirror of `innerKernel_contDiffAt_field`, order 3). -/

/-- **★ `parametrix_contDiffAt_three_field`.**  The gated van-Vleck parametrix (the ungated inner kernel
    `radialCutoff · gaussDdim · vanVleck^{-1/2} · transportSum`, all composed through the inverse chart)
    is `ContDiffAt ℝ 3` in the FIELD slot at a general field point `x₀`, from the field-chart `C³` carry
    `hWC3` plus `hg`/`hgpos`/`hu`.  The exact `ContDiffAt.comp` tower of `innerKernel_contDiffAt_field`
    lifted one order up (`2 → 3`): the `C^∞`/`⊤` outer factors downcast to `3`, `det g (V_z x₀) > 0`
    supplies both the van-Vleck smoothness and the nonzero base of the `−1/2` rpow branch.  NOT
    `a₁ = R/6`. -/
theorem parametrix_contDiffAt_three_field (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (τ : ℝ) (z x₀ : Point n)
    (hWC3 : ContDiffAt ℝ 3 (uniformInverseChart g gi hC hK z) x₀)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 3 (innerKernelField g gi hC hK a b τ z) x₀ := by
  unfold innerKernelField
  set W := uniformInverseChart g gi hC hK z with hWdef
  have hcut : ContDiffAt ℝ 3 (fun p => radialCutoff a b (W p)) x₀ :=
    ((radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)).comp x₀ hWC3
  have hgauss : ContDiffAt ℝ 3 (fun p => gaussDdim τ (W p)) x₀ :=
    ((gaussDdim_contDiff τ).contDiffAt.of_le le_top).comp x₀ hWC3
  have hdetW : 0 < Matrix.det (g (W x₀)) := hgpos (W x₀)
  have hvv : ContDiffAt ℝ 3 (fun p => vanVleck g (W p)) x₀ :=
    (vanVleck_contDiffAt g hg (W x₀) hdetW (k := 3)).comp x₀ hWC3
  have hne : (fun p => vanVleck g (W p)) x₀ ≠ 0 :=
    ne_of_gt (vanVleck_pos g (W x₀) hdetW)
  have hrpow : ContDiffAt ℝ 3 (fun p => vanVleck g (W p) ^ (-(1 : ℝ) / 2)) x₀ :=
    hvv.rpow_const_of_ne hne
  have hu0 : ContDiffAt ℝ 3
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)) x₀ :=
    (((hu 0).contDiffAt).of_le le_top).comp x₀ hWC3
  have hu1 : ContDiffAt ℝ 3
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 1 (W p)) x₀ :=
    (((hu 1).contDiffAt).of_le le_top).comp x₀ hWC3
  have hsum : ContDiffAt ℝ 3
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)
        + transportCoeff (transportOp (vanVleck g) g gi) 1 (W p) * τ) x₀ :=
    hu0.add (hu1.mul contDiffAt_const)
  exact hcut.mul ((hgauss.mul hrpow).mul hsum)

/-- **★ `parametrix_contDiffAt_three_field_basePoint`.**  The base-point specialisation `x₀ = z = φ_z 0`:
    the parametrix inner kernel is `ContDiffAt ℝ 3` in the field slot at the base point `z`, with the
    field-chart `C³` carry DERIVED from the tower `chartField_contDiffAt_four_basePoint` (the chart is
    `C⁴` at the base, downcast to `C³`).  NOT `a₁ = R/6`. -/
theorem parametrix_contDiffAt_three_field_basePoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (τ : ℝ) (z : Point n) (hz : z ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 3 (innerKernelField g gi hC hK a b τ z) z := by
  have hWC3 : ContDiffAt ℝ 3 (uniformInverseChart g gi hC hK z) z :=
    (chartField_contDiffAt_four_basePoint g gi hC hK z hz).of_le (by norm_num)
  exact parametrix_contDiffAt_three_field g gi hC hK a b τ z z hWC3 hg hgpos hu

/-! ## 6.  Third-jet field continuity + the compact sup-bound lever. -/

/-- **★ `chartField_secondJetField_contDiffAt`.**  At any point `x₀` where the inverse chart is `C⁴`
    (`hreg`), the SECOND field line-jet FIELD
      `x ↦ fderiv ℝ (fun u => fderiv ℝ V_z u eᵢ) x eᵢ`
    is `ContDiffAt ℝ 1` at `x₀` — equivalently, the THIRD field-derivative of the chart EXISTS and is
    CONTINUOUS at `x₀` (a `C¹` field has a continuous derivative).  Extracts the `hHfd1`-level of
    `chartField_thirdJet_of_contDiffAt`, lifted to a general point `x₀`: from `C⁴` the chart is `C³`, so
    the first-jet field `H = DV_z(·)(eᵢ)` is `C²`, `fderiv H` is `C¹`, and the second-jet field
    `(fderiv H)(·)(eᵢ)` is `C¹`.  NOT `a₁ = R/6`. -/
theorem chartField_secondJetField_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i : Fin n) (x₀ : Point n)
    (hreg : ContDiffAt ℝ 4 (uniformInverseChart g gi hC hK z) x₀) :
    ContDiffAt ℝ 1 (fun x => fderiv ℝ
        (fun u => fderiv ℝ (uniformInverseChart g gi hC hK z) u (Pi.single i (1 : ℝ)))
        x (Pi.single i (1 : ℝ))) x₀ := by
  set W := uniformInverseChart g gi hC hK z with hWdef
  have h3 : ContDiffAt ℝ 3 W x₀ := hreg.of_le (by norm_num)
  have hH2 : ContDiffAt ℝ 2 (fun u => (fderiv ℝ W u) (Pi.single i (1 : ℝ))) x₀ :=
    (h3.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hHfd1 : ContDiffAt ℝ 1
      (fun x => fderiv ℝ (fun u => (fderiv ℝ W u) (Pi.single i (1 : ℝ))) x) x₀ :=
    hH2.fderiv_right (m := 1) (by norm_num)
  exact hHfd1.clm_apply contDiffAt_const

/-- **`chartField_secondJetField_continuousAt`.**  The continuity corollary of the above: at a reachable
    `C⁴` point the second-jet field (hence the third field-derivative) is `ContinuousAt x₀`.  NOT
    `a₁ = R/6`. -/
theorem chartField_secondJetField_continuousAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i : Fin n) (x₀ : Point n)
    (hreg : ContDiffAt ℝ 4 (uniformInverseChart g gi hC hK z) x₀) :
    ContinuousAt (fun x => fderiv ℝ
        (fun u => fderiv ℝ (uniformInverseChart g gi hC hK z) u (Pi.single i (1 : ℝ)))
        x (Pi.single i (1 : ℝ))) x₀ :=
  (chartField_secondJetField_contDiffAt g gi hC hK z i x₀ hreg).continuousAt

/-- **★ `chartField_secondJetField_contDiffAt_basePoint`.**  The unconditional base-point instance
    (`z = 0`, field point `0`, `0 ∈ K`): the second-jet field is `ContDiffAt ℝ 1` at `0`, with the `C⁴`
    carry TOWER-DERIVED from `chartField_contDiffAt_four_basePoint`.  NOT `a₁ = R/6`. -/
theorem chartField_secondJetField_contDiffAt_basePoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (i : Fin n) :
    ContDiffAt ℝ 1 (fun x => fderiv ℝ
        (fun u => fderiv ℝ (uniformInverseChart g gi hC hK 0) u (Pi.single i (1 : ℝ)))
        x (Pi.single i (1 : ℝ))) 0 :=
  chartField_secondJetField_contDiffAt g gi hC hK 0 i 0
    (chartField_contDiffAt_four_basePoint g gi hC hK 0 h0K)

/-- **`chartField_thirdJet_component_bound` — the J4-190 compact-bound lever at the third jet.**  Given
    CONTINUITY of a scalar component `f` of the third field-jet on `Point n` (satisfiable on any closed
    ball inside the reachable `C⁴` region — `chartField_secondJetField_continuousAt`), `f` admits a
    NON-NEGATIVE uniform sup-bound over `closedBall 0 b`.  This is the `exists_bound_closedBall`
    lever (J4-190) re-exposed at the third-jet layer; the uniform-over-base-point / gate-wide constant
    (blocked by the per-base `expRho` guard) remains the honest residue.  NOT `a₁ = R/6`. -/
theorem chartField_thirdJet_component_bound (f : Point n → ℝ) (b : ℝ) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ Metric.closedBall (0 : Point n) b, |f v| ≤ C :=
  exists_bound_closedBall b hf

/-! ## Axiom checks — every main result is `std-3` (propext, Classical.choice, Quot.sound). -/

section AxiomChecks

#print axioms pd_slice_eq_fderiv
#print axioms residualCoeffAWeighted_contDiff
#print axioms residualCoeffA_grad_tau_weighted_bound
#print axioms gradGA_term_bound_skeleton
#print axioms parametrix_contDiffAt_three_field
#print axioms parametrix_contDiffAt_three_field_basePoint
#print axioms chartField_secondJetField_contDiffAt
#print axioms chartField_secondJetField_continuousAt
#print axioms chartField_secondJetField_contDiffAt_basePoint
#print axioms chartField_thirdJet_component_bound

end AxiomChecks

end QIQTH.ThirdJetBounds
