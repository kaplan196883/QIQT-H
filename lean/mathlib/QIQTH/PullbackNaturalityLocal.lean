/-
  PullbackNaturalityLocal — J4-91: the LOCAL (`ContDiffAt` / on-ball) Laplace–Beltrami pullback
  naturality and its instantiation at `φ = uniformFlowExp`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## Why this file exists (the one firewall of J4-90).

  `PullbackNaturality.lean` (J4-90) proved the ABSTRACT capstone
      `laplaceBeltrami_pullback_naturality` : `Δ_{φ*g}(f∘φ)(x) = (Δ_g f)(φ x)`
  for `ContDiff ⊤` `φ` (and `g`, `f`).  Its ONE firewall: `φ = uniformFlowExp g gi hC hK q` is only
  `C²`-on-a-ball (built by `Classical.choose` of a geodesic ODE), never globally `ContDiff ⊤`, so the
  abstract capstone cannot be instantiated there.

  This file re-runs the whole `pd` tower at FINITE, POINTWISE regularity and instantiates it.

  ## Localization findings (what each step actually needs — proved below).

  The naturality identity at a single point `x` consumes derivatives only AT/NEAR `x` (of `φ`, 2 orders)
  and AT/NEAR `φ x` (of `g`, 1 order; of `f`, 2 orders).  Concretely each localized lemma needs exactly:
    * `φ`: per-component `ContDiffAt ℝ 2 (fun y => φ y a) x` — gives the two `φ`-jets at `x`, the germ
      differentiability near `x` (via `ContDiffAt.eventually`), the whole-map `DifferentiableAt ℝ φ x`
      (via `differentiableAt_pi`), and Schwarz `∂_i∂_j φ^a = ∂_j∂_i φ^a` (via a `ContDiffAt 2`-localised
      `pd_comm`, `pd_comm_of_contDiffAt2'`).
    * `g`: per-entry `ContDiffAt ℝ 1 (fun y => g y a b) (φ x)` — gives the value `g(φx)` and the first
      partial `∂_c g(φx)` (which enters only as a VALUE, never re-differentiated).
    * `f`: `ContDiffAt ℝ 2 f (φ x)` — gives `f`, `∂_a f`, `∂_b∂_a f` at `φx`, plus germ
      differentiability of `f` and of `∂_a f` near `φx`.

  ## Landed here (green; NO `sorry`, NO new axioms, NO `expRho` in statements, NO vacuous hyps).

    * `pd_pd_eq_of_contDiffAt2'` / `pd_comm_of_contDiffAt2'` — general-base-point `C²` Schwarz.
    * `pullback_metric_deriv_local` (N2 local), `pullback_christoffel_combo_local` (N2b local),
      `pullback_christoffel_transform_local` (N3 local), `pd_pd_comp_local` (2nd chain rule local),
    * `laplaceBeltrami_pullback_naturality_local` (N4 local, CAPSTONE L2).
    * L3 bridges `contDiffAt2_uniformFlowExp_comp`, `pullbackMet_eq_uniformFlowPullbackMetric`.
    * `laplaceBeltrami_uniformFlow_naturality` (L4, CAPSTONE): naturality at `φ = uniformFlowExp`, on the
      common nondegeneracy ball, with genuine metric/inverse hypotheses only.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.LaplaceBeltrami
import QIQTH.ResidualChartTransport
import QIQTH.PullbackNaturality
import QIQTH.PullbackNondegFromFDeriv
import QIQTH.ChristoffelSmooth
import QIQTH.LaplaceBeltramiFiniteReg
import QIQTH.UniformFlowFDeriv
import QIQTH.UniformFlowHessian
import QIQTH.UniformFlowThirdBoundClose
import QIQTH.UniformFlowNondegClose
import QIQTH.UniformFlowPullback
import QIQTH.UniformFlowMetricInvProps

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.ExpMap

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-! ### L0 — general-base-point `C²` Schwarz (localised `pd_comm`). -/

/-- **Local mixed second partial = second Fréchet-derivative bilinear form** at an ARBITRARY point `x`,
    from `ContDiffAt ℝ 2 f x` (general-point port of `PullbackMetric.pd_pd_eq_of_contDiffAt2`). -/
theorem pd_pd_eq_of_contDiffAt2' (f : Point n → ℝ) (i j : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 2 f x) :
    pd (fun y => pd f j y) i x
      = fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := by
  have hdf_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := hf.eventually (by norm_num)
    filter_upwards [hev] with y hy using hy.differentiableAt (by norm_num)
  have hfd2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have e1 : (fun y => pd f j y) =ᶠ[nhds x] (fun y => (fderiv ℝ f y) (Pi.single j 1)) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f j y hy
  rw [pd_congr_nhds i x e1,
      pd_eq_fderiv _ i x (hfd2.clm_apply (differentiableAt_const _)),
      fderiv_clm_apply hfd2 (differentiableAt_const _)]
  simp

/-- **`C²`-localised Schwarz** (general base point): `∂_i∂_j f = ∂_j∂_i f` from `ContDiffAt ℝ 2 f x`. -/
theorem pd_comm_of_contDiffAt2' (f : Point n → ℝ) (i j : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 2 f x) :
    pd (fun y => pd f j y) i x = pd (fun y => pd f i y) j x := by
  rw [pd_pd_eq_of_contDiffAt2' f i j x hf, pd_pd_eq_of_contDiffAt2' f j i x hf]
  exact (hf.isSymmSndFDerivAt (by simp)).eq _ _

/-! ### N2 local — the pullback-metric derivative at finite regularity. -/

/-- **N2 local** — `pullback_metric_deriv` with `ContDiff ⊤` weakened to per-point regularity:
    `g` entrywise `ContDiffAt ℝ 1` at `φx`, `φ` per-component `ContDiffAt ℝ 2` at `x`. -/
theorem pullback_metric_deriv_local (g : Point n → Fin n → Fin n → ℝ) (φ : Point n → Point n)
    (i l j : Fin n) (x : Point n)
    (hg : ∀ a b, ContDiffAt ℝ 1 (fun y => g y a b) (φ x))
    (hφ : ∀ a, ContDiffAt ℝ 2 (fun y => φ y a) x) :
    pd (fun v => pullbackMet g φ v l j) i x
      = ∑ a, ∑ b,
          ((∑ c, pd (fun w => g w a b) c (φ x) * pd (fun y => φ y c) i x)
              * pd (fun y => φ y a) l x * pd (fun y => φ y b) j x
            + g (φ x) a b * pd (fun v => pd (fun y => φ y a) l v) i x * pd (fun y => φ y b) j x
            + g (φ x) a b * pd (fun y => φ y a) l x
                * pd (fun v => pd (fun y => φ y b) j v) i x) := by
  classical
  have hφd : DifferentiableAt ℝ φ x :=
    differentiableAt_pi.mpr (fun a => (hφ a).differentiableAt (by norm_num))
  have hgd : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) (φ x) :=
    fun a b => (hg a b).differentiableAt (by norm_num)
  have hP : ∀ a b, PdiffAt (fun v => g (φ v) a b) i x :=
    fun a b => pdiffAt_of_differentiableAt _ i x ((hgd a b).comp x hφd)
  have hQ : ∀ a, PdiffAt (fun v => pd (fun y => φ y a) l v) i x :=
    fun a => PdiffAt_pd_of_contDiffAt (fun y => φ y a) l i x (hφ a)
  have hR : ∀ b, PdiffAt (fun v => pd (fun y => φ y b) j v) i x :=
    fun b => PdiffAt_pd_of_contDiffAt (fun y => φ y b) j i x (hφ b)
  have hsum : pd (fun v => pullbackMet g φ v l j) i x
      = ∑ a, ∑ b, pd (fun v =>
          g (φ v) a b * pd (fun y => φ y a) l v * pd (fun y => φ y b) j v) i x := by
    simp only [pullbackMet]
    rw [pd_sum Finset.univ (fun a v =>
        ∑ b, g (φ v) a b * pd (fun y => φ y a) l v * pd (fun y => φ y b) j v) i x
      (fun a _ => PdiffAt_sum Finset.univ _ i x (fun b _ =>
        ((hP a b).mul (hQ a)).mul (hR b)))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pd_sum Finset.univ (fun b v =>
        g (φ v) a b * pd (fun y => φ y a) l v * pd (fun y => φ y b) j v) i x
      (fun b _ => ((hP a b).mul (hQ a)).mul (hR b))]
  rw [hsum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [pd_mul (fun v => g (φ v) a b * pd (fun y => φ y a) l v) (fun v => pd (fun y => φ y b) j v)
      i x ((hP a b).mul (hQ a)) (hR b),
    pd_mul (fun v => g (φ v) a b) (fun v => pd (fun y => φ y a) l v) i x (hP a b) (hQ a)]
  rw [pd_comp (fun w => g w a b) φ i x (hgd a b) hφd]
  ring

/-! ### N2b local — the pullback-Christoffel numerator combination at finite regularity. -/

/-- **N2b local** — `pullback_christoffel_combo` at per-point regularity. -/
theorem pullback_christoffel_combo_local (g : Point n → Fin n → Fin n → ℝ) (φ : Point n → Point n)
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (l i j : Fin n) (x : Point n)
    (hg : ∀ a b, ContDiffAt ℝ 1 (fun y => g y a b) (φ x))
    (hφ : ∀ a, ContDiffAt ℝ 2 (fun y => φ y a) x) :
    pd (fun v => pullbackMet g φ v l j) i x + pd (fun v => pullbackMet g φ v l i) j x
        - pd (fun v => pullbackMet g φ v i j) l x
      = (∑ a, ∑ b, (∑ c, pd (fun w => g w a b) c (φ x) * pd (fun y => φ y c) i x)
              * pd (fun y => φ y a) l x * pd (fun y => φ y b) j x)
        + (∑ a, ∑ b, (∑ c, pd (fun w => g w a b) c (φ x) * pd (fun y => φ y c) j x)
              * pd (fun y => φ y a) l x * pd (fun y => φ y b) i x)
        - (∑ a, ∑ b, (∑ c, pd (fun w => g w a b) c (φ x) * pd (fun y => φ y c) l x)
              * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x)
        + 2 * (∑ a, ∑ b, g (φ x) a b * pd (fun y => φ y a) l x
              * pd (fun v => pd (fun y => φ y b) j v) i x) := by
  classical
  rw [pullback_metric_deriv_local g φ i l j x hg hφ,
      pullback_metric_deriv_local g φ j l i x hg hφ,
      pullback_metric_deriv_local g φ l i j x hg hφ]
  have c1 : (∑ a, ∑ b, g (φ x) a b * pd (fun v => pd (fun y => φ y a) l v) i x
              * pd (fun y => φ y b) j x)
          = (∑ a, ∑ b, g (φ x) a b * pd (fun v => pd (fun y => φ y a) i v) l x
              * pd (fun y => φ y b) j x) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [pd_comm_of_contDiffAt2' (fun y => φ y a) i l x (hφ a)]
  have c3 : (∑ a, ∑ b, g (φ x) a b * pd (fun y => φ y a) l x
              * pd (fun v => pd (fun y => φ y b) i v) j x)
          = (∑ a, ∑ b, g (φ x) a b * pd (fun y => φ y a) l x
              * pd (fun v => pd (fun y => φ y b) j v) i x) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [pd_comm_of_contDiffAt2' (fun y => φ y b) j i x (hφ b)]
  have c2 : (∑ a, ∑ b, g (φ x) a b * pd (fun v => pd (fun y => φ y a) l v) j x
              * pd (fun y => φ y b) i x)
          = (∑ a, ∑ b, g (φ x) a b * pd (fun y => φ y a) i x
              * pd (fun v => pd (fun y => φ y b) j v) l x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => ?_
    rw [hgsymm (φ x) a p, pd_comm_of_contDiffAt2' (fun y => φ y a) j l x (hφ a)]
    ring
  simp only [Finset.sum_add_distrib]
  rw [c1, c2, c3]
  ring

/-! ### N3 local — the raised contracted Christoffel transformation law at finite regularity. -/

/-- **N3 local** — `pullback_christoffel_transform` at per-point regularity. -/
theorem pullback_christoffel_transform_local (g gi : Point n → Fin n → Fin n → ℝ)
    (φ : Point n → Point n) (gti : Point n → Fin n → Fin n → ℝ)
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (m i j : Fin n) (x : Point n)
    (hφinv : IsUnit (fderiv ℝ φ x))
    (hGGi : ∀ p c, (∑ b, g (φ x) p b * gi (φ x) b c) = if p = c then (1 : ℝ) else 0)
    (hGiG : ∀ p c, (∑ a, gi (φ x) p a * g (φ x) a c) = if p = c then (1 : ℝ) else 0)
    (hgtinv : ∀ p q, (∑ k, gti x p k * pullbackMet g φ x k q) = if p = q then (1 : ℝ) else 0)
    (hg : ∀ a b, ContDiffAt ℝ 1 (fun y => g y a b) (φ x))
    (hφ : ∀ a, ContDiffAt ℝ 2 (fun y => φ y a) x) :
    (∑ k, christoffel (pullbackMet g φ) gti k i j x * pd (fun y => φ y m) k x)
      = (∑ a, ∑ b, christoffel g gi m a b (φ x)
            * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x)
        + pd (fun v => pd (fun y => φ y m) j v) i x := by
  classical
  have hφd : DifferentiableAt ℝ φ x :=
    differentiableAt_pi.mpr (fun a => (hφ a).differentiableAt (by norm_num))
  set J : Fin n → Fin n → ℝ := fun a p => pd (fun y => φ y a) p x with hJset
  set D : Fin n → Fin n → Fin n → ℝ := fun a b c => pd (fun w => g w a b) c (φ x) with hDset
  set K : Fin n → ℝ := fun b => pd (fun v => pd (fun y => φ y b) j v) i x with hKset
  show (∑ k, christoffel (pullbackMet g φ) gti k i j x * J m k)
      = (∑ a, ∑ b, christoffel g gi m a b (φ x) * J a i * J b j) + K m
  have sum3_swap13 (H : Fin n → Fin n → Fin n → ℝ) :
      (∑ a, ∑ b, ∑ c, H a b c) = ∑ a, ∑ b, ∑ c, H c b a := by
    calc (∑ a, ∑ b, ∑ c, H a b c)
        = ∑ a, ∑ c, ∑ b, H a b c := by
          refine Finset.sum_congr rfl ?_; intro a _; exact Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, H a b c := Finset.sum_comm
      _ = ∑ c, ∑ b, ∑ a, H a b c := by
          refine Finset.sum_congr rfl ?_; intro c _; exact Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ c, H c b a := rfl
  have sum3_cycle (H : Fin n → Fin n → Fin n → ℝ) :
      (∑ a, ∑ b, ∑ c, H a b c) = ∑ a, ∑ b, ∑ c, H c a b := by
    calc (∑ a, ∑ b, ∑ c, H a b c)
        = ∑ b, ∑ a, ∑ c, H a b c := Finset.sum_comm
      _ = ∑ b, ∑ c, ∑ a, H a b c := by
          refine Finset.sum_congr rfl ?_; intro b _; exact Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ c, H c a b := rfl
  have sum3_rotateRight (H : Fin n → Fin n → Fin n → ℝ) :
      (∑ a, ∑ b, ∑ c, H a b c) = ∑ a, ∑ b, ∑ c, H b c a := by
    calc (∑ a, ∑ b, ∑ c, H a b c)
        = ∑ a, ∑ c, ∑ b, H a b c := by
          refine Finset.sum_congr rfl ?_; intro a _; exact Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, H a b c := Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ c, H b c a := rfl
  have hJb : ∀ a p, QIQTH.PullbackMetric.jacMat (fderiv ℝ φ x) a p = J a p := by
    intro a p
    have hHF : HasFDerivAt (fun y => φ y a)
        ((ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).comp (fderiv ℝ φ x)) x :=
      (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).hasFDerivAt.comp x hφd.hasFDerivAt
    show QIQTH.PullbackMetric.jacMat (fderiv ℝ φ x) a p = pd (fun y => φ y a) p x
    rw [pd_eq_fderiv (fun y => φ y a) p x hHF.differentiableAt, hHF.fderiv]
    simp [QIQTH.PullbackMetric.jacMat, ContinuousLinearMap.comp_apply]
  have hcontr : ∀ a b, (∑ p, ∑ q, J a p * gti x p q * J b q) = gi (φ x) a b := by
    intro a b
    have hgtdef : ∀ (p q : Fin n), pullbackMet g φ x p q
        = ∑ s, ∑ t, g (φ x) s t * QIQTH.PullbackMetric.jacMat (fderiv ℝ φ x) s p
            * QIQTH.PullbackMetric.jacMat (fderiv ℝ φ x) t q := by
      intro p q
      simp only [pullbackMet]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      rw [hJb s p, hJb t q, hJset]
    have key := pullbackInv_trace_contraction (fderiv ℝ φ x) (g (φ x)) (gi (φ x))
      (pullbackMet g φ x) (gti x) hφinv hGGi hgtdef hgtinv a b
    rw [← key]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hJb a p, hJb b q]
  have hpull : ∀ F : Fin n → ℝ,
      (∑ k, ∑ l, J m k * gti x k l * (∑ p, F p * J p l)) = ∑ p, F p * gi (φ x) m p := by
    intro F
    calc (∑ k, ∑ l, J m k * gti x k l * (∑ p, F p * J p l))
        = ∑ k, ∑ l, ∑ p, J m k * gti x k l * (F p * J p l) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ p, ∑ k, ∑ l, J m k * gti x k l * (F p * J p l) := by
          exact sum3_rotateRight (fun k l p => J m k * gti x k l * (F p * J p l))
      _ = ∑ p, F p * (∑ k, ∑ l, J m k * gti x k l * J p l) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ p, F p * gi (φ x) m p := by
          refine Finset.sum_congr rfl fun p _ => ?_; rw [hcontr m p]
  set FI : Fin n → ℝ := fun a => ∑ b, (∑ c, D a b c * J c i) * J b j with hFIset
  set FII : Fin n → ℝ := fun a => ∑ b, (∑ c, D a b c * J c j) * J b i with hFIIset
  set FIII : Fin n → ℝ := fun c => ∑ a, ∑ b, D a b c * J a i * J b j with hFIIIset
  set FK : Fin n → ℝ := fun a => ∑ b, g (φ x) a b * K b with hFKset
  set GI : Fin n → ℝ := fun l => ∑ a, FI a * J a l with hGIset
  set GII : Fin n → ℝ := fun l => ∑ a, FII a * J a l with hGIIset
  set GIII : Fin n → ℝ := fun l => ∑ c, FIII c * J c l with hGIIIset
  set GK : Fin n → ℝ := fun l => ∑ a, FK a * J a l with hGKset
  have hGI : ∀ l, (∑ a, ∑ b, (∑ c, D a b c * J c i) * J a l * J b j) = GI l := by
    intro l; rw [hGIset]; dsimp only
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hFIset]; dsimp only
    conv_rhs => rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => by ring
  have hGII : ∀ l, (∑ a, ∑ b, (∑ c, D a b c * J c j) * J a l * J b i) = GII l := by
    intro l; rw [hGIIset]; dsimp only
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hFIIset]; dsimp only
    conv_rhs => rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => by ring
  have hGK : ∀ l, (∑ a, ∑ b, g (φ x) a b * J a l * K b) = GK l := by
    intro l; rw [hGKset]; dsimp only
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hFKset]; dsimp only
    conv_rhs => rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => by ring
  have hGIII : ∀ l, (∑ a, ∑ b, (∑ c, D a b c * J c l) * J a i * J b j) = GIII l := by
    intro l; rw [hGIIIset]; dsimp only
    calc (∑ a, ∑ b, (∑ c, D a b c * J c l) * J a i * J b j)
        = ∑ a, ∑ b, ∑ c, D a b c * J c l * J a i * J b j := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]
      _ = ∑ a, ∑ b, ∑ c, D b c a * J a l * J b i * J c j := by
          exact sum3_rotateRight (fun a b c => D a b c * J c l * J a i * J b j)
      _ = ∑ c, (∑ a, ∑ b, D a b c * J a i * J b j) * J c l := by
          symm
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => by ring
  have hC : ∀ l, pd (fun v => pullbackMet g φ v l j) i x
        + pd (fun v => pullbackMet g φ v l i) j x - pd (fun v => pullbackMet g φ v i j) l x
      = (∑ a, ∑ b, (∑ c, D a b c * J c i) * J a l * J b j)
        + (∑ a, ∑ b, (∑ c, D a b c * J c j) * J a l * J b i)
        - (∑ a, ∑ b, (∑ c, D a b c * J c l) * J a i * J b j)
        + 2 * (∑ a, ∑ b, g (φ x) a b * J a l * K b) := by
    intro l
    rw [hDset, hJset, hKset]
    exact pullback_christoffel_combo_local g φ hgsymm l i j x hg hφ
  have hcombo' : ∀ l, pd (fun v => pullbackMet g φ v l j) i x
        + pd (fun v => pullbackMet g φ v l i) j x - pd (fun v => pullbackMet g φ v i j) l x
      = GI l + GII l - GIII l + 2 * GK l := by
    intro l; rw [hC l, hGI l, hGII l, hGIII l, hGK l]
  have hCGI : (∑ k, ∑ l, J m k * gti x k l * GI l) = ∑ a, FI a * gi (φ x) m a := by
    simp only [hGIset]; exact hpull FI
  have hCGII : (∑ k, ∑ l, J m k * gti x k l * GII l) = ∑ a, FII a * gi (φ x) m a := by
    simp only [hGIIset]; exact hpull FII
  have hCGIII : (∑ k, ∑ l, J m k * gti x k l * GIII l) = ∑ c, FIII c * gi (φ x) m c := by
    simp only [hGIIIset]; exact hpull FIII
  have hCGK : (∑ k, ∑ l, J m k * gti x k l * GK l) = ∑ a, FK a * gi (φ x) m a := by
    simp only [hGKset]; exact hpull FK
  set T1 : ℝ := ∑ a, ∑ b, ∑ c, gi (φ x) m c * D c b a * J a i * J b j with hT1set
  set T2 : ℝ := ∑ a, ∑ b, ∑ c, gi (φ x) m c * D c a b * J a i * J b j with hT2set
  set T3 : ℝ := ∑ a, ∑ b, ∑ c, gi (φ x) m c * D a b c * J a i * J b j with hT3set
  have hFI : (∑ a, FI a * gi (φ x) m a) = T1 := by
    rw [hT1set, hFIset]; dsimp only
    calc (∑ a, (∑ b, (∑ c, D a b c * J c i) * J b j) * gi (φ x) m a)
        = ∑ a, ∑ b, ∑ c, gi (φ x) m a * D a b c * J c i * J b j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]; refine Finset.sum_congr rfl fun c _ => by ring
      _ = ∑ a, ∑ b, ∑ c, gi (φ x) m c * D c b a * J a i * J b j :=
          sum3_swap13 (fun a b c => gi (φ x) m a * D a b c * J c i * J b j)
  have hFII : (∑ a, FII a * gi (φ x) m a) = T2 := by
    rw [hT2set, hFIIset]; dsimp only
    calc (∑ a, (∑ b, (∑ c, D a b c * J c j) * J b i) * gi (φ x) m a)
        = ∑ a, ∑ b, ∑ c, gi (φ x) m a * D a b c * J c j * J b i := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]; refine Finset.sum_congr rfl fun c _ => by ring
      _ = ∑ a, ∑ b, ∑ c, gi (φ x) m c * D c a b * J b j * J a i :=
          sum3_cycle (fun a b c => gi (φ x) m a * D a b c * J c j * J b i)
      _ = ∑ a, ∑ b, ∑ c, gi (φ x) m c * D c a b * J a i * J b j := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c _ => by ring
  have hFIII : (∑ c, FIII c * gi (φ x) m c) = T3 := by
    rw [hT3set, hFIIIset]; dsimp only
    calc (∑ c, (∑ a, ∑ b, D a b c * J a i * J b j) * gi (φ x) m c)
        = ∑ c, ∑ a, ∑ b, gi (φ x) m c * D a b c * J a i * J b j := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ a, ∑ b, ∑ c, gi (φ x) m c * D a b c * J a i * J b j :=
          sum3_cycle (fun c a b => gi (φ x) m c * D a b c * J a i * J b j)
  have hFKcontr : (∑ a, FK a * gi (φ x) m a) = K m := by
    calc (∑ a, FK a * gi (φ x) m a)
        = ∑ a, ∑ b, (gi (φ x) m a * g (φ x) a b) * K b := by
          rw [hFKset]; dsimp only
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ b, ∑ a, (gi (φ x) m a * g (φ x) a b) * K b := Finset.sum_comm
      _ = ∑ b, (∑ a, gi (φ x) m a * g (φ x) a b) * K b := by
          refine Finset.sum_congr rfl fun b _ => ?_; rw [Finset.sum_mul]
      _ = ∑ b, (if m = b then (1 : ℝ) else 0) * K b := by
          refine Finset.sum_congr rfl fun b _ => ?_; rw [hGiG m b]
      _ = K m := by simp
  have hΓab : ∀ a b, christoffel g gi m a b (φ x)
      = (1 / 2 : ℝ) * ∑ c, gi (φ x) m c * (D c b a + D c a b - D a b c) := by
    intro a b
    simp only [christoffel]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun c _ => ?_)
    simp only [hDset]
  have hChristoffel : (∑ a, ∑ b, christoffel g gi m a b (φ x) * J a i * J b j)
      = (1 / 2 : ℝ) * (T1 + T2 - T3) := by
    have hL : (∑ a, ∑ b, christoffel g gi m a b (φ x) * J a i * J b j)
        = ∑ a, ∑ b, ∑ c, (1 / 2 : ℝ)
            * (gi (φ x) m c * (D c b a + D c a b - D a b c)) * (J a i * J b j) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hΓab a b, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => by ring
    have hR : (1 / 2 : ℝ) * (T1 + T2 - T3)
        = ∑ a, ∑ b, ∑ c, (1 / 2 : ℝ)
            * (gi (φ x) m c * (D c b a + D c a b - D a b c)) * (J a i * J b j) := by
      rw [hT1set, hT2set, hT3set, mul_sub, mul_add]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => by ring
    rw [hL, hR]
  have hstep : (∑ k, christoffel (pullbackMet g φ) gti k i j x * J m k)
      = (1 / 2 : ℝ) * ∑ k, ∑ l, J m k * gti x k l * (GI l + GII l - GIII l + 2 * GK l) := by
    simp only [christoffel]
    simp_rw [hcombo']
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun l _ => by ring
  have hsplit : (∑ k, ∑ l, J m k * gti x k l * (GI l + GII l - GIII l + 2 * GK l))
      = (∑ k, ∑ l, J m k * gti x k l * GI l) + (∑ k, ∑ l, J m k * gti x k l * GII l)
        - (∑ k, ∑ l, J m k * gti x k l * GIII l)
        + (∑ k, ∑ l, J m k * gti x k l * (2 * GK l)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => by ring
  have hD2 : (∑ k, ∑ l, J m k * gti x k l * (2 * GK l))
      = 2 * ∑ k, ∑ l, J m k * gti x k l * GK l := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => by ring
  rw [hstep, hsplit, hD2, hCGI, hCGII, hCGIII, hCGK, hFI, hFII, hFIII, hFKcontr, hChristoffel]
  ring

/-! ### Second chain rule local — the D²φ source term at finite regularity. -/

/-- **Second-order chain rule local** — `pd_pd_comp` at per-point regularity:
    `f` `ContDiffAt ℝ 2` at `φx`, `φ` per-component `ContDiffAt ℝ 2` at `x`. -/
theorem pd_pd_comp_local (f : Point n → ℝ) (φ : Point n → Point n) (i j : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ∀ a, ContDiffAt ℝ 2 (fun y => φ y a) x) :
    pd (fun y => pd (fun z => f (φ z)) j y) i x
      = (∑ a, (∑ b, pd (fun w => pd f a w) b (φ x) * pd (fun y => φ y b) i x)
              * pd (fun y => φ y a) j x)
        + ∑ a, pd f a (φ x) * pd (fun y => pd (fun z => φ z a) j y) i x := by
  classical
  have hφd : DifferentiableAt ℝ φ x :=
    differentiableAt_pi.mpr (fun a => (hφ a).differentiableAt (by norm_num))
  have hfdev : ∀ᶠ z in nhds (φ x), DifferentiableAt ℝ f z := by
    filter_upwards [hf.eventually (by norm_num)] with z hz using hz.differentiableAt (by norm_num)
  have hfdφ : ∀ᶠ y in nhds x, DifferentiableAt ℝ f (φ y) := hφd.continuousAt.eventually hfdev
  have hφdev : ∀ᶠ y in nhds x, ∀ a, DifferentiableAt ℝ (fun z => φ z a) y := by
    rw [Filter.eventually_all]
    intro a
    filter_upwards [(hφ a).eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have hφwhole : ∀ᶠ y in nhds x, DifferentiableAt ℝ φ y :=
    hφdev.mono (fun y hy => differentiableAt_pi.mpr hy)
  have hfderiv2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y) (φ x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- factor-wise partial-differentiability along `i`.
  have hA : ∀ a, PdiffAt (fun y => pd f a (φ y)) i x := by
    intro a
    have hev : (fun y => pd f a (φ y)) =ᶠ[nhds x] (fun y => fderiv ℝ f (φ y) (Pi.single a 1)) := by
      filter_upwards [hfdφ] with y hy using pd_eq_fderiv f a (φ y) hy
    refine PdiffAt_congr_nhds i x hev ?_
    exact pdiffAt_of_differentiableAt _ i x
      ((hfderiv2.clm_apply (differentiableAt_const _)).comp x hφd)
  have hB : ∀ a, PdiffAt (fun y => pd (fun z => φ z a) j y) i x :=
    fun a => PdiffAt_pd_of_contDiffAt (fun y => φ y a) j i x (hφ a)
  have hAcomp : ∀ a, pd (fun y => pd f a (φ y)) i x
      = ∑ b, pd (fun w => pd f a w) b (φ x) * pd (fun y => φ y b) i x := by
    intro a
    have hpdfa_diff : DifferentiableAt ℝ (fun w => pd f a w) (φ x) := by
      have hev2 : (fun w => pd f a w) =ᶠ[nhds (φ x)] (fun w => fderiv ℝ f w (Pi.single a 1)) := by
        filter_upwards [hfdev] with w hw using pd_eq_fderiv f a w hw
      exact (hfderiv2.clm_apply (differentiableAt_const _)).congr_of_eventuallyEq hev2
    exact pd_comp (fun w => pd f a w) φ i x hpdfa_diff hφd
  have hEach : ∀ a, pd (fun y => pd f a (φ y) * pd (fun z => φ z a) j y) i x
      = (∑ b, pd (fun w => pd f a w) b (φ x) * pd (fun y => φ y b) i x)
          * pd (fun y => φ y a) j x
        + pd f a (φ x) * pd (fun y => pd (fun z => φ z a) j y) i x := by
    intro a
    rw [pd_mul (fun y => pd f a (φ y)) (fun y => pd (fun z => φ z a) j y) i x (hA a) (hB a),
        hAcomp a]
  have hInner : (fun y => pd (fun z => f (φ z)) j y) =ᶠ[nhds x]
      (fun y => ∑ a, pd f a (φ y) * pd (fun z => φ z a) j y) := by
    filter_upwards [hfdφ, hφwhole] with y hfy hφy
    exact pd_comp f φ j y hfy hφy
  rw [pd_congr_nhds i x hInner,
      pd_sum Finset.univ (fun a y => pd f a (φ y) * pd (fun z => φ z a) j y) i x
        (fun a _ => (hA a).mul (hB a)),
      Finset.sum_congr rfl (fun a _ => hEach a), Finset.sum_add_distrib]

/-! ### N4 local — the CAPSTONE (L2): pointwise naturality at finite regularity. -/

/-- **N4 local (CAPSTONE L2) — local Laplace–Beltrami naturality.**
      `Δ_{φ*g}(f ∘ φ)(x) = (Δ_g f)(φ x)`
    with all `ContDiff ⊤` hypotheses of `laplaceBeltrami_pullback_naturality` weakened to the
    per-point / on-germ data actually consumed:
      `g` entrywise `ContDiffAt ℝ 1` at `φx`, `φ` per-component `ContDiffAt ℝ 2` at `x`,
      `f` `ContDiffAt ℝ 2` at `φx`.  All other hypotheses (invertibility, inverse relations) unchanged. -/
theorem laplaceBeltrami_pullback_naturality_local (g gi : Point n → Fin n → Fin n → ℝ)
    (φ : Point n → Point n) (gti : Point n → Fin n → Fin n → ℝ) (f : Point n → ℝ)
    (hgsymm : ∀ y a b, g y a b = g y b a) (x : Point n)
    (hφinv : IsUnit (fderiv ℝ φ x))
    (hGGi : ∀ p c, (∑ b, g (φ x) p b * gi (φ x) b c) = if p = c then (1 : ℝ) else 0)
    (hGiG : ∀ p c, (∑ a, gi (φ x) p a * g (φ x) a c) = if p = c then (1 : ℝ) else 0)
    (hgtinv : ∀ p q, (∑ k, gti x p k * pullbackMet g φ x k q) = if p = q then (1 : ℝ) else 0)
    (hg : ∀ a b, ContDiffAt ℝ 1 (fun y => g y a b) (φ x))
    (hφ : ∀ a, ContDiffAt ℝ 2 (fun y => φ y a) x)
    (hf : ContDiffAt ℝ 2 f (φ x)) :
    laplaceBeltrami (pullbackMet g φ) gti (fun z => f (φ z)) x = laplaceBeltrami g gi f (φ x) := by
  classical
  have hφd : DifferentiableAt ℝ φ x :=
    differentiableAt_pi.mpr (fun a => (hφ a).differentiableAt (by norm_num))
  have hJb : ∀ a p, QIQTH.PullbackMetric.jacMat (fderiv ℝ φ x) a p = pd (fun y => φ y a) p x := by
    intro a p
    have hHF : HasFDerivAt (fun y => φ y a)
        ((ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).comp (fderiv ℝ φ x)) x :=
      (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).hasFDerivAt.comp x hφd.hasFDerivAt
    rw [pd_eq_fderiv (fun y => φ y a) p x hHF.differentiableAt, hHF.fderiv]
    simp [QIQTH.PullbackMetric.jacMat, ContinuousLinearMap.comp_apply]
  have hcontr : ∀ a b, (∑ p, ∑ q, pd (fun y => φ y a) p x * gti x p q * pd (fun y => φ y b) q x)
      = gi (φ x) a b := by
    intro a b
    have hgtdef : ∀ (p q : Fin n), pullbackMet g φ x p q
        = ∑ s, ∑ t, g (φ x) s t * QIQTH.PullbackMetric.jacMat (fderiv ℝ φ x) s p
            * QIQTH.PullbackMetric.jacMat (fderiv ℝ φ x) t q := by
      intro p q
      simp only [pullbackMet]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      rw [hJb s p, hJb t q]
    have key := pullbackInv_trace_contraction (fderiv ℝ φ x) (g (φ x)) (gi (φ x))
      (pullbackMet g φ x) (gti x) hφinv hGGi hgtdef hgtinv a b
    rw [← key]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hJb a p, hJb b q]
  have sum4_pull : ∀ F : Fin n → Fin n → Fin n → Fin n → ℝ,
      (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
    intro F
    calc (∑ i, ∑ j, ∑ a, ∑ b, F i j a b)
        = ∑ i, ∑ a, ∑ b, ∑ j, F i j a b := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hcontract' : ∀ (C : Fin n → Fin n → ℝ),
      (∑ i, ∑ j, gti x i j * (∑ a, ∑ b, C a b * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x))
        = ∑ a, ∑ b, C a b * gi (φ x) a b := by
    intro C
    have e1 : (∑ i, ∑ j, gti x i j
          * (∑ a, ∑ b, C a b * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x))
        = ∑ i, ∑ j, ∑ a, ∑ b,
            C a b * (pd (fun y => φ y a) i x * gti x i j * pd (fun y => φ y b) j x) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
    rw [e1, sum4_pull (fun i j a b =>
      C a b * (pd (fun y => φ y a) i x * gti x i j * pd (fun y => φ y b) j x))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← hcontr a b, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hcontractHess : ∀ (C : Fin n → Fin n → ℝ),
      (∑ i, ∑ j, gti x i j
          * (∑ a, (∑ b, C a b * pd (fun y => φ y b) i x) * pd (fun y => φ y a) j x))
        = ∑ a, ∑ b, C a b * gi (φ x) b a := by
    intro C
    have e1 : (∑ i, ∑ j, gti x i j
          * (∑ a, (∑ b, C a b * pd (fun y => φ y b) i x) * pd (fun y => φ y a) j x))
        = ∑ i, ∑ j, ∑ a, ∑ b,
            C a b * (pd (fun y => φ y b) i x * gti x i j * pd (fun y => φ y a) j x) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
    rw [e1, sum4_pull (fun i j a b =>
      C a b * (pd (fun y => φ y b) i x * gti x i j * pd (fun y => φ y a) j x))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← hcontr b a, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hΓcontract : ∀ i j, (∑ k, christoffel (pullbackMet g φ) gti k i j x * pd (fun z => f (φ z)) k x)
      = (∑ a, ∑ b, (∑ m, pd f m (φ x) * christoffel g gi m a b (φ x))
            * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x)
        + ∑ a, pd f a (φ x) * pd (fun y => pd (fun z => φ z a) j y) i x := by
    intro i j
    have hk : ∀ k, pd (fun z => f (φ z)) k x = ∑ m, pd f m (φ x) * pd (fun y => φ y m) k x :=
      fun k => pd_comp f φ k x (hf.differentiableAt (by norm_num)) hφd
    simp_rw [hk]
    rw [show (∑ k, christoffel (pullbackMet g φ) gti k i j x
              * ∑ m, pd f m (φ x) * pd (fun y => φ y m) k x)
          = ∑ m, pd f m (φ x)
              * ∑ k, christoffel (pullbackMet g φ) gti k i j x * pd (fun y => φ y m) k x from by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        refine Finset.sum_congr rfl fun k _ => by ring]
    rw [show (∑ m, pd f m (φ x)
              * ∑ k, christoffel (pullbackMet g φ) gti k i j x * pd (fun y => φ y m) k x)
          = ∑ m, pd f m (φ x)
              * ((∑ a, ∑ b, christoffel g gi m a b (φ x)
                    * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x)
                + pd (fun v => pd (fun y => φ y m) j v) i x) from by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [pullback_christoffel_transform_local g gi φ gti hgsymm m i j x hφinv hGGi hGiG hgtinv
          hg hφ]]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [show (∑ m, pd f m (φ x) * ∑ a, ∑ b, christoffel g gi m a b (φ x)
                * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x)
            = ∑ m, ∑ a, ∑ b, pd f m (φ x) * christoffel g gi m a b (φ x)
                * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x from by
          refine Finset.sum_congr rfl fun m _ => ?_; rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_; rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => by ring]
      rw [show (∑ m, ∑ a, ∑ b, pd f m (φ x) * christoffel g gi m a b (φ x)
                * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x)
            = ∑ a, ∑ b, ∑ m, pd f m (φ x) * christoffel g gi m a b (φ x)
                * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x from by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _ => Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
  have hbracket : ∀ i j, (pd (fun y => pd (fun z => f (φ z)) j y) i x
        - ∑ k, christoffel (pullbackMet g φ) gti k i j x * pd (fun z => f (φ z)) k x)
      = (∑ a, (∑ b, pd (fun w => pd f a w) b (φ x) * pd (fun y => φ y b) i x)
            * pd (fun y => φ y a) j x)
        - ∑ a, ∑ b, (∑ m, pd f m (φ x) * christoffel g gi m a b (φ x))
            * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x := by
    intro i j
    rw [pd_pd_comp_local f φ i j x hf hφ, hΓcontract i j]; ring
  simp only [laplaceBeltrami]
  simp_rw [hbracket]
  rw [show (∑ i, ∑ j, gti x i j
          * ((∑ a, (∑ b, pd (fun w => pd f a w) b (φ x) * pd (fun y => φ y b) i x)
                * pd (fun y => φ y a) j x)
            - ∑ a, ∑ b, (∑ m, pd f m (φ x) * christoffel g gi m a b (φ x))
                * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x))
        = (∑ i, ∑ j, gti x i j
            * (∑ a, (∑ b, pd (fun w => pd f a w) b (φ x) * pd (fun y => φ y b) i x)
                * pd (fun y => φ y a) j x))
          - (∑ i, ∑ j, gti x i j
            * (∑ a, ∑ b, (∑ m, pd f m (φ x) * christoffel g gi m a b (φ x))
                * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x)) from by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j _ => by rw [mul_sub]]
  rw [hcontractHess (fun a b => pd (fun w => pd f a w) b (φ x)),
      hcontract' (fun a b => ∑ m, pd f m (φ x) * christoffel g gi m a b (φ x))]
  have hA : (∑ a, ∑ b, pd (fun w => pd f a w) b (φ x) * gi (φ x) b a)
      = ∑ a, ∑ b, gi (φ x) a b * pd (fun y => pd f b y) a (φ x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hB : (∑ a, ∑ b, (∑ m, pd f m (φ x) * christoffel g gi m a b (φ x)) * gi (φ x) a b)
      = ∑ a, ∑ b, gi (φ x) a b * ∑ c, christoffel g gi c a b (φ x) * pd f c (φ x) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [hA, hB, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_sub]

/-! ### L3 — instantiation infrastructure at `φ = uniformFlowExp`. -/

/-- **L3a — `uniformFlowExp` is `ContDiffAt ℝ 2` on the regularity ball** (whole map).  Assembled from
    the three proven Fréchet layers, EACH valid at every ball point:
      * `uniformFlowExp_hasFDerivAt` (`Dφ` exists on the ball),
      * `uniformFlowExp_fderiv_hasFDerivAt` (`D²φ` exists on the ball),
      * `uniformFlowExp_hessianMap_differentiableAt` (`D³φ` exists on the ball ⟹ `D²φ` continuous on
        the ball),
    fed twice through `contDiffAt_succ_iff_hasFDerivAt` (`f' = Dφ`, `f'' = D²φ`) with the last step
    `contDiffAt_zero` discharged by `ContinuousOn` of `D²φ` on the ball.  This is the fact that was
    firewalled in J4-90 (`uniformFlowExp` only `C²`-on-ball, not global `ContDiff ⊤`). -/
theorem contDiffAt2_uniformFlowExp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) :
    ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK q) v := by
  have hballnhds : Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) ∈ nhds v :=
    Metric.isOpen_ball.mem_nhds (by rwa [mem_ball_zero_iff])
  have hL1 : ∀ w ∈ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK),
      HasFDerivAt (uniformFlowExp g gi hC hK q) (fderiv ℝ (uniformFlowExp g gi hC hK q) w) w := by
    intro w hw; rw [mem_ball_zero_iff] at hw
    obtain ⟨L, hL⟩ := uniformFlowExp_hasFDerivAt g gi hC hK q hq w hw
    rw [hL.fderiv]; exact hL
  have hL2 : ∀ w ∈ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK),
      HasFDerivAt (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u)
        (fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) w := by
    intro w hw; rw [mem_ball_zero_iff] at hw
    obtain ⟨B₂, hB₂⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq w hw
    rw [hB₂.fderiv]; exact hB₂
  have hL3 : ∀ w ∈ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK),
      DifferentiableAt ℝ
        (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w := by
    intro w hw; rw [mem_ball_zero_iff] at hw
    exact uniformFlowExp_hessianMap_differentiableAt g gi hC hK q hq w hw
  refine contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (uniformFlowExp g gi hC hK q), ⟨_, hballnhds, hL1⟩, ?_⟩
  refine contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u), ⟨_, hballnhds, hL2⟩, ?_⟩
  exact contDiffAt_zero.mpr
    ⟨_, hballnhds, fun w hw => ((hL3 w hw).continuousAt).continuousWithinAt⟩

/-- **L3a′ — per-component `ContDiffAt ℝ 2`** — the exact `hφ` shape the local tower consumes,
    from L3a by post-composing with the smooth coordinate projection. -/
theorem contDiffAt2_uniformFlowExp_comp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a : Fin n) :
    ContDiffAt ℝ 2 (fun y => uniformFlowExp g gi hC hK q y a) v :=
  (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).contDiff.comp_contDiffAt v
    (contDiffAt2_uniformFlowExp g gi hC hK q hq v hv)

/-- **L3b — `pullbackMet` at `uniformFlowExp` equals `uniformFlowPullbackMetric`** on the ball.
    Bridges the abstract congruence pullback (using `pd (φ·a)`) to the recentred metric (using
    `fderiv φ (Pi.single i 1)`), via `pd_eq_fderiv` on the differentiable `uniformFlowExp`. -/
theorem pullbackMet_eq_uniformFlowPullbackMetric (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (w : Point n)
    (hw : ‖w‖ < uniformFlowRadius g gi hC hK) (i j : Fin n) :
    pullbackMet g (uniformFlowExp g gi hC hK q) w i j
      = QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q w i j := by
  have hφd : DifferentiableAt ℝ (uniformFlowExp g gi hC hK q) w := by
    obtain ⟨L, hL⟩ := uniformFlowExp_hasFDerivAt g gi hC hK q hq w hw
    exact hL.differentiableAt
  have pdeq : ∀ (a p : Fin n), pd (fun y => uniformFlowExp g gi hC hK q y a) p w
      = (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single p 1) a := by
    intro a p
    have hHF : HasFDerivAt (fun y => uniformFlowExp g gi hC hK q y a)
        ((ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).comp
          (fderiv ℝ (uniformFlowExp g gi hC hK q) w)) w :=
      (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).hasFDerivAt.comp w hφd.hasFDerivAt
    rw [pd_eq_fderiv (fun y => uniformFlowExp g gi hC hK q y a) p w hHF.differentiableAt, hHF.fderiv]
    simp [ContinuousLinearMap.comp_apply]
  simp only [pullbackMet, QIQTH.PullbackMetric.uniformFlowPullbackMetric]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [pdeq a i, pdeq b j]

/-- **L3c — Laplace–Beltrami depends on the metric only through its germ at the point.**  If two
    metrics agree entrywise on a neighbourhood of `v`, their Laplace–Beltrami operators (with the SAME
    inverse `gti`) agree at `v`.  The metric enters only through `christoffel _ gti`, whose numerator is
    a partial derivative of the metric, invariant under germ equality (`pd_congr_nhds`). -/
theorem laplaceBeltrami_congr_metric_nhds (g1 g2 gti : Point n → Fin n → Fin n → ℝ)
    (h : Point n → ℝ) (v : Point n)
    (hne : ∀ a b, (fun y => g1 y a b) =ᶠ[nhds v] (fun y => g2 y a b)) :
    laplaceBeltrami g1 gti h v = laplaceBeltrami g2 gti h v := by
  have hch : ∀ k i j, christoffel g1 gti k i j v = christoffel g2 gti k i j v := by
    intro k i j
    simp only [christoffel]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun α _ => ?_)
    rw [pd_congr_nhds i v (hne α j), pd_congr_nhds j v (hne α i), pd_congr_nhds α v (hne i j)]
  simp only [laplaceBeltrami]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  exact Finset.sum_congr rfl fun k _ => by rw [hch k i j]

/-! ### L4 — the CAPSTONE: local naturality at `φ = uniformFlowExp`. -/

/-- **L4 (CAPSTONE) — Laplace–Beltrami naturality for the recentring flow `uniformFlowExp`.**
      `Δ_{g̃_q}(f ∘ φ_q)(v) = (Δ_g f)(φ_q v)`,  `φ_q = uniformFlowExp g gi hC hK q`,
      `g̃_q = uniformFlowPullbackMetric g gi hC hK q`,  its inverse `uniformFlowPullbackMetricInv`,
    on a SINGLE uniform ball `‖v‖ < r₀` (`q ∈ K`), with the genuine per-point geometric inputs at the
    far point `φ_q v`: `g` `C¹`, `f` `C²`, `g` nondegenerate (`matToCLM` a unit) and `gi` a two-sided
    inverse of `g`.  φ-regularity, Jacobian invertibility, the pullback-metric identification, and the
    `g̃⁻¹·g̃ = 1` inverse relation are all DISCHARGED (L3a′ / `uniformFlowExp_common_nondeg_radius` /
    L3b / `uniformFlowPullbackMetricInv_mul_metric`).  This breaks the J4-90 firewall. -/
theorem laplaceBeltrami_uniformFlow_naturality (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a b, g y a b = g y b a) (f : Point n → ℝ) :
    ∃ r₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
      (∀ a b, ContDiffAt ℝ 1 (fun y => g y a b) (uniformFlowExp g gi hC hK q v)) →
      ContDiffAt ℝ 2 f (uniformFlowExp g gi hC hK q v) →
      IsUnit (QIQTH.PullbackMetric.matToCLM
        (fun a b => g (uniformFlowExp g gi hC hK q v) a b)) →
      (∀ p c, (∑ b, g (uniformFlowExp g gi hC hK q v) p b
          * gi (uniformFlowExp g gi hC hK q v) b c) = if p = c then (1 : ℝ) else 0) →
      (∀ p c, (∑ a, gi (uniformFlowExp g gi hC hK q v) p a
          * g (uniformFlowExp g gi hC hK q v) a c) = if p = c then (1 : ℝ) else 0) →
      laplaceBeltrami (QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q)
          (fun z => f (uniformFlowExp g gi hC hK q z)) v
        = laplaceBeltrami g gi f (uniformFlowExp g gi hC hK q v) := by
  obtain ⟨ρ₀, hρ₀pos, hnondeg⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  refine ⟨min ρ₀ (uniformFlowRadius g gi hC hK),
    lt_min hρ₀pos (uniformFlowRadius_pos g gi hC hK), ?_⟩
  intro q hq v hv hg1 hf hgU hGGi hGiG
  have hvρ₀ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (min_le_left _ _)
  have hvR : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv (min_le_right _ _)
  -- φ-regularity, Jacobian invertibility.
  have hφreg : ∀ a, ContDiffAt ℝ 2 (fun y => uniformFlowExp g gi hC hK q y a) v :=
    fun a => contDiffAt2_uniformFlowExp_comp g gi hC hK q hq v hvR a
  have hφinv : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v) := hnondeg q hq v hvρ₀
  -- pullback-metric nondegeneracy (feeds the inverse identity).
  have hU : IsUnit (QIQTH.PullbackMetric.matToCLM
      (fun a b => QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q v a b)) :=
    QIQTH.PullbackMetric.uniformFlowPullbackMetric_isUnit_of_fderiv_isUnit g gi hC hK q v hφinv hgU
  -- pointwise pullback identification at `v`.
  have hbridge : ∀ i j, pullbackMet g (uniformFlowExp g gi hC hK q) v i j
      = QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q v i j :=
    fun i j => pullbackMet_eq_uniformFlowPullbackMetric g gi hC hK q hq v hvR i j
  -- `g̃⁻¹ · g̃ = 1` against `pullbackMet` (the local tower's `hgtinv` shape).
  have hgtinv : ∀ p qq, (∑ k, uniformFlowPullbackMetricInv g gi hC hK q v p k
        * pullbackMet g (uniformFlowExp g gi hC hK q) v k qq) = if p = qq then (1 : ℝ) else 0 := by
    intro p qq
    rw [← uniformFlowPullbackMetricInv_mul_metric g gi hC hK q v hU p qq]
    exact Finset.sum_congr rfl fun k _ => by rw [hbridge k qq]
  -- the local capstone L2 at `φ = uniformFlowExp`, `gti = uniformFlowPullbackMetricInv`.
  have hL2 := laplaceBeltrami_pullback_naturality_local g gi (uniformFlowExp g gi hC hK q)
    (uniformFlowPullbackMetricInv g gi hC hK q) f hgsymm v hφinv hGGi hGiG
    hgtinv hg1 hφreg hf
  -- swap the metric function `pullbackMet g φ → uniformFlowPullbackMetric` (germ-equal on the ball).
  have hne : ∀ a b,
      (fun y => QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q y a b) =ᶠ[nhds v]
        (fun y => pullbackMet g (uniformFlowExp g gi hC hK q) y a b) := by
    intro a b
    have hball : Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) ∈ nhds v :=
      Metric.isOpen_ball.mem_nhds (by rwa [mem_ball_zero_iff])
    filter_upwards [hball] with w hw
    rw [mem_ball_zero_iff] at hw
    exact (pullbackMet_eq_uniformFlowPullbackMetric g gi hC hK q hq w hw a b).symm
  rw [laplaceBeltrami_congr_metric_nhds
      (QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q)
      (pullbackMet g (uniformFlowExp g gi hC hK q))
      (uniformFlowPullbackMetricInv g gi hC hK q)
      (fun z => f (uniformFlowExp g gi hC hK q z)) v hne]
  exact hL2

end QIQTH.HeatResidualBound
