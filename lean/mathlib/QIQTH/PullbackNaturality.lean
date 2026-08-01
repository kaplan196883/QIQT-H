/-
  PullbackNaturality — J4-90: the GENERAL-DIFFEOMORPHISM Laplace–Beltrami naturality
  `Δ_{φ*g}(f ∘ φ)(v) = (Δ_g f)(φ v)`, the capstone of the E-identification (`Vmap`) gap census
  opened in `ResidualChartTransport.lean` (J4-89).

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## The insight that makes this tractable (and it HELD).

  J4-89 firewalled the *contracted Christoffel transformation law* as `uniformFlowExp`-specific,
  "infrastructure-scale".  It is not.  Laplace–Beltrami naturality is a GENERAL fact for ANY `C²`
  map `φ` whose Jacobian is invertible, with the pullback metric DEFINED as the congruence
  `g̃ = Jᵀ (g∘φ) J` (`pullbackMet` below) — proved by pure coordinate computation, using NO
  geodesic / ODE / exp-specific input.  The only geometric facts consumed are:
    * `pd_comp` / `pd_pd_comp` (J4-89): the first/second chain rules for the coordinate partial;
    * `pullbackInv_trace_contraction` (J4-89): `J g̃⁻¹ Jᵀ = g⁻¹` in contracted form (no `Dφ⁻¹`);
    * `pd_comm` (Schwarz): the second-jet symmetry `∂ᵢ∂ⱼφ = ∂ⱼ∂ᵢφ`.

  The crux is the RAISED transformation law (`pullback_christoffel_transform`, N3)
      `∑_k Γ̃^k_{ij}(x) ∂_m(φ)_k = ∑_{ab} Γ^m_{ab}(φx) (∂_iφ^a)(∂_jφ^b) + ∂_i∂_jφ^m`,
  which is `Γ̃` contracted against `J` (so `J⁻¹` never appears).  Feeding it plus the trace
  contraction into `pd_pd_comp` collapses `Δ_{g̃}(f∘φ)` to `(Δ_g f)∘φ`.

  ## Landed here (green; NO `sorry`, NO new axioms, NO `expRho` in statements, NO vacuous hyps).

    * `pullbackMet` — the coordinate pullback (congruence) metric `g̃_{ij} = ∑ g_{ab}(φ·)∂_iφ^a ∂_jφ^b`;
    * `pullback_metric_deriv` (N2) — the product-rule expansion of `∂_i g̃_{lj}` (the D²φ source terms
      explicit);
    * `pullback_christoffel_combo` (N2b) — the Christoffel numerator combination, after the
      D²φ/symmetry cancellations;
    * `pullback_christoffel_transform` (N3) — the raised contracted transformation law (crux);
    * `laplaceBeltrami_pullback_naturality` (N4, CAPSTONE) — `Δ_{g̃}(f∘φ)(x) = (Δ_g f)(φ x)`.

  FIREWALLED: the instantiation at `φ = uniformFlowExp` (N5).  `uniformFlowExp` is only `C²` on a
  uniform ball (via `Classical.choose` of a geodesic ODE), NOT globally `ContDiff ⊤`; the abstract
  capstone consumes global `ContDiff ⊤ φ`, so plugging in `uniformFlowExp` needs a local-`ContDiffAt`
  re-run of the whole `pd` tower — a separate build.  The abstract N4 is the heart; the geometric
  content of the `Vmap` gap is exactly N3+N4.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.LaplaceBeltrami
import QIQTH.ResidualChartTransport
import QIQTH.PullbackNondegFromFDeriv
import QIQTH.ChristoffelSmooth

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.PullbackMetric

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- **The coordinate pullback (congruence) metric** of a map `φ : Point n → Point n` w.r.t. an ambient
    metric `g`: `g̃_{ij}(v) = ∑_{a,b} g_{ab}(φ v) · ∂_i(φ·a)(v) · ∂_j(φ·b)(v)`, i.e. `Jᵀ (g∘φ) J`.
    This is the general-`φ` version of `uniformFlowPullbackMetric` (which uses `fderiv … (Pi.single i 1)`
    in place of `pd (φ·a) i`; the two agree by `pd_eq_fderiv`). -/
noncomputable def pullbackMet (g : Point n → Fin n → Fin n → ℝ) (φ : Point n → Point n)
    (v : Point n) (i j : Fin n) : ℝ :=
  ∑ a, ∑ b, g (φ v) a b * pd (fun y => φ y a) i v * pd (fun y => φ y b) j v

/-! ### Smoothness helpers for the components of `φ` and `g∘φ`. -/

/-- Each component `φ·a` inherits `C^∞` from `φ`. -/
theorem contDiff_phi_comp (φ : Point n → Point n) (hφ : ContDiff ℝ (⊤ : WithTop ℕ∞) φ) (a : Fin n) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => φ y a) :=
  (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).contDiff.comp hφ

/-- The pulled-back metric component `g_{ab}∘φ` is `C^∞`. -/
theorem contDiff_g_comp (g : Point n → Fin n → Fin n → ℝ) (φ : Point n → Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hφ : ContDiff ℝ (⊤ : WithTop ℕ∞) φ) (a b : Fin n) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g (φ y) a b) :=
  (hg a b).comp hφ

/-! ### N2 — the product-rule expansion of `∂_i g̃_{lj}` (the D²φ source term explicit). -/

/-- **N2 — the pullback-metric derivative.**  For `C^∞` `g` (per entry) and `φ`,
      `∂_i g̃_{lj}(x) = ∑_{a,b} [ (∑_c (∂_c g_{ab})(φx)·∂_i(φ·c)) · ∂_l(φ·a)·∂_j(φ·b)
                                + g_{ab}(φx)·∂_i∂_l(φ·a)·∂_j(φ·b)
                                + g_{ab}(φx)·∂_l(φ·a)·∂_i∂_j(φ·b) ]`,
    the Leibniz expansion of the triple product `g_{ab}(φ·)·∂_l(φ·a)·∂_j(φ·b)` with the chain rule
    `pd_comp` on the `g∘φ` factor.  The last two blocks are the `D²φ` source terms. -/
theorem pullback_metric_deriv (g : Point n → Fin n → Fin n → ℝ) (φ : Point n → Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hφ : ContDiff ℝ (⊤ : WithTop ℕ∞) φ) (i l j : Fin n) (x : Point n) :
    pd (fun v => pullbackMet g φ v l j) i x
      = ∑ a, ∑ b,
          ((∑ c, pd (fun w => g w a b) c (φ x) * pd (fun y => φ y c) i x)
              * pd (fun y => φ y a) l x * pd (fun y => φ y b) j x
            + g (φ x) a b * pd (fun v => pd (fun y => φ y a) l v) i x * pd (fun y => φ y b) j x
            + g (φ x) a b * pd (fun y => φ y a) l x
                * pd (fun v => pd (fun y => φ y b) j v) i x) := by
  classical
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφa : ∀ a, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => φ y a) := contDiff_phi_comp φ hφ
  have hgφ : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g (φ y) a b) := contDiff_g_comp g φ hg hφ
  -- differentiability of the three factors along `i`.
  have hP : ∀ a b, PdiffAt (fun v => g (φ v) a b) i x :=
    fun a b => PdiffAt_of_contDiff _ (hgφ a b) i x
  have hQ : ∀ a, PdiffAt (fun v => pd (fun y => φ y a) l v) i x :=
    fun a => PdiffAt_pd (fun y => φ y a) (hφa a) l i x
  have hR : ∀ b, PdiffAt (fun v => pd (fun y => φ y b) j v) i x :=
    fun b => PdiffAt_pd (fun y => φ y b) (hφa b) j i x
  have hPd : ∀ a, PdiffAt (fun y => φ y a) l x :=
    fun a => PdiffAt_of_contDiff _ (hφa a) l x
  have hRd : ∀ b, PdiffAt (fun y => φ y b) j x :=
    fun b => PdiffAt_of_contDiff _ (hφa b) j x
  -- `pd` of the double sum = double sum of `pd`.
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
  -- Leibniz on `(P*Q)*R`.
  rw [pd_mul (fun v => g (φ v) a b * pd (fun y => φ y a) l v) (fun v => pd (fun y => φ y b) j v)
      i x ((hP a b).mul (hQ a)) (hR b),
    pd_mul (fun v => g (φ v) a b) (fun v => pd (fun y => φ y a) l v) i x (hP a b) (hQ a)]
  -- chain rule on `pd_i (g_{ab}∘φ)`.
  rw [pd_comp (fun w => g w a b) φ i x
      ((hg a b).differentiable (by simp) (φ x)) (hφd x)]
  ring

/-! ### N2b — the Christoffel numerator combination (D²φ / symmetry cancellations). -/

/-- **N2b — the pullback-Christoffel numerator combination.**  Assembling the three
    `pullback_metric_deriv` expansions for `∂_i g̃_{lj} + ∂_j g̃_{li} − ∂_l g̃_{ij}` and cancelling the
    cross `D²φ` blocks (via Schwarz `pd_comm` and metric symmetry `hgsymm`) leaves the three
    `∂g`-transport groups plus a single doubled `D²φ` source term:
      `= (∑ (∂_c g_{ab})∂_iφ^c ∂_lφ^a ∂_jφ^b) + (∑ (∂_c g_{ab})∂_jφ^c ∂_lφ^a ∂_iφ^b)
         − (∑ (∂_c g_{ab})∂_lφ^c ∂_iφ^a ∂_jφ^b) + 2·(∑ g_{ab}∂_lφ^a ∂_i∂_jφ^b)`. -/
theorem pullback_christoffel_combo (g : Point n → Fin n → Fin n → ℝ) (φ : Point n → Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hφ : ContDiff ℝ (⊤ : WithTop ℕ∞) φ) (hgsymm : ∀ y a b, g y a b = g y b a)
    (l i j : Fin n) (x : Point n) :
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
  have hφa : ∀ a, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => φ y a) := contDiff_phi_comp φ hφ
  rw [pullback_metric_deriv g φ hg hφ i l j x,
      pullback_metric_deriv g φ hg hφ j l i x,
      pullback_metric_deriv g φ hg hφ l i j x]
  -- cancellation c1 : A_KA = C_KA  (Schwarz on `∂²φ^a`).
  have c1 : (∑ a, ∑ b, g (φ x) a b * pd (fun v => pd (fun y => φ y a) l v) i x
              * pd (fun y => φ y b) j x)
          = (∑ a, ∑ b, g (φ x) a b * pd (fun v => pd (fun y => φ y a) i v) l x
              * pd (fun y => φ y b) j x) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [pd_comm (fun y => φ y a) i l x (hφa a)]
  -- cancellation c3 : B_KB = A_KB  (Schwarz on `∂²φ^b`).
  have c3 : (∑ a, ∑ b, g (φ x) a b * pd (fun y => φ y a) l x
              * pd (fun v => pd (fun y => φ y b) i v) j x)
          = (∑ a, ∑ b, g (φ x) a b * pd (fun y => φ y a) l x
              * pd (fun v => pd (fun y => φ y b) j v) i x) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [pd_comm (fun y => φ y b) j i x (hφa b)]
  -- cancellation c2 : B_KA = C_KB  (a↔b swap + metric symmetry + Schwarz).
  have c2 : (∑ a, ∑ b, g (φ x) a b * pd (fun v => pd (fun y => φ y a) l v) j x
              * pd (fun y => φ y b) i x)
          = (∑ a, ∑ b, g (φ x) a b * pd (fun y => φ y a) i x
              * pd (fun v => pd (fun y => φ y b) j v) l x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => ?_
    rw [hgsymm (φ x) a p, pd_comm (fun y => φ y a) j l x (hφa a)]
    ring
  -- split each double-sum-of-three-terms, then cancel and regroup.
  simp only [Finset.sum_add_distrib]
  rw [c1, c2, c3]
  ring

/-! ### N3 — the raised contracted Christoffel transformation law (crux). -/

/-- **N3 — the raised contracted Christoffel transformation law.**  Contracting the pullback-metric
    Christoffel symbol `Γ̃^k_{ij}` against the Jacobian `∂_m(φ)_k` (so `Dφ⁻¹` never appears) gives the
    classical inhomogeneous transformation
      `∑_k Γ̃^k_{ij}(x) ∂_m(φ)_k = ∑_{a,b} Γ^m_{ab}(φx)·∂_iφ^a·∂_jφ^b + ∂_i∂_jφ^m`.
    Proof: unfold `Γ̃` via `christoffel`, replace the metric-derivative numerator by
    `pullback_christoffel_combo`, and contract each transport group through
    `pullbackInv_trace_contraction` (the `hcontr`/`hpull` step), matching the three `∂g`-transport
    groups to the three terms of `Γ` (pure triple-sum reindexing) and collapsing the `D²φ` block with
    the metric inverse (`hGiG`).  `gti` is a genuine inverse of `g̃ = pullbackMet g φ` at `x`; `gi` a
    genuine inverse of `g` at `φx`; `J = fderiv φ x` invertible. -/
theorem pullback_christoffel_transform (g gi : Point n → Fin n → Fin n → ℝ) (φ : Point n → Point n)
    (gti : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hφ : ContDiff ℝ (⊤ : WithTop ℕ∞) φ) (hgsymm : ∀ y a b, g y a b = g y b a)
    (m i j : Fin n) (x : Point n)
    (hφinv : IsUnit (fderiv ℝ φ x))
    (hGGi : ∀ p c, (∑ b, g (φ x) p b * gi (φ x) b c) = if p = c then (1 : ℝ) else 0)
    (hGiG : ∀ p c, (∑ a, gi (φ x) p a * g (φ x) a c) = if p = c then (1 : ℝ) else 0)
    (hgtinv : ∀ p q, (∑ k, gti x p k * pullbackMet g φ x k q) = if p = q then (1 : ℝ) else 0) :
    (∑ k, christoffel (pullbackMet g φ) gti k i j x * pd (fun y => φ y m) k x)
      = (∑ a, ∑ b, christoffel g gi m a b (φ x)
            * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x)
        + pd (fun v => pd (fun y => φ y m) j v) i x := by
  classical
  -- abbreviations (definitional: transparent lets).
  set J : Fin n → Fin n → ℝ := fun a p => pd (fun y => φ y a) p x with hJset
  set D : Fin n → Fin n → Fin n → ℝ := fun a b c => pd (fun w => g w a b) c (φ x) with hDset
  set K : Fin n → ℝ := fun b => pd (fun v => pd (fun y => φ y b) j v) i x with hKset
  show (∑ k, christoffel (pullbackMet g φ) gti k i j x * J m k)
      = (∑ a, ∑ b, christoffel g gi m a b (φ x) * J a i * J b j) + K m
  -- generic triple-sum permutations (alpha-`rfl` on the last step).
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
  -- the contraction (from `pullbackInv_trace_contraction`).
  have hJb : ∀ a p, jacMat (fderiv ℝ φ x) a p = J a p := by
    intro a p
    have hHF : HasFDerivAt (fun y => φ y a)
        ((ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).comp (fderiv ℝ φ x)) x :=
      (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).hasFDerivAt.comp x
        (hφ.differentiable (by simp) x).hasFDerivAt
    show jacMat (fderiv ℝ φ x) a p = pd (fun y => φ y a) p x
    rw [pd_eq_fderiv (fun y => φ y a) p x hHF.differentiableAt, hHF.fderiv]
    simp [jacMat, ContinuousLinearMap.comp_apply]
  have hcontr : ∀ a b, (∑ p, ∑ q, J a p * gti x p q * J b q) = gi (φ x) a b := by
    intro a b
    have hgtdef : ∀ (p q : Fin n), pullbackMet g φ x p q
        = ∑ s, ∑ t, g (φ x) s t * jacMat (fderiv ℝ φ x) s p * jacMat (fderiv ℝ φ x) t q := by
      intro p q
      simp only [pullbackMet]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      rw [hJb s p, hJb t q, hJset]
    have key := pullbackInv_trace_contraction (fderiv ℝ φ x) (g (φ x)) (gi (φ x))
      (pullbackMet g φ x) (gti x) hφinv hGGi hgtdef hgtinv a b
    rw [← key]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hJb a p, hJb b q]
  -- the key pull-through contraction for a group.
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
  -- the four group coefficient families.
  set FI : Fin n → ℝ := fun a => ∑ b, (∑ c, D a b c * J c i) * J b j with hFIset
  set FII : Fin n → ℝ := fun a => ∑ b, (∑ c, D a b c * J c j) * J b i with hFIIset
  set FIII : Fin n → ℝ := fun c => ∑ a, ∑ b, D a b c * J a i * J b j with hFIIIset
  set FK : Fin n → ℝ := fun a => ∑ b, g (φ x) a b * K b with hFKset
  set GI : Fin n → ℝ := fun l => ∑ a, FI a * J a l with hGIset
  set GII : Fin n → ℝ := fun l => ∑ a, FII a * J a l with hGIIset
  set GIII : Fin n → ℝ := fun l => ∑ c, FIII c * J c l with hGIIIset
  set GK : Fin n → ℝ := fun l => ∑ a, FK a * J a l with hGKset
  -- reshape each COMBO group into `∑_p F_p * J^p_l`.
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
  -- instantiate the COMBO lemma in `D/J/K` form.
  have hC : ∀ l, pd (fun v => pullbackMet g φ v l j) i x
        + pd (fun v => pullbackMet g φ v l i) j x - pd (fun v => pullbackMet g φ v i j) l x
      = (∑ a, ∑ b, (∑ c, D a b c * J c i) * J a l * J b j)
        + (∑ a, ∑ b, (∑ c, D a b c * J c j) * J a l * J b i)
        - (∑ a, ∑ b, (∑ c, D a b c * J c l) * J a i * J b j)
        + 2 * (∑ a, ∑ b, g (φ x) a b * J a l * K b) := by
    intro l
    rw [hDset, hJset, hKset]
    exact pullback_christoffel_combo g φ hg hφ hgsymm l i j x
  have hcombo' : ∀ l, pd (fun v => pullbackMet g φ v l j) i x
        + pd (fun v => pullbackMet g φ v l i) j x - pd (fun v => pullbackMet g φ v i j) l x
      = GI l + GII l - GIII l + 2 * GK l := by
    intro l; rw [hC l, hGI l, hGII l, hGIII l, hGK l]
  -- apply `hpull` to each group.
  have hCGI : (∑ k, ∑ l, J m k * gti x k l * GI l) = ∑ a, FI a * gi (φ x) m a := by
    simp only [hGIset]; exact hpull FI
  have hCGII : (∑ k, ∑ l, J m k * gti x k l * GII l) = ∑ a, FII a * gi (φ x) m a := by
    simp only [hGIIset]; exact hpull FII
  have hCGIII : (∑ k, ∑ l, J m k * gti x k l * GIII l) = ∑ c, FIII c * gi (φ x) m c := by
    simp only [hGIIIset]; exact hpull FIII
  have hCGK : (∑ k, ∑ l, J m k * gti x k l * GK l) = ∑ a, FK a * gi (φ x) m a := by
    simp only [hGKset]; exact hpull FK
  -- the three Christoffel-transport targets.
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
  -- the `D²φ` term via the metric inverse.
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
  -- reconstitute the original Christoffel symbol.
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
  -- final assembly.
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

/-! ### N4 — the capstone: pointwise Laplace–Beltrami naturality for a general diffeomorphism. -/

/-- **N4 (CAPSTONE) — general-diffeomorphism Laplace–Beltrami naturality.**
      `Δ_{φ*g}(f ∘ φ)(x) = (Δ_g f)(φ x)`
    for the coordinate pullback metric `g̃ = pullbackMet g φ = Jᵀ(g∘φ)J`, its inverse `gti` at `x`,
    the ambient inverse `gi` at `φx`, and a `C^∞` test function `f`.  Assembled from `pd_pd_comp`
    (second chain rule), `pd_comp` (first chain rule), the raised transformation law N3
    (`pullback_christoffel_transform`), and the Jacobian trace contraction
    (`pullbackInv_trace_contraction`): the Hessian block contracts to `(Δ_g f)`'s Hessian, the
    `D²φ` blocks cancel, and the connection block matches `(Δ_g f)`'s Christoffel term.  This is the
    heart of the E-identification / `Vmap` gap: it holds for ANY `C²` diffeomorphism, with NO
    geodesic/exp-specific input. -/
theorem laplaceBeltrami_pullback_naturality (g gi : Point n → Fin n → Fin n → ℝ)
    (φ : Point n → Point n) (gti : Point n → Fin n → Fin n → ℝ) (f : Point n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hφ : ContDiff ℝ (⊤ : WithTop ℕ∞) φ) (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f)
    (hgsymm : ∀ y a b, g y a b = g y b a) (x : Point n)
    (hφinv : IsUnit (fderiv ℝ φ x))
    (hGGi : ∀ p c, (∑ b, g (φ x) p b * gi (φ x) b c) = if p = c then (1 : ℝ) else 0)
    (hGiG : ∀ p c, (∑ a, gi (φ x) p a * g (φ x) a c) = if p = c then (1 : ℝ) else 0)
    (hgtinv : ∀ p q, (∑ k, gti x p k * pullbackMet g φ x k q) = if p = q then (1 : ℝ) else 0) :
    laplaceBeltrami (pullbackMet g φ) gti (fun z => f (φ z)) x = laplaceBeltrami g gi f (φ x) := by
  classical
  -- the Jacobian trace contraction (as in N3).
  have hJb : ∀ a p, jacMat (fderiv ℝ φ x) a p = pd (fun y => φ y a) p x := by
    intro a p
    have hHF : HasFDerivAt (fun y => φ y a)
        ((ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).comp (fderiv ℝ φ x)) x :=
      (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).hasFDerivAt.comp x
        (hφ.differentiable (by simp) x).hasFDerivAt
    rw [pd_eq_fderiv (fun y => φ y a) p x hHF.differentiableAt, hHF.fderiv]
    simp [jacMat, ContinuousLinearMap.comp_apply]
  have hcontr : ∀ a b, (∑ p, ∑ q, pd (fun y => φ y a) p x * gti x p q * pd (fun y => φ y b) q x)
      = gi (φ x) a b := by
    intro a b
    have hgtdef : ∀ (p q : Fin n), pullbackMet g φ x p q
        = ∑ s, ∑ t, g (φ x) s t * jacMat (fderiv ℝ φ x) s p * jacMat (fderiv ℝ φ x) t q := by
      intro p q
      simp only [pullbackMet]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      rw [hJb s p, hJb t q]
    have key := pullbackInv_trace_contraction (fderiv ℝ φ x) (g (φ x)) (gi (φ x))
      (pullbackMet g φ x) (gti x) hφinv hGGi hgtdef hgtinv a b
    rw [← key]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hJb a p, hJb b q]
  -- the general 4-sum reorder (pull `a,b` to the front).
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
  -- contraction of the connection block (a↔i, b↔j).
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
  -- contraction of the Hessian block (b↔i, a↔j).
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
  -- the contracted connection term along `∂_k(f∘φ)`.
  have hΓcontract : ∀ i j, (∑ k, christoffel (pullbackMet g φ) gti k i j x * pd (fun z => f (φ z)) k x)
      = (∑ a, ∑ b, (∑ m, pd f m (φ x) * christoffel g gi m a b (φ x))
            * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x)
        + ∑ a, pd f a (φ x) * pd (fun y => pd (fun z => φ z a) j y) i x := by
    intro i j
    have hk : ∀ k, pd (fun z => f (φ z)) k x = ∑ m, pd f m (φ x) * pd (fun y => φ y m) k x :=
      fun k => pd_comp f φ k x (hf.differentiable (by simp) (φ x)) (hφ.differentiable (by simp) x)
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
        rw [pullback_christoffel_transform g gi φ gti hg hφ hgsymm m i j x hφinv hGGi hGiG hgtinv]]
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
  -- the per-`(i,j)` bracket identity.
  have hbracket : ∀ i j, (pd (fun y => pd (fun z => f (φ z)) j y) i x
        - ∑ k, christoffel (pullbackMet g φ) gti k i j x * pd (fun z => f (φ z)) k x)
      = (∑ a, (∑ b, pd (fun w => pd f a w) b (φ x) * pd (fun y => φ y b) i x)
            * pd (fun y => φ y a) j x)
        - ∑ a, ∑ b, (∑ m, pd f m (φ x) * christoffel g gi m a b (φ x))
            * pd (fun y => φ y a) i x * pd (fun y => φ y b) j x := by
    intro i j
    rw [pd_pd_comp f φ i j x hf hφ, hΓcontract i j]; ring
  -- assemble.
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
  -- match to `Δ_g f (φ x)`.
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

end QIQTH.HeatResidualBound
